-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2480
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:50:09.522876+00:00
-- url     : https://prove2.me/submissions/6d11f14e-ebdb-4a41-b638-e0014081d5b9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 445863309 ≤ n < 446043165 has `n! + 1` a square.
For every such `n` a prime `p > n + 1` (from a per-sub-range list, each prime certified by a
gcd against a product of all primes below its square root) with `j = p - 1 - n`,
`Q = (-1)^j j! mod p` and `N = Q (Q - 1) mod p` has `N ^ ((p - 1) / 2) ≡ -1 (mod p)`; by Wilson
`Q^2 (n! + 1) ≡ N`, so `n! + 1` is not a square mod `p`. Checked by the kernel
(`decide +kernel`) through the frame `BRFrame`. -/

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

namespace BRFrame

/-! ## 1. The criterion (Wilson + Euler)

For a prime `p = n + j + 1`, Wilson's theorem gives `n! * Q = -1` in `ZMod p` with
`Q = (-1) ^ j * j!`. If `n! + 1 = m ^ 2` then `Q * (Q - 1) = (Q * m) ^ 2` is a square, so its
`(p - 1) / 2`-th power is `0` or `1`, never `-1`. -/

theorem fact_split (p : ℕ) : ∀ j n : ℕ, n + j + 1 = p →
    (((p - 1).factorial : ℕ) : ZMod p) =
      ((n.factorial : ℕ) : ZMod p) * ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) := by
  intro j
  induction j with
  | zero =>
    intro n h
    have e : p - 1 = n := by omega
    rw [e]
    simp
  | succ j ih =>
    intro n h
    rw [ih (n + 1) (by omega), Nat.factorial_succ n, Nat.factorial_succ j]
    have h0 : ((n + 1 + (j + 1) : ℕ) : ZMod p) = 0 := by
      rw [show n + 1 + (j + 1) = p by omega]
      exact ZMod.natCast_self p
    push_cast at h0 ⊢
    linear_combination ((-1) ^ j * ((j.factorial : ℕ) : ZMod p) * ((n.factorial : ℕ) : ZMod p)) * h0

theorem crit (p n j m : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hj : n + j + 1 = p) (Q N : ℕ)
    (hQ : (Q : ZMod p) = (-1) ^ j * ((j.factorial : ℕ) : ZMod p))
    (hN : (N : ZMod p) = (Q : ZMod p) * ((Q : ZMod p) - 1))
    (he : (N : ZMod p) ^ ((p - 1) / 2) = -1) : Nat.factorial n + 1 ≠ m ^ 2 := by
  intro hm
  haveI := Fact.mk hp
  have hw : ((n.factorial : ℕ) : ZMod p) * (Q : ZMod p) = -1 := by
    rw [hQ, ← fact_split p j n hj]
    exact @ZMod.wilsons_lemma p _
  have hm' : ((n.factorial : ℕ) : ZMod p) + 1 = (m : ZMod p) ^ 2 := by
    have := congrArg (fun x : ℕ => (x : ZMod p)) hm
    push_cast at this
    exact this
  have hsq : (N : ZMod p) = ((Q : ZMod p) * (m : ZMod p)) ^ 2 := by
    rw [hN, mul_pow, ← hm']
    linear_combination (-(Q : ZMod p)) * hw
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have h2e : 2 * ((p - 1) / 2) = p - 1 := by omega
  rw [hsq, ← pow_mul, h2e] at he
  by_cases hx : (Q : ZMod p) * (m : ZMod p) = 0
  · rw [hx, zero_pow (by omega)] at he
    have h1 : (1 : ZMod p) = 0 := by linear_combination he
    exact one_ne_zero h1
  · rw [ZMod.pow_card_sub_one_eq_one hx] at he
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      push_cast
      linear_combination he
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have := Nat.le_of_dvd (by norm_num) hd
    omega

/-! ## 2. Modular powering: four windows (8, 7, 7, 7 bits; fast for `e < 2 ^ 29`; exact for all `e`) -/

def w7 (p a e : ℕ) : ℕ :=
  Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow (Nat.mod (Nat.mul (Nat.pow
    (Nat.mod (Nat.pow a (Nat.shiftRight e 21)) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 14) 127))) p) 128)
    (Nat.pow a (Nat.land (Nat.shiftRight e 7) 127))) p) 128)
    (Nat.pow a (Nat.land e 127))) p

theorem win (p a x u d : ℕ) (hx : x ≡ a ^ u [MOD p]) :
    Nat.mod (Nat.mul (Nat.pow x 128) (Nat.pow a d)) p ≡ a ^ (u * 128 + d) [MOD p] := by
  refine (Nat.mod_modEq (x ^ 128 * a ^ d) p).trans ?_
  rw [pow_add, pow_mul]
  exact (hx.pow 128).mul_right _

theorem sh_div (e k : ℕ) : Nat.shiftRight e k = e / 2 ^ k := by
  show e >>> k = e / 2 ^ k
  rw [Nat.shiftRight_eq_div_pow]

theorem w7_spec (p a e : ℕ) : w7 p a e ≡ a ^ e [MOD p] := by
  have d14 : Nat.land (Nat.shiftRight e 14) 127 = e / 2 ^ 14 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d7 : Nat.land (Nat.shiftRight e 7) 127 = e / 2 ^ 7 % 2 ^ 7 := by
    rw [sh_div]; exact Nat.and_two_pow_sub_one_eq_mod _ 7
  have d0 : Nat.land e 127 = e % 2 ^ 7 := Nat.and_two_pow_sub_one_eq_mod _ 7
  unfold w7
  rw [d14, d7, d0, sh_div e 21]
  have h0 : Nat.mod (Nat.pow a (e / 2 ^ 21)) p ≡ a ^ (e / 2 ^ 21) [MOD p] := Nat.mod_modEq _ _
  have h1 := win p a _ _ (e / 2 ^ 14 % 2 ^ 7) h0
  have h2 := win p a _ _ (e / 2 ^ 7 % 2 ^ 7) h1
  have h3 := win p a _ _ (e % 2 ^ 7) h2
  refine h3.trans ?_
  have ee : ((e / 2 ^ 21 * 128 + e / 2 ^ 14 % 2 ^ 7) * 128 + e / 2 ^ 7 % 2 ^ 7) * 128 + e % 2 ^ 7 = e := by
    norm_num
    omega
  rw [ee]

/-! ## 3. The factorial table

`mkT W k j f acc` appends `f = j!`, `(j+1)!`, ... (`k` entries, `W` bits each) below `acc`, so in
`TB W J = mkT W (J + 1) 0 1 0` the entry `j` sits at bit `W * (J - j)`. Nothing is assumed about it:
`tabOK` checks every entry against a running factorial in the kernel. -/

def mkT (W : ℕ) (k : ℕ) : ℕ → ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ) (fun _ _ acc => acc)
    (fun _ ih j f acc => ih (Nat.add j 1) (Nat.mul f (Nat.add j 1)) (Nat.lor (Nat.shiftLeft acc W) f)) k

def ext (T W M J j : ℕ) : ℕ := Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M

/-- `tabOK T W M J k j f`: entries `j, j+1, ..., j+k-1` equal `f, f*(j+1), ...` -/
def tabOK (T W M J : ℕ) (k : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => true)
    (fun _ ih j f => Nat.beq (ext T W M J j) f && ih (Nat.add j 1) (Nat.mul f (Nat.add j 1))) k

theorem tabOK_sound (T W M J : ℕ) : ∀ k j, tabOK T W M J k j (Nat.factorial j) = true →
    ∀ i, j ≤ i → i < j + k → ext T W M J i = Nat.factorial i := by
  intro k
  induction k with
  | zero => intro j _ i h1 h2; omega
  | succ k ih =>
    intro j h i h1 h2
    have h' : (Nat.beq (ext T W M J j) (Nat.factorial j) &&
        tabOK T W M J k (Nat.add j 1) (Nat.mul (Nat.factorial j) (Nat.add j 1))) = true := h
    rw [Bool.and_eq_true] at h'
    by_cases hij : i = j
    · subst hij
      exact Nat.eq_of_beq_eq_true h'.1
    · have hf : Nat.mul (Nat.factorial j) (Nat.add j 1) = Nat.factorial (j + 1) := by
        show Nat.factorial j * (j + 1) = Nat.factorial (j + 1)
        rw [Nat.factorial_succ, Nat.mul_comm]
      have h2' := h'.2
      rw [hf] at h2'
      exact ih (j + 1) h2' i (by omega) (by omega)

/-! ## 4. Prime pools

`chk6 P T`: `6 ∣ P` and `6t+5`, `6t+7` share a factor with `P` for every `t < T`; then every prime
`q ≤ 6T+1` divides `P`. A number `q < Bd` with `gcd q P = 1` and every prime `r` with `r * r < Bd`
dividing `P` is prime. -/

def chk6 (P : ℕ) (T : ℕ) : Bool :=
  Nat.beq (Nat.mod P 6) 0 &&
  Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T

theorem chk6_rec (P : ℕ) : ∀ T, Nat.rec (motive := fun _ => Bool) true
    (fun t ih => !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1) &&
      !(Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1) && ih) T = true →
    ∀ t, t < T → Nat.gcd (6 * t + 5) P ≠ 1 ∧ Nat.gcd (6 * t + 7) P ≠ 1 := by
  intro T
  induction T with
  | zero => intro _ t ht; omega
  | succ T ih =>
    intro h t ht
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h5, h7⟩, hr⟩ := h
    by_cases htT : t = T
    · subst htT
      constructor
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 5) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 5) P) 1 = true
          rw [hc]; rfl
        rw [this] at h5; exact absurd h5 (by decide)
      · intro hc
        have : Nat.beq (Nat.gcd (Nat.add (Nat.mul 6 t) 7) P) 1 = true := by
          show Nat.beq (Nat.gcd (6 * t + 7) P) 1 = true
          rw [hc]; rfl
        rw [this] at h7; exact absurd h7 (by decide)
    · exact ih hr t (by omega)

theorem chk6_sound (P T : ℕ) (h : chk6 P T = true) :
    ∀ q : ℕ, q.Prime → (q ≤ 3 ∨ q ≤ 6 * T + 1) → q ∣ P := by
  unfold chk6 at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h6, hr⟩ := h
  have h6' : P % 6 = 0 := Nat.eq_of_beq_eq_true h6
  have hall := chk6_rec P T hr
  intro q hq hb
  have hq2 := hq.two_le
  have hdvd : ∀ t, (q = 6 * t + 5 ∨ q = 6 * t + 7) → t < T → q ∣ P := by
    intro t ht htT
    rcases Nat.coprime_or_dvd_of_prime hq P with hc | hc
    · rcases ht with ht | ht
      · rw [ht] at hc; exact absurd hc (hall t htT).1
      · rw [ht] at hc; exact absurd hc (hall t htT).2
    · exact hc
  by_cases h23 : q ≤ 3
  · have : q = 2 ∨ q = 3 := by omega
    rcases this with e | e
    · subst e; omega
    · subst e; omega
  · have hb' : q ≤ 6 * T + 1 := by omega
    have hm : q % 6 = 1 ∨ q % 6 = 5 := by
      have h2 : ¬ 2 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd
        omega
      have h3 : ¬ 3 ∣ q := by
        intro hd
        have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq).1 hd
        omega
      omega
    rcases hm with hm | hm
    · exact hdvd (q / 6 - 1) (Or.inr (by omega)) (by omega)
    · exact hdvd (q / 6) (Or.inl (by omega)) (by omega)

theorem prime_of_pool (P Bd q : ℕ) (hP : ∀ r : ℕ, r.Prime → r * r < Bd → r ∣ P) (h2 : 2 ≤ q)
    (hq : q < Bd) (hc : Nat.gcd q P = 1) : q.Prime := by
  by_contra hnp
  have hq1 : q ≠ 1 := by omega
  have hmp := Nat.minFac_prime hq1
  have hsq := Nat.minFac_sq_le_self (by omega) hnp
  have hsq' : q.minFac * q.minFac ≤ q := by rw [← pow_two]; exact hsq
  have hdP := hP q.minFac hmp (by omega)
  have hd : q.minFac ∣ Nat.gcd q P := Nat.dvd_gcd (Nat.minFac_dvd q) hdP
  rw [hc] at hd
  have := Nat.le_of_dvd one_pos hd
  have := hmp.two_le
  omega

/-- pools: `6` below `16`, `30030` below `196`, `P3` below `32761`, `P4` below `1024000000` -/
def pOK (P3 P4 p : ℕ) : Bool :=
  Nat.ble 5 p && cond (Nat.blt p 16) (Nat.beq (Nat.gcd p 6) 1)
    (cond (Nat.blt p 196) (Nat.beq (Nat.gcd p 30030) 1)
      (cond (Nat.blt p 32761) (Nat.beq (Nat.gcd p P3) 1)
        (Nat.blt p 1024000000 && Nat.beq (Nat.gcd p P4) 1)))

theorem blt_t {a b : ℕ} (h : a < b) : Nat.blt a b = true := by simpa using h

theorem blt_f {a b : ℕ} (h : ¬ a < b) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · exact absurd (by simpa using hb) h

theorem P6_ok : chk6 6 0 = true := by decide +kernel
theorem P30030_ok : chk6 30030 2 = true := by decide +kernel

theorem pOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) (p : ℕ)
    (h : pOK P3 P4 p = true) : p.Prime ∧ 5 ≤ p := by
  unfold pOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h5, h⟩ := h
  have h5' := Nat.le_of_ble_eq_true h5
  refine ⟨?_, h5'⟩
  by_cases c1 : p < 16
  · rw [blt_t c1, cond_true] at h
    exact prime_of_pool 6 16 p (fun r hr hrr => chk6_sound 6 0 P6_ok r hr (by
      left; by_contra hc; have : 4 * 4 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c1 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c1, cond_false] at h
  by_cases c2 : p < 196
  · rw [blt_t c2, cond_true] at h
    exact prime_of_pool 30030 196 p (fun r hr hrr => chk6_sound 30030 2 P30030_ok r hr (by
      right; by_contra hc; have : 14 * 14 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c2 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c2, cond_false] at h
  by_cases c3 : p < 32761
  · rw [blt_t c3, cond_true] at h
    exact prime_of_pool P3 32761 p (fun r hr hrr => chk6_sound P3 30 h3 r hr (by
      right; by_contra hc; have : 182 * 182 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c3 (Nat.eq_of_beq_eq_true h)
  rw [blt_f c3, cond_false, Bool.and_eq_true] at h
  have c4 := Nat.le_of_ble_eq_true h.1
  exact prime_of_pool P4 1024000000 p (fun r hr hrr => chk6_sound P4 5333 h4 r hr (by
      right; by_contra hc; have : 32000 * 32000 ≤ r * r := Nat.mul_le_mul (by omega) (by omega); omega))
      (by omega) c4 (Nat.eq_of_beq_eq_true h.2)

/-! ## 5. One `n`: the test

`fm`: `j!` from the table for `j ≤ J`, else from entry `J` by the loop `lp` (rare).
`nN = f * (f + s) mod p` with `f ≡ j! (mod p)`, `s = p - 1` (`j` even) or `1` (`j` odd); this is
`Q * (Q - 1)` for `Q = (-1)^j j!`. -/

def lp (p : ℕ) (k : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun _ acc => acc)
    (fun _ ih i acc => ih (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p)) k

theorem lp_spec (p : ℕ) : ∀ k i acc, acc ≡ Nat.factorial i [MOD p] →
    lp p k i acc ≡ Nat.factorial (i + k) [MOD p] := by
  intro k
  induction k with
  | zero => intro i acc h; exact h
  | succ k ih =>
    intro i acc h
    have e : lp p (k + 1) i acc = lp p k (Nat.add i 1) (Nat.mod (Nat.mul acc (Nat.add i 1)) p) := rfl
    rw [e]
    have h2 : Nat.mod (Nat.mul acc (Nat.add i 1)) p ≡ Nat.factorial (i + 1) [MOD p] := by
      refine (Nat.mod_modEq (acc * (i + 1)) p).trans ?_
      rw [Nat.factorial_succ, Nat.mul_comm (i + 1)]
      exact h.mul_right _
    have := ih (i + 1) _ h2
    rw [show i + 1 + k = i + (k + 1) by omega] at this
    exact this

def fm (T W M J p j : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
    (ext T W M J j) (Nat.ble j J)

theorem fm_spec (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    fm T W M J p j ≡ Nat.factorial j [MOD p] := by
  unfold fm
  by_cases hj : j ≤ J
  · have hb : Nat.ble j J = true := by rw [Nat.ble_eq]; exact hj
    rw [hb]; dsimp only; rw [hT j hj]
  · have hb : Nat.ble j J = false := by
      cases h : Nat.ble j J
      · rfl
      · exact absurd (Nat.le_of_ble_eq_true h) hj
    rw [hb]; dsimp only
    have h0 : Nat.mod (ext T W M J J) p ≡ Nat.factorial J [MOD p] := by
      rw [hT J le_rfl]; exact Nat.mod_modEq _ _
    have := lp_spec p (Nat.sub j J) J _ h0
    rw [show J + Nat.sub j J = j by show J + (j - J) = j; omega] at this
    exact this

def nN (T W M J p j : ℕ) : ℕ :=
  Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p

theorem cast_nN (T W M J p j : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) (hp : 2 ≤ p) :
    ((nN T W M J p j : ℕ) : ZMod p) =
      ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) * (((-1) ^ j * ((j.factorial : ℕ) : ZMod p)) - 1) := by
  have hm : ((fm T W M J p j : ℕ) : ZMod p) = ((j.factorial : ℕ) : ZMod p) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (fm_spec T W M J p j hT)
  have hl : Nat.land j 1 = j % 2 := Nat.and_one_is_mod j
  unfold nN
  rw [show Nat.mod (Nat.mul (fm T W M J p j) (Nat.add (fm T W M J p j)
    (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1) (Nat.sub p 2)))))) p =
    (fm T W M J p j * (fm T W M J p j + (p - (1 + j % 2 * (p - 2))))) % p by rw [hl]; rfl]
  rw [ZMod.natCast_mod, Nat.cast_mul, Nat.cast_add, hm]
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · rw [h, zero_mul, add_zero, Nat.cast_sub (by omega), ZMod.natCast_self]
    have : Even j := Nat.even_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring
  · rw [h, one_mul, show p - (1 + (p - 2)) = 1 by omega]
    have : Odd j := Nat.odd_iff.2 h
    rw [this.neg_one_pow]
    push_cast
    ring

theorem good_of (T W M J n p : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (hp : p.Prime) (hp5 : 5 ≤ p) (h1 : Nat.blt (Nat.add n 1) p = true)
    (h3 : Nat.beq (w7 p (nN T W M J p (Nat.sub p (Nat.add n 1))) (Nat.shiftRight p 1)) (Nat.sub p 1) = true)
    (m : ℕ) : Nat.factorial n + 1 ≠ m ^ 2 := by
  have h1' : n + 1 < p := Nat.le_of_ble_eq_true h1
  set j := Nat.sub p (Nat.add n 1) with hj
  have hjv : j = p - (n + 1) := rfl
  have hN := cast_nN T W M J p j hT (by omega)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with e | e
    · omega
    · exact e
  have hsh : Nat.shiftRight p 1 = (p - 1) / 2 := by
    rw [sh_div]
    omega
  have : NeZero p := ⟨by omega⟩
  have hw := w7_spec p (nN T W M J p j) (Nat.shiftRight p 1)
  rw [Nat.eq_of_beq_eq_true h3, hsh] at hw
  have he : ((nN T W M J p j : ℕ) : ZMod p) ^ ((p - 1) / 2) = -1 := by
    have := (ZMod.natCast_eq_natCast_iff _ _ _).2 hw
    push_cast at this
    rw [← this]
    show ((p - 1 : ℕ) : ZMod p) = -1
    rw [Nat.cast_sub (by omega), ZMod.natCast_self]
    simp
  exact crit p n j m hp (by omega) (by omega) ((-1) ^ j * ((j.factorial : ℕ) : ZMod p)).val
    (nN T W M J p j) (by rw [ZMod.natCast_zmod_val]) (by rw [ZMod.natCast_zmod_val]; exact hN) he

/-! ## 6. The prime stream

A stream is a head prime `ph` and the packed gaps `Gp` (8 bits each, gap / 2, low first).
`sp i ph Gp` is its `i`-th element. Once `Gp = 0` the stream is constant. `sOK` checks every
element against the pools. -/

def sp (i : ℕ) : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ) (fun ph _ => ph)
    (fun _ ih ph Gp => ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8)) i

theorem sp_zero (ph Gp : ℕ) : sp 0 ph Gp = ph := rfl

theorem sp_succ (i ph Gp : ℕ) :
    sp (i + 1) ph Gp = sp i (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := rfl

theorem sp_const : ∀ i ph, sp i ph 0 = ph := by
  intro i
  induction i with
  | zero => intro ph; rfl
  | succ i ih =>
    intro ph
    rw [sp_succ]
    have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
      show ph + 2 * (0 &&& 255) = ph
      simp
    have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
    rw [e1, e2, ih]

def sOK (P3 P4 : ℕ) (f : ℕ) : ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → Bool) (fun _ _ => false)
    (fun _ ih ph Gp => pOK P3 P4 ph && (Nat.beq Gp 0 ||
      ih (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) f

def SP (ph Gp : ℕ) : Prop := ∀ i, (sp i ph Gp).Prime ∧ 5 ≤ sp i ph Gp

theorem sOK_sound (P3 P4 : ℕ) (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true) :
    ∀ f ph Gp, sOK P3 P4 f ph Gp = true → SP ph Gp := by
  intro f
  induction f with
  | zero => intro ph Gp h; exact absurd h (by simp [sOK])
  | succ f ih =>
    intro ph Gp h
    have h' : (pOK P3 P4 ph && (Nat.beq Gp 0 ||
      sOK P3 P4 f (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8))) = true := h
    rw [Bool.and_eq_true, Bool.or_eq_true] at h'
    obtain ⟨hp, hr⟩ := h'
    have hph := pOK_sound P3 P4 h3 h4 ph hp
    intro i
    cases i with
    | zero => exact hph
    | succ i =>
      rw [sp_succ]
      rcases hr with h0 | h1
      · have hG : Gp = 0 := Nat.eq_of_beq_eq_true h0
        subst hG
        have e1 : Nat.add ph (Nat.mul 2 (Nat.land 0 255)) = ph := by
          show ph + 2 * (0 &&& 255) = ph
          simp
        have e2 : Nat.shiftRight 0 8 = 0 := by show 0 >>> 8 = 0; simp
        rw [e1, e2, sp_const]
        exact hph
      · exact ih _ _ h1 i

theorem SP_next (ph Gp : ℕ) (h : SP ph Gp) :
    SP (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.shiftRight Gp 8) := by
  intro i
  have := h (i + 1)
  rw [sp_succ] at this
  exact this

/-! ## 7. The walk

State: `n`, the prime stream `(ph, Gp)` (`ph` = the first prime `≥ n + 2`) and the record codes `R`
(low bits first). The code `t` (see `tsel`) selects the prime `sp t ph Gp` for `n`. The fuel is the
number of `n` still to check; at fuel `0` the walk requires `n = nE`. The body is written flat (lets,
`Bool.rec`) for kernel speed; `walk_succ` gives its meaning. -/

def wr (b : Bool) : Bool := b

/-- the record code: 2 bits `c`; `c < 3` gives `t = c`, else `t = 3 + ` the next 6 bits -/
def tsel (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) (Nat.land R 3)
    (Nat.blt (Nat.land R 3) 3)

def rnx (R : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) (Nat.blt (Nat.land R 3) 3)

def adP (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3))

def adG (n ph Gp : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3))

theorem SP_adv (n ph Gp : ℕ) (h : SP ph Gp) : SP (adP n ph Gp) (adG n ph Gp) := by
  unfold adP adG
  cases hb : Nat.blt ph (Nat.add n 3)
  · dsimp only; exact h
  · dsimp only; exact SP_next ph Gp h

noncomputable def walk (T W M J nE : ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => ℕ → ℕ → ℕ → ℕ → Bool) (fun n _ _ _ => Nat.beq n nE)
    (fun _ ih n ph Gp R =>
      let c0 := Nat.land R 3
      let b0 := Nat.blt c0 3
      let t := Bool.rec (motive := fun _ => ℕ) (Nat.add 3 (Nat.land (Nat.shiftRight R 2) 63)) c0 b0
      let p := sp t ph Gp
      let j := Nat.sub p (Nat.add n 1)
      let fj := Bool.rec (motive := fun _ => ℕ) (lp p (Nat.sub j J) J (Nat.mod (ext T W M J J) p))
        (Nat.land (Nat.shiftRight T (Nat.mul W (Nat.sub J j))) M) (Nat.ble j J)
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (ih (Nat.add n 1)
            (Bool.rec (motive := fun _ => ℕ) ph (Nat.add ph (Nat.mul 2 (Nat.land Gp 255))) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) Gp (Nat.shiftRight Gp 8) (Nat.blt ph (Nat.add n 3)))
            (Bool.rec (motive := fun _ => ℕ) (Nat.shiftRight R 8) (Nat.shiftRight R 2) b0)))
          (Nat.beq (w7 p (Nat.mod (Nat.mul fj (Nat.add fj (Nat.sub p (Nat.add 1 (Nat.mul (Nat.land j 1)
            (Nat.sub p 2)))))) p) (Nat.shiftRight p 1)) (Nat.sub p 1)))
        (Nat.blt (Nat.add n 1) p)) f

theorem walk_zero (T W M J nE n ph Gp R : ℕ) : walk T W M J nE 0 n ph Gp R = Nat.beq n nE := rfl

theorem walk_succ (T W M J nE f n ph Gp R : ℕ) :
    walk T W M J nE (f + 1) n ph Gp R =
      Bool.rec (motive := fun _ => Bool) false
        (Bool.rec (motive := fun _ => Bool) false
          (wr (walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R)))
          (Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
            (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
            (Nat.sub (sp (tsel R) ph Gp) 1)))
        (Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)) := rfl

/-- `Cov A n`: no `x ∈ [A, n)` has `x! + 1` a square -/
def Cov (A n : ℕ) : Prop := ∀ x, A ≤ x → x < n → ∀ m, Nat.factorial x + 1 ≠ m ^ 2

theorem walk_sound (T W M J nE A : ℕ) (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i) :
    ∀ (f n ph Gp R : ℕ), walk T W M J nE f n ph Gp R = true → SP ph Gp → Cov A n → Cov A nE := by
  intro f
  induction f with
  | zero =>
    intro n ph Gp R h _ hC
    rw [walk_zero] at h
    rw [← Nat.eq_of_beq_eq_true h]
    exact hC
  | succ f ih =>
    intro n ph Gp R h hS hC
    rw [walk_succ] at h
    cases h1 : Nat.blt (Nat.add n 1) (sp (tsel R) ph Gp)
    · rw [h1] at h; dsimp only at h; exact absurd h (by decide)
    rw [h1] at h; dsimp only at h
    cases h3 : Nat.beq (w7 (sp (tsel R) ph Gp) (nN T W M J (sp (tsel R) ph Gp)
          (Nat.sub (sp (tsel R) ph Gp) (Nat.add n 1))) (Nat.shiftRight (sp (tsel R) ph Gp) 1))
          (Nat.sub (sp (tsel R) ph Gp) 1)
    · rw [h3] at h; dsimp only at h; exact absurd h (by decide)
    rw [h3] at h; dsimp only at h
    have hw : walk T W M J nE f (Nat.add n 1) (adP n ph Gp) (adG n ph Gp) (rnx R) = true := h
    refine ih _ _ _ _ hw (SP_adv n ph Gp hS) ?_
    intro x hx1 hx2 m
    by_cases hxn : x < n
    · exact hC x hx1 hxn m
    · have hxe : x = n := by
        have : x < n + 1 := hx2
        omega
      subst hxe
      exact good_of T W M J x _ hT (hS _).1 (hS _).2 h1 h3 m

/-- one sub-range: the prime stream passes the pools and the walk reaches `nE` -/
noncomputable def sub (P3 P4 T W M J nE f n ph Gp fs R : ℕ) : Bool :=
  sOK P3 P4 fs ph Gp && walk T W M J nE f n ph Gp R

theorem sub_sound (P3 P4 T W M J nE A f n ph Gp fs R : ℕ)
    (h3 : chk6 P3 30 = true) (h4 : chk6 P4 5333 = true)
    (hT : ∀ i, i ≤ J → ext T W M J i = Nat.factorial i)
    (h : sub P3 P4 T W M J nE f n ph Gp fs R = true) (hC : Cov A n) : Cov A nE := by
  unfold sub at h
  rw [Bool.and_eq_true] at h
  exact walk_sound T W M J nE A hT f n ph Gp R h.2 (sOK_sound P3 P4 h3 h4 fs ph Gp h.1) hC

theorem cov_init (A : ℕ) : Cov A A := fun x h1 h2 => absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

theorem tab_all (T W M J : ℕ) (h : tabOK T W M J (J + 1) 0 1 = true) :
    ∀ i, i ≤ J → ext T W M J i = Nat.factorial i := by
  intro i hi
  exact tabOK_sound T W M J (J + 1) 0 (by simpa using h) i (by omega) (by omega)

/-- assemble a big number from 8192-bit groups, low group first -/
def asm (L : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun a _ ih => Nat.lor a (Nat.shiftLeft ih 8192)) L

end BRFrame

namespace BRData

def TB : ℕ := BRFrame.mkT 1680 256 0 1 0

def MM : ℕ := Nat.sub (Nat.shiftLeft 1 1680) 1

theorem TOK : BRFrame.tabOK TB 1680 MM 255 256 0 1 = true := by decide +kernel

theorem TAB : ∀ i, i ≤ 255 → BRFrame.ext TB 1680 MM 255 i = Nat.factorial i :=
  BRFrame.tab_all TB 1680 MM 255 TOK

/-- the product of the primes up to 181 -/
def P3 : ℕ := 0x30e06b35ee39cf75358315a5c3b9b2bdd2e46e25fd10a14382537a2e71312

/-- the product of the primes up to 32000, in 8192-bit groups -/
def P4 : ℕ := BRFrame.asm [
  0xdf0c850baeddb2128ac9d0fd36dd0ec2f329ef90aca3308ae6b7bcedec1424921497fc345111e60cc412113537268a736f809fc9cefc2bcbe959a57ecf6fcdc7dc216df46f82fa5bf3720c4270cf6fb13e1dcf489d98985e4f734ee9fac8505c106eb7b2acdb6bb26b79b9cd02729d2a2b215b45d1ad39b752020674f4f03993d6c7a96c9df2c43cdd5fcdd4a2a82b5082c3e0eab548cededa2cc10cfb2c34e6f98c290160b64fdf83e7d3438e6077c84a97d92b85d47ac7b128a35167b6e0531f91938128b16ed40b0ea8ed276a4a879f7c745e779c2215fa0572e7a15cae72ee309c077cfb5b3d707818405d883f07d24cd50cd5cefb61fd23ae30b49766951623101af6e194dae9d45749c5926504c31b2e31d16b3a1d8d8f628e30e1137c5dd8637ac50c416fb56e780354d53f83146505e0b75b3fd791dfb6d1cccdf46dd3bacd8c80998bafeec517c181f3bb39e1a7ff75b63960e7e4fbfa4ab3cd18f8673b3d211d62f5e0b3e98f4fcf16bc36e8d7000957b714c4798645de1678e06a21c7cc25ca8fd857afcda85428c1cff131cba807766664cd1ef92b24719ad71a1cacc089d80d1baf2446d3f91edab2290690b4fb849083f3506e79ef43443cfe351c5874753757cdb387af230e22804870783e587646125c93d5e22899c55a15ce29a46aa788de770abed396e6fa35fc451018422e12cda42c1968eb0b94f01da5b9943508ea2fe4ba6651d5d47287366890f2cd535e3789780c5933d6df7e974200cef40380b365f780703c6c344beeb37d043d1ef50ebe5b4b1dc45ace9088eb5474968a0e3305d300ae7a40322ab01357e0cffcf44216a95c444ff2a19bac8a80242e5b642615b266fa3b82e4ebec98b03bd5f61703e03d249324888f88edca090f5ed1243e0a4675f6ae3953d13092b10e09246ac59dc44eba77e164dbfe0f4949818965554093616dc9e4d28ec2f4206870ee44b9ad38fba67c42730b4845e2204f42dcb968564cf342d81da1dbbcb2ad1f705abde27272ca6eb434e635441102a00bb1b3837369200971d33813d146a5507c16e5102a5474ae182d25b8f97aee76e787fb717b4826f264800d01b229407e10b46c31d717cace03707e9813842dde7b9c675f84a599ec1ee76abcbcd5643683142b3af9a5e3ba165a9c8a2d3a8d31de317adde8d146dae44c42d3d79b56996c6c55111ea3f81174d232c5ae8bcf0f11585f68cb32a6395e58907339157f0717bc3ea165222c9ec5363162cf78432b92d4ae5025439cbe242ad10e1460f96a3b9257bb1a9075a34866508f80116c20e59d9ef0bcc790262003e760d1d5a97248b955f6cc61eab2893f5cb8e57f2f293c308165efec92b10c382c1a7f4d7b6b32691a1b62141c02811f4b3027674bebab643b34a70f166e082f1a3489b265b5b1fee25e582b1b076210fe9a,
  0xea98014cae2ac4237f4b4213a735cb3415a1380744196e3371ef349273475b1a9a19eea2b2d83e892b4404ffc9ec8f00c804866f9a9ce72904a292c8101dcfff2039576180f44def879add63b1eccb590677693cae9f49dbf554c6ceba32faf6e84616a64ecc2681a2c895e1090378b6222b56e1bd9cb731fa2064f7b7f066b45169170ba0d08741bd1b0820d77238b47918f994c8aced205746fc0ff5ddd8cf95dd8ef62dd050286266519e45e40e5b2950b8b223c07f101ce162963018ecebd501267eaddb02f56ee6b654257d20d3bf13f73db708520ed0117af6564bb8b0a469856a8cc3e2cae84a242db11e2b060f957bfdc5baa0d4c74a319342609401e3be3e2cf7e1993561e8784857ff0965514a4a9f7a10dcbb1fea1c8cf72786bf6e32594aa1d4908db83d4dfb1c3f8cd9d7a4aa673346618dca07b597d1815974f7e7e86e6d40001b0442574f4404912ee91e38bd7d52aa3eb4ba0fbd5446f731b1baa64f5d05d16a29f33c5cf42cf1f8c2f1d0f96b9a325944e8f02b0169806f2efa153ceefd95679ff923ecc80ceafb98996c16305b5e644d2071399cb7883f6b8a85be82455a9824ef5c3288e149fd62ecee29447798e1f5ea7d3919c51b567ea37288bbefe5b6d943b1edeccad5d4a1284aeddf22256e16e5017fe48dda91d4a4172047b9b6ebdbb35f04afab8a3534b41b758159b035c092cc36876c6db744cdc4558288c5ada4a7c4ca4ef963e05eb3b79ee9f2ba92cca910e4fe4419e33cd12dbd87527274732251e53c0c447842cca8504abf89fb2a0fe66269142a99315d9cfd1cb18ff00a8c0cc9b7d21e6b2d9bba36823cae88b84340801e5c81472d1211357bf791b4b9a83cb8f885a19b4d93e68561301fa92d04eac64892047c44106b572731bc2bc586f7d428463bf12880ddf84b9bcb8b75d18f68f07b2d3a4529f33c265efaa9046e94f310aa9a47d70bf8cca38f0a707a6ce8c2756003dc094a30edb3a17ef3aa4894be8e5d72e22421f097677b90ef6274cb0fe493550d58529e9b9331d11bb641d336d163489ce32364bdf6ed4b327e5a56409b1e276f1ed03f5afc4b1f1eb46f50ea2bd818b6ce560fcf4033323b7f46aab313f4bc2688a9e8ccc1545c5c811b34d48d14308a334a169c2016d94e11129100571fa1dd1c841f5a7bfccbabbc545dba69de8cd04f05f4ad32d476559836d35aca9a7381fa618e0c7e7855e9cd829a0cabdbe9e3c01746e3ae03c2e18f4aa76ef419e3de8bfe4b21500785d9b6964477b8a840ec2cdc45f3227e280e2c5f8f6c6a26c3881003f03b9c89575763154d252dc974ecf290538b9105fcea649307d65a15a817627084c27089384b6073f28023d245a2d78437adc9909abf78ae77d00006f6386c40a33acffa01cdf3667bf58b5a38e6502cd21718fca0d04aeabb5d7635e4b4,
  0x1728b345ae1d105890be726995db87cb8d8643422401f2b9d4fd947140af5fdd89523ad14c14787386bde21dc9610b22e07e931ba28009eb69a71e1cfbc0df11d42c4526b66824c91f442c5636d120007e4d24e3bad931045a7365deef650235aae6a3996d4288b7a45118f689202f6eb7631f39ccfe3ed30df63f6dfa1eaea9abcfc0fbb1889d08158387786d5babb4711aeca73bc3b3e7f510660123273125559e32ae86789b3eea846b65e518bd1b82f86a68b6622dee93c66f28b57bb32c66c334eb0e4e18da04a01e1458f10bfb1b91ada31354048151dc2f7b5e1d35cd094790b3a592983b79c98f2002554d6ac0753e09d4c95de4b0a2dc4af58bc18ba1c404b3cf1f6f5e6353388ba00542736dafb6b3890ed4eb1aa021baa0a1027503756833e069161f3b5df47575a40f2ed8ae5cf84444b7fb646bd1ccb521788b5d39ee4e9492f45b5052f2f8d973d0e798ef2bea1edb9884c1f5ad82ff9f2da775d8c1abba03a5c92ff2c3ccc31a8afb22947e1d06745a05cf02d819e21c1b9eeb81560ef0e999cbf56d4bdb20ee9ae7563555bafaaa67efb0cb235529236a4abc3bbed82dcdf54e45470f179f2174157be3c2cad7e76c7b9fa12a3cedcea2a33cdb5facb5327aead5e2ee441ebfe4a944440623d53d4bdb3e5fa4e7f03a0f3ce18b1b2507fe33b65c49534c5ef0e31577cb2e11c80dd4827e40e09ce1cef2aa8a0b6d04973a6431ea0e721a266ed55b1d51682cf24816a6ef7c28d315fd2c4efd94b46caeb7fa54aa9b6e0b0061cbdd73b551b7a80783e8e600f9a9162f2199788c98a444e28ebb46b57043028fe6c474260640a987cbb7babaf34191506f6a669df1064bb5d3a4522f3706dd1a5615ca291b33cdcc418266d52fda48d187a9bd0c40513361bd5652581c1b2ab80879f9b9c802787745e17a9791fe2d94f2bbbf9e8bd08fed5d2fc21b095a1d18135390d99ffac0dba4a55c77a4ccdef9c1b63ab95770f5296498093b9806389530270a161a78b2759215b5156f0b69960117f858d201d20305aac1d8936d3d8c70293ead432613a327abd5d6b7ec767a694bccfceffb2f505bb0e8cf019e8ba6c25ba9c8a66d8ab729be0c889e5c33b9b003a2777b2ee1a7f1ac50a0b600f9df13abc417f92e56a627fec3318cfec09c3ce8ed11cd38beecc9fe62800f28b554bbb032d54ec3265b9510da2763ffbffa465ebba8541e162029eb43803ead99cc036eac2906e2508acfd0b87815960f33f1250c4c93c84772fcf343e319166a963b9438080e93537495f38e222f30b9388f432d57e061f06db832fc76cd7c2246cdbc725791eedbb0f020e4518bb711c9947fd13da39b34eeaa20b783fda7c7fd6bb5a6bfc5ae0aac9be0260efd746edb56cbad7adf1f59b4ef5590ebf5dc901afac752539f95fa616c0121643f4021b923b,
  0x3c458fee709566842171df4fdf91d1866173d1b733c3309816fb19e69ff4d6644f481709bd1680e21b432a184cfcde4bd4f9b43742cb46b2f3ffd58b5ca10366aa342a9454eedf37ffe61d5b7b01c242438d0aa617697b258e4b6e05f86953963e9b1fb21af5ca4ee94189cb1a9899de56581900c1cb81777ee13638ac508ece1dd9c8bf76060130ee98831d9c1fb6548e12387a276ccb9a1faf40a2ee45223252152bd2949b6b5a7ee3ed5c2879d3abcd1a50c7fafe7d7464053500e063887b01e11ff8f5c27000443e192c9ec6511816a4ef4f6c73c364b4b4e11e4b0f6f2bbe6941fc1002d33c2ea0d80d7c2e37e70d298651f344f10070630a47cd0f686b749590c52fe4333d58a21b210eb744d4e7df8a6d79ce7137a4ba9425114e86d112ff16e899cd2041bb3781489ce56232fa4de91c7ae07bd635bf1f0e554e20163b0a43ed81ab1095811abc702564c76b49adcbc3f5264e74823a695e1847b559021d6babbe9d6989a4eb4d5ff4dff6de9169bddcac984a8bf3d9f653c91cd620b187bdf4e086e2cff33827ccf543d72f80d31c0cfa9b0ec3344ac92fd84b3a3671009f4929fca57466981b49b59806ec5b95115c1d11b21099d94bf85ef0b7bdfdcf30ef86cc521e5a4d267c48da55d3b81706d40dd2e26357d7c865da72c94fd723e3cd37aab7bc2e17c9ae1368ca36ae70f1bb5432a861bc0a79709b81f23807835b1bd97dd958f89f546ca0e74a4d91f2231841b97abae7f63d1dfa52d8d2ecbeb25f730e389347efe4030f78f44b1349e216256ce33d6dcbfd14f9b722f85a32cfcc28fb734de661fad78e2c6065b1a970274a9d4c4b238078e5ef2675620ebe8efc5874a7560f17ae9186eba32895c80e9ab5a9367ceaab065805a41b340cf88a6316b15964530bdee05e98635f268eb9aefe7c81d872c1f52d89472c117d4ead5cabd5874110e0a849337c38acfc60a476b55091afdb9c59ea0200bc2c98cb8fafcdb89a5593e6169294a2d7ad79b4d4bd02449d332f5f101f8a95a668b28a9aa5d4ee6f63265932a22b93e6b08c3cb4ce49b2114839ae8d669db30e78886393dfa8e92535a3232ce2d3b388df674137547d46af3ac76aa08a3962b010a924cecef13be7fc1ee1f857c0c1b148c8350206d93cc1c26bdf2f2083e0632187a7170294c132c8c96452ed414567d17115f3d810463dc5845b0e4b2150676860213d04f9e6b1ee1530faab6ee6281c815dc26cd93cc02c8ed58742168b4bcfe102c25dcf152f8c36ededf5c24b756d43201d572e5ec91e785f50244eac7936a17ebe3e80d537492d9ddbfbc53ed3828000ae06dd1478f12304cfaeaf8b594901c5010f524a109d67422dcf2e00b03dddfcb9ee1060b28f0156ff8707686b109c780e98ff3732bd116d2f70c96ca688419b65cdc52070b6929bfff088a3be5f,
  0x33fb30670ccc9d9161ee291159b243d56af86e6c0d29675ffa2c459c998f0c513dd30d097fc73d45684ecd2c87d420a96eddb72894cfb6b134d8599ab23ca2ce27ef0706a741bda8807b24ea39ef3e5da8774e5f2219c3cbb5573bccfa96c4c5f9b3a11dd2cc735f288dc3a82281b63255a99bc8a5e1c55002df7fda7afac36a1d276383158d287c2a4db62276a331b0b14239ceb7b72b9229337e828e76bd3b13316c1bc98279fb890663222d6f91722909d219a67282cad6eed54326f5e3ea9b7aa50d70e0e9caeec704373d0bf36057bfed71c9e794676fcf07be1e1c0ad66e7790c09f157620dfca3e522db1ac9e18ff6aa4f5ee9f682e9b4a56211d5d51aa3fb19b25926b06393d3c4c47ae87ed8c52d4f19f54ba73ad3fa32cc3da4857c98d0fa5363a46671d532322b398f90422bd732d02d272ed70fbfd0cf7be141b677000847b96d192296c900eda94ea4023fdf00bf2e7a6a9381d832e4e1189a35136b481179ba243c5661a527b140c93d9997eb066a8554bb1b07ac04974f076092dfc159a231f26ff9e7fec54a1a4afc94c723cbc812012373c707e0c81c5783247e3416ec84e3a4aa240527a9339adade0e966d9acc3a1867b2e62b4ab1f43d342508113196ac649cf973d1f98067ebe3662022398d0617ba378bc09596a6403112db6adcca330e099daa38cf9f921c1459c9f97d4be291cb38007fc34a018edb5af08589e98b71ab0e99acfda859889c4a0360109261ff6e40c85327af396767fdac713adfe8caaec684bbcab3fea995f660af05b974c5ba6ebf52d1f8e2b31117cb8faf93a0e939836d3b6af25604d7d5b4f6e144a0485d0c5b5400d4713de63a2736fdbbd20ebb835cc9591b48e10764f4744729730117cf94bd42e70f0f2e86b609f59053a2f94f83d2c855f49bc0563edc62683301a6f1af059fbedbfcf1769c0e1fe4ce07b65de8b71ade682636d0abde0bd94cdde2e1cef86e715d495cddfcdf0e420d7fc6c7b523f6cc2a181df5c50d713f7142e22812e9b36d83d5c41a754fe1e2243d67bcc372a7bc1f7b3cd66155a6d68f2d78535f6ead61180b20a9b7345e87ee56618dcbe69453bfb5db4ed7337f698e5b98735b83d30c6b59ca226c04df477bae76bb50da3ba91f4f324c51588c99d2b8258edfe273d77883d519f5059f50178c73612660f88af6f622035e53bb5cb8421128833d0e2963696885b2672976bc22bdef66a3f79a1eeb5745b266abaae035f56d7da1f92773d588519cfb671cf7f840b8c0eece8eaafaa8cdc7bd8e95db47b86de2f99a5c118b3d336c0cf108f8b13199d11f183c61a0e7fe7d42a609536ad880d22ef9acd6e7a26f94aa1aaf1cddea57ca24edf80e18bb54dc9142b3f9de36aa66add5c83fa9a1b3827de04c3ac9a362fe20443937a0dc21250e8d6183c51a530b2ff77d24,
  0x556d7e991792de0f391465729fa66f7cb4cd30e9aeda0d488686bbeaccac9ce166df07cb523e600a3b36496464fd6e277847eea66bbfbbda8d20d01bd4dac96841254b0ff6c61a90385a3239eaab5887ebdd5a6bcf72691ab6644a094162fe467ce8c72e372883ce54ca28eb67362b5b180ca57cfc027037004145ac514e280b4249af145522f74ad3b0f6eb124e1ba8e994e4ddc0dbdd8cf3f80b42f338206e5313438d9856c4af110573fa215009a4a69f506da8f1fc03695d08ba2ea83ba5b5a7e289910d1ded13d31f5810300e41bc97799d709db61c06dd64bac664891f71d68e45800f73cda9d18f19015497d2048b5193e343f89677fa0fc96fac78929ca8a69f8eb195e7705bb820a2c1d044b922b3b6cd5504ff78a3cbededfb7f1ddaa0ed0869a39884c6f13673cd0cf984a8bfdb025a3bb1af56f4031d5d5b37016db05548dedce76724a7fd52bfdec469e49a2080da2082e93fb0e7b8984d7515b69b3237649436f27c00b00035ef33f41f982ea205940153bfc318e858a5987c952474bca14aac913b1b4ab909216ee44902547a558dee848dd30c0c77b4d2794e7b6b4757e9816025934a0ca36430fe238884e8e64fadbb0d3bcaba4a39af73014f4c5e97e70e5de24c3fd9d2783b3a430158d1a672220b22612a92cf52e32121f8a5aa83d3d87fcfed7751c93bad78d5787354ebe4574d159fff7971b47dc3e0bb5c71f97a51f75996eb949d7565f8e6a18beb27aab1db5b87394d2b1525140e3493920f7b50ea878a9be48bb9e59ffc3746855d8bdf084cf0ce93a39f6f14d5b3a7d76372b40e5870bd37b3449fe5689e]

theorem P3OK : BRFrame.chk6 P3 30 = true := by decide +kernel

theorem P4OK : BRFrame.chk6 P4 5333 = true := by decide +kernel

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 445864559 1250 445863309 445863311
    0x60a110901210e011a0405040c150c050d0302041a03160806150409021306080f0a0b15070303091205070b0105090403020307050706090603050a05010b0d05071107141212070303 77
    0x40d038000c01000c0e1110b100030701c04491820300242c031110400643c0410030f460741460b01c00c200010800300b40803c87d142110010300b001803d01043c000c0003035200784801564424a003030340c80e200072503980070b05019000d000b080229030003140c103218501140c80b64448c0c0d50b0f040130442e815481d004c014030041c412600c0d40e102c02c3c0f10040c80403942c01c2e1500c2d00101c42845004044903921652498114001d6002c00790018042010740e002182e464404e4a80500426850300303451100e449800d00c0d5002080c4204610f80d001201614500841c1401809000b941d802500c0006a00905050114041480385943c1c41040810045d0313800245440080c103064902c185e40b41c0f5034030f59403850140d01e18410340340050b08500c0740000000d52254451144001e0341d4103a9030510203a1202c04e0088142e600a00408400c3c00d02400202c06031986075100d2540960f0300d1030960b812280745840c0c01c2c2480d01e16089000d11983c003d0312502141450200c01003541d0407000145400301100715120114010000020105 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 445865809 1250 445864559 445864577
    0x60f10020a1401061710051f140d0c0311010e0f130e0a0609080a09050a0e06061305040501080c1509090c070807080a0c061a10181701020c060a110901 66
    0x3a080075031110018103904100b00c40f42216001c45107640e8110f13400c3d2a00040e0400c0005407610052101c0700642c8208c0c5086400c000d4200b08001c0000c8503869200c58210741d004031034801003100410203000850082c1c0c0c01d122070a6043c0c0c001003002c1c1c295660107000340c42440c2c09480984170b21141d154541c0820000196941d1180c4410b424400c0c03088020348030034140311944c0d003404280401405a142940c48103000c00340d481083c4401d8192070310400300c0a0b80d444001a0403414000000d088035503620700c0c42d41000f612400001c2c101c641c04e801640080c0e10440c42d041e181c0c205800e00c04581c0081d120043d007003541c03243c0051480f110007007200050701d001103604420850f810b4107030351500d6404050700d91242044e410003428060414400c1e180c1e182040012000360303210680c00344c906040a0035141c102007804100340d400050307a030281c910303034030041c0d4001580d4114054003c0c0e084050200242e6218111a1040d107489005402581d4191a00881c0d802c8052258115500302d80282041500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 445867059 1250 445865809 445865843
    0x6031a060a23010e03010203040c1502060702030d0b010e040615020d03060b0d0e0a1e11060310050103020a020a02030109050123070f0309030c12120f0c121d15060f10020a 75
    0x81c0280103000c4c030307019070000c030034003080058042d510003d0322095641085d5201c1000012640c503101920400b025030003c00c02030604400a8000701105075040c10050b4400e01802d0210381181e00075484221912141c0d00c5c1c5c0d11003030b41d05011103007280d80c2520b000e000b82c900785a0405054466250440c00c4980c0d00e001c0c40a0701e0009201c040340994201d0001400c200d4461141030480f060200115400c2d00140490000c5150074000d80e40a034101586031130409051500642c02940061790b03d40039885801c00080043c1d409019070308074a0321400010840c3c40070342000f032400081003004001445500010454006e602c120a40141c1003240f801207103a1110b800c080c0e402c0036105102030f11010304240c00340201038003e82c06641544034941c081220b40c49100040c0200c2e5861140d100014a8154601043d041c9a4110380c1d00380a41a8021044030303031070b0030300d240751200074411f480c424100c00040200b00d28001c2101a94a5000d0b100c5503200c042c8a80000d407507100c1c0410040402c5041c0b800c100c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 445868309 1250 445867059 445867067
    0xf0903120d06050a0509090c0108090c130b030c060f030a09061b020129180405010624140711040213030506090c0f030a02010806061c06031a060a2301 66
    0x303003004020380310580d2840115101c0300503181901680340180d040c40d100049606004071082d10a040500141802d03501c21030044917000405001c0781c415200d4020210304941d1142050840703080441000111410008240341c2846107061170148100000d000c0200480107440880c0c0d1722694010001480e01e02c00c1c50031400900c59135489000e89000b58080300346060301580420300d104407461210310715400d1055103100c09040e00c003449030428102046040d84128150300a60414070540021810325281c060014041e010799a11000c1300e000d1005404a5680202000c1c0c00c80c17480450003490181c49886541c001510030402e81e0080380e0000342c4c10001e10411108001841d40301c401c0d06c01c02d0800c81501c40e81c4524000e8940e20500c80300c900c0c1c02d50f80c58000743c1c181c1000e5040e1100601941c4400802c03e440d0007200d400c02c580200a240c1d0300042240d80300d00d0020b140300d60441001221000b00071a100c2e40020700347c9005220008080c007a5a4800c4403560f649800003104940d114442d4004031 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 445869559 1250 445868309 445868323
    0x1d0618010e0a080304050c12070b31030209090d02060105010c06021c0618090f0807140a0c03150203090a1101050c0a0b0402040c02070315090c05090703090b01090c050f0903 76
    0x1d05900804000404000d0881c0045002d58010360860b80055155020003541400881d5507100a0303014032001c020389040038004d0085001c9450344500044000480085400e404000c0107a0203108682c0910031441c100b100603822810580c020300e5100c0300100065a1404c0600902d410710100000c1c0701c0820280c0d8040700d55040c58022201d490300324580301e40000e4500350190b01040141c14010044404013071240710038143c2c124810244001107603e444100d607000400645d40700c0443c0700c0c81d81c5001c10030425280054400c5a0f40d4a0700307455030034010101c0c915509070204142c01041444009a00042c50351403540d000071501500140400040e54140305004880039075020b030100110601294241c01032056000fa1014044083c1c901022610b0f0203c90000502d40e1300c4d21000302c102d01083da07100420703c0384211900716035652500d002030410700f001c85040000030380b41d4402d542000301d65500b00d40101011802845a022030b414050400e01840e40c491a802c140401c0384403655030100709030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 445870809 1250 445869559 445869581
    0x904142b031d030c0c03010c0c05120a030e03040e04030e0603012d08070e151801030b0910090803160819022508040f0501050a17100302060a030606031d061801 70
    0x40c1d0743c6960034134005403540b43d0308058a11030752a0240e0074000a00420b07445088030350040244c41d074041d11214403401d40c0c0200a0140130075940300d45141040d1030802c0104040c207050320140441d45031510f001454151042012400f40c5014001002401e01d2404c8079684089605482c0581c460325102001081446034020602032091100c0011001c00c1c030b52080d03000c0c0340c528840d0080040850709106005404041c820b80c10010b040040001c1100b40c021981c01c48840c2c0103440340007400309440c000740c5402000a5a001d800001400100401501000c80340240c6d810030840511340000e40301e110301240c840d0b080c002c9800061100ca040500c80c2c0360104000d0840c4400c0c1d00a8250804a003203030000e02407600d2a1031020b40205503036000d0000d0b11100425580d4503010791100d80ca1a690300340d40a80500008000080084016990b203400f44c40705040958001030040d251545c01010384403201c0c0165180c001d84464009000b40c042013040d0b1004aa00f0925041017440d08458010030051a40c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 445872059 1250 445870809 445870813
    0xd02060307030603020109170c01140c01050c0307120b010f050f090d03050316031404060906020c1509010621031119050604030801150e0910050904142b031d 69
    0x42103072940d050351110042c2c070f00030303a604c1d20021303100da410312032200343c03482c0c0103110b40d00801e100b502d258410605150790700e003502401420600709141c018256241170b070b19115606400f01c00c00800035030142c003015140c11403141c1032045421103400603007031110b100350460820030002021100b502c074000440752008006072800156011904004010b030b00706458403007856082c24a43c20007140300307029051042c0907019620100d625030f603491000824840c0e504072181502400721352128070062110080481541d0403100f66450010122821101c03075402c06a602c840074040b614030301c88008100809654103090071451016100600c0340f41000e41e42d100346003081d28100c00c004200b000b1031014040c0d4400d4131070843d10307622003c0d6144081906e50700e03200080c2d0b1061550002d450401d124071f420042032200c0004184d00c2e000440e0180d00c0840d02034030401025410a12800000c024004000070b0b41c1c00d1020701000200d400f1204001d10501c01000c041e100e10b4641f0461400c1c1a0842c00c001c00c03401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 445873309 1250 445872059 445872061
    0x210b190c031e0b2e030e0a11010c0611120a0608160e0402060c0601090c18060e10030e031b0c0f21011d0c010206070f051b070807060c050d09050607030e0d020603 71
    0x103020504132014188400003820110000d8000b00700068020140d507200d060494510409401101c0c0020080c4e001c2e135007241c0f11070700c0500d030100311f600030152009180b45101183c900103410805035034031540300d001e269200300c0c0074400f10042a601e01381610040345021003282ca40b030000851074010506120003a00030308000054120007a48005459042a10b8100094002034041c600401c458444d00f00403a0075150b00940701c0c40d00642200001000c1d090001d60000400780c1c0a1854100e1400c2c01c0d00d0401140030400504400c00000c2e00020b02110103140c07829107000070800f11f00400b0401c0c4102030324018280000b090a4106414000030b030b0b000ca00300c8001c4922802d40d2031041e8641c10f070250007900045207500b48030f42105a8042001c1d01e40600c0c100043c2c0f003058a21503003045861441c0154040491845018066403000700040e54032409016801d0910074103004010150000344803031404100141d40360317107064841701500760410005116024000c00e0031100b015000035440b2070004 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 445874559 1250 445873309 445873369
    0xf09030102040b0315030304030c09181209060215013203030708091e091906030b070206070908010b0a170118050105190213210b190c031e0b 62
    0x50f40c42400d400000d4010340b41824240340d07c9114501010748003441522060210010030f070405030001c5940d00b0754031038902c8261a8000d00c11100103092000500e000010005264100035000c0c0808a860603412030b54504203001d42411040e5a400c00030402641a040b00c00f07900b8280400d00d98000ba041d6955001c0b6481d05901a9100d182e0f01407203090ae44400c10f404c1340035020b4034200e00c20058184110358880b515082d05580c19500074000c0c00d03032180700103c006a030240c904c0f4000c038202e400600d41400d0404010303182c0709480d0040b030143d80c5040c00040c007942d9005544c0342110380b14504c002ca480c0d000c03e209405840e501c0020801c1010f109510303010007c0c1580964810708040c1c0440d225140350500c00d20982c4140b500e00c405468021409010411110002c103070b541a01990400d8100c2c46503880030150f03201101c640b0144424a030914994420600850039100020315080141e040564941000a21070300c40700b00d62180e440340303044015150014142e0341e6880301400c00c40000e80340d03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 445875809 1250 445874559 445874579
    0x140d0212010e03190c051e0703020d0501020a08012102090703020c01020a020708161a090103021e0304061b051e0c030408160b090a060e010201091a1501090b040b0f0903010204 77
    0x5024018240b04c103030810780c0301451183e11221201c075407020142c025031030411034218a03542c3e01c600c40380a5014041000005a850340104509a03106800241e1140e91f141c5018148a405a01400c90440e070140385c9401c0384a19540240300a030304680c10002d5842c1c1d900210000d00a24000e48801e40c4002800300101d900000d8140880d0b11704030849040c2200001c041c0041f901c1031003030455400c4508800d001c00c107034940290100c084185401400d0190704088030881104129500445201c004140f0052004c0b90240309060440c100076040f41400744400100f040c810141168071201000082c81d000d0030800045403400041d503000c417511142c44104203603e403100c85c0f0480c0c07650602440c000076038a040d2030030b851089800a050b4040c6da8a8000159181e035000c100c1c1504556881c0c80b004d00040701d039400e614039050344484902031072800c14081050b6100c0c0c0070703086043c49020b0b10104448084542101c0c16602400022611550800c07508000781c0241900a90f143d400410041100448 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 445877059 1250 445875809 445875817
    0x405120a06050a0c020d200303100801050f04021e031609141503030a08040c2102010f0e0a1202030a020d05151e060904080c07060e040c09140d0212010e03 68
    0x58000b0402921500b504604503803000c002003015821003441c480f090b40c0142140d1122400940288800702d0040c03040e5170071588206d41d9001402c82521040c071181d0002d1066a0707100040d50740c2c10b815421b040e00040c100c1d4102c60312101900e40703404107450746a00c0030700c120500c0034080d00481c112140c071500c000006c1d20032941307240e00b44e03108500020300d400f42c01d550744582a4400742c061840c003c8910802c03140001c2c002c0080da450200b28100180c02c0744e0600701e15011500c08900800400d50600c001441400c1d0f22040d101040f1114110b11165500d030f500c0001290b000582c0410084001d1010074103202a000c4065800b107010142c00e800e10002050910b20619172035210011a910b00e0b60500300900803840c03400c0c2d000c64000010340a4100b000500d40c0040c012a01ca40c102a4040000f614207501c80c0c10410025041c20728810550034a40950000c00c0300500b0600c6400d401c04803c0100c140c42c109680f80700d002c5080b144811741d11500801c100c1030b404200240041d02a0030415030384d90744 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 445878309 1250 445877059 445877063
    0x15040b01140d02210a0903090504140a0e01060305190203010b06120a0507030b0402191202070b06100c020604060c05070608090607030e03092206120c06050c030405120a 74
    0x1050411a51240d842525000c0c20003442258003410032512111280003900078030248010015040032001d5200e00200d0054400c21004002103181002c500c5d0040c10000a030384100e000f203040c83c0e8900140d0080b03c146951108141c076000500c81700c002040c1e40502516031001d0518001e2851071800c01c4941079800b080c00340242c1c020300070b070321005050140070300c60303001001c14641c07024002c0390044050f50001e58001395145404511508400f00007800c07030b070041c04071030307003101c48072110901503504072030001401c1c24074160450420000e510381103039890000706410300c50b44403001000305a0b80101c001c040c101c3e03006401503844688845000e000a49441d6065801d48a00000060340c030b4440e420243c8104103450141100d515100c2040e000b401840f0b0003419180028044d002031511400605201c2482c03048a030001c0520b00101001162410340007040303641c00501c00c07003002c10b80b4100e002086038064900103680722083c0300218150300464200a03401009005084141540080c180301024 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 445879559 1250 445878309 445878311
    0x16060c2307060e03160b07020c090a0504050c04060503030a0c020307170a05010e160e06030a052406030a05070b0a0311071a06041b0507030c05010c0816020a02060f0306181504 77
    0x61500f59035075034022010b0304c18030141290041c00014500e0010103401000e6030046500c0e0340002320000f00c2120040310082c040300d617282c00300018003008004c0503e44103401c0e1820841107040c1404a6164410260402c003840078184590045444c00c10988005002d01c40c4d80104e04500100540d44030400104140c03815820204000540400842d0303410710000e10203000044645088481c80403104003c02d8141d00d809480000c50210764244983c041148004040409a001503141c3e011100d42c060181402a40b01c8540c0e10002080020b0042c11398804003c41612800c80d200c00328041c014103c482d90344005c002c10341908022a105400e0202403c1890020340c50313172440188812101100740c003003c4442040d0035841464044d01c014101c480c0a0302e0300c05100009900c900313007235450005241c40000e40c140c0c00c0080e50007820b00080c6282c04680302508540440ba00050050f000704551302426050000c045078080d90703950344114030559040140c03000c6183c109140c00c08840f426a100d4021 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 445880809 1250 445879559 445879571
    0xf0509030a0c061236021302090307081f02090d14010b0907170c0d090204050f060307050d0c1e211415160203090a0f09060b16060c230706 61
    0x10b0602c500644c803a002103543d940c107510803c41c0b00044d000301c5c55101ca00040313401c41c03421030140e25541d8102502454600f000340e602c41514040c10b03d020141e82c40321415401203e04e56a00010301d04080400b4801e0b02c4000d62a42200000100a004914801008100c03c0a100300c100501034100c1111001c0466424125980b40e400c15142c40781b06117410142c8940313600c0007030b40c1c2640000150100e40c1c0320907c0020555100d40c003080460394151411103442016104103c2d103450100024030252500ba5084101420680c6c1c0c0c802c02d800ea240214000402d400c00c0d803500018a0034008030060500f1941c6904030028004c2e205984c1001000540d07030101060141004401c00041c2d26400c0841d02e480064143e40b0540441c0c00300b191a841d100c11800100500c4219654059240f07010b0100c108130141001d24185002044640c2c0d42c3c0f00e00302a420510800764406112015181301941101011a5030360a03400e007100d880009100c0031040720030380d0b0b03010941510000007408903507200d01410401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 445882059 1250 445880809 445880837
    0x140706051909020d0f03030f1109090105030c010804060506190b0901020f0706091a04030206030103032123071101020313020406080109050304030312020d0f0f0c17070f0509030a0c06 80
    0x1602c0c0d410401a42103c509940c00000a11700316142512501900d4001551400e50b0940011f5941000301d4954a100204128180c0d1400d8bd503003500601c402c0700145200c045000000c1d100d03880041024160554600000302e440d140d00000c0040503d07002c0b45c00710700c039840e50388074440f07030304000d059074014820b50300a000c819400048001c00d0b50748580b585007289141c28a41507610540c1d0321103071043c107001d01c40000107860754805903002c1d52190300c85040d0400340c010038003e00035100c0354202001e4100194031400c2c449100c03a0b42607501d512181705441d542c4404094030030b40f422944001c01c641c400002c0140225801c40c0c2604458821070f800c9c80350a6560110909070f444035013001c3e14a4208000c2040080e001c1c01880c444000101000340c00c000300320250204603401030089400c0b0a84514038845e800300244120891800c0314144203030943c1d00702968450441000300a1014130084080304107034580140c081d00d0b40d030640242154451001442c0c1b02e44032050034880c1c803010230315010403144 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 445883309 1250 445882059 445882061
    0xc061e0f0c03180c120f060a1505060901020c03060103050c0f040515012604150b0d050a12020a0c080f0f070e162718060b0711011407060519 62
    0x8007072070400840a085440c2c031999840718201c1043c00104a02c00c2d410120041d494403000e55001e814040091314040e102030b041b040c1480002807400701c406d890211003400020003d18000142c2d007050b02d65036115000603005030302d44070400030016814840d02000004004000900e0506039200340c40d0b04044030b001c481400f0641c0c1c4c0540340e10000d15405016480340e5407140541403941600031207000424059019503403001002520103844910710804030810078115401400701d030020a9451860b09013035510f400ea2641c2c406000100315424099041d02c0240c420000350340115002408041c40359a00c0c03080341c3d41c407100c01c8594441070048029041d290b03a000b0074001c0c12106400c00c0c0d03400c0c655520251a0510240c0310302d01d414030010801102c449002c0d100340c0007100d560f14a0a458440c1840c41511990303012081d0354507494180141482550005010b980b030343d039807290324489040c6a034001070300c0810011811103d42407001c0791603810f000383d0303800140c018108201030761502c2504078681c0c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 445884559 1250 445883309 445883311
    0x110301020f04051005040e09060a05220f060209060a0333030f0c030b072609030d0e0a051c0801050301051006050c07051f030506030727020c061e0f 65
    0x50740c10103090104100a040c503a544100c010711901e00301d85419111140d29400120980b01c0c401154880b804210708400c403442600d030404c000074120700c14480c031a4a802c440020303003038008100c0d8980c0d0120004101444c0c055a01090004200d2030309c50b4046140200141020a4400301c034402142507030121074001041c20210350402128038040b03070b0860300c901008482c0000115101ca20001e800404256028680b602940d616511079145400700240820050400071103804455500c905102200c8400011a100301040c60001f01e9a40a0902958100b000101000d046800f521440b03120b0321152540c1d00d2040050340e12100d4861b42c9600906088072000c8544507402d09126400b808590b0180c006400e4100c1c0f035008403034880780c41b040032407a403124600c40c0c2c0c3c07405070707420b49000c0203950036010f0131354049001d070018056149005d82407a0aa002070911900000b00c40216001c040510b0f01110071407060704044071101e00300f0740d03146c08a12407c64440042c1c00d012502040c020014000f1403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 445885809 1250 445884559 445884577
    0x21f02030105060702120f0709050601080702150106260a0203060a120201021513060c050a091e09020c070906031a010909022b0f0b070f0f0f0c080409050a0911030102 73
    0x541005115030911500d0400702c6c103410064424a418041c28010030418100680b026000c08900c42c20000005001810098100d6041d9041130000d801606014a030031070440710390745407120078154006083c147c50552451881805500c1c40300300044d1948640041d400744c0c0b015a84010a15a2004046a416040f00000b40180c00c4500d00c410780202c0940c4c125001908119403110081075982c0700c60445004c20b0082012401c00f1034010882500305210318000c080040200440040c0429a103100312100c0c040c2481107940800c0c88500f140041010001078100b4507000c000242e02c9062010044c0b00d10310000042401b07410010526501758040c4580065000c1c00d1801504140c100c4601006401054180a906941e00035030218054949043c680c1d8000c441500c0d05044c1500010520001c2d181304100344280e450006903604c0e1f1103d043c1003220110b2400c910001d51901c0d02da0703128845d42e0311403148a4201800e10910007500d50041040c0c1d482044c80083c4450b0620900d4240e011703038015 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 445887059 1250 445885809 445885819
    0x141201080f240601122306040e1b19150207090f0c0206040b150d03030212090f100509010b061c2403060209042a022514130c021f02030105 61
    0x2044695005054500c81482c2045005ca00700405200b0003032070901b041c0d030350006940408248441c3d4141441150404103c2e840034045410030903041c13641040e106007009000394070190130303c0c0751061040c3ca1a000b900300455002011100c2c05802590381040380503901c561071070f020204281c42810b105480c41e4a441c0c1d005000d030f03551691036004581c600188450080c038814104803045588280112031111303c2030f10010388521416030b1400002c4001404842d40340d0107144500840310b03002403440030301000c560011443e5a601c4425901400150f10003940100d8007061071808401c040750050300d010035a00d020410540f02144944039502c5c00c0d400c0c185d246100c507070180042685074004060048028001107843c1d82d02191103401900c1621101d0f410b914411481c0b403a10754148009a0700040d96030700340e00782001002c00034410718130602c18810f09000001d4450075136100c0703000d841500c1088490412009000440c0a9103844040203907010580050140041c855442d1080c1c134107031240504 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 445888309 1250 445887059 445887061
    0xd090909032718020a080f070504030b092b03140f01121406010303030912091505030403021e100b030319050702010c0b160e0d0201020a03141201080f24 67
    0x2d402c000300341e500440310916403248004652070104540e0302c0740c00b102e4408016510440c0b003800402d003a501030003040242c0ba01c3c0f000d0265491b4400c00759000e41c0d0b046495140319440b140502d52400d4103851180c11040314840b155180c80500001d00d0410181c00e0f141801000303124801c0c6140e00100300c421b1814159100014041019900c0701c0a040c41c0c4070300120080f2801c1018420312b046026031003180020b4030f0341c45031070400007400c90ac00820003481c14801d60640c108540c100ca8103044101c01c81c2000008000103013030520030840403004c0f1100c400b00c3c44604000904035038603003054184c1210509d04044441c0d885080002c02c5426100c103400580031000010b400c100e50b1a400020f06a042080d007409881c00301d00e501880320300909045c000446c08210058000d8802c013074030704540c1e21610090584001503600407c0c3d1090b00c81c5d041c5040881d002c141c0c0810b08640c0944450062040742c0500003007903607000041c0b80b58514030322904480c0e88881519650541c00c8091200241a8040d88 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 445889559 1250 445888309 445888337
    0x6040305030903070611090f010503090d0c15050a0e0f070803092812151802190801110409140601120c02070314030a14040b090607060b040501080d09090903 69
    0x140a5500801d02c2d070b0a4a1404c04c0f1030311554162011035506403043c1000003802a030501c0c1101400310f040c102800d00e0303406c41c582000b140d42c03284c400803142014450051040d40070003190f92801c030342020740f40c80100000d040092030b8800401d00ba69403241d02d4421800860b502c034500185500444d802e00e00110314044040051010341c0107013810720812152030039429404440702d9000300c005418641600305440c40a400c0201001841a120220140c030b000000b070414040503001481554041e10582144001200c0c903400b00c43c601d9200700c025500c1c180744c000c80280b60f50001e00032529008070601159010407070702d28a1906c140d8040d800700c1d1600c0b8013040b684841d500044040500b90054030b054541ea42c480c001451318084083d891600006607080800750010100607a04204013100c501b01800d20420801c00d1103030302030071403203601f003c00d6080401419402c51084440041c00c03d02c01565948072860b81d89070001d402201080340307d58041200035080c41034500507501950f900701c650401d0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 445890809 1250 445889559 445889567
    0xb0306031209033a0e0a170a080a050706050f0609070f0309050307060203071707021002070c2412051027060b180103151a1605030405010818060403 65
    0x812a900c0c2c00d40940182c5420941010201d10180309813051994102843c000780c0440f00c245440c102e10a10600000d0001d803178541e903d0440a46d480400740f80b0302600743e504801d141c00c907080320042901d0030001c0c0c0154140d0f403090240c44a64403500c0c041c010b40e2200c10200b50805c0003214407540203900200000e0380b203849803c52032580301050400007090780140c0c40d842d09552110000b83c480a0300007041c411070503071003480100d00040410951401c0d013401c14000351509041e500541032079070046402020701051690041c01080411000859140380f0f41e90030402c4584e07005030f0008100c2c03080080320a92154000daa1003240c0c807841c501021401d01c94031f90580021422941d811411030015103640d50762034840d0f44040c00e404802c0d01d40b100c842400d40c55261a03400c8201d81010b0400d8045042e550506070340c0000d6400e010500f0702c01c0380c1d15000050f05400b030f00710510f0146101405020500102000801c00d403807080e82c0d040c00c59034032905c00c202120030100803820705500a00003c2d011902ca = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 445892059 1250 445890809 445890817
    0x60801080312100b0c03250506012603030108011b02030a0c17070b04151a090103081e0f0d0b1c14191a0604140c090102030f0f070204060b03060312 65
    0x244400500e00c00c1d2603021114654100c00c0b00340000f0ba0000418281f0740c6410188030411a41a9441141c40d444a81d05d81340c032510180304c0d4400030060850000d00d440014a04403101e0381132503007141d03142d60751160310754082d0a1408952140310707a100b503190815840030089030000300d0661144002c9008595800d01c1d448100d81000c0840c0000384451400110f001c8000c81c0543d00485040000b108402a1681199004420044070146140d01c87e5500d84403038502c1c40c1180e0308402140d03261228440504540c001100340d032000e1030000220192114000c00141031b1585000d9010041488044244101404800c0b61401c1d00703aa41d680794000a02003041d18038207280d05400755030b2144401c90001d900c1d404030620841e181c05507107440a00042822200300d501c900212414407004a00300804189030340c0140160240a0000907001c00c02e0b4020800c0741e200c02c0d080400c45513641c29041400600341c0118800f24452820014009042c0d041c00c4192030044c007009010344902c81c00040f00c4051540 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 445893309 1250 445892059 445892071
    0x3040e0c0c160914010503010b1507021f020708120906040905040201030603230f0105062b0209151e03070b090d05100209010f081b072316060801080312 67
    0x32802207250364400c1140181d0b00205044080881e101d4046503810030b04030016080b480c06685031094661456840000300d00c80c1e403211403892a96142c1500120b840d040d50050b05981c10036131300840b80d031603980c00600c1c10102c600d0790064456561168a140180d44907030740d00c1e554444018070090000d501c0c0e130350110390020b07c14100024026940d50341e91045442c000720310840100c0c410340a1070141380501808408108031030007081366107010b40c0042c2d0100e080d94101c15212140000300821407440c0421041e40030340007031030801c051801040805aa0f40b81026450056650259203580211036101c00c41030844010003915800d810b214031808982c019894290b80494050100c03070104034280300200c18030031110800742e59030401c14009040e204501d5200010803540000708810901113021802c0e0301d4110411103551a0183d0900c3c1040c0d80d501c440d4410b800802d41443c000031000080d080c041240400b004403100d81c0d13901d0b8240d40a080c24421416260010420800030852162150394811 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 445894559 1250 445893309 445893313
    0x301030209070318080d060e04171e0d05040201091707030b0712020f03092505040207020409050d0914060c060604020f160503120c0c0d0305040503091903060c0203040e0c0c 76
    0x31825003041900d8131a11505031501c41c400625080941c0c81e40c058107000d44620280c170022400e02e5500c007075000d4450030b8203184031034010a075012410b190030707040b4000d440e6400c805910781166501c0403000f04019039080303000c150f01000025008840942c4010921010f0002e810782a155841d08060001d0040c80c08040015602c460100f2815501c0074040300114100842c0d228a018079417180fa160b0305852030501c2c803002c490420750010384217100d20141c03241034a016803101c00b03501c0420041d0042c5203009000b80221000c8003207050380a0040d20484900712202c149420107802480356621824001500a40207100001c0c0750f420b040e001000c0c403910b010201c51914841c488c00800051207410129450b0b0800603400c0e001144290503031380c004080d55640c030b250403003084ca01c0341e60b02d80c80c05400d01071603200d10004040c02401d100f900c0710050058000404042a007044580f0f02c000390100f1900c40389040c1560481b940f0010940381690262244211180c4a4001c0c2030b24503000700c00320007054 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 445895809 1250 445894559 445894571
    0x80c011103030a1a060406180501020a02150f12010b030a050a0b0f01031e0509100e010b100305100306020d140c0313030c080c0d05090f090c18030a020307060c0b070c0803010302090703 81
    0x1905e0300f80050005001c159181e03050040c032a40c1e0080a0044daa0000c2d0466024420300350150752500b001403580d0015844103941c51b16400704800b06802240540d000c1500c22a0002070520307c8000114071418150008000a5039155044021070710312201c400d820280c07000d05048254000c6e803250741c4c0f140400c04a029800048401d0105440040300c10b10750719044090f83c003000c00918043d10003444c1080e40244800203440000c00c0c21605221450340815807200c01185400e200080040040d5070004e0066503181460072520b070280a01c0901074594520400002c1d43c2514410140ca008090b5140050481846038034101c6038500c41c110142c8450754204074050000200700304210700000280c13629611440b2480070840750104c1c000407503004400580801c1010603801d021606000c0b506801d1440080c0c5a5000c80c0c41c10f032103200000d400d0310801030041030294114542c600d2442c4039892624413580d505000711007081c1c00c02c070010000c0100b80018001842d240501c1c81c4e011281b4900020f507 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 445897059 1250 445895809 445895861
    0x9071b0c090e0c0a06021911010c1703070f0309080a08061804050c0a06030e06180c09010305060a151406160501091b060504050306010b0708090613080c011103030a 72
    0x1142d014200b031640c1c07a800403603000d40b142460540f98008010f14009448030605041200001c03001105c0d0040440b1848014014035a00031000c01d50965000b00110b2501d42500c0703100040ca60040c0c421001180f0a031825004180c8030f40174040c0056409404182400c1d9444415140e02c4409131103203034414022081d503160340e203540301524840d034054401040c3d940d032880148104c407041c641020b0105400e00d0350342095024005000e541020360004400d46c0e20b81080d882c10304042e880442d080c0d221041c02c0002040c4800015054042e15000c0410440c0420007400b0f41e485034440d00c2103221048401140c0c40082c9001c0000c2c003d8201946828000a42155656401c4425209049a0403030a48440301201c5241d0601c00740680054208240b429082500295440405106020200340c000680e0070401400d030b800e40d50352035009000d0700d4079806525045501642c00340617040c5184640d081d03100466114030b000030109181880990310355259100d0309000341030a00c4200700781030340141201c15 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 445898309 1250 445897059 445897061
    0x70f0611070609020a090b01050306010c020f1003020408011508070303140d0513120206070c0f0501020d0c20030a12050901060302150c060612060106050c0709060902070201080609071b0c09 83
    0x3201c14401c1c000020001e0941c4100606140795411424a945c6000362a545598010044076084242400c0030a804071503880026052001040030a40240c2d5014005480301d0b0142c0241c810740340820000d0003d00c0031728039a0145080e061203500c2190340304190400110b40180c0400c0c8011001030340c068504501d103645031085e108240e58099180324850820001c1c07103800d40e08a040c412079403000d441c03a810700f403c00034007a403000c08010381040f032040c82404c1080801d41c1124552034060b002882150740400014240800504c50403010701c0c582c0300014500c01000c42126824009510380040c400d49149010f00108001000e0621540daa20400b001507520707200c0c0d01c00380c4040358950380c0c0d45d0700301500400e0611902030400e0b805212540301840009034040303201419180180b070016140c00407001d06d10300d0583c0d25400104c02c64504600400c400b216900200f090324000c0e21810b0319a107030351040c084e0b03081c01155060006003604039408228141d603558850300d580506540755841d0f0b15088075030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 445899559 1250 445898309 445898317
    0x1203141608011a0f3c0d0c170106180f0312051c05160e090f0c07082209051510030b1203030a0b0909151302010314090703110a05010203070f0611 64
    0x1240e41e0400f4107a007040003c440f0004015016044480805c0c0405210600050700881c1100c0d141213850300340c1e090501c1e10404582280c00d4034540d894441d56920440509041000f6540740c071040007003200800c0758a511600481280c0d806400c49500c0e56030004101c2e030b40d4101c1c0044c2c5180c0d090412603559842814007516001d20f00400c0c0c907015003680c030a0003501444e010b0681500941d03032034080201015603906140d40c0b101c1061240396a038022882d201c0994440d80302c138103840c4407440d0a000500103980707030320340180d034002c92040003643c49030b48001d420054029103041c2e00c01718000781c00200300d101750890503a00340c01400421103d1448100745040d5042116130782c0265a542503010028039207805103c4d0000d2001e8040c10306584520b44005201100130300801c80c41d448411100e086902c40c0c0d0020040900c04410b115860502c000c40c503866000700e01c03055528856032031400f0003914113005a5011200140c0065151442d25507400c0da80f101203800c1655000c0d510f040c50340c4031602e090010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 445900809 1250 445899559 445899577
    0x30c030e0d06060602060703140c070c03020a090204080d0c050c0111011d0610060c1a0903162103060501050426030a18060c0b221203141608011a0f 65
    0x45629804c021000b40f80401c011b00032400c150402503044a040f4240c0d42003034118002030f102c559106210704240d01d00d5201a1320094020300c1b011400203044010342e016105403071011083d00d1803510740801c1100d1038a0340796000740c20ba410000303032081d2540c000c07500c0c4044041400c0c000300384c4c0c01d040d40080c081d03880111603241e0707590040410003444071040e0001c8805044c01c1c2c146810003222540722424400c002882400f1840680c1010602003001001a52120541351035032111900b4141b030807a11184140802c1c84130503d040c01c4110340c0b14040d001c1c0c0b405a4006075182d50516241014800a40c0500807118210000f41e52035411040d00a000402a0541980f9500002d642010b076440440c0d8040d0b000208124481d03190340e00207a84072074103035004440c44880da0500480521116030210154070002c240f84c1c0d00f003c6002c0001e0705600031880140c9650700d1720302c2c2c550350843d07020000ae8004400034001003801005014175901d990503250343c035604900e464107058940b204024076038484545 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 445902059 1250 445900809 445900811
    0x20304210e03100c05040605070303020c0d1706040903081b07200102100e0c10030e01090b01080d0203040e22080307030203011a16020f030309060d020307080105010c0c03030c030e0d06 81
    0x78000181020012045564070105080140040c0c507080104a4007450080204101d0002414001e062203034054902d81032030102914840c02010074050001c1d0b0004458480d240307000400030f211864244038602c1515015140d543c01c0341c1c0c1d000700083c00c0780c00e800141504100c0c244088030100320090a0712500540300e80c110143c000e4680b00282c540000c0c0507120300840c0c01c00305105040e00011420850b03c0000341c80180201d6240e003820f4001d012454600807032903103411840401c1c0320191200c54100d0300c054055079000d6000c0b00c000c90b04c0b403049001c1c90920705161070114003201d0a0480700c9003944200803c1040e011002c0d5181051b540c0181d0320710001a4022005014801c0c001003400803044c0d40c0c10910b8a402c0301c03022440d00d00140c01300085e11401d60b1a100d007003662000d000f1501c103c0c00061001d07503203484151160009400a0f1382c010300141c0e620b000800c065028049248280e604480b2030303074a00f0715540e000c4404400441c011030420844000080e113a403100205007102d244030700f03c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 445903309 1250 445902059 445902077
    0x3081204050c031b0f01210518032a011b120516020d0f02070f08100f060e01090906110c0a030f0206130b0c040503150109060f14010302030421 63
    0x705680340c41c40c01210588650010050a030904c02019401c1c040400b094030305544130211a401070f01e50b074820b107200480414811041c038020b0040c5a021038420080351242d80a1000c051a05907074038021002104007041d49003c180245894840c140d00c1c80102240011551149000300307010300d00c10705800a0040b81c0310000c0c0241c07040c6103000d415403101d0740030000010890400802507481c17540d0b003280c90074010b818034940ca00620a0241e400a01609000701e10490740d2200c40c2d0369a80c64100c000ca140524040d603160101020b80690320480751205076404d403603420f000f03500d0024400440f00320342a9603108500500b40d0710140c01340c440d80e0100030140844010034100909090003100101e070440d0040010885010b07007141e103a008194000449810782d030b03100c0c41079000034404e0360002e80d0b00d40b04803405126582d5080000c281070340c103881000c0c0449a40c44000e030080001500502c02c1242204c41e12403901d51080d40510307400350040800e02c17071010386002c842c3c15034088140302e4000185211 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 445904559 1250 445903309 445903313
    0x50d0b01061101200a090f080d12050c0702060f190305090c030c09220b1003050f0a051005060d060e16060c050304170715020106090e1c05090a03081204 67
    0x91115420b5005480080c0940c030400e08406008060201030010000004a4000307035244c85003c69101a198985800041340c1c0c4a60b201c65480100383e80e14400a050f0154083c8034036060701480d0700030340452400504140c1d4030341c00c01215800c00412044002002d0020900002520080c1c0c80c0344d14031920300140302d0402c05030490800c410191428001d6210351507100c42e07a111003a016500202590810400d079403001c1043c1601071350407102030403440b581030a02030140001c070254030880c0d206008903000103007942140c540f1102242d102405d6901710301ca82800091071038000541c0040d0003080140050b07055034841e81150340502c03015480e0352080801082c10702d101d2401c40f002d0103890804960220441d0f4407a6034074400c41c0640f2000c080600d0780c2c500d503201e04006e010301030314480088824030140032000074001e020310702ca8401c045003094108030700a140401c01d4000040313000091000348109060030707145680500c81168000070743c83c1c0300101203180b52010780f515124004840c2c0032070a1138 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 445905809 1250 445904559 445904567
    0xc020114031911031005090c0c0714030706021f020724090b15060f0714100b030c150a1d0a06020f010b060309070e0703110c06070206010b0301061b0507050d0b0106 72
    0xfa40c50744940c0ca2003082440940f000d10100d10007141d00c11101d1176107907606d01d00034001034050130480303000c032348150007021400c06124964401099410b5048a2905a03511412a07441a025143e00c601a611004c002c08942c01d40d00208134071400b400314000f1940d030884810700d4030505108011001592180202d0800c40c1d9071603529044113100b14144e03003165020b4009042845242c244200307131140014203400700216540c90008058a0905031507402c141001400003400c0c541c0308040c4240295501c0c0045458009038a200903000c5400041c145050b0b500c00b0b96540000403100c80411402e8007540440799500c80c4444050f204507030260540c00005010036007174841d003001d018480c240c02e20810802041c0014241c0468070300d55618411602ca12405074001c111701c001c0c48128140c00101c5034180701001076400c0c040c0d6456070032070f10701e84e0380c4082d0304020340003c0c01094006680c01e070b400c1d03c10bd5000036000721203500900941d000b4036510000518502d001c1c05089840307d03c46070040120a0304 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 445907059 1250 445905809 445905821
    0x8040f06021614010c0921060609050c130f031106160b010f1806030812070e0d080315101d0f030328031505060d09060507092c070c0201140319 63
    0x150700b40541b0302c03801d200c0508442a1500c2c01c0040b00e55a072280035091050035000340c0c000741503c1804202e1170500d8829070308640c0c4490120354a0300000074000506842041e5540222a04001e160180148000811646500c0414500f8150941c00c03104004260403070502030007010100341c10003601d4502079084450180402c02d900c110b9181100c1000485c9045085408500b503c0c00c50381030b1a52012819903180504086c40c40c0c10500908a010802610800860042e10740c4036424240d00344d0003042211842c11407940c1c0c0c0003e14803900b64000000a8400080e01007001051b042c5100e030030b00b000c0791854000101e00403150b2201304860398102c01c0c3d0907840785400240d28080c8000c0240f1074000b54010700901c10359000b544001400d5080e9072080d484a610942d00920030700c01800d010b40001d1420055001c1c240031440401e08160344044a25201d1038001c11000d83d1001590b01c50a0641c0d2204551001360b0610002500728055013003040021486190704450540300d0766000c2a40b1811105 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 445908309 1250 445907059 445907081
    0x7060206150a0e070f120c0c03140304151a15040e130302060114040f0212010302011808060402090c0c0303040c0f050d0510050a0b0604140f09010608040f0602161401 73
    0x84604014042403c0410072642e0044e5181401040215480403c42e1101498103030342040628100429100325807004000078060b00a6441c0c910114810f8080c20b12403200382c1c0e000302460039950000303c0115042d0411903464500c0c9505295029181011901503400c007142140101c100080a004040c108658240c001d011000c0b050455102c90b600a903541c407040c0a00c108081442880c91442c2d50780b80c00400c0803070701122003517407609000d1001c1c825514003800100d001c01e0400c0d2208051100303948000b02281d110724000c26190703d0700c0e001c0c0711031000042c1030700240740f10130400a5940602080214000d900c903080680e4454501f110307011003048140c102510580d1403602000c0030ee4400038580c0c070405001c0c0c07400203581c1c0304c05e44c100001f801441c0903250040303004500081da05004910844904e00d0079114505140064010030101c01024001c907004030356580c010801240707807641c004800314030030500140b80400c641140d00c00481c1e11041112506a040e161310700303003c020700402131b0b541 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 445909559 1250 445908309 445908319
    0x7030203010e0f060d21020d050c12090d0606030c180203070827060106020c01021c020d1d18070318120e0120031314030706030207020409050706020615 67
    0x250604800b280c2c40d034005014035214504410210341c4d259221111038401503800403880d0550000310f000e441403040d11484000150107441e44544640d030140c011990720080510144c6001180841231000c107400510705a500226501e07071400016101d8403031032018501403418112a0b500c1c000300c52440c80303143d9100260380c9006005000b07a00f500121040e42101201155032006c000711075603c0c82c1b80c2e0700301d000303003107148260000060032640228041d032017800c0070303170a5a054080e12050180015079894042c0d005900c60f000481e0840e01c9064082541c502c080c8140500c3c0044600140d0540c020000c400c10504211041c4140580c0511031442c80b8160b43c4c100440c0400c0d1900c5081c0e00c40e00c1503410340305100180c0001460b9070f10500c552011180c00286981031002680d030305582e2504540301c1d02101141404001caa003e80c0000080a07940c0010014401141805c101b10065080b0207000c03a0002d0300c0d200410b00184060000740d004d010240e00400c000c0c0740c03102c24080145001002a8052 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 445910809 1250 445909559 445909561
    0x20d02032a0703120216020d14011112010b0a020f0715270e070c080313030e0909071806050904201002100c090e15041109010503060d05010e010f05090607030203 71
    0x80d42050341c955800211384030068403241010042c82400c2400b001c000d5020215600c450200150041e00d440c4000412008001d0511a074440c00d450f0711411010341c12414084004101180700c000c010640c032500b80c4181e030040311641074454070303103030b4660400c00700c01d02808030500e20301e0380c060a1115402014074110243e812014520f01987d2a40c0c01041000781c01000004e0440e4002c1e0001c500480e4003500541c2d0783d28203860084100e07404000100d00040e26107140c0c0402c0d140c00c0c03801d58020210f220207032403264902030b84120b001098185440340c0230f8a4482c00582c60b6100310205108a000e404501b1031a18000704191107070540c01501c0c0d12a00c18a80340b0360006034005415800c48a46a03130020301802680c0c410b0300c4020383c5500500c01140c04000300301342070400c0d00c01c00002c1002035401303000b01e00080b0446d03030031400346011340382c0058028000603542c2d2900941e0114010301030000080c2d0600e01403200f0f4203542c400c290644100c0d40b01e4050000c00030b400c20072070364170803250b203070031415 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 445912059 1250 445910809 445910813
    0x1506280503040f031d12070302031c300204090209011206080307061814030408010c0305040b04030509040f1b12090305030f1f1403160e070c06020d02032a07 69
    0x4040d00c20700c000e000c1190301c5051401404246a02c00640480141400c480c1146e82d1803081d036405075400224041d00482a01101c03251940d40d403505106003584488030050038a40c19400f0340c240070442e034160b094082102c5c0d1030100700b40c801003000d00130310600503994500500c005401c0d185482e01c0c03155143d20b4000d0070840f00d403020003902d040c0c0341d00a00103c7c1e600d8134600ca403000915414409014000500707000d85041500000610464502000a0040030b0760300c0820741c03c464003268058000c00184000500007031169001b8400f130a001000040d40480c800c00d0001111100c20000761030b40385030780d550b9407055002010512000c004550074440000281d80013080707070201614400340c015011b004170703e075001040c07403510998146400c10204955101141c09048840c119146d0180c040c1a200e0080c10ba00c20700004191542e299141c0c8294880c048121072025040780c040d91400e40c01d0001e000c24490a000450180c0c05519403100660300c1120005624011f0080b065000300040040c880 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 445913309 1250 445912059 445912073
    0x90f030d110409110408060f040c03030f110d031e021c1e050a0c260c030c09091e180706120e2b09031505150628050304 53
    0x20308100300d140201d6007107081240100580100d0304048056820603e501510032031080107041190f04207011940191107800500100240c241c401a141c90000303030040c0042800303624402c1c8000194074068503135688002056052011907150680040c0d03d642546452144400d0300c0a110218101d0440c07500d8a0350400900c21089043c02d12076081d10740d41c0400714450200d1344035034100c02c03401c8240581d14040c00143d00800210020002040d5502d41599007242c1980350710381041580b4101c45413503100c18440360600c0d00010300600c141e500410040c070198884442c810300030703814480c03c04210074007411600c2600ca00103285030305400c0b080c01042407400c3c0003c3c600e401c0303c0ca0313428150200410024010042e103429440c0106511030440d4403282001c2d00d4800c10030403299503d613000d008002e400211408511403001414600301c0b001e2140341041da40d84519041994034406c0c8d584d0b40001c9000c2840380d0005810b0711000318005204000c200d0a0384600c1c2c03940e200514042d0300e146410764500c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 445914559 1250 445913309 445913317
    0x20f0c09090a0209010902030a05070e010509130608030c01050603010e0d0c08160605091f0b0f150706060e040501060501030b09010e040c0b04082803080414120d0c08090f03 76
    0x9100d05000004281e09600c148220448550054241070f083e68440304880b01070340c010741e05a16035901e0100014a803501c90640c1c1400104169209454001e01e4001c0004210010f01803c4c1c01507900e80303000801400403c0105841c56400300007048500d885002c05003110745401020f413130b0303800c004000107041e41d1012105002990080101ea101c1e4503170300301c2442a40581000810003481d2009014215400107459899900c2001111a0040d0f01c0c0a420042d20300001c082e607008498100c131110949400c2513100c2e02c0c00b80d0852218205072043e241d03902a103805a000024400d914400c2c801488020b0040c3d030702070442801e050003003245281c04900415014810381a0740d400c2900850100011290102c008040000303941d80c4907602c840e00241c4134030b02660f031402110b41091700c6030601c3c030320305040980c25a01a100d00e00f040c0d50781d8844090410b020580c101c84ca018443d0300b4170303840e15014082c001031000c00000280c4044c031004044d000c46c00240c1488040e6014000310560004000112 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 445915809 1250 445914559 445914583
    0x19030e0a030c0e070201020d090c030209090d1407051207030309410a0c2711070212030d1401030b132d1a040b07090602370501051501020f 61
    0x4043c41d6807a10303030490080c000d0180450081d8140183c0c002405480c000c5c12003030b04e0080340c4290980d22050030b12070b80c0d061503007802004114160200b800008514015088003406071044d01c81404134135604003031542c808101140480d80c3c03070100e082030124505070580c0201b410007034900d501e1201d503001c0b1400c24016244188005040842c400d007040c0030301c120302200d540440d038191606d0700c400c51701c1c81c4603031594100c001d0502e1491240e5240915401003907080d903008480130345400d8082d003c3c0a50741915042035802072004001340c0f01036442521407440b275840107444003842d550540c50481d191140c05401c0300b204004000161001c02c0440c070205441d1230504914400b0090203450a048124400b400504114074500b1441c030a10202010548220710600c03940802c1d68a20200390b80102481c010000180d01c5502c1504520310b80500c0a140700c850024003a400d2031280c8400c2c50040c8100b24211420b03510b8002340311080c116102103101c400c009002030410071248072031560b0350b00740d01c20003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 445917059 1250 445915809 445915829
    0x1804060209010e120706080c0a081b0f0309060702160b0306120f1504060608010905030307050a12092004060b07150209030a0b0106082d090c0319030e0a030c 69
    0x7070360384140c0c080e2403810250f07200903083c51500c0c44124002134591400d40300701c601203000c40740040d041c01350010803035240c40c065442da001191140701440b07502c501e01301000c0f0103d207401c2200c5074100c0d420301d000c0c5200301c8411004060500d4440d40080c01c100004902c00f4249400c46002d1200318015010b03680e01600c10b44040c40d84121404589190000d010301043d05401580c0308005000850286184030b0343c041d95040c04115a074a0301182250072a42010345103070800e04c0070030600c0d03205000802e110340c481d141142c54402c042c1ca005085030359840040343d09006044402d04002402d614000c002e130b508980c100490391520079504641e2003041d02c002c18500c1c0c8501d945141060590690f801c04002030101d403002c2d030300f91620b00b004400030300074400070170b52600014000b5002131540d10f15140900c082c0401404610103450b00000c80a0841681400f660940b10310a890400c10400c0308640012085040b103091706001e8040d0ba08507001502402a0700e07800c0c4007003015111903108440091725 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 445918309 1250 445917059 445917067
    0x70218070f090f17150108240903040519090c26070807050703020109290c09180403110f0d110105040c0b07030909090b04060c0203031927080d050618040602 69
    0x110003810550000d8170a006100d009001082403003001440c0c2c4e024400d400b4004034101e030a0500d820322564110741c6005136038000c0105000900b8496141144118015a03a003d039076200c03420ac5081d07460011581c0d0008141c800c04941d4190b243c404844880c0409030ba40005080110005041f004010f002e0820301000107000020503201350301801c4010b800410440002c03001d010700ca241b8030f8940c02c84440024107003011680c050031810803290707a14401885603140d40c8084051042081e0300801c2036050044801c0403034551a402e00040c0284207047c0301138180b07900d4585000d001c001e01d410640c1016850281000300107082c42000d417095a4000c8001313511180e803481c0488086556801c01114035080ca84040c0800400300e590900480c49403105011921101c94100c0e40c1e030004480b00c4204d5a519040140340030310720f9000606200c043d401d12564140580c0788d117504010110406c460307400c2c0024035191003842071303c100c64001c40101c68213400c95681d0689502c940b4000780000e17003203076030010f = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 445919559 1250 445918309 445918349
    0x108070c080f04030b0f0103050d021f0f02090603090d110705010806120309100306030507050d031715030a0c0e0c03040807030f1e03050603010c05130b030c070218070f090f 76
    0x101680d005580c081121401c81c40d0440740c00d41c1c000702c01c0c44100c449102ea84ae40a10b418004a200d2482d49240138061560811417599400506400855514600e500308410318050315618029846101d0b80c000030030083e9171428005206d441e801036044901d802c40101800709a0b404560960480011190b8140f030b0030310316a072941144100c11001e40c0c442410540b810046426030014411a030160301556401d03031741d46080c020311003a142c200a00103015007201140340c01d50327001c81e00c0c0c108840690300c1c54140d9100c400b0900d0051180c0c001c0d42d400300501c0e030030800d0441403030809030302900e0710a0950a50400359182ca0050045680003028807448103c4032480510a00303405112411120401b2180e51902e0000380040c03505a43d064065400c001c8081036950003003007129085072903c94260301381841e02007100080e40004d4646c0d2000c1c4000c00204000d031765510354041507620280c0740c070b10040c105400041c0c07104002240e00340074800c072001c08001c0300c51005805411141a5800c0f040d505a0f64 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 445920809 1250 445919559 445919587
    0x171006140421060f0605010806060d060801060f0302040506150306130b100f080f060616050a02060705032106030a03031a04110a1815030c1803050604060b0108070c08 73
    0x20750030610341c0e40003500d021071a19201e04022202d2078021a030030001d82c50100648002c1c0e41c0b45000c0e1031f020805000106410342403c00041400011403500000c8850310f4010345400e464090b440707101883d10440090080d80340c1441005d0304000c0444075100922030980504045000080c0724a1082c541490000030001c2130383c10034440b490004220301c1a14040c40320103011004517201c5040000c01c41000601c1c8141e0f030000e000e001d158020409814004030003960030b1500003410084035039001d5a852507006803181d80140c98003902c107001641c0c40360210f618000200403030a40c51500c80188005000c0e02e0b48001c255685640c5e010f240106004c03001621000800d0a4140f017250003c0c44c007107461000b58500d00242c6a5124140e44200e14281d40008855842c4c20b80c0c062400050714140d40702c2c00d1a07019912414500700c082c01d1400384c417010f41e09850110103060b071003078a082c4c001c0e004000810078141700e00403080c14242030605060501100040200d526124018840030b40002e401c5105c03064 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 445922059 1250 445920809 445920817
    0x150509060103094d030c150d0e070302090928031103070309050f0d02090114040e071401030606030203271c020c0906060708180105090a080d17100614 66
    0x181d80400311a0107400c0000a56502004000c10340301c20056820109944c008514265000b004008042d0703000e08008018085401c041506146a4204141c0c0500b00d0180203034042c041c4150003510300e01d89140140055950010010013542d040300b04429121002c0d84441c4140e42c1c840806030b481e480f070340d00e020b5a07420f8003c00800e089201c081100c0c810550301100c0c81064400a9855408030301e504420721041d507050b600000d41c030072030003c011b1106a80300c0f000c011394124020030229000c6200c4070400d041c20181d40280d41c40044400801610b96058082c107001040f20785011840e41c54100000c40d820028240c0e0041c245140c003048406002c010001d41749140315020410741081031074034000c3c1d90382c0458030b003550148080720005030052402a06035685142c000c3c450314603110841682030020020f42010506000c0144400c420780e440f80b105210140c091400205203028901001400d865403c0b641c54450705060010410300c02c0d82030314084100c0ea59400c12071040740b40690b1513900e50107 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 445923309 1250 445922059 445922093
    0xe04140109360305030402040b10050c1c0507030c060f0e0a020a05030a050a0b091f0605120a030e010e04060b0d05041719110319050405030115050906010309 69
    0x44a00011a0762400c60340312120a01910210b0481c000d09110080b00d2034000010105919041030005008a401803009560052004100081c0c4482d01400a110149100780320304c000358010984004208081040308500320010103d01012508040b000345184a40c80004041050210551081203c50307000712003440d01ca11000d0202c92079a480f021313662140c03048140c0c03140c00d4003400001e8a0038003242c0171520940100140148121a0300c0790100e00c0c81c003a155140b0307842141054450030741d54039903280c0c0f04808207002017959441c00f001c000308045441090a0290441c504101c0001d0300149004055602030070541d8601000c000042d00818903503024400c07804002400030f030403c1d02036000306d200e00c0c072440b038410620b181c01c1000c0d1540c0c02601d04450389100507086000c1000e00440c3c3c503d1946042000f100d00c0c15514500358401c110045148001103100410180486c0c5401e0144141c2411403c9491003205d1500b0b0001e2000c410240006061668500000701800106a06110700c82 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 445924559 1250 445923309 445923341
    0x10e13020d03200f070506090603010b0a090801090305210618070912060b101b0201030207061e09050c0d08090405060303160302034609050a120c08010b0307060e04 72
    0x14880740f110f49a2052a280151901071a28007107058a04035050707480c8040c02a040c50704503070030300c000030303803594000c030150380c144101c5420015550030240030b401c01d41031196507210780b20031100342c007000e00f580740c0311708071212042d000300b0881181c88207440d00e103c5141d1151412003e4954ad5001e45030031002d0f80081484408500000c01400a04e4102600c81e0300c0030b50340300b9880703011510100c644000c00030700c6442e40880c014241e0090341c07080d0064411140910800540c10344401003000f041c540205200e100f80713131150a60b0301402024401900141c8094504502c141a40da5030b00b0780603c40c03203008a01c030b2070b0303a08040342c4a074801f002611722034441e00d66400c244004c18140a5640d41100381040d1055502c0800c02c4501918041101c9003418010110724103030b030341c0749a184400c011802a0f2810400301c0a4005629555141c08100614008001030340e41070003030401d8103001c3d81c0c580006d0643c0e0b041200c0920035803000140001202c40c540340480401000314002400751002c820342c0604a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 445925809 1250 445924559 445924607
    0xc032007230d020d150b040e0c0a0504020901020c19030c0b031f03020604091d0607050414090708070507060e0105180d0f02030f090f0306010905060306010e13020d03 73
    0x40e49800e10949031801e008429036280402004020452000d0341000b500481d0b0301c0c103888002003108401c0016140e62000c0820500d90380008030302112400c1390241c00540c443d81400c0e50500340101110058001680c05515107110300c00040d6071580205003860003000d203104100c080900c4241c0790300103075030302c899040e0480743d80d102d9140d0039030410b03039000c4245440681c008010605054902040b2070707001d043c66050501d4018000f0003010060000620007401e0b50501f000440c0500003644109425140c042d107850400102003145203200b40701c180150603190600807569001502c10754070004515110365100c0307007031800b500501543c2d640d608103582014103004c044150400011450490541291843c0d11152411100e009050b014034002da00100722003d0f01e034443c0300090064246c0608042da40005800100c0e207041000d0340308400142e510400c0c0b00032440d060004130300400342158a45903d061100c00d0000000da8140b0084c815804501c2c404205030042251041a05124260380b80c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 445927059 1250 445925809 445925819
    0x2c040f050a090b1812090409021207090b0405040c0306110d14070807020115050f04140a060e010e040302070504091e0f0212011e0c020715090f05040204060c032007 72
    0x14040c0e03650200c0d099025200000c130011180c2581c07100385100040141102495051400426400044243c2d000b039155540000940c0302c0c0030700303e90240400d0b030080503c00d142003414000c543c181c00255200d14144030602c400b1030a0f4400d0b420540323400071400940b141460f40340010a20030b40c1c903003d42c21814510194503165500355021311440070380d1949449540c500400320b00301e80071501f0303400c1c1c84008808103200302d041060700012034000180c0000b51410701c2c5214a60b102900315840e170300701a00c3d210140300891002e01400d0050110031451185402c05550107903c60189010751401a9525005d500070b014048080f41d55001081500520011540c00d10a05181030140e06900030b040f81220091038420520074200c1e21031400c40d280c05000d03005e212140182c18004800802c5108880d0b02162510924030381500c08406a103e4130b0071149084075903d03041242d684814401c0344140010410240c01181c03d0000560500d400c40320004070b480500007c4103e070310182c0c0307180300d1b5003c0419 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 445928309 1250 445927059 445927061
    0x1180602090102060106080f04110a08031206030705030d020d0305100302090421050a20120327030906071e14030c160f030b0703020903031602010f2c040f050a 70
    0x464070a90aa0344141e8071b40c1402e8800b00400e8901341081450480007070040b031080a0450420b580082a542c00142c5d184855072543d0403072401070107400b006400b40073b0319180400040d00201025000b900b204460303008040d4484640a0b0b001084c55102c00014090984c001d842c440990f500505c81c140b1414941086d280e8400c2405081e4041010f43c02a41200e5000da400e40d40c5403ca00e9444180400400c0c0d003180c0142c1141004000701c3c85002c4818010700c9080000c0d501c03030b415041080c042065a4004480c407100481d2941d82550030030400c0000da610303480102d5140f00e13000320013007140342c41d80d00c103100007001c1c546009170140c02040420010008007000502070840c180040f20f81d40b03000f40145108110b51341c4640c80301c0d0b00c505001080014a2a00e100ba4015100d050060601c29444003180c00d65100c4030300c1c0707406d03122074603942c204541c2c0110303a507194848203103016461a01c3c801406219070120032440e06da50042c1c4401c0303c1069503141c01007a07000540355024001c9046c20682c500c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 445929559 1250 445928309 445928317
    0xa021f02011401030b160c0b07170a0908040b0c1e160f080a1b090e060105011205070c17070606090b10050c060402010f0905061b1207020604051201180602 68
    0x20055081c540404022403918698505a980100351980300b61034010402d03190040c10210742c0c05020241088130041482141c4d101d10641041d1500224042400b034040310100c4010038085510707103071250280114280700140c40031f443d2071900c059900c621a07000c01e458800c4125080b00038144015110104460100340310104500b0301101500c081c0c2c036034181c00034984480c0a2040d09a001c3c17401d1034007280394102001c0400800c0744446c80c0d06901c400c1043c1c04d50300d0342241d2140c0381e070141004210f035582c00040d60303503038540c031000400581c140100010820210042e0140c91b144201503c101001d50403030483d0072540e0f000b80c0422280b9a5182024054803400700c0a80c42140000d0052030760901640480c0c0596602801904056440703034010f4521444805200c0f04104030001d001c11b0503180c1c08020142d0b1181440c10360090720798011620300d80f40348501c014005d50003d001c1c5100503100c113410b0301d080d50011101410521084401d041c010030080c800e01e4400b5190b960764109110b03040c0d00130 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 445930809 1250 445929559 445929619
    0x4080d050a060f05060913020906160f020102060f160e1513030c05010f020613110405070509121603150b100c030e0a05090609130b180c0a12080a020a02 67
    0x20b9480d40d4008105290041d6030005802251200f00000304048588c028844044020043c60600c80102c00c0000904940941180d034090308048010640d82c041101ea0380c0144c90308203030710140c07518107419000c4400391184501403008030f40d080481c41d500c0c41030501000c000141d03043d1b1285650031400104010701d100a1710100b03d801c4010036154850861244403601d590010016910342008180c02e9641900096980300c000c00451001341e45d4600940d4084c1e41196601c68840b440703e01040203086441405840662019090700c020100319040001220340201064182254442c00240074002002840381e128560020280e0300c2c903045070f94400743c24001c1d42d070740078151400300511404640724040c3c0c9500070042d400040b014501030049035488074038803491a840300c090350740741e50507881c00ba10502c2d070442200c10b0900c1e2403041040004081d5008446400220b450040d04ca00081d20007000902031040004410941174005c2200e14103e80c0c3c00b42c5084400303003001000403442070725504e507 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 445932059 1250 445930809 445930829
    0x10e0615240301060c06060906032d051b1f0507030906080c03062116050f0901050f0909070b040b18030a1101050901030b040e0601080706140a0804080d050a06 70
    0x1191014481c8444002018071a002030038990790801130291000e0704400b0b02112030303d03101c0e031000c50610694020f400056105440c01c8100f04c2c4960211340388244284542021540d1a1040710003062000804407114001c44406034004002800407500302d1455007400e007404543c5401c10703883e26034030500501800380079554080420761603060442d111481560100d027041800d001061592030505000c03840404906105080c2c03402c281006c81c1040c4a0300042010001039182c00c01c07260030014294110401e0440e00c01d442581030030001000030f5a0f104055010700005800a076800100304100005004111212030711236070b4848a4500c1a84400f28402d509004500100d030942000255540300c103500400c00201214002e0044480750000442c590415803180710b103ca00e51220322844200c2e9600c0c0d0701426035503041080340340c500744960b80000200615034880d080d2640110080e00c4004000d8608070016460324106400d00d0701620030104d56191420007840a00030300c80e40084204c0e009444 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 445933309 1250 445932059 445932079
    0xd061a03011503171308011d0c10050d02090f09190c0c02030c0103050a0f0906020903010e03041a030703140a020306030607020d091404090f140c06181002010e0615 72
    0x21100303005101440000c03c00041322440b0138a0307121903030140040c41c0f040018001c060366103203a00e5083d03c1b020b480c1000794941e405d0f0580c0741d501c001c0c0245c0442070b00a6801d1403468186240c000c186203c2c0ea04524012680407e100d032007680d07507008105000d00000d00030219810403000c1c10340c45074502c0c00c1701c1201c42d2a01040e0790295000f03d001c0d454168005011303011260311b040040d006090018021143c0d9641c5218013005120248502051203024a1006888591101c145421a21500030018556000740070421006003840e0300004200c503044000c070740700c2d103d4000507005000d0445901e40c508082e0070400c0210718290f03000e54820742d401c908031440da0721141016a29005050356180005182003000c0c840d020b46027440c081c02e080c010b4000100e10506e07803504441c844401d01e08407a00480000041100342040107440380000040707404920300300e07619140e00003040c00300a41d2401440510001c680040c002c0d807050b99068801016175005190054400e116882040e19061050f41041 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 445934559 1250 445933309 445933331
    0xc02071403010501141915050703021212041e060c0509040b0a06050f07030e090f090d0e060d0c12051515030c0702040e0709020a0923010e01030b0d061a0301 69
    0x10080504884044402c020003480300002c3c414400079801444801d071011100021f80400400e030030001100760b560b80d05480d0021854003c1c141404e110001881e90001c0c418803a01801e0703c140107405c04c0d0302c8078203450380807462015010315030300c0c090000d07040c84e20f80700c5203808041e00071004000c9444102e504003d000801c00400c1601c030481d000d001d0010744140701040994401340020164070303000b4105105085162000500880f2041302ea075900c6554020601505079402c0061040041c1f0740d043c40841d044038400400c8950084503410010192249000c0c02064081e8007034521184542d05c090000c0d2410134949240203201d0201d00d80500005103003050f6210140d825603010b0075101d400351b40b504e0348039020800641500000c4980310b00034000001aa80420710003050070303810503151059602d18105000b42d0b1285401090220b213022130340c40c600380b6a400040c0780d0310f800b000d080003d580890035000c10030780059843d00901c40d0346020501082c1c00083d5000d01c079050003c8000744040b00c114 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 445935809 1250 445934559 445934561
    0x1e060501031401030b0a0e06010b0d0c0822140a05161418100806090708010b180a150b131a0c0307031202090a12020f0306010f0611100c0207140301 65
    0x490b8003246009407005100140100d44180c1d00041c0344d03c0007003540400c1c03a0714141000c00aa0110340e0500e0000784804c0828039500840741108180d05010b590342c07401d41580d030031550900072030148088e800a070103000c121801034903000e442c24203001c0b103241021502d0a0f66803640741a4001440850b842c0c0c0002c1e4a0340f03440140d035400000500a101502c160b407410841c0b0b085c2c0508010900101c906002c070b522002005401d205102110042024900d400c400608489820a01d41d001d8450201d81c1c1c6c41084003d941310ba00149582c0c40028410301d401c06075101004960403040d0003100000d00c005508218103181d4003680c02c44494032084041000c20406507108282041c0d1950704103100a402003401040300112007410305401600d0306401e18001132201c9002d800080c0c00c80545000101503043c2503035441c00a4909134014200c1c0d50400541c80c840381b44a1107014100f140c0d0800311106400148443c601510b90103100748522100700001039103d8146014185180c00340038100f01c814901 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 445937059 1250 445935809 445935821
    0x5030705010516090501030905190308010f05030a0b06280602030a02101802010c030c0c0e040b090a0209011a1309021c0204060c080a030e0d0914030f0c0f131e06050103 74
    0xc0d07038803464413803440e100c0150040e11440800f40d03418040c07007a40030703c4410841c0141c4480f602c2992001119810006640081405a04001d009902c00701d020000101441c1a031034100c0d10484d100162016032590740744052f18040280c140c403c00c0039100140445e00007000d41030112071a001d5a00c050b20b1200031408403550310400c002c10880382c1c034040c1c025500850800090b00e01074a08601c0c940b03601c0d19500c410141c0c5500c0f407052580f042c000c0100f4890400035417500001a0310143c84081056000079402c82c03018010602e4510701c120340d01d000b0241c00d030201c0310070364a50111008400d6448400500035000700c600901c0c1004a500d15400b113220320f01c21241a5001a00e40f03401da45d041d61031302c100b40e812020070381c802d16644486290300d080c0d00b00702e0404404030702c0c0d0302c074101c00d800c290400492003003000009000360300110014003070300000b041a030b0b200c58040e220580080c9034400000c107902541d8103090807007807500d000c901c40009101c03450340b032030640c0c00c6040c0400e540d2080110100d0300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 445938309 1250 445937059 445937101
    0xc030c0c12030e0f0102270f130b0f0418030810030c0e060402040b0c0c03010f0e031b03091003061a03220501020f04090203190221041e050307050105 66
    0x152207180d140c98080c0d4001c0109458020440d0b491208200d82d882c2242d008059001c1d50010341500e290080b00c04000e180c4881c401920811119015640440d26008815a1000c14180c84005003019500d034541d01c03510400e00100203200300c01109100406a2000c103100b6000104424005240250303020414411030354002691002a440c0100c82031055030080c04042d80603408100020700b0030300c0440034200c45400e20000d00603000b982c1f010507003142e060840e9031820504104010400440101c1602d505485214144011407078901c3c2c80781c1035108800d00b0b41d9100038220500b03480c07243e040d44400700352003102c14030300a440c841061030138190000721221107000d5246288031456148007160720a065215100242c208070003100c665000360400e030410603a040d030120030041340081081d410250303154018402c528150001e0750303041000c08101d1810101226610200301046003030302040c410451084200740254609240103a16548000010b852035824a4081800074204042c4118061 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 445939559 1250 445938309 445938323
    0x90702240703060f090e0d110709050a06091e0507020105150d0f0822290f07170d0b040605010905011b0605010f174c0c030c0c 56
    0x2924046020148000c0249510101501e8000004440507412150409010100004074102d4642102240b801004548170001c000b8140c50070900401c002c5520701c10b0f40e03400100821244c0d6002d211102803c0c040c0c1c44000024900707106804801c2d0540c0b90306400700d4000c4d0040c0001c0c1c507803c000303c0c241c40c000c0e03801440a88809106840f146042c0c14202891403064090814480c06074840301030941080b42c0c1c40600c800311818100050141e502c0000184c103103122803001034400c41c0250301c10b0418481151100d0700c0d001501105d0749128400703480c407907a40030400010080c0301026031701c10340c3c028000322050300b400d00b1034401041c034250103540d080d05c02c103a40d42240d56260100448945000707281c0000a440307810001c0000c20740768003689010300780501c04401e015162882c2e0303408820003108092640d40155042c2c0e018540503000e01c210490002c41180c0b1001c1704603220111a580c100514000150b100c484524000b0540d0000fa280060a80f81000080c25022042d0b8401d4061031000300b01c0f03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 445940809 1250 445939559 445939603
    0x8090105041a04060b10050409060b04030c0303080c0d06080109021e100302090d02040603050606030f160506030411040c020a0209060a030308010302040216020901030c090f0b03062a07030e090702 86
    0x140809460583c014026803010031024603100102e0325410800c8281c6002a00c0060280000c20130707070080318020702c3c0070006149402c0c91500c400c2805152400010200440c035004038280203456001c2e0f036903140c5120340420401d5a240401c0c5d0003007408010890184c40190031058282d1506c1150300400c001c064402c02d01103854000441c0250300040c1401c2e4420050960440503844601c20f0501846c8a9801002241041d004141c500002c0c0462403060741d01c442c0e007941d1408101801141100c000b9108162070391560302c0c0022007880240500c94000385405070007a0101d0340094110740082c000d840110b5940c80305818810500703004d02000d008161f511303004000609060340100502c2410003030420300d071115580020f505003401e90003500d0a004a0344140401300700342c4250151003c0750002044641c00e550042501c071070000384007502d603240c02e01c0801d54003021b10024007103148483e40c600da615041841d010389415a1618a280280041000500014000180344001d0f0b04000807840c00 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 445942059 1250 445940809 445940843
    0x15010f0507020f150c16050d1e0503040306230c0c2505190e090a0c03030c0302010f061502070803090d0b0c070f03080604230c0a03020c030304120809010504 69
    0x207600b0f094000140c12803041c1e2400b1222204001c0a058815004070240c00080e4401d0451a200c11035500a1842a00344a85010004140d501e18402c9603400c07048664078501d0b0b0381080350030b41c000da5002a0455042880d4011400c914245542c503002d11821000c1d8a81c8801102d001d9174091842c4481031540102c00e040c8108003184e1a40794200c1e0040046604103032218007042030290529642d142c5900035040620060360488890342d400b00c0c40c00e0041950300180d40b40c0505095562002070280b192400b1000d092510030b40141250354125502070100039a81c01d400001e00d0000b45251005000301d110108202c40c011007250300840008041072118503041d1294042202c010b0078000c0401d004021880c0003c1841146900701e03406512900303801c0c503120b801d010a0781c5030440310b0040c004198043c0040e48071641c019681000d10b08441d0368480d01c81e544168001d20418501580611003c03041004000003020b0300110350011355110880380c0c841d40d80f200c1c00c1e00c605842c024424814002c80100d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 445943309 1250 445942059 445942069
    0x3070c050f1f0e0f070b0a230a030906020d050106080105030c04051b0309070f03050102040e09061312020c03061504150e0103060b010c240e0a03081303090e070815010f050702 77
    0x20051841c3d4041d201c0040c52904014030b443d80642c8000031900340851103500170764000660011406501c00e4100121284408654940c41616044814982e442d000f00302444016810f40303034140039007101003040d940c68410180103c0000d11520384a44224461110541001d0081c1401480c07140007400540d01c0f440b00760710b07458000805100031481401000a040c0840295107801140158001640c490810050150040d0b0013010141e656000c0f4043c010070240e40b0703103d00c40168120035805600700c0c0101c412410b008000000c694107220340c1c4140005001c1d410b080c0742c0400750446d020400900e19400aa00c0c4095a22655803083c0100e0010004a030085d000191002070502d40801c40452541d40e4142d0071803089034401101da041c000e202c3c41550544581420f00b0b01d000020560700041c1d55004000100040c51400000481552541050301072403031a030241c074070110911214905800002d00034801150141000d215450200645500034241c50744070083c00c0d690b261504070b454080c0f00d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 445944559 1250 445943309 445943321
    0x201051b0a05070312020d050a1b081308030d0513170a02100f0507090e060d030e0d121e0906050307030911031009060f0b06031305011103070c050f1f 66
    0x6900c501481122a001407818003020000e548111a07124042071507080c002e25100c211812030040c480200401240340da00140714102014504d000b802d076031b03000761030300e0b0304035000f00381c0d940c1c1d009121300e60041480e44001c030181c0f0110490103010812a540c0c0c04007181410b0070103402820070b070712a440c2001e0355000c4030001c0100100e640120307148070b1823845100c01280c010000c9207200e0307a540c0050000d100d42c008480002042c14011040c05820002c00041115160344c034018103000f4480c901c20600d8444a90611500340c0000d03605001011912002c0c000c419046511510326103900600c0c84014010b1001c0ea05588190359060b0550f40c0c0c010003500100603c00d4103031008000304044000b50381d001c029280c000007078040085180601450840c017900e0540000c00a0035040030034000b825210041942d038045c02c150790410301c2103c1410064011300e4040c80c0b02c1c440400c0001003140e00307074101a402039000d214a00f2281d904161b0004981c07200340211080202c007400b00c000c02440b54a82d003040b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 445945809 1250 445944559 445944607
    0xd150c171506211008060f010e061c080711011101021303030c020f040c051b120304110d1a100803090f0123040f06030b150a030504030c0b15031207020105 68
    0xe4a00b10f1030000c524203607070211500c0e2003000c103214092101038014003005404c2196036032240104c1d410407a8022400800070092800f40000da01110040381d00600d42002c01038026884d03d50302c005030704102c0001c0440076000360104030103c9118940310014030803201c404140c1441c144606040d40d4013110050304840d016640119904403171286613417035100f01522100c407030711020f03568500070070501c004c0e040020301c00c0250340003080550040346100c41101c0d40694010309152041022074001000d00b5450f40019020360711030000365061004042207140541102482d05030119074403900030340d40e4030403025015041110042090f02a5005501401c2c00180e003015241c1a3742d02c1c00320080d101c3d0816800140c40080040b002c01045416105200c040181501d5640d1a107140d101c140394607200703800751842050381d102c0000d000e0611680c00f4051180d402440781269044c040681d041816011179080d100f0f000d802d0803001006c2d580c1e03040780d0a150303040e11140e05000407440005007200040c810 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 445947059 1250 445945809 445945837
    0x1090e0d0f030908071a07020105061207050906150307030b03070906081e010e030a080f0f01030503070f0302011d0d0807023c01090b0412020d0801030803060d150c171506 75
    0x10b11000501840301054a040c2100b40c06c0c0e10351800850003400e403400500060300520848107050710108000c1034400544605851820039521910046841401d0100164900e61404014800d1550703064018260041c030031030131a560343c3e45460b0038104507009885620203a50100f4142c0c1c8141c03056840440c4594100b600008600401e00d101c0d604551042e1340c8180007034403400400050400c03400038142c1004280d04042d44030f41c1556a8150703244a45200504901405945101014400d400080c4809500c071140200c884030340c03102c29075030a079020300240031941c1c40001801181c400641c0390052480080c00200340c42410010301074001d0029115203203540407004902d044e1109002d105681d0b481030001001d40e10342030030040d02c017a840b01d41e400e0854010a144404141c0d02000c4281074039002203540769207480307030707000102c0402c6288002400400c42c4210388610420980c0002800343c4161101d400e20b040809124010071001c8407025208034064106500504240c3c011340305045600c48 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 445948309 1250 445947059 445947067
    0x801060e03150a0f0e0a0b04020111010b10050406020d080c0d0b0a0e01030c170606030a060c0c0b0a15090b1513030807080a03061d0103031b060f0501090e0d0f030908 73
    0x150b820340e6044111400802c00d5111401003621054904c01c0d1805028403102800608040ea40c8060002c02c0c090b1000c0d0402442c0c4100008042e000c0d80204c8100700000c2c0291004c00349500f0260440e0480d1144c1d002600039002c1822029010715003488c070803540e01941074605000d4014907002000c40d91411600444030300307070100b0181c40d681b075014007850282e5482d02c1141d1400d1458045400c40344029640c54118405001040c0ca0001d20f00100c0703548404040340403481003104503010038504101500402c458814082c241c0c5c1158007100140280364166810642c44550200a5502103031040f50001c110684200d04441104054029090a07003080d61800780d5985980f881904480010784960000040c8505013540600c108c000908060307003420303000c0b040d1508005407a10b0502c0b002d4144503d0102c001d401d41300300707500744094030b034880307020011040c02150b0600180000d001d546a52880e0922007552010002414500823580340d035642810603200ca4220050b203002c1404860a0f0420b03c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 445949559 1250 445948309 445948333
    0x20f15070302070602370f0c060f021602010807020a1a101a1210030206070f020a0b0a0c050106080c090403031e0f0b0301240b03041b031a01050406060801060e03 71
    0x4002004820308103219a281d44103c00c0342880300c4414000c91b011500140321601205641014544006260500304440300d8002410028080e014a2088601c8076100251a19200000c15413012526000f0b9803005041e03a1900c009a81c2d840c8890400341030038404c020350740d1040c540703a800300e035005195800700b101c0f9540d5901036051001c0c1880c2104210a000305803c0020180c00d80345940c4170404d50316210040785145c011964900c2851000b0302174001034000039065496080e60040100f800c5403099a540403030003401000183d500d90115840d5017000000104440300003004100707094020070b925260f0b01d5030743e001d60081c0040681c88004046200c1080f8011922342b0070300e010f1303510204001c50301c4811350040608580800640400c440480841d030102d85a0064003d015500b030002303526542e840e581400310000207500440898110942000b00411030740080c0030054442404054040b6601ea108101c1a034015025110009400c40010032103c0d1140001581d00c007070140644614082d03017 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 445950809 1250 445949559 445949561
    0x1b0904020303070f0f060c0311040b0c0a02090106030e060a061a160c0b040617010b0415020307140715170a0b01110114010501180506030408031e01060f0f020f150703020706 76
    0x4040554142e0035030105c0409000301402203031214003491400304900303c0d00303500e80091402240110540680b000c20307444401c80b0704101e040807998004015400569444030010003818140e80110018021100402c030030020901070351043d00c05080b14034180350200990380c02240c0060344610380300b81800c0c100300041500c0443d1900501442e041e0542e4507401c050010b0a00744000140c402ea6010000041180000c100300782e4040d80d0a040e6064140d24850008038914040d802c0042c0041c1c0d6030b0070180c06040e5000421030100d500f8109026100c8002c844161802c1106242008000d02c007800041c05214842d030080300040414100101d561464050990848034081000c0b02e055001c6001072100b903800c2141d5040010341e1010042e0f2403410080851000c2c08041c00c010000700700400842d007a20f00c101030307078061000e250ba03e0710425a503d002c01410520107000c2c010114062560100d05103201044840c41680128000e209070010300000c00b00b690401080d00f0b00b050390900c0743c04006042 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 445952059 1250 445950809 445950833
    0xf060f03060a180227181f14030105061507061e02070c141210020d0204050d030804061401080a1101020319090e0f04030f08040f0c06020a03111b090402030307 70
    0x206940050301c1e484c40514800c1403070148968500354000c209a054501d55640c41441c500e6444020703900c00b1619910080903030016141c032285401309907c00041411a80c0e4102125401400c40080c070850301c807901400205003140d00d8850700404204442004941c05800587c1e03103091503a035041c1e0300d1f00a000a1800c98024410490307034001039003c104400b2100c40d207c00d0f500c05003200c29000200b4810235865440c40008000c4078665000304a015211940754140d07801040058060090b000301c03440c009124071402c44040307901a117441541d400c5d000b41c442029043c1d400d200010078901c1e4164481c0f81411f6070b40809141144003c10040604560300c250344541c00000e0340394061080e00b4001d07240c3c21400020000d0030000d861004000c0441d41c07050f00703402107210302d081c91056500d440c00c0c01041d401070f04202038140195814009600c5030300142000110380070b42d50300c40422000c004000e031600740c60590524000450a00004d17580380c480022500184014102c92034400140d0b501102100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 445953309 1250 445952059 445952099
    0x513140c061c0e0105070203070609021206040f1b060e01111006080c0405090a020922021503010608150102030f0a0c0c0803030f07020d02060f04030c140115050f060f03060a 76
    0x1107908006a6440c2c0d8080e07001601c20f604002c4c80f8900d80014025502d002d0361401a21060b01c6004440554580300418010040d41000f42ca040b803500b420f0030050f11002d01012101000650050911030f22a204600706454145c1d442440c8100d044004554804a85c94210094041e03021580c1e08000144a100003c14509014005000c520070401c8201c40d40240540d846030000364010005954083c001c691211805051f9400e035002c20035003208035241120002e4100e010308030503d40300c000c1e4602460407100b03255a0030035507035580c41440a2005020810f980560300c14400e081d49419903002501c8840510b1401343c040102c1e80c1c45010b8500f4940e84501c840e03410000031f2160a242c2c02c00e51a5004020340020300348007031960f100a41c1c40100610702002070640700702140401d0312030001c50a80b00d40003450003991001451245000746a800d801c503d0526901000040703a080901082e44406002002c450a140341310170640965400100400d81c1710042010100d40152070381e40030f000c4d080d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 445954559 1250 445953309 445953337
    0xf0907020c030d020106090c031812090305060903120601051c020c1f0204030516080606090613090b070e0a030b130602040806040b1902040302130902010315030b1006030513140c06 79
    0x28600b0000c0008c82d440d60071003a042505190003100c002c50f0480c032408903507500ca00c0c0c034030b410010011700b100c0180e666040284903020786000e001240f40000041c0c4110301902c8104001600e8100c0103556a103c0c101c05a03030104041a00e41052891a601608107010043d0a50710b80c51001085510080311140410a0322a400318040c428003c04115142080c0662840c801e0028100813060b07a5540000740190300c5105414001500c1791112400c1d1450500140000c0c4140403403454103002e0407200712007120020340034a02c0d40160745400c480620851f5000101503580b62900c054449460a2482c000d84445408000008030610204070042c030803400384409140d02d04010200c60340707410905c55511a51401804144007581c0d800c004c003245842c1405c000118034a9920041e0098000c0380080442004a91000010300c07410201061007400039007100c03d08151206010303002c03680295181c2d41244641092100041c00350311030340c0c80c0c0111003002c03aa078000c40000045c4c0b981d800100610018 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 445955809 1250 445954559 445954571
    0x7121b0c11030a0807290457120c060201060801140f15030d0c0203010e011803230f040303030b010903050613060b03010e010b09150f0907020c030d0201 67
    0x10000c1c08800300003900084000c0e02c1c60700d40903201c5500c1806003080c080c08884010b490b244d100398451242100b0900e182c1611411407402e41410202000c104c0c2d01e0704400c030300b2903602442e0304080d520aa0340328204a41c80400d040c066003001e50108440380d0031406154400c04c00807a500c1038201ca8050351602c105d44c0c5c84e14035424008024203654003544076040c560b040911100310310100c10340807640b1000b202d82e80c41446c3d403420010302042c1c08191b4850b40601581c603403518100c1d8030a02480c2068003da00a001c1c80a1401d940c03030888445900300c044865082e85150006445000e041030700c41d1240000c0c94640854a4a000c86035000c0915081d98840001e01041010f030940600c42c800842402d1078512503183d5100d103619040e00804924000401e80b030040c04102140d48010080600a40200320120748441400d00034104003003ea441140000d0010f042030746010441c6949110252503410401c410741d05000d00d082010708080107602171903400f215140c03010803005078010650b034000300b81 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 445957059 1250 445955809 445955813
    0x6051e0405211525030b0a080607020c0d0c0528060c1202010507080601050f0c010204030f02010e0a030302032502030f1e010c09140a08071e050f0907121b0c 69
    0x1520381028140910703c03061070300b00310010303d4403074400d00012104201040500040e1004400801c4101e14140c0c1c02449450301040131100080d0252183c860340c1c00301c1d12640e1011003000400005154002e0804000d44401d010504007055085550908112405031500310210b15881d0000c8a4000d5070000710205c1480090101c50240980880160b0008100c54109503d00500194000b003425061240002c2d482003103034102d1088520044107440215156034032894040180d0415140582c000340c1d0000d062103043ca05005010100c0c0d50580080d0718104481100961a00c0c0b070b515510301d140d094620a4001da2014800d20200202d1840600441840c03035840c06103154107508a0f880e0b0703130302d00043c09058a402c00d50b4603054078042c00301010003241c10400a070b000c5100b604091500d000b003000016542c504203850001d2141c0401c3c81a41607032303c7d07100b03000011000c07010b00d0394404e2000e8041045140519482d180c030402da00d0010641007120b98030043c5522500801200080240b100001 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 445958309 1250 445957059 445957063
    0x110c13090b01090207201804031e1206080f1c090323011109180415021314030c010905130905010e0d0206010e1005060c010e0613020907030606051e040521 68
    0x6110030171b1440540b040086011a49900801101e64242c440c501c01081c241030060b545242e50300c0a810048801c3c0c000f04000a151001203814844e00c18101800412250404506074040c40305241c014100b00941c1c4009500c00f01d40076460a0520040f00c402102180a0000310f03000c0701c05000075013081c0e05501340c46900312000c19490348103d071020b1001940c981d40e005e4501500301c090b501e610380152034070b04206c001144511944407000b480022a141c040603000c14010860340200307850715907010380c50241500d84504204603400613158031428001844d0940044400b18840c81c40020921500e5581d6403c403480588604416480a140000f80365030411445001d0109502e070b00c0d41609000c020861100424081c00d071080e81c0204200c3c542d406c0c250b0001c260641503030b00b2030b241d40c00d186020350485210030000f41d000b11700c40c90006801c6c83c060b024082c00c072020355880c1854018059880810141000d281c040d10101c00c02c80062903070f0301c203041e4041c035188010004c45400c1154030760314 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 445959559 1250 445958309 445958333
    0x15020c150712060e06040e03160605010618080c01080a0207050f073f030512103201050f1303060605040615020307080306041103040b04030e01110c13090b01090207 72
    0x3180c0c40b410100c3c1840181c180510b01c9400602c252000b00e10003e5001c00301c1d003580580e0b016141d8210f0000742d22400d0017030035003110741200c800d52070390020491450340340103121300300340510030503035114107407056595110701c11240d404950484010305005543da90141403009020800003a03a0291405000c94295a4544142e2910300900d404041e80d0b24100c24104000c0490070700c200d4140615440c00349400303001120075003250308139491403504c0c109403400d004010500a0703084003800682d0204501d5040011001000610072020180e048039100447d041e512060240e80c1910061206d4080c8000148082003d18400c183c0882c210f03003004284001c491555000f14103181e9078207000e50102c1e8020045074000398111880503920758405c404038010b820342200ca24141035000040005000242d10a0350240340b003035440b001a00203000046905c01c0c0402d008011503007001180608925100703403002c494103244c40c4046048121600c8064110b8002d074007001c1030030f80014606040040030031940c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 445960809 1250 445959559 445959587
    0x206060a0605071104090204090503031e07030204081c1101020c0c03120a080a0b0d020907020309010e03061b0d0f05011710051b0310030215040302041109010c15020c1507 75
    0x1141c14905240c4900220740c01c44c00d03119004030f03a90340c106029902c0d180c2020710714942007001c480e0340f0700b0000402800401d140103685c0c4003920303000c042906144217000311007c40d04003e00804032801c1d000703120321900b4049030b814403c1c0404070024141d034210130f0004e00040314940f07026100071003a2005060070704480010180408904111948480d03030410034041d0800640c20340004da6103e400042003600f0b1305180702941c0441c2c03078010010700307a60000050020720310a07a80c3c281654000403c0c10f503070748015500503910040c80d1401482d44160308014000310700c0100d002103201c04407605407000f150004e0b00540780385496081c8982007030754104100c030b60801301c00404200c13902e032410700c0c090b0032603030300c0541800300b0400004034030707540b1440494a0245130018500d13108078038542c020b4801ca034030512049000b030f820308174036840712604401500c00c0e103481030b150a1100010360390782203c07076070750361080d100c642ea0b09000c44864801e040000f040d030250410344203046401c0402c4007401001c802000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 445962059 1250 445960809 445960817
    0x90f030708010b03121905070f1509150908030a09050118030c0309060206070804061a03103e070c1a030403030e030913150b07060204030c12050601050f011e0206060a06 74
    0x105001d211003c000b66455400911f4000c2e00c0d408181740c410004a54044043e26403400b070101e05104070b60740e2b407003604800e100788903040032003120f4500241076542c10fa001800810b014000a0220035032a04540640c81c070460000481107699041d15a56500c07441042d400211104820700c205604184882c010741142e000825251929400c000c0422800030b0006044648481508086c80c0c82803094822180c4020160b45000c001c4121900080260906028810112034100e140081320304591440c1c515101c04500d10504540c0f00010842c1d00220080b42da000040000088103442110510600d007179424649903207003807500f40102602d1600109403a01e0300104440c06143e9070b0500a0040c490f4100b0010803085405031010381c1e119925400b0107654400010424100a500e40c010310903030313200b80f20200205403600c854034041c01c2c540302c00030040d521450041c4414035042c110008900780524010304600720000c000502c0c0c101040c4e0728405a80701c0b20174444c240c80c010303204201038801850 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 445963309 1250 445962059 445962067
    0x30402040e070f1a0409020a0305090705041e0902210102090307050117060d150e0f01060f051809071d060114030702070e0604060f0b070b071404050105090f030708010b0312 76
    0x2000e841c141d031184c0b0035464840712803c1c0800000c4418820382d0010103c200b021503d452010340041d010b840116403445d4a80501400842e00d0701c0c080c414031103c80b031001c544010f1103c03148610002480099410390340420300c031041c14100c0c1c008007070507010104060300240c0c44005880501d03280c460309401450500c1000c0e60040f0165a202041070340c004000c9803145c5000a0317a061000240f010035002c0700d20103045c0401c0c2d6a68003400a002d104950180c002004115074500441781030070064091607034800b42c15040e210781e00103410300154004c0454130513540d400d036564898481140460710380000d00c41c030700c404204480d0703041201d081401503004501c1e4650300c2c09120080d00c13110b00d03008004041681d5804507a03107840304e50240000d4221030b605034030b645807100040216600b240004540100f8583d0000b68010310030301d079242021100d110180d0400b42080015585900900c045542020034180e0a84803036404100010061004000008050659504ac1810b010001c542c00c0402d40d4204 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 445964559 1250 445963309 445963319
    0x3081908090a120507020a1e080709060b09060a090807091409060f181501030501150b090102101e0908190201021815190513050d030807080a0204030b040503030402040e07 75
    0x541030520040f80c034a0160703500c007401d00c002420030b401d1383c00401301d0301d22013141e00542200420303031b00c820707140b0200890350b54555a1f076007a0140c5d03105000e40c0c010150305102c02d10250801a014011000c9541815100e01c2c0d1030b44102d902d0503549a114101054848ad02001c028883c91855504410744c2d00140c0014602104030015203000503140310010310746103140034000035090000301d0b081d880c03010140d807455030760b070a0003030290580c9030100840b0300e242200010540c124604a4060034010780103003480c40143c404a01c020030355075500ea1440580c40544c198044903521500941510510800b038480d421031040780000c013200091241960300c10045407a0030303040030030300b2060360004862800106a8404c13050449000301c12040c0a031090152404035900d4001014141000600004415981d510340400400c522158009008030312581d022a5800d407080b04842d031f00003403104026140655030f59500e01291070031542a519900048148802c5160501900c4140c00440d4001e021140c241 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 445965809 1250 445964559 445964573
    0x211a0405101403030d09051b010903030c170903101e060f050402030403052a0d0c0f0308060102071a070203010b0919020c10020c010c0e042d020403081908090a 70
    0x3030003401504035032000e0300302da103903020030440c0e10440c00e100061284406ca0b1170010b5403a2004201e00d55516580c200384e442039407289140b0400c0320b4160ba92014407030050b480307c40c580c407810b503030510886608200601154600700320041c0161000c080006404030342c55180049000300c40103c5180c241044410410040440211815100304850050740c079103462a00703448034418211443d8204903e250040e40420082c1c4820756400c1582d025030351840d20008085810b030140c1140280884076034600700010a2150f0101580310714180100c0f50555212030280443c0d44a855405070814800150001142000c1c02864440c030000c0c1c42041c5c007410a42c143d00003440304144c13441c15490f4081004411b100c000c21098481c99070092003155034030141c61085000c0d0844410301004100000700420a50526124480d4a2005004501007070906111413a0012000c0700302c0c648400d03024072000c408900500300406030f8800005804e0407035000030b140506100c8004041d101540c00501002c0003107030b0f00d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 445967059 1250 445965809 445965841
    0x1006090b0f0f0406050910031205030f1302040b0a0f0914011214010b19030210020f03030612120a0201290105031605070b0a0606141e0703211a0405 65
    0x100301e40030380302d00c03062801090003401145d000e942d0041081c014020024042811142907902501719000d02c0512658155141e10040d908010010b5009001840ca0b0354181060240c4c40d20051020074003818000000f1515640d98200c50340c5291849410099207050344941c94022818101d45042c035854041a48480b84800c8030151258144c00b00191500c4020341c040030701403100500c0d015080d01e14140303040f8000700b6800100c2c000d585001160b02c0303407030000031150300100c418001146590348403000e10074000c080702d503031411612400d0080d0309440c0810025101d0745c08139900000c1d0318280c607810000100e1038156000c000c400c1c054a824240d0b44c1c4001101d5000d01d45440d05000442a02c0040307405200741a40030f0840a028400c0c000c0e00d80854004908803525a80e0b0f070f5614100c401d051190a104003080041110300b405080b03410800e600001d411700341d0103810700070f50001214148003001200701c00f81170349455070388071030a02c0c000011940d4032509009170703810800c0d072901d03050140c42581 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 445968309 1250 445967059 445967089
    0x1a0901050307050d0609090b070c240b091806060118230d0302010e070902130302092205010903080c0c100f020c0a080d14041203020f07060e1006090b 66
    0x800400598840c1c01403048413082c0b4250001001240d680314041e00040c078240c007048030902000004500c1080c4203a05204920790802c00001c40c6100c81c40e609000708410900d01e42801741c032850842525a0389010141c81001a0212001c00b00707881740c200360516030700800190500400400300d40e00c134045019100159060000c0b006600c1031070b400100b00c0341c620416156804036007403210340100356044d00600e009000f0310045076101070f210b80d4440164001c0f0242c00c400b203840c65500300058942043d0f40d80c0c014400311b40b51130841144c4140443d00581d411000d403400d81d1110381500070150311000455100709059030f101d091205508401c6c5c0c403449400c20003969291251441d000e02c250660450f403a8400c69412103100388c49070300d0007100c19000341d165061300f64502061a0541c89282c892280b195502c18050b1402d0855001c05400a4011401488040b032044c003c00d00015514498a454080e444000f44001012616102c09451a68204005490030b0070740e15021038560601c02e04401c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 445969559 1250 445968309 445968317
    0x31706031f0209030a020a091b1d040f06120819020616030905160807060212090a1a0918090f01090c0b090111161802090d02011d090a0203101a0901 65
    0x390f41001030710700014110007135801a03017588005000c90131a840541d5141c08102c542c0032011034070304242c65114580c1129005c1844640c0145041d20700f560103d26021020382000850944440b80a40c00b109000c1c0c0c216090000004c2c94058842048a09003058080d0b00c01004a858a02400c000341942c2900c084141522201008100034040c031840000190050300b01d030704240e9031b011a690703608da50b20481016010f4001210414100a0b003165681d68016111064080c9084010303828580784404800e1010804e20082d2920b580380c2000d041c2e14000782072604080e0800d10380707203070404001c130b01158030071f80c502400c900c0042c03401c61410341100c14100a260f00c4094200c0181c420171070480500c6020300809542e00c0510041881040c00e4540d14050101e10600380b010510480c840c80040583c040c0d201300e100001588607034040071905008040407401405040c000c078200d020309948a810a0703130084100410780110040d403000130007401e0a03202d460f1904140c8a41d46100707031421a030402c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 445970809 1250 445969559 445969567
    0xa111002072117070e0f03030708070809031018030e0103090c0302041d1903140a080f0703020d050f04060b0301021312020a150c021503010b0d0b0a0b07031706031f02 73
    0x1440c000c40250748440d80d070f8088407a192601020080030385401d03c2c0c03418403030032003c10442c400d801c00109591015a01c0078100d40707410a01d440701406900b052031082da051040180a10641c0424003414030044041801d03100d08003400c0ca0007030190b503466494a4105807034151b00c0f101060308a890308045079010f641c000b401c4023401c04403842c0310000021b0401207119958140b03007007510607103820680c0390003591920544080344d02030402a02c100568140060710b0780d00403030b400e6003510086ca07801848504006141c040e80003000c1c015604203c594400008000c0100010300025000f10f9042d00340440086280450440c54003071642e88900807502e040da403e071a86011901c400d00c10602800f0146c1e0f80c4400c0700c0740b03041d00909031b10812030708034010081140b6011804180a017a00d0595002000940c01c100301340601a0040000f81401603009a24050009030700e0044401021280d00070b949520a00410a009407103654024102c98013a900c041c9003038502488a007594140a04014000f60361 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 445972059 1250 445970809 445970873
    0xf03030430120b0d110909010903050a080c12010b1c0c09060e04090b0c040911040e0f0403021e0c01030e0304080c06030a11040605070605071103090d06060b0a11100207 74
    0x7001450030b101d82221403410340c00700b4007941c10004185d8110440315640681e0b04d920030203003612104000100403445c1803101080c1ca5007c0e130042c035400700458a146007081c0c0844481c2e4282c680c2a0300c01c0401c2d920008084071a00d0208450b0b07042c8041441041c89840205000140601c180b845420f0820480300c07520b40d0740d03035200d03000564910b401290b00c094a00f00303403a050007654040d214031840c00e441d101e010100030351401d090310200c54401c5044a00356503500540c14403014000c0c0103d045000d40ca141c111840c800d46034412400e4000d800501010122400140c22600f0203081d00c07196038000d000070021824005240c003400101628419101e8480e42d0300b00c0007905070765400d10b1942402150214440360b022001c5c0002c9801003009000c82c0d00c0c0c0030401c1c2c40b0740403100084415070704200541d240f1401d0203000b02201c0d44c4078400014003270343d131039855454941041c00b43d44002000f0881410010000300603031056204800f10440c9044d5a42c0c1d1007141e412035040c0101c28100340c040010368 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 445973309 1250 445972059 445972061
    0x30c19091d030a03290a121a0103060501080708060108100c09120302061b1e0a0c0c0f05090108060f0403030b0112020d060f090606080f040c080f0303043012 69
    0x38580a41411a52161800c02018000c3c10703407480c001500d0410340c008600003e200f8174204943d444003610b00c000740c0c0d00b840710500182c030380300f1410740760050021034850704001c10703000c118001d42c01003100160b00d50519013041d060149035031100d07145900c03c50046c13022913804200d203840109802c40c0052020261101901c07040c5082c1d00006800c000d02050000b85500880c40303034031034039151400c1c410920310300310035441501600805026004146044c070985400c100020072000302c1b2801c000d503400d100c6949010883c07540c2d8101000b0301c401c0b417100f0046820400f2140f030140402d0700140481d0701e0702010444080500400c00340404d80c5825072400c0e030780d0245520b15888501c0400a44d40c40d66421880d50280c8028420740091000300000010303001120700c100c4081d00c11650300e51a10792540c0c126202c0b00e000150040c0e0303502040081c005245141080341c501d034004100003441d207178909824025044107101503207406421a24200d00d0100110501076040c9400e141001e80e42030051401d228 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 445974559 1250 445973309 445973351
    0x1302030304030b07030c0914150d0213170c030a110a0308041212050903070314010e0322090903050702012001021c180c0308180d0809030c1909 63
    0x1a415020008002c401e02001850ba1449030032251000e01100c1d5072460101c03528119441a00048480703864007001a2601d15481e0401c94405404a81040b100d0500907080ba0b1240c03d503e191800c142c3c0d41001001580000e0703000c4004810050b151300e20301040425160000300c0b8004104070100b02da1007102d0b980d03125403400a103400c030300455121074403106404000c540c034041c2030303400c0b19452981000c0144101c046230064034001e0b000d03042151466a8400d281d0781c2d100401c0d480d954840c2c040c0f50b00400300b0400b80080200314901d0258400e4201d240c0d81100c00c55401034188503040805150103e0f40003411940f200d5030a06c1c05130750b141071010805a6405070b0100c0c05696500020b5542420050024510203a200a41b02002000341d80c4a40c103101c810307813501c01480c1c5040385070100007050b821300150081c0b6400207080d1012443d02000500c1510100340100c0d4815004136480380d46040400c0004040354054030080219121080034991001903403003a143c000740c42c4d440c451005a10000c0c00c0c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 445975809 1250 445974559 445974563
    0x1c020108040f0501061d060301060b0a0c05030f0a050a080c0a0e1201150303020f0d030506150a022107060f09030206190605090a050117340b0304050f0d050f0d0513 72
    0x2000143e40b43c025440421b03001c411001032807410100420954034041c0709820448019503407080c904400c0078002d841c8400c41d40c5040d6080d000a1059540e4000c41a004001141080d03444a40d1018681e0018003003102c060300002c0c02c0340c0b0501151200c19000303103484007000e5084904d0f1180d1800720300c0c21405044003181e00448990040000030400d600066007000c88100c4100b520059080300904070100c0e10704a85141d803284a80e04251001560b4000504030541980305442106c00328044840c801d04050301d0b02e07105883d0004d0300c6030078440c984c415144820382d0714000340408451510000d41d41c490151070003c43c0d10814240c0c40b00d80c0041d82c0004028500a040b0151916120350904000c140c00d219a50020301040304c642101e040104050707400c100c942805012070003460740210000483c0f0b00e80390b107090100d480046880c03007418010710300c40da02c68401440481c1c800100c0c1c60500204500400600800f4002c0e000d0380075681040c0c80802003003800c002080e03511000c00d00514100c107800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 445977059 1250 445975809 445975811
    0x30803040f20030c0609010c11041401060e010906050703020303070e0f0312030901181707050c090a0209010306152a141006150906051e0408010c0e1c020108040f0501 73
    0x501201c8805880b540302e00e48044041e00e10180c0194140310041c46003c01031800510100e03c0e02c0c0004011420340c0c5070f082c00c068000184402282c840100314a03003031304444c006c5400200654090341e8803100000240003546041814001789a03400307552400050a054144603c5c0d4202898544035a81001103200008084a218403150405980e41e90300c00c0c0c990651650901d030000c0f407903d1032122011003007584801c038070444000d0302e84040703c00e40118400f150740740148041c4040d80e81d524081280115100117005aa50303011900142c12100654001a5010702003070070b1900340d6030880c0b4850613600400d00104421f100044031140d5900c000340d002440d460280043e19008180010380381e4a0403c8000108202e03920b40d688024402c569a11000c00207543c001c013804054420009816041c0500c0301c11103000c102510501d08a0b04035800c64207081c0c2d1b55001650f00c40e5804050031040030010355440e1016181100300d114100043c1c28040c1c140194000403500700300744c480004c1c41860300440 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 445978309 1250 445977059 445977083
    0x1707031107090903080c03010803030606030a090b0f010618080d120e030307080912090f120f062d010f0506090607060e0106060e0609101b020d140607140301030803040f 74
    0x20b18030000381080a070603400510040c000440045440d07040324160f03005400110f007540d0300c0780208121a0b00003404460203545440310700c00058101043e05011301115941d0718410340c102000200400318a59500c00c01d298105020001d031600400c0307c003003c0d541d80c030b010001c00d401e041c0c10030080d2401c4880400c6038072001040014880c1e12102150141d11461b080c0c0f1449400300c03c0640725400f075140d030240c1c01045440d000c282850a03280d00c00300e00074003000703441000808040d86414420211079042034044008a12403500800110700a0004641d180d08920381d41401714108103080341c1d006440c0588000039850b0300301d070380304026074680513030200e03080c132141f01c1e0308031054003a06031403180201240700c05801040c94a07020064070b005000c0070b04007a0b99000c4e00c9800300c0704818203140c5902c034075850b0604400583c5884034003000300d902a05001018840f80d8042d00c1c54840014400e10070000342041d460703d150254070440781100e411814240d16522242042c00711a800c400c2c00810800e0481703 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 445979559 1250 445978309 445978319
    0x100311040f1d0103030e0108100314010507080703060b0d05041109010609090c09060e0f0114070c030b09160e0601031b11010b01110c0405090a23060a02071707031107 73
    0x1200d140507240101c2002c1d00c80000e9007095600580c0a01005011901030396155080354410030485a109403103600119284e55203854044500c42c850700401070a0b51a10b080201903500101c40035005541840c0c100189803812501e03e805000d100c66060398181c560b808a424022100c02070b014a681c02000400c007565555400b402c441d816220b00c45025040c0003807104082c1c0948001d0085401c02e88419a00d00b60032001c2080b00610061580d0501c15010130428a201c0f4200251941038896504405d01d5410342c02e00200d85640101328080c15440300f8050052200b4040341d45040320640c02100d01580c4448005034040c10f107150320040030341800106008141c1d41700e100c2c4101181038000820071402c1c00001101c441001ca00d40c803096601000d1410420704066000c02d41c09041e100c25903091084507590200c002c41601003c0e12492904541c00510000610030345401001400741145400c1c0595100005501c00324114118a00d000c51002c0905001e074001c41c1c0c0d000311207816907444540341c3d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 445980809 1250 445979559 445979579
    0xf060c040807060318030f03060306050a150b090315070903240b03121602010201060f090225110d020616080406020d17040204180b09030901080f060f10031104 70
    0x1600c036903a41441003002c00a0080d010707215079024039918040083e080d0099440a80704101c114a0407010540d0711207000010505500ca541d000741000c00c004224001c0031042544500e007150000302d40c0b24000c000030030003a600000c4200140c0200d66820130b2958030340f8025500c5205651016103072241e6202580009000d01072040f00d42e0f80403c4080281203103410a060f07568400e508102d400ca001001502c40642245e008001034070320510002c61065140c5190a03640c1d046640004001500483e482301e0300028010010032807000301c42e01005184181e19602041500c012200340941c4075507502c0d00643d06d95000b12a40201002e03d8a0114034091400a03070070f0b807180c0300d0351005020301c1000c244000e101c0d440307401500c10150b000710701c15120364080000420203501d400c05070310346900d07001000a0440741d01c94450f5000750003031507e600845002400310b6400524410050306d00c070040040039691144a02027451003910302d020040b210700360690040244a000e0240c0c99000700780000c2080c50 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 445982059 1250 445980809 445980817
    0x40201030902030f120a17060102121e0f180114040e0604180f0c0b040305030d0e010e12040603050a0509100e12070f0c1a03010b070812072c100e030f060c 68
    0x1550380b00c03041f14602c0a082000b4000a80e540345c010380080c0001541c034001440904240034480035401c00c0140f003040f15103441d50200480003006c40d00840e04004400325512102e40301d410a0900c3c0740e8801d007984003c06a4801c60040310025245000411007d807241d905c040c1001000303428000c2c2202041c10710300c268a20800040f07841020306100894809544815103044a620000071402c10282c2c40601028005405540321251340c0c980054801e010104451141c0c2c40c0d46c4c4c0252943c460502c0c0006040d1440105085201d5040c4818404140c0d40006d00c441c041c03601250004c0c240c205c80700580d090850000381d9240140b00442c41c2380c04d004001d1401c00800d8460300c00420110396a407034460110317079451529500b411062004108101c130060003401054400d010307451901203c4808180c1d400c03c251150310010b050803103550481c0c940e0b4401040340d40131000e941108100a580050103140d5030240c1c0c4420410394468070020780d207080013801a50304403041a00e1451628111701d0a031900 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 445983309 1250 445982059 445982077
    0x60c170a030518030405130f110a0804140106030f0f020d060f021c0c27050d0b06120c0f0415080106091e050708042411040f0e060306040201030902030f12 68
    0x1440280ca400f6016001003164111040074004142049041101800401010362001600754460301e410650216840041c120604d0507110381d4128140741c1030184a84441000c401e015038540541440801d10702c40b00050084e50200ca59958141c071413010030003500000f14002c040e01d0500ba201000c07003c0640180c0641032160721a6140f50503d00803960903980c02800200c04a8540b0b180b240a26803044074800c8042181c40124190035600c60104050821445007500c50641900504c0402d00c0c0c0a03c4181400080340001c0c202200750200140f0f802c42c3c444501407085556440c072011178840d42d00c000340102400d038002c22040d0b9440c0004006091345002d019440701071003040c1003003e111403040c14011000b41d0384604140d039959490766401c510150001c180c0c109114804180a03803240154500d00b400740b41d80c00d13241d40c5001310301242400c07280c201c9000c252214003003002a4400050b40390344a502441c3c04074840040340082400c0c030046406034903090003103000d506c103904036050060001742 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 445984559 1250 445983309 445983331
    0x5060d0e06010b19080f060910081501060905010203284103190207020105070b090d02060627040c1802090a050f030c0f01120608160806070801060c170a0305 69
    0x3030426013045600030012981641d41d6458000131414a0608a00c11039100001059078181c10342c1b2078000900e861400c0e83ca0f40061062400180609603002c802a4000c143c00c3c0002c500b02402050303481e01e1101d0150310645541c3c14100400c4c0d042c0d10910071242c50002007840308010321071110641d440404a1032200710b102d50841070742e099601c4d6200813203106a00490070702c41a06501c400d080b000c0d50000c4d009a0400506000d02c40c0441d00038290580100e040800801020b4010400642040002049544904810391400d1003c20a041086a040b042d04400f1951070780d59191841030170041da084a8030300c0d0102c0c1d004800642060303008000302c1d2811600d420502c0e68074002c1004a240128080740c01d40c01040c020f9085042042e40301075900414109441d17203d1540c0e1000d0704551702580202c00d01e5112030903181c1c0d000c0e040354000002c0c4c480c036806044d4a00d400e2a0103000108180b040700204144003015a0074484003408060214102d146844d55911100000401608050b02c1405480c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 445985809 1250 445984559 445984597
    0x140f07021212010f0e2502071a030a110c030414120d0807030501050d0f060218032a0d020108010e0415050106050d0f0c020c010315050301060b0a1205090705060d0e06010b 75
    0x1400d80c020305c6485007090031448200201c1e209408003101c0000400d0800f9480b84600108402c0b10086905c10200282481d460710b038581138200c6015107041c00640702844c481007210803440300000c800c4800f0740d0310303810414581403072010100701651400c070394800b1f0700e00508040b1090740e50301240190181503559814009640c88004000e110000d10000600501d5502c040c500024032980251191400c2a841c4000e01e448420220342400f20000c40003800301d224086c400c07030324510309040303c01e00303130040c0d900301c446d8401c036400a03107101818040d401c50000034500240c1040b000c0d070400c0f54a02c500010501c02545e40b4000541140c1203103004090301418600b003484e900303500340700310415110b13141c2c0104031405d103c80c015001004c500d440031030002032007540072519482c01d0080301c0c018512021019506d22981c040104080c01c40c1c012209814102010302002d8000018990140c030b4049603801d540c0c02c0d064110704018100c1400034900b9000746000081d00e0700101d0701400610620190a43c44 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 445987059 1250 445985809 445985819
    0x90313060f12050606220807090204031a180d0c0c0b071203020906040509010e06040513051f090f050d08180703060f1103010905150103140f07021212010f 68
    0x440703190004440300180400110a4450001c0d800c40ba82102015010520700500c001e04400034210307880c250929032014000800502508001203030042600d0f1004504160865848401c0c00112180408802100b5000701c0d1001e00d1503006141a01c1d01c15040b0307605880b40301c1c0064108001c415045d00c070103454402c0040c103690a07804548a6940c4000e900c040c012006d60300fa4025004000c0081c0c02031001c0c0004103030b41c1c03141e09903540030307190400c030f1351125103030660401c0151352004154250100302d1800030b030b00040e4000340140a980d4441c980802107101403007100002c050790719024215847d201d5005c0c09111000c110b40307108807c1540c0d900f03401d036100740c2420618100e044c5c0d05581d44e4400d047c100b0100d507045d401440140c94240022603074406585000310702d604203030410074009a071501480100b0041c041c07a40380710542800e05001080b440c6481b4909802c5c0141550380071446c910008015902c24032416601c6547c80644541b680030003070140c68142000d0040e5482c0c049403200100f0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 445988309 1250 445987059 445987067
    0x40e04050601241215080d1112090d0618200f0a150e1f1e0201060b0a1b05030c0a0204050105040b100c080405030d12051f09022109031306 61
    0x11110b403c1d445100f031042c8103141540007001d80d46100d0725482d003001c2010a0304141844141d5142c022503550240c0c0080e41251141000c005042601140e04c08001c444400c0d10342c0300c40e0740e60301900944002201ca4058143d05681c0f05d00c807000801c0311101d5448101d00d033b121402070b54041c2c0c40a071038a0780d00381060700911600b0096805510b00c40c0900b040c00f10b81c2a80320f602c42e19030500000d00043c440140250028000400c1d25541c00301061080051040b402c0310b031400f0701c0000c0b10b244002c0c804180761a801150b144100d420080c20000c0c0945100101c080c03080544001e81e500000712603441d10101c0049885188801b030483c401d03070030300b000010145040e0040c0612071000502d52080755140da0340c1078500c040c4461080f03a00300c1003880005000e603020300001180342c46580342c26103142c0c801d1001d00700700c038801808503510085081c0b05503c41201c81c0c4220b8103407080e80384010ba80c1d440704142151804184140f005a80380c581d01000304080010018040e18070005004030b82c41c948a0340152 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 445989559 1250 445988309 445988369
    0x210302150402061605010b0607050c091e070309031106040c061b0b0c090a030c030f02040e010c080402190b13090605090c09060304030c1e0b010801020c120906040e04050601 76
    0x2030751151090000c44104c2e04141d181801140c40f031300001805452110110301290881c88081e40c0309e4200a056541d5414014078450b4020032031454005103044980310084840fa004d4400010523a5415070a41014007170340301e902c1100060002c0b10543c2c0792601d01aa03546070f86008210019501c024550307510a20039501c0c85105e544181401260740c0c900240c025660080c0f51030b190b00c050740c0d6500001044c14803081d000614016656480c4110f0140107001c00c0d1003400007000000ea1400001c281202c2d0b004043c2a0003d030b04840c0310b8840040c466245070200708941011000e03010028030781140d00303441d03105001241c003110b40501400d41d44100300a0b188004561002c030000342000702c05260703d0080011580b1500c241060701002c441c6440e643c11151181c20361000080f00c0d8021308e001c0c041d0038007000d401480d01340020352400c0e5205807403c1c2c880052555080d204900851250300d00d507101015240601010860400c142c40c0c9800d0240da551700a1244400b00e031141e0f0300c4845e0b0004505c10742 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 445990809 1250 445989559 445989563
    0x5040e0d0519050f1809060901050102150901021909090f060b07080708040b0d05070e03060112080f12090d030f050705070209060301060504050702030a14040608070f092103021504 79
    0x14506046500d25889940c0c61050240003c00a041140100240e00c031006045003060b0003111081580c800380c03e1001030400685054458500d00d001080035a900040c482090841c50540c5602070310340c00050360190286c00c49290072190041284100240c1c003041039411540309030010310010400c1036070340301160384c28040d00701d01c200d04014050200d1884401031241790b00c1030790b56030300c3c0c10303a9402c40494039088500c18046554880d000d024515a00002c0320910501c21030103401e85525005148107183c8a42c0d000400500b00419060901c5c0c8010054403514600408038000b2460034000007500c5811035940e0f00007103843c1148103240d05401d407041c0380c881c0c03110740c44041c83c0400f0740d0200b00103c1b03401001290f141d92940d901103a240c8640c06507600a07201c0e90000c60301d514580da0040c0050050940da480802c0081c4810481c0341e50025100c0d0b000003081c1400307012101c07a00c070100c401c89429005203040e0700500444d00c45414807000c40d00c0b80c0300d00903400d407101c400541000000c2d00406a0300 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 445992059 1250 445990809 445990817
    0x327061f151b050f1902180106020c01031d01110c0d03060e0103020d0503090d030801090b011b0b070c0803091b030c030709020a0203130905011508091c050d0f0605040e0d 75
    0x9503207001c856146400203d0160040710340c1101005201850000b00081e2012581d415889800c11424010301140211090000d030b501e440d8140b0100030750f26880f00814604040d01d403101c065003000101d100c1510196040c0003840f241e03e5030011110240e020480e4401039102c5c0d00e4107070102520078440d01090303900101400748240d10710340030429802000380c0c0540c0c09000c01c014800f965a5a0010303284001e1080d100c0c0b03800c643c9403820510484119440035414000040042035050a90600c08056550722100c021040d480c0c81008540c400d58000c00244807850000502840d00c2c4001680e0144481099015504010390000d0603140c6004a160a17007540c068002803008420980143c0840d10342c520440341400d03281d0294040380b140c66800250455030320707001800440c00d0403003e000c0c0c208060404669074280081e1666032080c0c90b0304404407140c07040c034841d0b0485101d1012250480a5802e061001c4401e4603802c2000b132015114440c0b00e1864540c58405c030b80004103030100400801c0e21 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 445993309 1250 445992059 445992077
    0x50414010620060403050d020d0f0b0307120209011e0308040618050406050609130209060406050c060a23060f060c06070207060806030a08030c1b060910020403080327061f15 76
    0x24040e01d40340c0095421800094003807004842746c1403240f042c8070b00eaa0b007240e000700d60741c4000420705003001810780258071445c58010403000542c54080b0000c4c11140d10510b481484000c21402c44a1801590401000740c20000380008015030b00c103401c0b00c12008014035400e1443d0741c480810086814522845c1d4104909101c040e480d4545000c82c01070302d6030300c43c2c4d001d4901040c80e0700141d001d40c40354000134045100411820b035810340402040e0390054042c90200308507401c0840558007070f0261070f00b0303424810201000a4440d00c0300c80074181d0702040505041c0d1214200103005440781002c41e03048005104125000611074480c04600d0700444006c1e01505c01014075072503040082d88024095010004100440307402c0003e40c0319045441203007000035151900b40007403158200318508800f401680d0040c001480840e070b47c0d004503030f00070b402c0f901c014004500c5003000c1a940029002c2c0c141050144204006410000d42c0c04000e01c6a410903800c00700366101c40d078041c0414940340351030f000926514 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 445994559 1250 445993309 445993313
    0x82a0907090e2229070f170c04120c09050703020409050f04120c0f0f030333120201020c0d0501050115080c07021c0c08030d0c030911190504140106200604 68
    0x11303510040300c02604600050b1100c188810103255074081e80d541700003542458680f407145603c8000c8408030841c49121000d682000c85c6003d0003070140c0d019040e51881d004030742d0000c21000d006588010043c06000340120300e08050058000d41003332081e01e030b446090000260004203e0340c030f424030807a0b00c40002700107010a00002c64484c1845102150000000c0c1d54920120b0400141c070020716110350b40114800485001d9101a22241412090000c030b0310b0140c420100c00c1e4841c1181a17558644510200605600040b0b2603d03602c0c60318580c009000311451002c2c0a01900b045050310f20020501a00e06a4848102d0b0b1262045541e03e00c0590f0902031040180b502405003042c0060011403140803c0a03503c8000c05500d8560115001798000528040c540c02d0a010b034511000142c2800c00902410340c44051380d500418031031600c501c00032602d9500035212a00b522001d001d000d802005255050251560600e03000c0c096000411070081c000a070450300303815520307a80902e07103015003030325100c0e9 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 445995809 1250 445994559 445994573
    0x60a06030309090c091e0b1c0e0a030c0b04030509040e07030c1d1326030a1401120b090304150c050601240503040303090f0f0c08010501082a0907090e22 67
    0x6144200800404010024015111801922381b4581c101b400176046030280300e4003030441d510043c5d00482c0f50401102903000c01e811240c2c3c0c00c0101e07003081141105541d2898111014401c2d20130907a40180782c080101510080010b188041e00d110700110340480303448050b05001c41d540845100307a40c506400009010b00c42c3c0c640c0700085144100708084008d142c140d0440c914020101e901d98440b80b02208106103200107000d2106043d0b00c0c46100c01003541807920312604500c81c840c01a101580010101d1020070042007150024100c80c400b0b00c41c0ca600da0780d801402c1500403403050321584503180020070010b807208101d480a0880c414018001400c000003035407030703402c001c0c01501455585c0f0b8400001c9040703240c0094000c0d1050a6546e040f00403880c0c00e21a041c0c40d5049682c250707240c440144101180058501c82d000782c80b514ac03658800701c0d100700d03041100c80080910b800606130002e0042058001890074182c5101c0510400f0513540c40f0440b400d10a1446607001e1400003550700f440c041403017 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 445997059 1250 445995809 445995839
    0x41a190f1202182e0e0c090111071508090c010203041a0405041103040501050f07050a03110c0f010b12030a021c030e06010b030a0c020309091f08060a06030309090c09 73
    0x40502084010010f4800402d02d4210032214400c0c80c8401e0186402065031103940e031103e0414041368079801c0d1341090f02200b4200b20017001050382c00800900c242c00c607800741d020f56540305480c204070b132122601c5d108401600105032116101050724030300402c10b070f11000704000c54007401c103074004c50070a80381034000708c5190b0300480d030003825090030407003c10207484502a0084038801107103656542c1c1081d00e4060708690b070080090310244040818000f5075640982201d8409003e440d000c100619010f180002a00c43c00103035281900ca840e441c500c43c00c8040d00101c240000c101d03119800c04900d40c030100e07100e100d800072070401600101a1000c51100091120745504e0b034074500080d034480c480607010300d0a90280c0096a4844011041201d4a5000d00601101d029140301540c2004009808280c40f040c1c00b81065861000f00ea0b80b500c40384650b440560010306200084a806051400848006103803d0009800096200030040b603946030320301850900d6107580e07540d080441d00e45038011103c01d030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 445998309 1250 445997059 445997063
    0x3060f041e030914012c040609050f0601020708070f0b1305030a06060305010c09050a0e060102242d060d0c0503010f0605190e010e0402010c02041a190f12 68
    0x300034400046030300d0303911040581c184a82c0301d000440d410105034008007104000520b04112900004595442d409410765010f290015440b44200c50080c002074068811500b000b0b146624180801a40d182c00c4a0110700440080c2c0a8841460b19004041d40340c4d50140515148200c014108120f110307007400007000044003050002c0055034960002a09200e03920900f85c4015407a41c4050090100c207100711646120182410180345140c0b0000c208407003081c2c4140b51a059814000402d84d900034040c0403a01d11640d46241c4413014844912440d04030b040c1c83c40c603100251440c01d010001648a90101100602d101c04546542c5800400400041017001100c1741c2c0240f0130001176680b800d0050b48960745d4405804102c16040030300780141c203040c00040b042910190401040080e00148201d0306440f480c00070814542d4072400140c8011007032a400a4105203040380c00380c070725003100c145100c014104030b4615010080f604040d0b00441107a00441d001105c0d049030810840d41d1903004003185038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 445999559 1250 445998309 445998323
    0x60f03190b090c0d14060102071a0f0309060103030e010c0f2003031c0b0a060816030212011203020d020a050c0f0103060e0702070302120316080f0c1c02100b03060f04 73
    0xc0d14000400da04810a49140d5800500811300d50b0906005010312091030340b40074142d070821300e0903c0001356078009520610805001e60284000000c003e0400c40b0010004104c2c05a0340e814507140e1507a560000b4801900080c030325140c040403d40c03003010840c00080d0040c1000341c6408060322215038141c110b20985103038011041e00510152020301c042c2544e81d071140846208000b115001c1d40c10f8515410440d44600e031461b10030f01500d60040502030b005a1480f0303850840800d00403040d0001d00c10021118480c0f00c0007000001c00445aa94010f200ca01c00d509403225141c900d402640d07120000d03000280582c00407855900d1500300141485980d5905141c0030403460365503103403040e103100160b0f00b000c01a0031040c4280258200541e204226100240045150421911540b40007107040c8400812100300002c508403012075100c01d0381e500030080800d41c0c00e00036001c541000300c817211004041c00b500030099400c00303a100510031002a000302401034815561b60812070144400b0040c002c460704 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 446000809 1250 445999559 445999571
    0x20f030105060a050d110c19050a1e080408030910170f0c0d02040f0302010e1e010507020406051e0a090908030f090a0507080606010825111009110f060f0319 69
    0x180726402012159024400307a103507140e212035615400d01c8c040380c801c0031060b10a4605800051000286422040c0c0c00404074207078095142d80c50001c0c80e00602d40900580d41c0461f010442d10070120003049100401c40305244800c0400f241500c00c28407040c1c0c0210780410358030002e0740e01d04002d030303006a1101480e50190f2030000200c0313460040380c0141d00842000c0c0d0002d8014011940c004540f01420f500031a10f500a0100c203628a102c8500307008030650412401040000c1191525003010020749030060502e0103500c60b9010032003951900c0001c0324410061084005440c404901c114080c0b65089402075146030fa0702c01c1c5404401d20064840b10551281440200106500344484409060000040e2016040181c001040c02001030a0940c4030308401007501c800c0785882031a408695000d00701564810241c80700242420344818013800e00c0350506003041e0410129038202841c161040b42c216400e000c00405112080c001c1e40742d800e105082c104045614032403458003800700e1804d072400101e12 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 446002059 1250 446000809 446000827
    0xe0102010204050d2418030e0f0d1103070501031107170f03010b07050114010f031212020d0221010f06080a0e0102040b030403020609010b2404090c090303020709020f030105060a05 79
    0x1410f00d65481c152441a034443c40445a092110410076440386542014446e0b2114142d5a14903070799400001001d00450168058160f241c080410004410041ca600d042002505140842501c10001107229001d00400460298064480d0404160004110320b007040003940d20000c2c0b0303104100c2e010312042030a01402002c48070700710007140a0b15200c62090313203904080c9031403425101c1800301c2c000c1a00d03040c00140443c0095402000c100c82d0000c94100002c45850000e0b650120710300c000141d44d074000100b00320005415001013004045050464103451807614401045600038082c502c12040030b05410080c0074461005141c1181c20080002494010f01001608a0740141d0100c1100390002c81003106258040c000340d640000140700074401003590b0400100801c0c030703042010501d041900303c0f40041000c44420741d400b5080803402040310707150050000d000d07051680720440051182030b00100791002607000b43e845001a400c80c03d402c42e405d0004001c0325801040303200d07007000003d00070914 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 446003309 1250 446002059 446002069
    0x20604120506010b040e0408030a1506020d170f06010503070203120403020c040e0604170d020d0e060a060f061e050c010507110118023a0305030928030e010201020405 73
    0x1004010055481144003014a8480d0908105900003280302078140401c225540b40401229446580310f1072866503642c60308c507403200807c040401c3c02c0a040f20104007041d003640009541c14403020359100c0120b00c001c480c01485144004407080c011001031a8046006940194086e44d002903040c0103590501d80d0001004109200880b0284c0043c0c1c02540d4020340c9062502c182d00301040000f000e059145410340724114919004845030044040000e55600d210078198141c43e0015500762040c041142c0c0b5817903982e1344010a84620801074a4401d0008166545111040465080d43c44498880f0007141811014103000160300c030503c1010860784920711428880c0a1080c0600d45451011500c2003842d642180d200022100d4000200303046c45c00580d44584003285400c0309204c44040303a03001c2d1b4a890b2908445078040c01881d842c0f9002e01020960003001562040000e8070071106034004402c0010a0b14848a10056034002c171141007a000c203210360320009034900c06000261402d5510400f1038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 446004559 1250 446003309 446003317
    0x2d0b0604051e04050106030c0e0d0c08010e0102040302030609010207020a060c0219080a0c06050913110c0f0319090605071506051e040f0b0f0d050a060516111203071b0206 75
    0x460030b0924459150640c0b8140c070900e405070100c3d02c1c04000c94141031402411071010400414821900b240b0079a003003041601001003d81014402440900003c0c0c4865004c3e4005001c00c900c40d004e510001a206001442034400c1181c0040000c02c14600d086400e5070080c0042209076004600310040d43c420111403100e001c0203044000080c190041c0a08000140d2811900701d0f004014080000c0286a921240d146004030110322002849440031482c4d100e0502c600b0303c42ca05240910308104012580100103070000403820401143c142c06890b5003111508041d010302800f144043c0069400b2410710130f0985604200f045000030300c0d42c0c403440051451200f41c850179a0113103410b4518606801d040c0507070241d0f00d002c0d060a00031100b114002541c510401c1c92150b018115509040d414803200b04180f003040c1da0480010899400c1c411030072401100000c600720003095081852504003080000e08546a41011543c07509603120350380100c854940b1800c000d4900d503408050400560b442000030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 446005809 1250 446004559 446004589
    0x60c1f1a131b0c15060b0f09030f010513020111060601050708180a030c0906080f06061014040612110304031d0307082d030c0c04111b0706032d0b060405 67
    0x8070030b181c2d5103140601d0104040c10946144d1418140208a05000c02c0c00365881c0c900112a00360b203817906500071918001400541c0045982850280a0031904440301e03094098000c1c1c0e9444400d80b121554079940d0307441910114000f80007004601c0c00b01d131a20010345803d004c0000081c0704103600030b0010303020590079041510155910881009042064801d00c0e00600d03005015045200c080c910041e10b8030002005140104a01221280d101c1d00c680102c20000340050074103515580c50b248014061101002c0a040d1207240a854007561050042070728403c03a8566140203401d07120400b403200c0c89082c40003407509031140d03020203d000e510610084090858200991401a0340c0c40c0142c0701c010740ca54600c0c402d0b900100544404140089440d00c040301d015100891250f521440c181024421180980392000000c24070035509600480d0140c105c03001540e082c0000b1034016041000d0f07018044182148a214492829000d03986800203041d0541c000c0c00c05090540d80c4012807400100c0301c0d40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 446007059 1250 446005809 446005817
    0x403080a02010b190806130c150305060310020c06060d02120109030203180103150603050c04050a06020c0103050f2202031002120121030807030b040b060c1f1a131b 72
    0x8400080c20030640345038000082d13000300455546040318441d00c1d088080c1058206070301501c2030409000a4010081c01024025900181c6a010394802401000c043c1c860a1003030084223040a16030000380243c520204a0201402d4540c88080070000c512902250498000001c584000c1003158203100e41c40398103000b0b801031179992052406502115038003c1a65042c180781c200d90002600b0689043c40c250341c002e040001e403540396003000c03500714011640306680c031054070f500100e0455404103050102c60400c1e01c007484513846035241d026664400f224821307000303c4240891014141403600c0048103e00182c00c0e68241d04818038400240d074000e20a40c40200700c82c01c0100822500061001c0401c900c0111004c0c54501903075008202d80c42c054415001c0645805480c0c80b00c1c0c1d6141c0c0701041c454001010039642d94100032409485e144e00320715041604c9601d002c08400c640a60240081c00501e0341d10f00d02c8041500000c000660411001007801c4598901d01c01040e01051440d031000c801072503e03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 446008309 1250 446007059 446007071
    0x140103060503070b12090a0609080c3f040f14150304020120160810060b04053a1b0504090f0212031204060b04050705070c05060f0403080a0201 63
    0x1506680807940300a020b070740544070402a50300180f081d80d03540c80882c80307541550340301c041250f0b10b8500d07065030107442d162904030802c0400482d40000e103001e4600340c040d604410b113145c80d0925214420f9810f40480c041c0f0400d4241000c074a0f22552610400090a040c2041d0b1124010b50032004581c00c600c1c030310f1b240a00103605078035000e000c1040250401c14400d1543c64140d00081400c8045900c080ca10020540d208103c0300d0103009c1001440c42030348141e03010590703c0559695a140c25440700c014145400e07008143c2d0212541101c09032800505050f080c3c4076900305076008605420710303030041d139a2145612540024407e106a8105000302c400c00048a0305c299240200055944550b21551801c24017800003041608200520341e01110140c0302007000032189400c511821540303e40140e07480c0d0800042100c15030242e402c820041e9070400c0160707540b000c203032854030907918060400c1c02c84c81c2042002d441c0a100030501c0c0c05010144070b06044c0d80b0741e03031001103422018030000543d44681c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 446009559 1250 446008309 446008349
    0x10e071509050307080703060b04020c030705060a0b0103091a0a0608060717010b3c0a030e010506090705042d030f150b1c0204020c030406080103030912031d0415 71
    0x50080c001400d0100c2c044c0c08020301e440344856848119120050403a0b03154200c0e0041c1e0343d01da45c1580c4444525002340c81d6142c2c403e103002a1101000c84000d05007620317041d20322030355512a1050a00070303031b4003070403525060001070003006c3e070000001c20020310691940c1010034814804e1200343d00a18103611201300304182c3e01c4508001c0c05c01600a2188100c0510510158480700b41e0400c8220400220520b40051489841d074500c1d421074910100c410b100003405e10406074503034040c090b407004034002005142c079a00d0800000349006e443c250009501071005005404200c5450134011500f01c017a040710b0f1411020350303c0f04e4007031a07005544003000092688240080700500c0b083c4909a400200a0b10b1504070024031039030f221100b58001207071440200030864075242e040764100c41c10502100e4885c0d565107070050103140240011400a65000c6000641c16041c51700030030f07640c4d45515074000c4a4000340462001c440300a10441e882074481c0384001e249028144c1c2e050140164070f1b0541410703c42c43d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 446010809 1250 446009559 446009567
    0x50f03191e050121080a03060b040b0c060f09150907081914010603080d09030c060513140c060a0804030e0a03080a0e010203090303090108070c1a1e10050f0102010e0715 74
    0x59102140a10060010b0803411500c220404c00340d5034008065034031840b54420490041070180c100c0c0800e880c00150115005030041e001e0b0401c40131100c125000c0d50750750520801d5428080c0c40c050b40b1540000d4080d20000f2040a009900c040c0323007400c440f141c682d6040042c1c605008890108118019844100140050084150014049140244801f40c81c60351a800540f04a100c000b2013a40d41d103400c60205807042c0b031103010b2107410800070300c1141001c00945811614010048810b40c1039070f40580f031090750220ba044841e0100800341c41c2001d915203c15a4440b1000703100b00c2c00c21040045207030440c1d40301101d40703000e94080e408203602e400e2a40d00140202243c440302c54103550003403105403503640d0008200d600101c020302e880c80c0c2e00d072030f4501d0965030040802e600605904038002c0090440c040c240d02684a1181101000400d1184140800c2040810707100d000e1030908065080c040742c20005022001c01c0d0301071000096500c6a910642d0411045401c00d12400352604900c01420380e00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 446012059 1250 446010809 446010811
    0x308090a0e040201090303050c010e0601030804080609070b04050904110d060b012003190509030a0308040b0f1603091b0609050918030307030e030706110a0801080607050f03191e05 79
    0x10000511007142040d4001801062461200404200c0700040c013841800084d00b001803d00312030170849181c4c6d40c4a2601030f20b942c00500036102240b25504c00510040f10020f0f49000700e849c0a922a0715203820034003805400d6400400564250309034006103015034a401c00e81310345441c00360070000740c82c0c103002000514140140b84440c42d42d4181c000786401e040310200455800c2040203441001d01c3d240064180c6d16409204403295050140600213001d1640140b0114402d40c40f8151840356650340a00e005600e40301503a02400500c4400c0340b642509000340d00c001025401848420018400341aa8028401c000d41200f07001502a0508100c41c6c00c1c645900c0d80c000c82082102a08071943c01c210940d42c6c000205410704164640f000540758900a104540c00d45400050620003903e049040c140c0c2548403001c00c1c000500d90720000030315100c4c00b0502c0d5000381200d43e0b40e0343c03070301c50001081c2015400c098568418407110314000c2c000c0e98203e20506407008100b28200100d4442c5003a003d044803c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 446013309 1250 446012059 446012069
    0xf070b1602010204051003090c0b161103010504151505041107030210050f1605040b03010906180b031002070201051b0601050315041a07050c100b040b0a140d0212070308090a 76
    0x8018401070001ba075580099410303d500305d240c0002d0401281c10502014912988080e50200c400180000158101010b100c0203502032a202e0781c400d04107200341401c03518201c40103000011181d210b100c82e00d0356034005108180f58229210f03c0c1c1038544000900719078000c0540041c106000440c00d04041d010300c50a03107000032120b000c00c1300c0c4c602100d0001190800070b209910840341c40740c00f8807100c1c0c01681914050004024007644a684800f00301c0014003050040d4807900580e019502da071644540900c5140b100050043c00303207801111444c2e4043c0d04090012814000309112240000840c1e98028183c0000c4c040105043d51525060500f0000710f104582d4481c0650000c200200700d640c4100c800940410008000c556209582190240103041011645000340d0b0580c0c042c01c16280c126203a100300840b003c0040440c1d034000c00c00c84803464803443c500e90540d201d003a0302502d0040000d4040e28005031410410020f80c1c5a010f05000e03c1d40c00031a1095400706040f922130421002981c0506 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 446014559 1250 446013309 446013311
    0x314011412210906070f0521090109030602030a1d03030a14010b030705090f120109150c1d2701060e040221040804080f0c03060703050f1801020f070b160201 69
    0x740002d020108040a101000010410024006445403181011151100c2c3c000e040c040c19202e140c60039a4a564044030b02c600300700018000040381d50fa0383d031704594006105171240340300c19140d585d40e60040d40005200808159480703841c1c1404806540490b0400c0d018000696500e10b800b0b0400300803a1300c0482d01c00159001c00d4014000c5105100441c2c1d040f414900b0440d440e0303c041030000300f00c520100002500019142e0400f5240841508001d80d6203106a040c0300349240100340b2001114032b0703000c1d02000100484400242c041036807002100750380e0040d00408601d240c07100c03135a150034005010810440500c500400200ea8042025084200111420751a00e0359007044400112a00e4007012a030302c40d19000709080000010407200103044000540e40d088141d111803d40381c00c01661803074041c0c041c01002900e924800d110742d91091104025104040d15600364402240ca81110104d00540d820046540d441e4014030241012511508402c1100c1ca42440c044500c181c0c000100f400356 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 446015809 1250 446014559 446014573
    0x51608011203050d0f0219020d08060d06050c0903070e0f010812030619210203010b040603050a080a12060906060f02010603030e13021603082502070e070314011412 72
    0x38180100702880d8042d0145001521000000e0b503200003000d0111440b0b244500c0018200301041c0f5410003110780e200c05409450110707003100401d81e00303080200c50341350b0301007002c07249036002504640c8065003000503226041d08245004010074940481900150600400380d010804942034160505024181050103040000741087d42c49000d03010141c2110312480c0540550308840b11a11042030013418115004042c192286411007440d0585400c10380c0207500b0031461400781c0c06d041c0100022203601c00300400e044141c0ea06c13203c020380c0110500d0810096407c41c0b58204852600644000c1d0110901c00501c2130301e4400c01928651442001d0029a41031020800101e03412000900c3c000409680400030101c01d036000e82d00a100d0307031140721903001140d982c000038580d129243c1d5209084480401031018903c8003441d080c00d026000000059205031010b1203000c4100c11074075000740040c01d0101d828081c4408000e1030081c01d030021400080340041c162410b2070540e4180109190305030240c812 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 446017059 1250 446015809 446015819
    0xc1009150c030807031a03010908040603060902070803060103092301050117160e0a060b0f040303080c040e43080c0f0409152714070516022205160801 66
    0xf12003c000c09070000c3c140d880c0000e01550380070382850fa104c1e01c0b00030001c00114009144c4007071141c21a0140394002490414042540b040d175101300c41c0c44e143c105002905540d60000110054507401c41c0481e10045401702c002032007504458003003105c0e1080030010030998100303019521080710b200704000c456806410040d2118840300d08420980c1c6035441502c1e155036810081c0d03c0607190a5100c1101014001441b0600340b42c80000740007624400c1c1e41da101251144203540d42c043c02a400346000d01079289020502c03581c9201800da118442c0321410040200c4024606000c010100118150b9511940064445180c1c496042903100d4001c0b000c1900380103031000421b060b07000d03501480640603a40d15071501001031150f428001802040031051400310003d591004d8098101c10421805040c005101d2401c01052001486078490f5515203090540440e455600c085401d902660070407010707000040290a15134402000d1854044041514145410404810400c5401200030018031200600c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 446018309 1250 446017059 446017067
    0x503010c030902131d0304061e1e051c060608060f1f0c020d0546081b0303150109080d02070b1c0207200405010e06060a020c1009150c03 60
    0x1910446100001041a0710b01c00c5c01c1e10905e403100300001c036480081000601190700512185038400072900b0803800803a800003e40300b15030f0043c944007075024a4019108600d1281d000f52040d1100c030701c0081c10024404801c1411a4000c0d00301e0b8000811050801074941040162100c0350442592104511540d00341c400381300d0380034517003c9410498030000c5074080d580c03506218100160003405403204c6130100840302c50341140d080440900402e03104144c8810b103907a241404003085000620891520080c2d0710a6041d5101152100f062041282002d50340301c42080954801c44000c203c460428540b50f0000d0f002c650030380c2c070950981d40900b00c3ca80c00d69a0205102048428a80354203440d030700c104250300c1c40001c111210050041c03011a0110600134107401801400e600e0f400039074402c04a040c248030590f0800d00866541a8500e40070922904101000309540c0710f091050b01c18554842d00016501c0c515140924006a4811420700164504040f450f1055045041088191000b0764000e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 446019559 1250 446018309 446018329
    0x30506090c0405150708030106180b0a05041206020c0d020303010f0807290705010516080906061f020a0812040b0106020601080a02100e030a06050411030a05030f210f010503010c030902 81
    0x6001c1c1403a2503030b180c80122180152080a58050307001b03070b10703982c48680051064805c003042c107800500801c00080c9281450007103800c080f003151b542524250400b502d81c1040c42491800311040d9500b000030f804204e1090040244800a59020390307500d5140a07942c2d5542001078104070310903040b5880800c0401d2520961030343d031905802000000741801c0c071200410780100d030320186c0107500305400c008150003124140c1101c0a003684803041036854506410b0380d1500112144e41d0845e001c0341c102c6035210f120301c424510556142c0f0407221244041e1382c4e0081541c0203006101c0039400c410f82840200000c003108180544124401014150716003444c50b0303540c1801300f101a0260f541e5082c0076a1240c0704150310070b801c60010303084030002c5010f0f2608400809044405407003001d00799407540c030580390205a608210b80c205005504004402c00b910302c0c1940304180100040038150201c644412100a58602c951508121480d20390b01d07080500d4255814101101d081628020410740103a4802d4021 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 446020809 1250 446019559 446019569
    0x1b04060501022d0a0b0103150c081506210105181303031112090319020706020d1202160f0b0604050f1518090a111c080f07020d12030506090c04 63
    0x691400303000c10300e03480c0c000e004090383ca00150199440550a000750001c2c0305040700d1003803246035207403103a4840542c1141c5131041800f000a0300300c40816031100c0c1e04078403080425401081d403403404810f07010b030b0901808a120000031080b5020b004201c0c4d403500404007070584e10f250070424414940200600b014241c400380040c145561008014403807098441514409d01118595046c9420f1160440f40d4036004100d00c00032160914110b820020b2000c1103041c102e85881d00280310320340040340c0a0f1810083c2a044003580d5909202c944488507680c5034412406000c0c0d583c2c50001e15035420281ca1a00c401000580902d003000c3c18003c3c3c104600f6285d13a8896520800c0314403140c4d850001811030303e007d6800c14803440c00402800704082c00030844801c114411850075070600c04100901141112003e401015156038008410120300d50350001e1003400300143d1601e203403140343e500042454000300c0c03017030741c416014944120700c4030740500c609601b001d01119600b0b000c0c5450b070101110b910840c024 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 446022059 1250 446020809 446020843
    0x309060f0c070c030c361e0c0801030b1602030729011e121104050615041d011e15030f060902250b0f06010903020907021b0406050102 59
    0x5041009407029202100c0d4000c0014400c03954a05188406405c13a0080c945010203404264030041006036a0780c0ca5a01070b200d150740e40d0414049110010f100501e01540002c0c5610280f0591004034440c40c072078910700e600c2e942000d5045040008120381300820f01d40c10506009041403a00344c000058404190380a000705c010051403a84000740e003070000005024a01c1c0e0000040b403000004100f005402300b107262020080b41d9601141200b1400c4810054040c0d0000c60300b40b1040c1c10560030071039000e040500700080360900342c20450910ba00641c401207aa41c01c1140381e8582d0210082d49034018290040c030202450801c1c070007901001041d124841c0c00e60344590704d40500f24001c0c2c100154003101010104601540c031004a4080d503c201072051a0500030b49908200d42c04080c009804079030024110103c6680390407940c002c0b403101911403418800c2c00340c00003005079900c1d10b440e403288a55602070b003032064880440201700300060121500c01c0d41001000e100e140d0b400a4040c54100c00112 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 446023309 1250 446022059 446022061
    0xe0a020f06130f1a16080313080a0305010303020f0109080306060c0c060d05090c12030a0c06060f091a0612180109020d0f0c0b0306130b040603020619080a090f02040902011206081e030309060f 84
    0x48c5030706540544140140740c0030000c501e03905400d804d0380c09141200d00070b400b5181d10901c04903805080701c1403403400400c1000103101042981c1880310250039146820003c5a40030b01440c1e0000781103400900380d46000c00e42716010040101001d20600401d2031054580340c0154400c90001900c3c0c0c010b841031007081001102c49407050140070b030454402807550054100c0c801e5113550711500a4481c2d01d0441606400d44001d150b81c504140e811140f00d0043c0c103d0b0500c580e10386540c000794034928004664900d6496608100159441e1000d10425501c90b9111403040005031800c180e80b010268000514400180f00300441034a4034061280c2202c100800007074100140b2002500420395038001a410680226680f094500003002d80311800810b40c8550b811643e03610240000c0d1028542c00900748200103590100608103034201c489068070504107255252552a040c5003142c2643d4400a00c65000c050204035000140200c040390b4401c000186103585042100903030b0703c0d4005011080c084240c20 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 446024559 1250 446023309 446023321
    0x60c2104080d0203040c03020a062d02063904031e110103020903011d01020a09090b130f02281101090b04020d02030a12031407030e0a020f06130f1a160803 68
    0x16141b030051079009004250854440070020421090400f1464110484e000c603005020f20004481c102507000c1e500400c8543e40f001c0405082d100401030140d0384941581ca244450030821070400c0011601c4c0d48001c0e280c501c0c0d800d04042900c0d070058089000542001403001041f095488961700c81c000b800d0243e07496041c200400d0040c4049070210500070408800700c21100813740041981c1e208503030703030a02c1940d00c40c080e002c119202644950391000d2284100650028590001d55035200103140041c141f50345200110000f17200c0001800d580c000d030680c05c104440d00014280702a2240304001c0007115140d07500d800b03a4403000b03003019104030400400c050465800b00031040220781e00c01c4060f500b010150001402800c02c002c80007640700171060008903558803910401c45c088032010020300ca030700207603003d005056000f0300c9025003084040100300c881c01c61540d41000288001202e1410b0240342c0700c91102452001e1400d0006404100006140c1542100510510b40e0300b10510782c9d03582e1105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 446025809 1250 446024559 446024573
    0x1030213090f05060405071b0308040602040e090c011d01050304060b120a060b1008061003050c09030729030108071512050405010c0206010e012d08060c2104080d020304 74
    0x140e11041c80c690612100079862140c076000b49016074001d071424816500c4189040e107400c80f1064810351841c000030107440200c2d2103403c83d03540160141c41e0051609884081d064102042110203280301d900a26191029580c804400a450310f0f018106504501070500024441d200c09400509900d48410086d0f140341e0b00c202458510901c2101150740884007480c040002d800182c00c1c05104403009150490b001d0b001d00312103485001e0040040206610300282a401403502416280e500380b403d20011010391010012240a04001c1c0c0f100031208000103041440f18400070f0b140030302018140010820071100103130003005d4915a15041c610f00b4584c080440b244565050928406400c00c4103200500a041d40312440c8070700d141d401d4500c00c0c4c1c1c9072029090701000a12464080b61a40e1906000841c2402403140d201082003c0203403690740c1d56000c81d8035240c4150b803c507201c030000083e01c0499045240100b07940c50183e860003072062902d901e4041f050301070702c92201300e01c5800000103404c005031 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 446027059 1250 446025809 446025847
    0x28060309062c0106080619050a110a091403010903020307080304110411040509060108061e0112020d24050d06051305010c120b0303070f02010c050304090e0c210705010302 75
    0x740181d106a826008845030b10351810032440c560254070b00796001c1540d88020800e14802c4070141e02400701e1802ca0025500100300c003c017040030b4655544400b0f40b0995601000340301154a940d01e490415003080941c03030340d21000842d064841d0b80750a03545c000013074010098401c2550041501c0d51070355a50b0418a200c070481e50741c1103603c24600000006c1d0200505e015005440c007e45100c8416602c010040d181b008013500e213680d00c0f4400580e498602140503401803004403040c54030395104003404081c1400c0c4d801c8242c0201c5210785400642498207200f204420300001415082c8002d645401d0110f13054a000b100d010b02216200c4c00041c1520450300d89602c3ca95600c039000700f00305030b096140144583c541c0cac01d5180045040003d105024900042554140f80d00051591400b8000d40d00540c5c880030084012a070a00080c0000215020a446030304c0514852102408400c0c03401d0701008055001c40a46440d084040c0440c04008440001d1100c1601c50070b080050342c0d00c00c071107040000c2040c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 446028309 1250 446027059 446027081
    0x904210c17070309090e030a030e0d08060907230d0c0206042103060302100c0203120c1009020d02120a110d110103091b2706060c0b151c022806030906 66
    0x2040031040c003946d0704000020400700f00c3e04e6038100144102404287e07140e044021120002a508a011800b140307002d822207500803041d41800303000c0f455007180c1c0c0d00c45034110100d001070010002c034201204a08038011503498404500c080e0804e45003a5581504420360300c01ca90403910700b036040c00c0034428000c2d0702c480041d60700240064140d00303000000508140080104078080d0144030000444151000280c41c00c00c1044009000c94078018207030b00340140703914a0140da2204d1a0207203a409a115141854600320000014002a107410b00380042820440d4085500460449550f94080f0300c0340d405203440d14209103800f040807002800c01803100315404c2801c0741d01030640b09001800c1d206003101c00c4000a44414220103a0340414801800c07600700784100000700314400c086ca4005904089003940c81001c11140c15050000f44000c507107030034034640104110340c201c45060000e520f804800703c0101b65000900d0100403072242d4140400b034509100c0d85060545401e01035081000c1ea42103414040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 446029559 1250 446028309 446028311
    0x2503091b080303040302010f0204180b1315081504020a03030e0f100f02060a020903030a0f09080307030c14010501080d0e0a0b0309011b030b010507200904210c1707030909 75
    0x1615079244a8990f48140e5046015618001c15408507010a000b5902214824020004c00381c0340040d441c0040c08007007070400d40c004415403410b1440181d5100d0f0b81c90016800d5451a00309003800292454082928004080740c0c080c40304010060b030f0ad9101c5a425030342c2c10f182810190b61580086809261203041e42548403801042008066034040d02c803210102199007142e08030340b107180401c02244148071900d81c1680042040c4008540242040d1884840e0ba1408000c415520070f034080c01e540101d00c0460001c0e24168040d400d10003d601320241c0c145840d8002c1140b54505001d0300d40e942d004222002c01c2c0700251000c03402c19904c0700c440e0001055410305180d641c0c54805040c1c1c0c000e200c049070707100c0302e00000001c115030607129210350211140181c440074600701045c4c03500c07000d90702c00a00c80001c24840404240b00382e124441c01c1d80c0907500c9101000f04444400100010742807030100040308004840f4182d10118001d540300b92085003129401c5955120241001c441c6d081060704541078403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 446030809 1250 446029559 446029613
    0x910020a060c050309010b01110d0e03030c0304080c0f09130b0c0c03030411090c130e04020d020612150607030909050c040e07020a0309060f0f1d0d03050c0105250309 73
    0x80b50b0010b00071031164106400070480e0119010055071110110700351010b4503404074041c08070300350050ba0341d85c55002d402000c8074241009814181d1a540c0103400c52461604844009000c6041030076600141150032560003440c5d00c0d00d25000240001c0d001c40c05042e01c0c10550202d42d00c082840100c0b2000170150080d42c0d9a07160508000c2a04a040013980340128604800149000c440006880d0b4141c00c1e040308034812440d0114408210788060010b80e4090b2079034181c0d00c0141d8640b40181040520148030340709601c3d1007003850300e00c09058050742e4080c101c10080d030000240d00110040c180d038068140002d06071a604488190741c0507580020001d51039041c2440b18564000680c01040c500c80d54484100e140c540748211802d07000ca049007000b0a101210100e221409210010400803107202e02d55020400b100024851240380442a03021840004072007039842c10a00401e03a100ea180b00e4040300514881c08150100b848030f043c502c08040c1c1d9440040308014240000c1c3c5900d0002404244003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 446032059 1250 446030809 446030831
    0xf09060a0f0806060a14330706050601020708070b040909062c0c060406090621150512030301030203060c0c03090303120f090a020a1206060f0801060e0106090b0910020a06 75
    0x1683d403040d00c00600c20301c400440040c0c0400150701003940c40c0b401034420750401001d4100d680c040c81e402240317021000301d98042c4940c013843c0c0101030155140240408940741c05d28100183c1002e00b1500042c41641000400344100c03180354040728100c03400f5550000303c4d91201e0404400400d1800218031104149149002d224511000600c054201c584160384001100d44100400c6100304c1c070840c000301d490010104011400b134458010640b000210003502d005d0007404503c00c40303608d440c410024800c104824090b604084208000a074076803002546194116000030350303980d000402c600d04503680016400b15140041c000e070307290800098100c0c1c2c0c4400c00724258400c0000b0844040b1580000703080060200c00c00040d50048440c2c004d042c0e81036050a00310b00c6403140c8030110082c1c50b8591242e0000034540581200c40c80240783e040b0000903a5030511409080915040c3d0261080109425007800b00740f4119003203035182c24040b621300e154403440700c1d81641801d031101c0d0083e105c01c0c036103100f402e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 446033309 1250 446032059 446032063
    0x1030506240d0b10030c02070f1a0306040905010615321303050607020703061103041725150507050a120c090312200a08030a090f081c06050d020f09060a0f08 69
    0x10407081247c0942d4003903900c8026101001440d0f20480a03a00384510202d5415074942c00190b0300480042c1010554002c503031101401d40300550f010001503d070141003010074550100e885130f030501400c00044074013030300361641942030b031f0315410103040d04000062002e421003040700da100000e40e0b000d810380d01c45242041004e5111915484299022401d001c046040d0301140c10440340325551103850102c54588100011805420140351a0500040710020404bc490740102481c2c1647c03103901c110100c0e5000c0e05903041520740190070702051080900403c001c05030084660544001c1d10240003502941d0340740211641143c0e9803000d00411a403980c00c1c030307046520a40f208480c85120f0789022102c8182d904042e03a4030b16106010300000014404034001ca525900482d5255006641020a03100039881e94900c651106c624154040c43c8041c01c02c843d6451802001e0041104503207014040700340e40c010820321382c6a5002c00d0b229480700340010b540c40e510a02a030028081050b02c60a0194580854a0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 446034559 1250 446033309 446033321
    0x1005090909250305031206010908011406100806150904150b0705010e0f0a0b13080313121b0b0901060905150a09020301120f030306080d0503040201030506240d0b1003 73
    0x141d0020101501642c2c0485190b182240e5100e0011441c0484078842003130600406030003c0c0c10020084030001d101d40c1c0034011600c034000036021144050078003508004480003801c0000040c0300150381000701a0b503035007040c0c0210340c16118500380d882a104002400400002046500080ca00100818038008600c003415a040c40f60000b0008601c000b90000d603600c43c0c40304018102d80c4661240c10000d1a05d80d129600480d086440c0e4840720040e81d00c0e40c989801c1164062101d8103481140b000f40060803803504690035a904064210103124004660107958600b0701500d16064000441c0340c0e150254040c1c0d00404030044204401e043c075a0b00b281660707446990700f5106480e808000f140b80d89052080b40e040750151a20040107644940c1e40c410a400c000106078180342d95060001041082404090150b2000350398040c3d4078a4a0300c005011528040c21030740c003e400790005484a4140f00a40750f81d00b0395003030911500c6014210141010386802000381d9007180c151680452130ba03405070011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 446035809 1250 446034559 446034583
    0x7060804021c0b340203220602031b0c03060c031006090b0304022403010b030402040c030b130e160b030702010e0607300218090619051005090909 64
    0xb6241003050000792880720ba40c1008003a06111480c0c0c0484c82d0040d80a8802000d00070399004070f402a05800000c6008041c002c01000150300300290001a100c0b19607081c581c02003501410000203401d1001c0295a0702885213a5100300b0418041045942402c020006103140300808403481c81c0303443c15a1400c103410070b03101b589014511b0007000c580e903405000d0f60b0095a11007954281113644a03000c20403920040e0ba000c40000d101003001140001c072100080d800780050310f00c80381e42e0303042c50b2050004440ca100824410107182014403030a039a200f15180010018440d40820744540c1c289800381080080c03000c0c80415401c417100040c00b186071002030b500c10251a002080780c000c03840d00a070384604048134030030700041030f81c0001d91a41c6464045988030101024209410740c11a0f04c501c41203910a001812500d034000140614516040e0965a07024409550206604403160000e0100000c1405810b1161840303064960b002d512a8048d00c0c14070310f008200c0d100c01c0c01e0998000c0c0c0c0312481013200c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 446037059 1250 446035809 446035819
    0x120316020d03120c031415090c16080d050105240702120102090604031a130302100203041b030305120c04060c0209151f0f051227010c030e0709180201050a0c050706080402 75
    0x82c0c40d800e47d0341c0030b0a01040c00900b0391201c0d9a01c51020341015404070074080042c400e40c00ca001d000c2103801c03014011080305032000003120350418042064070710014030b003094080050701c03c01c4022400342c010303580039a906441019611030312f4079a640c003a000740400d0a400540104e40001800504182c58170b0408100548a42035200c500e05800c00e543c2008000c1c01580c48080060300050f010340c003e59015006202410000c5d84c0c00c201d84102c541e403948260005040030420803803a007a081c00b49a0030401182450f4a030a20704603001d000d80b11b0000020744a0800700d0000f4124903540ea14094080d44014543d1603600300c0244010305013582d00300000002003840001d040d0705800f52049135401e02d4900c0400540d580c1790b8103614a0007100392199260743c444200d503c507842409004c3c8940c2d80e1429100800c082070324582d107910b8070007560b20020004c0c0c108a10034103004000c03019060700302d40a00c1e22039030718041d046003942ca0143e102002005403260682c0055400d80c0402494002c62080398 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 446038309 1250 446037059 446037061
    0xf0e010216020f060901020316060207060c050a02160f090f0b030102131e050303030a0b0409151a010315030602071704030b01060806060306010206011e05061206120316020d03120c0314 81
    0x1003130142a028214186000d60302c100403504102e1500f02c08103010600c1104c01514005690361000280d42039820b80705c010840c049050b01011b0f80501c9840501c815903c22010080c1c07600c80700120910311442940805603035550314403041641500140b00e50318020b002036541d00716207002c001030403540e4800c0d003041901c0300c03105c410030700d189410800880300010011811500c032440e00324000c1580450040c0d001d46d80f180040000344e042c00c0301225880807c071002441442d05160341c41c000e401491454105498032009154289440c40c80b030007966008040140c45124900d040d640d0103038401629607040f80e01141c0002080340002c28a03041c4e0341c0982c1d42004a0322000140105400b0540701d55015801081c014440341c4500c41645c1c400b41d07070700b0940740101a0b0b10408510182d1180000314143c1410030204404d40c204072868481100140c00203500c1c0100ca40c00410503035004507002131103003503414640f8060500c0740700120984012040300700000005454003400a0032415841c65184180030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 446039559 1250 446038309 446038339
    0x30903131d0403081305190b060a0b070b0702070e010f051003181101120e031305030703021e060415030b030709051006081e0709030c0509010b0a030f0e01021602 71
    0x110003192600c4031521400301c242c590342d03001d468180004001c61080c50107180d4201c0820f9007000502c2c7d1410a00640ca81a00080d044c80e1299810040005029046101c010001401d40d0411600b41580014820449480d8201d040f0704014490340401c0d08060064004100000c801c5112002c8030400c443d104415402018107405455240307100c3d101e42000003c248010460700c01c101040b07520140341072010185010b41d08011038540d9180a40071703034404034200030b039283c00d805150b0142400311f00402110f403540c1d00007600704030b8045141e118000034900004158580c442503402509107071a100c0410b82c00001c000f8010002403903114132138444d004d80028807990602c52a0300681881c1460401641081c00595050f2400380c9982100c420b45060072480490342c40c4001d001d031400e50740d2a0f54280c65800c2070800c014003038000605c0f0760b5001004001800c106411600c50022504011943c4203407940b400c0006c0c44050706c05482940001959495104042c1d80d141002c0d100b02d8065203121040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 446040809 1250 446039559 446039579
    0xa0f110a0501090b010e01140f0409050c030304090e190506131e06020705100b010905010c020a09020d0b03060c0a050307030b1212030921040311190306020403151a06030c0c0303090313 81
    0x45d002568000f030091303270b030810b40f0b0a05401000c40107003d2001c84a8150402d400b007403450344950300c288091640e460b05a44607800c18008410200001c010f021200d41507501c0781d41d10381070b0142038900151107510b031081c104130aa4403a80f900400c1b0040386a00a4002c1c1021401307944a0801100c0d1402004082100320007144203030101040183c2d9922030250420005445104030420305030780c8003602160004143c1d0030384c002801ea50000041c08a07800c0602000e0500d032880181241d101c4100a0006d200c065030f021040d039500250614012803041580c0010818605094041c3c000034001c00324004020280d007001903009052481c200c451800c684119015604900d41390008081400c000800c04141510035201550500510b41c1c1c1054400340d401107510049940b044610343d8000c1400c0041c444031b07103010441004008024402002d00108107408d90030040360b6588107600110200303080d00900400c0c0c5200d40c00000881c2d94078100030b82e15542d40d4010125440985150900100b02c050103 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 446042059 1250 446040809 446040839
    0x4060b01170a021803072303060f061e27100f0314010615090e060108010302090f190906061412100f02070c0e06040605060a0f110a0501090b010e01 65
    0x618209042180ca03000b26100103980300801d0225001010f0102401e5580d0901041d401010040152216500804070710013035103410000607031003500310004108110540140c1990700c000c04845a1035220b500490940240b45030725540c035049803110200c14054404003030450102c0d02ca0001d04600c5545070080383c0b12582e414085d400000e0354211080001031561a451100302004600101d0342c19105e6031001c00c900e1680c8224000181103607000c10a0f01d0710b5100711a044034003880e00490543c1590040399010324088e02103e0b1981d004800600c80741c03c038460000c0d424420079401e001c43c800c01d050942c081c14581c014183c65902080c9102c10b10b2a0203038141054072071120140031203903c40b0208c0300c0105407080c03100c001240c00304114800900e48040e118080c0c410750321700b0425814000184400c56849401c041d00465017003000446458200d82400f1944280e4075141c40d419405ca000ba600709001d61384010000d40c01c120f55502003060328045070741a02c000c0700c5801082c1c0e980386400112801 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 446043165 1106 446042059 446042087
    0x308011d061e03120d090506060f1c0302160b0c0d020106030302033c07120201060522150603060602120903060a0905071d04060b01 58
    0x10004030030342440c4034440004618603004001c19540021041c610030480311203076903400580d4040103001079010a6541c020303125026441c00c440035040c0c40404803000d0044000107111800c00c0700e0340e42d0030f4140c010030300800b111150001070008614010146c0842c051100e00100c10b401d41810a0005c2c150381c0c146582d95138850441904100520203e2011a4142201080466800419201581d1500300c281c0280300104102404056256104500400b84440302100c504400c0002c1c10384d0340d0141c900004203501806040b070032200b0038082d4992040740080302d10710400c2e1405510802000000c400a03502c00079000c0c00307240d0003c0b0b070f120304006a00c0ea9410f100c00e660500100c000c4240f6a9442030802415178002a190800100840b00e09079450001d5004e11804000c0305000f40340b241031395111800a9042c1c2d0b0b0541a04440503243d007414051110055407003030250343c40c004 = true := by decide +kernel

theorem cover : BRFrame.Cov 445863309 446043165 := by
  have h0 := BRFrame.cov_init 445863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 445863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 445863309 ≤ n) (h2 : n < 446043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
