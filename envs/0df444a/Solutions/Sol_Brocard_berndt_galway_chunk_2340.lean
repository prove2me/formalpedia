-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2340
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:25:06.817387+00:00
-- url     : https://prove2.me/submissions/d25cfd7f-fa4b-4fd2-b3f1-1bf3e9e67515

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 420683453 ≤ n < 420863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 420684703 1250 420683453 420683467
    0x41e082d0c011e0c050a0803070201150e0a0c1101060b120c0405010804080a0e0d08071a06010203090105090a240f17010501111f020405040501090608030921190201030b040c090b 78
    0x840d854990140a01640540c3d5454000d101f0944006c40c461001d6400038045000b150704002c86400c1c1502c14200c04908910114859540503000b4941c4e10703c1e02c1ca04031000701d40360081242140ca07141d002d0026104005030041c1d4030602c1d44034850b800340f008201103003814a4940080d28103170000307100814545002038514403507809008160400c110190203010381e101c6a2406190070b0b444900140c4440c1a1180c0b0a07a10310240300d443e5101d0f10060380690b0030300c0d83c3c000055540b42c10400e00c0c55071006414402013519800c540320140840c200c0c001003168403034500c0c005020384480d103414004000320024000d100e20340648415046660030700e004241b1042c2003040d00d050120441d240a0b00f0301d074180510028480c2900907200307540040782c0403c440e90f41c4484060032158a0300c2416020342040c00306c16464a40f2800920348551f212040c9034050454200c090308000c003202c40800605500c030700107403d65906210f2231001400544040019101803140500740c440e05109410706040009500 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 420685953 1250 420684703 420684707
    0x20040b09011809050f06030f1f0225060c080c041d06040216060c0f1115070207031401020d05010b0304021305060301020d052707030305041e082d0c011e 67
    0x28100824500f9010805802c1040c40c0b10200c0400782c0e03c2e07500c680301f007910351382c0d50060104684086c9803100320100000c0c0540b8a9030806500245002c007a8400518100c2c40302c05400c04c0e06c1041c85100d12400a0760004025018014100140120707100c0b04050000b84102010340c00072a1340300d004186c40034060380e02c50002034064800e84007009900700302d00d21058100015134004aa29080640394401c514003410400c4458a94201c540382280e0f01410600d0940219050199080201d41c030507101220b40320b4a50f168501c2c070502c10110aa0f60000f0300c225642441d114190140c9102440c140c82d504140c1c000415040070811622801607961000c00c103980e409504403824030201071401e000c01c1ca421994015403458a00c1c0019401c41105a1886120740110f45541030701da16844050900b800c01c100b446100c03920b145502c826444c807003c0070a2000c1d007007007401105840740c0286000c8548403540c21280507c4610500b1080c1c2c00070740038803600d07a00b100300340f00c1c01261501095540d240840c81 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 420687203 1250 420685953 420685997
    0x30c02040615030f0b12150901090812150f0f0103270606030b06010509100309052407020f19081809010f0317030f010b0706060b04080120040b0901 65
    0xc001c42034402c000c00039001540541140003c07002c03802081102c1e5622009100c80c520b0381031840d140a07003001c444413036180c2c4000030b41d40e04000f41a0000400e5010742c0e0722070500da4420318030300d110008443c040001d01690002400822001903810b0003002341e07a90081501d4503c4500107038103140e101d2058400c10141080410000c43c10301001001381d40041c14568024100c5010640f0010000000900c155001d003048401044015110716220300050804800800005004980c40d0003101c1540040984c6400050b00342074991146151504003100040c0c900421081c60300c9490304081800d2220000703d00c0c1405105800c0002d2a80d580c214078599800110b02c00d0b1102d41c401c041c18000310b140c0d020a12040282e911907003050302c10607a492400700240c00304848002031440318400601c85141c07440301800c1305501c505404507956445a0741c0000c160010713000060169580c12031242180340071174000c11400049490b4916150070884103c28910a01c09290306002c140070844900e0006810 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 420688453 1250 420687203 420687209
    0x50d200301020a0f1409010912080f0f041d040b071202070507030c0518041110020f0a05160618050607140709090308160e0108070c0f08120f1003030c020406 69
    0x85503102a041400713000c0905503014100000e541820218a80c43c007102140d20145058542c025603d181050500103003502800495808000744031002034102c0f0000501004480910125207642c10041e40d802081c00380144842298000303030038880070a60071403413a50401071500d4004200320701c00c4100c402922071402c0c010039a1150100000520540081e00030507034904441c1402c420740c1018010146000c00e0700e01410700c0030340c0078411407030f840c1c1821a944a55041d0064030400c0c4c610880d03c03810103042040075145034001c00134551a00b0440940107010340743c1030401100030003510605540c15411405410f00901001601a0070f200b542c608a1440d60040021510a140c0394826400a030290a608030086000c5002050710740e00700d51030503501070509580d580e52a0302118011543c11801074004020701c2058481140031900c5076401d070300c40314004c5005603031324440304038001c00c49035005006038200321002c0103100752440306c03000010440390545443c4e06100d2803800024014007141e4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 420689703 1250 420688453 420688459
    0xe1f1a03030d020a03060f0308040b0306010c1e0302010c051c090203070b030a020904050c09010215062107030210080403080115090f170d030b0a030303050c0403020a06080916050d20 80
    0x101c2c0540d081c0c409a001003140c05010350702881240c1e030f035541800c0d11007841c2c00014800d00c02404140140c0360718001031540702e41c05140060042009450301d0040002c180004400003403855945014236409028003030100000d0b1070200d10344000001c510307009000300420007906039101c035920420340d5000c0051070081e102a5007a1907072414030255840095020b014441c4c002c1741054001840041028182c030920401030f0041c04584218103003200c4022070041005078000303080320394843c0643c03509200000c1d030146540240b0303080e800d500402074110768544146082002030420400065801380c82241114a0b0020301050005d00d41820740b514407460300180c0655001c0d0b0b8000800140004c0082c1d5406070300020b5130504200180110140d84091208c25045084c0d50010000030f40703c2d9012a41c000c0000302e03a075042a481e0b0340095803c1000e50b10510000d07130a03009201c10324070f05006802144101c081420403203458030300459400c1c0000100540350034644c02803c141052080440c1000311001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 420690953 1250 420689703 420689707
    0x4020609060a020610050f21120a0302070309090204081e011b080403120c0509100903060c0c0201120504030f11010b040c02100e07050d02122505040e1f1a0303 70
    0x19000399607030000c650705d0448000b0003000103510300b0540d15200088501402000814941c85581c43c1020b0346641c2103840352080d14100b25454490101074540b1054650300542d58669500340202510f0302030b00655000c51040104110301000042c811080c1e40c56902517441140780d4841c443d004000141402d40880c80320501c502c0d0b00c95100401520a5103c1c4d200d10781d50414610110f012601404903150115100b0420100c5034580100e8142d1390401d03c0c03600f49103294403030751680d00341e440c009118030105529030881c100715a0040f96007800602084020401c916140d1001400310324510025810702c661500c01d514200001e40000000e004080c006105a00c1c820b1030003942c41482800c030144071032400701200e0107034078081030340d2046480081031a0760603240c3e9003c0100f20b0411421500c000d1060110820038042880c61107100700901146135030400e4034203810b210030344034801c0c82140c16400c40d0411041010020715010b0340741c00c55940001c0c0220000580202d400c0c0e281c03502ca9814840 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 420692203 1250 420690953 420690967
    0x32a03101a0a030b1c0503040905070305040209060910030206070501020c0706110a0f06060320010e030a02090c161205071e0b041b1a03060f0102010b0306070c0501020f0c0a050c01050406170402060906 88
    0x4000300038011a227444008101c25602d810b8124100d030020794000350300580f0f480c040b07640380c580140002d4118054504041c0c1b0b0070740c1c0e90b00103660350f0300080085450784d4001c03400f02d041490912208005000a0400c000540207401c0100d4032940380100040114082041c11030900c91076034820000746612001c40c24051b1210f040700100325110301090350009098610340800c1e41400705541c400150301606644040c0c40f46101c201d4030b500690f034140d1050030b8204210b03001c591181031640c1d8403005511115601c50250070400070152035901021081180d283c50a4001903101600c0355001d45c101402290305000c4a1b61041d003d90140c1c8008260034010b800c41a54242c4240258004d08040302c034900c0103081d0390016800d907015215900d41c1600404d00050aa50081c1b0040388110b2141d40010700d00100212468200c1d08211401001036104903615000c00c00c0c00c011a504120342400e10b1824a8644140200707442c10800000480c0106040490708540f13550003a03400d8401c008041d0707034035070030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 420693453 1250 420692203 420692213
    0x6090504020a0b130501030f0b030a0308090c01080f07050702010216060207061101063609030f120b030c01030e07030c0306050405060f01150302032a03101a0a030b1c 73
    0x442a24160711a0702c100c1d00000f0b5a01041c8102c91109040003a2020210716010041d0002c010b00c0c48415121a20760344036030810380d0f0511010040b944261200165030030503240851801900307213403046c144004102403100345160021815030205151500d55506c00084c40102c1c24041a411030708400b80782c0000c0443d107950040754a00039030302165544410b9004c0b14460070b083e1840d0384980c1007144292400e034031071503a07003111410700c8004080c08040e44403110219841266444001980000d40c0f20f60300140455103c00480e2003004110700510006151900007500d5140d20503610b418155110b4a2090020040c42114001c54001404011907680d9041035009000211001c8405016410001d80440300025029050700c0107036140d00f100d800a1101a002548007801c0f80b00d0041400010f10554441c8442050040e1200c401e00794490901200501280c106034015400d40d820303d207940341d09000e50b41c094402081d8186000302e01e400103003000c560306010845144211000e1000755200340a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 420694703 1250 420693453 420693461
    0x18092d0b1915030b061005041805041505040b18100e070302011103040b070f11030a050f010c030b010509041a0a0f0602160302011d060c0d120b1c03050d09060609 71
    0x1241d00d807040c03007880e20105010107419200d000003080c090401001c07030604d040800380036402c0c0d030503410f09514203502d900181480662201002d07140b07540381c02c1040704001d01c69064440701c50800c40203000303506060f0340703d00174154000c02c000d41d9840140305c10720f001c4030300b048864221911000f080050b405003034659501c0750204d000690101341250100700000c44000200ca0488492101c03407400c0c41103660300c2005019005005440300301c0c612140c54082e646c14060804000d110b48010081410003000180c251404070400b10141858503034942c2003070b600081290a070590844d4001500681c030100c1c150400790149000e45c000340c40c0c24001ca00500200310700e50507a080d60702103d4628104500c20f8141c40606e000080c00602c0800f14400e07640c28050904079544c40040c03d02e41011009440300345803000c01001c0ca000a008409069080c460354442c65034141c1d001d46000543c1021003050001007004040001e04002c0002203840c001043c580c4228080c130341c005401e004079562099842c0c054 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 420695953 1250 420694703 420694741
    0x21014063006041a011505030604020409020c01020d061703040b0c1006030506072a1b090c0c0c05030601140118080a0309080c040c020c01030f0b0a090618092d0b 71
    0x2079140e052503544c0c94010b4150399070485004c446c2140244a5151080754070b0f800c003401080c0c001d41c0074040868803610500151541c420f0a0000503118401c249031001a2905940100c0c0f41181880040da94a5000701c03c4070242c44081c0782d61541c5807940783c11301c0d1800f0b025480b0810090300d00781300441000030101d1101c2c003801c07866481c007440e00c000692b5005603400b01c0307203c5006c20000c00c041d480003031041802c80111111480744074540c55034800c0800242c0f0b181e0394548000030340b607031054000c200d00c10b90041c001d4403050700100444c0d8103140291710101c42100986041c0010700200213030780301aa1711180702800501040d00c07112665031a01900c420040c2c041c1200d1030140054008407420300e841a002c5403011507004040c0f00640c2c20054008140304c03090020140c1c2c407251190b0150b26a4002e403001440111000281c152905800c2c40000910781180a111804c1000c0e6070007145c1510388060b840b00100e14401c00e5610a004214030007203803100018412038001c020031000a05440da40210 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 420697203 1250 420695953 420695963
    0x10050916060c02010e010c0c0b040501120204051309021302041e0504090f02040c0203040e0c0714150c45030304030503070615080f0c0102101406300604 67
    0x80e0400d1406106031628450240200007074112280002540c820000884040c8041c14040c3c1c1500b02c503110402e0180b11500301a45541d0300140421503541d0055108550302415281142410b040c00000b61069241510000e5481d0b2112029015503a43c600d107254160b02ea07074802c5588e240d44041c00d0110f06420601c0ca00400e07440780c1c0018690900b0b020f41641c00f6444040741201c04660b0b82000001e10816800c841117210501c400f0030415000c3c2d4542c0d0003109010300144d191006468400320f40350a458078101107400c00030302c004075088080c82564202c13074000b03105919000c40c907124889440014024000007401d000d075501c1030007005040101a110340c0141c54008070103490074155a44114400100035a10411244000c82c1350f640c09030300701c1320103805580501540e5000b480d01c1c024180c1c0280e6401d41040042d0401581c040110b0703440044030301810f00c62950480807500003010b00034101d6024030450270002c0d42401c010030800141a40482d07141b9404050040c1c0c142d030360301c41114100d039 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 420698453 1250 420697203 420697213
    0xc14031513060305030307140d0606050301080d02030c06150d0b07080402030f0303011401051803070807093c0902060d090c080a050303130f0606030b070e0a060e04090212100509 78
    0x81d51640780d01452056030740110046282d07444141003103801048c5d90b540d1482d0341c1c80c148540034003907605000703420060031165682922541400d00090610038a01d21400644d80100034091856001241c3c895000140c082c03980c40c0d598104011605d078030300840e00104440c0004007040369030350b00508854084d40c026000c075850039030010b040542c1c2c0c0c4000e0182003104d442a0400c5201c0750b100301e00910140004a02e962001c9001e00c0c0840d01d08645900400c01d16080008180040401c03845002d2022a950300f031660004d1400040010b48400c1e00509220305070194960b45400c08a80c11201c40d07140d014200341e59a01200d80c0d9440100000001101c60303c2d5090302c0000c201c0c03400a5080c508542002c0658034588508941d81900348108c0011107103003d02555402c0450018481d9000460007880d41803d28501503030700510740d8400c1c14146100301c602c0c11003030103815444120122094000d8400192803000342c0006002d03034601c0304400314036101c0c00c414591b9044041d0050340c080c2030f4a031300b103031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 420699703 1250 420698453 420698479
    0x40816291e04260c040b040b09131b050a060507260408070909080f0702030f01020c100507050c060a0b01030b0a03060b0a1d060409140a0c060f02030f0d0c140315 71
    0x30000042c4044803010035441280e03003005902c1d2940c4206c2035150001c000007100d1003c100416424030007101e8050720300d80044500014409107110b50314100140c90030688001d800d010005969040798040d900800c50701048000c20007000c041c1c641101603002a03184880d1850740c2a110469006018080c51800307a0440051600518020340c804545d01c00f9645052109031581141070b504008401da80c944100391440d40f42113000e00c0103189000d006405000a85201e00202d001d982000d4105000c02004000f845a161400b0a40750307000b00c540380022600c0d03845040101d01615103150300542c010711410000040111035031005030201030541d0545046581d072103801d40d220b800e803440e41024100d41d00005000d45410351015241c9171203010100c80b07030003245028902e801c803122011245100c0102c414003200c0d412100c1030201d03007103a100031440e140740740868000a0180c05981140700340c44070b80494805015216440c0c1030b01d0880c041c25124541090070b400251420103215006881010b031031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 420700953 1250 420699703 420699749
    0x5270c220609060e01021b15040f0e010501110a02090406110a091d010b180604090614030f01110702220912030509030906090118170102040816291e04 66
    0x4e5888a201600500040b0342040c082109481ca03090095071b2100742004003068004161000c3c0c400380485a81d003c1d582420701c42ea0121405068200d103042c0081c00c002c148a500e40082d8801600d43e040d9040300b85500d444c80c105000d41a2614940c15600c0b01040c0300b00c08980c041805c1007183c0c510304002d00074003203000c048500c10b4400c1c0246000c81c4d904004260751802c5081251807071003009015246829641c004800071100d03c1c0d0884450030382100300300000da00e020071044244c02c400500030080c198868240e000d8502c25080c0080c018554010842c010800284940e6240c90302040184807520003407070042c0c00c980d041150750b40400d1820020641b201c0d0004250381c101d071009090782d490b203451400107640706051440c0707181c031075030b403103480821542440c201d0020190030f03500c00076071514101204142080008500e10405500c1c0303520030800e11941d410040a4102102c5140c280b041c44000c1c02c00c80f606ca8400d1905200a055003802d078200c85101c000c004461588002c1a4ae40c001d5000c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 420702203 1250 420700953 420700967
    0x21c060b150901080405030c1605090f06061b0102070b10080d08091f0f1103010609230111030c0109111f0f0305220c0f05270c22060906 60
    0xc40180c1c460a0042c144a94080c06605820030301820450703061081c41c1003241d15003503d50411142400d1020b0080209041c04102e464000756001c07810001c80c070b0b040c0d0106516000f00c161001607900c000c45103003d0042c00390f041b100000e40064103c4418a00f08182c00d1101c0c05501c15001141b2400d10390070442d520071491540a0b4007410301a003211151070f658103512010401c5009400381d642c00d0030500300b83c00b502c40e50710000228405103480e0b6240c1600508210742950061035442004a07404e0000300714907640540d40740b13090030403100000403108c3c001c3ca1401020319a10440d0301c1c00c0c200005109182170307002c081c0c480454100749010801e8490440254007030740c1c03003008541c2260320380010390300030f80142c2c0d800328112103c641030720400d4000c40a102000c29003901c03c902c1140080c803040b01601c0b20075002e0042a00c2c2aa22082000e040322a0a144856540003c0e6081c10200d85101c2100302150700c06c03402000151140840514905001034140c490a00484c041c258001a10b03409801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 420703453 1250 420702203 420702229
    0x1606021308070311010315081015060e0f060c0c0d1b0b0c031905090301020f09040f0c020729032d220606081204090c092709021c060b 59
    0x1603910301404c0e040015005041044960502d042d480100440c0c1403400300002c0010840c200c6010480c10710309a08002c40c0002500004204810f001c5114003d441c2c4211483c480395054642c0f599948030b02400d141811740c1c9980040d80000c1620102c01402458a40c0200c642ca402c00d940070103a0740c40402e0406803054079002c80d041d400038442500907540c0340440308038a00c580d04015141c183d9600c00203089920078802d00b10303000c9002c56441d4450406102e10b002003040010104041c0c840075102940c0e40c20144941e000c90144820302265203140101e250100380c41c0c4284d015240e060180e0f40c004100143c1100c6074920000130781d003580d44801009218064410600d0100b50425110400d5034405001d10044d11129242c00000a40c50030070005c111aa40d030080216441d40e0801c4001000c0c2c0b0200c18500f0208004143e050004a0314401a45200140c0c0c150800402c24412108806000001c50180d402401c07521055412280c00a640c0100751044104000c041146002c004442d10062 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 420704703 1250 420703453 420703463
    0x606020a02090c07020111060c12060901050607120908010f020d1a0f0103020c01020f0a0905010212071101030209011b0302010f2f03040f0c141201021206130216060213080703 77
    0x8000c2400000183d00400b0400d0040c03421040c02800320304990b28100040d14141810b6000042c040305044803c582a6003007a4200c5c0c01110703e51402c00024002d0180001c0600020a51015103054500500b03814000380148002440407001c0c0018000081d003003107403000700c0c13181007114014894840d0102d13011a400c0c014008010385142e040118001e41200b050620559800c00021090180e558040e15a0b01d4507680c5812541e8105000242080c4903400c002807060070502a0600140c1080c11089080d80e0a10300113032591641d6004039098a1410116400943c180c1d00305000c1c560706401650000c0562801881610603142c02d071035011321110a4600d40106070b100640c2070940ca0f0000f190810700444074214600283e413a441070741801940301140c030780341e40c09000e00a401c04411411035a90302400031030922407901160100040010401440f031082e00b40f0301c9524580d6507054802203d80107007010481d016074a06200298045100142c0b23402011100003403841c00014144282c0c0e40c4a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 420705953 1250 420704703 420704719
    0x3030a1805370f02011103070803070c020a120b07030b0a052b0b0c28080f09071d010305070509040f0b040f060509100b01031104030f141608010606020a02 68
    0xa041c0503070148480e800b01040070280503401d48610010120300243e00030b0060350440c1c4032501c005001d01c0c4c020503031604607402c14000100880c2d106025203034848214241450151000e1000034100405034021050907904a44804180508018500c1c0b040307510340c9041004010071810000c0400703140c0f05035130b4030510001d02005d04101000303680d001c1d06040804001c20440b1565002d40340a0f01722082c0307000c20000708000003501c20104070000e030750842040c60a01845404402420040b0060511042c0754900380400d80c1d015040150000130034041c161805885400146134084000038403050310148030362080483d051610a6041e4041e41d4004192090041c25aa80310390041c00200240d502d07a880c1c00d01e02000c80d50b1409150700c21203002c0068010030008407920700c100c40000389003034105840c0c001051520800c078021103064030381040c0d4065904006241c12900b00c502115604841c0c0550418103104080b01c42c00769042d544404002d00c00c8585511040f41c0d074003100c010280d881a14 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 420707203 1250 420705953 420705973
    0x12070813080d02092107050607020612251d0414060111030f0403111e030304061b0512040f0e07080c0a0320030610020105040b040210110a0503030a1805 67
    0x5801c010300311456812005030500ca440e000180c4980c0440010800103100503080302129001800b440015090880344c2c04c1c10310fa210b030081109409501030001400c5950710110748082d02410641950f195200210000c910456000800e0f4075680034110020710500074901e40a880c00d4000c02c1141c08040342c8030b410541d0790f08011140341b1110040d60710140400c10115403910041c10050000c2c50140700e5140840305040b00f130291f022038400300040300c40c41641000855590110440d030440b101441c3c43c10500c0c02e100705c4054000341542d0000c0c024410b09400c1420442a41d0151040341d0103424800c172100c0e51903481c08001c80c0201c4100c1c0008544000090952001c00041d202008040c90001030b0703014140ca00b1403c2c0402c21403400d0f40e03c0000710030003e8601d001c007803942907100640b00a001e90704182d5a0801030070000382000740704141040910107414410000404406041011169031200724180305440f07030301c25100c000310b035400c00301e200e040140020f0601c25000da11070001c00c10620 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 420708453 1250 420707203 420707213
    0xb09130303050c0412061a0409020102071802130f03030f050a090e041505130501060f0f050f0d05060103080c07090902130c12090311060f040b0112110405070512070813 74
    0x4003c4070b0300450500c00801d00c08170805095084920940000420705100301d412545090414001446103080104c68401030741d020480303408a48403a42590146801031039a1400307409180d1ba82e0001c2041d400d0002082e01d00000d180c0b007101c1c040c5e00e0b03a00d01100c0d82d0a04440c5403182007840d10104100300e60420020015a1000b680180204084068031180103403440546009a466061002040713a81100340a000e10404004100c52050750b072100745000c0340c030b004140091243ca80320303140c0780085403030b25140e007800011016480029581031350b84070714240182d608501c1000c0d0052050500210f125555403044006030b680080401c200c4a40e80010341000c0c102c2c901175079007000404118100052081c0c061548050304c241ca41d42d41e83e000c0010614034040005203004000341c441c0342030102140c0c050000f14195210401000e2510013030f410615a425108050380703410a1900c01080a115403141c00313408045030703070f000b40f800c152540c0f601124040826905024400380a03813800000031 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 420709703 1250 420708453 420708461
    0x5070503041a0910030515190504020c070e04080d1b0e040b0a0e130605100e011514030711010b040605011e032a080f1614070b0a0f0b09130303 63
    0x294a020303124580034000700032600c002e002d280013070003007502e820501c8444442a50344125500d03003518480d20a00038888121400300c014400c25020319800150500683c0b000c0c4505005030003580000c6500d400d00e031030500842d620403201c803190203260050452420f40c3e44100703c88903481a64590b804c0c8002c41c41048002e141030030905078021030031070700014840ba0b441c13001481440300000c2c55628a02c02c1c2000c0068440051580454880300c040a05c4595441d91300c403419100e1003d2030701c140d05100f03542910940400904950882c002004012440350300541580110071290001e000c102c840c6002d0105481050007030f01d000c10a05110300080c0d0300002e40300443d110141c5808070b9030480600001445c9010030300b8004041b4580342502d54040d40211016402400c9007412900b00e20309a11464501ca02148001081100400158105801c1d540988001540100c08060745081581c0d90400600b1402000f1428034104085401d041c03500405041c40391800302134a0902d40b5080e60210010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 420710953 1250 420709703 420709739
    0x50405150705060907060f02070509040b130c0f0302120a050a08090a09050c0a020c0111030304151b091809031407061404050606180402010522090c0201090b070507050304 75
    0x26014441d150219004101d2240541800b8010303065080c101100240a00a00c0072068207540c080c150070010b646825400c01e62042d0070441408068890b0201c124442170340c414081e0011500b1100410551511041d203c11a482120304031502801810015100d506614001c0c11903000360039032401140d6900d000340070740e000040584181ca0f0315080c0c04001c4840070b442d0308440c07020100b0800b12140e010808521410b0003428860340e0201d10310346841d034908c8000d000070700d00c0708402643c80100595800c24551403030707002c1050201807905a4002c254036128820080101c4d007141c01c81c001020340d40b00d1810419016a0340502c80718491003081c205600c000340445002d0b9880b041420500401404640118441c00c040c1040c0d041403400c10032030480b449180c1c00010003c4c802c0c000141c1c0c04c6401c4030048043c1324548032a9510311802e00301c6400e1981c9c0305880309814140720720842603040d448580c01c244520480086070b11041c104071401d004070500200958410407007840100c0014019140c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 420712203 1250 420710953 420710989
    0x1050a0f0e07030b01091502010f060801050c0d0b010e0a0e0601020d110a020d0c030f080c0c01050405130b01030e060a020c010e030304030e1302071509050c040b010815030a050a030908060c0a050405 87
    0x1b483c1d5441120f0110340400b0003050041c0d41d074900e410101c0038540582c00003048003c1c0240000c2c24410a81d500d5880303072424502c9095030303c2d894450243d00030540c00114560041819403841d680322651508050308032542030060044e4151002c95a019400380c0500303d03840b2004146050880c2e003400030360034003003509503564001101d00000040121003101d0525114401c90364862248002c40b80c078004c07001030b0761414010309100c20300c001e8451604801342641ca0800c04a8006031002c0107900030010000c0c5550b844c007400c41040b103161891740040c450805140020040001d40880030b9450b8001500c00400051505c21010300900e4044111a8440c5094030300510b417216941c1c42d944108800c072078a00d883c4d5281c00c201e100707014003804800c55519007550140202406040000d100043c02411002c0c0301509400003a40c60b101000040075440d401310840b00d1080150401901450300c0344209d02092280c1000a1600d03400c0030107641c3d642c01c440d115241010700300030401c5202819403e200c94 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 420713453 1250 420712203 420712217
    0x1504030e011b0c1202100e061c090f060218010c0b0a0e07091b080708070c0602160212030d0605060403030207090b060706140906070504240e030a0b01050a0f0e07030b01 74
    0x40840c5500d90360b100201107513103202000f50700910501c00341040c401c104100f0301220301d41010254481e80100d038100008400200c01c580a01610b0500401400501030600007519403000e04100050303008150b0081e072803030940c200302613a06c01180c600105600007070200c01d484021400c6c519054022046000340750341564260b41c2c5442000c0200c92002d080101000030301c1d00110415508120217540203407051914003250f151403603014004501c442c00c01080b241d40003554044c0329254030103040615030b0040841d0070180750f07008186d540b03401c0341c41c80c00b110710b02e0800000303000e1509130111411254182c016010440c580180e4200a00510640942100382081002d000410600c182c1c01042c4d151400c1e01312505000207101e203086e5000f400d0101b401020001805004000eaa1601c512810f854010000902c2113500f15243c0c455252415018464101132a0412000d0b4a00d24180c170400d4994002c07042d9a050b4074003000b074007445070445040b2a42c2c08650400c0c4070347c0011140c0c600c10706000c030f = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 420714703 1250 420713453 420713507
    0xe060d09050a0b0708240f01020f071403011a1302070204111908010501110a021203040306020f030412020c1e01020c032e0b0a0b071104060f081504030e01 68
    0x40c28211640c0003140c1404114003001004c0b500820000d8101e0054400901e040d4002600440d5242c12000807503c5040b408000111581c401c00001c1c0040c0e940307a060f508925512600c1c9031590355100c2c2003034402c4d420800c0c0072650321851008400280c40c0180315140181406803000001d520141040e608241c6403d075283c0c4c451a000018410302c00345440c0c000000d40d04903030061407614180c021074100b08482551b6081d6480005445400c0c42c0c04a80c0a21505102209036242d81b25551000f4052400820740702100c08130750300954855400b84112100600b10030300101c0c0c54043e0601c0e129481003000c84040c11203404050104020001030040711122004040080d00d0710402040d0b2901c4400345210780c2440c07011450140c041e440646406100039000c000005001c45518043c00c032401d035001c20008240300a000400a5030031014108005050700d80301000802c50b0f442c01180f005204100301402e40000140b400c80c030803a0503075500045041120011600b48881c400c0c4181c0e904d4280c00c3c0e003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 420715953 1250 420714703 420714713
    0x2090603040803180106030b010512030412060c090b040e180a0b0412090503030708040314070b040f0e010b070c06300914030408060105040507051603080105040b0a060e060d09 77
    0x540c00780b409040300d80c0d201d2601980b0740084548910030114540d042200410000d02d170b4030400c41c19914100d51a08440d07003c003000b1407450085034007200340005240c000e41c0a102aa61000e00803810780c0e0388950004e42c07600181819486140b1912042c84905800280309102c2050103541060492065440014454039011100082034406845040043d900161001c2c0c114140780000c00080d0007841c18903034941c0b585000c80c051844003030541c4c03604d500705003007011040c8012009040701070860b6484588403041313041e00340c0ca03a0203400c030075000c106c0000c80d00384109801c0c0c403945a40416441031107402d003882114088816458110001559040f11100b09180000c040c2d0720110002c0006a015040c280040c140040601c9040145c1080105001c03020f00071602905564040d50301064903156454229107900ca0707900100201100c6400702c90400d540003078a03034102c41c8112020312034009032104000c0051801d128000100e80445500003c03814114060058900c48010010f440400ba44030 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 420717203 1250 420715953 420715957
    0x604150f050a06090c031802120f1207050607051c240e100902031e072d0206010602010204050102100b0a0e0405060106141801121b0309030306090203060102070513020906 75
    0x41082a1200b6003804200c80c141729112940340d207850248030192030701e240080384000c20744019005041c040b01c0c265045600300706131407078500e50b04102c8503070074103e0401242c1e64100e07240440321070203003001140c5034a1107002694582100b8100d0151452084880b9000903d40d07281e03c0d800d201c268920280e0b061205211701001000c500000000c0c40c0380c84e9400044141e55604807050861050003404080c03280041a864103114512500c02d80b900c48001c203039196140c0b0900e80580309030030000c24400a40c1c044480d0035810391174003140d00da41d032200740503030030313070040703004141c0140e112646402414003150800085160701800d0171804988070b0050201c00041260f080d2010352021004111980e1301040ea14240201c1070100c40c203103001c041c075000fd444003c0c14118100080a1075045030340c0070703940c4124185030940c2d0080503000411000a00541a041f0081d00401c1ca05813001031581e0302d5008603882004168007901070907040204000d4211500b10700c0a4000741e00b07020032680c9440e6000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 420718453 1250 420717203 420717211
    0x1180b0402160b01150e060c0102041a0a030b0a0e070e060403020406030b041a01050303090f420403050d030203070207030503040303051b0a0f230111030a1d0604150f05 74
    0x3602a0b401e038418149240d800c1d00607885200070f1a4116040070381d5546c06061b01e0b40c03082044849a0391914894a4a8003a0045800c580506451341010488180803000100040103550304c080c0b0039407020f0000c00c862900d192050740641102d10300052203440c4500c0c0366020a800043c0b0b05c0b424070392a038000ca021500180c10854002c0301e2358050200b40014420001c1c0c104007202c481d8a11503042c500429107a0041200300f03406407024101c91141981c2e80540040103c81001c0036011203518584520215640794000301e902c4605d00c0d103640706d08030000381180c2c140c3e60000024802803101c080102d009500c010301c102c1c118081da20010000500c10300050000394040c0e903456841301a0b1b8449542162690010002c50790f01030080c1c10001007800c0c115142ca80d0708211486a0b11a01010303481268070030042100c501e5280600c03d14407a015100554018121000200032a00b030441030000a800001615960750b1f2000c1d0010f400140c84c10035941816689082c04662030505040c0308091f11000c1e1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 420719703 1250 420718453 420718477
    0xc010e1204080106080d1e03020904050910110f0702190b130e01240e12030a02101b080f0402061c0504060b010801050105120a0e070b030f060d0b01180b0402 69
    0x501000b03100d001340180400f4090b841c02910680c83c100702e0260428800f000740900e940040c410110f20329001c3e43c1910fa0300540a0302c284003524190020a458010030b174000e0550380d2804100744200c0c021141918202420041001e00e0003219400300041e0881c00100400c0130f0801210206500504802424485d41c6d5a1041400541000180303030860005070003240140c00405005c0c582140040300f00c80d00c2034024280141c1e26581c4401141d40100217005011181c400003d001c5a040da00150300d1501249560040040c000f40003414014032a400740c10f4000122a5000f0469241481c00010380040c03004001b2440c0c00046d07082940c2c034918000303d695203035944d007041006020060242c0074402109180842d40c0303604043c00070300300380183c05540e0000300f4050001130b0000040e034801890280c04804a030b0301c8603075a002e140040e600495809260b042071001094071400c080c000b0b4030001c0d602810801841e802d00901c1461600348501e0501680d80341c190b10f01c0b140d1a18402071207001804 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 420720953 1250 420719703 420719707
    0x20705010212010e160909020318011a1e0a05060307030b1818010903050d110702060d020a110c03060c0705010b120d020f06060306060120030d0603170a0e01050c010e12 74
    0x41340c41031111050060004400d018501401d8504660107614032090300e099000040e102d40b1380f12201d01003a180d40190705080c2d03180100b2a80e0000f495820091300c9441217603507081d600d141800d210f4a14075104411604100312485c20f01140ca403010103581d11512528000500f0110300c400294115485074140e0700079030454051004004c2005902d00103000e80500038000f1003101c1c0e800400c107100d48030440003000e58a00310810b5940d8007108552080d500200f00d162103d43c5400400020340c00f03515060003080600b0220a6490380100d803070346010308014041c00c869902c50400002d65801590111855580c501e14501c0039070741d01000030b58801c881402805446a4018080d1420b010360120810301c0d8070010400c40165400101035070b00c00420719104141402080d440c050b416440f00d11900701c2d0202040400070740385613a20000440b03020b4490031440a03c241b2000030b032446241a80000500c1c0c4e81c2c0340d00015401000282106054a000090317420905203819050441170000100c00c0100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 420722203 1250 420720953 420720959
    0x1005040c0306060b03070c02010815060d02040512070f05012102070302071401030e190219060804061104050d020405041e06021b0d081f120305070c090b0f040f02070501021201 77
    0x583c03250002515040e8181031650500e588003601c11806120024104001c0200042007110ba000342c910035110060310441c0c455a0b01d031842c0001e9000740c01803e0003603803099060038200741c0006211084030313990450302c1a51070400d00112580031041e603941e003031305a6040c0d007035214040c98801800c0c9a40641e01418455050042c0200c2d0748050000343c43c1054100f01101032204808980c0480c8200e130b03007240d4408200b0520114100d42c1207202c5042506001400015500c0d4112203520300c918402c200030440980060312480c054006c07805200e1b000b1202d02e00301c20050402da80400d40090060820030800c01150504104003849480100c81c1d460300803c458221440c98519034020180d000c0140118502d100c40c0100403940c01803180c884c140380022120001149014144050200040040725406560401030825800004100c4001c0307003030302e0300141e1420184a50100d4000080410740700c200c40808002c0900320008080038803550800c040000258248014002207001c1c0c0d000c0041985 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 420723453 1250 420722203 420722213
    0x418090b01240e040b0a0611100c1b02040605090702070314060103020d02100c1709091005030706050c010e1b030609010207170705011b1e031109090402031005040c03 73
    0x601a80402003064040100c0e01c124203101000900701a900d203800c8000508000000c1c0c05030843c2d10110790403d852103808618254403c8614101c2c00340e00084030b41768502c840d2803102b00c40400310708038005405045214100031042828104145c0001c10108016850740700141c1078603c02d80380304015a11481e41001000310000030540240481c10240a1662458000c2821481030850003845426401c800e00e580da4010048007080c640c00160b40c140310903034070700714010719805801a140b040d402900028280c00c8925041010b803240900901340705454028152043c1d048124002c0d07465489007410f030107404040000d04c00d44068a41e20300860500705061504192014059850341c0c0d004001c9030000c0b50015021407024030455021a9440c1e01c2401c20031700601403186501f0340c4006088101910583c090070454258240711554851150401010340c11900c0180d60800d6100091104270040d2801450180d03005001400b03480084c107207805840304580080300e08030b5000b000802c040c82845 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 420724703 1250 420723453 420723473
    0xe240702250e04020d0b04061e050402030a1103030c030f04051c0807081e0712030501470f0d06060e01050316051b0303160519050307020102041809 65
    0x104600c20051205400191a01004801c41c0a10381c842d010380000b107411500d44c000c0d202c3d901c94114011008038207080c98000c002d4500c000c000003449007070840d801201505882603600803070340207005200d00780c0c540d44c40f030601a00c4a4071a0b035040c0014080483c02000910003803290300000851543d40d50f040004101d900b04810150803980000a2004000540751f10112443c59401004050721044031180b0210030907001440c14140c407101281c40410410030444140004c4c1140c7c030f0034012030f81c135100b00300050444640200c060120b00817500703040b50020080d039003010b0b5480300042140040f03d691100e8640c41030850642d403c10003c1c0c2c00d40701c40340b540f00c2c1d00003620080c9004000101808002042400041c00310b16061306042c11704400940118100c2d4001c0302036175010000702501008268407500100c03035000e40c1c52981000c0100842c403640855010074010141607807002001c1000302e40640004040d501590b600300300200d034031601219180c10f0f59416010100c0c10080e81d2500d0300e00c007 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 420725953 1250 420724703 420724723
    0x11011107062c0304090e030f16031106060d020904050102071704030c0b0a120b0307081002041802030108151315020a020c040605030d0c08040e010e0603071a030a0e240702 75
    0x1004000741c2c5144000c80802224101d4103112000301d002c01c03c0044e482d0562103a10030a6010240000f80c0c20b034401007042c0400400b50007a203074204000c20300300e4000e840b510211140781c0c0c807414440401d40140b4080e112150018000c000040c1171445960b40c07510002000c0002040e01c0300d021404204000c2d9240b800d2002c0c01620480c01d052410441c8003070302c1e800c0a10101e6218648405a001140c2c408015000040c421501102d12203c0c007070385694001c0d40540034000000c00320b03661950202072030b802104d040341d09100041c8481c1514003041c0169910107082e020090441e0704010340070071b000b40e01c2c0d81c402c40050b000060750b50107106c100ae807070442d8000460b40294100442040503a4010031000f250680c282000b040000c028174001c80c6510564222400c8881044004a44d0301000c0304000c4c8680002c0e002c80e90300c1c5403141c006245012550541c0031020f0410000502c841c81c0c560008081c142d5844203ca0341280e101404491340c80440145d5114044240104a01280d0403c0300041c4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 420727203 1250 420725953 420726011
    0x90c12090b09060c090d02090618100f08300705030408010218010e0f04050903090909070e010f0b03060609010918090605070f05070b0606041e0f050103110a1101110706 74
    0x2800c101e180200d203181d601b4420192280341c110340058155101c1c409061000c64041c15101d0851401c141a820a0703840d5004e180c08071060802c0218042d000080e05c0c140480c10104802d011640c00044c0d04481884002d0200300e1070b40501601c800204100007070401f800433440096100c0105010070280301188000088c104058440d4424142d1604100c0803880c0e00c0079100442c1507500c080e00e603071440c42070805042e0003201d240108010b00302c0204082c000d4507168400d4243c60390ba669101040c00304240a6052030000400114415260410003001c070b1042c181013524809035a010000a0501c0103190201082d841c3d208000405c00240301d85940300103582022034916142c440000c1503400f80201c0100070070f400002007000c1c4e903101c10664006200d45040c5010300c000c4040340301004941c078400c00c11080351801000c00c1c40d40c0a0f001c0d441d84404450303489414058114006c840400c903542c0516038656079115104040740300c0000408600740101d00c00721790f540e80244024082c403424019152 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 420728453 1250 420727203 420727207
    0x302061303021f1d191d0a1b050a0e060706020d0507211d060910060609030807030c0303060509011403060109020c1c110109150c0315090c12090b09060c 67
    0x29819000340c10f0303450200010303c4030030840010764045680d101103c0d450f100e072241e2080d030024080756900c484141c9005206211b40ba030307840718140305080d80e682d040762381101035081c808408a544510041e04850910746082071041d0380010208206070312014041ea4920340001e0540000d0340b840c010f145d0032107021318029002c404071113240d01d2060120080b0604068490880035009580107040040d0450f110007a1101d40c1061207569941d00d2503408008035141c140342002038800c3c010200d20040f00d400040c41464001c00f50380c00c4500d0300901c6021018550b4903480490f240e1a098042806088140f01c4042400c6d841d100b010301d4610140e004006c0940100811400d076040400d40c20040ca80c01c00800d8042d82031088191001c0c400c101c401780096290903944d005105c040303004a8400700c401d410070803a141440c20100d066a04280203402c003502c01000420001c0c0d010f81c00004190310350300c0e0580d01901c15000c0f00040d5082141c064441c0803d410900414040a00146401c00d00c101e114034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 420729703 1250 420728453 420728509
    0x1b0b0f1e070e0d0804051f110606010c020103050403110105010602010c02010b03061003110324040303050f04020d030e120102191704050601091107020409060c0806010507030e19030206130302 84
    0x2002d66141004142c040d04280070b001040100a0007950302424000b040b0a00d480300c0b6a02004001d600a141e0b03000060f40c641c0c10840710300c4003080c618040d40060307540520441494006401525010f001207080115002034a05007031400e1282034060200c42d4004142a240104c0003800d40e1030345021039104c0d802c4041404000081510020101c940c0094202a0a10500000703400c1500c018180081000c00c2e105500b15905402d40140c4114880d880070089030312500e0b44411180d50807100290071110f1508a03401090040002c2d2200690040c035880b1004451500c0e503007682c010f00d442ca004481059400540540c100c4040612100751550f0300c4054907041d00e58070f99441040c420720002c1030fa543d69a0450350410800c8820487e000f40050090148a1820311b000f0000c0c4a40300740040d402c04003040c41588120200c824164165507225101c259040400c900c1d08035002c4502c218600c40c2400000685451001d0700c1d2284416421384c01c3c0c03a1030350040c001416900380d03145540c044891604 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 420730953 1250 420729703 420729707
    0x20306070f30110702091302100302030103240b06040801020d0c02010225290906091c0e0d0210050a0201060815160e0a0f23030a031b0b0f1e07 63
    0x8074044000700c642c04641015003072610001ca00c512113010790008508400c00800d90088481d40514038030940724100241c02900c2d04500301d00081c08000c2c2100e030110140403201480141e8010031200c41d080008580201c00002a00c55010360302c0925665000f1070003a0600a0078407400c0c44502c0303180001c0d460441e01701c2c2c0c414000004c0c110810302d045807164004040c0402c0c1030300d0001007442048018820510800348041d43c2c00e080344c2d2030845d44602000101e05410102e24030640c0d68603d101040f42d020302c880107072420f0032113100e03082e0402284c9844030701680e0340711b80c0c0510106290f2280d50350b5680c1e07014000e0075240d80d900412070303650140c5021000300300c0b00749415034803c0000c214a2101c00044000315069040c82e0b8090f40c0c4105801000720f480e05268600314110f61080c40d4070300103035441400d44581000010605c50389900044002c40110f4080c01d1280030b00381e0081c850305811740c00c61b514002da8003003d41b0b800c943c20a2500400245c0e0f2824103c0480b40c0729000b18001a51904001c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 420732203 1250 420730953 420731027
    0x230702031e1b040504111203090405040c181e0c0c0803040809030f070302130e0a060908041e0509070e030a060501030b070f05032e0905010e070905091918020306070f 73
    0x1414001d0607105030611f000b450910941c0c3c0f107210021700500050500e401e2202c01440c081c024200c441042c002c07107604040042c0b0441c100c80c0a050704600000390b41444000c02041c00d1000a001d10008002000c001800c1c40e00551080e40b081440e207489191960900d850460145520740155100640a10140c0e5070400e0020b40d1000840c00400c014482c0070702c040c102041c00f40000e00c481d0511440d0070400c1070040160041c2d4890b450040700e5038050f04414240350081c0c0c030a4580242d42c66001c5400c0c02d100f80042d1810290207001c5400034001e59462004440c030076401507030200c0342e442c103214610740d00900c1d800d1054950f190a9040d410b0080440b03d2444060b80040c12080c200307805c200f841d013030f401f04840040203240010070180d1717074850303c804800c482251240001750080340080380741d26103440340600403007540c134190007174030703040b85000000f4141001c11204200303400fa41040165020401241f044038181c0e20030460011011010f09007014142401c034910811141002280441c03041e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 420733453 1250 420732203 420732233
    0xb0409140106080c030711032d090112050702012406031a0f012304170d0c050a0807030c060207150b041808072619230702031e1b040504 60
    0x5504d40e03a0f42c6840d0001d813039a800300d014008039400b01041c1c0901094010320850b103070b030350301e480380541c8480c03400d1581d11544a4070001c42c0c0400c4801c0008072070583d007a4440342d8005424000020360810881c82c03485140c1e901c0413101d40040f41c6081c00e1004944c54000e011070710a002c0c032207816a03240d000000380d401c9404c172940345c10003005031100b0910522110341030031540c4003500250b41e11925400c100c0d1030440c114580800310f200e03254450507054410110315240700d401c10301510755140c440e80d680444c3c0d40000010b808000c1000c031040041071240c802044003e11403205580c0c22030130801c0c1c0c032055826841d01c080c4220f240c060b60b013407000444c1c01d01061660b4012105661804203240c0b19089242041d54070126034143c201100003030410500820009504003409100401da008086403030b00d042e00d05d500920a0004006a00303850290080c110b0244000c0a40e41c42c000d044408041c050310000c0300131859400380103030100414010804041c600c034192010b001d145003584a500400e09040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 420734703 1250 420733453 420733471
    0x1c0203060a0b130e0a091407030b010e070c1b090b090f130318030b1b07110d03050910030614030145050d080a0e0a03110304080303010b040914010608 66
    0x110801c0c3e9400410300c500c058501841d80030b84908202c111280100851b034001c5411901c3d0414900100c900050308000b08d0743d108004007030580c01d02038001900072000c0c190000f8030500411000010f0420224841082d29081001000b58604000c00b0305555919406500074122202401852140b801c0c840781c1c002d00c100c0304140c1c440010b1600311012a0307108400b1381240081c680c0481009100303a00310b40904c40b03034a1401d00900380059007140d40d101e00200184106a40300d000c24140c11300c0f40c03802c68214081c1c10003031f0503d0845004201c0d00d003100d40c42078000a680d1b88041c4131244140d41200c2c00000181d000300080391070607040704a0081e100000302200740700e42c83c141824041c583d404100b02c01003800e180e46400a10301d425a035130384010700c1c103401090200000540c503149610429051211201c000c0200b00d49070f89041c1d4850700d503034a4480150104001c0451120743c00c0000f14001d2260740492582e0b10714040180381180d110742c0304903280002c0000100001c5030300020300c0350009044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 420735953 1250 420734703 420734707
    0x5070b13121b0609050604230613230106050307080c0a05090619061128150615050304020307060504030203031e12041101170903070b04050c04050c1c0203060a0b 71
    0x800e26801414150b8a001007959090014a400300700002c9003180c082d40c42081c4180c406610802d0050b01c4c4040568110500e600400014200d60000d0b0102d42c0380b140201840e4042c4078104d000308260040f0801070f440c40b60f46402d403c00050034100035180c01081d08401400031030740d0302000201204601d2107420b1044035a1004900242c0c0c4104030240b0350f4044100440b48595280000340600010300e18001703860060040c450b0700d503002e0f03501a05031418100d5407800350140c00d40c1c48520700000341d15a1100b082d950680410305041548a42d420b0003031a03298070b031300e03490720748100346c80d12103d500140c0030050306000c00c10058a002054a841e0040000e26240d0a01c040c3e11902c15402030705521441c0c051448140014070a4000c180c50001d103080ea035030740216243d4a005580d08100362000321103903200300404030120f0060780e0303040d41191280b41640c1030320500a00190581c3d0f01a500b119021000295800e60304190744c091840350a500ca40540c15032400c20001212448144a0340e0482d004c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 420737203 1250 420735953 420735977
    0x40f150e0c0706021e130303170606030f040f0506072012030f090c0303040b0406030e06091f0605030d080601090e09060109020705210301090e06040b0402010c1b030305070b1312 78
    0x705c40c410303100e4a042d0801840e215034041e40a190104070522081d00403890800c0150220940d00421500c100f41c00340403280703182c4580c000000341d50350080080d01c803504488140800030381c0a00c045805645503a980c2d81684d0203039200349c2c03001c0140c46101c043d143e001a8a210303140e10110203495000124907540c0c011580d505034210f007024080d80d590390707040c0000907004c80c0e0001000c020308180c920740e503020090800d000780300582d21030b001c0c1c40d034002c9903001035150755050622020000019242220100700d4130b5031000070a1a00429201200c0400c0301e0004000702541e014405800401400101c8075840c01c2011419441d0385042c01f405100c00e400003040b005010f810044074a10990400154401a0304002491941e42080c003d146000b400c2c100421030710803002031418007854000b002030501e52126801074418030f00c414001c8841406920141013170701c00840d030349402540a0f0b103c1913a07170080340c90000c40800008020310762503d040c0a05034040740c11040b12002400b41800c045d510481 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 420738453 1250 420737203 420737227
    0x3090a03030c020a030c150809010902011706010c0807050f0118120c0c08031206100e01020c06090a030f0f03080f012103120c020a0b010503030703080a110405040f150e0c070602 78
    0x13900e410180203180080700c005000300d0212800f40c2d550700c442d17407940b00c152504e40c0d02600345d40c6401c0b80680065a80304000b45c156054400c0d4513085501414017a0050503903582c0c0e01800d4200540907100ca40000c0b00d8450f0404080c0143c0402c040c51945003807054400303a580080102c43c40c4d080d10100070102e0101000c000d540b0b20082c0203071280d0f10440342c0703a0a4100d4120809a011035117140120518a0490f10942c05036000c2c000c1200140c0103030815407001c0080c081550040c0340400da01140e0f030f40d0001701056018101580090040e450b1720040c0e0b00c203050103810705030081c006003500c020071001007103101030403038201816481d44002e0700340c8000941021a400d503d0240741042180c03800602d105200e40001c0d00b020507038801c0041e030702282c1c1d841d802c1545a01842c1e8029000c40c2140c3d0009000d140c00b5840a1000381d40d940c0341c24241521600410b046a051801c1030406998580300741900f2030500081c00010410700481d54030518002000c0040303801245070090102d6004114014054 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 420739703 1250 420738453 420738469
    0xb04090f2310050103020414040b0319120e24070c09050115090f06050301170109050106030812100302010203160302011404030203120711071703071b061103090a03030c02 75
    0x800804003080003503040300012028003002e50344400110b2107607000041c194000d000b1344044a882100c000443e02000d010f1101070100c80000e164940100b001003d4034110441a0b0350a1034010348408003075801721000507094030a204581881220600401c015919280003200359007070084c80c52544075030070703442d04100f000030540060312081d091000100d80c0004008810a682181e561220003e598880041d1040c24607400341c400000c100700010f1002c403030305d00300c410800f0000000003d10010203440382d50844405400480d8410350000303044054809824103182c008400540055199141d640080c3d920721901c2810b141c5084100007032803c2c18000e50012008000096803281e143ca00782c540252a03a0200d15821036101c000c4021441d158411003942c400040b04000425a240c1440660003030301c0d0100d490070001e0701c000c0144030005a116071030204214030180421a240f410841c024040011005c845400c950040c0203c0480b655150358032811a600f608101c0030941090000c50001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 420740953 1250 420739703 420739721
    0xb061801121e0b01050403050c0628092409030b0a02040302090a1d0d02121e0a09182c1c0905010206221203020c01060e0f010f0b04090f 60
    0x9149007607119450921003a902d9118102c1c1d5210800c0600c2d00c0000555a5001b01e002c064219805207654100508014005200e10300e00b4102c0004008507451600d120361506000311800980306120400c14000d0038107100c508082000c8801003552007018009098590f43c2c4005080d8203001e40200b003402c549a81100e000e9034001e0045151031a10780b20b443d001e010384500000024115141d028106040801d580c0c0494030140c0c091300000312030140c2140306800c181c0600e003986581200441542003610010943c804140e210b10034017620742010341300c10708000160081e040382001039048a0514440514916500c503900e260f85070000c551060746840742e00380e500c4003001c0d05541203141007504101403104440302642101c040f0303520841c505105a4429050600207226801e400c00018110845520b04203040d04d40182408045241c190940e0501e038007120310103206000703000342c003124441d81901418044411140d051310f003001008291045204d0240c3e0980d031208117644564081e0404104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 420742203 1250 420740953 420740987
    0x8070824040c020105010f0f03030503010e09010b09010e090d050c0c190b030f04060c030b06090d0611040f08150103170a0219060f14060102060129030703020a080a0b061801 76
    0x42d08002c410040c0c000d0000b0b010340c003040412002c0019600e056407a05c8001d581d4181c0e5240d0560b440c210781c1004010004d0400302d07403035403a910b100106440e000f4216008008506c0c520303141381001001541004004003446003001001c10146000760400038120a1003a030a4484c0501c5070780b180503020b001c1c1c00e60b0700503c01c3d12100102b0b000c61600305001d05405039000b54410040c0c0071080f001581120394113400d554000744c09014180b000d203842154030900b1380c001c030300201d110305070010f56011a40c07040e0803200d600c8040007018400010100004104e402e400404500d4a5066440b2101081c0c14001403207690080003c402814a10034400c15510703121a240300c0b00844001d00e44800a00a0040c120108514000490321a031075060b4144d030203011b06030050087c070b900b80028046985607035850351590803400001c901208074500b004610450740342e9001a00d581c445a0b00425190020b03015038442030500d440540b8550380c440c210382034102c0c0d090051850841c5000148e0707552003413101c5444 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 420743453 1250 420742203 420742211
    0xc090721050702032104030e1c0215031503070803070204110c0d0f08060108071706060f0c0105040b1008030301092a08010e0703060e0609180706031b0807082404 71
    0x2d1070350780003c041c015220816401541401a02e40100038189040f100900025008a00050181008035512084921142000949c1300d0150081001c01e404036481807441d503000404c0210341d0a8030032104a01316000ca01408401d880c080c1441c0e9280100c40001c0d2003a641d070700924078900d07001401c544440c3e00d48030540e0b1800070421405843d0072107844001c000f00341000002041740d8400c281c503911032030403525103401501114480d410b85d024000d001681118042201681c4d0700f880101a020041c1a0000070038036180500d031544501e10050700c2150260240c01d4180705149010043d281510304242c400100d48500109101d00000f01c0b060454210050a83c40d4284c10350003090f16060361a17000c071416007a00d46441c11000c44401d44115042c0041030b1000c1603241c940004182c0e00002c500304540a074503030220815050030140d41c00000880d58a00880203a0107110b0703840841c180850428203e2498400005052a400101044141d680d40116090340341420100c0744051500500204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 420744703 1250 420743453 420743461
    0x30612230f120d05010905090a03142b06080a05030a032406050a0e091006030b0303041d090f06040b0105011b06060612050c162d081b0c09072105 64
    0x31a099009080050301c0500303040002c1b820b49400d0090f180204101f40003442501d0f4592411079161000004944224a0401101e41c10140c000085e101000d54100c43e41c4860213050307050b030121030b8241c2c80445960007440d200004a0b80100c291248118203040205d0f0084000400342030300340304e500c400c248d041e00240000c81d8560344907014103c003281c0c0d0346401062a11010800000b04001c580b550a040298501841001c0c425004030046550141c00c407801c2584444e402100342c16503841d00824115807504211070b94804001500003001d1890140040d802d00c1d840d407190b5a4030500602c1e040c043d18644824002800000740d44941d60082000c12441b6142d0000038541840c0a004082e11400c00001c0b40b4001201c0040710304001080a00c01c0b03410802e5900e00c02d840d0f2418989104d507040c0900c10301101b2001411a5221900c038480e800e070b850759100c4141504901d111100d00d125403246098a425442e16880542c11000508002001044800082815801c000e40d10441310741004c0c01c2c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 420745953 1250 420744703 420744733
    0x30c050c031002070b060d0203030913020d091202060a060e041212050412020f03040b071b0314010603061a1815040207202407020406080102031501030612230f 70
    0x1130f040651040c910285a0307280c40c0d040100b08281404080c4d4150002c1001c40d2152402ca084105c510400c2d050150a0900140f206400c030b43c00361000399100c0d03c803086122025a03050003000e0384401c8110013042214100400c5c000141402000181121030540f000c4c5048c0d03025200906a034005004140420302d4070780b5050b18100c00c2b285100c0003502c100d204422200c0c0d004000e4400b130720001e0808600300501501c82c07010703418175100180681c048040d0080081054511017203614070340302d40081242840c524240e02140c041e0400118100d01e0b0303806444e0f8640d100c043c110300c0c04420245031040313500c0d03051601050405a0042c2580948000340300c400704540d903000300208045a6000d0303500c01c1d1140b018094118412910a00b00d500311007643c20705d500504014280b4940040e0002039000d482c0c0c1007050881e40103a0f5140710030850207070701d49800d603414083c08010300795400000c0c003d041d00c1e50300e002e0700d800c20110180d20b08550144480c1d03150b108110000b9060140c008941306410b520b440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 420747203 1250 420745953 420745957
    0x405060a090806090307151802060408010c02060c070201050703080a112701020303090a031d1002060603010c052d07020924031506010f021002031006020f0a03020a030c050c031002 79
    0x400c002405800005007200d2800b200761900140c1140e40c10106c0c115404501c0010242d00d00164002c0140751407408c00360715400701501c00350414000004a000e41800040d190a000500107000d480e02080740c840180d91200690300745640c542014005034403412b0400c0050101c502c115039010342c01150216a0400b0207484214060842c0043c0c000c20030404012601d903c000c507401044c9038030140c020000288203400c010701050354149084500440d81c00081d024030420f45d0310800590081c1d0521039580380a10a0700c03062455401e085c1d00d080c0c042a0072035a0324240403402c0d0816900e101450000022102c100e03060302e540100b1003200c42c40e001035940e0480c44084c0540c82502c9005111a4041c00c0028110080d00c0304061404080e6031000c00440307484001c40d000b04214001d41d00c00c60300900182c00914000c040c61091000c010307061410080c50a0180d043c020083d07407000c000c220119401286040342540c062609a20a014600f085450459401c0460740c1601c01c07200d2042d0385900c2d684c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 420748453 1250 420747203 420747209
    0xf0308181b010305010b070c0b1e130303020105100303230d020a020a0c09020f07060902181510030212010b031807030c030c08030c070510020f12030603010507080106090b0a050405060a09 82
    0x20f04100c40d98070381e0201c0a0601803508000c0400110000901240350944081d08039021402144541c07000c82c00440d10058214201c1c0d07201c210022a010300800d07030203000d07103507018602c451201c15080c0340d80c46c010042c140c6d29107103010b0000c8882608044405140c2150310031051904203640e0340c001890002c0d90340d4a03180b8240e8150205d4180400d100c40580219218040400b900900300409034540078010210080708a03032022400c2d0130015105080304008d88594981001c03040d182030000700b4020080f2804008408040c410400e1031032190218148034156150303e04410f0b02c82c1d03140741100b0900746041c90f0a0074140b003000000001c1041000ac080b080d40c0c410340c4560b841907591011955240184210001503030011902030240e41040c0c0c1d00815001c81610413904203103141e00542d4203041401804880c891400001c2110509090141d103030030498600e0894101d624241004001041e41d006180202800049591000748100140c80c09007500900c000e640b03040e031043c09441c1d030744188 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 420749703 1250 420748453 420748457
    0x70903050610210f08030705041805010f06050a0c060e03070506090c0a14100c0201030605040c03022206090315060e010b0a1106070509060705010608010903020d0905030105040f0308181b01 83
    0xc0c3c2d42552980c404414481c00d582c0c0311042c04903400080d51611090f420052025040000a0100003400050f00d1a840034000205c880001d465061141c2d54408071000c0c6c210b102404010440b2002c451341c003944104d4440d03000440060000420640541144240e03040034042d03100e00e406000b0740740b1000c11140300300c10044404a051641c0d44d5032620081c40b4590710580c0c40121819441e20681c0606280d00c8524814900011003640392000075088400c0340052000103076002c40d001501d41c4162041d01c3d442881c0141c0e542246d49003440060401c00140001000001046018102903e440d041070024101558140216684403030410755a030700184c10140001d040301c02c2d6005000004141d00740940b05940c0c071070385000103400501503030342d10000046420b07640e503d20009682c10207200b0780c0340151080e4007402480101300d00041c001481034100134030a91602003400000707030071a40309888099041c102408140e540e01a091030301004403d801d541401000704a40030306c0c0d0407003589d0301520402d0f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 420750953 1250 420749703 420749729
    0x20603180607020601031203050619120b060604030f03051e0703031a0901030b010b1614010504020a0e090d0c0827030f0102130b070206041509050a060f0f08070903050610 75
    0x1280102e9030340d4006e10015010091354600203a442d48250090b44d4800c40c00381c601918190a02030000e0107000d00e0344120096469140900d042050540c01e50360070200440780b80782800c2c11038403801a0384003800402018840001000e50005002013000041c40e01c0140c1b07402d46074082414058040c21003030080800b185010700201115240003020302d4162034100304020480e03824007100720215032090710382c5210801141d800130b00007484000c0810790000640f0001ca0141440d00c1440410f034420740010214060362070800850900c00174050b000800c441c070740b149281d0b40500700414944100f10790004101400c2c00d80860b041c071500100c40066005404036000d401c10107011900302e000d030000359141c00c08040b03000c10915800c240545051030000b02a40e01e4591740b80c0c0d500b07148480c002c8040b000301307260301c00800952401040710703c0100494202805aa4140107008180c0c03100e60800009002d070310707004214098442d80d80c0c4005503038000111401810110006820210790b8803c01c0d4445103a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 420752203 1250 420750953 420750961
    0x5120a0c1704050112054602090f1e010e011e030603051006030b01030f051f1e060810050c04091802040b0109051302030403050f04230405060a0311030a0206031806 72
    0x210704c2160710901884460803105002c26070300c0404187c1402040b0350440c0072582d82c0a007910700820b60401c0b00d00180005a945421000f400607a14034000810310401198450301d4082c8203142180d910f4000034a801e08451040500580300660340c0a42c000751760460810580b01d0a40560041050701d005800b2210602800c0d440ba605072070081c00010446140c1500400c0041e58000002018600c5501510008020410900104010181f91100c943d4851a40720012054a0a48400c40b00501003c0c03020a0404410790395800f80c45883d0f14446540f1400500b819841c03038213803009810144414004080082c45804000d10002700a030f101d1032402d0040d100325801001454101c4030082c110540f01c00202d404a8025000208298103202c401c020074281c5000c50b0009102a0000c03031031864207200c07109188010185170642840c055803800b000c4c80010383d1071f814904112903000fa02c424403c20440082803c011302c2140c02500520080103120600c55a4030351850300103290001c50b9211340e5 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 420753453 1250 420752203 420752237
    0xe0604050601270230100905070906110f12042d12030201060e0708071805090c0a03090204020a08090f03030601080c090d0c0f06020d0302040305120a0c17040501 71
    0x3441c4030000481d4007400c24903e0640b4a640162034100380300c03056442d0b0000b5084004100f00048605030030241184410451135641120301d01024129060040041d0710300020007824001d40f90092400b400000e1001900714132040004c2203501c2c1e03039102643c1c59110300460850080d0064010f400100c005c06100548043b40603800c0300880c0d100c6000c0403001d6161a00110300341141d05400e0b811952140c00100b202038000e904180690019907580c8124070b00244010107102140ea41d500c1e810502c00d8040107107541cad2205094111002c011525910345030090258003e22502100940050000c17801c1d240c0c907a005000c141c8502e07615810785440301e110700c6042e0745030701c021580c450110f48028040f6199800080181c52483d038050480302000410f80c40d0290203000917440804814400c440070f00200f50b05012000010805040c20f6003414216902c0a86819054400543c2200c1c04644407050f40d20402054072116000070403504852800085501280c2c80b03401941d020518060b03000200c02 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 420754703 1250 420753453 420753479
    0xf10050129030106180f0308030a181212060e01080705011b030c030305040204020904090f2609090a1d030d0b010804080d05071e020a0b060a05060d15090e0604050601 73
    0x7501d0203061460f800d000d415924008200901483c8002002d03011500301090180c441c095401240b0003510303031034080d1465094802c030300c0998a58400c4008820001003c01e94036124100c900d00340f000140846454400040441da445948610904000041d0341d030340118100c41900c0c13003a070fa52081c0002003103201e40d1107050241c000f0000750603501500003084c8654003041d00644010005444c00e207490b000601a01d481702c2c000d45500c4040c031660301c2000101000708990303280b01c455503040b03140361100780107090090348107950241d0f112800041c0c0200040c0d10095181c5501070040d09071030030110401e070352500300c160b900381d5040c50405034042a6000d0f4200d60b10841e1b2202c481440c2c285c1080483d005844098001410300540a54400001c2c0301e10502300400c3c0e010f039004111200352814844070311007020704502c0c000c5900c1c6100380300b0303074031010200d5242107194003000c0b41c0c00390064034242130100e05038804503809182c015603240703101d8007042480c046c0e03010304110390103641c9a6074404488 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 420755953 1250 420754703 420754769
    0x21050a050301091806140f09010c0507020603090a17070b01230f0a180e120415110c060304060911150a0e0609041508100c02061302030f100501 63
    0x1103002030004005010240e00810120f030b0420344014000320f1965103241c1a10350b48050103c4402141c4100000c0408240d841e5031700484d903800070301010721441405051072244100182c0104030000001e550300008000b224440c56020b044a410343c10000e0020707003560060360b02220700340307110760000840c00c1001c04841a044003403503869448610001c200268410340840998001c5002180080e926080300c074401003a98280e040422149034000010b07003001c1d0f226002048503641800107103d10a03030700d0151503103808181848440500c40314641c0e4507080038003004941c440d000004201c10011150002d01c04244075604080202d5583d80800000310585a03202d0f503441000c0c05a081c2e00c910a801080342d400010f00f51a1604485201103029662003005129030340e6000d0400304940f8004014503100b0460100c0b0810502001c604001d4840744050030003003010040342044001d5503030602100c8000c00d81c5d903085038400c01c40c1350041009810241300d4010b285040e1081c2c5040003003030100b1b0b4110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 420757203 1250 420755953 420755957
    0x209010e0f0d0b071e1d060c030c060115080601031404060f0b0604030c2117090a0503012c1204032a030501090c0b04080a170c010921050a 61
    0x92030440418412210301d0300a4482d4440803070900c0d0310109182c00d003c94018412591107102c82c41711041c6540c2c0e408810140700c002c110381c10801e10030400c102141301e641c840c1c044503c2d65580c0e440c008928590b00a007181041e407030040000001303411071543c0d0119412280c0f0b03101d01600d42e807204010340403180203502c80b10050700301000007000202c840d842500403280c80000060802c1c80344002c11002d4002c0e800031624505140d4040c08a1103880308903405501e0b003813801e1b400c0102c2c4c070f0340d5070f2140c00e090404144030740c2d00100b44d2601c655590b07039200380640760150080205501c1e15a000080c40b0030a15541d03051700507412b001560880100b030980c43c0c005006402072905146a6402c0c0e40c0351711580041104d008120b000d0440c940b123500482c1d0085010300000b24000c002c60410007000b8841d9401600c030603208210421444001042d1b0781c0245401044110742c94500f8110701c00c5a11502032100580d518196100c0b041100124540c40385044c1a088582e04014600044c0e0781ca01c03540c81c103900 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 420758453 1250 420757203 420757217
    0x20301120f1407082b1209060605040908030a0b03071208130e09250f0b0c0a0c15080906130b0709080d050c0616050301050409080903070605071203020901 68
    0x10074100808905098401c900aa00503194001000c0c00d0102e240c201c5001a04a0030400a80e07419076011402c455408040011001452010190940340344171070a0341d0090311080f86c54140300180c0c3c420001481c0c050028010b140051030a8102c0c2d03401201c64210340c601c0c288c0f103249070703007400994101524100755041006403420385400070980c21440d103a842141402101096a0b001c40c2404c1d4041c0a0140083c4a054812200602502c1d105801915070320007209003082450b81000107d0b0403200c4c08002c4581d1400390903070507810020140300107400d0f20044100003c1f1000c0c82c80005882c44900d583e400c001d501c40500c1c0c281c442d00140c5101503c0f070780c0d00e0040c0e07012412803d1400d4100d90305040c2001c10b01e40c0d03480440e09140d50459041e0204902140d440d16810f030922556502c08040300401b21840c0704c900b0050303e103000c10700a136402213540740c140400f0404a1004c9818102004049801550381c8080040c00b55104900817913100001c86110b042050290003a40e41201058641c50 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 420759703 1250 420758453 420758489
    0x2130f18051c02071a09030a050102070c081f0504030519020d0e0a03080d1523100c0b0403030f0b120d020c060708030103030c030e090906010510020f0c0d0c030b09030a0305010504020301 82
    0x741c3c061740b000c03e40340c04a810401c900c42140d5810409001114417a000240e1100c90070304000304202640e41c40903031240c00c0403140d4a01c0107181c0e20396044412160000260685544c10222018007441d602100c9449030300210082d601d40004850143c4410740c2d4034915600320560920040821034032008141318020300c16a00c0e0095540c1051900c07040003452072124a981c0ca01000404510010391401c0e1140c408403440c0c3c5003011040d119004809051802101c1e19565030b801c49000014805400c065a885280310030502c117400c02d103402c0b1002461091f0415041c0c80b001e45884072060807101600c50598502c0ca10b00706541500c40c001d4204811a0550307207980c03801d840d403032200f0500b2010003141848ac01055965030038480e01651081000b40101e604103000d200200c03007084062810365100340f010b01c41490000455180c00d00c1d06441c02e00060700107150840003e1820340005042103e5801007000c0440000301500050303503a50703030500680e40da40e01403000700e00c001e004014001e40401a48 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 420760953 1250 420759703 420759719
    0x7031116030216030f060c05070506040b090c0604030501060905060a0614030901060b070b090d08060a091a0a0b1309020f042705190f0509070302130f18051c0207 71
    0x100d44818000c1c015a001003007442901c1000480700d8100700c44210321324607200240300240c8103d03d80c80e811828060f14107845511011741c1c40000510060554060000003004510705003d103d0160b54041c020359200c0b038481ca0028060482030241520f001c0c5480b000512518214012030200d4001d9110511180300a8200c0000ca6100802030700c10b66480300d5000500141d80001401c03030764041c00c010032060510744a45818035071010031341002c103e00c060a002c4280e0305c3d200d1007000c58202403400106241081c90000d88422401d003ca0740c424a201d0000a140f0710000c0203100310340031040444810740c2c0b60700c0580100c0c082c81030031051040c018002405001c010f050108194081207120307400c081c40b02c201c443d00b910310031500b17903281c03200ea241207022101d03990190080e150070f02c5005000078600002c1082e900c04c2c01e0310000e44101081d240c4520b92005940c8030420303804820005000d20b440d01440035103e0042404201c540d4811940404602d00300e0360000d4800c82d03034690281840070f1408a42c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 420762203 1250 420760953 420760987
    0xf030f06140d0614010f0e160816020a080d050906010b1e0906090d03030b0321090105031f030302010504030e1009090b030111040e150603130f060f150806070311 71
    0x8480e041e94030884c40011020120415000b031406001c004a040d081501c03079081180302401c0c2c91995090009081c003403640241c0350310f500c44040f084166031502d0910040b80740030400b60001d005050002213600b03041c1e07600e811640c89045000c003100c2869076141a15021442500d02107605060a09400c481d0600040000c1a01e0325008241900386205030000844131000c240040700440e5403850482154107080c410310706054000000a503a80064114400e414852099014100100007001400341c3d82c0700c0711100c2121000110403c3e285480b454003034020030003568150301048054000402928084044001ca9102d596401404a1500c1600710107014040c071065499500d0388605031006043d600034000800c00103825200c2e5080c41880d07102d480c1c0550a0441c066030041040141d1400f00500441c800c03030703209618814880c07450410780e0040459102d4450114244203a0f200c82e80340040101081c3c2d40c0c00415118183c81c0c01000798110740b594003492910403000d00c0408101c0c0045e0070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 420763453 1250 420762203 420762229
    0x1409032103161d1905031507020c0123031e090105010501021009080904050c0417070f09060302092202130504060e1b06220b0c010b0105031003140a06020a0f030f0614 73
    0x1440c4c695911000064149103143e00780745024100300b420000b0040d410444414040400c2c2414004016550184100140d80c41801c600c0650000046454100d1078203100401d107d4005000e00c0605044c207010f07010709020b01c101c90040c4110300000c4600b81903889141c2046510041c09841c268200702030102501c0014600c0c5000d01c814000001c00d40c0f0030b0021034203c078212002809041382800800c040b003131019004501518942030b0180016100d80e100c0381c2d0400c00741801d06080005046c4805001041990000d4109006400355250402290440b901030380c49903100b405a105240f0001e503441140485500c2120710a0903a81041d04100c40200780d86400c2c110600b0351030210710b6403007180138250380c404003001c6070005580002075004e01c80c0d1510481d0910b440d910314201880b9840310b5030200d0102500c0180d010481c2c0c0500340041290064640d0301038000d648910307000c80090165032055901c1008030f824802c0303200300083c003449020240c230f00100ca0102e10060201c240500c2445101d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 420764703 1250 420763453 420763489
    0x50f09090a12050d0509031303170d0c050304120e060a0e03030702040c020a260f0c0f07090b180609070c08041a030a0c0f1409032103161d 61
    0x3542900403460502c100e28618260343c4071603680700c1081820700102c0f81c004240c0c8407582c200f4400e0300f0300c1802000c2d0f0882100d8024040e01e240a0315030041c01182c2c82008041c40f6880d15041e1445000fa4009010314032031400381480e0300b8007440c3d02e0010f5801c132400e00c031466030044081001c0c0e0092402a40711038143d0034040e00326810700e0207a07808101143e03601902d24000d0b900240c0e00008100e0000030310106503484210807000303481c0c55200c60240d800781d9031035061400b2000ca02402030300c2c000c200c6000d41510311411a10215500e42c5141e004060b0a0120740c02466403ca043d929810407070000b03401000098800c0c2c40300e0340c5414046807107400c03010049810003410040003c004041160041c10f0009003006180d4900705081554112983c68000005010032400d08030794054120b1088403030722503104500c6540c1d00b80c450000e8241040d028507040c01407542519242030120034030255200c4d801d0301c0480e1541d01c01c1d5004c1a6002d46c0c01c640c100290030f122100380810740c00c3c00c103500d0f04010811 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 420765953 1250 420764703 420764713
    0xc1401020f030903070b07020f031812160501020105070314040b04020a180522120804020301020d02130807050a050303071506090f0207030914010e0909030c0303091006050901050f0909 81
    0x268920180c2d000740d64041140d4000709010050150000c02c407900610540000c1c6045940605850341702d00464001103103100710300c101810b50f91503c83c1130031941e602180c01c0d0752104160f07420070801d5490a001d22401503203007000281301540284a400380d078181c82e030000b080e2540c8650340d500625400410072600107981000010741410610030703000480c212098046502d15110078a20200c0400c0502d6200c0d80807a588803e0110790345107240000d0308642d29000e01d1a83d958004640a8440c008121803420b100107100310041c005030702001d0a4400190940e040e15954404004407204503000740d661542003000320f6400500c0b40300c203015403000f040c840454903903902e040c1c0030101c5d6a261000c811542d000a002030406078080d00e0300d005003104e400031181c00f00600e40000d0520640d00d0940740900300c9840481c001103000c006981c9001240d5080340e5480c60040e01300340c0c0b6944880c01d0000d80f50b0800d100480c19260524a86041c0c82c8090841c0324000c000400f00100d078030f0043e0a1805034055 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 420767203 1250 420765953 420765967
    0x715110f12100f0605030402031612020918060112060b030102041401030f050103030203030106110705121518030d0b01050c01050c031009110904150b0a030915020a0c140102 76
    0x2809068100c0c411405240c8a5800c801007500603000100401980312030210280048403450040c04103580d0289061074681e80d80340302203440c00094111140312216080340c00101c140303a021134404a68402d9400c20a02e07115800700387c100c085955020309032a04010014044620804c0b00d070360b0b105000346000b207036061f52032002c41d08a80c4141c200c1161440781031208044c550309400303145e820510300001082150b141d0346000b5140d01041c01008208458111424001d9104101081c041c020081c1015070321a0004009aa2691182c404401e02444080000e00a00d10900211500003c80f0f001c2d501c2e00300349100d188000c260300800141840700600c2034070751001d0240704561081d46c0100c48583e40782030a40d2415030740e810031740c01600002e003020841000000790301c0a60f2400c940603940441c2d0120100414a03010030a42c01501b065103000c140560540c0c1e1540148280314090b05004040d6040e01c01c48100f13074442c40f4100c0c8040785020406100203000309a4065101821400050501c04 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 420768453 1250 420767203 420767231
    0x3060c0c12182403021803150103231c121419020a090308090a0b030f0402010906030b030607080c1308070e1f091503060f0207051506060715 62
    0x80303041e680c60005a903031801520041c0c102c50b988000d8030080d00c0700b64101d981011060105000c076484002055008614110290700d8203800285806e07004013699807004030302840070507500b024442540d01d100580076104405070311001d0b0580a1503002c1c0030b03001070242074800342102c0407245003076000c1041c10074403504503a50070b1195402c0c5280180308041c09091481200381c000e804fc01926004910401000c245140c2102100086a9001c01b1035611101c1c007074009a940c8400e40d0102d082208000100000c90440c608080c1c07007140300b40c03600c2c840c007a00c8007030480803200096200c50305984242d0100d5000c5019400407903001451a040c030b440c0047d21002202288a0760380701480c1c980c8a0030050103959000d0140c00d504c088910505d010007006460384000c140303001e00c540e0244076590348548012051422101c4090761300150240461041c40c4103040080d4086003007501d013400303001c0d0000645034070300000c0d501401c0020019810b04800e07860340589407203084000d40200da42c51204440d020 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 420769703 1250 420768453 420768473
    0x23070309150b1824010306180905120703050703270303030b0f0301060b04170c060304030c05070b1c0f0b031b1f080702070e0712330812030402090103060c0c 69
    0x30144c01d09110144a04d8968203540416418032814107003401c4081c40f0800412038401e028070000c1c00c0c040340c4a03015041c103034101031003880c010700c1c07030140019402c060580104c010f05049109035604046d040e0380850005a41001584920320051240c0d02080424480d4000103000c0900810016082075490300103400c40e581ea0340111031003000413030208209a0380920443d000c070900e002910010b00342d000080c60910000f00000c00303216000c0300c8503091100401c803401c080c1c41e04000144c1d444000401c00100c8249000f801e41c0498140326250070491220f0103074440811001d00200081d401101c164400c405d024081036400c070340c40e40031070000c0d82c00c0460351500384641a142c0189034104082d009040c00c1641c3c1008520740e03c40c43c00d2010803039105044010078003110200250300e601d44400032481018207008840c2034003201510b00d00401c841d250f104204d4100104541c28103060358046105408202d901030f41c010410381c01000451116040601e003d01c2520f00701741003c4440d41c56038a04 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 420770953 1250 420769703 420769711
    0x60c070303030b1005070b060d17030c130803070b010314010b030a060b01030608071406070309170c03010608010c1407060b060c0d020606010801030b070f020f0123070309150b18 78
    0xf516112601c00c03c0c01d0094101042030154a80545032031025150b0404002004d001d1600500c4484030304001d00c51444540904440c10200e01c51381c900340b14180126a030040d00e40014010500e030130020b40e0503030000c02c40751000e500030200c001503869500d03401003112040000c0c40003952500c0012040d65018032031002c81b144292400100001030310f0005048454641040c8455401007806024512017003490124413042183d24a1750703088036240c00c90320104281d200381c0000140e24450108220041008020441d0a40c000c100c495903400c4005e0070707030704d51145130000304801122060325920b64200501074280100c01c081040040840410080d912540c042c4280ba04002500800198184091500a80c0074a04048954115210140c0002015110000740500c50000f0352046000784100c4041d01c141400810620f500906002000107982c2c030a41500381c030000000300c0c041d00a11071640d090b0740103001c0b0304949400200070310042c040c15511603805941c07c0c0781c12041000140b1143d02c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 420772203 1250 420770953 420770957
    0x3050402010203040918170408120d1d03070212060c0a050d090c1701050109050403080f041a0a020703020c030d211514090702011a010f1e02010608161202010509060c070303 76
    0x7030720710a00b04140d1200461fa004007407041c0801c010082c0b81030009140d803410001c800c2859481200340c15030f2004040f40410414032411820780b0124415011003d841147d00983c0d04041c40c100d40d1807015100d07070382111503800145043c000707225468450405015080e101c004000b4126110f80c80740143ea50440d030140310170724110082c4003060002801201c0c01402c0400c014009230030180d5018141e40300082010b040031092000040602041c000040e90560000040235070500f89400440040c1d40007200590162151141032001410300148050580b1040d0359801c000c4000482011040340301c02c0c1c901f500b072a8035003000804485d021001da000500c40341c400d0100c0f0640381014418250f1005103c00156450a4001440001c00d005910046079007460501080c00a0400581b03003004070495000c00c0c1c41019445601ca55015800324041e81d8050341295070701d071124004424202c81900803a0400680b5500f01c02c0154003032800b4020303280000307004c14104042c510305146040356581c01a00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 420773453 1250 420772203 420772241
    0xa02100e210105160c0804090f0f0e0d020f151623130e1302090901331e231315060c020306060d020114070b1501080115030504020102030409 62
    0x10540144d0000600b9589903003816a1040e10031b403075034403d90146218007102c0c42e86644041140d8034217980003000036410050308001480a4004441c0d83d409481004405031151058100300c410000171a04900c1e1b0080440320360b26542c082011192032000c01c502c1d8103104048050504000d1507240b89c10303620101980c565284d42050032645520700385640301f41c2040034510284507008c03030712111403c41c0d2030b0159640221921418080c1d4010502c0b12a04241251104020400041a04208412201c1072003003600c0c11502c480c01c0c800c00051090388003045600030f40d402c100c00070307800d000340001c1214101c12500c20800c100200c0c6401180704444103480d581d030b480040000840340c2c10100989020301e00003e05400036408203a0300c4501801003842011a000700004581c0b2a0091554901d00c0c3c012030b603102c1099280c0001c030048155100c8010308240058204154851a2082c0c1210100160f0740e014168045081e07000b000041c200768114001040042080c0785503001d101601541c82000c10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 420774703 1250 420773453 420773461
    0xc0f05030a09090525020715080f06090f040308060a0323010609060503030702190906030803040c0e0c0403121718010e0a0201140d020702030d110c030a02100e210105 73
    0x1041451540c00080341c0f02d180c10207005400ca005004030030810030003107181a180322501001c0e407405800340c3c01000d0701d611159800740100da0200001e07014914402d0200155114001001014030040780d107007490a06d240000b03408240b00303031109604040c001e0880e8003415140d031210381d91034803040b06020b01c0c03048888112a02110901c99440248100a01080910305010000f610f0344074030b51000e44102070900701c07402400c03810791401d00184020001008215070303134500320324190401c80301134270f000140000008006842c0480c152180ca500e0b03502c3c0d80703070a00f141d46d0740c0c0b51580500040d20400440019a40715800401c03541801469440d0103012004a88904142541c0c4940d040580580040050340b0050340c05c0000c440203c4440f00c0c1413515035401c2112000280904400030303500d403140d50415041342d504443d404020044000546000c054140103040d503908004200035044030984050b102c100d8401c800c00100048e00902c40040b050b1401000e8410304500920030495075540c4c4148 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 420775953 1250 420774703 420774707
    0x142106010e0103110f130801020c0a020a0b03010518090c040906050105310b0303191d0d0b07050901020c090405010515010c0b0a0218041a010801090e07090c0c0f05030a 74
    0x1180c1006400d20f004c0c0710800c2d0b001c03180c1d4550b00408112060500010941090110503403076408050003d40c40210344604500c0c501950b1031007400b405074000c0701000c0d404904800940d0451b81641d001800100b0100300f0b42c200c402c80814000d000170858000c06680012540d00c0c0d00410000b1401103c000c1100d5041004005028240c150300900031807101180d11703041c80b041c5500300d5080000440001d00d8112404c0400d04610580544410442e039405041c0010764100e141c690701e24005014240c5c00d0a83c00050000c10fa4403000040c2030840c4040c00a00914800c900929882406205617100c251114020601b0084103a41c11246651500c080045c5d00031034104880c0031400034640444412480e84440c1103200000d00682c02c103540000380003c0309400d00105110313414028104100b42200c070300640c5044e82c5c03802c9100d0300182507000001507644260103012940c1c141c880262031003038030785204400181610b40c2940c0a02c010800114081101503001a058502810155584040c04280 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 420777203 1250 420775953 420775967
    0x8130e010e011a2b0b03010216060f0e15010f0b030106020c0d020102101404050d08041a07050702060a020114010603150b09040e06010b071506230111061006090e040f0314210601 78
    0xc40b0b03006c1d030f1061040a17610648171101c1d41565800490000d142c001a1204030098070711a40002140d104040692450f800c0d07592000341201c9402000300041c3c1e840f183e22403040d00c030a1068800591188454151034502503d034200d006205004440015102941030000d803910407011004c034081c1c0c2400c02061140610156590390b9452800707a0b040c0c41c082d5100d90911b8240c004403c45d410745070b40002c1c1e60700c1c00341e0101c0e405150018210b607109c0c5c0d40014001d02030300003050b1000303000000400000c0c070303940203005031441405524601c405203424410303900c583c0e030040f20220b035100f92160b0303250140000c1402070b0707030182c02010708560343d80c102070a00800307415480c1e2080c4591460901c0801103030b02e9041c68001816010060640391500c5400102d403505085901102d0310700805060160301e284c08150300c400c48500d40c450f1b031a429a21140b080c40b101d411103018011070501c05040700000e200c2c0d0b0302543c09090b11030945d42010010350410040004450484e0702d40002ca1050044e1980c00c181 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 420778453 1250 420777203 420777221
    0x1060311030a170d11030a0c0f09030b0711010b0607050307020a061106040f0f0b0f09070f0311060318030c0c090916030b13020d08130e010e011a2b 65
    0x30040914040c5540c0d240c0c070300305000d5542000080d01290b220644c05550304080000d040c4901e00b15106e040c10340c4e0000081a0034041b14000c2101950a070184500410b82d02c4105d035003100c41ca2402e030f514401306460704403503070149000c05e569443e014413059481c000680340c0240590010768840300d0178414080036400030b0b0820401d010800e4050913000100040841c0d11980c031420b42c04102000749420310183c0b41c900001001824030200300100f0b60300911819104030010022034000640c3e4966104100050780030292801102238030741420740c02c09000450700050206140054004000001030a50b0080c0c0959000e61304845051410786c50b00305103680d0020010710280c646c49210410310340d0582d0483c0306c000c040481c0c1000050000e000c141c0627041494000c1c01400c8001d10f903203444170700307540f00301c05400309600d200c1008a601c084101d0800d040c0c4502d1060320318503900b4090800084800344c04d000032510760401240240a00f100300c2c54140d44d81c4550f0000c8045803c0030210700f038941c07080c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 420779703 1250 420778453 420778459
    0x904060e012405030411010c030e0d0f030e100905090c1b0303092b0818010903030b1801030c18151401030605040203070903061a040e100b090c03060402280201060311 73
    0x80300317100104880d821900c01c115024200340c982070710036103410349002c990500c95a40c480c44547c0c040051201d4125000d101710300c25501c005181210104105146038808480790001e21460024450360500c00440358000f0b149070b010b02d003004c940440c248a0001c030940d41061581021040c0101c400f801c11031200d4080b0030500400d403540710038003075602940e189040360080240c22400328601d031000d01c00c881000b120341c01c0244100c00c1c075401c1c084c000c5d00d5511003203401558100300c4404400e0420562906983d80080c0103d0b65074038001d13440380302e1a607200d021118503503100c5807101c1070420b004000c8001c010001c1038150f5810703030740000740844009a1109001318010005c2042556108000c5816280e00c00b40018070038845202034a86400d56601454004d441d040441c8050400001c000d6069404400309101c20079818042c090807680030340e19212285000d00100b81945040c2d005002001c0014808489074103c5440c00d03c40004100c0300c1402603551001d062040c0980750080141c1c580044d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 420780953 1250 420779703 420779707
    0x21305030d0f180b0f03130c150914030c0d1103011401060f02010903090b0a120c171f060c1a0c0418061427070306050907020609060c0904060e012405 66
    0x3003901c021842c81905d401030103401c000000552401041c0c0c2100490070740100b46152620345540114004464084500020076032038200003030960021600a54884800341c0601302d00c400117030520840540307002c003c40b80c2e0162303800c1d0a800354909206001030740300081141d04c2c1e00e515201000e415a44800c603c0001c59040840d0040426001800501220700140520780c0e5100061400c8501c1083d41400800b41401c01001416030f640c407551032040c010744075020b2465522940c600c004440d0004181400c48507101c481005854001d0020780b038001c0c0208100c1d80c421840d18030102c0340c480100c402088500c400708007442202e0141e159010814100e8804010080c2065059408442c0d1400e515104a50030303900061400115410300d000c8140174803018030381b8141840050301070003040c01224080c100c40740000e40d2136880000e006009021081c0a04510f88606c0880829640801c070541c0d00f03c2d03118007000494800c0e40b02c00301d0080041c000f614142c100400d01524800300445000760400c081 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 420782203 1250 420780953 420780959
    0x8070c0629040c0e0906030c04020f0309120c0a0b0a020415090e090f0a3e030c090105010f0c02040b150c06070e0901061112070609060b10050409021305030d0f18 71
    0x82c10b0031010b060220340c01c0740385d44e40350400280b40030b90358010a50000e0010410340030100250000d54000c0c03c1010640b1844410040c03035921600076026051031540c024410000452030791303040036400c00c0c00030401624083d00c8250280e181d000c0e0070288400589110000c108052070305542541203070300c810181a44122140383c465842a11910240412070403004400c406499501803c410040c030300601110682c018559850303006116a58601138068003403000c5061070b02d46451810780da0147c403101c001580102e0b0072100c00380c0001d0100c0e082aa01c02420315180e0b52101d08a880c0b08010450b01da850180c481a00e042c00350184c014000c0c80500c0d0304039020741d0794950003617066448920b0a14195424054514940a160780b84024500b1000681d4014403a0030b4005120b0f4900842007400585440001c4c4120401d0035400100054801c1c80103000320100e41c1c00400400d10b03114001c200442d15840002e040024006d400004500c104401010154120002210030400c660841028501d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 420783453 1250 420782203 420782207
    0xf0d11040503120309010e0a0b090c030a0c060503092802120102090f060309030d1109030114160309050109080a03060e0c07020d0303090f141006170a0308070c0629040c 74
    0x4095051030f80740341c00310010f50301c070500b5440411520311200c103e42c0c03007104a0410b441d080e40150f1f808000c030702503031760803020724100007031840d0b000c079070001c0307003580c4c951905e40f08581ca5040944541c08074000c0e031071408514011b000701c500050000007000c41070b400d09841008000da0300d500c1c520000e03034014441980c039a80c6d0407440341d00050050750b1040e42d958a09a1041c02c620462801d0804180b074440a5072400325060702400811509400030003222020340c2e503542c025401205d94191014094246154140c841c1e0440c4058a100c0c00001c10130701780b180d45510013a000030000c000045d0b0390310130070802403440c441e0582d0059040d0040c10b15100c45a0007003000300c29501400303001e0507101c8054004100c01110100501a045880e00500c943c0c12100c850f11205100048105103042c01c1001c00c19269010f80084035141d04001082e0800c0c1640c0c0544054034005d02c0310003800417000000700410b100b4000e442c2803003044403c3d8010b4072002c421400c441c0c00340c0e002d8180518a07003004200181c1d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 420784703 1250 420783453 420783463
    0x807180b0c0c0d08070204180c090f0c1d01050f070503041e0506040608070e06090301090f020916020c040c020705030d02010c08150906090c0c0a050303090f060c0304060506010309080f0d11040503 86
    0x16405031000b040145070f1503d04940b01d9100c1c40024613001503c0000910226292f0165806200d400c4080c80f524180c0081100e0320b00501810184040c1703503050039011507000d10700400d0b4954850484500384103c0d611490304540007030344048220901c1c9070300502c4000031603003044054801214040c0c00e1a040000c000c2111000811030410b0141c41c1c1d0030b084480c0e45180950700b0700364006000f44926034040c54107500e840c82181049024502c440b0204108690040802038100c42e1540106409800002044054429580c0c00001d5025420340070445032001d0080120305906500041465080341c41d00821005004044901c454003180c001344041d076580d15807540141003203c4022032503c540e4500003040c8660395580120f44101d1800d4006c102012015612442a00c002c0d5031042c00390200e407a0b15901c00729950102c000040001800182590340110781107203042c5400a2180c000c1d543e01e000540c0040c030320f103038101b0003c101031080000a0061003c600d2404054038289460711010a60ba4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 420785953 1250 420784703 420784717
    0x2040b0f0705160b1206040b010e151303030c050d020c010507021012020409060f08060c0304030c050705090708091006180e0109061407120216030807180b0c0c0d08 72
    0x1140001015400d100b4104802c0d0729a85050181e4070815954400c40f0303880f940010030744200102d4440025005151920900030843c106840b110383d140744031010020780c1850348034031200fa90000d01202c0701d00442e0102d908042c621a4541e0f90481c00705040c05442c000c09116020210342c4001034030980340c3d83c040305942c2c0c020f506a9004800784404c040aa038000d80d034900d410402c034802710300000c5031405600410215400f606c4c01d84086516071541c1c0d9200c2d4011030710001501010000b080019220314050fa10041c02a03054559031030301e440018508803001c0c0c41600001d456003050111002080c040c20500c4d1540c69403c11000f89421038904025800e01da900e46600c2e03440000152040003034100c0e000b00d42e4402c030100100380322020b541612400030341c0c10b4000540d139040303010401d090f41e100b111802c200c010300074144c80912b95401c80360514018880c90802c1030b0080d0041c0280b121401d001c0140c8440391319551203400c110509440c00510040c411f01c03c0301f40703d54080108014030119011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 420787203 1250 420785953 420785977
    0x9020114131404021b1e03090913050703080301030302100b0d050607031a0901090f05010605030403120906021b0a05010c1818020903070e0a0b0f0906041a0409050c031002040b 77
    0x4818807000010f030003401002c158001c03000780b0110400794800c001c02d40200207440ca00e40101451405409550b03a8000c0f50035480e0400000c01c085041c40d48520083c1c10414403d000701d40f201d5449685403074854000f81d008401690010002807a04003490240903018001519030306060314654a90f5030340c481000d8202c034141aa41c5268a418003188419203ca406000c3c0980e5207035650740d01c4070401001107580842d030745442c0200100c0c0051141e0112805660990b03070b096003541440b4220741c010020890100d40281e400c000c500707100952140014008130381107000c1d0096070042c1c00c020382507400c8072000d00300f0060070316040305030801c0e081000000d880305141314107820090201d01d040244a801182c0780e161058400c002041003045514505c02c0c51014020720110824509200944124031620380e4800b100340000b56050070030390710124985401c220710020000b00c00010408880d00e01d40140c0701504604000425800d0412100480c48804c0c5421845d00d890649400894090b941c0e0142c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 420788453 1250 420787203 420787229
    0x50c180112150308070c14013005010324020c100e1608070f050103020a05070305131710050906060616110301050a06060e040c0203040620100902011413 67
    0xe803051036038400310241e003a01808030b04860312400e1000440d00000c0e0116145810700130042211511220118040c003810303120308089001c1c203034a41f03018440c0c0c810701094207901840b580100c00c0007402940e0003180144940305464441144e46212803240728900315030b40f03004101000040c038000948170400d045015000951350150300d4101e007040f080420f00401d00801d05408a015840462000c0c00c035031401000d46903d541c0d480054050340640966140402d005005080109000314020161420b07450100001c190b16000c9036200081e0308105140c091744880220585482c807442041e80084e00100142141d00d0300c40c00050041c4525041c1104035580c0e94418410403505204450340b0909c01402440036250030402580140254818040001e2005421804a06180c45281010202d6070f020354600350514006a40409942c10250300b800c8808808501d244414405400984002c8401041c0107143d80001020707200301074040d00342c40c0e00030000200b014510118190032200000c000e80703 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 420789703 1250 420788453 420788477
    0x3806180604090204080c1201060e07030504141221040f140703060f050615090117220f02010207050109180903051207021606030608061f03050f01050a050c1801 70
    0xd4540c091540800c45070780c00402e0104d8490f4000c214084100415039001c0344a4540b059118203980040c41007000300414500071a000074841d4004940c4103004440030030300404284640d92a04c80c0164003040d81c01e002094070344613817820702031061005640011004403414140c5548602c9880c1040080c602e4040b00d4403000401e2050000100450b00210100119040c04007040080c09085610b540301c1d181c000e040010f42046c6505a5070803030bc043e0b6460740142490440d640804401800b50b400d400d512450070789101c44c160a03500d4001d440f50404200032000713840060318090103a0015418003070403100a01ca2500ca50a0098003142c0d10500462100315509041d030f1103100f080580c28540c920300d010010110f4000524504100c2d501c440c000302c0d10b60b140411400c0f00d259003c1c0300d080b900030030301180080803180f6048040700c15040c1d894001940c0c83d0346151410f83c03808040086651181b04102d07402015100341503108040524447c9402c40700c1424001030207030180c8950520407180004c1c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 420790953 1250 420789703 420789709
    0xf0e2101060503060a02090906061603031a0a0308040e01090c050706020a1701090b01090e06030705010c08120106170108010603021302070606050a0f03050618061b0d380618 76
    0x2000300b101505544040c2014014a4041c0d800510018020200c00020407510305155040312080c0402e1031001c03850382d10304d0703a04a02030864203581c0300c14140d51a04560003940d030100d8060080d0720603024a41d80f0b910300080c11414840580c05664182c4c0b0304002a510380e5000f030100d4070711541c030100059803000316440039502a1031540e80c040019500c1da0000c01c8440090b8885c086003c3c00b6205c071080e80c0c0d03441c19440480c8a0854040f50590041c0200300441e502520714000c100e4401c4400d6428440003107100e80344000240c4c0980002140ea100b902c03084c4200f24402405031013004003d03c003050454000c905803030170301e8278080000e03540015606c05002207540502c0240c84010400d1004907600c0d5580409040e0b24003095405010f05000b0a62880014403d0800d489114000c1c007000d0755500060a54209601c0010700311620030000b80c28004003d108090700241032000e0341e080ca64034000140c1d030a000440511103150072a9001094035aa02001d0f10341301ca20309001c1d035a003401a8004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 420792203 1250 420790953 420790961
    0x1502030703050f0c030a0e040509010c0e21011b2a0b06011b0606051003050f06060f0c01141801020703140306030f0a08030601032403030f03020c1501060f0e2101 71
    0xc1c4e1800da020100b40d0844082c2d209500600e0303040103d4041c0440c2d1180c0f00700a080b03550482e642c0000c11a0704240907060706100081000260002c00075066010040c5211030075a0034403a030f0101031075403414007240216005240d182e8410704e1b002c103c011503006641070001e400d5010201030905030b072840025065a102d584403000c0c040d403460740700f680043c0e135250003c050301d458020303070348641d2000300e50302d00300d0b482445064480c041d107183d9020b80d6150041030007100c0d8030003604c490012070304124010020200340608074950082480310300b4035242c0800c83c1c0d45c00b9480d030f01d9902031076401040700b8808268024440034002d0700420016942c4c1d00c40d68000f0740303004018049071005005e02e204a00905c001500911301c158070070b80381031100c000101100c00e00c1c00300c00c1a1003214142951000d00200f0321410181d4007a90003424014a41683d04d10b40e01d28024110b802000446101d000502c407507940301c02544214401c43c142180c81509041c001100c4603d480000c005451400e0180307a0090001d404c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 420793453 1250 420792203 420792217
    0x308180d02100e12090d020301060302150a02011112060f0307080a050102031b090303220b0705030306100201062303101506170103030e01031d06071101061502030703050f 75
    0x10868451a0000d000a51a09411010009141d00e4520004100203001c141403500c40c001038031241c548443c4004001d154554040d080e60190341e202d001000603205e000c00c00100c10040c0c00c4164480607500002402e64000007a000d89000081c802002c103900e150942c00d80109048800b105d050b1682c201003860400140d000e0600e500c0f84081c2c01c418014194002e50141c05c142565440000642410710204c3c8902c20120b60182e004000024401d44004040e03036400c44088900306050365541c4000440e600100c030141e07450b400000a01603e440c2150342507041888038002444118134000751107900c0c0109130315860a004076a0644d40c1542e50500c41c0396032200700600c04001e44035100303d14100e0180b09005600c080385111110400c0a85080440e0341201c0d4150781d4006a0001000110003a00ca42424068495072039244620303070010605c00305100301c0c001c0d80d40c5c07072000209010050945200d50303c40c0b0105d10b40c40c0d14840341140c0c0801210007860b00340c14142c1ea50082000903a940d4400c040e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 420794703 1250 420793453 420793501
    0x60d020411030c0a0809190b0711030d0203070f0903021e03030c10060f08060f131a16030605060c0304050105070203030705240a18120e09040b04050105160c0308 71
    0x2080001220b1050301401c0e0000403a03907200030503a0380d103a5241d61f51010b51510b11054041e04040d04c00035400c2d461721940001940380030066966580d110900d0b40e046200d448000341c1e00030040200c6282c3c4854403441030001c5251480500d865078000c00c00000c120b40342003401e1406809000401c0d24200101da207030b104000b046039075405003103003000004c08841c024030800c1100c2031800a4400c800040c09401030119500040740b1751940c07039800404081c44030003100d030464601400c034074040303040601034800c0740d10b01d207241400c48403110b0040845515812007886100c4c14480c01401c0c440c00400d0f502540c83c20b08100395220b1407400000c2c511300a08100410b03606c1204540003001012024040700c803524100c484280744c642d0924081500c071104010404040d14481002c08a0240384280b41100320380d09000886000d034101040400340c04440c2980e510b8204818881040302c06d100c0c050b07000c09174042040000500140080500404180250410031001c0c04515031003070020b42000450041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 420795953 1250 420794703 420794707
    0x1180305090118080307020906060c07120f080a0207060f030606080606130305030309030702044a070e090f122209140402030d2109060f05010b070b090106050603060d020411 76
    0x2103c804d541c96004c81c070100e0044200d800850f0f010709081e030640d4a0074513000044c100f054104890710080c4180244103580c200302200c50f00000c540e24170010004584940e016242c0541001005010040f03400882c07000c05141c01c03401c02c5665408100b02c1d0f0080d80071100e070303552002151080843e842103a04081c01e103000010034802c0310040080200003580c8252420b110001240320440842254103005895012100803001c002c0103120200203c2805590034030218608919803c80c80c102030394001500d40015002404505c0c0410001c400c06404080300500100019142e20f040c14092003140d80600101c1c044021b84085450b04c0d490301400c0b4840c01007007407900040c2c0d90703603031503405640982c081e00801100c807010758802d4410601c1c0000804800e41c2c0c0700e0061060a0040000070402d0b01c060303a6941c910f80c0c14403500c0c0100c034000c1210814198035030203071b0309100501e00000340c4084243da14001081109484e0319060f42d51100c011103a00180301214001309024210b80311344d5a8102e100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 420797203 1250 420795953 420795959
    0x11060a0c2d060f0b040c180b04050a0b16080c07030c050a03120c0609051203011404060e060d0c0f0f080f0616030207020619090911041823070c031101180305090118 72
    0x44052016040ca51f0248840c1413190b0300d0141c541203224602505411048826080c000d0560303840040c00c4000074404600d28502c80c940718000190407a042c460b659401c20300c2c04009104c1c0385015a00584804c0320f1030040c080c40c590b00c1140c541901d0380c0d01001e200081d0108800e00c0450b07840101c1c2c468024094910302c00078400d03040b000e40c0c4240039203200c02104042450f62428984128000e640804880b6402900c84004121854410703d40071540c25403049070202d13801c0450300204e4018803003085202d4405091100e01410464034855003440b0342d000e0702c10054015802c10302f403005060306007030050f90ba0000d4008030301c0600c075100c0d0314007201a41c1d54641103101e03400b030301000c121514a0004c10040e0155203003040c4a1150344158180d0f00a04002c28098030790b81e60145e044400b412441c220300d000d59402280c503d000c11180f84000c944006011018160044e012560305107d1400800070101e1050311b005040700f00c01005003c206c0301146840480c0d00590980d00071100034203842e21140d43d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 420798453 1250 420797203 420797207
    0x903040b030f0a0c0302120106050d020c010e0609010b0904031b02131a1003060f210f05150105010f120f0e03160203010f020a081311060a0c2d060f0b040c 68
    0xc2c1590036440070740c03501c1c040c0700303038284071384240c80c240290544040c000d42d01c1c100c821541500b1094001c00d2080c0d0810620004290910580e41e1200718440904941e02d0113100842c2101e0b41c1e5110f482c0106c0700c034001c1100003580700340d5400301e0050f10784000210365400d0010403002041c002065100c107151007400e0003d21a5446061101a001c948038007600d1021b0b0422419198148540f02250340180d100344600004000a130220901e104805054865aa1a02c01e22840c05d41010f40d140c2e0400254100509200030075203001d40b400382000c2c5181016000000c5c00e4401418521000b90741e550503802c5040c80e42d030010b122407a030f1041220389801064800340e5508030390440886c032035861b081414003841c105000361400600944c880305172640e110300e420311529000c0c800031582d18610130034844d450fa852001901e06150365980e5032690902c40d01e082e409100c410b01c000c00030800420780ca000e0006050703a241070f016600810109200015102060242c0080104960701034100321220340015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 420799703 1250 420798453 420798481
    0x305071e11071a04060e03030c03040e04060501090207021008040606090e0c120d081602070806040609021c05120d11040303020102070c060801180c05070611091005030f0a050903040b03 81
    0x401c4809a54400ea03030303011400a00d61070340c1e03030a5242c03e01c01d0004008441c003800d600440300c140074080ea450001200901401c40c1c0c040e0308105181d0607807500303100c00e00c89184200c9000d4558420110f103002e00c2900011590184401007004005202c000079040004a80110008080ca00400d200c444000419a9100d03090809002e010302a0b0703a408030329202000070350000c41040c0e901d580c8000d85901444082142c0d900351280b055214007600000c0e00c0108101c1913100d1303806150001080d440314810030004490f5200368802c86061442d000c2c0104102040d814000724800340e4240c1e640314a20900c8001d420300340b07110050340714045000014181c041d001032004078854039140c2c02040d29507c00b6030341c5c141c0078096120480030b210811000b0042d41c0d03204000010071800c1090924609a59000546000140700c1d0034018010441d4001410001e12180045030a800d180e42186030800d0038040344d4a000b040e507114039886101281403d5014001c40e805003511800d51540c034901800070340c1542e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 420800953 1250 420799703 420799727
    0x2503080106271401024605421806010303080c1c090609030306050d1709010912030f0e300709060609140105190305071e 53
    0x41120240c070340b45000412002282d541e4002d26184958504014042507070480b0744007084c3c19032043c0c401c3d24411140c1c8500b00380150b40303101c0e401151159518004810442001104c031440c1c006280fa0000040011a509a882c282044040452225480031031000e8881d04101f0010316129040c00070690b07920300b8443d03c00c003440c59044001d0350894065a130780d80400d10015002a820381d012880c8041c00000a01101c0f0344c601c040f60068641442c04811146031410803611155510308200801d034050092200901c0100d4a032012000140c0704c410503000742c4029440c00c640c0016040320704da030084000502031301144d0100c041d03254a80c41c0107401d1624014150020a0500c000b02c28545000045218081207805440b00021505c3c500c60054800306011112680204040420110118805e1074000c0c0b2890341d50103a601e00d030512490b000140d80211504125042000341c0d0340c0c1c1289400c0034101d84841c980010156030700f54080342c42802d00015002c0c40089003c1d4010001e078003102c01110 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 420802203 1250 420800953 420800957
    0x5030a05130b0a0b01090f0b0d060f060507080d2c010f0605100806180a0f0b030102040b0406110304030206031303110d020d0f140403030306170c060f2503080106 71
    0x291640c0c540c0341120401814000c20010700301000500001d4076130451044903c060600702c0c115078580d0f6080040300b116800400c078100003c515040d08000798007580300180320b800041c1008505214006006100d101000342c480a000981c241ea065a26801401010784422500e04e205c1c0d60b0005003500d4803130348940000c0c20340c281718089807155414450602129402090381d459140d0185c01a9500a40103104952010300d41d02070040081e0b5002e2618450350a0f04800102c00c803904039440c04540341c00503602d000b68414031051001c4000c3c0070880f4103276115400e090722103440343c040c01465031041e03400083d0403100210601c00007905030308800040350b1207505c9814090b40c000512643c0c0c1d40c2e003480740c1d5005038070100c11226420300038a80f07075210049518010136401c5201c104105142e1044c0e0080f00041e540d0380c010032210480d070383d800f003030349200101400c03040400b03030002402409013048141c01040c002400301503001c41c0c50702040200380031187c00f40c510000ca04000d043c440d02403082d100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 420803453 1250 420802203 420802211
    0x7051005010e1f0b12090109051e0f01060e010e04051c0512130b0103230a1a16020d0f1e03050703060605090a030602030c070209011e0605031e070306090c05030a 71
    0x15094220b0703c1e2040d2107400c15003d05240c60004d181d228000c015003182855580d88003040040380c800c1c416000864502800b400a1511603031219140c030a0701010600c060740350460501000b65540041030440300000b03060440354845051050a003a10314200c0c2d030000c0440d200c244440c5821401810309400c018500d0030a6036038061402540d0019180c0041036030f112180140000b41400f103012106880c1c0d1000502141541051180780c48030420b02a1740e440e0841c5071380c000000903504000d91000c0030302a04041c1410544001e950b421046800005000c948001c02d80551310800f500e501e440c5c0c000180700e4110107800d01c054020b103400c0da004030000307081c1580464032500810441e12913400c00343c402c04a40d0301d5034881c40300941000c1d2110080b90001c206601c00b69944c401d98034043d007031520840003440d0210548044070101c680c041018060144104041a04505400c220703034007e03180110603561b1402c80407030040c03165070003c0c40702910304515010115400800381d88549143c0070104 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 420804703 1250 420803453 420803491
    0x4060b040204081e071a070210020106120b010905070302040302100e040b0d12030b10020d031808030c03090f060c160c08030406030212130c0b07080c01050a02070308100e0c07051005010e 82
    0x561181c1040c0a06c1d01407000030046072006080030700f80000804690310000803d181c5038507007100502c0040e9030544844d1407440040c0f0011200d8400c1c00d4100c4401d0800710b1a041c40c5a021401086400d05640188010107107022070036103564000f035560880041c41c00c0c294030100e142145058600d0002c2c0740010f0302c3c100441741a07040c021130070004245241c0003041401e8810008501504051264050721000c0f201c003000059150703400346000f1101c0c14440d6403a89850b1111525149031074514140692044040c011094442d03021038801180d00903201341481690b007031080c4002c021754000e00d40c0c1c4c07100007000241e03a98954041d1500000d050140d40050b201c1e01391002117103408000c0540a1020004c080016050340001420310307034483d103923160500c210100001e007142e10841d52022800e030001090810140d100481d86e078000c0c1d0401c6e510400608042c8240c80c0918021f10510120900140c3c010600004200d1038045000b03c03c014881d030b6854502040d0710080544008140800314280c0e0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 420805953 1250 420804703 420804719
    0x20d020703031d0d1b080d0504030e10090302061803150411040b060903102d02040e011221020c0418031103030925080604051501050402040501020604060b040204081e07 74
    0x401c0118a0f0783d9681c03080105d003500780c4040b4a10844040ba07000c241003100c6c00c1d0200070380c010a44110301a468a1501c1c0d080d40d41030007800d4050414000c10001d646034244010ba8414081c5c0300e07003045001180b01c2a202d20404285030000d49034440410300340103c200001c000500168000c00d5206607000d001c105501c90510505000b58900c85078940c010150004c803925042e8001418201c3c064598055804500482400311803001e5504040d5a00001c05102604414241c43d0040003140c0003c0034910b80c0d62a81612108151100301c0c0c0321000200101030a4070270418840000b20041007041100581d0010080030300c0b540200310040f803942074804442d201c000c000d60f0310502c0b000f0042c100c04440b00414031480b2140c01e4403425154602500414500c07000c1011610652280c1e0041c00042080c100e401c043c514160312052050b80100f00c01e00150340d001c10595041136000130081019445440058082c0c019600100220f1040201c43c001040c2102c0840391442614000c0e81c030025124028 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 420807203 1250 420805953 420805963
    0x5131407030b040f0c0e010f03111c0b091204090213090902010f11030d050103081210051003051509161b020901030803041502030c09120706080c030a020d020703031d 73
    0x201400b4a022000081c020840700111070300054424034449031095250700704501c90182c00c0c7c10001048800e481c0510400103066a540c0120a080380c1c490030b5242e680c4100d2824649443e801010010b070000402d600f810100004011114000d40c0c260703d86407110f002c00000d400c00800c0d6110380c180480c0c0010180300314440d0b100c0701030701070b5a0b030b1440c84800d22045d107602203040c6401d16584820403101c0c0180328107211311800303584210f082c20364030f160307076804032421001c0540948050300710307074004004a541d01006504442074500700810f07690340319401020030402041400c1e80101c10b040c10003220040481e150308500d0215100e00d5001da02c4008250056203440e40000d4024031007500610118807e5409160301c144604504000f148005128034240e030001c1c3e03901000c1d00004140b0551501e090303103c0c0794a0951440050412034a003038401011910090100700760728000002150088031640c045a468105000040d0f41d9000340e0b1400070001e140700c5d1400c01ca4003441001400d4040c10110f2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 420808453 1250 420807203 420807209
    0x5120c131a091308070f0213050402180906070e06040308040e06010206010f0803070809040e07060801050f030f060a020a12050f0709080c0907051605010e060402040e0d08070f05070605131407 84
    0xc5444002c2c803a030750344c078651540145800c0d104035204070744d0040140d0305da0308a055403050804021405081520511210013003061004030404400b5040008003100021255807000c010310300a0004115240804d40d070340b01e16000030300201070000c1c0100700d81820100c9140030303250aa080710500e0381c1c4c1e0140046040322500402c585500b08003d4000030030040c130302800c041c080044c030004070100b00d005140c2c0340941c02d900803c0400e50f03581c0104458900007841090800c0b05401034646100b4240304140c481c000203015620096000c00c45071080340c840c1180d00c4a0340039030f91040100f4240340710110241802255030382d00241c0706039404241503401051000c0e034000090009070983d212160140c480e0340100120b003004501c2c2c1440e8001080e424090a0413070080c00000c4c01c03450415006110540c1d290b290b40140540c07000c81280f052039882244158045c0300361604d000d1506641c10101e0301841040350184c0042d040006001c104003507804108a850701c502000d15204100480e0261070301d010f44 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 420809703 1250 420808453 420808471
    0xf030f010605041805070905060d0e011d06061915021005012102010c060b0301020f0304021e03070b0a09030602030901020d0b0a060903060b150c100f0b0a05120c131a09 74
    0x420311301c070890016005150003403640c0c184510600e4a900124105411161200072141d0312080c00d0310412000b8030600c0301015155944045c004000f00c1401c3e99010040c1031607007d644440085080b52400022201c041c01258000c014002c950800007036542e08110001c0d00000d203890000200000500e80708216010540d14000151140d500155030003408040c003030381c5054a640402c411541c0030310080c80c030750ba0300c120469281d041c03038010301a065480185191448040c500310140d42c0e503001865400300c418504032942d4a421003a01100c174404c05600041c5a40d0001c401d00141d800c06402411000c5091802001081c0d50502080050107044c8120320110754240f0045c004a221138026842e1000080d04c80d8060040702d410b200700c02d40c0420003000c0560400c00c0314130764a41040c091000002c0a54105003d0740007840001491111944182c621803180c2201c1c25800b000300b0b2100040341d290040510343d00c01da980c240040a4aa0b4000491420300f035040051102e01d40094400d00420400e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 420810953 1250 420809703 420809729
    0x1140106020d051215121c08060415050904051005040b041b15030c0212041214011a060705010905010c0e100306080c120a0602040f0512010207240e030f030f01060504 73
    0xb2103099440044000c8a80141a00006c51030b8000200b010301c000a041070141c1c4c9130316036a404004d000301000341059101d0b60601b9a094822400850b0078030940d401145c440c03003161140c0c0f401c5442d0601c00203d803280982044104028840c07203000541c400e9000360409100c03c1c04a07203144c40349201500ac0c1c40c05900200c0c182aa0091190703110b00030900c2140115810014010215039040e0400c0d84144903050082d01900300f049200c0e0703004507803d10014020300101504180f8642408030308100c1c9405000042405e60502100f5080401c0840d0040e0082208202020380145080c0540c0010ba0003a4003c8100d4045a0701c20311136082254100406032505852800800c001c00c8006989402c0781d20035010b4010210381184003d1009281105080c0b144500d00014032400441d10186036200d41d105100d042d01040e011a9605103040c1030700b1800281602074900c0000501c42c1e407410903410f110103c3c1540c0700c846070a00950282424285844443e0303a03410040394144500d004114802207a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 420812203 1250 420810953 420810961
    0xd1e0c080313090b030703060603150e0706050d09110915011d0a030b06010908060f071d131113120605010512072c04120801080102092b0501140106020d0512 69
    0x1107a4402c0c450b401300181520041c4d039070f0b611020159003103600160b400c45480c1c0e0000000c0340343c5204c0e81c4a00c414000140c2200380c075100d806410b134043c0d8003000c00041d031500d61910401805c203030424002503008000f61000d040c00410380c605480d212101501081c1000200c0d642e410214240f03154081000389490781060440c0d032031055041010302080d0501c5a4150003040c034010a0001e1407241004040d250050f05d017075071000300100c440a811000e10303101c21741d0354240c03074403610a599031003444032801203000648d0491080e030071310071110b9200c011000d143e008a2075411084254201c180190000d00c0242d807079804010110707544050b10145a031159004100f60703159908079610804c00c0211109013025002c0c00d416401c1804c03101102d4020040030640030440c0c0148141e4003402c0008021400c040700f070400700340c0c030407500c090400174007450103242c54480310b180107090080f551090091000004140c2c030000d6000080c06600c0160040042ca0010207105100b580c1d124141440e2040103030311 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 420813453 1250 420812203 420812219
    0xd05010c03141611010b06040e4f0204050c070c0f0b0301061209050a11030d0f0f0c06061d0402090a05060105030a020a020f070e011703090a030b060d1e0c080313 71
    0x500003030302c3c4e855480d00801080d6988500140000784071640c0300d01c400e4506403140015500044040356910250124840f00c0403607a600b4142d40e0b09414442d007140d0340501c03450208940c442c03240007513100341448200078807408035070082c1070717034a01c038000b080c41d0b8a840d000d4503042c14101d80070b055540507050004000c007030b00c1110181d80c41160ba520018625441e5180c0a081414a070700545211382000e8140030340d800c080194982020041c0751240e4001103a940c000c0007203192142070002c000303204800d00244985940510014880c440f42401a0801c0a0400514040c02c84007a4490b400d0b00000a070101d4440c09814480c0d08142d440d2442c5944102ca920003d401c43c501c01821882110860380301950200141070250850200506c9150300d820900213410000780014403e40d0414070450025403a2051004240c0ba400030a19030350f80c0c0c8080205144030704810024002039183e074100c0010414082c41329905170700400c05600d0098071084e082c0e036a44600d41c01c1c0841d41966a07801c11180c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 420814703 1250 420813453 420813467
    0x706050402010c050708010c11010513020622080d020f06090705130906020a020f0c03070302010804081e0a09051309081603020f0115050301060501090305070915050d05010c031416 79
    0x15105041c0680380500700c0d2540c0d1700c1d21040781c1150740169911140c031a01640c100500f00131000740d5070000c0c400344c5002d00031200440c1041000070b024810108100e88802150700b20230000a10b004080d40405039a1021a503a0710041c09a42015015040c02030400c9140450030501c41d00c0410002c0c00c0c400c0c908002d000c16081c01d100083c51096441703d5181c0000c015000412545149500800740112004090b9003072140c4140c030707240701e54071034501040181d0700200c0380395220b40c000e00c030315464440019891801c81c00261702c0341524480041e01701c0110350080000400c0c0c0344262481135103000030b40b0320f035804c03101b69480103002d10006010030032140501d8828400a80d2081c8169040d500403030841c1401e40c1c81c0c00101ca800070900d0402845142401d100c1c0380e00500007441c000000903d0740d160603480e0210f44c041d0701200b0ba101c1c00b201446810908490300203140140015258031003d08025000b49192110f1400003810583c0705003018010103142e5019035064245841d14582480003034882c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 420815953 1250 420814703 420814711
    0xb0c0301151d150a030e0c130203060f0405040f12030204050a03141612060e1c0807090f031202061005060f0702030c3d08040605151e040b0a030206070605 68
    0x188842e0865095544402055040d0840d40c0a503560711078182d9240a02503482e18450f8004550240440d075101e0380c0c1e490025680403420083c01a40d2352922008902c440d0343c0041c030540c0050603c0c2c00e00c03041040d90380300482064080c00d6011516513503420110300768800ca11402d030388889800d1050000c9400302a02103011080e03541100c24401510304402d80a00b19503010203c008280c602060512442c0e0051800302c0b801000905052048a0103110481c0c040444600c00c106601000410740360046202c0000751022121484240766286020581c01c00215854401070050300d0210f500b02a511f45c0840545000600442c10908680340e004ca8503044010207030380c588961001508070f61141c220340c80048250b83d859900441809c414041c2c0001b00ca0588009507012008450a142c0d0101882c0c3d041030744841c0c04215500c2c0c06540c0883c000e02669503580c817000c03e4651650440080321141c40c1c8000903a0309008030035054040040150951002a4025208000c0c100000d581544200c0e40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 420817203 1250 420815953 420815987
    0x512010305062d04290c0405030f010b090c0717122205060a02130b0f0c070803122404020a09050a060c03080c0a02070f030803011d0426091c0b0c030115 67
    0x10608aa656092010030b03071b40500760351800641808542414400d0384010b09100000b40010903144012550511004000d003020034030204040c0104001084856900c0e2192038104c1d8480108110350f91031024203640d050b110b8840c080f03040202052500c0034001442e04040030b400940c0c0e60101c12006940320300140c40407845801da011500d80c001030b0240128030014040c01e80c44400c1c07405524a05403181e0015511544140105511a040f40500c030b0f1340034244505401c482962041040050b03216840102d170301c5070000c500600d03069408031078a800c940c81181c41101003030344d07a0340c10342c0c0703034070071401e01400048c0d04c840001c4903e200513009169111691049607500707170b5204000d407041a456081103605503400001045541d02c0200c1660050b23120142080d05414a81d5801d0a20724048015060b01c540c100c2c0d884101e030101c8415174a4601020341140c0200700182051a00025090340c203d44200309080402c80d59000308050342d040c5d40042c42c510b40820345194047d1070780b416103061407030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 420818453 1250 420817203 420817253
    0x150e0d060213060203090a0b190e032a031006081b0f10021014070e01080402040b0a080c1c02030a03230711010806010201150b09010512010305062d04 66
    0x100b08031810030050040101c0e60166803103003440c0c1d08200b040c0902e030b0300004100000b40071014801740021240d041c0c0c400c060901c140540e150002080c01c120342030420001224170003003107001a42c4460b801c2921072508506031040300c0d80c040542c2c0202c60090007040030030b5201c6261100f49050b4442c0010f901c00d00141001e200c4000540020303100701160b0310403401a00300791354513005401280503d46040b184801d03e55818a0f01c000c000344183c0032080009d041101050118003503440d00d03440700c00002d1001d0081c4800586440003595504049504c29000302c22064007400500c4a140322141c1c1503600038054003031060399031012244016202142c1c0d041076405c0d0100410060350000400215105032074092100c038100f4005040c0740c000614140c15a41007050403c00304618460f404142c0b41240d070701d291110303040c02c0100c80d0750044e82080f5208056030300011090050000d01c86100756030b0790050284504040c4c120305804802c00c01b039a07400c03194120129000841c0c841041c0c0c042c0c000718902c80 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 420819703 1250 420818453 420818467
    0xf090c0b0706021b010c023a05120421051216050423041116080f0403080c0114012102090402040b032d0109050c1e090106090906150e0d0602 62
    0x14184c48460000f42800c1d80d9034049224440c0d4040c400d0400e92030300c0c007144240602400001c4d52540628119041083d54181c01c16038425016500343c904c55018425105918a090f2400303080c0c0d090400280b03001c11201070b051b80c0d489071140c800c0796111821508210855101c03d00890b40c2141e10000071400c0c00000c2c800070030016a0011245c20408110a00d4207802840805000850300c1b0000103402c541d5040225961103081003409006160740b2840143c0d5070350440140d0016401141c00080100074009000c44521030150042c420021118a607400e007640d890f29145c204001000d1404007000b0300d0002880580391000314294002e0000d000852282d038000c6c0060b0804184260086140304030412241c06140744c040380c0e001010409000700045070301525802c1d0f8940118080b170380f007107150500c3c1401100e002c0e0400344078541c01412101141d40c40b03003c01b50442d02140144000103140c02d00c0040c054080c101d990342042525116140d80071001c2e0b080c031550703603000c4200b682d910360200180 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 420820953 1250 420819703 420819727
    0x903030603021003140109060323013b0a0515070e1201020c0c010525020604030f03080109180803130c0e10060305060307150c0c0e0a09060f090c0b070602 68
    0x540003416903030b0f07400035800a240203500301010b01031b0018114603182c100c05000144a559400000c064000c1d500c10019207802107480c098039040242c04cc8000310504100c01c101005000c0d403c07181c1e005106003180640d0321644503030743c8c4000302001d811980b1900350f04501e4155021141c0d0001c001d860900405200e00d804601090f42d8015040402c2e0360014500080d02014000144c07107100c24a4041e140100c00c43d0102c0c0451345001064000e035001040d1202190341d02022500155840007459800504034180580501002d00c96280201d0174220820303d03440410303d03481c0b107165000c448542191102c0c494289007a0301c40c9002c40c2c8115074660301040c1907240007807030b520030300d408054114002e09082004040d03c4001d40703458000d601290060003290381c11000e50a10150501d000c0310500f096082c1581110117070ba12468030200510180071410701140c112010140c01201d0030b104111000701c200c421030340344010241008902c100c00303000614010000b0940e19000d45c13409420b1000100704 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 420822203 1250 420820953 420820969
    0x4030f05010b09070f020c032a0d06110403021c0f141006080102040906091a060a020307140601140108190209030c1302030109110708030415020c060f04150c0210090303060302 77
    0x1c607010030700c40101c080710a5070412000300c401e48107501404003e030307050042840400350342049004460002492790641c1e00d07030804540c0a19000031042c48035241541410030291700600060707001e00c1a01c81725240803410031040801c556809400000b03014159202d40e18a042c07406412a2180121094030740070411901405010b040100c000507071310f6107007100010444046a00407075055040c11501040c40c4080003010b0202602642d5460741c3d0010200228154441c3c81001403258480020404070001c0014007941a6902c0c0c0e0351031000741c02c1c90700c01074820f00c0c412031f69060901004c0915000a076440c5c1c000d0a0762403400707030440300d9122101001070b0141c10481e8103000102e6000c001045010356600070043c4200803204c00b5845d001098030f0f80e8500307110080015045402a507030040090055504a80356082000f056030402d04100d0007007030540c4800c2e9030543e5131a074403c0450b211000b051144c109a2252900203040d120079040c5040017829040302d06406050395200004003584900074 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 420823453 1250 420822203 420822211
    0x2160b040c090b03161401050909090607030614090a0b3c0d1520030108011a01090524191214060d020d060605100c0203010e011104030f05010b09 64
    0x84031860b04161581040b658402c0546101ea44148003450918089210301820f035501440c1003100b075040d000c010384181c820341002a402081c120b04014180b2400320780c81c0c0c0a032169540c14004140d03644a200c5910710781c65403a82c0d108022070302203201034074107034050400c00e00007a112140304500c2c0c41d1007c030040003000d0700e210013010300071a00141c8902c020312424a514111348086181c5d100f6110030420024010002d036866a88445003110310000c24081da500501000b110395903980c48540180c0030348142ca041c0f40d1800c0015424030351941c002d0754035009413032000d800352401c1c41d0b0141907200403086100c00c1111107082000301080100c08201c1e80c0708084c15603190140706c2e080e407003a0315040303d00300e420507a212101801401074999032440c0030f210054040320722250145d000c0c00c001b402400c0961003581e00025100040d00c0035500001c40c1104140218000c116401144d404107090b180d1700c490700104548100024000600807401003800d190141d400040c180c50810301062030050255 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 420824703 1250 420823453 420823463
    0xc0a02070306110903060916150203160606090507090503060a020a03090c060f080c0301080312061f0e130504050601030602130f181109220f0212010e0f011802160b04 73
    0x21120061700b001c210b9103030072240341320050909020300181106031041074010507552906d01000500d009100304180c0e0348800c4001d08441401101e86401c0000b00030500c540c0c3d010504100000e00054002c0c00e1120031078001502504091742c9520700a8001d5008400b0380c0c0a06a071148400c02060401031100c1c007516540e29200c1d13280b000b000001e02588801412010292070400051000f8040801075543c070030042c2e004540542c903803000048100c0001070410a00e8071001c2070358044140d101e2341074454008192642c050140c10004190305441044a02804036444000108005849a4001c003a280400c04e05810500d4940054a4881c01e03140d104040d080880d10400300542024458440001c0a12150f18500000b41c808500c0704008840e05108024100100100d034801c0c9801c140500b0228042c00c542e5291086280c15095400380100c03490030b03840000254407080c81130700c041e05031140c0d102d900c005440c0601c5424040c1d1b026820345280c6919109070640020342c21a4024003591240c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 420825953 1250 420824703 420824707
    0x3010207081c0e0d0509010c08040504050f10060906090b2115150711010f030609020412060605190e040206130b03150f060a081b0703050d1505090c0a0207030611 71
    0x1158181c0103a600d011100c0f90300b6081603406101040d002400c8400c407000078249480358080c68100040d8600030341d401035030440e080404002ca41101461090710602d810390300d050801b40c1300c260481d510b00e114010540030661030301052115400c040045d0401e040342c8080448a45900840341191031000e641c210058400d0445c110342902c0d00c5c0b49281d03c4c8010284110342044140d844450621440c0d109090501a4078110501994800d81202d0061700c082801596200c2d84c0b420401d42c40c59450500380c0e02d492410501086500c2c09850f01d07500700c0c1c0c3d1b000e41d40408030b050034182103007580b01400490f8890010054008101450325a0b03000404c00364074925205e14110f00d03610f1555003900380c000c0c4070710800c00e02401c0b59a200f03000e030703002600300c1e29054080d0750f255003d00d000c0c82c0c00010001142e10b03002c15403000305035004c80280100c0580382014010540d90017540442c081c2d01d40500344c3c0c0090524009110400030401907c40d02e4490f10403035805076581d0301c0c1c980c110360002c03020b05116940 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 420827203 1250 420825953 420825997
    0x200102090a0e100b16020904051e0a0b010e010e0c0f0c0105130317040b01180f0e0717010608030904091e080919120b06030a12020601061218030e0301020708 69
    0xa5980120001d01189420a141c11003c80707401e0300d100d81d17180d00203105034418800304051010402c1034140b40750001c03801c56201c2c01420103165a60360761160441d21000c00c0c3c0700114070708100007101c9040300d44141e00044641c80e0040c09028a8100c00d0200d500004180b190720001c44003409000e016034220015102c580c3c00a090041c03828440501c450000d000b900c06000019103446205811600b0800030040e0485401160101800d0800c4c070240b025402c021241285903008940001140c081414000f5a04150f1409500741e4510340300300350302c2c0e4105105c9a8100c0c1825006144010702c11070203003083c0d0410781201403040301c5090080e1080b21000c5090312081c10706c0d05000e8165041c0391000c401503803402ca400c0480b00b0101000401004419002c00c0543e10104201e42d451540408000000103074510700079030b00c0c002441010001040c80062004c484c075103202d400c03c001c9801007100d4811030651000c1c0c0d05e0b0f502080d1700e00d405650800c61030000c61510006854104140713b01c1012900d4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 420828453 1250 420827203 420827221
    0x14010608011d0a0b0d06020f12070f0f18090e01090c27020f040f03060b030106120201051603120603060e010c05091f2001090311030a200102090a0e 65
    0x8058220190440300c1c01c0b00100020101c8001030307804220100081079003018140490010030122070000c0c500b5001040c1c038030b801040140030300311038915400903c90030340d1845403c0790140900e45418001c14000120054501d125038138002c20020403070107080e9603d80e1240804101e61880c005122582d554a10400c02c1090300130070500100014503200760110200c1900008054520f60907400032a40000d5210801c1d030740c1c90581740100114076240c0d00c050b550b42042405441d110319140d10a5182030341c08554203040256011b032564041e0340f000c1c184405151034804042c2644410b40c148a04158480d0140c00d1501a41010314032460300415040b401e00e80346400c1d14040140401407150621141d40c0c01c0d180c41e51501594030002c40800d800c0d142e042c0c800e84a446000050391050071500d0750070221054150444006d0751310075500c5424120100740016128068040b9803000240e484500340c0d078614041f1155494102c4020005182c20442d500007500902c4982c400113a45800a0170803100c59 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 420829703 1250 420828453 420828467
    0x9050618030901031e0c0c14010c0509130e0706020a230a020121090f020f100503130309170708070b0a051207020a060e1e0f0604020d0213140106 64
    0x5103a440000d60035580824291039000d0310410078101540e9540e040c001c442d1800d0141c1141034116010041010910b03402000125980002d5414510000881c840a601441030010b0240d2035510903051042c62410821026520603070744c000b0300d455440716051204140002001840c4513001443d00c60114544074010201010b8000c80800c1170400346100c441011409001d9154246402845a22002541c004034050a20300031700742031a0000403800c00018098482c907040c000c550707540100000c0010070000300000b40341c250001d1800d1001c00e03121a2560010380180340f003070410036000358440540410352282e401d0310104681c04000104a8204180000e90140c07124101207480c101c4206000380243c070400e4020505a0890f20005642e40d10a0003244140d60b44010b040c8a103c0120100550750080701c03420f209643d61549d040300020f400051000039800d048000f40115594507003c004449590000903030b000790303650000382c90a41c0384c0d1103032414100c0402c882400c0c035414014010300c20 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 420830953 1250 420829703 420829711
    0x307060e0f01050c151b03162028050307062c2d06100602100204140d0302010204080f030d0c0804020306040b1b0403201815190801090506 61
    0x4048100401c1c1003150000c1158640500c549000c824251541d011a001d40d503000d00c0c20a89540c8080248194501100300311230502c0c03004c2d503405041b8403095440d034100c4050303003e01c40707050b5000901d02c41144003d0010341e0740448854103050304210742c1d500c0312415a8482c89080b40c000c0e6841c4840ea4103c0c0301c0c81c40c0380359a80308000c50380a845174028801d9983d01c01a00d603090048220307080700081d210400c0790702030640c80382c1c1054880a040c4404801070b00740d52030040d44058000c1c0e8074441c0c007050310381c401c0d203080b10b4255510010f4441c1501c10301c9245681402c041e01155020000403400c840104070700040d000349000116503480c2140d51603403c50741140444c4042081810604c00542d500042450300aa0003810710803442d2905c54414a030640d81410007003540602160005c2031005100c0ba0420809500035950610030041c0200000d85141e0300703d40407a120030502003910500c1c03852074140c501c100a4503070120400d0065881d1807400555116800c580e44a0007050200b25080c45100e400c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 420832203 1250 420830953 420830957
    0x903200105040201020601030308101a091f05040513020f0423030a020d0308070c0c2706030203070b030a020d0912021011041e0317090909031303060b0d020307060e0f01 74
    0xc1410b155000039241d0300c040c8400703420400300c480494103c03411515001c0040943c4c0d4891001090861495100e5420490800d4410900d0175158440c2c100c008681e29200c4156580325442c2c6070402003004502150243c880c039000e90709100400702110200010f201900c581c1030710707200700d920403c900903a0a00c09405540640c00141da00340050f2034406220781103640c5800d144019694118046401011800340a04130070a60600000d240c002c9950100442c07910101c040030b9444692200c5040e941e031848000e40540c4000410003024203400c001c0c582142603a4000351401244030088c10980d41e107520240c3d00d2040114170111100e0301001741400f200e181800521000b188408507000314000d901c00c201c06502d103042c00004d4114100900d1001c0c540c0261200c1115110610a02c403640052000034010168080450010107000058a502c2e00c100802210078a06590b1454040d0120440d50340e00428071064540041e5001d1000c100505074950f101d0304603043e124100310000d00c1070498281 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 420833453 1250 420832203 420832211
    0x3082a030a080a021602090406050a06050108130215130906150813200d051b12060103080a051b06060a0504060b030109092f09010518070c03021009032001 68
    0x101c440d003295030a940f12480280058445250b80340300c2c00d1281140d84000c1d48013484008100030030091780d00c018014643e812040200b140c840c40103403103c0c001960700c002c90107a0300405030010300e04000b4a0000208500c1d6150622020300c0c031a0980340c0e103940003100780039107a51003400202c80340310720242600031a24000405040440340c400c448456100d0141040d801d001c00389000004100600d68424005882da445000880c20455207c1021000503108050252109810303460044076500d40203180c030020b0651b69180d46c0c0d8000b4154401201081407120a1151210559030200840c00c0c08480001800c41ca02c0e207038042210035480f40e00240d00c218a400c00c14003094030341c0700030342c0d055a04c014400192210141001801011010840300003501d248030901c0001104c200c20308400181500ea03031020343d0700d42c010010b86c0802c20100c40096080d5030009a81c00d441000400c0a8030b00070700603140348a048000e8071050b500790a40a502207941840c0303640400b840d8180d03200c640c0220000800c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 420834703 1250 420833453 420833467
    0x904050c040507210b061e070c0501030c020d08101a030403230d050402030111041e23010e010e04050a0e0c10020613080919050f040b220603082a03 65
    0x14042c04a0342c0e40d2600075542c0e802c815003581b41c25080307402c9440380403019070aa03080e05104010300e600c80324084070076018940380011a94017a025400c9c8091041d0041d08454071101401c8803900c0f80100b01c0c400b0340019034000148050b1140c0c070742d00070340001116203503649003508002e0300e030001030b100c500d03092800c241150380400d180c50142ea41c01085603401064640f00e600020740500680061042411000180003518880542c0c0081d615400000c41228030f42e61034010302400c107841c4000d82c07841d101446007104558800e06a03803c036180141000b499100004003c54100d0f502190174001442e0b45030403144840404002050304183c00321190b41c011504884002d40300c0c01c1c0544030440d0800140d10780360810a0483c1542c442ca203010b0444ea40c0303078802641c80100b840c640c3c82280d000c1c0300c09039801c8055013440e0103032034012403018003254542c40300d81240307044184085c000344050b19603c440200000d159071004000d07624441c51001c205007021040048100c180303566101c56a8401c10400b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 420835953 1250 420834703 420834737
    0x170f0a0c031b0b0c0f0d050a0615020109020a0909080d050a0204170a020312092b02010e1e1011071403060105100e01080c0705030d05010611010b01090b090d020904050c040507 77
    0x1030344100070b4800e084e102c110004001889000d084a5290424185401c100315590302790f200400702d8600445603080000c049200b0381c200d078070000b0b01039000045460f044c001c07140c840d004401c1b041d108039400c1e481d190034000440304840701a11050010317900064100000044a0344030000f0140c4400507200c1d03c200c0e540013943c1d844015011645066000c10000740680d207800c4404418440c003003440064613407001120b9158400140200e000c50030300c4101021074200200035070003200c2440781e0f81541d0f4605000308144e01c4150460213040180c2c1003032040c01c003036080c0103d0380100140604175695140c504d04150903ca4141c20003070040c4110084820340e664880040c8440c0c0c2d40070b0800211039110455500098450800c0150481c840058414542141540032504031511a9544030300503601c1050b4034282c0e14000c0d41c5a00042c8035040500100700c24000502030200300608032180e2042c20b6000c00c161001c206d4054882e40c001e0206c1c00150308280c000d150340f10405281c4207030600903142c20703 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 420837203 1250 420835953 420835973
    0xf0a090c0c060606140d0509211e0306010c0605101d0108010b040908042c18010605030304081015050a0e09010b01050304030f0c05100203010b1c1404170f0a0c031b 72
    0x611b8030748644400c0403440449041c050050480c0c0080e01140d05412546000b2009500c0700a800c0c08810031046003450709500002500d000c1d2380140d440003c1000380ea22100c0140c1405400c1501251251100180401c6007048400514020714000f400b1585040e50311804c40b52201c0d10319000d030382040710703000000382580c0494064035020f00d19035004542103410080360f40754210210b4409039042062100c0e080401000010391041a0020b01c041900c13442455100d0160f84140502076100d8503000400200729001042d0703110000d0350b2810a940e40d10001590042290301c6443c0c001105070503c51420b00038050180d40050a003030941c42c60074240d500400042080710501c04028004002c142000000e210b0140509800c000c00d5441c1d5031240d07210301c550f034801d44403a2089011048600840130f07090142c803d1103401c00070040360650340e54880282d81d80140c418a508180c0811002d0200c40074000545410072840c0d440320762030300207850050312003501e0003140c085241418481100040e90022 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 420838453 1250 420837203 420837217
    0x30f0501141503040606030203030a120c171612020a03020408150105130507031508060712092a171518100c1106010806070f140301050f0a090c0c06060614 68
    0x2800340d0780c96413142010802400b494000035454040020000049a40905050301102c000da600f0000b4840082003500d003846405520b82a0402d203000090450305411007245442459051205402e0500700300e0b03030300300d920440e03102004c40c0c0c1c046028094480e08000c012412400080458813950400340012101005001c083c90300c2929800002d42003131103601f048410542c0304d050348980545a4680544034901240c00070002242d400e401c44000d40d5500640c0e0740c513500458a0300d289071443e4040a8201c0141401e94200b50200400141064010340f41c0008515500060000f400322940213114444024010710107d4881e940e00e1000f102021400f0149a504000005070518004405031340c04101d603c280760f01c074022107000144000340030170141d1141c07038148e0710703000f010342007040c2030340e00040011803d064100c3c1840180040d00f0207107181e00c8000e01c01020400c01e13580d50901c8205072580c0b403000303000280029000b00c08011007030003060050300c03581c280340013800311b2441140c103a40a500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 420839703 1250 420838453 420838489
    0x3060e070509091009090b2d0604050c09150d050a0204030b13151409060603030a0903080c12160c09110901080a022a0616170a0f0c030f050114 63
    0x340102d02c50050750104c4100401a2100034000c2088038100310380d50b1a02110070058503150f00790002900082082840700741c1b4030b22684900140c03100c40c148801010010400309043da010041c0d00020b40c1e400030a0500c501018028685e244000f581e41c1e400d0318170140c22070a0341d03401800244001200c440c0349030b03405902130040800309d503e54204884a1101002401102403030210b0b006084042e00c10601c0c0f141e0300d03e604503030751612407100b850364922400a5860000d6810481800000c01c4400201010310300b410845000c0000500781c40400d40c800300301c3e0000c24403044c05d08000c02007c0a0a4002041d419030104400140c1c400f10303600c036104145800d030400c2407030030001e4070700f400d030398103542141e4401150f441e4441e0204000749200c4083d10584160b0340306a00008201e0b1880001c0d034000070100f907a80101d6aa40c2000b80201c1c0301010b05022451501e0b0581c40300006080c0c4180c5000b11500c0d9400b052021990410a0880d00107800641004840d10b0a84840b511051800d0141320489 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 420840953 1250 420839703 420839719
    0x3060c02010605040e0a021c0803070503040615060c11120613020a0b180a0e070c020402070303141513020f19181e08030a1d040e03120703060e070509 66
    0x1420080380107006039085198443e1400d2004a90f0440014806a14510a8800f01020a0940068036502c02c0c010300003400620104005100e0f580302e0009560814803602000c9101c0006411212890100b0f4112900040c00c40341001300380b1000301c2c1c808081d69425a0514810880748024036120b060003800c403581201d900f0810f0085450b04450180100380c00004143c440410030200000ea130400c9040c60310031031081e000030401c000041c41040c080c00054603002e0015405a080c130010303401000082d0141507595016516807455035241c1c034170641300200e185006882c90001c120208403184001181c0034030612188100a00480843d00700c0d1303004200140545043c09802c68446640c64030000f00603000040c00183d071407240c03d07020004101c0c0107001901a0710342c180d46a4034096100f00c1000910000100c14010941d07a04040865001502c040340b60b00f00e101f00980783d6400035000401c503203800e201300692540c0c1031207107102520042038020247e0911031001002409031710400780c414002 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 420842203 1250 420840953 420840971
    0x109050405071a0c0312070f09060806010c0f060e0109120c0b0f0a110d020c010c050903030901032a27120b0a06050a1e0605040f090914031209160f0306 67
    0x40e4041d0f0b070318080c00301c0880e5a01e07040881b40420f000b82c15212040842e0b003003560114480e00490020043d14400d030f41d024415600c020044604a00c050800d036100303440d80180754082070040c0205014134106100125802200d4509481c18801103406c3c03c040020305010304001441d4012040d4100d000c10101114541b129107030389001303080600e6054000440001d6141009100307401420480603900c0080003401030981081c1c0e154440c1f07080c50369250b0000c0006003030640c00381d44a40c5a5040c1c90b010125081c1032100910342400c1c00c00828004102d240315007242c0410400302094907044141101c0c8500c503e0805455005e2000700c60040c0030b203800100080041c445640901c2c001d09004083d80c05580d03640f0104202c48403514110000515481c1e03022070614040d0085030103c500304041000750510301000b8000503ca00e220858540031180742129400788100050408910403040140f4207090015003289060307103c0e90700a10240d00c50350100080c266404240040700e403c20400b18512007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 420843453 1250 420842203 420842249
    0x13020c01022107140703050901050706090611090a09090c0302010503090c0904030503040308100509191104060e0901080d0807030f0e061006120b03072d0305060a05010905040507 78
    0x9041c0c0c90700481c480701c2c00002052900c0102e102e00800f100c0e112000b07040400c45403070a951150420260120b10300b040006800d500c170f44020000d4a00032200041c29414a030f17141010b41c3d078019081e000405000c00c8050144ca0011900c10090000f40010000302819964040c1d4843e150312001e8144100440000e400d044c0520003c0b004c08802000480c4a140c50f240150007a00240c07011750001d241500094049080a100c540503103c0040c07800f561035481d02c1d6017081440711900c0000c00c1035112400700400c1c0340800054005401551210894500e01900780503103108160b2100006034810088031102540081500c2c2e00300d40c4a01c1c0100300d8854442003171014040700000d09103030f44100710410514031494210001500c0a60780c411410491140884054881a0301519813542007100204081c400e0040303840f110f5020390020400e104240010a800107000c1d80c001c0e20590000000c2209500e85449414054400c0010400241c1000c0c1c0b600d5035905c40c103001d901c10071107021401000d000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 420844703 1250 420843453 420843457
    0x9030715050705030316030b060304020d140a060e0f0f03040e061c0506130606080705090f10050d030c060609050408160c05130f0e0604021003110927100513020c0102 73
    0x40c0c00804407580c0e801c2c591b0401859001511031000040e181800c01043e80c40e00204881c0582d40082c0103040c81141902c4240c205008028405441c0c483d101c6401c00244039400303952210030074100a4030303000c070910014909114a4091241540e001040207010382c41d402c651003900310740c042e10341c0c510b440000108440d880c240000050414030802c003c002d607203174260800034101c9101d180103220055075554859903880ca40c0c0255070340407c1d82070020301c03400e607600d8516a1121000c403020f0101d0f03585a01107000e062a4010a6002916010300117091148a004040041013150380400c03442c606900c8282417801541d5245031884182c00c504420301c0a107200d2980130b45401013500859074120b00b441002001c82810b100c2029040020403030100502147e02c900c0350790040e08110399421103540490080c41140040050050140b214400b075465007440c481c8050301058220507107003a00c400d0441514401007540b810b042d001a001d11040d203c82440340c000c01c240e80d001684a000c0020001e000e4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 420845953 1250 420844703 420844717
    0x30307020607240203090c091906030308090601080c0105040303050c0703020406060c020f0d050a0b07030905070605071a070207050d0503160807023c13050c09010909020903071505 79
    0x3200c046500340520080b41030003003500c1200c202020502043e0201842680000c8402e208181c1081d000540c0c142811100380d5480724954160782005404004001e088a40540003a400240588100182a0743c00c01806024000d6080209a070001007000241144680e0200404011000c50701e00340302407040080b2400307158001d00c2408101d464901c02031201c00700c61420303031140c107082e407600d403403401c00c1c46140c0c0b00e182d0404045c000b000441d4075406255000941000c1c00c0555800013900400d005103c104050a420754500380e0311001030070f05d01d0900b46401709024540744004140540300350001814421248203641403080c08510341411400e601139403400c0e5102c51501e407009810028500300900781103208503880300906202c0e10390301c0b024a403201e070410412800000501400040481c2e0b034090084002c15400d4141e84050000003551401d0740c8541030324202240314800c540e045030314207015141c11a02141080028400607507a40b07400e20450071300d015001004d002c258890b01c1254030b5 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 420847203 1250 420845953 420845959
    0xc0d0203010f050108060a230c0306060f18011d010c0204050c0f040902070201020f0703030c020d0212011406091e010315060b0f0307020106061e030f0f15050a0602060118090203030702 81
    0x102e40c0d40345c26040e110801122074000061425542400603000540c1014144a000303c900035503540300c0d903101100d80c1c406880c0e682d0240c8140203003201c14a00c40014034440c403419520385188030201001412900c20003d990766030300b0303580c0e03486181790740d00549290400303404990100f03998940010400851280e1031621018003000200810309142d90b40042c60501c0c17003a802c83d20030660100d4810b86a081c14000100098418901c030301c054a00744014929003800181165003416030308240500315241500b09050b243e40c1c0ca0100155407030840c03440d40d84410826842d4402e170401401003801e1080502000b000d17121822402d5034006141d50245016200c8071107442ea8521a10190311001c0c1c1040741d680c0e00541c20142c01051309403140d220028000003145050200009000056002e400a2200880c0043c0c0e140301c81a80d42c240c0c0c1c0070702200031003054100e010090802040c805a500d0079007100040d0350101004001121030100b8102890000960025203c0001e2000a00b18481d000000e58 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 420848453 1250 420847203 420847211
    0xb06060903251d010b07060204050603190608030f070f050705091f091116050120070501050105090f13030c021801090e0c010e0103150504090804081e0c0d0203010f 72
    0x1601d4000341c9070161400001c0e0740d901c002c2c2580c60b01500e503d004070012854809481200412000c6070305805000d800e40308070005800e0a031104003040c895081214220309103c86c0c0d42c01c00049244a114000180900e40701451a1424008035611288100c50000342061040d040300014020705000d000c2c05454008c143c02d243d03003061590f4145e0008001980c4414650307022001500d075409210302200303032a05102c1f2504150301c1c80d11507045880000d00968580d500c82607d022100d0101c041016240401900c582e128986410f04508481c0c05030021401500644203200204502d10103441e4400f50483c103e000e044810f2038103c5552158000c02900f1105524282c0200c3c203108050340d050300d138480410040c2208501e82503580302003080c1c171b941c08144044000304c01548640c204a0021003f1803910340e07426503490100d002c843d10031009030340803100443d061095050511400030b1010656000807003106010385403039110031070840864030401000385d1100454500390818454030100c0c0c44204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 420849703 1250 420848453 420848473
    0x50c0613030c0b0309190f08030a18031e1809020a0507050a060c0305160c0b100f2903090303220b04030906090609080c04110c161409060d0b06060903 66
    0x10f042030b04199034140103401184004100c0d200c080954103081d58010040203010a002e86481025070b0020b00910300050f1a025034401d2021404840c001079442035440031519401a4054005410091041da04110502130544040001c5d20384070001c0d18210440140c0e01c2d030081c0801d81e194820b05a000740a130240c10361110031300034640d0212025815a4500740070550b550188900d0b60f10b106407401c000f0503100d18110303007c100c945030712540c4100c420581d14105034803460304000030046a40a0001c0300240414601c41c81381e07030800b800100d42e54000d16800c2d401e0120600d0307220f000041558810080c0f805450f0884641905c5c13054505402074045405824a410300030b0800c0310501407480401c400c2c40c0001242071040154a007101c5444014140c02c81c4208108409080c00d400110001401848040e0007050b0910a6200d102d400d4458101180c1c1707130000d208911214040190300c2040171004224507a141c801d80c1c0c186482e032142c80d2504c10396444000030382500411401340d42610070261a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 420850953 1250 420849703 420849719
    0x2010b09011409070302040632070602071a010501120f02090402030a0b0405010e13030c05030403080a021b030a0c030204090c3c0317030a020d0c030204060e0d050c0613030c 76
    0x40e0403028000e480c3c1c502c42d5915960b041d0300743d206610650000a10804070140005808103401d1660400c3e01030b0046110500303102051a80c001201c20b0b91100c0c2d001030b10408000c2c0309c4141c01c0b410756907003440078a50b40c500000640541040d0354a140c1040d00c4410010b28402941d0440706800c0c4018402c6403a402e25840d000000d04051103910300980c81c2c80c1c0040742c007010840490340319900117402d40404402e180d8084609414080040b0780c2c2e44010f1102200060366040500481e4100d68000d006404e503110502403003403143c2414031f000b900a403440c4004180c1510514065980503a400b003180b00300c0f0b280444a9442c640c0c031008000750f00c80e03aa45003020900c0da0307113200d40130b0054000d941104800c20b1412548114400204441d0500c2c0091031014401c50195a03c103d2096005041c83c1500031140141d44450314144000f1703500080c10b102c1190000700c401510417082d100700c1c41c6400a42e030b90f5941c8080c0082c01502c1404081220084560b024454001131940070b0680c0701c0d85d554a546c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 420852203 1250 420850953 420850979
    0x70e0a061a0408061e18070512240601080c0901120e0d02250302010305070c080307031b080405060f0a09051b0a3609140a0308070e06040b090102010b0901 68
    0xb040315500404011441d01c0c05c0310750708041c03000640114003505031200400404081010044044c1c01d0045030000911681c0d02400303410441c000c20f0107480e40c40f02090034a800ba8085446185503520f88200f8445541d80c040c1c416603004c03010584961340c0e15000300050310f0301032101042c04251810202500d000c4040807401464110840c0c00702c841090005c81c1c18494070048868100b180c1108000c03c0000d03610a400c12a0025418280641043c00c540c50b18200c5520849030100440d441302140e6640d549040120300c1810401d00d80110715080507500c181d04c80313101516415802f4181c0000c2101e0341c0099101d032a0b5258040101c54549118070091039103c9010b00400d44610300c9620001091609402ca070511030014210103212285a901145503130b40501e880c03000c0711580d0303450490014065140a183c0401200014040b845081c0340091616000520344020400120040c0c1c105854075170070340341a1034001150300c0e01c070300c02c00004078014545c000d901e0780e00004941c000142c0c8040190 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 420853453 1250 420852203 420852209
    0x250b070302150a09020607081e0705010603030f0806090f07110a03120b040c0f21020c012a090323121903060b040306020306040e0f030a02010617070e0a061a04 70
    0x109006860f40c1e0f4403c10803c568402c076019401c08000c0059400046035000241044000100001c0c60500c6805c400300c1984c00c01441169181c0d0340d12340900a240d000b01000348100010b242c406810328081012405117500500300c0540050003c001c240514011003000800d4001501100d4641d1403d040040c88071707012680e6405910310b0541c1044880c140307400b8210121055840d03c211080024104469030100383c55100d40c03200c8000d500c3b0104a94900042c1210014100041140980e55449403134076800d5140700010408d540305130307075041500038000f40c0c1200d0304500c0304100e042c0c240420854494a015001c13840340100c40803442e0018150340a0071a0010001c4041981040420140e080351b685008407a4824000e01c002c100044e00c90b0010b50740503401910200d1904109010740b0b140182d40c8043e00e0305c0760004140709460541c244202001029580d04c1c050041d10328003c9a51181c0c0305002e007030580b5900000140b500d4241e600014010400d0b0805007940c00b20400041c00140c0081c0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 420854703 1250 420853453 420853483
    0x4090b041b0309140d020717030702040609020403020103050711070b0a050c030d1409070e0c07081306090501030f05010b1905280306080105070e01110708070f050f030d02250b070302 80
    0x13102054940001e80c01410111940007084000e0501c5162521400300088184692000308608401a103c0f80103207001802c9110015854901794030015055560081070300f01008a94440e200307101c4400510030301140c04d0501e2142e41c41c8420241200c0794403840315080e00d030307110005075034440c1c0c3e1155101114142200392000e580c1d4a82c08850303610754425101d03e4403803c0a40c8003080040020400400c12140708400300e0713203002d104540c450b9951845502100128000280401603960580581700c65042280301c100030b5981010010082802a10301c1d0300c2c4600c80d1315200784611030185048031002d440c0d081204048a441040d040940d28920584000090400c0320000700c4040500819005d01d005403500300303846042000448a034090b504032030000e4400c607513000599220610000016100a003200310304581440d0600082840e100c0c1200e00a52200f42801030b0954003050703c01d080b950821582c18015201c4444c9030140080b604000b41d1200000713002c0c020190001021194054a4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 420855953 1250 420854703 420854723
    0x10b0a1e0515181807140903060906010501030b010c081920062401080612070b1210061418060403061103070e01090b1608040e09150907050604090b041b0309 69
    0x107401880030440d80c5000010030f8513294404546228001d1042c4040500101040f80c10070040800003440c0020959445116400c042c00501240d641802800031031442803c0c480c0849207540c0d02c40c4142d1107410101891000ca001205009500c500b85039810b000c06000b4200540e6041041651942000da03110440303040c03c00c0101c1d00845a908050480700f405031105941541c03208144202280c503958000d41c10b0151102c04299488504007524951491082c2081c4518141444258101258101109100b2208c1e1850039181e40e1808555101c0c02c9000d981c1c0401c520140442c146001c0d03500300401807030811004181d8140d4090140d481031219503950700c00c0740018801510a11818017520850190400c51500340125140041e440248a0510706140c1503660218a0307201c0f4003568140200e030001017041c030310b400302a2892030300040e030b850140c007045240000083d1980714034803864100c2c07030f140c07059030702e0555460748000c004255a24a2403101990804010b004203901e00049542c506c1d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 420857203 1250 420855953 420855997
    0xb0c25081b0604050607051606020a020a080312063a0201170f15190303021c0305010f151101091103010c0215070503100b07060f0b0102010b0a1e0515 66
    0x141d120307410303401c0030058802d0b46401c1c24402845030a030700c00c1c4016100c40c030840b0026488008412102c20080010b64054180c180c0a80704014a040d546d6000c82d080350b106202140603181505603107600003101b1a19912001403110080d40b2000051000750404503000110008a80b8191007040d01c1300d100340c1c0d441c0a602d03d51325800c049071f40c0a840d03c5030316101e03540005007411300602c2c851148000060100c1d044101c81ca249421500d8903030170450040e00503030b400c1c191030b03412100c0452170280b0780c3c24140711039030500383d02d800a6202445450501540a2001c6c0b034020302a03d192a103112aa0009000c0782085050255100c50007401041c0070f90728154401d000203101113403c01001610003c0b0003030640300c20004031a030f500042c0c40c0b025402d41e01d56001803011501402000410301c00c0030040b4014180820310f00481b80c40740b403e9415a414402c2d405100da03200e041d43d4041d80c403610700040703076010401307904580403001d500542d030020310507681800c5c07041c415000351160600d911903034010804 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 420858453 1250 420857203 420857233
    0x10e0d030c02030c07030312141303030506180c0307030621110406050d0615170a0302010b011b02011d0402040b0403060f110f0c0309040c120c02030307090b0c2508 72
    0x8220000701a240c0c01170001070000034400c40d0070745902000020080f61111034030181e041485c030161400c0c121804072a200004160301806079aa01041c1107621041e030000074100210040002040090444000000102418080e5008002030035176000d40121243d50880303400e0700051041c40c2a950810802039001035854240200c84c02c3e64070290004d40318182d503681e8003019005031740669410300602900850300082059030344030300600381d800400c03180c1400d0038080d00f103400f400b007140d04200c071130480403107159407103162000c6140d030a280c00c410701441d940949881d2820302c8411503000d030000a0003e1301c4172140010300306982c090001004000d420101710f204440700014400c102c1c03c803d0110010580354403003d0706200700d03030006903840c0c00383e543e002508460390069000081518880782003040d0b1b059200303500900d12280000d46c9941410003004d0300540c20703881005425680020103c440b9001440100d441c0c3c4004e1031240d1003400803075078810154105008519161160001d0552148 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 420859703 1250 420858453 420858457
    0xf1a0a08010e15220b04061103040b01060c0c0302040e391504080601091a010c0b0a09240608060a092409021e0a1e090b030f010e0d030c0203 62
    0xa404001e04071071540d100c0441100f08000c1448218800580c0602020761194500e80e0b406841804100e0b0189000c1c40c091040340c034074101a80015a0a004010020f54150400c50654806090110000e42245801c401c2965150070082d0030508005441000d800000ba103102c5420196030491041452031100518065206001c40303440020034601107540e040000c5d148907410603c1031030314602500d40c0d02841c50580280e1044044542d40d003e9182c004148030504844070b1801d2038000a958a141c4070100c2d03641010b058140d11940d01c2d1019000c03c91070b1714141e0700305001e00010701d8082c0e88d1003030540000e1509105091940c080c000010751840c0041c40340c000c42c16407090150700720031000d04a8001c40e0322441908102e007030f038030b4800401503a69060003001c0302c04000c1c8a01041c100b48810f000c035043c00740c2d01008801450031340e008a15071b9000200380603100e44210000e13040740d010300080d161600c5959620042d510301024248080e40228409149042c02c0c1c605206006041d9401c907070364 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 420860953 1250 420859703 420859721
    0x1a04081b0708280b091507020606130203152b08030f0105030a03080a050a112a0106181503150e06060901060f0f020c041e0f02131502010f1a0a0801 65
    0x2e07000c00c4804000400082c1240d4004070100210313206e03072000515011000006407500320241c0d1198003081194688007650481d22585c3e48019415810240300034031380c0c8006071050320b1040d0780640c104000140d2000b100150350094580316442c4914a0402c9034490b44161841c0a4055901c3c00108190a00143c001c40042c0d00d42d6401d80e06541b010502e000404000c4c081c184125103a0b055480200c14440142c4941c103050f1001c0038407104988011525242140540030f1640d0500703604000e0700300079510000400c0016140800c0e0000c1c800b00d900300d450b4050300f0091501400b8003040003162400e60000355001c07901c1d0202c0d51691145401c011664070240309040c0081c0c40d074188164a148940f044a51040341030040762005401040001c060351039520000086008031a18003400a00d0b60241000b202c0f07104200718a002c0141c2c030420942d41e00c600170090280030741c0415001403072007540209181e2a80b51410000d80b804401c0100c07002c0c1520039072a12405040078003045030303a418841c900503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 420862203 1250 420860953 420861013
    0x307080a080a090302041d010c02071a07080909010609151403070e01020a1e201f02150f010303030c021b0409080903030304030522031a04081b0708 65
    0x2440d42668030003140e070740884544001c00003980710000042c2c503140640800320045a10031b449070f801101980d800c641c00000c0c3c54045501040c002c00c0000314105490900f01030a9103e10395651040c104481107104a240840e005817204000103144d9503c12170130340595880740081440d2184400c8200d0b0a0b0110074410940404100042403559016010308544101c042c01501c0e0414103d4440c48001c2e5940303050000041b001e4205c440c1006000c1c2c041850309036540c92612000d04165020500b01c0d100e0380001c0d0f055501440e80403810600801c0f60402d0104035003500701036840d0080d54001602002c0c80200c001c40c4c282850b03c1d018078000b0400310083c500c8540018041421002044081d04440d0700c2170b14071200c200800e41c4030340c0381800111f10890080e180c00d03030340b1040400d10f0810300c002c1c080310788111500e0304e01c1800091200908084560f4600d1140200d0b91118140300d0300c6403103083ca00c81c84402502084800381c420218961302110001300998000701d1544840c45148030400c030054507 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 420863309 1106 420862203 420862213
    0x40f0212010b04233103051c0218040218191d040807061109061305010e010306030c050d0611270406081f0219080114030708 55
    0x42c04190075000550b201c42c9104a407800c803a0041c0850b040c094811046000b00810001c0858056058076428170400a641c03030003030101e500c60b010244030000402d0303003500102d2940c0709030b40745000141000d01035010200c04010080d401040304814071618441020066140c10504c082c1c4c41d044002d862500c14200324000b56080701c020f860418481040c402c00c80014401c0c000c0c1ca20407a80079801244034414004101c6240c004c1040041c0c11150120364034000007100c480341c004981c4207032140038001424400450540c1c0c110f0001130038038403150382c040016080c18601272102078001c05001840b1100505250200c0d80b0010340001c034000080078201c5d41000e110107032103038540b0440e010400145007007500c1c2e0f1070380c4084686035050160600461160301da01c2c1c040b03c9000406140031032000c15080400b0f09800d5082c05168459456450640958100020154142c03030030440201 = true := by decide +kernel

theorem cover : BRFrame.Cov 420683453 420863309 := by
  have h0 := BRFrame.cov_init 420683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 420683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 420683453 ≤ n) (h2 : n < 420863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
