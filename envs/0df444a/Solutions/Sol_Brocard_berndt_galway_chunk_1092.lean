-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1092
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:12:16.116607+00:00
-- url     : https://prove2.me/submissions/3539df52-b14e-40c2-a68b-8a35d9990d41

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 196223021 ≤ n < 196402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 196224271 1250 196223021 196223029
    0x3020705060c0703030305060603060d02040e03130305060a1109030613020409120c05070608090c010e03121c0b1519020a06060f05010e040e1e070509040308060108330f 74
    0x5905090800402c54140313942030190031181c0281c50240903c00400400c44191500b0b945c00c03c00039415203000030206090003010341540070311583e07114a88400440001030000020700240600d680d00000c0007101d0301d8440307460303191060701c0c216900741c1c0055000a05419203400c0d4801003600240c4041840e50866403010428031102d02054085040c1414003028400100312a0001d444c030350820340070034105282c52035950100d8004060400025000701d03a0741d501c040c00803450004004035072a486110387c45180312442100c2c180020320b00c0c1b500111040c10b241c005131001038040c2c80c0741080d10b030050004413224580c0312007c0d88010351040c0700c050382c0021400d12038440280707190f0a401c02d42c80d00b000001419001110383e403510aa040c0395140c10b0000c00130401d04010a014003c03111400d0381202c00034109400d80d0302c03885d84050000200424590080000b600c1000260b844401799610b0024a03046d02400c1c810211000c141c1e42840d40e20000c10003a0540c00ba036008100c02c0008400760006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 196225521 1250 196224271 196224277
    0x140903060711150c19090303051c140403030b03060702060c0304060c230405031911120a150203010e22032f10050f09100b1309030201060302030f0d12090302070506 72
    0x40d04d101c0100090310008003182c50b0f4100c0303074a01c40f0301e42400c0d110328503140142a405220703103810b0040f01d003800c1341c4404405980700c918881c40f070000c0f1140b03a10f46030802400030302648140c0e50080c011070f40002c0f62284041101d61056080d071940d54119141e81d221040207182c0300c110300052240c021089940d085c21b0402251890810040ba42d80c1d40e400d0400f4541001010249207810081044011000582d5800c1c01304172100d003590b4211070000ca01e01c1d110300d451000c3e9030240049528010001c0e00c006c107500158182d1b01c1c0700c26a4411703511981996950001c2c00318107482c038640300e07440c040d0009101d050802c0c145811980703101a41d80c0707842000042c3c54006480c81480340d010303401c0124444120700034543d21039103143c0d01ca04c0d58a0881c0e08503444402c3c03000c248007601d0703880200560560b20154560052aa41e140c104004041840c010307009002d5404183d2203407107408905580203400241e0501490314030f580c0d00020346030041c80303140030380142c00c0c040701036000340840403603603071500009 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 196226771 1250 196225521 196225531
    0x60503060906040212031201052e030b0a0e060609090703111b2b0309061d060f0105060a1b0f060212070801080115030b1f0801020a14090306071115 65
    0x82c0041d820644104811181d161038000d009401c10300c5a01d000400d440942d90440c2c1c0240d4080c0a683c42c062910315281c640f590543e680700c1030702c0d41002d0b0040c7d416403007211586030a0327a2488030f280e110710a29005070822070f400381d40701e601000b41c2002410101a2250040071506000c203107071610080d203104642188d804142ca40003903034041d148801040203e08842144803c100b80d40443c103003400f5280310f200440d240107140d16180c1c0c2c003007007120a60080c03c00780100c50070f9003140080008140d44440d019642c4090070064180082068501101100c0d5508210f0316000d9051080080c805d542001c4001c1c142d880304000912100031484500041215411140c07c0102d9440d00c0d00740900035002c181c105402a071301d030040d4662a090b60240d100b068a400110342030040d40c860175901c940074141c01c805983c1c500c02450005428a054001e449000c8554490389030108001e0204030070fa0040641e00c5505074030140c040340750030707015103e1142c8040721401980e92408031120001c00c001401d541c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 196228021 1250 196226771 196226773
    0x60209121213050a0608010b0711091006080601080606030604091509080712020606010903110f03102c071a0705010c08070801080a0b1b040e090102040f05060a0906120605030609 78
    0x19030154024282d090308016100855149400900f4400001d00c041c10500800c69050300004011091114038030100300603400c0186040c138103141c60740c5030703102108061240c0000301c6c6488010a02c030f0341c080d41f0418401d40c0040c11217030855440008001c01f90100f40301c1a6490348840740400011085c9005002c0500d003d00d404d01d0761842d039840c0203c10750200700c4860045400c44024082c10381e80c012100b41c00c583d0802c1000b10458030480004011a4044926075030521412002c0c0c4034428481c0c10190614000500c2581500c04803c0010135101c140440d07a40390ba0071a4034244480c1800e60403030030030b0700302540c0c40b0760a2401300d135511401c40d142c40b4440004039001400704144a0350001c280c5014003c2171001d0903010707400e69a8299805070180c0100944c408084048000300c00720000d40f80101b60450180c0201d050004000c1e000390701900030f1403180002050080f4a5007840c00842c0e8102c4455502c0c106030f140391400854109018030302c0c44004540311600041c2c01c0c2d40401101c4c1c000c83c0144 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 196229271 1250 196228021 196228027
    0x4030302220906030506090312060d0215120411150f0307020123010e250807050c0307140d031503030305060a12030e030105070906020a15060306020301060f030b0a030b01030602091212 81
    0xf00f0000d141031b00042620005070b0040140307504000f01410000c0d0441001d0710705603800a050310000702042c1d801000c00e40341010106803120320340c02d0240454003c0e40500088168054508203005000c2e05a10f0900e441003420440c41460020030401141e202d9007920001480303086410505407403415042010b40880900801070240d2482c007007160781c0110010914940180001c40d000706481c001e541e8500a103c0c0c000d000600c03003406841125014800041600c0d44c9146a20302002e0715502c01040b0000ca21500c81d8002d1002d029200340c403040407011042282d034500d1958110094240108034582001d01a00002020025140904899842600c804046006000c01e050840d90700a01400403c2083c0342e04104558012070084082038005805213011081e847d4410007a02070707a0b0006105030310020000450301da001c0c200c8501e40206680030300405000d24204400d08140d800040e02d0841d04400420005403164020039060074058820314010803031418490a1180100d030403540d4207000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 196230521 1250 196229271 196229273
    0x80a03050d0f06240c051c080114010504150302040807030b151e06070201020f03040e060a1508010e060f030a0303020406140403080912100e100501060807080403030222090603 77
    0x180203050841500080c108150b9142020f8181ea500000000e4007541160a241319801ea101e4102070001c503800004480010524411401e080000840c0c6180014111400400ca0801111114101c000165215402c0c10304003003030070003003094284804003803650070000080d00f4003040c05001c008500030b00a240a92424900c80c220402180c00407512070f0401840494040203040300400b8007407006da0313100e92100307410b00c0140c0c9000362900302c0900e20710000c10b002840101c00700145c3c1c440c000550ba6200029980c010050790b59620319206404a1280c000500255440c03880141d40102c000b480c60100c3c6041d040400d090150303e4801ba80040d40001d001c0c80b14540225401c8400000f545010b0b20f800e1a40d192000c0c0e50082025641c40f98000002054941000b00720400b52200055010446c040380401101e40c0c8800482101c8003560900c00009050390154010912070403803a01e40080315651554110000c0d842512280040e80303065901814000720500380c40003900d9402e00000d40c044c21 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 196231771 1250 196230521 196230547
    0x806150d0f1a0604090201120b1c0b070f0804080409050c19090f060e01140904090203060c071509050d0e0118060507110301050415090c0512010f0e010b0303070f0606080a0305 77
    0x40240034038001c50174400f6040050340d10044000d104007040d9000210042081c0c001341d41b28604c0c4840d005038408902440041c8044038540070700945858551348480b2010400030b803400e00c411100645050320600003000703140b019030011540f1922001995207485400805204001c101005890003c4e013421340500031003405944070005055581420035443d1500f40000780f40661410000c5c02149010450014a45680c0c03c92402c1c60343c01030644646262122801005d070300103803025030f00c694509040081c008414403440c511141c2090140400b2403504005603180d4101d40f0146041001d00060003444862803e06440030b003410ba030b02e199541840d0304200295403d1045210b1090b4075002c24400064011446000e40c0016010041020f4100e8100700b0080400d0f9444030750080b003c2400d01107104810351041d14000382d29202041544040540e082c222149552490740541c0b00308104d002051300907920b5442940300b020042800c07503c1f070111500303200740d02c0000c40c08684007107000d2400200c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 196233021 1250 196231771 196231823
    0x1050702060919140309150d1808070f05100507091403031819090203010905011d010302030d1107050d030908071505070303020c150423070806150d0f 66
    0x159580141440120b0040c0d040302c1c00c21108004220350007401610b0004c000c02d20079220b101d10001c21400d503d0b141000d032a4011340c0140c41c025140341c5444d0044060400f14070320030001c0d503040345c801070a01c0c01a80d2070307510031048500141d40c0f030711a02c60754400032100b82c050703144100c0007a540c0e8185145010039000035404100c0c06644290414000403509100942c400704100e88112070038107860f030916101d8000c0c002c0315004854150300010001c1802491a00100c1c1206d0b030908400d08003695509503900c004400f804005c0d81900f0601d83c00c87c260348141a031094490001050360390b5a0703a20700004452040044040f00414400c040800c00321000744030b07141c010000c00e42c00041c4001280c400410038402d030711000f818113901050714a940300c0c040209001d6a010920f824040d030400741442d150381c0031b030740c00020240382c47c1c11010803031000085404400c42c0c00501c02000c1a440f5030032940e40d48903100d5100e03a004031511002c000400d64102412101c180a6403801301911701da208001072400d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 196234271 1250 196233021 196233031
    0x40509070819050309100c060501062021030a0204050a0905040b060306040f031412150307050402070f02090c0909010b030f01150f080414030703030608010608010506061e09060c0105070206 83
    0x106003060b440300841c00200446035011411039040960350070303041080e100c0401e0907074040c1000740303032100100d0b044d500b00d00b8250b01503002c081c0f00d104c3e03114041e01a40d41c507048568070440e801048401e006084011001071a007054072248054202610f0b500444c02c11680e50340f0240035240c4950510052001110b4072542183d4150080c01d110703c0c098480e94200e030388910f8010704000858521024154403e000e503018200ca43c604185d0300e050500c000091242c0c03041c0564401d000d000400136440c40c1601c211600c1e154441d450004600300380d02080050319000b000c0750398a0504100301c41840d5644012103001c2d0000d50b07946904da05098814030007000050704020131030244440c0342c2c5001c9420801c2544012058a0280d619503200c0c984440107002107000b112480c80301207448400c141d0146c215400703440098000708200d0b03903038581803402e80b00d0541e0499008442088100c0490841c20084070b0301002140c89689403001c00004100350764072075114000180d6590050058455041c005c00d0703006 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 196235521 1250 196234271 196234303
    0x8030a180f0807020d0204092126130605041209080312010b0304260c060a2a020309130623010f03020703030902031204030311010203160c0609020405090708 69
    0x4405651800540110307660003030000e40b00802c42d04119a984501c800007160b01800900c800400d9150000561850362219034100000c0c0c400d0300f01c070318400c0c074000043d0340280d80c13038403010082909041301e424009401e800304544c401102c2404103138240140d90017148110035001480c559544024240801c5400016040c3c008001000c06036080c034861905490a41d00356a40d20340700c9180100c00c3c07a404a40424104006c041024680b100360400340010055500945040e9524102d211044880c5510304a4000b102003164141d590304502c03106950031914011241751000e08000110350400f541d0b0700340300503601e0320400d008422140c6810320061503c40884400400c11030000b81441166941d40c6080650104520003814401d40081d010b4580280c151250a201e6800c010070790380c028081079005c1144a00c4400e41071205100b1a84a462550601e070201519601c04540254600030140e0f14161511034030000341e501c40c4500c40c041c0d04d013000142400c51030500c403a030800c510750090000e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 196236771 1250 196235521 196235561
    0xf08032e0b0304020108060607050106170c010503100b090d060f0b010e01030e0a150605060c2b0806040203070909181b0506190c1208040b01050d23010608010908030a 73
    0x11010001c0c1038035000382d42402d25840076915100440d031a401140310152a6600b00007000a0780950911a0200d04801809031000a400701005417001e2100303488416a9907135214040124604100140a00d99402010010141841e84883c410703220380e280500c80725982c9907440e0f0155a005125a01c44200c01e09060000002d41281e294582c10b080d080542900106a804038480c4031917805540500030003444580c07a00e180500c20380d901c0002e04408000f203d1b6402d21003110181007004001c0502003551014420354404050101070341001d06010140411850082008071140c0954416000c50365189009180c02d410a0703d23019003035a40c0300c4181001d01c10244007070f46401c0308172050780e66004100e03a6050342108048404151510000d08001201c2c000c40e494103500014190140e070003420084816605d503010405054035207440203040a10000c00061a0f4150030211030f280c2445000001d1655540c09199080d55040e08080303e00080000801a85090510130001410204464411 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 196238021 1250 196236771 196236779
    0x412320c010c0809010305090f0a030302042c070e180c09040f0213030609050307050d0c06050a021602190302060307030c080a0203160507060609020f0d05070e09060d0f08032e 77
    0x1503d1113030b150035904143c0c6030070014248480402500e04945c7c3e409040750403012581c103000380203400c9806810408000002c0c41103107405420709413410400121107810640e1a50201501c200b001000c80c01d4000752001c61501c08040c010124511030201004a0740d070794010007081004841c080741d10090003920600807404180740703000c20030302541d50000c000104809941403a510b180121400108684240d0807034040d52640300242600071403142e001030100b80c0340c5c03c61000582c0203107071800c068016800562405841c0001043d88940c10304848494181e07165000300301158001c5604501290720344640d100b60720b9200059950140c0060003c50071403d20598950302c64810002000c20030601091800a01c151548000000c114800d41195265410711b11502c443e0410340d90740794028900f01c005881039004440014180e00d0040265806503141420400012039813901994a8054950403c0000d04100010350240c0c1d1800401c18071180448a80e0005400403c0000800016a40c2c104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 196239271 1250 196238021 196238033
    0x510180e011d0405060c0c0102040b18120303010b16150c03021305030a020307030f0c0b0c01060312021b090a23010918080d18050118020a06050c030412320c010c 71
    0x81d07000f2606d040b10540d500c40d845c1d505030190003079403c03d00b052840040e040401200313a40c0c0d40144d13400280c6031640b01c4540b0145140c3c490000740706403180b680003007001c106540120035202205900c40c540402c4414000c3c40390004842452112102081c0e0019929600c040500303681c6008000031001440c11680c1a400321380ca6520328030005069044034984007041007081c0f84440c02500d100c4411642b2024088007076070103882c2500c010385002c21584c00308034103280301080b500301040904141c050040412030501c02c0c1d81a0050840342d21941d5024541d5568610f1032241546030aa91000046035040110314400c889602800e03501c00c2c0241c0e910480050043e00a548803412940c0002420b40594500c4e81d00085006a00800399460040c0c4100b152148a0500c1c4800e402030301c14420a6464990548851054054041d050340c0240410000c030050700988142842c0310321200e5001daa101e80f003030301d00d400740c51400c44101c0e400d028405520750420082203a0780070003480c1241c03801c201d6031505 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 196240521 1250 196239271 196239283
    0x60509030705100515031504170406270504140907060503070f0305281a030102031311030a06110403030e0609010c110118060f080109090c0510180e011d0405 69
    0x100d400e075904d40340056200c01a04a407065480c1001c0e081e6035070800c59400d081344080085900311809230003201c5400100c5010410750f425504e8a44a040c102c0784484115203080e8428410940442102d110120b203544850007680c8640307a00030541c28003030804503c12400e00710290010300c00c2204c2401001102648641c110b0820105800e0029050720750910070200d8455040468010440380440006d0400d00342e403001201144180a079081c4501c80e10416003030b48004d03510b0071a8182040044c04c0498050865684140c0d0014100e50368610540c3d595415188100140215000702240420906401408030b87e220001142c0f45441e10840c60000780003031a0300c0c0000b82c000400942c010109034000e06d00303800540d1030090350741c0310f0310baa07003074020924990304e511540040c201000000c2c0d002e03414000d002125030b02c040b0035000c2a04100610400b10600424801000f08070030440e4207000c45425014054070139000c0880466060188071443c035105c0300051340e170040408003000b001c602d002c250 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 196241771 1250 196240521 196240543
    0x801021e07050a031d030105340503060114120403020c09010603050402090103122706090f0f0902090303040b0c0705090708160e040f020d09140a110f010912060603060509030705 78
    0x251040d9020310b1000301c0b0034101c840d005d80c041d840c08041c00000c02100100102d00105880200e0880c010380300d90001c004038034000b110104405001041c100e6020303a0803840c070520109111801d01c81004020f1400210070388065001d030700040050704080c1810301c100c50141195040600050400346d000c540b12801c148006402c06104892243c4454407600c031500160406800e41c11310740c905150007000480c510701c00d04010410540300003076800b6511440e90111071401c4c001c0310030103140180c00c0e806544529045030341804100408560105518080c0291002c0d440042c0001814a400d02c0011540500342806000000d4100050508401c101041524031413420300060b644a4000c10007030250340850300b82250001c1488140078041d5403040c2101400759510500000c05600c4d560349941c075114001e481c0c0040031032551b10505000d80050079041c03043c501804516030351000d5222400070118110b400d2a1113010030028050203004c5c581d0000134904c0a50300d40380c0d1a40d201982c60140c0c0d44 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 196243021 1250 196241771 196241777
    0x6090307030e01052b0515030a06021e0d0509010c0c02030319090b0409050406050112022b150b040617070614040f060210110703140c160801021e07050a03 68
    0x4401c0564071450a03a6440c0c8180c0141807099000c65503402c98008000c085c01c0d00c1c0034900750000364078801c0c0140076004000040c000d4801e00000d40c44250195202150b8030b0900e055003900c01c0652000700c0024218640348050005040c2085007141d400c1d90958940d50082100b0007002002696010040ba800403030703a030001c10000c500c0010141c854160725403180003904804500000d403030b60305030007049c840d612660b810441a0b807502410b0001101c0c0e12000313908038010361202980c684c40b525562000e5803807141070a810074603a50300c107030b00b292100020400a540b0b40307030190854140ba028a10141c8030340c46116003610312804a450750346a05118000400c228803100325082c2c0031030f40444028004200e4883c0c10141c40300000395581d040711003480b00007842d1596441d0b0b50800078081e1003d080c1d140d80c0d116481e500301c4448802540294088030803d00a162018007901d1050341840014a15100003688039801c00f40e0491b03818440f1004400459010071501001503408500800a582d15007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 196244271 1250 196243021 196243037
    0x206070c020a060f03110c01020703020106120f080706090203060406020d0e060c0f1c020f070201080f040506010306020f0d050f010518090309040203040c090204140411091f020f01061409090609030703 88
    0x4e08210068814842c0c0b45000010020f4a00c0200390306400529001c2e001e41c0007030100d5540c0d1424140b4500300b0030000380c0342c2e4070fa804072040090250001094020b01824001c02c0307016141e00064249003068408846107940010000703440e8030540219600c0fa1802400b501c92071500c0d810f0074074039109807c49650760140002c2c644094150b081c0140002c40e902880840d00d03520744009101b81c3e03611401090f8040b030344080000c1d0205004009451241341c1c070070041d0030140d00e542e5611020303410603401600114024401d1521141961050500c04c0c031042c112175100c0c0d403428060110b200c00c05040416018403440410074504000000c8400c6601c3c10b560050b0f8030741d41c9040c001c0451117160000c40c205400001c0018103034048401942074400d0031a010805405404e405144034428074410382c0d00700022103002418414458810301d003103210360060702e030078500e0140b456003180c415422008440300303e05140d0380c0a00308031080982c030201c09401480e05080040c0555500e020b261001000c20100c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 196245521 1250 196244271 196244297
    0xe060a0c1103030a0f060509070f031109130c0e03011104050f010e03030a030204050406120b041203110d090501050916030b061f020f0c062b0b0607120206070c020a06 73
    0x11018188440c42032000c1c1c03510fa090508612025207529039202c050721b411b00c40003044516060b4071290007113880c2d454030058003a007054254003030004d4100c40b140b04d000030f103c51a8580c80700c0090b111162000c2c040003c2c5108003800162004917120051030003680361140b154040c051250440741034500445818080a0703481c0d0040b00d201c0c03100c054280e01800301107030b0100c016400d42c004e801030351401c517001d015042d21011690b80e858210100644044110f001240209107107404c00c1c4c1640e0414a804141e070700500b107002486030b02c58556240965038071224401800028072941e07801c11400c90160003d0551600c3c040c080c159107001c045d0005403010040b480f00e0781c0303550b039280f50040035041003100b020440101030b48811082080501c64000d02e4090340c0b19240100440741415012102140340300385170480d002a04940c0c1401e052840e942d401d00c1c8a044d9264000f030a5040d10880d07180749514101e510003420004090b020000303200c0c5403100d20005980b020407600585884d45020260041c02c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 196246771 1250 196245521 196245527
    0x111c0f0201201b010e0d020f1b130f110a090f0b0306210316060617120412021210020913090c0311041b02160807050f06130905010f050a05040e060a0c 66
    0x240d600031440717600ca00002c02c88055008198210b0480f2a00c0c2a254190312140030031580003051a09554001c6036483d04035403204ea6079024920b4070314865000161040b4400b840310080e07010f0707880c45001c0bd80e50b880030055808007604d241c01510403c403131241142021000300d202814245504071800e012004041d44006007001035801c200280d980000e540400c604046008110600841000002c10462500002c00010b104003040b00200c400f0741c6060324081950101005600c400c0b40d201d550380782caa82ca4040308001c041403c0440b6403005a0b5a040842040303911800508140012410200340b1404038140030880b800300c030781042440c101003040800140080c00e001525040e09071000d040194025070000d0105003079802690400341460312605a02d42da503642d8415954000c0c210904a030741810003001a0070491640c10003003641e20b880d020b1210540e84240c121035142500b0b003108010300d20784807103000010701061b1410441840c01c3d0400907219000101491502c40e200e01150441501c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 196248021 1250 196246771 196246781
    0x120a0e0d1b06051c090f08070b07121a01030c020f01090b0f07090303020a08030c2205120114130602130b03070215132a120209091c111c0f0201201b01 66
    0xe80180c0d5a236031842c06140c008032000d416540c000010b0800c20f005903115003140b040c284800021071503404561034100c0110f026021100c4042c0c114001c10500700d034409402d0017440326aa2044001c41200e242603924402c40c44c00080c951030810100d400304001194010606101441d0400c8105640e07555508108a4500c108131200f0f80100c42ca0754080807518540704030030309864044801d00d510014448016081e00e0248030040801505800407a16074050341054000042c401e060250420001940c04810001c070303036110b400d40d00000000c10040326418891012325200712aa8800141040705906019048008005207600c0c001d094207148180814071343c028820300c900040407901c2d1179118810026001d03190490291305150041241010041062080d140d04440d80240078103125408403110014502105c04074020203150001c0b00c48104500b003048510b03510303008506548884001d00312500030044201020441e0005101103460748215801015144048100c0d88003442007a80186 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 196249271 1250 196248021 196248023
    0x41b050f03070207051f0f0305011404091a0115091a0d0b0d02060c0d080a06030503091504030f08040503101a04020f040e010f1e050102120a0e0d1b06051c090f 70
    0x40300801e2042c286c88103000c00321b040040d060751011003110b054841a0b0030741e00c0a0080d0a804403014800010743c0c18a81d020048444c06030408003201092a40344046540703081e00701c507200b0001c20204405154014014500a0030403049030050000e85c0c401030407841c0901403422407201d88805403010542e4500c0d040e90721840c1c00418550365419851140c0360b46858038482c1e0b0340031403142c80008010208034403411048980001c080d40c5000380700310030480318910803800d114080005000c044089241100203c00d142e1054101e1030b60b03241443d0402d80b40860411004c2d0300e840c2025009038130030034580081230840310180c4015886010000704140c030f0340200e40028a080b0b8404000007960382d8003900f000c044402829441c4021910f025240d004804039010701805030b44540c0301030a200c00c8620003082608464178040390301c80301b0f0700e000070520304050400b03650700141c01e5810420340081034849401081d8609015143c1140040180c1d589407010410640320307641e40201000340311106110a80103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 196250521 1250 196249271 196249279
    0x307020604091e0c020106080d02011406010f0917010207021e15030702070e0a05040c0608040f0b040f02091f1401020a0b0405070b0304061e0c0c230d030605041b050f0307020705 78
    0x21302d4540200034000c0400384200b0116110340480c03006002e0041c81100c181e0740700c01c1205102984d03900300643c1d0981e40340c040b0b80200030030344600050000304110a802c2c11088140050303a80d40107401004110000ca908510301900365100c281500d40e01e01c860901e0080b0603900840d242c1d0782d43c040603814800300d82d100884009080e41017105140280d4003141c4070718440c0f684002903d884000c21500050704980007403807050004140804203c2ca210302982c0035124005140d6551130355070204103214426201c600a291801c0c5515111b00e03041100c01015140310302408080d102a140003c0d5180e80c040740140c9444140d40108083c04821720140010300008521503560f81080e01d080c00040c5607106181130030908c01c0001d419548042c0c062821209055680e440050318203440e900380191803032100d0040510240984140c480051124141b8803900fa01e000030303414900410702050b1402900310703c100041c0100d0050149400a0a86510380307a902d16880d10390395090401d034909017094000c5544 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 196251771 1250 196250521 196250531
    0x90a060903030b10032a17060a030618150513060f2307110607090b0a03140a09060e070b030403081503100515040504031d0f0a08011d0307020604091e 66
    0x42136805801403840c0080c0c1440e401600e03025041c440b08801c08100403900015035515901403004141c6031080c0d00141c00a01c842c110558a640b410100e9003402c142600d02e00310010301c4001e00c5410300003407800140d9500c1c14051445c200b420307280c0b0801c00e020010507503070342e0342240c2507500e60035480541010032406050860b0300c007411404095038401c0304c28600164062180880210b404201180582c0507a00c1c0d5100c1c1a081004023501030300817020304010181d03070343c402081112a180006014842c02d20740000c00c5000c0e410440c003600c01c59842160316901c0290200860380c1c0f0003086990141e0186042500d603124070030061071380008445c0c001c3c0e242c415010b44200d5403810b544003500035144403030742c060f0055100c0305020035280100c6020303000c149521000c03a0385901c9180c4a418118000300001c50070107107000081c4088240744c01690483e9580c1d400d41012109580c0c103a2141d150480040d030404100e40e002542a11650042100b51504c441c0c202000c1c0d9032100c5100c905c4a003824050013 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 196253021 1250 196251771 196251799
    0x7060b13140c0d1d011d0703120503070c060614010201060504020f0a11070e090102090f09040c17011113090b03071206090201050702090f090d0e060d050c07050307050c03011103090a060903030b 85
    0x800307045d0004042070290501b007540c44000718002802e01c02c5941c4070600d034510740e22204058030650801015034081c060712064031400a01035108035070141001c03030554440010480e00090842d1415003055025500c10808030041201000070b40d00d212285103084131150031040d05890914007103600036511030801d60140800b104040d009841c440c8026166012060784100410440110a03900075103860040b03001441001c1030307030380d0709480041810000b1502030a00b42658081d42d0017a40720103094040804240400c0c05e03640520340d05520220b00602c006814460031418000007050002c2c10030303940d060304004590060064411264004000001c50304c0d00020308000340204981c2138846008591f0a001c3e11401400c01d07114441001e80345504140018104800400e03001d880724100744014056500000c20800c007e1110700c0c4608040c1c07100600100500d800e46004244103813002c0014010019181000240d50361000d800a50100d01401b580c10180d00a044281116070000c040340c0102c2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 196254271 1250 196253021 196253023
    0x3070b0306010e041a0d06021303050313060f081503070e01090e0601090e0d0804020a0509040c1409060d0209070309021315090504020a12110607060b13140c0d1d 71
    0x61141c1800c2e2261038038000e40c6002c020440d6070000d0000085400e030424030b03a1174107200034502015445010018604400c5105001000480382e2040303e56600000300609112001180c2d413006084908051350100302c49000a0329841004141d02c3c0828072003007401d03210b9582005003074000d00111070ba104280d40c4900c8040c018061003541e440d0681f10700e0300000b4019115108004d04605920081c01274541008000c65007100d01501c2668000900701022415030703074070b00d45940207e20500f00284039514141866022501c0070740660710138200c520410241d600d6441c51000c138a541125415101e5442c8032081d4000e080e860700203508003901c2552004074203420f51000100b0404400c5942e40b2568074680d0702c00395002150000e42250115200f0418240c2c03600a01448511a6140904d410710314004500e140d000311005a07030f541d03214070049809080c45070706500c2c2d0508090003407000c4100002404000c00340509500319203007000464040c4404154081c2c4001c03070140016108800c403010300a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 196255521 1250 196254271 196254277
    0x3091612030f0801060203041202030705100f2601171f0b1c080f1e03040503031b031006050a02010b040204030506010302030c0913060f0b120708100614090603030903070b 75
    0x80700450600601d960303480c1d0050f90b009040340c2e0183d005601d41810000c50f5803009007030384001c03030301882019408141d503542c203101c0745000c42c91a03a0f0280805103140300180100204c940101c40c3c503403208410306034010400728aa054075140f858a04441324900f04451811002c00540600c28110720348400014040c0d8022400c01141100c1003280394002004002e00da08001c03600418807001040100d165220260280c40c03140c1e08101c00d0441400c481c1da0703617140c1d6482194111003035040002084400300d201000c1c02c0505240313070400c0b800c40c98401d40c0ca400b940031354020303902403203c04158068518403d410241702200007078030642d11030742d4a1a046983d640b003800124441c0c020361846100c0750611a1f010f600c80c1c4500b2880711410442900d684004004034507020580680318001020760741c4450901c0300c1c4030042c2c2c200404420703161100f4142082c440c02000c02540d8140315003081650300500581c0da0064044648400c1d64070746000091451013403c040d16013601030000001011003186004d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 196256771 1250 196255521 196255523
    0xf1b180d050c0901170601031b08070f0f0b04030302031c0e2407141909170a14060c0403140a06050705130503030a080a0f060b0d0b03160f0b03091612 66
    0x80d01c1c3c0d6a90f200d03140c3c0700c08480002c0c0700034081d0b03015100400c082007001c09010328100c240b0842d5819541c641d85424281006034220f42101c004000d41000495180d140e0302004101d10110303e41800c3c2507aa000351a07101c4e0004c0c6040080982c0072148a503d455800902106080e5085504c00ba01040c00d00510071015074210380c48164450005040d140a0351052650410255044d40b4080d502000c0a04245000403071038100f0151500114105c1900d00da0f5512150f0300c20000c010b10080303480c250b103080c010103901707040a80082040c415160105402c0c0c0e0b068a41c04024030b0894040b058100b482c1213100c4201421090400040c0300c0c0140d000401459403040300a050003071607480300305047c1d49101c1c04035a4000a10300ca00011600b4469a00000f07420101c12804105a50303118488003207900101c480f00060740c1d5414100700581380800240c3d400190901d212201545001c0c1001d4a25070580309505c1b0149001001810030030f4180040f2146c82041808000b0064850328419400c4400800c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 196258021 1250 196256771 196256779
    0x60705013308070f15020c0d140d03060501081302061e09030721030806060714030a09060c02030303130f050f01060f05011106070509030717010c03050f1b180d050c 72
    0xe0302082004001c03a20390144da07079030180050100c0c83c0c115000030071464141c4050031802500d094800e01e54820500015290085006d0704802d51000781d141d06203010a407580042c0351801200f0840c42e40c00042c05688034035542c03403401160559001003a0300e44078070381031030b890751029140c10505600040c020301030f880307000c2d0100d88016484034048055046515244040c1d0f08441c08080002031241d2a41a4840300c040c100074180750103543d460703541c110309401c074440079000441d00306402039100705900c00a02080c540540f041440e500440d490f8030024208401403511404280240101c18900001082c3e110003110309100707207407881038000c04050003132500070300c0e00e40d0380010150b00c10404c25080c4801000600601d4480b01029550340c0c0c0081c49150f0140940380c00014403c0c00101150500982d03417001040030980d11000a0444400030205a41040458140000242d002940034400f415040310305944034a42d49481c001d05028030452540024078048038006c100c0c011a00c0b02542d40151 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 196259271 1250 196258021 196258121
    0x6020f0409230a231009051506070602160c0f06031a0102060601031d03070605010807080d05070609030302130815091902090a02070803090a110301021806070501 71
    0x4410111071107101c07104190191100380c0812007540e41a4418502295110151414001ca1131107460007070404a45034041180c0c03040040000702560b0103842d500000816050441e0905000050202d000318035014201d00e83c0803a0141c107408440428600c06a00401d0032085032b955411180343c500707490300440740004c0c105000e443c180f8040074600003114034140c02821485d40c4c0c0301c1c0110b000b400040000b04503800c4000241c0313400e0030203000a0860a0041d48081015814050b03076034a010200c0c0d001c0030ba541e201c801d0000130306500c003060391621079111602050301e89042c14100c010340994080c640b0b948040c13450000305404005905044500f0240209515070b440000710743d1507007070880c1c04a52071407002c1e440100614002020b80e0f0f02090f0060b005050100503160b040c00ca400c1194028580d6104014807000c1c0000720300c2001011500328001e42c41c0c4074641c0351000fa42a440d01c101809688041981e4007044829040000105045a03048100943c242c109086d85410418505400300e001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 196260521 1250 196259271 196259291
    0xd05011806090903090e13382e05060f07120804050303180a050114011e14010c141002031f05030c01110f0d02030714010209091b040306020f0409 64
    0x15015083d002c6405480702d8414038541120a030b0302d803000410064500c0058a292000100500811a125444d401c0c288050910001c99045007041d80401090020b16020800070707042eaa003c1c4100c84540e105007103000c1000c40c1c542151401c605078100f40d501040c003082440302503040c58064110389001e041e4440c0389004c10613040e24952003e481c054400d802c1040000c4104288030712061801d9103640c1103412141c0c0c2c0341c03112400c40300242c1c180c2d21701d107550400400841e003002e09042009151030002034540b915245c401243c2e03000303030500c40e410b104c40a40d01109001c4440c1411346480d00700c0d025540e4040c0d0241d0301d01c0003036004582e030941c034680300c0d0000f403224403148042c4e90546101400612b45100c1d0800155002100501803024078418021a100601818441410110403580042da112610b52403c501542055030090392180c1c4180035640c0c040da0381223041900001c10500c109059500103094015510868001408c003070300008180c883c5440081c0240210790800104010800c04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 196261771 1250 196260521 196260539
    0x3091c1e12090e150f060d02040f0602061f0306180b0702060609090a03090302060f130308120a0b030a0311030c0316110103060302131e050c09131506050f0d05011806 73
    0x420b075801c00c10b140390201c4080d69400c3c0351791880c41404004042a00305145940c100050340d00603001460f2010708400c0070840c8540400400740c20119420380e2400c10f0f6070a40c4510f40003682840301404050325042e070701c3d804800020a4000113500207110404900d8803000107035442000381c4034603004041000005040c05404280c0c040d01a0b0b159541540280c0786400f002050b40294006080601d0b08100458400c403c101003940194459495191a1034001e0868004100010301502c240c8c0d0070000e01521940c0e003c944206103650604104180b162140c80c0140395000d11600f4107601d05c400608403851003030005505800c180300e000036000c80d9000b6070044040d240c451000030b400a0102d030740c590040a02d82c2041490f480344486000503c1040310656042c5c8105994010041500103458561414150b048615411211100b406060940d185e413030a5800d0700e100700810040c0c00b1604200709046001112602e5035080c006015650b151803000d40c080d400002400000e0340b43c00c00010f00f0b048 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 196263021 1250 196261771 196261799
    0x906100501050a081b071203151202040c0215090a020306250507081201060c2102030f0901030603020306040803010e010614180310090308100803091c1e1209 69
    0x181d40d12410702941a1095404c8200035207480f440c6925441c07260180022500504116802200c480200149215002d000c07248207280b08500d051010400340b08036548003510400e0703154181c6000901c050700043c100d040c010501600142901d202d4140306040b880004c0c02c03c0024021019a1082d49a290130b14900c0b100c040d2170849041030412106071400e002d14003030116240504010391410104240c0c1c1890705400760021008100b0500c0d24000f800810401e07000310315450103011144204140011350340c4d014803100c0000680c00094025084e9100303400c028000c5074043c045418504051a00c0e1a02d80c00900031882c841520200008596124a0f03501a61200308101e007442d0003078a0420904241c61040800e4140c4a49076034a0003200b0300f0f1050703103e035a0081d610180f1030300b0b090841808001c102d0344109010340c818020080c580d510020180c01d500ca00320103080200c05a0b103080c60645007544800145918459040e0050003650440030142d81340d42e030342d0803124640754060107070a41 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 196264271 1250 196263021 196263029
    0x18090f1902090f2e0207090507170103082203060b011e0801120320010903030f0b0102030412060e07080d030b01080c030a052725030f17071a090610 65
    0x5043d0b41000002800c0c0b03000644140009500e101078200700c660b100d81000fa0f100c0c41a2001031b4881e5200700a02c0d40144101c2d5040106840c08880c50f0612010080704040e060002400e5601c0000e51090b02107045105030300e40040521040031441d5803400e00708010302d05915900e01140000c0b80c8208101c0d00c039120344140e00d10030b440c0c40040c0d900b048245800920119011024410030300800c9146004624006203a1018000085400b400919005040c3c0e01c011070354890850600e01140a00d80e0040300b91000c2c0c459402d4101e240160904110014240080b00b140e002d0080c10804542c1080215000b034844600e52018030440e0000401110301d490101d41d40d0b4980c01081c0045149402160402031700400a18901c000e0506101220703066103e1300c5000300565030141550120180315034a4090b007802c40e104e0848a010f1842e00d40c1c3d9415402c080c0010019940f1501c0c14040150340000d6560083e0040105441c800d501a800100d0b50701c01c0d50101c0d4140b244100142d0900b264440207c02e40f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 196265521 1250 196264271 196264279
    0x12070303050c0d090509070806040b04020301090917031e0406020f040b03010f050a0b18030f070f0302090a0606050318070f0609030209091c0e040e0a050304030b010e090304030818090f190209 84
    0x71f941e814000c88096501408580d805034075650807640c142d40ba4001b850103040403000c0002c0040c2e00f454812426a2401130520701044180104401482c0e02d03d102c4081076840000e18903195141d203003083c001d209541200c0c01c02d200104000ca0300c040c82c1c00c06181600d10304002e10348215103d00400040804512070b0010320702003004500c501100112050039000e901808035107000c4a08004141451031507007002c1b1826509a508105602c0c2044160b50020403034202003022a0800e40028400c0c4001019000b40d4810004242c0403da400c0000c0d42c0186114188603242c585c41d0f0310700030100c281700e2105078800e001140c04030700007000214114070325a200c0401600d51250024081c0d8081502c81c6c0c103950300c0b580d5100d61604290050040b808483d2081c0080c42c0d0315801c40c50609021041a00488064406c100c00c01224890020850b42600d40018025403901d2082407c19551208443c050317410000c002e003840310a0454450f098003031004546295902021215018228002c1c0384100ea0702c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 196266771 1250 196265521 196265539
    0xf070e0109110409090809040c03020307030b010507021f11120901120e06010612060302030106082515050d0b10030906050105030a0807110402071e0308070801061d12070303050c0d0905 81
    0x4d0440316070200e4005031040e03054038103220300c1e0400503048401140220340466000030411480c1903151041e00302060017403c2060408071550003095000400e4010705148076942000030503002c1c0a10f00c09109220010116034000070050700f103040c2c40e049500040d01080b1f82507440800c1c0c0c1c00382d024039295405040000c2000fa071030860b040f102d408400f40d10480c5e40d540c80c1c0c808005601c0c20300a03100541042002007002e04140c100d0043c3d201c4124000150b4451449401c0c0221690401e4501741e103103c62500d0380d2501098465100204001d406590340300c9007102002035190342580011103c1c078003d030f03030400250b039a49090584550341c07a02d00421400c030070481c1800140c54007880f6040070034041d10050521101e40d41b4800103502c0079071030184084405464808165104008070f600060501d884006540350000291036000b184000242d00c04030f000f40c3c109a038949461040343c040581e0300b1907036165503d080182540d030140d00070103002d000b441e800008990280c84018100c031030160010070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 196268021 1250 196266771 196266779
    0x3050c011403060405180708010b0a05040b0102060f04030e1e150a0f051e04170106061706060304030c0c090f18020f090903120c030703050906040b071b050f070e01091104 75
    0xc014500184070b80c50481b00715204100304001001707800040c0c010000009103050440080025954180d44030a00c61420f004040103140d03404500c03540c009a4008a00046491743d10301540c103e5000d464140e00704c50180701c2508018564596003908050a884050020024404c0c80e000d07441403a00581c041050540d25100c540d1180008180300c964080c1111815180cbc1804040298800d81c0251031120120301132a0050300c0c20712454000700024141840c080344108652a92500020a07980c410b8074040002401e141c0680316102200354040c5120b96110717100d4178850014041003050707018031460030310b59445076000403c907180000d4008102d0503c0e030a07540100f05541e00001d18000903070100340701c80000400d40940315401405010b00d41034882c42c2035403004040301c40c010505070307032030784113a0500002c02c04291415801c00780078903103001c6048400480c0d940035055910020100d20402c03884100d800c50105d1f070703102540c00400070b01030b090742d98806502c00c0c0d41c3d012625006085040000300 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 196269271 1250 196268021 196268029
    0x40e0a030e12030f0c01060501020712050a02091905090609240a020c120c0a0b0703050f152b0b060a030c061d0d0b01031e08071e0c0f03050c01140306 66
    0x2980b0503102140c0ca40100d401940d40660080d101102d401ea44801091200d90380600180c405411044800e404141b540c2d146e01d503030340c2e034080c80c060b000f2603001e004034801d11002201c50000c0fa030b1100c07042c803590800c40002580c4090454208120b4041d4141b08401c01a040d2100824200299034818250704c0fa61030060007036100340c1c2141d40754803136100391001c3d03404100050170b4000759030400740c4079960f9580ac00001080005000e102010302d00010000c00320001341e941900300b01641140340c0b100759000c0200c0e01010340780d01d108038101e02413904941141103c0c2c0d03100c6801ca1003281c00c2d00c942d80310365003881980403403404014402081d0200c02d1040740e100b200e001c904a001002c8202180c20b14601149101c0304120301074401588070401071007401400c60f918100c0c0210540760f04000200380e121003c0d24007905000809003509044016034280410f509510402d41282e500003116030380e00c101d030012000394401201da030b00a0748000f001c0c41d8055a800f9500c186107104c01486c503503070300f4100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 196270521 1250 196269271 196269289
    0xa0e0a030804020f0d1e02090106030204051c03020f0304090e010f02192a0303020a0f0206061806061b1506040b10080402220f0605030f03070b0a0908070c05040e0a030e 74
    0x358000802c0e44250010031641100341c3c4071000080450b960415090040c23200c8600c05801103402d050041001300300310b403034004045481e004205e45d0407504041c0740c035080b4102004155000118030000c1008206c601c80e55000b01503100e103480c000c11413407220585080030fa004130401da0b00e600100080e503030429402400100d070308120403400d030780c5400c0c0345150b8491040074115090700000c0d400304e070380600d198100070090601406400140307030324a403900004001480340841e14180d81c01d001d01082613600e8107400c0d80e00321004102c50001807004414619030700e402908401714820070f050086840c90a051080c170440b41c41c098015202961140c00c292030140700038000b02d0b003103070031592440c00c0500282503284181c10b41c802c0205020712001c0400c801c3c0c49294005621941007860003200d4803100204603800c03658048000c0d60540d484810050040025100142c002000015460108003021035440c0c16a10700b101c0070401d1030302d982d84da01e80d207480010000740450701c10030700000145094010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 196271771 1250 196270521 196270549
    0xb06070201120f0f0207111e0d140303011e0b030606030112020102100f020c160806010e06012d080f04020d061e02120103170307050d1a03030a080a0e0a03080402 71
    0x404500440001185070407183c0d503848018841e45e011410344204200d00041c107011080441c0c1e03c1c02c0d0030010407200304000c00c484048502c42c5481e2415202002080300302c80c0d1007044000f0680b5107d40c1c2d40c00e9140385203a6480d07a07210341e4201500d80810545451026a801030f04003524007410340c1c1c00c100c40030103d03001e00501a8154803502400c040d90070003500502104280c840e40240e203800603001990315003080419042c103141700007001801f8080002036802d0450f44100310302a9551105801a250480e10b162011400c1ca0000d0502060011740c003c0c1c94000442c50340c1e0804240d5030305001c1e20700c444013910020342c4401d8000500c0080f8800e03800c51002c4410043d1024244030170182c20002301d90008158400c80e001e0100104103001445007000380c00e02480c1e40ea10318602d40108018a10f00c6201d072030380c001940d01c1030740d9650340324040c401c1241040041c080785e6541e540790f00c000d0801c070802c503851100541000c1b10966941d10219030060802d9140d2600c1c41180c5441e42008110686420 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 196273021 1250 196271771 196271807
    0x1501050a030905061e07030b01120b04060b0706020705070501050a0c020906060d0e06010906050409030906080705040f08100c02070f03062301121a1611070e09010209130b06070201 79
    0x80b503a004600c05004050140d2281e011040c44000c81d1600c0c0b4041d13820042071801850b180c1551603040ba600090164604c2c01c18150000d02c0c0c00c1c05c140040d0040045030820700c0020404034180781040704d16030080502c2e03801003003221845a55a0011a0544649030168002601503903109006040c880005508018014055410840745500c50011110f000c0f4101105901000042010490a00c0303034001070002075030b003400640000c3d240035084000c01d200d19000c221f1132100103600035100e40d090b10041d2100c812055542a40d801106a4481c030310020303440315500c4d1520702454a13000113101c408450038a08441c85451031511140000e04940d090748410070801303030050724603415001d10580603041c900b005802001c00e41c1030280d00f60070009101e100c3c81d0071031010b109014080600c0801c2e89440c51814007041c0c1b90010240c0e080444650000b61240111801d00c00010019000341855440680e07010020002c5408403100f51080c0e0310749241c11210401040001d540b240200f0741c005140380c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 196274271 1250 196273021 196273031
    0x50909090c0301110703033c02120c0a03050609190209040e030406050421020a1703070506180c0405010f1202030312070507060e010e060f0a060e1003020907081501050a03 75
    0x9000c6802d54244c02224102a18005a01d008054140c030a00d00c0705410310014040c00694150b05190091a10180c2009403035000c010440001203a011504012102c4034041d00600340410041041d4005084a1002c64100301c0080c41a092040c81180329000030206884214a10100e80c8000e600407a40c0c581c000c1d442e0b8100d03e46104007040100f00502080e90352075581e6240c04403416151000c0301c01d041541d4040302040000da55210020001c0c0c1d07505500c0c0d01404150b00104d20b1540c462104003c02034018041000703004400c8d114888100c2510000792004d032908941044201c13182401000f40d070341c10102d0306004a00d2010b80d6028040e10140440c1d10749004008100e00c4400c04843c0e90b400108006100010400381d4002e148000c0740000c005c2c801070b5501065941c0724280184501e4018020800080a00c401c82d0041402803800d90708913245030500c1050f00b0061101070200f03a01441c1010040740c0010b100c2c5002c40d20800406001552070b02400004581c9903010444007410580c0728 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 196275521 1250 196274271 196274293
    0x6130c0f05031308030906010303140a050430060c02100b010207120c030807080d06050a050603070f0513030506010512030306090c07030201060f0806040204270204020d09080712021c05090909 84
    0x41c80003107008071641c6c0000d11f120361442c030f0000c128054044441209100501c0004d145503041026282516095000c1000c01000840c005501e40456244000d90700409600d440a2140aa00ca13800949031503007664125001004648150340781003a68034016400042e041096407000c0903001e4401c0c4c454420384015542e0b940b10040d080d00102d03000d0720f85000019a00c5030039081441242d0050205441101e01c07a03103080d0000f94039000041c642c0050003c86028140d140e0b21640072201c1c2644450340c0b00500f0b0b03490713080540d9104030074003965004280c5100310301841e190000c1070b00e00c220701c0104804034071b58a90032101c00c2600300b00d904030250340d00c40801258000c42148204090941e50b8014411840d0500401058486143d080f1594a0b00039032142c5444083c019004134440e01901c02503a142c0c0004000d00040c012502d0240400ca404251740042011520842c400301c00c1550840d04038148800ba5611851650610900403800402c12200c4034200080c0c0341c0d50010803d01560310003144 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 196276771 1250 196275521 196275533
    0x6050f16080705060109060503060708160c0215040905060415060f030f05130b060a0812071511041703032203050712020706030e030f030403031503150506130c0f050313 74
    0x1140443c0c0c903402c01801845800450301c174a800030481200107200d60704010a0140c60329038068008201075022a11020015024600f4580d4071603014001081c05920f4482c6c0c01205e130814002c0101450400010900c03501c1e0a0055103040b40071204120f401d546010020340b40440f100300c40c01d05040c0c86c2e103041f109100852062621401200203407044503080f0b403030107981c0d11030001d008500c28801c2d5181440742013400640c4c0381841c010711b00e5080d903c0089042280032508402c00f009012407c2c00c05450541009201078801c685e10b0301d244a030610306100c80151a8001100c41e41981c005c120f1000c1e0702d5181134049019201d000781082450038065446592000140150300400b41c1d10081c01000b85681c9882203075482e0312600040c0d810700345640d00d00d02c903520024102400300354848011a044c1072017078408000035035009554164001c1070034171104c003810003100c0141c0704841c00800c40c0300b45051405607141824090751100d0006c0d00e00f610560b1680c0018181001400c4415207034400110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 196278021 1250 196276771 196276777
    0x2307020a0e04050a060b0301051017030f031608060604180209040b191703041410200106090b0a0b07060e030c0f010209030105070201091e1104050a020c0105010f06050f1608 76
    0x1018101030807664005045c48410b440c400100c15000c0c0e0b140800304840035040d81214810f41d2600b81c0f02c40d0042e501d410b01c040c6903014010041294840001c2440307510000780d050b0a00890701d648a00103203695080c03c10903540283d20030000c1091015400703070841642036004001180b07000700000f03580d00c06040820340d1040e00c03115082ca280c000312801d220070080d4061040300074605100540c42c050801034109003020369010658040c0f4146110003150306d004545041c42c0e030b0a103100500001c040a1121030107498503116805203145030202e00c180f2030401c116001c0a5a040301d0200b442c00c070309981c4101c01000c080070740001601044c401c950342401c0900103000c2c101602c1e000981c4904041c4101400c4031005402c1c101960b00d00100d250000d460302c41004d4199080c10020003060000307050182c840040c2d80c100341c0d8041c1c544410045800340c19409800010b4401008201680e00d030f00034040c0040890040d000400d405220038610076007140c000b04802200d050340a4012111581c80700b030250 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 196279271 1250 196278021 196278023
    0x20f040f06031e020c0c011101090b1608060415060f0c05070b04030b10030b01120c0504050c040306051b040b0a0507050312091b06030c0901020a020904051605012307020a0e04 77
    0x2030700c42404a00803103c40516400e203494986085103840300d0748140070360f05d4520583c024103100c801902044482c9080d807103001a01d4100f40d2010a038a0240c88200503420a44a80c101140940d00401c03098281803080410072000c00c40c4501c0d1003030030a9015140702880340c2e0000200b18510030f0f07910000b08140030003802010310a802a485505501e0000f00d841c200070300c4490010040701c0c0410100307034043d4200d811507030081d441110208080c2440c41032608540c1240b074209052805210008078420001e200703d82c0190820443c40d21003010380004141d40508103080102c0c10b1200380070780d0b0956002003140d14000e040952070040341c1e80d905415a00700e4164030030a08040810814802c80a100355062107050307959543c0c00c5c0074000d0014001d40070240240c01c0082c00816204004d9000b0801900c3c0560014260915440d2074038103241c1d11541c0c0c1085c1d0140d90b100b80400191540901540c08000c50070303034843e000c800300c5901c02d52000e801800c2d0a9031303c170426800000342c4000f0204524011 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 196280521 1250 196279271 196279277
    0x31b121b0f0804091d2d031801031a01080f0901020d11030702010b01050438070b07031a130e12030403030c0810030b04110301240e0705030712020f040f06 68
    0xa138036249119080300d00342002e20b160f88002030b19a518010340451600d080040001202c1c080c004100e0309031481001341c085500c4c261000003812504214684000844d410007641c0c18040d114042030b200743d201d21038850242c0030074285804035204c120361078070071070344250306000050821403002d072001d041d80d40b400b2108030b0114000050149181e828000c042c80d000c02800d001e4501442e02d609c104801d00d071040784070748a0a2864480340804885490001d00c05a0030b11481d80350000c50030000c00f0f0340c6040e1880000b103484c0500300d083c00441c1b16956020b0703a4000300b500d0f8080c90020101d038042c1000041d504100e009003c1c07240c81001141c4050750065000303903800200c03542044c1000c0e10800020b01030960000c0c0f241000c10000b104540c59660095000380415040b203650000b0034007602c0705812880050040803d28440c5022640d504030403074a0b0350101a60980342c1407000d5034544000d44800c80050f0500481d9690103030190000d0070210351a50415103459680e01d050501c0e254682c0101d000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 196281771 1250 196280521 196280527
    0x15060e0909060906010b131a1308010507020d0c050a0507031a0106030501051c0f02130207170c0309010f110607080a050a0506030316081b0604031b121b0f08 69
    0x1400e00408003603114035404014900d034184855841d541d803105110304000c018000848014080002210000424001c8086202203017003d150600542001074500320350300d980a00007625407414060b842c02a00d20781c010702003c0341040022103104550780000e9a80d44108012000065404c112000046001d150011500340c407440080c1505c407010f0744480c0400d030802c4014030075991040c280d0101ca6101c05a9555020440d251816002d101c002020750310501e1600e504d180e201c2c0c1034000341400382c419502d012128101e00021019405005901c40361a8428003001e200365000d842c640d9041407240c20941210f030b04070303548540b50000480d00c03100002c034100f0a20012048902895800210460701804149040d0b80400d6580c06102c0310050340f158a29410010322507040201d824404540e03130602c2c00c031460404c4051b660002070b0780840000c0c0108841c4410b0f6034050070340000703c50b4092000086518400b81c1181e60303100111104102c5c5800c965090000b8004500c40324501d8403554040392 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 196283021 1250 196281771 196281797
    0x2090a0f0312080702060403141614010b0f090c03040201032a0e0f01030c020a020931020109060c031b031209050a020907090807150c1a0603072114011506 68
    0x40720000307004c82c0c0a5611031000e21002913084466140001c000244442d01e904d1030500c5924202001c41003d00790440c88a001c2c1c3c5507440642161014800582e880441c60304c802043c80758240c4101d82c3d40756513120910100300198426085100c410350a00480c003e03000f4541e030030550040d040350000c004a801c200c0b4050301414048030040001d032007400c040100298106002c1c2d2540b40c40b18000b4444c801710400209242d04810304684142c00884084400080d1050718501c56890781c4400d90101d101c5c8a40003c042d803141b00303184e080680c10f03038a81c03c1d01c1c0c186041708048070300319900440a000d4843d0000c0c581060741c0c40784444c258003034401409001024010b03c50480000741c80e400421498140c14231200a001406100322041d15503840106400070508981ca9041c0708001054158200c40b1a0304034030606030180d004503412004e0700c0200f03a03600050b245210010211021500c5040b142d00c0c00326680541c4002089034540c004130f015558484d00b0191a441d03504110041101590151 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 196284271 1250 196283021 196283027
    0x60c01051911030402010e043b0304050109231816020d0c08030604061a0a0207090507090501030f140115020c0607020d0b0c07050703081804061802090a0f0312 70
    0x3400c070800a40c410407140c0b00c071051418061000410107414450400100107940e02da51303100401d0340e1821041600c0030f80c0310f1010750760302403d1090441e241c10390248254419203400700031901241c00503199202480e00d40720400459998016560b18000521401c000180c0c84142c0d40b440a600030b40071001482c60a0107010030f0b54000c50414004540c004002d428840b42c00400303000d0300c0b030381140040c0d440e42d88240005000d0305240c0c20245000d040d8030780144034103038000040c0c83c9440440c0c09861106031103070105000c41d4812100e4800064003d4820003455020303a00c140030007140010b0105140c0f1041c0084085c03c0c40071781c42219a0b5a4003000141d000d9418044902c05210449071140382c6022030b000290201010b400180280400002082001d0403c0003110300c0b182d4070400b951462036603410280c01329044500c0680100c4c03204003110085141a110b00c03002c2d00e810b02e24140005151840901c000c5d00076805a94016801c41e00100b100403160100500031840707001c0111403491021001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 196285521 1250 196284271 196284301
    0x605010225150f12060b03071209060606020303040201110a020f1e03060721090c0b28180e0603060403110a14100b09010f03151121090703050c1c02060c0105 69
    0x41c0002e50301c5c09000340320170350401084a81100480c0b80c452410450f84411034028850018020b00040c5010b40c00a040754006c8007440c8501c2c001d032941000540c088103d151181d00464009500c458804203503c41468a00405060104404882c0a000003032001092030050183c0d00400442c01d900145100030540719804824015107a4003401050860303943d5000076841400b80c10007401c004200e4075044c58584e11855955140300c8107d03100c042c50b0207809818061041c1daa1003441a40d2880403d883c818118100d00645014000306140d54603500d00700c43c451148051001c40c0c1c040c06001c3c001140104102001c19005113000e001120f106007414800c03608029203850050f80c2d920010001441100101c4080f00d81064440c4185100301004c4402450032040130710703607080c010644030480360440100c40f143d8001445130031100d03110b03030700d00a0343d41d8030350311000700564003041c1015041e0802948107007142600303c1009111000607070000d880c3d40c00c4200b031094160354600030031100801086003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 196286771 1250 196285521 196285547
    0x6040e01020901080123030d03270b1f15030608060912160c1809030e060f090f060c01140f06010e010509010c0f08041403100605010225150f 62
    0x31440e242c41400080c0600005110b19408100d400c0b01031000c00d0344013101c2c1900c0c04401000d403201d00301030070000340017022034408450000b00c910500030340005c5d00e080c42c5040c41d40c000c031400e0310300d0347d584d003252800301c4562102c26079a082c2c1380350014103440034840e41c0300c0b0924261030200301d01e42092080751400000402e1001c5c60740c001007024060300a8903040302c4044850010701a03590724207042c0081c2e07002960380010684c8501d0022032014102c00c1d40400f102d107100343d64104c0082180c1041110a000d04a50400c007620304000c0c3c51130610b006050381241c1c4802a040d0346c2003080c0300b1040d9007101c1410103100603800c10038040041c01201c041255034006800d0818403008821140003c09174003074645094140100c28a0002c140b28108003140d41756544035601d00c1c1c2c3c0e03d8944800ba04490703584407510b0b02070710503280b070380440d52000d004040a5400c1a4001e00384615249030903800d1507940c10607400b00e5010041c0c00f162000b0010200322244c20ba944030550b6070500382d44010520221404 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 196288021 1250 196286771 196286773
    0x3040206130807120b131e0302030405060307030b01170f0a020a0c1506080d050f071104240f09020702030a0807030c0c0e0711032802010608061e0c030906010306020711120606040e 79
    0x1070f145000510541f200c42e01a004074003500c0c1000d0a40c0b40a034958490385c2c20469000a001c000c118029516400c4103520304801c1c1d031352a1079841104040040322005982e0041c62418450015603040007a40c05402c10903c3c88c0380425480c03485d80c03944522014001c01c2612003689400091100c12020402c0104100280c5005481c0049903c2584814021450002c1080c007007580101004d070380c0c6411902064060803d52090850508001c2028104a205074524155072490018240c145803090300d444a802401400112007140d07650b1615130301c40303c401c40c00c0c090301009405c00305281c40858400740804000d20041c80c14101c0d03000d4560a909425861140d104110604021030f041e41f150020b00d41c038120400604082c0c0c50103038003424040d00100a20321440741007081c4006807984045000c442030303182c0e0ba0951031b810f1990000d4401190030b081079a011a00420001340194003d101081c0940340d1846010560000a006004070b020800c400b9840a0184a035918040c07103006900d8403284 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 196289271 1250 196288021 196288051
    0x20f1e0f07030c0303140901060e151e04150b0c01050a0e0c240a0201021c0207170f070c03230123061201050127020f03040206130807120b 61
    0x40900c482441494002010009500030f5a010140a9004407100041591a002c5146030070f00890b40204840c0c4106002e0f002c0513400705060070076016000c05544000351804007840f4088210504250009400701c2d00a6596072207400c40e40d80180e10f1310050803040300260b42e03030b10012189900b91000a00441c149528019804c00352034000980340e142800c050f03801050f4410b4400e03d034040600303400000c1840b090000744100c0c5103981940200f15203807214120512107841181d4400403409140e1004004542e01ca4000d081215044003608000340041e98103480c02d1041d50b50103003070503030951040f200340c00c11021000c0e07040d55034904446104183c1000b00510490426034640190fa0303140f240c0c501308800004035050b81c6401c0c00103180480d000c4000e01c11940d48800302041040c40107980040b1030900080170300006054021101940d036504100b6003076850360b80800055500c111200149014000000180001d0501080c0011b011401c2c024104400c10b0408510082c0c004000203400c00c1c0304 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 196290521 1250 196289271 196289287
    0xa080417030307081512190501060e06060a20100b03010b181302060d06030b091207030f0536011b02030303010b0f04080703051c0e031e0a0204020f1e 66
    0x3007804d041e07100400d03a0180d02000784040109a00549448841200740504c044504002c0c003041c150840c081c0c4500d0081112030360307800b00c0c0701c00040c0684850f52301400800a900380c2c039118507200eaa02801070301109020f40e200440883c41c01d000c0a1001800d941c0300c1d0400e5a46207400c1c4114040c111094902d82d4400c1580c00d03100c50006c4006210401f02d02000c0d52500a5444000543d4038056014908000e01c0342c59041040240320100c0e840b0415120f40305483d41150990026520141d51584440103042c00c0c803001510709070040c84d00e81d00c0ba40006038600b0004001d00800c00d03003071416400b90809412805000600d00401e03601001741501080721038070010f1f02c00204403030450300400c0d070322074540020072800c514a00c40c81e4420005c2d8031801070003005004000c60241003000c04034881030034080051005640000c034482900307600d504218010104040300301258000a08140203480710424035a0020f070880e081565140000200804e282c4420038058103224000700c500880242400c9003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 196291771 1250 196290521 196290527
    0x7061205150616080c010621030206040b04020d0609110a05010c11040b1f170a0b010206040f0c0f0608010810020c19110d0308060f0a0f030f050f0a080417030307 71
    0x2880070882d0181800241c040301d0983e070528034481065100c07102a030f680f10703e185d119011f0401d074012a600314985103096203600400f004010400d070307419000313004144d84685400c4c0c1c0c5400c00030010ba07080041040b400740003481b580319030415144501c840c25034503c025824010132031099000300e0706000401d0398110104004800083c0f42c840212408980d49a101001c02c0032400c44030150001805404070848659811200c003290507071080c43c40c9504c44d618441c208040e907100f0500a80075030000342c04079011a031811102c2005c40d005140d88100e095071900c0424100c2c605503c400d0020b000000144051501400008100a031203c0158103280785031161342e0f241c0202c06240101840c0e130a244408024005c0d040440141c2d00900c004448601303818042d1140e0b2044448034494005400403c41515144403000d0684000e15400d00b101400c41c2c2d1072441806540304191401c1c8101d4000205148042180342ca039070b0f21170210140c980d0302e083e544203088224075468283d1900300340100200e490f4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 196293021 1250 196291771 196291801
    0x170c0304150c140f120306040f060803031f0b090f1f030605091e270105070521010b04090b061201080f120c06070311120c03180c060708031b04030507061205 69
    0x340c58031702c0c0c2e50340303840d090b00003070007001a01000b04140b13040c1103000816550200181d8459003241080030303007040c001c00e141c1e611005d0600072100b100109102002881c200b03141450000348020b004404d4580210b4413100421036451405400a511032006000d603081104c8150782100308885030a04043c214188502c1210b40201180c4060281080400883d0301c1c0e4480100f07400d91101c020001401d1002c0c0082040e070040c0040400001c2110895030681c00503d8040d0480b00c0c0e4000c441c4c1801c1c102801c8402500c1e10014041d80100c090000581072409803000500070605a001001100020b51203941003d103105414003003c00c00b4001413040c1d80001c154258481c56070b180000d01010320784100181402000000716070416070f00100108081a04000c3d80504074924880030300110483d4255034071044042c0281d0001801e101c3c12001079120006160003040c00c804070490007846400d46d1001c0d0700142d00585065111590420400d0303004078108820606c68001840146020840318510300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 196294271 1250 196293021 196293043
    0x2030304031106041211040506030f070902030705070c080321040c0302010c14030c06060f03030c0703060908070b04050c040f0c17090c06070501020d0c0903170c0304150c140f 77
    0xb142a01e80880ca980d5a50110303000303407500860700200348030f203030070500800180e1090343c501131494500810701d549000540c44480c2650507008054040c00e0451460282d000a0904020302500b40a000c00107140502070300041c1c4000d00c015516210f004400400890110145045000c51b000900010820800d07881083d2074084c28110b144501e1032800038000708100d2142040c601002c10000c0f2504804150306004990460f1203900101c4c001040689030302c00c00741d004841e40d11032001040001d089801007010180151071060400781c0c16102c1d00d0745180c1c201c40840303a5030409900b01c615494944584a0340181c4082d0800041009080c042c0116071481e1040801c0b201c680002086420108a4016002c80c0904440d4840c1c2084c9070141c040d4001002a02805040c40110b0080358441c202c1542241d401450481041c80c0c081d403a80c0f82c80e808090209400d00007040f010445c51002906000c56401c55540c440c0c60b60107c0c02c00b18200184081c5400140e0020b0010039213500740014888010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 196295521 1250 196294271 196294283
    0x50103060806133806090c1c090501020c0607110d0e37050405010801110f0a020a020402030c0403020405100b0d020d0e060a06150e0d1e06091202190203030403 70
    0x11545501308810207582c0c0c40f1410702450510803511480009010440001c9081e0808240890b101c48007046003408080b5512060702c0f0060080358020307258182580560800c5600c00109c02c0d0f42c50311540c2c02c0e40d00224210449501140c01e10881c07542c440e91292007084160090b00c5106000600101401e010b16842071041c0300c5150352022408400e100c04407440b18040c504c0c0101c10b07001d080404400c500f4865144158680000010707000018061249040300c4a0403440c94041b003080740b00b40642141011a0071886642e141e2001a00c540c40250f02501c00c010380b04d900d0700c0c80c5104000139110020540c2c044141d200e24100001e0305408141d85408180c201c0150311089461a604000c18a01e141198984225424060600351561068058070070391071088111030740c4150162001714007114129040f4140d5080080440c000070340084442d0001c4250f840c41c03414503102c100940708420f0040d02ea8020400c0003104c601d030100460081ca44084c1020180000260002a1039008902c006889 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 196296771 1250 196295521 196295551
    0xf08060601050d021b0601081e1e070905190609020702030a030503060402070204091505180c012607021524040c052106030d05280201110703021501050103060806 71
    0x400f098060340c410b9454020070841e0300000c080d000d41d450100b03205924450091345100358030b44506041b01500c100140005060106176804000c03045140407045103014000c10324007040079441805a280a004002e90340300b111016825003034212035035075010401c0d440c41007049200680740450404403907900750400786d03140d56490022402034403916500940c0b2925003502c3c1c104104040c0c1c050805140680030410a560b07075204a69250030204041102580c0100754003080d9620034002c41103e050704484078962a0f00e20b0300c0d4600c1d844000d640c4440503812550025100384401c003107443d401100302d00e0003046001413a480d10780000c9045c0425001f20344a01810711124002c07002c444d00c0c200c400c40003da2612070116108a03020301960b10900c01c0c05209450201244110181c030382d400c070607a20088600400360a040740b0312100c4003080d4259501c0341344601c241081e04c00900400d0b0b029070080c00c20000c0c1078541042001d07050304041e040c5441e181c02880141c03400220941c1c050194141590 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 196298021 1250 196296771 196296787
    0x1030506060405031005100504090f1104020909090607080c03010f030f021801120b0105030c0105030609070c0206040915080102070c03120216171902031b15030717010f0806060105 79
    0x340074420343e04859014801d52000d18100a4540c3c01075100728a04a0301030400d54540041105540b03000e500070340b03100120000c4a01140c070000b0a07030700f10b03c001070005203003288a4011840320f100460708003c05801c89002c2094054000854507444509090203c0c038540c10000c44404081c401c0c0405814043c001410200b1515071202118600c00305102c400c40c2980d43d02e108040c98080014226a8551100000200d5040000364444984e005071121811075130b400046c440c2c01d550091000c810058400004c034050303222040140080d003140c000220f0380e00c9058030041c8001c01c42e0350043c0b8050388100900004240005916800e581d401607186601c8164000128070b804080f0390600d0300c08109800001d01d1514800503040303100c51a02c25100e404043d020808010303406088084e401d600564401081c030601d840c400844c2c050014850240d020060a450540b900110b41c1c120120b14894518811760400c1618039006000c0105260700d224140b071b40442e00c0321405003215050040c0811007107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 196299271 1250 196298021 196298029
    0xc120302070f0e010f0f030510050a0906051f060c0209040303020a0908060106050a03050c03190b12031c11031b1b0a0510050c04050603010b0c0307080409140a091101030506 76
    0x72004000594015204544030303503418a400c4028802c101e042c2800520000300054403001079030031280c003c400703410034244130b544e0013020700401000014034507601c2c42480e0004500c1e104543c050251001c28070500000f8045401c403140c000c0c1c10003401d0200c208039900047e610100f050780d105a05142c09a11a0504031040c0d440002d560025a014080d03000081191a4084041c0220409941c2c0034480d070740742c031489046144800c0d102120700824100340041410742035048005a808040c203984110000340c0d034900d0031500040c604920701e003000c605010205040b4010024500d1602c3d80741451410003144e1513210180b869101d0401c50782c0405d1101500c0e8a0b07001c0300f07410348030302800d580500c9660b150560321101510f202d810360030f14000200f450281010103607000e44402801003440c41e4280030b00c0c0d510f10780142035107130321030320040142000061190010304010182c455011410040181b0702850255000f808590303a07614154221012984400510701030390401c1c24000b0702501c0e10004a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 196300521 1250 196299271 196299283
    0x408060103201203090406090204050f040c090b0d060e06090c0a0e0d02090124050405030c0108060604170d02071508070c050f0f0c01021b0f190906030b070f0801030c120302 76
    0x140d0b00040c2e8070f2107054618400700c001c01e40150700711030403c14162658402c2049003d580101a0000d0342e1619103481030505030b0100d140c00c4482d05186400f19031311904080340da0b00c00746000221a483d4201001071150400305250002c0c41203c6101d50341c580120800480e000c0e8041c17040c1040006840c03042d0036140d00d00851550741e0064a00c2c2c42540e103c5c1c1c2d103010100041c8051250724400e440207a10454847c00c00d540640b040200604452900074004540d00100078005580c0a4010040000e85e09001841584450040c0e00034110803d2681e901a045c01c400e41d204003800c0c02041802d940b030b560b010360340642c440c0f00c034102840c08103143e007042403501aa00300c482c203a40c414001c1d00c442007000083c0e80040e0100980c00c031212102c807070310103000e008403214003070350041d02d40d030000c1e021072030240244149008036401c8a51529629040307842178811035881074601c0300d0218280501e8650240c0180031200d0282403404031545036a13206410201d440c42182015040006180304051080c858 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 196301771 1250 196300521 196300583
    0x1403061c0c231e06040501050c010f0f0902011101051005090a230a060816030b0702031603080118051603020d020904020c011d150a05071b03020106030201140408060103 74
    0x1502c0807440c600d440840906441011443c03045038010982d201141070300001c804001d43c080c02c0e0070f0400c5d01d09001912503410000038000d455484400c00c0d202c81c001c41c480d021024101d004041040c80381400050540349800e40e0036543e44c0d040108202908580c030341000c049400175140071a5580c0d60f0585000141039580741305c607402c001c1c51f0600d01c2c03410f485c00209000300002c1d101002020b84e1081400c0e6208208070090340501441c610800214000710a02c0e6032080c207a0042c0c903d42141d1451540c1c4007010424203c022540100c01440411b001c2c50720780d143c0440c0c24100300042c2c20a005060a181203805420040540016001d018031403d90192591880050b04c155110040d010307e8a02034254195541e0002c0c010036160343c420200050820b50014000c403841c0b14549034140c40170041c3c68001c6c1140e0030302011040385071300c002d4800c0051030018040c0d030000403003a0071031000500c80780c5040711407413082c0700a100034070000c980800c2d0141100d03030103184110356240c2c004943c0642412005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 196303021 1250 196301771 196301789
    0x4020408010203041b121e0c080a14060109020702031e030f04031a070f050d320a0c0201060f05012001090f1403210703060314030a1403061c0c 63
    0xb0600c01004841005c091032a4000018036441c00d0310b5603819154000c4000c0040d005544414461000b4080d142841c9503440c050381c071000c0140d0303c41028600e88030220408850030618004140510b0b035081c441140540120b030020361410505800295070f988400c00a1a4210f500c050305c4540c1880070002c680c2d010761007420b050b032119501c0c18001c803c6540031904e0483d0900700000100120300c542101e2100403542c0c4c554908000010300080006e0164a903104803580018030078001281d00518409003550320380c0040300311890250041d0b0250b03020b124800d0b0541e0f06204040c007019024400403000e4030001c2c645094501150700b007000c85001080200c50847d403030300d5040c0c41070201900740c14143e54000c114403100e15140c2400f0b5645e0b440b60748070074003c03e4449681074401c00c80c0400183d40140c1d5510f00820525144c1e00c03000407040f0301013416003040e030001510700140c6400c102c1d41000e46080540060a51a01c1ca01240d210580f8560028100c035000380e11000b00440101c4250180070811 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 196304271 1250 196303021 196303027
    0x115051308011503020103050c04260304181d0703050303010605090d080c010903200303010605090f1002061006030207050d0507150e0607030509030901020a020f0109081b01030c020609060c0702040204080102 91
    0x114514281203e030005034002801d110008180a46030412a000c0b0394086082e1240032404082641e6005203581116445000401000900340c1483c1c040d005030030b55008000401c8600388001d444003d00250380042a908200707000c20201d580802a24115022400c140e1350b81c4100100240321a200c0c0e0b44010508203001c220504d01210550085981910070740700c00051115001c0322100d5079580451041d882e40c005c03c0148902c038404e0001d00502c503c05040c0042000800c00004c804031940401d03580164040b0302049800680703200300031300502c1f02d410110f20b4145141c8a86890b0b1012144507418440001043c03030800428003915050080b05020030004454410303245038940600f5600f40300080c2c1000081008448040200d410325241600101150710003942444135600e22421441e051140160300001e070503e050120f1a007015008200c0c0c096101c034100050100e80d03007000d201045520850403c1038907a00080e10980000542500c00d440310b03120300c0010040c0c403035a00030f511154008 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 196305521 1250 196304271 196304291
    0x3602030d050c0c0a18060501050c0a060906020720150c06130317010b0901020105101809020a05030102040902031e01030f0f0503190503091510210602040e04050c09011505130801 78
    0x217600281400707100540030703c170850382c400c01101c032801031550a0a10303030420180c2800281580c2e0013800400d10510380903041c40600d80300d01030140041803107641c00301400008503000c0e2800c140c601c4a60303107143d440a0f0810101081c3c0343c0c0d5800d0001c2000181241c024020f00900d03026404090100b0038541702c0300011b40e1140300d41c40150300519030060142d800c1a0108400041280000c0141c1d01c240400c600c96900415280d000360910b4081039802c005c09503004030703564a0170300084c0054542d401c400341c0e030703414144030034080c148400605000c1040400d0062001411103000725054a40001901020307181c681442e904510800c2c11480c034050f0b920680341401038001016620419010003500c092000c180310341a1400d10480d021869220004c034240451000701c05000c100e11108110140c064442e0780c2c0781801c03030740250099100e161140c41000104641003042c032402440640b00a80d141d4075007001d05a41c4c0c44000d81d4601441000b00d00c141c40000d2210b03409004006840090000e80c0030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 196306771 1250 196305521 196305539
    0xa080c0a061a06030c0a030e0d020c1e0f090712061203020f0f061602010b0303070b0105130b1c052b110303060609223602030d050c0c0a 60
    0xa035200854001e0300300040300a100807100c4045600980c0503040720b2643d070b101d26912003680d011004120506999101d505261082000421448000c80d0000c2000f1075008040000c4000180c4c002041230000481c40800c5840b89150072412000543e01000b0325103440c0c009a0303003010b40450303600e00145011000251401003071080400740c4d0094099811804483d11072980b03401003c0411050b5038842000300d1049003240c011603400002510000400461150001303007954810601a14007201d4500184528a030030108560220782d00c8c0810080c0800040c04690080c580a841c0c02e50018842508424400d0504c50a10400398518007550440502c1075084203030001c0100e900e0002d800c9490056444100104490003038800910341030408141500704035030f008031049203c0c68164000d98540750b92440b0700540001c01c0c90f0400c0c3c0490b410005241a0780320042811030f6408004010f40400540c40100d03500454100d6490005d9851841454281c500000b100250b900b103160200000782d4644 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 196308021 1250 196306771 196306783
    0xf0c06020f190f08060f010504120c060f09060c0f0f080a020a0618110603070c0b012301211a0d03050c010f0c02120d060b04140301061a07140a080c 65
    0xd00d034012081501c40500302103c00419280280001c6605600859100d01d441e056a0420704014541145441d4845022100111044070111201c500b01d082c00d01c54141c102240c50840b000d58030303001040628007000101581c510460281006101d00c92803414041815000409030b500301c4610360340e43c0d40c03101009582d42150ba9090703c400d0700e8245160200403210070315144103904003d001038801028010403295910207803070602031141580c02040000c1e01c111445000704440c1652200b41e51110a201030340070346404140e410004600c40c0211520708024a044880d184d80d18005007900c050180b84492281c220b03803899015103070500785005c0507484401060f41c0c031031740d03c000e0005080640c80f160a0750310016840000d178000c044e00c4190b07a81d061014020305000c8901c00b02e80c00355a400d1103d560b5026401c845080a00a00002c2c0301c1d040074040c02c001040002c2c224030380710f241509a0101c500034860000c01c2101611540f451003803080014001c0c0a8005401d1980c400811214a036a25 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 196309271 1250 196308021 196308037
    0x402010930050607171608180607020a0302060a110a0305060a08060a1e0e0309060a020109061503060c140f0a030f0501060e030708060402010c02040b03010905070e2e060f0c06020f 79
    0x790403581c02c4070300f0020704d1709100d000c0c43e41411018407080288a05607580d000082c540341c040241c4002e24412800308000d864002e0000350094100c8094a05009040640040043c40c3d12810018400c0f07144058608403a42940c0c58640001c0c2c0d519400000317924200d075a400041280300341e109100e400e100c545e220182d000c80d126030482121035004410803e4514411402d000c941051264100b242002001000c0c550010b200001e103411090384c0d410708880b50104906011080300c00c0900c1000302920600c00e0285050500780c80c505e811113300e404030300c14200c00148444022441c40403440c040e4003c1c81341e100c400042400590307150326004003010800a591442440740c04000500c10740081001401a6010f0707407280e5604000c0c1e0284070250020340161a019980c0d665500e021500c14070502c1d000d4030260f1440c00c0f0f1828810a5000420765401034004d10a885118401e506000700880e00c003140c41d0f906013803007a4011007000f6030f0b105610340700144c0300c01c0c00054079205001180000b02140 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 196310521 1250 196309271 196309277
    0x150103050102131a030402010c0f0c1401200c060a0c0605010b09030106170d1b0f1208010603061d040c0506040308041e0b1b01020c032d030402010930050607 69
    0x1241e503100b400c14036251041364131490313010800218004d948204000c02200d40910f074100b101e04243d5075549030f034042540c880380c8000000707041e203025136a0148006a845050210f0801004c0d070240110f0b41322070038522080d00c6030600042d2444818000d10040002e20342150080051750307500c81c808580740d48200300c00e40c820b5181040100f000e0050a520740c4035016508001c00d4030300c6070540300382ca05c203d2441c194103c089030301f410700e030014201454404070381c0c4c030415141c0f480c05066540680030b140180c100c0014141803090900c0311003003021810035900100315203c1d40613140c83c101443c008219400c055003000d0001008020b0088000003041103035221142d4407d08501c2d000c5861500d205c2c0d001e14a445507041181802040300a00d1016101407070200040c078041d180d1001e02e2469020000881171441d081041c1c40d52480201e05c0500c500d100d400c0c0d86851441c046d400201221b101d400b0300f121040741c14940441c070021003c40500410701e0894103401d00d26403410015642d0710300722200000 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 196311771 1250 196310521 196310557
    0x10b0d0302061f1a0d1b0c020a0504061224050f0f0c0901090306021c1d070807050f060309070b030a0218030a020112230c13090b0f0d05150103050102 66
    0x180382070a9890f001c0311901e45200850031a11030f21800e25500c141c81708004103440310320981e4000d07810018418070f1502519880d031305052620502210724801ea0000c2e00c00c40ca06081000326461400c00d2405007a8040301c900700040c519440c084110302c0d82148040001d207400d08005001c0d000030704d000d00404220441006940d9101d108070941c0c0305103100c541c00248256010030000310a600a8500d140410325145191030b2400f800340304071101000780d241c3c4003045150b481c0d05444d050203450044d00d50390014280e541d040801140264203030160550148800000191003080e0600610002e4180b01c41c019a0b80d0510201000203500416220880c3c0c4150340840292031400148100718554181c41d0b180da00740c440b41941303004003013000034007001c141001100c464101004460b0b92054141c044c1d4180c40d0405042543d0b00000a82c20164070345160484030441c1c4c0c1d0341c1c199214100c1c10100ca4803a03003a40c00f0300e0801d0401326015080c0f500303a2418000842000019006010b00b03528480391986 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 196313021 1250 196311771 196311811
    0xb01091d01180308060315070f0f0e061605101e0507030509151008060901060815190203071403070f080702030403200609100201050405070b040e0703090302010b0d030206 75
    0x401c079002004030800c81400e280281d00042d014494580d0305c807500505440b0081d014071683c98241204480140018905081e00340b94a070f000f40072402120030302d11300400c000000c036012510521942143e03241414a214000041010410201c1d1090b0366848007401400b0351911459008892500c0c140c14160601000800480c030034030541d407103108410024540209008551100c4c0c40018050070b551a141002c01b003003016080081502503009400005030007031400420381e041488000d40300e140a010503040c07140e04d8005501d0031604c2000400016a03a0b00e41b1001622001d80c09200321090000c04001c102d1400d030008061001c103111500c0300740c0c00d81d41d104030891726071050340402004c03104003400101034500c201100030320340007018000c0c501c2c010000f00014850328003522042d0041c1c0d100c008001c00c00101f40041402840ca00030524107144c00d0a02841d49503500900d03050802d651110312006052003504120300ca5000034110041c0241181030094546100300e0700d2007030010302900c0c104 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 196314271 1250 196313021 196313023
    0x1f080c130207030503041211010618051b0301060e0a0509010e040501060504020331050304030803041a010302010f08040606030605010b09010305090a050a0f030e0604090b040e0f030f070303090b01091d 88
    0xd40d1442d410350341d0905d19905c0340d8a00c0c1c5030b9a4096410010800522044864100248030301c0000c2e2683d00f41a16588511000d00f2080d07880003042159203440280c2144082541201501c0c1514094141056030001401c00f04403100b81941c8004c1e0311800c15000000c071001c940c10036902850240000f400303c65103078400c1c0401c1c2d201c29144810845010714100022a80040074009000c005101c9074900161548405141d40c105030800e0b42d0940001040c8400c000c00001c92452141007800c040c14298516000a464003044858010900c403020001030104401c035400103003d190300900810a0b561136901402c1e60390018220940841c1c038050201d08205800288051001d034000001c2110b09a19a07410002085080c011010b011020701440500e644480c040c001412140100150800540d01000b01b0b03902a641403200030341200540c0d070410440401180c2e00d8802c5019096580c014034a412401400d10030000f4022403886000890201d5403134008140b403401d26004000c1c0410010b902c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 196315521 1250 196314271 196314277
    0x302040b0d02030c040e0a0b0103080c0709090c030206031f06020f07050915040b061204080a0305060907020a06240e090105060604180b060d0203070309020907020a080409051f080c1302 81
    0x103940340d40258240e000502c1e1540041d2121b5101c2015122060b201d60b4803404400400e030000c80d050000411241032203842004048020104a1401e012010150301e480f12003551601010b800381c00004001010500d000811264211400d2180e810090380e80030000d4441d0501290702400703000780d4900080c0c501d080517a440c000d50100c80c1d06143c07110210104801444140c50031a04080180154440541849613080c03181380110582d40c2d484480e80c4006044450040909201e50400b006011086a0006c4d58902e8254424000140010604020b1a9542c9108205440f06101b10008287c2c120382403038032809502c0540092120303488807010010f590040c0d016021105d41c040f04016200d50f007070380002406000141c40f4614010228180d007080e80c5c400c48003a008603458548440c01c508000d10580e500106510245c60910314950320110148294821b10501070b0305d54002c10103200700f404c00400c044504101c40000c031075440103040d4546031242c0181e4441c03c00f880c07028881c501c03d0300031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 196316771 1250 196315521 196315523
    0x1a0f04020a062a0f080f0309070902040b0901111f021e09031507121a1201050c041712120106080106140306060d090203010c051b07060207062003030a060302040b0d 72
    0x80d803c54401070640d0420440c2052509a0b80088402040c0000c214035500134140c6612100e90030b03940e481d09a52043c58950564840c10190b0b2041000b0002002070406840aa0801346009080030017600803484c40e18507907102c1145081500f010750207404a4660052803c0f074220000c000b20314200303014800c054014207101c503030135407c070110b03040c01400320f041003d6100303545081c104180886151010b00301e94061070102c201d03240100c841031036450801680440c0300c44400007401036141c403170b07504840c0740103510810140c1124080d809400c1e10f0188450302817800d079807842c00c1d218010070090b0f01c004503081c80350802240c20800046501841000395003418211030305102d20b592121410310080c1e80c00b8450000000780d443c140040140c2d020701617001c500c880c583d40c071521200b40000200d070070181d80c1401d51480d80f14240410002c0c1d00401c0e08001c0b5007090511010010300e141200215100000c03408141e4000042040740e604116803050b815a40296070400c840c0e801c074011b004101e074074844 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 196318021 1250 196316771 196316807
    0xc0f010b0913152306190b0c0705130219020c090103080d18060b01021005011d180a0b07091502060c030c0405030a1a2a071a0f04020a06 60
    0x190800c002240d18115240c8103088030b240500180e070356403080341d0080c00300c0200c60b404003511082a0340d083ea03204d600005d08540104041c01d1100007606100018421942480004145403040003414400f0a004140c06000d18000b200d10140441c0254040c103007081c0002c400390319484005100061040310120003034625409039086403640b282c1a00400000c445141c0c44d5145102d43c082e500c44402a001d11845020440329000f4001904041c1c41c0c0403880c1d080c9191000420044149005030900039034251507910b40e9454644203520100c2c00d4404040c5184a500140820800700c0d0703500c02d100e00e00d00c2e91035940140e152000700100005012368600103921050101d4031003601d10008540000a6144a61600395101d000c81e050012824055035414803000b41c03c0c006080340024142e101988020307011813019116041d4036a224191069200088089100c80400803202010f8109a00398400700f007031032401182900406e81c003210101c2c02450300d804000741203401540b540e0444c500c040c0c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 196319271 1250 196318021 196318039
    0x4030219080a0809121005091207030e100512100602010b09040206071b1508010f120b0703020f090d050f010f0209100e040f0509030d06060507080301030201050d060305030f0c0f010b 80
    0x5110f445164120a2003140c0c451994916103a040c0000c00c5503114604510310007080358a4800c1482d81481801070140c06810340070054100020b910104a12001d90120703003041c003d11110200700e800b406801440300c0d82117044024043c408038501d803003100300c4105a00a0000d03e8049046c41015501039078025000b00041c014940010001070b8400d5007085081311100b20070741d0301c040400d030700c5c440030820a020615041c0103020201001391600c0c050441800e48480d85400e80c0e880c0c3d66002e000401c0d4504040c4d004c20b2a00c00721030355030220b0f400d032600101200c03042002410300035100d135007220112100390f1034201c81805071041e50082e108901c41c002c0c2501d080720310060054410400d03a221191f40680d42c3c0061140d612010b11849000310100c100071a104c66500c2800c004540c05604900c040c041c0510040c0d00060b0302e84100c81c19a0741c207113002c0b030301d408448180002401c4240c100400500010440e5812142c50b08090a400101d0302c040b0380d11420750146443c2250041c20340603800007144 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 196320521 1250 196319271 196319273
    0x409050a091a0a0902040f1406100926070f0e0a050603101d060703051b040e0c0705100905010f0b06030603030301092a02160b2704060e0c04030219080a 67
    0x1442d0b21940c082862240440c134080c15900003021120200025810a6a0b0b003246800c90840da000b4282d00a4090301d0b02d00c0103410200b400752030805036108054140500702da020607014041c1c800e040c25024440200d50180f0b031500c1700115401045c1c092450111307880c100103130100d001c0b070140a0240c1c0c0050050034a030400c001ca131401030b12401c201c210f51000142080310005008010036441014180c0e00090581800d040582c46480c228038024210700b018070083c03001c0400307030130b41c540c201c8006014a642c5030018a0014100b507d0043d0318906246400700610a10006400801d87c200403904100002e080034020000580016030b28a50180d1050005100c006030326880455003d40c2122003840c600d840346c0c04101a03c580302d104400581109501084071000c242c4e02001408000039440c0c10112906200078a03030b990034504860401c8a00d9200321103449550010740580040100b02d4854034019800110680c4107110403801901420b15040b45207041a44440c107940541010381894006 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 196321771 1250 196320521 196320563
    0xc02100e01090b0d0504020a05010c080a200f0c030601051e09060d0c06050901080a1b0c0311030a08090c010206040503030c0d060b041401020729030c04050a08030409050a09 76
    0x385664503040c09903100c804110601d0640103814080d10642c0080b4040c681841806192403280d4407140c10300800402e40700000d5000c100741e4440c80700c0c0e8901500c601120211880c11b91701214a51581742c010510a0140c9210100701700b0340e0394205030202e6403103980c4c5000340030303101210041d130ba07028204005480002d440d042d80c4241d00003000400c5104083c206488091030a400c6501c00d0020580006050340c080d40c21810b01350740300015500800003d2004058500b02c600381044072820001880c030300000305809990281c3c401101a07084a80756551454040d010302c100f076900220902c00c0310003840e11580300103821480345501402442c10b6031030311208140303d60014042109250740b240401305e0b10300c111401800040194008400c2020f0f401c500290505070700f50450040711582d0840d03550075400350040c0d040e800d201440010795030381d02e90300f244205010307030340110340c0c00b095448000031070080c0000a8410350b610403400b0404c80d12030800b80070840e40210801800084882030240104030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 196323021 1250 196321771 196321787
    0x810170c060a050a0e010507080d09140d02070e102105031608030a0b0d0305270411030601090828020d1b091805060604021303140102070308070c0210 66
    0x20104044031400c50554001400300e401041c00b8800043d0042034282d182c640c0300b094268040e00c2820135505e022401d8480e22402d00c42d103140588207079100e44000e401c05c50315042a50b00b00600a003030b58182c100609009407a03200300c0c40f51441050a003004140303103410401c4080101c8041f40f202c0100084d1500039403038100c41c4c200f41540d2a0000707001074100040e018800c8511039214000e203541d40d00e4421546011134111603120340c003d039040704960b00000e407c00f044130508600c81d01010801600608840b09040b400707290150041c2c10094105510800d4502660007a01c090b20f139920140d4488078515650700d0f00001807017080c580c1d004103c13058803410107006801030001c2d0071511002c106817910f400d035002c50b00072040069603640c000c010b0310385144200d1500c8000342d84594882d040c2ea84504d41d80f104007400c00e40c0b00e0f9900040d0080c100380d800d03010f64020750740000507000140c00310001c41c2c000c3d00b008006401180520780001c050a1013040d0207250710780d000786581c007020000e180c01c41740380c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 196324271 1250 196323021 196323059
    0x5030c010e1209150403060203040b0106110c130b040204120b0a1404050a02130f050906010812040509010302120a020d05010905010b041418010216140d02070e010312090308070b09010506010810 85
    0x12401700800300200d61280010351040d0302540824a80d5454903000030b010000980c640714098010a1100f10941d0f15008145207001403c000402c44250650020f030081c455580003004241d55451105c003007000004805d403294901c40000c0142c00c0e90700c0104604d00314210b500400300d4000002281c01482c1024141521031111a4001107401400c04504100c0300160741071440c680c0004010441110200144240262080e01e0503050502d04400f01d010080103003c028410840082c912401c0d007410003100641c40c4e0003d15245016402d030070054028401d040043d59194240404080c83d8109030088951584c484e0b031120b819076680360300c030855040390010b1b02441e0f035408000c001003450714000000040303400b400c0c5e111a030444240c40300c1d103040c1310000c200c000d540040303030100720000405640e0790440b80c005900c40c818941e07201003150b4100e515040140907001c0420700302e09101360700d04503a1181008500801250721140015108040c085541d403600c44841b00043c40400c2c9240d000150003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 196325521 1250 196324271 196324309
    0x6030a02030c12010801090506011e060e03010f06330504060305040f1403040f0e100501050c0a06060905061804081c06050a06080702070911043005030c010e1209 71
    0x80b540c030341d0749404111030a174400d5002e0b80d104c80c21030052100a02c1910300405803061601d456905d4205040f50481c650310034242070041100c00701c001a00d0130b42010682d00300c8080d082100985079203011400b4282c0029011910308895510705042550003482d000c403000d903844882c182850020100d02406008104a4002d96402034040000e0000d0101e550701f010504051740e02c485c1040315070044080c40e03a00283c1c0b880b440c0e00c24065252401d91028085d030f9401e203020342d5100d80a150140c40e10304001001040e42d0b00e4842e0010310f410b0070b41c1c0b0590040c441151040100e20000d00500f04200082d98003a0407408200070044544045940303440100075000720101d41d469969001900070200c0741d01c0341002c10781200c100100343d90b050050101414504030100140c5030017101c10925801240203911410b526202c0b451000000c0c421f4868400800724140000300d5814034203d81c41e6002030a464040d582010a010116000411060f0700b400e9503c00041c00c0034190002c1014241e5407150840c0c0c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 196326771 1250 196325521 196325527
    0x61710061809111e010e0303070b0112030207180507090806070f03020319110a08090d020601030206071410090c0906061e030b030f010b0901061403040b0711010c02280206030a02030c 80
    0xe1a141c0d0300404c640501c103030b0f5101c00125004000503028855011090341b180d00104090000200d045400a041d0b8804185c2116420002e140980c9020019048180c0700c58039028404520b052540103144180d509036600002140e4840000c0c0d0741d0181a2003100101d0fa09690b00c1c090244654065030340075a440064400451740c203201c501c200c0d9140e011a00c0035000000e41c03400301036013000e03500e40c1120744070b0000c00e10107130b0300c107c029190503060000a10444002030240148010700380304040301c603800c90079581110b564100300c1c40100305d9094116041c40707881000189200c5207104590442c0c030541c4031a03061071110700f0341402034040284080289070f51a00034070031036242000160070108042c00001900f8034600100010f42005900040422007101d403078105415002d4160703a04240c1c802c01a44203912503920503501906520000046507203040b40d4005200c0c1c2c0051001e850510746d64102044039140307451a61040c801510203900710408101050034142c05034021070303004114561380c41c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 196328021 1250 196326771 196326803
    0x81009080d02070c1e0e0f0a02090a120201021203061c0f08070f0605060a050f01031515021f060807050d05070b07061a030105040b06040c05090301061710061809 71
    0x2240c03c054010395019a8942051221a0500040c8002503004135808480c0c1e43c03504015465461004000a40020900c0d0108403801c42d03a40545200403002010110040d4840002101a0580d888107a0040c03085e0301d0f090300c2600358041100e00400c8003030450200c1916502030383d005046000021a240c508140415011540c071700007400c0f0851040e6140c24400400d81000d00c1546c10185c04a8460085580c041146540e000b0020701d1360307002801c4c007003419030413220000c100301c24940c40308210003404030369031021644c041009456144002d1000403514040f41504007299040d02510495600441c010310035440c00d1309003005000d1150301100c0942d902d0325048911608802c004130788132601d5281080f06810000b030b02d03141004098008016514181c1c81e411248800900481e000d40d585880c0c02803180c1c41034040b203403060000b030002d01c1850391741c10000c14034400084c00e032140d0b030107200c00b00003088000740a0103081768519000384c449801c040003521f004194008044459101307807a41c2da0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 196329271 1250 196328021 196328047
    0xe0112140415020309070608090c0d0803190626031903060f05010f081902070803040f0203010c05030405070303080604180c0801270803060114040e15040608100908 72
    0x510600c1411924122800c082c60006100c40008050101a0340140200400940005200f070116583c1d881c1000c41900c54240c4d960a089810840a400443c004088024041c44a00542c0504500d001c0500320440c0d802a0b0000c6803024000c0d21490210750b45180350300d102e090350418503105001c040d04d2a26580d0301000c00c500b440500b0b94404207403684820040301302a00c0351030000f4002820109003501c400200107040c0361004001c602c00142a0495100c3d010b115816a000940d002c0513640d0350381018104030700c0071301c2c20304030881c441c1d07003030003d0b0070100351040040e80e0207241c0c03000c014000f903030542c2d03400d40791894000d00c640d030041d5895040341a400328003030951881c940100c0c40ca1480c2820103403054213448005a00710540504d0545902404405c10301c0e031041c280c1c1000040d0340f00d85604004842c00000b81d42c82c28425000132501090b1920b414003010f0003496007400e4201c100c900042031005850480c411581c003030300138154800b18440b01c0d400c107107400361140813410720f81800c0500607 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 196330521 1250 196329271 196329281
    0x12010b031b011e0e0307090b030316030509100c061d03030403110c180702010b041505010e062116020c0a05010c1a0702280209130809061c0b040c0207060e0112 70
    0xf600001c07003984000040f1300b0240f0148001d051a5101400b5104070080072035981d2041c410750542c01600800c412091500c40c1e0291840a480103100c900c448401c44401480324459107400d4404625101c226040e401c2d20101d80640600075401035401c40e951503d040d15817885485841c1d95034011912494055595030f41070701d9016414100703034402c0e410004070080c2161070300710302d542c0114504201c66905002004040d0100ca0003464464001d25008002c141c9a000e0b121a20070b1010007840700304050200b03100164404e4802042b8480322120720b8504070703510171a0920464001d40e40040510503948261408080d09000302202c07040c800302c8802c80300c0600b43c00c4407d00d0050300000c46160b50796031032104071441d010480c80b04104904060700080c403003040c060a905405150406c00c40c0801034407105896490800820031600c40c64100004424403c070300e03d05601952400064403180d1401e4410101450031550080c585181411400c2d1070b100400d841407814402e143c4a0614041068021 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 196331771 1250 196330521 196330577
    0x18081b0607140d03020703031406030c04020d0f050403030b150f0306090403020a120f020106060e0310020913020c070504050f090601140f0a09090309080619050402010e04020c0c12010b031b01 84
    0x10046e0740c1c034558100103049400d11003280f60a140c200c0240a010b0f5800501c1c070703113410400c850040ea152003080c001002041c0d185040001c0c94105001c120600d41c140d841032860000c10b6030b41980c05e4404640841c0a48508507281c0184d1405001003000707410300b0600507603c0380c42401200d12000b100d40b03403440c00d021008080000100f030101020441c44d820700840d0002d000c00c0c181302040407405c01c00240c07150b000d5800341040c0ba501084180603540d403041100e0760094884403c56444040c00941c8c0d40703c146038040c0900803800c10022030151030190b80c81318407602103040030344910f0b400c00c40c00c032407400101411164005500120740e1040c0d42ca40f001c0340014400031500084c240c03410f10300603007904032a5104407a2074000d24208180001e000845121845038200c002482e41d44030303c01610110300c40c03000c1e80d81061002c1220348010000283c8800c0310300e03045400b8051130340000c10762405d0b80c1c100c0200700d405030841c0d0007850562119191042103540305040801809441041051190788086c80d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 196333021 1250 196331771 196331777
    0x2160f0c05040e01110708031f08060f0f072106050a090212090a0c0312050403061a031011070201050d0204080d090e0609011d10080d18081b0607140d 66
    0x90400040ca00ba20400328841c28040007413040d0050350651050a000b0264045c00d05200040040c1c010840c0903011800b0034800708a0380049515040c10f0703965070340211640110801001c02117141ca4400e40b203040c0c4101482d507510f8a280d22140100d03d41150402c41d03400900c0d0711070501080585d2940c00150190110030340041c0c86d0968094078450080d4050043c4d002a0001150040030600300c80d044802d0300e8100c0f40c000900c90003508112110720456001400341458034141d0b0003074030070000101c2c40317201d011800c83d09464410484a000c440c441d04080c0d0b0394a10810107100194014000703400e00c1b00d60750000508269030b85001c0d5007040d80d46441d803000654000420301c10180c10031440ca40107001078034064115030400500c25440c10f2848034071411300c558403000600e0450b103003801501500d0b48805481e180064100003408002242c440310000b211001c101055214000803040520100017051941210340501400100d5024400986010403182c0000348521010461111495070740d80d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 196334271 1250 196333021 196333043
    0x302011808030c0a0c09050103020a03170c030d02071101090e070e030f19020112092d02030106090c111c1112030702070e150a03021e0a080a03110601060f0302160f 72
    0x8a4001c17500040c80e00b010089902d000010300240e1100c465110999520101d0110061103090a42105010755029008036100001c0d54403000b888540151100f00d02c1090781109581d000001921241440d02404100300109400140200e1151000409d10309001c1e080c0d032140d032144500c503800d01d03944070000d03489100210154811544d00c1030b070449245204030010845440e0540e1541900340ca85034144020360b40c40307541003101040c20a08514010350040c000c00040384d50740342c1030003d000103c5c403010200d442035129040708003001c90103404013014600c0a00c0511030481d0240d4010120501d00e05261248590b05400f07090203200441c010015500100120307850700000d0f0881000040c10f20540f4074034001050042c1e11000b00030000da0798112100130384111100101c10300a62039001d041e501071071340c68000914040110740d00340000d0096543c5445460f481000aa907031741c0a104420000c3c040d404010740943c03107903000d40072010754a0000c20621802d51940721049d00c107001d0907940c000c605 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 196335521 1250 196334271 196334273
    0x1080a06080a0b2505040605070215030f040302010518030301230310321b13060c020f0a1d1f0902031f051c02040e010e0a050d0314010302011808030c0a 67
    0x1203036211468040701054107002c0010800600b1780c0560b100301401d00c03501040010031540d40100200380310181854003922031400303285d42b4041e82070070359080d8055468840440c107088840d0707641c0707040c404540300210b195910707110603414042d100340c0320080680e00c03030b00d0ad1490581e003c6c003c00040280c0604046060b8001000520003511706500c41040604100c5510384001c4540d850154007806220171003490000d01c809030086440b415940c00380c8840c42e0400443c4c1603403c00d01c0704414500990707030103100401410901c92600b00500984011084418140c0408103030009119271241d8081d09518419849164900880c40b16030064000d01d034011007002541000103d581c48018524028061030703603e0140840e41c2c90b906618041c102403510050030080d900c032908801c404141c410020880000b120346410385603804400110307800e000d8400c40030a0a032080c0104091003440d4070061505900e160700540e40c89080040310000c4201711600025514014400f500b48403c454000d04030748009 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 196336771 1250 196335521 196335541
    0x40f0c0504060815090f06210f0606180f0403021510080d08040c17011515120204050f01050901020a0f0b070f1d04020703050c010504060605040605100e01080a06080a0b 74
    0x10220300d202c810400c2070314525603900703000c240c021840c92200135281d203070b540c0443c51410b1040f0440f2084010000c07404420300700002c4060310085000251901c40c0c4805003004007591041d44801c1008443c0004034525442c4dda04054100d0310a004490485601810309101941d0450784440000d06400e005c102485050208600c010703001d180c15000f42c5026a551005003c50b8050f08140c0d8025044641d160301c001d6004507402211201104480750740d41e0511100151704200c803000141000c100c010b82c4000600a8406688009000c45413880c0c1c0c0d500110350a404c80b00b0080e04501c5a0b84280c004103920f090310380782c02c6000e00d09a50380c91400c22405000200010444820020000d201c0e040c0307561020340e466101c1404460150f034800b480c3c107040711580504a2840707019441c040c180010043c580d4403201c21a0411b88003804000c2d5202c0400004045540c0c2d0394001c00c141b407882d400380c1e61080030265444003030b44000254417500d400c043d501c1c0000440040358800000d009000110720 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 196338021 1250 196336771 196336787
    0x60b0a08010b0703120b010207030501050c0a11120d02030402010e04020a0c0203061602061308070b090c01030b04050402060307081b0a0c02120705010c0f1e050c040c05031e06040f0c050406 83
    0x4084440d880c080090b13900801080940a1503003140c0d907607a45101c0140c0c400c3c005a401181c110000380032904110503c400c96612401302d0402040e02c034000013480200100c0c41c400c3c801b040c0c031901400d10090394010320103076100400490400c25140b21001a984d2980f0103400c40d403041c0d55070070000345000d02c141032a05d10050525043c222403002e880c1d04aa60008419030301c562500c100310046c00303d9180001c980c1c01280d60040101c10304004020410704000760b424001d03a400d80c1c050020b995020148001c4030000d0350082d40140e000c00008100c64010006640c014003142d550450709401f000c0003405a4000040580001d00001121025850100905000c10b0548009080c060342b401001030150000494020300ca05042840b02e000e00422483c1d9400e02c15060b44400c107240340b00d00e005d0f500c0d021549580c51196182c0391201c04424070410641e8440c0114080d03544000c81740903401c0901510080803980c0c415104c40c2128840d94281c010318942492507201c1649490520030040c04901c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 196339271 1250 196338021 196338029
    0x7060507080105031e030910020d0f0c110910050319110324100806010b0301051e010f03020f0c0109080310060507080a0f110a0c0603060e010803070303020c030d060b0a0801 76
    0x101d40310380140800c0ea804151071003d282049840500003549000c11419405480303c0b0941c004a074900d2450720350740100b0301c0324080c0c10542d5462400102903905440c0d40703400c0000600410700c09250030000741410101c0d582c2201c02c511107440b07200ea4842c0081d2514201c400110000c505c5404004200440b0714403040074404101c025001040d841288403003a103a0711540144600e000001103400100341110381e001900c164000e9810545e15251080c02a074000e11603980180301483c442780110b100c000b140440c801c0140e60301c4101c820f0682044001e500302d40000e80e102882046842110070003445220081c07031142070307825104d260202820140d120f242d8445000d01c482089103d0008180c4c20484600340c3c180e042c074007858148400e0843d01c14160910000d9a0300c03500f003581c0d00f0300011000c040101c03001c42d80c0a00c0180d480d00b103400d120380000e12032506107500602020000078041c0d006003e01500d004102c070305000e40c080c00341f0281c0e001580b018516400002d100b0210303a81c0202d1280c090 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 196340521 1250 196339271 196339277
    0x40c0216082a011407030801030b09010c14090402130906060e010f12180203191e020105030c0d110d020d0b01030c0c023f0c090405060c0c070902070807060507 70
    0x5000d5051800742d04240d01800440d01d11560ba81c1d298a60b0180c01c02190210900d130f2132a032103840d40d14001d41003250038082070301c0160400300041c41d001814000d160030809259100d81f0f400e00a440021200e402c128111640f00341c09200509511460514110061003500d2000c0ba01c00d01d0100c001c0c141c4149025094100540b540f0b59949042e04104060003031038040f4400135040500d0f9214520100b46001e000354103000701c100c2c1d6400030748840c181c22107450090304007c0c9503520010800a4110182e030000340402d4040c00040c0e6507140300c0018103080c24582d51b01080240a0080b800150f50101010064880d40485c2d00081d40c4058843c4808070703482800c082207103689009001d4001d520b4082e00a200d44c44c502010001d100d41300c04252101c038500e5228040e10304c210160b128001281c03115103da40e100f008101c041da40f5000c2d039500c0c003036a001005000b482c2c80c1c04540d585160301c41381c603080c5035200301a00058102c0c4e6600c010324010b4000c1e000c1680b194554a440d105850000e0700e0f000130 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 196341771 1250 196340521 196340533
    0x1090b070507080f07050709061d0604020c070302130e06071101050106080c03060d03140d0f052212090b1204120201050c0406030c030b090a020304140109051507020c040c021608 78
    0x3511400407103d084080d650308175140c210380e19000f40750440c170b60401e490443c104840000c1000212007180f4881103107201101d1650b1380d020a201c1240200c490340c907a990b101a0b010070240c140141c80a115021380d0001051707104009558a181480948103400010051340781007440400038401c0318007500d140e2800991500b04410303030308194000034150a11035142c2c0e041c60310815001d90175491900000c0c1403c151194503030380882d001400000881d035500c60501c030010b9000f0100c00c440a1804401c030071401c8501325a03880c2c0c400b8807004211070710207100c401280807601d101d4200c042c203640e01c0200d482000e14501340c90b08440d4070102c42d03808400e5a04090910010f00407400940d1305441c818940002d00203500c8000300c024260214400307800190340c10500007015210740042d4030035400703a081400081e8000920360308a40c1d00e95405842a0040311b0384405440800808540001040c0b0484101404031030000f0125511902c030140541e1190070702d96105090301b840d8000a107004406810 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 196343021 1250 196341771 196341773
    0x9110901260103021c120e1e0604090b0a0909060c17040c0314010f1e06060203070f110103020d020c010903020106080304081e03041e030302060a020c0c010c032001090b070507 77
    0xc0905041c003000f80b1500c3c0c0e645680c00c54111210780c800741241c10040f00f171606e80002d00b028000c4003402004901400c1001e4020203058000310001d000c0d008060300c80c84c981480d010210303006100080e91286c0c803c0c4200400500038010380208641c20307004500014418807600300180800c8038950407000700308030b08820000420318520b641401c40e90000301070101003800ba18058010400d420146e00f10300d1420b00403860300c8090304a0002c0c031250040d000c1100c15103131202aa0b0b68020030900a01080300070942400003038590050070008003042c14050b00b0071042812000a98010081d09803040e1741d1013a41c1030038142d090050100a000102c05549011708000c0c07900d803104180c4254600303992806460044880341001121300501880c440100001180f1203101140f544902c4140c0061041801240a0400c60b01c2280c01a0109100500744006050010340b013851181d1030a50134000d03d0340d103021003a5116410340251036680c900010340001c1030301e0021302c400405002c1808219007804584 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 196344271 1250 196343021 196343087
    0x90c1e1e0d030e01021006120215030910090201030f0914151501030203040c03080403050f070609061205060121090203120702181b130e070e01050f090a09110901 71
    0xd00746030149400200e40440e2801070345400c0c00c180c000c22049142100c001a200042c00f185240b1500c00c8805400308c041d140c2c1e0821755800244c580c000550803810404032682e22075441415614418100401c034040020f0606003295882e04040d90716060320400341c1e41460007882503002c14500c01c9003111007820300144100030313040e409501c10b040c1030340040840c080c0001d5001d400021603000000b15030740c645915000e5100c01c2c0300da105460f00c1c070480d100400c140340074800840c19030b0507a41d07810040e80b541a00d80070240a0107082c9605001c0c030300641d00500c8180c0100e035a00d1812400e804039515100303105261824449010301030b651741c4240052401a0340d029a150a8200c03988088080398443c10160014001a4081d440000754002900b59100c01d03085101c604030f03480d8460445240ea110f1000b55010742400320040d000a5082081a0316101c071036000e4240340c6006800c418031551900981400c80d144202c49400e0b151003c40d0b040140d684c03000c200426003403c881d2000c44550120a20 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 196345521 1250 196344271 196344289
    0x90102190b0a02070203072d0f0b191101062301051c0e03220f0b03060907110106080106090615090b070f0303180b161403010e090c1e1e 60
    0xd42d90320ba0001040802c0d076a0070030081700606409112041c0d03803242c0e14980b041d0300e246000041078101c031b034140c00141c003150140c4a0003110785640040c1d180a40f101c02441a07101c80505107400e00c958440c01c208603903403d00c60b00010b0862a20501c1c04412106080403a020341580c0c0b29040000c01c20042c43c1c0740e09032900143d20306881110118042100001c0b040c194040c00744d240321205461408000a5140c03d50802e084480401c885040f41da140e01041001b488211601900700c0400e101080c0101d100e036001056122400f400000d0b410f0700d80d0780c41404d4900c0d55220b1175065450b90010301054090031030541c0f906170b00e401c1023459185840c02c3e280310ba004811000d8220900c0dd4140b0092500a4202c2c441c102c0041107a02d20b0101c19160401c144c6806560904142150f540310304100c0d409030300d404811405158905041d0381c60407040f41c02082c1d00402d8443d407400303020ba00d1885070700c0b80d9800c046a803060f4603c6403070070b5828030b003485450414000380001c0450140341c021800d8aa500e19 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 196346771 1250 196345521 196345531
    0x30a06261e120a0c080d060e0a1107020f030c0d0507090b0d0c090203060d1410290d0f05031b0f0309010504150309050601150e060301050f01230f090102190b 69
    0x316a840d60f459000c2a40c24080c110405080c00f140050442c3c601429548005c094590016041d07245840721460f08080324003402d64850b42403410050000980380040081c01407800c01001c0f64a504180e201054400a08902c104e030154090b443c1404401040d000302d0f1040360040d01c98640c5074500d46c80714861903019210301224140d0000c0030403104c0d2154483c00c100c5035008075407007111444021000e9981d000303401c0c0e454606807802c100c6900000d110782282040c203d08102c91000610301504102d10740e034030b503c41110641d41c48a1420001913051015001038015410080031000c01010b1080c145512960316034404e400800c9540d4040c0e82140030381d03081d140c070000030741e2960000d050140d0003804c0c0e40070040c00620603400001030b915a52110102c80c15a07903520701d54000c0805080c00454082130007011ba008212940c801110b5219041d014940d5141060311a146514804800465404895400c0b40321600081c802020358041207050508070302498010548445501d407007000300d2001c0c0c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 196348021 1250 196346771 196346803
    0xd02030705091e161d0a1e08120c121309051801110904060e010e070c020607080403030e010f0206090709050c070510060509090f0703020402030a06261e 67
    0x40031406048400400380c3e06880e4403000700055040c408030300101c5411000c40040000c411310030103034080540d2500301c0c59042029100000172800c1942031180c0e810318a8902142144e0a0300000d0105001c129090b00040342049603585d4007203c0f00c13a01d0030184c8842d2000710411040240c02841028620000200c60302184005071076220007245401800003010301c035103a9820141600081e2410200030100300c001110300b04403aa5452401e440030050034070480024601180000e08054011448400da180c4002c142d40c0c41c003d032540e1103009c25045508181c0c0000d0200408210958220200d0010701d40c0c1c03030008015030700d00704044503540d02d841e00030030803241d8464004c9018090007005031402907078001c059442c0c0c0454094030400402241c841c0c0d0303110304210004900e494201181d01c200c020400f00c0605115415902031101940c005001c55142c180e0320100082e42c0380c03c032144c202c555560408500400350500d004549441c5402200c030b5a6200e0f0726010100b01180003801d81c1c07003d02250303 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 196349271 1250 196348021 196348039
    0x9060509090403030e0a05060109060503010b01020a020d23030406030f0513140c0a0602280302060f04020f061209010f06140f12031c0f05011a0306030c120a020f0d02030705 76
    0x11500701d010b40409172494a84d03100e550b202c00b08011000c2030300d9060b114110710400c4083e42e200109800e0700c1ca024085400b5030004681d58015003001c0f481c46440d01c1c005c0b00241b4103244001c200d641d0a9400a030401c1907030700f000c202408455814001e180501d10040d0b01440340d400e092200240c1002e50260080c41c3c5000061038a01c0b1480c1880040d00d8048000d000d1024070b655418060340f036540581d08085450b00c00f008040f85d8100c1c0404001c3c2c8190580e00400d140e0b6a1030400100040700a0300076644001d0700c46215016940b914001c04406a03500d044100c90f08050900e2402e440e10340b4040044e44d401c3c21010300900303160202440c1c00d500b0031503840391051124001b04450001070840400b00707000c001030500040c4030002407030060342c19600080001040100480080340c00030302a0102e4180601161050500c0f02c5014503005000101918080f0341400c2c0051002d140c0e548240600e504148074000a5141c1005014003075502998800c406044527070010751200c000f8041c46100710641c5c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 196350521 1250 196349271 196349273
    0x1b03090109121110020c150a0906050f07060f27120309111309121707030b01050909010602010518070b0f070c03060c05090a0b18060f070b0a09050d090605090904 71
    0x42c01d07002c0f0400090034000202c029214000e4a6000c20b942c10750003202100700449101912800f11010b8000aa842d404040d0070500100d40b03070707405034000c095030100a101020200350244074034008140314800010b90510030000108150b80e014011490f254544c101a0002c01c10f10300440c1300080d0145800110307d6990314000010f500c80e92034554011481a1440701d040300c1c60340c8608102c0e80125a000a10a6481811681001c819003581c000f1840b0300041404e40703010303400203075001205061040c10b00300c051001c140d1a0070264800c00060307454805000c6c1c180140741c44154410100c5c8040e150b05804c0010f200034a114881170b480386280f00041c02001e00041d1b980d808042e540c0000e09001360000b03410024025000100c4181c842c80340c0c0480010043c200d54221103155126a1030180c401d0030b80c0e010800f5582003c0e030745034600c5808105030380c006140840c1d174611034075407013100041e0030645003810361600100900e410144052104244902034001c0c05580681c2802c442c2421643e40c0c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 196351771 1250 196350521 196350533
    0x1020106030c0314010605060c0322030204021306030507031808031b03010605031506030603190204020c0106260703202202030411091003080c0f121b0309010912 71
    0xe40d41c80504184001c050200030801c02103501c1070000603041c0240400b940350800c12500f84201e03a4910080d6004005640303003d41070110320202019460000c0c86038030703503a40116042e40e01001a004c844618018107200e95078251107880c0e000a1907190420540e40d0300c501820409244980150100300080000f41681c098000794000060a000c0300ca0385a5964103009041d582098030907260780800d0b042c4010640c100f43c41035034070801c1e002340209a856903200da030400d03d89030b1500998000342c007042903101d4503000f406500010300c8080912000180c000408440280b030300d50f01c1d0b40b456001684100080f40700c2c4071954009940b02840c82c12601042d00c0024481918100d070012409a07650036900d82020303d038041c5120381d00800070318000501881c200200071f06e003195800d50710194410180041034111000e48020b0581004807040c207012803001034900b504500c81a242001c00050081420841030390000603100c2400c025403c000c030940029021f10290700132001195480010b403030038004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 196353021 1250 196351771 196351781
    0x70501141303021002060a140610050a020f0d020703050c1807080903040f030804050f04060303050f131e0f060e03031c090b0a0509010b030609120717031905090d120506010201 77
    0xf03070081544521030b01c84500691034400407690302040c1e61406030b10840031001c10a242e0b00c107030030041c00e81101d90f00851044d206600188041e0046200c0d441100194820410944512550720340007803410f60310394500b41d8505992524128020190b030540740229401c0070822a400400c1ca0070b01c060203503241d500040ca10302847d4401e00b03c0894a0800006014005000704143c0e0400e0340e08503e6446040d05200540d4150f04c8013b0004008000101515080c1009084140003280e62903c00c0d03a42d802c0b1403559214040b00c0d0303003895940210100300045d199403400740105a40d0801a81c0c0100440000b500c038001d0aa80d84031100c8038009409503911070340c3c4550a900e61201c9605041d080c4110500000c0a0850300807030150310f0415049400c0c60b001035581c0c4101d007000c0040405a44a0802002907041050110b80c6000f12541045992141c07401943c411074401c41604d41400c5a801030009a41c0701414841c1e150f00030000d000c0b40d241d8402c0c007103030310418092000b00c1e5070740342c160040740102 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 196354271 1250 196353021 196353023
    0x20d0f06090308061005120c0f07020909060603012405010807050c0118110f0a030602070f080403050105220206121504020d0b040c02010506060403120c08030403020a0311070501141303 81
    0x1803910001508140c0c0240400e4000ca40a42d540025140003442c06d070b43d288182e004030791801915400194020007440c00801e500c08182d00d42d00e040100700c0e408103208100c1642d40c4201ca401400401000341002d100744803130311030412071140c3c203a907901c070004807100f0b0b26014030303070402050794001801e03180913800322138029954000811001d040448088104c15181c5000c40b2403503408605d02109103004e811318944480028082e00d034191940ea110002540071880c1152140301880700007003c83c440001400041d4001e40011070316280c20b80720703c1d00d0030601082d205040030314202c4100140c0c88041c103940f0710440c006141a4540c070380107400c00c16600308980300c80d4807600015241540700656048400c60b00da0582e4140b040341c41004041e4280c036400c46810307030820340500040000c00d5010644611801d4241408107034400c55840e80c00455204480c140c000d60b009c0401c0404044e4000c5c10002480803c10183c0701c2c1500b4840001e100b1030741c45601162140000c20480d80104012415000035 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 196355521 1250 196354271 196354283
    0x3230105130b060d0f1413020a0603061a0c070f150306050907050d05060f0406060f090b0901021c03020c010207060209180103050d23030a0905071a0d1109180105030f030708030103020d0f 82
    0x1d0726210b1010074015080c7c146c224001d485104001480c41c2c000d001b1081903421180c005551181412002300d000d40240c040c642e142e00c00d40d900091361030514203d10002d07000c01401003c1e031b00c040b0a0f002d81551400d0303010600a0a4050800003569400401d54010709100c4401080a4485000062170651135072910340d48549041c000250268210400d1074050240f5180c4410880e40c50340742d04203501a00100501503003001c41c044886800145060314000098200107041128904405d400ca0700480e404442090b80080c00c0394003440e050394031200f11919081c240d0101d6066030703603445d1129440c0b00145e092003000e40304a1221603080704401081c1c40910b02e01078880c90220424405828040d100351000e01030758201150002c03d600d80650f540105501d264035215014856100816102c0782210302840d081c03001c091a59500302d0344881041d141183c2602650500c410542000503601d031015965004120b503400041801d4103480c11603030102c482c0301d00f5000d24103005046002900c801800 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 196356771 1250 196355521 196355561
    0x10605160b0a0506040c020105091203040305040b030a0b0111031806160206120a0c09080c191206090b0c160f060603140708070515070b0703230105130b060d0f 70
    0x2c1d074203465228501c1070030120b909214000318104181d080b00e0065031025040c1e00310702e498600f08580000115080381c400c2c039000c5c0ca8169900c135001002c0d08240c408035511a29120480825a4050070041c03080050740c0156207041c402c8440e60a84107103000906005040100d56240040202031144081c00d070094030155a030f4600c600714801c034840894212031540d2a048440310070308d04c5000c0890503911004000c1c90b1425400d810001d5503400d20440340050040d0500104034040800040345034a48182000300703403207820780360031049184001d08050b69030b2020701035240c0d004001e0703611b801041c2e008014546007000358107184000d801c0b03e800c080c1105c620803030028100a40050602c089810310410303101420b0701e802c10000c42c0c00c1d648040c150b55000500c0380788080f9603c0300b502500a00b0034100090000c2802410140b00107c80300c14000303410700c5000401c16801d04003000104060421001c200700c098250001c0ca40b0f0051540c081341c4696a02225042140550301c0481d82c2140d950300035403 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 196358021 1250 196356771 196356781
    0x50c040906090b0a06031505150a060503040501110f0703030f06030f031d0102010911060306031c0c050705040603051917030a050a0f111b0304050a03060608061e010605160b 76
    0x8003401d07540000b15850700d001c0380004c180b540d007807152005803644029400c6c4040d2858102c080a0040a4000f10103010601d0040b4900d544a00382036005240540b685078407032910741000c42c00c480400450b03114524080280445480408085940c51a8503050000d0101084c11110008000d0342d0401440d6520078407410003411742002d9004031625000100c0c03441002c00b04012401c0e185000401440b0200c4140844068a860009141d000b0310142c204c2e07002c13019011244c1d0441e068450306c4008511440101001d000741444100003400701903c050020030700d180d03516035139554507048071070b8a880811600420402151089a081c9001080e01c60f280e08000c0b4050300104000e4980e14903c40c5410a0f0f24080421405008406080c2c000340f542001104130a40205c80c1c0b40703401103141400100000721341a40c41c00c00386c03009180601000611345080800c0d0901d401d80c090718242c102001c00d248030030544e024501890555405261854170b440d581103104403403401929005019071156003c0003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 196359271 1250 196358021 196358033
    0x20d0c0507170c070b07110a2c060a0b070302071e050108010e0403090e1012080307090e0910110f07030f0f110627030a08091c0813050c0409 62
    0x1010780c081d4104000081c0c1e0321044860300d1050b09204400358010751010003440b030480f4003800d1480d01940300000b1000c0750348005582c122441c0c01c2410f15a070444401440b4826404030030070080b07101040c071421401c107440000c11507a514030900840110004142041500c00d0080ca001803464015162541d00495070103540d07100c180c0500e40c00030340f040740005600100101d0007401960107440fa40b80c40c174100210140250740082c100281c0e101c6603440014200316201d00740c90894080c0c0d01e1a5101e04041000800d8903502d0380c800d0714014880710511020080200d45c05900425a541c00182000f02201c0070b07006c0d0107010003d034000ca002007265014550040303105005844640d884c0107403032044540507901030780020b15403055a842400040d100c4124058001e0042c0340100101d088560500903181c51640724056601c00220f1000610101e130004010391802e03d00311900010394903555202c000d00ca200d005186241c03006c140503c0d0014060b050020014411001d0300620044100d0b007442c1c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 196360521 1250 196359271 196359277
    0x8040f08070815070f180f030305090307080f120d090b18010c0212040902030c040306050118062106202a01020c030702010c03090503061305060604050103020a18020d0c05 75
    0x8840b1900400c1c4240d001480c80c1030744a8443c0102d074030340320041c80f0940300c12200c0c0b0030004080075030703c1d007841e0012400d14031640010008500c695a803c1c3e544511005043c1000d000c0d80c0000b4640d80b20f404071107079100c000320b00d5480c7c40700c145915540358a42020414050f11900d00083c2080c0048814411198201814400c088070120028000010042802c03a40c1d0f0413107925102c0b075480140014013000700b00c2d40003141c001183c0c98a080c24039460b40c032001c0c211a03080c0d208070385e1b103910903551000f6019640140c00c01881581c0407030760701018400b000c05240301c00e0b001c005c01d4075075602076680001105040142071110010202519800030901401181d03c21062170124131410068080c0038010500844003031400e8400a54208105a4015202202465012001c1c494180303008501c50f102008440c0c8078101e0f0a1911040d00401d0400780e0070440082d0100c2e0107241082c0061000da00c0301c904c0c01c81144e050302c02d80020414000207110081c001c50314560752450070485002032069000000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 196361771 1250 196360521 196360529
    0xe060c1c0f030b09011503091b0f0305060c0a050318030c0109080405040b0904021806060706020c0c010e04090b0f0915090c10020715030207030302072f0406060e090408040f0807 78
    0x2c00c03c40e03142904018000380240b00d614403030818400d55081140c46030304520500c5100b0981454034038121000c2041d0b02c0c556401204070000c241d4410001d22100708201908031180e140b5151030403800e1000140a0302c4000c141208a80c50b61001c40c055581c100125400858820020001c0c075800707141074040360303006114951003a0704000010304145000508070340a40c0c0c0c01000b00d500420104507803407070110010f040702e50145080c014400421194001090510030f454080c08004905100140c0300320041c60b40c050042d49059210000103400000b455002860b240e90122150f4a1950b847e1a00c1c1981c030841030a40e83c1d10041c030040a40024039070218110854034200713100712049089a0f911034501c00c0c900304049903008a02c2043c0298010a0142e0081c42e0151030041c442c0c41b016845880144072000340c55016655842890b5a42403540005030121000d1006502d0b000004009034010131900b8440d4040202103020402043c00700c5008002404052403c19070798500b540c1c450365984a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 196363021 1250 196361771 196361777
    0x60828150f06030605090a0903020109081201030c0b030603101509020c0c03012d09031404061e030b011d0d020a1d0c0901090324050a0204080c03030a0e060c1c0f 71
    0x110b001ca000e805080191440500365000d15510a108540904400c01d0141d00b95541c81150b18040740300c08008042c2c80c6401c4441910a516518083c0c031058402e41c050303500100e05000b03001035580d001c02c0c20710404401c44000b0505200c040a8104203604947c001d902d22840004c030022440340111300480c0b9000110020000001d4900410140496025600d50480c2d01151201c007000d072240e2008102c0c034041e2401c00760001c200d1114954650003500310314007280010b104c40c4035144c0282419109040780380b074148104034150002030404ea0009041005009201c04c1d04135103911002c0c27540c07200e580c000b030005120550383ca0502c400407100a0309010be050150001400e40c8580e00b045905160069440d5610649161035000303118a904a40c0010a907420f60401846841401254055000208010798451078480350900d000c040300341c0c990094005000c80385265410250030f05100f90107a0300e02c0d503a0603001902e2401e00000b1000d0101da540e080d4555402e080d480003103a01a905151 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 196364271 1250 196363021 196363049
    0x10b09121203131e0201091707091a0405150a1502011119080c13050f0402070c090618050c0a0503131b06080a02160222090f03170106082815 62
    0x4680315011188980040e000c54003003030f41044070300c0b04c5a203030700b02410152301520155a02c603401b00c015544032403030024102c0c600b59010b80c1145814440c15401c0345a6004130101c040c841c0000c507441241c64801d40000c41c020308190540c8034000e4104840324600410459a01c400100003007590681e40d18030340c4001fa02c40d10004105240700421902c01d5040c18158a076810302c3c000c20090056840e9140c1c941041c2c090120800243c8039400b020050040c040c0e0200d203641c00c1000402c60710381c20f0001d00303c2542c24081070103005a1182d0458141c00310600c1c056540340d1310f429900d9080b141e146d400904444509031180c06200542c1504026120140d80b51096501d03000b020809034022450142c0050182d1110300c030040c903001070b07201804841c84041c2000c0752000c1014800f2039180c040192000030394440010101a4041480001400c040800d100f8a50500800801405c0010041040351302e1007554618640c20f08103d0703c10440c0200402d005640ca4900301562400e00f5104d400c0150441c4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 196365521 1250 196364271 196364303
    0x6010c0f0b150a03061a0d03170406090827030d091401110a030906080c0703020c100e12010902090601090e04030c08070c090209010e01020106082e0212100806010b0912120313 77
    0x40076047e20b0950190b071042c241d801d4a1070b0b005c8800c04081c00440d20306d9900da80110004a80001408040000f0555083d0044072514038041c10041d01c051030744a904070780c8012803010740114824040e6803060081e99240c480b40e40042c1c0301500003401d40030082c410f100030041011f42c401000c6c41925010b954003022900c034104060040d002c0c80c0001005a049088804801c1c2444811240958036510b0701c000c010b01000081140040f0011402c81c40ea510b1308800419402c1c81c60701140c00000070b00c1c0081e20945001035a4400f114040e10003800c010b4446800000d1000300d40c1911a05900217210300341641d0f480f0400d4009611880b0864007080c1f40e18040b0a43c2d600601c42c0900703c07020040906200392107050110851a00300004510011760016007040c54100d41c030141041c0800a4181181400c0c042040c040429003a400b80b4051f50042740140181c0401c0c1058030070800040e1071580443c14080c0c219130a000a10b607601c03030410780100170025882583c14261110901a1440c0f00c050381303079 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 196366771 1250 196365521 196365529
    0x4031404030c14031606032007050c1203190903030f030522080c011109010909020406051b011404150e0f120c0f100f0506010c0f0b150a03061a 63
    0x51440094040032412408110443d0104401d0311258002002c1d61818115440701200b2903030160001400223507111403e146004c54560a80d8105814000d44e40c2068550303a41c0555551b1582031040c056140781100c3d2007040b2040003543d240b01d601d08090340c822008000d0080100c00c0a01c002d400180c0301c00d0b03130391071141d02078400c4a0060103c40d80a90070614105110070300080340e03100845042c0f00812900070100028440c0c6001c49042d01c095a40d595104000104544510f8000e4400340784100020040c890700300080700e25011580002001030b0125030340300c0380101001c074003075690840140108010005c41013041c0007261030340300c020000080300c49210382e07032100c0381d41134403529900c417400b6844c2041c2a6405001110f607110200c90604034030492940c240081900152030b2180c03107001141c0510300301d01406901c50002c1ca05940400700d80d4640d84e11502104002130700c00d11a03803000c43d04045401c3d542c1c2000b801c0181802d5000c5650380b804038000c3c600440c5007445610b410041140b2403070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 196368021 1250 196366771 196366777
    0x8070206040314070203060a020309010617030a031a04020309010605040e15060f0409050d05030601030c030905060609060402041a0705010b0301090803012d0602030a0207061b0605040c1a03040314 86
    0x4950091031103a0341c0d50b80a8804003401c600056020300107006110050b44c4c2001810301c941204d003000758490410000c040e0035079007150800c415031a058204000e070180e000095980c049140e2801042d4100c02121781c50301210702000d03040c2c000d4000020060280380c15000b034400c840c0c05503008c108084112807070781d44031800ca0324003000400c401d1000c1450740c6040c2491421100c4020f10006248070180d681614180d00c11940401040d40030041043d19038040c8280d09800380741d41400d11a555040d5901600c81d64010100392203045510701061079501d4650542d00a800c070700c0c88104010307144204509064024081c125829030070449046400c2c2410b02414141540c46a00700d81181d0816011280d1410b00380c40c60307102860800c0d02c40050b401d82c00040d00081c2100e401442d520260000004d080c840e0300d0704400d040c4030100b1103a0320900d10b15042c9540140d0004400105501d4528020640450503444001c02c0403a1002e10440006043c00840c01703184a5110020f2112142d582014030380 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 196369271 1250 196368021 196368031
    0xa061505090901240804060b040e060103030e0d2d15060314010207020a0512010f11040e0702060f0604150312050306091e06010c0218010e01090c140a0e06040909111008 74
    0x51000444c81c0c500030f020b804103942092103140d010901801680104080b1203000031005201d0740420010401c0c10340000080031281d10960b90620440400d8032000d0f445800405598854411540c1400d2141c084112840300e25600a00101100b040011501d0181095000503554801e0034130388104c00600510071200c03919400350400c03188500d04020045424146565a0304554036a56102c0400100e84500785a1291042c4a2620303141040c0c20065842c0d0f00401c2d8801303640c8000e080c01405d803850054203a02004c1110042401500c0b00b000100c1c403090740d0700080104914810762010030381c211024522800341074804459079554202261500c00325031081000340d10300100032540315485501e11041d081d0000c0e101c0407a04c49910300d00c1c591020240d00160361841d80e400180800100f500581801890514048100000440f5007010b1446200309020512071030341c1c990071280c0c450304150340080154500c20440e09900e41000142d0300d0321610b0303941c030ad40101c3d0f410801d514000c0700c0e00713030282c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 196370521 1250 196369271 196369319
    0xd030b0a0302030c06091516061404020108190603140706020d0206130308060609030604053412030207050913030210050c0304060b0103110a020c030d0206040f08030a061505090901 79
    0x9105101d0503c200c560041b62919008131380c1c2c9401e2480e4511510080c5848189203850b20841d0105003045404c41c2d0380e481c14404150042018000541e03440301c0d10340d81124482c4071048050101980c404014105580001e0414a059045514100e0003140c418226031841d003d8410351401d141040340c460f40100d40d0200d1040209900390301103031040c0c481039071101c07028168620740700359800000d1500e601124111141d501c0b903201c8c09190340d10313014024a6000309030440b2801c201307104c0941c0c5040416000b0222111f00010651050610802540c0300078000907100c9210b034203048180c0064941242c0d4181c0c0544511501103078940381621503980304901c1d1460041c1591101c3d9a050b014000045000c1d0402d900e41040f40001164080100103c00440e0003d0410b54200c90a150518503c01051015034001c14104000300d030f440c1c0e500010082d40844140d50340d98851542c0d4009003800e4100310700007440300c10031030f8042d5080030003081100f07030846a0f40701e16a640d9500340102c07a82d00100510b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 196371771 1250 196370521 196370533
    0x90c1c0e1204030c091808270306060a050405190c02060a060605040b070f1401050106170a0c0519020f07091d07080c1509090a150b0304021c05150106020d030b0a030203 74
    0x3d481e02d06d40c003da042c003421040b41500c402150b00ca1002d103420104528910a0041203141d03140241c035440f070160690160050001c518000c0001200c0400500c10340303002c3d035200c00c00500144a441900c68984034140001c1200c0005401c00958415049404034209072601d800030607150f00034800d407001c48003070500b20742c940812503642c105640e075074440c00c0354043c1065400200443c000e008803406007801e81d9500403c148817420b031010040025000e241e100380384c40342d001c100590040440d66880c45010b00504804403040f803c91030028a420800c2c29405134034000300d900442070b0412151200741c141c070680c01e118261105c0e070b102c01c0072707218242d2107600610001c1c0b19414044030b5040c1449000440b5400c011405e808540e50f040211600f41c51503a84030aa081641000010f6002800302020765606610b0158081241076502103002e4513401a030041ca501005820854045030381c58070f54924040c0d50355014065030301d0b08048210740100c2d013080d1041625041a8200343c04030f035001001404 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 196373021 1250 196371771 196371779
    0x509030c060a03090515100b04030206070602090a0902031302090105030d081902091e03070b0313020607152910020307080306030a0f03080601080703060506030402090c1c0e1204030c 80
    0x109652040b0b00000900d51075030410350200360706020206401e0429400c81c1035600e0300302450f400c108040e800014091900780030a0016031508400e60342c42980c044c2d00141d4408440c0c000411185032075100d034024900001c01c220001001c49690020302c1e00c2682c8005540c2d80f01d10401d80c0304d520000881c0000703440c00001402c1120f21103050999880c0e10b100051a25005101042c10380403008110514599107072201c500d00d0070100441402440d10954050550401b0501041f00000e040d4003e807141c5408101c12041c0090032540303030039031504401c04000320842c0d5101c0e0040f40744016080720381c4114000208c2c200b82040043c407486480f10b0ba01551070502c80355214203003604050324188e014400c024918001400c1c0035040d148050107a155502e080c50104001447c80d003004148108060070000100020749502080c1c80d001907044802c81c500303503252092140a03000c0c41100d4007000e110341e901c031020304007598801040500ca010030764000c038403404d210880314071580c03100808090007414104 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 196374271 1250 196373021 196373029
    0x1a090c010c03030204050301150e01060819090201030f180605010f05010f03090614070c0512040b0a0e04090215070c1e03170f030a020405011e0203270303030103050c0108070509030c 80
    0x142071988281401410f041d100c801090850780010001c00400420201c103000c0b03008545071141c014681e62034003e94034a82004054020f0707001c103c61300801a119030106045a020f5040318655841d030320400c001d09140c5098044400324146070603220b0a15200012500d42661420fa105840040e121000900741c0d00100314001c0c0b020301029101c040c0da03003030a180e030034603407010f114003407d02076951140500a40c2092401c000b2600c10042a4041c104001c00c0b1030381c07109043e00e01804443c1014800c0344444d80105018200301035000390700c249410003501d243c5030024080c2030f40c98080e180d0003a0349501d900169031644411600080c0312010564204000b42500c0f64070070b6024640200242001ca803882c03101c0c0c0e1a00f040e2400f0b4003003500070905010950b0b00086045203070303030080c271079074010080d45801035103a1040880e071082881d6220409203410f04074400b181d4500c03802400f00daa8a680d40e0800c5502c488810441d540045e05182c003142e15144660190307030151600030040c1c9401c022010801c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 196375521 1250 196374271 196374287
    0xb19050312090f04050a390807120c2c0913020102030c0f01061a09100e04020f04090608010507050705280203030703030e0606040c020303241009031a090c01 69
    0x70700d40c48880f5015203146900d980c0100c3d40076031003490010a0700101a8114010b221403680100352460030b0151419140c0c44280300b4070a03d1885041c017a03481d803110303c41215280e100700080e1444030b080c0606d0404d042c0d8851018201300391762007a00390485090244502541c007202d8039090340150b2042c04228132680e00400892410310500440f0324041142e01c806042031402031481e0416559401c0400c150311000c14045035114401804034a44405800001e0500c1c9501d0150020440c0300002072400351201d904503501c40c40030901c4651119920f0100c14094010340c05030400550a110110b8102c81c00755040c1ca50041e846000341400300500c3d400f140c81d004407440c02ca00710171340d504601c50142e281400148140340c065030f00031032101101a18a4034104001d03085c18022498515006031031035020094a401900c032030080c80454038110341c0e000002c035410b82c0c06a4030101d101000615140c0110308041181d00ca5040c00503c5000810325a10749401100c4803040c50f0408001650158131855071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 196376771 1250 196375521 196375537
    0x606021f0e03070210110c0409080d0929010305210708071104050a020d050906090d031d030a020f0c0f150306040e0706020304031103071a0c0a05100b19050312 70
    0x44a04103c02030700000c00d450050001d04002c01c1600f18400e030500d44c1805180180c03c0d080e6410320542080f0f950790011481a011408405940c994440b400c221103840c078452180480e000c52041c080c03020800c2243d500f002c1c8821201403041402c45040d041c14544041c21450340c101486003012100e8688050311b41c401035080710180f0703d400419100340e40314400c043c0180710300382c00141c85010703048600040340d401a2045002c1c4d88401d0411410010000b5000340c2c0035528500421070180d8041c40d8046509820a0041319000104804051036030000d0060403000c1820200e906001400e001e201c0815441d410843e00070410544454085041e1070085401010207030001594202c089140d500b0400786400c01c000681000800b0001e00522468103150b20b1300807000340c49414501004403042180f81c54200c01c01d0751011035446030304034060100602140c0c00074191084c0f03001903d1008003d20b42100300b40d2140d0642e502e0440724484080961301034500190051000f4a801450746146400030b0344 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 196378021 1250 196376771 196376773
    0x108040b0c0c0601030c080c0f0a051507050d05070506010605030f150303070c080d0f05031303110a080409090b16120b061b0303010501080105030604080d1d06070e01030606021f0e 79
    0xc84100d900702c003004214021400703502c1d03035800c241c180030110b42041401c40d000b034411410309803c0032841e43ea010080048410482d079030400c0001a0b0885107150143c05405840c5019044012030b0303154000340104a1913214200b42e405c01da880349401d54440c001641d50580b125103410008149103815030013103c43c0e61004080ba401e0a20550741e0301e04402443d0024410794020341a1240f00c80e41041e08010902ca0b00c0c20a98114a0484503040e0103e81090018040003280c210f4035003070003020f000046040e900102415903c5d501c404064018010b0103c0450344030325210001040c1003d0300c25200803401c1c080e521550541603083e6103002421558092660010301040040c00701c0510285041c1d28610480243d926985000c00241c42c0c6c0c175050744414041d820400420001800300811200e01c41d80c0c00200203180c80b940c0e4102c4101e614422001d03000c3d48150014003076042c9d0896154110b1802c04d036424040c4644841c0e007240c8600300c500206902d81e14220200700381c010a41c02446000f06850 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 196379271 1250 196378021 196378027
    0x62d070908060907180b0312030411120601080c1002060a0b060c100b0f010c050601121104020403030203090427080c01020c01020f0408070b030c22050303030702010c020f07050108040b0c 82
    0x1c03580e08181c2c0541e0303a0a45075202d01c50401000e400c50000d60714051101c0010403400307a03103078046034641080c0400600c078000000f00090400500032042c041c1504050111032600030741503201e9648410a004d800301760700c0340300280e030325074034007809413154003e0b950f4080c10440c0c49402c84217000d804100f042075402482440103250360041000118200664101c000c1500d20112050001403448041950304021642501c2c0d400b040000500e41d044803000c40b01d051816402e41000c4000103002c0740100c0d801400005e00209066002015152102c0215410403204007490904c0884045581003204012940e80d10700d4081074140001d4a45408028005850204860011422039000940c400001c000124041c44074402c200700c20000f92914262080c5541481021400b040c05008103821054200c450054421103010107100c0082074090100e03500d9040080d00a4040d1041c0c03090003006125070031b68034004060001c0d41a0481d101a10b49c540340d503c031074907030441d0300f100104907001c081c1c410 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 196380521 1250 196379271 196379279
    0x1a04020a200703020a0b040f06051303080a0809011d0705130e0d1713150b04020d0c022107020a0b0708070c1214010b090106030216050a1103062d0709 66
    0x1022030441d00c840780201a00c426030031841004040800d5401060303e0410900c0b040c0000c501c4601414151100750500d00c0c1c44200c101400b0700442ca0541004200d9900401c1c0907000c01e40006050f401114000002e0051100344910301d182d10f21540300640031988400d40400990504001c0b9144c40f074071400000c0741d0040f2070007136980307002d0400e055103000440c1d603007201c440911182c502d242c000004080026220341070351109841c50581c00040842c050703807000b14034910b0783c499040318072050301210107000317510100b400a034030790070403601c1000d42d41403029101600c14a06012503004079802040049042e081820150240d044904105c8000b4020444040480c01d030480c044e00625941740f40c41c080002038a0b100b007000401d641484280da050105042596803403903000c0e030641d45546401601c0764907050300041032891240c0094064010020302c7c40c00c0c403d0105038400c18440a6007161100d444090118400b07040e03150410f0442070580840400042075142590340001d100d00e4030721032068507 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 196381771 1250 196380521 196380557
    0xe060f04050c03040204110f2703010e0d09360e0303040804080c011d090c0d021206150a0c080c010b060a05030405010b1905010c0606150203040305101a04020a 70
    0x250b4181d400000044100011854030b030040003400740010f074602e414000000030362a010f00600d5480c0300c200042241502180407040b0b81c02c1d0807948000c00034042c02240d00790981d2948065000640041c0c0030b45004124424146002070074904200e1407a01114060031150041da507180210400250300d4010003e000c050820107107004900520041c0c4e40c9a1030061601d242180b80e5941a0502c688a001c3d0f8500c90360162040c80103820a8801c122269a0000804c40c1445070000c1b11a10030301c0030071100c08030000e10444511440003a03a500f003099215500508050060b9040071000a040307924010000b900e4401a203944c0000768008107118410b680014010303041100180f000070700201c00c000510a090150f80281c800540300700da9911070280c105401d4007441d010313042c1885803820f000001c111459004000624220101e884010312a41d0004d441390300074401070300c09105005613198004076910032050f01e901248000d80c1e888045600780006900131003080c0050104214040d607960751 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 196383021 1250 196381771 196381781
    0x90513080708030703050609131410060f0608180303220f0f11040b0f010e030f01091103060a14060d0809150c010f06050d020108040c0b0706020a090b090102070e060f04 74
    0x202c20038a403600c03031924000060031074000500c41413050f0030300010b0040900c00c40443c200c6080d00456070620100c90243d0862070300f45200260702c1d105192450000300c01703442540b1780c0c050b50301c2e5584074542902c030f02c031101505001451000405410400c045030742c0d10886a2604800800e0000516801d00107488800309110384c03030300070789201c203e5000da502040304210340c1c0f95440d138040310304101c0c1c8606240801c0c2d0644030f40150a040c0f040d03180c2c002c007448da030030440000c0d0080344a00030310441c4180d1900d400340c6c0500d504014000c0c0b1842d00840c801a61030301031803209603254040d0017880c1e50348100b041000450110141c9074452b08001c240b0040e2102c0c802d00510100011405540c0d11000e0b1415003110b041e000b141881d10f2421505011941e070300c4002060442c1c0910b010b960070340300c508285040f8042940a6480341c600012290b040001a4020300350300c240e5a11404841a0b54001200a80c8244e26400340107030450a001d226150251000d907070088405001501080700c0400849e040f92 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 196384271 1250 196383021 196383023
    0x72303062d090c0403080705011a030304120b100e0a1d0f0a021201060e010303030b03070e090a03031a0d05030d11070f121218030e030607090905130807 67
    0x1000010846141003020000440d18000e081c0a044000c56507251074540d50008000c0307110b820345801081500c411002501c020716005902a039440d2920724000d8001c164030001c1030300b43c2c41c0d0304000000618001c02510220780b0350107910035a0201940d03580b0301168004010646148460030086640016100d0251069010040024441c506064590180c50386815500354a80c0500c001c0d000d01c80c0041001c20403a6415a1150400b0000c080001c0c05043c40750030030540c40f00c03140b000101f80340c0d060f040000c429000303070142d46c105511803039080010349048815807426844040d8240001303100e039100403c64980d14061400c0ea00d4400d000030780400c19030b0710a440b640e00101e080b1010011501c1002c0c02d001d10540d00a1a00d815540c03111812014140044d0028041c03500c0e4200042c01100c0421036401c07490350800445813081071002c15180303c00420390028802e084804020308000800a01400d81c50f02d4400030180740c200d19001402c4006c142c6040ca0484041d40d10001e108813029049403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 196385521 1250 196384271 196384337
    0x30417070b07021e03040602030a0503090705040e0d0806030105041e110405071214091e0708070e0a0506040603080f09150c071707050f0d260408070816050907 70
    0x25102c800c0c3d40c84d0007554000d130b40e21607401c01c020400003280c00000b00c81c0001402d0800d55120f039581d20320709007000e9182d8402504242001d0705440c805002040355820074500307841e808590344542050508071001143c004103624130440301d00702c90300c402420344482c00d8424501c2c42c0c425117002c004242612030903901e150104030000514140d14090380107081c0700c0d4000c200c0c85101450b04c16021681c80810850200301003402e030102001705c0ca400c3c08003801400702c4000700c50203150b448660801404003101c1c402001c1d1310700800300b08d85103454018101186d81240580341001401c445110855204c020400d500c10040e8104401c04100000a05400d00000b0080d262461900d4098294151003040d1011a40c100c848140016500c0c0301d00700010440545980d200c5c4c5e012450100c2c0840105000b100424032506684e0020b051004010825141710740180d070310181e41c50801e42e94405031400071869085888406114904101d100281d20140503c2d224003281602c0c0301d034100166404251240c2 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 196386771 1250 196385521 196385533
    0x41707120306230d0b190c0207030204110c0601060e060408010f230c0d02181f0315050105040312020a0b0c07030f0903031d03071814100b030417070b0702 68
    0x40c0c82c0c0702401000c103e603450107400038a0300081000416200341d8000060143c005440824010120020b40242803614000200002000075030081d40e59148d510049100d0383c00d0051030380340294460203480391614008028010303642090420b0790380008028406030021310500002071560404d009481c46070b00e0b09171000980ea40c5d50000554804400b081403010300c50017406010580031504100d8800454a030001625608080c440c40c00049121000c01d80c0415804c14512012540c0840010064002e44081004180e60841054041524450103011a400780410400714071089a02134050281d441660f021154594800d10107110903240f502c409140451aa02090340004c40d01110f4003690921200d10b500d0740d80c00602d81c2c0e003410000314004031404403180e03080e00c0400c000c101400340b04403400c1c481018900100c00408000300710043e20710308100414140d001481c649016a040ba500c2c8500d0741c1d442ea114100f40300454007003022400303070800c0028082500903079114000d1a142d4090a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 196388021 1250 196386771 196386779
    0xc071211010b100305150f09190609050f0f09210702040212010f1d162607030e0c0420070302070b1903141005040b0a12080c160806041707120306 64
    0x40ea00040c00080c5001f051454400e400d00d1756013108881d031140040100081040721413000402074241940040c10b0241068207001900e4415036003a4071905c801e5500031042d68400c0c240a640351510f0641c00d12072018074000320910200700d00241903441c0090030151070320551050310003240100340e102410040f2034260030b02083c98074402492001c03d03010281c102505041c07482e120215851345010b810f0026644540004810194130806008080c25000e16140361200300035020303213510090f5011600a09003542c240c4d03c0e292242c40070510316040440003192100704080032503441240d058080d4401e0450010b040040d07000100b90b403400c0609110708131940c0340406019130f8100203d10060a00c080c0822001e0014111000120b580440e000b00b0030490440101d0b0815013a80c2002c111280d04502e58001d01460303030000c061a48180c4100c4500340070004141d030b40c20000707008507000c0f038200d040800d01103521010200e5606844110f0a45411120350707400002504d04040b00b00440e40f5420204 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 196389271 1250 196388021 196388041
    0x1a0109020702031e07260a061506081509092b03050105031b040c0c150606020c030f030a0f05091c03020d0c050a02060703030b09010e0f0c071211010b100305 69
    0x1602c3c40d03c0030340000c0348010522121a2943c17200d01418400c1104511a45001e06a105c441c4002000d5071b020344450603150704161025014a110308152800e9034840091072131300c90380440d031080f01200c007a08030b000c0070103082080e4520041c0825803203100d400400040e071160700700e03510005560707103001002c00203c103070000d03040d030f44140d020b40d04c0798018140e202c14200944031080d140c09001c440006041d1540034050701c449007416009044840064049422002c49a11020907076034160212a2420b40c00000c150750b4201c1da203001d100750340040c0300c00041e5500908000844000d64113009080c50300d20030200d849410460b40124200c09461642c0c1d0a06805228844d030f05c2900c6c0c40c2c4462400d049440301980d680c007009000340500000166541818402d500100040800a00c000803c0d6590200103603989010342d0350100740602d5001140c600d5007450100e6010399030280000c0c540302110102910310241001682c0100d5407103882000c8250b4480b09a0034040704e540d100001c003810561240 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 196390521 1250 196389271 196389283
    0x31e090306060e0609040f0303180615050303070201050d02070201200d03060e07020d1115160e040b1e0316060f08151f0903050604080715060609121a010902070203 72
    0xa40c103d0321440140036850b03d4000c00e9542c0316070403c201e690000d0180c0b500724000d03c440d1151720404a441800300c42084084d03000034240a030a206030181c40d50301e800406441e4030880780000d001c80c204200041100e50385801070207000303005041003a00c5c41090031400e140042d0a034403804654002120000350181c240c414000502042d8890324807601d0484406036407260350a04e1b1409101d2040c80070040e24000304888803540000008100182c1441050008540350703d11000b804229501c1c0d074031704107007820300c0741d4039101000409805080340da04272a0f080c0d00040c000495094040c020081c8002c2e00410425001800541d42d0103001010b0554014030307107100542841c41c44c40c3c1d583c103092442c0d6100c1d0041e40603484840e10090030644a40001ea4503080582c1c0010f106000301d03420441030015410141c203401e406124161481007008100078200da200e406560301080c01c4001c1030120b002c40c0b8141d01c00051040b03942942842c0115001d4076030342800da000ca800260000f9400303003141403d01c10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 196391771 1250 196390521 196390529
    0x17160b04060c0c080d150b1b0f120d0903110105040503180604050d0303020f0423010306140a14150d050105150703091406070209071d0607080d0207031e09030606 71
    0x8020119020313519221503106500b4140c06240c3c13a085041e0040d9042c001c450020480c030510103955401c0c3d0324140b0051700c0807403203090450045180c0c0c0182c0c00c80205000306840c944140143c60091034948600003004003e02c1901004445130541103804c40c03d1140a01581c040d00065403211942610904c1000303024003144d000320402d0004000e0340d16000b00003003450380c1c9800c025854540e003400c0708065004503401050310040b2002014901c42200b41c1d140151503080e40d0500c9451745440c599403001d240c4161360740c1c0151804804101070340241911900c40c2038014280c04c04034041c990348085035000003d003601103940c2c907001004140b0b81310030710848d4850b07030540042c142161501c02030100c0ea0320b0310801c00034904c00307044404c0079600c040031a9040c3e90300070074001403410103220080107690311442c000445d40c10380010036058502001038921483d44a0b5915141c0003101000c1c0c00690019041181446003858002c3d60201401340c001d82d0b0641c0e0390b942d94031400d01d5420300343c2c2aa01c036640 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 196393021 1250 196391771 196391777
    0x2030a052d030708040b091516020a081201030611030603030703031e061707060804021e130c020609010c0203160f0804030203030301060804110405101512020c07090f06080a17160b04060c 82
    0x1c4000381c1e641c041552700840c083c9955002c0003400c00c081c6d092003200200104800e8001800d00303402840541500d040e280211010403100b03a032100070504070700c010348010368543d00600000700001d1103034002100c2c8105481c00002042d240c0708a0327109544c0c49d03401003107904440d4510130f0070030751040240e007008210928003e5007a0074113401003907070403002c003140b640200110240ba100c0394a60984084502069500802400b02e040200035240c18099a03955820f50801c2c540c4420148000181d0b03110701101b502103c250740b16507072000c4c42c1c400040403c031401807040c8400005a9410303c00f0398000e000a84507150185058034102000740700140c00e080c4211b1810050106017005804c0200594800c42908061607034060000e45402601800d4a0010381c000984566400b0000c200c4100f1104000d000b4040c44820a011070140e401a004084040e8880020034020642c0350150b1460f80c1c5602c110a4906403040d10b503100d000380807410607038114003030009200070040648909016609545 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 196394271 1250 196393021 196393033
    0x303151807090506030414030a05070b13120e01020f030d02070203072306030702010e0d02011b0503040b070c03090f090504030e0301050f0601080a15080a060c02030a052d030708040b09 81
    0x501c0140101145025003401494044005410414881c00340e41002c1c0241d41100d8981c000c900d00149a580100002c07100d0800840200b1240d9420b5016602d4550b4401030350056460280350440340801d4120300f4504501c255101420301141c1400103182c581a01c00000d07a542c05180141072134501c20b80e0004400c40a00284640143c00403584030b00490310450302540e813921748103000c070b01403c88041c41890b03c2c003416000c040c1e29501503110036075640c6920503082e400803100c40203491600040b41c1c082c001d00c26600000e08094490b0080b00b03092842420f02001058450404d4042d810541e0440e0200c907035030364140018160030015600c1e24004c1140280028030f0301410703000e0a401d0141c42103041c80101c0303010888042060b080030304c1001da0845008421540e48036625592010031000780c0c0c89614000914641c64808000c5030490b42541e140c007850321002d038410443d107002d1448500b40b003001e102181000d40c8107410056000340c84940d41c6200038100341c00d20030283c05c0042d0841915500c01 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 196395521 1250 196394271 196394281
    0x70611060717042d0209010911191e1205100303020307020409020604051201021c02070b07080a0f0606030207020411090109030618080304030c0302070e070c080a030e03031518 77
    0x70901a40c00d040703904195496240c500d8280700d81d2440f0f00c1c41038010035030319640000d003000c2804c41041e80d60080300c490040e80d036a590041c4c1142d1980d030651030082e20410040c01042103003248001e0520141c98694001124002c41d00d604010007440710002400701220300e0000003141c0580b40d0070294621b070300281d507455590043c0d036911031588024007807620360041c00b040d5900e603c1500d000300006085d0120303040003110220b0007503104410482c03089094180c0c0c0d51020515200381d44400303501010400341b9842d84401a00c0141004140f80426038482540b44515003890040100400c41500c003d49c440c0000c1c410403050380c2d510241d08150000910280446a07804a0800122500243d000803c180c00c004007000749041c001c2e000d07100c08000014802090780c001c910391601c0340607500f03540e523440e00d401808240c004241c4030f40b000920190b0401d800b16240900610b030b00009401e0000350074000710001410b40d0030803203400d4900c40d00050404e100b410003000140640034403040e41c01c40e038940 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 196396771 1250 196395521 196395527
    0x1401020c090414070f0b04030203070e0f0402060c011b0305040506071d010507030201140708061201050103210e09010311120c090412120906050a0606020d020d050c0109020a080706110607 82
    0xa0028100c2001c1c40c2d00000b24403c01d1000c800074104900404003915110000d951180c1d1180c44124020700c54800002404014080c6031800b0760407602c604802920340c0e408100e5203800449c1401025560381d224810481c4d8444014040c1010980300412503203000d080040c18440024954800d1080302c0480282580401d417407180b07241401d003051038070750300c140c201240140311030a410200350907040140441d454214400b140305074011103001d5910945581140c1c2611801c0c0720042215981c1d0703c941c0050001040003410340111031500744503e030342602c000b4016140a902c00d440e150111034000c2218102064501c640d104844028290b10744001d010800d59400104054040c00c81d9400c0300010610440900d82e4840c0c2225042c40443c480313040c404000c2c00b003520160606840c14100090640c0003045800181a02d90054603c1c08072410341914590f000c11051600c030b5503500004c200580d035030f0303103460013034a00f000c001e203e03042c00c00e00003074407215000006500b2039102100700882554 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 196398021 1250 196396771 196396789
    0x10b09010c0308070203040e0a05010807050102070b090d02062a010e030403020a030b0702030f0406030b1e0d0201030b030c04090809040c090e180325030e01090f0b0711060a08011401020c 82
    0xb9040c54200c1240c1d40340c6200301c1c1903001c1e50304030180081060050200b1914035803c501c0c16511800d042d01c031034503660001642e07692024410701e143c44030140100590752a146c5800c09038036001610040c80c102552405002c101a962600c01c681c0f60850100350b00340500b40b00744040f4604403002186441d0075900052004e440f5031000034110150a000140c54510a00542d403e8505004815880e10b44491020707003d080d08107041c500400c07801e1300326010b50f10080740485001070003424086880302035400440160040c210000e4251203940c09050710b940303e0344101403442d4007504180d519450985c040000352286140c505081240c9624288241c01c0c0001c2c2c40d5030400b896081e41350720415409030090450042821711000c0c3d0183c0381d88500c0003001c0343e0101c2004c40c442c0c0e0311608101e051000550f41340b602030251b869004a1564140b00132a00c171700003072491900450b0102d000da20a0400142583d0103251f103940058040401081146c40c60f103480d8141200c02d0020300708244004000c42c4a1390 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 196399271 1250 196398021 196398023
    0x1d070b0f04050d05010e0109030903050c0303030106080c03060301060302130f060f050307150903120903061410060c02010c080a1808010509060a0207061d0d02100209030d030209191d010b09010c 85
    0x1101e6510030004c03c482540020141e41c03041000b4070002c00d8604001c0c1a54019100c192040e0050701c00030782c0035107004800c4074166003072511032180a4442542c450040e07003006016581665031014044050ba450440e1002150701005c004150842008001d8061b941c103640702d255007810f04031080c0141c2d54041040d00030b0705caa9820761000b49084040c1290b80800b07a030700c0509a0344102d1100d110303a0f503002c05150140c074080c1c2010b22110352803200c3d031407a004c02141c4000c44000c083c0c5007070100c1380c402e40d4600a400c0c014588451895040d4440003119403140c05080702041542520008c550410320318100241443c6000f0899031504500f8261642c200070250301c5041e07800105001081901e03481403125411484103084420385c0c1410030355513130440c1b1010202610402c0803042080301c140c000c0f0f40703101c50061b0140c40900c540c000c2c164065005021555405000c228900d02e510b003da01a420041100a024002100c0d41d09045104c584040c0c11041c2501d00401a00c000f590f08a000c1060306 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 196400521 1250 196399271 196399279
    0xc040605150306060d0c02030403110105070b010308160b0a0207110114070605060a0e0a0e010b0409030e04111605101121040c0504020a0206040507050307060903060c0905041d070b0f0405 82
    0xe640701c3c0c000440307038031601050454180c07400303248000a650000c06002541d102e4403550405d48003060042d601c9001d00d40c2c0c0180701310b004c0001440020300c007030007400302190780c40d04503034880c8216038400c800400c0c02ca810940b1680d000c1058010312030404035600d000b001c01c0c20201e5054a801610030700a218070000580403a466001003062a01d4020141000b400001c0400300a0704010b22143c02030a844291003119600300022501180b401d807140840059150b111059005030403400e110103400e069024407100304041c00051080002268062515842440545032450481079000d086071502242444c2901d400c1c41300490380c5c40868415080d4265110414506a13998984450280700c1a002660403500104518088a400048642c000c0e4414019a032520703403610103056903800c080c41071000140f40000d041000c629540c0c031071701520130289000c4500d13945070b402050075a50304080b10141d16041c203258050724201070000f0806408801405854903000e1040c0850324040d50103140c3c45 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 196401771 1250 196400521 196400527
    0x60a0509031b011a0306070507062406050a080702120a0309020a0503030d020430022106161205010b0406390b07140318030705120306030c04060515 65
    0x248403040080c1d80650750100ba00d00741032070520480c0d9000c0c2101c01d080380e000c41c41e04000400c0d14500405d40382d03c20031440d80c03403e00300005601e17504054014450560000006031401c1c00141d4107a2a109014165649965542e0b4040102c02091640002c0450045400418402c00bd0300321400443e40c0401c09442c000c2040301007400092118a440c2d440964540300c00120b04191074000d40141003228160690001d072040340304140c01c521111040d018101c400d00700e07150380061031318000324000300344c14a440000044140207603500d40740064880034402180c5031820440c180c0e001c0001c0d04c00741881001031000e0351416114110034000c6001c0d403030606c0380c0190102428021280c041030a08501c2c5140c04031040f460f101852441070007281542d1004480340018602d81c0101c1d01a1005441c105000d803440d42c03a0b1044102c405204406030b201400100325101c0420310811000241c000b030680c0c0d40b41d690502500309032900b4100d03507105000e2810182c04000e0366540c03c0f9031000c00300701248403030340d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 196402877 1106 196401771 196401781
    0x1030b030c0907112107022e050307020f010513030e030304030f23010c08070905120a110a03081306020d0302030402030c24040801090c090608060a05 66
    0x600815040c0104040307a10840401c0c4490101000b603c1d042d80307040300080c5c00d861341e20080304d105c030300041074050540c60003c82c1401c0120090605c1c02601c620681c10b41603500100c0032240a2040110000d4011402130100702c045841d090020005460b040c0c90407005007415580580000d18651481c1402e0b080000c12201070f00c1c3c004003040d0207004107603036400c6804048141008207040744504000c011b10b09003e00b4259441d55142d40300c0074a481c3d800201010101c0c0e03c01441b403280842c0700480c0c1c500120f440207060341c2000000602c0d601c00300120364220025030004161103c009500c5043c503000c000003000f07858903942680c1000e41048401c82c286c0c003007540c0207985500701a00046481c07070406074903400444c01c01d000b00810046c07d9544842a041540018602c0e51180c8403007041101c045850b50241c20b01e12000c20615080180070b40d500c180040845508070f5036074010035 = true := by decide +kernel

theorem cover : BRFrame.Cov 196223021 196402877 := by
  have h0 := BRFrame.cov_init 196223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 196223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 196223021 ≤ n) (h2 : n < 196402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
