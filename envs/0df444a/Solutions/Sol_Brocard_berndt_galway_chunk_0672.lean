-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0672
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:03:24.421657+00:00
-- url     : https://prove2.me/submissions/fec03161-b82b-452a-893e-9c8d65da8c85

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 120683453 ≤ n < 120863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 120684703 1250 120683453 120683473
    0x905060d060911060a030b0f090103200a0f09050f070e010212071b080304032006031f080d0509090610050f0f0708071415040b060d0c0b030114010210061a03090a050a05 74
    0xc01e002341050704600510b154030051002400117004088001800003851a142100303400080030092190000c030201c115461000421204903001075004240b01c840b030312034550b83c20400301d03448011800024010381c018181000b40c94132000003410b420f401205901c480074128240c3c1d450181c0c1960140b682503000003004c00a00c014000c01c01c034540e16092042c0450b0b200c01e0002201400b010308030340080d44281c1100c0843c1005448144010000f10050f01c1d100c0103041d00c098038039005040540e00803c02800091403d01d811020300814000503124a800d0000e00c0f103000d640c40e000f0400e00c005611040100390003107007828014004080c841c04e0940c007250410802282071100407900b1100f91080c501c284000111003410a6901050a0310b456010701c1c7d2a0034444003041456100010340d40d000000844c010501e16280c1c030100070207800703c0718005c1d80c4c0224181101c04910270342c42e49400c40b00d045c061940e48030000f19000083c08007140c0102c050b903250b840c24254070841c01c5800c0c3e40502204 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 120685953 1250 120684703 120684709
    0x110a050705060705130b0c0c030d020706170118020a1407150606050702030a03112a01020c0604080c0415180b0406170a0b04050a0c0612060905060d060911060a030b 72
    0x102d0b900901515049041c04044240360711070908078000c503401118003150002c0031100030003109405540003801c4400e10341400101075150b5046001d900b00040740070a0100000325060f06842c1207505000c0c103030b901c030901095548000d4100806510030001c090b02540b0010703c01c04040c01c80d141c01141807400c0940c41e9580c0720110745c4654040000d0100a00210015a82c0400c00e40d09140cac05081103082211915466400c0c61b0002d00c8026146006021020250f0b42403030410040100c00e800302c071088280c003001c0182c01c1c0200d01c070f140c065074410528a00ba0342040d1308101c0c0d00861200240083c00d86960000c2000c241105662021640d502c82810103407625000d0b00e0b0003810004600a00c9186085800303444450b100405030064005401007800c00004002108429800500000816885000044c41402820300210700b0604100300030a94034114441c00b4020070009001c802c8042c2d584d85d03850301070640100c0643d041250081403000a486260091900c0c2d52280d8000407520712078020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 120687203 1250 120685953 120685963
    0x90606180308070209090c12010b0301050901020702090a2a031505040e030f03150a23060909070806040e06090a02040f062d090606030504050c1002060105010c06110a050705 76
    0x854034142155031042002c14042c104560302d180e010384002c540e07661a20880343c90602e440c00150782006031802c10000130170065204c40b0310f9030800c038001c0c8226201d80a500e402c3c3d0184000203540003244201148200c10250700203003070014450561030302550401c040300c4415003d0448000842c1c1c950422814948500134113030044d1100301c034100114045508081e81e01d02800c62020840c6400201044402d4101c0c41c0c03841c0282c4006190030316490711910b079850010720700e484600400c503c590207440c0b40d140030000d450354a18080c00c0c41e10282d0b0380c20411070742c2600160640340c10550791890441044814041e03280304901d0040248448041481030104958100307842c002e041d4640394050265140700c880103080030440d20004000071000320203041c02c0e54040d50000594624105000805940641205100e036009600b0784844000160610801d02c001d203040b140160020b9005111540c0901d890f801070600940d000540440350303001c0c110480c1c1c80400342c00c001c6032020a20200700300c0708101d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 120688453 1250 120687203 120687227
    0xd0f060f050405152a040b04080d09090905030a0c0201110d0201050714030c09010e130501080d0305010b07050703121b08030103050607022a010302121311010302040302063001090606 80
    0x21041051a150702035085d941035080040007a41e0505031004d441601e2801a40d002d402d010400543c0c80740c1c0e4090440e903440300b40b1105004600304820000750314103c0d03c600c513078194010014520b041e0f070310070007214605400307a012030601114094520303204604114404084140303800010b41030034148001b4100305008505180c0c03040d420010050302a0701c0c070003500c2a500d000c1c00c01c03240c100300880c0010b210000099000c0e51543c9084000a814840005c01003801d11480e01c0070400341c0d13250340d102d180c01d01c00e1101c064a240d005802c108001001c0c102c0440c174400307071494141e068803107080c06054008004902600d40c02400700050082c010107100007034000c090341c001001076080401900c58001e60700b90541c0c0384190440d9506c05a6406901114050441c1000948071031500b096822500c00d1008401c1d120307000a00d0134800554004d20031501541e40052004d4106940003400c0070307801001d0081c401010503203d500d40c15104000110303030701134015820042811824188000c04240d0010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 120689703 1250 120688453 120688483
    0x12010305120c0a060b03030909071205061804030c0602040b0c1b010302190e01091503051b090d0602160506070f030c08060a03020d0c0503030a030b09060306150d0f060f050405 77
    0x1101c400642c0000c1c000500f190b100801090400070040002e0840c01140c030a6038000219404000c0c8043d81b02e80c1440c00510045400c011917254101407009049440d0000968815201c1c0403c0c0428000c4250000b114452207000d89030584407a042c1809410940c4c04a100782e1240640c5054500c000880030302400080c40e00314140303800805228146c4039402a0201030000360010050103074031403074820303025141c010344541802200020080003080704984044181d2124189180c1540208044a030002c0b002031100364003a10946030311000f544500c3d80d0418400c23880d01000d0019405200840c40765040d501c40c00d59500c912140035080e0f60040e00c650080110110401c803403941c40c800c0402c2a00d40640d8914801840c0c1c1c549800e040446410055041c400441c0102ca01949508040000d14040e5800c070586d407a82000e059880001780c401c0744c15030f03008030f18049503814a0340e03c1e040854001d40c4401c001d2011a2503c20132110340c000700c21252516003003003000f400f01c1004140c139010244 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 120690953 1250 120689703 120689707
    0x3040e0609060d12020a060219120c0e100c0c03030513082b030b09011503200306041107060501060512070507030206070f020a0b010b03011a0f04030816081201030512 73
    0x6000003d00c4030411100060001600e031020032107151017000f004144580c8241d00319662903c406081d54420004043c40c070000d16005040c0f190b0742d0140c0540d41d1070340116110b8040d40c10342d0801f00144129004901810043d014072340b800030444101d0800300940c00fa0702d41c590749405082c007070010082143c00081c1154008005c0d000b1556a11401c0fa000311508500110700b503800300d1007140500f0854088a074445210800402c91501e21010020140301340d0700c1c20840000c084100c0411242940f0b00f81c40c0881082c0b00089040c1019040b01c00841000d003212490800d49070340740700c11280300703800403400100042502d000042e411081c05401046c142491410710100c0e030780007561000002c11070320400100009521105008000e1203115651240b95140a507840e54a02120743d0024800c0c00d2016100810322050300ca201000c07201031003a07d0112501d05030842d254040964445590003020b410620808400306071031801038184244400420b0505500d1414045c0c581110400b0585160b202 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 120692203 1250 120690953 120690961
    0x40b0108061320061c0c03230402190f080d0207090204030f060b1306080105040b0601030b06030a05040503040906080d030c0e061b03070b072607050409021303080a0203040e0609 78
    0x201035201022060380f01012601440350001180043c000c0c0120032400701081003d50340210313059000100140c0f02958100300c409501d510b00440402808900c00c1c0002c4071601040150801c04c1824280c20f44081550b0341003036646028032003101c9207a105c008541c21400000460346d43c1401188014859507105604241c00d42e1214130950b8001e1800408050380c5409a410710745441c80405102c0f5030250040211903034901499002c0e1004481c00c403054400100003812560092145030081e01c40a0320b02410342e0b482076103400003040040c0040d900c80c44284030015152038a8019240600841c8001d000e40d011401000307800d075240f0071f201000384405079150208a454100a9844040c820460070220100b511281c504620030000041c0c11741101c13104120481e50001c2c0400c40d00e01640da112120711201c4440d140c410030040c1e0701040090030822080162400790307005000340e00c540d2000802810760741d42c2c416403244d1020740c030071300941c00100d01003102d0800d031480b09034042006e80e070344102460 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 120693453 1250 120692203 120692213
    0x6270907050a0c0303090804080714090f060910050d080a17060f060703090308043201021002070302010b130f0b01020309030703020d0c0e040b01090f020702010914030f06040b01080613 81
    0x540c1c04001c003084480c22120013494401c2d005040d00315041002c5076503d5440340a825190400c03401244550020f41d04000c0075800c00a01c0c90340324600c480300080c090340b252020401082405003281071007030000580416182e60360100e2043c02441a0415941c0703921205000d060384150f041c031039009041080802c60a6100c114214084082c1118055a1440c092034107070360f000e4060b04081d24441c00450b000c0359038801030040ca00b905200d03000700127086882d025510920b542c0c4194003401608080044001d29080da00940361041c8a800003145044940c004110510350103003000070040e440344101a80c43c1d000d8450502000c1086c4041d41c54110b050001c03e90301d60040c800240100c2c0740d2210002030000c0301c00d01d80041e085040741c001d030508007801c000c0541070027070040c00c2020741303004002000c1c0403152084815840c2d040e1a10958985400904040004008515501802403481152100006004051040e445802038628550610150514140c0010a000980305001642d400132076 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 120694703 1250 120693453 120693457
    0x6010e0f090f07020f0f030904180c03111206090606090106090302060318070f03080903060703141306060503030d0603060c021f0f09082809120803060402090627090705 74
    0x14290b1210002c0366150404102c3c43d003600301d1560720b0140500c903804410010080003e0442101c1218180714022508a41c8842c07100b401c40c004085d9951050200001550040110000c0314010415208402c01d01c90190400500312441025500000100025460008140341c050030356850003800907401c56003c58440d10024004000e0003003000c0e007016620404206550292030401c5000f0100345c7d0b00e1808040941011840c81d10034040c810004104c07a1103445002e07440c08100b0076096440e00c5001c032100041e1040d0006949a580303421000c02c050318204010903040c9601c0c00d0001e0300300e00d5424854102d03848206d0700011500507002040c000000e010021540084000300012081e55100c0c0000045c400c02c180102129408984d000000c45071809041140305050f0301314000070340018007140d010046001d40c03403540502030307071a801040d848070185510580c0508010314240b0400e0000b1019000400100002c00080b91880c014000c8060799034202e0708141c85a0409007004038000d0007034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 120695953 1250 120694703 120694711
    0x1008030309030a0e04150609030c14010c020105161e0b060f01051c0b1507060c2102090303040f080a1208040b0604090203030d0603080408120c030304020906120304080606010e0f09 79
    0xca0310418009a0b41c0d11a13001a906d004000307410301010307546403400340030903409110070390f0010050f00001841c08015288812080d00503543d100c080c54842d801503410f900481594050508041d5107800010440558a011030559040101c4801800e150444040600400b181e0090314031a8451251380d0b001030603203501d05050400619011100c48411006100603180700b6484400b40c0c08070515410300500528005000c1e1f1000d10250801250a94008010881d080707034400281a800c0b80101456014080500004056034078003940d8800d04010071b4407d0700080100e800200e000e8081040c1c0d840003a00100301410410954a4241c9808900c0040105040d020f50b03103840c58002190b40030310403505800c00141c030401601c1d0312420001002c2c4c10602481c040d03441042c2c40200c0e80c0740030704155403980a940005510710364660342402401c402c050075180e08640c48140820b90503e040c2b029001526031040107080341c0c5441400100154a51145580203280703294103e582034403058045584 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 120697203 1250 120695953 120695957
    0x31006020c060f03091203040b07030f0506030a1202010e06091b1017070519090f081603080a0306081c0305010506090607030c050c060703030605032401090903021f02031008030309030a 81
    0x1240c1d1240b154501b40181206c00c0f00702003200004100410500302011806450341f6901003210b41d030380341909400c403001602d8581e41079100c01100340000300506603045d2400258030012900c13120000c4020324045064070038042e01d4011400c1940d41c0c03131080010304024032044509040f6100b00080150112500b41d40003409186818002070343c0d41c0c001d42c111005514002e55142240a980100900103103050058002410402400141400c4000340c400010b10b01c01c581c9030491482c50390f400343e565122100c100c0c107150319040001030741a400d20401d40d082180215601c48100140c00007005c8480580041e032103200c1c1841811603507284c500c00c2c0ca04031585801c20051040c0c55040c024078002c80d0100683d80f003003002400d2070426074550410000c480054049482c0320000d010484071540002c0d004c040340040c444010069402c280d0802c00109000e8019030319010414080854aa10480035185006400109001e00c05510004c5840284602c8015508504280540301e44902c181004201 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 120698453 1250 120697203 120697207
    0x5030d090f090f15091409071406070204110403030809010c091202060a020c1504090501080a03050a1b05030a110f010b0906040902060903010c081f03021c05160b031006020c060f 78
    0xf02e0400c40c0c0e00c5030820a84001d48210601c0d603c1090f940070704000000e5103560305040000c158003c40c00942c1d0801e0307521442402d640c0200304002d00103503400c104001c3ea4010344424001413100b4808000b0b001a6000e66140740c3d0510b0f00c0346055007074410003800e040810424900c03c00003043c1102c40710302c550740c0c1200d0159a8013a9254101e02c8c115480806580c4801c060400136030361b010200080c801c8461162040c003aa03a43c60041540310019034a01034040b400412130032038460b1180003005440400c50141410600c959144c05185030000c5007260003140c0811000f1400213410440303502c6c4103592070020b201c046042400314542d00300141c180c50059460b1a9000d08559036802503500e07800c0d02a008100221102000511203003059441c5110445845140c405010000c003529040e81d80103001c045400c107a190100b804104150001c0d6070a0103034405141c0340899042c1d402005242c0303c03510b10f4890801120300c001260303443e800501554040703103418085446200603284000c0c461280c0507 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 120699703 1250 120698453 120698471
    0x10e2505070201050d020c120d06050607080906030c28031a130b010507060f0606140f0403020105030c0f0a020106060206090d02060a0b0f22050a050c090405041e0305030105030d090f09 81
    0x407011f030054101c000c8490140506940000502802a0018000004c4140401e56482081c0001440b80381c401815074101049021190300b4003c0041d60401c400080040c6000c034809424002c0030101c0c41c41d45003c42000010000e200e905000f2030f40004a01c01d00c2501c094100e00c00558038454940c02c0c600865110450015541e001710151500c03140c2041050084800d461800c80c020001030051001140e03601c0646552560324109071481e690020504918180c19600159441c0d00002c04000c1030160400544007480505006001c60521036000801c1d194140304d0040c0c02d10340c0040080900341c0c413600110300015400241960814001040000c08030b15410200c2c0f0001107030010507401110000e94443c8404518500b50189601a80100041c1d12120031580135600f080c1c1c1c4a518045051141001c2881c00b50b02c102c0e041407064a15180f080040403a08030007100303c00003500407a1001c00100000e0905000d2100c0c2c840003403403e81c0d425410802102e0050340300e07010f24207030b09907628440 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 120700953 1250 120699703 120699727
    0x5040606021c110a030203031e010501050f0904060902040801050a0c0513091104050604060f090b04060801060f111b01020c0402041a0c101109010e0102060609070521010e250507020105 81
    0x10050f06038500507902102210300700a56a40e0065840194122011140000c20048040c1e60380c140c5005170f4949140c0210715240c1c03d420780087c080c055010b0b0b611a000102001e0900c02040109040300010403245045e92242d0100ca459040140c14444200460858105038822100580741c0004001400c1d100110300c0e180d503400b547e0440340d084840002c0c04142241c00007000c0b44009041c0d624040040d880d0449503d41d40a02d00c500c10118032074030010f011260040740080c030b0000c4070385447d43c0f074034074104002c1c3d18000303444102401081110115400b2568140508510380005079401d518003864241c8644a58140e07010403a00300070003041d90b0080007428400000c0250a8070303014072002015082642045e8401c00740c4034080f468481e03a80e8032950001c5841c40c86850000e040d42a580e071041001d458941c840e40d080000510714481f40b0303281810800f00e0901900c04207008104a01d449103d668200303031306012000c03451648104c00011260700c50200d03480b0313540c2840c100351180d22103820 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 120702203 1250 120700953 120700967
    0x306050603130c0914010302100c03080c09010201090510020910030b030a0204050c120103030e1f0807120905010f061d010f03021306050306130302011109030a020409020d02060d0f0605040606021c 86
    0xf05140c005d080c0140a044041c3c0703000c6540c141c0e8002c0325410007039007621005840750554540010040b80b84840003c0c0c3c00b01c032300b00207080c89410600000c201000303140d44450078915580740746444a6800b05d107101250030451008603001059080800c0001c80e0000020365581d14484028030031a117400002d4404481c41d002d44001480ca0045207505503143d250203041d10018a171618090f1040c81c903034010b03112486804880000706030b295075246da1102001110600540303d17407122900d40300c4143c80f0004209101d201c83d031803902500020958100301501c1030344858448104440c01a6100500c50002080c042c0001c0b04da044484803120081950300c0c501401c0d190780040c0d410b005240800040100401c0e4240e061071095000b000007141700e0a403c205400703002c0c0e10541650040406c000141481e5104986840c0000e213048101030555000400c680d0041c504a40784a0715001d03c0d003000340f014010310001d428201c90600840e41401d2000750b960104c841c50018500c0e2290000c5c0019015070a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 120703453 1250 120702203 120702209
    0x12903070504030b0a050601020c0915040e03191d03030a090e060f040609091101020708190204020d0e0a1b050f042d23090303071116090f05070306050603130c 70
    0x1544c0040c40c21242a03001808112611405070007060241509440d0481683e0720940e08a80d050246104441c1444000c4c01ea0b0104d0303c0716480304000d20310300c00d5000421082034444030384e10790f070381c402d00c400c0754494502510394094000d500501404004641000b1480240c40714030b80c6124441d0748020020b5180b42d405c0c1364a41d0041d140440105500c9003903000f989001d40188035a12408141500482e43c8900e00c3c030411810780c1184600304211003006008000e82400100003501b4044480404801ca541080510085a005200480801148103403c00703035840c42c0f90011280920b800c01040c2e4582e409030301e081c030032a914007550b460314424049550210001a49660f01015003101d150010510b48041c0001500300400940d0420303002214580f2401c2c0e61005541962144601616105802c038803040c06400740360031481c0701401c003030480802000c0914011031a202001104011901e018101b00101410007800703001c030761103400482c1e41044a4044042100c225800c01c0241104190 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 120704703 1250 120703453 120703463
    0x32709020f0d0b120619020705030a0906080f0c0307050306130603080a0e04090c051012180c14090613020403050303042a080c010c02010306170a0b01290307050403 72
    0x8181d941011004038068219010700300800c00c610b001c12010041041c12a0314021120b03400403000560140ba40411103482505003040941070805550ba92421604a118082d0000340030180c10003001d41d000200d00e8004400340c0704038180f42001c0850955a11000740704d10280500040450000d40b200e401203850f129425004010704e940b41d00d4520040d9101c13000c81800074036070300b1054105190a209030500d240d0720005e0204401d10b00303802c2c8860314a8141a800901200c1c0f01a175036844104d002d61810f03c3d10700301e00381e07141d9119440d00b40b090061540089100a040700400d5005807074400015810100450700c0720410840001412701a10990708001d0841c00040184410010f07400b50304962100c00f5022603608140150000c030340c10030385101d01d02c80d03a0310080c0d80c0c14003540221840c0d1010360042c9404182651110708000c0461900b9003590030a5018203880b806002081e45494050b01284d020040b034004021401c0601600d110403030200c558000010400320f5000d4021140155402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 120705953 1250 120704703 120704707
    0xc04051003050105040c0306080a02090a060506040905040201020d3e030a031a03060708070c1104060618140d0602031503060c0a0206010b0405181e16020c03070303270902 75
    0x106400a01401003131140501407410104a544128044d00410040e95500b01c0103042080d120b8080115410700034000003019581c0e0040402c150325944c000304050f0050101c0840d032824540b0009103446000c100c840c04005100f94607018030b081c1c80c00c0030013807503214441207440d414849291041104c88400451a141302c006109101d0b2a0940c00c060300c2c1d280869000e1004d0101d034414035484400403101940080c65685c0080c500d01d002d01d000344100c50140040c7c8002e5810031001c90b08448664000e003022980c5d0021040070340080c0385184024050740740d501e0380d0401d40305000c06d00e00060118004c210340e03004030020f410440e00d18485004650014101e41281c245452240300c0c5500520900c80103006100020030f50f4902c1000f04c07000c6038006050121000340454020380e0000e4082d10000100c8010b403020b030000c1102e0242c160144801c2240c4143c400e800150183c645840803a20b18043d410001d410801300703411008100c003962009450541c25500f005c1074a2480d0300a8202104403440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 120707203 1250 120705953 120705979
    0x201050c1c030e070803030f0f1b160212010c0906030c0c02030604110111010b010207090f1b08150307081005040201020a050d0201021c1a061602040908030717040305120c0405 77
    0x8550080b101e0f407089442501d4505846880b100e8803172104a802c100e62980d43c034085901010900c90455108000400c611020100719541e004154001510304512010302400141586000e00c0010031442c07141000308165294548061701c090f00c64440c2100740750f038038000042902c7c01400d100c03ca1070fa005040d103109248c51324060050740c0001c02428000303842202c01015165051040b0058803105800a010701da24010000d80070b030580c0400000110748414a82000652007409184c03001c5964aa4090740d191a4007c071400c0c00c05142d185d442640040402c00541e031010420700107407522428041400d40d40c80c00140d00c0c205102c50010814814015220200d0742c0c10340c060107040070307150030504407041c1c9090b00c0307000c4e90300380c601c48a0a40c002d513071450341030b242c150010000101074551001482080da00010100da0200030196107403c000420001917540c086805460740a403091481c0980c24240c80c01001c0f800380301000c03003503003812801080c0c060707005000f9103004040c01000d90b024404 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 120708453 1250 120707203 120707207
    0x612020d1113020f0a080903030405070b03071106090a03030b040b090105060c0f0a030206060406060309050c0108150415150306030c090b131e1d032a011b0206060f0d0201050c1c 78
    0x301545c91900001c0c03e170300204484403c0031084074000d41c0c1181c0100769070f07410054540903582c8040c1111061154100001c0d081c01d90611a0328031500c00180070b030450300000c0c213000e07058483e0f080480d88030758945040c1b4515592114142c0d415200155140d5403582e8814003100d2030b02d070004801c1c80d184d10501609108143c4c0c000f4200e445520241c2d82445a15a01d800c00c0c0c00b950380c26140102550403030049414254850b00707802e03520403d1290f130698268032803008201118950500f14000d82d0740403605111160540035100b50f401c2040c98100980e901d9615600001c028030700a2065030b60315081c0405555651102d80d10a1030704d4032200308030440e040e0710741d480e9940705030303001190b16030401d14800c1082250b0340b01320000301340400c09145000c0c150300c0c0060f81c081d800110808486c00c5003011146005007445001104118100080f840d910401c1c0d020f480e002000746864803800d424080c0380220703110700f140c1d00101542802e041d030b00c503802031241e1401e10003036114007280d2141d422031000e0055 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 120709703 1250 120708453 120708457
    0x705040905060414070b030a0e0a0209010b0403050114010b09060f04031e02040e070e0a0c020106080303070203040305060f0417071a0f06100c0203070e040206071b06030612020d1113020f 82
    0x1910440d13900c0c00e41941c0c24011600d41e480e511504140a1061000800321030b010b801074011440c181c4269042c0b4035076903001900c820340a8201541c1c4600c00b143c10f10030481c0901c0f4000c0a42075200120a0a600d0404107000521800500710b00036800450305407002c0b20b0b010300341c130040c66200b0100b03100c000525826510f07003040c110050748503c0c20201103603e610002700700c00c4150303190003035640003d6640003001c0000e07248004d20801159030b107410005a01000340003843c001da24035400b96540d00d180d4140f0b14900b03c0090113081e2010500d0050000180400c0f10318240001504c0d00c2517203d120750305201d003d080c4128008111030a1600801c9600001e000c401c0d0303c500011140c9010404440c481214404141035000b50141d00c00101404808034103100c1c0e0354018402408946081416500c040d005a180410311041c07080c8001c0c01c1c0040d5406003d014082c1400080d041020b00c410340005030a02c0140c1d41c0544140545c4070171416a0701e524400f8101809581c2c0c00790f660f1032801001415a03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 120710953 1250 120709703 120709711
    0x312070e0112050405071a0c1b0a08120d1d0a03030e010f11030105090402061c02040303020c010e060a08070e220b01090f15120504030201090c05041517070504090506 73
    0x90385002d0300d551a41070034498030b03010300d4101000f0007201e82004968040343c01e00c94440b220210341171041203090402003002409449414030003404110800040c0202841140c0018655411142c1d082c12064558000d4500d4408101d0001c10300d01c42da05442c104040c02c02e002c1d0589805402541c1301490340640203881c0d585007070002003125000040035002210885c07d80340d903441808100400c10741c0752403501c958001d0300042c0741c10701d0b040b038004c9054030a4500c10080501940c02080800600d5014804948014800e0030540260b40c0c076040010b00c0341c46500456814004582c000c512030902c12a8035108109010b00303007840c4800241110780c0310601e410320103110f55007890044407255109445220071513003030b0704004000908101007028983c8001507000104404a80c001d1007040d43c1d8040c06000d00d0090b000043c0d148400d0a10015055007500998051800d214019000000021003a03003198102520416852480491182800501d6100c0346d809814940c1075814003001007819805 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 120712203 1250 120710953 120710957
    0x114071b03050c0a0807080a032003040617011a091003060803030a150909020303041206200a1b020603150f031c081621020d060b220f03030c02030312070e01 69
    0x6010398840c041c0d5521b0b1064080c60701d0603009040114006030003035122041005918288080b00e01d003460690b0310b1900a07a01c0b0307000041d154203036402039000f030740f01c101d000d41941544003410040090b030001861084041c50303801006002042e5404074440d80c0408041d21003172080d69035a08140460380040c000b400d454603030281c0301074000600420a88564144242d000c0d000d1401c042c035106070f01040b100c1448003580c1c1551610b900b80001e6481c0020355030001e03101a450341d01d9080c030090040070201d5203a81d030071072155041c1819000d41d0b00e00007a03d80c000d003580d118144070040e400100b00c00d0b081c000c4020fa0144680130f0303003000030414056000e41701666540c40c0c13040c980d2590034041c03011008081c500080f52016031030200220003c14060b200822060340545004402d60042c1d045500302d6000041949000c90f109100d00d01a460340c0c100c0480c0d41e8075082a81e420440b0031000d503616844020180842168620115103003442030b030302824072030400407181d0f2901040c09840700c00340c036810303c0c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 120713453 1250 120712203 120712219
    0x2508240d02151b150a051807081c0305070801030b060d050a080306012a0b10120b060102070914010905091204080f0705010c0308070f020c0630060114071b03050c 71
    0x403d20b00004900302883d40c181034601c1c10fa00c0d01030444008020103080e8981a41070740c051541d61703150803c40400101402402070440034444102d0340d0200302a40c181c3c0c000c150401c170070f1116990340503103c5c50550340c02c48007141c03240e101c2c80700050b031a54641d140104030b4024941921305000507640030314490f1100381c8459400039091501c00c9036440b50400e855a0300d50100c402ca401081d084020103921a0311540303840c092544542082080c2c3d00180d100302c404600d04000c00219503414800c02004241e07a10080c0110045007241203402c0b60140a41c61010fa5200001900e00a040109107501042407069956403512001c1840d107603095034901c44a20311405100041c15486403444401c1c1d107825903589800d9458001c070485060894052800c11440b410341080401d69a0321f000f45104012038108203000740b40d4003081c50110410100800c101c00c00602001001d9070050034072a1200d101d4100c550f030720034a03890241702c1540c1e000c0000c0034060700c0910100c00c000c0005100c07402402d040315000703 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 120714703 1250 120713453 120713497
    0x2090a0e0420010507060e15090604061a060d0209040f020309071410050d09030212131404021615020c01060608060301180c17070e2508240d0215 64
    0x5010b00c24003803481c000f07141004040c000c20385580c460600203843c1415904c0700c503030403da100c01640c01035514643d1500300100b07001c2001034501c110040424a10340c040c8001007544c00245150140c01010386040e07800017000c09990756207034010356466800540464881c00c0c40d401c140d80d01d4901d4050b1401d00e101c000c0c00d44215240400000d203c010301c696075a807a02c002d01501070040d0050f000110150300c80e040f00e03c1d40100301d280c0581000340340680408025880c200103485824517030503d05005a1040151107440c01c030101c51074000b540c01440d1207082000506841c03009105a95640c0020b519002c0c0c0816400d07441610396025000840007840310b480f003403982c0c0c040c44001c803400506502c03001c0b20412000200d450b072150300500900a848000f66140c607550020751089901c54400480c94102c0c084101031400840e4140c00907242100c500d2512600e8400f81410406c0d540c03c00440a6400d000c16a40310000c8480c400d60191000ea940c5002c914400b05980200c8501c4843d607070403650710 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 120715953 1250 120714703 120714743
    0x10507030e060a091e020d0b0705190801030f032703060b0901060302130e0604150306050405121e0d0209190e1605091203040509100e0f0f0402120102090a0e04 70
    0x30360740e04d580010080c00c03042000701c880d41800044044c126000340600b605c010200e00d00240c290303c1030610b42c4845550b44e031034001c0d10b8503088400e0889800e2294420050000c01c00207084100c0c1d5503414106088170b0194201943d071004602200c001d891010100044100503d5802460b0641002e807240070300ca0341c03540b60a5050740502050740301200d40c8040c0401440c4445e0017441d4104a01410000340103000c03c80341450804a60015603165440340180020480100b0001d82180bd84070036075818030700c6e2020021211190b520000c1c4980c040865a5100c69503103074104d94081500030700c003512501549101c160b07041c00c0c910401882180c41400560a0707841e0070380844d0310400300e03521149452049402c2206c0001da1400584442c80280008074440d1140716117913008010800500800e40d20b4804240c3c810b040080070a40c0035030000b424008c401c0c0016001c1d9400c19811501506000401c00c031985c02805442501540000e411000103407a00c43c004903030780280e000303103c0c007541c0c0c020724041 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 120717203 1250 120715953 120715961
    0x60f030605061923130f14090a0905070b0705100e120d110405181807050108010b090409060f0f061e061b170a020f0604020906130e010507030e060a 65
    0x1121183ea0800d031002c04030f82c0b1a5408501305900a205040000191605006141c00038005140c01c800003a800303002c4a13034907030915401092442140b400707100c0b9250110354006009842c1b0390595466058840c00c0003402e01c181000381001d1512280c5500e6142806903841001d00032240c6003910b004142d00a0010101d1082c1082519440f00c9141500e00c18508000b4007041c90301e01003201c5c05010100d466034034840980301d0881401d820780218204a003016040700d40031031041149074402e2604018a90f00b1032059070444034cc20041d540c80b100720402280181941030710040c2014908040d40501c000b03554085103181a076040c003004a240c4907604100a0b8003000341e00140c619182c3c00403c2050711680d01800e002d1002d11a60364010400c1d80c0d1f508203102c05078142e6201c0c00000c5081c140d4541e0400080382030082c414014044c6080c280c0115180e400302505031402080000500c15040400707403c5810300302c6a0030300070030542c80c2195005000306911041000c4a001d06404901c80d85e84c1c07409 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 120718453 1250 120717203 120717217
    0x90c02120a0f120204080303040b1302130906180308010f0506040b1206031c020109020f0f0a061b02030f0f06070807020606010e01033b031c020306041104060f03060506 74
    0x14031189030600303000040d074003020040c4040080010f0780e2107050301c080141c0054070003410b000008640780d060924007a0700d564001002c1100b61107031304843e900540c1d10a40d0134104169402c1d0000b074944160308103070010309070280140e00003010020a007020541e000200c40d04035a15102800701040d01c6d002081800d110b10710525900c0c580500c401d0a0a043c810103240d00080010100c50b10310000c5c0040b410580c0c2880c4441c009030359919444010f604081d090b2100d4040115004582c0c1100b20002a540307075200c0c080e1100700500d07000c800140803c03000d9281d40e299001011a01071141d00d142981d038800401080703910038060b040210756a035008008041c090750194018240c0d0f5540c0307000443d02c1841c0b00071942e0405480d17482c9403000702003011440c258040c0c150b0f104403108a240d0700141241076911104c491a50042010401048088900081c14154940096501d494001c005030281c2007030b10300308140c0800050001206078105030001ca6140d1681ca0500502d07507281f04100d59401703550 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 120719703 1250 120718453 120718483
    0x2901060e01120b030703020d0b091b130f0204122402090a030f05011409060403110c131503050613050d0206220512130509010b090d0f06090f0606090c02 67
    0x1c00200032120598200030303d920f00203411a02801d560350000b4503030503c545015626802500c0910640b0036040c07040c0c24922089502a10f14071760031001161030748154982c400040ca070b4480004000c1e003d15011180146110134480c49240380c2070810010b008004811405511044840c4180810142c003c0c0c0e68490f1004248108880c40c41d140c061020b01e282c142141c03103560394094102c0c4c10011445070360040d030003600180400d20349441c014000f03010103c0108030541c0a28010303146641d030907a500207000612540400c0d0060320803044410f10b0300030380004149000b06400c0040b5001100c807643c84250240c400ca07801c60420070310580e00e0316820303a05a04d50740300e01e00020b0000c00303440007035001d82072049044a80d5101a40070082454201d4112900b540380800820480d520b000104d081c050240503800901d8103c441c000550340501412009103503401c80d001507010b101040d4080c20800c0e4111803030000e8243c0390328000c4000c0001d405015446454111590811407001501010081c815 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 120720953 1250 120719703 120719717
    0xb04050d170a090509060d0c0909050a02030a0602030601090b040f090507020f010606080621030d0c180608010504050a050402130e011d0a03030c0c080405010302162901060e01 77
    0x18481540d4800c501030368054032031241c0d80c1d00c50719000000c080d44a00d40d5501605141001c08119203445d000e0b0a0a01c58100210b940d004100100c0051003200d001500000b0039086600d02107017018402c50001c0e5250040303402072000d1042036001903105201c04da803015a401e4440e10054685d01850007140f80d402c0c07100a00388540380e29640030540010040c0120713403000b402d4004c81401e50300e268010368009051102403000d90b0a00d000000801c0040b60a0180c901c0b5100917019664091440c0d003000a60700c4410101809001e0040c014600b084890700c00d217000d0301c0c0c840141543c002031003000c0c0a980381030009080c0410b207106d07960246500409484030b0059540d400800783c1b00000903001d29541c0d5420620024030070380700c00541550810040c2c20071000600b8040c00310341c00354070310000b4005580c4031040040d08103070494054400c00d01340181c40c5c40e0b00050000c5405558034004000d04200b807460009010010141c0040c2d2202c0e209580e42aa200d082c1181c1815031811514041811 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 120722203 1250 120720953 120720959
    0x60c030e010c030e1c120512131a0106030911060405030a0b0c1606091208040f060507031d01021206030d140d110a120b030c10050c0a23070e010b04 65
    0x1051150030b0754076000b803074000c82441003034000800c841d43e90394110b50300202042c030b41010080e0856810700149100d044c0113040040f1440380f1030000400400300ca8600307a20b64003503c100624024069600580145041714644c0c640502800030b204240702502c2d005050201c010381481d09a00301d405444c4041c0107440c2c04215503a0f584021000a444000714102c2031084140511442a840031403c3c01214086101203da00301140d0b80c0d214208564200700b14a410840400ca54100d40c80d00c081c3d105c1c03000607107a80c80c28822801802c08940080a2041c100480c10401005401610040d40080c1016101fa1500e40415951704a40848100405d140d20342883c904103100c0003914082411040206610a1031000c20300d0b60b80c407015038034001c41d83c41c1040a480c09050301c035103250b030001a0014a1100c200700006000b0000100b041c000b006000142c1c7c0c1c407183c40a00000c408268068105541c603001c110344140b191088040040132441001c500040c07076804001071504807034a5100b401d01c0c0c281 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 120723453 1250 120722203 120722207
    0xd05040501030203100e0703150e01050108070c05010906110c150106080c0d0912210c021506030a0b0a051509130f0c0e10090f021206040e07090e030307020106060c030e01 75
    0x141030805403101c045c000104035403034541e214810032a40d030700050305101e84045503120300342c0d0780c0000c0030a200c02001809282d0700720000e5038020f0080d0808810401c814500b42e03015209441e4003c1c81241030204183e243e00c40e01018160350b600f84020b6502d2410350500450701c03203000b40310b8100041c2840c1c020170760007902d507401000c0004001501040c4071405840c0c0400c034101000c0644001880c50042c40c010229610b24004428603400d014007403510f086000a60300e240385000956081c02c0c1ea17010418954081100c3c2131b2a66103c0c0010303101746481c4001000034102285d907050042902140d4005a246c58046984501c2c141803007201c00d001283c546135034105200400b1180005140c01c0072030b00000108105205800c404002e141c82800c0c000350304c0c29510070360a40000c032801032141c0c050055007194010380c00401034800152540100f9a15464101603038800541c103850302c28440c2582501000441c03041081d43c0091003940c0e0f5440d01281c40c40400318010300003410b00e0110201c03640c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 120724703 1250 120723453 120723457
    0x30f010e1801140a0606020706020c0108060406120308060906030d0206041217130512160f030e04020c160b0a02060106031a0a060201090204050a0204050a050402091801031b080d050405010302 84
    0x1056041d0008110311800240c21212604542108140389100f0003000401a0240748054039052026044d0640b0b0514040d588084158040b030500042c4000566151915405070f03000300240460b00c21084440d090150000000703540003030180c403501001649604001540f441c030070341168018011540c40780c4031034002620360f035241000c10104805c580351000184040602404040101d55540c2007c0d281013440c1c0b001e5061194181303003092044030041840c01080e509103540020305071038403090764502260898800031300103511510200c0c840e880d04200090301140b440107000003019640d1501d04018160096a403000c0050788400c0041c4001407180d085011221080301c000142c180b000c0c0b00003084446990040350060303548950b0788095182c24003c03640c000040030700c11442e090418021600607812802440d000c1c036000100458682c94034503011600c00040f01f420411940c580c80c0218a10f45001c04821000c0784054000c501141c0201c0c0040f0300c40340c0381d1111131401c0d2520005501175 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 120725953 1250 120724703 120724711
    0x1b060c03030f0515122119140a050c0c04020d090605060a0806070c03140a17070c02030712051009060606090801230910050a0e210f09060408030406020a17030f010e 72
    0x240c040c0e000042a60b1500c0c07040c540c0300c0389803104040d840e02000c4001f8201046c2d030404042c1045150b9145000341e818000c100c41101c01245445170341d621140151030f00d40600700c040950000c0c4002400c05c48400140c1c400d0440610070a010300041d02c074001080b0005000c4e004151058111070301140466010341c010048061080c18079510158540140c190305401a542020201c1c1c40408844804120600c079030381e0100742030070f09040b120526000303e990750046028400706513011800071010f004040200d80100c85448100340320350301c0b90b4600440a03043c2485a01e0200b808108040380c0100107005001c81d103c2180003c50a140002c40c80d9080140042e0924189020f1010914034000c0c047c0100c5120340a00305001c24580216083c1501e4245038041e0b00310038070000e4080442008058044810500040c040262100740d1a00002c040380f2407a40955031512002400140c0c554001c1920b400c40b600800100d50b05602520340b1203450f00c0110350890b1900000c10050100c114440391041d08 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 120727203 1250 120725953 120725989
    0x30c0504200c03090a081f020f12010308120106080403050706050613140103200109090e0c030a0b0708070309120f020c1c021c05060a091b060c03030f0515 68
    0x35080c001449440258480b121485664200243c055114203152030322000410022000b0402d00c40c00c1708044403440107400c400c0c004a40c000488102200c511010b070b491758070204444400a5a41c1e14242c12540d00540d60040644000b00c00050300d9401030407060300c101d805441d01c85c500560f41c0c2d0342d48000d21000b0102c9600c00c5c000786211039404220320401c04041618502e5020b10f5046040c044808a0040c001e401114800300220344181da01021040840d4110b08020540000303000440f81803810b0f508401d034140c842c0202e2941408101601707039010f41056294148142c4813514110181d503050071000c0c042c65004481002c0c2d862254502000100707031807054a8041d0002300000b40030122030364030022603c2c0351038601015464911040d40310a0004d44045107003115a540d51603c4000040c080086255245249420b00040f541c580c43e5804400c1510150641c5501003c5c0812000b0300054000901c0d0007404c1e804109a17101c1d05000e0500141c421484000310000c01c540791490b42052a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 120728453 1250 120727203 120727241
    0x6010f080a060207051207030e04050109020313030c02032103180705060703110705060d020405090105090618181203070206100b0301120f0c03051e03180105091815040c03020301030c0504 82
    0x11105006c170b024104880c401d40c0d682e103941c1045010001980c4040c0c214220309803042080c4207480f05007400044140f070b85070070036010021240c0006401c14040e102203030207142c5034425132119241144002e40c824840619001c010800c0c800c60241d40b41801c0c00f0303690304030004200c503101081c0942031403900304064004036201d46440b90f0114850b0340004081e5142560040380074490b13850000072003400b400056580c41c18a01d400300005801d00e02020a895207001e0307080104042901c0d44a200c1101c0411208984200d002da0a1300a400e03841212800c0040c05180301180d0340300c0c0c811407100111484c07144442d0641e402c1810510202001810449038104440e82c1c0d100000d4081d014840114081c0c0c0107010080d03004c142030301510380002410320187d003081082100c04104180104550082840c00d551104841c030013043c84448901700b07140d0706600c2001080302200d98032803091141002610148448515102c00340c05174002800000c0460340c0d0480d0034420390500d42e0102c6070304064060361038 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 120729703 1250 120728453 120728473
    0x201111e130f181401121e0305030103031403190506040605151801090e0106030c030e0f061603020a091205150403020a03030501050f060306090402041d0f06010f080a06020705 77
    0x2001d4090340c1c0d846850b03400700000c02044582074220050240f0780c800c010031311200413034080301c401d50396050161600032014020040c0c188030501081314405400e4940309001c400382c07403c000d443c81e00244400c0b0000741d5800d968083c1242c504042c2e90140f6107650100211503c0c00781c401d80681402491650402d40e104030019007a696500f0700c1c461009002c0c1c15558819121500404240000c186d407070611001080400010080b4411941110541c1ca1b0005842c02c510800701d01524aa225000c07561282403000c48400030080350141c0038525101440c00d1a1414200c103030705a0040e03500900201e24189020043c000c601884000d42602c038000340ea031954501003207051711034000d640980040c1e00031010700381003507010310031540546000c039203482100c81410300207041440002c100502805800010804644558200c8001440e45a41c420038407000040015904c5024503121203c500c96107000280e000d07610041c08003030303400c0740300070341440350080d200c1d0b0f8080d5010307001c12106e510403003030780d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 120730953 1250 120729703 120729727
    0xf0609030f02040b0f130204090b04020705030a030b03010906140609091c11070e0c030106020712120c170408010b092d1009060609051003050106020d110a0f110a060201111e 76
    0x311b808207280c16030041e296814241030400302c0c2d601a140702e001d0b0b4410011900480e50000940d05078204500c2c02103040348062010074090843d03000010881c50800a50085490668090600c07480301651030104e150350366200c0d5a038880e14244034012440d8508040f0604a1240c141c810741c130885801240d080030f9550500440340c5404540c540000078000c0014028654144050300007003804559a685515903a284c0e250711085c0c2c44080c905100340788003c14100b144030182c54094002c2c2c082110b0b1100d80d41c0c5002400b0303000403500680308000c200c00088240311407401030881c0c50945903030074520031014009417809a0740a080f0745295041508005600c0c031050040a01a00083e52444191480c0c0410722820340e980305402418103040c1070051003180e500003074052079020319180c0319880c5403074446100c1c140503240c03101404c00d000c1c0c0558241848481101c0600707542c81600e07140c5a80d96103800403403ca030049151021003000402480d03805000c140f80e0240803528148400c0c0c0751140180725 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 120732203 1250 120730953 120730969
    0x203040305030f04031a090d0f020c3a050607050a0c05010f0c080a380909030703090b0a0207050108060f0405070f020f07120213060503070f0f0609030f02040b0f 71
    0x10030720f1003150014003481082030740c0c882142c0010150810080600b801d070201030701c0d4040044c10b001001208503d41044510800289001d0040a06822850b0340d10107055039040803445650328004910702202101c144a80307070044402d0f034010002c0c10f40340c1c6a405040b40e99601101c10142041660249580400c00038401c0003081030000000003600d0100c1d15028104400050145100c0c901c0c000c0f11030044403000700c1c1e00040480c00039071070502c1318000500d46204585c0401c1c02d40c2103d100e804103c2d00020000c0100801070007038481044455466040c28001d01c41ea074440d500580041400b0803132540500c4a0a80000009200500e00711b50307030021400719401104c444000840c14041c442800390180a808121040c1101600145041c10740c21002601e060700700900944008400b00582c00d8907038040c10240500400361800c0d5a0f0310003242e00c0c042164080c00103210100b0600043c8103006103c41002c482d030002c181400141d45400308801049103202d2290404140204070307000350b56002c4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 120733453 1250 120732203 120732217
    0x1f06140903010b06040801020a1b021807050f07060204050a090b06040e100e090c010e010f0c02010e040228030b0a0f0b0d0906022106030610050d170307030e01050a0605130c020304030503 82
    0x400180c0327a8040c441c0017000304a01248c00001a00b403001844096119140205003140345943d0b5443c4c20740742d2000c04c460502c52944045200a000300c1c13a5010061a900200225101100c0300c25400c0d4a80020b1710840f815602100c1e4002c2c0e00300720070821b5120010312603620600701110020080d640b0b100a03c0c11500c00c8403004e425410244401c0340e950780082c0ca01c01c2040007032910400700d09020002034a1500003500181c14440d080446c1c0c0807507541c0d40c0444001c038180401c050000c103078016081841105448903c40480e080038241004c50030815041c1c4100c4044609000016190600b02e543c40d5000681c480402501c43c15000e01246c4c55000904100940c0c02c1202c41344030500c3c24580b0110000f0700018400d400c040c3c140100d0034a1490100103540080b5201c0c0038200d5079203001e01080d4003804048560840c04030401c690395070903921413049010805c009018a40d03c24000c202269040e02031075900c41442c441d50508580d003075010354040b03403103401207900c1c2c991a929000d1031500224 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 120734703 1250 120733453 120733469
    0x150221011503090b0105010c0f0f030201060509091b060702031c05030601031d0a0602030702030d0e070f090e0703030e060c01240608091b010c0f05061f06140903010b0604 75
    0x5004108031000c10080c40ca01d041180b404110b00601a03903001c0b41d8440600c140c90400000745010010301a464068642c1c90f80d03c14192840e920952601038040d10b0103100d594031514041d0005800c40030301041ca001800141800c03580d20019800c01c004003030301310410690305031065100c041c900740704119803403805016540b40c0c80e4680c5410400181a81c00100348490340a07071004594007196000181101c1e03180c0d1280b00981c680da038039101240341d400b442581d20f8100f801c00040804100c0c01040c10030548910103603600c825529911110166191583e015080d580280c1c001c10210348a081080295403005080d645070502c541180744c00d558428401c09080c80442c080c071a0080701801869004100a041407051441d00310f2582da1108079041a40b07004040d96040032580d603115404003e9400c4c1d000d00c4441d051030550805554504003224010b80382a04180401e906d0001e640020049a4080d0380301c0c03002c1c050341c0d81500d02517081015940d415640790740103400580c0d0b4800107007006d84517007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 120735953 1250 120734703 120734767
    0x2010b0a0b0c0a0605040201030b10030b18010e13020111030c1006050f0a1802040302040c05090102010b04110a12020d020a02030c0c0603010303080112140316020103050c03070c1502 80
    0xc110526003507602200e01c8000030420b031400c512002c2201802507800c540d00003581c1e940c074001a000341c60014111030f400707a400b9072150346145e0158462407000800f0b442c101e80d154007100401d600400203014900c039030768400000840030640203011440440c410714001d4200304002003900c0c031b50b400007403014a01c1d800007140040ca103010340c400c110091074100c584810502d014008980840104d001c1c18461903860b6044904080c0701b0b40403070300110b9010300201305400c04c0810003810b9030440c00e00702d40154200841c1d102c4502d402d0041c1084d0007819031100d4a4850540010f6030640c0c5624640710700f90390240003900407000c1d148040d103112a802d802456891200c0c40c0d106042120180031340e1700c42d440510040c40801d42c880c1d640740c19607202c2c52041400d40c0980c184009800000300c9103518510000901340c42e10680b0940510405200780ca05000b6900c0c3c120901044d800203d0703d00c800a02103078400741c0815040700400da10885501c10041ca044043d82ca03401d40b515040c02401c2c620030030307 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 120737203 1250 120735953 120735971
    0x30b1602010e01022b020a050f031b030705071104140109020a090f080304050102210405040c020a05070609090c1704020607031b0803162c01090b0c0703050c030613062a0201 76
    0x130605000594905c003110440c0380000d441000740990081a0300c0034240d071004000507441d29001e400c0201c0104824409a03200d03c1c00c640000e01d00c0d48503110881c1c925481d50a0101681408c2c06030700003592504080110582c28940043c00940050b40500d04008002d6400240c02e01003090348005811400007030365499040000182c50070007280b18132a11030f1070b000550380083c2c04140c240c0303040e82c104407400308901a015204038980b03410f840000e032041c06403050015009401095010403250790740340c18003460140b00415264900002170586010f18160000360061410304d000b4090705200b401d00503021002070400d501c003072100860489003018000103000010142207180354884989151403400c450100704803040c40074551140340301c445403d00444045a009541440162841610040e1030302c801140307807a9200751030701c004e55540c00382d9134100380541030104606100e00030802e040b050075240b907510000200101303105003540d200c00c071f131402a405008500d0400548003650001c81c000345 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 120738453 1250 120737203 120737257
    0x1020a0305060603041a0a0905010c020a0606060c030c08030402031504030c110a06020c090a02040b0706020d0b0402040b07120909090b0402011706010c030e12010603050304150504030b1602010e0102 87
    0x1a02c1d06104003414010040011030b098103255000f0030010055800d500c840403007202404607140014001d5003054032103925280c1c00598400710600981c01031000e81d41c0d6242c10b0314201c030840c1011340000e640c50415404205140f0043d03422a00c041c0403280301c0c0d1500745081c9106c10040c2c804600042c4000130060030700140c102107180000d022a404488076142590281d075849507481454041c021460024441c581c40c1d5058400800300006041d55807007007850442c0007580100460090f0f0f03803a00301c1611482c03d2a100b80c8040d03900c10000c4e989403001079114810300d02e01d02481102000f81d8140c01003034020040c090491003610230b49440c1d045007001d10024183e02844541f41c6840841c03007003044080ea9211804070314498140c00c0010040c203034080414035010089583c03800d55030900d8400010810300200030400c48100d1000e00703540349045c040464040c810380c403002d401c7e4500c05000c221031401c000c5500a035220207000000e0541341d4078522a003680c002c101120700c0a10340401d0400810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 120739703 1250 120738453 120738461
    0x621090304091a0109030609050c030f0a0320070b0c0102070203010c0e030f060609070e0406380702030a06050c070f0c0609050303033d0b090f120a031202070206040801020a03 77
    0xa104500c0c0103c2d200c60f940008055880e2440003501c0180c80300c00000074014148840d100b400c81c0681a00c42d20b1588950782503507032106a408074001045810310880b40c641080a28058a240c00d02525030305103885108a8a90848001444035540c01c02520006035001d101c3e8000256880c0c84903800210301d82c04240c200711040e01c06846c5500308008006059a80b2000e2a500240380d0601120249000c00424000c00b8150400c20442a140154511480340000c610030b048204440c800110010100607814134010703c4802074040c0e00c09001140051180d40000b544148246e60039420003041c1d45030b5001411601105803000141ca000900a0a5102c8607100240c002074004524604188d0004c069807441c56050607806020340c81e0700d41c040e00b01781c0c8000d201c030010740d24240d82298030b8406028050b8000f10039207205441c0c2c4482c10410381011881c82d91815030310405410b000e040c50700c09603104103490340808019070742044580b0040c0d03985005400645101000141c682c1d00c83c40000d4111 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 120740953 1250 120739703 120739721
    0x140307030b040c0f0c0b09070306020403110306100803030f190c11010615090e07030207020d110a0609080d0809070f060c020307090204050310090318090c1715062109030409 76
    0x2413502c0c090407079070010034200c880c0380d00804c180d0140e500c00010a081c0030079604000c00240c00002e0000601021041308940c03004103c007614034a072a1020200c4808142d4030501883d50002d0000070b44a00c2d88448c40c940c805400e00300c052410300c0c03000300303441160030340107400012461480310303031080038024810384000d803c40500c0c19200d0003a25001801c400150300c6429a040c15600c001041544283c0664201580c090542c04c0c0030301071441c1c19800b03001d041c001c442c0902110400026042c0c401c0034560300b11101100030b0012440003000854425000905849036841140c0300041e00045811202009007440e548920000d480c0b40b040509110443c1d006000d50341c018001800b150391b010a058030300141c1d403400060441d40ca85015521900380c10b440c12440450140005038058841c0c21080700b4021940d0f4010380052400140052044140c502c60410320060210742414103015004284070109000c0c1024800ca000840700c900c0c120072034680456400100d42002510141d0244041e0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 120742203 1250 120740953 120740957
    0xa0e0115110c01020a02060702130c050409180f0f050c0310140c13050625060e100c05041202030c0d06060e1b030c030a02070f0b010810060e04080a140307030b040c 72
    0x1440b000c0380000e42d1042c00240192040c400004c03014110354a540d400c0307000c1400761703c041c0701c51000c8180140c40740d08640710b601250350401000090031011505507540b0954006203800f6010065101c151500c0c5001001300c2d40340c410814408070700d17a000c003d041510851075202040082c85600d801c41e000c0303400b40c4400c052482c1440011304440107903600000381c510581d02c05440f440400e10301001a5075462000c0700c502d20303003401002070205e1600040d509103142c400b11140740c42441c0c0c0c55801c6a00b20b60403580068020b105c1808030501c04144100403900040407560152098400a00704443c0004100c580d2a604c1e2000c014070031031003001940c8150070142404107808000f07a591118440181401a040390000010760000b002ea03041d120020381080382e07000c1d051030525000082c2802030085000520550349031829400c170601820701a22103540540f090343c0c07200c0c1d4588541d5040308110b20240805021051007080c1541c01071740c810b0314182e0b80800c1d60003544080c0000c580e054002941 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 120743453 1250 120742203 120742213
    0xf0b1e0a051504090e030d18060608160302041109030303090313060c05030f0d09080a030f1a060d1d030c160b28030b030d0e1813030503060a0e011511 66
    0x301c0c282140c8195070484c0d03d840381c08958402c000d458541148940801243c0d038901c2c003682e00311200d0201005061842c40361400700025034550010740d03503900c1313000b00c004640d010080f001e000500301f503003101240b0b205040341207040c0500100000c0c1950002c580c0c403a015400410a83d0309558008102c4000300000c0c108105402040d855060b2648074940c160071070b943c00028144000b85145d8080340140c0e42103a401621140e00100c014058188292800c2c065410001160b4031414115040c00c40c5c01c80c024001403074909003c10302c001601100f22074000c0111001c500100c00101072000b8109c2110000160801480c800304039181d188940c1c20442800105000d08071124800c1005561004451801400404802c940c220041c0017500030307294043c02070740c1a10800503048241c030b0b010841c0c100c503483e840c3c1484007180144440c0458141200204044000d00483e010b100250b40084015014110007929204a41040c500070ba00945150608a40743d64420758445089050203d00e0341c0504 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 120744703 1250 120743453 120743479
    0x8060a15050d021e0417100e15060a0902070c080601060c0218091006090c0305090c01020a1506050a030b0105040b04050601082707060c050d0309020102100f0b1e0a05 73
    0x30040c2c0141440030450550014030f031000c00d00b10f013a4520303c4881410440d0790f41c80e1511100c0d60707110f405a0404900d88100180211140c00e14010312400d52003500003001d40114000c41a81d44250181960b40c12107640e402c003048125450000b804c0341801920040b10017842d09090610300700050740203100700800828824010ba462100050595102c07100d9200c0d2500c401d40350904051168400e04c80403840c06200244e6964a500b09108402c0e580d1002c00c01d82c1e9458014580300c2c0882d0b42420300503080010701c84001100070210a0200d0521000050980d8690f00480c001c0d03071190700146c0b154121040100240d282600542c1c188080940b03050041d8140315002924038900608a5010a480e904040301c001c4a196562000000244c0441d121395a454002030030214015074107403064010085415500760003409000c6c2c4407541a80289860455408a00c0040482140d200307001520b1318510780e00d0ba6506001c0c800c10b070305080f60003e1048003c0c000c100400a15a0000340a40d50900c080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 120745953 1250 120744703 120744707
    0x30606050f07080c01090c0807060504051003110c0706082202150a03020702030a0b16020703031b030522090e010b0105030105040902040b0d1110090e0621070608060a15 74
    0x7540101c0384861015441d9941480c00d04400d001c1d040e65400903604e801c22103028065800071410403100c40a05031074410361906d07401c0f9140d1046d8080c1c243c204010b212082c0160b0b00c213a0040420300c80c1d20b1581420f05502d014801d08151030395104000080b40c4200340840b10502232810003240040480c0000301c0340c02507020400c2d98460343c2852210780380201d00c100f003081c003036012070f05115401800e60308401c44030714100c0c0307440d00244c0d800381d20740422000100f0300070f00000c0c42070142d030b8140d12030101507010030300c40524228002c8012810004d061041c1d007480b8140e4010a9181c4117550f4002c5841400c0020308011107040940d0031945070304160b4014143c5e6040030880c1d05451003a40c012624602500200340549045141c40303030030400c0e02d40c80000f4401090304200d1b040c41c04481003105100c2031a0200da99591a0040350541c100b030f4004214585400310100c40f85650b600242c1400c0902d40c00355906000705540302902140c02c0d04100480b40c506002c050010380001041009a00304184d40 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 120747203 1250 120745953 120745957
    0x705090112060e10020403050a0b0912070f020a05060a021509010614040f091718061e032a090310020c0303010b030c0f2a06190915020307030b01090603060605 70
    0x400ba040c03540c1c6640d04201e01e1401d0040410040c10440d0655485589240c01c6640d03c0c5450070649030818100c010031101c04000c100c00c0d0303000d944140d0060824040d601c84966226480300104c1c1d0280380e01c080011aa2600d50103011040ea9940240c030360825503220444101400400303880c620f0345001d00500420a1030b2460150302201aa40081e6102145181200405142d440a800c960f82d8806040b02d981b131060003030000c604105e5030b42c48814180342c113005940c01509890301c4d0f084408202c459041e400c440245034001d5143e02c0e400c100215001503001c001d114400841c08454000500340c0a9040c1000b0505038948403203001c5140000c280e00d02a100c0c0418005c641c107084001010641641c1c0d0701d01500d58000241040c103546228080064061078441101c81c0410304010700710307000905000c00d81034842d160090b520b00440d140202c000f401014160012200041512040358088115101852003405151070002e401c40d1540b0024118001640c460005c050400400340f00350360f440f83c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 120748453 1250 120747203 120747239
    0x1090e0d140c01020d0f0204150c172526030103050d031d010e06190203040218060a03050601030506040501051008120904020d150f0503010e19030207030b040f0507050901 75
    0x3074540314250045018061311030714041e044850304240702030f001e000c03041d8002c02c1160b01041d407950b480d8220040961b00100c510502070660021000f50440512080000b0041e610101555a442031210220f080740196003000540703814000e000581ea00f040b400013810790141000308200c1c1158590740d1959605c0c0140c4d00b6042c209030701c0707a1b0b0381c594000440c40c0c001d0400c10b0803002070010264502c141c03a1341d10404c50301c208a14000c0b0055010521883c403c072805960050100544c0f40c1000682b000e0002c0c0140100ea0003c90414001006c01c8044c0641800b841c403800281106003000c1c2881030a644016004001451100a08100b80c8400048540302c0c82005104251901d40207000070303000740105c406a118440c2400d001900703800107400e42038160340e1320241ca0940f882d240c5040c1800c0351014420728405512045103000c9842d0340303108110b651031013441140d507074130789075070300c428410300280e5080764816802d840340d00c2000030501c6404040e08040d5440195136150141007100104131107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 120749703 1250 120748453 120748487
    0xf060203070c031b0302130b010e010903020d06050408090a0e1b04060804150219080709240513030519060b040c05040611250305120405010e19030f060501090e0d 71
    0xc4c0b480311840f40411070860041d5001001800360980e18040030b00507003143d0030b86a000a100160603260ba600402640b020b4980140c9046418202603440300300408018100b5202940e050201c0f1a59a466001340c501070030442050b40e0341410f00484a004c44041c011211080e04014042071111590060020b5400368101400d41d900d07035414600c1000a1040d0034010070b2800c00400707208501c036002030344a03008006035a124550a0340d80c441820048101c02180c140c84031324054403219552142014005c0011500b8210070344540e0380d95a5807601c24034180c0d0401180340b14203640305000561045020041003690103129000c0101e03c02041441180a200288400450103031591070081040c83c0a62400d0911000204000c0c03010510360f8881d0310040f900f40c0300e061007001110b41c19400703441c2110810b07194072158903c1903040061003815400400c048000f40c04001010030300009100040302e0080c00005172a50403c0417030000c1c0d50340c0200800f2980d0100c080c84500c10360020981e05000428 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 120750953 1250 120749703 120749723
    0x90117090d080c09040c1e02120d0e010f02160c0f0303091208072301060f180b0625060509060402030c010813150c030b03070b071122060f060203070c03 67
    0x8540340d06103501132200c500b600b19282000c143c807000c2d000010449082007090700240c0085240208a0303550b80c4403503c0f003003103c40500c00c0780c14500702c980201004a00003000428048004003e1a0803a040361001c2211040e114801109124142a1910161101d0fa106000c0c0340c0c255100136001051510494030b03d14548110b14061000301003d80d00e80581c04904505080032010f20382c40d0550810302c92001750751030701e10f0004400c1491240c5100f181d846848003c541c400150300c480080680c038844075002102007085031051180c0010b00054040540080c040442d52803e00004552005007000c003903502c081c1c180000b40e540014041e003051024604010b40e5510380a032608100c00c0c036407006000c0c2181d0141e0b0008040c0a4000000300c0361181e40c00c0015001000030150303260910300c590700c040c140800024000c1095500c2d1142d65001c050211403001d411002104403903444e802c0b000d940580d4a040500041c10250044401071000740300642c01c1012544450072000e665201c014800240 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 120752203 1250 120750953 120750961
    0x4030b070509060d02131403030702010c1403120a0509100b220e1209100806060703110102090904140706030b1813020907020a030801050312040b03060420090117090d08 74
    0xa683d0071102c018640381419500c480000c03010703050340852401031001d5166005917814040c2000019502002e80503524810041c000d51500488040882d003460428001001001d4004156444e0035024040c0f0200000301450704a1410b828014441c045400050800f520f00c00383d0703640d0f241810012518407a50106402c1c000f010003000703140d141c02002a0b80a0680c0d041e40c5122084c01401050702d0a44c0c504050b409400800c54840c0c0044810540c043e02c00d22101010a11a03e03912000600340b00005182410b1400010310700541100c045803406006001d120300b089050081c4001030819007401d010741c0780000c0c00941e020300c80301408041038941c0c000245030072034041242c0200d90380140c80c400c410308204030000e4490801e41015004244400c00005007814000340c5000040350042996007000e08004003e031180e170010380b61962203916060301c10160302e00c7c643c0d4500f190310b07103c4072182e65810a03400984650b4001c00c0c81c501d103400580402c5090b176804161030f1034480561600e0407131561 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 120753453 1250 120752203 120752209
    0x10050106080a0b0d0210020d0e0609030601150507050a150c080105010509061e16120819052a0a031401050604090203060a0f0e0a0b040e07050f01050403050105040b0a0c0504030b070509 81
    0x13132103c00113540300d040285035800550b004100030410005ca6510550300e030b02d0b0981481075034400c0c680c01540651104004001034800680703803c2102ca824500b5608d000103540310030b0701d406442141650041a6416007213907404c402d1042060680d0300e410714038a59803411001a101d0300030103084c28018a8002420401080144001d07ca030141015107162240040301400025078034217042102c0c070410035840d03440c40c54043c0b4201440743c8455046100151014070349140a0700c2e029044145c4890080c0450031201e260f80c49003a0002c507113203941900c0c0c2c504204004c050301d0600e400300645c00080c03401400030791030301d104440c04d135004582d001d603594039984040f4070348640d20343c0080090103001c8004220304088003003503070080b06403600600c4010034903c2040102c909450b01980310380d004c03560070013480c20501615071411170141000c508159594589a00b52441250120341595015081003100c6c012440788072440da040e440c18078105802c5641e1282801d0014250105001c800702d01140e00c0d43e = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 120754703 1250 120753453 120753469
    0x11d03061515030a0209040e0312010b1e1602190e0609090c090108010204060e0901050904060902040b10050c060c160318120602070203070b090604030b06060712020f10050106080a0b 80
    0x11000e140780d0341e41381250501000390095813810344140e090440f90700900200005507840904518008203403079280100303406569101518402c00c0c219070080c10307051058000040c1c1550760f8a0842c006074100c044c41004517140d0b040000804c60454104140103055102c0000da83c4001c05507507a41080e103900260524204980c21001d0740b1000c2072001064845040d00076004603506621070745d20b028400d00400c40440024000e59030030075204400036020481e142c00080c502d0b40040c200280402108010865041d0307441c2c81c0380f01041000030080701d082810061164001200e680c00e505006090f880c0702c2d59a1404a000750030081e2250b00303503900c0c2906410010003001e80600c800c2c1c6290032864140042d400410007a4401d014418000a0206025084407128000101801d01c0c00d410359644281c00440502166081000bd0040c03800140c00c0d20f110300100711998005041d0110351000540c5001c1d403175960304150fa41050010170009030000a140d4100385400c602003800c1e171001002ca5004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 120755953 1250 120754703 120754729
    0x110d150e0106020d02010c05090906040f0b09010f05090c040501050304031101180605010e090109050706051305041406030d050a0801050f190e070207060203070b07200f010209011d030615 82
    0x280310800000d803507500054001c260070060340013400410024602a2214001e40c01880d070800c00100001c0c0c81c5240a0b030140904851290b0b001400c609c1603808518009000d8004015510100a0500c060302e004091aa4400040302c140c134509800d050009016010141000701444410101d680810400790040015111800c001d1210fa800b10b00700400600f2013031054001c000055400720b08100018029100700903009001440c403189418021501980301d49010380d002c1d0364600b00810309a4507802046030200481c1100081c2d41010010182030a0180f030300343c01401020061b0304100340d0041c282c0c50440c1e8040302c0a051003640407002c01d414400320190503151101c07a20f000300c0c1c4030a54803030036405081c9030340c204c8410540312402a80d07a44201c0c00081e01d900c002c180000c0714507200307032909881c50000d040d80b10781c00d00a10b240302e4030300494030092003007030b940200b419142940d0200e0342e40c440e0045058140e12900c55480442d44480001c0d15880100107048004201a161107e6400b11 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 120757203 1250 120755953 120755969
    0x60d030305040c0924080c09010e070e2806051c090201030204030614040b090304260309060406050c06070503160e01020f150117030703050409021e07030201020913110d15 75
    0x5608a050340c044200048185c0c4407042602607802003503103003001540a10500c0042d0869803240d0800180c0f45004900900610400c1000040006141c0740c41c0d5500418082c101040c41d03c003101032031710110400050704034a04010050000003c03001c0034444884c1c16190540c0c00244c04405400124081e10031900702410b4181828000b4180303003034403002548a40d0060049140c07036110f070301d01540c5034480ea1040b800c014913105401412a01c1c4070607482124200e09040341e10309800400030401c01c0d0802da000001084020903019a428030a104d05507010a180c0b81140c550303e0030351049810004004080300030469803004000f100d900030001201035140032000c84590b40c0410340c0300e103500c080902880c0c00344890702d02003001c0903600006483e54550b045d159207003040c0c10000e101009400108600000000a038074507038005204000401d907043c06640056078030040703407061000c0081e0120180d291070b0300e080c480c451811700d0842079411a8090f200003180d006501d40361924a003004d81c0040360 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 120758453 1250 120757203 120757211
    0x12020c0d11040e060903121806010f0807050406032307030b01080307020f040e0a020907090e010902040e070e010905010f030207020604060f021e0706080403020109140d17060d030305040c09 83
    0x10500c22000345103141d450007140d052211100e00d01c0b02d10744a10069903c9002c81e48188400f1365102c40881c07009034088640102040020040044103103454001c0c2c1c8250380f0302600860134000e0b1803050001201401c401d07502071014620755903900700381060b00450076401e41c101d40c159840f1200107001b0940150740140c41c0c070409503152401951664000d0300f0032803245061400d60034441c01d0a012b900e008040c980c000d40748540d615028041d5440c80204558100003400d1004a1814190840c0a01030070106400507205c0b420141907030b00c0c1d0b40e8042c04810a101c5290320060f9035a0f800390041007502c9080c41c202110001c1480140c010340104c00300290f0140002c01c002c83e01903400b40641201c00929401c036410b2a601e4421704080317503210903000d41c4580000405112071360050010b20b801610920001581190030380303c1c6801402070788540b055039000101c5404440b0f60003d202c00f010700c000b00103800b03681000ca0029444840441d402402d158540e00000c00340002c5200800080085841c144 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 120759703 1250 120758453 120758479
    0xf03270302030405040606021f092402030a3c0603020a030f170f070b0601050d02031311121e070e0118050109020309030307031e060608060907050903070312020c 71
    0xa920ba070000d0046502651401c040002c000d880000e103400c2c2800740c0041d00000d51103154091000d050341c0c003000e0380c04142c815100705101090310f00303001cac211108410058aa007410300001c400c1e5201091a075529200c189140c590041c02d40081850f0b8100310f00308107d9607a89003682c8400f500c1980d2000c2e5102d01c0301d8000006021840940d02c0c8035500c10310010350203c1c00c08003440814041c54000c01c40c07401041c41400006102d00c80e1f080d4000c00305041007420002a002e4010580c0c1c811618818030302420640c0740104050031883c8100c0000480b07070320303000a01400180f40c0d00c030040c1140f03c031203070600e000f046092982400380d1780292002018901c2c0d02c1da100c0a0714021100030007403200129241100001d843d10840c030a8a020300c0d4107070041c61560701c2e00c40c002c0703007d0000000d1826110041c000c00500700344187c400c51004044036102c40c1610302c0d00c0c02c104a003e003001401c11041c000100100045030b5400304011003a294864812610843e4a050807858405840c26181c0c00c00d681d81a49 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 120760953 1250 120759703 120759707
    0x10080a0503070c0b041d0a0f020403050f0705010201111611030f07060207060309020a0b03060f040510030b0a0501030f08030910060b250308010603270f02011b02010f032703 76
    0x14200c0b140140b4800c0d405594800c0e550840e03210301e01c502145600da401c00074070b80c0e00305200c0e25900b285203800d0105190121015107412640642c7c82202c540d030114648649401d02401441c004103002d0000304400c2c0311000420805108603008002d00da070345064640200044007105207035a840c00b5044411024101700441d944258a00426016104103440018814824099640c1041c5d0203404001d80501e002181041c0d0781015020503401100d0f104c00b10701a03251071044511511101011000651950401c2c83d040c0034060401014030741070000500c045184030495401d29a840811a5540d5441c65030b0681000c11032080844514104100040c0d50200c0c80050a07110084c2c0f0103815200f520b1001b8800c041c0c65643c0d00802084171100100640e40c080d03400048907410b00a1640088802d84408000c820302d80081102e0b141c00b056514419549e10010000c41e40080001e07560164500c0e400192402c580308402904150300d070f003075400c4410f40b1114443d000480842400086290300d00e80 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 120762203 1250 120760953 120760957
    0x4020c0114070206100501020a0b06012001200c03030114012606131a060a030f0204080601030317040f110a1e090c0905060409020d061d040c0603110a0810080a0503 72
    0x80c2c0b0041c4205008070302c0504c014184102100c005030000c2058444a584804480c60700812450500c1000d582945420001c52410f4180604641c00000c3c0254107003021131950f5110052403019980610003628101070000c200e0381991b81c043d00c031001407582900100d401d00d8a01e0b05450401d084e04404040d085035007900c080c02000c0486115101e0f074075410320300c8112070714000d8542d20300320a032142c240c807410950020310040e10a8039022410b2102040c00c40b003a40d10982c4803070010791041c001001819813092007900c50106021a1075000e040075142c00151422100c0040c0c14105070311510200e542ea0301c8800070003090300e9941347e0001800c24400350b00d5001d051003800c1d41603003800302c0c10a24912440034030f81580c100400060805003003c6004000350020541880095900c141c0498504419206000254802410b02d40545890b14042c0307504c0346264041004d00d41041c0481980104c82030550f5480c510b1454006102d5031003e500c20b2012001d5400b0342c0305400f580300303180d05010300800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 120763453 1250 120762203 120762211
    0x40216060f050a020a05390c0906010906050d111b0604020108070e0a060e0604030b010b0a030b100e040513080a02150f06090718051009082e0b04020c0114 68
    0x81c100441da80303000c03040c4242c0c811203111000180b42003014031902406055048008001181610098071101900c02005001c04003842e0041d8030040c41e45207a89807109001d58429020700c2c101d25250703d0400040d0a601541c1c0140c100c1c60b4440c10800c5107051100140c417030302c2022510900d14404031400d4180c455000741e030280e00103034400b000955040d018241000c0681400303401f00c1480c91610070200c941081c1040d44640c4040100800000b0540031140329010341007191410350350b040d42d0507000d0110f40c80b65500902a00c1d0300344200e0510707070300000085820007013070303801040555039416001c0d80d24050120040c00d211001c28003030402c40d0b0000c1c42c000c1041d14087c002503a91503151320b500c042801200c149501c84c0054002502040c071466000039201b450110004502d0389900000303445400386403c41d00042ca2080c810007110313404000e0126550b059012840e0404600c1031148043c02c00c61303115603201a00d4082800003501c481e8102d45140350100003c2140901c01165480751b0f136404d076 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 120764703 1250 120763453 120763481
    0x702010510050609121c020106050102070e040b01060503061c0c0f0506040509151801120c14030c0609030c040207080c010b0102120a120e0307060608010c1b0602070204021606 77
    0x10001550340c41e241c084041500c400801d580c3c200240a002c020110030100600c1a09000b062003505090540c840c40c044d0f00b00740b907000850303803d040000081c6000b035983d0140d00b108410100b80404951902c0b8031a05489142c5800f59903a52000301041d005040746c00f8209807652000c00c00740500500c0040c440030342d4400c0e40c640103025614010842c403402180500c5034004124030106007056002460180c034820080e01c1e404c0030010284d40a41c14030400d03030224042e03c050300040e0013045100c0080c135020b040400c42c40c181524050b0040783c0d42d010b0003201c890003070700009800030080d0b5042166104103a0700a10035075803002146040c03200c9821010b540080d035820640107100030741c00400c070307101d9070392400c145103090080d000c1c01140d151840c0c03030903840e00f00d40d43c107442d017810300c001d00003400151700480d004210507160103007107400c48140d004440100980035000c400300d0071801580900c0c180d0440c00c0542c44140600000c0c4c000d03c64415600c4aa090803c010400c01100d03400c0701a00303110344 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 120765953 1250 120764703 120764711
    0x1081e041e0b01090f0c0504150c0b0103030801090f020304030c0b060102101e0c170f1504090f0c050102060c0405090901150f032904080705010e032116020307120507061103070201 79
    0x6141c03d00117072001b141c85000400ca041c0410701c2072403000348815140c3e0030140b80c504120401c40c1c0344c40c1c5003404207130825070004203104012300241c0d516025407440c940c074401d400c52031881d09440c014461000e01700000c044540200c00308803268803c000050350388801c4c1300300b00140101500c0620800141089014105090104004120b4061803c2d01e201d140e00804c800019561480c0d030b020441c000800c1c2160510700000c610400740c9840c0300c2c40c900c140c42003041b88003d58450402c1d192103040365100ca411075100c0820009101d034010295408c813402600c50391039a44607000001d016003031f080691000c41e00c4d8070340c0c0000e4000020004800f201d02400c41140340781000094030702440300e0500c030000c072441303901e01080c0004c40c0d0000901d081c80c0100700000700c00c0101201c0c181907600c07030b10700d0500310758000001000440010341c03241c0c0c106c0100c24608005483c40d1030f0180d10390160010141042c21182c9810b0241d03070060085400e600c1d0301c480e0401803440b80c404251101d40003627031107000561174 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 120767203 1250 120765953 120765971
    0x309050a050f0d050f191415070f0c170909090c06040611010905010c0c02090901020c0606122103150a0302090a051f030515012106050a06091503020f01081e041e0b0109 74
    0x4041800d0400002888d6000e81650ba0404280e0b03a500000803e4800c03c0a00403e00000c9046031144400325001d200f11a07a89906d090200641404040c1c5104804d800c04400590749941710b00444040328086d0038010a50f0903401346242c01090480300c040c0c6154200600c101426a1140310012010310890f02e16030079454030340030340d800c274054100700b20350035804000480c6251605591000b8000c0f0401d080310546003260300500c00e00b4003141c40010706460302000340444104404d6120501034416a0256045407454001075504100905032048a5956601060010641032200c01d1140c0e910101c4000995032440c0142da00e20750b0f10240e0802160741800404c4c650401d5824964104800710020300300c0419455200082c4400340042c4010340d42c5800c0017605042da40640d442c422104100040c681d861130060118071181c0c28050707070400c4440400c12100150070342c0b03105d48800754101001040d584603d085040584840e4082010710002c2c0b401c1c2041141031945941a5103201c0014400c03005 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 120768453 1250 120767203 120767243
    0xd080a1709060103170d0c21180f05070b1207020c0901050d03030e0f0109110a0b120406020703050918060301200f0903030f040b03040309050a050f0d050f19 69
    0x601581d040c600342e0051401040800d000a403150001c000c4812468500000b01040104450320804200085a00d020005107401e803174000490300100201801d01031403496260a24001c40d070180c0013025080c00c08411000d00c0400c00c101c2c8007405080e40420341e600a411005800004100e48001c0107210f28400c0110368105021000c1c1201c0020301a060303480c00640d4194081d0004043da02558032901881a40c48030f0300340a0600c14074010300800340e5000c8841d051055021480d04100c110319402c112203140078059164240d440758010317400507214085890308841620681071081d600c0100110100070103005800325600403082100208032001441c03840c043d0b003940310709940144d007000f4011101902070040c0100000da46c0107003a645040e8220350002000c3e0066000400c0b101c0e004010042010b40005a10b006028115680b0120615010001d95400840d0b009580940c00315401102004000c11007501d02c050701c1070507a04a0196200c6581c191200e2450644501d81032019500d0b500f0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 120769703 1250 120768453 120768497
    0x31906120b150607060e01320a0e1e0f0105010b040e07090509060609030a020d050a03020d0315030807020f0414091e0c010f050d05070807030501090209010e041107020d080a 76
    0x90043e06060820720302d6200c1d08000c000c0b9040c2859155241c980c2d502c100d00b0040d080540c502c401054000d488200d120614001c0c52000b4021045d9a02c0e00a41c0350314070000103030b40c9508078031000d40a140b04120a440300d003011000481c5a0b465800c2c800085030754201c02000d4000c0e02c0c032492150305503585001080b511071101303208a9401c040083c02040403030034128000c2283c628050201e031086101640800c0241109000c140c8545e0802c019103010581d040c0403000280f01246001d01c0070283d940440b84450802d8400200b94420010f2001704540702c10041c2508e02d80024000c20400300805200394452108a134100e8841c01828203542e500749918400c07807a2200c404004241c20700c040c20055600190304400041482000d1104c420801c1c1c1c28003071144035103099600c100080c02d05241c041c0c10f548043e08081d21440c0140055081a644a059000395078030858000c204144240c28609481c45441c00283d0840082c0440002740100d403070041504481aa45225035003000107004a07003c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 120770953 1250 120769703 120769741
    0xc100c0e0108161409030f030a11070305060a1e020315150a05030a09050f030a0f0801060912060c11100e15190506030c0a030f17130b031906120b 64
    0x207410082c0c501405481012800c6484e50318004440c80e191a9400081c54034540c000c542180c4d6000240800000b90703c54100041c0d8980340740201005815945c600792107040c001e00301b01c0255500c000c3c01c1a0040510400907211843e901c04659a00f0301d14111400390342c07808049401451040302c81c10384911800d0841c3c114141603a211411515000818800380101c3d070303c00d4800d40315039004042060014401019403400c29151041c03208002140548103c405a0068007804000201040502944241000705a03445031000441821581080c0c40700f1a04100c94051031080f40e1840b402800182d01c8030460350780800403984407880300d9030001617002007210010740d544034064421610800e290844c6800180080940e0811107440000c01d481003103907072040e01c540d041d04c12040c00748402c030b092034140c0c2d80400d0909464400401a41c50801074248125001840c0000c0050485a00e144045d178840c0340810b0240040f1795590b0111040c40e40300f05042c1d8403190fa240120300300814154110082e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 120772203 1250 120770953 120770971
    0x609030c0203060705160f08040504050c070b060409030c0f0201020114010810050610051c090215030403030e06040c051215100501110c030607080408130305011b0203070f020d080c100c0e0108 84
    0x892241c070341e07d82c00310719100d4030101e42064061002183c6550b0364081c1a100b210005011a200c0e01c4900f0b0800d80c144000e022107000e18600b41a140c003095000784100c80e910303000000413507011103510041740100328111801e485007108030004281401d01140c900700780e820100040c040c68490004014000000c0040d400206008020f20f140d205065242c0c401d404c00c140c8000504503420b9004918001d24050001c07507111400803c1004040d058800c08020b60041d400400e84c2c0d240c80e54484c0034143c110301495210b82c7d003c804002c0c609804100e80d494a00c070f2404540c0307a60514104800c0c94501c40d000d0903010501000100d828000001184041c0b4000140100b50301d0700c4001d800c0d21a18005081555203e07410003100300d040010340001c400a520035400080c3d007030b4000704103c1c10b181400441500315081004030401041003000c85884854049420010100452a05406a11030450b0486181c001c002440c400400c055001c0d072880380e0142c031054401d8401c1070044800c10400c4034030100c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 120773453 1250 120772203 120772237
    0xb0604050103110f0c241b1b100204030203071d0a0506041803090e0106090b09090603160806070207060804081602011206030804090b0301150e0a02070609030c0203060705 75
    0x41030350310a41182c03110450750080280380a09005030a00140d2154000c054036038804003c04901401d0041418080c0812198000050030039100b1104255170103007400c0da0684002c9200900413100c10302c3d12202104807c101c42c28a024200304c84080c3d040303440103904c07a0090301300004050050b030000c0700205182c100d0300d210320340e42c1d01011001840f01501c516002941d03240780380c0801000910a2108070300907201d240d142842c007a0a44601c1c00d0503040f09080000c0c901081141e0f5540d4410345042c0002101e0f500302c2d5582d1580800c1c40e14681802d21030000000c0e03a0b00140800d0702044807401200d09500b9903140686421040c0d4100405031001407003014200700c41c106804c840220190300b940705242c41d822040d00400c64505603039a41c3c00a071488078000604000c039205901c0f9100b40315201b035009000006c07030003848000c0d404140c468100d10403038030384c0000c40106940e030403200c1c3e0300d80c0490208081a03030317810300400182d20a20128000e1080b0340204555030301a10a64026050716510381c4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 120774703 1250 120773453 120773459
    0x60305130f030309020a0e150105090a060327120207141309020121020a1803080a180306021305032a0d050703140f150c0409050606090a03060c120b0604 67
    0x2500308059201c0540405a4520490006070360b01040c1e00011724410f0940c0169092042018080900e041d0301d15062050420001c2c007d61500d0044004543c95410005906441c00e85000501c0d000c10780703141c030280c00c030340f88190401c100240c00d540f10b504103034200c4007071540702d00008404510741030170300780c5c04200084c0440201c2525045400c0851040c500700128030f0b0300c1e82c105034800c01d201410a0119802140d004420b550121000c200f4400081c41100a06c0c559203400d2002d10800c11014200445e01401045801c030003003d5000a40d4010000c651301d003000303405034005510038018603209000c3d00010700c0c10f113900d48490b0100c0d200412400d0094206103801c019144000c00000c0300e81e1b0241c0a00080410040d00e407907996060060090301e500429190301909061400c05500c0e41c1e40c09003018060b00d0b20407182990195810341c20000f0309921604006882402501c4202d41e02094400000c02040800d03008542d90322031a89078a0501d990310340601040d036844031515604204240010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 120775953 1250 120774703 120774713
    0x7020a0b0d02160309090b030604021509010c05070308030a05011d01051e040501090621030516020111010e010b09010b09060910050c06010b0915042601180c050a06030513 75
    0x207220100c02003500525100f08803070008641c100009059022424a10041042c3c28090103540a0044118040c11552920364000ba09120300c142c1d841c1040071020586035010f90045c0c09074464103804ca82260002c0b0b83c0c0b45082034450b0b2045591301c200500f000c00008424084250b403200e800108102420740740e0030442404291001421500204161000600b6468981d446850301030b1490840c00300e00e030f9003410454014403184050180440d441e044401c0040b80d8004162003078a117101c000c00c0380c0c0d84080e0004807821440c9000d9089035519044140403442c00c15800343c47d02c0401a640c11036503a07a105000c404e24000d030880c0c03c1e00840f0810001602d886c00601c00040700d07116051603403d04d00c01e0040b980c901002600b0200404200284140140c6005001144680300c1c4140a41c902420f01403401070810308488403940404071001080d214400a420600c1c10000301188825000380074144402c980c01c4511401c0d01882d40a034020910a04c02d005061090111500c1c2134a200099590 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 120777203 1250 120775953 120775957
    0x615120204051b120a1a03070e060d48060e1201060b0d1104030f084008030403111318080a02010b090105090a0c14040801020a021207020a0b 62
    0x44409048907842503500300341c85024040b0100400c4c0c103c481d0740341a040c2c54045070644401041d124106142041c40350742d00003880c0e400d5409045544945031510408161800d9645000624400300b841c83c0700b0611a1842100c01c0805011809000040340601d10002c402080505030398200d60078a001d02110340a203080380c40302080540744002c0d01401c18405801c4642c0e503080000c1000e400a210b0322900340b20301803403000003c141502860b2a10715502c2400c601c2c10a200204040b001144030351400401440154404990607200213100150304529821694480c5906c4a801d88245010030380a40003c00da40c240c90344002650044010038040040114454115071245900c580d5501101101803020000c501d120f1400f164940003840d5010342901d640003d185c2c046d940800040020341c1c1e85c140425000f1100c258001075402c0780403011114140428003070b9078080070008002404c03d10560003440694601c2d0f0944218564294548001d07201340d481c041e5100104000521000c003c0c040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 120778453 1250 120777203 120777211
    0x601080903030109020f07050a0b010f06030203091c050d06090c1209050d0302030613020c010506040501080a0b01230909030417070b1c0204120308060405090307030c0f020a21061512020405 83
    0x4887d0030300c506944c0c0c891038181080c0080340c001114000401003001130b6050440988500d060940c00c610700f03800f06c640e80f0010400600e9428100c60080e9180b54040c000300c50303450302410000e00c0034940799840d041c064000c3c4000e200c000f402c00c0c040b00d04a02c2d0b0030b00c90481c0513070b80000070300518500441c0490103074002030301240d449840110109001c1e94240300400740341c1d42600001c21141f403d4820002103440503403094210741c000507204c00006014040c010b042d070303105008580c00107605440d0304031001c2810300744c103810484040600801c2c26000028108840d070b540b0b04c0c065400d054404c1c03140c9500c19841450008441401070000d040b2100e80c0da100c1e8000309040044c00c0580d50b0b10000e8810129140550110380c00c1c10510000d805c25024942e030000010008500d4154607a90040c8844014070b0084c00c5243d00d0704000e4115500d0741d060600a100c0d40c11407420f1141038040050440c95181401ca41481ca803002002001c808050101c044820b41b030503202a03420786400b8040a448010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 120779703 1250 120778453 120778477
    0x1b0403020d0201140406030f0c1d041d01020f0904050901020403030f08060d15020d0e030306010905040207141e0606040c0923030f010603050106090207081e0c0102031905060108090303010902 84
    0x1078050161300100064401051903541c00318440306003000c0a0101c0300d154102e00300f0440d107d003c0141440c0c052203034144000c3d00391000241c01c80d01c5845030082500807100f8840e19400000c244400050b000090480c03c1d0080314108260380303441e0400c500300e118522005021031044c00c410080d041c0211040d90703001c1c2e0701400c4030354054107996903c0000070f00a480000b16544c0855a07046030710080c03045004041101d070003545107003400000a00000028400e59205130703000a43c04040202c01001c0c49600c044041c115058080d180da212104031040c20400e156521903d40082c090b450b00c0e0182e0758404105440d03d0785a54105155182d45174000214101e15414030302d4000e40a84007044181444500c4100000301d09003540f402c1802c1d01c1003035001511590040c0074500204d001c00c1c08891440c200d40d0900401e80b04e4407006e00240d40602449035074554408801c00400c000d001d0f4810101c601628070800017a66164010b5850400c2030301c1c41126640144010b02401019a00070300200d4018 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 120780953 1250 120779703 120779717
    0x402010c03020f01090c1410050d091b030503040e090a0837090f0f0806060105070302120703030b04060b071505100f0f1a181017090a0203061b0403020d0201 69
    0x402c0d085d00e01121040790a4040201d0030014190910b40903914010102c40c074140b0f910703040c00f009025005811801030056515040d40c010008050166150311010f418403c0070296603041182e100d420607c25402d11400c0180001e19034100442c00d1020164018012424440b411001c00d40083c007203069803000300001c0c040600c20400c084580541111940e8424a8081c101003c1c50782c1b00c003c5034800c3c0c800100381442070142e014042044d0794408420703c0c01c03035240d210b541022443d10240c158280d000840c002200018076070306812068a109064906100550360341d41d0f002c20b00c0c442c084020b00103c8801c1090b4000141a410464001102004070f09140d91556400c004490040d40b10110b43e11007103034100305185005036452032902c12051705604204002082100c0b030300e00e0310349070361080603000d000c085114099602c3d0300c500e44405903244030728580600102d60300d204034001039100b407003404001400b40d00040b030300030481a220b4030340904252659081c0014032110030401c0341803102d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 120782203 1250 120780953 120780973
    0x301030b06010e0910031209080a1104060b0406080423191115130602010b010903080f040b04030312110307090b0d09060912090e160e03010603060c021006050a0e0402010c0302 77
    0x81442085c025036494194585003461450b00181d41c44070802c1400a000701180f042014800129a40554940280c80656043e10540009006043d290400268000c020501041465014070154407680c803035510291448152508081c2990f0714080c2e50744541d20600c40c08502d000c0c00c03942c98a10b18810b241043c10f400404000604a012058005050364008106016103c1c05424050000c054070b0000b00303c0078900c64002495400139010250a181d4009614141c400891084800504c511400c2c1c948480d00d0b481c0091441e1944d002d04040d442c01c0002440c400c2d500c88040380e00071142038450107042c9240010541042c3c10152502d500c03190340d80901400b1070064012126080c3c442c0380c51031003e0f00b40d844050605031142c0c10210060364040c0401209a0044d140c41c841540c1604050310b0010410000a016185641000f04518207100740780c0201a000035200780510300000301032140c0c2d622442440903030041841242ea410403003401140c01b5500034514001d10358009d105950420780 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 120783453 1250 120782203 120782209
    0x152413090204020c030a030f0603020a05090c120f06011806050901201e12040303020d0e0f130219030203041e020d1a0a0501080d020a060e07080f0309030f070b0301030b06010e 77
    0x48040404c0841d000010410807055243c45681c02d00c00c51080104499030564021802d008900e004d0a030086400d1404940500000c4054070b502c0020008600940e140c2201c0300c1c42502015200da070301180300040e114003005d0360907541d2029a25280d854a081030300304801162403020006a22a006d00c044454010000d4244280540410003242c0310703140000003140d6500c2c0090341708a6101d1018140f0003403000a82c0899100f24000341450040c0109440034006100803842c584166400070808440b1001041c154001d002d00c80c170003821310140d25840c80e600b134080c0d2004450003820400480f105800000b00300604070349031400601448800d001596644401c44d010039901c041e0761420f070007005008546805018050040b0780040c3c103030084030103030182d03440004c07900c000e20301902d41540e86c00c0c0401c00c010350001001d1101c1244c490310303102072160361242d01203180f40c0d011b40074816a44003602c0340003609208645640441e185180e10356100d108995602821311030401c003c02c00d0046440e5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 120784703 1250 120783453 120783457
    0x13020c243904081b03030a0507061505030123070207060801050402030408270a090c1d120d05091f020a060c050412050f010623150c030c15241309020402 67
    0xf00010700245081e20144030a51540189401d000b403080d0720800003558110b6000050310841d03940000d01040c2120003115000c1f0340251038021076010f40c42c007d0040500960f001d80400c020303403140d50228168540c601d0480e01e500b90342c02800003140d410001008075007019401941c2c010702844a4a0921003c015201040030244000250440005035108c02901d01103001c0740081903909020020290703518401b80c800441c88244103845541c1c0340000b0041c1d01c803420309081c0312654105842007080780c004040c203250000320700140a200728411500d1131594030310346800320b1203482d0018802c00f00f032903403604007403c0c13103149600420805100019401280a0410018500c9000900240051420094211242d607403004000036091031a0130380302c0c0d2580621901030101914250035003000d80d08008054801d021008246210000d0751191584000c140650a40c02d03d0740203800c030743c442e03602c1d108011281c9410403900c2c00c2c0040800352103107000407001030381a0485502150305e08858000800326 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 120785953 1250 120784703 120784709
    0x300108011b1d090c03191401060e040b060a03020409060801050c07081b0a060501060206070807050a030c03060e01030b07020d020a0c05040b030c0d080d0e03120609040213020c243904 80
    0x2d00e00803080c460758a00b2620040105a8100007c004600c0f54800342991b40030180300e00d4051100c1c0780300e42410b07501daa0300011000140609029034420118030010000d601612964003158034104021500c40e006009203030190a200c08224140801074031280816440200215082c01e041d40c160100c0706c00900000d00e01030b0107032600080c29854900b000e0708050740100701070104a1001d0400c00e00c40e4102094400c815400d150019240c400c0d070206a0041503180c01451103100b410000000b044490170300340e44100c4042e400d9034424501050f0070b0faa91200d50300c00508020060000340301c1d40c00c10b68404111028018102c8031025403032000700d40a551410010b494100000607004100703241401042c0b03414401000840ca040b00c80c0c41c00720074442c00545194400d980f800041415540c440b04040c403801c3e604c8804540ea44002c900d429a5144158500c800041c49044076421034072404002610603403c800320040d540040204804000000d8808d08280002caa9a8011595280c10142c800307 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 120787203 1250 120785953 120785971
    0xf060c0d120c02061612060b180f060304030e06090a09020705010914030403020307091107020a0b0703030f0902030303060114160605010f05030307080d11300108011b1d09 75
    0xc210703202071040e400e90707161000308010340d0b010800f4030581105031510680d1942691400341030700a0484070900241080340d0007910329080200d01e84001074043d5084802c0300004488242c00048440b040c0480c07404225000381c04641301581007080b604140c0b00601c04040024080080c0c2d640790342e000c9003282c1102000f59003da42d104005000c000d00e0b10340d40740e418443c2c00029400c0a280d0750001c1c5c2d588080313001d003210b80d45e15145040300091480c003d495080d68014480c1443d01e0f02c84e58140190342201006074002428500c4041745481c40348500040160080c1c0a10320715900d01b07005441c0414003906202e07180c0c0c01000ba03007600178003900708000d002e0711503100440c0c2540b400150800c0c09409410062281d00108400e00c00220340b84102c6201451401d0082084443d4000381c15490282c1c1041100c082c4284500c086042003407a01d207052403582520810145e40c0300c000e090300702c8582c04d003501401d200f0014015040f038050180e12141214002c000c08007250b4400109669150030303a400e101c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 120788453 1250 120787203 120787217
    0x20a060e0109081b07080105061e12070b070302011113030305130302130204030209060907050301051e090a1e1a0625030306030b0a0504020a0521120301090f09020f0f060c0d 76
    0x80043c030b080c000c1ca40181b485600034001030400000003001030010840408134440722a05031845506e81c2c1c12102ca00c0d07100001540c2400350750304120301d00c40e1308c510000c0b0010f51030300307940240c4090000180d485801070421184400c0e030446d40e0075652940981100145180320000c00001a642d1680c40c410300c0c1100c1c1c0c005a01e607840d41c410701ca01c03c400074014a11805008003003000080c0e22070250781c1162411100308200005115207940f549208107040e03504010250104401100c45401c107405003098103154800040d0001c240c031088541e10309000500400003001030507145015000b4100305000c0e1200b0704402c044101011600e1004140120301181d201d2404000b4084901500341d400182d001060000d4501640000c07081c603800c0c00703207911441c003081c65030840c55081001c1d91450011601102d103440100c001103079983d0002d100f12520507041c840d40c02c1c040c0c01d441c010030100b03c5d40501501e07150310454040082242d40000b042d90041014400e10603071442c1000003c21900381c54072050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 120789703 1250 120788453 120788497
    0x316030b22060b030411100903060c0c0b060d0b07050c01060b0705010905010605011103040e130506090105060307090c080f2a031b07020d0b0c0c0d0801090501080c01020a060e010908 80
    0x6507042030f40300002d050000d10030000824070071400b4443c4070f042150b84665030511100c060324a60110380000d0010381c40c0406071410340e504440c102d60700038051640c01600d0743d26030080221414400d10300030110100b14000c1803025014201411400c00f603a0700101d0031a441d100303005c10720703080b0580548560791128020020b0045c01e10500b40940703420b1031301340000740e29000e605541303100301e10508440e2150840001c0340b20000400b9101e56541c00420340b200c0f800c044410314040e00050b140725200c0e00414200152500040c4140000823039183c035001c0503903550240d48440224000c007202054000b41d43c0d244100642c1a44041c0d0800d604000192a41042c101e01903865400da800d00c995084104240d2000d81d842003540d0140340e910003620711866868607000c1c641030003050a44c6210b886426424603105401580301410b884c0307512030411050380e8a2042d03d41e143c8942101d24096041190288003051240d04842c282c4800100042001c1582e540c402c010303980300650b580e00c0041114000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 120790953 1250 120789703 120789769
    0x904030e10021b04270611030a0c0306060e01091211090c030709050303040513050403090e07020304090e0109020a06080c0403050625030b010f030f061a19080405030316030b 76
    0x85440001510b0410001740c501001d0701400040b8004080360b01941d549034000c00c40b19401c0100f031003081c5088241c40e030400740c158002401602600b440824100640030503d10b108081780030700b2640594411702035518040c01d028900c00e461005941b030301c40c600c481c03c80340d44803241018000c482c3d280390305030740e45000720f0000c280c0e00036500300350b03c00d4100b00702c00c200c19554070ba0381d2014035071407160010b4140c84038174090300e20301078680c8054403202052040000890300807010b00210307656040d040c003800007009800740c222580b036480250f20a00381e55043c00901d100743c0c0b020354400384510301c1074075040d280e845203403414001b181d9148002c1c0c41003001c81c01d0000526614180c110345414113001003040800082d060180261120b81095555505040c14115940002d001040422500e83d5118034242518995520034185000001c013001e4444003140e00c1414458801c94220010b1429512400425040c440e081010b070700c00c0686500a224076075882c05044140c00040d841a0b8560604102c40c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 120792203 1250 120790953 120790993
    0x40e01050f160804020a03030503090307050f1f0204050d080a140403060618050702060606031302120705010813050a030e04060e1501020d09050307091503050a0b1509070e0904030e1002 81
    0xc941c2c10490441d09110040c2c9403603c49000740d81d81403c00720f03103c1d9505500c8500c2c2d03001d2604050310070b101c2c24000311818030001c15412581c20b4142180b29240b5555014002a8070407071003000c1c0c000010140d00350206114602a0050562a140c450b0090400c103014134008d0300a90019500b56030754080c00c106413a00540c044900340b544c15800c1c0210700d412a006521450010001405610000006041e40c03074080800d1880c147d0017004191440344031101c0710307512110342c020940071500d20740200d00d0400703114000004407a4000d0003000f02300b00d1aa000c40e8034a0b0391200c426003050305c0d0900071401114083c61203104030840c4e00d40da003218140c007000900e061081c0ca010003e10980010034086604e003c9880e00540c3c100701d0700410b144164412446040c5044d500140c50b40c0a010040c104000340700d03201c5405540300e1889504629124001c00c80041000da03813080105003666540305c40c82c100140c8050380310780039040c030640302041e078800b06100ca80e0012200340141c102d19094440c100300c00c0b0b1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 120793453 1250 120792203 120792241
    0x206191205040b16050f0d060e180a060f0609020a050d0f05060d1e050102160501140105060301210804080c040501080d0503040b0a0b030d0905030c09061e040e01050f 73
    0x8001d000906080e15090740700c03400545100c0b8040145500d0310a1580544e045941141da1004259503c4142e444035100404403401044218001c410100706c00480c0c0f04071801034101a0005440b000c0015a0764400402114101018098882c0c00c001903c0c00365201500c0010495205c680d500e01d51104d46c0c90440b05113452000e199880c14042c400c0300c1e2a102038002d1016400760540b4140c0900a00d003601148086600030055800012040c00101e5400074542580d0700ca40001e1000c142801a2280b107a01c0901070a42c01560071300040180321881811003640c01d0420741c50502036171281d240c2000b642c0c0907401900e0241e002c40345411040c10944100e6004014501c050140c140d070002c4020306d5171001500180034a000400407a4592440c1d0744884c103000401001c039210000c0b0403201400f5503201c1d2040c18032a004400040781d50742060901c1500c1141d00030000d454103a403000a00c0d28050140c011960410b42d10051802009400d00c5654090704020b40c0d89995490700c614810086203000e1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 120794703 1250 120793453 120793487
    0x3030705031003122f06060f150310030209010e010612050a1b0905210304060807110105091c020607020c060d0603150219052b2309060603030c0309040f09020619 71
    0x42410000743d170002c40e206402200403a005050110b07204006550141d02c00082c030880036000003808140704401c45140c3c100d038801d1f10400c40c681c0c1e071070510700c0c100c900912400c4081030000c1c0e400c4004210684c00203502103a08036001520301810242c046510207420542404100040350a020a140032070320b10103051103c5840e5006400c83d409865128010361062a00b070010030030100d00c5e05030280d180405c1c580c008030300802072480d113101050b80d00e1807000741e40c85052480c3c0480c0550070344082036180c0f08003503030740061403c4001030060043c182c0c4a042045401c0b544c1c0c80b4080002175036699220000d4119005c050385526000d100b4103400381c2c2c4929100c042c4482000b003821800d91003041d406400b4040140e00b1040c007105072000b0085d0500c00580c44070210601c094001d45001c1144290090070000110783c0c040e0354103000e041c1e5038451100181c4030307a4000d01c1810b55600e0030303420403c072802c0c07102000b15032441d0950100c0e085400c90344135005c07080444000804280c2d881002140d10200342 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 120795953 1250 120794703 120794777
    0xa0b040b0f060714030a2a020108060d230c041521050304090f05040302101e02030414010c020a050c0406032f1e030f07080303070503100312 62
    0x22001801c144003101c003090090030040b031048140450040b0141c0c034120745800366540c2d01e0814000030710ba00038a04646c031a0014000003044400741103454001900c0d41a152622161030304401c0005841003070304121204040d082d00b4015104822850010041440004000a60322001000191a0240d002c00303520100042c0c100319141c0464182140f0752000803030340e204601642482400d500c11600b04011581c20010b900507480c20300e900c501d2059000c1e50a64858174810103940055524a55071005058250092400820304a500840e0490b01c1134280402c0c2d0003501c1441d1307094415510b80d04025800144400302489024040040020b0003224108000c50031560365250100400100d03980d400314922540045d0011640c1e1b070300d0380c450000c3c50f02c90100104030324940806e0024600500901030440400c0d40301b40c00003058000c2c0c820080155003180c2d034203402111f0741d4000500c5040440c3c1580b00000100ea0505090000105240e4030001d40031040e03008030403106c03c000c4049050f0702c80 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 120797203 1250 120795953 120795971
    0x42303030c030a11070e1003021206010609060f11061305060c1207030b01121d0d02030306030318010c0c03120806030c0a0b030a02070b0a0e07080609060a1509140a0b04 74
    0x7000c01103032071202030b070704003038496107060841ca07807404845800c100b8004000c00e0900140c0c840c040a0102168802c8031f9000191144030500d42d03c032402071041c04085401d5107024070440f800383e141030017a40c1c41c0d880e02400320361184540514051044c2c905050001e009104071003403040a102c2c40380c2c04404001c0c05881c114900b048488800310003069501010313030314503030220560300c0b0703c40700380701d50902401c03e024480011030f40300544014082402800c4c07284d2182c4042860021003900d00c2050014080c6061000800036a801c410f15021958100800545034200250a040c0b140c0d019501411601784101180080075203503c1e405800c1501c40d511003560500d2035515901c051055805107840e582e00d0341ca865058034064010590020400d403003400c01c1100c1c0c2c110316803108041e02000400c8a40b410f680385286603d950b82903c6080d1240c000000142e01c00041d45c220910540a807901d068100c1d944062040884440d4101000305207540c40034002c04159a0160900c3c080e000c480030804420 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 120798453 1250 120797203 120797227
    0x10e010207060e130207140d0f210203100302030304140415050d020409050115060e03010507050a0504031101020c061606051602030d05060a120b240907030e0109050304230303 77
    0xc044038a8030712880081c00d0130480059141c069a041ca540b2003131108003101c0c0c1504142c0c4810703207440d03064001134101c00d5100105101e180c40c07100c04c031a209241000034490304889000b13540024503942800390075010000040e201003008000520740242e4684031a1041c3c02000240ca54030f0382001d89004070400140301c1541c4610024052039411900015100c129140440c050182c0e400100b095104085d400299207822440d4030200b124100c0081085946562054600380181c910010010b0814402440001c552620740e20344030384140101c501100c2d50341c0c002001c1780e20413280d2001141d140c80c540c0041040da4054075812540d080c04554000c904208000d40e41d020f000803a40c2d0072503c41011490704e807140c0c00d40c0009040b0034003403c80c1170445801c00700c441c1101603034160013640c602c80301820030180000e041e00010301d001b82050b00c41d8031144000c0b4090306c0180c0c03090185550791400c800005008200a000401d9034005881007a594061072003800400014218000d400402500078142 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 120799703 1250 120798453 120798467
    0x106030f050f07030203040c090510030203150727180b030618280507030b040c0f050f01030b010509040e060117150402090903070c0f1502010b0f1e04020304060b010e01020706 77
    0x500345113001612030303541e420f0000b40c02000d41c2c0100c2c107481c034000038040c0080030105c006007030300d00a40859003d02604100d1416111040394044000b440403196541900564043d49010314080d801540109480706c20100366404110403442201e699611032010038101802480d91101808590110761146514110386076591845004d104003c2c2641001041c00c8040741c620081e9002011600ca00c4e48078a000204820152800d486145c02c4810000300c0d840c0c445690700079100e015002600d814000780055001e4603c0701d03141d506002c82030055007019101d51007a40c039400b000301c2c02445903500d04200d2030304801030003441c540705412000310007041d44081c40721030750025410f42d48c0d80341c107950f0621600e0844c052071400505081c8040000038041c213102c0e8220303094807225905500f0510418005a0885503a030044540046444035601c03494500f815443c50000c03d03001e000c41c0030070740b0741e030000d41243d20444080310b800d95281c011030010350784504500110070b02030005007000ca00301100500f44c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 120800953 1250 120799703 120799711
    0xc06020718330b070f0209060d031413120507061103090109120809120f010b0616060b01090902122a030c0903151519060f0c080c03120106030f050f 65
    0x301250300c109040c0e4078801080b00014800c200a090f250f280e075180510300341c0c440801c145d01c01c4040c50041030462600640d12804140c2c56100c3c40721200300d40d0744281154111060070410551400b4001400d0441c5244100703803544500050544117050600203040d03e01e00d403c00c02d016901c00d03c070400f00d0b40d070026205000e83d1041c0c1c04000c1001c0061030003031002d01c14042860b130071034601d00400d40e01d90400100d0b0094400c03071b0402440f0004a5400b4800240220104822041d600389100004641c40e940301580226042c503040641c20b44805010b03050340d0083c600c140b4480020020030101c120b1002e00c111100d042d0780040c0d81c550000c096012818080508500c80300c000c0000d00d50709075603082041d1502c1098031412401a4908011544120b40f132580441e80181c40d0184111056034602d1011000e81d02e868440310344076445010304841c1c00c11210000c4414810802444410b44010130150000710440700d141c0300d203507040032001011381f103540e40c0d4282054100414044407101400c0c0b481c3d80 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 120802203 1250 120800953 120801011
    0x11060a0b030a08090d080f041401020c13020306041b0f090e070507120e04060b0705010b120304061d0409050d02210a05030a150b1b03130302100c0c06020718 69
    0xc0382d00c1040005e0b03100d584108000c181220001d04078241d8000480076204032444601000200c501e10801a0f0712140601c001d6544800c0007590110b00b4607070f40d4061604401e0191000a245820440d1128100b241940542c003213108035030761400c8075a01c6190b0b00040c2c4400003c40b105410080d0029082d8041e090b002000d14209032001e8241c18840e00c009004204000c1042c005e03180c0d1054150260390211a00795250350030202c0211060a00ba6043e2038848008002580f60038030300b00f012a454a070950800004e5410004006010755685c05003050890184002e0711a2520030746010b0315004203108481c001c54031807002c004c07400d40341c0010788122802c2401c00c01c1c1c0e666038a84122004017038400340810803a903151300114404200402901041c85404268403410403c070b1583c8be500e0150403c0922115842e49003480181030400541280f102c050915030a2941c1603551004a210702e81c10000c01a0301c039044c2045488080a90a60b440380c0c141c004100041000980b03c03042c04004e240c0181d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 120803453 1250 120802203 120802207
    0x91503110c030d1a0303270402041d09070f0f090b011b030215010501050403050601050409020628080f07050306090c09030a03020c0901080105010609120c0f0611060a0b030a08 77
    0x50102900044035000d60769501580d0307a810303410b144240140051407420303666900341490150941000002c0707070b810b80000b01d0614804428401040a83d0010203c6290000d0b0280030008403d80e00d60b480e081100a546807031481850006022841c08601e64000050002400c2041101050882c4c0003400d0302d0400f8408540c02c03c1c240300694440d40c10080001420108601030b02c00c0c0b59000c180e013400c1210040e0200385ca40d036680011070701030045010140c040d411220040110b49443d43c45020120b1000e49041d04004850310200d05000324070f00700780d68441d0a0503244180070b0f4011310050740720380c8880f2008a24202068010254003000300b01900488260001c0740d0f000e00310a06403022504001d0803190316401c1450700079110ba4041e14618000e03c2d05000208910350103001c0c940c142e590300d82c0c80c410020f24050368240b106c01c500105440302e08548002180700130710b440301c1d0300c064001034640084510031a69218030b0000300400384441d032443c1c12007034491680c0c04a009009541c02240d855 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 120804703 1250 120803453 120803471
    0xf030f151804021c030507062412110604030b100608130303051306020d0f0f0c020d1d030706030c02060901060302210708030c0708280f0f020a08031306091503 70
    0x9103080000040c000500e0113420141810554048010704003a1b1245500744150240301d460401c0c982c020440c107010340000d1708030620040720711820000d8014040e0310540c00b4440f441010030416030041d0401d4840c06c0303403c001c010501400c1000030006010a00e42265907240240740103072046010b0b94020300309a20b030b00100c0d0101800b0b16421a94a82040045568080480c1140000c140520120b6030580c1442c00c034150302c42c0e00e1320441d0001c5104d82c02a10041440a40484014030f0400704240440360782100c030440354800f0041b00025203456140000c000102000103490140c2c024200d5603181c2c102003080c00183c48641584103e8418103046800345138408811038200700c00313900030360306034032003c60395071404400010103004031088a000d690b040082e80d44420810715000b030b49c4451001110001000003401c62895405045c0201a40e8100810725800504941c0e91a0310401c000d0b4070201d0968031340312501c0d080d10002d181a007441c60703100c2d180000c50a901840b81441c4420715544000c49 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 120805953 1250 120804703 120804709
    0x602060420063603060903040e060a03080c03070c140a05040b180f0105090708010303091208040308070b0406051f050d030215010e0a06171c0210020f030f15180402 72
    0x92180e080c030400752101450221441e103965101840040004200e080e0b004061604001c6482d41c045d1006c080650718050600d11500c42c0c0c1a0040d002d250000364030b01c000004240800060800108180043c5076074182e5030802d112000c0e20340e0080301d60301800145104190352030707141150880b07405443c049400b42148000a501c03040980c2d4405140e807019040045c210780f14410780d41620f0044034100302c1a00d5215080321500ba0900000b400f082d025017050048210310754004a03924882c00840e89019204e558a42150f0841c3d00c048034500200380a000800000c0d0041c55400803071340b210b8200c9040013503607000d0990550b2250034015221045004207061081c45060100921403100508030359440c82000c101040850700526490f1a29002140030b4030017000e45044c40740c50100801d1540402410503211442414800341907210b9002125004000ca0000d4800344800c0e0201a071a03250401d00c2d5000d6003002020300201240d15242c541c0f0542e5901e01882054403400180307031441d9550302c04 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 120807203 1250 120805953 120805957
    0x609040902030c040e03070507080c012a0812060909010e03040b090406080a0f1208010f35070302041407170a090203070909020f03011505010c030201110409090c060206042006 77
    0xf0030303001414060680d042060000c02009124400d40440d00d80c240d07207180360354030784240e81040c0380002c0c2034510450030b10481291480c481d65000100541820140d5255402507101d241c44002c074805200c20070555140c504403180e402403201000b071110305c2100007010380f01d128900070702600240128403120b080e1141d5003c00090026001282e107407070101d081280342428050401c0361007045103014480a41c0c41514554101d41111103880c02e82400c0006504010030704080210060381d041550012600c225285040c0000000020703145450541c0180801d68105100c4041a80c0041e020f20411960140100b82c2c110b12100c80318015858011080005d420458000380d45403140301070104500146034000d1302150320071540300c3d0300a18581d0605091350460031403094481e102d403104004550245400c61701c86440b9100010f000002000240660341254200c410382687e10000c1d0000c0081700c4040c0c002030035180c0010286441c00c1e43c2c46102202c0e03000900907480a07904030340b00140d00c400c82 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 120808453 1250 120807203 120807223
    0x327060f0c0c010e0102070605100906050904020f130507200105010f090203090a0b04200306090d0f030f111905030c0906070606032a0b070f1b05090405031305040209060904090203 79
    0x81d540c54407141402405050181e942e90780c1c90030010ac0004900049101d110116103002c0c015a0580c0d44075000c104101ba0790a4800344c0046460220001c3c02d101c0748109032050000c0d80b5282603c51040008010004a542010580d42c0c074100060011010740d0788003100b1143c100401581d20340c1d40948840c240164880000e10100c514004d11040080c00040d410b05240701c8280c1c40021001d0303c040542c1e0b9201170f00c80216035048039160f02e000318419241180c41014271f08021a42c41e866080c44c4085919072084070042c0d410105031240f191002c4140455680b1517440d010b03003107003852341e103140603407141c00c20300c40c401d100000f0303000c0c1000016000760f00115000101c50120108900342d0b010314030010480c005d0b038a150540003280d00001d1405803402e440d0040001e140301c4000781c1d2011b40c10f052130880c4120407508020f000456603501801c03d4490340c4140003460b203c40003140d514010f48026000740c0d200d14010700c000c901d60340320b50042c0e503940c3c40d0480b004038100c4002d002290501160f05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 120809703 1250 120808453 120808481
    0x6090908180307080d020304081c0f030b1c0506040501050709030b07050705070e0703020a140a090603020c0a0b040302030a020c01030606050703050304112805060a090513020d020327060f0c0c01 85
    0x1171a03407890190084050f000b01d820600a407084610701c81054401d03405400c21050200d8900d02c44a022244654031407084803001412250b60303d6880d6240d16a0fa85400d40110f6840c0d0089040000304002070107000e80004041c103128520500f959152a04101c009142008114000c500c50043c400c040010b48000c006d0504d01b00041d0920140080182d0b00030b4648074013091190b488900e421860344116140000507a440d92915400c010b0124041e60110075052400c2c418820300d40f011400d802002400b80f44640c00640c1c2d1070f81610b0380a81810101c045c0c043c103252800804100d540e4022044428103945031400b1640d079560741c98803c0c00c0f506084006600310220106080c40ca0740d04292500896400902034a24180d54500704140c510401e141d98001444905007082282403e00625040300f408800c00360505641950500407a0005c0703540c01007040b0208100b44440356101d00e07a1400c0300809002c0c00035403520740700028034414040c0c0160b0301440c000a800e0800f40c820f5000d905603100300c3d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 120810953 1250 120809703 120809713
    0x228030212040b01030b180d0e0409020301020a0c02150408030307082706010501141602010f09080a06020909010803070f0b15030f07030303051303120216020619030609090818030708 80
    0x3d0400418500f400d00044400240c61070100f480d65408401016418100d42c00519141508800c2100c1c1103920900943c0c010f030301d5224032001aa401c0c0082c00e130034042c2d0303a5020322200701801040349010b0a1b0034030703d1007543c04010511000d0350203c104c1f544209107081400c0707261100440c0362100c0104000e106890285420010050f91000c07940354100c0303e090b82c500c1051902110154291f1050351842016032010307884400c010350203416455044e40039411701c07007101d5030f07100143d60030010307150011591242c3c0059034031b11518006210714058264003009504000c000c0c0e5407074180d40c2d10030b41c014184410074400580d05528000401b001c140c800ba0a560801d0b4a1446003956425113000860120382003400054110785450302c4900d0f0755403d951610994001e05113404000c0d03001c944003c0030301406607140f4004da2564001850b40b186c0c1a44014103080c0e28a20080031038946800509101d421302c0c071228003280781030043d281c440074032803411615141c50100091400603d41d2105d8028010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 120812203 1250 120810953 120810961
    0x23070f0f06051f08062d070c1e240204080304031407090b0a091e0204150f0e010e04050604090609050313120206040b180310021c0228030212 62
    0x42070b0082030081c18440244100900390141800b801d402c40d0044001c10b0b4010070000b00b140461640c14110740344032004850607001d1140d00011030070021601000032540914000d0304010308074150501c10309040410701a003035856500c00005421112a5000811822416501d40501541160300a025070021207548603583c0c603202042c05450008154107001c0d02c14002580c0e412402080304094009024000d507038203000d07800005240c40c1105510300941d00410b80500210f0348000d00c050560078010b6200001c410000404056100b0552000c00054481c80708069810142c82a003020080341c0104e415585c010201d030042c440b000307001e011541000c2c4002c0c14860040001d10419580c3c440710601c80e9204c002c0001200f0916200035000f5108100c01c000d0300c40064050002540100c0001c001d1105c2c000c0000e217841c41c40b8101c0d5000c2640003030291241c1e4102c1840142545884205504100120200054901c0d00da03482d482c10103034040c50009040c1c800d41c110340c0d10b001c907a030000c4880d0070 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 120813453 1250 120812203 120812213
    0x1031e020d0f0b040c08040209190908070b0711060a09020d02030a210801060512091f0e010c030612060b0a0905010305150906060a09180c03080306030d23070f0f 71
    0x482c4a00c1a585141201d11040b506250043c90810040364466035025111982446640c0000402c1d4015110360f8852554018004d030040c62070701c9024400c060b8403199107041810302c0c0303040500001e06200d072442390200848004502c0f564090742680c0700040702a000d0010411041c074100c0001e62500541c01c4a000304440c800c07040001050f240e200220440c4500016100d8400a003d0400850810301c08071b480403071300c2040c0e04c0d401107400094a01c294041c002a06001405405c030f07003092a00d8036543d02604c1030910641400e1000c5203130038800c0d90311f04045d043e4a800e0740d0760080c1513561030740b008c480c0984440c1c1001004040340e103410405980d4904115440d5401010341342c52002c08140030801c0e005000442c10301440e001804042603e2910300010002c01d468101000310341103130601100825888181c400007140208840395032850014205401c0185a42124050100743d0020704070302d4502101c0611108180010030742c1d0303569141416403810b1000c40005000381212841c80003005 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 120814703 1250 120813453 120813461
    0xf1210090c0e0c250602030906160e060304021915020a02010f0801180c0e1309020f0d081b01060506041d0c16030804060f050103030804050705091501031e020d 70
    0x2900403000c007900c0e07903100c1940030141402a103a85240000c00d02c10f0381000e91141d1544200c80c1c0000c104090300455540c1d540003681c004407006911500000e040043e0030303480e2a030001152541e860411420903020f0001f403110b000141020f4040d0300d181141c0d0340070000c04c1595078003a003c41d404440d20121540c40081d41e400310310b20100d0024a1410742440510300600710181030302c1c08142100c406044511024008000405c00401001403580500c18940c0b02c1042d0017840c051031050104590300c2c580148000d505031800103a015280300c41c850f001080c0c000341a00c50341024444408865403800314864090000c9030011544070100081c005040d2044001c8140c1071005041c8920326070b0307180070030640b55028180c0030000d444020080ca1b8002031060340015401403040100140b49044a0480707400c881c402d800031030200b1503000512050007402c0154000a150440b101401c600d072148000703201d15800c0f00301505140e02c800030806000190003401e500140c05c10030454840b0700c403800c000058 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 120815953 1250 120814703 120814721
    0x20a0b0408120f09040b15030106030b030111090904081b150412030c020309101403090606120c0102030a080403023a02010b0d080a09120b0402130207020a050f1210 72
    0x1d442004110140c0c040101c041c0d8168010740c1d8081420315880400b800043c08a4244a99000800789000d5aa4040072000303140680565500043c000401205040c21500398410b400342c4c450050020034031f169901620607521035401892552101001d07600f0b1000d24181c0c4c5013410744d9005442e2a200313580444d2002c0c07881180907010343c2c40001c641b04410782c12200a0301c1c1000043c3c00070002041641400d400c07005241031186410f190000420b9402099908103841132981a0450b80c02c0c40742615040f0701b4140b000c0140005031407851078441c0007031358074400c52010405119021000800749802449820082095011078100042c50680001c0b45404400c1c113810314150400079040c4840e02c1403080e0448220050b0651118035001d4132008010340044542070200646424045041c031000c0165840c1c1e0361080c030a842d078a0409104101c41d500d0314220b00c0300780b80c2c414072041016a07a0035040104079107007a40c003500114001030100c0c0c071003114030030b40c5000f0f0b200710041c480410009074800100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 120817203 1250 120815953 120815969
    0xc0a080a030b0108060306010320120c030705100c0b070c1406010e0115051e0c07030507030b07050913050606090604080f121e0913110a09080606030d0302030c0403020a0b04 76
    0x20351102c800040d2104c0d2402c1d200d031601341e8448401480064012881104242e852001031b00c042114000000c04003440501034500b5500401c00b00819400c003002518081e010882e80c0c1d104900d030b003010041c0b001d030340310390060600a14030300480d1056025003d41c0c4d00542c0c0128a40000686400780d40f6580e160a00c6003058a031500c50000800e948a005281c0b601c1409503030b41460702c80741c100c030451101d500001d40c0e41c2094003000700800c108000c01142c4000c1d07105d035014040040c554104000b914100404c40014003d0800507041c10b80d541031503410001d1007840000a59891b4036010401034090030f1078803500f01302e00103000302d0003000c0091440e03a00d18090040701e4030006208500f00150040346000d4041c1070703281c81c406100c0c5203042c0203400000000380c114820351007041d43c3e0b00c041d200307840c0c1424403d510006028216a6018005001034185c1034020482400c1080110f86d488503c624031600f0182c2c040049003071a43c0d90022140259001895a0029900d80c200047c89032300038490494 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 120818453 1250 120817203 120817211
    0x20d111305040c0507061a06040608150603190509011d010e0f390603070905031e070b0d090f11130b010c08090d05161a0f0406050f0c0a080a03 63
    0x5002d1a040c0190b103891105a541c050805829607a904090900107a042d540280c5581282c15152140000b0b0001028265101440c0303041c030240d485408100c0000980c081c0c0000c1013000f2100e008800d1000c004600d900c00007403543e55074001580148800420b444008156020301403e0f050150000081d034080c140039144144541e000c00c550b01d050803c50702c44101c0024102c825054585a003c008144040d40081e10741200040081d0a903402200c907038002c0f8000a074288201e04082000c0c024044158100044803013000d102e03d41d81c0c1c0c07000e120390540b6070f1000030800c08801094000144640e40590303010200c20b00c62503d44510381219060314003403254080c0508075581540103803900941c040c2c44100002049468099040e40294900d58000c00c5080240300091401c011030140c8420140710000c9050070070340d0702622560301ea86d59480c40181484403040081d480e00884044030500d0034269503a000c0f90b8290407207809164600344060007141180ca051114480c020070081a0a940800c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 120819703 1250 120818453 120818459
    0xc0504050f0108040f020409021201051e130f0b060406080a080a0206071403060913050a0f02010f0c11040207060e060406020403150c0206180f16081b10030b0103020d1113 75
    0x440440f000c68016001d00001c10281d400750421340d002d610220700140c070010700300300d0f1442d0042c29584180c031144020b814103005140e0881d0414400c80d0002d502c001602c55508071900c49003052445414082e00602c00040070402c40c1e0390320b6000800400b098402d503800d441c0641012021074001d500e100c40907010f002e0005865a100f005241e4903580b0350a072650031a110003041c025000d07001481c01000410340c19070100031640812020f1480c6109e80c00c5810740e400749100051201c92032110b044148402240d01c1000101402084410386805403801a00c454490415001030305100d0b000f40342e64000d01c3c0a01c000d00c541c9400501c240c0340a2400c00a010740c0b0403008400301c43c1c409082c280140c00c00c1340421110352111204580002c1441c003241c8001c02042e034098207000d50015222100c1c401d411080001c3c941c144042400700d0344007045480384100b9440031500742d0003819911070402d079a468003004541c3c001da06403074180e0403c0300d00704030003024030b05202221350000701021103414401e6000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 120820953 1250 120819703 120819707
    0x270103060e0708100c031e0b0103060506091008090a1406010801110a050304020613170705011101061202010c030c05010c091d0606160206090d03030902010813080406050c030c010c0504050f01 84
    0x2000840d00c0c01c100a00b0203d160313144213070003000d4500d4074000301078883c41c1070040590300d0303030f41148080072503080040d10000c081c0003d41180c07003940c8500e0183c0070902400855540b507407064144402e0714242a6901d5541070346d0b290903e14040b100401064400100d540c48610024166040c0e1300803030300800c00400405036a03032840c02464241c400249040000600500382240940034200001c0301038070b580e64030380f032954a0756202035924582e150311019017000550391021801c00f0052495000300411030510300c80ba040d9512689010f81030150240020341003612a8074100041da0f00300f002007012009980000700030003024450341c5402031003c81d540400b0203e031181e01c0e00034400104040e01e00f941c1201300181d4941d9200c1e00342c0c0d00c128180980c4285484450700418202c0c400d540c00070300c00c0300c40e10000d80500000341aa00c90141880d00f0540054103650440f03090342c1c0c8030700304240c80e210700110040ca90f21400d07180180700c0d402e141c48450419000f8010301b00b50f8500320340700c400000d0b0070001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 120822203 1250 120820953 120820963
    0xf0a0806092203140c0f03031905040807080705150106021e06101a040b0c010203041a13300c03020d0e091308070b1906050d03020607030b270103060e 66
    0x522802082e0854064001034014180c06540c490603007401d60500f01c40008079814400341c1c0321800a2034100104005080f80c400d10b08810000c150340d0304120310309207500c031030300d03d4000d074403006000390300015603801070050810102c0e400c3e8400903040419981c4803503009494000c0400e1401d441d400300300c0c0d240c50300c01012403024402c03010940032549284c501905d580050324640e00518004404002c0851070414040003841604400ea00140c0d40c1e060616211000402e001483c4034100240c4050044807481c0c2c02041502c5500700458035200d582140400c19455141000607440205100411000e00e400540c00060b1a0003502a1820000c24400a44d01051084c809651000780c050029407080400c2d00d06200560185005900700070075982d03003240c0881e0544041c1a1035600c3c202e1b0b8058454180a108042c0000399169401079125650103561200c026000d8001d00da1240410402511005c00450002c00d0054400c2e581400600030072074400301c01e020668580e0b0a03e040c581e94a540068 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 120823453 1250 120822203 120822241
    0xa090c03111003143616090e0607052101081507031b182d140d02090411060409020703112b0314010b1b0c22020f0a080609 54
    0x1c400c00596171107800c10003842541140529591700d40100c03918020000f0780c6022034070880d10f40204014070305407613290398882183d403203140c41c68201840c032440d40d0310114426410400301d0400756142c1c50f141c2e03030a1100c2c2805000c200041d10307198000046044001416801c45408030030b032040c1c680c0b00e00340114280d502200c0c180c20702300180d004003d81117102c0c4a40d0711880c0c43c00300e28406401c0e01ca02030040c18582420384000003100d541190b1281b50b01c01000c1000404044000c1c60728148070f035011404590013103902038491899440058144000c620348501500d00041039140e0382c2c1c2c5c8510700c85000350010074090700051041251107602c807200088503404a58000d01c01d40000c0100880b094850b004102e1402c109a19440b010f02440405074035140a8080d003a4400d0310b403003c41011480d080440b40f0801c4036a44031489a100b035131901d0620510385481c0d415110125104a80803a001c0d00c0f83e5441019003060005070203034080c2d030129942d03002d0a021108400381d0344a6581042481c861a1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 120824703 1250 120823453 120823481
    0x2090a110405010e0d0b04030e09090601230105090307030318080313050402030c130303120509010c0801060e0d080d06050406050907051603110a060603120c0f0204050a090c03111003 80
    0x205209541c0650514081484000e2881002485c1590b40c884108000c0d10100c0c04200300303040c05015850b0801d00740b9404101c0b54010b0800d507240c0500e04105001c07000300071034814020003185080e80d10070707011034410041c0602115401540e0b80740c0140108145061520b907914428400314640d60080100c501040382d0405000015041004100080d84007502042c0902005c010500442d405a92610001c42c00703503c89220341811a404181a100000d020900b5649442105603210340c110004505507052443d0941c0d1001c03032a4003082c1003107107402c3e015251110110b00c10100d0344407504540107480d03003981d050021950b00c0c03080c403c40d584250b60400204405000b145048a1b92a0460080380d02074501102221842c0740000e05060801c0001d4a1040d00d542c0280284000c3c6c0c9038001c103400c020301c0c11048810340303600ca108020650403030081c4165250004122031284907001046065041044080f4041d500c2c81d1070900c100303001c0382c2c26001d065216040e0030458028803d50504003100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 120825953 1250 120824703 120824707
    0x6020a052a0414060a05180606031e13050c09010e0f0405010237031104031103010b1c03020c0a0602071a04080105240603060901091509020f0c01150602030703110c030d03050402090a11 81
    0x234820448d00d9000103107800010304030715018810146001000e58000e0486600400c07030440341c0c1c10400d09003100d0824850050148a004100203400c080301e0652001c0305c032440d1100d0761214545180603200e1145030840c4c8019800302c5007180644602c1445404020003032016a02046074000d80595054010403481c0000911040022030005403020900b11030060002800303100e8207000a00442e51448500443c550050600c0101901000060a164400c413848003c1500e42130b0002e540321f1190003450100c508104078403144040355002e0300c002e40390f803000a000030f01d0f081000404110303c0103a561011044190740c0c0d00300e0304001c004c481c0039001c0030b054a81207030f0070200c07640c02a1803411491710b07100c071180f40c0000d0700c07031800c0c8068145a1284a0190b40c1c1c0c0b880c007a1424251103140c0f800d04c3d130b41d0340c5c0104204103154000048411590340342c28444246221180101e04104c2c02e86046074041c0a04201c3e00e602540c541e00651203a4421698030b01d445e19041c000904451007001c07032804260701 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 120827203 1250 120825953 120825961
    0x9060a0807060c11090106051b01111c060f0b070507140102030d1e09060608070b0301300b0901020a090e070c0305030916090f050106020a052a0414060a0518 69
    0x1040d40b4107040f46000b805030062840c140e80214140302005d80c803101c00290042200721801084c4940e04100d00c0b0740710000d200d0034041460808492291595402600c00389100740c140744c4200b43c00180091651040000d006559540051919845018202c41a006419003c0303069466981660940c3c201a0b00a606210030788403001c00400c651100b00d0912a00345080300400782040c042e0525003440b070840803038650714001c003d5180c24007e4119201c400818001400301c41b5024180c4880409080020501040c0084c401c5004011604014012860940401c60f210f10150014008034000d40d480d150015601d03005005400e50640300c032400280d0600320180424400c201942c8c0054864090301e00791760210100e299107101540c8505801ca071910b0414074a9440c40c0701d201d004000b1800504006541c580d02c3c01d0725000c401c0107104c07041581c0c003d4200ca0003003e6960a00504016004000440101f1400c1900000480e049072107118202008101740c28a0380380810090100802503501e626 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 120828453 1250 120827203 120827207
    0x31b09030b040303110a0e1e0f130e101e060602151005030a0609050c0603010302090c0705030d090302030d0b030d1718150403030c080c0f0304052a09060a080706 71
    0x60280040e0201358445a61052880c001401050280c5d01500c60440308000802800f42c0503810101010850001c90900a910f842d600c280b04028401210711512003201140c86000800d402080449a4400c0308845404094203038414003165403140500d00103110b01081e05001d40d2403034000c01d0010307081a40204156261012036980100e048402540344548500c0403900d0003114541c01e45d00b2588600300c0e041808001e0203c91410b80703041d24844d01d15030464000c00c4950f40301403c10950a1800584841441800c0c01900c0c8544014003050050701d52038200251b030798000c2d0000600c19450071864482928001410016480660301d4103d04120860910007100c00c009140d0450388807085c2200030010014804566182c824010b11001d50a250a00404907003c2080820030301c88614140008170060009891581c202d80c0000741d92aa00c3e490424201521522a03500c02017410342c907100581207500300e0030342c0c5403025a43c0080d180c1d40d0700c08010030706455114402c42500182c2040c4138141c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 120829703 1250 120828453 120828473
    0xe09210406090e0403030b030d090f0e070905130204050a260f0d0f0201060503160f0807140f010e09090f010b04021201060c050f060f010f0605070209060f04061205030901031b0903 79
    0x140681000a8013420394004a070426218445940002b5440030040c410014400c00100c041c02030305092101d949040c14010b00341d50194002d01740f10700d200560b90102040d003034045034041c0c4400740c0341601c0150359403040c2d8402551021107982072548a207104120f4500015040041c1003048001c020501400f902130301ca16444515500c210b54940c00d003c191903d08001540c0d40e072050b50749840002e490301c031101022428641100c003994001c01d9003007151560842194400b25400c40d0b508404600319001030300d206882c4001113030000210000c0019a50012a958101e811000000c2c050040319000308800c034481e0001c255100904180180b010910a84802e13440500c110b086034484c10a40304950700e002011510051500807540040c440d120000b6070b40d10060143d410b00074240012640080c52003c1c00529042c000e01c45000c0c803144607519500004010840140c42da04148810700f0161349960228070040c1c0440e0500020782d1f4110294400583d42480f2a52481f03096809c56035990880 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 120830953 1250 120829703 120829711
    0x7031113090506030307020301060b03040308070f020a15060509040302100b040c05031504020c0610031e0203030a180b0a030e06100b030a0506030a150b130c0f05130e09210406090e 79
    0x345c4800e104a00058600744204009810424445500da242500d402080c039080200303a1020400100c0d103c0701d2954001602010050344100c3c1c1c80034415000c0314640c000e02c84c0d0780c03001d0391100c0031a043c00141900480c10310b14511030f00505110030447d41051006585e941040f000000b5020400150304d03003a0403964030107000c0002c1001d0710f4801844001c0e032800070140c036500710b07800b0780c800d0070070070480d000045889080600884070321101c01500004d84a00a841156043c001380c100c502c00d5a04001403101c018264010160742c91321f45503a0018000c14440e0084451841400301060b0002031280d0341d101200e01041c0151b256030303580441d89020308000342000d5014400d0075448030000e00011500c2c065982e00b50701c0043c0c049003034000c01598007400d8045154840c03510680450207903018492400728100d500300359035160644034910b00d907e94160301c00d0750010501d40031311452030381c00725041d20b4010030030b110560400344034884410341788180d204510221319188020000070340320014407580 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 120832203 1250 120830953 120830959
    0x3160c0507151d03010b130e0c0a0807080606090603070b0d020d090b04021f09090b060c07030809090117190206090409123b13060b0307031113090506 66
    0x35640d56040e1102c080004500300c0c0125a40d11000c1e01000e422204018050800710001d020000d68080400c080c044a501201f1803070303485058248610108010402001c08040c00642140b5580d0b29217071b403194030501a5403500d02681010910398034080d01c084cc0204001070180c088189080502c1c221035115449a1f54a580c09100b062203c1d401c1b44684a42c4900903108a0043e00d014410014004070320700c56004d15070200c0070148280c42d80017102205030742c4807900000e101e664800c0000d10754020390a8040091051040c04820071503020007a00c0045420f48030b44117140d0322015035251140a007110190309500c4000c619281c5c1c56082c110b81242c41c0058802382c5482146404203055032030302e80081d207400007846501e440c01503108040040e040b5001941440040c002e81521100801e011203400e03001c0e5500c803107001c103507507804101120080d211000b000010384e160080a129082281c404c40807a141140301c8056408800489200340e40150703007458400d0500c3d0b11140203150203044250 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 120833453 1250 120832203 120832213
    0xa0210081906060c0201170403121503050a061b050c0d051605010e0a050c06090d061d031207080601050711040f020408030a02031e0a0207030f030c120f030e0303160c05 74
    0x588807070a1090070040c04059450640e101c8036070002406210404045803280b000383c00400020903070010481001700040790f030114285942d4000c8103000b40158001912500444134140e04200595012101c3d0f0003840a076520b020762082003c0e1080c2c080c00c001c4100340c0d00130024030183e1038440d45c014001004529410050415280c481600711030076016009669030090090005124040002030818082121210b00e04140e40010880c09101c2030002041c07240c65440b0707207000102c2c010a0f02121071082088a498840d00f030a401d405100a0b10f25001150004000c20b186500c1041120b101c9a00504420b01c3e0405241c02c0c40007d2460a0034104896402c1c4000b04c0d40480c24030040800c1d2113541d004688800a100d026124581e000e000e103200d800b02048900701c40364000c10668112034000600c2a401c21090400703039094058032000400340c010b03001c1114989030308004207200d8590340d40d40c00c110414a00145555a1205480300504590002c008100580c49110010f45107449003003514 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 120834703 1250 120833453 120833491
    0x50a03020904060f080a05010509070b0417031b0d0e010302030609060904051e01021c09020306010b0310080102030703020a020c01092304060902040602060402100504060e06031f0b09040e0a021008 86
    0x15010b072401750050001034004201d0a8240482401100e0300506050090115180360203a00da40030b20440c4a4481d00c60758154030b0104021084c005e44859206085407034025400105550f42c540c5407083e01e020104008800151a551091081ea0b120306030290503080c06484030780400060620040c001c0f111031203140b0740e005680800a44001304010306000250b11004260b0a601039a0380b09454103e229240681c0040583c0d00060070340c2c110340c4e401240303960b00e44402100f110400c1850300960700560000040c0405164154001e00a01e803443e802d4031300d000707104401111891101d01c10210550701415110b00c06032090f0322024a000c000034400180700d0340c2c644004d401e0746c00642c0300d100543c21034801c01065083c810901030b500d484c0362814600d403d0a092020f8503800300350414901451021000500041c2207014440c403801101014001c007955a0b50504816408060b40c14085c5050030308100e0190400030307a2010080d4001e240b580034011141d0100c400b07480044c103485102d1040e000803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 120835953 1250 120834703 120834719
    0x1b140a140303090f0f060703110c0706020703030e061e180d0b01030b09060c03010e0a0204030b040b060406050d021309081306020d030c0516110102010f020a0503040506090102040501050a0302090406 87
    0xa002031108000c0034607100e203400300615003000d813251041ca426800100800807a144041200b5038440080c6c10f00140484032110303280a58024500c0d151030b540704104004c5800b40d0000780290480b4800d558455032141c00000b440941e000302400002015542001c4810011102d0090409144000410754184170b000c0c00044e00a4607894090315030501000040c81446400f00005a004500c0c40091a1904192a010030a480148100803d04100c100443c034283c41d160100c50056410803c107283c41d0502e401d00c21200c11080c0c4845218a150900018007810094142d022964000340892100034a0b00780382c1c0c000c0c14140f101101d001c141084010440340818801002030901540100356041440310040d0482e0348100355042844003d0042c454007003843c0d0710003e821031b0b00c410f080c0060a02d002c0140e02610100b40c6500b403036400492551216135000001e548240c2c001c0044032515141c6903865800c138403881c0190f50020750208442c21005000750001c10170030790081c0c00004c80704d40e12605 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 120837203 1250 120835953 120835973
    0x30203090405040215070c090606080c0403110a03080301080616030e100b0f03030c0706020c0906101808030f0a090b09181801111c0e0c040c05090307060309121b140a 73
    0x80341c0d815247e00c402e20140005101e084090a40d0307062218050601c542e01c4100c5000e6840010421400203038904250344800f6500030083d5800740445840b561508c540315140c1804564800c05100d20703441200040d4800d016001015040d83c0280003c8160360780090044d010001d24107400803940e01c04001c2d0f0b910108010301020180002030601e450401c0c000a041100303000e01148038000d00024054941d5a604905441c40b42505104480c1000d00404100707003055644000240d0002240095510b80100c0041c4010b02190762660000e503181d005400250203803011142e000003940304004c5468400f9a1441d411204400d02d41081c13515006569095899024ac40048140d000ca20301040603d1450303541803000321150705007c40340191060035624941c41020a101c0c903120004640b400780601c08882c0030324405001d540c10180c0b00c00c8042c0c06044004000c8a0103000700300d000e01010f20070300c1d803008010000c01c00c0000e0ba0003d6100c800c05170088030382102c6180a1008200005850405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 120838453 1250 120837203 120837217
    0x3090203030409051b07020a0b22240206150d0309030501061203080a0e10110d1b11030c30070308040b010f050f0405070c0c060c061107030203090405040215 69
    0x10f0081403914024840003214000300b0130308581401c081c001d40006a450104c1641075030200b5406545808001240701c0316110500d10350100e0b0b4407500300201f03403d10400034880c9240558503c0b02c0803141c2801041343c1d950ba040b200e000410400c241d0700c3e4003500d4618845441d860180c85c01e20080c50b202c1d242c0c3c0e400c64100d940000c8075412017061072400c15802610003179110000705070130400c060039111610b455200351031312800090340d595a0450440c42c03a00540703448041000040062515060110801c652445000c4010400d5004070f41da95450000803941c960248a0103031403000960400d0381c00c80600d10f03000f440d01e51800c4810907003200b4a90b019001140c0070341c0e200d00240c1050300305800b00b807006070040d00303081c41c10b62014011516504140d2528103000d0307800150954509408450107002d0700001000381e03042402c00140c603607010703056a80060044404001c407a210141c2c4100500c00d420006025030000d03c00140c01d860150b00487c5e01c1400a0070460071940c5404034250349a108003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 120839703 1250 120838453 120838469
    0x1707090603050a0e19080c0307032303010503120d02041a0a0306050105040b0f0310081e1b010804080a090b04060906020601090603020d08030408040e10360b01030902030304 76
    0x1002009403a41c180070345900140000420407070301004440450700d1300d08021428454040c00c4032680100301720710382101c400440080039070b911841107140080a505070603440f201060b04103401c40c0008900241100c0c12200000d00800e00361801041c847c1054001000103406103a00f8040001c0000042958100d0028140803d9603160600310014085504030341042c0d042181c207020a0100e88005400c036140843d0301030555407a03584402400c9141100340c0c00413a10b070b0086070040d00d840d4200c003d2a00a0131100d00c01d9400c5040d075441f2101c801306a0000c01400038806c000401e003ca0003035002000d0001e004d19101ca0f03803036103400c030400301d03680550b00107400524840c404004c4035506200b280e0140600103014800a491900054280c0c2c03134a1030046d1000c000007000c6820030400b0b10455004001c280c19540e020700d0008c0c501c501e00c9600c0d120306604100101c40ca420100c40414020b4403908903d06000c561a5580881034002c0c603424000d5418141c0da602010050703603080000d007000344030b10303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 120840953 1250 120839703 120839717
    0x30f0c020d032d05030a150b070b01061214010501050a0315170d0305061513030c180b01020616030c1b0b07021c0c06050403050405120109020906030a0f060c1707 71
    0x40808243c075020000603001040001098510030b0380d0110881e40c201500c1c0c240816800d15002040e00030101541c042c410455000486504004000350403e049a004d610703034a503400c488540b05010f0301c8541420703031110707440e100060040f0f60003200070300003c007060301c5c0020754194104d04424894040d42c0207003511a060440319020304600304000041031241d440c0a2150b42002c501291030b940400c10b2002c0641c034041200307078015440d03030281c40080d41c10481e15082150384550651603030218200c0b030340c0c915040c0041c403646540001062401a0154080404000340300380e0f040780245010351400c0c0c00c0001150047c080320007030800007a015401000d84040034101480302030302d00f00048000b03e62071540000c0307049030160040c000c1000c194001001144a50b0b03181390071100390ac995003041d5441141c0450150624205500050070301e407090703610411540303407003042551700d1b010b0050062041d01984114400070b5101e0700420011240e50400710301040001da10358a001c402124000001000303 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 120842203 1250 120840953 120840977
    0x403030b040c0e0f0d140601060507050118020f01030509071505090901050d081b100504050102120f13080903010609050403110d05040e0a0b03071e031b080a030f0c020d03 75
    0x1849400c5050b015800c010300d5001c0c407140030450303121058203018403a050100e030070400d0241122220030812142d009640031580c403454058016000340b5825906586482c6a42590301e4240107040c02041e00244400a00000c203c0110b002e4030004150b070605010b030303840000300410710852100003c0300c2c980720203403900150030500100c11416400305104020384507804005c114401b08990710780f0f20a180000948984100301403514a40545040d9040e04d0a020171041c020103502900f05004204120315098440180301c100903001a60b50b0302d62409040050f40015085a004042c1c04802030004599036689005450407900120fa007030300071901c1c458480807881824050b00a6071000e90508a013403d08200c3d0860520900034102c401c50740e03840f40101a255000c1100400400718412000c00e007043c11103c24008030382d184421184a120307683c0243d0041d0301c161055040d278032010001e25400000f41c8089501180c10078040d014001d26030540d0b405610703980003420f001400307500d41010780c1320 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 120843453 1250 120842203 120842209
    0xf06030509010207022101090c0e040b10080c041505040c2316030309030e0901090c020f010501050d0305071e060903080109050403020a0624090b01030606050c030915120403030b 78
    0x2000508003070859104103c0c41c00144c1e9000d80c0300d045c000d0010001315064180492941c010132007410050f1100b0714940c0002149540d103402184224807400503cbc0c0c1da515651aa503844460a028420b07158001410111803802c0c558490403200c030815111410080d500d0002c039007250841601c078000203401d000b26800407031541c2d200360008120384400318600b1050b500c8281140c1c0e582d4038000d04058030703440984249072080e802c004542c400285a40341300e507520300316400149680300852001d401f0780c560004241c00c06206940c12200c0c094103000d01c03683c89a07800c031070700c0d840480121000c1480da1038280224000d5109081180e225140008106202d0f050140500105920000103103081004000000354041203c001c1c141e40141c0202e20ba0910880940c10314112030390200783e0103844e03070b4001f4181c0c40c0b6811034070541e002a00c00300802502d030a0304407035911031200c0c072a405500c02c0100b000c0c5405c00e9850b144024000c0702c1407074280414488408190001178501b5000a5111031507003100349 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 120844703 1250 120843453 120843461
    0xc040302030705010c080403060504021305070c0c05040c0504030b0702121903050a0612020d151118030a0302030708030c09180a3c0e010e06040b06010201020f0d090c0905010f0603 79
    0x203c070900f041d0903400400d45e2994854443c6002c02400b480c5c03240d01060454030380001901a8000042041c0642e2920790002451a0107291055031000940c4500040314240b40c0b040b1507024030180d503840e14282c15a151003002c4c00001e02244118401c1003411050100310f140540105000b8450701c0c000c030944513200400381c4070003030b2100c07081500c1d00004011031072140311091078603513054034404800e4500f41480d0800781000c6c00e061050f203003440e90f00580c41c40a08024203202e0a440711400ca40c01c3ca172014140d554200c680000c016074070401c203030340c0400d1082010303692002da0710004030300e041d83c220003180c0c61100c1c030001810406083c001380001c148840c06072204040215151407400e0000000016036881c1c00c2003074480a8281102400f58892030303402034000214a00000e01c10f4406540d000c5030748860449003590000c082d2004140958818002c403031121520a41140c10311954411480c01043c400b41d0480d0300d8460003100003011401405024020a0350426004d526844c5c104040d09035 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 120845953 1250 120844703 120844709
    0x706050c03010906090615120b211501060807110109050d11010b04050c0f090d0212070e0903070c0510110105010312020f030c03040303140409090b0106030f020a08011403150c0403020307 82
    0x245003001001d000d9030b000021512600741f100d00c0c1c85207a00c6071450000000f08424860303150000c3c1c0d4074500211119180409980c0802e800044514030031701000d610526000038020000003079603000105494a100d0224200d1004c00a00006891205d60352100d14200030911013070301040e01500c81036905042031064411100c4151414049071a0111415115224000800e108801c01141c1521a5242d102030700e00c03215800342c20305165410507802d442c2e03540500c0c0328403803403d0581c400141c03443d0808819100410303404650100d555007400101702c01080c0d03510a0508010b03400d131038001402001d0040314004d40c090310308201c15044804000b41000e041b514040ca0ba948104100c00704080008211400c03203802d441d1020100400c1503180b0b00134440d40c1e205240d5a0308100e4814107008000c01340c40c0c101c500b5502c00300030f022200540c402c281d01610f1040b00c0420300c7d103070040148800591040050b820020140c400c49520002e0060803000c05550904603c04045018001c6090070468a005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 120847203 1250 120845953 120845969
    0x40b0a020c0f1f0605040c1e0201020c0a20010504030f02060d0902091608090c0a1806050d0302070503012007020d02040213060207050a17190c030c060e0a0506130302060f0706050c03010906 83
    0x7e4849219409031031040ea51315042000382c11018030801b035900c00e5040e10014240441680c807650203901b0304158814041c1144520031004c0c940039402ca40c0968102d400b12984000e40c6508220541c00b007000c15004144803040440e183c0c01d402005a0354000c49605c06c01703514502000800c15071030000d01400004100c3c59031030b40059491100d43d41c1e29262181140c0c5500222621854160140e0000d08041c1d4031180e000341c0c00d2003040040680108903001510000d40c003c01814448034048890103400841c00c80c10000700308030750800b42c11314011a108007400640054036001d1b9611810300140034030381c0220016003256400348068580208900010b20921180803007680425202da600c0d51014a1114110307003809503900f08120340f800b601001141c1200d031040101f95940b070b0207460b040d0300c0e06400b8170520102c1800315981c9800d0040e2403019103000800440c080c155404c0c09030303952010380903c6002c2028002140010400d02a582c45580b81a0110b41c407075141280c03440640d660398020180c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 120848453 1250 120847203 120847211
    0x1d031203042303040b0d0b121204060206070e0d0212070e1e06040e060106200304030b0603100603030504051e03030c030c120705060c090d171b0105040b0a020c0f1f060504 75
    0x246403078442a80d0001c604a4000641d0540c51f40000310001e0000c000d01206d8040c0c1c1d4200107035034020380041c2c001c981568084d00c04070b0340c0380c50041b5001c400c0080a40d03448070140aa02c800b604110007420032808250044440094035010a200329000c2201e68565441000291840d101290f0f00c00350780002e000d031410300c80341000c1e03019a6111141406114100000609480300724800f000840300c503d4040020380e540c80d0b03182d00342020148011980389019110703552505c0020480e5101350801c40783c065440e903042c14180005c0041c2006c84401040c1d070080f6034043c8203a1a6400c1c030007003011540340720003540c0c0d414500c03101c281800100090210480018020440402d0300459407580c03000203428115500c1481000103412581c82480144c10700d20107980c060141d2100708014011070000f00e4040c0300c50000480c2d00e40c00c0e51404c8a00900403000e54011868440d107540142c0485a5490103941c030281601c0c41807450151080999003041a40b200103212507034440c07092902501003968280 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 120849703 1250 120848453 120848459
    0x6060503190f11010c06020d050105040c1b06020c010e010e0a0218011404021b030a02010504030e060418050901060512010b0406050a080307031d1206040b0a0c1d03120304230304 78
    0xd220051980025041084180c01c001d0b084c1c2c41032111340302d010f511001c115195140381c48660001c5c00b0901a45004034034184550341403c0c00340d5072594001e000034100c2c444940042e80c400020350821500000f003592101002158450280901000051100000e05940e41640104980c0d4600041060083c800420041c01401ca14024103c000d18090360096070301d19040200c0810340408441882040c000403e14800c49581908680c5c011070080d40c49000710985001000001e1056225040c0140e540408149032125142c1005500c034141400000701560b503180820b900e0071074400e005a00f40d40d102c00c034404601d0f207840b84a000e0b02c4180c441c940c0700360410a0142d540d108000d00a414024500c001ca00d0154003d01c03c0700c400300d4003403c20408200c50203a4650385076819642200d80d0b601e114002a80b401e082e00c151801e0f800035982d801003208201b45500500280d10314695010702070740045003c2c290900c030040d03018522031003801100000c006003094030204a0111038100b600100010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 120850953 1250 120849703 120849713
    0x5060301060906030510120b090f030a020309040509030904060305100f1125080a020106030311031809091c080402040c08010b0901030e0106090507170106020d17040302010b0a030606050319 83
    0x2c0054800609001490762242406140100c00e44c1e844900c000881c050703040c0800c0781c1404a83d009040e40011034035602e0348540a0780d102c1c05581000c600503801400a1040707440d01d608005d40008032175050304d103403104800109041d520706400079143c0d64803040200b014074005129100201c0d116031020000501c00d681c20240a108601040c000891414003e001506a02100094440e440103001d6564100d403880030f4040d0206200940119048090078548401e011003216200ba91411440d0711500c002020480d10200180158055129404d0300a02e1540c003400b80c41c00b060207076200c1c1d00343d51619104000c15100d10310350b03070002c010001004211032001230041da42c1c1100f090802240e0700d16107a281a0060070640d00c9400180d051005110403940c000404410309990410020401c4c2c0e01e03020300341e0741c5010180301724000035452072001c0c0c201c01030212100d400030700ca8400410340300d031020009a0080e10b59042640d4059640604001d24641007020f0380c01e0304103580c40304810410326251 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 120852203 1250 120850953 120850967
    0x30406020706032a09050f01140f0a1205270109030807030b1c0c0f12030f05030606070f051c021204050d02041509150b2503092601060506030106 64
    0x5034414152140c50100d41c0c144c1c40c105a0003900c1c040080c10103c0b2001c803100401000c00740c440c1c5400703441c040e50190015485085803510301c40f0702145007844c01c202d03079610540310341c00351f50700008008030b40c28104070007002c0d4003500d8000d04011622048984000f084524104040d840031003903a85801880c0c000660400030407544032a05080020b00541407002240c0108000c229200110300300c0100c801c100400120040d05840c0120141c1c903070302d0f48030300c19402c0360003800e600070b0007203407901001d05005032103217009503481840278040e00c0c2082490741d1031844400c202001154141c000680034880240200389a100d41501340c801021109070f41000b030741c602d00c941d021395402910403286000070b544854208812000d40001c4036a4001d94521003100102101d00e070050f804003018000044001c3c00000340e590060f0a0300c0545c00b503940c0680c02c82d0340c0390526107084007840106100050380000148410811001007451344c200303195000400d508561154010318031684042c801401110b0744014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 120853453 1250 120852203 120852209
    0xc030c120b0f0a03210f02100902061c0c0e090105011706030312010e010303020f03090f04050402181305010b0a03080304030c030915050406030506150316120e0303070206090304060207 81
    0x3002000100415555074003400820b42080f0b0349000007041090300321440784030301c0b13107450526a50341c0d81c21380c100d6115000b800c0c940016413000d074401991181a9128520640c8010032003072400c0c4101400004a09501021040203951622400443e5400c0100e803508060200d0703c0c0000c540c140000030300f440e1032600c01c841d118000540050340a45003001180c040c1500036540420740d40e03503121001d44048090008400500541600402c191000000d880c6801c0340140755202c0c40140740e00740720080500401c00d983c00091501c86030115045244081e000d680180304180d45481641029400d50b011508402d00a8001070001c0002c110780b135081d00d400ca40d1510786000c9081c5641821a2070611a8024401c11035840060034400e6400600130801c540807070301e040c4100d54500e4200000c0c1d6446e04d0394003100710010800600030101c4a044081c01481074100140c4811500821104a80180d0041030481e4400414030041c0b603010000d85a11912110045180070708000009450345080c0c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 120854703 1250 120853453 120853487
    0x1008010f0902160605040507050a0801050c09120a020405070818060906041220070e0106050c0d11010906020f03011d0c070f030c0b1608100308070b0604060b070c03060c030c 76
    0x42900300920007141001d040484d0000c01c01d005604042c208a13450700707420300c50907118062010000400345810b022310f43c40703a207a03ea8061f04002542080c84000c14103060038a4840c060007a00300c0040e51503200329805040a07517221701d10340c548040ea01584105588000c00b040d480042088203041001449651199001c412101000d0b1038000079031315101010020040309011503c0320402403030000750b0340300f22200e0400440d102d0b640c4a205441612a8450202940e002040c00c050054052406504254200c900008000c1210f45a9404070380042c1581c020100000004004000b0140e901c5220001620801d001c6814400c96098035482a140002d1455000c0c10010042c507000e1442c0c00080c07908003084c01c0c0303146402c07159142244800120340001c2a080d01c0800c120840300307610a02501d5100317904030f1810040783c85110003910005d01c59076210741c9408000c2006540c0c5000b404000e803203141005456030851078044191042d9008a00403d03140c030f0100000ca03a48a4481340c040e620324 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 120855953 1250 120854703 120854707
    0x30d051b0408030409180209090105070201050606030103030206070c1b0b0904060504020a0207032a0602010504120905030d030e010b0d050a151104090507030615050a0215040209011e03020a030602091008010f0902 93
    0x18544007203042c1b40f1040007a520881c40000c0000c0140103410003445413030300c3d60081000d940c03040c0070058580428000640164000000240d0342801040c62019640c02444103400741c0031125030080305c00d003160f0000d038842200802da901642c10302d030090070007815045405508160300c55100131340e41c500c5440003801d96481201e01c2181000c144400350350001402d1a0542003a0701d030500070f03000e4241550f044984103090307081c03419014880d6140d9010340e1390040140c158458400c41c1140500014a46c0180035581c03000019950ba271000000d0903058800c0000d02041c60135402e1810180170709260a2202500380943c289020725480c0c01c0310203940c228440000c1a03110300000301d0042c04590040000302e0905111382413420f40000240815158a40c2155441d485903d040320300340d481620300940210045005211500c0100e00340d102c0031204050030038a040da20b8000031280fa60a520569140f64000303603022041c10314005000c0e01c1c0c1100d04003546194074144030b21130114083e1088000301640 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 120857203 1250 120855953 120855971
    0x9180603050d081305010203070f08091c03020c2505131a130e0a0c0f050f030a0f030216030b0411060306031e01020f0d32040f0c08030d051b0408030409 67
    0x31100f500c1c4c0f040d0130000031510380c5400340300903007088607881054021403d4400041c40802002030b200004000c070341000140364019010590182d00700107082440b07401031801455040000d43e00911002e084140011036451400c02406640180c0940c0f030031b541418181d0451140e0702c000e9a0444070303102560018507102d210291200101140d100c110f441d230150707210703400512213003d50365015100c40d0050111425a581c0400c1181c010100d10160184c0003e241d02c3c0105000d02d400780c1e05140680195000c074540f402022203418415001101e04480150a000500c1048441c030b00114a01707880051071400d280c00004e654421601210b010303091154119803010000390141c034125643c10310481e4940c2c0c5c01c421400003501302e90444202580755800030404492140200310f003512000c43c1d810305192a152960b00301544034000c151201035000340c000515400400081000910240c00003d20f07052030130010072940700071041180741d400f0620080c05205404401c4030102c80340e4a0740040c950b65 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 120858453 1250 120857203 120857221
    0xe07051204022715040e070e0a051314030c070515030f040c09060605040503060a0501032006071502070b010501021c0e0406030c06051e0403080403030f0c08030709180603050d08 78
    0x1044410310030301000c2d40e091000c200340940d66541c081c40b01710f07028428080040c2c0520345d540514491103c000d62000e020130104030a960104c0e800c00f11040041c061303059240c40d03205102c848807000da0103640c0000f0b98118081024400b1b071000d1b007000c507000044020f4100000590340005011140c0000b1158003041c100144610f140c001402840c20502c40e140c0d0b580c1000e441074009111706806405400c002442954184c414130f41681e41c000030200b484900d409110898080348205550895410002c0102044c0900503002074036a41010140e0780e0341c034030b2070003071084001a44190705541c03002c440c1c0300282e00400520507001c24076191540903072640c2d000140282c0801e6201511b103d00d0011302040746ea5004008214180c032016041c50100c4032601140c00302d00c9903110141c0810401d000a0000030321848054101c441c0901d0302e541d00c10029207440005910582d1864040b540360b6204202d0b0036000300280484075110001008003500e55182c41742c407088801c50300700412200d4400200e10328 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 120859703 1250 120858453 120858499
    0x7030b040f0c0e03060a14130305040f0e0412030606080712150b040806160905010e031e010b0109060216050409020102030d0203100e060d05070308090d02190e0705120402 75
    0x6a00c207441801101500c45029080d00c40c80b02965003c3d000e400700203480d0702d440b409446940c03000300407122003940e2801310b50031982645080c02c401700a82040000742c2ca020100100c07010f0000c84851550703034201842c149540c0001d041183c030a02d810f210040040d01d81043c20b01d540a030440c03e120003c028001325013002401498010030206107080004100c00b10f1060103003055074040381c101e6a00e5241c441144058040d01c42154000400b060418495035102c0d1404050115014040301c200100c162010021024104000201603540c1d841040306582d01c5502030006100a0000d03040c0c0200c070758581140418107028040c019a15442e151017164400c20445070422000c100441d22400c110703200d034411411505c10b01034514514404a60107181000100f00c1e0315501a0003050300303900e51340e10355810f900007029003507021203c0200380300580c81d02c0c1601000210301e0b049029241d405c003403030b8504800300a441c010410109000707100e80126040d4285800540444011003002004d482d410025 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 120860953 1250 120859703 120859721
    0x140f0307210b190c090b0304020d11271f0b090604030b040507032001120e0c040f02030115080103050703170906180a05091e0c07050313030b010506030f07030b04 71
    0x60440300d0400141080a4407400306043d1860301c180124160a0000c030741410705402885e80c08001040401c0040c03501d0480060000c4c130980040da8040110000070b0181c10409508251040030b0090382054100e000c50b600d503000580c07000c00694031091405049202c0403500501000050006000c040c65803900103840003543d001c041420b5510b42450a25100d10301c85c8012100240c41c09200042582c144410100f40f40045e0346040806050032148406044120b1048000e40212609441a41c0b41c60140c0205030070455170140c0c0d00d51604013008004c22030301c12a0810011000300500000b08049008000c0b00c2c0c00501030441c00c6000c2102052911450520943c8054005480078901c034007000d00d1004040c003200c281d1301255451040c0b01d0b585d407007280c540c0020f50380804003502c1080c02c1c0d81a40d400c00212100682081c01d1550b81c98036513804050001110006220100104200951428054181640c0e042d00b18200712142c0d945e00b14000e011801496250f000d03500310368071164840f42c80 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 120862203 1250 120860953 120860963
    0x20c0d050d0507020703020904020105090a030503040b0a0801150203190e0402030a0f180b16020a29010602010605031506040e06040b01090e16050613030506010609140f030721 77
    0x125008000a4915401039801001c581d00380700005200d5400410041c0803650045d20740d18065656600450b0303d0ba200c010718030b034041070100703011000c15400c20192005d02421580c159540d0b40d2888040c00c900f8050707200001290429441c018640e0740481a0383c0300c2e408003070074503010131100c90041d83c48440900325143c0003403000c000c001c1c0e18022900308035146000468108900e41035240c0440102c01d001d00043c0102012401140445500c04106594000f5a20581e495010b00f6941c5c2c0c0341d4a40ca840140071070000e907600101061031011042401041180000c100b81407808010903110303040121407050f46021400083c0458445400c001c00415110702a80c0301d41c9094940703410710328030a010b12410300e494000c00d8600c100c030014182d04034201504032050058940001c000c41540b10050441e5516103081d00000010300130010203029209031b4803102001803d0030082d801c9112440c0b111440790403a20040611524042641d1041d0b503207507114020030315880000003008201c80000202 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 120863309 1106 120862203 120862213
    0x1b010f0c0809160312030608030d02040509100e1f031a040524010e0c072003060c07031709030f070303021206030105090d0309030210090f170f0d0e01020c 68
    0xd0105506d00455115224003680d81107803c2a044410304540104080c411407601007100b5502000881d5649019403070078042181c0d0140c05400001d81d0651380c0000074107182c91400800c06140c002c040d440c4200404440420940c100311000c0c7d9040c010901845002c0f00800000c01c200742d8506010b107400c0c0d080100342e001c4c0c03000146c5203110400c42082000c0004142d0940e0780b007003000d81d21003840c82c9102d01003414181040100b01c0c042ca407500700030031400a900000030041c0c41250844185183d602c0342c02c440d00e148241607507012040404100a000c055240e0001c10b5006113441c0c0120442e21030300240350a890b07090b80c004603a90030801014011921a03030000e2402c278041c1c0704648071300407009809000c07030b4411703041a155107080c0e2240900340841c2d200c0491150030004078852030481249852003247c0200107440c0007280e280d03540750907440402d4042c0c1c0d118040b00000d9071 = true := by decide +kernel

theorem cover : BRFrame.Cov 120683453 120863309 := by
  have h0 := BRFrame.cov_init 120683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 120683453 ≤ n) (h2 : n < 120863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
