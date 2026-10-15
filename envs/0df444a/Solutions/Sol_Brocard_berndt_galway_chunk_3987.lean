-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3987
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:14:50.842975+00:00
-- url     : https://prove2.me/submissions/8d0edbca-b90d-4ff6-ab0d-a65cf32d1bbd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 716906474 ≤ n < 717086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 716907724 1250 716906474 716906479
    0x1101020609030a02151e15100309020a03080a020a150b010e0405041109040813030303140f100b0d02090405040302010e010e1b06090d1a16180b16050106060e030c1207030b15 76
    0x2031b9801c1045840d0001d0034410405071107104c0300c4608929041c0244540c5104941c0a480380b4021440d5890707080468000c82043e8045d4020312103000c0c005601381c0300d0b21205403000640014a0b1583e40c00041403d011801d0304e0b40246e240c24140004240541070504c0221001c40d480c3d46543c2d039501d0103030000d0180961080702c44202c0c007070220405400d5041480c52039104108020203030b59202d811714a452013641e0145600b21400350910101404900820000c03400c5034015140200b600701240844808440c190010b035914642400c03005400e01540000d90100e500074014058204901c01d0001900300c440c0c1c0c03250f01c0024107401552119034440c24030380c1d003000320010032411a02012400c0501140d014601101c50544100c120b40515a240c081003003210350410381c00c1c10f101079a59107901002da669403c5140c400355400254003400ada030701034401641d03590144d1751000305040c0b518110300720283c40b17980030003110480000002070180403a5000461924a61924500c495064868101c842d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 716908974 1250 716907724 716907781
    0xf0d0b1602060415022110290405131512030810080c01110c04020304060b100201020f191112040801200d1814070302011d0d0b0709050405041101020609030a0215 71
    0x841315440e80c4020045800504902d04110810490901000d86030303901c02c0e5410038107000900c62b60034031202181200e0800603000950b00c2485000e0020030044e6808030303102ca15104004000c1552020500c1d800c0380c1c1c106030243c079031404c02010300d07140c9403048000c604000071aa405041d041042107841440706000e082103540f4100b5041900c0940100d0310ba0728007c0c540d040182c04440d1052084650a850004a15007403454a501c2d0050204440d0810410031164402d8810002d01c00d10000c030810140d001d143c1c0d940c42c0b800e02201d003521552100d440c0342c0031082c4100c5805044113030882c0c1215401020000300e001e14285c416509480340d00c2c003e442a8031030004010908400504070064a001741c98041e0040049103590b49107400c28074003160030264078030b941c000203414103a50f41e40026150078001d241d1a22640410700302c9004680648514840c140500b0142d6010300000d40c2107611070b80594941822800080c1d603660904030b2145402601d6030008004500501d44001040114190342 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 716910224 1250 716908974 716908981
    0x1103161e1b140102030415030504020a030b130318050307180e07091a150d0507030f0e030403020a0b040b030103110d080c010e0106091b08060f0d0b16020604150221 72
    0x7104000c0080c011400409007892110000390b0001068800f1106400500c0030b242a142d00704501a000103081280c11504800d4040001060588900e00c80c0c1d1500345103525090003410010308114400a01d1076444042d00c1d0305000307d80740031410205a03000f01c99041488a4440722a200800c409005213919000305c0c0c00224400600303130401c00100403010b9018003110090801c0042c42c0c0c401200b0448240401c00070f50b0030b60f102e02c0e00810317449442401d001074040000091101503a11f42da0030500650030006083c030442c034120800d000079050b02181541400e061201c5142544410b00002c2c0014103030103043c180560b188101d585c02248d00183c3ea5171070301e0081030414040c140054078181e19500700b04000c00c5111040c410b8103221111440c141519000d400415180081c0141165030000c091080c3d00c02c00352901000070000d6407150f0f103001024030741625505045044000b850341190408024807001c2200d403807141500c45000c00005035a40c941d44c0d000d1068210341c0a12194021105040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 716911474 1250 716910224 716910263
    0x51b2b06170f0303060108070309020f1012060b07110d050c0d06020a031b120b1c0b0f180607201204061b0b0a110c0313061103161e 58
    0x11000c15220003114080900c50030b80c2601da00080760f0703050010f19030000050b00b0500c80e41100c1e0402c0d0015100101c0075880f100452407080e04e1100034408500408000c24500c203091094000500c42905018109010341d03603450f4184001c000010b1064075a600340e201808418028103c3c0c440c001170140d0f901207001e02e0f003040650458466040400d01d8081c40c01c00c0c0034514040c18840803186e036287c4480c072440100b003030700808202c4d02d49500a81c0400c0d40600c10174000300901449406002648110300d0030705580400168020100d5034500c039240500707240200d0001d200c0e17402c90820308141d4405004500442c002000360401c98409104000705100e50040750001070068450968030701030740c1191756002c00308080c02d040d80103082c00f900f900011001c0c030a50b8005e440000e03020002c40e01c1e1410040195155402880da0346004c2030341d030201040f41c10f400c02c41e0680d00000f8070003d103007804405060403807160498140508410903c06840d4080401801c0c14400d0b035500110a04210360b10000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 716912724 1250 716911474 716911499
    0x6180203163b0a0e360102040909060c020304030b06100324050a050303040b0d0b06090621011a030403031a04020d09150510060e061b060a051b2b06 65
    0x156203010310100b0001061401c1c04030b81451255000e4401031105c0981d0082c80c605030035004000340b0411080ca42080c1d0010b0080c0018402840e41c101d020550480c40e0402074104c459014100095600c01c100070000a060130244682c840001c55402c500314454080550141102620410410302c400e0720a41042103140810030503198180c1d4101da25646401c145541c0b84924051410402e42c00d200c00309142445412400b4905030140501f420464000c0c0450400d4002c800358000d2031000180c0c80444040c220a400d0046c08150340c00c503807d41c0308039014140c0d888042e1002d002c250322540031032940c0388001d0358400440c10107003086554170044480080244401c1b50102d42005000c0104101054203000382801002c4846415900519200e802c1d540c10503091500d0741c01100501800e0140e0b488000e003090b034101c240002c4e11007850070344440c4044640080c202e02c00c030948a012090104094400d5440c8284004881e8010410406c035003419a00342e031076079002d05410114045040c0d0305008 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 716913974 1250 716912724 716912837
    0x5130315050a1d120705070509090a1202010b010c1e0c140a080c010503270709061502010603030503160c0b0405150717070c03050705100618020316 65
    0x2d200b040103402d10744410520a00030340d82c00120358051480e0202c01d280d5a0b00800b06948643c0c202ca00259868012860b6030350225441c66103a000300c04c030038080c0000701c0d82d49510717000c00f803001704a9140300300700103420300c088994007400400c0340300800700c43c112024102044440e00105034542190b5101d043e42954481505a1b40c041c44407518005400d850001c0d4110403214141c40b514199074658031a400710b0350201d1214804c01074861058181c201040c0105405840080d402140b06420304001c0c6400d101c244001c9421a0301d407142c03c10210b5804016a60840242e4509601410200b06c0480d01c1004000001d0803254200c8140800c10000160348492520040503002d1030343d5035810300760350f00d40c100b2950040f0140c80700c00040300d81d4410074100c00624444d0800310700702407080c0c48041c5031194188030039600503070b00c44090000f503c40d61541842d9401080301075166182604041100400f0603400c003080c40101405d544945910b0046000001d01030184200c20030118001da002000850 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 716915224 1250 716913974 716913991
    0xf02011812031103010b03010504051306090c0302010908060f070503270c0f010507080403030f050c15040510113a0f050112112206060503100f05100513031505 70
    0x2a41c0c0822941410f0140d904030342c540b07200075045a20700428407000d800d000380030510000c1162201000920f81e0312411503810f0144c130300d407400c4a0541c40050240e440c1600105003550207101040700c0c08001c0c034401030f40300246240068580d1590106510348440d03860f41d40601400b0b00314800c400d00e0f0006404080407808540d807d0404040e10015101842600d0020b008180200301c02c0c008a40505a200c0302451507160240c54001e0030210582400280789164040006a00500090002c00c101d102100f102c02d2000f00601c40b80c1d0f4003540d005d071142e1200516169403038070410010800c04900c0350216100c800307100d61803000101c4e4084c0180200f0030900c1c0300b58501000031610403480001030007001d80c4148a88a07003185c880c02c10000080c0c0b0341c031110320910300c0d01560030300396000d0207103200910f060344429840c0e0911610403a440055030b00005000d102c030303c03810802c5503220520303103c0d41c58040c14681d0750307014404501401c0c4186904050701c0582800c0920300c8940340c41e4044c91007000e54 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 716916474 1250 716915224 716915231
    0x10f020f07270207050d08040f1502090114030613230c0a110106150518040e030a030b0306220f06021201050f10140d02040305010501170d02010b060a0f0201181203 72
    0x340b10318104034059014050f189900c03007155400042e00a000c0942c109000e0100c19a4151065890800030b081703a083d0322084030b070007041d149610b50f080341c80516900341c031a11842c214541200459860380c501d030306880f0465103070201c5140000c00c0c00034591001368198a090840d2800c0e541109155120000500010703904280070203501ca41031180400740c4040c080720124002100d401100c05c0d0304a000d403203415112203c2240a0350b0f0380da101c1c2c0c6034240c3e00300d0061911440e4910b00a822952080404c0b0301035004101004820000521240f50480b050f900b180f02021040c1815403031410705d580020302080c40010000307650f803144d5580038129501101c4030810300248a0600c0403014a810300100420131010020311000c061700041d049000700d0420050074070f13560340c4500703094801c20b0f8002d02205203100e510003008a428807441944400d01d000070300c8610b50420200d9800d00c621900303102001050b542c40c0c080c0724401c1d00000ea030440c41c2245140d1208181c204001550010700c0c0d0f800c0440d28 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 716917724 1250 716916474 716916539
    0xa08010803030402090114061303030206011a0408030301031211300a0806120c0901090504030306080a0c03020120011401080f19061d0d03020c06010b09090402010f020f07 75
    0x1030001c01c59100e581d02401d000c4041c2d00e0034004204101e003c1002ea90300c25400d000b01180a444581c412004501075402410786504d400701503070702c50102c14200c80420408100500c140140002100e045a600c1a0000195400118100c0d00c414590b02c0c1603003240280b0320248101781c01e40810881804010b00028a00e0019601800c410300c02d038940c6201140622000030004c1ca400034010060511800540f44040850310001b10002401d0f0440040b165a4105100034541c2c0340c46204054038400c002004144010348412003040c0c550301c0024104200c99464040c090300c0080c0c01156000f40c64001e010f2459241e00384501303903100740141c807642d11601e42543d00594000840800119400154440c0315955071079a201400e0f070020344001094002c0694400e60100f0004400f003810190740c0180c40d401c941060a0806034182e11541e942d01050013601b48036540c10708202e40003a4242000d25007010070341d006070f083c100b0040300301846000c1d480c40041c49502854400360014400b6820300c50303140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 716918974 1250 716917724 716917739
    0x30a1e0c0b0a06061d010e040b1c26070b0a020306010c0c121101020d090e0c360102061e100e010902120105030f190c050405010308180a03110618150a0801 68
    0x5400b08190390007e1514403517080541400d5010f40c0820741c3c040d02600b02014038542c3c81d079845c14940f90865240300e9003110f480c1e0040d5840c0241c00140c00001501e4500b662540b83d9030001c0c0c0d406080000101ea0000100e803481e0b014101c60144183d10824105542e6038a60b030f0001010800102682e1350040043c0c0c0d1a0158070208010000b10310644458000a003000c982c4d40901c0c0e00241b541c2c9204100300181c84149001c0c94582103511403a407050a41c0c000f14034503041c1c0100f03031900f9140c1554040000e00c4000360801003004580404444035030519074805211b03182d807211070751129051111140010440410a40007880b010300c400d00040750b640d90b90414582d56070140754044046801c82d510408004080580300e020083c010182031003026100d000203002c680c000e81c011560309000242800c120310447d0340c0440c00140c2103d03520700540c903644401507550091952580b01310f100103515114070001c0e41d101060540054000403804117120318a42c86076002d103031104007040282d00001381c0c19 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 716920224 1250 716918974 716919017
    0x8070b041412071a070804090506031009120806042009210a0b040c0806010618090c020d03110d060e0f06030f191a0a050a0608030a1e0c0b0a0606 64
    0x1104550080103114988003881c030014410070800c01385100208000c00104050501a00180449010001c2e150611500b018648011800303103010003801c001c3c5041c081100d103216440c0d101100c1c20b000d0320302d607600c200180c000c1c00c414403140801c402d400700540101001070080d000c0c003003082cac0e40101200c407500e00c1020001140e810000060307100000d040000740307034150500d810a21800003036840540b50044542844000d801a10020b1050b030418010682d1494001f8018080d02404001c03034124210020b4032a6480d28604041c152616850a640300b008002c41c0c0340481403400c00c00005854001705420043e0035130305010034480e9840800c940d4940440d00d405c010311140001c0c01c0e814480e155400c0f004c484010252000c022100c81c2c040050a10000c2521501280b0303400201c0385807000d02e4208a038000d4009020a0344240800b050760380d040b030300c1b03440740840d0a0101e8443c243d44e403404407010410590000e215809410921070300d0030071608800140c03160f948850400c2550010100e550 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 716921474 1250 716920224 716920249
    0x5040c06180f030f02012105040209100509070f050d0e010b03010c140a26090a050f0d1425030f0906031802090603281e0503041701020408070b0414 65
    0x5002c0420081002a204c0e00d45090483d2040c14100c4034841c08480740d8220b201259000c6a07001e40303400c10001140f07024402e09601c012002007070314280e802c010110305a000014425801e0020075410180b00901420950b24094010301c8140f140c6100c016500c3c4c003030f00107800464061340c00c3c10140c05505000c2c8011f1a00c100d0148011030401d15a000202d070a21360f9520040c440d50f980c440c4030722a03c81020b00c1148a010b0340e03c01040b4030384440c80c1143c03030651510110301e01508104000c05505910081801a030f641460009481c0c204251140d80380b0340b41a0500d0b0021040c02c2540e03002c05420403030b90800c0d1011600c07100c2e00c0311358929080e800d41e000c1040c5002c2030821452140c0041c541051059084400502118039540f050202c002002d803080030040230b200c105995406c02c0004d1090507190783c40c06a800009202400d40e1516903034011401150010b02c800034007211110300950541c0c005080305022290b1280e0340d80d000311401d5000b401040401540c00407044030303500b06050b04490 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 716922724 1250 716921474 716921489
    0xc0e0a08030f0a050c1227011d0307050d03020f0d02060108060105040903031506030b2b0b06150a030609060b19180902030a0209041d030904150905040c0618 69
    0x10b4420745440700401984031000540c28003e05100ba0700202c8410050484607403045118103668055080584070740005c01158203a025910041421190b6440510550910950600141c0c030401000c00641488281d802260704005200010b406042c2d00003180c0011200325025259400002d2034100e032500c0c5c0900503421581c0c8680010091360400760700c925181d41c001c0c070300007500389000f4002c0310310044035070b0011000a4555107074030700e10318003030480c85081002480e08000070b88035182034086504a15001400c61300b2040b0004085464580319186241060501180e4660b40500040c000303005a0040000f014078192001c03552500940807100e091200a40310000c9048400040707800a400c0007034000b41401d40d02c1700062500c0300c4e0000d5401101d6200c07000d42c031407603440144421a04070000d002680340c1000b40c1c00b40c810f600441151f0502c0002e88002c103050a442c2e102501c540c20345c2d8000395445180c8410402840411001501510a90358030400f0101c0d80c590385111f1512180503612 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 716923974 1250 716922724 716922727
    0x504020f0307061d04111b07060302120f04080f0301031a0709052d0d030e12070b040308090d021203070c0f0b0a03021804060b071104061401030e100f0c0e0a0803 71
    0x1945800c4c04860511150700041010410200a00c0f40e510150445444892000b00c107035912151035005104039400f405442c5021410300c241d50b01144540080608102d20898602d4081014030501408072515211141c0941d6603c6d652407400f5140305001d80c5070454048404008038008910510b800c000f10b480081c080c41181190250311410181c0c10342c0d4000141105121449040d1107402c00c260001d4000d8482c2030400104105108048114484a281541041c2014416500c1241c25101030340d070010005600c0d86a10340114a0302e0400800103588001a8242400201800401011858410110314441030740d10003100d140500c80d400350100c0e664040c4150000107200354098040204041d5180000700822000b103401c550013500b00b85c3c151900001e983c014130000194034840140c0a0f5010000d240c900707280700210030f894400c80c604054070f0741404540260700704540131584081c000100202031000443d440180640020303c40882c40861204e40107107088460725080b2002d041c00345 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 716925224 1250 716923974 716923997
    0xb0109020a0918060e0106021005090705090c180301020f030103021305070f030905120c010e06090d020a0b0c090a0e01090b040203060609010c0f0803040318081b090711010509010504020f030706 85
    0x4118a203e100c2040ca92991315240061180f40540e0342d50300904868024100d204802454603017954030007080041194003000040009840e010001a40040c445590b1911440b485030021244244219803580c50360003c51454030214024000b50304983c03003210031041e0407142e005142c05445003200d424020a01801c0c01000680c00b079084100f400b0f1041c1e00f0b4501d441c22500c0d45511603000381100c04501c5c0c0d0f40780c0e2004040c090800410350414104130003040c038000745190003580c4840d0b00c54003c2443d1a804003103840043c2c54016107041c41d030000d00c00e0b0a050345491007040c0329002440781c0d1400d5401c1800c0003840b41010300c04c503409008007a14052501c002d0000541c0c2101c12514100d85520481c0301603030215045001460007644aa510350701c40b0414500300340394030b040b180c10140c1d05410192030794520080044501c011014141c5408080703640e5504151182031a000f0310320059400c1008110700d14a042d8000c40c401d80c421222250ba0920543c01d00d1f646040754081e03100441c2110707001c0d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 716926474 1250 716925224 716925239
    0xe0d020a02041d01242907060212190b06070804230d051005280f021b100c08060a090216020607060b030601080f0312060d0209130b0109020a09 63
    0xa0351510f1060a00000d050f840c81c3c445801c440b00f6a0a414454040b03100e440c0c894070b130b2441110000c3c9040d415031011540c00100010b8100c0d01c8907980b0000700c100040400811801ea0196040506000701d40c10359441c00309011080518400d000d808180c0c58081454070a1600030103803240a508054043d0409003810803158100012040c1500c00300400411202c455945071001003100d44900050451a85040e5007081642c0d0058075410050381040001e080401d04103482111040c1e840398007041412002410b00c0c002d11501c81d43c00e000120b814503920300710074001381d000501d08a060b0108440c00341c065040310441c0050326040e40c40300343c441041000d00c41540151803070704155a011416407403a64001902548885401c4400390344802c0c54480a14060010a00505052015094401c03107085090784902c1010648a002100200891001d40740d4107918280194060844c82140c00c120520148144804100701c40986120001050805042c000c0e1401d12181e6160100d403181001403 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 716927724 1250 716926474 716926481
    0x804050106080f0a1511160c06030c0c2a0603140a05040c030f050304120b0108010c0f0509240406020c0a060215061e1e031002090906060a02030d0c0801090e0d020a0204 74
    0x490f11081c40e2142502086c2c40340c000010452108600f051421907000d600e070035020700702c0d03d910013400c2c58078190754000900d070419414002d2580c804104107500419000b0000b503074403070100306d0289a000c20004159240c240c5c1c080c001c0501c00b03ca5100035030382c440c0000026207900300c4000340303c110000b0701000000c1e07800b42c841048600c5203060360700b0a502c62540d48000d04c41d0441c1580c0076441c010040150078004e201c0c241d400045841c14002400c001c0101600324410b210599002c0d2140c12801a01e819100c4040c80e100440e400e141c43c3da5582c3e68000942e100203900f0050b206e09414100041c41030700005038407400381e1030b207000c111155944504020440ac4050324500300031040d80b613113070031698031003814403440304903c00c0e00c0b00c5407400d401c05e0600d031040d03815049040c90710400c0506219503808004651120040f118184e513441c2c04002203007580140e0401a14040c10184d0350340045420850302416608465010081e0840440d41030b503071903540707a080c2c6000d60402a90300026080980 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 716928974 1250 716927724 716927753
    0xf0e120712050409020a0f17040f02060c0f10060306150608160c0f06050a0501050402090d060216050f0a1506032a35010608030a030f0902040c0804050106080f0a 71
    0x101203061940e13426254099134414500200081e2034400c01c07501d034503040081c80c07100305488801745c14030345440ea031307040080485100068132601022401d5015640100412145660300741d0503a02204c4c064000a40a071400d804101d801030700348607421052140b0307011603100b01c900c42d81d1805016107034006100d6448003503061050811030f0001c1c4250101d04900ca148003031910501c000035203482c00038941000c44038182c001c0341c4030390300404c0b959686030383c0d005150390410f03046400160703038291603140039402c403030000c50041c054007a8032100640c007040440d00c0e0607200c0c020304000401c0080d61255800301e410381e010083c101c0c2600c09500074107840c034601d078980850090086001c15a21500032541d410b036000c2c56401500140c0c203148681141c50500003144042c2e090080c00388909100340980c490080345514000c15a560038000c070303441c1568020014054010380304006c81c4800c1e03540103140b004100c034241da9940c2002400181d070140011054107964152000e042c08a16950320300f44c2050104 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 716930224 1250 716928974 716928977
    0x8040302012a080106080c0d0b0a0306060b131202011b030e030f1b030f060412030b0d0602190801080606060a020a05100603020109080c01020d05030c1c0f0e120712 72
    0x71000ea0b000740907200c03200e10124002254254010312500c50040c412001600301800b004400c50900007884107240645205140f900d10100b42c03201c0c0340001c42c1100d10075920140c0780d507061000c00501c0402d030354010b100328065500c00e4804a61552003500d80a031045070001d0014114603800c08100d0140c0c0070b6052418845d2508098a2103003000080c03811407034650001054004140c100c0522a241d62902005c82c01680500280f2000744207035030f00c80d440280054420301c0f00c822b524000a1003503121010102c0000c0c516113112045040a200031740140300341c260b03040300414602c80074034000c000ca58101da0850009100f69a11741040c44015001a0488001e52040303400a60000300c00341f1030039290b030124141c00518185180001400d010783c6610078280d5400ca00f90058199901046902c00f80517130f824802d50303079154400b040b0201d1190702c03130140c03001e00b800300350b100c81c1c00c442e81003a0500c07104603205102150700c0c40c80040d00c5100d081ca543c040146e0800542d0002802c000480c0c00d0036019 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 716931474 1250 716930224 716930231
    0x22412150d11031e060a0e070305030d05150d05070315020f031312090b04090515090405150a0c17102d0906060203030604320919120804030201 63
    0x25000494081082007204507401108403200340d800e402c04100103110603110703102a40001801d083d440d0346845000e043c0756051030f00d61400c054950720404c42d11004540c00812240d41c0d034006010400100740540d10700c070703090f440c20007516443d191180712a91250380040c06004611f28540c0d444181c0800e02807101c0c400758007070042441c05400003001e0f5110340950109415031308118580004d01c2080740004200303100c02d00200f441140d41020691b015600c01e4000080c0d503450700c4490058001220200384c0d40a00250200302c1040340c0410b00c2116407040000b100300c02c0e21220f912800b0b480c00401803400141907032560510101c2000481a00540b84030103005070680c40b24511030720004c0341021600340501d400658a0030f1803044154800411442d1002c200d40c1d81051002502e920015142d544103a484840300c00102030002200304046c601400c104110218200000000e100c04446801280c01001e2040281c4800128074100c117542c0100000c1d8500f4034114181c40e481d002030000c2e400c6658 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 716932724 1250 716931474 716931511
    0xc1b0f240e1c1a07050a120504031806030c181505030c1909060219110f0414100302031902091f03080d14070c0b0606070515040c03022412 61
    0x340020503039411030183d04000c3c40002981c4040d200703688064140303410003808000028507140c0c826191104180d4903a400f0071a6280d40c1011a900702e81440515000071516000089080d05507200a1005145450791440e50910301d10f040e85001051150000042c10414a580103501c175100551303001c2c90302504281010381030151446c2c0c8440da1802000425107803031040c00780b142c0411810340b460341c0b40d807a42c00d0751002e1230b43c0725428500d551443c21b0081181c0d0204059960322500400f09511a400c07007041c180c038101c1d05a40e0302c4009480141d0203070090114041d60f03041c26409841080360007615900701c6484802c00c1000c02201110f4140d0b0440e90300d10007100140140006058240d00d186001c034116108002003000002c0140803070050004101140e000100c04603030140c4d10880440780c00742c0f901c505040c0f0a04100040c0c210301d015980e41e00803c4100900c0350042400da030300a850307500d07642c0d0102800c006947c1381802d81c030141c00004c0c000440707001590400070f82c2c0101048100f461141 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 716933974 1250 716932724 716932759
    0x801020f040f0f1512140721021e1606020d090212060603060106050a0201020d051003060c2c0112090b0603061014060304030c1b0f240e 60
    0x200300c4411400c1aa100050800c8041034011180c0c0c09800340d401082812880c3c012540f80c440c03c0031403800140240012840c0d1124042da00100c414002c050100ca0035207441e200003000034107446035840f00795840031240c90f0485807510030340b09814100304204201f0344440d60804041d401c011480302034400f0005c0c1c0e0000154540c000390190b18002e5602140b092002d1041088204104a04040030303480107081003002c1e038000444904503251400d02a5440070740400882c06072254030104664103003844180045007410651039422640a00d800b0081a011050100d81c510303080083ea600801354004500701c4406030040a22400105040040c079a4000680003001c0c5c4050324003d035040940d400801c000e030306040c07003403690001c0324222489155051108034840704900e500168010b40b030100c00141014028a22180303450b0b0095042c0c024580341c1000040490302d54050030b10698101c050000e482e07110070300903000d6140c80c0c0c81500500340d110081240d28140c1c2170201c035882142c1140301d14a00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 716935224 1250 716933974 716933977
    0xb0405040c0c3c03051e0702100201020d110a230415020a050d1e080603100f150906060c060e0a0b01080f0d03051b071106040807091401030c1707030602120a0b010c020618010504080102 81
    0x1089c6400141e240c800c2c1c0202c907130450315690500e81e00100c00300100725149030700498070100c00340e2001d540098100703810111601402036400408a00c020021a40e1005400083ca000c1e500d00c10000c6a41501c0401170854a135034010900149103208240140b0420f8010083c055002c1005021200032803c1c4c04e82e44000c0d202d140325070044682c0d660080c860b01640c0010307408050a83d5000a0144518000004040d60480c000280c50030359075468140300c400080c006842c449400c14500381155841e030090700d46980380c02110000a02c10294445c0c1d9840c0a40034103803203840b11415140d1110010240c1e01841c0d4041c0c031003162000c3e05144900155540d65000c1c1014218541c020411142170894140c1140e084030008081c444c6054010800941d10705103940c260790b1448200b01314100740030115807400b20f10f034000900d02f0b400415044103803919003480d42e200d202e891300240305840da030b20b0040d12811460400690032000400c840c443c04510480c400d4503010040c0360071481d0941d148901c0d400c9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 716936474 1250 716935224 716935249
    0x11030c010f1d15072d0801050a09090f030503040f1a16140d0209060409140f060d050a110f0319110306010b0405040c0c3c03051e0702 59
    0x54558038008a104845405580c0010b50a060001c0840d118103206001585000804100420003861510052240c41d13107440c1d249461107160108010915007030181a10a00740a804e0007002c4d00c82000a80320314034080c400e50369400c903000a601e1030f4143c500f1140c940c4001c0c0269001606003044000154520300f106010304581d0f8140f05403414085666900524101e051404100070300041d8280d0205544c2110720005031200c1c016038620b001000f05149014076804610128506402440c5060b00c91020318411a000014008250f54010400654890123240541294000c0c001c400010f0040b5400070440d801c014200e50719814a400082c3c64114641d05061100c40075010040c100664440c7d8541189021006010340750f05290b290b038118096481110301c07943d150142190f5040c0a00203880003035400400c9104e2081c2081c013000442081d50801c101070f44090503009900103640c01d0801695940761351800d107424600041003a020f201e2440142200388100420030060b50b40c90043c0d17030b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 716937724 1250 716936474 716936501
    0x81e0402011812120807020d0e0918060f01180e19050304051210060501020106061407030527130b010c060e01060905070c03020601120b0f0907090c180b0c030a11030c01 74
    0xc0304e01d14042c0052000c04041c0c024030656000c0d0106403106070300948032021140c0700360f84240c811742c2d6908200c414000314610791441c0d4021041401040114041d62906a80c81744000160714201e04100704105c40d18420740381d00d640c002e20076192600040345603034201c240c0150304503420640c55800142c1b002001160760080355018100191801406000340300060100740002c0003d5031415001401361a41c02048001010b80000c14004250140007a6010510740290b00805900b548061a81000501c98424070801c0784180c4e20030307981c45074000c204a03540183d481c007003610341c20341d592070281013000101e400a540303c1c032002c61100201d204c0d103071045000d0380d1019607424a5003006030400106812000c2141c0a0321003041c04200f001119a402100b00804082a83c3d00c25003040d003844403d0300700011650404640c1c0c8903d5502c12411120705401d03400d0510221740c0c0b2018002c0d00e00c103245041c10250070031f01c91400c0c49030040003492441d10320381c012789180902c100b05e041d00319080d2005044 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 716938974 1250 716937724 716937743
    0x1c06020c0c01030608062502150c04030b0a0c05040b090a0b07080304140c03061603090f240501030f031116030f15090f060b010c050319081e0402011812 67
    0x71182e60341070284400424101016084a0501d0301c1c006201000c500d900704056007c404903007400e58400c210018140345c4951040d81c0d2810300031180c29255000d4402501c9000440010407517008040c420b0222503025a02c407e4542440c105410515400406010394000700c0c003032001030401c19040050141074480d0200d0380c0c0d00e25240c030740148000c0300805907220a60102548024070385000640981240008449240b4001122400c402800029500030040c0040d0800841000101c03500040071144010001c4c07030640722800036504440b024800544000c01030b24010000c82e0107065a105013000480588111071205034001a140341d079640704850b800903101c030800502220542614818403401401e0101c1101900e528400c520584c2c409440c85030f035440b4128050b8000d507070181260354400d00380c0303484d0b01e0070a000344210001c41b20342c0808214180c0c001854000c0921890580394244410402240c81da90011112403000c80420440d0303100000020549402c01841c40e083d40384030b1601c03003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 716940224 1250 716938974 716938993
    0x140901050928080304060209040c030903110f10020d150f0806071b0212010209041d01050106092403020409020c100c0801080d030906110c0609070b070c051c06020c 72
    0x94078111191070428800b40030144401548020111003402e41d03508030f42070f16142d440e141040402803041013280ca5000e4901101400c0a03178041d002071040324001d860701403425034010105900c0c0d9095021110850304006150f106100182d4041d1049800580f80003030b0801051003403c85c03188507034008030411045060704000b50001041441d40c40380780c0c0e03d03000c1004069104d4070782600c100c07038100030301c16202e030700c100c49102d20309505071282e20400600038007a0854003186807100540c0e807890304040307508200011038507038003c03854001144d00071000428104125641c000c448441e0400040400da000c11000414445034000f4100343c24440c5c000c5d100700c1e9031b52201c400c00c40c0d44111010052011500c010841040c000c60611080811801d0104554117246041130041c00f0384180c502d0541400301e0340c82c503519800a80d580c862004034003102c403420385880c41c0c00d140b4042d1010060807252600014001c074105140b6001c1142c944904038101450700c1e030703200f100381d80220009403490760010300328 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 716941474 1250 716940224 716940241
    0x1020102132903060d020625030908060c0405090c07030c1707150905060f130b07050a110c0a050d0501110301120201090611031e1b011505010509060306010c2108040b06100c03080a14090105 83
    0x2030380e400c00c51404201d460a403033f100200315094402000c4051071000801c1040525005e069160100b90b40016a5100005102400206a0440304095512540300303090f01e000d5445d180b2580c401c03030f50094018800c640d15042505e050100045c10350842c2c0d4070390591480040c000c400b0240c040c9100d51500307070701c904032060020300300604101e09090300c2d80009a550181c0d140c42c4920f0007520415204145840491700300700d405000c3c441e010441061000000158044c00340743c10350f034094800d9940f0034099541e02c0b000c89034181c00d03000644441d00204114001c844200c20001c0d0981010710140c0c1c14039100c00400745a15107422244141039460b009070250922388a20140c028080c04d0a04034100031166010800d140002000241840789400608041c0486a40440802191416040c200c1020300340c000304141030990b01183c9203c5004007044503403400c820070a0a5101980d1480700c0ca028070344044179506030152038003050707984d9000c00d00c5503002850111482400e4200020a0a0410303010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 716942724 1250 716941474 716941483
    0x18100c020c09060913020103150b070f02010201060b040b180d02030d020d0e0d0c030b0a0b131b090e0a0b060c030d050f0105030105040309090b01020102132903060d020625030908 78
    0x4607104e1060401000400294004250009902843c002901110700c0c12844c40c2e0302d680c1e401418441da00404c035502000000b2120940251007a4002d01030f040e036541c21000c045c0614014680404030034420f00110080b01440c103103142c90020b2040d01d504841d81c0100c0d0401550454400050708660007890005400c00e40c81c02d50300d0317004d542110391880551a00303007140c2054080146420a580d000c10004496134005111105000b002d800742c03103030103086010003003096a0344180c40102045007080d10b14001c58011003242c0100c00384080c1691840d407480c0043c22050120340e40003405200e01c0c5101a0100040c000080d2a01d40004040c1840d424114040c0e00580c08503110341c0c103060400000aa001d0801c20881d1000300012400040490050340039009484002c0e40340010010001451006021104114500d60000c642c400c8100620701c20140b208842e960f41000e650004a801802c0080086c1901c41d207015001c04605402207001064030071942e02a40000d809802c244141c403070034003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 716943974 1250 716942724 716942731
    0x30c03100f05030325080a020304031542080f0606100c23100c0807031505060904020403050703030807021902031b061903020d0b03030301080618100c020c09 69
    0x1c00c1201c9091034840042d03660f1050006844050740300c401041049559107000341d003030961148005881d214000d400a560750424403080e02c81c1d4503940c9050110350120300c00c0a010503017030300c0c1aa28045803903140101d91212100b0410404000074107805a80300d61040c0d510207042000080c2070403200d4492a43e160400c00307080244143c9108401e09282e0f40c00c6502c0b031460701e44c0700d0b0b4800740d144c01d40002c400443c6416015008940900c200b11380308032600f60b000c1d02445215031500f000b40e4a468204904503910101420b5152614540511a6160001c050400c902000340003510f000e8803035a4150030034540c1d5000300c020a00f104288104681c0500c1802c00c160034445400e0b082c0340181d00040d507901d000c0b12101401c2010b00151068030b4075027a044404ca9000384a00103465202d040e0002c0003903000a040d0364440d071800c0721030b40080c80c010040360304841d01c00c0001e15003621424203961034007003008407446080c0300d881d078800381603801c900131001d446c48c46401601003c1000c4007409001000103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 716945224 1250 716943974 716943989
    0x210110c0f0327060d18050f010f14060109210c030602070b07050c060c030c070501090c0302010e0a1805070c02030a080306090a020304032c03070b0310060e090103030f0c08030c0310 80
    0x30402440c20f4640c4c406560200302100f2011074406000e40c5204140a0145006070075402802411000390038150846211868104410040040b9030380c0800c00c0c084041d552240010202c8030f00300032100d070411010280c1045180e08440500035655610008640c580c0110b03150794021420400744000d00c0300c02d0354011080d00f8860b1030300d40032071412512008d000b011158014000300100e103010031184180c9440903440b50003000303c0442810403001c41d40c0507100c22400070300c0344100c080d4241010604002150000d48400da5299083d1440c200507203c014410410030000c8001200903036010820000034602411b03000340e886c00c0c49400e1101050008003502c03e0300b801041031100190703020001e8181c00541c0b103510810140c1210040000c90302039078800e6854030481c4030200e10000341100445c0a1001a031022040d40c1c0c1d615030070b4892285503164103500410300001080402c0c0104580c8072000480d10704144505a12380c0c9000c07140e002900c2500629201208102c5049801000305014003102d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 716946474 1250 716945224 716945287
    0x3110307080a14010207080f181903140a02040c080106020c030a0308070302090d0506010f090b0915130f0617100e07050415030f050d1b02010210110c0f03 68
    0x401084580d0b580c403282004000b4441c43c422100862420342c1510307849588192516616032000928610b0b6801203440341e84074403416482e83c44d482c5441201c0b0700c03034075240300030352058517246440b80d030b0040f6800f107000b00e45400b4035011031340107a480b07104220030310003242c80318a10b9504041c0c0083c80c249046000501aa000340305003404260081c401c079a01051914003d0ba48510a40c0401c982112041c001042031240c0000801d20903090001c07401610242c0c40d00700a03200c809010482c034240d080c2d40c5103111070458001c1c01380c075041a00c229842203c07a40004216480c01b4000c500856050780e00c110f078510418081c0c001c0040040c8000050b4119000b011301c48040440c1c00c660719248948251882190354400c5901400c607062044402960014000d505103091410502d8541e0b40301a02d61000802d0b03410010306400384540c010f840a50180d000b0800c15440d0741c0c0f00e90044c05194080c000c141800c1c84216090602041415583c11840024545035522180380e0045003511144140d6001c05 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 716947724 1250 716946474 716946479
    0x1506090b0a0903080901212007122313030b0603010504051b0409060203090703030305180d030207030509030615040c02011406040f0e150f01060914012a050703110307 73
    0x24400446801d580d08140e42d560364003030b000d00503034410422407c441460f103010360700c12005501c1c0760300603002c400184803245a806c109400e51840c40c86403120042403520400c07041c1c15081e1281c0031980d509038040002042404050314407805a0700942c07400b2040920744801801001405041c150300228181c009100b07904146c0d8800e51614000c945c002845206000000356558030364002c42c09450300850308541e2410444242c80d12806207000c1030380880e080c80080380c0c4a07103000c80001c40d05010036019092561030480105e0281d40254415070400606100241869a040c080180101c1c012000d400000b6010014881a46e480310065410369140440b446102018031a8042d4841800c4800044200941d00200700811401c0340c040c03e1071003002c540501180103550014090140c180f0130b4206aaa11101101c24410b05d008000100c081044184410350241c3c43c107120b0989680c3ca840000d0b203002000201c20a084501542e00e0707481403000b00180b040104c0c1200e541d0340168084c120050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 716948974 1250 716947724 716947727
    0x30f0c020f0f011e020c030c0a1521110c0d0801050f0d17030f041b050109030f0c05120109023a060204090213030308090705010e0607060f1506090b0a 66
    0x181000c0ca0a4040c01c0d00080300c901513072181c00190592644805910f10a5075482d500a58612049403142c3c0648100c00000c900383c0b0f840d900c080215211109400c1400c0403240301141e0010080c1c002e00300e0813500f00c03a48004003003280200b18500d81410000c54a802050300010318018400180a0620502c80014001a00c6000c41c03000d01800035204404611540c0c985035880c2201500f103550080004010b008800d10300d00b1416004500401040400086070402180d00008520810380843c0384c0e00010400901c004545c000b04a00501540500343c1c1d482011400558040740841c9107a5501c010407401c41c609070200b0301c1103010341c0703145094103005903240700e0b21045401c1c03104e52004031040240c02003004540480300034014141081d03489075a00040e4003c021880c0c042240807607204030002e030091030b00140d8001110816960103a5026030503003070201c9540402c10a4070700e40e4540c0551041c4c540b42d40941414280008284450f00745412002043c0000740e800c5906138820030025600646d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 716950224 1250 716948974 716948989
    0x20a0806190909020118060801030b09030a02060a05041406040c05150301290408070b131e03020105220f0801050c0403050a0303021614060f01050103020408100c03140112030f0c02 79
    0x5940c8190b00042e4207080d0700060b0350304440c01071070b0100d400c03a00b140405c10550080e100c504aa1055140782c00d0317511490070f4151a0b0180207200c00c01640301d1310020310741c4400c41e0002604540100141144d042d00306405c18248030049030241c402d4220004c0800c030f51f04202001114180850131800d0543d410110110041c00b809030124008240840078200c00c100c5000881c0e004005080888042c01d903a4403180106410400708070080c844e01c0000068140c80b41071102c11a1200221130403500760440d401950315411000c2115202810460b58000b07841003502010084c11003280e00318035180c80d01c01707640d09561004024401020042c48100002071000942d036041550506015840706409186500c01c001116000703890040c2031040700c60280c0d00454058001c1c28100f145130b4140c0c2c3c07103170015004d03413140b0700c221101e941c00701e034401c807000d02158442c9565034150302e0089400b800f4410759059071032085c0c00448803041c00941d00b0040541001c1210149100d5080000d010700780c6030000b5849 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 716951474 1250 716950224 716950229
    0x11833090b1e0912010515040608060402010c03030f1d1902090103030804020303090d080702010e010201050c040504021317030d0b01030c0912052503020405060909071707030503070303020a080619 86
    0x11610003084002030320b9071019140d8020b000750103001111407280c1c10307034060721041c0c90590028015440100c424102401150180c50102004140684455004480c080c10100c401d40030503694100030800000140074100c6002015417442040c1580000080d05000d04003400300c2c4040c8561100e03000588861085a04481e0181811281503a460010a045100304c1d02510b0303018400c076001e98104980f8401418100d8000c3e0f07101220b5550341401a422150140c5e40f001c80c8034001d0200300107518054000340f1111580380e503810101d59131516201e200585912103021613400209503140000e44600c9200e20034182403805000e11541e420780500600c29901440c107a40c904100b0000c18010108000203001003004c0440481c4940c1c0003c240044049000880c443c5c1d0509022a40d6450205140c50203100090098400307a031034440c0c0d4807031007808000000006d006e03407280000401c10a20240001b80d0081d1005690351003101c800400c8860001c10040c400c100c895100c051007001c07601d10009 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 716952724 1250 716951474 716951497
    0xf010c0207210602132919020a0c080303011517011a16080d060815131a0708040317131101030b041a011403090c011833090b 55
    0x342d10300041084010b11261840c007401481c00065910701d04030410140d441116043e503150341010720107880700200740c002065034004108051013200c06140001c110b082d020003580c012919540020780d280000f1030002d034041c01003030b00040010400060703000058900d031040b0f0b261481c0c06216949800000c800107004150b0146480d60b0031103504000c1c0f2003100d16601210420540c88402840c11a040354003148040c4c59181c00c0180000307480c9400165080314001050b64022180d4070044a4a41c40703400001c02d640701082e200e000505800203106580c060445170341c071001b09250506006d0700c0e0300284102525025440f00c00c04c4540c0e42031086600c009034ac0700b10006a0f03500c03074500481c0134280f4040b00c2540107250120101041094002650040800b0381b04c85404401d242d0a092140c0004c49180c4041e030000ca046103143d603c60b808500400d520f40c503003603254503110441030b0f83c81b800b02010b06501c402001c0724040d00c070a603610580d0954505250440f4880d0a0017089402c80c0610312072000f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 716953974 1250 716952724 716952749
    0x30b06090915070509150d15121e02030705061204060614030c0405040303021306020c13050c040308030402060d0f051f0b1206030c1f23030f04020414070c0201020f010c0207 76
    0x4940c1d0f646c6004103017107100200707445d0707101c6c240362141c0002800c02d1100c90a89202c0d464001403850058014201c0150f001552102c0300c03e84100c2c0f103144103090b08012a8540243c650204a075951803002d031913912044400c032051481c20b07140040849035107400ca10204081407070b01407859a00041e08503802601541d0102d12a2aa03140030342c06406804120720100746807100102c0c0325a40025019003041c805c86100341124006034030001201e84c1550030003403900080009001041d0514000c541051001d00703400e03e03012002e1071100864002c0000c1643c45615078090000122120700403e000480c118903240c4c000f85003104688261141c0a086403100650b000014807980d400c1c031200d002002c015002c00c08007054403003222076520001c82c100010440107150022100c02c9559a542c1801400241c5c170301d151510070148100c2400204201d90140d1545144041012030b40c1c0103a000342c4a50f2a082d00c40c0300d091002905200348000c5050044c0e2511102c2e445031a4002049011510111104e0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 716955224 1250 716953974 716953987
    0x312110409021803010c020f01051b07031b080301030f02190509070c03091a07051c020c04051306110c0d0e090103021207080a05030a0914090106030f1401030b060909150705 76
    0x103008498095682e2a03055103046c2400d9119078000c103407803c51038140402004240da07000c042081c140ca83d040b01c81c00d950300611800c4000f07401282070002403490150440101c0415580f484840d510980040751400540c18040b011401d00c040145000c414489035024040e00b000b002c2001d0179130003041801000310300840e0b501450301030200500500700c0d494621b5290006071a40105551101d00304031294450001d11101a4098100d20a4040d005034003803c100c2d0f04840070003010301009081880418405844140000c140344540606401086541d64442541c82d585505041c0c3c060207103002d008401c1c081d00d0302995210861030640358100c0d00380020300010300b041403030110340e600f102d00756105181d10981840700000190802199a9683c0f401154a408000e00000309010809411004c00001441014081d4004c0c003040d2144c0d0f88005402203142d00b6400b040c007000c0e40300341c0e9060715071821300c0b00c90f0501c1007980d948481c1401c01030481c810178a00c54511410f00a007690104000480d08 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 716956474 1250 716955224 716955247
    0xd0215090a080a021906050a051e160308060409020a0302040509120a08090c01210b0303090d060501080106060c0f2603040308090c0102010c021b060c06070903031211040902 76
    0x103030396030000e01404200509441d091120303941c0541c203000360302c681a2203281c0d0389255860385154098405594426090a107410815100354200040d5011440e901e640601410b84d240d2010701000c603030302a61500540c0301030801421008018080a025505200d04140541c4034003e080f82240d9041e10b000a1658412202c0c50a000da0040f044412460014540381343d1544030071031074000d55608043e2489802d0300307801554408585180d082211000c008100743d4440e141d4044024600701074160303407030080286c00080c0d000c402d286040304c03000d039180300610010303000344103500c00b9121504207003421400035100c15004200c407900040030074125183c0c0712001042241d21390034860320300b0203150310f03420700c1d241c041c101600c103d412841910a460200c0029841401448140780e01500a0310b4824130076142c0403020048542480e401c6801003004400103041000102d104580d50ba0741c0300002411490024801100f081038542984d0802d410010310280c2001100d007250391036440140d030340020650 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 716957724 1250 716956474 716956477
    0x30c020406090b240c06011701050903120a0b010e060f0d180302030f070318090204050405070e0f101107030602130b120c0d38060324060d06140411090d0215 69
    0x14505c00500888000003081c48000001d800b517034090000901c103a5a030313000d06959034010948001c2c540d40c1c5d03100220b491074a983e84150800c0c1c40c180340400c0890080404115590300c440300303001c2800400216000d002c0104d00c0761040d03881da07a0783e600095080c2520025607a0080c10400b1410020002e070034230405010f0003000716115001d400d020000c070340d642c4400000f500b10f44140b034001e03801c1c807000030b91180c03280500c11000c0d08020405c0c52015031240030b02c0040c007501c030990414082141884e814100c42041003000451282c000581d840700e0510342004504699800800f03201028000070741d4291040014a604c1144a020251584604103070030b0060450815981e0382c10032a010000d0035880300b1965507510b520700100d0200454640c1e801e00c002c42c4000c80300780031a401056035079600c00e0b1410014038810300740189400c3c20803856800490865101e6800000000d40401c42c45a503810701d0700442e890101e40c00c42c03860810380c03440e0102c5c0c1100110003000307220b00c1404060754103020b00e000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 716958974 1250 716957724 716957737
    0xd0f02090c040f0602030409060603020307091e080102031303090509090303071809090b240303090f030f0d020105011e140108071e0e09011a18010219030c020406090b24 74
    0xc01c81d1400f40c0d92200041d407258440e006001d115420b02c140810100c0c00790080301e000703070f07038503901d150700d2a14050300c40c10014110015442c1c4100103140009448500f40080e50240e031203c0b6007040c20036070914004e081e811507540a6406400c0794403c0010021010055a902c60750394100000d000e000d00c2c2040089040641008075100d292600020522000783c0c01c03e845980754002602e10304415260003c14540404110b03030345030748200402c2d16981040050f8250801c2c000d01210010000c0c1d1183d00d003003070075982c0e580c6c0c0141c0d540d000400a880d0130700c10080b1846c82c0780200c20a00750626001c0f001986809481e241031002c0310000c24111441540541c011a01002d600449011440001080c1c00c01d01074045209200900000c40e5621490383c80c004081e252402080c5422414066208286040234400c0e041d0301034055003a01102c840d0b510425810700c00d9440c03120441d85032042104680c001e80040181c145402d15130310660b00c4c2e209040500142c4d1100d00c00001e200a070140c1100d10401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 716960224 1250 716958974 716958989
    0x302100207050c09040b07020c0301060513110d02040e07020132091f020903250e18070f0510080403020c01051b030406022b050a080613110a09050d0f02090c04 70
    0x201e017040180052101c815010300c005a003a50602407a40d410103098400c00d01403030360310103003400d44880c00705155400690200141190030f8101003085c0381010481e00b007036210210b001810002c000b0f04640c203108001c6222030080035030440742400011540d0a92400c6600c0c211954000d0200f00d942d02c0400145038840ca4401d41c3c2c0041421605040c00030750030a00301d80e17000f0b1140004000a0304182c03407107003c524010101040d01e613464000e0700ca01c071000250400c2e405883c1e8982600990105101030340190008540814040f480c18003800b00b00001d4005401c10011060113000c00268040b0b07264000741000d10b801a100c09285699a404450300769241d005031000050004041d5008502d003000b0500d2600102400311640788c040304c4940100107070400003582006244800c82c051719419400060240c0492103411800c0c1454040781d10700c00750049510b0020070590b1305254081c01c50b10142c03000f42c5da07000c0b6800c07855036804000710300684024411030003107000a60780d1382081e0690b0010100d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 716961474 1250 716960224 716960239
    0x80c0f0304060201142a040b0c070312170a360201020c0a060509060a0e030607092408061201141501120b0619020c060d0f0c03090302100207050c 64
    0x840240e03903940a4420b0728095400c05182200c42d01c2401c101070b110b0b50a040c03c07211032030840000103000c00503410740a000e40c1c10a1002107a040030242c0a00020a00000240549030445c10405d03031121b82454003004000d07498000121100210100f0b9070411032102c400b1440207030854403800120702000f01a01d045c4040f041981c11082c2e0402914001c0b4000e800313955500c0c0181e41030102191940c001c201c0495020484103102d424814000c241920b182d01e0219501c4a1020000c5e0a00c0c0b4256900000141c04a906005206521716882f0303503940d014021030000c00a541002d060700100501103442030240082220b0000c4080d0450808109902407104451914050801022111811003400105517001443d0140500e11500d680c00800601141c1000c80309581000241ca894032804114007610070f0702c0c0c20b5a1998005017100c80340958010404c45078a000d0b24003100c152062450406040c9202c820120342c0102c1c10b4041c005813a0000369540e501030074001c0c50051401000b5400508 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 716962724 1250 716961474 716961493
    0x20319021f02070b1308120403050409020a05030610112a030d02060a0506010305130f060e1207031103120106141c02030a140402061b100c05070201170f0f04080c 71
    0x1c1503402040101e200b030741005481d4440801280032010b040380c1c0240288030070403402c17481c0a42031078940ea02ca03109141c00c40c03800b0340b81d105010503a0040348501d40811408000e1040c0b5150a50182032a410342c0d103050840f840d0012006503440961803200c20204d0210b150040145241c040020b040241c01360440d0841424030740002e5981d0340072510040c125161001050456100f030003141d0048401c0080c50000c401c5c16120305211102400d8112410340d0381d4050005000c005118242c2c02550640c815a00d035903a40c103015002c090f80c1c80681842d07400c10840c07520080c04001c0c00d50b06590241ca0b000011261030340f005800d9208804a0014007146001e210512a529400840c81006200024055a0440e100301c0481a00c155002944404203011030640f040e40190000c400c2e541c500112442c405010580e28111400070312440c000880000d000c20555801c9007514103012070705089a0880d02d03110303298410307225010b803100002c0e801010101e0b05014250040e0b0b6801d140c0c090a0310030202 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 716963974 1250 716962724 716962783
    0x1c0c23033c0121082b0504060b030c060f03130503070b0910060909030906120204122913080a11030a090905010b0a0c0b0703061503022802031902 64
    0x41c000d01c40d089802c5205000c241d0400c015a08084102d0352080c2030504206140020b03000b2443ea03c1d180302c540000342c140601c10010640070f5640a5030081c00c002645007544400c0c50b04001c10710310018011a170800c510f1400d0440042120342c803014455484121080c1445c14600714031401f9005000541602c040c0404000c0102d110800f940c2c0b014008c1207020340e0f8a11850565000d404090086a0040020032083d805550094102400c1c01c4e40140b901c0e8071000300f07451403003144500355040e903500c00d50b0b110300f5840061403600c1c0300d141071244c00ca0ba00d403204002002c00a503071030040164002050024000d03000f5100c0c1d040085c2c600c02903d40724010200d0041c5000d28a1246110310b6090200000300c9503030701c40484620074800e9580080030f44164662466480e0064804801c0603522000020401059042940220340036500541d03a1048000d1800590901c3c5d00c80d241059164440849081d4002080703503002c1c1d400740c41e1510900180e40c82a810000b1110781f426104102c2c0c9130b40c07011030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 716965224 1250 716963974 716964091
    0x4e0a0b0d0209040c0e06120d0e0103020d112223190801050405072718051c0906030b060d0911150702011107030b010b0f1c0c2303 57
    0x12486080c2c02c09050f81c070401045514080b00410041f00e401134846018090300c294030351071051710107040151900c9c207a011400100c40d055260802142e0700401c802d001c0540c0b106546048071849d01c0e82c212240c1c100300d012032042680d03404a1247c2c035500444d80e80d881c0c41e800e40c41c1d4582c07141040703684130320350780d413000d450213800100c9044519001d0404040341c52001411004003942100400034540140c55016070002c01c03181c0980702072418034402101c000340c030802241e100142c03d500d041c22034540c0040007402422301c0d074121509150400068980946441d8103481c20750010b02c20224144186080103201d4460043c10130360886000c0303031440d060007002c5004250b040d01c00c0c0d071040c0300f10800404030344d03c0b41c5581c0001405407241400402920021030082e200528101800c14680881c840115031700300c0b546851035441a881d0344881c0b0b01e07190401a103141c4104208a1190401c01c007540c030b1031003440000d0444a1191907a16100380c03030170086040452269002c00c00ea400c09202110081c00d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 716966474 1250 716965224 716965229
    0xf0c060c0f0406231209190b01140f03010c020c0a09020711151603050319020f03070c1a0103030c0605010803072a0e010807030b070c080702040c054e0a0b0d0209040c 73
    0x11440ba10101a290247e1035090207429074000419080513400c2034580300010340000e0030207512107859401440e4a54080c072808aa4150540090845601c0c110602c01030040c1548007518030352040c001900850700c040307003030808040210b600b041600024100d820050141818080c00042030042800070103401000850003880c508005040c1c18036192142010380c454186021541001400071404190242c00000031b071510500842c05404046000031460300401da000b40e001800e5405d0903000d1010510540b40034164a002841c0b9224490300c0d0040301c1c0c4801448419215903018001403603c444404503806000f014007910810350307541e010503a41c0c04190000381c0e41d2a0b1030b40e0120300e03601d01030540041d243c0e901411040c10a00c554013000010700c001c80d41e9500b4400d0400c8041e035200460b10482010158213500350003c18404101002c0c40804540d1440b12101d04405104000150001c0998000f02c1a00301140d0313020300f80c1c00b04182401014000350000c04140030b100c108501c41012009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 716967724 1250 716966474 716966491
    0x501020d0c1106071e050f01092003070b0a02030316050a0509010e19030b0916031a19050a02071b050618040608030c060403020c090105060403060c020703080f0c060c0f04062312 78
    0xc607c08800d032003422104c52020003070a06401041c403024080040e0046198100010141c809075075a9902012040d44880c0c2c2da41d00603000082001065000080c103e040c001540c64414182409444054054420256044d0500441d600c1600ea5031341c9a0803c0e400c00c0d02c41504030071209a80c0e1410480c1c0f114165492445406003032500b00282080104920440390086003400c00031942d00c2c40c9000d40c141c090800c1d181303582d019020561245190042c0c50149030707003450043e910205814115000070552450a203150142c3e4000c011039621582646d0340481c00d5803184442c1d50355400040c000300800e42c086d8a85010214604280240200b1198400e6000b80c01b5192560300340020000056000d0284603407044d0140818000305405601003840b000343c50044540c01500c9881d00d10540e0800540b00754003203000592400301002c00d00c001600940340c1d171091070820b18201e565114a00035801203808001044821040100030600102c204034568503945555000c9948140d248c1c10081b5645003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 716968974 1250 716967724 716967733
    0x30218042a030c030501080303060a030f03090510110d02070b0417030909070c0b0711030a0e01020a050f07061b08220308031e0c07120e010e03030c06100501020d0c1106071e05 77
    0x507614801000b103920450000f415038040340e0940e540d3780c41c8000c41310700550400020f45400324494a030b0707004480424041c1d8540009910f600740500b803030502c42113056811500703c81d0080001010103c155005d4900b4103100d82504510003071024610b014a8000f960b219443c0c00500c010542c01c01d2000d1852802019141015542c1003c2903403041610a08070009600c01c100030140540700b0208120075050500c140c1d030110b021610303603d25108500700004455041104100480c0b60032040c0100ea451403044104091038107602d801e10503000b03000c400303180011a0748e518419443c0700903001001d103a10030000c98403410030a0301c080b5982061030302088051810b101141e69240b5550642e1600d643c00070011000184d18681100d00600000641e4140031050004407c10b81d0f0034009081c044070b904004002d18500000000e0b41060540e0105040d900076030040707040c042e40b021480c40d4442d0000481c0d40034604620104801e4850312070050b024203c0c060320194032113032140d0f00c0d1204600030030072503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 716970224 1250 716968974 716968979
    0x11a150301031e0f0b0a0b0306070e0307030b1b07050d020c04052208040b0c06040203010c110334080c070e01080c01030b0f040203010e0115030218042a030c030501 72
    0x80040c0c4000e00014018070b0061040b200b26031507504448004502c00d0740130810070b00e4582d550b11790824054800440450f1a221699111f0808111856201000d0720308000800c04002c0420348070006400090008809000050440203840c050002540c0150002c84d0390345001d0300380203444884007502e42005004840180803280f400b40580360182100309900d05030000108482031000c4c08801c0d04455009062000007101c054083c054500203000001500681c40c25104040c21218060f18080903c01445062400d0030700000545104401c0080402c2d60703044114000c100d003d00120304c0b400d060300750303082e80c401704440200a410305040120445524030f456039503029200000b40100003d503440603034020540d42c0300b03070403000d840403010303000c2091a00004045401c1e640241c0001103600000401040301c25039514450603010f40902d8110b082000b01181d542d92441546103c5e8419619108403036625026050f510701344865000c050f4a444a0520010300a07014000c00c1c840840c0c50513000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 716971474 1250 716970224 716970259
    0x10b101701082a010201141005031002120f0702070f0312110a15020906160b0615031014220c0320040504021308011a1c0201140c0a05011a 61
    0x485151908a2075200303602041810705000f0b0703000d501c4080381150f403a4000701c101100081207040c00b60500d500c12200032030624090500e0b00d5540b01c040349090b84100612903032140004244d54024120180d102950384500c20124602130580d04442c80b07194984000104000b01250503448100064540d00390f82c10546060036103401c002c20008d403400d8102c85ca4400c00142d55801001d03142001031810341096500f002c40c2040b0f140603601100d00107010b000307000071481c04810300600c2c010030609152441c81d0110019a0001061141c0c9800d600e1950005102d81c3d03641031180d401044503024202c4032164507103040c014284034044400460700d03214455402d6180da1610b4034200300b00400c62132800b803404e000e200007588440701076800c0700c4100102151000f000e00840010b52410038801e20503d0350f00b4100302c00034a0078240102807081c40544540141d82001c2c00001c0c800c640b14116813514401300680741440b07115040103185518010901d8003005c1c0b44420000b040e203055070304810b0388150003075 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 716972724 1250 716971474 716971483
    0x130504050f0c0d0f0501081501081911150c070302040c05120c0f09030f030c0d09080a11012a05060106111903090e130213020a090e0603010b10170108 66
    0x15004514020240040e4002e1112402000c0c0b602c43c504002075040442c1d100f0404880080e081404641c2100c00c41c00c003207180030072809000d003512001801042c11035400d400c20101c00300300c0060140040c2087c2038542d59172001d1145002813040d404641c0c0b640c1e050901e507100c0d035440c00308a03c518030f09055010150f01c10001d5581c8411500310380903d07a2590110300320f81d50408903141210140c1040803c0e4680c40500001c1090300c82d8100840d00c035018a44a1030801c0a000c25900c01c004005c9400c1103400790000d5145440354200e400181280110401207680e41c101c04280040d8414003405c41d00c0c034514074400c00000501400130b4610301d9032030740c0046410560204910950751f1008060302076034260301e40c04601d060300ca030404600c010342d1402442d075100d40480b00038646003840c0f1906030a50a254031004440e181c01c4c10300310300c2c00d000c101d405444900d0038010100f058103640001034868030700354084181381c0401408007643c03022502d8014001600d02c000040e0a00c075940000401c40800034 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 716973974 1250 716972724 716972731
    0x6060503040b070f02030a36180911010509031e0d02190c030b07120f1b0903080301090b010311130812040e1305011b08070224060d0f0b0a0213050405 66
    0x90181d032805103102e0f000c03249112100d01c01000001145c0072502030205500d001c0d0940c0200701d0380302c801a481c041112142724400400301c07486504103440348000442500070650811001d0074025241c07540e40010a00e084071b41d04030710135412041c40ba02d40d4915030001d603c03210804685d003160745048061300a24111901500010181c840003c01070002449100003e81e01600704e282c071501c95082d41c0078a0007034442240e040402ca607981c100c0828400001222006100780720b0600c2014585503503111880c612051058a880f141d69900c031a00d281e06c40d03000a80c0102034070040c40c0d1510942d89a01241860f544a83d407090b10681c06ca00c56082e8580701620100d43c240341860a0303907900d0030080e03031008107100400c803002d5589900c24842146071002c030f003007042e12581e40c0203014681520302078601119000b54280c2c01c00700300c1c110340c080e586511445a01010550718684c01c0030b45850002080100342500800c986151010810309020b00d601404244041102e9032645660302c1050108030340080c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 716975224 1250 716973974 716973977
    0xb030a0c03060b060c1c0e01021903050a02030d0f0506042016030e0409050606090601032a18060e0f091e041b0305030306031605011d0a0906060503040b070f 69
    0x204200045140b5a104001408000d4039480c58080c101048605283c001040303c01d262188000f6607000ba903010500c07888042d070a00090800c0c410007800240310510104008080240c0000c0c45800c40c0d2081c01950000307070540e5001c1c0032000e403d281c2c60000d4801150054000c500e0040d42e80c0c095580c4034001c4036109030300c0b9007480ca02021900d4000e80b501c03c1e404241e06000000000c1803c42c1c40318403a0034a05d901410107000c8509040c1d04001c042d2102415607410107017002e6046904052801410a004c0c800c0070594445c207a00c070340c083d201114425038031b10840c6004a00080c801ea00111401c50010003160440b40544002c401c00008000a507081d00c41b452202822410881b81e1107c0e0903007140c0185902401d100ca4880d0551600c090340d00211400d0b0008020302c000c0c0c0c1801c01000c041340e659000881c0c246800d090000b01485a50505940c2860305d032000d81d0641e44030600540081c00b4002c400307106854686002a00b540d00c02c2c1c0e0110b41101d41c0a0019800c0c40c4a0f2410400101ca103 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 716976474 1250 716975224 716975243
    0xc180612030e0301090206030f040201081819050c0612090d050f0702090703060503030a0f182106090c06051b0129040e0a06051e04020d0b07050903010614040b030a 72
    0x1181c504030340d0142100394140e095940c4004500142e44c0f1a07020310302c40d400419050035589024400144040400f50420081590181005020a1000c10442c006111040417140c501000d0b01b4101d103862095803417075800c5480010400d6101c0c1c0302d041c0040c072580c03000c0e0488240c82036131103088030140301d561125014039030706200302030040c82c0620b4843e80000c9903240101e992619003000a0440d400305403040c0110350712901005040c1d410107020f81e039080c00c00800000c0c0c10300e003100d140c2101070001c41c4588200c10b101100c104001c00c075805550400e8009030058038540e1600f40140c0300d940a40d56005101c1c4800d00c6461554805005660441c942101c0501c50006900c2c0389070140c110183d40f40341d110b0b03203d2180e000383c80e0007004014401c90040c040481d050910720305280400070208410a00e600180080201607101c19000705a03c03540040440d205507510901240c96004007102c895055090017070015500d000c841052882e030004440400c802c1075401e003010f0fa50050715800030303c030040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 716977724 1250 716976474 716976509
    0xc060403030b040e0d030b0a0e040209010902160b0726090705040f0902120124030b0705070309090911090a020a0912031106100f3606050d0c1806 64
    0x460303005520010b2010740007241181c01c005940e820300e243c1c000004e0010340e039402c00c8040351503c2040380b0000c01d104071095042d0305103034001c68001401401580c02e41900050310a9415a036a24542202c6400c5000c50030075082011004080252000c103004c4407000d0000380929407107c0640c00c6008000c0c510040c10b900b85003c0500000d80f1103410070984040e5030719560000742c1c50310b0f400e101d11003242c000005043c202440c81c200090351004540c14007484080302c203000280243c0e0340c403500400c1d142042a22a241490100d03510700e4290400440d01d07083c208070708200643c1c4051541052012200005144c0c2d0302144141240203004c1da00000030780c00001040b00f80280301d201c11201e402441d001d140b10120840c1c5d541b406009640e10440070200c1841000840c0c2400c9142003d4164801c1c2c0800201428441c02d8948400704583c4401c01c200302c0c038511422000c0d0f40580300814014011259465071030803c81c40c004154890200428075424280e450007059216042c1511400b030b21004540c2c9 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 716978974 1250 716977724 716977727
    0x5061809040212010603080405030d02160e1506070f0317060109030b0405030c0d0c0c0504020405010e19030203012412121808060a060603140103020a210204050a020c060c0c060403 79
    0x3440030300300342e801c0250b01251198850081c040c0a0255028a0071583e8035071601e0245460040d40200020841d00300300b07564400202c24000385001c030f03503440301c032251103884843d6120340034040036080542c050382c000b491008000c501c6070849041400783d181d801c4006c110030094000e1000465031680040c6407094148002108003040603001030007241100c0c00c1000321400706241c205181700080200f0388628941e410005101004001340c801594150300302450940080c0817507018a007007910a44c10010301d07486c01810100b8840040da0000d0091180a50a1030b9030380500d81426400301003c11124804030301c22418004074103010381c0c05072545084017401201201c0302d1201c106041c01e01d180f20b14000444010400c0140d008407481040040e0092810101804443e46500100c2140d00c05200400250340c07500e24070380403508030780480c1407991040d40d4034080c0c41d02c000c100254070603e0003050101001480d4003421094000200b00c640c1070b00d07500d0741618280101c102c0d291055012000150009 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 716980224 1250 716978974 716978989
    0x5040c0501031a0a14030601060507170a020109151a090f13150c02070e07080f060114040b07060203010305010c0c050c041a0303070303090611041a0a0203070b0f040b01050618 77
    0x2a50946918000c95044000445001095000b100f4031303000e0b50706020342486c0500620b0300512203402d240d45012080d60f0741c1d0510404940501003180004150b00000d64003e401c880c0d5070301e0748400f01c48440703050740d4002001070407202e194005001400f201c00140381440c0521a005501826105590f81e451c0f0300300c6035040003841c00485880880d00c0001940e640c4030b014000744226260007030300da00c0f42489084027102078010010070402c0f10000502440ea0130303000445400403c286040400301020682c1a0340c9441598072001501c1d800044178030501051341c3c0a94143d0b8800c100a00803035040050032a40307200300b100b007e00290400000490b080c5400c0e80030800900520b4280400465140002400c0d6007141006601198458030b010041184138482c4490b2a0043c2051504160424894280c1c502e03110000381018a400665911124001c00541c0d510943c40000e0700600d1070801110b1042c480280c8007155609600400410b0a14258080e0768000560701d0b00c003e5014103030340820170a03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 716981474 1250 716980224 716980241
    0xf1d0601030b10030b010905090d30150b13060f0807030b21030909060a06090501030213080604030f0909180818060307020a020111070e1b0d2d05040c050103 69
    0x1030980f00e4100000040c00d86800c0c038020a0404000221490614003a03400c000c0700c81200000c00003400c00180c3e0302d80d0161030103000d014959044510318035002d25460000c01421400c0e1301e03030207200303240041c103840c414000b00150091880f003142440ea451406803151000c1001e40004030740e62100040780030748a5401100718130801402e403000301440e40010bc0a940001840b40440d07000000d0507062814400d40b0300350000825291149418901140140f5040d03007800740360304060700010303500700da0a88805000003610000050712003a05291401801c1607608010000105400110015020065200e02000720502c0700180f80c1c218200c0d03a0384101070f4440c141c00c00701c0611061901038903468260265210380002e030001c04035000280005000c0c2d0307039003000d0b594950744030b204e061103102c10303007264a5041107a00300c240b000c0701d084d00000001da029038402e40c0ca14a00d0094074151410300020540704c6610150051082c104481c1005415240201ca0242c0344101c5100e041007954480e83c4010003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 716982724 1250 716981474 716981491
    0xd020d0c031e0306090b22020903010e010c0c140606010203041403012d1401050f06160812010303032f03100518040c05031c03090309080a05010f1d0601030b 69
    0x8012084286407001c100380e03802d000c00003991800c0c00e1001d584141b14400d2032071800c68000002c403120f945031a90200041000220356500448c04210a44094120611580c4050001d0081d0900298018214411000180d40005216000d4180308801048003402584180e003c0d52520f410418004030560b01800030740c0d090f40d607400307003d900c040c0f04600c4c46402d6040744d1101c1210031140c0d030788407003070b03480115007030b00702a4560004000740c1d5118011030400030002e4990503241c0d07040488401c06d110a090000c0c000c01800581000ea65103c41d2078103060724441d8070100100401b0000d55003c400303d00c0e00e660366814041e1a1180c007420a0405144d020410744c401000203501c9402090203504480303d08402d40c58603400748003c11942074185400307004280c00801e44c0c49500390348070465210130038090b07091550f03904452003894412403034000034250b4002112802802c6c0d180041c02400c070106044000f52801c4000000c131a0341100c40380710103c413075000b8444c903401d43e114004600c5c0c02800c2d850 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 716983974 1250 716982724 716982737
    0x9040f1203050402040605010207140405041703010608090610030506190f02040902120a0b011d0d062c03040b2703120a08010b0f0a08070e030f070609080d020d0c03 72
    0x111005040c840d0289240d4020500d400c29206000070740c0c0c0143c005a065400180003841110722020101445140490780862103860304c0c101100c00138800c009120940c1e0000001191851300304000b50f0080d10700c2d40403111241d4030031f000c9a08844080c04020516000080441c1400c00710940104400e201c00c000004c1454900c80c0420480c2d005134480c07081607402240c5280d04444882950f9849400010188002010040024440420788101341c100d0080054048829201c015031094801d902079401c000858050700b2041c010030803040001682c0b800c00080724440c2002000352022613801c19080d60502d01c04000e40701c1c1c00d98140c0c00c514001d40d4500b82c1030941d03503420420301c0c00c00b0940b1001c0b01c1d40c80c1c000303000007442c9120507001560b045008202004020340080100c0d0051102890480c00030344503580f0480d400400175480300da0510a220181f50341c1c280102e401e50444091742c03582c0840940d80c01103184c03117040c00c10303503040541c102a500b1a4420b0141d007102035080d1281c075114 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 716985224 1250 716983974 716984003
    0x90e0708060934030e010209061c0f09061a040b10050a0309210207080118020f130e010b030c0f0604140102120403030512010803090306040305130b030c03041b030f020904 75
    0xa02c20341d10f03110341d10b0042440c41650f000036034041c0301d07848001e212000254685400100800c1c6548200620751146601c0d050144000300c40c1c46d40240403580740d504091200c4061801c0001c05440494003d141c0c041500301143d1040c5020310404148090180213091011348240c01550650002c00c280c005242d16149220009024001e90541d10942d4010019050204c40d400a144c042c40d90014800350385886440300f86070010b0b4001c68083c66044035010a01a110b101081d07998803030380f125008060501d40a10b020500641080c030640700705a00311a44000c001c0c08101301c0052038038485400420070842400402d01c507448048003164103004407201d80b50003000d2141164040e60003900015404201d244210040a5446004080d440300a500707040401c00026103401700544010103110b40000c2c0021500d0203111100010480306091640360300d021440481d043d4401c40d02100d8000340e07030a60a41c032201100124040d030f500501c069520200a500384025130b04040c1043c0c9000d071420510 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 716986474 1250 716985224 716985271
    0x6010e0a092301050106080f0a0906020426010506030c150a03060b0f030403080c191d03010e060405190506011418090d110318011209050304080a03090e07080609 71
    0x11040c0e0b01115a5580d54911403884886003120303410380054041107900d4062180da09102c80320207802100b2203400060404c0f0351300e0450004d00c02c0350b100005810544641001800c1c0c080c0c0c00b140b034014210000c0c05969946410581c0300c1d0306160681d03a002140000d4540e110540401030115094942000143d960700d95102d041c10346c1120300303100061500001004201a07004040581107201ea00d9140e050071040290b0504038003d07601d40f101001016103c01c104c5a4040711003506151015000300041020358410540781d40d0125000c0d64903214040524582842010401c40720300d03009409424242d09045440080810442c00b8940c0003140340d00c410403184015124a018401190092038040704103203025200c00208211104990024840261240c5190310f551004d4402460000076070041c83d40380c04020224118040c0c2144404600465103283c0000c420400c0d6019844500d820340d56103240e500c0b04501203551000145080020910074282240d0303803070308074030940c3c4d2444d20006401034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 716987724 1250 716986474 716986493
    0x6211502220503070605071214030a2703021c140301270c0516050a06052712040504090f05060703020307030e07050a120201021c020304140d0506010e0a09 68
    0x10042902002031981c960303140328411100e00910342070700948800d038601000541903004004010303129881105140c1517861141d0f10700e03610302c1c1034128941d480e0700348402400e004000c03030051145482089003503820003900c003080d05548a07606034001c2074404140756201c0107904d0343c0407c03402448692658901180740c200083c41c0070b0442280315004c205450312000740440c000ea92a90855464410070700f440e243c1c007200300c4104a100300c4421959201602d810703464100344180185c011841c1000b0302100340b1402e080d00200c103507401640c0d5985508004c00c030b40c41b007001e500540c960600c1088100b205080c070340c0040c0f600c01d0064907042600d481680b116400c1c1b08080316202c00190b800001c00c41e4903070301841624a0710b010a402002c9045c01d103004a94000c3c03146c0214900180e1102c1c040085a20802c440f00440c0c004a0021011904210000c0e5481c0c009008071904c5689400e140842801c141b00b0914010340c0000041c40241d00c0d1aa291000c20806004c1504480e261990070010458010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 716988974 1250 716987724 716987737
    0xa020f0708010c14070309050609060706320c03011e09020703030b01020706050f0306151b07291611030a0302030d3803011409060702060a06211502 65
    0x5001051640d0403c100420b00c54948041c1c0960f030790b080c00302c500403a50003c00301c010ba90081d510302e6a038500c0c070400268036001d5410014120303414202c5000900640101542da0024151a203052283c01d0203d80340b494801110120341c040d1003400108449d449801c030307100b030b08484241800006034842c140b11003a039010803400e0340480e86030b0340c00025559040015000402c1c0624009081c0401d4641020440c8400b034100e9115514964076a003a86e0310201c11a400d540c03040c403d1a08200294034469150301091152220105c600114000b51526a040f201d414210480089107841c040d66001d03241c010303918509449a03010a084a005074508004052966010740c005584804600000703d09840081d01c501010041c61186248401e081e0001c28001400c484000c285c1809040082401000c654603080c0c4d03c0c64100091042480000c00d03034a00070142503003030b11038580d81d9101060a483c2d01d0b01c00e02d104507620300c0706010000e120450808003207104074000d1440f0840740004105a81104 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 716990224 1250 716988974 716988989
    0x609150e06010605030618040204022b20032205060702160801090b1b0d02030406140a050622020c06010608100e01050a050d02060c011b0e03011b050a020f07 69
    0x4030440484084100525401008079103020740c694034006005c40c0d102810a1943c0042d8030780600810219680c0b038041e00d2411008441c43d561003800394404490301c0c0c9a0f00b2465020b94900b594450038400e94407548514a004912003600c8c42d16070b482c50b00c40101c0108403c0d81548031581c03050000170014400d45000340200d50040000001241505004404551200500b03a00d0910107000180140c5480c55000440a0748480340203140c2c000401584203070108203414900c000208000c1003500e40c0003400100d2030103ea41c0041e42d400b6211003c4030001c0e600c040d4000032001083c8150019118003100c02d0401e802d001d0f090844804500745049801c1e0440c5002c58910400c00244105041410b401440000400c040365403404002c2178a050b2107004d85800390250700050000d544810080f00c0300034180100030424036400320600d03a142a07040070508002407905d4206052840c0500a004034003034890f0a1110420043c1c1c81038035190700041c0c9840c194080d8105c0b0301403005082c000f420003802c80 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 716991474 1250 716990224 716990231
    0x1e02010b0a060806030a112b12320903070323060c0909150303031005120102040501080c0c010b03120409050a05070c0213060b130311010f02030d09060915 68
    0x25034200034640d18142c000303008008001c0100006070b5030000d080e1080603004510410000f4040010030596002c00c05164800041d01078800401c03048004410358160107240405420044840f04981c0301c109004190440840700c01000c41c0186600144502000800d0342c2c3c40c60b240251001c2400c0c80d0460b4001e44081d410911012006c010006240362801c0e000d2018024034506000610604d0181541d4240940148000900d040d880701064209001c0300800b01c03078880c03601d04e1034068111003e0148a0013901c401402c0c0c070b00704e6414001d0342c0540350305071100802e60382c0d1803090341010342001440850b10f43d00d51001c10003e0702c0c10720410701000400306029a42da810030710124250340001d04200321305480c110411003500d50049403070904950480303491512000d000a982c3c0078020f26004000c0900001030b40c01410250a040c40c811207201d80714062017403c0032001520155070044052015802c2009006000007040c0d0060541e13502c0f030100040c1c0300721035490300503060080c1401076406c20394 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 716992724 1250 716991474 716991491
    0xc030b06030102031909020a120819110316150c020a0303050c0315010c170301090f0b040b10050d0e03040b09240f0a02070504020d1b0804030804121e0201 68
    0x44202295500c418260020362035420900105411000b50481c1020701d140d40e03020074011540c408031040d009003001c00c0e01800c0c400060800c03c0d0650300c41006a440d05440081703165116005090503001103c0b542e0145042504603128000c8260501c001201c20040ca4090401807a03500c0c0305000c1010b6141d8000c0090141501d0050101d4002a00e0400c1b4510188100300b10f0216101c0421880007081c0382141c0000c0c003c0c60580d64500c1e4007100c4029031750002c000407521500f1a846003501c141c00660922811038034005200c101c51385e214220303400402c0500b11104241c0524005e100c0107600920024561402d44080390840d0051742080e19040e6002070402420700c0d280f083e007050a40c2c45400300d2032022201c03079112400d22403400d0a903040316003c55102030b603a0003806400d004040c040c100755030f540014040d201c01403221240c507100c0d01c152241d0010600d80306099180c804c940c15141c00c0020344441d00c0d20b40519004c01820010050380c001118071141c84500380c0080d030701071500042a01003 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 716993974 1250 716992724 716992733
    0x9010509041815090804030f020d0b16090f0b0a030c11010c09050a090e070e071701031b0b0c2e090b01080c03010c0203090607031b12030507090323190c03 68
    0x1101c0f076500c42190901e6140c07408200c0030000c843c200c9038018a140c0000740c0c680b02003070341d1404452001d003402021500b0085a20104903140d102c03c02030395140340440b502c8190301c4040c00745c0750040b0208800305019101519001e80c1c00801d101c400c1e414640a100160480c0c9400d68141e41c0951000400c07801c0108414140741100324007030a02d5010501028540d1700419a50700100d00c1949150346001010a40e400c3c010504c455113545004418802c03907840b070410744004c0e904001140c0500c01d80e01d500103501c1c0320041c26601c1c007500e0039019261400c042d182d2241166201d8032004185160400700e002c034040f0a00c114010a88602d40e80c03a00ba625041d0940e040400b00c0980a000380d0501101c810056404412200c20070000c031469511001141000c4500d044000d1540c003864444408850501ca400d00a01000d0b509507503043c080ba945120080302c00403441c1c80014030b44000b1061900669003070128168504000c10200c8414103201c0e08080c0840c40d50001c00e54080400074014024007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 716995224 1250 716993974 716993993
    0x11505241b0c150307030c1e110d111504150f05060a050901120204150506030f04060b0f0f060a120606180905060d121b0b1602060417090105090418 65
    0x803800c5440f8407540240c1284122188001031010b003c050b550070210342003d01802e000c03100d4609125081c100350028060140128000a01540f0700e0310504900e03002092203900c80d2001900710343d0107400060b00800d0078107040300e4007800c1180d4400d201031928424102c54070540c81d00442005000c03585040910520100e480e00e604541d004121050040c000880d01c50300165203594143c0700059212a541d0440e0b03c1c9140d00c0d000150b21281c00005e01656080450025016a0280d001046400b2203030302000158080000d010380c10a03840c080d0f0140da403805074003500d800b01441c20041180c41501c50352108031290b0b034000102040c80c0c12902c4982c80b11000c40c1c6405098807410800c801d042903c001500d410740848024280680309c001c4614107403042c42040341c0b01e1890b10200b084c4040c0362400c8034407002d003140d00c07000242e0406210f4004a01c001000c6000e150000c00920490614604c00102d5601504555044c00001c00030b40d1219203881c4140191004c001c00c0340ca102080074500703120704 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 716996474 1250 716995224 716995243
    0xd0606180303020715020109020603010b12090c1003050705090a0b04080f010203010b0d0b060408100f050601080f0f060414010801020c0105010503030705070b090d0f140d02011505241b 81
    0x200e080c0c941800065000511072040c1c0301141c000064140c64940b0417800742c03040c0c0700001e401c14004400015000c04040240c200030b02c1c402001c4c0016a2440710155030b66071100c9507158840440302803140e405000c0d512143c1c2204c01032421501c0d215810011401505080e401032114030b90005003017095a07028082100c00c01c081400961031540340c10301c1ea0200c0e004d17400d0180030117569603141c24a20b940d000100c0340188100800d9418849010803000014103c1807401e91000e0708100014030342c2e40c403c6c4c1030707030b40b09005000c054486601da51264142d03140000301601d0700a5900c20800144100c0c0c6281c1d180203141000025950310741150b4500d09458040c3c0c00f09000303a100b130106d500000d0002c03505800b6261004040c0342c844d59500000f80c110095000060072500c0018503003818041e50701207030148410414201c81c000305140600f24208c135440d56080900c104551014445450180d00504e080185036549142500041c607944900764005000151228018003c402d04101d06000c2d9441 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 716997724 1250 716996474 716996507
    0xf0d030b030106060c1209080d09060e010c0201170a020c010e0a060f050f010e0a110c0109020a08120f0304050106241407080403060b0307090606030e150c09060705010b03030d0606 79
    0x10302840e08402905c4001c1210006018507400101682800d214030040d100030604c41d021101424244600a455440c590041e013001440038201089107500074000210b0450341030351000b08030103030760424400ca92800f428010021b82c0812000c03210311424050b208101c0c8100000c1c01d11194980b9048080303e1b50421928000e900348420800272030050540b07076045034607020b5103a0b0302c0d84c0e130550100b0040101710800d01e4502c801281d00c01d0510415444010020b1007a110403148035101c05401d540c6900c5807101c004004820004025198210340181d03410a10560010509949442c102029403031a2040d2041854400075178462b900d500c00716204005003039401413440e040d0140c482e54001e114601015000c0c54940001d000140c501300064002491501010040a07442c0d41d0014080c081c104c2e85242d0502c01e20003d00419003000103601d018010b00b200d42454035041c00300b8030000d6081150151155582c0305071125107030f103041c4010701e01a548140001072a50806030f001d031203003054460307801 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 716998974 1250 716997724 716997731
    0x30d020a090f0305030304030503150306070801030629061803060a0b030d080c03070f0c17130608060a051c141006080a0b010e09120f04140d0f060504140f0d030b0301 73
    0xc82c8005c01101c0e0465010b00d003141c0d40356981905014039840003c801074140c4510000c0240050b445035801d41a41c0c0b01340e5040c045101032004403101040124a500c1c6412413080c0c15040f03500c1c18800800100b1034000803940c202824100007420160104d07000c000454075008105a01e1606000341d1100840d00d0400381054103005141421501000f09003d0a120401c110003a255000e1507158840542c04004281e01d442e9180c92880183c00140300340c1c10045500c000402c8081c041d41e4154461000504581c200c60301d08030402c81007070019501e099030300304132005c1880070409a40064043c0d512000040c1070a10300960081c080341c04a40c004c4145420200315a40002c90040c0036904450481d1135203039254a13a1000ca41c100407001030082e01c0050300090440300017071030074081c02c11140b25514044c3d0641c040c40130302c00360426490303001707048249804058002441c0c0f82d2120390840d004081030b0041f904230a0425241411800304002c82d6801601d45481c0c882e85030051065807001a8000d1 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 717000224 1250 716998974 716998979
    0x6060b0a020c0103150503030313020907020c0916031d0102040609141f0504121a100303021e070f060e030c04020903070512191a0903071106090111030d020a090f 71
    0x75250b2214a0569040546901c407803002c0c61a5500d80318042c01004094036170724140306000d015207140d031442c124090601d0000044a5a00209400b2081200074251a00d541c0d984a02d2006501060000c541456914400c10003a000c40c40c0074032260381d400c4000141da40342000d0340a44144c44075441981d600000181c01d1070ba036100c0c0041802460b01480f10a05661045601662140a0380d0040030003400700d2900c540c180b100410702c00090403c0c4040c1c00025440c1c1c8512404084524040640584d100b00c58140907001e0f08540c18120260a0044d0380c4041d449200302c100344c00841d4007110004901c14840150f0345000d02c030440a04204907401c43c40d10900070003182d281c850070320402d0b01c100d400071a070b9220080144000d46030b1300540c1140882c1400589014080000170380303c00c03a0012070300320004404800000c00c8030702c9d036a0891980ba400881d000d0070824180d2118818604105c07021088030030210082003e090000d00d86103001d40c60300301f107140c020f00420440d40408500550b06408 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 717001474 1250 717000224 717000227
    0xb010e060d030309030909110405090a020702060a11010603020a090507020609010606020d030b18090303040c06260601020a02091015051908332701051309060f050406060b0a 76
    0x216070680c0e89800c02261440c842e00f0151400170990380000103c9040449141940390321a00410580e00c040390104819100c1c00b074154100e0082c0e0360001e421090030800405d40d94001c8410090000101002081310b680380e40c00314070030325100e41c071020409440d8005c1c000c1c00d0b41c0520460b54090800c0000300070b100e107000b0000b581c600324002c0c46e1042c150b0391100641d0649503607000500410b90b20540e600a41400780e1000d40e41d9101300d13000c3c2c4014140500c0442d00794820320f401c1c07109142c51842c3d05100b256411000318080e9002d000541544114004000161160180503204007640442820640e190540f0380c5130f01da4051a0040801a0401c00d0100c420ba000b001c480c1b401e402460140503075940c59440c1407020490b45604135a10710030400a440f01c4001e501c950642c2d240c00d43e840c250b40c860303944c216030429005c182030b40c103246012030052095041038003546420a1043d14089018605915668212102c501413a20555280c4040106104590064400800c92150f4081c60241045070 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 717002724 1250 717001474 717001489
    0x19030506071e0f12110c07081510153533010e0d0503030907060c0b04020111010b06181c210e04050901021b01150611030408190b010e06 60
    0x3c04042c40f0107211030040c2240103620001c148100149400c0d5505201804581e581c1d50b18801e41710b440c0f14196200940e040000d442d64000ca11180080c0da055007020041ba91040d01c4040c580200501781111140000d9400b810340400745c1d6501134000c40361022081c600c0812001081201010b01c010703080c41d165080c108040c094400800814034603060100012114081d10080a40c0d2140d0080e41c49400d101d03010000718003401546044810480d40c0784c0090f40c560049820113403200464000040165005100342c04842c030040000142d9652144009011a000310f852400449400340c08191241406448900c9a0140c44c00e0007140c954595180140360340902c01e03100c1130301074911008504c9070007424030308060040180180030a1804410641c000d41090741e001a07c48010a00ba040d03081f018072841000354041142001854209101510400d6400400d09200e2008110000d40318a060150115481c0b113240d0b0054180110f0404040801040c2c012441c00c03604d200510243d0380d41e181 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 717003974 1250 717002724 717002747
    0x1101031107061d0313090506031c050309012a0215040b220209070e040b0a03021f0c06020406030506150a0f11030c01060b0408160503150619030506071e 67
    0x110042030501e070203c00c490320002400c0d407040d010302c0042085094648912024000d071800350f401002960350345070405554910070b81028400e9448d04005100c490320460045034031150040000c40d142800d440d1032075044680280717002480c500d802c054070920b44e0501050300c0001030710501c0c10507402c240c4c8500d01d44c3c00e4040c0a03800000c0c0311680c000200e66050741040025900201210302500c0d141e07501520000d05100000c2c8528076040401c8a54541520f041040c0e0741c0240a030034040f091007a42e40c1d000d04580703030f1500500c4013140d40080024000c0c0018030180c001c0c0c1da03020030345081200038003c40c40c1c0480040c80745040709012800c0d8550340f0030481c2c0c0007484949800000300c00010340650451150159050303a9508040c00807c182000c5002402280c8040c2e046800c0070500640ca204a9600307809200c2d4560444c41101801c0d60310075109a800650040071581610803900840610f00c945a000300d0f03240d08041c0c10800c2c4079411031940f804485a10b016901c49001c4100c00811845200 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 717005224 1250 717003974 717003983
    0x60115030f090233121006021f0b0409021c1703040f0204090602071e0b07020304060203030a0b040e0d02070f0b0c1911120c040516080115020a1a041101031107 70
    0x14070b8490030b5484455000b04070501400c0904c0e13076039004001341c040c1d514021a070614402060b8440003c80b80d200092207038400110341740540c05601c1c2001d46001807d8841c0c0c0d4075602070748462040d070141c0d803018080e000c10b650700245c00c058086035280c00495650012058078003480140200808205e03005064507400f03604540000b4458250318050000703000741280904815040007245000c44c5030080c582481c170740202282081d80c2e0740c1100890783c034403450080800580050012400300512a0015602c48400500106640ca1030b990f58900c1c0030310600301680140d01141c030402a40910b450094064a03880105c94940321000700700c1950b4802c40c0050b001c4400715103802c0024049080728030856500020046071464180c1000c0d03036514031101c0c120034491480c1c01e0205980102d6091b200100c202a6169008181c3c0f03484680d058100300d010081040d030243c082c04400103280000d02480c2c03100d00c001320720b03281e0a007414468000a201c020190505146ca82d24145448440007540c1915611 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 717006474 1250 717005224 717005269
    0x11a090a0e19050c0306040e1207020405130f0b0f010f060e0d0f0203010c050717090934030501090f060807173c160b1803060115030f0902 61
    0x15811900340740031111040004007403900f0140f00d541d98061000758007400c0e007101c0c10b1000c44d602030145c6031520444003112030820001c003c00f4005041a07001958002c1f401d0400714010b60a84e101d030741c920034260804440104140040200403136040e240b85000d015a0148405800d08040703002d1701c407101c0a01da4610400303526400108100703400c4600b10701180c0c09002800040c15090b0081c00c0c80d00702c0801102d42641a004103080c40e403c5009039000e441c001000d001c40303a00c40881124042405402c50058a00040028607208ad40b580a00c03540c9800707a03400040c03c0d031521840f40221101d030319504103072074200130041210351000603000b026581040043c806040c446114070303103004641c0d100580c11407039035490000c412407070540c0414006246648036451815010065440c1c180d032003200040000e440c0c00510130072480308e000e0490302c1c0f16880c94001c04100200003c2c900340302640605811307240034003a8400c440c0e043c09601c0202c20928030620104605070300050400d0b03803020420120694 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 717007724 1250 717006474 717006481
    0x1812030903090d03030b0a0504020c06040b070c080412020f090702100b04060512102d0902060721020715271220150702011d18011a090a0e 61
    0x18802c554480d240200342d03060150144c9806405403011000107072181c2a99900060700382041d0080343c00101005003d400c0c1035480303554011039000b0140c008410001ca8603035100c00195070b0070007440902000c0d00040540c100074410010705188d80c0340365a001d411040306010b242900010002c80d00207045902280781084500850000c00c020340c00305502c40c40c40e0122001042c00468002d00d540d6080d8000e0149000d010200380154440143c45c215140300f101c0c0e802aa005a548018125071000b001d0030706c0e06119071540c00000c0a24928844803440114041481640400020001f000148010340a4114444c4040e0100c01000306e4896041e030002c0d4841882040281d0320ba01411021030800e20300d41c0542000b8a0001d82e41001e84921f0580d8503030f110486c038001e02d0000300b00805480c01c0785400c000d9030044840041a421032120614009407501c6030b9601e11075800c1801071541044031603985401075094142010b03001c881c0c190242084101805d444901c45e54003a0b4482c008148210344 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 717008974 1250 717007724 717007741
    0x10c11030316110a060b03010b180f0709170c010e1032030115111c03090501090c08011e06082d10060303020f0606090a1109090915181203 61
    0xc204543c4403150f0041c600b04208115042c1d000313002044040d0002c00140c20381b42c0501c2511a105810664011090000540d113040200c03092a4402514a0b001035100e94401005d560581c00c01010b004940100e00d104010356440300100c1410981100e12410544000c4e501a00311944c2c5500107500a00034480038044400807002610245140091a039496a403424603040c0003031090b2515000440740d403141d40b04c22000040010000008034500710122030180f0090b001000c0c08541111255201c0c00e206000c9071024040388000c20842001046412030007200492004140c2d80c041541440c005d401c0c4059840006c141c42d003414030f0080411000c0000184076030440740c50010030054450700c003802c404040756401010803a8440e4089505e5154108100c9813501c9040311000c1c0c00401d07403400216021610f801c40b4030381c8045184440e14140c0b512020a440c61000c4403c0803450f804159480c03103900c50f42a550340e009100e0b648100390704070140b0440351140a1041c001031064008404a10301c075 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 717010224 1250 717008974 717008987
    0xc050609030a050f06010501020607030501140609040f0c0306090b04140f061c0c260d033803190f030e010e03030c011b020c0a0b070302070b0301090e010c11030316 72
    0xc1d0803d00f12113000c1d42038408295179a1090240500601130b410215211038028001c81c0d06803003145642c00c030039280c84001c5c031216030000c00722168130540780c1ca202034114607a8801c030f0b0030000d016500410950304100745403064411107040c0c68011460080048101251121801c0d000261001924859200e1800103006540030000c003070b00d2a10441012420803200c044203c3c12110404100c805c10340311640b82a1050340c0300310b9000d41c541c11959100000ca44a64005400c8442510114800c005101800c204030042000346d1410840080d443c030445140401c192084689040320703920a04410b643c41c0060044c0f9060000d050010614076801160300824110701d0010700074040780d44840a101401c0e01a203043c40f00742c2a500041201781ea545880400c0510144402a0140c9001d51428000719a076501811090b02140120305c4041600500d407001540281030082c40800e0307460544043d6070850300010311803c00d106050200314070420003c0b017540c0c0e11501c0e4008a03200c80d0300700d01301039412 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 717011474 1250 717010224 717010243
    0x20a050303040602101a010c11150412061a01020d050904090f03051b060132030a0c1d01051e030c0613060e060f07082d070201080f01030c05060903 65
    0xd4000820b0110744194002039505a80011420030b00c0b8000c109407a4459a86002020500041a007500035000c1024954000510344011f40201e09186413420108142e82107500720f04503880c0082090f00500029000340ba07141c2c011824000402801800080c1d611080111258180180490901d00c2036a466105008643e0004400c00510149140041c100c2d404104520b1503800b660184454035200000d503075060f60003140e08052258180e032505412501401112400d1001c1c0c507061010944040c000640020b00c81c000004001d418034545010002c02180000181480000108495602c0c03e11700c0c0403076140e04e000c4140011005002c241041080c21000350020000034a581c1d2040b080004401180d80541e2682036040e401010080340b441445440700c014202030283c1c80209900200074100300a4440c94194034601c12a2754020b40c80c0040e81c18450b0200109120007135503001450154080c020202d19140396041d0b540c0c0f1051b0a070070b8003031355020700404140c41c005514100701205c031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 717012724 1250 717011474 717011479
    0x301170705100806090a050402063103120f030507020304060f0302120f060415030203030d0245030f100209180a060f050d03020c0d030c120201060f080304080604020d020a05 76
    0x15402c282e910040c000304419100d0a000e00380050010300381805c07034440c7c180120381c0140694580103030000550856080881050001d420030140004a003050400102c000c600c1809140aa80d0316110302400c0003c1c0c40f60050f090500b800c00300030360258007000302c17410780350203040a00c2c044200d80c3d021070003401140d51801000e9100010705c40303c00803240c8110b202e000c0489040c4041c010010700e08200403a540f2000350190b10601c000854001540c018198451140c2004084440c00502109071455031007101d540c21801405484428248a0314181c12008190003c10074048651005a66807290600c61070f4556800305240c00e03281c0c0c031184944030341d011400c0884e802e8108039801030001c000d41d2045040c500f1000c17030b0005480c10103481440070a03406401501c68803004105000c0a40c0c22001c1c11010441101290000104843c45500c08035010380d000003461401c0c143d910000032020b07040040d0036881070000300418540003071425802941502d0880c5298030310300c049606541a5040307541d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 717013974 1250 717012724 717012739
    0xc030f0d0c02061c1a0a080703050a0605150904060b0102060f0708041709040207031107080d05030f0613050906070f0e1e06090d080d0c0302040e01060c030c061a1201050c0301170705 80
    0xc5840409409082c0384003412911100751b02d9651034410b903984094440140340c0d82000c0c0748000030900382c2d4005075000c170f1604260f411103d000d0000070904030301240c046800e2540c44041e4039595030304215069115004104410702760410190240a28000030001030105480d441034030b400c250600250b0741038900c0540255225103051402070b05d82106091510f0301c1d845568000181c180e800070f02d41c0c40b02910f940701c451841d00c03440a05c8100c80f100810064115142021546c0310240c94415540b194a805001e0324450a203444020080e44d10503e4960400c8a511983c0c401580d903800c40340206070500c0c41d24090442a88081040c9001d003901c0d081d80b20040c581d051080c4100c280c0100b16994504504115100056209400f00e005038000e4428003900315005120140c00b403030040307800758020300700442c602456035030315415030304150401210300fa15001c441c055800c04080d00030004407043c000340191701e010003140b030150205201d804542001d0242d50b0711301a0050040c070000d0b00340544400d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 717015224 1250 717013974 717013991
    0x20a090c020f0105090d030f18143c060c0f2203050609070b0f090d050109022e0c08090918060705090a050121020a051b0c030f0d0c02061c 61
    0x2645446c04600c2d0f10b8040b9040540c10000003070b8922508503c0303e00c5070505034030502c80c1e40342c80303501c0d003480c20003500d091003516440303003444500310020132b40e20f8a8442800a800d06181e40301a4090172300f01d8402c840d50144041c8001064003e0941e0020b000c443c9040e501c0750022180402980d02581420642e54007824010080c8007021503403500c940114000c480c0391540d01c01c0d008443d07114000c240c40111609204c42040c6250101310402843e01031400400c074260140c00181030b81201151408041d00007810340c00501721001d0314480031054a0803c0c401080060312003010a1042c06400c1e40700d0300a6500145240c08d0342c515003035104100c40e080703030880d160a4070060920342c80590b141c8d00c43c060400c00020319610600d28865824203805007001c95002c806c002602075001010f03254180f100070701c1507450360a0100c4080c2c1240142500a0880d541103205140c18640c0c015039240b05a044425222001a00070300400c48035a410794100d55250300c0301040300e40201c1000c1d4a04907090404012 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 717016474 1250 717015224 717015241
    0xc09030c040207120f0f080723160308070905060d0507050c0a0b04050c09010302180c0c12040e07090b190302070609110f0108091f090b071d0301050103020a090c020f0105 75
    0xc003d0080d080d80c45c2c1c0d2038203c0d1640400d0381c41810006a001c0000d01e40000100c03d68421800e001c11000500d02c403203803980c0b0381030f8490200d40010702c840003200505100e01041c95808206503410480c00d0600404003070902e40818518030810100b40c400d42e49810120b0281807182c001c82d001c9860100039901000e8951901c1c145100050b2015140d070300c02e0704440c035a9850103000a604072035000740983c0300701000c200500d8844000524403002c42e6000d00100c082c0103400c2c480c2c05003808620403203d50315400c182000f811548058110400c100d5081c80074801040b000040f070b028024001040d030311000c4066011400f074402c032040102001d0800c0c0010080014404008650004c11107076042c1d006030701001103581c61021600d182d480c0d1b100c001c03100c480d030303112524000740c1c2c004904000c10351201c1519103542840d815100200002c025100041c0008209003424001000880c021310403549103400045500303015001e2550120740d510303120700d0320074002c003e500c01484032003009101610348100e9 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 717017724 1250 717016474 717016493
    0x901060f0206220f14300424090b0a020a05121303172a010f0504030207050f0303040b07080a0807030207030e130f0509011a0109030b01140a0e010b210603060c09030c040207 76
    0x8900912120503078000e02a403c81069070705031030510310202e901000d840c8c42132031042450322000040c80aa000c0100b030200340e60303000f03004034034180c5c000b0031480e1240d00e0200e1804240c0e61003180c1d1000140007422401c42c5840040c41101d030010b18200d1010702000c8817154500c284003840c0c81034903403804134407480f849504042c90f610038014000c0005c2c40c1218807030700980d01c044a0040c01030304140c80c244040c2c6403004010240b00d40240880341030545a8515810552061400fa41c2d071100100b04100c00f0350307001100d1644064589010760030700003107940240c018491041d00d5071055070450640c49002006a0100301e03010140740c018040c40c2031404400c1d00901460b158480054071905c2c040d482540185c1060301104d5000c210000183c1c82c0800d012003060408003655400b02d00c01000240d4144191031702806002008115903440d110002d882c443c1e516a00b000b0318107011164200042d070380c1c001c90819070150a03213003043d0781d489c0c4c3c001c00a4105071020310380f1030303000d480400e160b400c2c040d8080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 717018974 1250 717017724 717017773
    0x70e0d050d0c15020307020109060501081b190e04141204081507030e010c0905010206070314040b061c030807120e062403030a090f080f070618050901060f0206220f14 73
    0x40c04010be030741ca918056460b10202c00c0c14000c1715002020320300341e0307003440c14182d03070400140c3e1410480940c4074448021881d5090310141c0c0c1684140e420102005020701041c04015200035031145058030300302d003203030f1151000c1d140342d4102c0700700c8000a21042d02035001a043e554042008010320300c1d000303802030300090355030094038014415003001980247c00703881105511a52100d5811441d42c7d143d8400c485124020800c607002130004603403489003640d91020b02c08246c481d0726a0b40003031810000062090414641c590599401e06041d654407a002168035900684910101d22100e2406844c0c2c102c6040c0e000b1300c0a406100c0029101e040e01c0c0c0c03080b01181558948480680c400381d5a81d241a07844230b443c0b0b0810b400e40c10150301003181d640100000c1582d168080c54078403000703030794900044400c6001d80c400c1c80401c0048401251151703052041c1d80e40709060301401c1d100d82c0c0d00081d42503216158a02c0c0103001080b0311103140305009007000e8401c40b107840b80003210b8482030701c858140042e50020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 717020224 1250 717018974 717018983
    0xd050a1401110c01051b0f0403080f120405100e150105010e120d02101a0102060c07031202040605030103020f120607320903101a010516020d0b070e0d050d0c15020307020109 76
    0xc1c60070180c80c6c0c1414100c514074508801c90b03509181c255101c0f10f0180d4090f00c074070703104034a080090440100c80348000034407a81c003541c0a40100c3c000f5443c2da2056035004da40c400e1103070700f0049000b0461101c058003c0d0640d0000e1030082c40905c10200851000324820417440d09c00d118010300d48003c95400160600b4580700d2600c2031003c481c10340c005204c84001c00c0700e0540581c100b500065040b61884001c0c04091b8064a8503a2031003803000b00000072a4815001035000506c000300500949c246080810360b058815a00c105042013800b0f0301701e4032020302034031480c01c0080703902c140e015290080d98280a0048004403c007980c603c000b032508401d9200700640740c020701882d01314048018492203004000d0780d40c1d6403245200d4650f4001101c0c5a4030840c10340801407403412000e005602c54000824023188104c2d800044c604010002074180516482401c1c0308400d86c00c580300c0000e001040010620426040c1a1440d0850349080c0d840f1803203629010401e18404001c200c80182d0541004060358082d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 717021474 1250 717020224 717020251
    0x40f0c0212070215030601180306020a09120b0a05060609031507080c180d03050d141504090218040609021c020907090e0403120e0102041706060d050a1401110c0105 72
    0x5010407079460700503884065440030969200c1c0b82e55200040c015548181c0500d00203602c3d402c242d515007000c8040d40c0040c0c0785039a000c1600503c3c20f800929800c0a82501a41d10303144404030340d200848800e004005070012500d031008520280c943d24150340d200c102c020151000d0810302c0204400c2814201c484078001102c410118801100f49022111000c0d10046844120030406003800088070741460203d080000800c1100c0366210144201440e201c444689a24242070184e04081980b807180201803140c0d04e410b50000c0183c3d5035842544194014001840782903599080220040c81d0480340690001e0903980d0415a2118011007034418520032544100c8030b8665003000c48441455000d81c680002e004070101f40881c2c000e0b03901d440000c0c08641d0115041704c1d15078016003681c11a030f0000d122a0205050050741e85001e021540c0c6c801c4080c0d92400c00402692607295861580350400340c41d0101050604143d40c000307412507000084808840d944c0d545481c01654002c040488010001d080e2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 717022724 1250 717021474 717021493
    0xa030c05160f0614190b0a0b0c03030a0f06180506040e120c0d0c0f1509051002131401090308031b070b0402010806030105040201121112130b0903091309020f040f0c02 73
    0x4124078110b01440c00caa0344440c08100170304281e00182040e082080d44643c035990001164002e42008228007002200990748a0820740651001c0e00e0b40d548911509604009060243c281c48242eaa205100240302c00300302501c4603c003041c02440b21041090795402140815422662810010014041032204480c00c080c040354088a024008110080c4945074001020300810b1000e46801c881c411452000160b03807241c0d41e00c0f1460503000b080c1302200e064000c40c05000b01c4621074002001800d05840440c2043c00100000f03003004214040280454800f00209403100d64000b01042c2c014130441c0061b40c1c5650070309081c151090304560890000380580b00081d928181801410302890341a1a0413076200c8460448101810201d600d0091819060180c1a91046d0680078180581c40101081e0592401070415144840b0000c01d00d4010394020007079458141c407001d000583c809846440041c1c81c4a0701e20014203e000c00f0a412a072050610304e506603000c0c040d40c48844c100078030340c01311a01d545 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 717023974 1250 717022724 717022751
    0xc14070804031a100902030601180806010513050c0d0c020304380a0e090711060117011b050d0f1e050105040e01140612010902090408030f0609010b0a030c05160f06 72
    0x80040780c201e40c203004c0300d10b0b0403c68014940c003d19040001410043c060080340040c884165902d42e001140c1c035030048004002d5401c00d10041140000072510500103850074008200013840750b403041c034540564640134007680314428800e86025040e00d0101c40e4100b0528000381c00510b000405030010031401d41c3c422440c0d001c88804961045441c1c0e20b070194103001d001e0402c0b050303100040c1a0b2082c00200340c1d0060110394240280c6010b0841c549600c50f681c0c002c1814942150f00711034044082c403075000001c2403c00d8104060720b581d001205000b061101ca01c60300240501511103002410850b800392007104000c103600706905071401680c00b0410045400c01c060f0990f00d00030b103040da035801000b01149050030b0800320301000003220000031403e010b2035400319101d20f01c11101555600f00100034005442c880700c40e1150800d4048070f85000c1d550400a10710b410340306031248602890360f1200b22030543d038019800d4500c428035402d0303403110520444c28001c5420ba100d5104a03100c614010300344e01c031039 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 717025224 1250 717023974 717024023
    0x308160306050d03140d090b0a0e03040303020714130f0c0e1507030c140d05250308010506030411090c1e0f250204050a0b120a02060a030c1407080403 66
    0x8030001003075600b407070a1646081da4460344643c95100414400c10011b500103020b0702503104914442c2c2300e4222540351001120741110030480101d240c54004100800100e940040c0340801d032a003a8120982c1c012004002804032644031081014040c101095403041e03101c1540441c09805464581000341e03d0174404000d001c042181d10000405828052500070078401e504d61241d01c2e00c50f00b140b410b50150341800601d4158401d640b41e000610004599601d40c118001c402d500d604400048145c43c540c1d6600500862414000c0b5070140c4800f00008007845440c69071b007207a41c4070280030f04d00d041c203182030546002e502c0326541c59441050150348039088000f0f5070031229801c040c0e20401341025600404a010310300c2c442c0664a4021008200f040566114451035004003004000010382d8412182400141000183d00320300940028503c040980c6440d421900110b010380703000215501c0315141901c00142c0d0901c4d6650341040400c51808100c404c0000384141d82c0581415042c0c5034102c120700418 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 717026474 1250 717025224 717025229
    0xb1b160e07141603090914060a090c02030f0702030307020a080f010606020304050a170307051522150b151303050601051207030609061d06060909030c0a12090e040308160306 76
    0x241401080704428518161083da070045100e4900600815a203004880c00d03601e0780051100303000c048906004003480c01e1030340d040c01010245d000384074100a84101035141c3c0121403c03040c195000040210031590b041c81203942d42e42d0b00071316801510751500780076540d52403030f0315008581798a030001c0030031580e00010a4404940b030007014240b00f941008160041c46039880001d0f040c40c030092011100107101408510015940c80d81c0587c503901d80340a406042490400303c00c0d201000310002c01c000b003507894800d5800c4030311995002c15051004000721340c08143c003410010100e0340201d8011070f5640407256010490740150300300d50060f62540c00700140806400c880d0070f000c0d4001c0f4410400030701e03580c0020b461540941c4c1c000400310070b80541d158140742e100e402c00c503040d08000d00300545440c00f112070541104007540210306180a480760150f03100c0c1400070203890122060280f0075540c0c070a04425014080c0024621302a040600d0068180ea400b514001400c00d1072010017003a180c03092203a5001c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 717027724 1250 717026474 717026507
    0x60608090726010603080f0a1701060507030c082703060a0b01091806090603151103011409040c03062906090d12120c050403020a1e0b1b160e07 63
    0xc038014403803958504104142e84088682d5250070380080840d1200d0b004e00101c800084d40c0c503541d04440300c2c00404003480c0d28034001c4285a0040148285035000054414440d810300709034451001c00d0506641c2e40c00740c018600c01c0130001003902c00c407514459079400041903087d0200c400e02c5e118605080140c1d8007862001e40000c0d101c003402c10020100040d100a0507003a284001070403500c0324281c90580b84540c1041d140d20001d00081c0c82c8101c0300b407082032800001c40301c4260542d410300d500c40d0000341520400c00e10038106040401c00740a01c50480704001c5500c6513003000b80516415a14070388800c119582c60007540b03104540c25540c200182140c040003c0101403803080442c0e960b40c921021240c1c440d84007088090114985224002e01c00c00040c0d903550340305c003034946195104010340b1201c50b420181171141c001440003171031500c8a6410059414002d078071500d607801c04c0d100440c14105840c0840f1a4800c030320461840401c0400241b040e02c05943c202c0c05180d40300c80041da500000100c460b42c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 717028974 1250 717027724 717027749
    0x10905031c0e0706050a0210051012050c0301050f040b0f0f060105180a0305030d1811090601180902040906081504030f02031c390e0a0302090a0606080907 68
    0x6401e034103107142810038141809001070b4500707180d034069203402c241c0d40116000c1100002c01302c020355010000b521005103450b00500183c5003402c9010040d80a603c280d031000c030180c200042c208807060142c00030b01c0001600800881c43c0041c8001d6980710151819195000038070042603210002c1800180b02c0d01c001d561100c100d455240046a40381d0105c000b80c0e201090340c401b02c062980c0c41b0b000d55001580188001d54644500506140803258400ca0320880c10a51400f940002140f040703598205801c00c540301039a0f6600c0d4401070f209030180180f1422010004540883e0300c01c0701c0da02800a841001c40d040101c0381d01c5030740341c0d9680c052404000c00c44840001c00100001d100b00140107001540740706403070403c0401d85404440d4010048400300c51511039031501e041412091004d0a070789007000103403414480d5030f00d4140b12210024040f81c10491907503500000313a110b4039528802140d002c2c0c484e880e00e02d800b02440f402000c0c54050180010100c20104a90160008215050352510500003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 717030224 1250 717028974 717028987
    0x6040c0e0925050d11010e011d040507050f2107050306011e12020a0201060806090309061c020918040b0f10061d030706020d080a06060801120c050307080a060e01090503 74
    0x80c014050510a03041c103036141500040f4140e21000ca00000d4a4441d0a0301c0d041480d0880000d0f02500036269414100111420501400d01403212807003800402694009800e45810303504071401d00c11080300c0f5402c160f0006d000c0c40e01c1c1031a0900004201b4240000a1603501c603001d08a484d848280c0306076002451740342d007030070740c0c0e8401103071030b1a050302035080c00d503a10140100040280c4c0c12441c0c101002d40d42d02e8104214012083c020300e0b6014898101440c0b030070b510314000501c14080c07907000d040d112100300d0004101c040c407a070444100503402408226042500745102d101041c044904842211209001c0303103011000c40b5009006031490030082107124140700301190382400101d44042d1160501031108bd4076282400a880034020550280120300c050304405005440040c01840c142e9103000004c205083d0b01403002410340f00c1003a0700346850141e03420449400003068101980c14052201d0000e1034400010b840c5000b9807180304240100d00b040d07400c0d24200c407a0104e000c1d00580040244 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 717031474 1250 717030224 717030253
    0x1060801051225080c0d12050c01060b0d09110102060108070506070606050d0c1d0903030708070c05120306120118111302070b0406110702010e090a02040b0c06040c0e09 74
    0x80b82c4101020008880c000307210942c22a600e03200400700114800500c08090000070784c10b00510010410641d2102c1c11040c8075590b03131500c1d00c0280c4890007000408202e18840040030f4000f10010000c060013141c6620705054214014207070020200d6a5010103007084100e540040794103412606100090604d0740e280074240052544035100864041d540c4071008151550b41300d51400b120b6029543d10052141040d03180b50f415000318005000031640c08041015030103002049a03840401ca10b4609010b8540c000700307907066280b03044000c1c000d0241103521580c0703240d5040918407070b10084807014164010f030345289080368400d036804602411038502180c04500a0300d050f002c0c100380941010001000383c804001241c00060bc00c4480d441398600340003d10600d0702074520f80e060f00f00b0900d880e1840603800138007112440301030b43d802181010005211080140d050310010100e84108547e0b401110300e02c2c80d10380804440849540800c0c1d40c3c04580c10551044035807040d18002c2c01800d210f444401c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 717032724 1250 717031474 717031489
    0xe0f0112020a020c280b0f041a0706050a0e0712030903260c07050f0603011206050411120105060310090b0a0b040902125b09080309060f0106080105 65
    0xda0010f511450350a03072940e407a03840f10803004c2d0708111030500d036171406240e65070300301046903120007016581880006003c4101c10b0882d001c58101ea54208103146141c040d00e000d034010400c003e082c4914080411002d500141c0003904d840c4842c4040d500840c0d1101004030a60400c403501400050307820b1001d00000310250b08a41c2c414850040c541e4440684c0140603006900040c2c40c03210a0304a07080c00c02081c10300301c04845519400303d50150035507041103c80404107855880190076a41c849002c90248001012a242e610001421030108210500c0310980603010075182d65010303101d111a500b061406611444c5a600e03031082c58210981c5401c084003000d0001e4117503103a40103580d45400401a40c031105405203040513000070700302c1c080300b00010b2010034810b80180c10b0402c0f0704241d0310251005408007000015a0001c85090719802c50314035110300300c40310241c203801030b140540c210244100c0002075031250f071240c801c4410965035640d84a188038001c2c031034800481c030040014085843d0145 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 717033974 1250 717032724 717032737
    0x60c0301080a020607140a12020115061b0c211e080a1103041d010e07020f0601120c0e0a050924010510111b100306150302031909050c010e0f011202 65
    0x46c03101d000401915002030800c0702c041c034112280f44514003105501c64082c0260038141c170f4080001c18a0b1841d01d88080c02c6403001c103e042080242c03500503003081100030a16000680349060046c508800d0403c00c5410301442d40c0d0b400d40e8040000c80b10700c0c0d641c041c605681d414240c1e002c0065411300d0b0300080156401d54070b0780301440c150f000070321020944110107140d040390800140e0310070f076095142c0780f1400e144010250011046400000390b807000241e0003e007044c11610031206052884203d418100c60030702d4640c010030440c0b01d00380103010210046803c0a402008000c081d20060511050b42d40740380d00c02a040c00c440100100010081c51070080300c20300040c4402d08000e03001c51205040d160811410012940754450445806090341c106441d03001404c0e401c1d800c1c01c004040c00c0514080d00c490910140404140d000000600f01c1c030200c01509a065040c1201404200940d25025484054400c14640010780041c0324144038504a0340f0811524010f13190b124200d00c2d50400c0101035401031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 717035224 1250 717033974 717033983
    0x806101e03051603030807020a0209150411041d07110601090c03090506040308070e100e0904060b06030f0609060f0112050606160503040906060201020c0318010926060c0301080a020607 81
    0xa03002001c02c0003030081030141544024202d00301e03030440c5009410050080e14070b40c01c5600002300c500058965101c00303500407a40c500ca042c0c12440c0c2000160107401c1d01c4407820900c100201c0e0000b01444c0a0354442c0c000d0015600120305607423950340c01c0f03422660100100095610a000400035509103070b110311401011880d001c46e406d40300780c6803180382c414142c07230880028028004002c449a407003d07180c20000b900b16a40d0307104102210000344011b1030403001c6886083d00c100881d04100e0306500a01c00f03407502808050312850240c0c0d4941d2540380c1128000d01800030b90300001c807546042107000c209098141c4900c0071200901a1241c01408010700641c0c004004014610321103d80410550620f441200155030300c90408203c0700c15205540c1c841410f6a00600c0081e4040f5004810f49003401c3d00304044080030714009004030742c83c13502d41d4802110f0a907603404003505070359014404001c8090010031282c1d292510300642070036100901c50040c081d00800c0c00c001c010700d0000018502d1340e026 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 717036474 1250 717035224 717035279
    0x1207030c05160312030e03030c04030b1f03030f0318150207060603080d020405040b03010506031e12040f0503010c0207060e010518100807020610030f020d0318060306050a080610 78
    0x400030402c01c1c040c0140c00581d800c8080f00003280c1c9942d03050040080c50240d5501031800d42c101811a142a800340d804000e00a0301307400d0010300e0070792042079190000740c1c00301d81036207001f0342c1c07810050f01d000708080b81d490010341084020800c05081d0082d400d50168402d04c00c50f108592034070004025000240c3c02c0791050344548000010403001d40150514030302c0f0361070042c0c0e518903103020002182c144950042c00707030b4100303810131480340e4020485048015000740d014602c000300c18880e6003000c40030482e400040030003142c0460b9010802407074a041d14800d40082240340b68011040c0d0351000d66215110005010b108007e501d544104003624243d54051420600100d1030400110852036161007100010f003031100b0060b01c25030402c501a004190104010031450840c1c0714400c6070209000040d0042c0c05600c0d04000f010700c03d035660281641e030180c64061840e1500b9004010302028800c5600ca59403100740030440c2c00c0d000c56503038021075880d44012081450700781c2c1194000408040018814078 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 717037724 1250 717036474 717036493
    0x901180305070b0912101a09091903050f130609050301050f07050a05250b0f0403050a180e040c09061406041e210605010e070c030305040203010605301207030c05 71
    0x1401c0211141b510000100403c1d01e040c040140500350040402140c071171103480003403289000006c6003c2d03142081e0554000041100c0d81825185031185140c01e4050b0140081c0c2c180302901c04078a007a0a580301c1d590303400d007266910030806007078400980341c43d0000a6041c020940041c020380c010924402d55061840c10122083c110242c1c2030b550800c0d160340d05149402c202e0410a4038200c1942c07001c0c4d46100f008540c100360f1002003082c05581d80d00801d0103905c0d0600160806200000c4c0000c0105c3c408441c0c02d0b1410b407030240c60b00031881c807c25024508000002c034458402203a03ca40248026064504161400c00b103040b0300c1620b8002c00300c0c02240703602c3c00b06100014029501420f0301e000f042c2a5201050701e008411142e050340040d8203880310400741308880d40e02921050b80281c00d80f0300170030252030341d0002134014022540a141d01c28902c41c800c0400501003004020841c030882001c0c06032001d040403064413884a0f94018010311410040c14000074083c52400f40c4030360046086815109 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 717038974 1250 717037724 717037759
    0x5010b270601020f010923030421030c2010090602190f06050c030103031e0c03054009060b090909030c07031103060a15050607060b040c050901180305070b09 69
    0x12441c2105883c2d1b10310f030241a40c20300c942000700c0a90b018041c03008528061030403420410f00b07084002d01c18565a80c42452b032041c148221552280d40360080340b40007100c402c2c40071520114410307481641c016441041c02604590049440c81d007100c0f6160054001903992080701010703030361800000c5504030685903e11010414a108462003114071042846c0d40e0b506604000e00005076051110a03800c00e607200f1900701e00d0380540488000c9a0505106450704041c081ca05c1c0031800e01407031401c81c101c0c603408281050300d4258001c04281e10f200c4101d407445443c2c09030001603030524081c0c0d000320a010030200b441401c0c52103003150b110031101c064a04084024040c642429140e03817056a501c540850505000d180c1032103195002a03002c40b04200c50390b01d902d011150740c07455224082c41032101007600c10a000c0c842d04801d030ba000004204100d070000c0380b00094620740002901900041c0200c00c250114480303140c0440c00d8a8000005061991614034130595076880a00104d8100300460310030704001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 717040224 1250 717038974 717038981
    0x6121e0e01180308060909060103080f07060e1c03113412020d080a0b0d020616081204060509060408120444090f040c020c060408060405010b270601020f01 68
    0x1d8071a9489807150705005d000c110a9500c0035001d0740305500021300410000d8100d10444094190100615480c0c4072141800390040040c101c1091507030088081d00ca240e0400010800214201901e01308800d558144101c401c50040072600442c2044415540d600b01d0181a000718880174032020003190308081740e88603285031020f10340751800360b070001030b415040c0342c2c01c0a003043d4010081d120400442048000140e802e00c0700c2e860290044500041c0000540c0709402040b0055811141180ea5400e0900c10b01000c02170495007620106c0ca80004100160b4001c90881d0081d60402c0b0b84a091108182c502058020054030480c0c040e200385022100140701070789070031445002c1c04030010035192016034290400070303072031010550b9840400c500243d1b0381d982d04968a1800b0190340c0007512442d02c044c1079241004071400590f02030340105001841c07800c001031703680c8224030400091200071081c400703200c2400400701d04030740d14140400e45c0d0900f070b100d079052103644548144120791040c5c20010105003103 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 717041474 1250 717040224 717040271
    0x315060c1203061c1a0a1104080c13020a1d06040f0b0306040608010b2d120321190507030605040510030c0b07240906110406121e0e01 59
    0x740300e002c0100035461900040245800c08400c40e0082090103982d24208074680c200f2450b01e0490b5001c001c01d52000581e4030442180d501134032601d03a075a0f100d01d6079550b21030381c4030f030f03110301c02c0c01c5841c1180424861b5009403a15036440c0c4d11070050366200b82903030b844c48803148072505400c0b140500c000146101844144c000408111540b640d4a00700001800700b5a02541c00140d0305a0500320500110389074100728000804c0000b01e008804010310088402c1c1b00d10001d0301e80d5110312112409401c914002c801040b2075a01c0300082940250911103490451204507042d000f401e81021440300035003d1600416442000e519000440648070320008044640a607420110604041d000b8010440f40b0410800644085a052400d008203540c40b4158081e40245520007180359542401e0b42d4440d81d00184440d651201c000d224011001000740c041d5005413180788002541307483c1903032104c02140b06078859000a20380c60108180e507450700101a21681035441071540d1394500800f0982e0844041ca4403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 717042724 1250 717041474 717041503
    0x121b0602030a0b19050f0f03011d0d12060602060610050c06040b06031e0322030c03080315041b270f05031c020d0c110603180106090608030315060c 65
    0xa02d00c03c41030520904441180d4402c948000a810601856607051045a43e00750b0494828090f20b08140100b809420500c0e41c40920203141c640a201c0424003154681070051150b031020380350103420404006948080c0300324405600100042900c41c108001865190020360030907a1030003030002c40c01e61038104221000c1e40c13954600c40c14065a8a400c0c440e1609080010060300c103004e248a00711902c1c0d208182003900c1c9407a000664809062504184000454010b14401412541c0742840e18090380110ba4032001c41444c1e14041c40e05181c04c1c030038540ba000180121605c0310704511401c3d83c03000300201c007044110030903c503000d0003074158940032805480502005031003140b4080a051810321112120303002d80c185540c1c07401080740d00095021300a01c00d0324000d40780d48058101641402000c40449030804c20010800c0010000109280c016501c4000200300c2103644080400c100d410500401c0c4442e0010000f241d9207018440c010503561000a000a26080300000c079549851003401c3d0016 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 717043974 1250 717042724 717042731
    0xa030903030b04090218090a0212010506040b010306080604020d05210403050f121608160b090606100f080901020d0204030b070305070903020f060d0f021303051207121b0602030a 78
    0x80405626010301d90031036000303440c20b20031107102e80c0c0001c0454190b035030188a61200d6034006514000204443e682c0590007504610031070850103c031034081c1c01c08030b070201c9c0a10b04180040d409540700e403180300c0440e004071025110a0f1a03683c01c00641d891508030030ba903d80b050300000c201002c04110388850307072008601c9051303646180d898840d08012100c0628589038019a550010801280c2c1c216001440c40a5100320a002d241c80e04013418000da225101d003400b02020018200600031174021301490107001110f400355104010403c0401c20106000300140502e8a02c0c071100340160942034200d0108000503051641901c00c442c105d030010750059a030030074484e05102c0da098140c411940c100a2030300d0700c8085141950007207111076401d1804607014200002d0320500e686400e50000b20b8061440e0400d40d51200c0000c544800780b0000d0006845038021f140b400014030308000101d500450b413140301e030304151010710f2055503404004034162803030981d442141d0f00000c2c83c602c0103520400070640e001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 717045224 1250 717043974 717043991
    0xb061c08091f09030b1f180905070e091c050901050c0106081203180607090308180a0801050601020f0f0c1c051f0b33090d0803011703030f04080703050f0a03 69
    0x20401040250006c8401d82c9241c440e03d480301c02c042d0414054840d0716203842584220b110488000b45650704024000c1e002c0c055010803c001344868241c0515041c10440d0381044249400c12005042c140305100414030801c00c0081e194001d001505407041c030301d400041c0c1c40350307540e0b41c260616a00711076040c0b00c81000810846030128071560560300c480c000d0020816480d020a0240c22900f860001500b12000800d510404450220700c3c00003901e0041c00501100ba46e03640a58040c10041e68114054014403260301c82c544800a14480103458800007401c4450795041803108061005220224072101000920045041000300b44c050b0750200c51a40041c8aa0882c024205d98299060382d200b4008049034450110341ca6408200d140368103d039150351082c901010006511a40740700315040200089910f0501ca10040514100d070841e40246103814403081d035141d101e12040b6030316821324401d140881d0205d5102d10107410101d20906004c0d1801203810421150360b00505c50110000c3d40302d481c017 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 717046474 1250 717045224 717045233
    0x90f121011070c15120f0e030a020703060e03090607020d1e030906030b120604060c18030803010815040803040308090a0b011e09110409020c190506040b061c08091f0903 74
    0xc1c801009441d0f50300d003031a009210010202e800e16035417882d00301e444a0719840a03040c00e0b40050300e180c01c820300320b903030300e43c0700c560069200c2030b41c2c1c4410713038280b46480f82100d8040c0c004000c60741e50300b2000f000c03e03181844550030054081d0b01013009540e80b070b0040c2c403c1e869003101942ca900e6910300a84443c24a00d24152006043e16a959031150040210844511412800280c096040780d40300e44003203080310f80c840d8110b03940f401c5c07104100361076005118004140040040194140d5000f03e042c0d500350304011129482840040d030b0300174031080003040001d0200f071188e441190801030310410759000c480181c9501d96000c1003a0410400104a1112010300c0e01d0500b030306000602c582c0d007092000b15a0681c000410340618401c2411443d00001c400303c4510f0700748051700c4001041130036884035007034604080f2358841080b2012200c100b510030126407180382c82c4201c05040000550900d00d0561035540c0e2540c1e03500100d200c65000111b6002003070340354811002c07a488020040c0d41c0e20b4401c5245051 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 717047724 1250 717046474 717046493
    0x203010e150114190c08041d090105070e0108040510090b09010b0301050c1b030d0c032f030103060b180f07032301030f0302030c010203190c05090f12101107 69
    0x400d1418084114115803003c42850240c602107000308115400410440c00c00f43c03603100811900801c0719100280c00700e4003507072040e06010310012142c0b0000042c0d41e4807030f61900301e401c03c2d00d5480c081590b14109180641c8184803540d40700344a8005e84001c990540c01400503501030100c00c984081100081000c2860244030340c69040904400030300c102d0821143c0010284142a403146501800c0d00d02e04820200800c00c85495244103081040342d8500224000c000341340c50000c080c4440c83c40b14030303500e41c0302d251564507213030005200c0f0aa01e1a46142c1d9041c0040180008042c1c000701140f00c3e688078042d50940721071141018025820386490300510080407140618602840b40c0b9810040c580e140512040c2175054070341c009150400c408071030074268514001d01ca0050f280d0342c0004200000b0342c98815030400003400d107070402c2c082c0d13000400b0240c4140c011103604540001000150490502d081c0e45151155a9031000303442001078040c400100759020090b80000b83d040010300b61040020148 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 717048974 1250 717047724 717047761
    0x7080319030c080a020a2a02040c0f0801060810051e100c0c0b1e0316140403050340170c033307020a050f03030610120605040203010e 59
    0x1e010031005001400c003400c09140903110744069a40841c1401200f0301507040c86d1748151001c2e0b001d40d8440c2045029540c80080c00800b28040c03400c0c070f130003030203410300070401100055260380b20b1866580c00e0042c100c4049a009050900400000000003201c1c0c95140d40070031103079454844002c6240340d86060005240051600e54100800e011003400800c0c2c2c4100504143c0303c0124509076100b42809032030700203c410b10507a60b2175450010900c40d00c69510540550440c0a80d01e88200050744506510480d0040d44006002900f0400c480c95010300180c0d5244160803550050b0049240036000b0700c2c2d1488a5001c402400c50191030303051104a00000210003001c900030014a08944210042034803940c0c2209004142e04031042e0422022a4030000e0b00d01440b82403542900714074040320000e60320084140700341c0c0c09001c1c4003460504640048200c074071400000d4900614044800402c445202d91031b425084440c0d543c880201d100c3d9910700055000b081c503420010814182440c40303641009148 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 717050224 1250 717048974 717048977
    0x10501081306020304080d0e031215090a0b1201060b0d05010506040308072402070c06031d0705121005090601060f05180f13050115030e120d020f0c07080319 69
    0x90070401221540c03880003180340d510800268482c2c80f14070f002440760091220000c00a410101c0c141c020800c0000030f010010716407003002c0000d848500200c01300084040c40c0b10303000109003000868415603600120041c840240a1141d002200380e43d01c1d0841d411500520425640080c035030b0804002d9000d500d02420003140c8040c03038503255980d00141c5114200004140518020440917440300002440390400c01c0f04005560795441850400325100f201d014140100e4607101b00380c2213002407070101903a0810150000e041503400c08042100541e00340d6201e0b0320700c1c800c06210341583c100c1c60203942d000f0340b031910040056506000c00a826060030194003820807000340a500c80a0302d121a114034040002e80d43c400340c101080c40441c0e02c4c101310151a010a5003054000101c0003006c0c458036641f1101543c04010b91107000c0465901d60038452100350b0103510a01000440f03035160380c020310107031b0030403140c6500e8a04590700140c00c02c481c80e44945000d030030100fa035104040c3d40000c40b00110456 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 717051474 1250 717050224 717050237
    0x905060a06171b0a0314070302090a020702031b0f04060e0103030e09041a040609050f06040b33030102190c12140d0b0111100608070501031b030c090f120308010501 72
    0x4508455a9070340c060420f5100c0b282c010800007249407034900c84403000d142c200d40200010700c05803800907501c020610080b40603c0c00000006c90b9180c145c030980341c1c1d50358000c0243c05800c44450303d481c02000142c00c510352200b42e16200c02140d9135140b04d4a0020030300000507609540c59418041c00201c1141d07035642c0111022400c1000184030b052100b4070301c0008042d0180ca030345590074074400814684400070060310500300040005240007e0091041d4454000380240d40c0e902202c48401e1404444c048002c4e00740f01c8402c207004014051140c204501c080c0c0018100003030542d041002d203c500302c0460210300800b01d07030030131320003010013840c43c2d281a42040030b443c605854113011144aa031404940442ea41d1003a040168411000d005e11071702148211446114099a8000104128821001d130341c81820000a43c41d4041d00a148000407090140944100c544100341c3c0a405585c240b18100300e075803100860400c01c0700c403084003c0c21502043e1600800b00d89030103421240180c12090503c2507 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 717052724 1250 717051474 717051509
    0x1e15230a18121b05010203090f0c0d0605130b07110c06091f0311030c0409240e040c080706110c090f0a0f0b120313060f05030a0e100905060a06 63
    0x141c1400203451182c0c000030b403244809441a003100c1488082400181000503081503009006054000d03500035619001940c81d011a0380ba1055511045208415001080000a0303004030b00b0941c8411750044810010341d000307001c2540d030426942d81c11150080030400c940320680c00a1000c0041240c2508103a80c003038540414400007462241040b9507040103c9072180c3c19041d0b540c0303c1e8220400c0c100c1c60460781e03502e9040000c4c213015250494004d0180c11498111510074000d2560580301c000c040588842c0041c6081c070389180c01c0590300400036100c0401041c0c0015440d030b820001500201400d5aa103410f41c803084500e142404080b614084c072032808201841010031030303032038041c2d000700c048040050042400c00c5140043d01200604035801922240146004e1038048020f01204410705c0d10700c148035480b034400381c850503040f48104000800038000500c1a880d198042159900884c040314403900410b0342c1c0c01c0680344041402c44064200d441880f5108104d40101005001c25250011018a = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 717053974 1250 717052724 717052751
    0x40801051608190203071704120e091909030212030703020a11060702120d0f060b03010815070509040b0a0506070f02030d02011406040c11100218010c1e15230a 70
    0x20f100007401e040c40c0d5400400725410301d01580f44100051990106c1244500e8035040413003c020a103200c5a01242100d40c0e0000d9521300a0301c1644145001c43e50346001c9003d82c24690f000b4800441c0c00c0b41944511040c034010740d000d130300c040c610803040740c2d40c050b07903c0410802c005c0190304801c5020645504c104188201130750003058492204451183e00e2381c032120500607007400f829000c00014500d52500001141401880000710306a520103000c488061811883c00102000c085864000240080c040404c15280907003141640940040503c07070b0b42511000042c506500072402150502c0e03001e0030207021800d09001c090184000c034002089030789000101c021501c6070040195110302da0b150040d400032801403c4a81e40328141d20102c520780340c4507030b0500b40254419540c910020300c01021080c1c49600c00e1207411f07021135000850010301140b240010320252441d60044510b0b907114846810701081602c15146c1104400d035060303a600c0c100e20b500e400b0440c00030b0300d8100020b00b0001a44140c0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 717055224 1250 717053974 717054001
    0x14030c0a0b0a080703062112110604110a091b03150807170a050322080c0a090c0905130b01030b0609090415020c190308070216090e030f040801051608 66
    0x30b841c2080e0003180c2d5602c40132001002990810804888070482d105d8030fa8105800681840d441248002c43c15080c0d03842c01d03600c8151034040030304190f01c24030004000544100f00403890346c1026065080c0c00340c4465074242580e001d035000c1c0505442c2074800703285e002d86c540200c50111158a851404140c2001c1c1d031580ca4107402d0003005882e100300c51455502d040c042018040307480d00102540c1d128250280784c1903a04c404100090014410140c010031004008541110f03801c2e40141500e0300c0f02d20f1308143d8800390240f00e5004c01032180d102c0c80055280c450100d0360716405a10b50000070041032070340002d401c6400c174142a5002d100d090101550a03102c0f6404550010f80000f04090b406607002665000f901c0384011300c1407a801038140300301d500b880305801c10029034881d032116080c1e9038a0042c102c1e0b0700c07070300085803c0c10318a018504015114540d40448032021200e01943c1ca010b403103d8540d0051340c410792000c00f9607950b83d800c0104032034950302503420140c1e0501e013280c0182400e60402200 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 717056474 1250 717055224 717055237
    0xf060403030e210f160210020c15040b250501240e011523130906090e0604080a02010b03060c04060f0903030507021c020d1b120b010e0c090a14030c0a0b 67
    0x28050020300491510342544000150a030700603e4003401c148000c000075100c0c401c2d00d84c2d1500486075001c1d0610034060040035036040d220b29000041c00c14037030442c082c1c00482e0f55141745540b0706038986600041002800f494421004154110641d00d11400e06401e01444580c494a03248080c40018419148075003400249046245416070010703015951421a0240440c80340e0702454001600300d03100e00c04208403d0490344032890400456587c0c1c80c4c3c59060700c00646941d00540c0222001800060360203000e0201f50605100010340050141c1c0420715290b01030711028417940c400f1900f005815403149000c407032165140b804d200c2c424036540c0d004d0304074091140004d21802d03150020080c08040c4814100080707400900800540c11581000c5680004060002d040012000004540d14192140c50001c0c10380c0080c1d07401231a807030441c0344003d0780c0015092020f203050800404a0590302c10341e0540140c00b1241c05d40c0114902e0108040c40c00748040107440c000d607500c420820003044411f095940 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 717057724 1250 717056474 717056497
    0x8033303070b0a05040e2d0708040201120e03070b0a0501090c020d08070e0d030f030e0313090203040204020f070c0806130803010b0901030e0f0307020406090203010e180f060403030e21 81
    0x454007446801500c545c010381c0c1010356150650704c200100322940c80c00c44000c80b482d401c4122620a44001ca0000503101203c1300c101013048003004c41c0065100318a4546a0b4409050002d24625500c43e11811a804480c05039a0700c0c5040040c002d08050358418540100458801041050380d440c40c082d440d8846032850100307121002380081d14090241e00d04e280000c200a10441c4081464a40074003010034074041c00d0000b0780f4010142c107111320004226003070f184c00140e0100c42c40d460003034480081e41c00104100c0e0426028001c1e034807072180c50300181c1a41c2c2d103c3c140d6811060709180c11a4501310004101101c0b424030341502801050b221401c0701e06503101d62280c00d42d265080001a070141000041c08481ca01c2220582c619022000c4080e0030106d1003110b05104190313480112605901081c06528104110980800e480c2d001d9900e2203429810060180e50014680c0d008650501404a074164042034484c0f61100d13080078244101c0c01c07025409090100310058840e8100241d00401d0501803 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 717058974 1250 717057724 717057727
    0x1206150e010b070804030215270121060e010605220e0f070e0310150512030904020903070b04150806010c11040c120e030c0c0319080d0908033303070b 66
    0xc0c20302070131408072000b950700681071084103860300501c0612070348490760000c0030700644144240e84039000400c200b0382849c16915110b00b4420245900c898070140302c2c4661800c0d940d1080025080e10042d1801c1c0284032545890340c4035220940c00d02e000c0a0300610103103c81c101a1000c0c808242020780782c0c0c3c0c0000c4080031b158500e130f40e02d0784103507508180c1411841d49031264402e6040102490381204190720144600c2001e0180c3d0b40701803043c0320310105072415803038000b48000c1d00e15017019806070a0700d0b64020708076088541e44150380740032540715800402d43e504969080d40c920580008509401000030f2810502070351294075504001006614910300c56915001100034880c4100000341c40408480800c201101c3c44d580210350f260311000d03d04001e070040809102c3c1600c0c0c04160341038a0211940d12240311002c555411106900444900c1c183d00d5540c4500000309451001551003800c000742d014500f4408288980800308100d6460030210585c00c49540326914040b83c14003c403081d0b401480d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 717060224 1250 717058974 717058987
    0x10e0103030804021c110f01141b070e0a0903030606170a050702031908041101081902030c250c1e06120f02070b19020307200a0c1206150e010b 63
    0x3130b40c0c0d005d0304501604501103201804043c0081c6003220b103480d60f4111980c41100039981c005450485007584c249041000c1484000c40000f00944081ca01c03240360000e0341c085a484010035003c1c01c800780d0340304080a0340e40c14503402301034051040c40c1c040d10060074411200e0350440039100100c04010003007a05a502c90000c00e10a81c000c10540300008407441104a180403200030040001408071016117028014003140762055000340c0240f4000c2c1a1442032040c2c0e8a40d0340c4405004c0d42c40600a2203585004106810040b80050b01c0c01d4200714081c5951360440c4480d003400c03801406107410485040c00c200342c20800d0507101c01050070456049091001481d052040c030b80e0001d2072091040c507505400010b20004000385c15602c0e0784580d1602c2f505600000141c50307200101c0c0411503151b004584108500100c8036402010b0a0200070500100c404c40a50342d500d90703840e001240e0000110380c002000d00070802c00640149104000e55441c00040d40380303010300b100b0440806118144114a000070340 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 717061474 1250 717060224 717060229
    0x60a120201031401141503061516080715050f09100e161202030d020127050313030602030604061202130203061c032307170d0f1d0c010206010e010303080402 69
    0xd210b192940c40c1c0710319020b41c5d50380c0002a02001400d030061268004440d6098500018401c2c0ca01408000d0443d60b56001c01002c0c2811320362014500144482c2601c603c0d600181d055002821010311409040c0d0700407402c030b1001e030300359030300580b04000d240c040d102000b0f407a110000f01c080361101c3d4030300701050f140c007104200343c00e080524090041e42840c0d080082080501401c401010324420303021110340300b41c47c8104a00300d0710985440010f80c0100440c0450884451107400400c1d40a03000745c4c0d2800e07000d070301d402c0568036040d40105c03403198001c010846585407070320600008022000c2c0c01d81850043c0c2d23000612400d00c10410b0316926074044017051058465402420b81684081e03681c1e0408a401d08024004500e200740c00f070000c084000b0b24125a074286010340760038607808a41038514034081c03a03001340180c00c1203804070261030791400c40c0c00740c2212034050030071003000f01d1501c00089030540c42c04134104814502d0081c1503600070001082500c00d20348003241100c2c1c2610f40001c086d1034a100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 717062724 1250 717061474 717061481
    0x210708061e0a0308092d040507200c030c121213030507030c05031e0a1101030e010212150306010e010909050304031a0a0605100512090a060c0908010f05060a12020103 73
    0x11190300324030b0951002c400c200468008040044084031034104a00340c42e01e501229801107062149540c21001403450305003481e402031078005265041002980c42800300f1555000c1c0f007d2841100c90f84141c407c0b070850304092003400008a01610410f0140a1a01145944140544071180900d81c000382c0b03140504030003a00800550343c801c084d034800695a00300b090702d08040740680c51180c040c264216070200711001440122585120151110007515100c01000d030b03c85001c028141a2180e0091031244002e00c001c00f07154255101d401e0142c00c1c80d0903403e03500e0307040f110100d001c0d030701c881e0060058082d40341c10103045404c8402e01145c0b00d0800d240c55811030040c1e03800108801d00302d0b003070b00d09250041d030502817160503c0003003007090540d0752f4100803034444100740384404241c0401007940c1c0700c0300c0025996400503250044840103003241c0e580300c00721032540711003400003540b0410520004500303001e0b1100b00b84400e00280300c28202840020b801150741c0c1b2408165005445420046901a81 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 717063974 1250 717062724 717062779
    0x110f0d094d0d080d380f0a090207050105360c040903050406080a1a01050d06031703090d020705030c01110a05070602300304020904020a0906080321070806 68
    0x2444040b241c5038520340708009400c8900b5490390141483c250040200e81c1085003000d940c429540640c60150101010880424039424280c1014003e16940020340380c0450038801400c0900b00185e403988a8140079003102c801501658903540100b0300521210403125640007032840c4010706840c0f02c3d92405106140038580354859030843d0501c8940c9040c5038000c03000d80100c500c107403681101c035030725006050102d580c2c180c179480a4421088480c040da51007000544425a005840098456281c2d200d8102011460640b001209c000204028482806000d02c12a8201500003070510a04100009482d00c216903220390400107840707140e003a030110801c8540e0318a9004000c1e074a8031600c0307510081d00c6010194450b40c14550880b00c1c0301108541c034080044c41102e04981e14119103c1d68200060214040c0081c0c0c0e002490410100e00021b080c4121001004c48600540d507501d0504114158015920540300c1c11109140030440310341e1b0070503141d550214048408000d8107106141c2681c01c5080c50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 717065224 1250 717063974 717063979
    0x110f0d0b040f0b1f0603020f0408030408070503120f0a0e041409060403090506120a020c0111160c0e010303020a06110c010e03070c0b09030d03110f0d094d 68
    0x400c01c0c4030a021072154240c0001e03000e0307070310030b00c80384e40305841e20000f0402042d078012030004d5400104000e91003540900f000981c1d5100251070142d0710001c651860300140c0002c012500100d104204a16040102586d02d03c2560211410040d00b84440003003405076421800174400c420002c1c0b802c03650799500c0381b000c10052114185180c1021a0256540d100855080b404102c15010128103840d1000035600400030341000c14186e81d4400b01650040c1d040417912403019900e0702100551140000c014020201c00e130044071002c16000c0c02d1444051445a01440001d091400107102182d40031900d608041d401003808030b40125010a0402503114000d0103210275480d0440b48112008084020040e103070142c40421046038851001046900c6040032040c0d0503404041007529a9010760049082c40b101a1410790070003401421510103640840000140d00d9910719090701001101104007141c01c1501c0280540000141d0407480c919184054841e00000307103140a40282080044005451002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 717066474 1250 717065224 717065243
    0xc080c0708130e0901020904110306031b12010204270c0e0f1504080705041d06161112041503060b0a03090f02150306010809010504110103020a020309030708030d1404110f0d 76
    0x1ca0704e064001d401088200d03100f18102005400ca00c3d840c90f003030301c0c01400c0080182c071240c903100055408880d0902c0202c1d4218908288680000100784068801490042030040c0341c03900382130b040440f0203410005844501e190000150030203922001140c441d92050b1000600e440c1800c0000710072108402114022840014000c2001c0720003080d01402c40b602a038040c00200d1043d000300c1c02c104881410854103500a40001f440380ea40000384810038240c82c10900071024840d141241007010880c0e1070480c8040006040210132928800d00704286100c0c45e0030000c0500708510f420303c2d03200b100500420182c0f125107010070b00078101c941c81c5145138010038a1a91000001062850b504101da1460103c0c580500040011320180501d40c442c5510580f100b0100c11000011340c000d400443e841d02c00c6100607c09072619440402401780904520f40c02162a450303906115400d84e418440c94440c2c50f8884d006010000b0008041041d8181040311690100a81c041c0803405050308076a003e07184495 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 717067724 1250 717066474 717066481
    0x507060e0d090909021005070318060f0e04020c0c1e04092006040b09013b030f0f1c05120406270503030601180f030c08010c080c0708130e 61
    0x400109000d140c40141c690782c1d00180d860024900300e4940440280d002101001c445c40c40c03c1c0300d9001844110b00c00c0c10024505d280041e603a01c07516485070000340200321896400540c0301d4000208904a4004580c190300c1c152040700d44c2c648030244044a1409808000c4940342c0c2d2100c289841e01c00320384054002c010480450034030510302141a4a144c00e0b995911240c5c3c6107506110b4100e500f0f642440c24542d00c2c040b4560011a115000078000501071282ca00203030b03030b21030400c000503804c84140e64010845688440201414580fa001207903805510404804a942c180402c174862942015400085e114018407803d56240c0f11b180718bc40300f9000c60b08200410446181d014400f020005e40320380001000300a014000800642c5001d00103910500000b9995032041c081d8900a1a0340c0400a0340560b0781c21000c101c0300e060ba00704540703210300b25005004074142440b40e45018041490a05c80b142064070341e0394401c4c072507181e0183c510040001d122440500d05844c050040109070082d140614 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 717068974 1250 717067724 717067751
    0xc030f061005100504150c0f03050c01150f050609060d05160e041112060f10020a0303181a0a0b061809070c171b06070807020706050705100c050706 65
    0x20200c0c1c0c280d1201c85129400b140c54181030b0401c0c0e41e00400380c1c5401e40742c2070400241104685403014858104139900e547d8600280c4684172248509100f900d0f0140c0b5003500ca900c072800e40300c2c0d00c03c1b03000707200c440018100004050b0030302002c11560156181981d4040e501c3c0070031400d2140c01c100b28582400d00082c0004d1481c03000030841104103558a0076816001c900400046c1d440031504e182c0072280c22701c02e00b69480544164660000e40c02041800900851404110701c41c01c0302d8800341c0541c10609a510615426002d15075410b1200d14420184070410364502c41c5009171111304502c1d003505040050000705031680000c2e45507100a1055440d6420b20658480040076003a41c0d03401000440d0100d0603490147c0c0b80651001c2e48900c1d010012851000d4482c0960030030003c0401004250b51b2070340311703008140038081c0030b0629070fa02c0f801c0ea0300d09508041d18060b003540c400000c003d400c00842000c10030102d0b00c0c29000324019401f01c4e184101840884aa001e40b05c0054612071500c00c1014286 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 717070224 1250 717068974 717068983
    0x30c07030c08060a090b0a0c020102093001050f0721090b06150903070b09131107210503070c0309080d0810080a050a2d050102040e0c19110c030f 64
    0x35180d03041121401d030781390070036030055446609005001c0402040428000f010580084c10200b004d80700040c00c1400030b100041d482505101812a440b100401140002401c4240c182c1c0c0485010001d001c1d40c10088550354403400b00030b0100c1c04002548040c10700059410300060000014141c09005600e2981024410008103840b002d02c5408154402502c1e50a503a080c4d500f4544004c1c0a020920700c0c18440e01e1050344014250381d403107036020203c290800500d1142e0804d04509901841c0c9461444c42c014140d11f050f001e04600015820803909081a4800308895005d4180d1403c1240420280b6054480ca2256001144140903907100c0114407030340903d10034820130039100c0030740400307942e038000b6910307041628006095a005038500c0310200c0d00c02090400702c0503010702c1840070220502d0410710050a82d4404507601d9400081c20000c2c400107022054102c20010905454041c050b0140400710007000b00d2401401940214400713002000d03c25800700800240a80e01c03901c0040184d03d481c1e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 717071474 1250 717070224 717070229
    0x16030e0a030804091d1906020f0c0a021305131b03021e100305150d0809040e341403010b120a03031506020a1407091a090a09020603150102030c07030c 66
    0x1051030000c140340350f8030780c0f0b00d0b00d40c084110405c007805286c00d40d10010608070601c000d041d01c0d202e8003000004c610b41103040c000c0c84030103031a001800070f2030443c1c41000824000340d079176500d51905100a1021403034800721824103136907100c2d11200c110014401010700b03d1110b944003a500412500981c0405030440c40440d0b800001190040c4103030642100903403c540056400303c140c00c0c03101c1200140d504041010305000742c00303210f055040c03240403030000b030039030740d2503d070483c219040046510507103001b000540c080c885035840b010301f2414030300350111000846440b4102c0381c2c1e0740c3d11562000c1610300794400701440c1d00151170a070b6107250b0002c40c030b503840d6207561003200002e1400710454000502d007000390781524416400b504040095072034dc05034078554015510140e000b60500003c0903040c503c41e010030600c51a041c5c141480c180d4042110300781d0000e202e00b0149040040c12401603892038202da5000910302090f4100c8100040101c3c614020380420042600c58000080b0600a02c0307078a0380704 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 717072724 1250 717071474 717071489
    0x70f21080a0915090c0306050106020706080709080a030e0402270f01020303061c0302150112030f0e0307090c020a0b040605101715060d050d03060501030c09080316030e0a030804 78
    0x65441d54441042102c114030b80240010f000302e050512100415085080da1a0003040502c3d2416180d031141c20448000303911441c003585c00824104611a04003401690020481c01d080e0035580c074240485807203d010100007000c103c20307600c1c02d80c41560741e50306882811070f4003502c0d100343c070850400402142d002c00102e103101e00f0102c218120a5840001103038840c0d84040c03c060309600a00c29044d18100200c00c0860075400750341004012400a0040c0324028011064880c070050180c0c00d0140c12541441a00410080300303286084954030000303007080c112000b0020000d410144080102d08091071604000d144464910030b01082c804140c1003140603405e8000585000340ea5070750518000d5000118003569070f0080b0110030707119603407a02980c0d070002000d0010a198442c640e201410084030741d0802c80422baa45c1c07014444c55925100c0c0114000050810941807402e0410207950382c0540800e0b040ba446c442c1c40c141080620400d41d8000301c0d80098424441c168403132401c40e80d00d4106016005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 717073974 1250 717072724 717072737
    0x204080d03050106021018020f04110d0b0423041403040902040f08010e0601051f0e060705060f090c18060402070f030c0302011811090403170112051c02060705070f21 73
    0x190080c1ca14481c501c200d03c00c07034601f001c006d10b0550901100f2032107443e80e44e46c023039030300e4811400315038680005144081c03081c400000c40ca150407080200b11501c0c486464003003800300d0599000848228055074001d5000701082c000c10402c401d039244bd510541d0052090355002103000031f03d43d01040317810001d8800036802804402c0301148003c1d62004c003441010f9100003884d8001c2810003080c0860380015541c0e00d0080c500c42d0310700c1d004c10220b40c40144100c0d002e5100004024040601205083d003018804000d02044ca083d003000400e10500d140882c034407c01a040445c50300d9a50303604a0717007050b0b4000d0640000c00d10604010340085059030040e4059400e00d10303111007100c1184d458296080d03001c03131a07003101c1808000f403045503440280200c050040c18944200c041c081510801d0080400041000f90664a03103016401c1010011030f43c000800500c51420820350080f40c00d0f80e100c103541ca00252581c0d03a604141c1c005402420018000010354104900800c3c40d810140305240203513107031032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 717075224 1250 717073974 717073993
    0x10030c0f0e0906131709030106180b030703020f040c0c020d06140f060114090423090d021506190317091e011710030602040806060306070f02070312030204080d0305010602 75
    0x1e40c4400c802c07030701410000c59080041c0005000310b40d04e004211742081c0500c2c02d051414002c00d0843d01c6907000302c10806540700e01c1088105c0140100c00c0f1160094015015880c616400306042c3d00b180703e50303544219101c003960390314140304841a1b84142c0d0010300c901c00c0880d00c0d00b0702000500d10203086c4008401084c0005421200841109000711010b07502d00d00840c2540724600010303044110030b185c6c4213854402603404041016016001d072140840304500c00e0804619661a04500381013160642d001104803030140b0401802903944608140c50a9042c2e45003040352040001580d0001008018a201140070001c3c1c0b8501502c101502902c0c905840101e581c80c0f0000400064045400202c03100c0450341d104100080041d00546035140c1002000d44036603600d82030360070507040722085a01490400c81c181c5010064030f030b0060780e41c2c01c1000301408103007030080d01c41d006400041d14113030070820310303505d2284a50f041744d005004003000d680c2030a440800080180c4420300c5220010311505a10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 717076474 1250 717075224 717075241
    0x304230a0f0f140f010c08061c290f01030c0b0301121203020c0d020a12090302060a081b210603240604090b011805010803070804030b10030c0f0e 64
    0x1940c212504180407982103401640e40541c0c1e0b0707030444012510454903401615541c88100461180d5800d003c0010501e401e070580010b0565000078211481012203540c02100f18850055141d00560001480c0c8103484115a03100d0382c21440f2003407944800c1c0322404100c3e56802c500b134940e05880c451100000d01c1650317206010640c0c0404c2c00390401c64800f114031400050148520444102c4041c1005420051082403c0d030070600c5407501c00000d83c000f84046000c10043c080101903034403450810303075910b9041d0f03008603000f4014000e45409005542c2c000c20840346400540080250500100780e90390482d0189000340d82040c40018a00c3e852400082886841e000c900d0701000300c50142d0242900c60340b03681950340000b004c0c1560350031945e909160404281450005406021001c141e103000300c1c1c3d0003040c1c6040341c078164001005500140405000616040d0885040b243c000c0400344490310f44005070003400080d075000820300c40c00c400c40010300342001800d81040342d00d05510f02c40a5a51b0011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 717077724 1250 717076474 717076483
    0xc1101020c090f10150f08090d1b1e08040e160f0c031206081c050705030f1c050f1f080c151e070c0909032307050102030423 55
    0x40d2a40c01014800000c1961000f00c1d945070b80010440c0c45208081e07070b00c1c2006480ca0004510340c5000076030320710380300c614242c01020b841d4106046200500e071201401c030f001811410304806008808241d0718900d424000a040607132000180b04030100c0e034014140c44e01004690051050103400001e040018102c04075440300020050140c0c0c481c020f040081c0e50040f1b4000d805400200c0600802c96802d140d080d1941c491803001c1d0200c0002000c999045540d100d20100d202010386041050421034080000c5010042d5100500801c0c0020346031980200d10481c501c1500784140e100d5454042000001071003198164040c8840d00b84072200c0302e410703640340c000c5825140640603269100b0210f13242c0ca03080c84038240c0403c01c10783c1d0060341001c0c82c101030300c144e55058a402d2a40c00501288035030901492009880080000c0c040c200422540e47d40c2c003400d14007810300b0143d010112103040c06c00c48050103040f500100d91000c0210f54130300d40b0b45030024500c4200c0300c8004042c055200515803110300000d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 717078974 1250 717077724 717077743
    0x61d0301021e09130908130506040308122211010f0e0306010b0d1b030c021504030f03050901060b1314040e120f0915030604050a020a120b0d0803070c110102 69
    0xa0302c2496152080055503a80801e2140c0c0e00540d01445808000030544617002105124000c11030355200322103001d840c140c1c01030b04801d200750410041000064064012525a500d1200c0403400035514032550301101b80ca00c40e07a8241f41e11300d1403075840070060450213442000c1001d0301c50b80c205441d5110200c07007484001030340582513072080c00184404100b400180c40b05030711501c2c02092503200d4400c4202410301c00c56901c0e01007074503102c03032184107034051000740310300c01c0c0200781c00700300385031a440040c80250544ae409052540d50b101041e0100c0083d046038000d805c0c15541e140d900d00042a0811021205114440c410700ca40d003100c118a203440c4c00f40c401c040c14103c001b050b243e40e00600560f1594030110b03203c1d64542d8104007400341c644403011b281101d503004d51205900d9141680074041a07901c001c1550304220b1040040c54055500036030118000b0800a03000905280802c0204845409080b03001e000c0103400b10800c42c0d0a548000c265040e14032542680e14420a95401640e8030420075 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 717080224 1250 717078974 717078997
    0x10c020102040f06120f090c03030908010c0e09071709100501050f03060606210a0603030e0a031e081b0d1b120c060207140c030f0c0334061d030102 65
    0x28004001130352082461228110301c8001c0022414800315080b03003107401c006000c40708444e048030100185500080000011b0604d84002c0c0016141c450004200c105000443c0f031046035000042121203200e0f41a50b012154403040e240f4017414050b00d0300f652803c490003d204d01030704080c000701d40e81c140304040300301d00034000c0d0007404151035041c2005007680003e50516185031410310151070b07030b409050703116005900761b600c00217500b40bc40c200182240b41d0521a40d01401340b5090070800212900c420708211030000c1c00004481c036280c90146014454ac428a801d061101c2450389000000403682c0e80032180241c480c603d03003140311041c0c44d507680b00510001d014103c0310322224075500e000e406580c20062080340c0051070448180d803080c0210b000008200701560000b950089142020890b480351251702c50f00610f120303203004000a9541d0001c10100740121501e0309503a00c1002291006440c0314201d580401116450307800040141001042c49440c2101004025025040c10310071a01060101c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 717081474 1250 717080224 717080249
    0x100204050f120303013f1203150905060d05010218090708010605030105130905250b07050606130204031719080c03040330020c06010b09031005150a06020f010c02010204 74
    0xc2842200000c000f808843c5904200b0a14400c02110b88466080d416000c101e21b1000001983c05c0000507403015580107410316281c5141202800c5103a0800011610180008581c5503900800703e0304600513039030700600f150b00200b4483c0000111600d20140040262400043ca6449900450344980280310717200125900300300602003030500880340f071150000704501280c03165182d51070f1490103600e15444042642038101074134582030b249c00540010400244460700340401a00c0c0c03691160b40141000c1d01c92100b541c822114440182c0595004640000001202480303580d4401031a910046000b03048060f80f03078a100ca218000c00109000340ca00100290541e03880c3e82c0c05894501c0059001d4250401c2d42c8050200140701e6500c6209024400c2e101585505031420703658a06032068002c02c80311382c02800181101c1d20002886001c408a00001141c0e46e21803003000c416141c022450f20340c10084070ba078086461500012100d42d40203800008000d5140d180c04124200d002c7d0b4020035400b03154 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 717082724 1250 717081474 717081479
    0x309090a05070c08030f060a090c021b120a2109030f110112380f0d080f07111e10030c18151101020a080a05040f0203100204050f12030301 61
    0x965844280d20032290f0070085591800c0b03031942c6a40742c200704c4280100f440031000700806800c1c0030a19400a1001c0300050202c50800f4401a450b83d07545250b2050b00400441200300c1c560795524200052060801a1a0765400504126041d0380305907110001890b5401100c000603403040c41e440080b04c0c2c0001074142441b20300d903180041ca461030000641080707100d03840000b059140d40704040d044641405d05c1d1000140780311042d144203025001250b038034405540d19503500c0d101c00301d816840d1b2404442c896a010401d10f44400140900c41141038030179008100c05040101058507803000c00e204940341c200700c81e40c0450142a651640034083d800500c6d45000303041c814000c0c1c0003c00c42e0405402c00300c21500500306c01030200042c44d40224080003640420300c0c0342c60b412a18569005040000962400844110181003283c2c0a000400c0c030965810000e0180120001c041c2c106903801000d482840020401090107034000740a101c4c454589204101c02500c0d02800204140c04110080c60941e131 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 717083974 1250 717082724 717082741
    0x209010302060d0e2e060305030a03050c12090307020a0905090a060e151f0b0a0207060e0103090b0f161d0906010207120524061e1903061409030909 65
    0x200507110044a113510746444048030f40e428405c00c3c06140d441e0161450207951149419032002c21390100280e202d2404506001198001c02200c5214140342004291622035400701030041c46072002c000610798444091010011000c0010801c0c180200e585101c00c43c0c5804400c41212016102c088565010f002d8040c00101c1581201c98003a00f41000ea60108440c0300032803040d4401140c11003030f05010030580d015185171486841004d80070b6000c100c1d0506c503c110f0b001c2e54800041c0103071000d003d03e80074589000c1e0f2103a080840006c1c2d00002070b4600e03050031094a4811300082d150700c070420700640340c504003030f0f4490304407000c070380d1421017400300c0e90301445061050000003d8580d50440c0250340000c10240c03014400c030002c80303100b10000e042d21310000485000c0482181041090030020700c00340301c0b00c0e07620404600d03032100300c00305190018050b410000e0508800c11911207096081d22500006104282d400b1440e20540d02400c60010381c0e0309201c158413403003860318150b070110184000c1400b18 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 717085224 1250 717083974 717083977
    0xb04051e04110a0906090b120105010501080408030613020409020726120a02071a09060a1b050c0715020a15061a0c0c06030c0406020f060103020a1716030f020a12020901030206 77
    0x4603030183c81a000b694941283c40c05481c0316410140d080394480c100341116041050034000c070794514200170043c81d414a0002000440050300c044c080f04c070084045449580c82007408a2968404002190b813260f0f04d590750030203504084403e54221010043c0101064003c40402003c0700e030800400703141c0301c104601c2c803aa000028241144583d8244001000290b06400069102c840055501100c4ca0720104441c030b040707001040817411a0416490101c45d00c01084502030070310315814000c1d100c40300c00c03003940c2c0340181e40e9000d5101c6003840740c443d2101070380204000301e40703e000340344280c000c10004c03042c08240e4042c0d20581c041d02003844194040c080c00d80000c0d05051075110705940b85422548000340d66a00150b808428030080002d0070042660108030483c00100e680010748031641c515000961070000c944250710402c01c005600d402072803c244a0828520800c140e0b0403240b94607800c208120903032501c070803402418981c80c04510850454004a20158000e01d10384041e030a6a0078490b40303 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 717086330 1106 717085224 717085253
    0x70c17032a040506030f04031e0e030d0e03070302100c1b051c030e011d0604030b070201050906040c060f0e061c060b09010503040f051905010b04051e04 67
    0x941c40308005e0303e9000c0300c0c14620400c40d03503903800d0543e2801500c0e03166101c80b454400008420710381050180415800642c202c8007060414041554114001850540e1540c0420810130043c50004022030381d4001500c0c0900c0c60030320503641c1d20351044820103101c0f07070002424424056414084010780c40007012030040e80841c00d482d10054852660054079504202a00d40314140011020490300075034100580200d664641d00d00701841083d000703071070312001542040003040b103034503002450902554100c4142c5508610b880025a50070851322407800a0140e03100c1300b2401551007070080c106082605080a00b030800001c5042c0c01c4800c0c2d50444c00e80703001c0c00e0103903942d070340d82c01020f403070f40a1b41c45120b0703d00b80c66503420401e1500340944107804c1c01b561041d0810007004419045842980000d4030f00b0f018680b680004109070011495003d02c4002c00c2000007000700c0e00c03c0182181 = true := by decide +kernel

theorem cover : BRFrame.Cov 716906474 717086330 := by
  have h0 := BRFrame.cov_init 716906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 716906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 716906474 ≤ n) (h2 : n < 717086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
