-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3575
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:03:39.966625+00:00
-- url     : https://prove2.me/submissions/c72b63a6-99ba-474b-acbd-37fdbf060f8a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 642805755 ≤ n < 642985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 642807005 1250 642805755 642805829
    0x509060a0302030a0915241a07060e03030403110c0117010306090c09050c090315010803120c1908070806040506060a11190606050a0603150512010905010e0304 70
    0x105044080e4800c40007900010200c640c505d68032046440894091795a4005448606a0106425066070309803403202c1d0a0002070f411416a001080c03141004c1c4001448564842c00300b20fa449011500b8904084d000ca42011543d500000090105065112030b00003440030513075044410300724804004403902002c4008429080c00a100140001045900032101460180040c88800c0b0303140d240b9a01102e60642e07400c03030800320008400113241808d00c108a078112000d0350b90f1007258549240700340c4074424294641a03031118600090303158000c0e030098030600b100f4600c2224416020400c040e0150109a400c0c00200304101e000031410310301402914403c03600035040c2410710801190558400c850105c41c11094010306100d0b4004250309002c1c104502d0140314040b456030300c0d02c01070001d20001608100100340c1081e4030400401d81c104041012180c003512141441d00142802c14018600032200030455400e1105100c00e5900000252040d0b4100e40c1c47c1300c1092000c242c802002020300700d0680 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 642808255 1250 642807005 642807007
    0x5160915020c1c170903010b09040b040305031b0f120115020d030519110306042003151503090d022406060f0f0307030e16051806032107050d050906 65
    0x21030b8a081441000c40350326280a03490240703d40701c1c0d54002c0c40300c80d084042c0c0c0b6040340201c2c8252051409006209a00c4000c8e10040ca103402c064a500000100040004d803e11200201299034180c0701403084009296400d1196107420113145502e10b0340c0d0281503102e848880113000841c0703100304864400d40a03076198008011500c41c078071041d130140400401c5240c611140c11505d04050016015203188842400641a520315114080004448101020b030703805024441221100c45050822a0340000d01541401101100e040000301401142d00700c92010090102c2401520700c0c0000c1d4001c001c4141c2c0e000c0c1c80501480d24168030075540c030140c441c3c1044030400c0100381d090510400800d8280d038152103051801101c8041032a1542c000d07215440065550305841000ea0402d100f800c200c1c260707450310b60880e24a840009400104111030a0301461078100104008ea50100720513450f07140150361180034142140c0081b00c0c1600300740d8055550780241000340e42042e02c500112941050001c0410b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 642809505 1250 642808255 642808273
    0xd120e0a0b072003010608010e060a0c05040315020409090326060d0809030316050d09050609060703030c0201290310230a0b03100207021e130f020d0516091502 70
    0x7001c400c4034000a60600043c0d2040368598900380508009007940308004180d244100625920303066008018010b0a031410480d51031559004040701c0440350030000e060100d900d0715565900070b02c16a44141070491034808541304141e0003080341d002080d5001c10384010000d0b982d160481040b000c40c0d00d5607011803010040000550054060b00003080c0141c222803d102c0829240041c1c40c041d8041038841d03a2114034103051003644680c61401420003a102541000e00e5000450801e01400070700409050316032081c140158800d40c0000c0340540340100c0b0201a60b03218100d030b0b40c0c0f1407210310040c0c040e0050500b040300307182c003a020745a407031790380302c0800c0481e02d080030700c20703d02c00f030000e0042ca85658035200b03921104c0d40d04014410b0b029a42d03000c01a51890144104100c08800c808801c00034603032000c0000c05d503070b034034007018202a2424001003818201024550004d1040000241001d4a440c0c2400b00c150003542c00403240080544500d0102c4d80c8980c803004841c6c101d410f41c500107900c60b50392 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 642810755 1250 642809505 642809513
    0x11403150115110c03030a03090b07030902060d02210a0c0f020c1c140601140111010e0718091a0610020303101214010c0816090e04020f0303090d120e0a0b07 69
    0x5a460700d183d21000382e4407002100300020703003542e1287d50f040c00080d44500c9614148a02101030076000407050034200320a06180d40414464080c010862412036404118081f59a158000401c50b90484039802c000c40e00d8258a488000d140c0740d15080d00255001906010700c6000288458440c20300404034001e0f4410a240b412455a040404503902d1840c08034103031011a0801005000e015600610710b60a000c0030300040c00349910027888481a810482802a40000401c110b010703500e02c0f01c040c901e10701ca00c04011000d4018100e0040050107001c0043e035a40c1e080c00112805140116034905400354544000c81c3d0343c1c00140c400c566040c0342940108001940030182040311403003108500d448441901295084070585041e003401301d08850100481d400702580c251880300441c2c02c103440d489041030142e01d06910000c0009016420004020801d40c1d4208207070b030060b04000f003448040c2117107841c10b0440362013091580c00c04034461146100d240d25056071100181e070f4400103220b04050458503 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 642812005 1250 642810755 642810767
    0x13090506062b020c06040305090f100c06050615042306091e0316060f02120309252106110307050f211e01080f060105060d060e011403150115 62
    0x80050b0941c00c202c0052010014000f25101e103019840c1c00d91141c48070400d1000900e02c0380f100612450800344090601500031075880b01c0740381c020200050b66510b03440031a010100800d00800d0020000c10000390f4072428010b003400f801e08008125046003000c4091101d00d000e610700407075200d50303880306080c250013464601c0b1005920003070440c0e03450710000688409090311038103c2000075207400d002d40d0780d030341d010041c840c0c401580c01c144d18a1490170380b4855448405031480341c501c0d4550359524014070107498040c1d6024140b07074000c03411100e02005044d40d950303503501d004550b00d03810312000617980c1e02c080d01500e218a2036911031510f8007903e420360004641c0120024a503100e88607030312041c52800400018403172200220b981903580400c8001c08002c100503405090035a0140c0001c0c08201c01c041101c0381180d40070f581c0b994035070b0b9840c04200050041600191607078440340000054140315644001d010400170740594400004118441c0d80c170744000d01800c0c1030400e5007a601714616102e44 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 642813255 1250 642812005 642812077
    0x4091101080a0603021e0906030604020a1a0702030102040e0916030308040611120c030702152509170a06060e07090605090a23040c020d080f040c0b1309050606 70
    0x199000840c40d8617a400211101114001141c8241200064081500380400441d40040d003c900900c0302c1e1500358005020728a643c0a80c060b0100a0f00046481030031010944034080d500400a64445480c0e81c0c2808030002d08a99050a5104200070401120640e100c04c2e41502c0d05561200569a100c1d2250303809040c0d045002641d140041008400007201154160701900042d80155601c0c20450402803500300e51000c1c1952850b43c030300500c0124815002800240350040b81003100c0d1036580ba00c15944400036500c2195060386800034000c0e01c94020a014086130301c01c480c20491240c548001e24081c150490740340c400b18505144c2031082e540200d0182c203001500800c0c60b003c46444441400c00c500300c0180c0c4400a00c03030641c4401d85880c01e4050095007004e03610040c02c3c00c41c115000200182d4000e040d00c404205000041818418a007018201a050161100c0d65507a0f0710640031205d15114464001078624041c040340e00c903e003c2c403c42e106068000c81140311201c40800b80c1240c01c80c10 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 642814505 1250 642813255 642813271
    0x9030c0306051b1602010207091a1018121205041d15060c161205150403260f390d050117070617070c060e07080a060b0409110108 57
    0x605810f54100301260300074410341050803e14101055280b001915296564000164107410a00980404001e01071040c54a06084503004101c09502c242510b105840c1c10790707110070408083e00482d080700100c404405440c450314094038248110b58003100c250241c0d001c5d0003c01c40040c500805403000040b1100d801103509034a4542030070322603002426542c04008100041e8201c0701000411841c000e41d024010550360784020451003442e41c5007030300ca260f101c540306800c0c2c103842c000c201072501c41c1c5030803403480006542d40f005e42c030b4041c092050500b0301120710340c01030800d200000360202084100180e5001d400c00440008025003800890f101c071440784082c8156409005290849400e40121b0b4020010206030100e01340c0702660040c24505a41c0046040c4412410485032540071039110684c014020710701003803100c03810b28150014029038803059400f4070450001240d905008550030f02e05074469401000100c02071000d00c0280c4004030006031100d50110001e01c2107500503121940d0001700 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 642815755 1250 642814505 642814531
    0x103020712180905070908010615020304031b0e0a0204140d020102070612090602030a06030203210a050304110d05010b10140a0c080c0f031c022d070b1303020d09030c030605 76
    0x407003070f040701102e40031204240064080c0d081041309040030b1041a02400b0428404038002d400c2c0030003e0341e0381c4560701c4000d00c5151098000c00510010480003805030000ca562074400307081c00f4401d28041d40080c00351205002c00a00030214178500154032500141d81a0080c007841481c1c501c055400301c1051521f1840e1640b074042d90000220b0380d20044d4861210850002012420360040c10301d014001c0d80c0d15603000d0140c03440000d10f294060243c450000c400d1514030b0341c99956103404000d8081002c10140c2000e410100007007000f006403c04e40c070035102951600c1c4c54100d9520100c85000028103a105415001c210007103a103032050001103203080c051030385a031074440c40e81c91091403e140300f200f0b80c03c01d40021907140c0c0501c00001d880e205c2264120380c1581010780b90400c0f440344c4210b441c000b8481c4103c0d0a40303d2003000c0001d041d200d40301d42104070044035190a03c0c060700381d108400e0003200140128000842d259000e0408101960f80200003411540d085944440050002811015013248 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 642817005 1250 642815755 642815759
    0x30c07020415030b060607030516060608033105010804060c09080609030301090c1d010c0606150507050607022e0b0a03060f0b010302030601020d14072f010302071218 73
    0x840c0e0141401002c080035100901c6451070405540150011300b200388200c004015070f0001c6a80035060703440300391403801850703505102c80c54804c004003900e5000514a01000c10799092049080c503185894100c4800840305143c2250103601c0314040601440d404500c000300802c01046079a40724043c0c03030701e481c2400314036a9210840c00d850084102c800000e0395100000600c002c3c60540510751685480e82400000c0500c40c1e02e52070700300d030b0b0300759a171504100701c4c1c11348007080c4140f81e0800d200608a6080140549548110082c8254800d050a942c1489440c0c0466980c501c00104481c0300c02500180d001981011001038070300842c02d03551a09110380f9100c481d540c0381e1b1400c5030000218440c0c44002140e5885220b142e091303503039036810141454814420081d0070b9802007194407690089142c40c003920301c91803541d241c940c01050b0303000c0d01c003005929680078003245200d0101c2c2c120721546042c071070710002c00d0011001c2e8814800000c2c5241c1e60150086050750085100ba03424900503000500e0480d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 642818255 1250 642817005 642817009
    0x11040204032301090f020108070333080604082209050c1c0b0603070c051c05090109120f0209091005040803060a050f0303071e0f06050a0c0e03060c030c0702 69
    0xa0031541080c0c078000d00c260140101c0d02200d103800d06055104100070f000b543d0325a00c82d10300c0007452200c064107020003900065200c6103c0e07402814030080c4000c00c0c1c00040303140c0c0c0700c40f088041580144007503600e4012010a140c0b50008615200301c5d030194030f661400c18546059282102c0c070804408823018241004600d05680d070080b1031084a025403059110915401d804c0c2c1010f40c41c505080350070303140c542d41031000e031074060803294000d4250412400300c94041c03400a01c0d1040c0310600f40c1044200a0980348207550003001031659071401d99500f000203884241c140e03038941010384002c142c101d000700890300504141e808240d01001c503500755400300c55044815000c1d0b503000c40c0c086030f07420750000030804145070042107840a0f22043c1c84c3c001c1c041c01843c021a0380c9110b6000080e1803556001c980360402c01c0e81800d1180da141d4040103d9043c00401c0c0303801c4010b0034044c5e80103905603003056412a58240b2515610303d0001c401001030801d6111110900d8541e030000d454464080c10400180d400b503 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 642819505 1250 642818255 642818257
    0x8100c11060a0b04140f0705090d020405040c17070b04031b05090f0609090a022d0a0305101413020f010e06161106030c30070e031b100804110402 64
    0x41c06200c1c2d003c90102d11040c1000121128180c01c0418101c2c0078041c00080e0b25078001c06540480e150a049503598141d0000800384412180c00a40c0035003804200700402c00700070135890440c0c4020202404198085000701e0b1540341390301030154000303c184801c001241d241a24880c0890400c1780710415aa101c0b80468217005d400c0351903024183e8000c05000442c02c10145040c0d001840c88040e20b504881903001807a544002c622560509007003126602864012030504d0310f10000040c40040100e44d80c0c9080c6803105441c103400c028091518448842840504829034883e1042ea20080b00c00c0925508011240042100903810080381101c080250b4039220002e0000090090168103040c01629084522840d952501d500804c030510620102c1860300302650f0b604020409000e03180010a481d0740301003440c4000641c00303c0c00320428010925009881e0501010003902a114180f441c040c015465400f0318071107c0e00544240d0800c48a2481485041e0300503205681e0102c206802c80009030603 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 642820755 1250 642819505 642819511
    0x210a081909060228030b030c0607150507020f010b010305040b190f0608070e010803121303020c060a08150906090a0e01240f091b080702030d0501081e0708100c1106 72
    0x41e034408130161341202041e100154540d0a0502e0148214a41100400d4590750607141c00d60188201041e07200070420401071704813030007030b841302c00300100e1910400003075507a0071004000f0501c1d440e00b40d92030490352080c010144116000400071130151605c016a420b4413400d0051003c2556540c070800c6407143e09401a075004214143c02055020700704104000580d106920030308e010380c01000607024024031000a150b01c4800c1300940b6000b10101d040590500841c40704260b07014000103071041403aa0411800360203026240040164010720303030140140b00b6000e0f070f00783d075100c40c40c100004c0d80b00d002e68100e148500801c000103c2da1401180d50202e52443ca0f0b05150305080040d02c0c240700521819080c03500415441500340585c0444401005c0400e089540b81820000c29a00040c81c160003001284e4100d5115207081001d90b035a0b608443e1206980091400d6181c500c600d0049854400107482c01603880315130260400e21207007003074034006001044200041c8034061092031045041400300030b04c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 642822005 1250 642820755 642820777
    0x901030309150e0310150b121009140c09150f07030e03070308190c15050115031e0c09080708060a150e0411190602210a0819090602 58
    0xd4654200119810031108114682d010002e480902c0303001030390002000d8400c44504030002400b4003a104440c102070b00603800c5242182030000d101080000f185902a10580c3c000e42072500c80760300e9810704011b0b1200c681a400d04001030030081401c6113030050052540e00001000c1145c0301c0c2d082078161001d608001d804008a10700424000d0a150704444c241c03c0c02e80c1c0484c0071701001403c680e80c0b10541c1c00360840e5886a14501401c5114103805100700c000d06c0b91304462841b180514050b0800007600e02401400044140260f1500340580607020760700c60a000c40c28041c2d19440c0d0106190020320240705c94030100850904006400401400000050094a800b914040c40c2024641003900e1504450ba803c1442d030040800801e45204012a049036014400b805081940d1001841980701d2100c0703070700d101d02c1e10140080c0c840e40002d030f181010341c0300d0340480d118081a100c440d03115000d013075545408a03e014000a4950390644c84101e050b802240d00080c8005031070303c48404982083c0c0c0140 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 642823255 1250 642822005 642822017
    0x150e0a150606140f0a0201060b03180f160e0a0204120f0302012d0b0433230909010e0102070f02180412120902060c03090112020a02060c1809010303 65
    0x4510012600500d4007601181c10208541c202c3d18400041621401340c21150a250104007000040c0c802e41101c001040d10003900d507182e0038004c03503e01807041040c0d0310700b0940c82120380d9110504e40100d84810b000103102c800306071151428044c03010f1400018403d8400750ba0030040031400400072001240a00d00400912145a503103140c0642112002800511241d180e01e100050780100b4851410340c1c044002d43c04110800c039000440d002d8039a4900c1e00f2007070103540840c40b030f03129005404480740c42e01340da40d040301440d9a5102520310403270080d01c140e13001c64945141310507410203801040d0002000e0000007140006031000500b241c0105008407440030400c41c1311019803400300004131110340c4c845040d001c2424559182d480301c000c1c20030801e050010074039107071030982c4240e4404102c9030380181446544a140b03003403440d26540300844250100e515000303030244079582da20a6610b401401c1c1c00410403501c42c4c1c0b03000182074003c500201c0300c20170740f0240030f031180d106d03610198000c41c806d407545 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 642824505 1250 642823255 642823283
    0x30501050a0905060a140412170c130501030203060a050d081b100605120606090c0d05010306020a080c070c0605073e03010e2d031914070f150e0a 64
    0x594101440a011017907440e00f005c05880f94000c1e0241c1503500076134043c0c4100c294003a161400e82d43c03551200040340c0d00582c20030070030000c400d111004201c80240b818013405815141d40042d812400141c43c001d4220130502070500403402c116240d1034131140120a283c0c00c5c56020000a410010240c109528680000e0300307080c2c00e95694021030020f0b201c101d42040d10b80c655440e841d0b03520007009001c64490358940010030b00c1907110004903504800b684a00380005c1da100e00700f0300c01940c07041100e035000407040e40010b03e00c0101803082e601ca01d031340710621989151070420100c98907004004190b400080030a859070400d201c000002d0b11300394182c0d004102c022a000c004c00b12110191320094040c2c4d04102c862501d031000422002965180c02d030815080c10f01c44042c503001110780c001120482c0c800000c0b4007020700d4003141300b40c0e400401581c0c0e8207007403800d440c461001c5001b001070040c1a0b45440c1d03544c2d80090042300c1850202c00c10700c0e1000445c42441c41555262544056068030311000000c03038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 642825755 1250 642824505 642824513
    0x60b120a0309051005030f04150c02010209091b0a0809030426010b120a0b0a0207050a03090e061503010b07060b04110d050f01050a0b0a02070302100806120105010627030501050a09 79
    0x1120000305800c541c180134240301c803040030303080f484010301c4068040006d100140400403440c02c41190881c000004200075025200041c1c001e50015441030710401d00700000070460295001c0d00144404004001410a026040181c40400000d02240c443d404240400b10703404890440101c44c402600d045801d03090541420740f03007140c154400d803602030b540e8030018004e80200003a10030b14065101c558810183d41c1d140340c00d002401440001072850084c3c2203000140b6a001c4d9403082036071085c00309007142c0c0c0c81d41c030108a10000c0c0c1c014500c101c1c0405100400c81601c69002810415005174004201180c98038006422500c602c168040601c0011800044030328840c401c1991000b0300d01d22010055043c000010340035081e5200b03540d412840083d601240030b10900c582002103601810950009104100c00f5214540c101c03401405100c5001103001c5c13122050007054101d5a241c0c5501082c07130301c21200c5500d0005800203417a0711072203001d40000090000d114003841100805070020340603c8078a0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 642827005 1250 642825755 642825767
    0x3081201060f032a171e0705091f02190b07110a020312160c03031d090403090302090601180e06180106092c2419030609060b120a03 58
    0x2d007000805142007008040203400c80d0001c110700e2046201c11054071181d10b42241c641c803402c60042950200d000500501c040c5150f0004009039244960291a40d00c03c082200c5502420b031a00381d00c80001e4886045a80c1d20760500284600c3d14415500ca05204440c2c08064a880340c0b4100d841d0b4001c00100075059600c081012480c0c04010080c0800e46041d4000940e82c41481306850b10050001a4201405103001610551594004484041c43d5903d0070058002c0b00c821402403108000340c0041030303491900003c0c4a109643c10b071038040c0c40906540134030403442c00081a0505000c038022241071440050350b00075004210340c2120301b0240c500742c81800504c407119881502d45c01c1548d070044c840690040b1204007514441186013015500c1c1601f41c158580c0312540d0110321401d180107010901c411129150300324590020ba05c1e40c018052024050301d5884856800130382200401c003400010080e07040050140c0c018100840c14418040c00100154030010102c110769010b0b1b9518401c00d03410031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 642828255 1250 642827005 642827027
    0x504090504050c03011803020619150801020307080609090613030e0402270d120305090703020d0b0a050105030c06090111070f0f180b09040305090a080d050d060801020a0e190308120106 81
    0x203070000041006d540e4000c1e6555202506d00c0134948907248402c0310101c195404011508860a000d810842c1d5941c14a8000d602c1900e2140000391031a0005589082000100340501d50b1040201656a11503a0b00c00130600e014200f107082240600d662001c1d50707501c1c0064032212900d00701c2078860f6020080380461494140c85402e00a946003141d003404241349417156444441c007802c02141e2a40d070103103183d040012941000b94420a100d81300c209110240c040c6c940310303030380c0c0200c00c00850341c03a03004155503044010343c016889402040b5040c40c6503c202a407407150000c80045a020507107a41030003001f00912381045942c40392240c010807041c0c51008503402c0092448a040040d580742070086021103030001c0c005018000005182cad0701507118415044014000c4800352040003114903001000c0341c0c0000815420b2a040400c0815000018400c40365801c1494907070100c20300f810000c0c40f45811000500503810b115940c2c2c0000451303820001818201d002c1e10000c441981005005010060b0b11 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 642829505 1250 642828255 642828281
    0x61c030e240c0f0d091203050c0a0b150102121e120a05070f05040501020c2707050c0115050906190e09010203070f020c13050a0609020d0204050f150d0b010504090504050c0301 77
    0x45644c05841d030003181c504140c0b00360040544c00e149032800c064402d84102c14000481d841443c810b0700512000d03007820341c01043d2101010201c44503c03001281e503024000300042d0440b030100000020070401c1801c9031b444480640d40d99003000741c0c032035485090f5a82114050021611b981c100f064980d404540706072208440e0804900381414000003c0d03585208003440c50007000101d05250421741c0002a41460310008528460a498448002401604065801d01c4c0960030105140c10000d9100101400c4d544054048500e81d6510b80800800051143e511400d0944000b404a51401000d50040c80f03401c1c802c0015980b41440c00004164040d240301c1b0b030045400507407070100c8507512510060171032000c5481c04a06516078000100c000d0089500c10600c842c4000b80021885c0c02e9600900b003102c00c12140b5907000309400c418800b40b00315070596a260301004201034150315034698018402c0075810324081c1d040649030309080c1b00700c440c1039805880300c0d4441e40083d04540780c24010400b5041304 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 642830755 1250 642829505 642829513
    0x7031d120d180f02012a050c01020601050103061a031506070f02011211070f1112060a05090303190e010902090106111b0d02010806150f0a0206061c030e240c0f 70
    0x14075111518003d652103002030400c01d520102401091102c8680c2c6603414180400007002449403500c1595001030180c410f0160003441e00005066011f80700e008104c07010b0340b01982d050040c5070420813090344010304007095002c4c5142150204c0c0c66910241843c5441030b400003c1c070074800d00014155410352001280964103124044115208004c15603c00c140d210380d80c84525482881c0c02840318000e030100f150494250414103c5105000030a1401003c08040030099900c1d00a0041d41720300c03089507210008103241145450684069100001d0507084000000b881401c5500040c0d80310350a078401400504c4e100742c085d5500100344454001c00414946000390300c164400071074040c00064801038140049440060650b40700d03e400915009094806980e450110600e1009103400036810000140b0903500000c00c20f04110f0407600d207183c18000d0700403000300155805c4800c04c00c807188075034002d401c0d03483c1c4d400d4501f01c1c5014a400c0409211089855030700070003490b817501d010480d0311403107a40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 642832005 1250 642830755 642830801
    0x504081306110105060d03120b120d050a18080a0320030301060302071a060f060d06050d050115092703051201060f120519050403171e0c0a020607031d120d 68
    0x3401823080303412881c801001103442c1060340006801c8204100b100070031809040580c8005551080040100000f562200031004c034820084200c041201e001e5100280c0c00003072408007103801100d114601c14116000000940490440141580c0083e80b1000102e0307004a289000c1050403030b9400398514806680c1c40280c5003801c001031926480703086160244c580040da04803091016013110014010140c00e07000040d05034980345008007841d0131a207200d1003480c0004100140203000d15041c3d04000e4070441d40c04440c0030a0f01158440f13644040742800010880c03840010201c0d03007000c3c0200340503140c5000781e0980620203000098219140803645141208000d47c200c03200c10f0801030102c035107100141030751b03407403406035072001007680a08440d07142d1904006000391443c0058011442c4c00d040c0c0c400503200c89602980d02d014014030000542c000d44000341c1e04034400c2c3d00c2084040e2035044c0c03000040b50000101c1d8208850450b0b10f240b550350001d001800c209081c011040407424649400110038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 642833255 1250 642832005 642832007
    0x705060411010518041a040204230d03050d0c05090d0b0414070f0b130f090504050c010504120209251d0a03170c2a010e09060d060504081306110105060d03 68
    0x2d036942020340709a46d00d94040c55000c0e0410300c980c460600140003103599545949107000301c540e0180103104181e00c1103003044100c0c107001da00c00c03c06a0341500da590510440000e00800b410764000c5240410009120341c5885940d29545601c40b207028603d00526424103051410000c01c20325010f1820b9844020200400d140902001007200c2c00281c1070707510742c90b00340380310000e4130005d5016154490030364401054644050340101c2c05584204202d031390001d8880010355450203a0300c60041a00098883e42001d802c022404a40c400140905108440907c0c601b0409401c4d6004035200000c14100103204c1c15681800d401d207014500300c4280f501d03030780355543c2c000b0020342c502d054040c003d0000c1040c94030ba10341005034050000307400c0b904403500424550880c000407034020b10075000850807035020040342080c4040074003412024103c0c080c4800c640d200c0c035002c0c01010b0002c9481060400001c0080c07410461008041c2c8225615407041d0f42c80110b4080c01d68a018101e00c1c403403448108620006 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 642834505 1250 642833255 642833287
    0x8090c03210d15060e040b01050405040f09050609030a1d030a230d0519080118020a0c08160b150d1e02180601121b05030603100207050604110105 64
    0x503511054102601410704060314074070707026a9448200e4075060840c0c40a0340b01e10100300da4103641c041e60fa0510102e980c01c0402040d03034040c44284c1d0200303504010a00540c285504447c44c103007904000401e0829140d900d80c4d141c61401c55807a0440e80003c902a90000c0d40801081801071602c001c084011507154002505c40140203c0106034061100d0b000b9a082071046203184510300c01ca09503200301c0d054030f02c0a02682d02c45c096030700c220b48407884200c20301c6000c0d01149051f40c005040ca000c030700c108080c24074001d5009a00300420f20031030101d10000500789200402c1d0303020660b044114801c440745400c000d07105002d0101c840507442c1540318490354444443c01c40d900c503048007182003a03984158880c000d0044245010303401002050019942e90304a00803580034200aa8820750f2090a00001200311440c5800d20039032000000e03035281d0300d6441440a140c004a005013a2024108003030781481c100c1e800030740212520380110003000144018006258880d0100b820010b241144442601c0c41d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 642835755 1250 642834505 642834523
    0x1706060a150903061a040f0e0709020a030e1b101112031503100c02060a0605010c020d060b0a03050a15090b0604050403020723040e0109080d0207060f11090108090c03 73
    0xa80041c0c0741e9200c0c081c522507141d0800950300100200841c1010311740003c80c40c1c0e480030005000b1410100000840d40c00751040061081001d00500381442c2402044006544010346c01c0040545800d4812620042400401c04003642540c00613030b000721150901245590542d440414400c5d186000e51103103401064000960700018401540d170f580b880c0c05120080c2c00e1000007a0503111703a03400d51044610b01d900142c80c050030303038017200d15913a40c16041a00b55030072400b8550010303582a4101d0014100810402c0506218910120b1100d200b5000700e903600c1441d5005507141d5100080043c107000180f4000e0940c0080003074244210000c41d1280c18101001805040c0100d540d0000601818030034001000a0b003284009000110020300350701050500e51060148507c0c6001d07000c100852052150070300e0183d00400040c1400b510a1420009420286081d1011a1200b12142e1203092600c50b417a800c0a010b80350f1a15043c81000041411100501c4a0502c0d0301c481291403407583c002403a011 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 642837005 1250 642835755 642835769
    0x20c0d110d21110d1b09050f0a1206020f1614071212030902060c0708010506090f1b041e1508060901050d06110a081801021305040f150e011706060a 65
    0x101c2250342c80d402e1950348071300800d4140c03091138100344c0d07000e01d8041031280030351840755500d4183c000c0d111400c000210301900d41080c0d1000c07501c01e00700002e681c25030582c119140504801418501e42240003245584001e0055094144081c0c4001c08c000c5514039282007035603002c0007041d4541c00c1581c08000304120142c00b50049550301412401140b09030040c900941c0d024081e151103818200d1400d544450600035040c9a50a11000940030704200c0b40306449a020a18040703540d440315a001050048220504404600200008100070990150a0724680310084840817141d1402808100c400394079003540b810480300d003040c440c00b42d8071280030905540c0100c0d070300c03120100c6c54a070680c001c101e8243c01e000d0700840440c1d085540740e0080d080b1403113a05541504240040b0710b20f01c20f801c1740b08001017018108078680051081d0b00302544004444405400001488a400807081c2d071255081e0380010800142c101c0180464040d41d55a143d1103450700c002803a19082550008000100e0703801104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 642838255 1250 642837005 642837011
    0x10c020f0d0801120f0203100915110c030a18150804110402131701021e040807060c1a041109090c1003150317071e17032701020c0d110d21 61
    0xb0a40d9130601003403040001003c01001320741003070300e4500d80c400e000542e8078090500d80200007141d2180e00c1c084ce201071500030003851070820301e003200b906d0b6001c0300d102c0c24103049000a40480d01c2c0c0039482440a0420032030b05c0741c80d03403807400f0303e000790b0300715400741c0b440380180d0050003a5142101203043e4a41078800142a03404503032071003240240240240607880c1c00c00500c110250413000c4403000108203990110040d07800c140c0c0c5402c003e0300c140c1036904005000ba43c0c04103402000c013151030080c0da0030610070030105619a04000020700b15290940301052107030048400e850b5145407144240c240134020b410103101c07020043c6540301c20392445200c0901056100f1815000082255080b181d4181c0d01c110300c428140e11084004040c4070440c1e0040381c00708083d5440d10300710f8041c942030f03071320848845504c41d00700003030500003100b80700010a040c290b640d028006015500b40500080610440d2907070f590b125010003480d054580031001204006002d00880d08000340381400d81031004822625a000c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 642839505 1250 642838255 642838283
    0x509160302060a032d0614030d0507060f0b0904060e16050a0b0d240801051b030112060b03060711061e06210a060501051206010807050d060e010c020f0d080112 70
    0x8062407084a080394040c481c0c05178010b80c480c0795030f5010b0400c0e28074907000e900b03100401c10280742e9524050171000c00815420700504c0006589600030500c0d24259490208e0014a180c004c1f45004406482c11581c05848500061b06071904010031002191200d800b075195524040115154103a24007890b0388810700013038441c4000340c1c5600800c02c061895206c0c0c0c081520706c000700d40c0c0442864061704046508040c082082c61501114040a900200c1c010b80e1859203042545180307954041d0007201d44030340b00e500300c1043e550306000170351280d1915151480d40c0181c00c1c1c451820318400500d110303811031503000080341d0007070039442403580400c05580003401c003000d03500c000f1409840032000006c6031103400400001c010704c64000e036040b00c40c2694000b42c140d440e4940c6076140c076402d0182c0240b13a4040c80c000c02041c6030230704148940c2401200005a0b802c452100c060944c1d0714121100c0140e404180c0da14601003040120340d080c01e58070301d44920070354180044501000c003c100043e08202d855055 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 642840755 1250 642839505 642839531
    0x60103022d0316050f120402010e130515060c0a030e0607051f050a0207020d11040f02070507080c01050301032001120c1e020a05120f070b0a0509160302060a03 70
    0x7200081c0840810140707000c1075a006000c500c0c0e1003103440800040c0b00008a2028501410035503d2030f5488016060804d041041d58240b103c0c0700800a034100f200c00f8034495001c1d00c5e28054000d688100c1440419185010302e50451145581c02c2d00c02d0051800300100c0205030f801003545001d07580d040c40c04403000c60002c1d0008146009500d07000e02603000e01c0041000e5101000b64890032102440030501190b600d00e003400301280603980d00039401414081c4400f000601034903500001007001000010004000c04001c0226045018122440ea010504c01d11440604204c82100d0b60424139200d491581190780da0303070340041540752041a100c005140d200d4282e01801040024400a400070049107042020080000d00007072005956a0304510464510314404104a40780c20f41010040580300032100070301d2081d50100402606d4120184171100002c2c045240300e6000f090400000304d0103003441035141c0e0800020001841443d000300390200016140c40050b110001c4003420002509018510 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 642842005 1250 642840755 642840787
    0x70e0f030c2d100509010e010e06030a0c0908011e050a110d090203120c0115050604060906080c070212061b03160302031305010e0a1505090319030e030a17071706010302 74
    0xa14641c2c48030001403d2101030b41d118000d07141c003900c00d0340d5034404a001000107480382c5090170f40f1541c110030f0410001d20200c4254020300301d00b200501d0207075001650b66882900310340381d5101c000c02d0001030036507820070303a840d500a03150040700d001410802d2a00b18080800d01d4825844003d0201342c9034001e0f401555001d1202880480039041400e40c1c13024034808550007018000011305003411544000b14079828603134242d0b8161401a281c03010401d050140590380c08000824103055920f04100c04c100503290421a400c003d18044010321240c101084807003c03000c0c1000011264030814002c11801d078054070b0180e03071250110704005a4a803101074002c0e0580f00c0c01c00c4040c2240d82040c0840301c081c90002507140c50680141040c545001c0e03020403d1041d260295209242507006018407854016520703a901a80760041c200090140f01d00504c1d0703800c540081e040300d40410344c07140b4042580b100749028503501610340c3c680002c0d1703080e4802d0a20302041028102e9410580d01052401403051008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 642843255 1250 642842005 642842089
    0xa0f081f2d0605090f0a0c0f0503010501110f0a0503040807090c0e0d03031d28230a0b010602030415020c220e060103050d030c0807080105091509070e0f030c 69
    0xa41113507180d00d00f00128080010341940c3c15140a850140c44a42042c899801800303202c500da0348542c5540d01e40f900440300514808130341d40c240d018445030b060030000104020000b85110f20301030740e2920319041c002410710070590710110040e81080303030300280c0561080000c002e0315821110126461140d040840007883c841ca500398032080170f030a0019508500241c4005202e01400358881d84100e000d1100009801c3c0f00c5000300800320809403101d0181d0002d84140000030801c2c1140d40d000050b40361b54900020a90006015810004040c40042d82d6000f043c94154643e000400300743c04c099002c9611042a103c2d281090502c2c41d031a0140300c0345a4020f2101500040211049540c403810880e03121580d58902c040881d00c0e10b08021103580c05001c1302485240c42d501d40002d26864542403090b03049004144425200c00020706081760b688940300d0318003a48295940c2c040680017a01070040c540d103902040da1082d401480c0040380f03a549d1500c806401c61105004140c4401108142e0784215096 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 642844505 1250 642843255 642843259
    0x40605070318050a020405060d02030309040f2c0d030c1209020f0604140f100f0309030c0b070512252007030f050106050607080d02090a0f081f2d0605 66
    0x840e50b210900c00006801010b1900895041100f600c413081000042c0c2000d0710002d405803c14498007849107480d0b4440c00c83d49080780307004900b80c1c14001c51500501108110015501c070721440c8000000381c2003002c0c01c600141810100700000d170200740078005411038018141555200c5042208549598608507120100945099151070315004021440010150014082c0315200005501032900200104542819840f042c9a80c00c1f1148101d014001002040e400e00142141d52030008604d9000030384109a141e503680d440308180d0b840f02d010044064003101c004505408140018002c00080302d440080a04004c00405440d2620090444c074000c061405409400400414804050070411005102c1c4008000c6a519041001640e000c3c01c80003800c040302c28850305110003110340c0180880b070001480300600c3c9075100c4004601124039040402c617500b21441c4040f201c006003c1540390305411010900c4400001c0080400681c0c0300c100d4601c0c90042003000e96641503a9a11040c00381c500 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 642845755 1250 642844505 642844541
    0x50604140310061505031f0b030a050907080d110f070803090a08010603121d0a091d01060b12041505250e091902040503030c0106060905090106080406050703 69
    0x26440040a104103030412890090040015401000034a4454803040d1202a460281c954042240403151508010580704001c1000d8200d0b200d1005054588801000e441060a03503e02e052580c02042e600040e01c0c0030110713400700009010520300414030070b04001d01881c0c440c2e040400c0441c2c6c00e14004071692440039901130500c02140e4040302000504d00c2e44c1040da4880c1030b6607a21903080c0d088034500c0c4005014018001c174580511886904141c0c25181e81502c090450600400080d907020915400342401035079a6281825800f40618200400e516440c000c0001c546001c2e4224400d100381c82113410104c0c4001e00040400052120011070074505d410100b105141580e06801c5020490f4810215004c207014500110b03131091602c1c1c1d2a030f01000c1c10121450310f40401c0c03448840c4842c5540300704182c0a001c081060345041010340303d003402c00d000104000c5e02d03141c0d0290084003150080d6005460580c0103110341d940050195412903800000000c056444007012001441110542a00800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 642847005 1250 642845755 642845759
    0x903071401062c0105010c080d0c0c170f090906060705060f0103051b010e0103090c080307080d0c090e191407081e130b090a0b04050d020d180519050604 67
    0x3405501c100240c4030706150802c1080c1c50034032008203e07494141003466220960300140310651144000004452080c401302e424034400070034090640350003070390b004001a5034518400500031000c1311950702410064000d49800044161385070a03100e4240712500800d01c210204074203813a00d1048074485504901502e990b0b042440cc4041c00038000e100507a090300c078200402003e810055140902000140c55a19840b40303040d00540140c100e1400c15202541402000079800b001840109070252040020310707918404184881c003141c00c02c581c0e28040141c500000d000ca07407001e00c0c6560704a50f401d2582d00303405020003440c85c05004c0600c0300c0509090007030184800703944c10000c018050081c4008071940302614488000f03000104035105075803056a00d8014000c0307000c40a405030010b074500240c0760091240e45402c41c00000c1a18200c4066204502201606505014003501d400d405d16110f403203452002541103040c10756004481c41000e000c04034600c0c0ca000c01a580e070040c0303000750071030340c0381d0f5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 642848255 1250 642847005 642847043
    0x60e0d17070b090c091314072709030903030c0516030b06030c03060403051909080a050a050609070e0c1b0a030906020c090408040308130b1602010f08041109090307 72
    0x60801d0740111a03070812040400e008103008242d00c0d052400c00360108031669241c0c500c0001100c502c940554405240d2080030203200c00510201001d00840300028800c59144071029503181d205501e1144160b10317001c40f51002903030180e446001c894043c40c242c1215031b0203082c018104104084140e09403140c16400004100316450581e114902c2141682d4041000c0c8080c162656002c50300240020760400041041c405201125400524686032072035140380c94060b507038a820100442a143c81d4014644034040100411015600c03525031409460ba49281080500d80c8806c042c104c0d0070a0714012803c00201c6070540788125920405100312040403d880c10b0140c0364a455010f050018003a448440d007142c108055118002ca41c0001c0451405241d03450707500f91a0000c000c0128503c0e0300c02000110324102c0307405040703010b81d440e01002c107141d0f03a8800035110084422a00c400c0c08000410032020034034400944200480a5480f692156035a81006045100d101c40007099540740200e030710055 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 642849505 1250 642848255 642848257
    0xf0a080a0f090e1603050112030915031d0f0115080d2001090b0103021528030b060316090e070f11030d02130f08010e0a260f09030d030213060e0d17 65
    0xa1342c07540c40410071643c9a1900802e080071001028011a1820000f0001115070f0002180440e0303140c50000ba5414044441646984441030b039040e056120340585240f844081c4a00c14003022600813003101207140840c5184c403100340c2e0a44100744525030f101c003400c9941010f5601940d1200078000c004080481ca0900d814040c28002039005030b440c00d01c045061010303c8122544110130510010004d0440081180f07401e021407101c504168540c400240c00e40c4031140614040c10462400d01d002030345a01008005801030391000b814400c543c2c041c0510f15070054000c035800d030094a0000c4210200400c000e18500c540040c021480c1d100048480007021085140425a0509800a1005a41e843c0c01038203840131940340345500d401950307408000900414507910f48501c00d414080b4030f11010510150f4941151a4075141000c0c0056201c005140912441c001c0e8070030b5080850074150600b040030350390030aa001c0c150a00c00341c0410303282542d4455080804807603002c00c07124030256080000c0d51403 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 642850755 1250 642849505 642849541
    0xf03020417031c0c09050910030609030228030c030507051507020a020a050a0b0316020f031204031b080d0f090f0f0219031101140903010c090501020f0a080a0f090e 72
    0x10490942c801203c2803c0701c0c001c0ba11607290595602542506200c10441c45030380c0a0f02010702005469400400101103014404105010790064240072050742c0304041a0030042c040340c0035001e5002d88100020780c209890028075605464170944031041454070600e80f520341d140462040c5240c0741080300039580050611860382c82501c0410205a5071000c2c06480c00c00f90140c4d21180f201070001521064020704606504603d601c12188a2540c600f0011306550100d01c94003400244582040705264018207819059140a140e00f8003005140d140d0151b9030150749071150400c0d03101c1c01400b00c0c200450b00b01540c980c1d00216058050900e61805100f40c0441180c100e0140c0b010002452075208603001100c1126000110304a03110394500c011921000809621501c200042c428000e0381d803024854400000e117241c403082134007810080003a1401c0155860005036070302111040c0c0015046900f941ca080b000d6040c251100b003441c00043c5e40030303001500120080400341040200c400200c0701c151030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 642852005 1250 642850755 642850777
    0xd0f151b021b03060103080a090902030a0605090c03070c0605070c0212010603030206062209020a090212040314250c051905040c0504060c03080601050c161e0608070f0302041703 78
    0x480c07180d116220030b402d50b48000561681050004102080c2e0754802003100d40710901c1c01100440d2110300c0f550880c1c0081c1c49680d0943ea95580c14001d9040001d01c66800188070841c0328158940518000c02c8005070305001072200b070701d82c1c0109240350b008080c02c100d0958020b0501031100c02002c9418024411444141d005205d400301044460902c0c600400c4815825103110504246103080741026240c05a01282c010f0300782800000c034400184084c01e02d60283c1408a009401c00d400d00411102c3c582c00c601c0b904060810900484440502d160f000403c8080c0032240c107401c01c2c0c01d0111420b01030f980865000350903c21040008035400c0504820f07100120343c20000e1500e4404102d0b0b02c0d009078012400841c1d580707000341011038064070025034003000500d07140346060031a40c441c60420040414214030345001090a12101d20040a00206016400030300c1403003500d0078600414441c0050200014040311592500009105ea01180d001d000f0b00074150b1400315481d21010394075407001c101c200c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 642853255 1250 642852005 642852013
    0xd060209100905100807020c0607030c06150506040504180503070b010303171b0c0709020a0f0914030c010c060b03190b060d150f020409060e0718050d0f151b02 70
    0x852080c01001c41ca42035030805450b03500c583c142a003040e520741700c2c040e0151040d40301d040c031040d080c0d81d181001000f907148071340d0380c408040070117107090b105403061f40000d8451740403103c900348601c2d110f200c10f840071a54221404100d42940084091007051403c0b406425408000b4200c0180116003891604a920940d44c0c44a8401075800842210b001a582454402d40c06800c0504140317108018280c84402e24081c0c41540795034a000303000702d038000100300740414040c6d030021049541000341c08000b070094000000300300c1d60080000e5181d02c0d02c1d6200d503052000070035800c030038412160700c9403505d2030001c0c04985801c004591025210741c0761400803641c40703086000140b014148520121025070340441500c08607124600c100d0040c05052081c98030041e400d01000607106203600a800080c44412a0841c6606110308002c08161203400e076407414282c6c0d05420040d0780c9900c0d810169182d001faa8129480040703142c03901034005200102c2c0a0340741040462030100081c01130101442c00550216 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 642854505 1250 642853255 642853279
    0x180b0a0617030301030803040605060f0a090c020c0402130e072114070507030804140a02060d0f0b0a0807150329090901060812070204061502060a18051e0c0d060209 72
    0x1550b5244004d0000402c02e010a2021400080050300200d402120080c804800011054046401411103078400c1001d01c2e103400c485824250140320000b200703901a60158a00640b8464005850300381d07200381030303101d100440001d0740c5510442e050152681482d4001403e0342410321240051300300318662800d40103042d030102c0d0009001c0d0044480003a03064950507800c3c2d941d6114040700300c45500e062500c07806a05407840c010f03a00c10009040b0a080c4040000e02104086444400c40d048601c1c014000c401e441030a000c56400054a01c086441c61000c074600318103c058120003520b01e001c007503403828402c03960388842d8540850000a43d244152002c1c0703110382e200e110701426030b103040c4641c00c0e16070442112105021418801818614001340c070101e035090b6503011541d03480758403c00c801c005800030350a00c601c115450040301d000d10161740c481780003201d0f15120282c80340612000c1d078619401d43e5000d110514030900c480450458000c000c0d004404050615001079881011141e00c00c1c841a255 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 642855755 1250 642854505 642854549
    0x150c0501060e07080a090309080a1505060904020a0306151203050a12020f0a030b060c030c0d110d12020a020109050115050405060d05030f0c0c040c0c0b1018180b0a06 73
    0x1001c1c0b044000b44d94036145616818004802019082415010041c01c4000440c54103030401113000030510941e04845080c0d00c1040040c21110048c07d06442540d800b0248401b607910160040f00340c94001c0c4002414070004840c04000c01010fa000e941e8000c0951b110310141a0000d014100140c40790b10382800d00940c00d500c3c04128490318003584100d100c18401c0c50b0b0200e1180c1d01c05000c070311001d4451480c10058409551464200002108a0350700003240d102c000d070360112040344000180401860f084009601c0540001144078520070265404110341358847d1017500101c500700c3d0044000c1040000311081c400c44220326001e4540958100740204007142401d03002c41d0201c9401a0185042951018502146510040d070015146c841d02c100c000ca00d90703403445013903007400b140d07110480004010700c1c05514041c4002d1280f000c09520010411120b48001141501614502400560350000d0b52102110f45007900d00076003c01d42031030400490800310b500c2002070f921990404840107034418a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 642857005 1250 642855755 642855779
    0xa0b090702031c060506072102030c060411010e10050a030c050c0303150a150e041107050616110f0705011e050904020306040902120d031b1e09150c050106 68
    0x52a00059004100d48003d15420108400640ca4110004544682d0300c500156098002c0c00c01500c90081503181040a01c1181003403082603103042c000703141001140c201031038940703100400c050154400307041c070500300303a1061204021b8094005c2c585040c141032144002c0841e0044090703000424500740041a4880c0510192403262094500841c950b54441345001d0240c00da07281d290340c2211050b00041034144c0a0443d0726081c1c00c850b640e81141043c100204410b5604101943c0c038000e50401051000c00c0e00859090b43c4608007a000101038220300c642210f007280740c50100c402c280a0f101503d082c00801244100480d80c0981e58914102d0781100510107602d038074064400031500800251007070b410150080c5501c280d0003400001c040c0000c1c0c012030301040e0303d1403a078021500000301c1c0420145d01881088484040c0c07100c050394418004101810041d0406900c010503100d41441c0004680325803124005440000d42007481e00358401d41c007500021080c14115010350030800c01080c59803040b2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 642858255 1250 642857005 642857011
    0x15060a030b16050702030703050a0c050904020607060c2f0708010501151b020a080303180705030a0201210903020304030510020f030601051c060f080f01050103080912010b180a0b09 79
    0x1c00000c2007a1101034201c4603400e400c0104500748036082c00501e015a806202c0e139801580920082c0c04510b141c0d2502c0043d0200c035402c014881c24481c014000981c9844094544940e4005400100c0c01c0e41c01e0025640f1101d90808900c46413840c4400418400c01c40d43c3c4650030070000401c548841d03464100c460b00f610030901482c0602e1108a55080503284181241000d0200380180111303075182a03008101c0c00d0110341c110351560303071001041c032204400090549445d621014083c2041a041c400082e403203608980b8047c0c10082d502c003000c50300c880e001c000c515680380400c0007005078440c0e030318001e91240c10034402135846000c0c03d92058000002c078021101e4074489582035615550703c0c41c1c01940c05400164229000c0070598031746403208081c0e486844040e103105640885030500e011711040c9000038500b810f1440d1f0f410440100700042d4420161210440d049440c2d00729420010809401011000100f80c0e11102c69421310000302419201c00b4001c0358403250030301c58000c441e414446017500503 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 642859505 1250 642858255 642858263
    0x14030901022703330c03090d020c030d1818090314090f010c050109050f010618060b0d091a04030c0c05010813061e0204090b030606010c170306060c0f15060a03 70
    0x38204144040ca03c0f00c03070041c4d9480002d840b13001c80300701030103201800324002c079110380b00c40100206000085101308242002c20b501440207107461500000401c1c0c0b2010084c0891062005034841041d1003100703d0307440c50151503807542e01e00c01c1004c60b128010240c0a80300e02030700031502c83c5148410710180f00381129008507010f09240c40413006103004650301039141c0015203023550f0b02c9a00300700290084c031800c014004c94000115800b410700ba1f15440c00d043d200404074900345844401c001c0c50304160281e0301e0080c580c4400003078113891402c0074090070009a1041c007420036080e04220400d5041004140d805e4058145900c9075900c500c019164083c05803201050304000c41030810002d442d903004104881e200301c030007104030812205a44141e0b041900100344858481040c40101d040400185510400900e4050121802501c40d0703c0c000b612000c80d088120340c0000095500d444600c200d688030b000319802c032040050b820780d0890f10381d00c0c140e440e85038281e0807902180d22464510080c0c001d413904 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 642860755 1250 642859505 642859513
    0x3080619050904030c08270a060905040c090810020a0909060b1b01420f030609210503190b0f0402070c030b0f09010e012a14030901022703 61
    0x208001c00003a900b000740b04600b0030102c101c0010010320240c2c040c01628802c0466000c1d0084083e50410080c0d0ba007111450241c8034103c002c0020903405032202d02110001d85002900114040301180c0c45102d40e04a01c0039841040840002188181d00915a10301c4603620080f00c0c0b9151000141950743c18891005c000905100d000d40c1d01c2e200c00311500c45503441320000203000121300300700003102149950381c0c0621030907041c20700e400f01ca0000b00180d110082c0d50b86000f4150504c02070b08400456804040c107074994a4440b8002c021a45410120302d09414048804541d00c280008010f82e104456000c0007280c1a004e1686141d400d0045d0404c0d00390051450541c001c1c41010701009410980040d190700a8554000000c03d1420302d041d40600c40f600b012014600d000360103d400d542c40c0c002d0070012a85003400c9101c508021112003064120011465611740003860b6048800008503580050402e1001092007080c4130154002c1068410b07101d0b0303580d1512000352900c43d01c01c07034002c40c1d2501900 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 642862005 1250 642860755 642860759
    0x20a17010909120f0905030d050403021c050a030804140303010b030114042903010f110a1b0b18030c0609010209041410170718090b090f0d0e060f120403080619 70
    0x101031031913007080341018a05200f60301d9440001034580020540f0070004110700250502c150304140d203840004a0b64504011601c1e541036858039500d140040c8042c0400007145c0209041086211041c20600b1919049a85035612400002d200350b1080c4249034400c0e04400100900e0304260081c00c0d01c26001c40712540382b024a040d1584142848000c003c1e80c15561003042050300d003c41d218513000020f40c0300460f6102d0920b407801400e9900030445a460101c4808280800100340c402c881750322030035049a15040c51241151145075004005c0107001134040c4004100c600341d0158060085000119424840d5036240d190004010f40251810200d540c0420f5090100c88070a100404080b07035880c1c2241c10280c2d80b0541c481c200307000c080159010b2911456040c0501402c1d500307058102840c1c038080e020151820407259510602c4c22650400c2c0480101543d00381e945074016680d410904142d002e0f95140d00000d083e510383c02c11101200070139030b054045903807410002500400d81c641000c0340c000702c44c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 642863255 1250 642862005 642862007
    0x1e0206061e03070306020406110303010311041104094212030c05190203060c030f160918060e0c0f18040603150e010c1404030b0c0c01020a1701090912 66
    0x203021068035855081c45410100705500c041040e500194091040180c50380c2c20424002e00e40708583e440e92003160300074030040c000304000001d0380340040d004450009075441e56040800e4203006641c06110b10030701c0c05010381e1011f203400060200f18484c2c110038602040c80d440c004c00d001c003030080034640302e221181014440f0b0f04e2081040300440340a0b00b4600900b40c4596030b07042c601883e42001b0b890241c5d600860300210700b410040c00303400c0f401c2c0c01e82c40342c2585004284c980f40b1300790040940c18003141c0704100118150045c50844081c1ca100b4160f0460082c034510418003030050b41c494034050b825070000040b01101c00c40c094640703a2058136161450180100208028101e22000c40341e4081e586603000400580302c100c5481d40300e241144041550000d440c4a035085400a03504002030290101c9151a41c207001030031901541e0f8800a400400d0701c400070b002e011809098400c40e1550320014000354403503000f00a01036a24a0b91040400c641e890710a01c0040e039000c10340091a4003241e010811081e = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 642864505 1250 642863255 642863269
    0x2010c171003080a0504080d140d1d0609030c06011d06150904020a0e03060a0b280b160c0803090603010306051306141009140a021b0615011e020606 65
    0x88540c803541e403000e90300c0b034503041290b6100741034110128a0000d02001859824416105049403504140c041583ca00054080f10f1041c01549041035a0380c0d0328080d42040e00954015481003d03000700e44080c070704005080c1d52540020b03107400980c800c8100002d0a5040162210400700c2d40000c400c1060300c40c0c138248203160301071241880c9900c1091211080d80e40360792020f46030456095551041e11850282030509000c0003a040180d410700b406401c0e00306440e035101010760700007041541030000d0442c0a80e682035402c503800804000100141ca0000c40c075000502100d864015414080400c0c2e440f5031a603640c0c0726802040e50400d00500041000c5141c907440594801454420782d101a840da0346c401b0111103060b048401540e6203d0140301d050180078000348040c020050042004e040340400070651020010560301c821900014128142000e000c04419610300d401d00b100d0f03031030a09a4210b03a50f1001285483c0c00654560074811070a02030160702e411880268000c0c08681e01d801041c4522 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 642865755 1250 642864505 642864511
    0x506060415050c010c0e0405090d0c110303040906030602030f01120f03230c010504060b04020a0509040e0703080c0f060a111b1903050c06090c060a0e0a0e0114010f02010c17 76
    0x51180a010500401d03c080c00340a4915505030341e8482c1246000080004455010700300c180d00d98019070f4904040307900305c80d210480b9600070f59120502031942d00002d182d4030458000c8c091460034150b00204000d034a4003d075002d020500c0400c2030310fa0b00e07031607001c0c0c8007280c000014001d48000b00105020a0281c00409402d190201250380c1302c1e1111401e0000c03540c81491500c010b82e5407101000103010503445448800c250441d81940340c507092a070000c20a0044100061189035100006000070030100841c0300215031202006445100382c03850301d5200c804600d140141d50080400207040070a00c0e110b0641c050105005580c1442900c0254402ca01c00c820b0045050340b144940d002040c5080290500800744255240c69442c201c00c091942030100103031605079942d01200b000301c02d41d1340328803c0e070b18420018601020a141004009540301c595503002000c0c51034410000300b000d2100c40701c6988115021780340d4408052001c0c404a00700d48110103c10f0009202c0040856030030098980260 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 642867005 1250 642865755 642865757
    0x7020306010e1012351e090d0503070c09020304020109120204090822082e0b040c030e0c0a0b041401050f180108010602010e03030c03130c06030c0e040506060415 71
    0x404031303031910410016240c1042055030358408030403032081007078005002d9440c030b0803005120302500d03691034a442049002d204441d8a41c5107040c1304000c5030b900d0410030340d09101d80083c03503010903031110b04150b034032540425000d50f20601325000114403010301d4001c0702c0c09243c1c10b80d0b83c200d01c0707071401c010381c10000c0d40caa10407030781b1a44910f20310000c01c0a0358041c11100e111503c01441d059080c400e04500481207500501482c1c0001072904141c012210360301c10003031020a042d070950b10070782098800401610400543c8117207032032584291241d00d0b61104001d50241d1084074207104503241004219030342d034030a0100d402c40403c002d205808d0781c4003810b0024103040c14801e0805421000d200c10079080305441c1806082074000c51605584c4c003844c464010b00d0140000c000429a0903000c40e242d1000511020b07180b24000041001c2813441c1c8128890903800041e607480f055150b001c01805001507418020010301c000032183c14501d424803810b400b99800404a914040c5031004814501003980c0b0b0b020 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 642868255 1250 642867005 642867031
    0xc03010f05040b03150c0c07080a05120a2717011803140405060304080c010513050a060c17160815030307111503070309030f05031e0a0f0e0c040c020307020306010e 72
    0x40d41c1c040c05910a14050010301041c0c07910303070400154071f03407070300070158030603a5075900400000003c1240420a00740650143e00c003107596001c0e00e241034408200f050100c40312254001c0c1090007100410440300140c585001650041c18482080c0c1c07800e03201800f080b1441c06e443c91607400c0000f409003080064081507448041c0c2400d03921000102c0c00e0304100c0d816180400006001001403c003131140c7e44d800311514101078107850310b5441d40d40e0349440018008003205d96038815500b00c203000c0ca511036040c40104044400500d403101c101c5410800211000010840d2800455428583c091481840c0c41d0b01400541c1810b003140c0b01e00c00218048030340c01c0d40120202d1090001055140300031032048a46c1d4802050350f40041c58001c0c00b400c3d40c00a01000c028051040c171610a41c8042c0c0d100c240711201081e082c240d101c1c0782d543c8000b0081c00000b615110700d41141400310081c04104581e00003422a0704101e03010800308141d84074882d0305c0e0000c3d4540c11000050100603281c0d9242d0760820441c603000d0b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 642869505 1250 642868255 642868273
    0x1e130e0c040c080708091213090f051e04031b06020904060f060f0e04060b040f06080c070f03050901030e0d090f0803040f0e04080f0d0506040b03070b0d0207030c02030d090305060c03010f05040b03 86
    0x7c8501680034000000d0360b0441c00f18248032030a258040c803210390480360800c000c4c6141a8a029110f44030341707241c1c00000344555000c1018103114009116001c4001d4285103244d08251030030304000c0d0f201070642e5000701d04180c000900c80f00b21044410480d0310980340c45041c0350b02943c08454040032402c01681c0195a00c0011580301d00140107000a4030380000017001d030710300300b00c80a015010010a405084182084804001139a000c841c02600b0f42c1400c056895480410040c1d000e440c42c107811300800d21480420440130366203c201101241c1c42085164006501e07410055140e00c0f4501818002c002030321410024109100c2c03c40b540075000e07680e51400c5c8486a60100b0091740701d2000300450760340760001c7c009a850315204900744090100c005100c0d00b858028145134a000d03403145540c1c020750110300841498051241c2004e140d40c0142075031210a07050a001e425065207002c281c3c1d95104001c0091250790604084906071210100d400548925000c20070014022010440f07815000da03101c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 642870755 1250 642869505 642869533
    0x40f09080d02210403020a0515060a060c081210050f0427020a0e0103060c080601050c0a1e08030f040b060307030b0412030603141c0306141e130e0c040c08070809 71
    0xc0640940c3c886e6000d040014100d04040340380c45050604140f0106002040c00581d83e07507250707540125070481c2410b460007449030910b8141c0e80100114030b00d001c2c02c41410442d01e00075104c0d0300002d48070104c1c0e000000700104814001295200e001c1d14240c7e4210301242218201c1c80d030344500e4400e1008019120322a100c40661103e03080a900c22550662961190f0300c0c940e40014046900403070030300c1e040f414000e4040d1656079581c042000036000462207150040748044840011008903003084896550341040307506285540c80071603040e2903881184000c00e105140200720342e001c9940210781c00c0c0c903d4443d500d400c00e010780d5101d501001d2554504000000400070740c54401204503042c040c0410840c42e2070012480901501d418040514201050003442041c0390f41d40e0140c8030607288e0762080c820903103043c981c0c6820101600c0d0b004a10780b00c00780b501c6800d034111000c8038461000f07071892609820144010360300d00304004070200d480140081c10583c4603821807a03001140c6000c544440d040100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 642872005 1250 642870755 642870817
    0x917030c1002030a1406011205100b161205040302030d050319051303080f07140c070e0c1305190902070f12021615020622020915040f09080d02 63
    0x211480381c02008220403003559125600d80117078200d110320366910349140000c020400d50341031484166903d1001c500441013003800d5901810f00307164041e5480c010362088951141c0440c0d41120740000255070846240e1203541038400300c0c2c1c7d019005140e420201041130304e450300000c016580307020100c40605070701c1c60300e17000d0107005900320305950809440074140100000d40060175203509034100e40600215540c0074100320014a01c91441d5038940c407078010b0b4075061901a40c07002e000411000f0501100701c0143c2c004200403410050305692050341d41007800400a45466070103165400c0000070410049190014078100e803040401c0017904405a460712180380c4028100c6005034021001c0c84e20403c64681c044014100004489403d0300310400020f54862008050342e030748414180710b6a0342495082c5091802c181d004080203100e03d0886214911040401c410512940c24003d2003c0200c030b06201c2e03840b10f1904400c030b091500c02c00c0c55500003c1d521a600d54500381d46202a192418400c0306 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 642873255 1250 642872005 642872023
    0x120030901090813051f35040303050612150105040908070204110a02010b0a031e0201180b0a1d010f0305150d380a1d0d09031704060917030c 62
    0x14013113021107030800c014040c41c00041100100e0294800c000c154800d0b4206000000700c4880203030042c6100c501c4202d100004002d031081d00b80e5552a001031000301909500f202e4402c210039100c034a038072554403040302d030b4a1000980350821080300c2d01c01440b103410a600a002440e0096084c1450a0030700da003c01e0466201450512504401180a40000340d0a01a030b50401000301c074554800c03415911500708100051046445440c04d0714912011640200005145000c19922500180c0d40c0c1c0c403080d403942e81c40781c80e900000074910780507522009401030040741d82442c1070751055082c0c0d000c0d60042d80201070140441040e0050305416590360f80d07a062540400380c3c4160340c6c015404c40c03550048001d41c0a841c8440c40c0c50440300300c00c000ca8600580403a54024541e801c00300d840320605184c40101c0b215041c004001d0b00800f1020360f49560804000c0044a214400c08030160380c05041c002031500450085100180603017200b04a102e0ba0540280f8071524284190703407500d03d0001005181001c16 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 642874505 1250 642873255 642873277
    0x81803030c0a03020c041104090b0f0306130213060608060d08091c0c080105040b04200a1202090c090d0f020406090c122909090a080f0d0e01200309010908 68
    0x42e03040c4008050b8140520b1440803801d07501400741d00d42c95100c0000b0703400b030fa00504400319501c891000b00c0e99503144403000300e420003a042d135a9a0405d58000c00700004400002d0380200000c00d41003503892201d20450003112025a1208040d480f0802000420458848242c803421014010380c1c01559880d48807514010000400d100c8030030711451f043c007160320154030981c40ea91506080002003282e808180354059404008400c080c240b0b2119010500160351465411071a600000300f02d02c0c124214414078140215008844d95480203102030301c0d8440c1103003031b5400450074091500041e601c0007114010303a100400100b281607c440b014011580d801710040001582140300c11200340081c072641d4144400c3d0883d40c00e4241061004140c000c200c0701c4100d00a45026000401c4020107002c3c1502035688520080d958103407025026440f500312031400c07984c65181840d4294120014402c0070140c003a242241c4c00f03541e0307143c82c0f00145500000c0a100040d521070442c440002d4415005101d00d00748 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 642875755 1250 642874505 642874513
    0xc030102040f0e060406060f050310030609060b0112090222061a03060a0801020a020a0201050919091d010b0f0d03090e0103050304090b010c0b06090703020c0a060209040509030412081803030c 84
    0xe892a07a40c0d103c1000b03840e06016a107080010701840c2c5c0e110108250540007820100d641c0e44904030b040c504844d59520152540d45005100390810506402c080c10000c0309aa403700303403880c000d0200048541261000354001c0700c1c2c40d22020364541d2403214000c0c40d6112000041d06503621103421131001c202d054030800300100042088240d10700240381c007014006140007142081041e4030040c0d5a49207020000c2c0c1400008203000600c4d6460919180344c0c07030007640061515607503c83d002805090300f240c010100348101c901c1b041580c90f0500c21444240c40080000a5003800201488010044520160308010340f0000101e0040003c40482e0b00a41c85000215581d502d0404540115810501c1c082c0c1045a80d00c030f80e401059000000c03507007081003120300c0d180b01c2d140c41074240d009100e0900b15000074042d0f640b22205001c02540909000780b0241c0e030a1060f56038036081c0903142d124500130308140c601c038401c00360080340c0d446024003038945600300d410007042d09c2480081c0c45c64001080604039644 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 642877005 1250 642875755 642875759
    0xd020d05010e06090f060a1e0207030906140c060103060507020a0c03150c03020a120c02010b100908010b060918071407050609010b0108070c1103031605060106031a0109030201110c030102040f 84
    0x10b401c0143c994001e05a078042c0981d032400c04980c03501c500001d40111007d944401e071444010360f14001c0c0d80c1c2914089141150f5030ba00d2407902808243c0c0030300c104000b081880c90310714004c40c4413404032480703e8100009400d00f0703821540d42e030006007400f41c00c803001c51103007001c080b000540709030340c12019601540c0020700c0130b600101403106444610402e10105401480200348a9400c494040b0702408000800f154011051004a00500c422140e072a84103042e1030001180a40060001083e6500000240080744403034042c0103d52240c2c1742203a40040e0f400d59000c07441701070f02021a41200091030013000b083c200140344a516045001c0c1074440303800c85c07024005c0d450001d00c18032404000030b0905916a2800c0c95015181348072010f4094001c1c0440042c19131556070a10031210f64003c1880d80d07c100c0105400c14940c1ea0740c09005150110b171a00c441031030500a200c0c03e6030070015050355800c10700c078110b90044481812465101d2020311803000d480d0f0305e5550030f0003d030025003419455541d45c58 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 642878255 1250 642877005 642877031
    0x1811040f06121a0d1410020a03290904080f070510021908040804050d0302030906030c070302060108012009240a09051503041e060f020d0b0402270d020d0501 69
    0x803150888046050114003010b0010b8980900c1000056003100912a9140c2c1700c00a09080c0703d500c81c442c0c907886100142040704160143c1c4241025040c1131041c001d00030542004e0015503000380403c9901003062000076001131000c5005007040a0f000780000e08203d21507440c0351074403110182d074401068000c550103850302d031810704441d20300c211450040382506064450f204580b013035008182c090007a01201005050080003107820411002c0c1c031056691401031a040340c01c1e00701d102c0440050041200014200c501409000f190002e03146544080c04c0c0660300c20750059002001c0d054000040c062030030100c8258000031070b84c14400c0c2401954450621b440100214000d4121724859450180d04641b40031824045d80d510941c0b1032400d000d140c0725005c00d000006d00c00c0300020110390601130780b680c0c4002242c02810014000b01c100303016121001c0100026801184d0144a90a5919000c0c100c2101030741405441200c1c094290308841910b40c000c100d081c4484a01624160744945082c100c00f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 642879505 1250 642878255 642878261
    0x70f03030b09060a051302160b04020102010606050c03180a09090b010504050709031703040501200703120207200a23120a0f03082203020c15041811040f0612 69
    0x405402c848030a030724a0100c0005000c0603135030043d0b0f80a07503904c62125906c1503065048a448001d030303410844d480080da15040052075000c8800705d005508180c0c000480303030300900030385400003180c501a40c14041b2551000580c07442c0c5500385a409840c641000420316454421007410300e000c1c4240715050340c144010b010658401620354000c0041c900420070200714000150700042e403402c11030503030380d80b96810114003408540b4005400441c0b403003103000441180000405030705200b5159a54003450303da100800b2405807000c05002045401f00030503001c070701c2c1c1800949002000300286059621012080a40070001c000035a46840c0984803000b1460580d01800307004c0610030085c0700076001682d9800400240b18402000d020040b008582c0b46c1081c462101014134032910009880c42c1e180c10003d540f41561b900300c500030140c00c00401000303924402110140d40008111280349075100704805c3c010400459040c0d0810400c1c0310203e2940404112900240395a42e41c20b1714101d42e81c0841c01c12 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 642880755 1250 642879505 642879521
    0x1020d0c020706020a0b060604080d1d09060603040209071413030308010504052205030c0a030906030c0f2c040212071205010f06030c020102120f090c0306010f090207030c08070f0303 80
    0x7998402c180030840d040e80012400d4840740c2c811806d040c5500c075140840c805000b1500501410300840c1d584041c1194450b00ac0401400300c494540d0b00703d500300e014800c0984040d40c110b50480e10400001e00503003404d100b602d0f0070000d0b03480c1c4203202060005002500703421110072070f1520602e4045c02c200b0f2650198102d805801c0844041005082044100c28882c9000038640194240e0320301102c28001c1c01e1094443e0080700100352a40c2c240c2514004006d1030307541c028940842e241204a210203841402010301c20701c9103440b03800784120040b450340584481071503c001c40311f010b141070642c5a11a80043d040944a0244124079800e2544000e0500d8900c0030003642d11901e084010440070341d100b10500d044540a082c0042c2150015100b02d0180c40790407032001c4481c0c00382c4248112a00c030089500d10030344500d401e072041001058101506c41d9401e200b10301000c0c01c056800e000424440c0d0007002207a2003403c0800c206101c542d41c13080203800103d02650035078200558202815014010608 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 642882005 1250 642880755 642880757
    0x19020c040f1406120304080601090203010f0902090d080c070b28230703050409090b0103020102070b130e1003020d0b0105040510120308180a050106090e06012706090204060201020d0c 80
    0x160580c0540b1009602c500611452050804040e000081c0b803080c4100c034040c18803403050b9030056031144090307000380d07100317118102105003601c1c0b0004004c2418400c0d03a080c070100505138490036046886242c010303040b5007c5044240a106030004150300d05d00c1c0104803568040040b0b1500d5000001841d00d844403903001031040c4528040708820381d00c08800d0191034070005001c0c090311040982002c490710301858102c01c4005107420816001c0c0f00e14002550704a9200342e0850700c4117a100d490070584c41c0541c40c000c1841d490245428407120104042c0c2c40d502400703003d0b001d100c5940d0303900082c00c074201c40c001c01d45005940c48014007450800380501540219192020003400d880d1100750890412881c201404012018000c2201110340e880f165802c0000082100d61459290410038000e01d141d01c00c24030011310f096101d101c5044082415412210594000e50b4008804540407070b40030140c008461032582c4d910030101e015600c40c8007400203030200c0d0307000580341c0311a500300204903000720740180 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 642883255 1250 642882005 642882011
    0xe01020d1d0c1f2f010b03010e0c060904020c0111130602060115080c09011e050a03180b07080c09271b03071b080a050703121a010e0619020c040f 64
    0x15448000f60003009a42d040e686804000c0c00340700384401292000c41c0d50340740310181c0c2100100a4451054219a2113102c080340200800010781084941c0c41860b001001e400c0348061014001c10b24181d4050040a0000740010a1051549039994419841074000700710780030700d0260901c1110390400000340500540b0446551100d5202005414404010680c0100d01c000160701c8115910580c1e014051284041380742d54007041203400542181c00803820352000a04d0030311078400030107400409d04401c0c0d82014071038005840b0002c00301e44c40480100b0701401c4200030003071409280c80d000040c0061041510b030a104c40030742800123605028024114400300c4403100c08510440c400e040c1141c0c0c01880c0341c03c107006c6030042c100784600c001e0740c070070006407001c40c001c104801d03016002402001014800da0b103d4048003500d040076000c0300c2e44010784140c0381610035218607595003e810001a400001042c99041c19002e40c0359032a04100c006094005822111310310340d007414079000700303001e6041a00045c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 642884505 1250 642883255 642883279
    0x60b0f071401061211010c0b0a0e16050a03020d021c050a02011215090b0a0503030408030a02010e030a0f0c03030209031c201209010918020702190303050a030e01020d1d0c 75
    0x150003040106070703005d00102d089421030409a8002d64804461581c0480c070302d206440d000d0381c40001004415402c1c41203010340084114211a090104005c0da5001000004a541036409000c100c4004600032600000038601010b039a288180100f20814030603001003000900a1000500c5200320185070403055003400d0440c0c081403020404242506c400c0d140c0041c010084500260036080c0c1d03544200d4142c000043c3c0400c0654001c0000d000840458009004194294681c540d403442114001d800040c048810f00d2250b51140b514100c03c0d40c0a071a015041100400c0082d00305108021016540c44070420074028480c1c00c21680880c4140f0001c980b0200c0d607803c000aa01c400b03c5280c1799488480c0080c50300c91683c014076080002c0c0003180710b208045030150f81039400135070000000364400e101415610300506190305644d01500d905a03281414210701000660240204140c6440f01d0754007070100c0c044151807880b41120300e00c0d0390a281510350000000036400c1019241c14140100001849 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 642885755 1250 642884505 642884519
    0x31006030b06040b06210126060c030a060504020a0305072003040506160c0618050901031703070c150c1409031203070306030506040b07020f1c0c06060b0f07140106 72
    0x41542c0504140c4000c030701003052500080140c8624100041c0c056081000b0111649840c080c81d4107803001d900303540c050700014405e0103000b01d41d00a04080103034001c800082441c0003010145401100c1d4080101d0900d0f00c810008040e6044070b4110350019540740300700a46143d110721030454040840c800703005910b4980108a480e4032540c060701d8007a041c0021940181c40582d44100c8190f500800500c1c1000c1d25154002d00b03507c081100c0e5490410750351404255454080c01e414100d070751040408202d169550700a4129401c020424001d2001009681012030340000d1120343c0d0350710b1000005040d0203090009880b809049620042101c024402c403100d5480001c0c40c17030704480001400710b0f16aa50b1400481c09080150001041c5020f4031041c04200480d1003921402000c0075029141105030040700c065580311030740034803000880090314403d0314074000d40ca900790081c040d5201041c2140c903940c0c0c140c1c4581c0700d11a00103803604000358490500100218202031480b109000b40242450149 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 642887005 1250 642885755 642885773
    0x5060f160c02011b020f120105010e1f0e060d061a15180402090d0c060f08060306041101110a05012901050f0301050108060d020d2003010c09030b0912040b0903100603 73
    0x2902d00312200400072a2080d0740c0e0380c89801229600040502490350821f009840c0031b41001c2c030400504010f410042042001c400042814400d0380d042041c030190301d03240c04122202c5c006009990401d0081c6000741c04030303909028540c003040b20603e0b07140300c00500d01c0070b1014609200310301d6252440148294202c0003038030014048090030440c1c003d61100641d0b00020404c00b4103036401042c2c04c49420000070815041b0b10301d680000500c3d15031300c0103680d40006168039500201d40c010000f0030110001907166004000c904480c005000448030210360503600ca5086806405111100f980031441c100c0c2c40015102001288031020b2030301504100307100184080e180010300415040c080e101c40098030310703201d80f99103400080c0c000b0310340c0012802e18182842400c1a0300380d00740ca10020041c5a9010b410140520b200079401036803010001031447c0c0300c00740c2c2400d000c0e088992501680309441c91200100000c0d0001c0c000d01d501c420f660300015420141f4000d185400784c821181486420030116050381 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 642888255 1250 642887005 642887027
    0x10912110402130807030213050408162111100603120e01020a0609080306010909060b04090e0c03010c17011d07030b01110d0c0c0905220f05060f160c0201 68
    0x205615000c00305040000703000c1d024510f80520f40c00907074034000400c000c001441d001124000d0b1780d42141c10301c01d4a055400e03600200e0f000f82580408000b600300440070101c17076074050745c000c1b040401801461380781d9848031f545e1392440c03078002014415803c0c3e4603202401540403079103d0100c00c000c110320b1a5524182d40c090310b01c40405101210503041780c940d0090000d44401603001a040010011914042c06682c2056840324002403015101080b500c40c0d511644085c3d407418901c9600b0246041490006480c0c45000101c050003aa10070010302e0b1002d0103980194201e40e140d1100d03503c1840d0400e096440140d01841d1040a0414141c41440340180c480307400010501d408188404c140c07006070741620b01100c0c3d844051103100702d00141d41b9400810011124403075040d480b80103903581ea0003020384000b550440c401d0041c00103810803902c518411800c50754030a8144004075603284d01d13203c0c00c28008030307400a28018030504115139092050b01d01501412070b4200035100151035000241000c28030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 642889505 1250 642888255 642888263
    0x40e060f21030403080d1d070b0f0d0b0301020304050c031c0914061209060106020114010e0c0c0f0d0215070c0c0302060a03020c0a290f0a1d01020c0604020f010912 72
    0x98541540e00200c180300300c3c1c02a682180e40996505000e2145100034628820360342481e07407034007492488200c070114400048990100c040780c1011120070b00b0001960040542c500d60503a1600e40070103a85080c005188940d010b00003904040d101d813414541442120348003038885050300c4101924194100503d40203032041b4581e407403a00300d281400302e0034a1089400890034200c2c2d4004000300400c00186030ba050302c0050b0300034480d40e22200300d038000e0400217000e2280c0e00a24100050380071000325018100c4105840100c860848140c4841418402002484401030300301c4e1020b110f542d0503c82c5040d0700900c003844c2c440034081c29516104540c91280c00000e2043d0000282c0c489218469019074841c50320110644005820510389103901a12598031540400305e0050f0390785a90300d07403147c124801c0301c1d15125850103070b03142c007198802407404503d03c0c0f40100340c0c800584c2040c0c000348054800541d4540040c00d85080c540100800b408a483c2c4045c108040000203200341c4056000d41a101c0780c0c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 642890755 1250 642889505 642889549
    0x8033414130902090d02130b0a080109031d03120d06031a0121060e0d050903011103010501050714030d02070303140603071404021305120604030806010914090603070515040e060f 78
    0x1c4e460000342440c010820282d8000602e442d61064800d2982c0020990300045803900c0c500e551710084a0300b42d0b94000341c00b5001c0303190010035411041800804010f0706800a09030303101803406580600d041e070000d500121501d0b0f9210028400c2082071400c101c407107042400c00c5542907140420381040b00f588008000441c82c8180300030010090542c01000b10880c0c120265a450598450000c1c8a900100d006521039030a080d80120903d4000701146c0c181c2c1c074180d64403071500c0090307101e510720030320741d0f030303400c03502d900c010000c03a92404014400340007114400c0d42c0208194102041201c1c645030054500e621035004550200540d103101101c004100409031009030b169920b8600c1c9101a8000d58080c3da0010001088110042c20200b8601d00c200c0c401d8442c0607072511030400444402c4400d0080e095000748402c10701095207000440390364001402002c03688032903142c0000c00d420095100441c2c1224101142c18000307090300a01c4179034844270a50314a402040d44800140307503a803100300c5019600036 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 642892005 1250 642890755 642890767
    0xd08070605070f18051315050a0b0c01050c04050d170403150912080106050d0e100c0810090501060807140912011d0606090c0304080706020c150f1308033414130902 72
    0x7c0711a80c602c01030500074941d00038507564031180178044e80400d0701440c0325403034075001440558000d419034064070000340a0003c800c1e07c0e680c40c00c0c1408140302c1c01c1200c40303005003c00400102c20281d840d080400200000c54a90410301c0c1203100e401c0e08184030703018401184014050f5580c40740547e103c07c148110041803015090050509161040c07058a1040e0704045d07800c0c1c100354001e056a03000d0501340c0c1d03407250081c0d56140305404448080c01004000703a80540807402c9544500e504c0f2f0852a003503c9260301d001d5001b4005031702801140c45c0010540d46414030341d001c012160741400090344180d07018080354034200d0700003144030743c0042c01c407180c03840c020001c10280300d40c91040c0c503880c50340701d041190b881643c0003001e0342d260100c1c3e0040354810200700002d04045020000240501400130050403018403940d40c0c100e407500020b24031588120750240028100d03541ca015080488245001403c459007003050003000c0d41c60101e101d002500d004c01007005804909a20101121454200181c50350 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 642893255 1250 642892005 642892031
    0x92115130b1522020421030203040509060406080a1a180606130b060f040806070f0c0b070e0a0303030204081204050a030818090c030601020606100507020d08070605070f180513 77
    0x10149070110510f5080340b89007201e802c1036801030007954481c40102e4032408080130540c2103076006000c0200180c100340004c20180c201240426082200140080744294481603420318003440d6103002c2d2611082c2c00c034001c511400e2a1201604525181114114910307140080c40e590100a8955805460040d0010964003940e42c000c1c090b03260014042c035514600c0300001916504507004000c2c031030250700c0109101c18041c9000c5088a00c8070342756000c0b413200d6900c40001030310700142a003080c02910540c0c91251388d108030420340958070907140182c580d820100307414501044040c0c4098155400c0106000030358808e010807080300c0d806135440ea5a42c2d420400d07903007216203302c5841d030450301035400d0240641c07005014500c40e000c2a421242c3c0e5540340c404000c80003e52100c1c140101d0410000c22015040201004120f00c2c0144040751601c4116520702d41182e1080354071400007416803080c244090b5104a00019402d01b110060140a00781000280071001c4207000c04001c0f980c92040c50509 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 642894505 1250 642893255 642893269
    0x80d3c0b010509180c0c03030906150402070f110310051e150120010b0409080406110a020906040e03070b040602040305060903090a14130c03020901200604030302092115130b15 77
    0x890340a030a40b88c40c0d00748030300042c2e903072241960a0b040010781c191010501d410203209443c0c220ba0000010514000c580e16a003516140d840c00c1c19425010304610192603402a0081501400341d8001c08c00c40c0b6500c1c3c1c2c1c242e40405c50040c04140742c40800381e007600760070703a4403800402c1500c1180031044000340300490502d004000160000e81c01c1420700488030240101c00c0040c20484441340c46420095807010003003070312000c1d5808029440310017a00841c449003001c1c0d001090b00c155080c00c61b494400981c58080800404480c121000c6800180510420000344203403034105840400071030030240b13034500241201109004441c440c0020178007040d0a542d0321604500d600540e15001c000002200300000d0203940040c2105012400702054202c1c040e0007082c019007146591409414651a01d41d01100a980032545241d0b0112040e0000300755400ca002c3e60320f0810000c03800a1a0b100900040da10801800400300341000c6682e0102a0104d400c512905600804400e0714945200d1891300044031 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 642895755 1250 642894505 642894517
    0x1c02040209010936051611030408150402041d031602180f04030318172d0a140a0e090403050d140901060f03080d3c0b010509180c 57
    0xd0603040401c0c59582c024200101a02c1d1032040100388140e0300072420380040d51019112040c441c14a90396803892207204030b04a000d0b895440e425a458240c1e2b4103040c0c0e1070868040184031070089400280411840c143c400c849400d1000302080c1010208422450307182d02030ba4219000b1400303490b80320011950764000106003070b41c5106060b032440c00c1030140c1e001040c004441c220042440c04114081c3c400384100c00c03201c0103038001d42c551980c01d14144036884c203400c00498100002103006404d5909402000204c103043c01a000b0f09850b0a0b030351000512008101c050542111000c000071103116074001e000041c3c4031030130f56500140c2c4d01d4910b011a154460050429881c0d4607011625a450001200742d60007011140d000b80705464851000300105c850506c4010306084040103007000d2501c0581000c05000103403401c59807505a200e907114504820041c00c200806c1b2090030061080030701e40300e1034241d4071080c41c01504114402004c0356030205482449103000b192346000407050519003049941c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 642897005 1250 642895755 642895769
    0x206090a0611041706090d0201060513020d0f020406020f160b0f16080307030b0117010b072d030302030412140a030216050307120807020109080910030e0d0e0f1c020402090109 77
    0x400c07605810351071526103205440565660080c0000c1f0b40302e152050223058242c0d040146400750210410154070000e610200030b040250b500c480030342c1a0b0380c155102030f00080c401034000e4001015400d802602700130450302c4005009010003018030820480600769100c0800c02d920040c0d5034110a5140c91384040e1012005202c0c06001040190310f07980f641007000e000701e00783c940c2c6032808003024070f1940301142406034103e401400e005000114120b00001c034101907180c0b107828034000303020100381c02c08200c1110a4001c00c5c0c0000602c0304010f00340c05a00c03018003a80c6040504c0d1030056650300210301c03d620202e4100341d00810420300b0a078141504d100f0307941d0b00a0880355610074515062140f98204209200403401c248002200035006014082030305a2202e98130b89440c0705581000082c01c1c148030f01c001055694000b00311b07403c40402c80c20903520903070349520f10700140308003c00914807016182c02d4040c4401402c22500c040c000d0004186d01981200d02688506640700100d9a0004030344c0700e91 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 642898255 1250 642897005 642897029
    0x50d0f1718060913050402271503030306030a0b0912031609050105070c050904140d02010615020d020a0b0c16060203011a12040311100f1b0206090a061104 68
    0x100c00d200500024012009140100409448001c0c20440280104900581c1140f80603045020704900741d0b100690041c03005084080711600c4c08151402070004950f85144800c030f24040c0b1154440000c4280da504034224010351a5182000100c1e850384594400204009800800b05032010824011940720f0340412a525449203001a5501100042c402e1071602185140c0d4006c01e00f54030400444442c1034102c0c18191046140000380480498000e000361000c0080303681401c268042404901c0905925500106000c1d050042e41110b04492007011410756004c00705203400d0a03000b00c0c903100c11a41003c00e11116598050b45030210f4801c1c1d1b1801840b000c8506100e0003044080e134007139410b81381548543c0c02c0c00c0d084404001c03480e00c54202d1603201c41c4900000100024072428040e441090244195620038403400c50681c2502c0e4580d03403980e00a41c4840e100307481c03000148041c180c07283c8148008c2c055030409451407516819040b8001d0401e5454080b4240d009103014112001080001210 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 642899505 1250 642898255 642898283
    0x10f0c2102010209040b0f15130b0d0e12090109061b020d1b0608012103030b12010617011b05180a2c061c05190305040e1807050d0f 58
    0x1e00130740c03080341c5043c030036444c00c21050401e050040205400d1800030b404611350654003408024981c00c50a86480d0640c0145400710700b03440d03008080c112152103001c02143c04045505d4060800f001503c034404050402d000400f00c5a0b881010601200d1450804001d01140252101c03038050a03c4c102030b4014889111540030049810300c0000204583d4404c841503a486440440d05c1070800e102d0b4000c1e401c0310a88200c4c0c5030f0912070700303401c600e4840e0400042e10034440340495200d42091040301d041d0b940d908801c1020885800596036192011402040582e140c00f04141d41007410441d000c00708400403500d03a4101055141108203003000808015030341e551414001c5440240707a4240e02003950480f07981d24403c41b21403140340101030040026404001086400701c216080c0e034400d8800c1d11039140f21181ca980007042c81c1034198001e5450b1640d9900b400701d441d084204c00362880042c3d00c0c8500c5010340d01080421100241c0e03901308c44407144040c0074200054040c4442d40040c04030040d40e000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 642900755 1250 642899505 642899507
    0x2030703030206070813170c1509010605030d030509300f090a06030e07030b13060207080301030201080f0f060603070903061a130603020306010b28050903100b010f0c21 74
    0x30580c8a01e03425170b18141143c2e82d100314545611080d410043ca042e0728848105511403110025155407400c88049941c1d544000c0341100308804103841c9021315955608041c8030070b003030034050800d2400c040d050510143c10f114460070f54840c8480100340f0486e10014004040c2c40c2c041c81100500d1140c03217802900c840c2003544a43c5260700464a0611500c81c1100c0010700034064020300c0c07051440e44020305021807441c0c0b251141084001c1049807914484e1943c174001901030320140034014095002c460b02e039811480090034225000e0010060a640403080125610441010326032003042560207a8603500c4004050701d03a680d882c2c10082c01203003441504800000302e8040840b01c0340046405000e4084011091411036a1500020f0b4143d0480801400703140b140c0c2d0010000c1360303000b0f4100305140394416000c4075044682420380c0c001445c00070740b0840354641003041c000c0380c43e00c0e03400400800400f10f0000e40420341045c240414448145d003208142f0184808141141a202039405002c0007a008 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 642902005 1250 642900755 642900763
    0xa050d0206011d090d0f02010e03070f0c0f080604030e060f0d0c0215160e0d02100c0b01050402250516060c05120c0d120b0a030312050a0b012703020307030302 70
    0x42c1400104031540c1c80381c1907a900d40070f40fa000f0200c480c080c010514800d003040703540b14000e03428407055640300c6020340801c120801c010482c42d8086e20080398400e02d40d186c801c2d03250340a5440b02207080c80e50b10b810720180c000419401d81160307050920070101150b41d03001c1801801030241c00900c5a4001c982074580000e00c0d003050b80e0005c0b041c5d0998080854840717020407a46030603117107607010700f01d202c00c045c0e642405802c001c403544000a288a10032099580003800320a1200c0c0c2e0540003940510001c01001018040c0314054201240d09608013800084041c103528423203014006d5102a040004003817002c240304c104070440c02c4250350205241c40e40d20151005042000488052040004281410410200384e50b6080c400a010349000f900c1c0c0315080341c2040c1413034440b20b5925903400000e04550b0300c4115941c01580b1035244d40b480044c040c0d81d04811504010036140c005820441e4009191ba44015103500d05041e03003045583c4001c1c0c01142e80302105440e00300170b402d0b2040010110906070002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 642903255 1250 642902005 642902009
    0x120f030b1e03010507110705011b06020d0b0a08010e101107061109030c06041d0717010e060a0503060601230c1b0a06110303010501050715051e060103090f060504050a050d020601 78
    0x900240400c5d00c80c01c02c215070202e0004184442030704641e10520240d0310030203c0e20507405800340d443c140140c65455800c00c0345d124038000b00c900b40e0303a600078807602c1c2000700051008003100b9008110010841e40c1940e122008440c0304002c1079500d100c04a07a51071600107540400d600614100010006441c00c14642d60000c07050510921a1030301780c000f14030340081140c05580300b407000001c900f6044803140d10400c0006e003640051115403408513012181500c1c0da18001d00c142428006d15040c01018448501510b03000b50703000750840da0410080382d8010b40f0218103000c17941e10444c085041408030580e1405400541f401c2c03030155001001c051030444007109a6550101d505025603691284161031078034140c0c0d004040c03904113100401040d0b0040c0b018103456402044080c801044000c03081048603000c0f0340c050580401550100302d02c203110500958051420700702006203e165440d106d01505540074014610380d04d40f40020700f00031041c80701c0c41e1104d0b80102122a500364040000e5110342c024 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 642904505 1250 642903255 642903259
    0x3080402041a0f100e10020105251d010530090c0a0306022a030316050423060d092904081204020d12030614040504120f030b1e 56
    0x701441d058404030355400795003100d40c01090401e075510070801307000c244060010b00106010307121501d41e40f16190900b2815505426030300000311464840100007108903101c48000c0052406845003000e82e410410224404171403810f401e0741e090320030004031118800e48040780f0142c8140f400c000e09101c402c0c6481100d20380521180790040d510341e41020b075076840f030b915203681c0303c40010020000302d482907004191050310b00e00079842500c20000140490311041019400503031000040058181c10094545051003080c989585411318090b418809103031044c0c400414072009600080c21b5940b48400c88030550700001c1c0612250000d404d0180d011000f1008524640c0c0a00000105844d42ca82e0344a105680c050704003030800c0400701d981000b211004104a800029282122002c24421102c5804400150341c010071a241421200c5844110b000e01403401036003040305100004041d0762090340840054030f040c5800c0409000c045019106e014256500842500c1d0003040350850110007242a10003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 642905755 1250 642904505 642904511
    0xf010512210a09120b01052e0c02030607030506091501090f06030e0f070b03190e060103110a05190509070207090204180c0e0d1104020903030d090606150c150f090308040204 76
    0x13482803a41181501d00600404075020700d00140f100e0718006000424117200b03104080d00d03d01003120756108609081d4801e0300400c03540c15010b0118a01040b00c594490002e01d01030243e810300c0008911f052002406403a4122032210b20141036911860051005011042070710120310f5807288060001e01e2200e4910380701d0f01172600946581c41c2c0004018040f1160381420b40e20b50795680f41c1c0d0000105078445502480344d03c400e030b540c0700c401040182d22702941c081c01d86803821a00c806c0c10403c2d16422640194012802c462003551008000240c4404503141a42c030400c5565070380368221b080115641003258881e01c042400324214002240e09040300c040780d8000c00460090480940791700c0c20001e034043d400b200581582c0d0003c0e02c41e440e200c2c112640030380050704000d070308000281136411403284d004005a4843c0c1c848140a06401080010b100b420080122100800402400d10820030340213840036a180002c04250756441d0320812a054070741c0e00c2082035607110f00e0000d04034541640c0a07449682 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 642907005 1250 642905755 642905759
    0x303081302031905060f090304060315080616090f0602150a090507030318060305060f0f010905100e0f040203010b0313050a02060a171b070f0f0204051603050703050f010512210a09 79
    0x10191b4195070241030490021824507103088402c82c00b92240c0c0140030940f08807480001074030241003001c10b000d40a0b0100c500011034840d00000d00c0c0c81509d40c01410540361180b42040006e13004103c1003c001210f41544071507035942408c02e00900b040c02030003491032045030400010305a0000c0d5100707000888008510f1941d40d00c203c04c5080d14030507100558001d03410b044c00c07581c1c1d18006940084412041c144051180d036100c000902c0c81307034940081c0c004241c50310040c95151500018210142000300e0b021410765040c00c034040d8160100921840540c1005070100c410311004100c4043c4155000b0600d6981c0c2d45c040c28000c000720904070490a4500c4000003207034171140b030441500d0401000785100c5040c03282907202c804484041031020381d41400c41e450883c0260300c5500275644035004400c220703407201d000c140005040360b000414400400d45414140b04c00305e60f1001d80d0700e0450350b08a540d203c015140a460f1810503d02140400c041c0684512140646042801130441c504907500e0f1842025 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 642908255 1250 642907005 642907021
    0x80a08070302011a150a02100501080c010912030e060315130f0e01060e060d0c092d06030b0a02070206090d0c21020a1a0c1510140a030308130203190506 67
    0x1480310004d50340030345d03040148140b20088202810030f560003441110314246180d03014604a8400fa0070081c0e0b141c1041c0048005542c200c0780d40c1c4010304003e40b130310000039200e4400030014110250303210320036000000410000c080100c02c00d106440000c1060404410880e4000000c4c135500340c1600099040480b49962404e041c03041c4c2c0222400926100400d5a03401704001c0002c811200454911b00c01c1c450120325400244a040808000c21100c410340e8502420900c0d014556400a03040c1e0398105042800040c0d1000c00d05900240c2000c0f0258a17505a0300c0012010b0003800742c4180c005c011000c42c94244491115044200c03484d251003450322a480c1315020940c04080f6030044d42200d0603441c20000200150b103845000d10000030b0b51350908140e41318603801c0003800e024914520001000707006405021107188801031110301c44035840712944402207100c0604c1840701030184118400014200702c0480281414168014113039440680c456400c0c00c1e13240081501070f1151710030a80014410 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 642909505 1250 642908255 642908291
    0x1302040e0a0510020a03021e0310081209010e0409080a0309140703111903021c12030513030c020303040f03140606030d02031e0412080a020111090a0302060310080a0807030201 77
    0x1898110010b0f0840c9544101d0303080c069032051100c0020168200007800c845901c014010704820f0088882d5566414000c1d146940c0394441e402085c515001007003110640d0f09260202d8076082c80a080c600e042d5442d900002e8004c2034075080240400c140021711242c6180d0680c0980d42c0c492091140b1024594001c0d0f12907034403821400300420341d440b00d8428070700d6454080152400c00d0703001d03104000520388a6001c9240d0320120006a030000130300500c203c0070840355602c00c8110045500c2d041000385802802d15080e4003c0c0500541841849940f80042d5202071044802401400880100b0541e0b2854070349400c5402e06000c0841c0c0c0550404100c0720314000c80c81801001103540294200400080780c1e680300b900000d020360040108000002e010380400407407100541c000e074441922851518030284c21740b81911a080c0001c0c104000b44012561010004410349405031001a1a5510946d400740140b12079001a52a885900c01c4442005000c000424409100740e001340000286407400d219a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 642910755 1250 642909505 642909523
    0x60114030c2d0d050c191d040b010f0f170108030901090b0307092120041a010815060705010e061b03090312070203120711070602070812030606121302040e 68
    0x20b4190400c80185040503035080700b0307001703013106406a1900c0c40783c40b0741081d10608660701e140030628004583c2000080119a0360000c0700c152018811030140b0740c0000e14042e00031802d6820700000010b001d18451144201c0c0852062034000e1010550312485983e076607400400076540000d17001d40000c039a0701045401d42c0d02503a41910b44907001030800921001751100104508c02c40040d6042c1a0302060104418010340d500f440300001154600005200644070340b99400c148181c6111406ea600781d038082c0311580d01002c017404038a460801039001401c14810030101034015170811041c5150b8803004180b0600a81d01c0981400d0360028a50440440d408202c41281041c2c009000540307070740c91084039059000c051841501d1405105018800241c9030aa600c80c002581d801c00341c1030211003c000301e41c060704060008007000b0346420400342d50740280c900040c03103040c07010010881d15207070f0809640070002102402040e0b0300c4c1c4209403c46000301c11a060b40b0803418040506841d00b804140940 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 642912005 1250 642910755 642910837
    0x130b09030f011a040209060c0a060f0506060a1d0312130f05030d052b02070501060f05062a0f1506090601170f0c0418020d1d070e060114030c 62
    0xf1914140b0700c1000000c3d04150b046a0f0800401c2090100c030900c188900d1004501c0380b900090001c032003031003603421070303400400e014000c0000700303c0000d40e1900100b60458203030710108148101c550301c0021130b0500304028400100140042902414244200104015142c0c8103406413000c07541d40c8101541d5441e0002488081003041005444000301400c45443d400d030100398110001c08000350840891b40480c0e010755460355512018840c0c40ca10484070401414101c2d4981d0815002c003401078000e861200280e0a9800080010590200140b0040301c40c1e040d04801d4401600702c0030300c0210100c8080303c076541318100d5140015000d45c01050403942070aa5103000da480341d900c0c418134100c8124041c0011059490610002420300f50754146803251180040f0b0258841d80d02c04480c1c02540c401c44071020040315a80c0303010b0f52084002036503504980e106504985e01d03440f120010303a000c0f400c1c0b42c0e030301028500020801440f14a0b201c01024000c460301040115151120243c403e1f40c03040710090a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 642913255 1250 642912005 642912041
    0x1b0d0813050312040f060f0605151e03090715020d0c0308100503031309110301080d05030a0b030102310810270c030201091d070507050102130b09030f01 67
    0x1285850025900d040c26407088085924107001980c3c0c07581e2210007101c040b00c828120018032810441c0da40074801104140a209022540c1001c001403800c1140740071f0341481c510041000040030400d03000319041d6800302003141ea074900300703012007035100e0a5034010755035100550b8075641c40e6107100280059650b00300d56900f0b510341a5594003150315a002610704042c00c10516000710361039505000a00480d2114030100503e00c0c40c241100d01611000c45003013080305000d000412446801042504015007907250503580d0381d0301d561007440241112a4281c6d0158404950a604003030a8400207140d035408540d000f641c3c411800801440e8101f1740a60000740d0456455035090128a42108a10f1441e07c0d0350441d034444c03400340300c00c09003040500550304035000348010425560044050005031641540d00d00101d0751071603a004000c10007070f1401d01000030019190090110a41c1521000c8515280111109503203032020300c0e441d0031040700c00f840307401034000c241c030088014440c11401c00c1110040c0d07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 642914505 1250 642913255 642913261
    0x3131205120f0d020a210507020c0a080a0803040f0804090b0418112b0c0e1f030f0609020d140c060702150702060c0d0801030c050f01120f021b031b0d08 67
    0x51019401150310340c824400b00242c246c0b0102d12050901620b0060060000750510700a800203240c00f281100d20f50096041c0c041c248140207000c190a8402c42e08410120780d039403140d1500d0240042006000b42c21802c0226012503481c1281c0c002c5800d207101282d05000060f84001460b044031054400100155201510320305281822134130a2030519420000700b41d100d00041020308440740320402250304122501c1c007403103d20508405180c2101d65020243c010702154100b00181800f40c1c00051f0101521890075410061a0b81265a0159000c1d104d030b18602010b15043c84032405451094145000342000601c0ba41000016112200d13001440900c0360845d50844808640c4000c0d03003660410b00400c0040c15030030040012904201156940075030b150701d1810010100c28194001901c01c107c02440841240c1e80f2020008032180e5200001540c100418900c2009128084440c03500d844804000c80f100007021010b4200c2e0002c0e8001c03160030f8040440a551503500e0301180c00013054409004c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 642915755 1250 642914505 642914527
    0x6090606140a021c020d3e120a0c060e301c092d030c02030c1008040b0c0a0e04051005030d0207031a09030313030c06050c0715060e0a0e03131205120f 66
    0x40300380250340d02415510307510390404c248c6140d40d000600e0140402c81109c8090100310580c815400e1240b900c401034001c4155000498084c0015240804140c20342806442c8a48684c4030498108141c030030080c45900250302d000c83c2c043c0841041c140c8950700002070503038215080702035041010022211a02c00d40d40b1968080c0c0c1c0c00d981c9200140e0b01485100b051070a991a480c40009142c2226150252589814035040440d510010300c50b1600400030b101c5030038026000f488050101d00c5c1198080b80070740d03030326502c1131298071103030b00265061044000d08410b56130081524000d480c0100c401c50101d0147c1c0611022032041030b00c5c03183c010b50007000040c103840c00004011a1080c03081c500031861080b291507050641d0019200382c0d03071110340060740c00c04004030000c6050311800b907581c040c0405440c041c04451801001002c0c06020f40e214005a0b00d158824012900b4400700703e203041b1287c0f0b0710388804170f8402c0b107401800c485030300c42c000d41c800600d0000b00540e85450003442d280c80c9040c1d103600e0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 642917005 1250 642915755 642915857
    0x81504150f020906182d270a022203020f0d0201050408010204080d3e0a08030a020a020d0912020f041404051006090606140a021c020d 59
    0x401015255090005034029564071009041004100754403001c15039400c0c0c20092150304100381160800320242c04850106ea03101810301400c030b002c1341d0011804c04010002e44107051351910000c840c0d2071104c200032502c240d550280402c10b610300900390002d4182e5910007401004ca00001c0e46c0000707000745803041c0717141800b5044101403042c9849070070725986001d072a0036604250800401e036009491001c1800c0c0e844035071058081c180110580780e91041000020032155265100c0c42854000c0c031046440074010402c002010754020390455403480d009400c04002c0d00300c4c40c40303500180912020301e030701035110f40b500e01d09540030034072140003c031010303820806400c00c00f100c0303e90066100c00403401050032100c1218466030080014101c4400342460f924100c504c180c0101e0001898080b0501c039095101141110405801852070344d41c1054800907481c00045201139020401c640c201c0da0001680400c0f01f40c01d190240d00c842048103024158280c0c2e050340070000b42c0604441d40d00e81c03038035428000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 642918255 1250 642917005 642917021
    0x605060406030f050109120c02060d0b1210150501020105090616140d020d050c04140f030f010615031512021c02060a0c050712110618060a080108150415 67
    0xa1002401654039a66000703400d5005406403005c4c1d6540d1440d105000d0010802a00c01c1014606800f003050b00742d0004801d0b004a0f900c0c0260745a6808080c0d205465103583c2001800c1130f64201d0b02d0403001c540440001c0c0000000008039510b00041c0021654014014a402501c07980040d004564591401c80034441101b00300e00c04018508482401d1072615200500d0700c940980070242c1d4440000010109440c0d01900010030040c1c1007108001c40302c1500240c0c489c009085400c09070141941c00081e02c1c191800d0607551085d440c000d40000c07c5480b1803111244000240c9090082c820301c14500c1c074102815114071108580103800860040c5001c0b880e16142d02e400400008004c400c03600441c0d15504166001c201050010107000c092150411020000780321288101810303016554907520048615015107000c0d00002c103690007410301c42d040d071040100b0003800b020740b0748008030401403144900384207040300d5015000c1d40c0340007100181481e500c40c54000904071a0740c4c1d0200c0c2618000c0c401c0e6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 642919505 1250 642918255 642918259
    0xf041208040f061119020901090207080f130302031b0a0e0c1c0203010f0803070210050318060c0d0b0301090b0610090f0815010608010f140f040509070e06010504060903060506 77
    0x4010100300b24504061041c00703410507650b404103002402685a00d0100c40e20304941e00301011021610060740d440c1c0c20340f415914102c10261302c0d208240780083c124091400703d840031080c0490f1400c56842000592802c40c0d008a0803a165504003111283c82240a80303c41900814804818000c007010b94a425030001c0b8444009480e1180104000400c0d124943d40450746640010040015030011000034020b000e203840650301c5c02165900240d034110604820300c0074410040005680d84801c0c416141c105150101680d04600c0c22000d40a002c1c0e004030b60145001d0710b8a00040c03075505051140b964402e61141115403d92140c0041084404100318000100f284c03d8101080b0300c180340100c070000340a060010152032900c00c48010007030340c05800c0a0f040040280040000d01102094502110075161501800d1035405010a00103591140b2080d041803c00d42031013504500050113400301d403044441140a915160300444881c40356106100000704040710900102e2025408540c00c9400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 642920755 1250 642919505 642919507
    0x141e0601120c030e070b04060203030a11090316031b15110717030d1a030304030f02011e05031801050105010203071b120b0f010e040c09020c16090218060f041208 71
    0x1441901100750b62501e001c0000290b26405000400c2004011040141c503c4100b02ca080500b045402962030100601c4040b0140e243c1c000707860b9142c0f080040f240b1542c00581a16604017038a411121031005038442298846011003000700e18640c0d42c41410f0a07145c0d0b4035081c0140d070092000c00c544107040030070303815000d020380000000c08000e01d5074884088040380010350b4807041c1044242c011203180c13241c40e00d01c02d0f11740d2101c41550b030703008012035055a9000d4258202000c03503000490b20004a200704819200d99000309980742500000514072484000f14004010711180d90180e01380c031028414640960f00a0dc9201c0004c0d441d1459007000007030000d61070304120f644811406d85682900802d65034100c800040c01000101a00e0f842d000d00008102a18242000d42e00e2441c2c0950300d08c03078100c3c2a42e001c584140b9a00040c40065002d188000c076102021341c8801c402c50080d4002c400010101004112400550410a007507802005210902504080c40d21f584080d80303e104d0403040b01c40d920 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 642922005 1250 642920755 642920777
    0xb07020d020f092406040303090b030c0f03251409060f0d0c0305070807090617150a090e160e010509090703061e050c09030a031107090603060e01141e0601 68
    0x59a0b10b0381c40c403e103080a80003120304c036071400f030281041c050b5240c50f00a01c000c00c01800800e80000441e400c9403518014a641e96444011100080c003a803401c4580204c000014031585101c04041500f40401000c00c50024603007500e01550310428240390241115014040700d07040d450640d018001d900885c2c9145450704100c180004101c43d900389004021a81c3ca070b050148059005100300e6000d501e50408804507418400058140340740e402d404c20300700540300300180484080d8404480c190501a242c501015220b07002c030700261000c4402203603140715211110440e0135110000300d0071103010344685989a400d0034140403810780010020521071080c00e034000001030300392203038900980210000c0d403503107400001120180d0780c0c082d01c806400201400a0401903501140c1004600d9050600201f0380c010f0103081800c150703181e4081c40c1001e00d000400000d00545402c000100c00410380204014220320008800012082c0d4207031100d1100040664210f000000642da0007440504011aa0803 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 642923255 1250 642922005 642922009
    0xa0b0c090112060b070654050d031a010e1c0209010e060a051002100b0f0d0f050708060103120c0201020a06060801152319030210051b070b07020d020f 66
    0x2554513400f200c0d0007140054548148019842900641d0b00070f06101400c820039101544041201c1400503111240000420b080000e0708004040400131703922090400e05410341480ca4681151b4190302c03021a003889800704081006809403551000161924042a060031041c0204c2c15181c8047c23b1b28181c03025241750150ba01c1423401e1f070007019000318480d040e16003001030105440c429408580218203c9524801082c2c022503040b000d1341b00c5e907030002202d801e80c07000a0101240c840090f60086407083c070303034000d0185092141040c14000c0c02251031065882d0b081c00d607925401d10000d003045800100302c04006100e42079030b41d040348c014811104140d0071070325501d088820325880760075103a40d00d590369014450f8400d0843d00425603452080d11040b9540c46005000c0c00e03072103207188900391307030805400d50401040303c800280d6005454240e103d0700e0b5038000f40c415444003880a942e0318100c0f0011441c58000560101070301c05644455091061940c00c0c000500340319801264002c00903c00c0d184aa = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 642924505 1250 642923255 642923261
    0x30f110c1e07030b0c0304051002130b090f0405151903080306010c03092103080604270c0902070614010b280e13020a0e0604050d030806130906090c080a0b0c090112 72
    0x5d2403072200d03810740c0c038181481d1880c0341c0141412001c8140d40103100e05520081c0a11080b0111001e01400a60722449070000130317811407c0d2007003107900c203103048188413040c107000440d20840d06003a161002d00d20100900c0400b40d150358030000341410780400000719254030850088011501c00e041c0f0244694541810516100000000219008410881d641810b0740009403940100c001e85c1d04100721441c0018480c08d1400c0d00c1c409003071000710464a101002201c4050600070310001c0d00854582000345400805002c1c13424000408071501e0001099403000e6008031200c94484900003d0101103411a1009640f13801c461003062060010894840703456403150200441035a010040c1c2e190a4441c0c094010749035100c0041c01200c00b404107010b00d8941709038141e109605030800c0b03c41655100006807030042da20307070100030075400d000015040000236041440c2540c801c8d01040d000d1074491607001c1d507817502d40c00003402c1a03e070180482e10840c1c08800a1011003410300d452075440a142c0300060507 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 642925755 1250 642924505 642924511
    0xa09060f12140a030203030412050315190306060e2d0609040609021801060207060306060215131a0103120f12050603030f130e06060c10050a09020d03030f110c1e07030b 74
    0x243c0c06c008200020481c03900b00d44140b40e11541016801c40c05d080320350f5034000b2000e520f894094250041c011030120380d200c054038025580031300144082c2d80c940c4e84810211006403500c0c01c041a01180b1081c07074484000070541c0c64020390803402080d0391588108420060054825145103a46017445009a02c802d807a42007100e45040b40301010f940342c00b400a141650710362051081514150043c0318459004c01d00c07902110780050442d085440e130005100c0500f50f80d4074001c2013544007200d2805400c8041d03584070304882c00f07040e802100d101522402d6401111240f2444d000907001e92048030a121a5403010390062400f6040700d0a050901c100700e0840e0f80701c00d030340ca500c0c0350710100204400d0015860b070341c1d400741c01585c0480c14020089412a980c80d034410f00f8440703090711080041d081104a9010311100d903001809622200a60709018000340314901d00e8580355802d09410880d120759602c1140c07501681c0304003c18196001191381d4040d06800807000d5a20b0240c3e25000011885a02d02280 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 642927005 1250 642925755 642925757
    0x80402062a1b0f040f020d0213030c0501032304030e1002100e370203120a0f03050c0d0f0e07060e0a0f1409060409050f06060a09060f12140a03 63
    0x1280d00c9038448245031580c08401101c1e0081e0601d014195510b03004480f034508402643d010420108241021001e4003c80e5520141e0754804600503000704400d4000c00304490103043c01e60b090548a00044054408900242d0f6905407902c0b000d00d41c40041740102603100c1e000385020b0380d0003400c00d0700003605404000d5611005034444100e0503c8441d01d8401c544070121800014041e451039955000c44809442c4000ca18419015a02c2d004400000590008071740d0b004050301d400362041100000309410500a9000280400e9411b011050107449840d0207565405042410010451503400191400601003d41103885800e1550500820040b034805044a0b4036500c91100328001800004140d81c0d22504034019501c404000c40c1c000c90604d03808800c000e44800185036030708004034029010b0150028039510960800d1900c102010500900900341103d190f401c15035108005400c1c1d03482070107640e20032124070804000010342c03062400704062041c440111040107d4081c0c03402c180011405078 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 642928255 1250 642927005 642927067
    0x7032a03050306130212152710170a02150706140618101a0c0a030e03011b08160e030316032006060d03090f090204080c0409030c0308040206 62
    0x2122030f14204c6641030388003d2040d03003107042603000484480c070210064082120500340340441441920303002108840c140301da1120542004810000c1110410110341418400c451440c02144062003030141408a50100c030051114407096001c001d40003c8000d080032445104001040000342c40c0d00030700c11801400070b0307414101d2820b1018464440eaa070400110740b01030710720401901e0a02d0304004006e403840300d220103003045003000715142644228084940300b131003101c8551007010703803202d000c0b00e04500c20350080c0310040300c0240d00c2034064444551200400c4607440040c1032a0001c0640c3e9100d001c0178034000030300c1c0c0e42203800300382107612061881d010342c00e000e070108040c1034020320a00315241009000039101200716500941301c03140603155078403030310b031a8600c02c09142c85400c54001400180030b03d4401b03c0c0c0c0d1402e070340009500910a40d1303214058803046045921382441807061003501905c3e40321001440d55011641da420040080340d00240500140303045140d846241404142940a48 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 642929505 1250 642928255 642928261
    0x3010501050d260d0e0318041e020304020402040306020d0504020103110a0504170a06110c0c09060604061209140a030813030e01080a18060504141f09020f0d08220b07032a030503 78
    0xd40503209551f0898091402c05070303003c0103c3c6408042c0751207000301c0400103031039480e80c0c400100684241d0348050020390003c2482440e0070400d0740f0a07402703580b007620100a480e100f801d0b0002c0c5806400a45000300781c06000421008031401c02900c080409082030f6a100c1025685110840d00d01040518a440d00440d9281210100300702e0005111001c48940c0d14074500000018a0340c072860003150100325003030794000740506c41a0000c0303109035844180c0a5a041720300c001140e031f4003080481940000c00c8030022406014680050413103040d055524074074882001030040d28040e0700640b00d240800c1e9100c000e070b080c4620b4004010000391007408049850308003401c0a00240b10b103682c541c81c4035007103000c100d40300d000340890b01010303041c000c81c02080c620241d00024051100214102c0c3c1c02c0544804c00700304100043d001480310000d000f400740b40e0304101a02008050145008902e5100c03810805400407a0140c6d40d007408556005c509400401d211070b458030100c039030282045010075804818 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 642930755 1250 642929505 642929527
    0xc06030a020c0d110304120f02090a0c120b06040501110f03070615090b030601090f1d010c02010e0d0906120e01020d06030201110d0905091b0406080603010501050d260d0e03 76
    0x1e40d41c038940d03041c507107000304208540c4e50540b20701c41c03403017900d030904820510038041004100d0340c6a01e1a80042106d04145011070020000c0d21180103000000390000040300000c90251107454040c107000740c99182098140f000540f03504030f000848100d24415450406960001000180038003840f554000c54070320109281e6000c64100354200f855264140407107001a610300047c1d01d81100c2d01c080700824052044004200209501e0960706002071a156183c810404150499621840710341e0003005203554046401c0d0721080b207041c0903000120007644c20000715204000300c03100c012055000096080310708881d0390032030f0b000001c070040361070f01c40d4030410666030004159440707001c450000c2c1040040c01c03040105000b0740c1c0d002e62803081f00d50501198000c00b0340290030443c013140d000c64a41d91a103c0d00c1c09480000c2c02c0302d000344a582014008110b43c200150144410307680007801c040326004814000e4030b25107c0a0081c0201c640a10132a0307004503160140c501544d0307006024554035a960300c4 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 642932005 1250 642930755 642930763
    0x21020708070b04081921050705040b040801050f0a05040c0303050901030b1806090106050c2e020a050d0b04060501121a10050a140c03032e0b1b060f070509030c06030a020c 75
    0x5403418007464851540c5400844540c0808240308206c00103007994072180c00382c030030f40600c0d0803d595a120104000ca5214415805940580e000402c0d00d4801d98a40c14a00150b07941290001c1c00c14005a10800001e8040c602900c10342c0f2050601080c13028003403000c1a20514128001723900461038005000ba10b0410801c00c5000d1f00141c50a0381c81c00400e84031496541d440019a140070324082680303d045c240c0c1d03510711201002c011403025995819450b00044c1315410842d000c00031586420b0444000d0714062090348200d61b01a15403080101104010000601242c0c000f050f41c11031164840b0030b02d60310f841c400000070948d529440c3d03c039100c40000625080c4013000003880c52404000300001c030023001003503907800701100f107000750341c04031403501d2950b40d400100820505445200340828141d000d4005070182c02407540445d003408881c80a225038610043e10041c1045d00b10f41c0114020b144282c006100503d8050304807021080c1c40000304c6c0c2c490f4011600354802c507501080850030090184 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 642933255 1250 642932005 642932047
    0x1211010305130507050d030c0609060b030601090204050a051315060207150206090c0f010903050111040303030b220203060d02131a0111031c18120e0121020708070b0408 74
    0x10a0b0881c808280d60b5415698040e507000707040c4505a0021070400300740c450910120030766070001060002c0034840c81c051028003001d84510b0f200703008410011038100f40900c00e0f2001c80b079008010b0559280b03010140061400d90042e1440e4542e00e80002c0151039003020040310003002594010a401880c04903505c82e17040781c03072501e10219088101848258a0001500250414112036408541008900507210081a40c6c00104154200000100800e1115014000f00c030300944013482944003080811800f80d0b01c1d1201c0c400072900001e00b108100300e040e4003441c1d02c494058251b0b100d5100e160001aa13507608505e000b000e1580b12105a610100110b419000d00d22081c01d0180149406919043d01c900034100d480d00c0782802820f0090590751317075420100310681400c4c0002c0105685042c0b4004810300c41d010b51020494800b415081940700d40044072035000a541c004103d14109145100a50f001c3c500c1551200c00910480c0089030008130b44d04d01a03441004019070343d03101a440400105524 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 642934505 1250 642933255 642933271
    0x109120909060308030c0a02030714071509030302030315060903190611030906010e07031b0c0303060803030105060a0c0c080304180c020102070f0312060b0a1106010906080c090408041211010305 85
    0x20200f04001001641500d4120b040300c885103441c2e054001049203035018514002d41180e144240e031500c00c034400714121081c1c8070345440c1c00072400e03a40340b819100000644401401607100700000f406c84000c1c40040c0003000c100402c50303480d004c049800a460207606021740180c43c40250209000c11510388524450b010b00d00310020704515004416945138030052040d600010800380000341014426800760950303e4000d00c0f014154414401c00410210942604402007840d161010403850800401c0e2030485000400071803600c2c43c0d04108030b440c2900d14500712086800143d020800083c1400a0009401d18020f603104070b140c11045ca1054030300d400d0706038081da407040103004003203640300303030180042c030780504048500720945441c070402032009511010101002040340031803950b0081c4c8240f5900800b004441c416600c98582c0e50803104e0324854000180c0c031184400d2682d0a000ca607141d48a400ac02a1a0425568980d276020381c41b01c4440484141070320ba007032580f40e980c0611a01d500b209034 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 642935755 1250 642934505 642934511
    0x3060f24050d0807030309050304060507051006081b180108010c12090201200f0d03020a11120403172521090e0c090301020f0306010e03031c05060f030109120909 71
    0xa4a07001c10700000840202415110001070034005250203900011941030744076085950701c40d5141c4000340750390000c1200722042e028440305c03200b11200030301546041c1c03074581c1c01401408400140010118280d0606540c01001d001541460f002074119602d0092074044004192002c0c04080146209401101c0b03104440c40c000390840542d038002c80711400003c6444085059036443c260151408001184040c01842034500e0b44142d564540c018000f51f5100b51900c013040701d40c289a035a190307200104141c1b0050070511041010600c2243c00d00100c040c1c00700c0c4140740c45400d0074480600c14a02c0724150307550780104901000c01402aa1100340c20300e0282c120f1441c02400c2d0001802b85e01544a510012100c1d100440c05601e0945c0c00c031413807084014001c56132001900b00600083e00b045a1440c081901228515046d04012080b40c01303181b03081c144602240c0f5040d0080c8000d08000c2e002c8d07500121041515404c2d80c400348200c50655004805980600090400040c00e00e040f0f9040b200c08581 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 642937005 1250 642935755 642935759
    0xf010b0d0b1c11120d03020a030f020d0b010315120611070b0709062d031a0301021201081212070507111002030c0c040c12021e0f07150908030411010903060f24 70
    0x401241060104c1c0c07151a0150723954605220440c00303008040c00d03155940f0302c00284403c50f03504503445083c00c14000c0c4c03014000000701010002e00c45280384100c810800032401c401c40083e606510502c0c1c1079018608031420020151650340808800f11581400700f8078081c3d05200b2181c01078032142995414000c0c10401d010303840340c0c00440e43c0c3e001d007100341032548a4902e200001d5030105400b1000b00301900031901d030000888201c2942c8028402d000e80c40c01008081550744070440100c42c84012086000b181ea52511a81103c040c2e114001c05d030303034002c0004070380c0c00955600c0046280b10211035005540b00c0099401260030201948805c91141d85880304d9801400d400036199002030050440042c1c4078007810b100794440440010215484282c0055018501e6440038058003406004008850300d5000c00e0b0754007412110390a00c094248042800040d001885110358400042810300d46103000d250b0303035a01d0b1029070f0103020036000308944800880d80c40400201d05801401080d5103140003c80c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 642938255 1250 642937005 642937039
    0x1204140616110309010f05030604060305100c030b04020901020706120902220b01030c020c010c06020f030403030c08010602030715090201030b0306250e100530040b010b030f010b0d0b1c11 82
    0x1b041e6500003884004400600c40e66a170fa070102c0001c0d40c0103c141c0340c200003281c640d50014440411502d000c030b40740c004181710504151080d582c4030700301030b00240503090910a003906c4410b04a02400490b645900700540107861b44401703140304500f103130359202915a4450307448003039602401546040500d0100c4003000c1ea54002a1000301c0030082c03c1a0085851320300700f20010b03100d80342140200710b00c000140300c02c0551661000704105d080395541c0320f1a903280c0c00101d0b183d00c610310016140071030604e000240c1081d00d5000c030030741610504000074035551503c0400e0030404100c900b504481480c0580c11a10222100640d11010440c41e02401d030444950000314050701a00141c0208040869440d850600c20114842d502e40c00c944034001d040c20515051000c15030031541151070b04c00c0c138400050a2019403040ea401900c0400141000703038202440d41c801b0350040d1200c031104680390210101c1548038031103410601c04814280364960440713400c0508610350080103440c0103c0306d501ca842e80607 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 642939505 1250 642938255 642938267
    0x715051b0c12030603030c01050906010503071a030109020a361a1c0e1c0210062d05130506030607020c18101502010b0406050312120414061611030901 66
    0xa000d80b25a0303d4803500c3d200302081c510b00843d4001c06172980b0342424070802060000c2d031141240c07400c0302110400e83d140d03110350701c501368490740703400c41c11409200506c4449075a03000707008000268940356441ca40c0c3c461400b060b00e01032141281e061070011900301101c5030035101c50009800b000303841720501c8680c1d0340b01040f030344a00110012501110b0b10200130b00419600f0100045e2a21811104030368040000500c54038880318440025104842d10250540150f0080f0000c03a801e0307212109000000c0343c1c01c0300031000703581c1425400c0e820300040400c5641c0c402407025158550b0940001300c9240c008189868160083d007010155032001c030804649035615050328500400f84c040446d1a074446465081c4200000c1d041029507014001c09101895815800381615541c221014000755a848092646400d801c29480b521110708200f00000d0450340010960041e2046a01040c48055004141e007042c000340c40d1071b04c0382c000740c280c3c40000d81ea00c089041810b080f1140a5458000601e00207807003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 642940755 1250 642939505 642939523
    0x3080d02070b191410061b0c030311060105030c060403080d11030703060f0b0310050d06090b04030c021c17091f0903030f080c04030f03050d0e0c0102161401030b060715051b0c 77
    0x2041161040c041c1c032203001e0710400ca001c55101e55208c80c141d4907864060a02c2c00425911070f00c40c4105070002484d07145c00984081c0411025203068602802e6868031b080f580d1000100c1d0301d5190300c0e40e16403c8182c5150005620070103141c4c0d4002826410900112094021036201148240c0d041c400d21070b0318845205040d0488074112542d00003c041442c14501900260901810b050254420042495009600032005601c2140e60040c50246200501500180410040c0400c0900320711103031400c420388018000c3c903400070b00c00e81c00090350f01842845118142e00060000c0c01c2d2010810405801407401e600344001420541c800d49041c080050060141c0e00c070240290444042c2c580606000c0e00440d560f800401c1403e101450902e5586542ea20601d4016801481a10814510707031000d2585a070984140c000d50341c10700c900070801180503103d4544015440b40301084421300088c60b464100c030103035540304030108480c60b10400540b401940143d00d400300c0d24082140c050107080100701d22070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 642942005 1250 642940755 642940757
    0xf080d0f14010623030f041703070c080a020a020a1206050106090b1905070204050a05070e030c01020c0d0203150910060b21280f0b01090f03080d02070b19141006 71
    0x20b4413011a20604840c2114400d50116800000b0521a805050240003440341c0e0003102040c50580e0a0b000701c1c2103501c411108600090540c401000000e038180d0024042000d0310701c11603841600c00d800044103140303a680648108080100b04404025150144a00400007810301550795881e0414503001c92141c02d8400314100795030428800e1080c060420703112030507005401000240b40c4000c00d480100740585240d03002c92102400d040c010320780000c0c10740101d00182c0c0a40706905014050180400d00d224040307901d170007291130a00c0b03525500240f10f031040648000070056800030300b03081e108603855a0408402e0a10811402d81401c1d8004a0001c1000c0007060140442c0d65000003142e203100308032806ca2080d8410102409081c80325040300c018031616102c1042054116001901c03005068804c01c00c1c418407110003040442c0d00c035805000071180020016140006642d91410305079030454000150650740e00055555158074403a07803001d40b111049034002428960254404601ca078806c0030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 642943255 1250 642942005 642942017
    0x1080103060f11161122020f07080a052d0a0e0307091a0901050f09160210063008090d0606080a23060105060301090906090f080d0f140106 61
    0x1910842d2160f102d06841e80e102d003220380d1503001c41144000342c5451a9029192411100e600c840e0521702211041c03003986026601452004901000201075000402c04182d4808140025000306c0da40381c00a0451016655849960f0b945003141a84082134000b01c0c0078103c080240720b4083c0c02c10800c111a9414144d050440214410b00700103071a2083c59004407100a080803840070008484030036594180100b01e540281030fa889500703200c0e85c188412161544950300d0380104841341800100000c041c0030f248103403000c01c0c100c6000b001c01e80d4a140d101c480a89040b040030010350200c105040c1c400a01c0002e00c005150803900c8145183c020400341600c1400340003010010017011313a112000904400f4282c4000c4120f45c20709082001781c480540c00c03809000040a140c0c440b01241c01030507108003c0129055900701040718000300360015080703400681d1040800c000c00d000ca0a07000b4543d12590f00d1a5588101410160503514840e1f131000340c81781010010031144009900c194159002840c1c05 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 642944505 1250 642943255 642943271
    0x402040902030723030115120f2108060402090f0103110c07180c0c050a1e0204090b01140f090f07020102130f06030b01050301081b060d0c0c050f0c0108010306 70
    0x24014031582000941c5441640800110b4190962001c40c011480781c2090781038034609028982a01d10060561402082c0441e00303100190000604c100b0f4140100039100100b201607490401c03d0302e084001c0380325a40c030303030b00800411070b8881c04003a03100300140d0f0300750704000d60000400c3c1841c3c03125811506140c1c44a100303a69281c1000d0a40c0c28104040c02103d001a0361100c00703000001d00140d802798162705040c1078805140c01340c1c1030044800c1d48140100010920340c2c403080ca04c1803540c04511981e00d1400c1b10500075988600601c0c60241c0a0075460f20654508046600c020301a9540c8a004003344510040d40d40d4420b00e02940c0003012881e10401ca82d1400c40803030083c401e8204000345096104030218520517652090402e90300580c40820501500e100151510b002c244258441c0354000703903c0c0e884000342d8862000740c4401c090701083c01c100e845020764041e196200b00d01c100180d0722002d07900a020f0704002e01c0d074112003060302610440c851500000d00000341404054102511038503c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 642945755 1250 642944505 642944509
    0x7060f1a010503062b08180102030403080a030c0212120906060405010803090105250b0f0a09110d0215040914060405010f05010f02190b090d021c030903020307080f0c0f0c13050402 79
    0x82c403400340c5811001c4038403880900d401141904100300d80500109040101f007019400003045400741c9401c59645402c3c1110550100c01070021034074a10110b016000c0c2d41e02c1d140c18010702420303094403204000d020502c3c005001030714102005024520481c00d007001000b6940000c821250007580030310303025030780d1840d100d0264441c02c15070b1580010f051030301d0700d0b04040c442002d05160007010255000f41107612140d00410540f1050346018108039089260042c1c0d0f8945591706048882c0702410f00c1c445070302510308000b840d03041640403201d85a20f400b0b040340c04900700076240c1d6210740d084904001a5041002d590340b07054803130190071b05002c803980c078001ca424000c00c4520b004840d5420410340302840d80c035007448d099a0580d03540c4590300c15000001203040c00410540300040611189080c02d41c01c0340d004a010f410401426404d601080000b9004031780c9040052800d1f03c5402c0038540e0b00d09110082a03e0710b43c02c261503c2452b00a00781001c0721341c0e51000140c0d26000900ba002c211500c480c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 642947005 1250 642945755 642945799
    0x90d030504030c03050706110f03030711100e03030105122b110604030c11010e0d0b071809051e1b070204020f0c010b03010e0a0f0b070e030307060f1a01050306 70
    0x20152914006030f0000081240c00220b94040e1401c0d503072844905604000d41030b568200318a003d84040e0401c2c0002840688140c10201c980c01c560f208940d2071070010f10170541150000c05140032a90000001403285060440d440d00d21011904000c1c40e5140000c045c1d981d40110600130700081c10b003040410030301a480303480200c8100518a0036100a030506280251003850040d80455000800221703039880c1d136010301c0902e03008103406005852403640702e6480050720303500204004140004d1022695040c0e482c0181c520151019040001e0682080c00e0765a0540c001d4042e1243c0c0c5040400811490303022100300160911038200c580d1741c0300e00640c800100a40581140082a8013011070360701d0794540b054000070341003001900200a1200042030640e00c034100341501416030007002c40030f540080e04120320b1950140e81407600412000d80c11001134255448410300ba40c243d621061524010081743c80303151080c0c41d842442200d60000301e40082c1c05804005d04080c4188941d0300d40700504a1208 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 642948255 1250 642947005 642947009
    0x1020a021306150827011116140f07090203070519031505061e0d020d0c050d0507090609120515190605060313080c16090204140411090d030504 63
    0x100303000708010003200c40c0c5004000c43d02c581c00d50100c50b5404501d10a01503034a040c00f45210300340d02460444044a501c0040309060842c950965847c10310540700e040c40700140ca400c0035244180c1c1000d4036142406102c101e0a40020f00c00ca405c0020a09101e150010b20382d03007119100e841c05616561881d0090b01d450244003441000800d01d4a80c0c103d8803a89544606424440c1c0c80b45103152580740c03824001103004071000a20900c2c0c50070081c005142d0000301900e0b1020110300c2c050301e0110407416030300a03981103a0315500420404507400715140b000340180c42c0d119000c2c1c9081c16400b89807941c01032242c20320b0311400c0813082c1e4032082481801400c0c018000f16140b400b010341018100940c80da1a01082c100010419a10700000030800d03203401005c40740030b600131154403220000c05440b176440e0750f8400c42218005109a1080c2d44040d41040e1004004104640b001a10380c3e10700801d24a20040b080d03d0144154985408222003c2c17000050320a21a401d4076100d891a4161400b43c619214075 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 642949505 1250 642948255 642948259
    0xb041406270a02061806040302060c0325050606090901090b010608060f010516060b03100e06040201080708281e0603031106100302040b0f06030403020703030207140603011401020a02 80
    0x3010800740c00840390340c1c22528030018014001c045040003040b0303203544980000950100c402c104000104032282003003d1803c200801c0249000d90382e90000d50b82d6406048030440a800115581c0d8095031803106244c0680c50b02d0f01883c44182c1c80d613580603110140103003402d11856540c0c001c02c2c417507082548090009648204101d503a0358445002a20a2500316641c07445814941d246240c02c0d40308605503103075101c8441c821000d181c81039607500040d081004032b00d505445040c2030101442c0143c000c13580b9414011010703100b64105400018207a400c010203500920080b00c0501100081c40c18030648040320700304480501d0303884002060003400c040140085c895001c030a00215145180d485041240e109482c3c19100d0031411100d01d44443c4219146c8058940740c12080002d4140354118a100c91001044000d4040440000039000e1f0070a45080d40141c0c4160780034030400d074040180170302400d1550700010042d1440c40008003944014090710340c1c9010b61020744100b1ba4000c01400400c0e541c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 642950755 1250 642949505 642949513
    0xf090503070b1006170a0b0303160321020306060702010e06130e0f09070510050c0a060501031a060108060d060b1504080604060c180905130b0108030a08010b160b0414 73
    0x79905050010500c2600c480c5441c0080b0203000841034040c0d241d003481c50750b2040140b119980c520903014001c0034042c250729054007003000000300d02c4883c940028106482501c41c010146900c0b00c0d584001e0340010015000c044c41082484410340d40d0b6400c0d9099590b0921781200d00032521004a0b21a01646c030104d401240408000714140c0068803019208640d0000440c0340d50341c91501c5141c0e41d11441c45455003042d404103d42080601c148010f1903032213210411140358003d90359030081280d0b026070054ac3e00c402c00d0540050700c0e6039800301c4550071040928048600d070801c0c000003031441d000540010251076440c0103a80c4581c0795100e6922011b1043c3c8a1580c8941e550590340362224400c032400c450f503c0c07038421818a003074041c043c901c802100c140181d8055a04019002c1c0007004041c040c000300e15002d8049000003100300031243d0103072454a02451300c400956102514950040c0c0111180c58818003020311b04516411410401319007040600c0c070a500e89003880400307180c4080c00da001e2401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 642952005 1250 642950755 642950767
    0x70b100308130305010b0f0d020907051e09040b0103061802160b1e0a050c0f03041406010308090406050306040f06090c08030d060e0c12190b0402070c060219080d0f090503 75
    0x2e011020303141224007070b80c001c0c03082c040d42c4805c021040e0615140e059002000071806805030405c24440c59001c250b5040c20742c40c00840504645c00d0820322040140303d468001000c00c060704080c0070780d84407a0000c1c20103000d240c0c00e1030305401c2c0346603001d05012038071640402d001e504001c501d0611f183c60782d04120140b04504000b40d040c138052854400a98480c03243c003010595200c0c8a1150310700c9001a4a00c06003809810015450300e07500107002910a0b20640419034850309041c02305034003c512440c4140c0c0e8861526042c0025124540d100f1031098001c0c1081001041e152000c1a0040358000ca0000b0013007160b00c4d00e82c1c0c00081c59081418184404150001455440e03408501650f42e0460300002c20307a01d03003295864074480e50080c03d03111041e00e40420040405007100110940102c4008110320348958003160803600116020713501610310b000c04000580d01400a0b0805481c0510411020316090b11400e400e8420b141c0c1c40f6908554134440012140e5440d48044022079014050302d694507 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 642953255 1250 642952005 642952027
    0x80910050406060905010803040e0103030503180d022a01021c03020c0604060b0f1203091e061c14040314090609041a1f020705121005070f0f0c0206070b100308 70
    0x81a64043c4041d80b5180c0000824040400011740340ac0b1000e40400041580c21568202e5582d040900120348403070004801c04030000c0c0a001000c54010a50f000305010032418001450180d8940c20495034034079040c49002003a40d011030641c2d090080d6000b0203c1c010081201200280b141080c20503460003040305001c100100c0f5000098458000c41d211401c003601038041200802595130800c0e0b00e0307401000001c0b640d0a0007a54140c050003824007252104090710b0119035a5440107140303e520f1030201c4a0100521001d02c60300003040400c1e804134039a842e1598014000702100705880840013400f1651100641c1c0d10300403030707041982c040c0090058051190f8040110200e1103030480c8211500500d048043e412080c8501e5460f595030300401140c0c0c90f240901031682c92046010380342d03024103043c041303d07810317103000b000d000e10459a210040c3d003940020041c5484290100c61041061442028001d031780d0b01029111a190460039600307070b507125940b0178401c01900d40d000511015000c10754000d84 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 642954505 1250 642953255 642953261
    0x21050c07050705030111030a09050705030d0f0216080c0603190c030e010c0c0c1809080c061006170103060203091c0207050117060904030c17040f150c050d080910050406 74
    0x5900c0307401141d2050381c5500130142a129412161a0344800910014144070526007281c403016014000b503401064407040440d0030452280c0789031000c950034003105a0190390400c20f030981c16280d403451940d41818452420b1b15520400900c82c81060080081255004484244805c81d8800d0a0800121584590145c05000c0c444484640c0c0d51030325203031500c00390154807000140c03584020406d1a090415040203042d406050480d5241941c0d40ca141000940d444020820306040800403c500e19100003c40c01d00c00c11600243c0800607144020f01da200e050081445c1901c1e44503002580703076940d10b04424903000303248500d01c01e84020083c0004045070089030706070130b0b04c0702070380c44210051400303540024084081d140d868002c44c0e000005000303e880390842c4840c0501c51007082255001810b0345400303a8200c0d4104140000d90b60310200446884203c607145017040c0307410220090201600ca0a444410344005002408440000100d102c031041c42813003109400840c0810403400c4c40c4c2020001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 642955755 1250 642954505 642954517
    0x1e12051c090f140916030b09040f050106050a1206200a0c03020c030102280201021303060507200606090c1306050319090f0f1b08010b1009051021050c 66
    0x2c140c4104002160701c0144280004a1403000b400d9039003551100802800d0301c0d4103446402040542d111150035055071540c0c2541c0c0558040d040402c1c03211001c0c1042c60840e40140d00040c070825002130104043c0c80c0031680000c58642000c0b00050100c54907c40804000f80000c03070f003521000001d96903005580003600c81c401580a0b90032940075000803802c0c14200e10564100c034024401030f000f400c00b252a02c4603800080320300c0d03100160901903101c005405880c0c0c1600221441500c80c0308024000d64407a80e9240030444181d141d040d5080e0540d00541c0f41c40e4050301040c001d900c14400505050003940445840c0e00440041c046441c0c1d6641004006030400c3c0c4441c00031000c4083c3c03064903040c0900407140c01581152110415601d10f9403246c058034803640301210044003c01099145030b01d65880207008040b91000883c2d811851410000405400030340c80c2d051082100050103603464421121032000968213205d901221a1400c2d1610f500341d40d2080301400c0c0c100000c200b0001c4581b00030f460 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 642957005 1250 642955755 642955769
    0x907110607030e0307021201020c1f23010509040c15020a0b0c04050603011806091103070e0405090601061214131e080a050904020d09080901091e12051c09 68
    0xc8940c8491800320103541c000c2080d00030070b6200780107200161502c040e000040d00001e00c00149410060458a0300701402c61030f8058425035101a245822030b82070040304003040c0810405107001e00e002403600311404060103107074041d140c41000030b0f007009540032100014100017281050241c503140d40080d52003503c098100c0d41281e9040105a002541d541944c1c15143c0c02030029065a0800b2942e0104100c06021806055207900b40010035109600c2440c061a4445a02c203030f03070b89019040a011403a00f000501e000b41d103480100004664042540c070705560040c0b80880d210010791090901604001c84510081c0c012502804000e80306580b410030900c2c031606d8010182c0541c281c5075420b6408144000d09084030801070360000c03d00c03505c010318200000820050904207407400420071180c021404813610711000034143c44035a04810081c008100d4241d281c800c440040c0b040211280c500c0c410312080c0030103070103400e040000a0180003c8101000842e406110350034000500907801442059 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 642958255 1250 642957005 642957013
    0x51908041707050f04022218061e06140f04080115051903120507050d0306080c060c07090525032c060f0703020d0204080319030e2505090711 62
    0x2041540205454040f180d0040040d00e03001c0c04030f0288800f96002c000d210079a481d215841d80502d42107100110060814901c01003e010241100301d070403100680c110f9541099103690b101540342c0d014480000355682c0703207418020152031900b02003c0d402500020111440c1c0400c0c00300b08543c0540c8401c40030f401140940c03020980d52000d0000d1040c104490035201801500d092001c1000400390b140c00d10034519010b494552903454407418102d00300c1840300000c1d202c200410030204104440940d40c08100d0340c50749002e40031000b50340e6a215074465a0b1901d51604e00046282021110003400351032072040d41c43d02410725140c000c0050129442020100c0101691380d440b809688032090a90140c1500034042c0343c403070038859550350800800c8202019020404074004003400d001410080c41c41c000155140c40c06000140c81c103d6034491107004040c03501c905210189000280000440c030551069040c1010068038245264148c0d013016030040301184c1401800381c2e0148800c0f20809890043d1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 642959505 1250 642958255 642958289
    0x906051f112a0105090603041e120203070b011a0a032a02031e030c0f030a090210020c0321030c07030201060320011d032a0405130312060501050a050705190804 70
    0x5407000c5c00f07080011900084180001740004801520f01c589078070380c15034003482c07290301541c0d03050074408610070880050f0000306031901000090a0524054842c1d41100c41007455034001d14101c1d402040c00900815440e000303c0d0000c0300d0042204c540780401004906501c10b543d44001c4c3d542d601100c1e0804401190342418a0000364020549005d222007080c05da2411520f0f0403030b1006600041c0462040503031b500c81010050380c0300400f00d4030b501c41d03a8010b0450044a10101400d20740c000da4201d81400d10040148500100107088a81c0301e840f030700c800c0c2d448a081d800d0481c01007200d604002d01203401404105044c848584010038415000d83e2058081c02540384d001c6003980000307007a0346d059445100b07514920ba00e450800140202113034a0003540b0850180040d081e61010f56a19000c1080c1900d0034050540c80030031110110301d580000c5c001c45291000082c41da208814100c400c104c0003103074480400c8001d210076880030b41140103000e41082c16081002d140e0b4854455031018100e54404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 642960755 1250 642959505 642959507
    0x10608150702031605011401081b1c02010c080d020406081b120408250f05060c0705060103110a23122e090c060809070906051f112a01 59
    0x111911890071036010718240556201c0581e6081d04114003141c00355200c21400b42c1d494004980c442c002d000000c0141443c48510003811003100d08594150700a00e1515840300b008841c1086c04640c03158286022105484107080c01c3e0114040c4148440c00107000040c0042c003e54040302d414080c1d200300210704c10b0081d11903030300c40440c400d9200d080080382c0381c3e01c002808100c0d907201400303030070017500043d07550090306500a44400c4408401102c5500700c002042050050800409070306c4a2044906450000d0700d444c0c0e180c0d90141448010550017801b51240d00c1d5884001240005100d1851002154040b0803884040d5900d00e030040c40c06446042840f2031105070008044040c000d2507640c4500080c0140c21070300d10494500c0300c80c0c02040d290300480c80083c1003c94024010242551009682e00b412610581421342c80d521062071a810408103000940d00d544040604601850751450003502a6a0543d11001c04400c40e14003030140200180111b148503851410309042184601b4940b5680c0c00 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 642962005 1250 642960755 642960793
    0x150905010924080a0b03191106040f12050a0f03020a1a1009050c1b1b030d050d09020112180311030c0a14010615050c0606010e0f10030e0708010608 65
    0x100b85042550601c0aa42018090307420305402420b200804038840c095100440e10b01040191022440340c0d118400d5070500c0b80625503031071005811031b091843c2910700560402c1d0095035025103070840301d9000c8105c00308001000f0010400381d01075140300c00f074445401e01035207030380c160b5100342c41d030000610303803215400c41111a0510802442010ba120356061004200c0240740046c16205203280400504000020f0440005210040940103014001c1420070700002560003040c400d000c5d50000004141e110303088404d8a01da03c1250705e001421840d140012907010548648034403105140201030f54401001c1c011088200e800381c0c8a03102800750919015940f4403500111720781c217420285030382d00021030b8040c94050034809080003041980d00c480c203281d600c98500310394101080002440d154920300c103002c4568002c0302420940c150744603003000300e03280744421500184940ba44200ca844a00c0c02640074004241726401160000d50301c910340c0600038219070051402d544510b940da650f550000304 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 642963255 1250 642962005 642962039
    0x10f170d020d0309110306040803180a050304050121060602060a1d330f150607020a0b090406031509030e101413051216080d14131509050109 62
    0x380c0100210002c1c800c044004000340c810448404400500ba129070303950420102c2c0c0190b000b40c001340c1d40e9040441c2c1c07000c03200030023003560005608421440c801154021068500b00e40083c01d00d03400040d02c5038002000820b0390448000c259141c11804207034594005411407045003005410031207240c036031080074041c0484001c0c0c120b283d03016541620703180e85d20000040d03c48075503214a082d1000b02c2400c00e05040e504440c0094102d8045003007110800581ca10083d10140944100c1e14001c415000b0803084a414050200c1440d0f0018241c02d040d1141d44c0b2502c0115004020703075013501100d5030b140d000340119a0050300090754402036803030f0300e251044485040c9281e64603a0012400d01d0b5202402603002141d0305185440c601c000060b0356280ea450362400351080303401601484aa04030400350091040c0c0202c1c03c15400f10300408105d0b03421200071000c0900d0f11429640382c100c20500c8086c1d0001e20b03000039000d402c19102e01514543c10020b980d00b50766007600e84980c2c0c161660b1614070300f01084 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 642964505 1250 642963255 642963257
    0x2070605220c1505070b01080604023127110a0b03070c1202070e01030b060301060602160308071401022106030a171b0618010b032103070512010f170d 66
    0xc031040242a100307100310f03602488a410882e040c101c4c20344a18522120982c00300003141c003c2405c000852401e06401103a86600d0321010008080d01d801e0f925402c07174580c030108001c075514018981c44201034040110303408802d44152103020302c645048103616a60300c0241740104001840402c503d81010300f5648260343d142d0300d40090700700d10303110b4403c0248842600000d5019960000c940240480403203400b85028000715002c070304201e0b09060854569501c0358085400220f80b07600403551105503501229042600075449001a040201004104c080e2031101503100090b40c0750340010501c100303182210140081442550380310140358807519804d40045c03a11310054000010362400710003034010300c9030010f0030340d284000000002c6c1c6003041c2078840c0120701d4002c0700070a040304001d0080c1d445c180720580290030f403488400f1010230384441d0203011110000000c00003410cd284104256101e004e1100340711145542d59818030b80044e21640510704260070005d0303001281c514002271a614442513 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 642965755 1250 642964505 642964523
    0x190f170315130c02280f0809090604050402100e010201020c010c030501080d020a022b0212010f060909211e09051003050403172211040b03070602030d18060207060522 73
    0x1084602c0e02840458044194189080008101042d6035201691501f4410340031140d407426520704010488100410240c071440c202800c000041c3c894209082c501c0005003081921040710000507400390207400440030302503292038401800c0c190f02d43c0080f4100c411360801e45a00d81484082241c44034808940130b0341000400c050f184030810030982810744000b140003c19801011540020922280071690440d103a44403580c0b400364100510030b1100401d01503000700070013612580c420a591107020024140161400708903546103020781c54140c2451010070000100e0203040314050641480b40c0900d501403203084c2103154401d4024070555014581580b00d00bc01500c1040308407805540c02480c00100c0e81d001c00841840700240c80c55010254414020006500100c07070500084030341c141c01191003a4001c0a0801001c0e401100f05c8411984a001c0811202c00c409a484141600e0365401032907644000740d448180b103559072103030b8011100314094020070702c200d0007401040a408080a80b82100c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 642967005 1250 642965755 642965773
    0x501080705030c0a0c0503070c0906080106050d02090604200403060c030e100b120106120b0a180b22031106010b0f0a1b02060412050c03190f170315130c02 68
    0x40000b004d4103890f03480d89032410761384c000369440030300b160001042295003003e010428455503850340591000360000d00c00801a0301e00d04070024000940e0220302a0251510764040341181e2900d4000403500c1a185c0d0303182d1507908820788555036a038424401561514680448461440d01c240111802580d000b001003d1000c1d007071580c03174000d02407042840d6005004011104001310b0138051400141000c0514038500f20460801501440b40213041821a07407070920942840740406140700d0034036410a048901550300d02d0b041d442c4a880324812211032140102c0301808055008560440c56402442941c0d00c5036030310038031100240516003102500c28021700c100c111f840e00c2914002c024070076030954052558141e8010a10646c826007241c0c034004001d100d4101440300400c4500480f8034194002c048003450b84406c60344080007010700801d80c1c1850407412041c0000008200183c00b80303200101d5982c1080e014006451203000c800c40d0141ea010310300d0305084850341c41200316103ca41d401500d4420 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 642968255 1250 642967005 642967021
    0x603070f0e040f0e0a020102010f0903020a080c01090f111306050a09020703090f0303050c1209011d0d02030d0305010f0f051f1803060c120926160c030c050108070503 73
    0x845001561030b00180d48041844100010380a034103069035560029107140e00d80e0340002800e41e98010a5501aa4103010860000903400101080c081d030300700c2400c0340c60b52400400f0f40d002d045441c00161506c06801360b03030010301c02d20501000e02d070041224a4600314aa441003c001d80701c040c0704996200000c2c882c20800140990000d0006070b00c246801c441c0c2c00d4980c8000e00e0107800b150410f80000d07001080403500c0110030030007418107840c88451981800c08000c0000c0610f01581040079118040300390000303080d1161a801c0d200c20358010181d401e4450706500c02001048244100c10343c0104441c00003d8030b07200034801344c0035078070080c0c480040032400e4520106003407902c0345540c003000440903803e2407284810b2551406184a0900031804074030034070000f00f0100220582003c07132840c101040000407401000d00c6202412540d03d24048121541050110b00950f180c240d01a0081404101004100d40001c000d59128041e9610352507102c0e001100c1c1c1c241c0c01c0340c0810200d441080814551 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 642969505 1250 642968255 642968267
    0x513060209032a03150903180a09180510060602031902150f040c050913060e031b060609160801091a04020d02131703250c081b0603070f 60
    0x12032000b5044440b0380c1400300c550b000780040082c480700580c02000a240c07007443d00b444180c400500c000c0010195090800300f15840f44942001c51000221907400940a600c0710b00f034000003801360400400030200c901c0c00a5000207514001164a401914480c2816205902c616000e0320038590003141032440b485800740000e0841802c04080d44101160071840d0280300510712310480312030074101d0550515113041440c20419400c114400d051010400c002000207002014002e074120b00080b800c003001402d014114031503040b446100900d40c0441c01c01c2d1410010710a8040c4000355450a6a0b80c0d80030104140f145a0b1030041303000402a0740104980c0d942c0b078000ca803031401c0c145024107030350403d0000a0208d0780724100d9849040e4020422080032100d88040344014020070310ba80012031842a03203142c0740d20482c40074843c03812142d4107e0b06141c00800134035040d243e000b00e441800b1a00c0c3ca01d4241d445441c81c20101d4a4201081c0c403550b076042c0f07141540e01414064844d0b140050810f50705a0380 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 642970755 1250 642969505 642969517
    0x50108030d0b04060b03040f03030b01020c0f01210501080309030610030b060909070801021204110d121b05010e010e060a020f04031e02040c030606090e041e0c0816060801050405130602 81
    0x21044e1a00c0700030602e00311a00045014038422a200328600c02c06280240035141c1000081d4195044240c22460b1600c81d4100e400d6982400d191090800c07100e44108c140000038081e481a42e1403402002007501d080c00001083c038040b0490071221903903074107403280ca0002070328000180303805080ca02180c0c060030b2001205401c070744a807003a41c014a450b02061802c9810030498041408a103600b400240a0380d2210410758600075107075806290102c2d260004001e41c1c109148003000354030310b6070200080301202c402c0103d60b272184c02400701100b02d840141c040c00700100e80c80090302583d8003282c500004d0384200c40429490030f41c0103040c03520350b89074491581064015054240004a2081c0050341c891007000442007181c0c800040301030074040e00a01c0080e0300d410440b0b4a4265400317000c003044041810704400980404000041c0d9002e1038803003040703413140d400500c003480740e0b240c442c0040c0c0540701080c080d02c501e640d0b08003007a0780c0c0d24104001d5a0094400c4c481c64590800020007183c090340007481 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 642972005 1250 642970755 642970759
    0xc05040f0e100302010f0c0b0c09120307050604081608071b080f25180501141002060109200408030405040f02270105190302120a0c020712061415011101050108030d0b 73
    0x2030b01296446000c80c016085072a241008000102c080d881c1c9400040d5034be55800803001181000010303a030b5a0750703a80019001810510380850302c41210510302441401e030a40c4070303613001c0d101d4042d80792503c1c0b5100301510010164100382c10201d03150200203040749800f01c0300c100070040d000003510603e48071021032907030b00c00c0e8508100e40445c41a1460b1030340440d01c090b039480000d1540c54041d40f441d180703101020040c0b00303115500d5000314981d07000542c0b50541d41401000607a0200c010145c040d01114002c000440d404042000a0071070800b1025008588060f64144126807420358580224441c40080440301142100c140100c00c44c610b0103042030784e4040c14110315180440088103010b0000b1560f250000307800240103002d8040fa030320004d4003e04213940500c42101140742c060b4644e0040d0281903200c05509a806040c8415900640c1380c5400c20011040181007040414043e0f4040e0100e83d40484d42103448200800d40502c91181210f0484018500384142c1e420284050a11072404603 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 642973255 1250 642972005 642972017
    0x60403140906220503060c071b051801031e0213020306030f070f08010b0405011d0415021605160e0112030c0203030d021e0405010c03210c05040f0e100302010f 70
    0x41d1a03a29102e0040c640000314480e110010b00c062440d03250b0007009500803601035040001408100a12401920440d0b0352280c05040200b041c4050440c1d41d490a6001c0750b8800c0c40c01150280301040c0c041c2031410b07170780110002402a103d880340742d0464000d9950080d08480340200b5980201c2d01c076400381d81c0041c002415501000c00042c81d0350f14083c49a080911802e100c0e9500f000004000d11a01c090301400ba28140b125601d052044c121050090307034485084904080010100100003a641c0a41c4040c3c84045440b003440810980c03855410003c00c0b106442107030009c0c003005c0074104044089400185030207025030709000d07487c859264001c4085003800014190180143c2c3c06101506d44a400f81c0b40050f110980c10800ba20300e52510101c0640341c0300100418002c99174014513543e01d082d05401c18000d544070000c0c000c1012054001d07c920b0552070300301900e285580c020000d104880802ca807812140da2158580307a40810282c0d000000712071441c10420041d4010700c144039000400341021 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 642974505 1250 642973255 642973267
    0x70f06080c030402041b050316020a0c03060903090b03010909020127170a06020316080c12070804081b0a143c070b04030c090204081504060b150306030f060906040314 73
    0x103000306d03092114413021a034040204207507440d541102c41c000d00301130310080540c62003944900141c40c0603800041c1203662500c80c80c1c0145030142c0550402800282405a43c940e0f40342c80500081074001001c0f4002400e401c1680c510107030950500c94440d14094404450502c0c0601401d200c0e840f803001c2e600c02e80219007010020030094405103104021b80c45a5407005c0c5a203400003001d545000b81074081064050008a914000d400301b659803080507406e240a0303a41300d40c1414461400340c0112072103014545418000720795008180709148034418608002c142c05682c0c0d196455031400d03d2481d0010382d041440050400700303c60080d290410b1b440e558000440380401d154180304032500020070f14240000d0800c10000581c0304280200b950b85811414903042c9007001341c4130204140c01e06a5102c1d14001314046c0701c400d0b480241c2001009060103d86182426155141d03041142c265102e80207020030001c4402020a41074401c1c8403200c058101c40c0c3c5c583d44c050f901042900c4c200c4410380418022 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 642975755 1250 642974505 642974531
    0x20609090411040c0305010806101211031603030e03010506010e15250b07020609011505190b040618050409080a08040c030c060804021014030c07020d0c030602030603070f06080c03040204 82
    0x36024220043e030750007003025230404501c9071400c140a4004c49400003819010040d4030301e0010003090150b4440400c3c40b4803089500021b10b4500d04c04136589290103807550002c100341d0000c00440d0b01310400d900a102c1c0790740c0c650040d600c101e00000b0640c0c120540f03010900301113890000400e190442c01650300e0f001c1e03030510a443c500c01ca8201c41240d81c0d00d2064140010140c04118a940c044040002442803800e041c1d01900502a40e06c0350b14084c203600e460345098031100f540800094624684041e4649550342c00090160034001200003010300801e001040c5800c0500441403c0c81d00a0045440c140b8003e10841d108c900007407069417010300b11030006c000129104c030840c1c001d20039590744030a03c1c20240108400c811412040c00305120741c0c240c01c0ca96002403038042c0c1c1e40c0110012401030300e8070110700100f44084040c440041000440700404010006240e005c0c1d0300490f170036000c035000b8076118040d80007003440c54012032000c6111840090b401000d400015684248003600c0480e038a180c400c3c17 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 642977005 1250 642975755 642975761
    0xd0201021905030c07142103160c14010504050a0b28080703110304170c150c0c0708030412020d0c0e04060b1e0a0e041e050309150702060909041104 65
    0x101141c654200240850804d4410411080a004c120030f034000610f24450000d8160140e02c015040584580b51700c4204200050060300c000c852002078045900d00186401280c52405014280c0801c4c240201582e10b544a1016182691000303480e03100041c0c01c003440440b03950098511f148a800d160301810140302c80700008070003400c18a0321824803605003654080e055901c88205544581c00c18010403021408491108a0011141a100d540d5803d041e101c54101481c4001d030410026000301440388032582c1c00010405103814005841c0300d40d882e25500b94480c800d511132000c540c5e902844001c094685501120415841204034a141a640e240034076000c41d0115000d13100302d5a03441122603142000035030a16800c1594001401e2580104009048101180140103085014600060820290320309001d842c1c501c50500c00314648031b030300e00555281e000c0301049000340840d4010051a1095406440c10954002e090a050002e240c0c00e02c00030160090040e1011041c0c1410303000705843e40d01c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 642978255 1250 642977005 642977053
    0x402070f0303060509070c080307081503030c1b0a0b040905060f150a0e060a02070e0a1409030a120612060f06090f0209040501080a030c120212040b0c0f1b0d020102 72
    0x1032400f244061925003040350007500141580e00340002c0d905c4000c002203020040344d900c0146800c0c80c40e00394a5a049200c0516000c503a859058400010390000207030001a0000c240700c05072000c4111210480c0521540020030302c106810701c1018002801100901d03000140c2c0302e4006403801d8a800c4006c000240c010040c1c2c1c0c410100c4070b000151001c00d0941c010812240500d054644905c3c020320307507000035a900964400d506603e4501404504014142d070400d412030342c200003905125080038661181c4030341c00544043c0101303020f0680c284041d90240181c40c21611019070a0700405907070384a410103010720f01c001d013803519030328500494030074200d21076400d861041180c0180c458030b4603004c3c032088650680044d5015888403200c04000796000190b150f034241d1280c1c150340300002401d0309a151444034480c6425140000c20049505141000500307600028001151005c0c00c028244640b2150f00d10380d54110401100501d0031141880100d140030140b040c030407203568800c103481c1441c00090702 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 642979505 1250 642978255 642978257
    0x903070605040b0906060f01090620030403080c0f150402010509131b020f01020c0a0303200a020a151806020a02030c1207110a0b0405091003020306040f05070b0717090402070f03 78
    0x201003440884c03402084090ba01450035141b03018580c6840740089d28800040c420707501003040d100d80032800c005034412011030000e407140803070f17848a440b0701c0c1c903e0b8580c0000706151040c2c8140c008201c262140028903440e03100360303040001259100d5400440350383c1d1041c00c0703c0c0c1d044815401c00042c420503a200f29080039043c0303500d00700d00b0300c15141d00a080020042406000360b005000303440c010f00011031142100e030341c18140000c1d400e0b00e0442c4456009551551096500400300301042032640214541c80001c0c800c4200c841ca0600203025402100c8a0501224054229038501000222030b5801003510401e140116400e200d40c0501142c42c03d00105007501d02103202049030802c102e0340481c000b00400c42210080111810f01098950710300861250318420f00031038010603a0320503c443c0c0e02010316005000e8a44a241904002c8031100c82d5800445662160380c4002855207000c1d4299101180e008a01c0c0440100100d50180b054010940f030a6209500b04040790000700c1068500700302c0d51103 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 642980755 1250 642979505 642979523
    0x6090606040b073215060117060f0409080a08010306061208030412200f16180f2909070e36010e070809010c0c06020c1e151302030c0108090307060504 66
    0xc030781244e5554000c6d00c4941070101d081800500b1aa0a0003a50f5008905880c2100d00c404905c0c005000303402c071104054002c1d000003420313030300203580300700c001741a00d02910302400790503034990440c03909040101014080c40805c0c00403a00042c0c012040d5031007179055203070100d1110342e548108000221116080c808a900c18900300c1030380c44040c00404510480040f646800d10300e081129500b10300d0180c1100c410540d98444041e0b507a0007940210140c89910050f1003000c2d00060003035001c1949040401d01c1014041c000510980c441c02c003080341010050408001407070301046600f081521440c001d202c02c2c1c01c0b45001445140820078a5008040c0502080c00f1410a1000540356003400303015280140d05154500030b00d1a00900d210300c000307030f10103401651040b40076215800d2526800542e4059000c81420444e110000907420460207101c6018070b0064503012002d0481600300d01d0000e415400241c80c01c016580a05031903640000c0c2101074a2070300580d62365240c00c5130401c440403a02500 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 642982005 1250 642980755 642980773
    0x50d030e01050f251202030a050106030e0c060f07050708121c0b15030421051801020127080d090c03030306350307020a0e06090606040b0732 62
    0x802d0140b25080b204070903400c0c40904141101808007624920b402c15621204035040d078800d4400e03404140c0f800c01360102151a414050b40f400701520b0207100d02c1001900381115840e60b5440890000b8416000614492800103810308120b0f25820000c425200d42c010b060000695800500c1038103004c40d80c240f042c503980d00c8070190320142e0514811006400500e0068a0b88840c1c80729000100c0c58900c0040c4240c41b81d4035850110306c202c0300d041c13034404401451240b05e25202d070401c0c0601500702d1075030900c00483e0b1240c80128202c8120301100701c07403401341c5846086189800403c800426000320011032030440d003c110181580e101c110201d41c030320b440c01d5041041c16414462900030b4400c0941c1039182d0040b0f12240d0200024400d0718019002414980c2c1c00c03034040400861b50800c3c0c4c0548003088d0165106030901012504403640d40c0509540c4000490615094040b03030140e81d0822040c504004840d2107540c0c142c0a80a4660000100c010750109640f1450000c8020310348a0002000401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 642983255 1250 642982005 642982031
    0x30801090e0d030e15150913031b060e0f060907090218040c050f0a08060301050c0412030e010216030b2205120f07020405160e1e0f031006082b050703030203060a03050d03 75
    0x87c802041c074022102803400b50f07400650b011200b4903000c41c2500e505111394005041200052103201c0611401d84240707c0c80c0d00c00940c005c01c0303151040c91a9001d40e0310441c0d130f50049005070300c5a04a207440380560311956036036920702613020000e5048070340b80003070501103030b2203060704954006503540c00800d0103030f410081c00e4a424064250300c01750200384a41864a020810703043c3e88100ca100800f480414489000e00e81d10800101c410341c0c4920326800384c02a501e040c910000c02094840c202c442e000514107000c1d2213114800b28811961280040c40b4044040c07a03081c0d85030300206460415000200100c2015a032140102d078040c85d29441c0d800da0600b442040035040442b2030501c640111554030703e48600341c08901f03106500035015141a41d00031a401c0000342440c100300762020481e880d044c40461801d0001078020007a503804054128145400d1a00b45040c1e202940799030006801009030400091003600a103402102c0034191030910750700e96645a01308140c41102400180d5541c0242001c1303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 642984505 1250 642983255 642983269
    0x14130314060a1503030516050a0510020c0f0601080d0f0924030c180504021b1e070611030f090105130608090c0612040206032d04030801090e0d030e1515 67
    0xc001c8480303050090914545d0060568011184a048100d043d485100103102c01840034250803030340a002d40311207002c000c4440b4000d4201070f004d40d01074404e40316400e460000000e0010b05031900d810003440480b44810003121015101803480c4100000c51000050b40c2d01014100c00c1d25540c0c800d4801c140c030003e814001d0449900d1200d0001704004220103008a0070100007140c19201d00342c0b8051380d14100c2000415040c2d40c5103500c4400307480780c1e401c4003030b04c4035820030000940c0c680071040d1044540e0342c41c8102c030f0000340600c1a02094008000540031000c000e0300401c10100e06040040c00e0400a42007401268420752140012030f041e40e007005a130810a0051109003c011120942010418000c1c8045800020070090107030000102013007900b00c00c00040c0141a600f0500d10844141c080c4412144140c1581d040300841c80000000c00c14240c00e028042090002000609100000e42c60440140c0641094613405014050108103600340f564002c1b8410205080f04005040c5c1000c144985 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 642985611 1106 642984505 642984521
    0x20603010e041a1e06010c050f06161b02060c12070614010b03040803061011070305010510060203040302061909051206041203020a14130314060a 64
    0x140000c1e428032030300c00c522404420301e40c002505282881000c1c240da007520981400309008078485140c21140c0d500c40c1051400140084282d03c881e405e0801c10604500346d030b0440c4040041c500d104646503103c46089140042122604107040c44c4400c501800007841110006030007441c00c031082040031038032100100d03642e40c3c4514510b00031005240360924480c0480782d0b0030001680d296110192445107070000045890341c0d64410410001010240030b00b403e00c0031482a1145d40b900401420014620030800040c213410b00c1089411000c1c2980e0240e021544100001d000684500042d1183c0e0242d10120100024040c482603e10030081c0c0c001c076400c00440841d0b04952030000988a0141e401030045540b4540d11000850980c030881802e17001144409401c0c1e00c00d4104c03031006000030400b404881d4141505c03681c45c2c0f001c1680030310107010709620140a0001c840070620030959 = true := by decide +kernel

theorem cover : BRFrame.Cov 642805755 642985611 := by
  have h0 := BRFrame.cov_init 642805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 642805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 642805755 ≤ n) (h2 : n < 642985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
