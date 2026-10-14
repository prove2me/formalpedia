-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3019
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:25:11.768674+00:00
-- url     : https://prove2.me/submissions/d5b46ce7-9a9d-40b1-a6a7-6ac583e45fd3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 542805755 ≤ n < 542985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 542807005 1250 542805755 542805763
    0xf040804030b070f17010b0d0e03040807030c14040c0801050d05010e0607230c031209071d010305100e03030a0c02010e0105040f02010f03050f071421071106190c11 72
    0x3d8180000301070481140d603255200b44e0910440590041c00c42403549040740380318880c016008000c40c520f64030010f20b0b5070f5110800494004014403419541d02c030399203052010611109100381071440c105152890042d141c10700c0703616501c241c0c41d00d84100c42d9003813009029017560650011240b541d0380f09000404034108000261240c8100d6881452405064200301404520541c0c0c0c60b00c0c0c1a000c1c819445601d1001c420394460301d1400d841016550317115002c0500c1d15981c1c1d07015181d142d121519003c101d24003803220b2816030b03014038125080c488840b0078010449840d02c0207134000e0f0308144085090141e8507001000d080c1d06030720010402e440c08801c0e00d42103a10035601242e0110083c88100b085581110030700d4020045410100714501e000c400c00280c601000705174400304144c1c03400c407407190180c50065928070301c02d100a00340c2100280d401d003400c0560660700d920110340031a032420034103c030000d811441007002d400500201341259081c8e4015001030380e80c410074070074051442d1628400c100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 542808255 1250 542807005 542807011
    0x10b010c0f1a2404090506070522091406030609070308030a060302060c0c101706010f140c0f160609030f0c120807021009060813020a0b0f0d0c05120f040804030b 71
    0x4403e01c011040008852104a00d8000002d0300a9080c101d500300401c10108000794400591700b042d030b0383c1d030308202400c4030a440541c0000c00c607445942e601003034881460b80020000d1840400900071910351008140c1d13100c400b2522420030b64031800048c03000460340030145800c8640f8543c0070a105450703500142e013035000240585041c0d80700e4141d00c841c0d072420b10900142020035091002c0c1ca0302c5588200c01310003400500c038505000c1c0641c211910f4074443c0c00328160302000c000c030040d26400310b03290036521040c40801885040c401c40036a5001d001c0680c0003141124929150005414555620f0030789100f15040113543c0d80e0590040026038203003413001c00e0881da00c2080c1071542d60344148100301411032000f695100b001440d920600c02c403a0460700307c80e000600c000e43d151288042e88001640d041c0d40d60024180c88401191800b200761071030003c2d0407401c10468003031018010a8404880c0340c000c2489041241e060000880d88031080340a00c2904540250f01c10342c07400d40c0380d48441e10018820b13 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 542809505 1250 542808255 542808271
    0x30703050a02030d081003080a02030d050a1407022e06151710180b0415060905090105090403140c010902060a0c1103060906010501031d011401030b09010b010c0f1a 72
    0x1441c40001140380510259990400600340280e4a0034943c003100a0f182072400000c210282c001598180c00f0300800a0f5404220141c1c0180020318200070340101070a01e044650f5898034140340851441c50010850070345003e0301e29a440b0003c6110040e5400549000d000310196640d1b80001281c00001e88a43e0610140b4507184c554184000200000c2002d100411000c0c0903040b09400b840707050200e9a0a4140f641d1005000c05d40f07004010019006161142d4000540510060005100c0e0740141044040310011540c1c10816a41c0e034081c484c0f590000c490060000d046400c64401031141c2d02d01501e01c4054020000907038100340e50102e540c0358041108900858840c60380541040085141e840d01d0780000c3d00941228141038000b203584e600c041c010a030606850750009105000d01120b10031951140d54000d008024040a006007078040a0209a402c1903042002954000e41400b5400c8600c5044e551580c40c185d013a00e84540a04001c070342200c15103542810001e003c118405d0742030244440f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 542810755 1250 542809505 542809513
    0x1701050106121b0c03121b0f02030f0a0305040f050a0507050909010903121d030d021b2a010c060e070906061d091b030112051e060a0903030b03070305 66
    0x61510240c6052000160b6000b090305001012104410411034110700c80300c9820404860030b614502900d8119082c2c10f0011090710f001d502c1402e1629284240d000601e058440c0b0820301c003c114102d03180d02c101042c041d050b100c03c02400e9032030f91190b4401a030040c012184140c030300c04113a8030305040082c1010141c07081e40c4074400610407458000003a50308424080002c003c0802c00307640141c443c1c1140c101522500e0766031207101c42c020f08210444404108041d05a0b40d480040b460144000e410a42c4000d40791003202c1144100024001540d0002c402e91100e181c0410031004500c072440c2c105200ca01d070410203111000400905a1702485510303190b018003500c11582040c07800000c45030340340c1c0b2030303c00c0011086528a024182c48030205aa11003500d41c0080c95561842280d000040c1c1801c200d4000c00c000f00000e15054100148020381c0d00c0b480548058100c4c0c2c250440340b5008107105500f140e00a0000305283c507c896004034075080c42400e010803400070b0b0303030000380c1000d4080d4019074241e04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 542812005 1250 542810755 542810759
    0x7020105010e0c0c10150f1211060915030a14091b01020d09090515060f0d060b0f27090709050102150c09010f021c05090f03070e060f0a17010501 64
    0x248030700b001d079408900403000d01c0c01c02c0300d201c0c80e240c2d44440300c0c0f03600540d03a0341d0b8007094400c080042c0c0d0a0b0015000080c0840801642d03550400d00b00d00c040c2c04d065900d0941c107442c6200b2868103204a6200000c0241200b401608001c00b00d04c1c2c940c00a00440c031340f207030b0b2000301004e18808400350521980c10900038091502c07041845142d106a99580c00d411500301403008011b0070f802c140c050007590070310b0707400148a9a40520303002980c8800d0302c541d41e00510100354000d46203003100003031403401e480d14030921549542c3c600030f06c0c0342e0013040026051110300344903030789004c0c41d94101c2c100d03d500342d06d0310100d0141d40400810380d00c640a4a0301030002c0e1304c8920520080d601085030301c024044007500d21403070f0f00c2d00007010034441c020940001c0c10819002c0c030050790316100300300d0941072208034441c80b0200700d119103001d42107030b001940b945d01584241c66140020b15011075120212035502c80016005c1c2d41380c034100030104000c02c00941d4054503043c2e02040902e0b00b41e02c294030640300c03c1c0000403154 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 542813255 1250 542812005 542812019
    0x30311041d07120f0b09090105090607030b060906030405010b010212090a060f050d2c0a0f0311030f0c0109020f1903030806180112020102151513111303020109050301181e0203060702010501 83
    0x781b401032400702c1c90303810003061065000c4000f0358103500030020b02d80010311241d200009540d62256030b0805500c00c001000380400e000c4194045030380040d090b001c035045518200309500160086212440d8001010001009500e0040e8050301d112007442c40d0507413410256020040c11070f0030041503041c0f1079004d40c9403c0030301101c0307080d2a040d200c3e1340740007002000754030360b240454070311044d01c001d00700000d0340c8403018040030070420f4401803038409003040c0c3c80d640501c0038140284500d48050f48966011940c0950318209000b0304120380c5058004001214110b8030107407003140010300b0060700f00314042140411041261081d902074450f40050b1011a946800028038003440c4e00301d02c180241e800c006204000301c402c15840c181440c00c1d1039149440000c02ca0000044c0840700e050019624001000003401d0442295a41524400d032a61300006440780c1c285400c840310200c9105d035403c0c9002c00680496000403030000c510080d40e040707582c1d0340881d40c04203090103020340300000540e4403240140605 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 542814505 1250 542813255 542813269
    0x90f0b0912070c0b1e0c010b0312030114041113080304050f0f090a05040201030914030d05070e150c0a08041d07051918051507030311041d07120f0b 65
    0xd003200004803030804102e40c031003460b81440c0e0b01c039049000c000010020307086501c15241800304c01c8a5090300342c4072004810024080c000d02c48a140c428003480e2603050016103404c1c141e0b810307030710807150f01d8411040103c24040204a40c11403004801030138400b030101e8928080c1d0a070041c20804024588441c80c010a01c141584007442d560701c0380201040034002031326054000d56100005050201d00b0703468900042c1c0040c2261000a04034003201e0406541d000030000040c03001c00700f03902c41044295a5000c04441c8000c02070075690f4800d20b611130b10361280900348090100032824005607003008017542c2d00d016803035000e9409000d081040040d41d0880f00383c6c030790402c1d030700c50a80d04015107801d0301c84c1e08500304420307503405040a2100c20051641d443d520000400d0143c100604910008003440951282a81248104800090400034010342c0c10034440d040d94103d030302044012a94001d155002c001c1250020a81001c10600410f5040140c1342d9000d24080c1c04002c400005100b08160144910 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 542815755 1250 542814505 542814523
    0x40302091314070620151f060f11070f0b0d1509060611010204142214240d060207051207080d050c09090408160f0b0901060f080d0f03090f0b09 63
    0x178610071501d4000c0c4103070301040003414000312421024559958081990300350704040b9211a52020034034010508580000d191640e406854032100151540b454074555204c0090240286110208030100030a6480101404400c0205034000c51000c00b01c00c0c80e15a80500c690003228103646500c403c000040d007110904000d0343d0311100035454a0b04000350500380c0c0400b490140c0c0600e079048510190001c030b40100d034288010030981440100440c85082e50300303520a550328400000e0030b400e958900817100c09101c031800310280c01101d084400d03840d030b100207410080050743e103405402d00d00c40a840c4800000c1040318890100c2c541c440081c80740340412244d00502ca00240b50082048103044ea42e48210b69911a80c41003a240c2d076201d1401c0e1103402d06041100003481145141075460403c064508200e10413010384000300901995814101e000d0740c2c00d071045502035000b0303601200d04580309007881107415140b418041f4004080c1d0b41c1d800c92080e070841060752000303c0b5009014142c0028081054 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 542817005 1250 542815755 542815787
    0x52406060310060807030f02030a060609140a090c02030405030d020f071a03041104020c0102040902090f030c130507180e040b162a0204110414030604080403020913140706 75
    0x4154a4020402c88a4900300d0182c101445030350300000304061310a804c4007401208642d030a54403400c1501c01b041c040c1040b40600e002240e6075440200d0341701d030383e08075401310b840e1300610b01032506141c08030b140005e190b20b040c02001c40c00100004980e07034801300310a51004195500404040c03003c41400d40c10104c0381e070000340000a1418110005e4506030b0252900142c00181c1900c45c84d400d000014000e1007416070000f10341d40040b40010b100c884941c080d201c1c2020542d41e0001e41d1142c0c000b09034840f802104001c0d80b11080a1002c0306036000caa20041c0e100310541404448200000300c0c80c0c07040d00a03a840048902c200400b040108440306958a0b0400800f5540721544841c1d484090000f14032120300c001e4010b0300100c1181081c10300f0030502c0c41190054020808041018017086080e8040d0143d4481c028403070042100d18140004d00c80c1c480c81c0c2102c285814681543d080160340354000e0650600c42c0c0a402030365020850a050101001c3c00b100c0090080516000020b064403407420142c0e5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 542818255 1250 542817005 542817007
    0x7061704030e060901120c050903070b0705060420150c010f050105060301050111070b030c0a08010f240201140f06040b0117071b060e0a0309050609030d08060d05240606 74
    0x80000707074014881004040c0c040710b01c15190301c400c40040320200003016407081d041d03080000450031580c01800074040403000382e058070141500c603600c0c03021030310a144004040340d220a00240210b44000880062440201881e2491040f0880018800010000310403d6804d0008940980c2c0310b00b449100d100c682290b800384150b40c0342c1000501035010505c2464140304202c0d41c0b85079051010700890001d01128884107850341001070603000e642d0400f180c80004940e1060000c00c0c984000c3c0740c03400448022601c500a02018111448030039510108810203640d00c9980e01d00c3d14800b05820644501c0c0300100404d40c91500900300001c0d00c1c1d070804402d052000d201d1182d612181041c80c6554001058101503c0c0219600380004070201c4e9031202500e407510380340e41e10613402d00224140d0310150080d900c2c031a4640c1c4030b40421503e4840e4a2010754140e0140203030070581409002e1855004000403d1031000803000d03240c41d805d08440e54130003450041d00d0841300100485044106801801c180c0f0b0352 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 542819505 1250 542818255 542818261
    0x615030e060621011515030e150c071401090b04061808120603120304050a030905010e030c04050c0f0d150611100b130c08090c0105190509130e070617 66
    0x305603034a00340907075110f0741c02a00b0040100454250491031081d810241c240700000d03910304003544d0316000d400e0b00800080c280001d01c0a191400203443c440e0100b40c22900041d078807148000c42d810380c48071408884070f22080001130007990b400e2040310680c6005652030b030714a152a28103070007140c0c141240b80501804604484010805070010303130711182ea40c607140c04450307228400024601601c454070301400c1c410001c1000200040490740901aa100c0e44807a04400d4807140103441c0311200700d0303000750158400a18000f01e894160401500034903440341d582c1c50090b003240f4400056201e421010180d41d120440503440e20b50300b00c00035000307100e5880c060560745103003401d060321911710100d040e44840d100c4014003038960b00c0502160034448403410400402259010161805000300c0c1d207000d46000300303004e400555018000701c03058646001050078608409400030fa45a03008001c210b50000b80c09034804580e00c2c0d40c0d1054012038100c90300148840c9190440003000e040c9400f070182140e50640040c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 542820755 1250 542819505 542819509
    0xc08010c0c0204051e041203050601020715270906050f150318070e040312200a110106030204020a2c030703200306010f0611030c07091e0615030e0606 66
    0x802424950704450200706034036035004403a4685e0f600038400c034400300d40005220800c00071403110441c005807510203100a5890400690302d90156100d402180101c00b200c49840300c4c070070041c0c25401d00005901c100c05544030f4044245901e00344e00007554207607403801d0520087c904412880d860110481d4060100121000c140e403a0740405000c1031680210500c98060151041c41303400054202c03100c0c007010900e45802c5c01415410140b500d1502249031030102d15544861114045200040440903407811003154801c0700c2c030718002c0f1000100780d50307155070100040c0d41c1c50000749261050707561000d4604408004210052803482113140005040743c03211091038030041041800c580d000b1886d070042d80c003180d42d419003080e0401c1016034140a000c00114cc1010110181010381d52942da4200340c0000043c201da5903449500760f00ca200341d105141c200502206504001c0c048030403a500400c414464540601c26100690050a03500004051242005d42d00d032080750006501400203244905081340 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 542822005 1250 542820755 542820767
    0x10504060b130b0721080a0509010c08160e0916181a3403120b090a1107080f0a0806180718180f0b030307020108070c06090b0f040c08010c 61
    0x4101c0f0301c04540400e2400034041461030154010b2240e418101d80340d40800801071401104850300404a03140c1400721380006e5051040700c030240810740340d100c000d40704d10f101e0008004d003d804c4102000941e00d070010785921956403103805601c80645050f04410000c501801c01380694901c08200a050001041503d003c0c0c0740b000319030b004480d0083c1d41d880d0f00883c2900c041d14000711983c3d04035103506869a400000b10812400745009030303aa51020a401600c690590b180100c0c200d03805544140031980ea40074a0b4068030321001d90380c0c80c05180c4181c50791150300c0c41c1c001c80e016a00d00790000c2515800c0342d070000e4a540d40322074101d44007200c4c00c031040e02010f080c1d80c02401100c00c101c64401c51340400440340546d4000f618541910615620364000441e01a12a18030282109424203460f0034140c14000151045954141c40d918000d549111044616a40c80601178456a4541c507a02020032850914140120349104040a140c501800c0540c1c3c3c16809501442043c0c1c07605400a8810707078003003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 542823255 1250 542822005 542822009
    0x302100b09061c1e08070203060a020a21020403060e0604050105010b040608010b13050a08031c0e07060825080405061035060109150806010e04020f1f020303010504060b13 75
    0x90560390703e241141c2044099400004802c02c44030a00d902c07004184500f81001e88a6103201301c0480f0342036038820001d43c0a0b130240d16003100100f02e000b16444c1c17444510001d014901481c202005051a5032070b190740b416518001116521500100c0a001c08d010083c00f0345405080d41c001045d02d01460050300038410701c3c0510903403400ca000441c01c5a0304d000001c10401c024a030040c507800d0095224040a500e030790015181c40011490b0465410481c0d44500542c0841c1b008000a4424907240c04c00c01e40b0303075000090072109109001c600211150464050191b0b5442240d0755042c951701d40351030203518064001c3c00810441c040300b00c0810030803404003803a045440c1c00802d0070289095000754900b0000300ca8168142c1801100700115030040e0f594041e441c1c644a03580b0701040560b03902222030f1246c0d400c0c0900c101d244031500004003d8242581038400010020b00207280c04120f880e20950408090140e0300c00507000000100884c0c81c1a0080300d028040c08146c1340e02c0c02c80720040b000c000080798 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 542824505 1250 542823255 542823289
    0x207170906030c18030d05180405090309041104030807050a02010e010216050f03071a0904110a0207030816050319021e0604020f1807030903021209010c0201080c04120302100b0906 79
    0x10813074031041c1c00f140001588180501199810307001c580c030141094208903418450240c138001102018a02401110b000d900c800c00603501d0255032600707102c00b420307588a0030f2910310410480040000d01c3c14009050a42c080c0e0060035040c1c21130310004102d921510700c21411540810a882200b10a0401c4d0100b101d034200c0c5c01740c0c020600c0a010030300340041030b404544003201104801c09c91100d800020286c044048608000070b0704403101c170703003030600400d5011801070740b090b0b00520020358018010200480e81c807804200c5040e0503610341d4a181e1100c00314400b4224144000c1c102d4940403c0180107526034903012042508001c0e58155a54600420180c81122000300d0516991200e03803030070001110b4002c40745140e241044014001d42540d990032001031282c150322070080f0646409840144005030f40c0c03801540aa5001159015005082e0540e050b030200000150030003800482c4046a100e50050808038071405001002ca0380f680c480140900fa4030710170884079643d584040d2071003400c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 542825755 1250 542824505 542824507
    0x905270114180f1609122d031706031006080d022a0d0f06090b0403020f0106031a1e011806050a060f0c050a0c030c030b09070501020d1b150207170906030c 68
    0x11460b00702e038500745139404150075410b0303c0a82c5091189213481c01c141301c821078560307c40c0b0612442c800c0e0b15046a4040103400203440301c12091030301e040004040d4200c0801421a00031103101c42d600d03421a06243e010b00b5169000c44540c0341c403d031f018082d4205200c0380180030007880b0409210303440c1000146e0541c510845072400b07100c08001d41055040c101d9504450304100c0c801aa02e00325400190654046d4003611501c0e40c580b68490b41409164103980d807040004980d4000d50540000c84240034000481d450480c4195090500304d00007094001c05180d50303013406030741100c2002c1040711001e8008501500c0c840200b0302005400050340c4502540c54542a4004045810441d091890921006140e241021000800e1000e540c2c8540c00b0749004507404540c0e03440d6080c150340d40d01c3d0907129030f0340582c008000111480c0d018a12620b0100551207200c1d210b01e42c1c036503512468120700102501229408110101800704509509440901034600180392803101d10000e0f0135800300400304030303216030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 542827005 1250 542825755 542825791
    0xd0c0203190c0e041217091509030c0f01061e0e0402060f0d0906020702010813330509030a1e091221110105090d0905270114180f 57
    0x101d410284001080c403a43c0c6401581002d00c1d010303958016040051001500d041810300000309003c2d6200d000705989030082001c05c110007035030848014010b12654082c04140304020380c043c41441010311001502000261981c2041c21181d42c0300300c0c5a404c40c40304208008240304840078101c0170b58011341c04035181074031941202c1e003c2c48544a181007511805040802c020701700592034014005851003601c0311001d0ba80d03440c032195102405854060721780b4005c140c07421800712020740911a09034900000000e10040415440141c0d281528140000e600019031000c80c9540f00c02503050501c00c0c2c510031566503060580060a450390ba0140746c84e55501c80118108020709803804203915240005590040350344044007524401c903840035040ea035400c10380004c882c00c2c0003003880d40b10320341c190f2952241d090411007400398160140b5941244003001c8030100d0603840c0d011411600800c2684502c0907601d00000500141c0600c01002e0b0417000c1d061028400d600070140d1080b90701c601c1c0592540018a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 542828255 1250 542827005 542827013
    0x90b0315031f062c04020d0203030903030c0609061015080603011404240b0303041707090905030c0f120a0f03090b01140a0b09090705070302010e060a0e0d0c020319 72
    0x10503108110a1400c102c03912401001510f900f041040312241240c150030b9003080310342e50852002049180401c4008200010018504030440407402030028044038101740d01200400c4c6540e00555040308264010810045d80b14800c0108503407202010020120700c1e4034090005e02c02070103c44c4403c091201020005e0000d803425400410248800b6890030b1250429040242103540c031504201055140001060344c030b0f04003406101050707100a8011031070303d8503109842221a03000d407080c03080e074040c0043c0003410700054040d000007640a40003440d92040c44501c043d20740074a1014a2400342c00446510b0620481c10058442c00c45950030840c81c038802e4548210000c00e020b13075000740041882c20010541e031b50788402c250f030440029aa034590342522512100042d001e0b0b203011035031000081c000a440300e84a0006881a180709000200740300e102040c15070308004085881d00e10380c594600310f540303001c80204103031401c036520b80c20540c0303180320300742c0200b030302c4805001c8500140003003088454108 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 542829505 1250 542828255 542828263
    0x170105011205062d040b1807030c091112010305150a0903090303141308030405040f0207051b030f030c0102030f0a0c08061905030304030501230c22030218010510090b031503 76
    0x80200010036100754501780c50701e10340324002680c0c074090400a0310403842d04d0f200c00041400c1900c1e00020054031051030003180102805c0e158807125250070051016a850502800d502400b80d03120310007a1240ca240c0b400b100b1718a041c002c2220b09a0f508080c0da05012a40003000301d801e998040c980001644000d5013121240c0c0305007040039140d2880c81130001247d000c084040c8c410ba590481d420b0207151400309207031007a0300801d00c1c0540241c010b035900c03014510b40c548408500d810041d0a40e2000906500c149080d50443c0b001e404082c0d400104024130344111045007944400c00b080100328840d2941d00080603050f00034840c5000388680c1d154140e0540080b40c6080042c0703c001c08903503480d626403600c1d9000e007400034101651064210014528000c3c00c00c2d180d0701c9070301d81d21100d605104405052850359001c0d280005590502c001d004805a110600c00e0b41154005003103900d155454142030009451b1082285d10130010300d10000d1050704d00c40000c80340c010380080d0004c0b034281d51410001e820 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 542830755 1250 542829505 542829571
    0x15240f0f181f080705041a030a120306240c0203030d060803040503011b1b11040c18050603160513150c03110109080a030e010908030117010501120506 66
    0x480900c6050034150498001082481a00000102c01400a40c0c120107844060540516861070700440424441424154030200d0707400000d40041c52440603540201e030a2844401059070740703404480f240010150940510b0000708400b10981c5ca50102c0e91102a4500c1c0d540c5400d00100070030800003409541c0e08005a071001e00b0074070020400195182c92260342c99210340704881c002c1d4200808502150701c1c2c0c049001c0346098030303103600000217070242c031070300148401030400c45103d0004c1824401c04c9e11103105201e00300806031101c2206d00f120300c0c8440c000340c006170311881c4590360810801c0091100f010101c0740c4400b0b2420f105803158120031401006020a8200e0400300d21440c07000310503d5800071032410601d001e0307114008c1452f13401c2103542c00d0f1010b8041c00340415a08200c0790307540500c0b076409600c0c400d94a1000007071650841d0346020043e4000ea115072258030760400640e207a10801c0c801c650040c9141540400389a900e95102501d581380101a02c450011085401108084241070116 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 542832005 1250 542830755 542830759
    0x6081305010c09080105060904120f050c100c11060402150d02040b032502150631020a0e0301151401090e090304030b0105011112160c0815240f0f 64
    0x2660340001005040c0c3c4031900c5400301560a000204641d8146000e140d405140c01a8514080b9181c4060988100d03044180702001c0000810013000c0c112003d115900c01e0072269007000c25881c90695008080103c04241c03444103070040da0a110050755000001070580d07001001b030b0b584490444454030024040c1d540307c07100d0904000304200c022801c000d8011100d450707541611726420140702c01280c4d00e1003212030b0701589844800220301e0724031704401400b00b1892042c404007174035494401d0f034070345000540c0b80b40c142d4a40c0104c1e000c0d03103154002d0b00e2030103c00b00c258006c2000b0810f015449000c2c43c903074400d03035162054070000d080040e449000d0071006003030b030101c1c0c4025a05003c41c09a6880d4080c2c40141c8000b0820b00c000704c0d0943c401c020100010421800401c0310024040c6101250b80c0855508036020800441c4000054004c4a40b18010001d11740036048507100207413003104d0180014519500c0c440641120401c0501304d0041010b501310a80d01100648005004a80e0402c000341c841c035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 542833255 1250 542832005 542832011
    0x21309052a03100f0f0e0a0608011803110c0a0306090204020903150402040c03020c0a031d1203030a0f05010515160602030109020c0c01030b032806330b03010608130501 74
    0x4903040354810001d50085801404031648140e0328450b003030a002c0c440c050a154405081010080c24218401c40c94007c0c000310381c0003440c1a80c03411003900311101c1c2c01002c00d29080c881c40c80c1c0e09050300888808401000e03400a00418031401000400a51403400000c1003181d6a01e55901551669419202580c40140c200c0e9902841899031150300340b0120760480c4664209003c030344106109000740c6d0403030103030b4600030154402641c1c0d09449200030889401200d003a90100000c40d40d0314140d1464600400001459680c01d15100c020103407075024901d03e020703d00303140c01000030303446820340c5810202e403170019161141d0788a04005040380d6480c4014000c0750001c000030610300d0090340101052541181201c0502d203520f0015415500c500b080d49905400c0840c2a114020109010349640c44200d40c00d201c000a0a03601c400c1103a003861000110281500d05d078004009140440740c0d8500d9207520681d8040d0b280042d0580684014041c030010400c1440219030032502c00d0f0643e494140d8004000c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 542834505 1250 542833255 542833321
    0x1206030c06090305190c0608090f0619060905090d051803120c060f07080c091f091d19020c03090a03050c0a06090806011202060c060f071202130905 65
    0x2001c2e68454041500e45010302d03416134501454a100d41104141e2003090811680c1c64a201611107901c010968040380c0900084103009000a106280c81410364a0f94102901d550480440440f01c00d034021021040c6054103100d01d207800000c8010340d0619a1402a0351202c240350854441c0b08001502e58241c4101c800d4000340400710302c05040300210300f008a85999852100399904404140c80d96800b040120000c168038a0000004026911000e04400c45150380c80960a035082c1855828000203411200107001040a1041303420903030315440031000b039034188040d90404083c0e061b01081e040540c001009801c01801344259010340b103004200c010078a42d00c0c01c155071540840300189200d513260000110340300b030149281d03400b5030b030b0200c1c0180030603805c003494a4206403070b01c1016070703120005000781942903104010141c403600c409549000c190511380e00c0035002c14490544540e6240c0140b0000f194024104400000c841c40b0f0013000c00c0b1a22440144443c507407640d1546045d942e032510310307 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 542835755 1250 542834505 542834507
    0x6030506010501030c030c1211040519140111030a0309290103260403020609010309140a12030c0e04050c04080d050301051903021c0303061203020f010c030510061206030c06 76
    0x50181260b03800c3c0c03024016041c902c18203e0844d6060010b14001c1400300701803c2020580b45e0000c50203d003c07400c003d01c0c2c241c88d440001c40c0c0c02000c146090b0111070404003800340d0607040441b000705d00d1081c00c0c84104000441080c0e516406503584101c10503070782d0070341542440000540240f0006862000c0c039030000c0705003400d012005c801d0000784d45000344410a03102020101d8860505500c07001c0e0001e080904540c00c200565010700b805604068441da0880e0101d01c01598202400051500501c44a1114a031895003030884505040603d8504000e5004441d0814401030f80c42070215000600c0342e49100e1020294041d0b030b0400313040c0d0321681c03030032004883e0084011030503100c049403d11036209005030300240311030081c04001d40000016080740742c03080b078001e1400201807007130401103401510b45000020401d40440150010790110460420650081c03050020449081c54188010f240800c0d4540001d07009205a001700100d02000a1000d20749134000d0016541c010401643e490399900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 542837005 1250 542835755 542835763
    0x3030203042c01030f060b01110a020111010f0204060203040f09060f1e0b0c070f050904050d050a020106081b1008090607050c030909010312080f1b0307021f05100509010b18060c01060305 82
    0x100d400d6031501c5101d47d980d600800f010412000d00f00c00420360303c8000c2e40115106111f840840c011592103003407001089000b4000381000d4034041d03004503290782c9044200091540998441d124851070450207009000ca440050025100c1866900b01c2c03c450034001c2124807502688002200c00000c100c602d400d00020130b64804a510300721700e40008503211405c01c0b1165200b503a00a00c55880002e0382ca90843c01500500b010350054000051200d40e91030300ea6003000c0d001030160100301080e0800d46002d280142299900b10300c580b42c2004249070044107a5550b1002074204000c0c0a00810300502010041085650008001d0070b1480d61303580d00d242a0318052498069480811488030020710a00c100100180c40b81d8104a0200f40010f2a40076111841e803016180e181140911003140d4410104050024240018a10000b03694030f00008084484003141d00094413900400c0d00400c0700d8066607041d15069580008118648000c507000201d85218030481c030840b0b5401c0c45800028004041 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 542838255 1250 542837005 542837033
    0xa062a1a18160e0703091b0303080403110f070605091903060501050102281b091a010e0a1410110a0302030903100504021c0302030f0c071e03030203042c0103 69
    0x44111000c940000ba00d100307581c440d50080a018654200008480d40d02c25007081034090b01031206162460000d036002a00da00e4039410a50100c0d4800060204040d401130b200c400c2d644020020705000007a40d411551201094401c4104000e0089041c0346982c0e20344c02550210000007040700344681c0e50346001000340909210300e42c0540030381400e001201a000b42814041034400610086840203980ca200d0f0051880214100881f0601070115160080388502519040744036400d00401c404d80000415007614485624091540902c0c10010359200c1c00c00c607001c030702040320714000310382c070019085645207005d001c4182a8420500b403107060617004001403030028400d1b42590b140c00304284581c0c0c150f40040d20001d41240381c51140121080c0c040000c5e0001520a00c1542c0c40d140c1d201d134000071140c000380d00c46281350b0801c81040020310202c9000790a0301e8858100c1391101d501d55200692a40580d20543c400255014030319105101d210702c00000d20075203e0104000395840e401e145900381049 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 542839505 1250 542838255 542838301
    0x204120b01080309090406020307050405041a040b010e0a0603020313060207030c030e0d0f06050403140310063213050604090f050901050f010626070507020a062a1a 72
    0x80c00000c681800080201d5030780c40c2c00900001c1d031a48455887c0310003540020400f000700802400086410782d0b65019180c04444050706083c6c0400042041104480048003240d050181e082d01d0600036480e420381000498010741401070720fa036644d250440880c003500e00000d100030b10024825007016001000700450754025660403020340d01c00c0e828072026004180001c0c0c015250f101003840002c8a039049164411300c6883c013200101c0c2c001c0086000d17900b040c0e03841c02603180b2500007408999802801e41028101c299100d1848510801401442401e000c1d0700300d0341c030580000c000d02c0d0a6900744103040100f00240520f6500c42d99507503c1c100810308120034442c040d061802040c600d5005001c2d42e80503002d490048030140e481c100042d518160240c00f0002240c00d50418440c80709140c0c0c6aa0b40310300510303203841d03941b2915841000b501001d5a00010700740400015484544850030214603142d1034000810440e244180c1010104042d4134508820124224400c00c403040210016851001c045 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 542840755 1250 542839505 542839523
    0x20c12061611150403200c01030c1409011b0c09020d0b0121150902040801020a020606100f0e041410090f090503090f040209090f0f1b0304020121020412 67
    0x5480300b1a031079009030001d000d5940c044520a842410075482142c0c200f81310741410789011502c030303a510038444042e500c1120145c1000c40304642d25609030060050120b5545410194800782c40b5a50801d03001d0b1607402c1d4108603402d407086204006440d580f020203034000003c080d4150307844024030702951291440080260409840d0f9400394051424138516243c002c944c3e00c00640540f100b8030003484640e158031070250700b103440000e008200b80300038005883c5002c00580d41d06030152000e89001c3c00580203070f014451108800c24080d510100c0548030080030710301421034034013070030010f00903045c403035021680d20503141c0a02c80c0380b00300510f910302120800c10003480006140184501192211074010300a600200a050900e2810150059a01c1c00c018030060404081c0c5000c40c3c0f1080040742c00095140905050210340b510303185007968420f14901ea01180600e600400c06080d0101801c001d05021f41c000d03041d035203101c3c4006c00803010741c0158011505c80c5d076118007649506d80034240940f41005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 542842005 1250 542840755 542840791
    0x1e0a06060827060f0106300b2b050114130803090321090f010c051e04120b1008060709030b0411040e0c09010803030702070323070b0903010e0d1b03020c1206 69
    0x402c0e44860b41e28248000c585450745104c07100700c40083c010074400154080d01d01440b00d4281200123000400710009c02c8000743c0e45002034a056400c43c2c068000a110a0b100035080062803c0e0791071301d015660754490341c901d440340c40b000da116217540907103410482400d18814900e00210358050f0746e1481140c44a08407407500d00544140c90803210040d02803030010348100080340100c40380080d40c0303140002c0d10040c3d03490281e880c0d407900240007035400d0440721154400103100ca00c1c01c8040100010702164006840e603030524010241050745240310007130240c011040000c051240700c4502c4400d050010300140040c8020418654071010385041d613034480d0440702e0011501400000607a441040b03103400410710366045131146410b03801140e41154207055400900031011106010420051208840c500d403512151b104060035505200301c02c0c280c40e032140c0356a580c2958405c200140c41144072140d94103c491a0408038284403050f4001c039040130b18654607240104001801501c180c81030113203011414 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 542843255 1250 542842005 542842037
    0x120f03050705031609050d030e090106090b070b06060d050103153b0f0706020c040f0c080a020c030d1406041506270504051e0a06060827060f0106 64
    0x28009565200c0066014400680c02c00070784409107441d9496810105c108643d600c0004072400c0000c50102c2c002040b00d980c6038003038101000181d000d882541080a030180c01c00c410f5104500405101034032440c440000b003007e40e15900110345195800610a111960b1641054580072a0014042c1d0205203040007a0600b117000218a2900c0c0015a030510300b00702c400b02e102c0710480d07951070710710019001c0c080f080341d102c0008004101c0141141e8002c1d2907060f01000401007100c944500c041000ca0802c60108600b0345d001c0081c652000c2c3d00d0340016150105554010b1843c003ea030b8a6038001e42c0b9143c007208080c1e210b001a20b1103201e00316028400074190b03451000c0309941b1482401c010481d840c8a0407089890640e0040030075681d10300c1c00c89026a10350014084c4e0f44252540f80c89a444000031032000400001000d50180721800305000d16450142c0081c14908020712206002c000300b01c401500a80c1c20b5040740541c1070020403541a030501c042e09444146083c41140b002c03a040c810014102 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 542844505 1250 542843255 542843261
    0x109080304121203020910170c090a0b03060102161e15020d0f09120501050f0610350411040c02010605011409120d09081b01050f03060a0b0a0201020705010506120a080c03090d120f03 80
    0x70301e2b070103441000094075040300700700395410107803180c0e043d405058010444007815140d42c0006003100f1000c038a1111250454640504c560b420207541c0c100501e860344ca005800150301c54070040d46141c00f030514844820121844002d41e0000581290006441002d104054011a010708140c6000c91010f0700c6220410540c16000e501440c0410b03414548100d101400340300c502d03d0114102c00c460301d103450a00f14501c13031100407078085540b04810401c0780d07060305040c803c041107506c1d640003c124440c2020006801c0380d224140794000542c000540c0d034881e0311a44803803460f201994003120040c442c00f01000d8a41c0e072203800303442031902c00d5821713003040449410200400c0b250181c40c3e461415140b412000285c3c0d10082445070081c90f0b08400251481b4800c1c01401003030b03400e070300040c3c4031901c0b46466400d46802825030351203644404c1d800b07058280086645510f0301d03403214800340e441d42801c401c01c0c154050f038500d05902c10700c0b2041c000e0a0100400544005030095034a8094111403603c0507011 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 542845755 1250 542844505 542844517
    0x30f1a0c041a16170405040207200301090203120c031c1d070605030403051b060a15080c0f010305090f372004020d05040c050109080304121203020910170c 68
    0x26034100e40392500c1c00b040078a84c07a4500c881d45805414900fa45610104050340d00c0003004a450781248a10001040c101c481e02d205c0c00c00d0214002d210300c900540010780d5507101c254a0b0600c3d01000601e862225104000f20b03a00007601c0c51484412800146848004100c0080045000e580300c040c08030340c00401154100688025859880c01c45d151514203c500350840013010252800503c928000c0c110200b140b00c0c85485012400306110251902c0c1002010580d80f1600c2958805040694150345520010061203003e01c2d0000342c83d9a0700c64603610b441210802e414060180c40c8484181036016405034045146c02600e0380c01da09603202940201e000e1421010780040b1003540004500c007102d40706c0c20300d40303c0d0080001d81441a4003002d8000c5074020743e41154585002c0710200159604011610000d100c0300000d181003074988000c6e580e8100504400416140da411400000980640d0540e0a1208050417a51801002a101812000407d05c580c8070340700341b81e0700252076500c074001100c107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 542847005 1250 542845755 542845777
    0x15240909060a0b281707030b01050d0501061d24031b0105090a0b0301050f04020c03030c03100f081f060503100b030102090603041b060f050301030f1a0c041a 69
    0x4980e403240242c1c002442c00100741c2d40d001070321005100b10010030341c00c440081402498040c012910b04003860300c0000c20081440d401d90030441d41040420b514100060450b141a5001100d4001600e002130042005400000018460002d40d201c1c01580383c0009201d00d04004035203030b010441703c4074401401080c0ca401307a40340c1e009078400b2840305181c1e55030000408041c10b01d2400c1000c00400107a4003407081e006070780c60340c20210040090f49001604e803c0c0c04482510708614041e07080191640341c0c072004100044865000002c0341503403515a012000074005640080d2269440340c5800ba110f0070002c6c5940036007084044506e8a19005114210484500030f0040082e03442ca00f801d000503010025050754195801c0c051b100050302d4000046d80300e5031041c00111700704003411003040301c542c030140c02c00020032004001030710741c258100c1e00300e9054a810451109407006c0620340310704a12504034a41c400c2100d00400d008402c0c0c65100508282c801c0d0030f40d464640d060508052401c0c1c01a440e0340c42c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 542848255 1250 542847005 542847013
    0x417190e010c021e15040801090611030c03010e0c07051002030402180903091e0301090c170105070e0f040b0d0b070212070c0b03090a05011401050a0e100303030c0215240909 76
    0x1007041d80300504c003485000701c090031118080c0c5003942c2608440c0c1103580300000c26510703144620100550b500c0794406040502d5a241d042d4101484401894001401040b0000f00e60f10045031346440c0c6038003a100c035107a200c0e0032988441c10882d80c400281d00140c0c2c003240600804140c0e02040840000340e244076100a000450400c83e40d841007044d0101a81c841500c4075402c5a0143c803540c0f002e01550840c00c0c042c811a150403460411a003040701c0d661032542e10243d24107014441d0640d44400c0100c10840115401044012100300160040034160691380d0305c03000304010081080384004a492040700e154003910000c01100c42d0951151080440c000c118084042c0f05100686c8600c024540102118044400c88007059403124212150326465140001040004100350b10b02042080d0203414282d54092160500724910b0b560790040f804000c040c140c0354a04441c8091081050360a030020072a1036910710304081d81e030791080080040d50043c0c081c40703504c007940440c1000714515010f803034060018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 542849505 1250 542848255 542848279
    0x50a060e011a011b29071b061104050306040318050609030a150617030c010b1f03050c090a18050a050405190f02180f010906050f0402030417190e010c02 67
    0x4407500301d8059004c4121052040c04031001c41c0f00c81d4141a80742548201001400782c0940c1c2c012400390000b4040d00410210007550383c1c2c103580700c03299048000d034890001308140d074100748554458001da40103641c151240b00100014190300036119840d0300b004128840109031174000780b044500c070344080d00c0d4250340090104400180e1b4031149500d038400301180045d41d682c44400c088900d0380440d02e1840550b2000c034907103286810a11441200000464501038003810b0060711981407141d90101c101403580e541e00003940b4180710b83c00c44200900c0100104041c070340ba8034000b05000501a51001b510f41340400098080c016449143c0c01281c108008081c20110044007100520320200c085890030300000015005842d59005405043c1c034881400c5911300e40080440c0401005030b20490000781031203410402601c0d015030314500520203840c00340c0e403540c3e1400e202000144041840d151080300046500700003c54001d082e0b801400ba51b02e01340c16200403c0111104041600c0c041d42c041411404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 542850755 1250 542849505 542849507
    0x20a0503072105030910080f1005090c0a02101b110703020114070f0203030708030403021524190b030613050c030a0f0e0d0e13050906060603040c030b0103050a060e011a01 75
    0xc500e16403041d03084924140c600c1d008600151040300c1b1600201c0c040005025041000407a041d43c8083d4440013610828a040d000030341c1d8101c080d0202842d04800680c21643c82d10a2003100480080384105120740062641e203c1c240b2417075801ca2000103018802100c1907a48085141c8081300d40507917030156900b00c251407296046e484010b04545c040e00380001900140c500344090008140180001c2e91070340740c02e080290403c5400200b080e00c3d580e8046c1084404060b400c00310101c4400c00f08400ba061502e0320106180c802040c085a48906040c1c000051030b410000c0210b00c90041644d1400003001d2040c1d0a0b028bc9505581001940800b4400981070301c04a40c04001e034490300c94800300710660b001c1d401c2c6042c0083d0106110003d080600e0070440703400c000300020524440342030300700101d00d4105586a200c05016005030310811000004c101405000d0740204061030300403a0040c1196500d1501a590b0703440e000041b0b0f440c40c2003403900f1400850600c00c0814201550620360800486000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 542852005 1250 542850755 542850809
    0xe03031311011218120c0314030a110c100e070f030303112208010b03120d050403170a06050f010306060806010c021c050714190b130e070c020a050307 66
    0x10181001038900101035200e0160241c141d1225503031220410251140c117005011448800740c0c0000e004a80d00b5400009501207641501d04002c98502c640707a40301d107480b120150010822540c1640c502066561100e507001c9000507100c1c481190800c00010341048041d10f60115206180107a41c101d0400c0011034001c2d00302034a0541810495803910800509201c8040f442c0350744814030b803082d00340500260600f40310f1105494070441c01440100400c0307803007140174840c0441289060b926800030808250050403461a510502078054070f0501e04107041c2c100034047da03c00d8a00c5504207000550071035000f07120b0b62090318047e40e18010700d60b45440040d5440c005c904012a044001c00380c1400d410070001c5504505140700e140540b019515041d44050040445074205100d49441c41250550107140100d010840f211801810380f100d5002c41d6006040c0d815500c00751002031002c0410070283d92041c10300d07058a05c22140f10500c1600c4030181130b43c0780c5160041402c1d100041c1300314809188451 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 542853255 1250 542852005 542852033
    0x120c0302040902030a0207020108060406050a170f0f0d09050108102105030d02040e01051c030c030e0a031a0915180c030f0114090a050307021c0606031101030e030313 73
    0x104000d0700d840ea60707489110480c0d10403102040c210754003003100400c44d03a00090146d009a001c580070300100f82040c0c006a628090f522881f0880000f030b200801d1100d90070300110800e8070709441510007026070210002d0300e50074420381c010300080c41c0e4200801d466000c0d1943c94014a1002d50400c2120f0074811240110300601000310002855090386000141c0c1c00c20050803401c05050000d41c41c0c0345440080c1420030410317005240304400f4035445450240c0302809000300300741c142c54804180000750800f550703030340343d40c140d017035040410b070350010061148056418120304000781c0b07107503020b90f41c11416a80b20564001001460360300d80740424016218403540c02c1800e5106000d541d4080c6800d00001e1409410000c4502640d458002424502d0f0b103032060940e0040c0e10310050210801c5a40d00d241d101d1252140003441100061070300001c0006c0710208860282e400b41e410082d070b980b03070f050428004240f0780f00a40004c0c104074546c8041d25010056900030300c402075400b807400d45180d451502a804070307 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 542854505 1250 542853255 542853257
    0x108030408120912060c041401090b12040f0f0f0b0c0903071509050d060e1e0d0c1707030e120a030e21100506010f050708030f0438070201060303120c 66
    0x82c0000b560703134241402944d00071011482480d680d035150020051340400140b030340d00d0500042c81030800a4050f2007040b1804000801d1801504c1e40e26450004015207040401418011204e680c401c1004070409600041324001c3d10804a55594040c0007840e92080d001010b4040c0c001c0c000402c0f04805100c030001c24a101402d00d4503019484601140c900301aa501c1964a075444a02050308500148030000045c045a0140140100c080c070f0351a0742d90440711060001c00208488610501c6601255002551082c2010719031300c41d41e500b8001c102080c555401480341c00b02c0c2c4c03101c3c1920a000500400b00350780c19141c54004100c143c042004000010304030500f8003914038003104d9903003002c3c4100c1c40e500500300b4000855041040006114900301c3c00064103014040040e040030078255401c0ea41e1004c003011401810b82c0d01c1d0300c3e1210407010664a140d001d0420700ca003940c0070300315030100301d0a071584800103101107507130381413041b4280e6002d440b018011800309002d1480c8102c90307030805101d820103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 542855755 1250 542854505 542854519
    0x51207030609020a0815010504080304060503070918020c010b120a170c03070f26090906040b03010c030225080a050c0a0b0c0a110c030c040b041b08090601080304081209 74
    0x1540720710a0580c0d100c0c41000d00000c117484100055410100c0074594000c0c4280b074214103040c1080d0b0a19900d120b507000d1403060007400310001e080c1d030b4072604422002e0022007026844074a0314141c0b4201a401c50b40e1480851f500700070340d040542c100100c08035140c0030100c0084c11b114030b1030b884d20ba0003808c0c4410040c80408003088a4130301d5403030410061982c50b1040340602a0035280c0d050104600303180d1355484000700c28014406054007510825918091001c4425402c15200c0e070002600911008504075095400c06041800f500c2c4c03d034dc0917040ea10342c00030811403032825540b1120480c071450b900c01021500c06211036140780740710ba4040c10f0100c0d81c40c4100c0b0280240c0351107481c2c40d41c1c3c049402196100c0b00182c51a0f415620081c01c05041c90760700010304114800400081e110034004201c5802603998a402040940c2e0300e81080310580054800c0404215100c8070040c1000c004035100d40c02440341000000d64204008101c03800c0384c03144000b80030400306200c0d2140301d81c2e128403c0c013584001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 542857005 1250 542855755 542855759
    0x70504020301140108151f020a0b04080405010e0111060a09140709050a0b0303160b090a0b0f04031812020d0f061d010c0320280e030106050603070512070306 69
    0x1240d10007076028000288040600e0300c00034000502240008000302e0340150301414800740c903100e01c9400e46075040d0390031902c681801001e000301e1401c4c1c0b8480c2d01402004150080c4014494290020429a41c013030ba034039151040030b00d005607008001808100010742c020030008000441e107034840700e91188140900c0059901960301310f460004183c100007041c995076018400c05010300d10074440e401c00d080d4051801c2c10380d003034640ca585055402010b040b07209890001005040103101c100c600c907a006120242c141460014180182d004442c1200856004102d101c0900041007541080380c1484100794140c47c49030b0b080c4451418000740403540c1006840340c800002e881070007584000c00c0490b80f0035203540203240081d800d458803d4002d106161030700c1c41c10041182e04001e1200100039441d6400e80d84d8250b42c1407900040480c4448100311641502003100c2d050b0b020900c5480920218001d1061a480d0800c116040c402603840001050781046420b0045104050071903000180d0f0900240f015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 542858255 1250 542857005 542857009
    0x110406051803031303030e0316032003160602010e0f0609030a0c03051c0207020a09051905090c04060e090106090b09060d050f100905150f2a04032d05031b0705 70
    0x44c01d60f002100401d0050082d40a1401c041080f5410780141c254881c4c8100d1451700c0390ba500e0305500d4030302c0030a00202000c00c070140d00c0c100010385030541e101c08541d808580e6410b0003402040d041d1624034a074003401c0e0940f00040c0380081c3d00c83c010007400c1c020750714181e2619800e031100c0001c000102c052100501160f29601021007080c844121032031005644c806403441003015480c415088415090710b4041440944a243d1103d5016405607850004003912007011651404c004000407546c014185400441d81c21011141c42e070142c00420000d008280c0c480b10031905480094041c1c58000c1250800102e5514101e001c1c041824055400c0d03941c050050391444d424000f10b84102d107605621078000104021007040804213a202c4801811120700780100351006010300a881441e918204220010007250707202d64080c244403800510654032540c0e07203441001010492507414010242d11041e07420640490303001201c441e40980170b94070f4447d411501740d003c518001420211481601e00108241d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 542859505 1250 542858255 542858287
    0x1050a110a0c030606060f181e15030204080f0606030c0f01120c0e100903020a060c1a1608090d090e0903040b0d021206030d080f06060d0515010311040605180303 71
    0x14500130200400c1c80c90500c040541032540d030000300402c00c8640018441854211071b810301c25504041b4140d4034090690540082c103105642100326501d0041c0d1582004540550042c412180d0070000d4401d4580b4000c00b15854420490715540c02d9040303c0c484942c180380400e00038891100c1414130380318030302000c0d00c0d400840b131a80f055680400c207031075241030a40c500308019560029042c136060016a046078081032980d40035204100034005800503103030420444482003c100040184141e499107010102c04940b40302880908021405840200e503800c04c01040d503c02c0041c3c02d40701c5140140c60985c045940342d5004044150740e000a010124017400f0040081281207640d803000b41c0c8412103034208000c0140c007d80000d100c0c0e4015000041c40c075801c00e801c01da026908401c01c13507855441c000461003a109a103401c80800303140a00300811a1442020050020b00c20fa034100301200750401d90403414422030156902080c014400a03401413034080ea447d140c3c040141c2901d0419945042c48485 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 542860755 1250 542859505 542859509
    0x10180b0708070e0301091e030309120206010e0c0313030e0a08070e160809100e010204030204020f1207030203070c0f020a032f040515040e0c060c0f1b01050a110a0c 72
    0x7424000034490780c60b501030400c1c243e50b00c04800800148443c3d6645220751484591483c0144c50071801c40400e06000750f0005c8000da0704042c0845151031080c000a40740c600900800c401d801e019004101101c1150b0107403031046440704c1d00e1345034103082500c040c0c078008450380c01181d0000c901c41000c200d40205003c5500140342803994090503040c2a8590040c600c45207030500104000201041a000700025080141c50100d0400045241d010390000b0302900c00d5804c0a900280000381c10b00482d80c40300000c0842513040c44504a458483c0c4070100c090303101c26584003001821444101002c2425200010451403006101a2505a5994810882d1a4425a210300c015106008120540482d541540f1503075130031a02045039107405509116000d0100d40110b001c1c43e0707181c9401807000420000044240340c01885261160201442569031340500c0c100f0021900441c0003030b15403051480b0281c141024161502800d10018110445503501c0e01032030311066101d0f20340230b40007242c1340301c00303400c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 542862005 1250 542860755 542860757
    0x10608010905100507080c0d060308120712060b0406200f03070b0912040605030a021201080c24030a0b0607290106020c152a030a0806011110180b07 65
    0x7580d02080c0c103006041410702d8541490075401c3c08100401c1542c40524070f40c1c001e800907465500c1d81400d400310002484c1d640c100030a2681c00140f945000b40e64460b0080c407500c184c0e910b240c021425549458291991417140031400c07a014007080c00f440b4090b580f10488178030b942030340c9a44514000a42860041d04280c10701c0755400019a40060044c002500c1c0e60151a000041c180c0b4100708601113100c0c031851003002d00308000030012800b060041d07011640042d01d4405030680d1540c4561b01192613004119a03c0d1040c0c04401740340b02685107441440d4020085d01090341d0865803681e084501074801801e000c2c0c0c1c421000c020400001e0b0758148040848070b42d40385540f00c5600c620410007103621703040c1c00c078500b503501500e20119240c0e00c819980c10703200744070740303d40d0b44a140c0e80e88201c5030100c0080074911010045071360865040030010140c40f80b01900c0e035034130440351074007801034801c490079400074212504940281d00144005030080420301d9401101a05036268a4076606403010701518410 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 542863255 1250 542862005 542862011
    0x20a030209280e010b040e04020f0d030f03050718120503070b0c12070309051c0e27060a0807031101210e0f0102090a03030e0a090903050c010f140c071401060801 71
    0x1c00072004501d0808080c0490483c0d5080550409050810714080e520032400c04100c0c0b00000317400c40d12900b050381c03140403000c0c081488101043c5009003041c1c82c041c82a0000901e06030006201d98403490b510041d043c10680103420407402d00e08070710300a40c8000300544941c441040f0a80004848103001da115801198901e600c500141e51f50307a08440d40a007110040500b00824440130074004a600b1403000c42145c4c00c1c401441c00c402d0f0079603004002038182c80e4460912102201c29019241600a26907403500800c40d065480c4000c11880f003485005050700e50b03120706802d00004002416100b00b4100c141001d4400c40384004049140704c3c051004e078101161100580881503108210880800409000960070700d0341000219002204030f01c006000c0007406040c4402075120565404042d0042c400203120a001c541000707002d641c4940795440c0b0300c3d883d20100321150101d0384503800c0b65000a0070a40740035101d001d01a17180341c00101d002c0e92141542000220a544240301d07a00080580750008 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 542864505 1250 542863255 542863309
    0x150403030f050103020f040f11160201030b030106060212030901060f060c1b0614070201110114100b09060a0e031e0715030902090f2815051e04020a030209 68
    0xc003618029600000d20780c2c1090018070050f5038012401c40d18000903100040c08110042410f800b419110030b50900f07000f4005000c45c0e2844521405064a5001380c90600c41e5401d10703400d05080303030101e1141c0e10058201420903140c02842c00700554218450f82c0002c544240c49241c06c2ca04600140d12100201e42e045240f081044038075100b00010030312400c8441c8441d0f10340b040150141c20f1195080c100084005504002c5a0260243c4a20581e00d10000c11201c822a40034117461541550385013410402e480001a000000c0004c07903501000c003422650600e100740c58140c1d442640d10000aa060068800c10711003414030309516000140d01c040149000303480d0001c0b8800f030191282d501c0080505203285200507072588003140f50445000c01d448041030f550040910711610649174210002042509503095003281a0400314200250a403c200301a94a400b044043c8141d2a08005240702c83c40001c680c501d000d81c090000b4000d281000762404800030f0015140b0014a12190640c264032144 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 542865755 1250 542864505 542864507
    0x61602060d14072a1106070b0a0501330e0f090405010c03051609030b0603120c010c08070305060f040e0c030d02070801050709031e0f02046008150403 66
    0x40003280042001103c01c00c000c608085a1301050052010b016842c0d003c000803615251681161506508021035640600b00100948082c12081c0301c0c010700c0540c1c1144000700030720f500d40c5040c0245100344104000500c04201510500c8950704508c4d0b100f2005040815641c942c00040d131304c00d910070400054848454074002d0202da80150000c1c0082d56982400106103410091601c140c1ea0011001c3c0701c5580c400000038540140c0854070a00e64802042c401c04400d0150400783c01c0a0450700c40034442e541d4408220111041200d4595000002c50380c1c5444074209580074a00c480c00600544050b188058080f03440c100c440c600030720042c2c2c04000c04003c15102071060640081507441c0592043d49540c0755188410f26041c034030314501d0600c86c03201007006880b518201f0110750207003091100c14240e002c6296a04c41480e5042c400401c941c9044450002814409a000504500c00e0800045490a4200c40c03120540519103896561314041103e803420440c8841400700c6684218443c607023450 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 542867005 1250 542865755 542865767
    0x12061311120604032c131104030507060206010506031e04171306090b490608160513020a0e0310090c1203020d0509010e0a080607030b03030702061602060d1407 70
    0x1180c060b0202401c00c40340042403403400c02e1905c103408550310114004140e00040c001d090b040f14a070401800018000200000840c4d80b40c00c603041c580988030b140c0c2e6a807007030003214841191130149080380c201c174424501d03407580340040c0c1090042a20880e000310100100c01607500440705c2c1c00b4044900301d0304000301ca03440b402c6c580140022030080c50400c030403aa45d03011300725454031003e52181c03115500e2000c4644d0710306401040c42e402008110380001111a944010032460191300543d01403803003003240c010802c0202d401281c0d809029001c1600c20007082c140203420038202d480c10458140541035a0343d40420400b403500180040000342d0b06218030b800110b0010b103902400c55051140c080b4000319801040d80e801e010a541400750380c1c0c220b4076004a59005183d09010f910488591010644034800107010748101c40a4404001501d000c10815680703018000e4029444201081800504074202815464203480500028204960020a08113482d28109401e03002c01a6800300144168080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 542868255 1250 542867005 542867027
    0x628090504060911030402240d0518010c170c09090405070510020d02030d050709150801060809191b050a030f03080c18010e2106151206131112060403 66
    0x4030301000251080d940d0b04c4407900008201030b2084100b078001d400d01860115110102215159801c0c4e0744070600030402000f0315094500d620040703480030300300c0d025040503c142c015460850700c0300701040c680701d0120200780700b00038045e06008000f400010300b142c07a02c0e00700900451049001d01101d60400051203016440382148504551021a2141c0840c1d00031049a10110102070041810341c1e488400303491040301540085502d407100b40c0c1030400f0641c0002818140c8600380e40d1801c00f52191042c0559915008458168207040b0b60311007800600d110300c176a03c1620f40c0030300003061542c0c0d44d00001d0444031107600c1038aa03c0c580740c50a60070540d0154585a01c4007500302001d042c69240640540291f81c0e0705078003414881d8501712100c0c0d80e65103808511402000c050709074450030741030041303644070300301500c002c40b0f892001c1d95a00310a00d0039400d4185203110346001440555102d1558044880030210305490346140c0499008a41d12018400341c44001c0f500000d007140e0800d868000e11401e405 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 542869505 1250 542868255 542868269
    0x20f1606181703040501091401050901050c130b180d05030c060a060b030c071b06020d08010801090b07080c1204060902091302030c28060c0507060806030309062809050406 75
    0x20042650001c2c0b110744001c1c400264414070141c03669280d180c21801040b40100241c11350b140c46c0d80c400050101500302030b105802c1c101c0280925100e80320000254080c4240c4070032012607e00d810302c00104044044d00c40607400500c00700700c0441900c0800d80707281c280541a15030b5040042e02440070340c400c00045400282c00d90080100504c0e160050085001c040c1280ca1a900009051400d124600c0c02c2142d2030b0b01d10445031141c581e91450080d6a500c0d00300b10740400714500b040009140941072080b81440c40d000030050031140c1c0c1340941141c881c8070003041e03112907503414412507000c40041004584201c1c03250f40002101d01c2d60b80100024014000d100e550b0440c50241707094010b840100361518464000e0f075040981003d4122050410312000707213000098151803000050095008201c42c4001e07008105030f8490070345402d011110b61404844460b0550b2040100040a041c484010403c605100d0041008002c00090991000c06250f0b03c0c0c030002280d084080c072881c1340c03a11902c00141070b5 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 542870755 1250 542869505 542869541
    0x270816060903081207051c02130602030c0604031b050604110a080c150313150903110303160e01090e0703090c051002100f0216050102190e0d0213020f1606 68
    0x5550b0700c1c03090611880154006401300180401c0056000d003042d140420704200384d207201c00041982d2040250050280c4451800c0c00c51000601140080100c6820072046070203401540e40340c0e2002d846606104000b8103000d082c1d0105000802c1c010300429010700c2c41454040c42400c1d40c90104442215160000989a0030140344552241e8a090060200c0200f0079415610b0b56a403403c8c2916210940b8409400040c0d100d0142e01d2403003c0394400000144030751100c2003090b0864003010340c1d03804102c8407070740d14410680b2207040950050480d0360b030904051600041c0301c0d491307550910700c251040c3c40c01404039480d101810100300e41c4010302d801820b0190f07a281c801c200c003104000c0d0758408481641e900303c0e81e640d100c02400c005a404407050209612000d6034501d420b841c2c124002d40c0440c000c2003080d241221b0303010010703100e080d00c22001074004100b07982042d0a0307020024040e00c600c0b01e050400e58204000ca021310318040140580c0003c030300301d208510304c1c607080400586120f03200036000040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 542872005 1250 542870755 542870759
    0x130204110c150c0d0c050309070905061021091103060903030c0405060310050909250e0a0c120c050d0e0d1e091d010510090302030c012708160609 64
    0x20001800401031010141001050b40b203e0029120fa8802c021000c030044e4140700140310001c0e0004021400f80d01208122400300d80d4804480044038010386a03682d020050320f548039200b91003070301a003059084003e060301e05828960051012504c0c0600100d0b004208003c010b00c25140a12400d5800102e2601462a5103004043c2190521070340c05000d00c26400800424132030070540002d60041e1402600745c10040c1000700509a48160103071000391415018940d00003061009508103013125801c01181840b42c4818410802501d11000b00c0c2040104402596240b400d040c060307800c8401c01ca03100d042d80e80c10948420000c0d1100f500d50b0084035030003602c480510591001243c4030311640300c48854108000c4020403207000c90203a000103040800510005150040301d81c00e581260000c8460601040444106985190092002940c1a04200e045002e03950051840071241200c1e200714101c1403501d8270b0b0348812051207401200c00d41c2d0200324045601409645000042d200314241111018 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 542873255 1250 542872005 542872027
    0x4062706121424010c110411120a3905090607020a03060606020111040e07110a060e03030a0f0903090306050901020f03010b07050601050a27021b0a03090501030b0f091302060313020411 81
    0x100340d1b403800700d014513075400440c04d8000e1030105032a10003c402080c0b0005082c00340031310010385400701c1c0049280b011145c0c3c920070211003040c0100b8020360f81450400441001c4415150380d08084903440d00701c9400c006a40050340c503071010001a601c104400204903040c403500030f084170403101d041031482c5400c000078480c180d2685101d50344110359182c14080d0030304114030f8500385810320b90014822410b05032902d074005004405544180400b080800c0041200080c01d4180e030480700d806030104106660510201e41c15400c0f06070700c180040d0000d407504040e007001110030f520903408540c1184000ca440d004108082c0041c0e4014801102c2c055005800c01c0459002c45100c0c0141c0c0801e0382e00440800c580400540544a01e0700070229103612075409559103a40fa0742d0304103421000510508400324243d8001d1040c00001c1c0030161802e402d11a204061160540002c0d04160203c11805021401a81d0f048005c51150103032919051a0b10000d20500064800321035550315103030402c0c040302c1d02d89 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 542874505 1250 542873255 542873273
    0x803130e010603060f030f020117070f08070504230105160803010e01090203061e0f090c090916020307081b160f090b06070f030306051504062706121424010c 69
    0xe0307600702c0c7c2800b8800c84103200584404084800564540b4203030001c020b90306801084e010070100351a1110f0801e661080e40490f02031080d80103c94249111240c024898282503495445507241030500c1c41c502007c144c0e0004140903407120440c0ca681b4004014464222002e1100b8018140301101b50706609001d00002e0810b41c5c04070900306480151b8080108540e40c00c6004000d01c0400b811a03406424641000802d03940007026140c091144d01f0045920100c0a01d2410341d2540f41c0c1e400f41d801c04100d952200c00f903074450310010380c580c000c0e185072007043c02060001d000d1030390401240c01100c0f46440b02c034058440503640005850340c98100030010b1a165030040740d80040d44240c04002c003800c1850294020b28540c2c00040e0050119502d0640d06e60214006006450040d200c9100001511b81211080200140114602d414420742009928050408403101801c9514007040b00419440da03d201d102c001c907803840f1034815021508070b10143ca200e0300c0c56000030038a001a5a01099100e10b000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 542875755 1250 542874505 542874509
    0x1802090a0504110f0f160309050f090f060f030106030c090e07080c0109060c0213050412120e07090527031810170703110705060709121a060a0803130e010603060f 71
    0x15000001c2c217100380c40303601070803038200e0300482c1c00a41100717016007030041100020340a0380340260500304c1500424527014550500c500300c08403040301c44d59940c0f800d100790708287c10b080c55019034030b4540200c001680d4a40c02ca014202000000809030040e84403240b0307000c203c0d44681c06640002883d41e2150740d02c40401d0080c1d034418203000f502c010241c03000c038541070704c809140540186824148000c00c280c00350240315060380f960303402040600c681688801c65514942101d002c0d8807481c0108506960f43e0030103548208044070a554807142103103090005000d011420744660000913411403011509419280a03c03000e8a180b9201d405036080581280c8800c082010440102c034005003c4c64400c0d004121903030980044151188428a002691400e00780c805c1008038514101c081207903251698050880c9400420110302c401c0c12080c00d0b0317248400644a242c000d450200c1c04100071200f000207103918800c1c842c1c40200645000c40c0301c0b41d07841041e0844c44c101810210300b0000c0306250303021002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 542877005 1250 542875755 542875777
    0x7050105040f0e040809030d020c04111213020315130c09021602010c05010e0304030305040302031005040503030a090c170607031506050a031104170d0e0402070f1b1802090a050411 79
    0x43c10b902ca43c24901c07514098524080d0741031080c9115003a40c15804100d070002080143c41c180f040c045030091b0149035020703024840d5900340c042030010700005d1010300170011680c000303425101e101510005a45100c4011580c51004250003002801040f462000e00310007004468000c50401070200886401161a540f01a0422040322404c50502c1020340c0003000f80601c460807a503549030380e8600a44150050f20007a0700c20302504040255001c00350013101e105a600c4005145940d0b44c101c408030040c4014001a11822152100070860345907044440c8035092051009044c54a8400002400d4418048500350116a80c035400c0001942180c141c801260241c10045112107172142c2c2d800650141e03900440c4901d443d00a2940192404075918420400e142e4a522202422205200c02d03032041c1d0400800d022103401106001c280b5420030803000c2c0c007515100d01550f5544002d407440c2e40150f003000302c4020307a000074a0065464406010310003448241e906010012001c0ca00300e207507024800c1031031 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 542878255 1250 542877005 542877029
    0x30f0803090c090609070e030f03033603031308090604090905100b0a1214030f070201020601090203010f051516050f070f0f0618030c080c1c11100e04020304060b0307050105040f 78
    0x203541e81403222690009c011421039489203010340b085010804420701e0681c501001c0310307520003800048800303060f50901c01001503141d03840e665805150458143c0c8151004070b01840070300907550b02e00c40100700a00e00200c6c01300e8070b11100e00380305081c4101401d210740d5552501000060540718410340c90100d076242e40c0107550121650520102c503403890b003240e10085c040058002110038405019007810380c000c1c2d0880300340c1c3e031b2144041070407444203015030805040150700400c0b0b51319180241151210242184500380103601341076103901a945801180c07986c10003006608126020030039400104040c0d0b000b100424074280c0d5048104225004000030885c03081c00c0c9820050280003e000110751084080c001d035683c4198160311110b80c2c13441507224840c1002e502120029005048545681041328003a04103941010089181601c5010340180882e480b40c0018994075803018510403405400086000003c010401d820034035280c200310305001d0107001c180700504850361200c2c161603000080d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 542879505 1250 542878255 542878277
    0x604021c020f04020d02041a03070207060f0e0f010504050415030203240a0b0103060e0405060f10081b0103060f08030c062815090f020c1b100302030a0204030f0803090c09060907 78
    0x82c0d01070322130340c0c124543d030148d84408180e102101000035031240d10b1030ba0988071341545419003100c6a180030320135000052020307881c0d40038a00d0030701c16000004805040880c078080d034032400f0a0668a2035000403588513800881081541428001c51441424620840120b80301d100c0700309071203c2018001d15240b80c0d80d17a49015159010398450000340499084000f2540ba081c034080e48d8031324003181c1595400803071001003540703002c91b41d19003070544c0d140c0d2010701280c4a0303500e103008460b002e09620b1410191250b070005960241081e82102034844a8040c65695086500e4a4a0210080c14404400c8201520041c00700d01711116404240d48204001c25400b500412440c61102c82c0d030014055a4642680480002c5003503000344401030030007054a008812555203918000407164859805c0f00b800c1421088081c80390340115402a20800e00500b41a1651504041c3d000303060340c101c410302000028021120010451070f03c40300c4040340c00d00700d00c0c03800c6008114159400b400c1201400004141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 542880755 1250 542879505 542879527
    0x1030209010c0b13050118060c0315030b0912030703090b0906131e0605070c0302010e060106140c100603030327080910024e0f0f040e01080604021c020f0402 69
    0x40c4c039540e644c01c03030000c0c0860501698141e404240c2d502d8100d60345450300c01003640c0325020b4024015101035004aa19980303140d03880f40000d94100505107441c5010784442c003012100858099070050710980c2d40018502c0e403524008407140c030058502852548040100031b075014207100e10030f080303d0707000841105520045010b04c0025015a50080120742000108081c590b0700c1864520100c2c040e900078003600155003100da88602003070140d40c0c0020305c8140134070450100c004c0144580180481143c2c078800d501c0038040c048420a420440000f80c41c0c180802162003841003e2040ba00041c0c4007080d0300100c0d81d164000341c0304a2041600a109800701210024001d20450000040303000102d014180155444242c240c6140384004401d4142051099003040c0c15523200f01e9142d65410f000d02e042c0c0d4685119620383c0140201c0040e0000400c00410f460707101c0078005000708030550080c10a4105407042140301920b044102c4100c030311201035000561b1f28518a80d41401c1c00751001a5031f420b000310 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 542882005 1250 542880755 542880781
    0xc03020f01050403050904050601030209030c0405100b0c0303041b080a120909021201030611120f1320030607030b091b0f07110906040605030a08090415060c03090501030209010c0b 79
    0x400e1070351a00e81084189500b140c0200385240c0e0407201049107981d000e0064040313005da9036585405a03c030b2000c2090509040d4001c5070001c00f100310403800980d480c0e02038613050380418040d19160b0004814401001a07000d02c501040e0001038200304440e0030040100c4e41c0304140180900280c24101580070014010b000307140c0a0044590190b50381c540c8a13484202c108020f10045480a28081d034411403070035008180d42d12000c0280180c54207417505508090404809044041600c1c00c0840480024101a0444170070181c1440741001c03c929101c1018100040144418145810141c5400190752003c039007540c000064010303128040c0500042c03040780c1c02400000c0c00d6001c03000580d84140000580440a0b41400300c80d000316070750710300307042c001039031780b06d10540d9095809140500001038030800030f4030005038081c100060000404044200012140e40920081480140d01d0b4040c1940040a14040c0500b82030a51030072844400003440071101e0000600302140c50030100701036420541d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 542883255 1250 542882005 542882023
    0x30112060e03250506101521020a27060903080904060819050c01090b030c0a031b02070806060406030b040b1b0d0b0319030e1207090f0c0813080301030803040812270705100c0302 78
    0x200c1151596440301e00907100c0581ca02f00340c031020100480b500301c40300c642c144400c10784c0e541c9d540302c0d030181d071440e80c401d482c5030852905c00d81c0c41602e0303482c0031860304402c025a0803031242500f04c0c03404405d86400c05604014105c0d200c18100b00b2405e005100c504101c200300c9400c041100041e0f944d038054043c084006100f64001040d12901500c1035040541d400076641d019600c03d642560840c0d1620403c11080300e0082c40000c000e504004001008180c090042c0c9070b00507200320034102d400c82a1461001c0f03a500c140f905c052040e68840000c08541420031039655444040a61914030188948005d0017400b480420355104800c0d8a02444040d0402e0050a0080920b2a018410460611800006011301401d007500203040080080c2c0303c1518010400e50613500b0001c0e251030760b401c41d210350507035a000034420348805038108842c6036880d095100062041c43d0360001c05403d200801046e50b5030542c84a00f001041d4014030b828450399070707120103044a201241c01d0070600071a2074602a401d202d120 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 542884505 1250 542883255 542883317
    0x9060c1215030f16081c0305040203030d020301090515030c010c14120c0c100f0c030e010512133f020f100603021005030112060e032505061015 63
    0x10000ca083c410000102d0620011424240b0380c60542c86004840c3c0e24585c21018442245408001d00d560074081d0740f1158010740007a06482c6420a141c441c102030740c1c401e90285120076a95820824548030500442c417020070101e010346000200346000070301c003600e020006001083c0243c9852040d502c100800b0071070701e100344282d0380c035009039a42003a03c40000c040c2240c040c8484d40307494006103100e0030742544801a16100c0c107085040a442c00c503854034500c42c090741400320412074000e2607400301c0d0046100340c0600e01500b10706101443c1080500c0c1604641010051085c150208480444407408070100300c80c1604070001054440300b2031a260307901c0a040120b000754036000b1348068040d002901542d009403005035010003c1202142d80384400d1080c03c40c000d01401202002545a80010310000d442004580c1000b01308211551000d2003000004441c1c40c03040c920000f0468148001c82d4845200c002800c140b524048022410050340e04c058001c010307168290b18001066100c441500c1140c1c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 542885755 1250 542884505 542884513
    0x120806130f0b0d0c1509031214090a08060403030b0103021801081504180c05090c040b0903010e060a141806040b09010906090309050405150604050d0203010b2709060c121503 76
    0x6542041e41080d1311a01544005001200008100b5401403002d030007242e5009100d80212190a0030480c0d0403100b101d2190340c840c0d010410320b8002e99036101c503800500742d0b901c0a0b001da401d2501c3c0103812285c05440700e5040c5401842081c908100c545034601c11882c083c2400e190a039540c3d07541c46928080c06134042d520a14218032000c1420b10210407200d004c0c8954609181d0035128010400c0c0d280085a503a00d80c5042000305122000d00c4801810b51108050000324510b0252008542041d2040701c0000c00140d490076010641206070181640181032404100f02e102d1504614075100e00c070081c07010b044401c40501042c08403000b58460b40b629078008004210350402c0d454020f022211610480d48194200300106540512802c0c4070543c1000040080e803030245418103210f62080044c03010f90381956241e040501c144c4480f0072220007501d0400c5a1440c0000c007031003000b0400c03009071628289500c0701007000300da007a01c1011294854032411100b603980d0395440b84060769150542040e505409 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 542887005 1250 542885755 542885779
    0x709050a050f0c0c060a0b0d060501080c04110c031e07060f230717070522081c080a020f04090207060e010509010c021207030e060406020a120806130f0b 67
    0x40c0c1507018500801140820000030b442d440c0b00b29030300d40a034402581d555001400400c18000c0240e00500180d44080c0c8001c521078280d880e000c0844400760f120142a40040400880030300d0140b2859441c00c221140c4c2d503003446411100507070307680a5240b40040d2402d1400d81140300400794004c0c2d40401750710640c14410b0303240d109911000f81868409a00c0381181000c61006440d02002d1040d101e40b089079103c90b81e2010714440001401c20180002050017170402c0b040c00c040303241e0040c0b030940806029070000b20b20f141c004e8241c54080f00040814000e1442c2c0e60490f4a10343c041803254000403250409a2194858450500144110781c84500110705c001000020856260041d41045d00d0030802000705940716510306080e9054140c40400680082d0b81c0c0c03c0c450a05e140242034001e000c3c0c946112070a051101145081c0e120b5000000580e1080c0000002c101d40324028020000c2586028213550904401244545407582d20341001541c40302850400148150b01003138001c0801000703200565 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 542888255 1250 542887005 542887021
    0x60c03091b0305060105120a062012180325020402040902070f020a14030d180503060f090f030a09031401150b0705060c0f0919050312030a0e0106080c0d0203070905 72
    0x80c11480116554000c1c913000107410b00c0c00081050a41e82c44002501000480e6501c3c1401400c0010403200c0380c041790461034600b454090f015003020040d50f2400001030910358124810b4416400409150794810803403015011060008a0564443e058a080341100c07284005800703805160811481684081217420a00071700124140700203000b95840c00e0820388520880c400c440000e044103405a001d2134a20801d24801d01b200c09103254090a0700307690035140c2002034203218080e40da600c040b086110a01c43c8a1400748025000011150001d510b01000c0a00192000c0300750311024001e00c880c044403c2c1000d03c00e400c60000c40f5200072400382023584a01c07038000b05810000b42070300d0138071500340018000100c0c2c1c800c94186084200901e800d00f010b200c100640900382aa51182c0545401000541c0303490421681442c200c2c4081400e84900c2c0c00003103503044801014109034203a050070420001030f100421011410603068401107503074195800443e284c8010395000700c114a260008003d004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 542889505 1250 542888255 542888303
    0x181909080315010201290f09070c030f090e0c0714070f082a04020c032b05360c221103041e0f0b13020a05060f07060c0309 54
    0x88030030140350520781c00098012400c880110512075040381b140001e80d0000380e4945071510590500070000d4003080b001d40701240c104603042d10303910085460450114201500300b50558542116403914446041c5490591611701d47d0181c022562a00c00044e040b00b44444c80c0000d041104843c4211803950390745903079441054005105500150042c081890b11490070f4280443c0b20a01c005001c40340040c00000b0400298002081e88203a0311080154000c55148920b11110199810b03000d040042e4003074040700e0540d8001809100b1109006416514082d0180b0700c2080e081c10b1307089240e00301c0e0b448401640c5041c540c40c5105030f224455038101580200c0b446c000007110250360704144014a0402680401c0c1d02090350020030346501c0400d0b50400c2040b058040f110540039480442c010700d1161200a64003400b520b0820000440740316075400d6060210807000140001e84809103000303004881400349004c0c10388010001c0e034440c5c0c04030580c20700c82e810642c05160401d440c0445283c1c03848480d465 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 542890755 1250 542889505 542889511
    0x903020a0c05010201060608060f0d140705010305060a05031b0402040504060b1308120304030e011205040834080702040626070b032401030f050a1d0102091819090803 73
    0x414501ca00d00441c840d403040c0280e1003150305540b03c0000301c0e2684001c00c040391035002c450079040a2000302400c0862462b0014401c0300d1030510180c41c0d4203082c58001801c2d51402003029005500720041088107450003d0011010007440c2c100f45904802e0800060180c8110b5100035071283c14910007103560b201d620020103008400810b00c0003441d5594180c40e890705090542da200d401414000100400c1c012410031907161014036218041141100d81d542c100c51003070354259403043c0081080d45488402e20b4000c2c0010b00311031402100d4014080d0820420b401e040e03c01841c6d0b08002c00c41504540b25a0000da01074030780c41100c6014402005540c80d4085101303000c04a01340700d008800290103003c2000c40e4010a0100701d80c8800c503440301e4034140c0703040c20848860304140d036800c2c4a070144950342c0b207000d024200a10001c0352015140900c1240c590b00c00b82003a426900c10080e1903265074070580b0b0903400307503200d104504041c1c0e00d002c5182040b4100d1052251018180001c072810450501b009601c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 542892005 1250 542890755 542890763
    0x1b020d02010b0a0311060307020109080406120c030b1005130819030f080402060a052104060f0605150405210a0605040c060e0a03080c0f010e0d03060b07150c030e010903020a 76
    0x3100d032038400d003002407000b804d1102401c0403100300062041420803d00441d0b1210440c00081016075076541c0c1c00c4625400343e40080c0c0007680b0f46070082c3c10008a401110003402541c5014010394031002c0002e8011440c44000d2010f2020009510702c03030900d6074204100074172802051314815a44c4102c04050070301004004c5000034083e205140016006508407030040790040d05990130a005078409643c690300a054102000d00c205081c0200c044030801500c1c4118420100498051246170300c04081d241c2c5030b00014800c4e8480d040040f12441c0c800c0075942241c2d400c440410408a5803001a600342000d440303aa00a0700031944d2074010701c0031581180380146c0c0b20340351415038540d540c401215002508640564000c20789181000841d0800300900000000c02058819046040403240e0031035065404521054000c00d00220400d901880b805c1c000b4414160001d2920040350355030a4030b54032141940005d170381e41d148042c414900c280d0020741000c032550001c000800c13040c20007a41d07039100721100322 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 542893255 1250 542892005 542892011
    0x32a0b131205150f0408030112031e020a03020d1407020f06040b030123010305040206090d17070c0e1005031908120a0f0501060302180f062b15050f010c061b020d0201 73
    0x24983c1308554607082c8256003202030f450031a400c0000030681c014800d88250204045011142d031814812801d800f21103051307070014000440d051030701030f080c10300c1c1c1e0141c64140045e0000d50403000b07800c0d800b2111481ea044400c009424090b40004025000d1500242d0441c02c1c08400841c0300c81c0020b00251306640300700052221900c20000450aa81c801c41c5d0094108809104030300960600200e0b00d6a110311a41c4146034001c40d00c5040741d8540c010040948002e16200420030050384008403050300120104604040681080f0120741d0b2500c0612402e00741100c407401e100184410300381611140103200c0d410049605000c0ca00b04003034283c07070b200b100003186010700014005001e4401c48100c0b018010203200390a0703032a4200a000b0035070100c41604507a08000351117540c400c0007001c541c0016403c2c1c80000000ba0b40d00040203e944144102c0d4000145180c10b000d195a10300845c3d0301e0301d40c240781c0000328051524202c0c001e48000341c560001301c0c1d490b940c207030440c3d80c003c02c86e0144000326500030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 542894505 1250 542893255 542893261
    0x709050315090f011409151306020d0e12070b130302030a0c150906020408011401051507051203070309031b03020307110402070f06061805041a04020303070b010305010501032a0b13120515 82
    0x181520340c10380d004d440718019502d0b231341c00003030060300549007001c1d000f84005500303c5c1840035541858482c0c218050345103000a098420040c0907180ba9070070000e10300c4a03101c541e50b20755001e136880c8035141c10790081c4a2800c45a1080000e9140301c003045000e903c10031301140816180840203074015008206c183d50030b104421440d072440800d50b81c100e91008040c0100003000c0d00c002d58469021003020307900d5001e00b070741c0115204282c800031402564160303000141480702c0c4c1002401e000c044c140320020700c0002000f50380072070b50000948002c103410440a00b10f00d04e502c00003e009105961000340081c290718844400e00015038400001c807100c60503e00c002000b0460600b003252821500108400a80084418842c40c0c0c0b1340803550161024007100d18042c0715456207103164800340c1c0100c1e92a034441005004016250703010715a6040c03407072850030a0041e805044400c641d006d004d0ba2080d0113012071003032000341840314070a004160410100d860181c080c10400d07250600d1840d0300e00001140008 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 542895755 1250 542894505 542894533
    0x1a04170a0b0a0b0d14030405030114180601180b1210060905061915031428020a0203070219091a040b15040603050712021b060709050315090f011409 65
    0x1a00c3d41804000d050140e0380c002a65801c0d150401650156898401804007107a503480912400b14101c141c1d40c0840d949241240da08a036031001c4c084040301a4115100401440c1e10b0074075003010b09190031501240018a890100701c1381c0202d04100c00e0f8620031390b03041c0e128505180e03014a099414030141440150b544a00340621413052019000b20421890b008118043e000d0360754040d04a000e1401080b68140300c88441c41c000001d490f4001c12542607403101c13442c041401c1c2082d10b09683c000c429400c140d80800d0103912070083d07505c00380c0146083d4007400840c20040322030001034400c102080250b485140740e03000e00c151858044500030740c075080b00b81c001e514100b4881d021000d05030002610f001c0c03e01c0c100320701500024180b08240505034014480c104480e001810004040c00c03a41030b0b14207441c248142c80c040024064000348403c602051044c1c0e180407503102d954454640c10030020b510342c6055035203800c14030403808180794a0300c1c03070ba0310580c07200910344d9004d445c01c10708030740300301081c000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 542897005 1250 542895755 542895761
    0x302090a241e0515040b13090207031e0905010806090910020d09030314060303030c0f040f0b0304031706031e0307060203070804020310060e160c060906061a040803041a04170a0b0a 79
    0x289204c1c0c0c118040c003040100840d0800201100124a0702c1c00018542d14076112090b42c00c8580110080b440c10041c50804c01c0382481500c1d500200c1d49001b600c810710b0180007804041000c0c2299014182d40b100003611000304010410051424000071540c13104e246103100c00400c0d1140c401c400080c28410b1104910100b0600c003405280d000b40903625545a40f0a010700f280d0004404c850071010170f0000007072403000014681c0042c90001e0710302c0c1d0340f0301d42807400030f00d030140038120507a0541d44602807200390f032030000f860702c1700c022081140f62101e81c003540300a1441c010034a006058900000801581e29400150540124400d6013180c0281151108100584900b800f42051452524000402c9415254040c04d595480c030f00b04866481c80d6a120304040d42c040340d000f51015916001e003040752501605c405112045402425400d1500f0308641035140e120f46c0c400c4000c450301e5250f0060b0480d04400c100ca000309100c1c003000303540c0700b00b4034495505c640c1a42c1043e43c4000c1c075000040d100c81c074640 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 542898255 1250 542897005 542897029
    0x90a0f0b1f08130c060c060b0306160e0406050a0b0405040e0a0f030804020a030b250e010203090603040c0f080f012a0f020f07080c0a050102070302090a241e05 70
    0x608403207218166240c00700d034072107002004010440190f043c0040410389992114001e4039542d51021011210b509001094404030300c4868001d6001008000d040341800003121841905484c1c42c81c005c0c402c03100000c01403c219041160b001c4031103680011205500c0d00280103c2d00c1c00d1f01d0500c14514404d040540702c814544000d00401c1180100d800000c2c40391000962040c8006d11854445440e40c65081c2c566000301c5803860392030003004030138605071300a807a600c000c00c0c250321340800000c00c03040000703403240205d0031101d004450120100782080500c8400001a1144031141d000c0b8603901d03020a5036600362070356485155481d107060030104200d4901348035490040c0070800641c1c58021001100c040444500e04402c60003030201114070b040381803000500a101079070007015400811000c101a10b20280d11050640d8040e400030001070b251a0141584400d40d400c000031082d090040c2c0d0300400c64440058013070400c1100010510b00710948803400f403500c00314000160240c5070020710ac1010540 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 542899505 1250 542898255 542898289
    0x507030203100306090f0602030a020a03050105030c13150317030a0c05041401080406111908060901300b24030c010207090207020301061a031603060f060c03030209090a0f0b 76
    0x44042807011504c030b40c01980c0391030310440002c0300034035068503000120f030410b07141003032115000103540344603690600606001d00000c0b03000d820010882000a520700d642c00000050a50b160800a8006c2400f211000d0003103800c40407080c1040c0100d10108a1a07004a40760a055890202c0c6502024403c00a032002c0d280d0541400e48440e91034401901c48102c0100200c0d003060302d80c102c5c0c02c80d81401e0b41c090452440103d4501d0b00ca6052540c028001c03a000812240c0610400c0004110340c1c190b9001500100841c14018040001700070310b80720300384800010140880c11100107001c0407403100c04869412408001103031003000c843c2010191101040c181c00c44c01030307100ca0350a008440d510390051140034402000003c04966612480f04820442e11003540320890100801501c81940f965441c10401540740c108280c0d03003000c407854504803142c0694000c2003002c400900400d40240d044030f51290006211384654a4502c121602604403001c0c0d8a104504050340d5059a05007154421030940007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 542900755 1250 542899505 542899531
    0x3032d050a0813060603050610050603060d0f03110a0812010815011427090d08092814010c0e10021911090f06100806061e1b0c040507030203 62
    0x5030310030450b044a030261102c1c1074124510114000607840740f049030f000f140301d00040c103900e1404201080f84e010495000380d00441c4108100082e540e603a4003d075001c070b6481008030705024580c1c2011622030401880400091203070104c1c2c9010b0180c210050070b0010010903403c500d42c2e0304c40320510b0316420307d070000790b801c0d40c840c0c1d0041c44809011600c0041c0c01c00041d00c0c110700e45441401c0301d254400400c5d507101c1c202c0746610620000b0312007400281c01008450502c4440d41c28100300c0c2a0703039007a009098180a42c4020003a003280305a8001d28010143c0068200c18001c0c0c2d0541070900034020820b160300480c01803c4146018188a1402441d50a1b95000b800400590704000c943c0c0480d000b41c02c03241c5440345201405199206013245008141c0a80c60003400e282038803c0c8074000151041000c01c0c0017121007004003551722401261a00c200d080d000205141c44031501c0d00c1c1c1e5004480314000120a4250090b10310740d030000d0100003140089034240595114603205604074441130b5007503210803035 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 542902005 1250 542900755 542900767
    0x40302240402041b052b0204060305061512070807050904020a030b0a290c010b120318061206120c31050f340804140c032d060103032d05 60
    0x102c6d240805030150041403099041141010b05441223911a82054010965900a120701c40c20108824480c100041c1c143d13624043c411421990b14440c007c04c0307581081258800103030b05038031881c113880c1c0c10503003c2e106640f180e10054000d4040c00c400240d05000d042c940a00041c0d480b9000c0c180e5101001510507401810030800351640103900c243c0b4540e030550b403501c0840b41d0070740303500300b0102e183c1405038051900c0d9500644142040d9090307058007031154501740070301c0130704003110f42106400003001c650402c3e1002100711510700784200c0484141d4440400d4010403c2180c54158180f100005141401c1c507407034204180d0000c8902c29602c00a00b4680100010400c4144025009120b0001c9a240c01154080c02d0f46000b07c58207500641c001521120a000401c00820070b8401d180440002411f0b01c12300ae40301007075540c40c0710480c014007801803030743d03e0003615041d01120310000d50540c195a51981c40e03090190440c815054604841036240c03e21141c8511440958207040c25107a58840c40c2203 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 542903255 1250 542902005 542902027
    0xb030121030e01031a1206010f0b0a08130303201e1201060807140a0e12060f0c1606020f180a0f3006090c060e18040302240402041b05 59
    0x558005d04445a4a040d00000e0603600d4440c004107170341e54100100714a6041c100074560300c1030140c1c400c00d0000d0091001c191455040f0354165841103010b50405038809040c01c3c02c43c00b078000c100c4071190900a11450004085054004000701c1e406900031400002c041d07a1503520f45c0c41030006802e442c80c1203400500080e4401c041458004146250401d02d181d40343c00e44080c02d034004641d000100d48020404012418589072503200000d900b0302034144c0f031414441004084900a000181c0381c1c20010b84200082110241c501003130fa0400e0b0210f48801c840840350005901c86801284010030803d40369596203000c500700341c250b42010078022241882d252079507807154185001010382140744480d28900c1030409203107001c120300071540441d84100701c1c01c0881c5418100c2d003000003080104002c4060a0300d80700e010701c176081c400003a001d07041d40d07550804034240648803400030142410006171784109001d0f080128011402200c0802523507440301000040c4080d41215980410000e00c0414021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 542904505 1250 542903255 542903261
    0x80619180c110708060103033005060613090b0a05040912080c1b0c0a0e0c16060f061205010605040605010e0603060a050604061218031e020c0603010b030121030e0103 73
    0x5200d66040c8600c0d41d031805911103040043c01c2e040310036a61300c40001001416404450305400100d200f80a08210301400707903070701c4241c1048410144168a40740449c070161503140c01c42c3d214161414948415644622001d0040d1400c62202441041da05101280350b103450700c0307195141030f13110031896500100c1040c1230303815141c018081c440c150018041c0755011908680b203030703004042200c0642441c0004d074041000b0740300103030007100180c43c030042080307030681c00181110003645009041d0904414140740401c00b91001c402c545500f14200100000c2c1c2240103004521001c3c400e01c028071401e038483c02401300300c83c1244a6240061903610854115091100056402050142111020503210004902168015484480003a4020103200d0342445a8401c07648580308000c42101ca1091a840040800d0500e600c0080c1c40002c581a40b44014000c0014405514010700915165a9110b02d120b907103400c240f00d52400640ca14401c0c001600c0c2584d00c41c40420f6154031401c5001403035400450003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 542905755 1250 542904505 542904521
    0xb010206040f110604030b01090c02060103020a05121e060403090611070501080402040209030a030206090f0a020603040204053c01050d03140f0c01110c12030405100f1b08061918 78
    0x10220f50782a008035840d030030001c101440c0100c2c04010365514044089007101d03031640e41780302150400e2006100590b140d044050440703078203c90f06840315454104190605210a140258501c2d0514030142203610214107148100d00075214404017075660038040c0e0342e0f2440100313a60582d81124405014940c0111007079504640080c10060901d8040004289055000001600564081d0003000440502084074400341d05090019244c50409603008c58a2400080d000038030641c2ca540020380380d60440c40700c6001440344011050b00240f0384454660254000306c0c44d0420400c2c85000124050602e00c000c00c108035810b580b000f03443d00c0500c0105403280c002a5411138007041c20099007904d00c0b000d000b40c07007416152804441c0e44070310714403043d89002c01011704030358802c1e000c1c010400414000700380540044541000800d2103c070141c414002809060404480c41030b04031201c0c12050741c04002e0601c107000a0761a4100c000b805a881d11481d0071900c21010741c041541d102250124035500600381c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 542907005 1250 542905755 542905763
    0x11b1d040911091306050c09010503160c0b0c0d0c090509040210140a08180a021c02010c0209070810060806060706020c0c2d100906180b18130b010206040f 68
    0x34024507400001e00741000507203c000f201c521802d1301d00b0034403e00d4495607400c000314803001ca142210140028043e070100a0002e03441c3c100304001041200d0040300d5500b03005e80c1c0b0501c0e0700b99030f152010700c20046400440c0c042c1d013864904140905d11900030700883e0141e4400a003480c00d10b60303441e03007007000e80ba015000c1c07041009030401200e0024841e0708040d024040c1e40e44c031030031698036160642515a0300b007202e000c0a41d80c40a000030015132038420001c11810400014540811036900068440e106086e400a4011240c0b00811050301d42c0a590203004560200900d1130459940c90222070450302503030100c2e800f1b1803c1084200080880e4000d086040c7c88d501522040000c16000582840c2c00355a440003903a111400c1d0b02282e4900e18400980450460340d89400c412450130082c4892018081c8a00f445503219480504c82d103c04201c0c0020021810b406a0350b8000103908901d4107841040c3c1c0303003d0805540000c0c9558247e0041d1031011506038001e00041d5a15120401c4450715640259 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 542908255 1250 542907005 542907023
    0x2030709020c0102040302241c140c0c0f0f030a0507060608030708130608150631052b121103160b0105060c060127020309011b1d0409 59
    0xa003015550020740440c1814100060b115440c41c01400070403412052080d044500c1c01c52481d00740c00000c0150b400c01c00c42003051a48060b000c4000f68010031040401c40030070b076288803c10010038030900040282182d00026100c4040502c01c00ca980d030310f20301c21a28456002840f80c6881581310700c02429605010701c001003281c95581009909551003100155025880080c9101e00e04c0f03d15081800280700d18a80244545030102d0b01400c16030350445d005104840000b0341091030383e10300100b05820704401c1d0070a07013607030b407130484646005416200e85802030107070040103000b5803580302c0389032444103400010b95031000d074507641d41c1c105d040d41c401440c003485003007000c5284103041000a0301116030412044204800581856609000168081032241c54200301100c00c00c84003007100f070304540011740c0c4000c40300e50f1030b440414a8400c00180c12991840030003009407010054000341e0f43c0d000c4024182d1a10840610215200002500406840c07081020950514106503024590040c09200f02c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 542909505 1250 542908255 542908259
    0xe0102160b0106080c1c0b0409023109170307020f0304030305040311121b060f07050309090a0908121f0e10060207061b0f02030f0d0e04050112080304020307 69
    0x2109005922100c180c03107a200e45001401915000303041240c208502d4841103050203a401407440e03a80140030b44e00c400c0a91110404107a40c2c59035002080350f583c2c014410f4080c2001e40103180818001058003a126858180001825103002e11501d104c2e03941252449002c01c2aa18030074200707a02c0074151408510600480050180d01400580081c0d4480d540d5595654510304110a030401900c451600c2980040000d480d1140c1c00141510f0540d0300440e04604a000c4000203007580c02880415403201c0b20006880c0100500400100381c4070200f03c485440076260b5080c4241120310460000b8580c40303040010301c0d1240703d0104a9948915050f1a00100b4490184400c500708a19072000c80d181ca00101400035001c80e40320180c0283c030480c0300500605190000c010080d0780010b1400c03200707034a05144003081c82000c2d50780300d0f002a00601219140ca0b407165905a690a43d500107800050107180c0b50f00c0c1906e0a07009050480300e13882c0340c51000030001e440d0a0060750000c0e0080340c0c14400c410340 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 542910755 1250 542909505 542909527
    0x4020a09061205072304090c0b1812010605210f01181a160e01090f08151b030118020c010c03050601020d05070b0c0714010e030a110c0d060e0102 64
    0x2812019104241c400c0ca6124400d1500901d0b06107540c1005c400d0806000f0041d03900300405904003e5030004960200b0000c02500340083c022503d604800c90074240003507441848010045201c03054070050f1480340f0007500340d12046081368002e01480354001802c0b446c0007900d64142074034004640c1040e040e60f010503125504a4219910043c035007040e80ea18280070410b0103403507010382d025024154241d039514542040b580203210a0680f1300810b00c240c00103209216440340c06e030030000e0a40e07036101d01195520b81c1c000641d1680400194400c06510700300190040d202c21980320141c464028404c2e04507403c003c140031550101d003449401d490b5003404a0038505c607003405180640b45103a10002801e081280009041042507070210040c44002c21031107000450034040190301401c030051098451140b403a00300314040c08001104815801c1000d2808412000700042404000e140c4030f2103050090b00c0e60180d1245d8410f840140d00c140d1f003180603030101d003050300002402170000000528000c40d8001d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 542912005 1250 542910755 542910761
    0x60c02071d04170c060609150d0b04050d0219080d090f0b090616050910020f07081005130503070f08090303040e1b03220302150c0304030306090204060504050904020a09 74
    0x1c040c1012103001014042807005141001528842d030340300c007910788405004c006503606000741415000742d40403400180d50500c560b01c503441e803050081c81d01032042050f081c0301d2501001903070f00343ca0b24010f64808080150000840f407030300040d4140c0d0190b0b184101d840340f0744290030440500c2134080c0c5030000640001c1920060941c9070b481340503015043c0c01d020386240e2811900628524078600314244d4040843c1d00300702641c502d602e003101c184046240a220403800c150380100041804e104030b240101c0c075048041840d1000c031807100401c010700d545113100c0503c01041080c0140c0507800800040c07000c1254a040495114007650069181c001c0c1c1c500030034a594001d511402c0e5240c483c1c414010101e1000c9158480600c035061000d003141800082c2810304900e0402d952000d0f074941e071249017054001d0102e05410001034004800c01d1416144401a542c42142c007100020f1816002241d000c040c1d100391004e40310644e8600b03043c81c0c02c0c40c2c1880304450001d0402e0f03a00400040300020f05000c140 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 542913255 1250 542912005 542912039
    0xb0a0f0f0c020a051501050616021813120e060a1107030c0603060608180d08150d0c030201170910090503090a06091701021207032c1c020f0604060c0207 67
    0x41d00500f00c40d8614145a03090400c584020041100c00300c00420807959800246d60b1001e0081106a9058140e0b100048081861f9a000b91160068008000c0c22610a0780d08140d214064640001c042c00240300464a0031540b84006501a1052194982c224410032400c100010f59000710350b40f041d12929500c01c02c0800c2e43c8900c0019840705c0e0f040c48000d600601482d04035480c1c00c500c01a070040f0700085a215030007000403000b04aa1000000c03c41c40d07840400c1042d10074058404905a1102c2c14014850398460005901141e62092400c02d11a049200c80f4807589002001e00881c0700500d5800300a4030b9078001c00d1714144070a00c4481c105940b2016150300600840d01d406001e14503292050300c04000462080070240d10500c0703c00740c2c481390240c4480e03011809241c00650f0249440d2a14050740b0b43ca0700202e55515040040800e00f800092200c03078149a11803980d14520800c002281d4484a0b440a40c22a0308403c01150005a01e60410301003c2d0580c01611615500c0d0151404801f04035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 542914505 1250 542913255 542913257
    0x705090319050c03100e0f06040c03020405070909090b2401120c050d0203180613080702010c0204020f071115180f0a031a01031b03020d0321020d050f01050a030b0a0f0f0c 75
    0x91b01030441802ca040198441c14292036000e80f00c1072030035855500c8a21101d100107070090752140001620b140c480c582e050040c2c010741c2400c101a00181c105181511002c550381503401000311811058405802142c902034501650303118800719101c2042c001808811300d81c0400c1c494240005024051680041c40c0b00700d040000c2c1440b41c580b602c082c5882c0c4000034048509002580340410003041c0800201c2e951250203007003501041010b0301c0800c0092184458040110202081c0342003002071301d9003000b464000448a28080d03441c8205145014412008011104821964880c40e1410701010002108500400d14003016669890b03407480c841c840c0719022214a111001401008803041400c0b40a6150a608244182c01c50380410160802030700c0c00f0b024040c508a1951060071001c0c0090254038155006549070815a501c42d00a40b6050750f244800440120022600d0b051400701d0b5400c903600f109035201d80717460323031694840184004800c03c550b16840380c208411605490040101c0c450342 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 542915755 1250 542914505 542914511
    0xd020310020711150a12020a0905040606030c030506091003060902280f0b0406090501032a092405041e08010c080a051005060a050c15010b030f0705090319050c0310 72
    0x4102000100f800e04c001440800c0f0041c880181d409030320031400500354606000050707541e106400c068821115541c4029400b5041c807402081c06540742d006010303c58203540701480540c94a0040141c0c4003011112003024204a150410118905800240c03001d0f0028060713003140c0140b020540b030349020902034041d14107141d01c800c0020209003454403006216076082d40f4109400d00c2c400400040345846200e0402d1340b151929103140c012031014480380f50586000101140c0c048002030040750300e034804d03135000307012a0300c00b001900c003420720b0f01040d0b519a541c3c1a140904001400c2020707072050481c0d01901910301004146a1400d100350007594085456a4140d446c0200e00c1300e00782c900040440040d0f03603500760100125106d8906a64500c4520700701640ca420364104064582032150316085428070906000107100200b034401580a1503050000200c5513440180a44d90340c1f0400c089941c241c3d010007641c1e0003854a401d600d101e4640b0130310a4801000403600083e01c0c02c0c851201070460075039 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 542917005 1250 542915755 542915783
    0xc150f0e070e0906010909080d15090606050909012c090616020a0c150c0503040e0105030c090915100e0a0b010e180402270a0207020301060f140d0203100207 69
    0xa8108034035001000500240c400310b10b403c45183d81c031110706100e68040300c3d4640c400c0f10104003403503094400100680b60b0404c203100110410500b00c040074401c50782c04514002c8080380c8244a98211000100050290151b41c1d282c00301210710291039a5000c1c0900c04209091a8401400040c26005280e8400100b00a092021202d80250174900c0203200f9940004210310002d40c0c0da09002040b201a070428606025421000340c5030440400030041450000080101d40e2840c254443da059800a074200c407282c003218000e01c0a2541c0a4500c0380890f4401045048441081007110f039020f07401004007040240d4a107503c2c00c000205454284881c6e8840c07000c5002540d00861001880d030003194150445261405801809000039102900074900600000d541011500b00030740360b9521000310303100307501d00103603544000d4000000072071195003090000074190006030a0392040d0f50000092100e90400c042c1002113503621b0500490b018084c1e0701c10101c1400722480076210141c050104100c00071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 542918255 1250 542917005 542917031
    0x50a03060902160b040212010c022107030914010302120c0304140c180a06030b0403081608190906060306050a090b0603030403080f0a031506050d1415010c150f 70
    0x40c4080e044141c1040c4140a000c44003401c0040302004541c0090140810762154004190020131039000c6480a42c02c1c08403150b951680040d841600780d404124248030520b40d50f90718429445880000350004050ba4404c6c007100b0000310140124440c141401441c0030707038541510714a040c081341c041182d0315000c41040180029012100400d0301000083d1181650700380004458852100103080c0050355040098440e19403580800061354101440e0000c5186c01d14001340348203421208c401c3c0c001940f080f0b401c0e4042c012003400340501109180429a407800f006180c0040207041e6041c2c5001d901c0da0000408a01a03114083c05941d2844000c5002259418407540391007004c1d103024000e030301c00c000c00c202040c0218103031620400c00b90380031640d170956034a0880291001242c0403402000f00700001560340d40100007804051310191003800910760341c003c1024209812544255544d01e00c52400c80f0780d6102e00200030440e44642c2d09640c0d0fa043c520b0a1408450400c0301604c100c90755042c07041650 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 542919505 1250 542918255 542918261
    0x3030e09090d050301090209060c030c0d171e091e0706020c030601050a062111031006170126071403160b0f03061c030801090b0a0e0c0a050c0d050a03 66
    0xc12680d0082c800c0500030503004000303100505c601c0c5401640407030424260340c0c8042c2260301001c1100201c0e0707207441c11240f01035200ca5100000b403010801d100f1100b007a0580c504c480c00d108840d814507010f1640c51110b543c00c42034400501c940c000340030300c000988848c541c060328404071340d900348020b080007800c007100030b850041c400b440750340b282c4d0213503004000903910071303003450b05449152038070302825590600600041e10b01c10001403419400c203031540f5030010203180603601c01c0070040300c1b007440f00c2e90705c0c01c0c195001c80a001000c00c0710202407005004590f40c907020780d4007400c1c1900c1e034200c076101c155452038103100e444d8111901c112140028413071145401c00840d40c1c1c580d03408980110f29031500c89059564810b01c040000c08040c088006040d981d2410402c80c10211390009402d4250014030300180030000034040c0b0120545843c0006266040c02c035017103070540e030b00c4520024003629002e041039034640000c28003004100c03013046a2120b06001340894102c3c0b16441d11800c1e2600700940d030203416 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 542920755 1250 542919505 542919511
    0xc07030c05040603150e01090506040f0b0f01120303090c05030a150e0102030f010909050c0603151201110d180c06050c07120c05130f05011701060e0915090f060103030e09 75
    0x441c43c01c011060011403d190024400c003480349000059904002e16060b0240c03207603900103441030160038108000e0054410300d5140c81131040a001641d6a24030000410754002030040302064500100903a002034000c0e80100070b464000d002c01800155a00300286c40c10781da0081c00c5500c001025400c00045021307016031001402543c00a50851030805043c01e480041441007104c01034a07a04130b1003c2c4070f0107026062100360003801d19a07880c90011603200803003512110107800b40d960080c041c003003928184100b030280002d2810044c54641c0b0420101c0103010307040c2c024a00344070140c4c0ca190000e50340300480d10003050192582901e49075001e43d402c0c180000c90703005440280000e459900020f003140301c030f40b056441c200c900300340c030011007107100c8002e01c0915950400f05281200209000d910140c110000c1040c1c0002440216101c0c440700c1c0b0900f4090f10740e600140d1051308008580c1440b03c0c40290f224100c001103480c0341c1d000100b43c600d8504280d10513804160007100750301041c1840c0700c0c55a4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 542922005 1250 542920755 542920759
    0x8060a0504210504180b030d0309080f13090c0305090d0903030e06030c0c0f0304140402040e0610022803080906070804080a03020904062309090a0303020906070203030c07030c05 78
    0x840c506500c03805141d440241845820812180b0601c00303081c01207084d500502014100d040c80410b44c1424080204a07070607a85109200d00854001158424080d40282590011546040200c4d0303451500d00340d04600e0f10340e4042088040d022420724001e01c1001c1d0496203039500404c1a06240190a0070402580a845d082005042003440440d400203e15103d00c5402d0b100560f490381c6005c0102114019180034003542c0c0145091001180c0700000603005407502c04800c2c11f8140103940400c0120300c201d101d1907240d84e4417007000444c14a0002486004915140103688900e200a4940d018130312808c0c1d1014030f122001e10000061503400640c595025082074020510360900d00d1015020100060004200d130744c000404003c160b12940543d4001c160190003880000c1d00ea42d0703032003980324011031a040021410b483d06152480c000c8441400b81e8800d10141c18283c00584086010398071503d00030b50007001c108900b03401078508100604282c04003002900c50385081d07280075040d40b0710b1a88040c2c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 542923255 1250 542922005 542922011
    0x140f042901170c0307032f030403170f0103030923040c0c0f06050901061a030f060109080d09140118030602070203030412080a031a13051f240201150b03060d020306070908060a 77
    0x4032501140c2d06542c500e0150003840d03507071603540c9c1d803804a41041071101d018290600345024400718803d00100941230780d01c81e817911985982c4032400e00100741290082803461802142c1c3e11000e6081540c0070700c1e1000d002d89010115804a0740361311030307a00000c1390121110b0b9500c44c2041044402071040c200075101294141c0c03803030301110f5850070550201074000d8002c45904000705801b41c2c0180e818200402030441a1040d04c0c2103403802401607403181c80741c2072040c19200c08404143d03100300022540d1500241e02401401e086450f421700a411001040303030940f004000100d801e48001c1d90080b607440c0b041155917a0754203440001020b4410540d0341d822640d0420320802c540d5510310040021044003581d00294030344c2e0700389803810310024a034480d0800b03046400000c106101000c10240300c1201d00e0100359040904039204a0032034202c43c0420100941d2824244140710303c850085400c528010802e20081480d030700002e04241003a51000e01003080c07c0400c00600da014040c03980d02a00d090410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 542924505 1250 542923255 542923301
    0x206040b0109021315050a02010b1906120e031612020604020916120c030c0801062d02030910030f060902090303090103022101140f042901170c030703 66
    0x10104080103009114402c0d07004036943c014140c1940002c1c00520b0211440c12241c4189440070304182e104d80c403108019401c201c80c16407241001505400c0703da00071000000c10514100c0c045510f24811403205400e01d03203800160760300c1601040504a00c0000c0020280d191002e0314101000790031440e4040255080803040201582c0c802038003590000c0040c42c20030741896a80b400721022480c06600c1c48400385028110a18140e15501c0300d0181c0c180d540b28041d407070740c8038501a04c40c034648040c2c0e0300b44540b400c0e0140c4508010404200d201c0c0760540116410051500700290b00080f0741e030075080001c1e5503000d03120031140180c0565030003032900d07400451420700340b18040b984030f111359004035040c942c002524a5480742481c2c10314480d007060001d140302c84c3d6140c000000d03415a038007808520030404400c02004920742071044400030031400b6014000b4401910070a540750713024914075414011030b0b000c1146440441c0300d0203031242051030340b1140d81c1c0c900700f0303009012192071a64518103800c6030102 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 542925755 1250 542924505 542924513
    0x15100e01020d0e01140d0204081509030a0c1112010c0305070e01021c0e120a0c15120504260c07080309010f081f03050a140309030a0b0c0c010e030316020604 69
    0x80c04070202d242e20b045821103520710010703100840c030040a0304908a000800c00e1044486034050310a41320240c003607034003628244000c11201d503400c0d80d415070981c000300190340d5881c0c019003055042c03900c00c00c001401c11510a0009208010100c1103011a9440b00f143c0c091180c0d062250691040b09410f240c200001400c0000359150a4081c44050210320700f111845094000d0130000c541100c0100400d01400f070b04000c683c0c441d852440122401c6501c010041200c824403a21340a40c41d5003603903090750720907641410001403e03010b8000d035681d0b0322501c00b80742004c2940c084024100d6580d40015502d250100700e0b1403502c5219442100541c000b801584803d82c0c0c41840b6003450449442c1c42026034540c07024003507034480991341500c5e03904d0700b4110000400a02041c0d0b503020b2402a02180252400d600d086c5032644506400e80341d154202c6642c201c005411907010680003c0c1c43d03541c1504190035080f1690840d190980d80520651010041103070403440d041024008081ca880a081d880c10159a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 542927005 1250 542925755 542925763
    0xf0405011206050414010518010b06030f0a180501020a09080705060403080403170c071503050f10060f0e10210e06280c030f0608030403050627010515100e0102 70
    0x94018039903503c41011800340203560140d4055003420500802c11401c108088003516805551f0320201da5003081401c0003a45041c00136240314011024191120740c1d0342c041079000804440710f010b04c20440048804000c00c1c4244081c0c4110003498490190b0142040351080c90b000b4141e00044c41a60100400d00004940070203440c200c0ba0720100002c0c1c4200d50800312042c5004125200081e40b103609000204011784020315480c1c004641c404210035101d4198104030200219900320890040000420a55100d030b01401c040113011314007008014006400907511010383c070210000194401d603d4251000c000304080036844a8440c104040c4801c1d481c0c554441100030005004000508640d6018103100c0341c0a6184220300e510403c294140e410018000b0420480000741c074030700d0300c5400300b042c44000040364103698200009083d07903607500c11021400e80c0e442203400c41c10030101c5400d504d000024020680110f403240e48101c1051800014007982d010805130501c04c00c00b0215000c1c140b41d8005c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 542928255 1250 542927005 542927039
    0x405030a02040e120c1e010e1e0102070206120f010605072a0801090302010e010f1505130b030601080706080a05071b080f0d050a0b06033711090f040501 67
    0xa5400300710040403011150414999500090000000045600c030100b000b05684000d0060886d0001c054054407006c1c41c200d0f9400c0200480c0c1e0340c44590483c50849802c014aa151b030b14000001d490130100f5400305071150480300b0a02da000c40c1d4201072103010520801071601501140c540541000d0700e85e16901104c4034020285610200b4800c4031402c29101240e007403000c1c0c07600100030320000050780b500078002c0c0045218007015510301501320710310200e40d00034420b01314007800b0a61480381c00c00381005000701000c01d024001c55510140c0701000c0d00c06008042c000c1c03160b075000d0068149420070290086d80000c0044003840d140c4010012100c0c1c10140d161700c003101a07092405180500d2409000900c141001641c0801c00800e190544010ba5000284030f00850001404601c81c0e000074059940400da0b40c060142002c00781200800305612109181c0000100c1c1110021140300030b0041180c0100301c2c1c2c401c0c2c0724400180e0b0f00381403c100c00e1000c0d01d00403e4908200c1c42d803504000e400e02d1083d072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 542929505 1250 542928255 542928259
    0x2010801030b0907170c10020706120506120d12150506030a020a0c080c33010506030a0b040f090b060a0503031c0905070b0304031d0a09020c01021e0d0605060405030a02 74
    0x2c03101141d60840c0801c04940508101840c01515504850903a6681c0310b522101511030203441018408035840807034404d04682051b11070042e003151081100010b00001048540c000e07800d29400181200104042d03184070441e43c42e004010040c81c0042010341d10809132100b000c00004c8010000303a20f4040483c0d80c807400c0744a006840745000c0380212080410b100014021000104000c016030101003111070400841d515100040d00c403400366071000454901c09a1800342456004105c46c1c1000750045034814030b40c0e00c3c0021480303012030008084030b800c03941c0c103d000c40c1d40c2d0460204101c8403000c1e240d04204220f800e01d50b003074909400a80d40344102c411080b43c4840da540342504031280c0ea0020004658024261400585c8a902c0350215810885041e0005090702c074048102c489244009076030358401034000d0103d9400c00b10107a010b540300665440607994200214070b13190301c04100c20000d20250044003961008070f91324540584170b81e41c0140b4800c81041000304103580d80025002c01c42c40d41 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 542930755 1250 542929505 542929523
    0x30b01120807030c050a0b15010f020f0304030b07020f0d181409010b0a0e03060a0c0e090103120f0c060e0c0f04065003100c0e1e3a0201080103 63
    0x1310745042401d020a0760340041c031806104040c03000e0703401e6001d0b5130b0451100c2030b600d0540302c1c0031a910490b590180000443c005400410007400800c2c14540788551000d22401143c0c89040c020006500d085d44140310b40c8000344c41c4007104082511980161001801e0310030558482050354800500c0d00302c410310034000c19000c0000c0c2505124010100f04030300c964002c068900a1030020329140c050000d003060040082c0080d51401c4041c03520780307d0503043e26008410303103c0d1245101001c0d03412510311151002441603c224400c0060681d004030080c502601018014015101c0e00744048001d640d14030358841c0f800c1100501610420044028008050072880f0501c01c807485400c21801d00341d003110b02030201010a503c512000304400c41303050355006404503500c098180100e03400701c40084c0508000180264044440c61807c00060030b5042800d001202208001c0c0c4000f80000001c45c2c0c002c0e00102840400c201541c3c0d40402048844e000320103101034000d070310341c0000c2003030005010080c48010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 542932005 1250 542930755 542930777
    0x50307030f20040e0c040803070b0903092805061905130b13031712011211090702071a12070c11030a061e0e2d0604060501030b0112080703 61
    0x220341d003010302194529441040000c80314210514550f1040c000e01345042e40841c0405c43c0130101c041290700300c4000201850600400fa550200040c0010301000c1d0a88400c0c4074004c01940d44003001130b00742c1e9003542408030030413004006203100500e40e804103218400a001c0d070a80e0345e246501c4614440c926150280e0b44085440e680341400c3c4a64101100c00700010880072480d001b00da01100076240118650805000a03104034122842000107540384500144010031807004e41261000040f8072405501801d400d058001c10327502002152208016807009a00300b008440007401480d07403c254038a200e00d80301c0007541458040002400c1350307041041c02d00c0b528041c4110490350b81503180c802010303603540304918103018019095a00114a0407030760740d800070301003030030a12848055800b0728010b0003101e074048201d1112400c03140e403401150b10900300340f80e00030003042c46102d00c15442018000760b20350640c101a911501c058116501d80d2614201d40720104001900340c0700129413610f00b4400c501 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 542933255 1250 542932005 542932031
    0x60d03090611030d09060c09090c120b1c030503060f030a05070317070b0c0702150702212e06060809120304060b12010e0f1b040c090b0c0106091404020105030703 71
    0x211940b104040d501e4917000b00d040400c0750300d401600c0c00034515590302d40416100d03034850007100c0074038403001c0110b000b0b80c400004460032904541400c210042c404003002c028010080b48103a10600c017200001c100008119081c80c140c4210307070050038250300601c1c651640355141a42e400c020b000141002d01005011000c0e40c1c1807000301d500da1030f8414014030042c1464070081440750001c0c0803c0b0700c54a01884885280034481c1e0030394405503002000000f0400600e42e9981d41d029001d07000207007900440003e103454000341080c48052101c000019270b190f424584282044800ba5005103080041c5a0180809210300141c101900c1490407201d0b40d50751240d00d00480103041030240c081d006040e4610044007890190311009244c6803020039281d0740341c91003000c0d030b07220b525031180085480201070502c0d1a505255100410100c0c0c581480c122490301c80700d0811a6030440e07120907031182c1d1a15001e000a0010f0b01601e000b5018056400d055800c0540c00a0203a0000800d8074003050b58403042d0b03003030103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 542934505 1250 542933255 542933257
    0xa062c0303130303020d1205150f03011b0c020a0905061e13060311120d0f050708160b090c091e1f0b0c01110304120c0f0c0b07030305060d0309061103 66
    0x5105410302d02c59040d03601e01c0c01039202c403291003821005c15803050004072181c9a90180601c90f000c8800110303c10300030481002061100002203580542d0b845000e541980040000040040319a898552600b00c5034410003030310445a80203000a03d04007402d2041781c0c0c5921507030000e030300710004414000522240101d0425111079070442d401e5410004000140720407242c0c4059004025642e4a5400a0342441c4503551402510f25034002104540c81c1c500c2c962180340900002072050220a15040480250f83c07007404400ca4156807590700300c4184545418200701b060344109065440c5d980d549070140d1218a0582c00d841401c0c03a0003c4440010564608c000c0c03080c40b0720020480c091101a1903051480c0c0381d0b0088050703411b0030b44c42d004d170b0402d2500161058902c40d41e402080c0e200684401c180071543e9062180d01112100c00d1505c460300021290f1000d02d002e01004c50404d600c030401d0b42001010f03128050026409040003d4070071703011035444011141610719505201d107900d55104030003451 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 542935755 1250 542934505 542934517
    0xa0f030521120f040203010f0e0c06160506070f1803020105030a0b031f1505090103020a0506130e010b07030306090b010c020f010c06050c0a020114090d0e1c030e0a062c0303 76
    0x542c1881d082040708030b100101105000b503000760020030248680e8030320750084403110426201d665012503080c0d01c96180c908002c01c14000c0740141720f496545595200b030b260080030703601d8001003010380240d5404541d025104102001200404541481c40d580000c0c01c54413015100700c1c0c0c826140e01c2c140426440030807030030100050382107140306001c0407124040c0c0100b45600c00820340440e017182c001058548054000d040e039070000d02d52100c0602d0a81008a02c2d03001505070215a00c0c400300c0050b100b02c078982064001c1c41c0e41911540d403695603181c0182242c5168104c40c03429450107c010050780d07400126031090755416201e450f4080d03440300c01a0b032415603000000340800e08081c20414102c0b0b130320f409000d41e01d0305500240704440220f00b40326070303401d0b085814040c42d901a80b0a401441e1040400c0100c00d44090010003c050180140ca040e40801000c15008240d9038a1240e10a0412860f201c0013800540b8115440ea04009100481040303100740c09079900700401da09842c02e55061003101e0f0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 542937005 1250 542935755 542935777
    0xf0f0403050d030618020f0d05101502030d060b040602100e0f010c0c1a071713020603070201050f06040203011d06030c0402030f010e011a12070c0804140a0f030521 72
    0x15100007140d20080141c8507070b0065211740901c0c0181200342201c0ca0003030301c006440c00200d09040450030345c2c10000a0500510b624189508404001003481e0703032503806025140143e0155a90f4040d044254040e82d52aa10942d60104200802c1022a5001c640720403500035014000c03c1040018600c00d262803002104a4040d51030b0a1034195080d8020b088041c40c079205581d800303400300c103071890648182e000715104e0001c600742520409440084500c131940c0035102f100400004801c54000c1001d60300111a510090b07035650040c444500c000005a9911003422941940f466042040c80c0e90a60186d900030400040080040b0300c0607501072140b0a24060050002c5482e840d008594084560b82032184140308200c0c040089810409001001c00380c00702403404a240c04981052180d081c0130051502c0d040200007425030000588400042000301070021440d200d4641c01c0b001c10a494225034800b12104d280808100f0009401150310300342004440c144500001005c0300c54121841a030401d85 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 542938255 1250 542937005 542937013
    0x3131509150608010605090105030601031e08043003090909030e0312251e140105090303090f030c2d1c09091a060901020a0c0e060906060406050f0f040305 68
    0xd581c44649920a5040300e40d100c0c000e1200da0350316814080440030a01840d034158100e0001072010842d40280040056103c1084101c1040151030b0401640c20a400c00b000042c130b5076140048244034294000000002e00700200e4152456550151500b1150b1007003003d410f03200d1858206260064031251045030001d0160340956515803980c5080745c0c40b01c0d0510190380d0140605280c0c1c10b500900f8210308643c0404114141403044102824064482c2802c40e4060960035170666004000c0c0501400340340c40340000c603121708001000c94102842c440103411642c1c010321600011041c0080d4140300c801505809504c07200328650280404190b8400403203440c8100246c91442c4420403003201c20b0086143d556141058940b500d20080c0e071580d0320500000b00301082481000e1038070000420002c3c2c4140102d580240047d0f64004d07c0c4443d0f40d00c4404a0010001003040d2401e01402095111404448041c82c20f410aa07000c0c3c11401002510a12501c001c0f6907162019221000c4070080c5030040111 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 542939505 1250 542938255 542938283
    0x141005011214010e04031713021e0301020703030e0f03070201051204110a030c140405010b0d0f0f0e01060e01090c0c0303090503390f0a0605150607150b010503131509 73
    0x5480306001d4038100d00061011f0502c0481ea10b5502019008901e05801c140203040c158003003022600d081c4a54042d0305030b00d543d086510f030350f09100400007644252000b184000c0b141c2c40741030038090448800c80568204014550050303078800111440105040000c41454445007450040c0d007100014040e0400400c900100c28400c4c41c41c1c0308003c07183c240c040c00841e41040020301050315000c0c420b00300c1071507040c807200d15000c501c2d4101906406400d5400140402c5a40b030040944260f41e40c2010140d5450209001201c81e004c0c1007805011048024841003800060080c4a202020000381c00c150382c07100e40d81d040180034800c544083c060356510003080c08080c2c07011500408182c1c042e19140c102021041a4000d0100300c0d043c100c9200d002804050009031140c001800004142403401000040a1900c0365107020181020b40d000b001a00045480c1f07070260421140a00c800605008013801080b40c81801c1e1030585443c154883c2c05469201c203020000f4003e0800e856000f040e0343c141d1012 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 542940755 1250 542939505 542939519
    0xb0c0102071e05160b04060815100f0e090606090d0c12060b0316030c0b0a051b0102042303060402010f0309020405010311032401060e0102030c030a02030d14100501121401 75
    0x10b40c2e03501c0e02610940d00301004001c3d06505030710340c0e8850b43e03000f1202031204001050143c0000b56000d0580303149400c0641c1d44a002400d1003400d6000c2c40d0120344004500303031925500011001042000fa03541c1c0c1014144203001036802d0080351811072007034024001c0c541c204a485108000103154142e4180190221031a00d4000350071200b20050081c805e207044a0211030b07042900c181140e0f0014580584142000c014103caa400401e010b42404010800c0e07130201c0a44466500346001c480000603211400c010280e43c0c080401411140056850861042c0d180e4000c42d002e60802ea090070300c800b070b28080107401d4020300072100000c0d501c94035040000003400644000e0540c1c90700c2c01c500782d0b10000010400902c10040d107003050b10116060000501046e4060010441070590500440c2c0c00c0c140100040c61569008031165401a0070126814118400c2070017040490a00122002c5030344c5400d0380b1380551803006202c0e103410443e0b000305540016003142d02c942da194a5120882180c1d68541107 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 542942005 1250 542940755 542940803
    0x1b0a050d080f060f0d02040b0301110301080d0e12030429031303020105090d12270606090506060c0c04090303020d06030b090609060f01030b040515010602010b03100606090b0c010207 80
    0x30b60048603076500d00005100e480c00604501d20990300604080c08032210780c0074000203240c10703050203815641c1c49411711074041c10000910300802c400c50041c0312120080c3c02c010304035040c510041d80203005841c0d41c0c283c0140088103940550310046410a030b00c0045001119110041c01c04409a15500109020310706038032855a601d024000d800902182c0c88001600c0d94840e00c0030840c40014540c920141c3c0408019041416281544032070038502c0d80d070250701a042e01e00a0102218025520b5008100b140f181d400303010ba01410403640c46052800b40328150b925071981607040c901c12940c1d41d02d0b02e400c1601a5040d28a03507401100204980d40c0c90785003506c0103800556512466200b0040040c01041c000940103108040c2160b00030856481c55590300f50240d006401252180161040001c01054003420940280003940c008550b91034110300381420607048811048015042c610705115032508041a001240d01968500b592211061115402406002c1004014604081c3c0c50300d144a0308032 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 542943255 1250 542942005 542942011
    0x130e0334050d020d230d0f110706061415092103040801060b04050f1203070803240a061d0105072001110c01080c0705150c03180105010b1b0a050d08 65
    0xc0c0031500300304003645080d41e8030140b008111701c003810f02000c032051985d0103501404800c02985d00115007844480c80a106035450f00341005114603011441d1000d105040c060000180903e000100d48100c100e000705140354081d440c1000002c40c00500d0b21200e0b154140300701d03c02400510350982d040405550152250f00c103100e2200b456003400004140d841c3e074481100d085030b8009140c0000c0100c054240200441003c07910680e90009214075808510704500541c464800b080d1415002040c96001c540c095024200e21030180351004010300400350040d481030b07002040f40c0030400456141c07400407111841400e200600d0902c14906880000d82d1224180c0140003098980c0c5404040079152290389124070840180066002804202c00680b03020007001c0241c0100103580ca028080e4595021002043c3c5070080d11480010811010f10081e425070711007449114002d1103503502d42001442580114800302d176140640c041400d1003900108081c00c0000d42c0034080d50420030003000e019004107411 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 542944505 1250 542943255 542943257
    0x4090318031b091512030219060b13180b090a02030708070602010c0c0b060f0a090c170c070b15030106030b0f090d0807121a130902130e0334050d 64
    0xe0b80410003908034080c0310242c50803582d00c141928905103520640b610703110425030a501601042e0501c4614120b884642280500380110b0300846890512085010896200b403140d450420800424540d41017a02c3c25140c00c0b4503180b00c03035100c000c4c143c2c0c1051210719000750b00d84100600061510000b1903018100c42c20b0340c00801010792241e00075289940c1141c0024448040342c40081c110749803405050105c548060b044880d0a920b4000c400121a00c6011120125034040c001c0c2c200716840542169220740c100e45000d00b0a03015965000f03100d14058505240042c1c105a01c10032070b1001d6004a004541103000e0300f80b41e040003c1d003480d00210641c0c01d80050b000e1641102019809004801e00130001d0b50398200074803802000b098000d213522407449040941c1c0c41081034507a40d58080b4440505c00e0294005000303000e034410403401c41c03620780e1108040390a018104200032400300540710340b510084501c90358254194036004454014200340c20320f81c103200c1443c000b4484000b900c2501d002c11 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 542945755 1250 542944505 542944553
    0xb04020c0a05070b0f0d1505180417090d0602030a0921081608070302180a0602010b010806090c040515071a0106020d02011505010309080c0109080c15010509060409031803 75
    0x261180c180c614403400800804c180d000300200c85800000d070344501e4441f0140e0b6040030030756813a03200040d036658410034220392444e0030307400b40304c10701c81285002c80e00300d0603202680349450169808203e0301f0389011070103041c0316804400640c0584568100c01e41840e03111000300c005006401141c040d01001c0101d80b03000a90060024840f1241501d10000072211900e5200c002c0e41c1340e07807046000c1e51240ea10546005d600c100361602e07030380301c954100010740300503000403981c420304a0006100d6100240346601c659804424846180d0f803250481d404d5a1040d20300e20744405840a50044c58440d0910003441e400d09a0b2100c0700c0c041c0c411080c141660304540c01d0340c1d41c022200404a080c8c54514005034001034098004001541c040d9002c1050301c0c0c810704005080c81c624003c03050840300300c12000d98034400005891240c1150030b1207904080201141d4103021541044045003800030010b0042c2c1c0502e40c2d5000240c181402000d207134140000000058141a45034a000c0c2200c949032100c040b041c81c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 542947005 1250 542945755 542945759
    0x402090105040f271802041a03150703200909040201090b070b0a05060102060417091302040f090c0c03020705040f090506130510110d021b1002091305061e040b04020c0a0507 76
    0x1c0759001c0c01c5c2d02c900c480780042c040ca001c0d0fa000c01005080688169154242c0103001c01c40310344092000c0303400f840c004844a000c61401c4500a403e450b0722450256446141841da0840d030b01c0c50405441c4625000d417820360340e5581b940300584601c002504107010104002c075002c01000170030340c19544101c0b1880c80034002c2d901d6100040e030740c803603054600800b179810700610b0340c00d0680e00704041e004a043c01002c0324100c040141444040b6809a04244120804810700707011000c01401002d2041500c0d00c2c0c02d0819810a8500035204d802d107004052180b42c86040410001846130000301e60150003405969031400d000100f00c400012048c0115454080d25070010003d003c00c2c4038103044600011441c40c500105411800020350000c440c42c1100f01a2101e4841d410404010403078040943c4080146d80b41c000408010b03002e5615098003840328141000c101440d1215111071a031007601c0081c0c0030342e00c8244e00000c1c028040030b411281c0c00c90b01c0861542c040450005081c0301c030500075400c8c8c400c881e03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 542948255 1250 542947005 542947079
    0xc03020a05180403030f1d070e0f160c05070902120f010b190809071509030530161509061503020306040b0901060f0b03040b06010e0f0402090105040f 66
    0x2d0b02150482c0c9000e142400060103c2d0103608655003a08035000c0001b1600494142c4403241c200218031018141d00000081c800a00000c0009400c041050b80002440c5801c0340b0142031521036a550b402000103942106003002010018034001d007500c03110a64407a000381010102d03054044907030026800140b000000c0460340b034412120305014040040b4040c400d00d80e02601c5229010301503c40f6131180150025200800013000c1c90080b10f19a50652800e285043c580c2c5400702c0c44030315020315507205400402d0041005040c0311074441441c0c9050312501c0c3e4010546640c00c1d04240a044d00d00f00d00d450003040000381c0d00080d0345600c201c0041001d01008485030710407030000e01000f90036070f000c076021901140c0c1c0c2c0d0100c1a40141d00304008a4180d484d02e08841070304040307900ca801c08020100c1803004000c10b003001c0b09d500c2002843c2c0680e410303410000140e1451514003105000726800038503030801741d21407411600504801800802800c0c0d450000703240c80849502010004810b04103604041 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 542949505 1250 542948255 542948269
    0x14090303190f03110d02090604090612050d0905010e0f12060c0d0e0a020a06050f070c1401170603060705030903091e0f010807051c0212041203050c040302030703150b0604030c03020a05 81
    0x11071300040c21141400c00380140344000303511000e00a42c0c40b050038000080c0400403801032102414642910080768080d81c5016031820b074854034148140845220144401e9074840402400d2050840311000d4600b908000304020045040d6144081e000d080c04000200c0b42c010010b0881e851130910420900700d058052545400314808001c0d809202000c042008920a5001d0482d0748072a4030814605003041c0d4a00140054991100384400060001d40300e80c0c3d030f0030010780c0100b04510040e4502c18902200080e0f102e10004024000b40b20010010403101034007001038941d444006008a556465444404401140c882491902c103103d0101001d4195124810490060040c1e4440e1401d00f100c00c1c008088020100c03031011f5400303600340003000c01c056460780301301d004074081c00b5106208401c408008068850044c461110314400308070400045e10001451000c03243c02412500003010319108143c050071240c5140c07541f140000c02c020061208201400d02128422142528000d940e00184a10 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 542950755 1250 542949505 542949521
    0x30d060f0609081c090803070b01090f110d09050c03010908030f07030204051005070f06020d050a05010b0c101508060403050301080f011a01210e030a0207050904110114090303190f03 80
    0xb050f0004030010288200b00903145400c03468170f0030550307031140c0c6401400703186420614003912000017180042084030ad0a00c80e5034481004a2030078815a213021404110f80d116917000c441129940e46284d600388a4140006c284903007005000b0b102c1041c1a090200444e0002c1d244400204a45d4000c2080d0500078801c5400305c3d5130252108204142440b000d503146c2e0004442603401c01d10421030316000030003e00c01080005504040041e00d8103000c2d18503003c4035416042018943c9007000003215284d40058601020ba138541c40100b410410401001580c0381c00e58424400c610070001400f040580000140d4180c0e981041260024080c03140450701341c1d82070700281e40c099980c940661500354030034610803480742420303550a00c40e4104c0c4403562003190154450b1510a030404106588039a03810b000400c02024112074036609420280c0350703004203d4000c0405418041070340d807140b540841850039180310000c010140da445801c0910340403581a40c1600d0040003c0c0c80286011226001f07100741c400e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 542952005 1250 542950755 542950769
    0x1903020f040b011e12150303020d11060c0c0a05010221090109020123130906061814040203040c0e04060923060f060f150711180703020a0c05030d060f0609 68
    0x40d40000c450b183d414022000c41301a0300b08039140181241d851103a0040032030b8400c3c85583d01c8141071542c10002e050a10056000d0104600200d641c1001000083c2082c0c000c105020100d0351400c100c82c51510b8080c015034014500e50005c60b0b0104940c54030301a03c4000560803003210110317515001d9250880c1c0003810000e010802c034031540c4800040035000c1400c40b80e000240d45103007911203d076a0300000c19030b42c090781c41e440e100d00c001d101c400d030b10040c200356001060002d04100307410b1844120200d190002d82600a0f540400050700b4050343c42580c038002c040c040002d5540d4145030030840c0c00740038403442c1a01c1c3c203c038860804004a1180000c040000b182c01c0203041c00f40c40e94a5000d00c40c0344064812a072084d1b2105d02800150740780c41c2041c03d102c0c041c034038943d5a00b815251a1000f0791003100f030588920178000c20300e8102d07117441c0000b6a208503549001070f0ba5a0480b5802c6d40c1201645001404500c0045000c41210490798840390130b4451403100c1e400e6540d030341c0504440051b01d074002c100c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 542953255 1250 542952005 542952017
    0x318060807081e090606310207060b060a05030103050c0d03050a0c0203070510030911062704110403080901030501090e0312090a020907080a0e0a0f0206181903020f040b01 75
    0x81d500c0c500c40c51449403c200c503114642c402c0064540b1154600c01c080d01c2c040d00d0780d0400d03000c0c0071041c6861800410100c3d803050300c84094030b0400d031181c400000307806141d03410316400141400c20001e4681c44101c21040080c603c90310341c040c20000805580090000311010b1088400d00b00d214641508440308880e4540d84030740c0780a1400e40f00729503407565041c00700e03014410000041156501c226441c00080c00b15030f40005d481105051541c0c07006803060745540114801c0001c0c924002002055400d604881100740680c5100c0f00c0205009180356242440345100102d030100c1080a041c1c02801c018200f6078003800f032a6200d441034001c880b10242442440d40c020421240c0144103206000c3c3c1c011410002e0300c0801889402046e250b070000c03107039040001c1d80c2c82d04000b0041104e200e02d68007116100c0003080b0021155940190240c2d10041c00780c40b0301c40110b4114188150700c0a800e15070b030701c00f80440d126421280038005042d01d90340000c900c40c5040386224a00d500303181c800d5a40c803a40c169148 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 542954505 1250 542953255 542953261
    0x9060103120306270609020a02010209090609040b07050f09040203010b19093f080a0810050303181f03050709120b040809060705061003021201020304150e0106080a0803010303180608 80
    0x182d0300d4203813a05401118507201e0b0b00000e1441101e06c00f81024035219000503940b50580000c018421400801d068443c98180d070900020581c03100c0103c0d44107500703007061643c9040107200106a030142c1c51245610600000020554440d0140a03014540080709413000000b201407055680310b41a025020000f521700700744603605c1d0b5100da001c94440c041d00d00d0f550080040e160300300001032285071050340e13207820006e07150301040d0380080116400f20480940060407410000000d4503845a03030100f40054210356007680c07032940d5161040000414500c00d020b20018525001b030050601158600d0118010120024a0f482600c00340491154000b5009249540d10754540215420846985802006c188840000518100901e501819262034032025141c0b66204001460484c12031140c010b900600910000610407442a091039008040c04074044a4211016004280540c048034852040d1900e001c01e10014034001c6050360f000b60b40d000400440038829140d0001c0c00c2c8100400100ba0300c2c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 542955755 1250 542954505 542954549
    0x25060f08131e0c0b07050c0109120204020901030b030d11011109010e090703111b010506060a05070b0414030a0504050406240e01090302100e0102100b0307030f05010f020309060103120306 82
    0xb0703410401c4500406540e00820989800501c008140c0003000d8440c000114881805410082c0c0e0306800000d28045900904042e40865130095001c8002d02031034000c60f0950250303011340c1000740c80900250032103541b170b00078100040905007210b803085219482c1c411a09007680030321003120845441238481036001d081074414004007135001050742c020103541d55403e4400e008404000c098014030300b1b030b0f030907a1070000d64002030031a03402620151042c08108681d41120b44c102e0f0030344641c9600a0a1000541d0f11800d0010905004000c180d8481c080060b44182070364101000d00203442c1e00752001c00403d900c0d03000c4400c0e000694010408145c03503060b00030b134844c3d01c01c075188a07800d0018900410455907a6012030b40d1400800b444e140800c090101906480d40e041100c03003d03040030f0300001d02c20185040040f80d00d490301404050300350b030000c5a8003001d01209400071061044442021552840c190040944441c0c080c0811581710068085a502c500e21a000c1d41c81941d5091058444031040019 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 542957005 1250 542955755 542955773
    0x30f051b0f0a060809070f030503130806061c02030f1009030305090c0904141f05011503050105060d0c0e09070e0a06050408030901081906090b040b0315040303020c25060f0813 77
    0x5179510580f840883d8100b51452200015449040110f0b01c2c0c022a0344400701c04880c541003110b1541c008810881c00d603465400521202d01d45050118140c8a58004217091640d601a00c403081d00c501070910070218030b198000e1480714000c2d0b4082100d5207458450640300da0003225129444040ea00208010515008103070710310b15200d80c00c0b20b9244039060ba0500200c411000e80000c52980c1d4001000309160181c1100408070003407404001c2903050400080740c0c0e010b20300359603e070280e03680031140c03040d401100000102c41d00100b00a10344e18000000500030544010803178003030b0000d001d0002d040350144007a50180c82a080c0030303506010100300119040350009048040d10031a05102000c0c914091007a0405001e55000115201802d0000c0c841a01d00b0101c8140c0a94070100e89840c00c9442910641e4204d81c0c581344c0960b580c0c1100e00e84510386400c82d40d4101c54526000c6003081c8144c00d80c10001d0448015459160f0034216085050304e03048e104642141290b15440e03028000951848 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 542958255 1250 542957005 542957011
    0xe0d210206040f1e12030504110402090a031712040b220f0f03090512070801050112030207030204050a020c120406080c0a08040f0c090612140a030203120c04030f051b0f0a0608 77
    0x142c5080002c211398031420f0b40150a5140100481d90303880901c814000d0700c0104021160307023a101540f60a01030030110b1401c251900c03004c0e1040d801107a00482c00041d410440ea540e0240c070440c4420741c182418016078103d82503504000749100000d1101102198002c1e0442081d082013002c03a80301003545031410040d034594030031010000d12034400704d001c1c1e890f00178080710070b280719000b003104509160426085881c10781100000040746403030000026030004021094a0381541c000c40c0c03d4171000e2450740680200603502c502030184000408220a9000107070088a40c1503480d2081511020802c1030588103c0d10408000f5415200007008140040e0000d020759114038403150115642d40c034404200d41a40d002071004140040403c0d081c003130181c100e0805007510301c020b4559044a560702031b54034802c54031241400703410040020b1154505e070060354029500491440103982207460400e4842806003040b4401c01ea0002503c03400d03080a40b124098050f01510320617840c0d003402c4050311034180007 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 542959505 1250 542958255 542958293
    0x40c0306271b0e0f010824030a050102041517010b160201110d020705030f070f05091803030403050904140123030109051204050907080f0a020a0e0d210206040f 70
    0x207450388528004140440040601441d681c52400f50500c2c400c110402d14268500750410001d0701c00c2c400005070038040404002400340d90300300c035030785220042410000d80e0b020103410ad500c08100040c5000d0b02d15800c00403240c4513a9480c490a0250f00706015030f074020301a21442c0d00c803d01604074002041e418510501e0700505040041501d22500d00d0315240703010b6081c0300140c121201c10032550030108140180c0c15801c00c058030b80701e821300a01c050503100a104051090039010041064858541441c00c0d80d10f01243c103a0740c3d40d02c0c003801d0242c2203510404c4400d020300d107011405000000d031035841d03c0c166000c0504c0003079a0341e820308080c40a0b00180e401664035540e40da0302e410000e5000c000385e011900d04c441305640c59600e403408011414900600240511071007908010039802c1030b510340359100c2918140185ca6250400c021100524400c200075040584101c000c42480056280d10b25000c0218100c070051101c0c4a41c02ca88910082c0c41c0100041040715941c070001d90600100300d426012 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 542960755 1250 542959505 542959511
    0x1002030a1d01150504020712141605060106200606010503100b0d05040303240b0a05040306360305070b0606070f0605041209080604030c05030c0a0809040c030627 71
    0x802919401007040006403003485a55400d072244403428400800002081c0443e030460400809440d01c080654140b450a020030540b5031101030307041e403004103459080308050000c2c0440080392030400d0782c5690a004507404281c029003040510b0302d403029041444262200038083c0ca0f15031600546050704080c001d802014043c40707000c504119443c1c060040603d26002c0803409050606004c0d0441360180c03101a0044146e00e540c800c25181c001e610021501c0000c2044d0b61110b034400c00b15000e0160b43c000501c440d050480f10f5191814100c041c6074083c140300090f40f00c81c612581c980403080c44404008010800512034a004194800059540040084c140e6450201c0e595107021002d0000b90003140d015a50b2810710062041c20170143d6442101e07420a500c0c41418108440e030744280c020001009c10528000c194200081401980c800032b22403411110004240d00e4051a02c0c4c001c0c51013a0f01942c9000308005026109001e0301c0b040720340d1049603c108400b6080110300c1400880c0030059040d032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 542962005 1250 542960755 542960771
    0x1608190510151a18090105030a0f050c060d1e022d0705060f0f090705010e040b0a05150418060510050c070302090106030209030d090302060f070501060b191803051002030a 75
    0xd00781c0290300300380012411150303580a40c4e0340319100ba054040001801101742400500c00364034005825005260000d001c10a61003da1529074a014418003940340c002001140284140580d41c1000d815204481d10852020307401814030b1049016030b608180030320800c0c041050107401c03621a400707541c6d82c420364228038185894507114a4034100362850030991b89004204400643d44240068100403104040c042c40d901d003100007030010884603180d511a660302ea081d51426552418003000506021301400e10008a5545c0601e558019204480c2c0c402e501e0140320459001c3c0d40b00e44803d440d00101103a00344020341c20100c1d041e4101c2030140929200f2600040090f83e20781020900a01240d074000d40d4803680700061504010320008510306120b43d66200f800166503050a60381c045140c039141c075450b103445040041c0036180c190f104450404000407210140d03019001709181c0c504060f20f401942c00d00003030030310342c0c0700300b06210283c1260000c40305040006000d400564000900e0580421182 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 542963255 1250 542962005 542962019
    0x712050f06010f08060709060503190207020307150f0509030706050705070b0d0c0e01030507020706032f070204050106090305060a0f111306181404150305160819051015 74
    0x40001c3e0440c0b001900b15940c104403a00c420000c241c2c0c8000246001501c5518200014000d804050305422081607001d41e094500f045960581e0380300e036001412190300d5a90340100811070810b0664a40000b2a100380d200c8000b0300540456002005c0580280b40341403404804850607000188101d270280158840001c1c0f521010f00608003170030280340c001801031240ca1001d0b19401e5020402814181007004015000d5004a45181141c035241000704d092041486a917080204810010141c281d00d0101c00500c1a80310028040141c0b007031320100003c0c2d0309ca940540c0d1074100c5120043c020352000700002e50103c2c0e035401950100c03e4640300403400803510320f41088141c1002000c03600f10f40b00c02d00100034480e80001c119030002081411007502c0d130704200e1001c80384008014881d0180780c0310540d2034001c03209040004019504502074034080001c41e00a1b48100801c2d10580c01288190382c00038032298412608103040c20b511200a24071402001008005030000e8882c6041c01e21001c400001c00c2c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 542964505 1250 542963255 542963263
    0x402030a051b212d0703050c0a050409470604060e070c03030e0c0406030b0a060602010c1d04060b03010602070f0e01080c090c090612090c01020a050712050f 69
    0x80541c408008920318070705050080b41000e103040e48002070010070090700114030200d13000e920008814000703c80c0300c410034801c4000194691044040c0d01c1121400001e00c0008070740000001022150008503aa881d010001680c0060401422030b000c0c11459140d010b00440c400451101810902030840644000f072602d901d0b00d40c80d03881d04c081200e03c03c0198502d058454840904100d0200310b50340d05200a008000c1d005441004091503550388807440034001c204807400042070014401d000c2309440389440610040d0944040003528100040490400e00601545210243c180d54079010b400307400300095280188954000d4000755640d501003404441400118041c201d550010409685040302d2041042d20b940d005641000700113005104a100100350424040c204a03103809070387d180e184214030380380300300b00003d58400170008039400c424070150440d81c8140d08410036680792582c800b0040e41c4590f141e032001811900044000d00c0510250314200d030a5034001d03802c4565080c469000e440c03030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 542965755 1250 542964505 542964523
    0x21023040303080a0f09053408011b0f2c0405010b03090f0f0709050c2701080f04030c12030207020303030f0f010605070f030e060c16081006080c090402030a05 70
    0x30f0450030030800c10001c0c6000d0801444038007082002900016101d10362910058607101c0e023188000400821a4108aa440841c0401d01c0000760405540c81032054024603041141d2054030b0346500c5401c0904d8000c540c54203030991543c803580b140c05c00020803400001c0d4800210a800300030050101380546a921409000c0c156003840d8503500d041c06a00781d45046c140c4407104a4940c0012003a82082c00c2c08100c0da0100c1c0c0041d00c0125054503232100e050700360b000340046500d52000a10708002080c945034101104c00e04281c0314442162904108061003017412240a008a0100c110101c00600011032400002a2038a8014103042d1641c1c002821603006840d0041101441000d108030750341c02a00c11401441d1905000d8500b0702d16030750f900100c81c0394041c081c00b0700450203504400342e00c4c1d0104860b4612035502c11b4a4000c45107480341d40003030740c440c001c1180d1886180c0b42c0450725030141c8141400c0e01c22400040089003800400c0001d80b05004108a8260141700c040e100064020131058007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 542967005 1250 542965755 542965757
    0x70f0305041e0c05130221040c1509150302190e15071b05010e09180111041503060f0501020703021207121401180c290309030a02100603021023040303 66
    0xf1000c2e10302010017201555090726165444d20400552204e000600b1880000e2103803950300c00819665401c0804002c4440c4c1c4c481d281c040348642181d400c6607480101c400649200040780752002c003a5100032412402500d502e40303140a0680395144c0303113038000c2c900c480307409200400b81c4150365003804a040954100140440b40740c1000c031007110030020f600100a018000a1030843c00c3c0001c0400024446107015140c074210304408080c801c03011071300307400952404502c2c2409030385c0ca039507803503443d8191403603120200e00007171602d6008100c1c0c01c0341c59580c50840e00705034000c05642e0300350740030004600c0781513124080c94800c400c0d000400245942158a19602440d0001c1191154000380c80c00c0d01d12184d100030401880030a42e40c005070381c010a81051b6400080500600010304540c0e44801f00a040d203450f00301804400c10888400000050252100d43d81c20755411218000e1600d05850141c00000e60180c50391000a5080b44150369074001080817500c00e600c40703008958030f0119544141c02c00c0d0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 542968255 1250 542967005 542967023
    0xd0b100b0d0e010e011404030507050a21020f060601050f0a0314040303150803040308040b030403020c09180f06060d121b05070504140f0c0a360806070f0305041e 71
    0x50ba8100d03080c820755000c519460002e12401268040712488401d004000505005001c05d0241c11700c00101302c40e9411075404040030307103841075143c15004030640d038040e124018401e000c41d105541c407000c58000d00503001a114031303082c58040c600a40b411b4114821803800c02d50303120400210401c00003c0180600d0190b03c001405e80044136039000b403052242c00036440c035071040004000040c8000300b02e0f000c441e50415116229140c502e412418400101e6901d54400c80d0b40c0d0902a952504403082010b1007485030842c0c1c624403a0705841c0d40c4032042250b9940e40304000e404c005021036801c400380380041d14240340c03800b904610a251003042c1c912002c01030303c0350341c004202400142024401c8544c0159074042d1804245010701141d040100014102c5000d45808200000c841e4002d491041c8090390402201708804003000468041c510000d40e0101c41e0f0000c4540000c00750742c003240c07081c020b020550791134044001e03000341a805440003800449810181c0001c43c00305d08141d1764040c550f9440750f4502 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 542969505 1250 542968255 542968271
    0x307050702031e0105010e100612060503010f140624090a0e0c03040302014706041e1a030708090703060e0115050f010e0f040f0612170403020d0b100b0d 67
    0x13400c44a05030000d031140c01d4990709122100d00950a4001107814914109000405100c0400080c20707440d8040c035055802e200202c0e4418640f82c11a4003c2c403880300119416a030f0704402c0010b94414000c000456a80c003101c83c01c100c54032034004016007500a40b03040075030381d503c0e50690149803003151210704500c80230051008255083c080c05081045440ba208203245400d00c1c00390310b95038181c0d00182c0200f038007600d104940c0752310069040e0503a00203002c07549030740c0d0703411035026041c036512014131007805100d101003401182e0050b040b00c402403203514a42184d031040c40c1601e83c4070018000b000c90744500040003000030301034020080c403004010004904071007101e00003609084d15400c694460070494200030600d03640503c0c3e101c1c0100003101d05c0011140704c0c038040b07030050003950b1500c0c85a5003007150124442d207050007142c600601c0340c0c003040a4842c0511640c03070580124000294005c000c948480301241a0f03585041e0403038440490021195600d400000c0c00341e00a50703208075510303240c02007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 542970755 1250 542969505 542969563
    0x3030c06160801050a060c060621020306010902031302060a020102070516150e01140906040302030d11060109140705030c130e180610150519030b040b06090306060402030705070203 79
    0x320714240546003041d04465040200007070908045000d440204030381303032210405010850b0400340041070644100070901c0381800d40c244800ea032143c010307030080c070070314000040d035008900c200c038400d850540d590944000141d0810000c2d90000e045101159020f100690100d1004d00150381010039600d8070714200c0d850070714070301340100504d1024000d00004880035013440e40c1041190300c1c01d40c1c610b5026980c8060b41c8000404a006a810203501803003180800c846180d003054003145a42c0740d580485000340c3e0785245070b500307071903c4540b00c0300d006030010701090760170740244003860304445907100203828032111005400200300e40303900100c4070b581d0380350501c4a0010940c1001080740c10301e80181240b8a00000200905a150302c1501e41001701c07080c9403008a84580244d640140300001c0a034500803101d44c0c028041e02c85541601e100740d00d0510180c0d010300c0e04000311140c869000e400380c01c041d610081080000c0d0070042a813010f010041140c0c1005070740c1030200c8484440d0310521200b40e40c2d50401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 542972005 1250 542970755 542970781
    0x9040905030705011104141e191e2108160c030f150b04020901020309090c07050708011e020c1510050d0b0103061505031207030c0b090303150618120c03030c06 70
    0x451f03500402d4642003c10481e2502aa1080100826500642c50260090f444030342260700c0d5024070007801071006024800c0030080d0751342003200c0d004080c0c0e2816401b046111001101044401084104c0811290114148401b00c01c95660f00400072401d0103540c0745c41e0040c00494210003105c0030802d256040003c90000c1c42800100380b42034034114200252040081c0d43ca02c980354510f4481c3d4200d0001461412060003100c1e905c9601806074bd00d85035070303a1841c0d4040d000d090f03039040b241400310000d15180a202d100365074130000d95000a0032403146403203581c1d103405005455420b5203c100c44020800340c496000020708640b003002c50500703561450030b240b07007224103148a40061100b01e4a00300304d666000605084100b00070280c0d144c0d1012549019034007080c804030001c08604050041010006001c0003a41c802c40c815100f0a1a0014035001c00c1900c2c0708095514050916440c40e64102c2e0601b410a640254002011141c0c1000e41d8000030345107422021011071154488802c02c10040b804403 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 542973255 1250 542972005 542972039
    0x8100f030515090c130e0a1202030a021209060706020c0a0606120b06040203010e0106140d05150906010c05101a1c1b03050c10020a0b0f0610021209040905030705011104 74
    0x280c00b038500c40c411305000901c42d94019650010468442c0449007002200f848007041c020350059922000070000380c8040e4603a0840110003002d030003010891040c800c0640100d52030448002c100d035250402965511000750410038001445100d03052000001410500c140720150038600d10503203019110f03103000800ca070340c000c0000b4011030042c00108812040c01d10900d0650b006801c000036407a6038a2009c1000d805480c0079100d10320704200601862800656201c078a0b45c0080da010b00142e40d940340103540705001480000c21682c4824941c00340903169a118159011040011104101c4000d000a000d0820001140c0e101511404860200314841c0e80038410211181c003041c0810386952216038542408158031350041c2520134070310721640d100b80b100704940c40d440801c1c03401905002d0f81c0d00152a45c220794240c0070b40b125144400c152030000030398114118840d11003524125a180510001d0110f0b160700311038612040c000038000034400e00561110106902c81c00b911a803034021051a420300705 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 542974505 1250 542973255 542973271
    0x140a0c0c170d11130b0c10020d05010e07021617100f05151507120c0f0606090b032b031b26090a030c17040b0304051501050a030308100f030515 63
    0x82241c035020301581d070504c60840c1d00b03103200d20342c0340c6840010241c1440c030310881c81404940300140014030355070150f0246051741c2c00741181400f03c1d542e464069a0f00c01c000c02072030001040c03034075080008a00d41c0e0003116045180d2401c6d10081071400c9540b5099070391002c5c1800d8495114820011003021450b01036151000441d56218808500714085000d489007040241011071a40d0b800c00c1841d00800f0488101c680c040d000001c021642d0400e0780c01413000b40100c2c0c450034100304040015140000d0034006856044403540710f10540322070110382004004034644e05041e100e00c0070000036615058900001c41e40b584502c1d04002410070300074100551003000c180250111018000441030005440a031264142403601459200b400c6c00b5850340d490440c0007514920018011400002440c06180158803500854045807500c0d01e500251a5003401602e0300005140c01c02c00100c0e1040075026085109075501c0e080f11038460070350a401c100c280d00262a5680251100b2041403015190b0560081d05 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 542975755 1250 542974505 542974507
    0x190b06120703030503041101031b020109020301050709051e03010f05010e1602010606050301050d030207090f090c0f0617040602090a24020d050f180402070c030c09140a0c0c170d11 79
    0x8607640908517020142010b0903102030399400c1d503c40d034060b1b40407603425040401c005401280e101d078028007078501808100c0c069403c1002099506001d50040c1040e03c5004000725103400c0625a00c183c6030031181c000b50341c550740b1640844080102ca21075140a480349426124161030455020560303011542302070000c40e0f1503d2420007009a0090950f81920003c440480e403400d0700e400c3c220301e829516000782c0e100919140d014101016564440310707055105440c1645c10795070300c2075045004d150620070800410000c4d0031080004801209265003d0321030140141804884404900b00c42d2403600515000c0c035200e1400340e203c1c1c40c440d108a0a68403188001c0c81d0b507502e19600100240540b80702240510320114500410404082c03e0b03404140c2c0c0503104544070f442d182000042203010784000ea450041d480d0000c994040c0d28010003a21800300d0f4180354550310340340340b40c5000b400c1a000310001c02062001280014000c8001c280407140c0c0c00520f2515149540c503500304aa032540f512003800c1d24 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 542977005 1250 542975755 542975759
    0xb0313062c06060a0501181a07170901110a350d061d010f030206030408070b15030615090c0708040e010f03030e04090b18190b061207 59
    0x60400881002140d2190022540c40907890040c0a001400200800e01484101821200035000111507106000440c1d03480e100681c0d8030010b50701152405914110a8620001403000441052050f40300c1c5401c1400e07945424840d4540c0419400d4030202818518800500d25105681c440c0c07d65500186480242036041c0d215030300c0300b00085492001c4800901404e03000c41b4864400340f6209905540035034550b94825081444c4002007c0c1402029801c0b01302d81d8600c086a08074054480c107903900344201c280f0040c00c40d020481c554100400460341002e04010b89000110350084050060904000302ca5491125508043c1003030070040c6581500010030346a00355507031303600e020703a174014403990301032603880c503460502048902c034075002288480030b00400041d07c0c03801c92003c101101d00076030b070b020031100084003008141c86403500c010748044040d04c00320b80b40c070158143c02040316942300f0803203180c405d800a81c2413141c41d80140a80350422900308000c45402c1000031444410340b00320240000d64 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 542978255 1250 542977005 542977021
    0x7050a0b2223010509030114061201140a11040b120403080c0307093c03060509011a0105130f06090e15030a080703031401090501080f0d09050f01030917130b03 70
    0x2d80048581d0074651900b1501e00700e164052401c49011842c040d00a000482c92902c00e081d01e03140075217065004121107458029040d0042c403c0d10040b04558100300c002d40c0790140b4401c0a85a54850717004580010000003682c1015000242814048100301c840d407850b003070402800c0366500610602000000f0001c2004240c0d004413080191003546007a40d881c0380c6000c80922801d2640c600394504800102004401041051265401c0381c0c4201d00502c01d81d07413251161821b880a4601440c0c821240b00411000d540c0940040e111000540288451329961001c0900c2c4a42c0301d6030000001c03070240070b400d01a90741c140c40c1d66a402a600d0601c02400e030141c801081d80c0300d0020f50080d08a50012603440c0400d072003908501064031000d000308415503140d0100f900141000e00c1414158402c51980c0305540f04040f49800254080d5211201502c0c07401c001c0c005020340741e00d415410107a60300c40313490010300d250440c0075500c0c07424160f0036124041503050301d114000b0341c2c224076848101882041200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 542979505 1250 542978255 542978279
    0x90d0504090f0f09030e0328020108060102010212070302181f03090c0f18060e09060f07020c0904080a03060b1806070305160b070201240e0907050a0b22 67
    0x80d00581d00c00034400101d049084014008101e03018026030030691148180360b403041940180c10011400d40d4000305080c40030310401000c01121101d11443d903c03c5a0140d0700820741207620075810300000d49003901905150710000300441d0040040796000c610510780e6207000041c2201410151070b0075442042c0d40c0421683c040c0490f10210070180c60b001d0103410400e944400030b0007400318804038088a03881d50f45401003031b0f0070700c0004c042c018a00800080c1e5403403901c0545000b84440c0019124549440030208901c0000400c0d03c01540301d40c5a0140c00340d04c0d00c8203020f22a9002e100c0107600c840800c0e100905a070410790003e058003005010054ac0c1d400c00125084200c036040b503d05a443c0d0a0345010346440c080c21007890200140c1001c10b8060010b1030080070300c506555802042032101c5060801200c0f44002c4000005040805060100c14403800d011034002c01844100c0d80344c2541c850000d802b0540c643c20a29030440080b41d104040c200d40c113104501d0b1104800b41200c0c207030a2840100c25 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 542980755 1250 542979505 542979509
    0x23190915020c0d110603100e0f0402010c0210200606040606050421060b1809210f03180f0d020127020f010c0b090c01020f03070b0726040303060509090d0504 69
    0x1080d903c082c90300080040045a03050042d0015003820340364a020307003c1d030750000a5441100708068a01c0001418480e2041820b80729660584650080328055000c1c40f0741c2504282504040c0312a41e290b11000c65051a90404200c402100402c0f0324600241880103a039443c0c0c2c00307101400f00c03d00044c4080840e5501580032010118100c503880031040c140710f4083c14400d001650000e07079418808080d0701c06007596a10840c0c0c8441180d80c0c1c008240c54000b0200c280c0c1034001d43d02402401100801614400210307044400185200c40c1c007540710010f035060003102c01c10758015a0040c03400311505034082c0650302020180307500e050a07180c62264000220484002d00034450314040c42090130701d80c0501c44084551741c0210316040d0301c2c40c1000da4103503640c0441c206507001d03100d05094075042da2000030499000b10361041c04001f0715110045e058504103000301d070b480248201d107400d03080001d05500b8098851802564085a154945406e001e003004014011000540090b00d200b00015048800c88003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 542982005 1250 542980755 542980759
    0xe0a050a0b0a050d0c0801080115030b071805030708031c050c0702040f140c2d0702040b120307080738060a0f03120e0603010f030323190915020c 64
    0x6035984441e84115080e04c110910600712a00d804032060425904c000d0a5040c1c91701c0100800070b000c80f805041d0b203900c01900c0020181c0790090000b03500e03d80304407603400360540d040d032103041c50a40f2500004d04100068004c16007650010828010700031420419191141080703c04200506000b942c08042d8401e0b4500a4002c0341c484450703881c03145243c1e00108000d500c100100b401800d2225245407d0751160903540210a812801d20240f0440392040103000e10412113094074050240c1c0c01d202c040e103030980303140c4e50016143d00c12589256040c8010300915110341c0c0704a58982051030403e000341c458903402064039000704c04c808004e10403640780c50411258840100d046035585c80008403080b01d03680080c401d251850b84000201300d9980c5040c41161019100c4070101c0c030540003405528002445902c60980200d0020400b10f4019000c1c1c200d00182021400c4001542181c03210a59005070202889400f0b90314bc1c40030625440003964001d08102d00360324842040c008002591a140344201038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 542983255 1250 542982005 542982007
    0xe0a051e01210b1006080705040602100e030408030304030c150b0303031f0812030114010807050a03020a0207030b01170d03050618150d03020d0207090c0801120311030f0a0e0a050a0b 80
    0x35050b07190350030210100591251142809140031101030300da404441c4036003004903040c0780224402074001c00580d825035800f1340c000c20490f191180140054409050f8a00450104010215800c5400c1c00210310481c000d40b00c0c140d01c00b1091420040012440f03001a00e12490316001c1c1d8020f65003c42100d4200f040a0b42070018181d915042010381c1c44c6952220320a4401c2c0b095034036407a2103500c00345040303440580140e000300718140e00540c1c01080071142000010010401d500000f8000d034064001845544100e520b071640300d59031118154000e0700314901c06809081d001005280c1004450b6401e84a440c00f03001c1400c00001140304110301880070080340815170002194a004000d00c0720041c0b00040401d0f904121030304003c0e4580c284058004010302990901145800717a50050b0300000c1c01d19603488021343e00e414480080907403021411010040c0f980100144584100045c1020740d1a4561043e658140420040c02080c581c0d01c044d40600c441e06810880d9a4424101c0c00132150802c00309 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 542984505 1250 542983255 542983289
    0xf090509370f0f110712031b092d090b031002030708180a02010818030d090c08160b03060105071704090902090c07051c02070503070e0a051e01 63
    0x3240c0824146000114181040e03001850307481298001840d10b41411004101ca4180c0b000000252810710354200042d0200b0840600011000004c403030507075007280350010b00d1034400207000f05251100c00c401d0001402840c17060017500c0c04031244c1002005200300c6036601441c880e9252001c1a103901c13500b01c02c2e036998204007000b904c05003c400022508540700710350b42e00d8088400f512160003510000b041c2e14a000e4246414807001031890962501616184515610800c00500e10a0b2807124050903000c2407180004285007400382c141400e00c500001001c2c1c60800304c0a0f07190810707001101c2114805010208100301c040c40c2203942020f428680242c2c0c540803130820440704c0028030a00c051249000a0001d0884055802801014401c451000c1d1540301c40d41040d481d40190480a0a9500400c140d0304144020102c000900d02960040d01c0925640b000001c0c14181030390721800d034070108401040340000c00d510460b40e2211817a400315011140855103954890300501a00002e0f00c40d015038 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 542985611 1106 542984505 542984551
    0xc1f0e0607080c0d14070908190f020f15030901020a031b050a0e031e060a060f150f090b0a020d12022506110313030f090509 55
    0x3038801544412051a2590b4000501c4e14961a070350695091a6400090464803a0308640c5442e0011403405c862079040041001943d00c0e0030302801540c4000600c290640440190107450501300902624046081e035044400e00544490000c010031028010540003080f4803512941c051080c440040c07401040d10030b47c0c04810000c62420300181c40034921860191514901c010100e484407400000c504803261442c20740601c06802040402400088501542c00145560004c000341c1e24582005ca582c0e03500d07400980f00c00c2000082e00e07a40c0062140080308007424000f8001961b800101602940c3c0d03140c400c01180c00304a00d00d44400c502e0001b442901c19141404400007642c1c0380407050781d00c400d01c80c6041124030035501d104000a010002011714818202400100741103400c1d410080c142114070608242002407140060006807608460a41c00110350308500f04101c00000f0 = true := by decide +kernel

theorem cover : BRFrame.Cov 542805755 542985611 := by
  have h0 := BRFrame.cov_init 542805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 542805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 542805755 ≤ n) (h2 : n < 542985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
