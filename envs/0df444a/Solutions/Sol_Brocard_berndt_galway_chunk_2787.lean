-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2787
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:44:29.310482+00:00
-- url     : https://prove2.me/submissions/25ac496e-2497-42c5-a5a2-9adf07a25d8f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 501079136 ≤ n < 501258992 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 501080386 1250 501079136 501079147
    0x2030601060f1202030105100c02010c150501090e030712050c01090203030f0c0f0601060903260c1c03020c030909060109030b0f240d0f080c0d020c0f0307050901030807060212010b 79
    0x40c0402c0204003041000f50b20400042c403242d5103416001454050501d4034071080000c42c801a2014440c451b80a41008100b4000c000038090300d410150699420190a021407001000c800d030340da020b201001044404080e0800849a1080b006852004125000411000f900d500400d0541e07019440c611000b10780080c51003408036040010550102a86000b0300540d85003d2001704005e080b4000180107812090354003082400c400046004546441030540c1d0700c1c580920519a00e041c0e03000660355820000c9103003012140207200781c07003014040c44080d51a0042a504010520384020810360521000c00c1020000c10303070626a442c072400e0300c000c07209200c0c10848000b0590000b0b40d07040e8402e00c1071550b05c40d00c00d0b0701e400410202c451351103103a10403803905d2454001c015018280000f1b00c03600c04c121141c0d03134090340050004200041540c00c0b0500c514041c0c10700d62910b241e0b000c2d21781c00030741030001000010040802440b069020b013000604080c0381c2c3c1130f8403050000a074402030f44a800800d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 501081636 1250 501080386 501080417
    0x9021918060509010f15030b0a0b211005060310080f031e071718150d0b040509060708041515030209090d020c130e12041d0103030504210203060106 65
    0x152005000200c070504844c2d032400181c943d200a0b20b0185060b1400341540780440a406900450003450004109404042d1940c03a00202900311b1000000210350300c0b9113001d5030040000c0014011002d54100d0b01e0154140024802d0940c40603048060300d00440c000052060800e01c510b043c0302c210307039028641c3d84e440d8000140c0002c1c0020005640d804041007800300003070b14420701c4081105080b814984035004400041c90019800780000e0300b042c501d240c0080100c1110f0b00811305501c421104100001004040c0411200c0c120f481a51990040c804102c1030750281031591b07070181c81a11510a60400c6600038425140000c45401002e104a03800f07004516054014a1b4030105001c000c00341c541d0b441d48020355961280700b16902404103550004095101c0b0307003001c522a04035100b22001c55540c100aa8041d9102d40b00d80c000200781012502255480000c01504881c2c00d961610306060030950007443e018002d0f4035001c0c030041e0042c09503005860501015000300510b8235040d00c80540c6c2030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 501082886 1250 501081636 501081641
    0x3040503030a0323070f0e01030b0a0e1801020f160c031b050a15021c1106010312020c0105070809010e04091a070807090609030b0604021b1c030903020a0609021918 72
    0x45071204141c13100010442a0740d403001080841e82140e19104821115000043c0d0003801150b070b11a8010b402e402e00030810020038036400c1d005520b1585080d44065507090351038200d000c0c02448032101c4904005106600d05818145150315008100d002c159665940e141945000056006000210441420442403622520400040a03d0f8001004200300390130f00944800700c9640803070f40c0ca010301e2820b404062190050314103424070300b001c442c465612400c10700c04416401007d01c4c0144500b0030f0044071948500c0a1303803400c6078841da0300760410061200542d049505020170781d40066039044808041118034011001800242c03142c0744450a040000500102d40100404244000b03020200308481c1d00c05100021a0b4211807282c40c41d486410000d80a0b10499240c2a41c020300b46010340042c0101003501c8050713a034a05590b8010380e0b20340382c00340c064600d2000081d015801200100021407016008400300c24401000c0310301d41a171064000354000429005100a03002c0559102d50841d0940f = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 501084136 1250 501082886 501082931
    0x114010f0603230a0c0203040810051b0406020312090c04020d0b01020606010806030d0305060d0813150212041502070b130509090a0c03020d0503071a04061401210503040503030a03 79
    0x4282c4a03c8410100c10490320301c601818800341140d0314011650098800e00c141e4018101c2d031019035100c00d21007551140074140544140d0080e441191801c031207a0b0310f41003254215030f003c0d00a94100240703010b0303108c22100002c1c980d003a68041d41c020090140d42e184001c1c1041100504001840220b10000925042e03009101398184490401803000d0741d640040c40d143d4544d014900407a09640f9600410f40c03a01540000514685010030400c0101764460b42010980e0155210003030550602c100490755403801054010158100708800d104c10f140d400f004030100f90081c011200d0150341d07440e12040c80d41c0101124816190b848800340254a80026499088102c1d6030041c071540e000c035161036846c00543c0c400240318000014084080000500642e66060340102416030340c00c070b80b01c050f5042c4034022617013210707039a14000c00b10740742d4114811114107a0b030124054200c0440c000300c0b180c0c115201e08405446620060000048a540030001030000d83c0080d50007182c100d6000d1040003018001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 501085386 1250 501084136 501084161
    0x807030e07121505061f03021c0912030b0d0b070c0b070f09080f0d0e0112061517090606100302040305121306111519051302100e0612090114010f0603 66
    0x8120912016079102000690251104100c1070200340c030441e025030082c480c80c0000309c110b0710fa54000340710762106584803080c0140140e046500104200030220100d801440940341d07c400b0020b0030f440401c0445000540c0404d807420000c04104454840c8500008200c43c010300180688046e43c3c8610ba0040302c00f0000c083c4c0c8402442d00421b08e401194550b1030343d03000403040088e20100d128550b886008400d58440100da0100840c41d201d07100d64642c10000c2c0b6403040401d10000d00711840104480040d440744240c0b4003d840d00f62203107020004991522006981059000c0c400800851000e004440d144616001d5440d03070b030140a01e0090442042c0c0e030001003800f002000c00d00601c01c000c9100c02c0000b24815010416035240e07400e441008507000c4035105000d14050810050040c900d440c1413070513000310390303542c0001c002d038030110740000c084031080d81c00640501410303d20300900d01c0840d0304181d01500100f00200c2d50107150175400000d921100e840c58070007000700200ca801d4410b0700415000f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 501086636 1250 501085386 501085391
    0x904061d030a020304090506190b0d11070209040b070e031510090c080a020309030d0c030b01230a140904090309180b09070c060b0907050c060603030c0c010807030e071215 75
    0x14a19000f0b0348030300442c81000c9000d0b0b200c40001c1d80c00e0703968951404030700321807a84481d00c0707613202d00c018135980d0090f80c0241c3c282460b00c120030244403034007c156841c0623802807910020740e85a81e030b100000e103005800001486801c2c152000300b903505124000b04180c1c2c4e4259207280d4030300003800d41c001c12001e9202c0403020b0b1401680e49440b03603201c0316090307200c2c0f006c99016030b8070349a40401c0c0307246114003003089144501e0082d4900d45640c2c16000a03c1a032400d0303803040144581c403030b1002c41121048414904034001007003103840084c0101e0304d0029407055100340302d040c000160b0200341901c800c440118002a5401350a0041c0c001040c020301603030300e00960400200030904007245120601514038014041440d101404024450700301101062019082404604000307401900b541c00a14a10240c0d01038030300010006c0c10000151107034500741e10010054901c41c0001500d2140c0054102c04c201601c41d9480356556104100800003802941c40084100d580d1b800c0244011200490042c1d0030390 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 501087886 1250 501086636 501086647
    0x30b060a020a031803050102360102060a0c0c060518061005090f0c1902101409060109020304080f031501030e0c090103030311272b060c05090904061d03 67
    0x294001038064815500d81460404e8480070003403402421080e0340003e01030342c000a2240110a0110aa50300d550840c1004040c00024601d540491110300343c49240141c0c0600000351940d10316401c41003040c01d0300d092103050004140c03140c10584000b02c608125010303803502c82040c11402084400d5102051480420200d4109000282d0f41d90000d894540007103220f0b00829024400642180d801e000400d85024002c0904d11010352103408401081214502e0b00714060b00207150fa0750640e200d046a40c0142c141a82003034042d60007504042c200b80c52225040c0400301e12441600b000358050800b06070042c909450035400103040d0703202c008010359940c0043c2045085a122551614156945414041540d03a09400008904e004100050115080d00d9001c4024151480d09d81140d4001c16103583d0740c240c0c2c1a50002c003020400c241c103041130b1700c2103442800200d00e6550001c40684d5507807400c189002146400215a40c0040c0c3c1c0c01c1d10304554601d040c001c1c0002084600e6403d00c0410061814035 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 501089136 1250 501087886 501087907
    0x50304210f0201142a060702121b0c060c06040606050d030e0112020d0c08192901020106090906050906061c06050a20030702071a0405060c010f02041401030b06 70
    0x20700e0021030083c18001040020894000c948040c0c480d0020903d44002c00641c048010440134508686400468015040031442e51840070500d5094160120511450842e01003400d298203542099000442d000320307186003146d55110700003084d0070308026008011703d040904004080f1005544002e100350f04075400000029000000d140c05180c00342886942d1410288002c000b81c85043c1d066900a80f52158084501c0c0e0005501c3d40550032180f5010042186c542c20813040342e0030340d2b01610070340a00c050b1003903c14100501c8030701182d6040c4000b1030300341c0c3d454010780103540d0081404c8030b1041c0c458007041440e050400c0741a42c03000b01124811103100c100004003004002c41c0c44007615140c1c403030f00064182c41c0705802c5108440c0e00034528824135626020f441d22907400990362140140a00c0c10000381030349040e015410f0380e103461240a40f52070320307050401c0019400041809540d54a66249440c22200b41c40900010001066020404403030440014101c40301c1c28000c511500302803040c00038a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 501090386 1250 501089136 501089153
    0x3121d010c030e0f03030f04060e040606090b0c0115120201030c090e070302070807020303160b01120804050d062021190e031216170601021f02070f05030421 69
    0x8550b014108200328200c0708011800000150306100c0d0148400211003034a184e00400502c1115890395a0003254104042040f041d501244a10400100220400e11114808400802c0032100c92800040d40c0070090018150541080c2e02c130704803840c012204002956058020401d454000c0e181c0550780a050107401c43c98200b0140400741016404148581040403800440d400c0b1030b00102103946030b9240303240641181038014000c5034840f80ca10000150b00700011040495190301c210020b04082c00d1605010000070501c4043d5500c41d19a0903002c410400e100030369038024111001c0c103a4030105040300299910100350b5041c1414a0f00c01045140d41c40c9551180180c041c1040100c0c0c100c84841c00c55166004020312642d014100e0028069200301d668114458070030583c50380300e0115403c40c524501b44504494003409a0445042950b003100300c1c2c2c502040d0440004c0005007040003030386600c0c0003620034650032922a840010305020120340348456414140c5002c9208004694a0340c80221 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 501091636 1250 501090386 501090407
    0xf0105070506011e0806040b0105040605031207020603070509270108031804020a0c0b0106030204030b0609132303120406050105060301030c090b131b09060f0f23030103121d01 77
    0x44000d000130f242c0b809003503165600c038020030b40042103800307500b0070f410000039002e801c0c801e50344603d2800700f002515040c0030891070362501c008800e09042500540900a0350b0f80000d01c0c810802c1400c1141d810145e589a036035080d84050a107041c1100c01c905000a10720b9107040c0c0150030107510501c5450720502c101440084a06000e40e030160b1210b0b010002900c4111320702c5001400101d42d407001240f495410b5024208903400342100c4ea00a840f05001d00010a10954040c0c50048243d054040400d07a010007841c410b08510b510071041c4080c1d00d034007a0454201c4281070328142c8010742400144440350007058090401190207038950751440c1d440d4403001d11070340f164000c00b070307190b0024160035640c0304040b2070381020081c428894058400e03007501d403564200703c0c4407001c50940640441c1e024424080255580320503220340a1824a035002035500500b01520001010404d85c2d00041c420f000a0285008520031043e4080c500c0b080368000d411800450380c00c16950812200f00e0b031640e03900c40da9101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 501092886 1250 501091636 501091649
    0xd0206091f060317030403030605180c031008010204170610050102070315061517070305010614390d0203030f0c03180106140102100612021c0f050601050f010507050601 74
    0x1c0140403141c00c0c007000c0d00c00756001414841000000445007103803400107520541c032a580402c000d90f00c0e58100a0a5503480412111540c5000c002445600c0414011a0040000380103041c00d55a50100d260a9074050740120180d00715402004a40d40c1c010060550000a050441d0030300070709020000f5070f01d042a10002e0842010700d400b01003643c00903031180001c0c21039008904405030190101400c0140219001001c0c05608030003c0caa0520a01c1384505071441a590b6400700e500c040c0220b060340e04078040c06c484107401900d0595841001020782c0141141d00202a06030380b44ca1810300c5e00307005103200c8401c2035400410400c600c001c43e03a240030382d0000103003410740e4030713911b521502c200202c82000d14040e80e586000c1001c00c414120001074502c505090703089512010341c080c508002d4900520802c1c031311101c0410440018a4880200801061100c005405020b03940e12800300a0301c61490a40e802d8020340014019130410790b50102c0001802c1c01c0551a09103556184c40d030f00e40e014801c10 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 501094136 1250 501092886 501092923
    0x60609201e0415080415200d0e01060f05030601050303030103030e1e030a051c020a02010909051b03040c05040b040c120e0c0307060e040507020a0b041e0c08030a020d020609 76
    0x8003041c00c401d074241c40281c01d902d0140009416801c0000e80500d400752815180801c0710240b0048042d2280203080c1c1c4803401d1200588040c06c40071716030407036400804903500d0b2542c46580f2000700050034402c800051100c0f030a18a401d9207003005060a1900c181c2055002c0d070420001800400e4100504408582d019180b26110754410007004100501c0c000d000c56043c09000d81c60b40a10400080c1e1200c4202c415605284503990301a00ba6515549510001e000c207c590408024000a85c0d000503404034026104000c44940f209503200280d00c111000c41e0050129031050049050603c42d0594104d070507078007080503401075040a000c842d213000c2e50160003915030700111044103003840070005a03103000c0d0031220391645802c800740840800900c5240280d10f000c000401c01840002c4002e403160b007000641031240c58948844a603c511200155003a100e00c54280002503104881c07040109503140245440300704486000b03041581d00b250207002c66011707405010b101800444c1a049001c40c0d000034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 501095386 1250 501094136 501094177
    0x301030c0e0a0902061b010b100f2610060f030209130e0f0f010c11030a08041506080312070f030536010c020109020a060203040e01140d0209010306060920 68
    0x502c00a801c18080007504044040f840e00307030001c641c0b500f2203d1440741034000e01004000c42c050015080f110500080050701c40060214024003d18001000c094504960f542c1c00014034000000018196040000e03001d41340801c21500354451600c408440c01c0d4541545082200d0000685044140260140780355540075266040c610400203005505000c0701076441e84410140b0042c001e001c1c400c0c050000c00c0856000c0240984088112080041961074008003900c0303c0c0c86060740b803401c14009100666860002045000d4100050400303c80701c2140c1d070b4035515002c5001006101c0c141240d006040c20b040c207000c41d400b40c5401a0340103880c03034032503010702000700b50030400707100c0448a106d1419440c000d4a50b0003550306400c40340c0140c0c025180090302541d00c110490b680d100f50302c280c840c0d400c0c88200610041c8064880c441d0510b000600d081e427800b8090300015120b147c2030b403003242c24640c1c5070380801a1b40c080d8010041e0107070040310b05001e9a81c038048170884e94482c5001555404000c1c0b03e2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 501096636 1250 501095386 501095401
    0x20601030330020408301303141c03091101050309011806152304050402061b0705100504080303060603130f11031e0a030c020102011b020303040213020301030c0e 71
    0xa07070030402c902c03140c0c503002924104007800942c00342c01040201c1c0240c88119030307403010413040840020381505070717003000414011203a41c4c16000713a00c0d46842d044107030900101044050103030207034412020028006d003005400e604110703074803d0080c1038141030621070400d010518045c1c084003004c0007800d00316529a20594018010b25140d40807040c80300076034115a007800307210760100d0b0031400c2a9888007005c0b0380301c170450082d5080008403025084c205404501d0242015005a0b802c1440034240038181442c0e48908003500d4440126083d2541c8040340800c80ca00e04604c00304103801603810614502810203a01986900c001007106004040000c0414101d00340c0540780b0701400c3e0024426146941d0740d2509107040b03a0303a50410b622a10030900c0101c0e171240544600e11400a041d0020101052155001c2e40d84000601059040d0b545c0c502d9801c401248411000803084070035405035950745080e104002c25015140390207a500392040c80107200141c000c113200026190314816003005582c4041 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 501097886 1250 501096636 501096677
    0x904020111010f0e010b0f03160b0f0f030a0c0305011a0a031a0a0b0a090f12020909011e140c07050c0d0f0c0603020307080a0c12090305042102011101020a0206010303 73
    0x20000f0401e0f10f05030181030307080c4042d80501a03210084410041183c075006c02c045e9642e4100140540c1305940c0c2508004541d10b0200411082116490080c00c24040e4030b40c62805400440e801d80718140ca0344840c614080e4103110317180c0035010310544155000d05804042c0c103035000d582a40c101f4556501700385c600410444498101d401d20040c2400c4800e900c03040c10000c0d540050f407150001c00c591a00c0450700003a2240c402d400d031000800c1c0d0340e05c001c0c425000c1040f0050040d140503090355a45a070b4004001c3c118001035100b4404403008142115402040f28406d80000c01da0401c110007841080001000030940c107488500c1243c0040181c0c615041c80070940656900090619485000004030542c041d005103200304250b45510341c8a983e1a140c100541d030300000c401000035003c1105071084155680045142d600a2411504041c3c9400c0d0b600c1a00e078129401601842c60810745100b190fa005064103000d0581c48001d600b011110b10000c0d58402046c0002818000c0014051681811a8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 501099136 1250 501097886 501097901
    0x70f0c021503041b0b07151a041b021203060604050123040608071209020306040b130506010b1911070515120f01060201060909031b0507080d0201050f1005090402011101 74
    0x545141d5503c3c00c1a10b03204c2c00301d18000301c520149011001000804181c104242d0b800d4a40107854207051070340d201c1100008000000c3c4031088690341c590803c4003030b01c5d144550070200c19005d000701038001d1032820192608030b0b00b190341411420100300300011605ca800603101241c4081c280740d6041c00340317954010018a02400705284561020600052503680529030078000c1c12030340c45e0381c80b49214404c288020b840b62036902a4065211101040c0014260780038180d00c088814000050107880c0d54134142410740c207a000311041c0501164503a401c500d686000180c040703541c24400000c1d40050343e00d0f81c460302980f184a00c680c445030105411801100125052000c3c04043c4421515041c0190500b07a83c00b80034503070040d03207803401c0844c5004c0c0c9440b0f40c40c580342cbc240d2a05064046c0652040d502159144000c90355400b0701100080c07070b580d040104015401a17600041101c0c9880a81d494283c01d00902c035002440380c440d000c100c29100c12501e503402640a1030201c0e4a030318003d451602401c4903 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 501100386 1250 501099136 501099169
    0x1b1e0705060d2c100c0f0f1409030a080c010c09180b06070f0b090706210216060c020601060e090708010501111c1809020307020606060a090506040902040e0708070f0c02 74
    0x3c559003a2a1910100f10049454103400041184207280502191501ca0450302c0a0110301200d0001080a00504000c45035501e0802c03024908840c100109040c800745a908445841010030403a980e25401c0c041d1048d164020315110790414035040030300b046010605076180c00039a5450350401c0320b85419003200d00c4960001e02e00c01c10352546240050400204640280c21809184030104800d4441c0c0011165060000154100c4294003228500254000c2c41c0642c0d0001d031222041001418038064650030034600d401401180d07240000180c099084940c00901c0f4101000401c5071060700f0850090540e4020f01e482c003140840c0a40039450425407000045841d403001140c84402540541d07004a0b5016507034100d14016503c003001c2d016804241c58a4006d6040b1200203481030410314060103062500d0318024442036a98070100e01180c1c0207030003203c1c0164002070140310129440c18070700d400035001d14004115280c820001040080d070590007070100801c5070300341410356a8020480196800 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 501101636 1250 501100386 501100451
    0x1202040308070f0308060102151501020f010608030a1806080f0c1605060a140402030a0311031c0b18070212030a0b0a08010903080708040b040f081b1e0705060d 70
    0x2c02d81483d0040b000d49103c22400039400c20300184507944042220500c02d1601e1407940c0050721001d114038a101d01081c5611304610404080c01c10040003401298000c00f001006981d4803660900001c00d660880200e440c0007580240041065503482b1403005ea0080340c0441c444d000752500a04040607104240d1f468829200991481c000c0c01004504e090280c0c01481d001c01004513105044000c000c1c0480c1d0196054100700c0008010034001e050180615501c0070669252070444a0241e00080b520b9155860059031145002d01506040395000340d01c0c40c1442a98405213000d00300250fa1301485052411050300c0840401c0100406401020007103100400c1d6505144d02d524209008110921080d00080c0407000440e40181c0900701c0d440c040c98109800c000d440e5207c0d1540380100300d51034011a84035004100000454002e965080081d0748070320041d00300d14482d80c10b81103401103045540003c54014100400c00d658070081115101c20481c100856000ca0901111081220703021114002c0340 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 501102886 1250 501101636 501101647
    0x161d01091203030b0102071a070228031101200c220c02100f0606080a05070e09010e0a0e01021c090609062409050106050f0904091203150909050d1202040308 69
    0x16050f404c100c0b0b40b05420380c2200c10fa035540307580c0800c10f10000e21100040000c100054405410042180c030701c028501450541c07400590718524202c0301603644199050340e1113140031007856910220160000e204010301144100d01e600303883d910f40280340e41c103d00c99441c00322118520080d120107105454501c40081000da64103030000b07900c0381e440070b0a01c80901e1a0075811294003440740b10303007408c0c5e4541d5921550950b494581e204018030000c0d0842d401d000300034805482c55502c0b038680c40e029003c201080c1c9401d051999644064031884444031042e6401400980000e5548501c04050102500004500c0c1d480070b0400030001c3c80110703006040d00b800c2800b80c10284d02408500c041600c03941d1050101c0d10756811108007101d0003070007000000b42c402c0042c80105080741003e4402144010310001c1c01203070b15980e0f10111521802c8040220b41c581e04241038070f001c8401044020300a0250034040644140c0d100ca03118441c10003110b09100d404074903024410a943d0540f0f0285038040100303503860 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 501104136 1250 501102886 501102893
    0x1061d091806010b1e070f080403060e161406070c08010c030e1c0f05030901230601030c0c0c1511030d0b120a0c14010509090a02070506161d010912 65
    0x3000e41c218040c00c548680e1000142005131203084a55161283c04035a00c1d00381040e6010728140d0040c4020769680c10003110350b20209840100510046200d40e10001d040d0030800c1c4202d003814a00e50100c452f100b01c000c000c00c035090040c0c0c41c0348041d4074112a01d0f55100d0807840c16907800382490b0080066507180810701c0794105d406a0203000d54410f04d1013141c04008000040f140000c090681803c0000c0741c0b0110042c01c07500540140d608072102e44004103050b0940d04c041c1007140f0301000040c01441c290010302105581600c07680f96040d41628210080b5243c03038490000b450300622650403440c01e041c034610f0f0306a124100e544503900464003a40da440850ba0803203005442c0c4614518801d440301100d04890003000500444000d44c0075640b400007901e40340300c40d6401101803601c0d5040c400b0030451030441c3d6842940084c41002010300040c1c40d03812038180f584c5041d0000302404131040c2c0814003174555940101e00341c6010982040081c43c900481801260103c1540e409035006c0110200e000c0c041 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 501105386 1250 501104136 501104161
    0xe030d06090603170304052805030c0c090604060e0610110613020a090c08070e0f0d0f0c0806071d01020a0206124623041e0b01061d09 59
    0x2c41c2c0c00313100c1440c90a40d8400d25001c4500c0181c0c2e0040003940440c248420036290004120f20940788440398409000f61900c1c3e003400c5601818201c142900100301e6a0030501d0450100b43d088070050303034200b04045c2000d0b00100d031110091700d102e01c1451030301d403c0d603455031040700d07802c04400c11501a2485400d098849501d2940303110400c80c8075440540380851a11260322400300c040c491036449032500c0c0c464900070780701403440310b1805420542454138082e0544034400d4200b41c4a00c94441c03041e40f00e1050602000d0442150070540302a00700700240040160300403d0310001311084c0d0400089640c102c40103030710304403a20030300941060011072011003d00441c21110305c10b408a0301080050490020300c2d440240c1c40c881e025069001568a00010300260748411491075072501002401004008080c1008440c0c6103200382441503100805c01040503e407554544494042c0c01c81481381302c1ca5540d0b02d0205014040d0408009003c0f4800d101110421004003602101824603003050402e620080030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 501106636 1250 501105386 501105389
    0xb06180a050627180402011b060e0f011d120309100f1e0b010909021b010f0903020f07030201090e0405100c26090a060e070f081606051c0e030d060906 66
    0xf860f003925010750300113040080e1366204c01d0f40b410645001c07590f100d41c015030b200000e40d008030820240804454000468511450300341c0c80e50703c0020075840e03903441c1949095441190204901c9040b907050810001800900c0140798042c070308896449507104140c942c90100d42da01d515614909007905400300b540b4950009420350114020780c01103c84007000c3c40e09891100d0030280c000349003004104158401036025000110b80d02c80080310f104e80029030b00f42900c004452841d80c0c10340d5403010300101501085007801140c05600900b14161a41e00041c251107524031440405002100025040280601108403506441101040a0448424000c204141d0b035071091341c1c505c540c51041e00c40f2015403000503120308035440080980500c5590b070f80000e00813900d6065450b10500c1000710346840e5100d40b0b540034281d260700400300f6000c160030315909040c0301d51288050120401402c850f44880c00e4103001c0384d144d0700c080440c6246000d50300528602c40c1042c8990150f1a00b500801d08140d1500580b0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 501107886 1250 501106636 501106687
    0x1d01050705070e040305160b63060916060f050702060d09110f0114030c070507030c08240411010e0310022a12070b0c0d0606031401090b06180a0506 65
    0x106c2005145270b03a25250170018001040a0b51008454401c17110909018241c05038080600001c840d03030550100c1c4400c140700c0030401d041d0440c1041040c60b0408200c1c461075511889500c018083c0f5018025002c8000703001100708000c0e00082510941d200e080c111444103802d032600b00a100101d050005010030401c00143c03185c031420007803007880d61140403001c2c0185200111145140c40d0789131002c09580c44640b08407071300d014025000001c01c0000340043d0040c00d4441c060411004151400c810781d4000890030781c18100e1040600000c00c08ac50f410b103810300300c04c0c24110000c81500b0002881d0401c010800401c1c80c1c000140c5503401c10341001c000c0170b0000c00f01510164140010301c1d840c0c0f140c518035000814440140002008100f00d9815a80c008070040603403483d00125544600584000303410030f0f00801e40300c0041e001c0f440000444a030050100203420003c440d92080020380900c940360000c4a94003210100c2c43c1c1503511030100500034100103207031561b111030841d003130380da080500740713055 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 501109136 1250 501107886 501107911
    0xc2104060b040614041d0102030c070302010b040612030c05010f0c02030913021e16060f0b0918030d0b0f0303182403041709101d01050705070e040305160b 68
    0x241181020f001d81c4003a1000d000c418811440400140720040c400e15185503d01c0141002c1ca4000390801c4c0f0055000e4480b0741c40d035907610441c904000c0d083d5445180d291740580d1612500300100b04144150004035945464460b50314503807800e10f14054159140302a5926140c90900c00302260000000d2166010550301001036000020040e4101d005500c1d400d407641e4000ba4031050074181003001010580710801c600c0e2040d02540c3c89020403039424403400301407165119010a07861410b2800300d644070029900150300d01c801c10382c03526100d02442901044860702c8404172482c80e649e00075078500080024044a0302c40428050012200c3c00c1109100e0152010b109440810300d450200c2070041800b42210070318685490b0780f04400c040d195149080e14034002d101092899540da004a0140c00305c580d610760302d01040c88018080c00c50361081160504c10108011000a8000320308030301140c80395400004180d90301d00302520944150034281080d0442c81c4160b50400c004500000e02035034018801 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 501110386 1250 501109136 501109151
    0x50c150702070806060915030f060109050604050c07050d05030726100f0f0513090212010903080a0213120c0305070602160f06080604050c0c0d0819140403080c210406 73
    0x84d4680405a8940750041c103c4400912100a01e401140340c1d49009001c0728486510840b10707030704061003a04125041c40e222014804145428012181c1005c2c08081445c03038000207640307041d503484410600009009022001130202401082e20600c80f8180807000545d01606a550500c44d50049900c50300d05404a0808070b8050100c00c2003100780c44450300ca0386515130a00301040385581c14071211340e82d41c54484201200589645050b08203101416002044211951030003604014000341180d00e994418815050210354001b0003408440c00c41540c41c80000c01410304106100480e00040c2070b911922074002400c681c00180b00014100c20a06032001685804000f02120218420311000548202c046000b03032420340d1043e600721a00f90b04480c54800600c4805080c0390348404103d004c60134140420041c0702c50004005150800c4071020052000d820f03403404140300f009040601004400ca0004e0000c2d0240350803203585100a01a80c85200003e243d03900300020100e404607405400e0400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 501111636 1250 501110386 501110399
    0x105030621070801020d0e070f0605040306200f07030f050a0c1104020714030a03050c03060a03231009170403080708071410090302191e05070b0a02061812040504020307050c15070207 80
    0x10380904ae00c50350380c0c843d8a450b01e5525000d0203030582d0701d130110703c100c48100c015401c0742648005140c0300c1b0200320342c0d544030080c90601602c0e510007190700310141700081002034240b9a02844050301a0390150074207510800003004103000b0701981800905001004001c0305505070000054213450500317940c144207a40e900a4851480e0105031241030300558246070620015603180d8409111210302c4008448031101c1c003c00d41c1c41c044800210f01d841c140c0d0f0b03070300c010288101c0c003008a04048900c6041e44c942440c41d510a442d520900c000a00410703004a814010003d200d840892100980b80c2111800703180088440c4c0141402d61088001d4031580c540c05440c0002040584096600400c80b00041801d0740005000e800300d00e102160700e805120004145940b499028004d80342095004110720714211401003807130001c403100807465521076034110400705c1e0701d0f00c01c0314117441d415100542c481c0c8440c00305941501a40d4102c0344540180c0400e40100803604002c07a214401d541d00316a0b0140e510708 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 501112886 1250 501111636 501111659
    0x50708160c03020c010c1b0f140901230a0e010905010e0708040c0306112107030e120901030c0507080d2a1e11100603110105030621070801020d0e07 65
    0x154000d003d42c10002c40304884d58003900301001c1d4540900700040e80082441c42d610790209031900b10034580268401c0510405001c042a0100c50000b0340e4554140d50400c030000240b11003029100050040210f80900c1d15280c484188000342514a4203c000d561035240807409000309006000788104080c0002d0325040c400c001c503e0160350024104a074050031344e01c030341015141844045a42d400c00300000517000110440c1d804c0840c24204001d40142042000142615128240d000d295032220041c489010b014130110341d5070b04000d080c00100034110840c20380d09809010009440000003150f4081403001c40d8004050304001d414122000011f40d84001040009090a600004040c956441048950059052420102d40c108a95107980203010303503107001e04103a0f54545c1c040c1c45400400802041e2910001c9485003424914218a02480850000080750310055482c1801c0903c560040b90140240800781428500a543d038841c0c94601c08040c01130104020020b00c180c0030002a40c103401c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 501114136 1250 501112886 501112907
    0x6051005061b011b050c3c0a020409030302070203070504051605090409020916021903051c0908040605120105030106060c170c16030210110d030c0201060905070816 72
    0x2007090b820241480c1c030244055040c45080701c800d42d81e4010340814004903090400c0104900e41e140c666544040701c6d0142040c104000080160080310082401c0c1000c245403401100c01c40341100b510301021542a41c81c001d051040a5040740ca04203044081c5079041d00103000d4907009900b22100c880e5034030f00b8001200c604441d00c1800310041a6203031049d074441d6000704100c140041c0701003140303110350300040c40070300054410860b02221840134042c541d80501c42d020105078400c1925031680819280a0003d00c65880140794058060b40d504106108a50002d412035400000c0310b07131a640c5866000e491a0f05c0903101409607504040009030078601402000d0030390701aa5510b0700740d5400c545e40c0d200e50804a01004e0140300c1c041c007291070200c2c2c04100702c1414440307407100150490300d540140644420100c07035440400a04440740890300c400084d042400103400e01d800144034403400d404a0040140382c0100da2481c0c105814011001d40c0030136520b008a2094010b0703240d00140c0481642d0740501c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 501115386 1250 501114136 501114139
    0x809011406031209150f0a11030a170c270f0f03100504150509070501030509030304020d0305090301021e1b0a0b04030c08042c0a060b030c07050114100306051005 71
    0x24010921030009043c000e400a03d6015100f4100d00d1807203000c60020703030002000c1c50782c1d00c1404210110900c0c1c2c4114070943c40c810320409903142c00e19160340201100ca540030403010301400a4085480c44084400301e401086084110192200d4005000e200000c50000c0244c0b090140545039299842e00000300c00000c10000c004000e80e2a076079950b00080c2600a0090704e08031044070a51001e0613490085d07034800c1c01c241c0080c0140f207050400150131503070b000e442d140303250388184100300040c0c42d2224003c6180703805050841d210034804000034060b1058042c1c10880130070b880315a0300380b103801001400200001c401c01500401b48540016644d004409015008404c1c2d400400c01090040d1031054416000ea48a42d01d005d03241c14101100031042070b99000c41400850303460080e25465042d054000000180c00d01c0164540b00c2d000c11079010103042101884000120301d07007003240035402115000000044441d1a1030710035441000c00400c1c1c4015240c06003071800080150400e1503811058590 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 501116636 1250 501115386 501115393
    0x50d1e02150703060803120a060e0112060b19140f040504200d0b0f0411030303270703050109030f091a0a0309151107020a050f1005070309030b0106080901140603 71
    0x10000e0500707030800d01405550a05a5416003c14003e0f81880101241024441e85801c2070034000c21040071922607a0220400f41c1900c0010300001329041054500684c1003180811130504440004043c0700101c81851504600308200281d410648500301008140441d036440740010a003044c00103540c801c807001803c0b0107011007018004001e81d041c480c14048040c04172580a8259076079050140c0040d1800c1c80c02d100dd4008000801040a0840350f03036590582c05141103040c05803900c3c44800600e50f0032808107511100c10007070a6030400441c0f0045070024000e000a0056041c0034083c5c8106c0895100060345030040400c9103403800c41021041e03c2a440c400d807804082c4001100207118009044400d155001d000b010801000c0c0101c13104018540d44480d42d40c0f03031a10400503d0546640010b005d5030a290b00360442c0e40d98984d52011800290811594401180c0f6049410b6003464000030951051341f400415034a40c000e400900c02d954550081208020405804100310710403140e081c1d15a0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 501117886 1250 501116636 501116653
    0x270c07020d0212030f0a0917150a1112150306090d0c020904080c06010602160504050603030d050c120106030f0507020604050c100e0312070c0e0c0d0207021804050d1e02 74
    0x510f2003c00e60b107616000c06403414000c1e0002003015a601c10102c0c07200040800c0c009101e5100c0305060b4294403c2c40c400109503942501c50030b4500d4040007456070100954841c914010750340d0380c4044405e403001304105001107141000c0070030072207140107440078001e1003140c1c0000ca090000084441000a41c0d407030707540307a020f407950030052082c0c4028811100f5000a03c44100203a60400116001e451607801800e00070844c2da0300210070182e6540158812802c140611000392000710440c0c0d954080040003003403035035503250400c100d0300c42c811010000414450000a40a9040d480a114021420300a010a858068049940740800e0350050301d00e80060042809515040c0703149000e60110b41006183c0241e1b510029050030012200b5a4070031000081500c1040742d01c1507000b01038820407190900f641409485d400440c09258412160f05900045080c01d560303406488920882540301090100d01d0b041c41e02948501c0100103401c0410400907540e000710681d0300d002c4c09181d50640c000c08014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 501119136 1250 501117886 501117889
    0x30c0601270f09230d0203070b0109050705090a03030806010e06180d0203070f031121061302041b030f0e0316020103020304020d052b0504030c0909030e270c07020d02 73
    0xe000309034081c08031035035500848001581981c000c2ca0b2541c01034510750804a102e0010500b09036541720040215041080301c5000920b00911b202d0544810b10400205a6030b40034090300c8910500d0011540600c100100000300b540c40b00000e07100b800700717a0320352444543c00d405000540c0921070703030320800c10b111890349001428800c210303000c0180000c085030f048642d145041c07101d0101c29001500c040c0200052a6882c2c01c20751304e0040c6406d030044d9039512074440c00d400c80b61540d501401d9200480242c0002c9000d41d9100d03081109000700c4604d1002e1018000b80f8040e00034a121052051818103010502c02d15031004015142c00503540b04144c15900200c0d801140250310043c4203c4c0e00270041082580428002c00108018000fa40c148e00c0b440e041c1b002c030b40c017140c250030002e04c01080030400c4248001035124981e901280c0b0742c043c1c041055001c602d4295401000036903407a42040f04900b05101100b1240119001400c060030000429103425640211921070780f01c0107500405032001c01b1005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 501120386 1250 501119136 501119141
    0x324010c0c0311040b1002070918170703030e031c0c02060615070c0806040f230705010f110105091006091a100207030f0c0905010b130b0f1308030c060127 68
    0x3410340040c00000c040d000c802c0006c1214141d400030000503030242800784500862440340c0c03188510180282d40c2c0301e14050740ca00100e01144d0442c40944d52006c03071042e003018003a4101d080891a40b2055030b89822000b503c3c41700e91003139110034441243c1412014a44c0c07a0000c1003e5006100140090400650020911007298030202c0c04031440345a2081c00103880c2030602c00f49000da44501d1507981e800342d450400c10749200d005400342c81200f814501c00c054442c8001415400c4071001e003000d91000410728803e032a100c10f21015440e05500f400204820780c0c2d004101d8842030100444200101d9071104480001c0343d00d42c0c050001505900f0200002c14680b82e04841c1c801c42c81481203d02c07003616681c070f2803104121b00c44103e81113800c0c03400501104645010310b44c00b60046010490030084040d01c10030600240340326030700d04070000140740d4001c01d458030200e84039011030040708001c255449076450794a52003030761848201d0140b82c0c0045070204030401a550b5070266048040c42400045400c0c000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 501121636 1250 501120386 501120413
    0x3080105151303061d030315010c020d1a04060516080a150b0d052d0a1a03030a110c0a0303050d0222030501020a1710060806030c060324010c0c03 64
    0x601828099104540340100d1144081c61041308017141000141d07030340c940d02e01101680d0100070340050080000600b16a0407687c060030702441c0040c42e003001c030700108030b40c8401c011024000300c10b030740608a403001450f50780070b0095109481c2002556580d421000b6030144c0c04090710700040c0040e01003045c5d01c80a402011040700841030001c4101d03601d0212061652120b031081508a07198020003a90685129980a80c0d03000d020712409804900344142060400090407036421543d00c402e030840c180c841130306413141c1031800390844e80e9134406d2500150444200348001c071024440e03000d04465504200659504803581a01c0e45400c040046200801941103000f4000004540042c3d00c80740301c0c4481ca004000314007401c0016a5000001c50003040140b40303502681c81c1c2801c64050096200080c0300c1001141d945242a40c516142e44000078100341404840e540c2c004000320030322182d0306056aa01000c0c1e250b032004040c0090303841005490b0344120a002504004140304100049038001c880600f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 501122886 1250 501121636 501121669
    0xa06050d03051308070f060e0402090a0303260a09200105040b07030e0405040309030b070309020a140312030c0c19020907080702010f2d051b0c0f07030302010c1b03080105 75
    0x1d801074135004202d00c1c008042d03200da8100c007503040041003000c2e001628059200300544095150004840210308290010301c0300404106c020a080c08500050030302e10131072000a4200d400d80d900b041e00e600da0141c4110b400aa0705082803280103041c02204c004404801d00040e181d032401c0c076180800506058010030426824030030074080140f443e82c1d451080500c543d21a8642030350940c00c50801d00d40b00c0c0c0c0000c0280341814603000c40d02c00507a0b60300c5600f40441d0407100d03004402d55548008079040410170504007203004404414410107840324406011000030301412183c0d025800c00c000a01080c503164040d4120540002040380d1030700c103d00c100c0c0d01c031b81c1c280008901448108800070445118014000103005070229460651b070100c226801c02242c3c21506010134180340304061440140c510b400d003050200055024103500b005d1102503400200b01d015a002c140d40e07410040d010b0700e0310b80081000580c0400c880118141c084040340e10160305030b43e4a2445030f0804041c00080542000e0b02e0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 501124136 1250 501122886 501122917
    0x18021c0c0305120a20061501050c06010906051801060e010c0606050306130c0609080c040c0c0b150f06071e140f0106090f060e07140f07030f080a06050d0305 69
    0x710108070200280503110003000c5401c3d41d60014544e0083c0701c1c0140c1c140801100c600141184007807000096519080042d440f03031015048100d400698003481607540300300c014000c101c000203480c2e54561141d07003220310641e0700161082c4030048076060640240078a101080c0c2c2ca001c0703a00356500c90086e000d111489510300003000d580b56000680b900344d00b100ca1011100c2451060b00c20424500c240c0ca006200a00b0002d41e07507820044100e4841c00d216801c0d41c041da59400e00715207054821001c0819940c0c0040310f40c2020b0500203056090383c02011a124060081d1040c11381460604100300c4150316040000ea0425400c520880c400c00180b81c1415913180c009141d80415400c41484010251a21078000280f0140b5003040c1d88280c40314604074291040c5045810042d414102034440c0d4041410b10741840c001d20406504001c80c0508001482c09000c0420305504064003e138050300e6200745504c60104c9592100c007140240d80c524020150044a0444c000000034040c4001d040d0000c810b0146 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 501125386 1250 501124136 501124139
    0xf0102030f01032a08100c09080d0305041a01080706030c090b030f0a0f020f09010206060f010c03050a02031608120f040c05120f0123070507470a18021c0c 68
    0x10b690f5810b5030010f141caa0800f40007103150030824440e0081d48880303420308d00412032600914584600f5814400c105241c0c4502c001380412401100f0803880498406007003202c0c2d6117500f205a5078656502482c000b20307143c01c3d0703121320705070250010038100c5480c0100c1d20301c4c40d5500780111054180140c14031300420f0301c0711421409240140041c00464800003038254440d04884002460110040c04450042400f110386090a0f684100c41e0318240307415045c025907440c1d50708801c0f03103180b2401051503590f215240c060010080004003c00a50341c1c4038150300c50320f03165040784128a03501960020110303d000002040310341060104c0c0765200010b68142d0309803813001c1c00c0290948072142e01c114000c4590300081e4041500b00ea202c203422498603d009810041c080d40d480702001e44100d40c003030500d0040d00e000116503546015268100280d4107080300384004204010030f0383d10003641c11380403040c20300200f4005542035203807010546400a1040c880c5660200c481c4a811501080c140e819002c03d540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 501126636 1250 501125386 501125453
    0x3020f0c0906120102091023070b0601031808070f0c1401120f11030f062404090902120d110d02011a06090f09010321050301050306180f0d020a050f0102030f0103 71
    0x1038407c2c8440b207840d10b020450107440030039040d00c4e002c0c140c0da060083c14480000400c0801050540c000780c282400140d24610070600c1e0442c00744110000c120b14800100b800420040b4010755002a00c10028641c04549524910035480c0c8400305440c00101446140c1e1038130442e503001040410102e501c0001c2c0980050401a4641d0003140c4030f02410324400184106406c04091001c4000395590702483c0c160443e04c4507448078459441551505a141e03400101550b90b46c11050b21154101000c595010360b41d4038019022000b2164020700c00d00822140204283c0107000d20b0000c05c4050040d44582007240041090640103802c106411150131039400606032681c42485000e580580002031902c1c05142030000c1c8500308640d9001007140500041115450008032190003060000c1540892106100070741d00d041080c80d034811461140740340e00c0c01050b4004c142a0a000d020701c080e034590b00b0080c41e02c6801d03403005960801000301140d0040000c1010b0483c02601c0c211528040300c1003268485 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 501127886 1250 501126636 501126649
    0x30b0607050309030d051e070203120309010c03060e0106140f04090c09140d2316060f090506030915070903080708120603010c050d02130f0b040303020f0c090612010209 74
    0xd404480e5644000f032a050185010000048090800e02d03001c1d00c0c0c440350104a85440074540c503c41d110307100200c1d004003199814458942e4448480115a4483c641544880e02801c00400c0150100785030800100359690107080e03480c11380305a80c80e0b400c210076404401419541c49808a171300d403480240300c0400c14012038025103440c0301484e40d8400d0342d01e0400c115244402441031000740f0558201e0b00860005074200c1e200f10641c0040345082c01d80c02800c407032140c10314003200c0d03005440c500311190203d517440e00300c2094400703c1344d03a41c1c41c3c0c481d15480d003040c4081484140c51300c5486034402007450000c000c07070341080d5901607110700d0035011840d40d1f99210143c0d900700800c01c0381c20840c013045500e604550b8208181d407040045000b03229000f8982c5010b8070902c6040a0070495076000035910554455400e00308000f445009030101c011940e4800b0220703190041d0000310014058580c48002e001f20001c0d40c6140c8480041c43c07401e884e102d6408000c42c0c0260791050300c0d515502070060005996402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 501129136 1250 501127886 501127897
    0x11a1e0a080717060a0312020c040f0501210b040f08070b040305090f01050a081f03140105010311010f020c01080a060e07030c0e030a1a0a0b1315050f09070807030b06 73
    0x7501c0785020760a1000c009040710070201094051903002004124007a901c1c005408122504041e03051100858580b00301c6c145900a110f06400a081030074081c1501401d03404207049031403801740f950f41c0e018801c0c5000120340340b403040501031100352404103011130900413440c85550322500d0094980845540e824440c418101c900b85c4c085807000c81e601d8480d0400e60241c194444091816a19020944002030f2524001600b44c5900528141d5941040c18103441e000f4095904010700100381c0156680c02130107403509010440766602c110382240c0240d40550f2940503c04401d401800c0b203024520011694484002d150184090b200c80d00040c150082200c540d0181040f036901040e00c482c0a400503100d0140119207500941c040848800030403108501402007030107122201e0282d860302c3c3c031401c0107445d81c0d07600d04c1e40c4119005103544c103021071584094440750034282d42201190b50356081154000401c003a0b103400000c03450028640740d100f8030f440caa0011150400048203042071000c5001030300718 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 501130386 1250 501129136 501129157
    0xa0b040602181002060106030c110607081b12010807120b0c0703030f05150f2209020a030203160e0f04080301060c050f0717011401150c030e0301050a091a011a1e 71
    0x7006001c402d515008000c0c1c818401d02b007458000344050300443d551580140721404111f070364408500001d600d02c2d87c0b0481480c00c0030090303072600b10700c0a070610044030078440d0384540d118507000010a54841d40074101c141e508007140034155030b2414845c41c59984206400c808255603104480920721141c4034850045405510380d0070696401020b100b0389002c2007844d80c0c41103606000044180c90000080c1400301d2906d4008180c194440c4086100003166800082d45402002002d0308200c58006542d0201c680044000086131907014120711190800e56024140c1c02d41000140100d900400000d0543ca10600c00c8505110301c01c0d10742400c0c0380d0305030021614130713510090158490b0002d01030160840c000303e291021551400f40d0450580e8007243d0740380140000110f21400741801852030004c0008003070003e0002d0f20b0a82e6092006084e450411210b003d030f112205072240c4015000300e41601c141000c0501c040700b404c10406200d0700300e80084c01b07080c2491004c0e01c007461310503030150090307042 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 501131636 1250 501130386 501130393
    0x905100203040e0703060302132702030705150408010c1110090302030708090d020d08190302121605070503040b090a08010b0a0b0f04030c08100522020409030908010e10050105030a0b040602181002 86
    0x61f520300b60f103840ac41c0c4070030f4404481c0d01031702ca80141e90081003500488004a074004105188218003c0c1140229030182c4015440d04a0700b0002e03d40051403111048141c1e0180d580b031503100108038040b070b00b0560020f40164018000840040c90000003092002d00003001c11400c8801036000898844d0b508c1011210020045100221600110302c2e07025070070007030f040035800c0c0103400f0680540c8c904010002e07011011014080c00015010364104c5451070f030044140d0f41c1d41c6458890100b0b90744c4c008110140151004600040c1d148410703c01c241c0e07182d40081101d0340382450316191454540146840c2c0034045002c2000100180780007014400078200d5801410740b2840c2c081c611030407680001c0c14442e464840c10103509883c1d10804500380703155812a0001800d01c100d00341107840712007940080e0019880c16442100d8541f000543c2003004000300300910490ba203c1d814540c8030960110000c2c034002017080440c0008505402602e01102000a1000001142400200b2807010101c041d405600b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 501132886 1250 501131636 501131651
    0x7080414012a0519020d2d0c0303080a1a0f0303090415030204050c03010b2502040515041a03070306020c010f0c180b040302130b0d080a0f0905100203040e070306030213 74
    0x3c01031080d00c000c40c494480c900005007050300030920b5a00d43c100018000074160b09100108903401541c400c294009a10301013a148561426800c9480c0724002603022039040030006190303924074021039010000d07030340882301d51104550600c10941107044666516000911040340140c403a842500d02c0030b070100f20544100782c698011b0008440d805003001c01209004c00040c40b0b0f880c01d4208403488034580070500342c0302d0700b06000300080081424900a6002e8100014010b0007988032440c07a1080604907802c002032200d5069581059034032268142d00f40c0c0040d0130801c0451a903a0250145c002c004001140f100c20400759581140c0480c03d917000811107030f002c0c00740d4250048a0904c00b03041c2100c105482c00d42907070001404018800c40c0105002e031220b59000c02a260405174002959000d4286a10792100641c081c002c084603110310000a20030460000b006e203015001d50104a545401844c0f82900700681401c0080c001804a403d140d05d0302c0340000107844110004c0017000d0305200c00200342 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 501134136 1250 501132886 501132893
    0x3c0901060608010f0501050a05070c0e070305090c0102011521050d080405150408042303071401030b220903050f0a0903030306231c08030a0507020105070507080414012a 74
    0x2c84180c002003030788001c1d11002e01c0180d820804941110f601814150b0301c600e2289810349295120742c021039410340c04201030242c11501500254002d03e2040140c034045207011004908a4091342e4550280d2042000200640300f20401500220000103404502c00c8200e030701c4261a0501c40841c540c0015101e01c10001030000c1448030b41c660303c502058154150602c0d446600460080f40250801c903607100c0100000d01c03401c14542c2d0602040507081d074000c0d41d1f0300e0f491014a00709041610b80402d0800d1300b200c2c180d15100d180c0b65241c000740c042c104050314011195500404000e02c08405111041100300da00541180240c10500722a64500c43e204d401d40c81c0003800c1c2d8000340c1c040d1102011082c04d00c2d440e0b5040f07118031845050141e6020004060b85d181d8441d490b00203400c00342120b080001400190101038101e10b1080c0240c0c1c00030300c800d40340c0c00000c840a201c1da95018040c1c007414801032000410140d040040254145889180c03e14414020b0248002c83c035441100074840800c81400c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 501135386 1250 501134136 501134147
    0xc03030f0801030302060f0a09020d0b061306230d0215030601020d0f0f0c021c030c020f0f010804060c090b03090d0f0203090a0506031009060e010317033c09010606 72
    0x1400311615200519502d9940d02a580c0d240242261041070322801c0041c01281050780411081c6030003c203901c000103154203001000d1070302600d41d540109000401c1004c640c0281c043c4004a030050718400d502c03c0b03003180b1140090700651784040d91003c61205510b01580e103c450000d8461000c4060745da032801c0410001e450078841c00c00d11014080540750700e100e203e41040800020990700e00b08480300c500782e4400243c456010141c80c00703034901a8030540c41815071250741c0d00191344c42580c61520b050840401c228a0709080340c03c2500142045000500094050f040f06001c2492030500c0c5504945641c20103040c1c2d0002c6030102d003a5480b4000103202660310141360b0000e110301c1d0000d546404030312008945020201d0140074004d0318000081024003151030080d030000c203042e8004005240d00c410798203c01c00420b20054034030103c1c247d1f150180300550000c0300e0190300a054016041541d180741130f0f001009540e0414030b446010068000710080c02003c851147c184000001011420000e000e042d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 501136636 1250 501135386 501135407
    0x30503010e060103090f0807052805010e030711270f0618220c05040603080c07060503070903060b031c03230c04060806030a060e0309040b011b0303020903030d090c0303 74
    0x405045c4010800414111550308404a13049a401c9940300164105245072848800603440d00310841c0c041c0b03900b040f20171102c0c00c00140c880c000910490300081010365076030251000140050141e040301440500e048070031140b8401b050130990040c1c140d00b0424100c400c00071166035020303046640c20400d0910b04203904440c020020203869880342406400d00780c0d4050325104281c04144600042c0090100d655000002004010800d001258581c41c01c2c8030309420540f09000b0a2280d0740380422464010000c3c0c920030f240365a100c5804500c1c50310b5580140413072030940352705402003c0480080c2c0d8160380d11100d150188e40c502107260900004485c0685100041050140081d50103000742c030506002200d04441440c60043e03600e468a0380060b08100d8400001400341d0b00d00303607100d04101008006003420070000c50b01000b00b8003138000190390203002822606400c0c1208200000007038000c1c6e001c0e01e034140300030b2f0481e0b003003040004190b81143c01c8000261055403109104108150340000c40350f1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 501137886 1250 501136636 501136639
    0x3050a080304030e09040b06040e010b0a150801060801120816060216050609010612060f0e030c0105010f0501030203041a04051f0b0a090b0901150c080d0b0429010305040c0902030103030503010e06 86
    0x105c20349850703100c691850b000a86403511490b1104680ca402190035000070030544402011560000d5540005130510024500c0d020003149107000001150350044030020b04840300c10711a2100c54256651b46040341c3c0c4402041c2000300d244c000c0d480d000c202103101411800c05803a0811507900c001d4180325180480c020110031003681070200601010914680e02d42c905035100340c0c04180b0155070740e1040c1c041c00e0250400b6049200108145107044015000113040342d010584901d0380076116001101613200848000d01039211144d04824548240c0500e01d074010b0080059944a00c0d0051503240c00350580400741c010300d03446d040c01141d039140c0911100010f0a40080c1004112610408505080014498400c60440e07000e00301e00b0705801200080e242d13607401003030a27a48404441242e0003c3c44400080750082d071501c1a1106145002c0c5a0b103650808a4421800310001e501c00440103400000c100302d8100502d81800107002c985030002c5e40c060342c031076110300d03032250704241caa1120b0000041505 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 501139136 1250 501137886 501137899
    0x21b010b0a060c060b0409050d050714060105010519020f030c1f060f0302060f0d0c050c013909030203010f2306060d09030302090316061b110103020c0703050a080304030e 75
    0x100031450700302115040484e030000000c2071184100000900501d49000050941e01030b003038100301c519a10100424040380300346181100480c1260a09540d0082405a20702140c010000c403031580144403080c1743c1c981220b10444001350002140702d400c1d074100c955060700e16401402410400030f4040d403180e80130030104c030003000341a141c403940c496004031902c4080d010344d40014012410b800840c04079401c001c004c4000344200b103107402000344158000b0101030035035441d05103d40d550281442e006034030f08020900d62100526040342d4000403103881008042445000c0380000010788003030186010b0000341c40c00c0094400403880d0341c001c8142244480d080007000368002c100301ca5441109403410030100c1140058403d03442d2a041d4001d100b02500c1c40d606108854404e044e25050382c0165041e60010b03a61003199030011500c4811108840000501c0c14402d41d0240c4000e5100e61301800d00e008001c07080b07401d907503920b031150303400d01d5074400d025158040000100800d05800990b00380780300d1001d8802 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 501140386 1250 501139136 501139139
    0x908010e01020f07021c06140103020f0d0f03050306011b1b061b030c030c06020304150605030d1b050c130507020601050105070302030711010908070b04140604060c0b0604020d021b010b0a 82
    0x5050f80d031003007120007445441030700168648188420059402d0341d81c040410002c0c01ea20100d0020125401d01c4201d1241c1c08420100005040245c03c1c070403c40e0380302403100d56003019640c09444c1034000401d407504210303c441403802108101188058001d008a6403c4041f0482c041d802042603503c1e080340042c0500110b8900000c000c6c0c01004d00860b40510b4104944240d52504896511302440c010f0407060000c0140014000076454028200d00b1030403023000442d0b0b0391030034075464080c21004c00b4040780030b18030840f404100d841c1a141116204d1429109000b1000c000103006107036100750810810364490030499038513010004103014040900380780303050031030903a0000d5803845140c40044c0f40341044542f840b5140d0041000d1000b501c02001915181764540141104a4006225101d0180780358100c006d211b0404804603807e0304d02550b15007074001f04a445407111402c0c06010a60400d900b0808890b50207a10f2010780343d00c0c40c603000307402890308004001600351041404110701c00c0100060 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 501141636 1250 501140386 501140407
    0x1b0e0c030a020c030904050403050903060609150f0f06070507090e07050d0303021e0a050a20030301030b1e2d01141302070204020c15010e070f0525030908010e0102 72
    0x10340364810004100540c0e903043c0c90598070b041d8029a0a8603401c01d0400042c0001c1540040250501170001d03805c4a54581c0c41c0000c0140380700040c0e4070072150381c04608103004a818591102c0b082d166015010710303000000a40031400c2503200030342c103079506e0b0405882480241d0341070060710074080307102009203692814140002c111041c03030680241070541c00144a00c55410400752a102411541696509c5408512000d041944024102d40000300e41c0b103180d22009a1a502d00305020b22488000e60441c0e00315611b0050700e0b000500141d2208508452041d4041c010750b51543c880e07403007200d40d40b42141042d804880036690480e51440140d40400c010320100c9080c85d1401c1d9010422500e01400769010b01021000788141c9001941040c0005007200c044000001c400481c00c2c0f04055100c0181e0380c40c00303401115201660000c0c00102004039400101c2e00c580c003c0c0001140c40d14803908140c2e140e841c030826074900c1c26011004560024000c07c4200000c3c4908128250114001d6103802113900 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 501142886 1250 501141636 501141661
    0x3110918031605210c0c24090a17151302011d0a090e0105010e1f0b0a0909020d270308061215090303060310060501080615090a031b0e 59
    0x360080c0d66410000385a90a2040070803494241d42c00101c1000c40301c0c02c540820303840c2c50b40045d0090080b80304070441c25440d81442c51500510080300700c0313031a2070b5540c04203002d44e55a01c1382c4a42503100161640c0810140e0ba142103900d00702200800500c5c0802c1c036881d0781103201c00c004044841d4041041000000341c0d8101c100903100071007000112280144550014410800582101c500e031417510290800d181c2d415482103050300c190f040c4510343d0b40d54021500c1c1122007000c02000700503602807402c01003241c40d100034028584060502482c84c0d40c0302c0450384100d070450903801103071304d8030b810500603e112041009405030300d100900101c0360140d502c0c050540b0038040c011320b001c1d45040e90409019002440002c41c0d46514000240060801c1d0112039500d4005130f03001403103070007446941c0c55442114818042225810384800d02c4070381d41c4104001061300355211080e01c5840810440d4100c1c0d8508025001a501c6404d014481c081c442019009290003600044040640f0348140a160307080c44 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 501144136 1250 501142886 501142897
    0x31b031c0e060a0204061b141509011404050d050307020705060d02031b0c070314010e0a1412190e01020f0f03041809030801150201150f0e0f15060c070305070311091803 74
    0x1030542c0e20180c86546801c0d01c1038071a08c41411058010510308030102d100c0d800da154010380804009100307804100a0941c0002c405460061a641c040003480104c14003a40180d64008100e00607201401d0361000445c65562001000109156001040060401814181c50843d50448610500381f10a4040980e07507130b0481e010190680c8172410010103966400d4100e611010a248180c500600952400441c0104a412500d01e6030203110a503051480d020015a402100140a4400b80c0d888500040d030f400c40c2054000f5046000b0489410641081003158003002e5030014021580c451030301c41301181104000046035280b60811040402007036014588605503281801007440100c00383c00141d006101b500f011002d00480c000c400603001040f51514001c9598508220741e0540e19200200128030085450592140d110b80c151255420000080d00815400308110342e00140c482d01c1e00303850644254400c0340c1c40003808081400c03500300b4801c40303600714010640c442542130000070b0094581c05030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 501145386 1250 501144136 501144167
    0x3110f0f07180207060e0102030103120302030702030a1d150306040c0201061410050c0f01020301030614070c08161e030e1017040215072d05031b031c0e060a020406 72
    0x140702561150382581101c4c0c44661044d0100000500204064041c0d0002d01c02542c0700c140c44e500e4a142c081c06802120f100b200c0a40c06180340c2420200c05940340c0c08507158541c1201c480c40580b9081c1e48601100110b01c1c482c59030042d48a02e401401c20007510000d104100869051020401005080d03400b242140700c0c0c1201c00c1c3c5150908000c003100d01d80106418014240720354994030341044410750095050320b000310420300005c208416040c0d100041914800006141c0803040c40124041e100542880303240c4409081d00645546c941c10040460078000807600340302c880111082581100c04020341d00c600f920000484108194054540001d041807034800c484401d00190440d03540e01500010001121511616003041c0e04100000224400400400744000f841d5240001405003400c054190f02c00015894115285001000c40d000101070403010711040c031400d440c00f101030060b14501060b2480001d851803d2801c0c86107419000fa00281e02c040c0704200500c60103030720000301d1890070789 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 501146636 1250 501145386 501145409
    0x507051203031605130b18010c1e1b03053004090e03070c1509050301060b0d0902120a05151e0703150816050a080d0203070b0a0608070303110f0f07 65
    0x4242c0d0113503401d1288104054144010303800c04550101001d014000221200e104908801ca5040043da58044600c0c405001031081711960101d02011300000001a445009181d04c45108070108100c20503550300211619081044142142c1880c801c890841350f4004804610300c0b001c04944100f90300c0303a0701070180d00380e8a81e05e508401c07800030022114416408480c0d444600d680740b03001a14080d2600f90140018400d040c00034880c501401100e09440304c0c01141441c0010214103c1c005120481c0100d800c50424103030002084010311090f040d240c02800580304c10f810b000c242c640c00300401000a03111000610f01100c9070b0354500348141d441080d9050018508101c290040582c1c080386d80041d0640c0300b1407001090013040b1820000484800f83d84410105440f50a001e840c2c040003108000140d10174040d00011408280381607030051000f440020380745442e026902e0810000b50400d5010402854108501d50010400c584459207603034081c0081c00340240d0a83e8840c081407141240104 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 501147886 1250 501146636 501146671
    0x2030c122a071115070f110907030b0f12030a0c0c030b0411010215070c2a0b0903070e0112060b061c02090a05030a02030a0206030c0c06040f0c0506160602070c0b0a0c050705120303 79
    0x410a6200610210024182c900ca403409c03d4008003e070121391466805a044801a00700300d06000104481c104e141d5400341d8181240040111500741850720143c880350a4444c002020a51201550780254051011510012080f4001a10b041c11003944802000245420480b0b255804000b2551a681c4115401032a83c404d0300005110824041001c403c4800741000040c2c01c02c20030010915110300341c0548107207540e124181d1405010034072608000700b10608400b40040c40f81d51101c10100c04c002c100303900f8441c1300501c527503500d115481c1d140941580082c14201034504a0003039401820204e000f80b24504495002c80d80f01d03103503681d000307005503808400309000540100c166198218090101c800c035141c10305001e0380003a000c100a03105119940350102d01410300504980c102c04084000c00b812109035035410009500c214402ea030340755411000812000900b1006002d40210b03aa04c265850a45082c030606020642d4000791080c504a1442c2d0400f602c0801940e40c032840703610f0549200f9 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 501149136 1250 501147886 501147893
    0x150921021c080d0c110a0b0c090a0b040806061809101e0c08040605011d130203070f0b0712020f0a0206090f090106110c0402030c122a071115070f 64
    0x16403009038002c0070010081602c01140b50503a000100c10b888039034640c8070f02070405803616116860914050010302045000400741e81502d40240b00c440000340117150381c0ba0b51002c106640741c009411015082d00407034180600d507c0c05440a4819102c0301404a00c1c60038000e9405940c2d080403510000215143c010f1141c00e010481c0c8404428001c03907409100c0001c40d0800146240340484045500724980310002c21480b8501401c1c90f010704061181c501541c45024103006803021851040307a05104945004c962184540d00c814010420003039070b580c0721178280c602540b000c1c000716543d00c1154040ca01520030034200044021030141c0540d900355641e02e0311402300300090980d06413107070405c04003000026041c2c0d00c00041418172203101c090b141900d519900300320680c401a80d07179000c400b00030b000c55a18505005403280e004005142e00c8100820402c143d065083c401204049541001090038010b11071000c3d04c00703400c8101180c0401d0104403540180200f409118030180c4400c0441c030707445003007 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 501150386 1250 501149136 501149179
    0x6081f05210f0a03080903030405150408041d04050d111b0310060e040b100308040b0309011d1b0301050609040609020a08030706090c05010e03150603100615092102 72
    0x1d0403009840b01202c00820956844807400403c4001404480000c1d0440b2804803d80b4000d82d07010000d001314425036454000707040d60140080e0707000402004001403080006030050717240240062104043e15040c2085030814807403810400c10308c82075546914402801065000040c0e502520142c0c1c494107000220b131500e100000e50400b500e00c4c20302e01043c2401100c0300c07240324030301c6001e0581c0d00340e0b140007040c600c2d20201d210082c030081050100f8000d04035490040c50740415400b000080c82280030250415070b40f040c042c4a281d94001180e480452302182e03051104d0746030240d000b404241020b0020032120f42d0020000340400380d440c00084110340c0e0303202c071020003032011000301c903140c28583c10920024042c015089909180050340041c15500030000340740b401e40014094660750000e12880155400010b0074603070304d0302030328042907084c041724400c920180103039014040140d40b504101510744031a0f50005007600708910742c0f441051032416a56007980d82d050300c44806400801560801d03 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 501151636 1250 501150386 501150439
    0x203150a09030f0323181f05011a070209070c240f0e07120c0b0a031401060e01080403030902010207080a0803010e07030e03040303050f1608130506090a06211506081f05 74
    0x40c6000710000028640f40701504c460740004081020055641e8074800d90360400104022b450b0a0380007809542c0c050303c0e1a41d0100d60049480c01c00d41c100907007a5980d07200c1070f0581012103442c104a480441291002c500c0b40f51210f42d10404100803503040401c103165240c6030b9106110000e02180d042d5000c10000c1d181c00d03001400801d0b141c0303031a903c0c91803010b0084c144c031584181c00700c08680000950382d84117880349090100103840c3d9040c5234485813400c070040c010303030107069055200b2154000b030350010402900c41541e01a40300740d40c5a5042400a002c03001c0c1c042d02d100101800c000200a00d003201004076400c8030f602d800d015a8446014aa111090003400c0e9221098440104281c040c0500c0ca001003c014044010409420b40c8a5080001d47d0040c4100242c0045a002c3e00780b05890144145180400001c005945852028000c0e08240d48018600b22090701c0c41c10307020407000b6001080e91750005c00013034004040f16100f10098101940503c621482880107080c0e0002810701420f0007030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 501152886 1250 501151636 501151681
    0xd020a080106080723150d06030209010602160503070e0606030a060b0403111003200d060302030105090c09091504201519080c070204090203150a09030f0323 69
    0x20540f80c0c2d40180741d480354070314401c000e01d50004040e03951401c54140c03d83d91815000410110300c2c05880a40025107070050034503100e01c00e0b81c5100120140e41c40d040c29900030001c940c003e10005018400b241c00100595002a000381d102010a02040000d02035040c0d11920a441e03c68507503a402c400c150181806500014400320006030100510039aa0380c026401c400680741e03d6000300640400700d00703c03400c150604070595819011306105142d0003005040c00b9210501c04503900b030300c03600003d0071603000740c2c2c41010700d0b408541c00001c0c5d401d00c0c009030340d0310929481c00f6040c0e02c1400141d0803101d40b40280003c040f00e45004107207201110402039001c404402074440403a8551020314811658000504114146400140358202c14443c03280300f4070035440040040e0405a9550921000d07142d42d40c2c08907807500420f80d103410f40d40d4005071031510513032545d88041481004d0f42030241016460445a40426041c00c2d00d6806109809444548070958a500d949556881405501d0903c0c00c40001a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 501154136 1250 501152886 501152891
    0x250b0a18061802010914100318050106170105010806070c02061b0f0a0b060d200a0b1c060b0703020604170d020c07050f0409020a03030c030c0b0405061f0f050d020a0801 74
    0x104040020000039080f8800c1e01c43c0914984c4441ca442982a09101110380c400c01442118101e60300ca034104490b0030110012100350507049907142c40c256402c642102200900000f20801c58038405d015407401402c1d43e0001d0b01b21414060401403040940d100043e0080d400080ca01e0104222155403001c1c00b80050140d840c000b01d41c51002e030b141c01e0b0504040d40d4541225003c10000d15220380341480303107540800c01c1c200750030740c10340400010449103c9c8190720242c3c0b03400006000341d4040c020482d20780c5d03007064100144281444a4100c07120303600103900c00039041c840300001030340004040390020f411100c0c0350000d50481d02e000c156031290000302c0c2e4179640089001802e0000026642e410f0350001ca0702c0a100c42ca0480501c402c982c240b000181d4403010740305080002c01d0007440c00c05242402443e0083e0006c0712034561191000c81920100c5650f401442005043d0340c1d80044040e400340180e103501c803c2450003400c1180304061303010f91840b6207103006420085584030a07004c0c00500d0b540009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 501155386 1250 501154136 501154151
    0x10503072c13030e010212120a32010e010f090b030705061602030708060603060c130f03030807030b040b030616030f0903110601060807050a080a1d0102250b0a1806 72
    0x3240c0007102840000c50101d504c1e03040000c000d600101e214110910041601424061000c292024030f00024210303003030aa9407034001c1d0b0700f10303018410088640c041d00408114241d580c0d8100ca040103005902c640d102008580c0140b050340c00c8400306c401280c4041c2c60108102000c0760003e801c1a0703480c2d00540e4030a50000340489100041d42051001500803005d90f01d10a503100c5001d40c4400045601c84d07815007041e0001006c40d01038801070054aa00c1e100070722103d544403411002e40d4003141d00203a01044025007001100755050140070a0544140c40078044000c10401081c1c0d02c601c09017605141d803480311110b5882611982c0408010742202070b040c80915000c1c100130f0003001c45510b0241c0c1070f0050000103c0c0d135a000c1c0c0b28031402001c131503480368079040e20b2000071914901e01504400c4419152015281901080843c81062460b8140016519510341c012140032071051080c0c3c1c1110408109200b0106010400e59580700001c44030120baa50080e0b80ca4058003007000d00c0c000d0400d407030500d1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 501156636 1250 501155386 501155401
    0x70318090b0a050d080f0a1106070302032415031504020714011d06010302041104050316150903020619090e07020f102a020f0f160e010503072c 63
    0x2030908188140e40030004540c40c3e1041c0404c4652042c40600360792404c01c158008000c0c030400501516541e840c0025000103070300c06080c141002035521a001079008001d0001c5517541408040b00011200e00780910700f8400000f00301c202d091120403d001c4940400014807240580003c0220000020011541d40c00c080c94208140c552200c1522015882c0840b0a10710b50b00c001d6008461142e08e400801d02a1310f10340c2007002030609101c3e000c2901000344400105d49c2c0b03040103510364a8a1000b2403103d480d050450307032102056100460800c01683c40350070405a100d6404640343c944001e0005403400e20340007016121000580d00041c11510808100030503268046040c04002c0311410a540000000541c40010303514041020030b0741d80f60b606202e21010b05102c00780340d804010b1380144e80c0c442c4558107003e403c0c401150380d0003036140c0040380440a61140c0143d048041d1a51803c0010f041d410500030959801113030003000038507a1039a0014520b180040d0401003407000c00d4068414500d003654 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 501157886 1250 501156636 501156641
    0x302191109190c120b0a0303091a0f0703030b01140a050403111207030f03080606040f090902131506110714091b040306060e06030718023004030908010e060c07031809 73
    0x1c0711400c01510f050002c205c10314011900804407505a030700c0d1030300c09080c800c2c0a005451008000501c01d10f0810202409252071006822080e02a440004818080a00240550841422094818808014201d1080e41220680781940c0d0400881e00e9072b0480c0c40c022442e080710208480920b0f200d81b00700081000114404685058469540d18201e0780380c41042c03004078001e0780a02c02c41020100d1007841850059885441654002000d117013082c0b0380a2060811501200041d00d20301c858144181311507508207034400449d2644400030718000b403612032100f40d41c4112501d91841446070002284819039400c5d403c074a0301d0103405e40d05035180d549203001c0e8000e01080c822083c40410090015049207808211001101d80080e032040c09803580c1c0741210029844040d1580349000149041d4070b40190841c000d031010501b4101c141801e0070b1905002d410f040f002c2d0301c0384010703a0410301107a403004000b007010764000000f428550f41f281c425113015201c4002551100c0e08200340700000181c0c801864 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 501159136 1250 501157886 501157907
    0xc1308030c011e020a0905042d050907080f0a12140316031805060622110409050603190f020d05060702101b080c0c030708070803040302191109190c 65
    0xc283c1c0038284019140c00280e006940500c804182d6440f01000307181040d8003d002841c2c0c003103d414040c2d541741c8400e0341c814a400001038055640c0d030002c0180c80d920412040d0003506605004000101c2402c071055561701005400078005280410102d55941c050b0300264040f21a00b1030903900d134075102c00c01800340c00b500030980000a0614101c074000c020102036201c00940c002011306201d58a01e810302170020703984100002c6a61004903074012a4400388110480c41e1041c0c0031003aa914500500c02c02a1540600150311035004141d038400610a45980d0006e1729502c60740d0301e582880b07540000b6003800b0000b200609035001d08070410ac0c140364049030701880411056410002074081145060f40130141403000d13400703da030307043c0850006e40400c00a09008000041120310304052a0b4600e0969080148104d440350408428401095010b0110302500340d0014001900c00c2103548482106022082da0140a64420008101c030071180401c81460748000e000140710940c18004002c0070001e00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 501160386 1250 501159136 501159161
    0xa03110f04092f0a0b0a0f02030903010c031e020c030417010b04020a020f0708030a0f08090a0f050607091e0308030a0b030d0509041a150f1201140f0306040b0c1308030c01 75
    0xc0c180450640b5100584d04180e8021450550800c551400c06440d030201aa0705c0e01e040d4841400018620754090041910b180c000741e03404680042c0c1d4000c0d219511134001910344001c2d0051004000101001054504031904080c2c0340708049120280903004050401d00f11780c00c10300010b440c159081d00010602c00941801c2c0403a9001691136507400d850380240c40c0024000340ea0300c9514056240700e03803031541d000780200741942e211080300c0d51418040c07491580d04480b02d4000004221106401803010f100400012000c144040c403401024640740c01c3c2030000416007100440071400ca5211a440400c0c42d6001074115001100d131244054081d40003510380c00c0c86281000350404201a9501c1140c4c20080e0182480c0203441c0b240b11500601d41024070b400c01e00b00343c148a465101700c91420304500070010505007420045060003440381c0b03e50f0502c9100d000350320003424040003076142d11000b5801090b4183c0e00b5103d2012418140c40341f43d0640c810106480003092111000c0c0707040d440003006188 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 501161636 1250 501160386 501160463
    0x9120503131e200a060e0604050409030306050307060c0b010509044115040308072a0213051014030a14150915040201051309051005010e0a03110f0409 66
    0xb034420840400f65142e441043c2c0010302d10900b000000d026101e1444481001072000e820140c80e035020a003162107445040d00085c0d21040100085c0c2010710506015040610b804900e07001c50703403100b4490300010b00c2000d0080b00c40100140510842c0640c02000000044400c0c05011080c0300750618801e0680d41060f1104212a20380c485a02c0001d0110f42d0003103031124042c0955a90f00d054580a1004140c50f091010034111410b10507507000e0800722003100190f1550040c84a40140308480941000615101e8500740600c850010000a041c00b21030807000100209010074001ca130400c9460140140710b07580d00c41780c600c44450080f5036804005802d901a0721300b940c603104515920048031443c449021004008200036501c01d80042404c0100702d00d031140c1c603a56500d040300858078120350284000c50700c00011f01096034070245003030307100f8811104c00380c0c5541503480e0b403a900e000c5070380c800b031040a00b5402190f00d51125080703100115000150b0303211040b8600720000e401004010b070001d5005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 501162886 1250 501161636 501161663
    0x6010306050109081e03070c230904051e010e15012102100e0a15050d0c050301140409060b040203180607031e020c0f24090109120503131e 61
    0x14421410401220398074401480c100121520417440c04044554030500e0b80400c2014902003241200d0080080c1351107255289a00080c0f52060070741601c040503980310324940800e00c03020030030000f1400001070103500c901e40a031f10184855801400f804c0a1148a801100e01018000d0401c01280d412a007036030580c002501c407002c0131031052049070407000303600030980e42000313410b58070480b204159488040c2100a405c5e4944012003400f000242c4c0000003c0c0d80081d0862000043c1d0207400d20004450a181e0b0455040c00042c10744201d003160441e014540d600700000a00c00c903500540c3e03412a001d0310456903401d1460400030007030b584140719091441020b0102d00310501c03d1044c0c0d4440001c9003086002041c5d1042145c02035030201554408510500481054400e0240400a2040345a0590001c0c020181e82042c000341c60050500794181d2402c030140d400714200d066041e5a103041450206d80d02d684106034038010303d002e0000a40380c14102c1d099882607091950301080d0b450b0040040d1417800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 501164136 1250 501162886 501162889
    0x7350106060801031713090207051b0901050f0a0902042409050102060c0c0c030f01021908010b0a081b0f09010306090506010903060c0c1a0a0c050703020d050d0e150601030605 77
    0x962041c401d0a0002d2400c0c030040020450040034281c4511040c0074140c030344041d82c0c2800070405019000383c52030303942c00100641000f00404c110342d290707945010644080007450b4000b03025070350144240d9000b100d02e62024000ba640360a20a030181c82c1421046440c2e645031001e50b0721400a00b0030036401848403640d03441c200d03801181c40c00c0c03c82e40141d0040040c0e50f86c2e02e000c0950b5800200214805105161144038903a80500208072440b101c5000181ca40e0f028030031003002c030300440011100344401d1400500030740a00c0011a8800c580c41e0401c464180c98249601554400e28045d4003410400401d0300001d90102d10004c0a0403040ad030b0741849511b0b102c184100896070250703807140c0421104070081000070700a400940c10340c0f009090540c019081d13600c130415030030030000010f441441c2d0b0900304103110303d180c80350451040d800d142c10f0b420441039603070103580d9006404881090050208034484060029080780c00c845010310192108015141d8400e94404019100580428200200070605 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 501165386 1250 501164136 501164141
    0x2004080f061f063c0e060f090909240a110301120f11150c151608090109020d0807140613020613030f050a060c0507081b073501 56
    0x1081681a2184010f407401c1d0080e41c007040220000d0f032180c2000c181c0c4e40201d2000e8415a8040d00c0d001d03494402c40c90020074001c140e01c2c4110010f511071001031200003a0b001c400780944607051310907031740300b01252220800140313000c1c1c15440014040607200e2048403001c0301d100145000301030542c014000340019100c101d0b040e000c04d0007050340d00740c03403802c0801c0824482c60492030000d0103412a900a0101034001c10f101207403202451110090000e11a48a00f00402000d440c850400031403010b54240034000043e0314080031125400c011035100400e424203000e620400b05c6580c0148401e141040a03d06404250031880007a1012400021016409500410031510030b60248000c0442c0400a07400c000c4107400a00340742040306002a00440055003003518006e241d4011401080b540c4200d01e4442e00352461284000100402444108001020342d000da5406124424034040318002500f011440d10f0082d0b0300602c544180d13411501090340d41c4001030b81c4110160200c210403030703840c003103010309 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 501166636 1250 501165386 501165421
    0x5010e0a170a110723100c030c17030f0f10030206161a0108070f140f040905010f0908250206030705090a0906031a0a0506030a062004080f06 62
    0x2040a412080d005a0410310003400d0106842c140011070b801c91a240e03525013040c507040b100c021128100e445035840c0e89209144802403048640035604481901c4c005c01044c4180001014000780711281001c204071685492540c0040740c501c20340320314000410b10443d41e8284c13840000d00c0400c80c0840c406800509540c1c0640703401170401032810b5003491000c151070041c04002d40c1c01401010308003646000f001405130081081100904116003803000c01004086260300000e6680f0444520b01c1035074036203a0002c01851801c036000a44402d03a42000c0d070140c07a0810790600103924224200e0f040203800f401410300685019140d000c1203c4007004d0003201d80307000502a5200f00184001540148148010400b440e00901009061690380c58110140c0d45035801c101c408040d4260346400301c0303010601c2103078803500c85a8203100030705101000ca41c50380080311001d480207442d031f42580c119a11420005110b203101c1c10307030b1581e00c0b0b0307560361400d441d0400f440030800307c0e0044c1000b003001304041d0b40e99070b80c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 501167886 1250 501166636 501166643
    0x302030a050609130206030a02040e10240f03180602030a050115090b1b120f28170403090f082407080f2203050a09050301020f04030f140a080705010e0a 67
    0x1c0300b1000e85d40030000907800040801300300c0b540801000c2040003283d140c40d4068003545481d1550182031041426816800c0d0000c4107002c0c2030b600713003071255581c404000d00c03140026040000d01604801c44d000402c0c81c46d5003010704141e0000080c41300e0369646501003812078241c1001d5071258030034010101e4a9412501c191f0721400014403481c814214500c2110b8030f110350480c2201d12480c0340411041840d0000380103601c0140c0b0110b01c804184060503074420f00c44030141110000055000c401038900340f07034a400840f296031400c000030101809182d0810280400c000070a086030360702c40340d160fa40c2e210304808a1510251200416032401e101c007510f4050101380c0c03602d454654400c9000b0800c45001410111b0505001c4a00a01d881d64400060341060181d528580da4045821010381040d0780d0758442c5002ea072041244140340070600c02540c0980360710185a5040d00c06606020315400440e40603240c4600510345218200913848006280440c4208000d20000450003a4540c46024411014 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 501169136 1250 501167886 501167911
    0x1020721180b070615031a04140c10180810020d0608060c072405070503071b031409010203070602120121150506120703261305010e030703050105070302030a050609 72
    0x1100019100c0d00043e110008140998889594a4840300c7c46803c540403040103035070242052005200a888130000310310303180e000a144002004001c50362450002c8003810412414602e10203501003c01841001000080d0481d5200025004e524000350b0044400310226032500300001f0310070401041251040029020041c02d0100c1e64448200e0a440e80c21810341c580e481c041e189111003400d00c00c5030701130142a0749441e01c901e0100c0c00a803106098050309d0001d10032500c00c07000007907440220440b1000403040140d03102c825100050380796000e02d0b130b8000c0410b80042040503000b01c280ae003044c1291070711541e000c2d00c0c52130301240d54604020340c10042c100c1c408158602c00e0410302c41d00300941141010303000c0c004004a22000d00e06120640d001220380d80d1034003024424004031f0451031081100743d000d00500e0b03c0e246042c40c3d0310448042c0f20b1141409800040c1c0402a0b409025407402950450001d004916018200600130750088403181400b40c90b050200b00d550818600991082c2c5d80304640 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 501170386 1250 501169136 501169147
    0x1a031011090402070c08070605030a0f0b1f0c050724092912190f020a0c06090318060201020a08070504080307020f0a09150e152101020721180b 63
    0xb404081e6101d08415144810180800641110108101c0340204031035692981c807810b003030300752a0a4660150404070070b0f034186402854655101c3d013000708100350303000e58400c10000c0702c90241ca012542d590050300764040c0c0040005e406071410b0103a05c510034043d51400302d00c0d1158400f601c02c440c45000e60545031440c1101c8034040c98511419500900c1416802c0b0b041c03031ba55207081c00303400d03004071200c40c0c1001c0c1c5202c41c0e45402d855030007440070000c42c4000c203504102030314000030440c081802000e861161150546000d041c080c0c201c1e60b52000c0071100c800009901e1782800385c00b0b0341c0010345420029000d100081c15192141e401d07502a2060b20003d540781032101d4080001401d56040b0103644100041c00003c0c01910034401d0110f03128400400034140c41c6088504102c50a0091585845a0010158542654400001c0c052006036121902c5a80010200703041c024000e441000709000b071240c002c4a4500c07a00307440c9032909449562108100f14185c8045102d907030cc1441121890310082c8003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 501171636 1250 501170386 501170389
    0x405070c060c020712030f08160e0405060d08031f0602030901090e1b0d0c020601140f060705010f06060e10110706031d03030403080717150f01020c041a03101109 71
    0x200041036140ea2049544d0030780c441440403c010610076081380032490b440ca44034070741908071143c42da202c043c0507080c900f44080c4407400b4049861104034544950340d20400203203a6510070000c5060240c0241d58a5203a281c86000103003540341c965850001c1240c444400030394544008111100e0000c10303914940107601c0d203c451400008054001641145d40c6280b5400480f80300000d0290452450008101007242e4000a401d21606811140400100e00fa1201844d10388590a050580302038850b00c1c0d640700c3c0707428101d00404c035802c840000b00e03042c4280003c0c071a5102504c0549948211001c07030f0080f07202c2106440e60003110004180a17089110208481402135000b4024050750307510700c1800d150401c4100341181c1c021a003c60100e0900d900344001c40f1303806001040c00041102d82d21002d410450039503105a080d071107409100b64588510814964400d00c03e250010038080c000703009040c60003132000c0320307141e0452807140688290103028603150800d00510322041e0440e0714441c5080b04410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 501172886 1250 501171636 501171641
    0x417070b0a050903150903091e0310060f050109051e060f040e01090b01030e060402010e18010b04090b010f0507120e1903051204120b0601020f0601080609070b040b0d09110d080d06050405070c06 85
    0x1036801c1810f10792000c007900c984ac244941001c80c03842e01c0000680c40c0c01c14a00c4110880c82d608010304203c8226001c3c0115240d03890301407012905041049400da6034600010454807502501010101c0b0114000902c0d480c0031401c00c0c140c82c1310b0241031204100d080011002c5500917444904981e200c2d9020034055406411030007030291001c0d1400a088209031600c0d403001c4400e034000b980b00c000024081001c600548102241001c00341b0704511010441361000b030003030203084400b4007800030b54882c903101140102c05074a01d154010b07000c1e42e030001360002d00b0200501c123440190b0740360144a10510b28545107200319005c0d200806008500030119456841c00828010710741c605510a0001c0c42c0700c1482d00300709507030080401c03c0c0103200c5031800c0c2c4001070a00016500c09948600c0600c402d210702c00001d030640b000300c0c1050900060300070150070b107004081041c055864000c040261510103004400d4000d1910503c90039041c40103660714424841104d504855210018080301040400580a138 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 501174136 1250 501172886 501172909
    0x9110c0a080406090605070f0b22110a060203041805070309020a0e060f0402090604062a050a0c0e041104020c1e03040905130819020102091503010e100503030417070b0a05090315090309 81
    0xc084800d040d5201800c10542072b40c0c1c4401591000080c41c0b0b02c1c421480c091458901600c80c5102840c02d061505819001c00b24041c5e00070000701d0b031038600103046c082c481c0e803019512540050986244039501c44249128943c00d407a194094110a044c407200360800303000719510100c01801480c0703000d203012000c40e01449004d80c41c03c00b03603450700124211462060f14a45d450b0b03001d1800b03000c081c0e0b8140b03000030501e0110392040e00c9000003c07040001041d80e0803a011281401560056074804500c0c1146041c01e208100742040c0002040814006000010240c010b0714003c16042060740c5038403414000c00c0c044a08020010304042003d135030f01120500c0c17030720611007050002500300884540010384c010340303200d50021211004070040201103004002d03280c100c0c1e51180d5800120307082c000800d483c1e12032405604400a10445541d041039420801d0000a29001d00e00a03101c040c3e0380c800071b0040d4400618688284111a440c0851200740b52b0f0090064071070703400451a04150109000103a41d14 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 501175386 1250 501174136 501174151
    0xf060a05130b031e03030105011101090309050904020d050d03020a02010b040218060f19080a0b0f0a030305090604030803090c0f10080a110d0216150b01080109110c0a080406090605070f0b 82
    0x1140030f400313450083d16814010a03902c0002440e229810f01c0001005240e5805c3c0740309660f8107041451000c00c2c0c02001c1c65080d200c082d2082e00b45c83d0340c1c1e0300206107520000d6400030181d2048000d0a502998554050070009285034001d00000525000f08003c0e405000080e04c10034070b100e00c02c0083c5180c00401010380448040c140d034140715241194210030000c03541c070b24002c00c0840c41000301c01a814031070f0118583c0210b801e84900c01c640b0010a802d01c041d800002d00303101d0000f600c40840d2b51040b0640340159031060800b070360392826021a50f120311b040c40010f400f40041c552440400e00d484110f507603400d00255290030013a511607180340007502c1c0003803211313a005a04100401c00400a40010008403034010084007100d0510b140c00079030020300a66050001d031802c000302805a91100c5e600e41152400080030a44c0450480c4149141c42000f031611214841c011224041050000180044490503141d05403040c1e0381e9141680c0d03d04c19075000070206006840b521000400361103625030000107 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 501176636 1250 501175386 501175393
    0x11202130c0c0f0602070512070f020d080c0f0f06090609101a0603131401200c160f090c0f0504270507032028020114040b0f060a05130b03 61
    0x326158100e10f91060b600503034101d03030001013210602030204110150300d5500c03254030349850b10941744e06251030043c800091007010041284801d00000c10143c0701c211050700706032403c003196030340c090b40d40c0c01a10f280c9424034020440021204030011442ca4440c00250004d850241000c1d0701500042c0007010300706c11041c2404c0c05a0400b515400d000c0e62049065483c00e900c80d075110309050800703000542604003c0d80c10440c460740e0070b44c4c0322a00f0300c1c140101000155120b0a03c0c40c403580c24000003006017850250818400140c0070508c86004c0204c0f8031101e82000700038915042110095990490500410300804c000c01001c0800654051569000908140603500c07542c40c03074007614001d0f10254006619803008500452010040f4070b05540c00c0c556862520040c9440221412444800f015105609400b5044100d0007900041c1c0704486803d0100094545443d008042d00c02c1030366445c1d1306c103d05c600002c1003420800d003280f00740c4100820410b1954200c588d03101c0a011800d018039054003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 501177886 1250 501176636 501176657
    0x10f050c010501031109091c12060503010e0c100302031b28030b130b0f0d080c0715030509010515191206061703040b09040c030608030307030c020105011202130c 71
    0x500b0b1003401c1c003071803142c4168002da40d10071041056004000d4607805064000c0e03031184003000078000046840c404581082c4045003051034034080213000f6a48169019400d1202c0300ac3d29400104459125a08c00c4071000c10140100600300c0c200d000880340c0560615448001220021032000501084140c541e00d070704040030860070215029402e0a142c2c808642c960020310142d00d00414020040740d8406c0c03080211801c4280000e40741c042c16110075000703900b00324044042c0010b9004840100c5a074604a42499695480483c20001070074840c00010380b61034003043c845c52040c0141030282201c2c1440d20004160002004075943c0d88510300814003510b00000902581215416944240100300000d02c42d8606a01c2e0864000100750700d00c01c540040100b844030b01c40328020380300080c000b07503400100000b80c000141e0007013501e6040302c1c00600c008002c2155030755158200e8075201d2043e600030700860341d032199134104002104000941c0704d032940c0800780e44c108aa6000045a010900e088032008 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 501179136 1250 501177886 501177907
    0x5270d05010905060601020c0607031202090102121908010b07080a03051504110304061d030301090e01020d06090515030c060913110a05040303020d021605040b0f09180c0609010e010f05 81
    0x65041d40b908440a8001c181080065a010b008112241c507065620030302d041174a0740c008009074000c8038600c500c03d078045490b40e03003070b4400c200d41c0520380800300c0002c0c1c0e1b5034040301c469101d030b80705480b080000600103000072543c4c190110030340d19025884000a400c1c40079004003074020b0840201002012515600d407a00d507603659018100411111032041035490038a428440300391410700b03024001104040d140b58251200020840341100c00c1d060001810040300070301240a803150100a860840c1005800b00e9145001c2c1d12260007041380c0c0c4101c41c58411841306044e141e03071000c0903a80d401141440101540c0c1068841a0b480011a000008800011807203081c49038118454040000ea4086000c6c000c2640400c258100500107000511461008120310306400340c140c003c4c00d0155441c0c1e4144070041e203035284a5868104001c2448446241010030f0061020240c241000f15104140300341c0760720304191045a00b00d075811b03074540c4240b1121100640d2903901401c032003010003904000c2550718 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 501180386 1250 501179136 501179141
    0x1b08120f060402041a0702041b0507060b1f14070614011707080c0f130204030f03020d08010b0d0f0b12011b05120a0509070e13031e0906180801060b070506010605270d0501 75
    0x89980790348030a038444409060580437903103903058a500403030010840c06401b840d00c561007010a011840c00d002e00b020110300e003804a005052000f00104e040444500303900a024001c541640e1160403100b8840e44004275071039a0700070703521508629030400304c000d1002c0d040415050780ca030b40002e00b4865254208403000070482c1c3c401d07842540d9483c80c0c0c5041108255043c0950094650540342c140604d50400040283d03900c03070002c0c80e401103aa20070040d1920802600068048c40c401401d9668003619030b10018080e00005c402c0d0321807460480c0d5100d02203800740040e10b0400c0803032026003d0030368034066608000c140250a4056910403400300103182c031141280c407840f92a400108140c903141510380904101102000400906194906290700307660110b5424121065858211a01518003130600d96031002030f009a6115400c00501080300b001110013050703201d10a6003212141c0c0e17070781c04045406000d6046500c19001d03d4142c044201d104015902294580061414020f101e00d03035112401c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 501181636 1250 501180386 501180431
    0x507020c06040b1317060f13050f1606090e13020301150b09040b0607080316110a061d0604020604120302011103090c0a0503010b010c031b08120f060402041a070204 72
    0x80b1a0004d0445480800c12280c10028182c131040d01d582c0c40030410b901e030707100d0000905190000038807c000070114940c00d80d130b1510403900001542c142c0180e102c0015102c01000074615201e0700d110000203140d0740300d50116012501c1c1040803403540d86401d05502694071207210266499901d07280607410703810800003000c3c000d040a03142c0e90356030440c001c2400107039400b105130940704200a202e1070001c1550b0200f100c0c7e000d044003200c41c2e01c5103e6010f082c0c4007a41501040a02445040006001c005541d4440300d0342140300c074500200c500c290920107580d1035048030b000f074010005000411401c4035214803100362907c02d000102c0d075200c1c5185187e096800c215a0709813540c2c044e0b040c0c006641004000032000e031000fa002800041450000038100b4030862000508000c012070b400b8070700750089410306001c198005440c039502e00b1115052105200180c4440e8528490384002c121a072405108603000c80c2d140c0040c414200c1e4200c4106a00e581000c031081c2d812a0716840c8041038124050002d4a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 501182886 1250 501181636 501181649
    0xc07060807030b061201270608150907051f02071a0711010309030504050d2109170a020a090b0409060908031609050916120903030b0f030a0c090507020c0604 69
    0x103903500d403944004058800e00b0b540f4600401040280c106200044403115044d94180e1580c126142ca1455210860003050281d903407210386003e00116944802080881051921603001c040b6030715580f240b01d89881c1c8038840c90760f0201c0390701c1510503401004150001013903003030f00641e02e01c03a50b50000981840380d104001420000001206000c0108a13203149404940a2070704000c3d0314030b15038015100384030f5400317105d100c0e04000118030100030801c4100080c039080c019540e4152620398030060700c4030400d401882860802241c1d8880301500028420314410703001484103910514040e60350009000810000742c006d5282d550100118166004450006108040b01030352460605800c0c2c04050300d82c09400b0402c030382ea540810480d80c80400700341e0003840d4555990140601e0800503a1001790032008400340a0404030b4403014141c240d44030209040095480729110071226080503180d000030780004201d54a401c00138408103030103500450340404a1700448400d81030150001d04a60410b50000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 501184136 1250 501182886 501182897
    0x60d050a05060115031817040803130e13201c03020706020f010605060403150617010e010f020909042307030b060a08030a02070315090f0803070305070504140607080c0706 75
    0x40006858960444103182e0880c54200103056454054100c00404103002a02c0d4500990800d02c01f0350111044400138080300c01281c1e6201c0c815000d03806050114814140b40c0078416001500205400402c0c0c51860344c0015400c03800c1c3c00c406c0090b854034050703c2c2020380000f00300c902d840440450310035070000300740290014241c42c2e1420000a2400140c228031103240d90600400f04100e0f03c82c0000d0328140c0740e001c911242e40605070350541006000961080404844110100219540640c4040f100710b02c40b60003030042028010450090340b25584149400000d00720009010401d07500c4010010048008070035908004280d10b60322309802e80d00309941c040d03100070620100b45851000e80c0c00030b2a80070041c50926882000c0a5151140740c440500850004813240b103c0c400c265000d030032841c0e401040381031b91008074140103610383c1044402d140481e10301f8003c140c21a00690039074046400d101881c1d8a118800800c0c8102070b00071000071a83d9800900105006076030a2000314007601c0140d5030f4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 501185386 1250 501184136 501184139
    0x1c06080f0d030c050412060e01020403030c0c120c0e0403110615091f180b10050c010b09092a060d1509230c07140c0f120a030305060d050a050601 64
    0x8141c1070292007031505061500d4034001c00d02042e00701050b542118641c400c0401e140b103581c240b81018140000346c1000c15440003801004142d000078410782c45a019045058000d03440345003d14401114100113010912491000c000c095290010180c0c0b2511901e40000322030741102e001031900781d01f0b490380c3d0070070001c00e00c030f0001c1401c044001507404840308529403015220f541c140003201c0c503a8059074002d203041c0300010407012401d40200c150400050820404403a200301d008003590041c410707880040d400c00c4c1c18020309242c424541401105014050700d05400445004180c0064100241c500010403010b0501181c1d1000013900510030003240100b100410081090601c80303ca801c103011040ca0f001640c40314410a6152a21400c0881e650142d5902c0f1080441e6040c020014018843c040135021205201d03000309540700420b50543d106007225020300108031000124020f1840d00741c2c090500c12010910a0300001d4014501404103110303080c1039100c9c10b00b03240704044159143c0c1d01c007000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 501186636 1250 501185386 501185413
    0xf0109021c0c0e03100b0f010e120f0105040b0c090a1401120e1005160c240f0b030601090204031a0c0702100203070b06010e01170c0d06091506091a1c0608 68
    0x1149001e96030b031740d01007080700c92840c0001c4c00b405030300600130f04101c0b0b01100d114180e141c1440e803107281d14200086541a0110120310742c0039000840301100e82d82407840c04680302080103002e840c4107180c01801d41c1c12150501c05080301890001030018100503002502610303d004034400c10031030014010140265107184000382003668006404080c0001c5441e61221400c1c1e440700000040a622244200c4400c070315047c0e50181417191f200300015140b8240c0440700400560f4809210340901303500791401c6a03a201074402c104c2c06548400f070000c03246080d00748292044040850360100343c10040d141014616004900c006c20b030441c1250150740005150402d0040605030141d00031400d2074200c041c0a09040005c1c0300600310181e82e9030180e80d500224203004680c4041d2600d200310b140c0104491942d80700d03041c020789560046454142c0002102107a141c2c416450030050343c4110405200400c940d101d56201607105004c1c4120001206030740203030070b46041c0908001411490000d0408240c55513 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 501187886 1250 501186636 501186643
    0x6050601080103020d0b06030a150207021e130b1212030f0f0c0414030109050f0c0a08071a2b0606030e16120203030c06010e01030b0c030f0109021c0c0e03 68
    0x14401410700c0301c10703001000180e8480003102100341d440030303550b0f40540700e501c0440d1414020140c02844030b015501c8110700204640c1c068100640203c0381c4e00b941141d6000783c121480d41c0320903402c1e0044100302007031031065065001081c1146000d00290907407686c0d54641820944148901402050300205115506210510603604044000c001815030300309110882c840b40708600c2001d881c0352651303018003503664080d0b011180c815007000a54000003040da950a8a544609100c64424510007401088101c0005401e0065500004000360042501104034142ea0801c1d10001002c1d5040e200c4210300c100e0031403041c2103804290102083c01400d000c0040c4c2514240304030001907a0021000340c0c019031405081804a500907800081c403240c1600110341036204050030100e2038810603000003498002d151100c0c1c126405002c9030441d0391101030141c007451105941c1021101e24082c0144000b450541c020660b11a07071b010011103243e541101901940e40c1c14002c9008541801c0d5211076508003170 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 501189136 1250 501187886 501187891
    0x100309030f050f042c09010507020d020604081e07060e060f1e0402091b040b0415170408090109090c0e030715140d090803040b1f0e06120705040c0c0605 67
    0x904100742030900c890f915000500070381c400c02007160044410500c1c0c40d82030944203041c8542c80340c1900d903946040f1a2580c01b80000b43d500d4030062103022000d00c803543c40816414052640849c13020315148007451402c0303114650405210688074100003042c00030300c5500c9030080120400b000351545141c042c01c003440403000102911020502c040c60615000040004d540d4016811210025586c0300d404100c850076441002c065105a00090085940d02100c0090000c966028154070201c07034819104030707090404240500c2100301d1080100300001c42220240054100614000c20010f0b99192b41d0b2041ea02298500c4001c02c00b00310314524141030521880c2e01901f10b401180c5c005480440c0300400400c8258407030b04814501095542100d222078004a001581041506889091906100e0840602554043c0c03c400300d1903410000c40341c190180000b19142e500911015075144010304c00c1c286511f10525055008001001c00c850b952881200c03040c05881e561009119100c1c40e0180465001 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 501190386 1250 501189136 501189167
    0x30a0f11010c08070303050703150f0e1302060f09011b060e120a12090809030109150605030607050304030c063317030f160b010603141003030206070c1110030903 71
    0x2d04110402184801c0300721103503180d0515000038a982d46810440041c9101007200c0b201000c450740001d90130f20001840c0d41500c00002c2000d01c00d40f14141c41c1c49a2074800f840080d00301400384001141030324840c0142440c03031010b04060302c1107480700001d0443c54100380411154a55284040c041042c020056001510a100c6000d8541042076a01401d000300a21100807620340342c0314010104030031441a5120136002030002d002c841100e242651a8845450407440311a1811100194070318001078494000c52aa0311a280f8544032030b10111403803980c003901500e01d03031340350000d001b90402908016600031407070805a00010310f640f2041000b03101164004501e9085519480c1c0d800c1d00301104441620151066050b40c03109035150080030303070505840c06840f850307482000053f0b481c4c04d50041d940700c18049241220a9803102140a88101c15000140060703202c80001020310f4010115244100e0007a14a50320104440c80020075610352052040700094881c9020340400d504011010309a45e807 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 501191636 1250 501190386 501190397
    0xb04091a0319170a05031b040b0306130e070b0904150806060d1401020c01020a0908190204110d05190506032103070519030903141303080f09030a0f1101 67
    0x940d5030009039640c0008040070580c0e044010030310100051034240342c120402d00d070342240c0c9444003404054030315002160101000e8217a5900705001400050481e070680e0080441d80e4123540f02c000030310842c180286840030040d5594207001107e004204104802064421402540c80d28400c0a1000391003000e00c068000d0011284248103c41000ca4516030140003074a0000d50100c0c54140701040c191b00c10941d0302c0b903504c0054800d4183e4810b400a08219800b5150b0186141e074034001c4a680340f001c40005032120729071510715001880d2581255402980e801f558070309103c100c4003920101d40e41516400290141d807401120381400d2030080540c048001c9019284c403800c503c2c021190310703802a00d1440503200010009aa45010b0030a0302d50a900303030110540d41c58010103000c0c00400da010416408180e64600942049141c03038201e0b0007044c40090007813021880c40d81e450440c4e40107100c50a006c16070030b00a458070f81c1c6082040c1c100243c05401c1d03500a914803030912424240c56410101e04018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 501192886 1250 501191636 501191681
    0x30f050a1116080d03060806061225050a0f0303050a11030d0c05130806070503070813061a04060e0601051c06120c0e090601050d0b0403030908030c0a0215100e040305040b03010b0409 80
    0x420108146a0002d030036100482d6524514000908094000c10b002a8040c0e5201c541d009680d40c501002f81a10400c0c0c9a10160f5a110540807100d414103102c0180050301c00c1000000c4544514501e40b00510840201c07070415411029140036190308200c01d600180c000b00311040248614440c410003810450080e05141c01c080d02c0040192000078060b00070300c90840d001c07602c08440d1008000c03e80c2e400c07070b104204072001003400190711068000c101d4070603420b249011810a40c402e400310300542058651a180401d9540c8445103500c1c1e88a803118815a6803000250041442c0e0112140c3c91044410382040ea007052281503404c0c1015040a0b01030780181300600243e00c41000400b8000d0b000410f0000c3c42c2c2e12403a040300900019840100380303c9003c02440b14100107100508038014654082d142100d1340719604040080701220b104c1054540c0784001c0003994001c801440e0054064074003a0320b019102c0350309019130340c820390106000150006007001003903400d200310395000c441214640704e01d1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 501194136 1250 501192886 501192899
    0x140d1e0605012a020d0b0402041b0905010e01110613050f0c1e06130b090a061805010c081603020a0204060e04023a080316020307030f050a1116080d0306 67
    0x40f039101200440c0d00c00b45034107980c1403030702e0700c0000385155004020800b91501861710200c20401614220b010740d0074040724010140031010004841002a0f0f520802d140c503140045514003100e11185050050305d0400981d01c203002d0140390700c01e01c488040c400004042d031900b81d245c440e005204401c1a00b0844030610641d84009141000141040402c209a03a901001400310701c076071940300c110180d0020300000c09a1001b0302074542c06030304459444009503901000d607000300c0500400500e80e0800301d8140815801940c0c1516040d000340c48031400d00d18024016501c0c070f155404d0075000b41c0d02040313050046142c640506006000c1d84403a40d446400c199000c1414859000c211200d040c1c007440004541403c00e80700c2152100b6000c0301d040701203001e82805400c136401074030500c40100085400c40041c41c000412100344030b40c15a105030300c19000040845440e0892510002003201c80003819512400410100021180c10512040c402d450028882d292400f1080382009160070203c040240 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 501195386 1250 501194136 501194147
    0xd05040305060c1c0507020d09120206031f0302030d050424020a030e030c0d08030604060b040501141e042c01120204090203030d1e05060301020906041401140d1e060501 74
    0x301400103a015104e001d258a00507019125404c2042420b1400c400c0000c10355002449188a00041e00c84294045d10360041d0120407415900c0a90030410030004950400b04e4250407e400340d201c40d080c14540e5440b039000a080600d10300300c2800060001c1003c0c421540107403100318081518000080800003440400703500c80c002c00d030001e8107005561010403e192000e204c6552411001400b004042485142240ca150415240d96015900d00440072940c141214101c03000d988058441500010808518044586c4904032030000d004000c0c18010540140f240940094080c540c6d5902c440005d042c041000c031458880310817040007000004100c680741043c0e11000668041e200800c01c00500e0000c2442e5200b1206c40a4020386041402e42c80c9d092500050f250107881c0c004280255110700040500380e014044110b9800b0804110800822400d83c000507070200b0113041100ae00c2144820030a0075400036207038003402a441b180c2d000381c50b044ea0010421b00c1d142034081008000c1c24000000e14 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 501196636 1250 501195386 501195391
    0x120f0f150705070f140a05120f04121a01141002011109040f11040305012913091e0b01141903060203090a12030b1017040b060409020603090a02030d0504030506 70
    0x1d2100000702007040c804620040100039411039180c814600d951710a81e035407510214420f036002d014100001c1443c1a00c8400c658818002948030380c1400d090120f014052514880c0c12104007581441c2c003414901502e103011300810031403000070b1010110070207203c011a0a28082d40031039241031429100030300c42c0d00507186411019180000c588034002580310007042034000307289510720082000000c02034150072080a1700264a17480c072000d50701074000b4116001c0c040e80640d1011849207035240d00b201ca6071001c507045001e8507441a01c55a003084820780f4040c0840e040e204845500700500403982c0180b16050201e0302502d56030054810a80b035010045d145000080080d90004040b410003041000074401094100e10301c080e182c0c1d00f044003d0010b10344400c03513900440e00c40b4106030300540528840780e244183d480c8540305075070301d81d81c5d13a05881d94010003050340941d03220300000168a940003c0c5109500c0900104140e4019004041c500304a40b02e901081140030002400051000b044868 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 501197886 1250 501196636 501196651
    0x10090b09210f0408010504080c070e0118090c0b03040f0c0b070203030906030a09150218040c0c030e22140108030a02070e04110d1a0a0204140f060702120f0f15 70
    0x292607844121805102e4440d640c0000115801c19051009010000700240007030742020046030142513503440c180c0c01c03080c001d1080b031007030041071411002b0100c1203070810b0080b24030820079009815280d00800b44e00ea0815207003940c50903031105c106810007070380071344220140c5a902d00031820219590700090741d0f440388820031402814007001080004a281d000003089552107640304060340d00d5000d440c4001d40101030840307541d00f1031112003011400c00b4801c891501102d41e4807201d08454a0b01c00ba00c2141140d02c0e020b0300b10a0603c1c044032902c0c1d15a19050b419482c1031404582d81d03200d50b5900030165010380100c03070142c200b04950705e840d54000034440700b00e54400344120645d030b6507030400240c0c1e04c0905807080c4c1c004008180d420100010780400d03501482c1c104c0081c45c0a0748901c1c0742d2808901441c0110740c400c0c815422101c10a241c03140c6010003035030340200311034504655640840d10084d81c0d40900741c0c0a50021091280d20704d41807150300c0940000c400140107032140e80401a0305440081d2826 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 501199136 1250 501197886 501197953
    0x30706110c070e060d1506170607020c1903062a0e010306090c08011a040506031038090429011202031302060702120114010f0603051501030c1110090b09 67
    0x80030490400d0b0401f400521045881e40d072004442549561900c1c000c941600c010301561440708111700c0d1a202840144806c00a441000c0b421661410018003c240554920400c00050000b03030b18000d18144c1454101a55907042180d041c1001500392a0b0ae6001070b00100c2c102142e88401c20303404003001d4112034209945802c030038010a000c004d148101d403c1a40c00c00390000402c00c07101c9041000808803807008081407030607911032405030070381180582c10040c00d207440d426000a230108070000c0c6c603d4040c000e0000034441a03508070b00809203003404424446030061054018a50303009030b60386489441480080d4594900074404008646a00d1002441820301056070000d6448681d07284040c40e031a04c0082041c00031b41411b4040c43c0901b44580f02800b112850041460b030300c203014503802010b001d11110300801d968070064025241500d1a0000c00a402c1120030179034008000000307150b0031034100014a030107141401000902d005101032541e80c00b0f5901440729030011280d4407022a80d03402d25 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 501200386 1250 501199136 501199163
    0x1006120f14030708090f030619020307020705030a14061b0a080a090609061a12030d0b031c181706040f21050c0105070c0b070c0302030706110c070e060d 67
    0x1458101c800440e1204980701c0443e00d0700420401d60002d2001140444440280c031790b5810825580b200102c03107280e1001001418060222065006550050524015280d40b00e4075000860301c0c11307201440c00d880c5002c1243d115040f5030300c24041181c000141c96907404841e41644d00320040c5100756407802080101d0000060900000d41e442103c0301c1c2c5e406402401080300d58202030307019010414000c40301403100310300d00c0c40a01e07107400c01214864025020710301b13040345170090100816070301020f95058080c02c0b0040080e040a149460389100c03050f02d070001e141c0c400300d04629040005411004010010300480540490006401035126a10201d01040e104046ca4112220310310f0a2607125035610b0011082c13a4682c108000e0300c117058a020003044244d0310400122000301c09010054020004180420041031043c9100f004590280c0120303490301c0310541c1d855084605000030400340d4034000c43c608001060a00111009015a1a8910032410154000380c00200760038002412800007905 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 501201636 1250 501200386 501200393
    0x3180d0f0f3002070501020c0f06090301060e040305070303060e0c071e02220f090c030f030201090203060a0e06090f19150606020c011e17071b11031006120f 69
    0x40c1c00d02d00d4044010194070880c542c0044000503111100c50708098090804003040b6075200042c0d044c80c240c4000c0044100069420900a86601c800c0c0f54540554032402d020652030b03500e0681034040c0b0f1187d61f407a83c2e96a1941401400c860841d00704070f402c0070200003407264072101c0300207644115030801b0300210300210210040700c1c403d03503244c8002d4104250003040c03801d0303e0083c0d060086041c0d032003000b4800391015078202c60407a41010b1004204151015082c404034032682c0c0c214003580d100340000106051240c0000307180a40031102ca80758261903810181000001f44023aa40168440b00101001d80750740c040c0580707690507200b01c14a001c11411080c0107011504070340e200d03900385400301003100c0ca849c0c050080d12071040b41e0340305000c40c0401710080034003018941a60000c940a54a500c04070b50b5030a100002507030082c00900c104072410301c0070242c0c040c44540c00d022091041541c8910603102074245820300750201445900c0034079100003080500c070040501140c01e039200312445008001443c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 501202886 1250 501201636 501201653
    0x1c0b04060c020c091015090312050c1009052802031c0504050d05010b041b080a020d02091c05011503050a0f05011410090b0a030206180604080f03180d0f0f 68
    0xa2070954030801c10018015a100e10029a00c15108110078851740e03602c0039035003507c00f60705038400208551480f42c0040d604c0c41c4038a001d080b060710820252180846031030710410a03242070364802e5800f600010b51184155422140000d6010400301d400d1003180701c50f800017a00ea545024112110a0285002c00c91040c4034100320341c041c1800070410450340c809806c1c00e40c000c08018003030a00441c0707000f40c80082142c100d80d403028010220354911203281d41c2d5406110183d0000307030b5a2423105809100c80c500d2a51142c0818000d9030080c0010300048a003424040e0a4400c0006200c0c01804481424000704030041120a852508042000100042454100d0051110145000000c0c7d1a4002d2004040c0e4200c48541181c0c40f08205000300c0401c58100801005548002542301c1c4081000301803513920210344001500d401007019040540d00d0740080e0410442100340c01490300005801105010181c01054000c030050f1250f00c3e004c0c0d03150b5651080c00d0141c2001904001c02c10010604110014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 501204136 1250 501202886 501202903
    0x13270f0e0a0b0117060c07080a020a060905010e06100f091a09010e090d2c040b060f090a1508040201110a0c1203110d0806060c010603020604030c051c0b04060c02 71
    0x24030072203000c03042600388079800e40000c2c002c801e404400403034000900d00000440e076001c1e03800d00150a2409071a60343d10f8416a0102c000070055014441028011914500c50404e0782c0303000c0c5c8000300d50b0440904841c1d0400c2001010001e004051003000e20441d4a11000c460030384144800000b2411604003038003c644c0303080590750f0750280c4114000324560701c11414182c0640030380012200b5403500710b80180c59103030710300c03400032160340300c116003030180b034488520b0030220200c0580002038921501c2e0101c0c81d168401c04050340c0300100010034090908000da1443e00402d25a40c250041c0030942c48000c004d02000f0740068108940d2001100b00b0050030b103c0c0025244c0d002c0c1100c03d09960340d106041510f04d052000740d020890503901600590300119003100211080da8440e90319981d10342c01c210301070b00703c0051072000e91340c1c80c0b60100050300d4110040010394020b244481c407143c43c0034100003010300700b82c4207034001104e803544010000b044202403540040d408500031486020341803040b4a8605213 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 501205386 1250 501204136 501204161
    0x405010e0402070b10060f050c0303071d031203150303120406021b06010305100b040516050a09080f0601170a05030a141603120c0306030519140a03020313270f 70
    0x104c50034811000701c030403030320801ca038555241d25240c003d03481400d03680c80c047c560000d0f00f1a0400c2002890891294031410420880040c0ea02e28a5601a010038a0801c00006100c00d146000050011503801055014042c0344228005c6180c280c02c0311581c2007901014200900b41c58020039080e402c068508000c201000c0280200d614641c3d490a10a030340708242905003032210300c1d000b0301c407038541007600901d44100414845000c3da80b091060403144c0c1e601052155041005d0b290340421105400c2c4404a01c4c040b001c0c004080c07070750410300011200000b94039601426170000d043c00340003540100980780c00c84424103041040e0f103020316400e0f00621600b0301400106048184000405411200740043ca0610307a904110a803550078080e0111a094080608183c1c400b88a15901307000e001007804507284103a0040e13003000c1411503014074140c1010f81c207c2c00b60f003002c5440000b50041402c4080208150020307001000c0c00b00004200d030003010070202e400c06840d44442d0701e00407007503000440700502 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 501206636 1250 501205386 501205403
    0xa0504080a030801031118130203010e0708150109050f0c03040201090b04081f0b03120304140601080616021501051c0209270303060609090417030f18120405010e040207 74
    0x1d6500e0000c064a5090004945005521702c1419850400304020007801c080d82c4038a401c1d03615594968241000c203280120380c95074079290503400c144400d0240c00010950003005048060a03444400d812083c143c000c00c9080d40750100f0003000d8030180d1161500281c083d04016640c0e1910b000403150b000031604860042da10000340024802d10002e11060801000282c1d64400001600d90784150b03501900141e0b4180d0251a40418109080005680141c42044140d081e00e07441c0e00c0ca241060408d0b07002c040e66410000c10841006014002260007941e54805031080c141c101d20000781c847c2d410f01546000740180c120348200e203007141a55401440c0c005143c90864944400c01185109040d614080080c040806444000c0030000540e07024020040c005030800b5a010148032000c48001c00654000703e40c81d1840403d8400390006601911420038a440d80e803501a41a91014100034191b41495200f200004c03800442d14003a01d003074a4091034030304600c201e02d01c00203001c0c2c000c82001411010 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 501207886 1250 501206636 501206653
    0x210f021225060e120d050f091e011202091005092404090b01080f01030305030405071215050702061e091006090c260411060c0a0f030e0a12080a050408 66
    0x451014680c0101c07810b59031036503540c200c800140014202e10360710010240c1e00403140e0b03001c160300500c040c1c90310611104186040180700d10008142884807402d16072501f5800240c9550395901524a640d50003a429040d4600030414010490050440640030100000825510030751341d1151020301007200010824100b031103840c40a46056031041c4117403140c140c54801001403a5019410303d03842004485400302c4a0381c84d41d02c05490319031000f0310407901c2e400f4007100071505a40c00b05c41c184104e8015414800c410300c40c1d1505404441000c5d0021040d548204100428003040e020302d002000701d087c0600d20702c0c4e1611251140b6024205440700c007100c0c1050000310760a92580d200050303d205954800c1100c3e0642401000c0c10800c401500c0078004c290000100403480d0b0308102c41802c60b0240850703280a10419000d400c20030014011244000e5600802c0207055210340c24441541e0112a0503000754541200e000340c40c41d4005005210103c007150b0038146c94081c105071801809500700340d46544 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 501209136 1250 501207886 501207943
    0x504030302090d051c0212031303200105040317012103020c100c02090a060e041205070c030f050606010311180406030c080a0b011a0a050d1113210f0212 67
    0x4603205c40c841e103044030315034404800d131510005181404200300d480f0b8520b0350712454030819805251500507000c0c845034007803849010320280154180400580000074160400b450000c1103a0521036210f40410000e000620010404c5090220640801c10b011411500f02d40380990900b070044920a0b44007680d06d16020295400c100304442c2540b00322190802c6580d01171781c241c200d03056030040e856000b84840005d000941e89054440380c1f081e86040240c2011026900e00610141c5ea81080702d00032151180303c0d040113010402d907a004002400c042c0300301c541d280b013085242d010300e0079851480120000c4804043e1103a03484100610f0300f04000c8241140c44008842e070300c402003801140c0e40c0c4080400010b0412400305405180201412140c0ca00002c001c81200c280e081518030600e0140d8070754220103030310001c8005103002d01c0401045400c1916242140c02060050820355000e100c1e10b41d0321000203600c548901100560444d1803074111442400812710701101010155180342c001900b41440c07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 501210386 1250 501209136 501209143
    0x601060201060305100e0703021c081b10050402090c070f02040905060f3417150a0e060a031e080d02091e01020d11010e011506030b0901030f03030504030302090d05 72
    0x41d07900031302c100c82d16101c1c0705c5420022201206000d941e281c01c28001070006127400c1c512900004031110141c12002056100c6580a901822080307022140038460424012001c2c49229489400e104c410442460140c0215036485401009907074141e4002482000700080100c484c4003890f0094403c000016440c034200d5903034603003600c01480318224440081d03511407102e072014204208402c4001524103021400440f1308502c00d00c004140300103d081c101000e48444550b501c10049444d481140c4480807041c0590550715821200d04800030904000090310380c1c262400450742c1c8959288040130456503125248c100c1a000141f0010000880d44007803c0c8580241c5400750044a810341201110210358020680b402c4c11103016801900548242c035000395600080303808050008201c0705410035009084508524540501e200c940409029283d0705100740b4003401d40688055240354150f1b1100e0042c068511002010075803140b00090405220380c05032480500e001e009007009119501d0100d84 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 501211636 1250 501210386 501210389
    0x150c010603150e030f040603050709050d0c0e01140306180f06011e050a0e0f060102010608120c0c040c022a0411270d060e0c120303010f080a08090f0111060106020106 73
    0x3450f410180300e0529083c000c811540c0031540c8500c81450503181c070900354051700008000c9018032059000000c0d03240c0710b40041c1c0404a1060003504800c0f41822034003001f190060704108003550340d4192095880e00d0002d1031381d41204903103801da0484180d4140252415018141c00c00e05806a003000081c0100100d4040c01056110554805125112014002125070901c60341c0380c100744910124549408003082681c0086040c800417800c40d0b150b009440c03070400300200a00700d03440006040303455000c1c103001070020358404580502c0f0101030013800a41c0c407401064198004414034071011550078600145100d0304101030010b02c0048400f085011075908182d6400c1000032a04d15040c0007110403100400801400a0141115000507254000100880480520144140381140440d80c0d43c0c3d41c0442d040c1c14400004503665030410400d41c03c0290035500c6502280d00010072900000d40c500305440303c40f5010b680a081c070b07164070b600407a0b07a05242c03090000c00307008020021494076410f402040 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 501212886 1250 501211636 501211673
    0xc0321040c050d12030216021e0a0e07021e1006060f111203130309031403070203160305070e150a030507060e191a12070914120606150c010603 63
    0x264640e03070741c03010701c60700b0105283d0041c551a02140d694074114007175409007028414081ca00103001e0240d0340031400d071400c2d0440203480c01d062840003034118501290090040c00220305d41c0702c1035003840040030b5a02c9180403501102e00b0303100012038803094001c0101c4a009d1120b10401c0c0519966500c018080f142e909130b0040c0014440510000140c0c00020310201c00900d4505e814a107903680180121401c241c0c2c03000718100041c4003400000700f070015441000300c3c680032010303641e0741120384100340c80c0603a072611541e40032902c0340040010810104848003101c48100785100e056079100d51412100003c022102d611410300c12001c000e120b000550001550907980352140e40240c68801c00c0800d03500c0c0c2c0034009245040210078801840d44002c080c4040c04914002800d2458154200c4100c801c2210914006241c00c0b008010394142010410800d26058a40003281c0b15180041030f11401c0046c0f0070350042070040190600101c01030112003003100801d00800c00c4030f4407442e00250a820312484c51 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 501214136 1250 501212886 501212903
    0x10b0d06061b15061d060f01090303020615120d0c0537020a0506030135032a011119030204081b010509040207120f0f0e01050c032104 59
    0xc5442401407140c003042d254494980007500ca0385580c1ea0010501d9240f583c1d080782d480d9080041c1c002141d00308040300880b06030744280145403a8042c00321800038030407801e04000c000394040011980100b4000c0d046004552121450000724000c279103c0c4081a2081956205041001c0c0d8003a42c0701066440c154460000c2c1d854070a0940030720940c50f9001d012a51000d580b000c5c075084012400b01c41d401c0a036202038540c80d40340e40d450000802c20703007003684103500850070029a40c441000240c40042c1c841a04003141c0c1003150b0803c405943c0e40620f007259248841048880e2034000c00d41400c00b81c0e1200540002d119180c0c0310714a0400b00c0c1c12110b4aa00c40c0c085005550a1130350081c02a0780540e046c4030024030400c18020071000040d1039260030641801300802c0b51014584590006255160280f1807200210554440c001e03d200681a00c20003000105400d10248507400165465003010900e019500c440d640c400d10341c158820010485003154900c2500350511200103400c0d8403d41c0541c003030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 501215386 1250 501214136 501214139
    0x10201060e0615031e0106200313090c09051f1106010302010f120f18050c09060618010519030e06010b0c122506061403030705060103080f070b010b0d06 67
    0x844a0301101607030501d500c42841e41d102d0200d043c040c0b0107568045202c46094100008003000354100c1d040c02c0c1c02000020303080d805100902980e80307480c034a481c0c0241004510b00340c0d407400d103021f1070340d003038001e80f0002a1289502c2d05e044e44a4a0000090703c0018500703c108c1480c3c0f40c00c4884402500d00d1840456514080d00301901c2000c80ca60f4100d81e01a11242c96005a0308000c60b026140c034404000c904d5036134030ba00701042405108020307010030110405500b01455060451424500b812014800d0b0280f004103c00c50326040240d61004216003081841424450010b0f0703071502440e440364598000511181080c0f55060b0442851a0642c0c1d081e1943d9907200d00c0c584809100e0802c06074030f2030f4000310f03090345462032070320040400300640c8402084186c210349900e50049800d080603076903d07884100a2140c04400804040d2561080303009510b09041599600e07143d1405200c0500188400300f8849240d42c0d4000032100d2076944440000495a11903000b40c5058105500076100946400300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 501216636 1250 501215386 501215399
    0x40b0f0301060b09182e0308030408040f0b03151201060308071109010503030a0504150c290901060501080a0906140a05070336030908100603020301141605030a06210201020106 77
    0x2e255004940c078006c03100c211000300c0c0c0d00d03184e020800e80c9045e0840713034010f03030000c0400d00c010f0166000d02c0c0f08001e0141d82d6840c1c403500348401f00c0e0b90b4104c2c68580e40c1c20003c2c072882020f040e244640800f42a6400c2c01009c0c4801c211a0040c481c507400074109982c0003d01c0c0342040704100c0c0480c0080000c032004901d80c2d0303c032000e2656034051200c80d4404248100800e001c607003c0c1200c0044100307210701d050746040200342d60300c1e450661a4954442c1020300000320343c0445c003400e0070050740642800000c014480c0360100080240d980584a90107081e070300c05840040c4180d03034100c00c0e0111100d14500c00181001c0003004000d02088070224000307403a08508000000c80d1000540200501c403440c20070420002a400c94000074214085083c010000800245172605100c0e04500d000c00d8140002e0061840c014507081d62603085050000281b2041003100411060744400e003015001e00d0140e8991303850405203c0104590340040c20804800041c1c80030102111403c0c4000300d200303030300170b20603a61340381c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 501217886 1250 501216636 501216679
    0x2120d050f0d0b0d030f08070f090611030d0e030705070617010303031e061e05041b080924070315050303090d050c0a06050a080c0f09040b0f0301060b09 67
    0x1906500240081058101d2410000082c100200140300002046040c46002455840d007040084001c10004414094060740101d0002e501c41c00508180650a03141200181190703102c0c050181809111300c0c04014100301081070b2001d8044001040018809146440790b0307940022204440c14450240d0100d60b4601c00d000d0304003200c42820282955900710355045d405802000000b00380100002e00d21701c0045610f00400000b000642c4165220f928405800c13659006903812860017641020a8070f03c05088101d400c002c01c505620300001e2071303160102820309040c07504d0f03140190340d01e00c01c40110b1300c420740a252038000c01c102c1d00c0070400f2161701110b40045115a20595074550401d0048a406080000c4802d440910a4003a40d071003585034000140702d1a1240c00400002d0408112001000d0f04040a9504001503600160401440a041807421300c5140511741c0165120085002107440391100c45a81c540010020b00c482c94031b07400881e41541140312040d00c6070030406142141615500c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 501219136 1250 501217886 501217903
    0x60b040b130605130b0307020c0a090501141c02210604030504050103270803181605040e06010f0621050a0506030c15180607080d0506010206161b0c050d0503070212 72
    0x910481145142082e5107811b504020041025030041c61f0054845030b55004030b0b038014180c626000507503541003003200103016500314140c0f80240902c0540c64105000100a030242e142d0458540c17070b04d825a0843d0004254880c2c100f000a8400c03441440200741c1c00c00080c0055900c20703a8104015460000101d00a548030080a54451600b000700c10111303071004011070344003080b41810f6202d0340c00b41c105c0e10320340f001400030403040940c8044140114036180c02025401a01a0001d041c154102107000b0082125441104144820003204000701040301c1c200d00340400444d401040726181c4030032004058042151203034400d00a02d01e4190103441c1117910008500c02ca00ac81d541041280705203030440e41040c80c41950300c10818441c04000820660050a105804c020085690300308800007900e400c0c000780c12060016002080b140505500c1100201c803010f0401d040000008a4100584412815000260400c1c800610203081c03180000c02000910b00c2a00c030300c1c0304010101c0149807102d040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 501220386 1250 501219136 501219157
    0x90714121e132018060a06030603171e0307110c040606020c0402090d020409050a060b0f1509010306170a0512132907030c02030c0f1c06060b040b130605 67
    0x19604a40407806000752182120004100c0022803a0f0f40400200011a0302042030303a4410ba003000c0141504040c0600304c01800d040c1428481e80e415651440451034514000003a8180d011444640305080f4902308001c940629040c0ca40d2030901c003900414444201c6602d154038820380300c2400c041c0c20148100811911140e010301420300380350003040f01a60000d4600340d44000080070200160303580c0e00c1427410702c1d0701c10401800c1110315864000305465441c4412482a280580030000c039440e02c3c5400130018904094450381c440300100160000c006a80003550280032006a90204c1000015030640c40c900900441e0181c81c1c071003229120741d105130307a0302e02200c001d011401c000340808161210220705010075010340c0618070749004d1499800044041d00040c0d4014881c100350f060520006201600659001c071600000030003250581500c0a503451070010a150f10707a080c40080e50100001c3c00d00140c5143d502c0d55154100401030b0004141100e01012095001940901400c01c0b00e110703070301 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 501221636 1250 501220386 501220411
    0x20415080706090b04151d0d11040e0a2f090c09011b020a1208070b0103080d0e0109050705090c07050115030c1d0403052209320a0f0204091b020d02070b09090714121e 73
    0x1a404043c3c1c0cdc010020b90000c2c20480810340003510b0b41e0310305d03c0c050301c20f99000c00c24640b030341c030400001000d103258000602500100d000d03514000d82c9881e000602540c2d4054070454100d0b5062505100314821101c002d0800240100044100504840180360600a039503082c4014480310420380c2c03c81d2000c000c01001075004200801030b80c1050f10038641d100c06e0714115141400002d031205829640407145460503204085801d008002403082c003500500031048007907812030503403c2070881e00301300540042e052083c003040c440503112001e2523002c51034042d1a080030400d44e0391081c150142c0a07040700110203048030424080e0407185001d066961003c180f500c450191900d009910040004051a111480e020000822080014010968001e00c04c00704101600c00030b03440282042c03030181582d02190007021080140000400c00d4400c44c45003101ca03504941c4903103405071500c090401c0403043c10034001c180c040004404400e00c03840f90049036654051502410300c4048008000c5400128010 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 501222886 1250 501221636 501221663
    0xb0c0d0e010914091e070e0102060c030106080a05060f030316020405060d05030301030f26090a06081005210123010b07020112020304020415080706090b04151d0d11040e0a 75
    0xd400b01c604c90b0007828902d02000a21515004071105c08821210100898203840001c556564100b0589500c2104031900e00d080d5410b1480050124101031710b8103400c0e03911100410b009a4500c1040c03060040000c00302da13903400fa404200d104072002884280e00c500d18280000d061400c003683c2c88070030142e01c50003841ca9603003142d03900d1507050010f950a80b59203c000c030f94040d100c400c0c40301600180d014844810380360400501003161004141d00000c0030003600a040c4201041e8a11103141500d100301c032105600492a4520301c00c4040c210441d007515828040c40c407410707a800050302c029050380300c038801c4e0040ea200c20000f503043c41034100007400034001d0080c043c442541c81c3d01854201d44010404100410101a43c020917a02030f0003041003508010f000304101c540200440c0e0003003e11100e62806c2a1511001c00d462400c0d24010005108048c001000764800740521861200801421a02c0c00f070801d0800600c80b1254006543c000c900d400b440f00c07031a0a00184408403554042c0c440050403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 501224136 1250 501222886 501222889
    0xa090605100f17010e0412020a030801140402071707120807020d030e030903070314010605120d0f11031809070e21030403140d0807050f070b0c040b0c0d0e010914 71
    0x80d01c0c01001401c209000502071500207241c000b05009114207400602c0c03030300b01400c0c001075507c0a95400005c1d940105c84550020780c008400d68111807902e03003107803000550440400d000e880380c2040108408062140342e1955200113002d0901107010351209440b44c1034160040c1e0f4100070a881407805039010f1602508428425000b00500101040c1980d0400c641c0f2004245440050b410445031511821090580c0c0301003403080c00010310085036440e0002040340080340d16010411511010000c000d0140c5078824080e000c6088548110421030f41e8404841c5503500044031503681c014810740b000d6020440d4544a030040d086860741c001c0c80c00341032001c0005941800758400740f1a4026000a00000000c10b0714081e14001d0b0700b40d40405803185842a4034002d089209c010240414000180324084410b02c1610965446980c8035042503803503125129020380600890388052504400001d0101c04540d01081002401300d13580c8464124400c0d480040d261416180078281c0c2e69000f2410782c0016 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 501225386 1250 501224136 501224147
    0xc071e030c090902130e010b0909010213030b180d050702100f020d03090507051005040810020f0f0a0c0c12050705010201060501050901050d090209041406060d1a0403021e07050a09060510 82
    0x603070701c02002040105c1c05540030500b80d0390245000220b0b659a503d412030141841e0400942c040c030034130021843c1c4003600c0400314201996000c0030b00003051440000b980c3ca0021501118000c607400b088450101000100424070391122808a004400a10040c10144d01030800d0905611542d0054420311401140460080c0603c8409031818460684000350310f440381400d880b100c003101d9440c240c3d40c6082c42d10140c908061076070b00030220780c0304102c0347c00504440002c0d03a0360803620011896a52541e09000c5440c09210740300500002c1da000b40000302c1c480702015803001c15115030709403044643e4800041e402ca40051251038003007031040010094540c482c500400c9899000c50b4005860003643d000708040e6042120200c0d206a040b0b02010010041045465032021045451702c3d84070001d6a9400d80d2810032945000f085c0701002d0100341094000d0002e60680561a83c1085611064035142540d58501d4403a103405201e203284e001c03900c580c05001d0501070302c5005d0280c20000f108200c04880 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 501226636 1250 501225386 501225401
    0x110405191107030f08270c01020f060606070f0501060801020301060e1003050702060a0903050c061f080d14030603030705010912030b0f033a020a0c0605120402130b0301020c071e030c09 81
    0x500001a5420160800c15291b1035041c0d00a881c00804c0c05031001c80029182035840c2c0007a800642c400300c200031a641c0c6074000c54400740d61145029808160070720700640500100d07041091994004400881c3c43c40d4081d1104010a030201c0e1032501055244030182c0c101c030810b6650700300507001035001400c032891139001651010300c02d10b803d505d481c04c841e4086040c214252410300d84800000141103081c800a001080a000c0390707405805900c070317940d2000c0e200c0b0003102003404040b40d0100001d440c61398180251607035a44c1040c001d100058151500b007208030184400c600c042440c144442c24681007020041c7c00d1000007800030100101000d4180c13200d0f030a18480b201c03407041b43c035040e00b0f4a46480003c40700e80d491190010542c4815624005d502c08901d03401c298104041030000c51590b003101b0981903081501910700080764007030001302c2d00280902d4071109807d5800083c20441016000843c981107810f00d80c81c80c1106040004503440689441c8000b40600300100f070140180151a0301c26407 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 501227886 1250 501226636 501226651
    0x20a020a02150301061106010f14010c050a0308091209030303040818031203190515041113120b07050307120b130e010f0501060306051c110405191107030f08 69
    0x403000301081d40040d075010340d882c540100040c804001000b40030f8000104809001801028156543c149017042d0040300440c403c02c0540c0400c054407081603402401c001cac51142e00b080507030341c00f120682800390000700c0030340b801d00403880384010b04007140c4188410f449078404010080e43c5142c07100d44410405401103210b80d070080c10300b00d00800da642c0c0c3c108101d4025443c181d0580d0f84a14000c1204003c262094080d6007406040c82c3c1004003c41a6000070300b001102203800064298004210420902400d450380c503005c2c0f03410304042041d2400d03039a440f480c28807800c480c20340780d038601a04903410700041e1200300102d0303040082c0b104600d9003600609070011000c2d000721003005552401006a90800003c0400c17659100c55402415041d40261030141a6900341849458604000f082c100e44450b00e0340f500d0301c4512428182007060003000b0828a12000700284520f050829020740d45400d442d460751095481e00c007004103030340c90280903641c070a60140c4821200400840e030039644040d0061454 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 501229136 1250 501227886 501227893
    0x1020a20060c0d0e0405131b180605030601051c0807052b030506030a030f030e0c120312010f0f030210020f01050117071e060302090a080d020c0f04090209010603020a02 74
    0x86280c0c0c8070040580800c0702c0b20401031200401400c00585469250340086014078180420000742c00f81c4407442050031584035118015185050100410000064000400b000c1c41e0508a881c05040ca030480c1c429190100c0661702c01c0d9a90340200a00c03211400304060084102003e824080381d406005003030740a01440682c0c007088a130388440c010031045601030942010802d501014015414407420342d0000c4103400420b0341c240705480140c040101581040300305920f4a0b03182c900003106201400a03200302a00709849038454010403900c81d04a0704440000002420000880c0480300320800100d80003254113208040c01c6801780700740c0311202c03030710074041d8407507800040341451092040b41c4c000e01203441e10003422031030205001e0400e821a8401144038034482404001900c0b9103003a081100c8007801c00503500d61110f00429000c131f07003582c000b429902907040c015011704e801003075480030184d088641d200110b4443c0f04220803103030700704006074000150f5001484158001e5004125210f0342d801103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 501230386 1250 501229136 501229193
    0x3091201051620070609030c060809151810063f06021213030201060611071e0f330509040b191d220b0402130204060c0201020d080601020a 61
    0x2d0a251004c40c0d0711210000d10b0242d0b0070401c1c008030000d8a00076041034a00604541000100c4680c3c80500300001ca040030b19000c040380400c816103121a42400030349003a00e40b44210b81d08810000c100c184622842c20382c1d07907003d000d001003040c1038070b9290b645440148400300f42961614009082c0d880003c07584103600700145008419a2010380784a0342c01d0349017a20b520394980c03400a00b5202c00380c0c44801440506018010f61010108024050740c0650900002080b03045901e54080305440d8401441003010002c00301c0e04c0050300003590a20102c0e507000c0361103001068403540c004030030b46c00408005002030210315410300c0c0a400c20140c4140c003d10503001d0404001030701040c500c2a030710180e0b0b107080b105130040d107200c08841d4440d40516039101c1022a80e0440f400014074081a280040901c00342030001411507445a42e58041110b00c82021074031580c490401500c10580c208040c0e001d88600c8800c0608248030390100c42c0300c1c001c103038080c1100500ca0395034480d03d04000f6441c1100034200c50403 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 501231636 1250 501230386 501230447
    0x307090c0509120f07090c090b0705010f050408030a0c05040501140a2c0901050402070c1203050705070906050127090f0f0c0c0b0114010f111509030912010516 70
    0x26907040d010f00700541104903001c0d800741c0c9003c09a9001c01d4601c2d0905544085080e044000c0d5411507021461b21503903100c0c0c9140840c01426103121855500d484d141c00e00040c4100301c3c1c00b0351310030340121a080107101c044980903111800f442c03081d503002585803a00500c80a0004029010f6410300d03051503141c207040c01000d401c062030102c8040d4510709070748a8407100351500c40b004500401043d0b40452405e82c4c592030368205030f0424025031000816400e820b40426108100320303280150410306880c2c80c0307034807000003401500c42d40c802c8500155540b002e072040c0e005d221446503c21204603600d031000b18540407115000d0113800f0001c40086607140c500c1500450a400b44c420152020343c0c0714840500e941c50801d00c21103041e0003281000c11800d192054990f00520911138810a83c02c1c800081e00c4080c00c0503260140000740c10f414543d20b141400040030300000904081501100c03a81e00b20414500c08500321041254540158120700303c61a0302c540c05540003943c031800081450300989801070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 501232886 1250 501231636 501231649
    0x30d0c1109010312181d06130608061e07120b0d021806031603080301031e14010b030d110703020f0a030b0906010311100e011812080c0606010804020307090c0509 71
    0xd02c00e5951350b0310b070300480c44000c0d40101c09820920601c1003042c200341c10903030381e54004d017040c0403060394407165940454201d0b035941960320b003001040e0f1810300840d138569411540b81c2078141d89000380b002003540c03402d0500030500e031030602c02c1d001c5030390b0b80345817540307900309071010b0609424815005600c40d440d107000b60b144c0d4880745010710f200480d00d03541c5003007005c149440c1542d03030161011905d810303482c140f000072182011a41101e07080300c161000d8403a4811299021810b1782c1c002080d1301d461499406410206400500d1071328012010358180c0034a0140582c0d04030402c0d124044c09400c404401c0c001441c0200b28034851510141030030405940303d5076000780482056500062a6002030010410040c1c000342e0700708a94003d0b60038880418800101820f40303480300f0308960500203004036203000c0132010301d200c00c002e1001401c101c04001c1c0c1410b0001103640b0081402c0c0d4540a20360008102c0d50007002840d01503070b8060008c210181c507041c4030a00400300c030f848060400904000e01d905503501c030b0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 501234136 1250 501232886 501232889
    0x2701020f04030c080c0a0b0c010b04060914060f0a18090b090a0521030c070510020d1e021905030405031225080c09010c02010e06030406090c14030d0c110901 69
    0x5000c0e140e51103045050046000d1403541c02005544d11501c3c0d40012a19001c241e00202c1d0310b400c1016480d1801c01800c00d024004412081d80c00c1840d100002030310362007540080c045003c1280408103a43c480d01e050006c08580c958940c4e070090800802008001034020a0040ba92a0101d000640300e45966842c01c01100a0301d00e01c1040c0d100041020a20105001c0407006402c49020398000495101c03061040340402890044187c401045a00c00c0c0b00c424001040000400c0004660307031303840008036800030003142c13886c015048204051041d908102e13101f01c07090405120b03400b00e01d1340803824045030103a04c010003c0341c03180410f1002e045c601d0514010603024207074a00d10b14400307450b0020b4054204e111902440c003001420828003640005840407590b6040080c078080420403160300040e00d12109280705990000742c0082048280f000c00d1388919178081c0308400c00d8410703590b5508213841c3d0800c0b10f245036030b050700074004000405006140c038284c0188164550040410340c0000281c201209 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 501235386 1250 501234136 501234157
    0x2a0e190512100221150d0303090302030d0501031b090b060306040203060a0f03112d0f01090b040e0709120b2802071212091e0503090d1b0b0f03270102 66
    0xc0d20100000401603d0a02e07448810030342c40c10174511715200051110100100007070141580d41e176062043c9482441161042900100305120650303480c5802903010001601d050784114107400081204001801642d900f604020b020900f1030310b400f01040020f60015207480d0b40100c0851002584d9448042841f00550084c402c48800303003c07000038048031110110503001d039002a0000c0b040e004125118100406c0ca060b120003124240c0080169401800e035040070003504070104001038515500801e95100d2482036980b0722034a552146820004224244014840440c103030025012002c2c05681030a11581c20100f1030000c0e1103400010126813083e5400d5595031a2085030180840e04140340d1900301c00c042104200d41e489030340303c04c0100185000d50030f402d00c4180d4040d20a0190070400e403540c400d00146038140402c40e5103051481221005004c000c140c5449000203407170800802030380c1e051a013410303140b480d503514803000740b01a2107001c1c81c1034043c40240520106041c000d1029001c060780 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 501236636 1250 501235386 501235417
    0x714030309130b040b010905030a0311010b1207080705030726030913020d060b13180603061b03050f072718060314060601020a0201122a0e1905121002 66
    0x4081800b0564040b00e08446c10b1000c83e0408100c02d8400140b421081a0149411140d035540d9284450142c00901c100640c04201c3e50003040342c084020806100301d440c2c1400321141c16685009058032250540704d41100c00718660ba0703542190501421200e030545101c0f0907646002a8100003a81401c450600b078138082c3e03804100320f607201c0454490b58003c2c08000546c0350600110034210301d9604520f0155084000290300c41e00c00301e038400c0e0020005181d03c03007000c0c06541e5040ea840004882c18029100010b42001301041b03034844822502802a6905d5888020540c02086241c040b410001101d007020384900000007444000f000b50038480070f0250b000400c000f0300c0c40c100520b6800d019800240c49070041c02c10700482d0303a0001140c81400d07a0a003841c41e071420030303079006000414000170540340b0f14102c001c038a42c454090b034a084800d0803807900d070140924808030501c2042c1c3c00300d0b46140c074103070242032051000c0c2c039000c50b83c002600154811a940c02d0060780b4a00e00341e0b007041401455091 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 501237886 1250 501236636 501236651
    0x3220b10050316080607180e0c03061e0904111201111914042601091b120b01170f0304090b09010b0a05030406020d0e06040302060402030601050111071403030913 71
    0x107424082c2ca04460301c5a002c0320380f400c0c20400301039243e10380904018188010200810340c410505001c50303000740302850640d0032a28120703901e50b02e580c1c4100d501e6072040b583e08251051490700c00c1c541c5916140040d00c11090f0b41d540b035a40b00c0c13030000e010800c1c0d64010100c40c0280c00440b4240903101062244810b070130346429140ca9041900902d0044900500080c00d0807202070048400c01e07201141d1114000d030030781c0482183c82011210400d01c00c0a03a650800550000340004103a02c010862a00702d0100075031561492800d0540040c214014001002d00740104681c0d40000b0b0b05011000c3c4003c240c0d240c130b1008180103881d55000340d00a001143d1030782d018100c540340500080e4010034031200218a090034820006060340700040008000c280e01048094140825902c886240016181150540d040ca810003070f580380e0003240e0483c443d20501002244035403042400c03102d100740f46002400d45030304180e071607003084040c0c0c06001c0d01403006005210780307a501c02402070f5400c144140b00003100d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 501239136 1250 501237886 501237889
    0x4030f0806030f0c040507031e020a1e020a0201030b13150e100e07110c13020d05010807050f06090f03060c0c010c0503150d032d2303220b1005 63
    0x8040040805110341c0240e99840c1d5103c50200b072414101c0c40448002910b65100a020381c020000444184100c00610a0030000819180c4c0240343e9101c2e9511840f40385a1194102600c1c811400c10300300050b04181c0c28600154000d412400405400810910a00101e00c070598111041c80c0c241083c07500204004000d603a02034104550081c0e00c903d03178090414100080b503c48240082c00b80020010000005540c5400a0101d000000c00081c0091030b08051140904040e4100c4119100d4444c0381c4070002404000c00100241255005400301c00c0840202d0104007660b003012020307940100d10800345040540d801e109040c402c150aa10700c1e6120b00c03850030040c0c00c4880d801724200038840c040003030120030105d0007180314440d003088540000c0300e02c5503c1d00315a40c50031441007401c11440e81c1d503141c18002140e035000c0e130321481e10b40d02c0c13842407254020302c4512000350f140d00e0041501c0400201d21030294145d00d071311405100d0280c0c50314442c0d240e0740ba003000710b00031616980d6502d034101c02403015 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 501240386 1250 501239136 501239147
    0x120a02011205040b01050603090102040b1b1c230408030a080f090601080709091104090c090e06010b030c030601140c010f24060305100302031501090b060c0604020f04090b04030f 78
    0x120310400400c02c1245802e0780c401c070702d042c01802101e102d001c011001500200003501250003401c00f107a5007030307141ca00f0603440d0f26106d42c441800e15810300a00c0044122018617210f03040c03415159544800c07101c1c1002649003038290721602c0c10412880104404074100360708200070b101401c40ca55a4000c4da14011070160144c0a02400c00010381e04408010412008000341140507280c00341000989101c251a103c00f00342e0400411907040781c1443d07a5103007403051503460141284c40d181d4003849504100b1020649601090007210402c00e0107201080c4800819000345a006e80306042032200b4a03400840a02c0c0c03a00b051035541d00981d12500b6040f050a00c600801c0d00f40c220700c448600b0000c0c8400e071812504d0242e402001c04141d603d50000701049284d0940500654000d0300741c1e490302e900c0e0208920000e00034016032030014208102a4900d0a08074200d03031500740d540000c0c00e10f07a12240c2c204100007514820080d449034441d24200041440d07004100e0159109441c0c5998584070b40b60b02516 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 501241636 1250 501240386 501240407
    0x11070b090d03180c09020a0302091806130c0813020a0b04030804090f020f030402100216240504050319060b090a0e0d18091122171f0507030605120a0201 67
    0xf035840000c0d80400501100e590f5003d0310521240580c079040d0090048009016610301c80da808104480209400c1d40824901400f50314140c90780915640811801700036500d004091000041c1c02c0000140801c0030f585514440600c0100010044c99803400c80d041242c1164005030f0b281c0710002803c03c003012040c450942001c8008a05504208510407042c41d1408010320180c010681445143c914a20a1040c0314694206030213595440e0744580440c003003150103144841208408189a028840c010303401d5070100c03100200100b80b0300404a031540e441d500710a000311080380d140e41c2c81d1704243c0d03a010251881120249000607007581808100362a05e816050103009005410020010107134914040b44e060701c04c80000030540500d0f281c642030903880b0700f000f20003060321841c088054082c130812100c000c071046629030100c0e904009600c6a16420f646001088141c6840c484420000880d0003184d4446014100050125565404122400610102d24101e500700c01c44040c11580c002c0050ba0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 501242886 1250 501241636 501241661
    0xa0e1c051204081b0a0303030e071809021912080f040b210a09030519051603021606050903030703080a0e0f030a0f0302040503070b1c06090b1c031211070b090d03 71
    0x5406106080405c00340d407428040a000c03d034440b900e03c0b00f0600d0411100006081c0f038070b45501890700402d1448010041c0040483c0301d88a46100c00a08468080d000c01c20b6500080c0000c1e4031490303a07910f0030945c0e071062801c6801c4440600001428181d4500030b0301c40701075a1501c100c0181a0010681501d6400a1407000301a140030401c2300881e0348941030f90801e0180e104034002e42809044207440038005c0710740100725a00d140e038900d808c040e40420701003000d510030f800d00e820040d11740e5415039007030043c4024103400d9071040c45100b003c684100b020f15080710280000040d0780300c0d0500d5003810b0400001c1c405449a00000c9c0c900046580212805140d00d01d5180450070070307003400f00298542030a440f94142d113031070224810b0051032550010300100c2c13010706401c00040f41d031001d8110103040502c4806228034103600035400d034006080c41a401655243d0358000c0c0100d03055090000810003e4025111035400340319980001c2c40e8480c0850081900e00028103c130458008010142c656440401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 501244136 1250 501242886 501242923
    0xb0108010507020d050a21061502120f030a0603051005010e100311040e011107050f070b090f2e08010918080409050426030403140a0e1c05120408 64
    0x20100550104070440d0813401da18046640d05008201111660410300c00d0b1480140c44080c80c0d1000c0d5880d038007102c2102e440a43c00b0901050f600c1d816602d8204100011404035402c019a1070340102120085031300000c075110000303c0c0343c0c60352a00c03403030300c50300b2035032250368a40d5170006100c11034201d03180590110704616590025801c541d5103144003802c030b8000e06c0c040d40d1900c2d003040c001c00080d00710f090072411461199890715014100399550f43c40690403031225020380c0101181100000c030446400d118050010100d0089280030701180003543c1c00d0441d485041804880740010303070050200062550307559542541c1d410850031000300e4250314a000384542d86500224009110b10081c0c804480111a000a156686090005200e801c203500c5407030042a0f400242440e400c040d001e10300480c0246d80300b110315200d1a540060f01c1c0700f16070b441c40115540e40421306183c40c1c20401e92000000200002c00810f40c1c55480c81d1038100401c0d040baa41a1011809221020b8100a190030036902100e44 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 501245386 1250 501244136 501244141
    0x108030306010908010b0f0904110d0503040f0503011505101e09090e030403022409030a06091509200f0a090c080708010b120c1207050405040b04020c03160311010510030b01080105 79
    0x7e081204050f1749034020070000c000a0140f142c070341104030100b00003501401010900745022602c0741c1c408c1c068244621401d203c04202820b0521480c8840c210084082c580c0c613080038200246004c040703009604204c2c082c1200d014030412400c9040304200300c0e444603102c0b20f080c9074012040e070b0810211440c259205000800147e5968200c4034a28201e900e0340601400100000314114070400c22403e40501c41c80c0090010880d1503401544424060010305614654a40007001038403c0e074280503140f2045002100d18030f000300503100f8000329004045030000414040480c446c0c1070340d035203c10f8000b50f0310341000f014160000c05c680c0c3d1040342884d20202c079604052100c0e005015a0146001400300c0d00000703484032a1400488a40c521010a2003526240c044c0000b4180d1784980901d41c001c50402840210320304040c000e44803a050810301460400040400200c0d01540e0b00c0003c0d020003007184035075650960280720781400740c4460511000c205040d800d2548010038182c0c080d844c180e01d001c08 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 501246636 1250 501245386 501245389
    0x302030613022703210403060f053304050f01172a01050f0c06060a090c1202130308040f140109060206060d0201021c02061b040e040b1902030108030306010908010b 72
    0xd00c3c0440e050701200100e0540c03440e00401e103002c480705c880c403500c68111081030301c0c560b0041c0080c0044034450300b018441d5281c03a100400644130b0588450a011003110a0030400800d03001c10010920081007070302c454446450002001d45905499a800c200038520060000015100c0c03111503121004000703103080321a24803030705002e60901c01690000d1901e92008449070303100d40b0890303040e00000110503032503880d601c008035200d0000f03480c1c50b4450304d440c1c5400141701400c0c1c087c040f0780d00c55035100da90f600786251051a019600114101c2ea294014000c003000003042040900003400d03005c0001036840c1d042900c443c4907600481d02540c103010007120100034940d40020108c1e4031500a8440a900c560303244010303481c10303d00e240840d00c0f015062006c0d405080e07001406c54404c0300d516a003481c0110240c3c614000350701c550b0040e070302d00c0c0749154001800315500906c02030700090303000b425001c42079000741c540b006c0ba042a0401d1107103800000a2128541e03009000c4409400100c0c000c1000b806007a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 501247886 1250 501246636 501246667
    0x302070c03081806031608090f07061b020d0c0f090b10030b180711070b18010f050c150a0509150a09020f0a03081215011b060219030203061302 63
    0x11008180030800280f14000f0055114568001c0002600340c07900c0b0309000103441242d0f040404008006484103002581c2c03200000354282c40b1051040190460a0502004036000d00010300342455a0490a080100680360144c081e10b180d070040004816580c24a00040c00050b1180e12694209041a44240d090381e50346540e03501c2d4078598140024091808000b03e410700d0ba4601e070700d203a01d02c4042c0400c00800e40dc01800981c1294140903143e525131114941042d60046002240d0424800ca1600c130b0594010301c1021203141c0c00c3d04103a030030840c902042d40d1401105030006418041040284040404a8013070142c2040d00308000d0b10020101200381000100c00801c200c08464581c40341500799103540c1441000b43d00040c014038040b03900e23424140d404e9805850050914021000010b8800a50310b00000e03070315205944170310000002002c000c001c0e0201d25415103c06908002c0340c03008103610300341000500c0050700e0250b04c0e494204100511f125483c400b8090b80b40c010003c0d90702040600 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 501249136 1250 501247886 501247889
    0x7020304061b0318090b0a0b030c09041d060124050712080a0e070b040303080f040506040803060114190e0607030206040f08120a0f0c030c050a0f0e03031c0b010302070c 74
    0x1080900904241030404854021644c560100310319a0201c020400b08180c1d003000e201c1440075102c204030311b940e07449440d0851104a8002040100c107000f640d003949801d8011480f601d40c046815120320004000060401070280e111141502440340002c0c88a076003070b40e80b64503580107410024103100316a12506105803e000d03000080041c6100068203030802c40c1d006c020f0307500c4920110703000951034009000c0980c4c028001500480c51150009034a002e00d800410300c00c0c3d03401000343c1141d842c1c0d542c0d40b41d13058201400c1306062025203104c01418050305006800810300c0d40172402445288400042d0543d01400c0c0000d0140300104030710740103c0d4000070501c6c4c01c07550100c2d541100d282a42480800d03401001841d484600c51001405452082a0403140140c130845001300300007200c450303050b01140c605808113008940c1c01c3c003000f030146000c3d0b2581211000141007000540003100c00003819a403014000b482030031210018440d03419005d108000308004203080c01c500e0f24080c1e0301d60424841c410b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 501250386 1250 501249136 501249167
    0x30f0d09111519031506030b04050a05040c060804031205040605041a090c1e1c060b0607031e0207080d0c0309090c050f0a02010902030714031b011202130302060406050a02060702030406 81
    0x8403d81c0c4078543c80790380003c440b54248039080300c2040d1620002006021002141d80c03050341045c0c00b15414802c0b600c201d90041d54000302040030f040c6801410f40d00c40f07200810503400e000703004400300800303c000c3c002ca600c624420840044c042c602841c0c1001b00040c1228138403800c10142041060300000020241e446890485248104207840c20881c00103a51f503800d959004902504c4400b588107481080000c12840741c80c040c80402e0508050205d68021094060300203801010b000d80c2401a40e07a468900c100c052041c2c407021a142c3c02080e14040c00c101090002540c1165440300b41503010540c1005444a03000503c0a4207888000901c103010340490000344c80e00c0080c0005070a4000d42c0044541b95000d000d4038446559140c0080b107803088901460700900a040343e40015443c4201c1c280300503030058544443c01c1e000f0454080080d04040070820300307100c600b600071015239541c901910061256507502c55543c0d9050b0380003410164050440380655006000902410760090002d84c1d01c81c3c05c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 501251636 1250 501250386 501250417
    0x11010902060d1b3f0c030605030709020909070e0d050d0e01020d23030601170702060610180b0306040608120306010e1c080a03060b0a0f02060105030a0b0a0905030f0d091115 76
    0x10b40003180c4c018090001c042c04070441c0f51210001c0c200350150040c60484a00710f00b03507180c050b941c501240c10ba11076200d00507071203000c0d01c0009800b00c1c01600d41401900029211451994940d514180340a032a08450310105400072160342c65980d0420140700d4070070191800c1c0c03800710304e8118003140c007146c440040d41c640c3c1c01c0840018516442603031050465144081c0d458a00d05100001075140d54040e2240740c05052414402d60a031801620104125240d8161504c04203241080760318980e00054142580552034840005e040641044000c0c01d0f0802c0b844140d0703407400c14a002402d400100d26000e4010ba11008030710b0b80b50381d00100071200b6140c002d902155919803e44048000744296000440c0300007010921005081c1c0c440840401e65a0a408448081e40c03103100301951210394020051006010600150b4280d1490b00a00a400d203c0e00440e8108000f01e119090b00342c0003c1304c40000c050740d40f40e140c0c0c00e00074a044103514140c3d0603a14078103043c80600041c03049114800440c002d840 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 501252886 1250 501251636 501251717
    0x71401020702060307180905040b070e0a050a0b09122404020612040305030a06091a0613150809060105060a051911030309070905060307080a0311010902060d1b 70
    0x1400e404a84405900070300c1113a4900d0038900c05003104000d060750040c0142c2090020030388903510302c0350780d02443c0c10100420690b03a548104450040d000040f09400092031203001801e40ca444142001400e602e420150301c50858200380580c8983e1820101039680c481003035640440d0030f84034480c50031841c001003445255114008074a0358401e54130685810344416040006050b401006540202e582d880180400369a40c89e000b8203492803d0703680e418000751042c0d40110b07807a20300010241850f44000035825940d54030084990556000108000710308034004010080b141405000c0c0946002c40d080d50504c10000d01c0105140075203040c8000b55a855815401c540340140360120340340103084c04484d6280380c10181152201d903107124516a0341d04040202c1c0342d80c9400703e001c4007520b13082c1c1c00400c43e0b420180c038116000c4d0351808029140e5585c1d4004400540c50f0703540240000003103d6008590b5030301c96442c47d451480c40360858401c01081190743c4407060400c40080b0a4a042c01284a6542 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 501254136 1250 501252886 501252923
    0x120c0909012105100f051e0c0c1e0109030906031406060f07061a271b0d061d06060703090b0903070b1801020c010f050a14091c0c06110307 61
    0x2140b2051000d4018464a215200203d01344d400100d006a0b03240414005500d501485007400801f100e260814005103100080c0400910b02c050305c00c1c212100c00715500720510085a5540050307800c0340c1200e80c0d4491541c4818540c00ca46030780000c4c6075524082020300b46241003030040d60700c0500b03058882d03000060b5011070a001103040d6035640703410003020407008214a030034055101402c0e00f014059001981c2002034581a09500350310380c0c0081d25011142d42e40c10b402d5240301c8c00c186d0000c40c1c03d103c052005412204c1e1610440c4007402950542e021410101c0000001c040d500600d000c1c4115410003400c0d000a80c4504d04808071404000322545a111000002e824011150000e0340950030100e01c5c0d0240c138000903540440a00c0a07000d4031003603034038940115481d8071401c90b06404141c0810403620454841c2030200240d080210400d810f03c4451800a141e1035102d0b800580c1c4ca4102c0f0781c000c0700303011000d50482d00401180c1880c035130b00409402c0e00c90f01ca016007803001d00004840d4590f440341 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 501255386 1250 501254136 501254189
    0xa0e01031a1008040b0a02160b070c0f050606031002030105061603120903090504050c0a0c0b10120b040302010b010f0207030602180a0f06030f020304030c061d12120c090901 76
    0x15800090401e40c2c40340c20707420020b0504038111010384400d4030f03003400303c0e005614a100f01c0303d1010021058410510607501d484085080c003034450340030444420b0039040400c40c81c0051404207171085002c1d0044d42440d1003054500030b4803000c2200154410130041189035504000c8800b0071015240d440020320303560400391000a012200508070b6401c0807031520406900c1359581d4113950003200c08201c41c0d1141500780c40ca50081128050200f082c068807000840c0d0b134032540c2030384620388011000b29940c5500040c040a00c41c00c1040701c0140c411000d01c0101074080c041d980e1608000c1c41e050981c0200448002e41e102d80070310028150319400104440340d51000304450350740450141c075000710350b603031488105914203051045c100001e240070301c0364004103001d000302e03400ba6400d079540c83e2401c00940c9408000300000320b60411a11840d0340d00d551104e106001003084810841d038400c0e16142d80075001e40384040001c000081d845c1042017100465510b40c680141502c00b964000c60000d81c074801030511 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 501256636 1250 501255386 501255431
    0x20105150d0f06021305040f050610050706060f060e01110f0303161202070302032d04050405130203010e0601080f0c0907181d100605160602090f18061002030a0e0103 73
    0xb0303d03000203450010681020340140807102d05803410800c0209140390101124820f440c241da21500303a0f461120040d100da00503140c110302071070740050380759a5244151400140799107c0c0c008100f00900f213200c03541e0807000c6940f082841c034000d041c0303280585020f50340382d03c4024040c070142050036600d1145148500d001c1601c40324588001c640d03508450401940c0d0f130f0007600c42c02080f14002c0940f501c4241300d103a540070310140c4044169003000d040000300f102808008081040c02c0e40e9114a0101580d424043c1940300c07002140a00b0455050050b940d092600141c0d007903655500400f00620f5545500100551000141c40c0c4064244600031146c0c6400003203901295186003460103420000c44290580c0c2d00410066071304483c05551440c3c190346502a80c2003e10f0800075001c44a004141c0310b4008000c10203004280d540040000f1000608030703044400e212203d490301004100e540c0c10482c0560440c5400d40c0019810f0040b080e00042240044110352810140c40e9411001c0b11760440d0308408 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 501257886 1250 501256636 501256643
    0xf060a0302130e12031f06210209220e0a0b040803180a030f1701030317060a050a081b010206090304031709040c02031810020a0305130f170d020105150d0f 68
    0x304ea403000d030000b9624542082d41c02d40200c0d0045415803088401c4d04034644119041601d4a034169071060328012a09401d40c841d20082e04d400700134140c5141c2d150341c400b00c844415400100280321030604000219220403005c010349134810f040e410302083e1030a94041d03101c0d0340300c41c41035660703690540081e10600d0300a000e485c00e446401444000c00d134100324203413032049491341c0380a40300840081101d241d40b028403026000c100034154490030044107614241c1e1180010305110043e40d581d0340400c40e004401d41c00501d26030091001044810303100d12002401c02002d10080c002820640007482d1a481140b00044c0346465030055080c42400b09410b0341c001100041003003105600b6200e01944a6015010250b1101841015405240b6000d0094404512a0307401003081010321f079025901913000c1e0f00411703094005020001440c04054080030040d00c900e100c0001e2020f0b0000ca540c1c54822118440419641007404008840c00851b82d0300d500d04030110f0783c998504c0313506d00f07146840c80035440018 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 501258992 1106 501257886 501257893
    0x6070e09060105070f0303110c0f0f01060e0f1816290301090b1315030b100e04060c0e130c0e040e070905040312051e0f060a0302130e 59
    0x7545c54911900713001550010b0b501418045410540c01c0000703907071200c0000c03003d54074213100306041050390800a102903410020f1022200f44010014034a40302c126000a5190f807045000f40d00c035410070ba059600101c42000100c41c01c1c41240120050509003030221b1100310602c001c2011807042c040c55031400d5900349004200a41030325240d0307640c40410b0003040c4503050041c2c841d8070380c003140b8590f0100a0a01d549000300310340c0b000412003030040083c403008000055a02030700a6005a01c0900012100e80040e401e4800c07104841d2019000700321403841e681d40900591141016030519103c540c041180c600400c801ea41300d05542d40c0031900310900c00c11400c01660403c07070300144603050800301600b402d214401181c2c4120364018407495407801c640c5038070426100d107581092450101114034a045030128195640502c03000780514076840101c2c042e13034030f0b41d4415504d45070a80180e = true := by decide +kernel

theorem cover : BRFrame.Cov 501079136 501258992 := by
  have h0 := BRFrame.cov_init 501079136
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501079136 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 501079136 ≤ n) (h2 : n < 501258992) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
