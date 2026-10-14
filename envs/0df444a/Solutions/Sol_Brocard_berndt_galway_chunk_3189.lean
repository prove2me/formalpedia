-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3189
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:56:09.49783+00:00
-- url     : https://prove2.me/submissions/c6b3263b-88c4-43eb-ad8a-c3181bb68d72

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 573381294 ≤ n < 573561151 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 573382544 1250 573381294 573381313
    0x1906020706050c0d0f1206031505010f05130c0c0221070504020c0705060310050a0303050a030b1c030309020f150903060a0218120106080601060c0b060907140702150c 73
    0xd151880540011040207024009420200f100040e40182d5030401d007844081c01001c0c1004942c200c220543d81320703801e800e18030300100b4000081151700070b41a0f0044148000e80c0c82c1c81c64000c542c0d40070b110b90760b00a019550a00702c0042641d101d807104000034689035548104503000074000c07481030f81c0256a4109280628082454100030f00c0c002007000b5182581080152100240c480f44c075031103418001c0b400080080d541d07104104114000c0c0070000d03c240412903c82c2070090141d0050f505410101e441e04840a0765843d1080002000381c0b1100d42c108814100c81d50b044001d01160324040342c00070300c410706038425a40e54072010b503040c141500c2019281c1170744408242ca4010040c049041da180704109901c1019100010011030080a6551116585602c2107403801454a980115030a01511001058407a408080d400c0c44c14040d83d613000781c0342c88000030017008410585410010481c241d51102c0c01d0b41c0f440016001160009103030541209001800560341c0c0d211814100543c1c1199001c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 573383794 1250 573382544 573382547
    0x715050a02041401020c0108150612091507050414150c06181b1005130906060f03230f06060c030c0a0506070f09030303091e0f051c0e09151906 63
    0x40400f040900c020000007511000203040707100c000d8141c00c500d0349000003c90190b1203144c1200c9a1a4412084082510b0304a400d6a2102149010316408000c9100819078080c071803000c0e5015203c401107541d01340400481003106445481c44c81007190501070100c2503240009001d80d512a070940141c8007109400c4045060501000310450101440170500344620ba4030f0300c4041d50311820380c0e42002c41e966021650380b1460000c080c2c2c4110044d60402c440880c0d650303442120b002d10144a034805002e01500c130280340141041900300c0442c2612300d040040ea001c185804940d0b040741019099524100038010043c0c1145e1104d07030680001ea0000c1c084004018080040c951701000a02d81020300045401c1c3c000c018046034032010341055186e511100a1010090904007009a0014980046030a40c40d285078001ea0400041d15980540c800405005115440f071010b010385c0ea07543d280c8010140005c00002c410050840c90400014403216100d98682111030086001450080032105242690 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 573385044 1250 573383794 573383819
    0x18280f050f1e06010e040204270b0c04061209060608010c0224060315040c05091509010605090105073810060512070302210c07060e010513080715050a0204 68
    0x30240c10407944240030101000c0c081010f5065071104043c0309403544842c000100030f4070307038401c00050ba900c0b80b2043e6070000d0b0303c05000c0f00805116000300c0c1c1450341c035440c00342c2c00c6024074426400031400104150807401c280790311200d07400744103e800080d459180d011050846000500307500142e4086200d40380400c030000307074455402c0341d00c1d183c0b2440751405e80701181c0c94480c0b51301c10076a0106003c011070100030080020901803c0013a001c510146402c0507085090440c2014035401401c001001003041d910400c115154400c041c2c64641c03038031a2079902d0134417400d00d5081007012003034100c001e0342607148101c0d000c40000303c0c40801c9200740d0600103046140d02d5456372040d400c6c02010010280012403000d0b54551041c1c482c03c0051702e440706950041851320400a100c211a40b9410030041c4c610304481c0644401d40c0929010801d4410700c0781c00d02d00304c0e081550144040d15012f515040060380b4030004000003441032030304006905102401509403802070f10b5107800c45070085400e0152184290 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 573386294 1250 573385044 573385063
    0x12180a080c0607020603070509060d0f0b0f1011010207080a030603031d130b03100e100b0d0c090c051303060207030e010c030905060f121e18280f050f 66
    0x340a44090024000010014400c88000a01030840400021885400790064440a103009000140c0d102d059042d01c20040035080750880b46030f481c1003520719207802d02c8070305003000d1100074086144a196a00f0b080c0d80400741a800044250340800c542000107040d500946580e00c100d0310302185060840c0350280850081012610500d41007104084c0307a40d80d503004214140c05032180006280b5056804241010035000d0311505203030800d101190300c80d0700015003000e078000c40d0a080000607045820003d01640006014101e59001c03a01408003641c15801102c4001086c1082464a1007403404861002c0e0254015903544c1ea012440c08141500b010901002031400d00c1c0c83d0800303002a07500a4403020903801140d004100c08200b0304211403442c4102c50580810ba0052a1245003c0a0821608010490701d89007183c802c000700b40c1d11009101c80b104000c5604000d070a001080348240b8600c080900340f4184503443c0c011800f0040340c0c07551040c824040c0910050300b81c620200007140c0c501142d04 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 573387544 1250 573386294 573386309
    0x10801080a03080c071a1e091b040b0a0305070f2603070f080409090b15090103020d1202011b050d1a01050f0d060b0c0708011802130e12180a 62
    0x564200d0001c1d82c03103d41960300c00c00a944282d22209941011030a004141d20b142403d0780402c0709204088201c000c848501598180340445603a0b124071005444100345000c0410147c1544440b09140c0303000d8000149940e0003400c40740d43c55a59441d4103180c0f141da03030702800004828100a1001c5072070b09a445003643c0e6640380c41c00e00076604d401103039600c0c8105017015016035504141d8804204822045500404900401b44101d61090408444005003500c1c0101c001560320300411040c108003c0942c1240c0e0002c01c0c1c1501b0b241c2c643c072440c418074041c6541c04115540c401c020744200304456000400722360b03d80c3c2d076183c8841154003400216141080442a038510034031902d82142c3e88442160b070483c0720740f01011b445032402003107100504096003012032034410204c1c0603602c0e90350018811003140c600b00000c0c410f4055940318203d500b804100069045100e00f403607541c1d4030075160010b034401582841116141c61581850721529003012a031041c00c080c45000101441c80e11146401c05001305 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 573388794 1250 573387544 573387553
    0xb0907170a0c080402010e0a08010f020913050403080601180504060605070506100e06130b0607030e01081003020607120c0b04030302130b0f19090f18181502030c0f0c0a0201080108 79
    0x1401c60240103c140200001e0402010100100c600d842d00b4500703200400400c030092201984c0c1c150142c0203900301300c030300d54050038555190821524450240c1c0d40940d4060300c80c0885501c0d080300440e500c141101d96540301c400a100c00040c0382d1160b02c038010040403e507541c02e485285a00d401401c140000d440c0040042c06140c09020b424400c05501d504400102d608111251030080c4000162050700603c60f031201c0f0120b10300091640014144142c44000d81c0e881c1c085070f940b108028030104d080d01010350041c41c148a00c42c0021600b184a0181201c0d904107a150b05d0320540d1004d0900404813412400640c0100345142e0380b0701000d4500e4042d2844050880c107004254070204200d01410b14041c02c801c81240229902d64060382120016203000002d60a1458a4099000b480c548409281c00e603a85003401540030500c08450b1014010f600010184840120304901e00182d00042c0485801050070080081400301290081020300e84100180c1a0240180005441c0040580c41080d25410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 573390044 1250 573388794 573388811
    0xe0105090a0203040314160c24021c0c0c0e070c1b080c131407020307052a04151206090c1d0403080705130305060f0601020313050d060b0907170a 64
    0x2c1001c0c119150200d5010841d8403081c10401400c2c1c0907a07e01c001500383c0c00006000b181c010488000c2121101818001e1900d80c4000300c0c0c00c0307943c1c1c03a013020140ca004051850003803040744555050034406000d200c0d56948a525000c602541500654070040031030000c1040004004c1c4182c9030202444480c64442c030131500d04100243c5070f41c0144c041a11509014600d0990290b184e0711000040b00e003407500d4a00c80c506000d01179031703a0340300039400d46440c4100800315003a400190a00728640703010b00e41d94800219200c0601020b02501c1c640084000080000030419015100c07088030710601600c0301086103406401c0040c144121500030b80312011240d4030345040801000c0107180c100c0e5051402003020b82d02c10300c0480340b500079a00e882406502031040001444800901c8074001d07020314074810240d07114800166900e00c62a40c052821a0301030008011a113400000081400d014410200c1e030001898005498404211070207004a240203080c00341e41203a680781ca0303511100381e00c0208034a94 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 573391294 1250 573390044 573390047
    0x907060206191503050601030b04060e0c0f09100803030c0a080606040f05211c030b0f01120b0d0f08031b0304050c0402160506090706020d1403131b0e0105090a02030403 74
    0x40b01c1c0348611180c80d03140c04440c0d08212080300588000c6410a0a464007541c492600e14584002901c0030343c0c0660406440c030b0500758000c109540325041c02001c00403040c185030240001d1503c01400700113480011030307001039800010300c01140300d1340075207545c0c568543c83c41c40d014025036030107480d150042c0e0013844140200d65101d25800c0560704c00315241d071303001c644c0c180701143c0d10500100500d9031409401c0c4455101c080c030344ca0981c41080d95442c1804031842020a21940c0c0821102c80c9000803c3d45d442100c44a5050388002d0b520800035104109000203600c0d802c00796202150308442c1a10b0001c02c020329801c1e0780614840303191800b4802455820152280340c0c5c0c1e030010080f03261040c0e030300140e13030211958022112116191300900f0746506140c000b0031513803108141d11a03031002d4002c41c1320500c2c1c01032203140e0754803554003031809642c00c41d202c103454241980300303c0304111510988034441d03141c00d50712182001c0c020241e45121402540c10070f01805041000580f11805490050081c080082d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 573392544 1250 573391294 573391321
    0xc090f0105130213120f060204060c020f0301020705061519150e191a0909131101030e1902010c0812070909060e04022e050d110a0206011e031203050907060206 70
    0x851801540c0410b603002806d2010b800f10296030010b0100c0d01c0000d0008813160855140b0308458004c6401c003000119205c2030600380c1c41a040f0040c4680c00c0a0300048400d20405003031090200060700742015165051140302c86111550000c8000880000f0815505070707002c5144611843c058900f00d01d8101c0003011401412642c0c02445091501c1300d0040c081004034409450b02500001e0010000c1e046c03c00e00092421141c100541c0e01015202e5005040d5010340141d01e40100d041c0c006014078446400c01d5008107024003000c030304002c0d80040318404030303da62000d0100300e1303c0ca1007a01c0c40c90428603400743c648080d50340701d03400080c00c041c01000720f140c4011420364450340640c0c002a100b000e40e0b8001c0c0400c0c4200140140f10246001c5040300d240d03010b030240c040c0010448042000c08480d9240c007406004080200005074040001480640a10400f10300841c0449480d60003554480d928615142910341400c4002541d074801c0007007103d41041460010102da002030f10f90390034144598542c9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 573393794 1250 573392544 573392549
    0x506030f070e1b0414042004051e03010207030923060a051c0e010207051207022b0204180213090b0114030708010f150b03101203020c090f0105130213 66
    0x21054403100051425010142000726040001d204070303504e68448810322124025081403030300032860202c50302e000b036036002816010040f0002d5200d05040c40e0100300102c81d843c0241d1105a0820b0090251994070240041c00303089129031502001d444c108a01e1200b00c4001202400c00d044500f141c02c0d196498110485211840e00e14025540d5035020494040d0400d04401c44101145812100801c00d40f041d03002c3c004441c800c0068401c0e00c143c101a500c260700545801a500c0040f0f000124444a5040500d00503010110b11070001e0703020302c1c0c002800321071002e4400007101250328440011860a20340c41c850071a2429410005820351313440d0714030742c0001405100251100d1000603607155404101401c001c060540083c040e0a524508040c068810300a02c802d80002c082c00110b0455080d00907240b20303441d50f003030102c44245010f901c040760156241c0d0650a500521320784603159112511b2141c45100c11a1443c0019454201031200c00403c3c0f103c00b81a0900c14000c15152a003a0711400c000c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 573395044 1250 573393794 573393809
    0x5100e1002090d061a030a0605090705030303011404020705100e0703060c110c12070b13061812080a27081b010801030b04140f0d02010c050306090f0406021903020903010506030f07 79
    0xf075000808502d105007205c03996803654907214002181c0100440790304034610880078101941c28031603a80c03090680d030780030a01a445400704a000e00c060a4101603010f07001a501500844060082c0c404514003203d2044480c0c080036000601c0034020301c411400396000740a05447e04178503c403403040070143c41e8000d0250007842a800045c002044200c01c201c140b0241204caa00250345a107014001841203050384188000314100a5402103225840c0c1500b038200c4078050b00a10b03c000550b51000d034154031403404207050004c80291b51080b843c02c0e20151900a51030110384084604000b41c50389065403100c015100c134400001603200c96680700790010304481c1e05c4030f0511101d48a500d042143d40b2414003c03010786200300f451144612900058488003490390340c00801c0510b44840c0100c0d11480102e0b400c0d42c012444c1b10100d0b1440050b0f04981d54442d01600006081803081c5e0f0248155250600e14000025000700d10700711585000c2c480d49412400803801040040100c12200c0d4490f0110300c00d842 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 573396294 1250 573395044 573395051
    0x27170d020723040923060105040b010e010c0813180213051f080901020c0105091605040c1403060d0b07020102040e0a0504031709070503070605030f0a05010501021f0905100e1002090d06 81
    0x3082205010706117003140560907038500015460500c0035501c907800d1140c0c500c641e080400281d52540200c0c192980f070101a034900d130081550b40c80b004190b600c040b6101145842ca880c00042510000003180d43c444c141080260b6a04240c000c1c070f02121500760005803140d011290884540100400780c115061402e0801601c40d80e18001d40c54024020181d1180495081000b00110010301003808046480c41080ea801465260303018001100d500002442c0443c00c2c1c03515490318072030000301450f07000340700a04694802805079109000c0000503030b014800340c0e401207001d01c4032908060809900440b5810108018682034400404e03040440745c0c030101451009000c540512401c0c001c0700090000541122031441c0d80d0180105180d200300c07030002c07200380ea00000c0781c0ba01000b8014903040300c02c141d008004880c101000650b4136808201f031034a500d03946401c0c400004070f050145607448801c5110005550030300410b00c5040410034250391290398810001d1101941d03030440e0301e03070800d41c1155001 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 573397544 1250 573396294 573396311
    0x14030310080c2d03071e0305120a0203031b2a010609150302041d1f05090c1509030106080f03030403030b19030303020f0f0313030e040c27170d02072304 67
    0x74100026504128040c038000e421b251880101c10203844100d0384244210b401d08040509140c0c800d0166098000040e08200017203004946081000015011000040e5140252112a2030300301174000e1940700010391542d41680a1841c2841060010b0032050307420702c06050703411080700182040d800020b1045507203000c2a810044028481044038207014120303940c090003114885904100c0c40703480c4e800345013000300240140c0004150b28541ca60701500b07207030700440c0014134090207801014440313130599a01c100c0010030800c100f20221038002c5003806103036281400d0600400b0b8aa08160342809003506409008140d58580781205c1140d8045c40c0058841d81c00341c600130710500c229402c03068040f20200034080b0564920b000c20134518400c0c0c440c42c8a450050051205842164880601262100c0d0380f60150b41c50010001200c255000015440c0b20b484494400200d82841141c042e0340d4410710030306109607010441d00380940b00d102041083c07030300ca1101d4104540c03c0b0007800c50080d0341341c400301c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 573398794 1250 573397544 573397549
    0x604170109050a030201020d0c05160f060e030d0e0c01090b0a0c06180302030d0518281a01090507021612050f071206050c040312080414030310080c2d 66
    0x390740c4055020054482d42101030030028040c0d04070344880300b0801e1405158113001e0b070103142200d0940e64891064a00e1281d16100c0d1082480741010035202540c0b00c4034541c10450302071000b03040c4045400000505e0001d21091035141c40400b10003103051088150081c00342c28101c1c2c05560025119103403000090b861480c1c0400039101c1c150001c001e2a0401549100b01900071001c0c3c517828051800c200025601e00000c2c010840041180c0200c85d0414580c004a03900111465070049415030041d00c0750103c00d60b100400720b4842080301c080801c0040062040000034000d070354001c082c3c1d100415400d113400d0b4986840e18840d10a102c103a4041d800240b04000b42403140c10740e03001441c81541e58560f43c511001074860044001240c8042ca850b0009480c0c1640030241c0301a660086600d69000b040d6003001d98a007240a07009503410440010303500d25400e42003000310b10410009100703041c207615014034230b46440341d0803000a220fa00382c1d48075500240d0139480202d00c41505c0d1840d0003990300c140b00c007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 573400044 1250 573398794 573398801
    0xb0f25020604030305030610020a0c060507030c0b0a050117060405060606220906050310060b0906131809020f01030b010f03110c010e0106080613030503010b09011e111b06041701 78
    0x90094010401140000c241a009409148240820b952450700e040001504a84075141114010900020040e00b440b00c80c1c855005003082d240f090510749803502e607079100c80104800403201d111070f060302c03100140102e840c400f010b5000c41c04140001c0c601c80c01c05903901912010028000342c06080c3c00b05000454150f80100c0d400d042402d42a81001075403030742d0419020b8241409010b0291003000424580003c01784140400ca482000d0002e0804110204001080d441100e02105c00e13101000c0104807980007214002d850940ea0400140f0490144184000c0894007001c8506040c900761b140500399812400d0801003628a141c005031030034040000882034000c0040004840d071920071203001b1900154410b80540d6440006c5845030365440049101d80c1070b0308800100041e106100410a0b45c0e0704d40301178030500805042240a654201c036490302c0030741c8a9141080010510132400c0e40011043c8106022513588448091002c203146d8081182807150b88124905031140600c0c03006820000e60 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 573401294 1250 573400044 573400117
    0x8070602150408340c050a0f0e0f1503030408010b0a090606051210080f0c04050c033709030e0a0608071d031204120b010e01052b1e0c0b0f 61
    0x51304c61640704180e08011110702400d018180c02511841401701e0442c0d4010500c404440070340140c94507982c0c418400307500705075000d8092809114180007086c4199814070140015007182400018141d160b01d04211111b4072540c440710701c09280010611440d81e02c44200e070300102c00282d0030351141e20f039442d6641c48480c581e448000c20303019807102c44560050100e010390141c0307021a010300558491424031030140c070044e29020010308a441a1015044104421410500300000740c0701c0084050030035075060300e0f4440c00890009000351050326040c40c013420010043c040c10f1401c141b0500d08580e0141403006800c0000c032003034003082a9a0610340d01041303285a040c1c0000f070895103580c1c0d149207050701da48412030115115000c0c10004104a50b2a09007941269401858a4403401140c0030440400b040021441c0000c0c2135001c2c7c010225061116901d0000c00040550021242d10705060f01d11140540040480842c2000584008803c20060f6002c0110844185a124481818100029194a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 573402544 1250 573401294 573401377
    0x5070c0b0c010c021501080c12070b0a0503040311010b1c0809040e01051006020109020906040c02010b040914070e0c030a0e0307050604080424020d0e06090301020408070602150408 79
    0x885010070001900704070308400540e0215100c1100e51000480959000d0142c0445a4000c1d9940c1c040ca24040800410288000c13003a203e81c107803162030503e129031004400c030021850010500c0201907100003500340c0000044003c1000b10781503000905032044410402544a50100128007400000c01c229584c401e0024000c0006003d8022018040d0500311205222030f0208a000540c06006001e01d0303c4450f4024a446069900c090400c0014402d02c00c0340c20840d076130b4000c181c010f0f86540c454901c01a0203282015440380e11061aa4500f0203640c0018141e04041410b00c210f028101003925000f020a42000c80c0b00e8911000c510303d5401141d07009042442000c0c01d010030700040c0300003403082e00c0c0c1d250503003060802c2c0c800b401c0000c2c81d0b05100c80c0e401640070300d0016000d10710800084c0d100c2c0c607000340102d1a142e90107001a0a9030040e030407107900c40c0c0280ea8100810754040103102a80c00781004280e200f481e01d602c41c00c0460061206070fa0350300c0082240850f43c07800030000c040805190 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 573403794 1250 573402544 573402547
    0x306011808070509091203040b0c190c05060c18151306050c060705040b220f180f0b010c0303020a02100204080f0609060606072d05160f05060a05070c0b 67
    0x8500619540b107200344240c5004030104404a03810f1140440c05c0c441d6403034101d88041c51b40d100d0b0703038501e20526402040012010400e016008880508126400d0443c41d01d0307a0700c00741d0302801c2c10501d041c807002404114450704104150300100410040303244625604483c5d81a0030121000c0401c41486842e550151015030301401040e0907070483c0150070075101c600c0031a0207a984142c0d0645161040d8060080268810303c1182800c1405002500800d040020a44219965044400f03000c8019030003080301100012034050302042c051040031405801e480080c40040104d0001a0040464035005800c251300012842d205500030000310701004441d16046580702d035a00382194a03a007a4408082150082d400481e802c4030000410724051100103082d680b030896140c2d2a44404200918a0460800b1418900c1c00d0044040460859207014030054100d54815540101d5481c003150421280c540c4440c0c0309104c0ca40740e500944800c031001b820403d070358030800e0401e44080b41941e4080c0303031010300 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 573405044 1250 573403794 573403799
    0x10204090627060518181c030f061401080903040b0304140c010f091404140702010c02071703041503020c12040609170307081e04090b0906011106070503060118 70
    0x15540018450340c0d202c100c0090440502c0708000080d6140c07440f8080c0d000c0c2c008180075084100902c2c0343c1e07420014030780044885510f0306082c00d0a1040c0e461109503050070300c2e02d4030300484c0d8140c003400c40c900001031000c01c1028245030710f0b030414440074030748541005503407400140c0e400804c204840113440000d00c82501c0307280500d40420341c9608484604035030b0107a1441401d580d40284003960707440c0c8850710b4002c240c46c101101404004102c0d80803641c041e440d154003081080366244e569000d4901d550001c10703e08041100640342142c0e80d4020400341d40d210300c0c003070600c420100a032400d1325101c04104015070244501200a03001c2d040344c3c0b001c14020349100e05511900e0070001c004851081d20790b0100f090355104200940d01050b080d00105400403c402000100000014048050442e0f240388401302c608900c840c0130341050700908500c40c2d6401d00c1c000f80c1e260110080d036000d1801d10703020030419500900d01e604c540001c5c102c2003d00c50b000c030224803141e0043c88a8040718003040c200014196 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 573406294 1250 573405044 573405059
    0x203160e01091409060103080d0902040207110405100e1501030905150a0b0307030218041e110a141f23030105040506010309020607030e0a050406030506071722050102040906 76
    0x100c01e10460682c107240c0000c500074200210800c1d440ba05070400601a103a1854132604c180b9072044240b90f86041da1485204010703520381c4050b09505003c2d0580c010954a841d00340421640e001c0c1123901d031a0700e0782c4002c0000902050040394442038605040010043d81401a0054860540c00070700038064148824903e04107480581d2190060800071300c03a4160810034903881d80c140f40402b0303421450900c0d04200c80c01c0c4079046a60003c6c441d012aa0f0b6255a088080d07009000001c030440308901c0c5000000c0e01807500300c903824060300d00c011000001d503400100040c0d400340311810382d801c2c03800170011207038205002d400c5501c0005603080154645e0001c1d507040b82e4183c0e0017402450310951a02d4040781483d44070f88035400410360701030101031130100e031034805407800600f00039442e50182d03540e2404284c5440780d02031031001f148144010003003810186805081c0340c00d83c40d010420007501504004c1001441c0300300059581244c0440c0c0e5020385a07041c03450182c840c1e07030850408142414000a02c0d00b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 573407544 1250 573406294 573406319
    0x90402120108030d4d0a090e06060a050d0b010e031b0306130305030f1003051203090d11071202060f030f06010207091406130e0115050109090b030a0807020316 70
    0xc80300080708228205003900242c41d2184079908004201020890036506420442225102400340350000480f01703001070041030543e4801c1541c00001503d4174800c00201600c0b402c140c0d007146040303804a083c44034544000342540102c60103900130b9a02c0d0151400701d83d000302c00d404040040a0b09940001031800110714080701044082030082c840c5100003600d000c03084084a0741c640d03160341c401d4510780780c0c004510b072000c1d0054090300020a103058001b001440422040c04406040a8104c0d01e80c039148100718105505504031809000c0481070010000c54046400c0090340c082c1e580d82a186021800410214003070091182400c0c80004144082c41505040c010711450090342240d180903142d8a10f03c083e901c0e0449001c0302034a4840200d540b603c0d04621111070301c0001c0380c0c00590940311440260a4540c404102c02c180b02c010741c4248029644240040301620345a0003e12000035078001190b500c00703090340050082c010108030b21f0110f507424000800d94070014208088803940303c01d035501c2407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 573408794 1250 573407544 573407557
    0xc11090c09120102030417130b0307230a0f0809250302040b0d0b0105040b010e032b05090307090510120c050405061f12020d020a030203040c240509040212010803 71
    0x208103020310900b280b03505008030391081d81d03c080001c01c0c6800891003d5040d400c502c1240041c0014114045031505500010b0351040b1003035542c00c1192514240c00c0d000f407181440c01c10007480e4041180040b240c0c0c00042d0514645150318040b071050307880d000190700b4800c6682801090418442e52486030140c0b2115450550b8002c9404124544810040040c5550548030040840b05075500400c03a40c507245e445000c502e44181010218000420000b9041482506441070358072410940c141000201a800c82a0590710b0700b085850003c1c080c0000e035803103003588224082242c9071030004522242c03403003030400140070400101d5000c2c2d07918942248250814000c807030190786000b0005131545084400060a10341022044d44944503190741190380e21414400b6442c810703001c00c0b08088044c480c0c070040c0703c084410340d001030b1641050310384410041155440f0409501c12038484074020440640a070700c03030400508055a4583d10680454043d004841e00c2c040c44c07803180000050702e854048000c000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 573410044 1250 573408794 573408799
    0x702031c0b0f0a030b0f0702030904050c03101707030803101a0406020610120807050f0609010e0c03010c080105060313061104171c051b0609030a08010f060e010c11090c09 75
    0x6925070302c4018072080d0302e5503100142881800e1000700b01500c0c6030407031030740d00400ca0344152440c00c10f03407002090580d84159902c51601c9000410008600c800845c54030107015a0000c59841c041d0356804180d80d40041d0002414041c0700001040d14801c0408080f4010843d000d06415030030700003080c3c2e100c20380152180c0405401204000340400f40b00103401001e90711090015001c2081d903860301600394000f080c1c1116640b02e1202041d440f100304200992080750342a0010404180e800103190602d2003c400c40c5000341c0c10080050519a006600d15042d50401d0391441e40f00d50307541200c0c903420840e861002e4891841c14100c4003c0318162070090094444a079184107184822060046d522400f0501d01c0592151407004090180d01c5039000741641d01c031030002004440c00380b03200603041400a0302c5081c12076000152624680d40c200c4816801850400d0010404515101c00501400c0c181090b050420001c032100c14104118045000d005139400b6115801034900b85080d008e555005145162 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 573411294 1250 573410044 573410059
    0x601030b04140a05100e1914010b030309030606042c030424080708070302040b19020c0307120209100e0a06051905060702060f070b0f0406061a120702031c0b 69
    0x1941401c0c0043c0343c440c0240e1100041525491030903800c8000d001c01b410140060040744d40c45406d03e10f0200c0c888100c24050300503442c00945420801d421100360b514507074040d070018040e5010075980403030380a0340840192804a40f00103404800d441c25030750120190500b40d1103100094602d5030020240c015a0344402c04c40c610010003001017400d0f058192800000181101c0018810078419041242c0080b01414054101511010802001d42102102c1c803141c4000442c940f428680c108007440740520207402400c103031424840300b150594490300000c1d010305401c00104400705600b09030700340140701c088264800c0d810321000080242205219082c424170703410780f03003100002907440d0140441c0d038020461460402c0c0c503424010190400180700c941c0c03c00c1404080041500016018171502425105880768602441c00c80d0884146400046d00d82000e00c030011001c01d002e03821284840a031402102c032030f548680f0228994400c44c001810030b01d40c190001034000c4150342088416410841d1103d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 573412544 1250 573411294 573411323
    0x203091008010302090a0e1204030503070b010512060106110312240103060602030d0908070503160318030c030201120e010e030c1b010c1b1e0e0609091b040e0601030b04 74
    0x80758244400c0c00041c0d0300500344070204040d034030660711101c2c42e1164501603900c41c00d41d00509504e15042548107440c1600000380001c03c021551030030b50701401c8200e07500740001407000c2c0001c0d91403105000300020311242e9504010780c55000c0050300c400410126162003140342c10b00c683c00707016698010700c50000c6c5265803440b90640c0039010710000d481a90b4001e50070301020124480150030f0020050703518030010131424000c1070052004251600782080791110310318161034001c2c05840c14922241840460300d209000103100c502440c13003100e8091810041070b00e02102140c0041241c025080e082d07600c0d0030000d46282c48040054003c032504c10341500c0c0080340f402442d00043c41204801800120903d41d0354000502c02d41c04203100341c441034850703a40642c036980348041c402803200301c0f040e00060245040000c5c00c0b020f040309030311080aa541d05001e00b0150000c55403104403546182d61b141142c80c0c60300d500e4075240d10036140e600d410012140c041d6580c0c10001c0c0750240907201a92080c4034520034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 573413794 1250 573412544 573412547
    0x605060301030807150b0108360304060216030201141b0a03081915060804030504091130010e13020d0803100f06090506032203030b010905031f0c0302160302030910 72
    0x5070b446e9064184c40d0b0310703000e6444401d00100500043ca070307030494220031008500c41c81038075011407800072075160007941e41d01e00300740010345801c03c40407030001d10b41c5050009000503640502014002d03c0035000d10b9442e4198035000100d032401c00808100c03a44641c8400307105040c0d01c0303070200d4003454801c540d2404c1c00c5c250018900990742410314400c000b81c5220401c0103054840c403800384e40640a450003506040c6ca490000c02501c141d07070040548060003040c00c261024030007111402e000920f902aa034003a498244412040d081441045103004100340003840d40c3d0508048129602c4e8005c0c0300f80c45611091a0810700c6400035525000100c48421010030049001c104690680f000ca0f140c03194843e00e40700070407003568001003600041c2880b50103c00759200200c0084002107102c0d442c0400c22891030000100400d2050384058403950040c038160b000403041818040d1060072146020445803410fa506801900c107101c0b481280b00ca030039103050103250740031010b000c1c03000084800103441c2281540 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 573415044 1250 573413794 573413801
    0x1090b0618040b06011e030c0905011e0e030c041404060605060913020c10051801110a1209020d050316060f0203040b060607030c0507060f021603050d05030406060506030103080715 79
    0x14560752004000c80d010602c00000190302c10b0701450f1402c0c082c581c01c0203501e0711105800307824002c6a10f544003010b4054004903c0c001411080c80d01443c17002031210240041182d141005081c00101c94910380580c40903c00340c00400e10240090240f048000200c018400301141e00b07031407040c90b07c403001c41c4900c0c125044801c42e00c0001e20385044180d04241d0b4500030350041d40700980c00d20640414805c1905540580d42c401c0903100c0b003d0202031800b140c16800d5a107400080954000f04000704810305420080812140d014044c000503004081d201013411306a40c070102815500c0041810f201d80c0041d028580c980500c45d070010b101c0d035818500e036682a8081a5401069040586c0021b501c03420010098848240240383c401128001915000d08000480c3c000307000280300080e0380c888860701003100e82d004000041d48075000d80d242d038413241d4803580310a14000030000008003040030300109030061000340c84010700459880d45c1d64900302c10160b110540c1155905240a01c0c038000b180e0302d10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 573416294 1250 573415044 573415069
    0x90203282307110a080909070e091305031308010c1b0b010306020c0c0411180307030203190314031e060102060f01180204090504050c090f090304290a0201090b06 71
    0x40c8000034400d0719482500c50007800401c80003c00c442c0241076100c2c21000c00c482182140100c0f03443e0356170541d49040c040c4202c1c00901c004180004403100c1d01403904c0310071b0140e030302c980140054403040c023840c6803243c258462040c040300c04035080030000ca43e00d00198015180208113890b4000700175034005030503184046a107406071a00b541e03d001040400e249400501d50b0301600c0d02a550300481c040300003800c0b03074103500c42c0b416062004545c6041e45000c2c0e142010b00300004400500780e5030305e0340d40045e507110491a0006540402908050100f500075001c2400c101004150b050b00d91420206540e0500f0104901100700c0f0090b0003ca40d00c2d50010840c0c0380101414480380c0354507030a105200c4184c480300d00184078440d5013007000240d50080c500c19507020f00e11402c040c22080d00c09204121010348054042c032201e1800e04280104440c2c0041100d040b542c02e40da90040a8001c0e03611b5595040c080d082400c0295400113816603015410b600189a8030f02c140d62600440e12040c00780000c000b0b0b40c4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 573417544 1250 573416294 573416321
    0x7020916270909060f020c0601030b1e0115091203050a080a0e0c0f030c0411030a0c0f02030d051f06080a0c0201060501052508041205060705031009090c09020328 71
    0x2441c051140318881e030048a0980c0c01628080384a8130080d071a80c0c201c0c0e000507901c0c0b04581010700188208095203840907003007000070408098040a103080c8000e01c0c24184290049401d007100100203082c003c215140080c10300d005840c114036081d040c050802d40c8540903c0c1c2c001100e03200010881051407140ca0141c0b501e20740100f6040306e1113424041c424540081903549889080341000507944d444c0100c2031811902c190781601c9062942c83c65041d2039070004414280300b0060f00141e466503000081c0c502900d0b00c400085801d4a580c2400e080e041d481111895904030341000101e5400e81114816009010300343c0c3c100030000c2c030b0707010880c00c039209401094001f950812165002c000c0701180c1e6900e10000d90070381140b81755a6600c0803810351250b448000100304885020044c01024001c00e9400031543c14442e1035454100800d9904843c44d004251351941d44403a61130034400e00001620180580c22001c5540742814008108000140c41203200e680309000d032080e0204115018100c407d0545 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 573418794 1250 573417544 573417617
    0xb0c03010e0c09191502120306060f070c03050a08120f0403020c1005040b03070207170d0c060203040302100e06060a050a030213020307020f03180a0509130b0c07020916 74
    0x2003100b81c10075948001803080d404001d5248207000d1524040071100140305044410b504e83c000072078042d08207480074500820b170344400d1040141e81d8881030b00322851382c406076400e542c0c0d4602510707109040035401e400c05025442510541c0d410003100d50000e1001c07070840400c4500990300c0d88000320108004440040040e0002580c4103070303038100340c4a00f442886203814030b1400d0584039562906031360030480d818001680304041c100b045104404d80c42d400c91420303c0203130201c8840914060300b44105418010419503001000030207141c400d00a070004080c680800f4442e045070070b4400340c1e41d03610548006110b460240310000740351410000301c90842e5030150440c5141e450418911000f5000200300c4070540c090f54112450209041c0000e0015803100394101e10283e0281701404050041074110500540d0350400784208807049020800e00180c0c450810040c903a9481d00041060041e200b0007900520500e0522502d00d00080038081e00703220741d50320600716820300324200514182608441c1c2c2080c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 573420044 1250 573418794 573418801
    0xe130b01020a060c1b380c0a03020d02120a06090c080a0905070e09460201031113080606010206100608060a050904060516050f0412020a0906080a0b0c03010e 69
    0x12a4018812960250400c4166440c014070f401415181000c0c044071000040e84101e1180091900f500211b08080203030640b00481c203014505041070080d01503500c7d1100030601e0b03920f003442030301195030030310203582d095480703940b104015805400195550a805070900201043e001050b104400c0c0340342a6546144807a2681d24131130b0020460144242d4440c042d4000100d1005122070440d40100d03055402013140764952000075600d400010311080b00008551013800b08113415046102801f41c240c01174044c0140c80f8401607004144500c82c01c62215008039105442441d003c2581044a0007801518815540c000049881d544200c40f40c803010f0f0180e4500380211482850456840f0601900c1c482109072200005010080300301d03411143d40d621501080001c0880400440d4804403070304090b1b00b40b4008503280d103090701a6000341001a101403081c0011b41d65982c01320b400a28200c101002074540352424151075025509090f5110002c0c5000302e10000d048a080741c0c1211100d0002000c245c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 573421294 1250 573420044 573420053
    0xf061203140a1b020a030204050f1f0b030703050a060f08030a03050c130e09031c0e0c1503181e0105010e071701120212070f080d051305090717070e130b01020a 70
    0x210185001c1c0d812240e41c40006c00161142d04c00c0500646006051890602c0d010186031186042218100c04180c50360750100a00b2a00100782c981081007420049a182e40b808005002446581d01041624044c900f001410841c04001002201740c0c0da0340c240003c0d50b4070842c03003025114840d11511082050042081416081401342e038109c65141c064070b250140301040390214205520150b81e00d10b580d030004100b0200c041080b004810700c142d6682d0306164201c000680503000007048881082c240c1c040900e103140c018840180601141d0020440360503030400b10074000c003030074010180c0e40b0301070740c010540d220f020354a0991740101181e50048540e003041c95406011013009805c9810403102c0c40b208506060078010000035110b40910003524a1078080b9441c90f140e80802e0711002e0080800010203990078000b60141a2a0103030745104040d2100541104d03503050321a400000001140c0034041d840341e21181ca031608010850340030403080e10040c034013000c03100001d2225015a01050340b200014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 573422544 1250 573421294 573421337
    0xa0501050714060a020d050106080f160c081b0706050c0a021009050d06150b1602040509030903030307030f0510060c12200c03060c03070f11010f061203140a 69
    0x2280b00d01140c0901c0d00d140002d0a15148081c0c0740382480f503402144540403200d0380c0c41041d004064520b00040a424031500740d2030b4400d00903200300721111440101c03409083c025801840501e902c0b2442e81e45c0e8501000d1030803802e5440f0482c0b841c03240140c3ca40040c60f18440e6050703442071013520300030b001c450156600b08850f0301c6082e0008006d00c02c0c24100020207a03140344800c50120b02640022800c04209501040d004500d604050701040c018400c00745046007110345400030b268182c50008030380d00e9060a25286000d4044a268103100c00402c000c42154550065011900b0110b07041c0401c0c0c4a50707400b402e095545c0d004407000502003d42050101c0e0400e02c580c010070b400d50910005840154100d0715852080e104401c42075484501e5a0302c240c28100412a400f0303004045a5056082c000d00013005e03507044600342000c0040705070300300098101c00c0d808494100071134002001035554582005030001d2002c2c4060703000c20311000c0c040c6c0d401e528500803199160000c0ea60100000128121040b40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 573423794 1250 573422544 573422557
    0xf0504051e0c090c070515010b1e0702100f030605090c0f160204060803090a1a121504050f16020105100902160501050717090a020a060e0f0d0c170304050a050105 71
    0xc03440707101d0b107074105610f031004454021080c19010f2582c0300c0080c2041da01c1c06003124040c50101103508010899421180c050703075a504030404c2d81084d1110107106211043c0181c0202035070080701080220640d83d00894000e00440c9151400e014050b500c004201c5428011204184988400c0054510066500c40240407003e64400b40b0f1007103010075001700b0b088403400d81140d0850303400040c81e21610300c0c060104000505405111841941c03c11030720180c60b00030700d40c0109448a02c01c1c040740240c465a204030700e4410000d0010012441e0036254001c484400390b404003200220401000d042c2441030040602c500400455903400c1481c00f80c413140250b10a4800b02032003030741c0d90140d00c00954280036070b500401860b994a41750241d10440e00f890000060f04160707260307115085010050b1034505941307003200c0050820038625055800803403445034030f1403011a40030b210240100100a0703640d00410650750f0042f42d8000740a640300c0803a0303407440b0318050203502207149074080003e58400c0000b400c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 573425044 1250 573423794 573423853
    0x5091b01051b1914010e0a170f04180f0e0105040b010611072d050307030c0501120908070c03050f0f190f0b01060806040b010314041401021605010b03010f050405 71
    0x4005510185441c110f074141c020071a411008000c00c0300c40910240100c012484150f000381080c0c0301c507980c440710071440030030381c91014141c003140f5140c610703001ca0161801499506038503e803111891042c2c10003000030b07203030301c4952034a00310340300d40131810502c90a84600e5200c0c850742001e0342000019210345e001c5040b4880c00f4490b94202044102da441b52040303410301180340d41c409000e108807d12508140030b80115020358040401007011a400d407075154200c5000703081c00d5600244511281c030180c2000031010b800100006524410840304000c040c5c100da0140341900d410700403950301d1503100c90490030b400040d64011503404d4005491180203403850340c4100d0155513508425590220145026030021010403244010010035092074000c034440300c00c0918040103068090710076206948009000a0005048440d07100c1b90000c00358101c500d07030380c1c00c9070030071801e8849450f116020b03010710b01440740a542040c0016a04c0c11132802907600070b59200000d44046e410b0300c58201824507244c00c0140 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 573426294 1250 573425044 573425053
    0xc14130504170a0c0b0f04050303011401020106050a23040501080a030e030a0c15080f04120e121b0a0801050601050712020c042c21070201050f040905091b01051b 71
    0x802d10006008025480d15521212103818844c20440542c3d0401840c540000708900200310001c1c1d008001c0b40e05441c00e86100781200c08407000101d004000036044250072916160011402c24109070004810071501d070180b0090294400622099800a200d1003000f81d102046250000c1d000780e52000001c0d4000e02141c031201440d032074280749000240d0080d650f040c1a400340a10099001c0c8407a903000400340c4202c01e882c14280c2d1820110320100c034800c4100610b034040644a5580c3c03489043c03008208404440f10444251005404d0821040328580f04400c1000005019001801458441c42d816100c244c01c2201c43e4450801c50b00c1e03945081e00c2180980c1d020034046d95118490004020740d040301c400e400c610429003a551140e8902e04d070901c0c6500c11895060020303019440307614204100c128294030f40f00c2070300c010b882900035800383c200c03450f01c0402c0c003180c80c6e000e980c45584511040000c4944141200c0580c644061600c1515400504200680245031290f03003403c51141c0741101c210b5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 573427544 1250 573426294 573426323
    0x715031a30010212040c060f080907060c1407140a05010306030206040b09011106040302060a0b1e01120905121809072309120109060b040c020a06360c14130504 70
    0x4c0804100403181103840600a200c00c1c03180c00d5120902c80310380055402c0c10f00d21800c1490f05980e440031144220740030002e9400521040100100841b543e110000040f030b107000b03488100b8100d2010306a500c031340c0107504072400040e1540c400d000c1c51040f03a0700500210b00c1e042c2062074480b07541d407000071490b040c013031040200790003401d00b0414244038500a6018000d1406e000ca540720503100410f41c250304c02c204404035948001d0800840203030b80042401c0a0b004244101d1010000e003489540c060f0283c002c00462801c460760541c001c194038526050400313003034030125007000700c1060107558150025044a2502d1441061000124100c0399000f810606101000001841c0d0300701c0d880340c000c1c0c90b94440901c101084818010301e151000e044a041c000303060703260002035850f1207000e4003520341e03070300c0b1000d089000c420803000d980d200c7ca15801041081c60345400a0081590405040f0344040b10040001044a440103101c03001841c020301031944045400e8108000c0c0001820540d515a403d0045 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 573428794 1250 573427544 573427567
    0x90b09010e1201020315180f18070602010b2106010e1306090302010207030809010204050f040b040f14010314120702101e17010e0603060c0a020715031a300102 70
    0x4074007000c21410b0016a89180c0a5000c0a4910031000018081e80c0c001d8090301c0091f00d21070700c0c10b9121013071200c501211b83e42c4080c034501c03c03030800c80401041d0064450200305103a0642000030880000d0703c41085544041d0400001d541d03800d14000f28070742014005000110707a000b40301e40c100c205501d01304540d07030700c644500c4111100c11400320050303980000c004e01010b42040c1a0b940c003c11044c02181814645404a01451024001c1a1140340e4840201d84643c0d00c960001d4060502c9020070060341c4000b0101e03c14295081c0030503180260a00441980ca040010340b4160000781b01c1d0403107041c940340fa0309102d12800b9244c480c60034007036261448001d83d02843c4060b0303143c0e00306942e050100c001c0c0d0214030041600c103800c00307602c50400c181003051070384000500310f401a5440a400e42d450f900700070b08a050000316003117290103400520b4030140b110b030701da04100c0203080e1701c114000c9041d40708010400401440a0008003901d607002c40d00d0003140700e42500d40085403103c0005450200640305c0c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 573430044 1250 573428794 573428809
    0x1302121606030e010b1806041104080a1208090316080a2d120e0307300305060109060c030f050d18060903110d0e0603060f06030f01030b060a0303090b09010e 69
    0x2103840081d0f6100d440d0080c051003401800307401d41c400c1d0f841008003000206124404c4400030702c0c1d90f020300e494a40c0e00802e01e000300200d600070048402902e07495000c5140c003088080c803900c41c0c02c001400100116580040c08022955901e84214984034041035a585508d05904401804024846064010040c002c0d0680300303030000d25084683c1d410f04032581d54001e40503845401400a903a8501b08041601c13030800411a041142c01c00010081840031030311380c02c1c402449182000072001d00e801e4010100e6010b822060040600b6228294504c0c0c8981c0b00700d542492a0704060002900d03904203818446c0200020401e448088002041c40d03000c0c07a603268101c2d000c10310b080391030650340d161910034141d110200c950444001805001035000e8828014070303801d940f806462140c18000042002c5680710001b400300301c04058422078881c45d007404c014400d21424442038807540680c0000615504c0c01d07031482010faa6040d164511040d05140382b114041d0040b81034981400405500940c1d10380e103585 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 573431294 1250 573430044 573430049
    0xc030509061b060a111e040f03151b0e01180f0305031b0d080103060f060e07081006020708030f0d0b150c1606050d0c020106030b100609050913021216 66
    0x7142d64111040082146180c180b009294020b4546407000f44135041005200710765881680b8540c4180d0319480650354a003910641e1701c20034071155070701000010403004000100ca100144d0504114044c2c85099044010110109150000d610315944040541c010303d5040303120805e0000740d500e030940b1510b0994010031a904103407565400480c0b5050001d640d00b000308850107032000941415000588041c02c20030b03040c000203016030b448007c0152003107226403240300107100003041984642850b04000c0e01e0310038142e480c0000210010008204240006401811501884021458612031920071201a04201402c107201030725803480007065901c0141050000a842164580c2c0d09d0400305030314901003091399500c400c1518104204681c503004025280103680075000490142c00070380040340101455000144000351950602a0a6003064001c009490759620b506041c84d03101c03410450444000c682d1343c01e0f01c0042060100050801c80300400600e4001c01c01c075513100549006201003400241c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 573432544 1250 573431294 573431317
    0x50406200f01060e060d02010c02120f010510061b1203110f040b031f03050a02040c11100b0f04331d0402011b02030604030809031b01060303022b0c03050906 69
    0x40005025001c0d58000e4203412510445030906c07051015030002e410a03403500400f038442c2d640115212682d11003070201100c0c07880308100030026072034a03211401010440303018202c0011221190001208140b410344c81800d070f008442c000d201148507030100c2c0940301060300206066070511002c80803040c0ea2015001405555044903185d18110b620fa0855800d002c022400004032080d040020a80100da1080c14a40548010500881460703007030b0303480c041407051003419115028000c440880d040c0d008139081e20007254540080b42c4100c00308419251082104500c1c049200100000580c0c150010007601c12183e466900c056500d8140c6140c245005440903c249a000104800c56034840f0b6100c60500b481014808000310b1070300803e564100c01000107041c0b1426401103a5066000c0041d6411069400c040680710729071107282a002e07007a01e10044015116100c144d14801c0a020840c9800da4550002c1c82a0708440d0344044a011500c00301c16428400104410307002a102c000c014945038040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 573433794 1250 573432544 573432551
    0x90a1e05010e06030705030103030c08041502070303201c1b030302070c1d06010c020f060c07090f05010605070b040219030605091b01050a08180a0b070e040b01050406200f01 76
    0x10040094100710a00302d00ea4460740b4100200f01c480ba41000c11340b81503d8042c84c20071146030551421188610454226001d0700c2c07070004001448590014401c0706880c0320365100002501d4000359241130224458003800140c01810718400540840352400d08005403d00e00300b03000780d080500342000d14500c5034090b00040e070002508004e000500500c000249045014446c8902052507114400360016104a0411854480d0002956280940710402d040020130580d0b80300040d80c1200e1303841034148140076209040510301d18030f007501442458102c3d41d40d903d403e86407800d20ba40b101002c52005000300d80c808c0907140801840481ca018a0000c2c501c10400001c0b0344c02c0c51b0180e6840d00e080c3d5020010300c0d02000402100c41c0e60310200750750340d0302c0781410301d00b19030b0b201c44021100c40d030143e60001d0b880d4440d28031290180003e41c102607000d052642c03140e5901500711018001542c81d020103c6012420030001048401d00c0b40a0400804a542c10000e0544c1403404210707041c0500381000f004d03141e46 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 573435044 1250 573433794 573433799
    0xa03020c030606010c0308040f060c0302220b040308131203200d050906090d020409030206061c0209010b1606090521070209010b071515150c0314090a1e 67
    0x40400004014000441c0203126a14000700001c1500d8100c1d40d00600308508003004c00c040054040a200b101e41d4800014054250b01e00801070080d00140c462704c00c5051040e028490000c40741c2c0c0d01c44140c2d1501c01c01c01c0d2505082da12190140d80c4a143e100c8c030007025050001580c191042c1c00b5801c414801c3e52003007040c00000c144000c102c0b00c024038800b5560001304500995540110481c0c0702036100741c40082c2c07030745d600e04c0001c1c40d00440c0c040f001c2d4020381480c500c4030805501068291045004407800420302c00c60402105044540d8500290800c2c40c2c000140200307003c1d500504186140c140c3c1c42d080624503075885230240e80805408503216480408031100c0d00c8490082c0ba4000004400708900f45806c40e00051501c3c0410b00c06c59151580c0001c0010600615002c8944852000074041c0080e491801c41039501c00b0b00c6215070880110389203599280c09104a5440d54400d800d45e0300c0001700c034030000c0015070a41c0001c0f2241e40c4944000c500261707420700c0d40a40b00c540781094000030702c0b03e403 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 573436294 1250 573435044 573435047
    0x105010b0403031436060d0207061803020a08072301050114040902060f0d021b03090f09041505061c1a090106030818040f050414010c05040503210403140a03 69
    0x1041e8840c1c4d40605000740030300c51545035203018070401c05d99503140210301100100003140c202c2c120300c030703000d6000600040c10a0380004241c00420031a03104e0301007001411a6198204840d107016100200182c00c170030030400101d02d40c480588017003070040c82c58882070075040e410450300a1011414034210307510354004014400c002284101c1e03944003940c081c0030710841580000c12610610b80c86203113101e00400c1c0b40104070748690544175465881903180c0c2e10324100b80742855494114803106881150490b0341440b041c1400c0714058007441e1b20002505000c0b00e10000c00703000c0e200c000c0c80d0903048001c122403e490b84180044000546028200841c9030021103015490200001040402181e0401c103003040010190030440d08025159003159480740c85042c0000c0203400354451481d6454249001d000034480070703140761824501310320020407a1148034074080e80c007801503101e65540340e0003d00c04c001c070140e4540d9103070460305d10030f0384c60602d059240d640e441840700c810307600d8200561010148a0416 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 573437544 1250 573436294 573436307
    0x21f091106031f0801110702010309080f03010816270207170d02040f08070302060301170708010f05090d0903050c010c0204090c1502060c19030c030e0706081012080301050d140105010b040303 84
    0x4010500091003004a45070041d106c07449050700c024101036507100310400303022060060703440001241c8100b55807569500c56a9580713900005038110100d2102c500041e01c010000400307440c9031170074540825a0054102004001e4000c000c00303403210000702c01e0b20550400118010a0f0480340c2e40390041c0c03924204034520311002115080001e0700c2d44070030020f00250303072203100352811281030344001c8001f4512450307044d080882580c0203804560916000c0c00ea4251340d5040640310304031410480741b400d038811a04071011040741c480a0f00c80d80240d420010a0b5100d803c101c400540050070108805010350307100340d0002195800049421142180c0c0d083c1d0b9507060050710703004402a240b103070800d00c07400b000342c20300c075040308008003071564880c8075a140c18000e0b008400c40107000001d03100038271360740c0b18060400d01d2b0481e032480c030004485601003880c950b854050007166400071036880c2143c0c00d28003401010b80031114180c4001204041c00b0358503007000d0086c0f501a00601020684440c038514019001 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 573438794 1250 573437544 573437549
    0x204021e1305030f1015150c151e02030615070c030b06010c0302030a0305100e190507051204020906011404060f020d090e190f1a10021f091106031f 65
    0x1c4d800030091000d5892000640004a9491000004058290380f213140c0030100c195010444420030302c3c280000880d00046060300320b0740220f18901403681d20804107001c0f2903002c202003482403c6890080b80041c81980690340c06000605040b12140200105c0032164000f00b5080300e4a8669103814401c10558020244d041002820400700611403680c0103512400707001c0e16003040550300e10000f003414141c641c55000400c1d00044a01d02c6040140c840c3d034a1003144100b0384245030601000c0713a1210310490840c0c0700e52480c4e5507150386a45941c3d00300b0181074000b4000c2070402c0348101e1062031000c0d4041c0207200516803900d825034908001403000e801d2007000b400d0751060181c007080c1000440320458056902146008820312441003001a1800520010400e458003e02d050812150b0001034041040411f02c101ca41003074041c044081284d81d512000d00a0500420400c0c00010f070000750380090f510544955086c400d50311450f0049445900125404009541c60074120064804d425070300d00c01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 573440044 1250 573438794 573438799
    0xf16051507020604090c02120315010905031f02030603070503030a020303010806072d02100608010e060a05010b0a08040303020c030f07020f040c0f1b050a05060103020102060f010812070204021e1305 87
    0x401c5426000108a8003551190a8050b512001d01c5107030680300348202454554002c2c8429240d08060040d1101d0103140071046002c2890040003113214500000c00c4416084943c050b8842c4205220550029420240c8200d405102d640c4001c42d003981d0a10141944e0304440c2d0040d44c80c0d40c90b00040a2405501400c0c0c1000d002485c2c05180c90b00710000094200940e148024001000780810300b01e00c0c3c03040714441c482003940303402000300e4461410342180c400511040c04a41d4039444900100f0b01300c1e00c0038442c4100352041001f0240340c0d2030081d1001507000c4d0203403c00500f0200001c44260031580081d4500d010510000744034021494004400c91200c1c00c05d071810050220b85a60142c101300e02089480c0911440a001c0030305440180d800c0d600700d9a100c403d0300d03040c1c2c100780381c09950f4a40c02e00040340035000f81e0b0001032212910390180c5048990203001889800944080325001d540700050907a0031607000c11226501c9030b0f84040170b100d120362000340c060341d07606085103800c008401034000c5407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 573441294 1250 573440044 573440047
    0x110f03031e060102030f07080702091501121a27040c0906140310110418020a1b0f0f021219110d080306060c1504050c01030c080708070c03020f160515 66
    0x201c0d0341d0b40041a0390101040261060340c0e6143c60072314001c14018001d00a50180e0484100030300c0149104800d4001c1e0020b880d04028a14982265010784610b0008422110310b0749100a00b14606001c2814108044662031070038245035010729446188103c40980b025001410308000a070b02901c1140c0050205801668025001100090320744408848407805070351210806104444501c08a400600c950301901d42050414007001004c9d401000d1035401186480703080ba100248240c4840320210380c8242000302d200071541c1c400701700c500c0c100d00a0343c110440b030b0302180300c543c030820076207508402640760802510182d1809040f41144501900c1c00340d048014086c00040c8480d0a494000800301c400c07944514142002c11f24010803400070340007661404081c4405d01c40b01103001d500c1280d00380d03418000032040c1182990841c00980310040043d031901e00268115101349600e022082c442c1c0f0558074910a1030529034502080c0c0c4d6042d00300f6594941c1d080101e071400c1840da03030b072420154031140d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 573442544 1250 573441294 573441301
    0x60f06150408100519020a0c020310020405090f190504031e0f12050606220f090501050108010608070c050d090f0801051b0a0e030106170c0301060e06040c110f03031e 73
    0xc6864100c0e60582084060301c3c0c03808140b017070780c05000c041e401a22090085484240f0194001e000b02d50000c0280d009006110342015408120f000700c82c1611400f400740001a210134101001d5404c0082c020302c1c100350601141d030260308a41c09801d0083c1d000740d41e648002811405940040004144c421040c080c0007002d17050281d070090451042d41c210320078005500c1d50340501165039031081e414003101d0303a1040d86800300902d00c00712840003a140050b050510310b40c0c0b110555130480f202030003294089240c100040102912880055510a0316032402a001c041199191842c20014103481c0300440e4030f6090030301001000070021801050306000a000c81c0c00c18804103610074034001c9800783c0480c4c00040006c40d05020b6070900e040410060020801907a441c10569500c60700007282355003c1c0100007032016646814040c0c101641c00c6654400e0741d9464800030080182a501040010f0004c8071641259546080c00024495003e000c060340d03480c0b609240d904d0408121204000c0302184040a0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 573443794 1250 573442544 573442559
    0x80309032b0b010e131d0f0106080d0c080706050703090209180d020303040c15110f03180102061522060e040201020610060c0f11031009060608030f070204020a0c05060f061504 77
    0x203800b451061120006140c40b540a01100c51920807160707135003907c82d5041043e2030110541c003400441d2954400c1e50084010040f00300c1d08110441406442d204084c800600800c499074804c64104005040004410603580d0100d50080400c485405a210500c1c0550b0002138040c0011500f10f4600d20240d4031390b190030f030340e10a0381d0203090140d011061880d41c500c80d034007401000400346c0c1c3c541e9401216800388a113103082e40d03a60700c08649000c2d096229560300941c1d50000802e1030040984265000440d0402401c1c0001c411111540007041442c0020804004d07409114030b601500c1001040800c3e071500f4000617250101c06451071070100942d06003042030720f0f032050340004220350107800d90320184c1c410704002154041d803a0409500d406902c2e120054200303d9400702013491b202c2c0038184906640c0b090320544034001da041600c41007104100a00c0185029802042c0340c42a41c20804460803168030f0f10380ca881e108a402c010704080000c14400740e450480c10038500401e20040300c2d4580341c1060b90 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 573445044 1250 573443794 573443809
    0xf0c0f030a050618010306050426031602031b06180c09041104090c1d151507051015080f0109020f040f0b090a0c090b0301080a080309032b0b010e 64
    0x700021250754074085442503440f1a0f60b400f40c48144020710b441561607013005001408191012901c503124211507126202d00804500100e480c80c07840c2034115030314075205031010840321103940d0131808100b11944089040000116900b405040100120301e0901c1030b00c22642844000c0810941c4144600d881c5699031900191344260300803141d0803501031001c003080c0641a5400000c0c510946000c0101e45000c0d1001c280301000b07030460801003607071034031051100040e8191501c560403284080790301780358400070300042144030302c5a81260861031400c1e60a800321140061000c1c00c1000c0003004100b808810070481c4100b0080d00300800210540794005644001000b03d198041c588802000007e149154800c0d501c0c031001501c404014505441b82000502d10a42c422022602110010448007054016241661300510051800d145c1c60781b90602160801007100286110821604079040d10100070706031410740400810000c41d04810400c410703510280e114504003c00c0031040380043e555003c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 573446294 1250 573445044 573445051
    0x12050a1803050a181212090302030c0f3706051309110720010f0806061b03190c0c0e04020a090c0e0904150518120d060909030201050f0c0f03 62
    0x2811583c84003001c0f41550304201800c00c500c5132240400c0c0020700b074402c04481503017282c40740c1d4602098402c0a2400da4622099010107509079001e090402d015003000f150f0340034010b40c02400c0c9d42c40700c00e0958030b0780400c000c080380c0c000030074441c4a0040852802078003030202919540c14400d04040003050300d002c0604903449aa800d05884e10018243c648403002182e9496412010810860b0014446a99642101859a800145104010020541700e062000d02400f001001c0e50318004040314a0365040d030390b03218410418041008000d800001841440d882d01c4100d4640f42c400c003005051154080d155036000303282d01c00000082200603030310301301c6410665000d4440082c400c000e040c0c04903014a282c0c000c89411000e01ea00380814082080c1c0980700c0c0000c0d607241440590b541820700304418004d403186040c1c60340714801c2c03914491000005456603a000303510004039207581d10000c00540d0000744c07050380540d558205009161404d898510382c4260030280762071502264040c040068403004 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 573447544 1250 573446294 573446297
    0x9050904080d09061803020d11210c07080a0b061806220f02041211032d011103070f0f0f02070605070204090605040b07110115140f1012050a1803 64
    0x301010f2080000c558440400e11000001e122002449841d010b0354400c0b5a0603154089030300e40d2515032200b00006440c5503548103c048880030b03048c0c0020410400d0700912904426400b600501281703c4504000000c4504e018035080111390501400380f210310780040405501303800b42c000820080751a0802c6520152013180d514000c540c1e0f001c1c9000b0010440a0404282c2600024000902002001c0c001441501070245000101501300400d035544924406a01e84400c020820700340e07100c0c5c85000c00e8500003c040003ca400241d0395103191256004035034081c045081405802a000e03031000e102410781c210f42c1081c80310030303001040195035900144540d00400c103002a40a045444940118000e10360008040c0f001e4105890001c64178a0700f2198140043d805070314200b8040346c14020342141084c8541c1300020242003496110b101401c0b0a0a90307000045080003a00a842e83c408100b0700ea0050784c0c4a10103100390207542d0068a00140844120701d041c18191002d07088140003110010360706 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 573448794 1250 573447544 573447551
    0x151a0703030603060e01090203010e030a08040f17120403120b0f041a0301060803071203110714210a090506032e1e1d190506031e0d09050904080d 64
    0x2480c044014014582008080c141400b03015601c507607054021542640c42200240008001c180102d50347c2e01584051100040134180441c1c045030341c05820b4100c0761b008141100142014100300c3d00e01da8048410b5031840b0045400300001d042d07001580002c00058801c0a2241500250000701007507c0c21008502c038643d0b5000230040c000080044025411019000784081503840c82c0d040e490340c01200c0d003070b5081d01ca060b01c6101982e22034480d001084c1c0c80101240c1c208062900d5a81140807613214152a602c0380c5a025150b101c4003842c00302c440558140115903548101c0744c01815101075611141c0100400e00921842d07039281035078000c025504100700314040a00c407a46000040c4158044540a070348a1021b450010500071000d01b0307a0501040202000c04042071066840c0c801c1324801e40460030030080c2004001150013080c3c020074004d080b030310500c0c00450f000c0700e10340e80b11400c070499611100c0c82c02e50141d000b071428402084100c491510368501522804031034820006e030400400e54 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 573450044 1250 573448794 573448807
    0x1d0606160b060a0f170609033402030a0f140109021c11060d020c0610080d030e1f050f0105030606031903050d0f05060406150207030305130b0c10151a 66
    0x84035840000140080d203540701140d513071042c0445c262140d41d98001c10324040e940005030002c0d00001243e074840c2d02803542c00c030780c1c040030305030114054080090b0310440040301e51820003581e010004491f50901403182d40c5440800c5e850104003040b06003045046690600542c4000b40e561302c0c0150402d4800c4032240d0004105034684060340c00284a1000da0014010a016009110540c00f60070f041100034201c40c85c68480e400020f9018600d442007803581c0e40f02c145d5801c840380c801d4100042c3d03411100c0495038101115042d03001d81700a100307104c5100b280e8403010003150207a40515036006000035009003149082500200b919850003903e40e00701001e13540c02d60810148203000300c41030450303801000c22904410003c035901074035087c1c1c2c1c824803442c00d1040c0401e0715480c03150722415440041d00140007042c590307601524503402000544035940c107035081c0090440f015000410300c02010401038282001604104011196001602e800301c6020500a00414100364207140d46100e5031000d0584420 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 573451294 1250 573450044 573450049
    0x30403032006090a1208010b19030f180218060a1e0302090f15010e03060703110f0f0306011413050103020304060b0315010f0e19021608041d0606160b06 67
    0x8410000d45000380b040104110000a010440d40400c03441030742c00d40d021980b50501203076892800c3c007520380304000402070000101c0300d00c843c4060082050038007050301400c0d22601b6003221001c0a1050f4407141e104405c408601d4600e800307548480040384140400e05100d0041918100e050203000c0c0050325401681c2061011782e0140d10080d940104102d0152078045500030412005543e449000d0084403078042d42580105442903c8182c09402050240e070790341c0d0120040e1900c26080242c05004021030b8400f480c100f8001e18400e20483c1e4000c0d51fa003014030005041c4685000101c94461042c00741c0b0007083c20000c0c5405c110f40d424030b000b40e126220f0742420702c01444084111a85480f8450f445c01300c4c0c082202c4a00c2c101e68044800081e41661120303c00c1d03440d10211400049402406020007016420b0342c05001102c40003200010131000a80c2c4141c41ca5019402601e050062040502c80036610600f076141e10100c292640703401c0070072188011a10421149001f01255803030000170b0000d4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 573452544 1250 573451294 573451337
    0x40b18010203190302120903121512071203080f070203040513021b010507090b0c0c0405090309030714030c01050705100f0b03030d0501152c0315071808010e03040303 73
    0x114054200c80032800c0070f1007400f0b0000e502c03030a0058030104801001801c20400072064542c055014400000c00c0d682e20b80c00c0480c0691100c0e0440e60207510208081c000c00d00800030740014110180100107540c0329400c003c0d01c3ca540040000c4014041041002646503000c0140d608a03203040e500c00c5144015100400080c0c000c64182e184c4400707440320704500d0000c1c1500464059101c0380c59460445864900c0281d1620400c4144109988001e18030003482c00c2c070740d000ca50300c600f200003500d050080840010b82000c6081d0302450405041c1003456605160500c400c3c10b181c002424114070f0300d0490b0303840c1e640b601100d0202200c40355070744501c0d10f00e441d2181c01446c1e940e100241542e03591148864442c000300801c1c0a01504d20790f003801c0d068845402a45070f402c400b0418044030450401d880902001d00211640c0d003600350068408901e481c1c3c0c04c54900c00d02415140d1208030445018003c01040c0d2916903001c072405a0510104080010b000f004590a0365014605002035816225805960 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 573453794 1250 573452544 573452557
    0xd0f0302120411040b060a2003040b130801180c06180f090603050613020a05060f0d150501081f180e070b040e15010f0806010c05250b040b18010203 65
    0x88440401040b04000301c03155501070003441181c1c20048600b1010501c45075000302c901100c0420b8900030444903045144030786803030800300001100d00e03240c2c44141203002900450501d80200c010745400703100c0315100303000305c0106446500e000300700300d0400d071100c034030300040380c1f0841c0148055403001154116540310342501400c550b0480c01d4199580341c00d0720340100f48522064032140a00c07008211050701d4411503003840c0b5001803030b00101d103003440100240c1d0340c454070420103208010081c228a0840c107014504007080403001c130382001c503c0c02002510300140108440c040004007a480180d01d0381c14003010050712000e0882d2a158007803141c0d800000d10084140c42ca19100d00c0c80005000d0922500800607201150410b0009446114865503007a0f100404140425074500c083c18101c1d00c5801180e42c80b1f10145000c055007200c41d210b142c10450b219400310b840088014400110804481c6c03550010301216a000d45090b1502d03450554034000c91004200066003a8404025684208165075a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 573455044 1250 573453794 573453817
    0x11505070602091206090d02010e0606030c01030e03121009061d0403180306050c0c160b30241e060a052104020316080a02040b0a09020c0c0307080f0d0f0302 69
    0x205d41400385000717583e09a159200c00056080108140d40c11030003090441c05100040e000784503c2d14054015009032400c01c628400c644018098480e14440d0030504034090b8100c102d900001a0412015030180c500c1904580140f08801c05081103045000300c44550040d0545800b182141100c01440c008a40590026256034101014013585048100003071461041c0b034812150741c0325039001a46a803042c54480c1c04101c10090200c1011101d400c80009202c15690340c00c2c20b2401c0d40981400c4042805588955004030748000c4802000c4805001c0d2002c580c0481d1800352001450341009101c14100d0341340f40c040c0c2c002080050000380140c0a07a03144c0b0745e00c6542042c240150180407810303030104803001d910920030301c0414120b134030716015038a042d901002c0c0607100c400034503002d10025258400c80e00b0b80000d00020f0015840c4c48500c041c004040740000940400302c2d10740c007050724000440c1c001003d5900901d606a0022400188400301c1003d14103244081e48059201070300240603503280d81c41c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 573456294 1250 573455044 573455053
    0x305180a1203090906060806101d040c0509191202011223100504020f0d02030613050a0b0406080615090901150b07030f0305071d03160306050f0115050706020912 71
    0x204054203c0b003c9001c0d100321020822445690302d200702d5541e50107a40302d0350800342e120440c00096101c1c0c15683c0c00d032007480e680d10520a02ea14040382c01c4a0100802600107040480e11201c0e078940035003848040d00f9800490340c0890300302442e10f01c074228075680081c140f21174522030710340c8150947c000100000324005128540e0780d40880e004030041d81203d9003141d000c407902d4041054a030a10a842c0d00c81e11114019040c82c850461502c020743c0060003060740800b42a400c3c0100c1d0459009640c40b5404186020170180101018803065542d075030070404042d040f41c1c0800203ea04560211a40c50310101c2e60040d1507122880110700624134680c140c82070340700038417010a407581c2040c01050320300e00c02d99403104056840300045044940589010700010701c0110881000c1d09003105a200ca100d008069901c4c03845a80e80680003640b2960040307032840e40310010401c0503420072103110b004002c8642082c900d0281400001d00034412610700400d03055021800b81c0b09038480a0503222699800c0d411503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 573457544 1250 573456294 573456329
    0x7030e0d05030901110a03090302330418090209130f050708060403141201051504180903020c010c0308060d0f06050906060f0103110318190606140406030305180a 71
    0x903070b1258401e00c01d0038041903000502001c82100040e00041e41501582d501000074115400c010380300c3c06900c0103024203450b56104600c0c10640aa02100c44441e04001590f65450154604460500905c4242620780fa00e400f100240c0c0750707450290f41c0032076108041d50302080c0741e1801480f0741400c000f01801ca481940300101d902c140c0003c95038000c0740651216030b040d003604143c140241c0b280f01080d2491000c1000100b015042020b185503511700100c0040c1e04264540e090816005041004d801c3c00d00d403280a80d00c14190140054051460286060303145007946403400303001c004d4003a050354018071100d042ca0090140d00c0000603030341503024800303218609041c098a0b54800c42a40d4652140c0c61818100c130096010b8850305d1507542e148100320b070640d41c460380c0320780018400d1250106075000f1001801802540c5442c0ca446036032192400181150030104920031607100721b040d90380100d142132000d04c08a80c00509907880e9001100007106501e08440110720a1344030381d4084012101c842850 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 573458794 1250 573457544 573457553
    0x2061e0412050624031b03010b12071701050907060c030c0b1504050606040f05130608010606050d05070203120a0b01020a0c061709031602060a030605060412031205090706030207030e0d 81
    0x1118021381818024500714240303402013030788000300e40e008a907044e40701c10803400507840340070761800c072030500103000188800039500800d162441904502c1c44a8129890030f2203664850140036181d400340c0802000309103008d200c1c9039554201c0d03006500a22040b030b030b2000101032040c4903044005078410310700c0181d402c00200f46504000b841c1c105901c1a800c10000800300e081000036117044402403518140c0540c5054184442d0b4030550a5010030302d5255240864940c2e000d02440780149442d9039003a03038500040755440100c0300094000d100b19002040000c0200f0610300005030000745482001880181d40070060340351205c1c0c408000d0181c280d06c1400152650404c0348000000540540d100d240d5940e02c03426500c2e48914907199540c40003c80fa00005800c01074003611070070015040019015482d90001800c0d50001d41c0300100100c0742d9107001d010075910111895421001c002c0500480c2090303001c10b5120411401403900705907010584c2c43c1454420603404202e031001400002c40c43c2a40c0c1803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 573460044 1250 573458794 573458803
    0x7081b0703030606080a090b010915050d030512130221010207051209210312040507031e030e01030c0c1b0e040602040f0b0301182013090b030a02061e041205 69
    0xd15801310312450000346c10040b160182d01d81480d40030307025000503130034036030036400034078515803410348440030030102140340d895a40c0c0000c91079000c0d4581649511824161150b03d5000a101c00c502d01d4000583d8030052700d41e9980601003000191100041c0460944c50900a01540c4c0c1c000e48240b0130340c201d0b115440034001c020940000156180808100c6400f00c1201c802003100c0154115070040080b010117100001000360094400c44c00c2e2003a1550365103500310f88814503541401070b24008200c9008064011601815100080c281800900d140c03a20203016000c1c0c0d08006080b428486400444101c0c00c802c0480c003409005184810b28102410410025080303070150f80c2e4a401d10b04408a41c0009040c00e0b64100d40e84691440c2116000380031030006040040c2c0b14140318000e0181d51419030800d103000d000c210000c04148165989411281805c1d120b0200c4c0c91802600700004480150312500116100c035201c010b0110005e0700300c505060024407503640611180c5da071541d240003c1140104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 573461294 1250 573460044 573460049
    0x42609061c0f0605030c01020f150a06050901140a170606040b0102010e16050a0b0f030703020a030207060606030207210f05250302071404060f0632090111010e0607081b07030306 78
    0x801b1183c0071900580166610190a48e0b400d4840e0720403440407800740354071620203a028882080100741159110003080102c00217810010070812082060309050a090500380010200e00801c24600404d80c0740c0140c407180042d080b14012a1100d640541e264004d42042440504401c200d51807040c0b10a00c1c07204401e1140a82441401410800104480c0384015100340d00f0f245d000c8149103490342c46d0190300a6203d039003284181030b024070400340468000d1050b88020080c075180580c0d2203da62406414005e4010240e00a00d06003805001a43d42c0c820449000b04c000c0303040c101c0e0741c0c0f11001c802111181007080302c0e000c0034040c98100400c055000c143c60044509540c03007444403a815000700825035030103001c0c4441e50480d100c000c11809108155500520024000c2007281c00825050494450341c0d17400e0014040000040c114101e591000c00f07074002d6202d00000b0090800080402900d41c04050100d0382000003a070301141204c0c810b002c8a0700c802e400c3c0e00c5c1c170507514580b41c607010b00502040d2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 573462544 1250 573461294 573461299
    0x9110603180c100215100e151903110114040b0a0f0f020604050a02041e0e010213060305010e010b030601050c030d06050a0b1201030311190605042609061c0f0605 71
    0x40346210311a0800714400c40c0400f0301074000d445401c1000403203000070500100740515640c0000e00006900d204409418010030045400200d0105190140005103a91400d400099603131200200042113000341b480c1c82100092030203c154610200c482c106c41d008541042d0301c0000c1c009600b500081c1c0060b80c44440043d280c644c0300600001c6981640c484008071009491078100d1b280310030041c40c26a00c2500007142d200703c610a190b10100c849030031101611942001c9030341c0041c00143c0f917401902c5500c018201481d04bc081c940c189a40140d55020600c66085407000c00300200e10107a0003917040c3c030f550040c1d20003200d450703d155003056400f501c904d10500f4000c0700c40e1100818103032640c10450701c040e6070340b0040e10801d901e156002c644140540718041258000c0380500740b82255020018003445000300d101107010306180c14072140701d1441c4201e0482042590031090710380310402c0d090b601405c0341150215143d44640c07413401098045902c10440d40c504d444840020315500d640120141c6609 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 573463794 1250 573462544 573462553
    0x16150b0103060f08070e0726040c090b060d09050c060a1e050403030f0f030e0708030301090c0302090d0816060f0507110f10050c19050433030911060318 67
    0x1911a0314800c10b011380101d4490760803441090110f1b811000300190005458179002001490407054031503140c01554400d201d4a4888040c4002d1000305c1e51008080c1100702c80c100035842418001803003601c41e104081c4441c0b03803078841240901c5000d10400c3d0f221000a8451662444003860051000f00440380c10000b810b2082440c41c0c0142c4104251425a40d1544441025044440040d500013103100c0103203041503100c100e07120841906002800003405890001c5483e5414602d29800f6105409001c4040620500020346140d803110400c90102c0d070000e440d540c0e5442416803006c1c60141060015002504180390340711500d0381a8411403148081b41c0e180074055120440c0f40da11004490311006042d842480b175806000300c6036020720b800c1555440072a05d003100146da14900c40540c41318000100b040032034200b000a005052441510842034030400c3d1010b2480c045440700250784200340e040660b0b030300d0700074204111801c2e026640040103181c2612031410b8003c5085440c80e01045100714003a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 573465044 1250 573463794 573463799
    0x10602070f0b030709050103023f0105040b03030909090114010303051b0d090506090102030d140103031706011d06070c150909050c1204031e081b130b16150b010306 72
    0x20b050003980d009004965032080900d16040046000e500102100e840c100c1c60790042c01d0011422400300c40d1660415502903101e1800700841e041c0c0030805034800c601940c1408642619503030007000b1920750b00d9040303642098a4980190a5004119020040c42d118a01c1170002c81450340060140000030500c0c90100c1c0c50920804490751a0003070030001e00042404100240014038003c1c1c05405220740620480c3d0802c3e100c14007034419030300c075400f8101c00448940c0050061680c030060283d01c85d11061603c4400781000d82c00200041403a0307038000c43c00d504440901800b42d44010445024580051003010401d484070342040b4926800c1034103c0104112010008601906028070b500c140894200203040514400f85c208580d80c00500480820034102011000d00440d000074201d8141c0c01e5030365051901e010005500c040c0072810030a003c0d40d01c24444003900000c6a4421029601c1244001c1d468440d81d981000c034007081e07120020200303e1542602d91041c035240d0b108040c251802da034140249075 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 573466294 1250 573465044 573465059
    0x131709010906050d140c0d0b0307060c060f0905030712030b0d030e0402090f150c0c06070b07180b07060b13060f0308090f040c050d0f0e0a1e0b010602070f 68
    0x1050541850100d030407103404105a5000700050161500b2001000c6542c80d9840d05003070100ca000c5800464261022640315006d2400c1e1081203404030099000b080158140000a4540110941d004201030f4441c14505a0304040341c001b80d0007180c0c03060860f500da000380d103040c0780300300012a031200009141c20450440e51a155005080c100e800d41c50b11440c0400d01401e00000c2c0d07001c829100c2d00182850415141078480e007407101c4180c41030074071985c2c13100d14041c090742c00c0c005074a011a1203440c0500000b000304160900c156008056400d211050304503036440c00b10400284d0380204080310300414044140071254100c030708141c00455148209540001c2c0810845009008000d403002128000340002202c4800900103035400419440d00365107500d001400f9170f20f000500c800050340c00b088540d581c40b11030003040e428080456007440842030002101b95110340850020303155079029400c080c020312418042c49400c0342c200020008668545001a65880c5203116682d40c0d00da038000b0000342038 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 573467544 1250 573466294 573466297
    0x111002150601021b0d060204150f02060603070303090e13060c0903021912121e0e090f010e0a0207030e060d05010e01060903030806090601020f0a050d03060803030f01120f0b1317 78
    0x4400c1d1044d22001d0300303a10090000c201d459071401c80d80390342c0c20400406d07001007084068031052080d40c0e6894030180c481070020708010000e40301c103009611100c0e05100189e00302c2200400c4d100b111b19510455914214000301c600e00e1000c1c080c050520300248241c0c9c0315404042e081c01e4a000fa513441c03120310301075100340076000300303500c18405466610409440060a4404103002c204c0d001e2401d1060125950030744100940e5040c280c0004c10b01a0000c040c0c1810080c4200707501c90703003a00c02850f066141410340303211154010040540103600045070400c0500070081b00100082c040e105a0b00c41c04c24000040080c6420300038580450200c500000740e140c455920401501e038103035140022900c0f00380500007901401b4000e94158066900341060000d8104914420140144014800c124a00a01508950803500103007444e402c100304101d240c82c800618581180c9086080c10191480c0c1c1c20300d14568502d20f00c0c01800c01400070180310312000d02c03141c19000103004032100c2c0c4002103c242c100d1a103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 573468794 1250 573467544 573467563
    0x140706110607050304051e150105010c020a090c03110d1a03120d1505030a060b011107030b01120f0c080c0112060530160f0b07050a0f11100215060102 66
    0x20350100c000101c000348220040d5400a2040c0110740b164030401d805147c4404140085161650181400c0d24480e21600c2c0501d00509003800c1c241424052a0082a80b800590150b0b400003a203d040c0308507441d2080c0d00c115040420441c1c0c0ca51604e49028444001d08403a8004d405058143c2c0b548d40030b1860f003c1182c0c030400c00c25080c070318034000342e594401d0301070309003107600c03030544141d0450004042c0ca043c4000d818a5115290010321910448000352002d00c00211003c100c6d840f03d0001e0000926142000f8151541c1c1c882203511125107241c00c42025103a131200812141c1e80c1040021600c00004070940e040034241c80d2403070140160403201c01190000d05c43d160f03001c03003400c0002181c1d1001001c1c01c03024503481c803640e1f10039528907a00189401400c0c400d00051101ea0f00040128000581002c0050004581c2c6613140000f01d440351643c440c1144c0c0c020301080c0e03082c098607003040010404050300c034034040d02e0001d03030340038081010f520b03601125146808030040c000010b245e9840826064403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 573470044 1250 573468794 573468827
    0xc080703050c091b040e04020a0b12063f03090d080d050705120c0306033d020304030504061101060f0603020a03050604110a0f03061e031a100306110d0504140706 71
    0x2000e18002500c810100c01030b0050341c1141490714040303150701ca2b0100416020020b44c511700881d0614200b0701080000c8a00c02c01d0748901900616a461242c0c10710101e00100000c140200c0c6c8070f00451924290321548141c2580242142d12200802011801400300c504841ca0100002c0d074911505955a2040e44558619100360100003280004624065900168044e040720f80390348085500328080030400594201c6a20440d00d607500b4006415400c00555842080550a60500e0f6601a00500450164005001c0d01848481400c1e00c2540500020440082d04008143d99124007400a511540358540043d05201c0042c140341068001c0100e4400d000420501e0003807080c0e0304490a102004120b804c01d03441e20000103200d2090391901c4031490a041c1c0041c0c0e441c0c550f2a11a40c507020002425422082010030818030104d040200c008494001c0001b04071594405c40d00b401e148201200215440d10b00f41c148020f0040c20700d012200081e8031070031521800e8480c0b60548061000c0d040522 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 573471294 1250 573470044 573470047
    0xd0c05030703050c03090405090f100b0f12120d0c0305150d02040209040f05092b020604261602030d05270a1a030618090312040c080703050c091b 64
    0x1000280f2400c020480601c9000c103032400c203d5401c0000b0240da8064403180c1e6207074800c00010030446800e001c00c00d407442c086038040003040030400c0030070081e82e440907406204000800074203250305414000c1505000c0d40c41c901d15070b25150f240400f03004190f01003a00002030305e808001803081040102005880c0c5009100c03080c001030641c00c01c07002e980014402c641044c1c40788003041d0403009a004581c0070f07000c510058646803c0c483d490a032031b2a18a181d00c4401600f2084420080307401003183c64003d03400c5000c0c28402d1102c00108454560300301030394440b00b8400a100c41980c0449000317041c4241c82102038030101c0054034001c840900481e24a00c1160603601090103820844181429400c5c0d0003030100c900480d0b82d224506004d402c81e010070540310400100300011883c3c5414009020004c0c0b8107250078906052105907580e0103404440c0340c0090381480860148000801108000c0c101882210b081c0ea07140e10f801501c482c2d0f400f0400c1d010720340c04004a02102c554181400e6070342030040c1d07503a = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 573472544 1250 573471294 573471307
    0x1701050618030118030c051b060d0207020f06040303030b090604020a050a0c060e37080706020d060e13053703030209040c08040b0f010b09120c060c0f0d0c0503 70
    0x24201c00c040d1465155140d035a500340146220414408455054004d0301c60345c00d00c0416050050901102d050322800344041880c941506941c0c410560b45100c6c1040c00041c4c0358030719440822800b4907590803540e40540301103000010141c0c99008080c88a8056408580d60344444050006034000d002944001c11000e0145218141c800c0c0030f00540e90780103100c007083c000090031031203007014050345040700c2c103aa44c82d645480e943e0b481c4ca0710b440811224080315a00c800c0ba03841e0340c003490041d400002c040a40000741e00c10b442c2c00c5500540b001e0020061245c400f814000301e5452800c4512104a0300d070b015480481d0111100d110800c40d081c01d52840c0d400d8404800c001e030721420125840d0072024035909000700c1d0070640751032294040c002081d8450301c04904042c1030488030170384c0080c4401200440c0200501032201440103540f8005000e0b074004001c500180d4140e07007050f50010f48642c01120125520740300c0d940000340c0c5208080308009940c1d486502da2000c0b20303040c20b01540540203501c1001034 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 573473794 1250 573472544 573472567
    0x207060e0138031501030303051b04030b0c0304030c0210051b011505240a021b030606011215090905031b060112030c0804170d020705010507021e0102010e0f010c17010506 75
    0x50031042c40201075902c2842c640581300241e040a801c1640001c2d503d800308940400c4004d90b00451303500c240724282c2490710355a50022180002400f8215419001c40402c08245c050010f0040071680201041045802624010250780208015255207c900c0b411200031000600c180c0c1c0c1e0400b8008401d100c080c1c2040300744090340070b1035241c41800071205049003035880440d030082c1c0113400c071375400b81441140d109062070750004043c00303261003a0482000c3c8501607070800b920020050a108002c1800d005083d40d10040c080360b81c0c80703007414a0401500500300f01011009003414070013528941802182d080f002c507903404090040a003110002808040031a0248140700100c600c80c0e03003007524043d01c03644550104600352841c401541d00542c048290b05d42c052103030304040d040c00c0c6030032810008903400165990041c030280040d00701d8540100340d20b40e4030030340080c1340c020441c008441c102140712502138000e00c2d814000c000080c0c40d024086403880e5041030114122100200903d0078844003581 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 573475044 1250 573473794 573473891
    0x412060c02031b070e0c04260705040905210301050d030e030a0f030206040201021c020a060b030a080a0513060314060f011107080307050606041107150207060207060e01 74
    0x56415403000f44107032044400c0440d00c00441203003500140a40300c0c03030b004505926010141403000001001d1009001072615a0101c54400c89011202e102e000c1500126500b0036500760000c03504141010441801d010002500d200c602900f2410b0020160004682180e140820f0180c00d40c0821450000f1010a208030120303144038000909a40e001c03c0c1c076039079103292222800c80481c05a049541000159a01030145c00c00c0c040e0f5668070040c100d00a07e200946610500d14006c020a80e114824042c98034104007210000341d10150b8190380e101d50750000340c50364100685004044440c0d00c00421918401d000d0f8a0058192801d994010307181c050030031454200800740d050400c9150404c80300015070801c40c1200600000c00a19501c4c036003810050300340040117060501950800c252141030540c50383c116103400d5008030b00070703040001800141c4040c0c414980090001b60000c1680800e0002c243d11000c07101c6500d4000300120b8001115080c910300750581c0040c03030f000c000000910401076061 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 573476294 1250 573475044 573475061
    0x60906090f0e1906180911030109022407060507031d0111040909050102070b070f120b030a020d140607030204090b010c110f06090d05070504051e0c090616050105100902041206 77
    0xd8041100340d1220a900c00481c142c0700c20101040c1c640e0349071b90500a10308440030040c0b405600a00030340840c2c0c1c011400c00d258040380341540381d9982c00c181d01c0518850701590082a031140d010b2005060404006001e80490074002c1100c2c106000c0e180003c0320148201800707400a410528101450800c5480003400609416542ca54081081800080b502c0d288107120703000c03a454914540e25215001445500460801a507462074912078041c107541c0050703860a03442d0b0480310090625070910704002003800070313050241c070707803041c6014001015007540140c000e881069a08000304107450b0011a0303a603888200140029203c0d80b80103c45081c400e116140050001d4441403070601c940c1c0100c0c010448000058406802035207050140b0b192034061560010000c0c02029043d460030300100c401c0c1c00015040c005d055200140d02e2206072940300c2910030442c01c44480c2c07101c500d06801c281e03000c1d103000c448542540100c0700f00400c02d50340b05c0c804e5030300362030041040d0102c0721040e6451130300400c0f449 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 573477544 1250 573476294 573476341
    0x12030402010504150201140a0207050a02060d061d070305150f040b12100209040c09031a0405070512030c06090f0d0503041a1303030c0203030f0a0c18060906090f0e 72
    0x8020100384c011240409820b08003040c0d000140c0e014a20001c40c03281c0310090504200c10b80100700000109100007a111261034044801d29a5068100b202c00010300c043e07400b03403070001d41910803104908000c0001c103203c1c8066440500c00307035844058070000480841480c81d4007007880032010b412030030241e10040810402a2001000035107800d052864009602c01168400c0d800043e0700c501810140600600c141590604114250540d90b8140740003c1c0c80b6001d10300080c4010002e41440700c01c2010740300030030003e4064041c030655142e0503600ca0740514054145480340c040800c1e100038000400c0550384214102030803c4210808044440c0e50014009039804102020910b103000392141307807180505a001c0c040c4900e40a10b150260540d82c1c5081d95809540052042103808881c94107029480040024005500a040e020030b482c0507410120020700303400344170070110b02282c01c86a2107041e1000c03601d6040046644169406040a050150041907402c5001088071078500c01340000d4040c250 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 573478794 1250 573477544 573477547
    0x70312050703210f0608030703020c0306040305040501050322060e0c090115030207030905040c020c130513060b03012004060e121b010c0807050c010e0405060306040809042702150c120304020105 85
    0x900c0800740c29100c2540003c00c0c9070700001007010809d60100300018400310154041d020900e072a03100540305000300d03c1414103000d00000020710b003001e800c0940e4154424070a181c1b4261041b820804002e04d00310f0166a6613104941100b49107142184205048445034110b003030041641c1c50089003c4d4010348022028030021a0003c159580e43c1d01030b050031740086030b0080004c0382c09070b002c010180d401d200340380d4038052a000500603c005c0e031100d1202519000f907408140c20b21382c6400300380140450349040c4d1030a072006d00b105400400b039000070000c8600310f6a80741e1403844500c041000d030422019002e06035500c0031120400118583c660744900d5101410b051130041490389804403294884203044509030041643c1d01c07041d60300003006a500340c03c00c0d10f0822882c03500f280426a548805000602400c0c4007003141e0300550740365001032020207120244042e03d4624030b54441d80d8080c0d0220101d200780d81c0d17250680240340c0c107902038440150039440203244400294812808a80c40504184d040100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 573480044 1250 573478794 573478811
    0xf02010f0216080d091508040f1106030403080105030f010b091501110d0306080607030c0512150a030c080c010f0207061409090423030a02070501030b0a0f0807031205070321 76
    0x30000a20003800010007030204800c1c01c4ca0020f200312041d401030400401700420042440340c1c001151a842a404040c407811391446043c1503caa208035203020381d010400000300800c1640c803401440c101c64041d42181c114020481c1000d01381c800180034103400c91040d80c0001c0943c04004881850090306041034032100500207d080d04011071240c504001c69243c64041011480801c1a0340c0d00a0b218901004515484200141544104607070302005017050008907400c0154031540c0000e101e4018040d60038035540346806003da00c130500c108100c0307024101c040b00e6294007459406a088400f54007506140e070401c14103403001001c81030b640c1304100c4140010200c80d2114003c86004d140141801c40e050400303400c0303c050204038440503442c2070f00309001c07030702209800086200607180c00b4200440d02c10022030100d503030030109600c642d102c19501640080c0f640303000f00d00b0106803070040300c0300303013000110480c191041c2c802c03001d0040c0011f01c0b03c03a03024520300e0401d002607082c5c526004003255580 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 573481294 1250 573480044 573480073
    0x9150606111903080703051b04140102061501050301030b0403020a02212103160302090a0e09160509060418050105040b061305010e062b06061406070f02010f02 70
    0x21200d400c2000825044541601e6a001c208290a45041540d03500c180e0a00660780c010078a10014004409140c0c440000c0f03201c240d10320700580c40c5181c80c40c442c3e9480d166280d50700002c000703d09503184d015004040c0450051104e07494240316511060b140c03180f075640796039908200188002c001350700310300900f0f0b420b10069640e00c00c5111070740401500c01c00080080881a0308040c403010f0328400700300c2c00c144c1103031490b00782c50141ca43c031402405006031071015607681540607125030a000e50344041c40c80c60100b080303605a6461400380a16100302c80c03140d450350012a40300d03541070082c2580300c00001d0026819162a4000b144801c204001c20741c250785a41d5245400e42e50107540c2110601012010000030b4285660280d21a1890070800c0c411035252280b0f60030842406812503000b04090b64000a03559003410301d12019214503175242e4142c00c440d04102008084a0040711180c442c02c2148103060314003242502c100c15000354000300201040d0b40103480480c070041d006c2c0300f0b60007000ca42e5410304 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 573482544 1250 573481294 573481301
    0x509031905030f0313060606052107030902060f030a050c0f040b03132f030a0c120305041814060f0319171606050c0a0f05091908030a09140102100915 66
    0x50700c645c1d0000e842c0c1e054910b0b003003042d40c1142d0865401c014083c0240050803503042904464424240340d0342c40642c0702c100f8200c4c09420780810180d00400002114010b50444500441c4140b000b4402080b10b612049003801840c0710365280d440b8240300612040c0700c140ea09400940d0400b140080141584044bc0d541d0312441200300c071140800300c482e0300010800c004060811046103411030150501401654629031101c40317600130040b00416035400031041502440403107010301100007211840c501010380c00750107801d001c00c031001ca49101402081c200e050005101d15507200040c003034440c5680302c021401020b075044c2c1c0300f600c1240d0180025170506454a00903d04440005603603626032400303040403016100c0140000c50081820031004802c55030000c414025a0b0040c0740c6507603039111000014013540025403040b410b429001200280ca544000024a030b4200642c8491140c90f554686038002a01c1020150b07025030010080025045115444018043c0c403404414551100003498007044 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 573483794 1250 573482544 573482551
    0x20319050909130303050703050c1605030d110403110f060a110a1203020c12072103290907020106062001090c09050402011403090c0d030c020414160509031905030f03 73
    0x1d44000f41d0301c280c14160300d409042d90100450500b40f0031805c1240180c1da171885110440b6a0305900014144100842802220304524000c2400e0002c024850b401711425809484120307030900d4010618003007801e01242004c2d111000a1190b030030600300c000c05841d070b03105680c00701409008104100c80041c1ca18240030301035200a40d070058960038901441c0c0e25000340c1401c0752802d02c1e01071000100184440f0300a00540d202e0050a0801841280081c0c01810400e40154410364210042c1d1488031401003100e0000315040300c46121036168014181d003200c21070b018240000706000d964070503200002542c0f50980035806c0000545d40b000d91550701840900d5000118034640300c605000a542e071104d401c04540080340d060b030341303542007214001340e9665480d8005405284800c00c5032042c14007810000c0845500588184050910210017141e6a54122080004d1400c0c0301c0c41740b42c80c3c2d0307c80c0b403d581d100e80004e001031544582150348201c030343d14074800c1207986210401420043d0300c4002c2c080c500 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 573485044 1250 573483794 573483811
    0x9030807080a0e0609160801060b07121211070204060501030219080619090b0405090714010f11060708040213020a091412030a090f060309080d09110319110306010303020319050909 79
    0x4100109407925a040f00c103611240387e60381022024801c1400300000c48074020783c0001c80056800019900f9603c14481003000b40005141095074881d84290000a20590f803007140d04128179511140190304030700464001103034615142241540d824041e8800640146005000403401c5000c6c424908192225421400f0700f9500e8401584050820b07015076500100460080c04001c2d00f000c500c11042c40038492002e0400c0783c40c038400c4250714040c1c0d202011102207007007658401d10700303450050951202900d04900448002c000000c040076284262001c080031a6118081d540c64900140c15440c4484580c0364130040351100441152410402001c001103182c03540d000c1d66240269032001c2180e00d43c4181d00340340c00d10051034009180c0310121800403000400003d40070149081402414007502c1e81e141c0c00d4407981e03410342c2c1031016102062008921a102e0450141d20304420305403501c0c02884020050b034000d100c00070300c42a07505003000c01c84646d0705d0b20500b8828541d00003850316000752603811 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 573486294 1250 573485044 573485053
    0xf0103111b070609030f060f020f1803070b132d0e0f062b03021213050909010207030801060c0f0501091101022406060f0d15050901080109030807080a0e0609 69
    0x29101e64103128a500420841c18600003051039900d401140318541d0340020115595a52075402810003941030300e031000140019642c0701c2105c1080f95010b040340382c901502c240b04115000502074510b000303e820602220301f00e200c0303080c544000d0086074685000031040d54035101c480c1002c1900f903910104000c0c541600b4403103480c00e00c480c00000c003060140082e4040d40210a4091000800100034091040d6000030307105145000c1c1401ca007440411609071546410007c3e502c40c400a1034000d00042d920110b03210ba0f91511008a018202d206011005001c02c0156004104460180100602c45401280080b2000031300d0340d5110700b102c1620710200e44803440c00c03103143c2a55034100400d034064807000392030078001321140d055448201c60003042c0703a104031400a4108508000344084d80e0855000590601c180102d8808840320041d50b03000d07480c02800198000505100c0502601c05140e4043e00d60070305588810404980701c400082c12920f94030f4582d8500810004200b000502c1000044081c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 573487544 1250 573486294 573486337
    0x1f0905070b0318011a0d15020f09011e0206130201180b0405011808280b07021b09070c020f01020a06050a0c02010b0d0c061d130c0e150f0d15151211090f010311 70
    0x1400e004040e000c03244103e510450cd040307030950001000da41207441940100c401c00c40324801228005102070f442d86000307411200000308103401d08050410b980780bd883d200355100060901d04451035440c0715035201940100d4905c40301001d184070913003d10036205007220b150806a150411000002d4a00b1001a0301c10381c2d1940c41440000149011804201d40e1418a400c0100d001402c0580c0004080e1042440c0e10307076034106030b00800456800c581d100c0f809000500d0300c14ac0e034a00800306105440c015500700b85940030700d4a0240d02c03500700340d944094102d560710304141d002c0310310003002c00b0342141500b070300340ca10005c5a0f280c3c0326030540b40095680104000083c07030401800300d05842581030091100b2002141600e0b2040b05072407244242c00046a211041080385c0c502400b804000790082ea4001c000100d049540b02c1060060b0030a240c80d0b2403485400310b510a011142c4d949600c0e08002c40900802d00c007450000180c4058010503d0049000480c071004040c4590040b01ca02d40b0681506410 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 573488794 1250 573487544 573487547
    0x210021602060f07261207030f180b060910150309020406030605190b030c010507060f0c171e160e0603010b0d060806091f0905070b0318011a0d15020f0901 68
    0x20751031180d005135001c015519240d03102074240c001d0301c2521006c1e440e074000240c140340c03081d4402400740700b88200501410f08864a040c0c0300360720300002500d010b10302100250950410201850081c0034910344a03891501d07141244040b40e07a00d4246508050701d68403078101503030b282e0040341f0185015401c00125410005041034001183d030309050022400c051003043c8075600400ea2902e0502c080c20501d03035814140c503100c0b006086230401d4070360ac145401405a611a40100c403c3c1c00d40c0300324282c80d980e689504240b081c11104d06801c030301903c0b15600014212108042d1200c0d014015402e000e00f1964419000039500d4000360044031801501040540180805000310030041100002501c09810406006a1034a40d07203d0080301c00f181290706d1440c2c02c1015484104060b4120081d580030a03200e401100f5140e00903600c0141c805101a16070810f040c040c4500154841c0c95001036840f201d124080c0900046c0520040e1081e2410b01c40c60102001d9500081c16181307000034015640d070000100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 573490044 1250 573488794 573488813
    0xc052401090f0920011e0801150206090d14120f09010b180a180507060201021b16031b0b190912030504050402130302030d020c0915010210021602060f07 67
    0x440b50341541880000c9000c100300100038544d00d0442d624a8128035284401a50101c4504801c4018001c80c142d0151a169000f06180d050307030710380c080a160300d8030401d0040b41d030340d1402c1d1008506034028284c0c0141017801441c004080400030280b00d4200802d46404c03000c90281121203030440d24a01e02040b811410038800c001e00b288007100c1c0010b1a88150f10780e00c2d1500801046ca003911651510910070710b08078043c03800d001d180d101c0e003240ca02d141c582c3c100901030f41060074003903000f11010b40c0c0045842000300b035100154202c2ca5400d0000ca1075a120400c005141d6804000c40700f81099001c50340c2a9010001d094400741c48000e42050360300158028054002c80d070103213002c0b0140c0c0142200190b03018003101d0444104640150b04c85c42c80c0102c508c051070150b0301c0251325100b03074280c0c0c0e0b1a02e6004038600150041c210313400409562504c07410443d44580140c00b50050b040a010020080c0c95580034242e48000380001d0503a8660560100b0440c0c0e1000e02104188074010031142e041066051 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 573491294 1250 573490044 573490061
    0xf0501050a0917070b0a0221091e0f040612020907020c030d120627050f0106020312041103030a02070f05041e0e1203100806010915060c05240109 64
    0x60030515005041800400c003049502815010821035114014640001c024003400340c0281860303580d03280c18a9a001c2c1d80c2e40450041c0c413804210b0840001c20450b10303c01034038104c50700a004c0703d580d04404054103203401080061aa40a00001c24907003440e01d40d84034880c003601030080040170451042c0100400322400030044011988400280c0070756442c003168220b00c00005040c02c4840c00d9041e0f402ea001b80503903030040c60542034002c04001025081410115000181000800558850b1070030700ba03000c1c000740102009030340100105400840001400341c0d0207030040d507100103030030601c100190a5078450300f008001a03000d000103020210410540c04020201100c00f0070030300c0c0e000c40000000c100900241d40304030707965038915200040c1c140b264071075030501c0c3c4802942d02e1038182d4482038a83c034a40180304140c89076800110342d080051054100d20701d45410a00b1801c1c0c42c100707040300c210545000403079841c09440702211601c40100ca07800d041121781c1d00c6980c1c040d81002c03042070468600d80b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 573492544 1250 573491294 573491297
    0x201020a0e060304120c170a0f1b02010921050109080702090703050403080403030e01020d0905010f271b15020304150503043908030304061808250602070c0f0501 71
    0x8001303100c000b8402d00411080503001c1d00b0296080c075107c2c2084240c0e202180721102d030700c2c1400640086004d51001584108203042d803102c072100564000f95203500c0d04640b40013408544401801e001500c00d80502131030b500d10074980c84080030030503604c20b820340c1c03080316003242ca20b07002182e0102145084910654400c80c117103010451883c1c241c800501400010708050705150303440391900c1000c4401c0d01145c2c0d000c11b44a40c1440341702d20526180d07000342204800e00c150719140503600c9104504d41c0000407110441400600e10b92800c640b10703074000403082200d194000b00c0c4000002905200ca41000131180a5a00916255440c0641400074262292f4019040103001c008100008201d0f02489032051300c048c0c0f160652541c3c1c0c078011400d4010f05070340c5440d02d00c103048000404950000085200d01e1003a8024881c0c20080303c005d100031025104024129502402002a00044441c24803042c588ed8110060701101c285c80d103c003280c0c8660b109031109075000d5800d01c503c414120400700148000e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 573493794 1250 573492544 573492547
    0x20904110c0d090510120504060e1b01020f010e0a06230c0301030203010b060304031b061805030c1203040c0e150405040501230c07061d150a06050409030813140106060201020a0e06 79
    0x5450000c00144000c2041b10201f6a64008181071282a038821441165040216013028000c0c40343c9000034541d0710311a500512590006508440041c0a103100e0b21600c072009064500c0316039130f4036015041e00c10707081c184030240c2481007140321019804140111404c2420300d41c0c95055005041c25200150801e50080e40104103010000b07500c00c0d8246803014441448600c245c5044c5800c0300034045d0803004d5107503070241c0c1c8609418440c02100501c0503406d820308a5141c905481c40500b0307180003c0764060000c80c10380400f002401850203246521154410180f0034210301400000c04a500c1614141d54070380d9611f40350180c90005d051617005685c2007460000847c0f07410b8125250300d200b64140146a9500daa0310310040e1071500d0365030080c6500041c287c4c2c4d5858003148054080500031902c25242900f04000060342d81000d200700104031740c040d034910407266104070142d4468501e005084030040d4012041070749108080c428000074200319800940d507403115040003043c0104034200184541d00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 573495044 1250 573493794 573493819
    0x304060507020402090d0204055415131209180c0507021806100806060a051606150609050114040501030b030325030927020904110c0d0905 61
    0x10480103036110554115070141e92112100c0211b200203040b43d00003500941440203000c0b14a11003001d80401c2c035544541d25003d04405408c88411301d07500c8021404079821003500603401e1184101849070300180b90111061040d402c42c645d02c01c44002c5a101040560000350b090811800401c11450341109180801070f0604001040e45004080700a030010b059845540443c49400780068607801c0b500100f4003100c040410003003081a4904444c007902c01c80f01d240c4001e4080780940003c43c0180006131070704c1e040408246080c1c45a1344610000081104400d1816000803158001c07191404119290400c030305162100150041c0070a030001410b10003548500382c42c050003030041e00c04880c03091802141014405000c40e0031403081c03446040042c214071050100c019450030214006600c0390b0f88220206036104600e901500e02110810702020501d20720000103142030b00500b81c040801000001c1499400c100302e0b8080c1d00840f620f80e6940c00143c1402441138010000e00014003080d00d103101130b0740 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 573496294 1250 573495044 573495047
    0xc1203032e030f080403120f0c0f1e03021501062d0903140706200a0303050c090a0e06040501092d020706020403140d180b0706110327030406 62
    0x5048008031900d04001c003a190100240d608108010b42e08540402000841401e00c05043e611030300040d1035010070080500012842034488c2c00003a00c0e0b80e960b10407903010ba6901c629400c2d40b26541038800701600c07803a0f081c40f00d165001c20031420b4442c1e0000c0031010402c10304c1041c24070703050b031001d0240a041070f2139200c0c641c021907002e50340e43c0000401c0b82000a15207401c0e0380720500da0704050001c2e4100c1007201800b0b0744c006028400c0d6582c0c1d4807800180071140d03e162529500c0d4408a50316500240100300010380281c21590704001e000941c1d42c00c0120140115420040583c004907014090000b40304107400c242c0f1420340500039651050001d03126a180c1c480340f0100d0f5502004a856a01c540c12132001c40d04d90543e404280e000c241555903a039241440c010f0f046e000b02c054445d900801000301600d0b809910524101c190300061005c17200d00d400f004c0140b41d0048201610019190000000e544040c40011071256000031404001c13841d0030f441c1030b500550807031180907091f8010802441001e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 573497544 1250 573496294 573496321
    0x20a06080c0403080f0c060907080c03060c190905030619140705070803070e10050901080f01050a090b010e0405090a0b010f03050601050904030302090a0e180601050907050a110f0c120303 82
    0x403904907a5440c5e4842180b03080000602c640c441d9007001e03001700d03418003010010100e1300f001103541a500b21810700c1045800c00d5203d5038140e5a090040e001000074013144a8001040030f1492600c1c01c1c10400b682d03489021030700b010300441300413426840320011510201e480748541c6100910000c40c88013640381c1044007800b14414014040c1c400100440082c1d0307510b1051101b6119090080c0003040d080350a208050f101d90450300d030060114240c0c0d400102410043d0070706504a0348020103c1c1440d9203030a6100001700160010541042030b04101801c05464900403075002c0c0c003040c1d000705900d01440c200754090301c5042e04800075010134080c3c1000882e20008240e410364108407640003890305c03640f40c01d030300900c43d41080c01d4210010050000c0d502125009140c40784c003580300404a64a40c10340b1b80d5499840c24002d8540c05181741d400310f00d185110358050880c0c40300c02c1c140b960301d1055044006180c00c00f0580c0300b020503403048481e4446400c00102107110944c5403001103086041c8030a820448 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 573498794 1250 573497544 573497549
    0x109111c1101080615040312080105030c0d1e06020f0405030708030a0509091008160503010c030902010c08070303110c0604020f04020403031e142a0c0102060f100918020a06080c04 79
    0x420803d180070a84540d5109920200f00c441002069507a0b40d49240840c1c3c112003100803c80441c0d03102c1c0001400b4103001c127840b19584402400c0d03004042d85555030300c104881105003030070886900031241000074900e10081000d610208003907610390b032502c010107207072000c2c03500904480d820901c241e511082d00311060b1201e00781e0481308147c05039072381c452a0500c04203a50014440c1e01c2103005070080003500d40041c40c1516010740c02404180c500b441e0680c1503e0207501c0090000304003004600c00301c0c251030b01400c8070340d01c43d14000c00d004e24809038400041c5c102444806c00c50704a00140720444c50031000e03242c1c6018040d5025030401307144d038801400c2d013094100300c1c1e611130300164030200d10070344100ea401140d4a0810b07805a21800801001010b4043c84004016070381c03401400b2221611000804140942051780203103a2551140d0b030310704e83c10345c0c007420780384024107402c00101d56040940944d07241c0681c02800a4800d034036500401845520360390144c024007034004103000e485012502100c09 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 573500044 1250 573498794 573498797
    0x61b02010b0415051305060301091a0406051b12090304150f120b090c0d1103070f080a090b06060a170c0319050408030114030f01061707060801080304051509030109111c1101 76
    0x142542c03081f0200c2d014013841d440003000d200f0581042d500e401e1a204002d80500e01035841000341d42c1d1140b5407411031401d05448020440c60a100000d500d0320703880d5080d54410541010349050a0b91a0a2852540c0e0b802c180d69001c2000c90364240c3c3e1b1a5440500340300402c24003142400700c0181c40340403506894000c3d00012041600250003110a021500701040721001d500480317650745010070b4020901c8001c0d02c500c200141014000c00d445075041d00500700d12641040025110740c0300c840c1040100d03440380380340d24148039460014460102c1517040c82845005d0a000d103036542e2410640070881103054400a076013441c64074052101244020003134074191a20b00601c034010074070f07c80c006841c0180c3c10358507410070360130401e02099002815503a05065816141180c81c526140c50007a2801e420074040c50501d03500500c800c108920380a003402d580a50a131503501c0ca460500c00110382514030311442920a00c03519104840c0c142000c1964603a4814268520402c5815603942c0040051542c4d42150 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 573501294 1250 573500044 573500051
    0xa02010c110301140405030a09090e06010501081009020409020d0509190602130e0406091127040201120c0804050c040c0e04050603030408060f1e01030b13061b02010b04150513 77
    0xc1c00e6102503000c510b120325207082c400c40a1402d032a01395901d078081d1094000240100c0000500c40800d401510040c0a401c0042c00b15a070030280116809500107104c0303564854142e8000900790164401840a8003000c1c0002d41e99030b048004000039038401500c04240c0d036109121a070001d021020001c2d0280f1740c003050241e038032070804d103684449038131a422082c00c11b025001800100107103507206d005503c4c841c0d160b00002c0003000c410454030200328201d41b04441c40d2449503170040c1031001c02403680300744141050511b0011001401c0122164240ba1001194103003003804280242040300300a00e00c82180c2c00d20001d200314600404400843c05801d00941c3c0300c00114040c0d5409000740c0d00540191401c0741c29601d40850090f00003041a02c2c907043e207e2402d000460300c040c0d562440d605994000745a00d940b500c6a96070701c0c40742081100301b66072007680c07107440285051400c0d40c0f54844003195400865900414810002241c1002800505d01d014014007085141c490500d441040c151049000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 573502544 1250 573501294 573501323
    0xe150108040327060503011a0c1b011716120606050409180602070510060e04241b050408100216031b05070b1b060105011209030e030d08040308090a02010c 68
    0x218003034402d0f070700e03403a2030008448001c159654010f01860403548200455288009962282541d0b445580b10418168110200105846056441c41141003406160914001c0052907450340c11480035074001c00c0840540d0107690719240d101c0c07200030150740005002c008261900c0170107030951080b4031404464607180c4407020301410004c00c4448032242c0221086d99280514038102e9203c403403040b00340c030700e0614006011a0a01000340b00c03600c03a84d40b00740792036040d0042d80e4481d00f1036006444120714031500c0740c194111a03045080b6841c2c44005503205c19495500300b920240c00c1004211072143c00500c184074004c2d2390034098101c030601a4160400c071303070f07242000356175100c54040b502c0300508540318281c000521442c180000700b00d00c6074a190303888500c040f52002d0546420003880b440c0d00042c3c280840248100c1c455105c1a00c0d01d100e070510756a128501c00c04281003086102d20030001c00c1840d001c1100f89038026803540e610003507410280a00c00c9043c0d0010301258603407c009821080601c000307 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 573503794 1250 573502544 573502577
    0x90f0f0306240a0306050906010b040b0d020318010c09090f0e0606190f0e04020f0907020a241e0b12030403060519091103100606050f0703030209060d060e1501080403 73
    0x40ba03014405400c40ca22076403641800c07405817034140d0b0344546074456007000181038038948094a00380c8804000b4031349000d0a4840c00e001030340014051000c052007981c55002e8a5800740b14051030501587c072642a81441d2441c1031040312009800d010b130580c00c0184070071603001c022445d107a00c548101c0380824a6016480902c0c0a0340e00d0341c1050388600d2203040c0c08900d01a00c51611442207200b250b0102d00902218140100c094090311320710050b074403e0509a0001c0d0b403110340054903202c00c07105031010311035054070f0005648403800551100c184c0c82040c6801d0544d5406030000b0f0040985000419029541000d52380384118030005d80402d80d6000460540020602c03000c0c4600014a03083c0100c404070b0401020017540d0040d003900ca4810200741d50f80000050181100701c40c0940c036481d00344001c2d076130301c24000d5000c88012003c02d0340c20024404140d82e10000350010007003012000030480d0502c00301c441c4440c00a0403650010362101900501c42c1c0e88103408960003541450b0443c414200c0000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 573505044 1250 573503794 573503851
    0x4150515070203031b06070309320114010f0504020702030d0e010302120106051306030b010912020a0308070c150203031501030f060f0b0a0e0604030503070308071b0602090f0f0306 79
    0x81c001d5050000051850345410400f0096143c2640c074020744201d5146c4034016012509120070040c00a500105110030205081ea5001307071002c0c803114400442080e000050f402c4030100600b100e4902407203001070194140754448580a0304060b542103141900c20380000c0e07039500d40c55800c1802c1009c803019842403039100e83c054511541001130342c0c0345256120780c0094aa504802907540580c00d1281d40041c1031480790190311a55681a110b8030011400c14a118904030300c085070591b00040c014000000203161500200b041c2c6026400329000d141c1044090101d000c0e101c0c1c0c038082103600903c02c0c0301c01a242c283e0f003220180403d00b00001c18007885a180809021340d1b07804410501644a80000c5081a01006025080c4550356610000c88802d007000307014040d40c08060143e03481408180002400703403003003030f8112b00d1070305020856406416034140110510074003240c0c05030b00400d402c140c60502c414125039102c404c8032000520412100402e0b07442c1d4006004c070b40031007180328541d040c0420101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 573506294 1250 573505044 573505057
    0x20303041e080304060504021008040b010512070e010b090319020319050f0a05010f230c0a050f030403030c171b21040f0b06240a05040504020c0105011404150515 71
    0x41d105a03ca01d031134244030000b80301c1203409900a030b0660909048140c4104012441680d01c01505000359081c007003403000304031880c00142c1c1e1300c0c403600c60b002c00d104500c0c05846001b010640038a90352204924281400c04079603902007442c2c0d43d040d200e0343c00187d074003141c0d080075054800c084c1c02400c240ca082482c41d2440303c12410815002d040c044c00103100301034001c5a04201e10742c809100c1c007070001041310400741000c0c500e0400204030502046500742070034020142d0204a117809030a200c440e07000038010b41d209490450109070fa0303140302e0865641000d241c90300c2440d508a00541440e02d008020507108154542c825a81800110a20f0b18040d20344080e00300c0742c42c44425031181c030781850045200200008241c031400020b20014640d85070003d000078260322882940542c156560300080b00f1500300348850000c2c400f0601021582e900c1c6c034400340c14101e050038001300700395151188ac4504840002c0d00240101d082c0080020101030030340d05401202c80c262002c1c5400740000704001881c1c003500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 573507544 1250 573506294 573506303
    0x180e09121e0904020f0c0a021e1302090d020909030a1404061b15060e180a031d01091221050306030a08090f0402040e150118051011030f0414030d020303041e 69
    0x2042c501c0407520b00203a500d46192027601c0014403414840d80304182c071605007060640c0f00120408000d80388101d900500403610001d06441141c403810390004041410485041031140d001041c02c141c80e070f501483c06602c50f20499001b030b24140c1000c0c0020b206c0300080b441c0b940300344c1e0703050f041c101000380c0040c0d004c04ca1001d07089d0810a4a4452284501c10300c0203032510208110302401802c540000482c5000c0d81e42d6050303e5002c0074010340108851095140d000325818030010320382c006040910007942008081c40740303540d02111a603030b440380700003c65840400001c00c5418410047e041e1400509a4102d54204001c55194482400001c0429220144950b0420f00104001840c2d9001001c124041c2e0b0308002c414a103270304002c004466010b0038a0380003501c0c8180c900200030302e041000409030b07488002d01d0128030184140d01082e14680c04001c0c010103c01c1d000074108107034100308640302440d07482203024001d070000e202d000a45c1c0f4040640b0140048915007401c440d040c0e403a07210180c020760f00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 573508794 1250 573507544 573507547
    0x30c0b0901020d060f0b0412060b310b010e13020f0c070305210f0903010b031605010e060c0601030b220f060c08090d030c180e09121e0904020f 63
    0x512070203900300c04080002541040e001081900c814200401620b8224004c5401c00f45003500700101400c51388003da4a03141d652020399000d85440b01d0b00c3c1e0040804540c0070000c000a07038038010414165400c83d1844130b15010700d44c40703d6a131040000482e800c045924510000080408800034410b10115014488000a203010962004140d10046901400940744a814032090003448a401e40c000c2444001c0100f1488407180040005440005005000010b00c8005c16001c285041c56120403000c0000244008100640c2d102045001c0100141c03442414540881602a528581800002c05401c0400009121a4448407030440180c001c0d0800c0c140f0403102c2e0515030048040d82400341c6059040011251800d4041c01d41da500501d048402042c01c4c034000d41044004001c06408a42000b8030002d0511407424170254910182544001041286c102230030030a140000d00000544644418000118004144107045001c0304844981c16520340503400010020301c2103105e0301e01d92840 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 573510044 1250 573508794 573508801
    0xa4d180609030f012415052a03070b06030d090317030405121201080105070305040f0f0512040e0a0f05060901380a0306050f0a090207060605090103121403040308040807030c0b 77
    0x15a40310b4004003614071081c518181b5141c040d842280304561043c8070104604020020888200075018550708030004020308c80f43e88032422003800d5a00002040c0c50303054070740c0c042c00064502408a0100004203060034403005d440c503904d4400c4c001003100f401c0d40c0c0100100000d800d000e400e110b02d0b503908000701259555544c213061101c054240138051007007190319040000f03e8490081c42028061707504281040c00141d00c981e0b0301c0042c03525020382201c841c003d0340310024080d010003000d04043e181420603601645856800035007210b0700c6001e40290340c1d00344001c0c00225100c600410b81903030014000e4142c03030860000007112807030048240b81c014441c94807a1080728031080c0054444524141e5080c06025aa80d00700800d56410361300e20755103c00d42305010019441d2660041c2800da00c950004a4801d550700000f85c2102c05c00d0f8025500c003a20400907907c0b0550142d107180780110842032107810350a258400801000c401800204544800203588051500505056007003552120700c10000c1d14 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 573511294 1250 573510044 573510071
    0x504020a1d10060807050702091008011104030b10050f1005070236060105030a1808040303020f06010b0412020402030c09030a061b090e0a4d180609030f01 68
    0x40c01101c054821403030403140440c41c2ca2003101c01c0750051096a4906d801c005c410703000c100300f07450094130700705012b50400c0307000940140a016040fa00300051158580b038a02c2c508208614140040c80c400003425007840c140b0803582c46041100a000d070680d1f00341300300d401d1950241c0b02e510404130041e51200740744a400858a0401c503141541c5001c01c2d45540810301032198400001400352986808194140300052041d01c0e907907c5400c2c00f0200e5010100710348540c2e1240d40c4190b106070400e50060f00111207005452000304403442c010b05a40a0030361509240075480c45a800303981800134802c0e5000008500301c012002c0030740794500f0004007582c810014601d40703d4001e282c1000d401199580c02044142c00034024030b904070440d240b1002c00701300ca0b40c40d902048001c18801803032004691201d03000e00500303500903d610340c554401c120f15910070b150b41034400c0b2825070031001e018013108080046411310390107816500047c000940e001619030900b200001d0034004046060305096280c81000d8a00c107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 573512544 1250 573511294 573511349
    0x1d01060b0d0e0a12110c1203030411031606140d0e0a0308180721080c060609010b0708090d080c030d09020909061006080702011d0c130506010e01030504020a 69
    0x5500c41003080002800e402c07002d030340300c19452401403e01840d405501d141d82e4010f42c480100c10041d841078401040c000300000b252555a220b2036401580080100020401511947c280e0801c040b801420081401c0b80683c0d1601c0c00d80c080c4c8400c10038418808003501083d4400c0d64002040c05034140b10080c50030361006c1c1d89400419080d000500d9201c041143d40001640e15071036003480310040e08690341032541c80d0030400c15500203c10a1450b840014010032400c2c4050064080544050603031410400d0400c1142141070300400381400003004043e0009030720b502114209001030701e00794010205820800307668000c048c0718102a010002d2840c90440e2a5840030302032a1080714051169201e40a03066134448003280d0103410064a0b91062140900a035800c0354002d02c14800483c4c206c0705140001075000e281c106600079035004100c07461f907504d41900c1c01441d8440082c820080b80c075100d00002c190381c2650014506266a40021a066450b91500c11015054043c2e685609086110303c01101 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 573513794 1250 573512544 573512557
    0x122307170705210d050a090504050c0d1803180f030318081002070c09020909071d180613050c030c2212020a0902120406020a0507020d0503042303030d1d01060b 70
    0x49000b1006004c0800c2e025100f03840420030b241e17a58520450612060100410014002c002421030a00c400d62103800d55015611101001d801260400441442c000e860030800030a000b418085101e028400441c010b1400812650075140c92b00c5104d04444010b04c0f0b8001540041e54903024a00414111205d15001482050f10030b100803007490b030795182200c04900950035620f50058520002c40d10592191000c8220303880f10b802040b165207031050018070484a02c0061900c0482458200091880c1c01e1246980d00036070920180264606106182c00601c00140840c05080d000328600240c90f80e1018550314588824543c0c207100388c0c0b0390000704001c04107801e017248202407100b0041503940c40d5009581000101d803528003820b450f15600e0350301a4010100707a03030400c00d09106880c0503903580100c01c0780590084000e544d90b5410003e142a100c40001d840000c0c5290b05840c20a1503203000080f5440c01c3d20f45400000c0c0c10503900d040c140300100c0610005820342c00c140c000f003604040c0030010a207 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 573515044 1250 573513794 573513859
    0x4140703050919020f2416170723030d02040902030f090316030804030509091303020115061403070212120916080604030c0219122307170705 62
    0x940e580d0710003c40180210807002900f2404e540c5040c1c0450910300b00c801a0301c41c890400c42c000012104081241e030308001040e80600c1d568a94203024003c2024524100014a03900c181c905409501c1c0d641c002c0246e035400c01751030200e0041002005100b84140d40592007071754802e5540b00c1c0d440385048080d4105542024101d9626408500034610000885080800232044100303103c406441c2900d100b13000410540c180715041250303640c10354804604034400d990191a00c403c5020700d04000f03003101c7c1207210703034400307224280d00c00d0050301d420540225045048607081c0303650380c0d02c0d16400c0381040701c41a000015401c001c20031015082003060014841c180010890f03000c01030080c1d00043c449894407600485401075808600864880c0c0302d074050407070002d400c00d0341400c100148a883ca01040c0d11204400c0da820545c1d900704185030160100020010110510707812800014a0b21148644114000d40c40c00c03005030390340d84c2da042c01840d006082c02003000e0300884c2105400748207a07158000081 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 573516294 1250 573515044 573515053
    0xc01050108070618060813081c0b041e0906090506011d09030406210e03030109020748031e030807021c0f0e0405270106080a03050702041407030509 65
    0x91003e01c03444c10800c44140b041c1d0300040c0107181080c140d80d0440050b15401000e134184202e40d0120307200100034246001c5210000107141d4440240303000b100e0140191920960030700815a016031109070310060300c5d107c0194009010900c5141501c01080c1c039031402402805580000501c18034008800b42c1c3d4201205101c19040e46e8101f446034680c890340c01a04042001240e8160010341e1007c6c0f098444c7c90700200014030604510015460361f00242d0001007120b400117180c40802069840000140310f8003403140c907614003503558043c241811030340150090440441540c04d652100000c2034019604845010400085140d00380b800204854041c1e0110701010045400d540c03001650842c0031800e603c0c00c1900191800c01242c44c800880030380c004101d00e080e03461859548910800303028500080302e0032714000304414107648882d90140c4900701a4034240c0e040011034408112441c03000c1e8180b0380b055031801e052000500400301424583c051412240821405540650046024602d0700d01220b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 573517544 1250 573516294 573516299
    0x4081c020702010504061b1a070306080a02061801050d0204080a021f1d0409080c0705040c09080a11120a1209080c0f1318080a080a11030f060a0b0c0105010807 70
    0x2100340c0c440c00d940207000071002c200400005200d0710014a44140c0c0101102814195481d10201c0c00b01e00f203a1441000e44c1036052000301e07600751190000410600c0007030040100c1c2500059040d0141e5000703091001d0382d010500304c0d280e00c104202c401504002c20b085448581304c04c0b11955580100741c04900a0342501c100100d078040340c181d004060800e41c3d5400306412440d418501c1d10011040200d9003041d200c0003810300095040e80030f45903582c4010000e0230813031701e03103000c120560300300c01c0e0540d0500010030301c140036031440840c0111205802c110842d00007400040071448002c2d014051004501403c20780000308010740130513600d003501e5903a869400640700d140498490780b01d9429075500941048511815080c21030820500c1c10210b50f00241786450452081c00300242500100c0c0c042000040d0105090380211145420450b83d420030000d0b048000720b00701d00c0d0b110280c903810707c007049140020066620100000082c0144401c042e0300c80a07c020000d020300360a01800c80e090040a501 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 573518794 1250 573517544 573517597
    0x10f03020903100902030c030706080921030a0e0a1205090a09020405011b14010e030d0c1d06092d0405010b070206030c070f0215180405010303090b1c050408 69
    0x1c0d5011100000c0282241e801c08254000040c100484102e0f00b60040c45881d400ea0f5800740529401040551a02c4055281c141501d50500c0703641c132228485900d00d144441a645c0d002c0094070b0f8070921412001500090140f030aa00d0312480e11002803100031038070282d110460b0b018000e840020400e40b0500e40c0184c442c41101c06a00840c000d05000030660000d90070b00c0070701500900c0e2071500510b10000d40101b0480008d0170345c0d078441c81c061829840000c00b00806d1b18244266440b28500c2c0c03070403130000f00b1814541d01c1114840252940b2481d80851140d419940d900003e0180c5010702c2080152500c80c0584500c02c54400100030344500d00c4c1000000e00043c20034126a10701e80d00902440c51039840004c03032841070b089190140e400c20f815209400041e19040346800d008440075501c01d4482024034003450740080411481c5010f00e080900404c0066080492030056030045081d140e292440c0700c80310182c092840f081e0211880c20003051009101020380240180030010051748540c0a1404130b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 573520044 1250 573518794 573518797
    0x4030e0f0d0503030a090f151b0306030b070503041b180f0e030340210210022b23010e0f0a0603120201050105210a060b010c0f0f02010f0302 62
    0x1c060010340040001a03004021580408921481100b1100340c0506540b03d0401e00034101821400c020f035204507403048003000000c0380e07415520320710b01403210a0035565010a298005842e180500a0100c003250822100081c14884400c442245144899645003c07000d64850080301c256420700d480c00300d28060003240201000414680020351841d12145111202c0840e9950b60780c41e01c403868042505201c044031954210100c60300321400715100039003030207100180055807006003204c042c02c00c0c84000d50041070b40031602d901d1480040e241d280d90741c8114600b42c0000501008c00b46641d1030602c07480441d0340180945030610301103500c801d00c1d00180981005003070051819864050700040c4d4086003100080380e01c1158404003241c0d040e0790382d8511052028031b1034103402607511100180420f042540b140b24291000c240b0310800c05030a0030714035031a80944c1801400c4641c0b0780185080740e9001c0e151314098158000c0c0044405051414920200003566000701d000a03110300018101c54803a00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 573521294 1250 573520044 573520069
    0x1725030f09080f03040b180a0308070204290405041e0c08100c05040314030720090a1a130e060f09100519050604060f141c1101180b0304030e0f 63
    0x4000c0d445c013420031017120025000068491001c0c01080491042034555015000084d1300c13590310281c50341894410030095a00b801050481003c1200360300d6110741c0c0501001204850940740007449464a003090f00c80c0382c460603400c00d60f94003848801c0c030410140304544012150f040d07054440c1c068035440f0f400243c030258102840010001c0c0700a0020420382e5045407046030450007100d15082e80c55403018000b500e100c2c074010320b5026004036841c090400d909010390022404a0400c00c4040c81110185032101c3c5e00c21041c06142c0411420f581c0b00300c1584241c24502d8141d0440e101c5241c402d901e01c1d44240200d49412280c0039030301482805c0c000c1400341a0180089002c09100810888d20480c01414028041a03006440c0c11002036050307000c402290260404403000f1100d01d62600034011009403480c0790b0342042e01d50f60310322804a000c40c58924210350003441c0941a041c1d60000c0d4940214480e00f040c0c0482d00008144401c142c0c00483d82e110750303c0107039280c04441c070741e4000f04840200f010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 573522544 1250 573521294 573521323
    0x5090703050d0818100c0f0905030304060c0507170d0219080403060221010605040f050d020d0602280203031005100807030507050715050a0b0d1725030f0908 69
    0x141e2003580344a01800000343d11620f403200307442c2e40503010394546240c070000c5e0801344045030703840a0203d007156010824102e44074107402d20ba0011458140030903a43d21480c0300783c40410030702103101030400c001400072200900d100880200000511250940c460310464580070251040c000e40001403031801240b80442c942040c0001d0500c3c0c90754440c500a5030020804450113003d0301c1183c0c1da4002c070600c01c24040e00840c1e803210307220350411440085042c182e40006106004072a00d003001a0364001001e00720703e51160005d604c40450200703801d043c190b11a02c00c40e4003d0014000ca028a074000f0246100c0d0f40e61400000c013155454090040040c528400c2d9030020320101c2c0080c5282d4002e4100641000007450054982506a110400be41c0d14114242404130b4555050218003081070040f103280b49421580071150781036945d01c0400c00b807134404200c1e51002022695050314410401808400300320344244011100403854014101204122014007080e060384000c60010000258114201c040 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 573523794 1250 573522544 573522553
    0x120f04031b0c2601050c04080a0f020402120a0504050d0807020d08100f1805180a0b07120e0a0209070509030a060b0303041e1505090a05010804021513090509070305 72
    0x1686406003141c1c00d055064500c0d02c46001c0004201d040500c90900c40c0d1000e2182c0d080c03024140c0200c509403500a4940c4906640600052041410115400140a034040d00181c00c289091002c6030203801001c100090000880f000c2011410158100c148910b1042d8182d0784000036094042c1e40c0c40c1380960fa0340e00144d02c000305e00e180580c09100a550004a200424039043d9a180c86610900407150041008041d0100d000c0b046c0fa840d50113015003001d0301c0b000d82d14115003003080f19666281da07881d01a0080e5081004100828040c1c1c0d008801680101030501201d00c001c44407030381c2e50400d41400c9018000b000b001031390040c8901d05a80041c400200500780041e0152038000140400b0001e032540350108100000700c041e007022450034207042001041d0402c074035082a000860840c1101242400740030880e1450b07a555a0001c40c050702d02c2424000981d407070350f00104019207040d409038074560000081a250a921403140b110442e0380100f42880709035500348810b500d03a002071000400c00d520 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 573525044 1250 573523794 573523817
    0x1111c0605090f040303090f05030408012f07031d0a150e0312030a0f060e13020907020c010906051c14060f0409051b0613060c020a060513060f05070c0803120f0403 72
    0x200e1f4100064140c0034480140c41d02516440321410366215500a400c16903507441e0018811126140c0b03d00d4902d4102054a113044040e50108514854101d00074100501c4190b0f400314a501d89844018080300a0403a01c6010707120300f0307030351540020040c800c00480c501c0c180100a501c0e001400c101600c88801c40241180c0f40c0a2002c0c0c080e01713040d12909107040c1c403048080b81400082210910440410b0280c21a40030b940c01031200703448000d049881190403030800042140d8000c0840f408070385082c5002a030320600384c03a60b151041200e06060010b1801e15441803994148154041d00544040310b040c452090020704002c00c40d080218028415000145515443c54100b000c1039494100070300345629083d41c030b9410348040e5516403c40404a10095102015824481c80070406881d076420300381c3c5408010090701c80310a1142c030580c0104250b03ca401c1001a2140c015603090310b0b48002d5007420315440b910603d880303401110300000c0310f4400400040c441161024154051505074483c00070259 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 573526294 1250 573525044 573525047
    0x150e1e03180f010306050d061b08010b070f030306030b04140c19090c050708070b0f010504020a0e0918010f0b090a09031e140712030b030601230301111c0605090f0403 73
    0x10350b0110090705156440c0d0000445850340b840b81189688259000a64401e0030803044004041c501c5040080007030f220b00510a15428400322418130341c018010a107000079a14045018104642000300314100341818001085031818650179140400400e03a80744100540510004001240c4240c0c2e03510b1505408003d40768960b840803d090405141c0580703010410380b1050050f0344507810480c0c00d0f1409a003040362004213212014050f002c11101580380546200c03004045548041d007092256041101048001302515070841440e84100028021149550440001043d0020810b80a02000790000340c80306c40701d11481017500c0d8940c40b001c04c10202c4401c4e05580c2c4020241c000d0030720001e200d51065032800c00000e401c445200da00300c40e42031114000000c0c1030314090b500d00f50180e400240148444841003140482d501d40d000c140781040f20b200c0e40007034054001030800c1c803100c0e8400903010031500340d02003844000d0092598140185a41c520520422040c11180452000071725008a40000e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 573527544 1250 573526294 573526309
    0x15100603110904060609060305090d0e19050418030e060301030803011a09030106121b08280204060e01081c1b0503070506190b0a0b16150e1e0318 64
    0x14200d48a41c038144040000482c048543c1e80d0014400700390141c3d0104646540340c09025440381d280d0014201c15070344410064207000349109064800c4050a120507210003111b0b034048000c0c84001c00c184002d0301340c3c615800340c00c2d601580540000f00003020310301482c20a007044a0403a0303417140308540355070f2a0801c000590446000055031400080040700030940e003d0082c040507160805403000c520803107150149100000c070310340d42602402c0000c100f00410020070201268502c0c11584c52043c0c103209058120409213685c006d600c249400c41c00b00d800c40001c512141a111040c0c116507a10300141d480c071603281010004e280024122200c031908010207813035804000352268088034108400d955031142009800c0740c0c40c1500c0060061f0001d00f02d03016000d0300140d103505031411207000b0708001c1905d2581c0b02c0c152480400781044942c25080003032b19509541d140d814104100680340340d03c40c6440d101c06a150780c4541513401120250300c011404812120710708201403046101040e14010301001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 573528794 1250 573527544 573527561
    0x3060d0602031308030a0f05090d090b0c03040513020702030106240c0f140606010e0409030504210f06020405190608190f0c031d07030b070c050307080f070515100603 73
    0x3c00c20201070001190f01c00910f015440e140f001081150916800804440c0b004060504c00d601011100003040d40100240c0300b0386215151032039803101002500b9285201f01d80c40b854004042c1c0340c0404c0c1c2c0500503406001c0080c401c40003401041e030b0303840e04001224440130b07000495440003101850903500a40d03a1002480c460f00c589522084640c0702e44c0962101500d6445650300310f03104001c02036900c031080c1304564508403002c10668800780c03001080b0307003e64001c2800001000035003910b4900c4854100301e148d80d00000300c81001c5458504130001c0d4001d17105050080d0f000f81c2e001880102d801d600c010036100303940e45003001c5503100004071b0341d10b82c0c0d091944840e160365151060840e1001d4054420541403a480c040351540656a103022080c11394034a445254018040610000d050001c41540100441c0f84c070f66940e11503400c2644c1548501c220040c141038000a86078602c400c500c0150144a0050003581c1e00c2e8003001060401481048400300c0b2410000070051051a000f540604c10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 573530044 1250 573528794 573528811
    0x8041e0614070206090c120a06110702040207080c07063b09130309080d08011a0f0711130903020c061305030703030c0203100b030307030e270105031203060d060203 72
    0x200400d88004600c6098030036102c2d8001604602c00b0000035500802c2407880f406425500c500c01c0d4644407503001e0300d5601c2204014061911922a09640f40705502529031290300100f00315510101031411803031f03541c000d40d590201c2e8041c0e0400042c417540101c1800540d80703108010700b000e00c0342a120305540400c5080e040b51883e451400c07202000d032900c0e00300c01c1c810303400312580c4840481c441c14040c0040c0403030f60254084e0740c0b00141c1020503680c8065081e044541031290003c206104180350325081c028481c0946640d100840e1400500c41e00c1c0c80c0b01c01520340180c47c03c40340514a42e103118150f90b461071000d000340c0c0c4500179040307003400c284000780915071160343c01860907600c95001900701903580d8401c2c0c00090416040f1020b40c030301802102c200d4900c5050800c600301e00d030404a5101c0c01001c1018042c031000509000154803203046043c074801c00107152141c422401803035407144100038003541c0d0282c81058266503503204040226030040000a259034008503640d6585806944002c08058 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 573531294 1250 573530044 573530051
    0x9020303070b06060d0e011a191712030403050415030c0f1812140c0102150f040c1d15010e03060a051302031b030c0916032c15010608041e06 62
    0x80c444900c51146280300d203903070f800101303034903e440c50030024901d400d001081c0300c2ca00c210309c1040c21032000012102210729604d403101100801281503820960011b90005446200100f00800c1662010041041ea03800500e617009a0303883c0c0360110116802005c000c40460319840100305c0320b6001b144502e240040e4031030f07022402d9448028031894aa441c0804035400c1d0702180c0400a0828244000c08c0203403400e01c001e0200d0700700c01030a520b0280340604040c4121401c400810107010240b925107000d41f41c035460001c90300c1400b4103036040e42c060841d6428808490601c03502d565600c140d5403511900c200900512098130b88044003402003102410600000403942840b10060314180240c8946208083d141244480c50078141402c4c07041a0046500c101004006c1102007003026a541030051034610f40042c1d1030502d6418030803207200e000d162240300c0c13504003204a50081c0000380c1701c82ea5982405900305d240d0b66018150f80302c08040d5030080c0020311401072046290700400c0c94903192406441c010 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 573532544 1250 573531294 573531307
    0xb040b0a080a1e05060306010e041e0303090206030106110f1605061c0e10050915160c02040e10110901020a03230301030c051918150e0703050403021009020303070b0606 74
    0x2180201000c0c1d2507a0002c42d1980c013040071603d000e01807203005002000410406190959402d0301781c8202c80b030f0321424006c13440c40480905220381d100c003403b5a4050300203692942c640c0006010310f48044a0b0103610311030b80d240e0322104000803032021091024022000c900703d0030070b8100903458000481104021946900c149910540e034016040080610703c082c4c0442e1700c40303220742c000341c5a009041303181a83c02281e13440c080b60003100784260704c0586500c0d0300c03054076001c4404030b504011449010f0341c0301e41402d16020f080d03040420808a44441c4140070090341e580306070307018081e0160400c00c6001d6001071801c840807038094609280d500080401001d04019001500d8031983c00030381007554032032a40082440f003402d188000d494449807034040f1f01d515515042c640212003c41c0c20002e1714854850800401d441c0d602d1508034040c00d000141d10700c5a10303010b0300c01002031508803020342c014419114103840d810072901c034080b03040343c026001c0d6190000e5034aa61250300300c0606413540100d000c0004 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 573533794 1250 573532544 573532571
    0x304060f14130302030d14180c030622060507120b0d120c020a080d0302032d0a021803010906020903210703030903050f0c0c0102010f0c0503040b070302091302030a060b040b0a080a 79
    0x1d443d200507d01001d0042414100da030140000301b04074003102c42d588420803000d0980d50010300740d6440f088051146000c0780d1080380310364407005551001800d184c10b0109016241e074104032071424a0501c0034082240b01070000c00c1001000d4a0400a403841103801c001991441c03003540340410540c0040c2450a445958940c1039251007010342e03200001a40c0803040c402c08480c450240009005006110117003c5902801d03100c60700710107400b4a50b4154009041d21201400301081d07940c03008020000c02c07000c59281007080296020448540c402c1c00384482500b030701014220201c20200310b46201c01d007050740b50b81e4103800600c80e2050a0381485028800c08440c2c2007103000501c40b0840080181030010021400a42500c0f821011488070134102402c484001d03074840160b83c4c1c0580c00520b900d050740c603401130540c0240310f0300b20b0740b58000480c100c01d1a002403140e0001c50040c000c4010030004a0794402251080d030040f40616000324804020340c04410b8401c0d9200358200b8815800020784002481c803 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 573535044 1250 573533794 573533801
    0x601020a0c03030206160306032a0b040f05040f0e03031302040f1b09080c1516080a20030915090406050303031306110f121009060b0304060f14130302030d 68
    0x200303c00581c400002c112509403a14400d6040000c01d0405020742c6046a42c0c101c0501505510b001114514004c2016000d0910b40400010204901c04c1b6544549a83c0c03240b0380e41d081030103010b0040f4188a000e4134100e4031442001c95403292507000d542591142d018041c01c0030420b0100740d03441600d903e40c02078400c00ca4802c0d8506402d141d422103200180103036018000d000140c0c041c0000d40c03c500907001650315020100e0401c2035183c68004d5403014241d0040c0f42040807010003034210000840d1100e000c9400240c5038002000d0058065214140c13080290354038814000099000514540314007242c13a12240500101d8900420100f1b01c980c490001c01d145400072a07841038603c0340c500220003400342a101c0c07001055040c61100c1d15140034007200071124410140b10700b44071002000000d880007a032201e204041c0100010601200c0d0340d800400407103400c162000d030740d0700d880c0c09161080c1315144d20801c41652104001085555210010307417403402680c14083c0c040d070104002c1950805040d11 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 573536294 1250 573535044 573535049
    0xa050a1205180607030527010e0115031a01120b09010e0631020906091f091a2211120901020d0506090108060c031005130e12070c0e0601020a0c 63
    0x500a042d032010352580365142c0007010307003c04181850f040074002040d8110084204a108240c4540200800780c50380500406d0f00d00039800313855207040c40e42c00000c0b68201021003260b007d01480320725402d6119601c007886c1020f1050201607450400300f00300246d041d105050340301c0d08000000401e000b070030503200c0c2040300403502d07100c0366014100814810305042d400c0594071027010b105011010095030200d124024040c04007031050290307030000f6000440c00e0f042c04444510500488842681d921511b8020b05031078254022112051607550f07001e8100b030900c0044101c40e4680c0000001e069000b07410040c14007500040034201c04018900d80924075041e0b40d230040d205003000682e9402c850040030101d0f400980103501ca0104200100482c800c0051a00c0d0000c00000500c2d0b03594540ca0510308461060740d001681164035803024a00750821079024001100c0a03900ba85c904442c1c20103001d135544600b0800901d260103d1000b4046941880012903000381d041c0115001a407158880001325040c65 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 573537544 1250 573536294 573536311
    0x30d0c0309120201080a0213031703072006130303020c030406080411030606030a060b04060e040302030a02010606020609070e060406030b0115140a0f030b0f130c020f030702060a050a1205 82
    0x1441900405502040d900c0041050807030014101e1101d900007400c504024180444040d0003003085180f444c0d4008801c4000c50340180000c83d000701c1c01d5507600384c2e600111000000305200e45031840341c07201c038119286c0905e2130101c05000d1a607904903c40b9404140c90700c081e42015400e1100080c03040d0200700520190190b501c0d80d65551a05240156414540c40d969078000c1d00040c046c441c0b80d45001948000090b032080001c280f0700224404500103203440d17488441400d00b40e50a000c1455000300050041c40002d5001788501d5850b4401a0303501c4105840d401810351101070100400c031810140190400030083c004034843d039803610381a802d0340b000e80101b0501500e0811480764030750450845000100054402428215005c13801b402d1407200c52586018151907410110f45544c0f20b0990001c42ea0008005486502400c01d00c0d400410392480107001522503105100c035143c0c000803c0d100305940c020038480c42c1000c01c03d0212502d400c00340c3d18a080c451030241c0d040c00074107d400342c2c51142554 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 573538794 1250 573537544 573537557
    0x130906050720030f1b010905010c0c0b090a021f0201020d05100f0f0f030f030318030302091c08030106180f0e0f06011b0b180708070501410702030d 65
    0x2140c4603418054110118411550080045060080c64002611902c0c40d0178455004110340358035444c1d0161259031802032a07546001c0c2c40405c403581001c82749901d14060480d004442c1d44545800f95202108517000e54002202646040300040820340030360344400340c0c80054184041343c8156003da42064829092015a07040284808091042000c00420b00b81c8907011070945401c0e10402e00800601014101d1008039814070241802038001c219003444da0740184d00100218100140250402c0034598841c4801c0d848200c1c14102c681800510260040c50040c0365074641002515103006141c400110281441d00024040c02c0c0001e103070000b030815103004502450324100c0544400c2000304050306024022040908000c00c01021100c0c1319880440384800d038030348291700e1508100070f4020721002c0c07040c0400800d44540200d20700044400030b072182024440c1c40c80c4e046000c040c0e007104017010402c416446448804039178201c000b002891241c001d01c2c0240700d030003003400d040402d0340c0c2c503010444 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 573540044 1250 573538794 573538817
    0xe1c06051e090a0b0c0a08130227040b151c050c09040501060f060c11092701090606080c010c1b17010218101403060612040b0a0b0303040f051309060507 67
    0x5100700121751141d00744550f90303c0c007510550041c0410380c001e4071400e510745800c02d00c2421500d800103101c0c03802e4011404d200340e40b402901040200803003180d00b2610407d020010803032007041e8003c800442c180051024403034901c0c4408004554060401c1645c1e43d12030341c03011071201d07121800301c28000c60064001060083c01c0441e0180030411a511803420413824411120100d82c41011030417404030f049035400259103621266140e1418050003080d21100c20600031080d10784c056103c8134075203200f07400c00d128103552140100c1d1034a00013400640440c00704080c40300059000050101d1001060303c1c521300150b100c0503440014540c84a0034038040c0c2d800541d460345100b941403400103041d412508010740d82c8a545000340009a22440c2c80007550020000c102160740703601c2924850b04580326490220702e030601b04101d490f903040d204c5070085403401000c41940e081c08000c842c1a5100d010b41508102c2c64a0144800340300390407120700700c480d501d4004600290142c0526405404195642850303000c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 573541294 1250 573540044 573540053
    0x81b0f061b07080d1b1718010e091e1b0f03010e09120a141c090c0f0308030f07051611010207120b130c08070b07030e1c06051e090a 58
    0x1103030004041540200c09000101d0b034000e10b424845c410320a400d01900e40740b442c0c855403040a100e902e011803440401ea8440040d480251840f48020980e00d180076624182c0030320010f90340079505034506443c030b030200503200d1114004054000d418072460301e0400320399200d01303805c2c0d80020074200210a00000100500381440e52056004400c48000d00a4009240078041c45440381c20000014003a05020080304808074005480003e20560340c8528444030942c150802013118140c102c0c2c90302d0803100c1c0400c41c42443c200900c207981d4444421803654852003025101741600500c11010041c0030064441c3c2c58038464072580542c1e10801000840662107800039003880040e400c40132a0b900d02e84611004a085041c8960700101c81c00c0315283c42c0191814007600c280f0250b00714080764400e0310742c0040c10f451101e008000309030103075403084544903e40c410402000c04c007030355250f00b604e043d4a2860200c0c0302c980c4a40d801c1800010820b0034250607503580d202803c07040341d1104150300004003d00500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 573542544 1250 573541294 573541303
    0x30309060c051218011107051006170d05131701060e06040c120b0d050601060909110a02060f270717031314010201091a04060606030501081b0f061b 65
    0x301024180309090020010340030309201c20080c41380300d08440004451041c07540c05e610400002d03405540c0950344402c04d00707180d0f6039000080400e100381c42ca4601d00141010311a601034501442c580d000d032900020b01417080780c07643c220040700307074032103103101d80028061070703143e0007840f050300000004145036103400550321030700600801681c081ca04012016000c0e42e400052454485848040001c00e00c0200700420300b0280000c200800c50f2040f2000481c20582080001081700c072480001d0140d1080c10131f151456005143d82c06001d40d120310302080211010b559604c1e0f1290641520390b03c0c02c103090110300c180d02c218201411007500001010b000e03601022408006100c05030f001036260481480912809400c09d110b400e00d03500c1d2100140038568400e401c549078164000b49910050040c801c004044018181d07811503c05103020b00c001202c3d030090207468100c41d0703540701401d15008648981007041c0c2060880d60741c404030482d001c2107269203800180503079503040e60508981c4402018114a403 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 573543794 1250 573542544 573542561
    0x1030506010909021b0a15050c210601110d0509180105030c130209040507031a0306040c05011b050a0305030105090a05040c060f021e1c0503131403070f03030906 71
    0x406042004000c4140d800c1000d9404030307502060010790700d11013601c00003682900500109000d004400000c014810408220020003510200801a90310342c248036041c1d40c171031041c07801d04450140752a2a0240071a60081d6400318040c18054100ca6825013040c1c18031741181c50446c00304801103400b040608003050074580c11000c5406400b2194181030000b40c0e112001c02e5258441c3c85c01c400107a100070100d806a030360101380038106000b10b08003480080d02801c07900481c44040040803c02105510b0b000405034003464000d02c80b01c07000c0f400e020044410166900c0d03072440d04521035034480001135003040003144071ba00035503c098581d410803040069850010f800380e109079045c0b50622000c0f804914142084821700e0400300045070200380244e04000d2000b01020098001c1400d03000d0403c404549610031040756020404550f100000030b035000e00054032800700840d55118803070005101125800b051451900c00c580c00c140859541a0006000307110481c0041d444054078400c000290088500b03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 573545044 1250 573543794 573543797
    0x4080c15040c05060f040e0907092d050709051e0f1e010815090a05040219030f0f05032503090b030613110c030c0f0c040905030d1116050c0f01 63
    0x400c0c1c2020749500816000c0e0703010b0644200c0c8000340d84104045884100c5c2d0050007000320120f0186481c04000f500c9200364481c0044180c202a20280c00c162107400e40342901c2c0c6558203161074000001c6020004040050504003407014800d004280350740d82c24803a15036161880c100041000c144002c1c88200000c05804078000c002044448040800c0001520821042803800c141680c2e620101403108444e032881c80f41c1c114142205000c0e40c0c085a82040e4456030003591a911042513604011581e841c2c144006408903108500550000d00c5801c442c0ba0350f01e01a0003145e003002448034044c0d2807010840460148041c0320781100c81099003018070344000b040c6003c0030a042d0729142c4c020500354020134a04848555481e8860b5500450754403d95121f251000308580d101c1400e81c12042d610f21084484030000e1040080c924040d107840d01860320090b6001c40510f0501c03011031000030141c0380f08089055498014004a0301d00314000c8081032140703005100515041d14020184403000d02044007060 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 573546294 1250 573545044 573545083
    0x41502070e010b0a020c040c020303040b071b0201030f1d0a0c0515090906030f070b0a120501050a030803090102300f0c0f0a050f04030305130f0317090f0904080c 71
    0x10400181c0000c040c1122001410b490759420f0b401022800c0c0210400201e41c020b02d0541144e0b0002d6000014611551181080304c28a80b507a400130b0f90a1714208884050b584036440520f401548280c00000040740c00700004a07610107859500702181d0b44960000c81e40b5401081c0c131800b884103064085000f014159490040203a0350310b03800358035100c0c44001ca405244194085541f0362020441c50813520140c1c010b89412030f07140c80f680f10559005148460001d40d800300140b01012903486114100c1b900201031445003441c59440003840e40004088801c0c55500344409110038107621428003030001d0000d8203540040002c948100902d80c054410200c1014000800809141c0340341240c0c0d03a10f41d558442912400703040000c5406e4406c0c82108055080d01003000410540c10002801d84450715921440303400780c40d1110400200824400031b00a080c00091800c54585d0800c0181103280028140760780c80100c40e400b041005d5030a070303802c59003c040003419080340c3d84280003880710752501700b5030785 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 573547544 1250 573546294 573546299
    0x71a0705090f0f060714010e010f0e06130201051315110d08010302010509121b100507050304060305180f0c010e0f130c110d050705011808031501090b0705010204150207 74
    0x301095644004180100f452100124440c2e444000381c4c2e526981c880b80002217450f0560311580608034602c00d0100541c205451080c032030100d8011006c006840b01c005064503540c0c000c0504080b400a00182d0510000308006000c41043e000f00002a014100c40d0460004210700000c0c40f0000b00015544070303401c184550f10341c05030320295150440e602442c102d07403100983e80000c0c601a4001400f8040303032041d00d400a40040c3c00c50348920701e51004039035620310030114020a84591049890080458000b00070a1000c1e074041c0c0d1000390440c0b6030388880c0f04000c58411001d482c00074680761840160b84400f0300c1c1c802ca0b690107558a60f400005038bc50540c540e107141d003c03c4c114030001c0303074015000e134983d16648120b600c00d0300d03001d80b01c0803881c0c01c40d04100100300e005002a404207800307a8195083c039060203184a000e010005205502c86507207840e41d5a00c4982d0100c514000d11543e0400101c6803001407848500002b901ea0140540300040c3d07100d00e0450f03c5400300419140a000750740014604 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 573548794 1250 573547544 573547549
    0x50d120504080307080a0f09051b040903050d02030c0706060e06040b040209010f050f1201030b01031b35031c450209010f0311040905031903020906071a070509 70
    0x2580d40003130290405240d5911512001c0000c2c0100004103207403035140c2403905050200c0040d180780c1d03948103202e240c881e844440e018081907c488800240104801700305451504c1c0d015070086510510710445d00d4144400c2c1d9480c0f01c2601d20030344c403244842c80800c041c481c41f8500752003400071507602101c04518162040300082c0080b0170170100301d02403210210705e1002603560b1004075180082540129003082da120301d000c8804141c21700080e28101d04813840c407120b48010300c080c40169030800f1a100e081d01c50042c182c83d16503201084040c0c5240d02c40a404803d000700f000500a00300c01e003401e110b00340c0c440380c46600840c2d000c0d041240c400006045414074101e02441c02c0c00c04904031000501c43c829034208100d4075015078400081d08444c1300400002c00c0440040d040d0103903441004a0300359011081d00300002d8440c1103001910340d40041000c0b0384812584140c1c0401420310307003000f50a080a000c0050308641214034142d810240d95120207800300f105955480d4410500d007002c50034100000c02 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 573550044 1250 573548794 573548797
    0x408181f030b0105040801020a08162c06070501060e090d09050f0f03030712030c0801080c0306010e1b040906170703030903110418110901151211070807050d12050408 73
    0x8038107260741d808000e9600d0744a2001c0380c0281440c0b01c0259559141d11038010312a80e0111501034501060020032038941d4070541d00c1000403904000030070950b45500d82d034100340103100017642d60320410800888001a0742806102d00500441c91946d42d24600700c1e00030745c2080103c110b800c040005000043c40303e40c0d6100440c284001c015181034020700191808a8034601c241c0b0f0b0050096031004079003c0e10f10b640f503005001111400d5441064690381d42691507a200e04196001da4103400070001030000301c0075200e1566102c0100c503000c6441900e010400c0145500c15001542401e44a040610541c9028100b0383d01c031106090050484602d19280204111443c0c00000e00250407440781180320354a03030300010820044400400801e0032503150400c02161116207050040140c035000144d101980201100401c082d9220010804680301140c0000c204141a90840b1041440325802117070250001c0d01d0b03814420401880e15a2000801800c0c0708061031085610038201002c101c0060780000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 573551294 1250 573550044 573550099
    0x40e151005030d020613060605090f060a050a140d02040209100e031606050403030509010201020405060a0e040f02030903160219030c030b01050d080a0305040c0504051302010e0306150d140303040818 87
    0x141c42c44a401b040f440e000c0080c09080c1e016a074050320a07428000210404124540107a1003226131a101070b07079400c10b201d0b500010b4482c890030981640c5003c059406c007a0068075205100500051034560448000b0702446500c01c0343c00c0029202c0700c0e4120007030408000026010743c514070362000480c5041c80003030141c425800000c04000303000c45c0e0000264001d4060758041c20000b031450b034440700c004100030114030641c1502841141005440c0d541c0c1501071003124040d030440f80c0a9444c0007040440c1400040d10702c5000c0b138010480d291801000c1403000c10300d1000c0c51003880000d4000d49141030150354400c0c180c03c180c0c424034040ac03d5070f00154880040362018000740c10040784070365590519a01284036984481c0d0043c0c00c00c000c11003030000040210100c40c0c0300741c0740c04d10300514030001d040ea11442213840c0c1c503920045003180c449a183c81800c4415107442100340e21072004080c0c0c01142540c2003a582202d0800c0085280c0380c951800c0c5442420b0b0200590b02d40c2003517455950305240c2d00000c007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 573552544 1250 573551294 573551311
    0x19050606060a030618020309011404121803080c010209091f03061a1509120304032607140703120c1505070e03190b010e01030818040e151005030d0206 66
    0x607040b41c65802500103100500c1c903c41015421355a0101d10343c0a5402152064025407801d83d2403000140c406c5030700c600450708548072a070020040b5805594000c0d140d1540000c401030b141001000030003010042070800c508e00300241e190600301c000d100b403111000d1315141c0041c090307000b6412803030f020041e0ba4048907040000882c0e24001c03a640280c01000d402a059000003601214211060849000f411500d0094074107089078140045425203034090350000a10000310200068081d0308075407003110000b40752425291520303086a40f40380c1071003e000446e803c0c90b00520420010b00506103201c1010680d6030070150003031b100300e03a24904203864401c3c16034512a030b240042503145210b10121140c1c2a80038040b100c1c0c110707000110060b411101042251400308410002c44c103a0300c0004c10720304999100040c0b508000c03000c1090121102c0540b40c05401c40c0e958000c64103407007020040513110703503400e8413031603100d041940644900c20703101e0300300b5802580031010056145500040056014882 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 573553794 1250 573552544 573552547
    0xd0305010b04180c0e03151015120f06121a070f020a030c03021617160609090f020f040b0909070e030709110408070303090821040909020120030c1905060606 69
    0x48a006131104216030416035058411648015128162014048e0264109055010201c0d54880d81180303012100b40841e4001002c4000c0e211024023950810030402801d0400818140d440c0c0e28581080fa2179035070140c90b003010100d10032038031170340d161121a0009014900868075054080c1d02941e90307485d43e2001010404902024800c0c0761003842103040c0e440c1c00c0b040004105a8030031158420001400c400007850154044100c1803811020450302101d80036140d0b28002c0b80341600354001040380d000350b01c07200c58080100c213032400c07000d8005002a140e0b40004540b141611750a100105d24000c200d4000e10000a185561a80d000a441c0c0107c907000100810880c0c1c00c2d4082c20098029507011400512581c08003000701070308031043d203096a4403141281d03074851050600d00c1e00e01d0490310a20f84d00140811040c04203081c0364000940c001d0040c1004000e540450f202080001450b0b1000340c7c45400c0411402c0290f20180403281000d164100b030f88030300c0002d036105c690b02d41d0000303071072940300366030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 573555044 1250 573553794 573553811
    0x1050c1b0a08040915050a0311091503011e0c08040b0c07050a020303033409170102160b060a06110709020318160e0c1306080a1104080d0305010b0418 66
    0x80140c1e107880340c0e00009064403070790795086040181100915010002810390710215441c1482c00308041183e070000c983d9503c00800000340101044084c004407601640001d015020392400d000c1c00401d01140c44a0640c10700c10300d180d1008450031541b05108104804050102040540f0a0507400c000b07c944070746e0fa14602d52034214600900039a0094041c000032007042600500403400720300b264880e0b20010071954031078032481061403d2620380400300d0305246060001050000741c103481c81209000041c5010a075440302d250940c0112000c8076a510007104000141c14802201c00044c00e042c103143c45603800e02c144098548080e400f62840c075960220000e40c1c560042c64100406e50446825a00d12440c00e40d24900c074105a4015000400d04000200347c00d1115102120b02d851804580c05403894100b11044070588000f801c40404951100c103555043c07048500140020075085004010321400b100c8050190b5505900031010a50140710400c14242c024404207aa01650240002c4001 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 573556294 1250 573555044 573555097
    0x6030b010c06060b0903060601050a0219170c01061a0c031206030a2001230d0c050c1209040c020c060d020715061d0a0606020a0f1716060c0201050c 65
    0x34009001d054281051400130702041c0010040609100603815118035564081c015903061103402113080041c5c1c00400840407241c0548070ba281840c1c0304502500f0103100b03840000c2d500342c11020566146964641c4100100800c414061540000c040742407400d10000340c00c078645030300949158074600c540c40303400201a03581c03d200d044002c42e80316140c1801047c1c501004400040d0640c034890204084540010181c826040f21001d51060003000030b00e441502d64044000e4440e104070882400820f02c042c01141400780601c0900d5908641c01503110429031003004260352441481038159001200c2044464450381c0c129100d5a2040c0b90240c2d480029190540c3c0e10b041c620f06440c20315240c502d01083e1011b1401c07540000c84a05103422003140c9501c42860f0403030344603114020150341b020301c4510010381c403d80070205d07060080c1400800c24030045c0c0621925800401d503114a04d184038140c404005581c800c41400b550584000c002ca0720b00f0003c2c01100d8070802204600101b40c50f00742c01c40b0003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 573557544 1250 573556294 573556307
    0x607020c2218030e1912020d0803070509041406090103081804090c0602100509030a0311090306010807030203120703050a0c0221101109090a1d010515091f06030b01 72
    0x703100c090010400340c00b00b60030000c2900d1020900320002150208200003d191015500c0f0105684d100c000d0f800d240341c6003034503940110000d8100d8004900ca21403801041905d00614801c0c10561039a6a40382220010003080300c009607030315008154160103002e03054941c5060207042d44c2d071202d052552102482950341050f00a1401a070b4898109070364641000005495202100d90940859aa8004481c0b51b841038601c1242c0e903a040d036006000c885650b501c02e401070320b4100042840d25260410010120f810001d00b40c000040c154000c0c0401c01c01c604040002c0110003448801403411305d02250740040180c07040900400030001584040420355139156207200c4a080ca0501703c1d031401ba82c400c18240c85028100e02c00e8805494560070201c101595002c035107018000034813030103841d5030b2665084000d080c01d0f86c88130042d8203a5900300300f00b48400d208290055950340c10000f89403208004109040000404804110603280b6801003810101c07451031040d0f4286003400b107035490328000105c0b900c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 573558794 1250 573557544 573557599
    0x1081f0b09180d1d0f010212040f090c21020a030b060f12010503060405030304060b0f060307112103041b0512070923040311032502120303070c080309031606050a0501080607020c 78
    0x800323000040c00200b540ca00d00c100002c6440c050f03401c0c00700d07168218050b100901d40804030140e030940b680280030345803443d60040c41c1c403036a02c0c280042c0083c011f0340400c400c1c1e002480d003070900c0300c0700281c2010003110201c215401040118020b11040c41c155549640320b000150004080644078090f1000640d0703107841032188a0405440c4540303d14002d800240b030018000e40c010b050303000e0038038081039202e0403014103444060407890103440e603240da03603440b00d0b843e80300406083d1010046001045551b01d0000751201c68191000500081e4100f0304600300b120641000c101c07018044000c40106588648095030307000d6014184200c284010312000b9086224454036080000300603104503c08141151001d01d902d4002c2d92030042080d5102010750743d80c44181c0d070080124101a4414000a0301c506c020340e48203c0d14002d03681014025064904d04202e5181c04031002ca458508000c0e06040901c5024010840f0f44001d200b03c2c04c1031310010b52113402c141e00090041e4400f10940311504000c1e07980d41c54 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 573560044 1250 573558794 573558823
    0x50a052103041802220609060e03100c050d050a0519020d09020303030a060612050f28060b0a0e03070506090607020f15031e01081f0b09180d1d0f0102 66
    0xa0503e083c41034000390f0142903a0360500e694a180c0124215045802d101500c2c6240c079510155401d18406440d940e11841c2107660501c02c02c0c8501482102c02c0c021491130340341030f0b1541500d0780f203000340301c0c000d4403070041054140d940352204102c9170380408140312003103044903480181e03103d0f42c0140c0c40024195a95000c0c4d0188000000d2124052441e404402110030075903941c00003146250360329054a20036207684614049107030100c2d81c0c5152507502c4503500d6040350488085001c00150a005482c000d0348458980b107408500003d1040d0824030b2600d40720f03c121b02400342c003402c1c180001c01c03502411901138000c17040071840d1000c64507045102d00e40300c540101502109141c8600e8100386601c00c4401c038180903080aa81c3c5995828032800c24141e4001901900b40d03400c4045400c1400c1c0361504062000c0c503294107242d4869190405d203e401041c1c0900790341240d4a2610385240f510300783c0000402042850070301da41007c18152110300142e10b04862250952140d03200403440c1c504100017514 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 573561151 1107 573560044 573560069
    0xc07090b030a0210300614031005150604030506060411070c0605030408040b1204021c0507050f1207080303041a1315060924050a05210304 61
    0x140d040c1044e46080c01001445a1200303400648035444d0003018a40f41042c070300c4042d07032405410b001e040c40c0d2901301b40415a5102285c0d4540c5a0041e042e040c1b80c1d9000840c83c0000f48150a00820070002d0800c1c1e05c80c1e490f41030468a600060380d1040c440c91410031403c603081009001e0710211074224080c4010146401700503180c2d5132006208842801c0208408030700f5801032009844800250740120503d45061720510008204aa81c11a050f0341e030104407400140d0001410000e5030b005886030402e4416245c04900250b440496079459801084004250715000102640c07140c0e00440000c00c0440c1640c2c510318540074159241d466054801c446a80410b41d07000084240030704404001405959031113030001182d000034500c1b04007010034102c003110301058030607084c06000f0482c1c0d02c6980380d00d4980010381c00743e16910515010b500d0794220600c490b0381441914020b118480054 = true := by decide +kernel

theorem cover : BRFrame.Cov 573381294 573561151 := by
  have h0 := BRFrame.cov_init 573381294
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 573381294 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 573381294 ≤ n) (h2 : n < 573561151) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
