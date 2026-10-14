-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3473
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:45:42.152532+00:00
-- url     : https://prove2.me/submissions/f9854334-e584-4d0e-80ec-fd46a7201940

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 624460431 ≤ n < 624640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 624461681 1250 624460431 624460457
    0x9060405120f06161b330e010c050403020904080702100c0c0f0b030703050c0d15050a0501020a03231c020d0c081009020c0309151e041203110f010c 65
    0x500c101070300403801d01d02e8551403c910b0500545080641895066200d100c1d0500d03c1c03c0c043c1b00c1d4a5001e0070140041890300f1040502d2400d50303107101e12888600d40e18a0000940d0040c0f80500c10609011445c1d00e03100e09203841e54080100c40c1000520a0b01c00202c00c2004000507903a003100152090f1090711803540640c0b040c02e001c014090710342c000760f081c00042c400c01c0c04204a2001926445584c501c1e020030719507200c080d00e44450041402d10104541403450010351a10780c103074600296407081e551480c0c10703681c0308012a9184000400035020940c00c0c0401d65500e03504010307800d2000e400d0502d117481d080c401c2d42c115003039441c140c0b0102d0605034086060704c0c000b003c90080c94a1103081c1d1500801e2402c0c04040f50114255034415400042c4e030005849920500600684d07c05040045c107042d0011464100200c90b5405180c00b04280c604035100e10480d200c69005580c1076410011000191045070355041e100a225480c1000903403181c94900c0d040c010b424000e00214800d55039411104c9031704 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 624462931 1250 624461681 624461683
    0x40e0f010f080c06090d030c0b13020411030f0c0c0f0d08040b060d120c0204140c03010608010902070804054b060909040209040f0f080a09050319030509060405120f 72
    0x190b4000e4080c2e50440344601e1002d0b540d80d0140c8090f10001c684d9481600c1d0b0600d000e444045040740014044580c0c0e00c00c1050f000d20207128101210f00946052080405643d04407140e88022218441c0187c2c00802044a460010780a81143d501510464600300380f2a1b644920f40400c10705098005030b0510204420000741441c8941c003c801500e20480380c5070941d580344d503113884a20b041e40410050b41980c0055640c0d80e003003925052000c000702c900034200b89880300c2140d13000340140c8003c00c106400005035140c0c41d10880e401c0581102295003494100030401641104503280c3e1032255008184003140b1031640d41181041d12800d2001d60f00721143d100303501700b114984103062845040f0074881c042c1d007a01c86203002c6e580140c0c1100c500707480e9955450940c1a01d08000c901038420780039002090308008a0a00408440e074041d1144000380303641d80f040542c0c0341d110107020700814040005020010380908042c0c40c2d60b6000900441c04c240c0c6500100e45000c16901c21103100d41d0280118051f8444 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 624464181 1250 624462931 624462959
    0x100c080f0301141201020a08010b210108060a061703090d06020c010509010b12070e0a020f2115120d0e010201020904020d0504120507050d140702060a170a0203090c090c040e0f01 78
    0x1301500c02541070800c00724010704103403c140318034262420009911a01a0301480c551440d40b8030107445e84219503198041507503600300c101c03015200c0034517001004c1400035002050310820210807000714601a00c1d5400c0c4031600c0c03a000c81c1150619020310280b07580410a001d0548181c20205c0006a9401414100007048200c2d20141610381c018070418002d541064000030b5100c2d156034000b40e034400050380c11044520884800404000600400e004400301a000440c000c0d42d02d08021610111302c4c40800420400d144e014400941c4002044502c01d4000e006081e072210f01400014103180440010805036408841d03554000c643d950208410440c4415a02410444612704581818107950b28a0340c3c40400ca1b84c43c500380886140d0b12b844601320f0030103d40d2000d5000c0e00003a2038000200000e4606c0d070310310566003555951000003400c0071099109803803040c0410001400060142e40c18402108070150080102e403034100000705100100440086c040c1195920a9500c0d40c903112078511410 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 624465431 1250 624464181 624464209
    0x50910060e1c0b1905150d08040f0b19141614100c110703030509123a020d0509190b030f01050307080706080105090a090204062301080402100c080f030114 68
    0x40d141205200d00b100000c00d180e204203034151f54403080400d85040585050245600c03611907030000480103e00150800060060000a000ca194094258410a03240052807d1520240480510a0312034004441860400c09402074400c40c1a9030580d091090810000300d811800c45600d4400c400700341075220100300c018440b410003500045055a034020064800d44118510404019241c2103040390705106403070303d90042400034901010044480d1500d50054003140383c07144105055246110300200e100450b40c44640d54451906040780d080003003200d0344603400c500300e41514101081403c010701c02503000d41490809034089615002c02c140c5803914a4108034415002000100545a0800026419603008590000b000e035228254503005065044000e5030190030003400203410036460350407100800b903110035050311084400c01945d0b44042070720000c0d084103458520a107d07038465032030410390621071010686003882c10702c1301c0034903a082a0400d0300070a24070050b411242c070344400144d001c0303 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 624466681 1250 624465431 624465481
    0x203010e1e06090a0b091c0221090901090c0c0803130c0b04060c15022703010605010c050c0405180d0e011205010303120e03040f030813050910060e1c0b 67
    0x1614160390f0841c2c5608560703070000c00403c0da9001003074200005100400c07c42240036070400e54910710b81402551241801621003041d910404000800d90707000040b918210760141c41002d840e407a01d43c46400610740100c4c4042009000c0060100180070034000f5030160400307080c08a4014642e040010520815a000d0704420804010070041e19810207103404000350880d0180b034403c8084403044019125102c20b10480e440e1a2809244c80854034051080c1d14070103078020008652036a006652110706110058031951002c02c5030001ca24154102030703400a151208404d584410102271880e01c54400a4003010540a0501000f03030b507842100541340028813032007803225514684001c0c0c40c1c2c91044209070031041d100c00310000e030b00c0803c00444006081c68002149016600c0c103020b107043e082008a07860340c2104000000709498000c0419000c1d80c000d204090b0454075081068420609210406411501c200114141048206090b40e0f405004000b6031040e89410782040e6240084103060040c0307 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 624467931 1250 624466681 624466693
    0x417030603060f1005090106110d02060702031b12070b04060b18060d031103030108031b010902031f0e07060806040b0145081606020d1209020d0203010e1e 68
    0x19a9000903140c0d41164100c03000f15100e80310304e0498055005140c1101d500122140700009030540d2000c5001d411214080544503440d90958040344c0300c034005c2d12020011303882440480d01a026480c1c014541d4401030040b9411840069821500e50b0400e00c410f491808426042100b48029400350703844c8000120f44040700030481381c00207003e581c806840070f400342a00703803558000c040c0256025640c02c40000d0490f030b203e40c0e440316100d035030b44d000e28000d001e2081d00b102c004458000502503201002d500801519044045001c56855103000300f02c205640c9840d41088900400c003031241002900ba2039449030303c1c0b0300e40740c0140415207000855050402240300d03c400d0103001400c0440400c02c290902c00ca00640200b441c24078880340e0000d160f404100424030019240f00000f84440195400a85099035282d8441d0f00381d031150710441d00c10340840d940641d0076104a54a901c010902c0e4030062104a140782a9008242194100720305031403c0c3d4410000119004c0c110385401088440a00c01800 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 624469181 1250 624467931 624467941
    0x80c0301030b010b0304020f090a05010f0803090a09180f031211032521200708030c1303080d1505030f070e061f210605012115030605041703 62
    0x2c0100414480c0c410300c03100110100301155505011849800402000707612a824018000300080c2002c0c4650038902d16041c00004402d080401501c9000d50300502c4044000c0c9000d003000e01900b8010190007044050054503c00240880d080000d6a4060b03070b641040d10624010340c01c2107450454442202410904c1048902c0208007c100c0c5281c02e034016107192402001019200c444184c8001c080201420000980e17013410355100d80142465501401817207010407610b000144244140039101403401c00005e403a02042d40700424080140c041080320103991391715050700b142c0008502081c05500e40901d10b881d102800c8502014003421805080c920b214035042d40d586240510401075001e0102000451995414248000d098900038640d42d95891100004055041042c1c0451019903400040350500700540b140308103941040c1c40305010701c10310521039401d0118603484103581c241c551608c0303420007030b08480540045104440215a80c200f920b0918800d4800b04480c8a0141041c01004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 624470431 1250 624469181 624469193
    0x14090c040b0118081006090b031903120c021f06080c0103180203010204030807170a0f0804020d05030a090503012a180e0f06030c0409030e100e0901030507030201080c030103 76
    0x448008450000301c0c0e5074200e0043e01d840e4401609030f540140d41c50800200058007007081c0d140400e46120800c01d09880d40d461008443c2c00750321190301540041e80c40c0c000d1001285d00060038070f01034201032140b5502d84100700103a46040f4200c00051304a40500c4120b00c00b440811040307018904000e01445040c82001540d0b684550707140f034101501c1d0107016480e940719413400003600340c010b0029903a5684a0610f00031036030041e0421107801c001c101081c2103c51068098a8541c001e6550358050f9042001c012030340320340d0240090303034807951032003003040080c40030030042444001c20b84a01201c03502c2c0c081018210b0300400781d40302e80c100084d032140c01030704059040f1042d103100505081c0d460988407140a2144e40c00d98203c241c3e00c00200044c070035543c104848003449000110304071149080280c0030f20044c3c13101410000c02154601990b02014035000032510100c10451410000b452890000220403170001c2e4000d44031900518410310541d648803001e0343d0b201c6101030f4818035651441da100 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 624471681 1250 624470431 624470443
    0x51306150c022e0f0c061508060f01031e080c0a03020c030708070f060f0c0c030f0611090d0b0703141801060e0114060d14103002040c02011e020703031409 68
    0x40c2e42000050524104e805014058005c16190000760820850124604401100b0044d00071510703588180c20006640c54807242d00c0760306036684507039140c500c003030044858144020a003004450880091005880d034a0b03003040030489040c000d030b00610816000c50300341400c04255811586607900034041c2071040c20300241984044850742c2c03502403030207031340034408496405202200505810100c2000818069044640702c181c0340104402c10103000106490011885000513054000e0b00814241010408000300c0c0f660240c0c131410081802c51208401c028983e4084038040c00f801d00d5042e0302d0351040c40900c07682c0d002d0101140710b800b41d94100030340e10b4090020400c1c0d1900c82e446c0096408082c1d00d10f60060038944406011845203400e000700321005900301c5000d0316503505040715a5020351191901580c0c0002407084c101c81c002c000d581c080c1300241c050140c08005564071107243c880202c0880c08403402c07901920000680f51200340c50b008068500201080e00e0b002000b4003801145a804501 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 624472931 1250 624471681 624471769
    0x1302030f0f0711031602190e0a2d0b150c03030f0c03060a12020301060f06020a051204060c02010e0d0b0106050d140c03060112060b0417190c051306150c02 68
    0xd05603017401440050910040602040800c00f2160301c000750240d82c44076417074020569600103202415524401e00030304210080003005001c40d800c00c00110075100da2000b1140c89024104074000768010b4008403442e44410703404005039100000304070780c071000c04000d560001281180d007842d40c00c0c424001407000c40780c1d0080144985c0c040b0030003411075400b544010000d1502d038141041d070325540c0b04044d45030303c4828402e6405004442091503141c0300d8400b101d0584400d07440e581000c80e069001143c0305400c2d007901682054161081034089203800742c24070f000700381598485d03546010391aa035200356030340300070300f502d040300c5480038002000d00c5003080e070303a1080081c81c00e010b4809a16110b00d01400c890780c0030b4006150001004074000c140c2c0c54201034400c40d40700440c0c1420701e0400c4e9108503407000100c050a41c0c80c51207801d00c040d1034495690070344030308445000b1a030a0b841d07100c0740c481118100c00e24004500d4451005046091000201071102200a110080d15581c2c00c85031801028101e0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 624474181 1250 624472931 624472957
    0x31b02150d2a082a0702060c011407230a08250801050a14030309040209030708030f0405040c020c010f0503130f15200901050304021302030f0f071103 66
    0x161510046415403007441104814064182c02200700030341c003904503810418842c0000c100c1c50000314800034044a4011900380c206081a603101e0400a2119503044000700f2a0f1080d0100030f0780040074024000c5407040c00d101c160205c803e0070502006841c0c80541004140a40c00b5100e00a4008411320183c031051001424400070607a115146440314a040c8041003200410040303011094545c40304009040c0c40090340c038000c1450320740381c2c5215411410000c895060748108000d1181c0e007416006840b41030b07400b5003280c82c01031b203801855003550003540002403d004084cc4c00c00040c03501d401524000344850028200030144400001d0022010300050b40030301c14004003040c87d01002e01000992550020320300301000c1418138001c801d41100580e0610700302d042c07110a08450b1560348103100c030001d403200c0440c030f02442000152800d0b0401001664060385803c0e81910940190004510403500c6440c566520701c0c0540030800004000f40c411010012124400e46003c81c0000880e500c51141007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 624475431 1250 624474181 624474187
    0xc0109030803071206090e070302091f0b0f2b0f0203010e04061a13050a0608070e010e0411041803090f0b0d0b0f031213050d02090f090f070f03031b0215 67
    0x6680341c009017400e9444040a01e10381460041400e8010560b2002e80e442115400e00c90340301c6004445803103080c00090240840140010081c107940080104802c021600319603041140002908400181050100304541c4500061459000c058840c02d07202c90b102ca4021405c65041c100c01d01c0090310003c10090043c2e42e50383c40100a0245806441840d803070003486d0106c1030201c3c080b140040d000580d401c605090810b00d010411480105d000d4003680c00c0300c240590035a04e09490054a250050b1042ea07200d00c40c203121032010b0310f80b80035142401c000f0b0380180e14100c0031440e00420f6480703960302c280c40e49200004140031980050f0115034041100d150041000e1200200140082101041c44c5505d80704a404440310704400c1c0c4040c0640314140d001c1c0d0a004c6070390f481406070888242d80000d5010120030f00046400c2107011115402c905240119100803a00c40300c2180f038117282c0e801c60540910314840410405501c4298904d8203103010803010095800d65010a81c04035000108074006070000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 624476681 1250 624475431 624475457
    0xe07090504050603070315060609140d0f060f18021806010f03090303020d051f09050c12040f14010e0705040905071226040e0a0905060708060d0215030601020c010903080307 76
    0x10449003019580190061413664007c10103000240301c58400c2c2c01c0404d5100c100012080c0800500b202c2005015000e02c01400c92551000d04581e8006011105145d440e9401300803084903104840e00c182541c5581c4400c601d081c010409184039140b52810000074220402000e03907400407041c19205201d04003c071322184180b600b035000c2e0084040c1c8050386e034642810056940b0440300d020300c0401d800c40d0741c0a1803a031503083c4801550700c11181e100e503d11007001071007005074520905590050280101048080407951481409203075052280c906a440340e1000301100006c0c003404009210498007044942403950b1456142c0c5650705c510301503c100d030b0441d0f40c1440b03081c4048081d160008110340c00b0380800d60b00b0340c04032504140104c0e0365000c0b0010005d4440c0d85a42f041545072034000d0024102c542d0342c1c90040f217006030020320b269000350b03c0b022182d0045c1c54110100c100c0b082164161034403864800c000a24000300001c2c4a0304000d00800104086044041201d40104152501900c05807075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 624477931 1250 624476681 624476683
    0x7050d11030f131409010303080c07080705150f0a06080619021b1b0103021c0c050904020a0e03010c05040f060f030b150a020601062a05010912180e07090504050603 72
    0x54514042c0c2d08100000707856409103020780016098501d182125900b81c0c07904424022045024000100415011404a2122644007014003981d0b44266040c80c90300d2941d035507190404020000340d501e50f250000610980241c4d040d4241d510000080c03080000340c0c5071075074541c0c2e2800050401003001085210843c40b065103a01254002d125490300c9602c00000001c0e680c0d0f031120354002200b04180c48040101b42d640c800d000b00c80c4214681c1c20000d01940056030749900038400b212204040c060100700c410a2a00e883c0040e1105241548034400119410310905003034840c80b080f02020400d0070801070241c90700f016a44015917149140946140ca003900081d00105038024900b58840008460740d000440424010440081d8590175284541d80e1500103807054814000d0941200540c2e0301074080404078140100681401070b400800c009140381c403509a8105c2440c0b4200001d01d0762003140213003e0856840b84014500c080c402c200754585804002c109503464040d80c0e2007607490341c0c0880c1706954 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 624479181 1250 624477931 624477937
    0xe0409020907080103030807141902070f091d0d200a05030403080408010b04050c091323091207050a0209060102150106021c03091e021f0914030307050d1103 69
    0x29019007940080d0506403005429244244000c8000490540015500a109a01c0300a2042c400c2000b1800c1c8542c1410340400c824000c084442140b164000000c0c04003054803108004000d0240009105191024603011001c084a0440c546900c1108588402548000d0f40080c401c0e00e440240142c01000c9420360422a00503c05001c0d4800030601109009040b0028012251044020003c55a0070301c144006d5803822219910700d08024003203032800d07003400c082074411142040800200c1d481e1701e5403042a828a15110401002052820050340000070040e011491111107101da0419070a0b030b50b61607550b00401002801128400082461b80e40201301141990403505c2c1840000e41c0c4501000b50741c1c80c40c443c030405081e8040500d01f203141d0702a20500b0740d1150400c0b42585205184d178944480c803001d0150880e00030080d144005c8003c40f03038001b018040140da45da0076020347c1c5404141004400c0701a45640705c0e801c1003144200103000016401c02244c03d5040c01201c501c3c11004040c1140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 624480431 1250 624479181 624479183
    0x1b1401360f060f080f040201021f290103110322060605091317041d0c070818033c01110a0206040c120b150a150203070624060e0409 58
    0x103241c801c0202e400c030f8106980e14030107505561150f120359105090140800400d41d0003a01682243c140c0300c1c118458007079440103a4090900218180405895250700154600483c5524016140b15480c240d0f9050151004000d01c00c1b42041c158244545441003610a101d803a1a1400c03a03e070004040004681220005100082c06051180f400c51400100806081012a001c1020b540d007484051035490075542514034842000580d0314110070203034040700d0042c005050700142406640c00299409004000440c1e40c0d003078910352480340d1400d2514101124604000c0d184a034a903c0c944560440300c42c0d110a030400d81c050100060408101c1d00528003541d0401c4002c900040070070782c00303030001415070041c0e00ca54481c0c10003550720342900301030f00303403012004014504850104514851428801008a0006144000e0140c0d1260031240443d00d0890040c00350b00045002020710006110b21036010200340080d140d119103910080c0c0c012015406144107021f0101803003d100c1d1110740c8000846 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 624481681 1250 624480431 624480449
    0x141f030204110304060b092734050306070c0305030601120501141201020304080316050c150702010c18092f0c0d05130e131b140136 58
    0xd61030b04580c0042c03550080314240d81c65801c04050050321309189660511034030307c05000e90001040e052001c0b40c0303481c1010114903988a0310f0840036403080d14000c0c96200b80b07085005d411100701d48100e240386c1c20038503501261094120108024086400422000c3d60b2740e40b42c6030207941da51300c41005842e40d80e01b0508070803441f480e00c00042140c8601000303040c41c400d400c07200c0c4e4107045c1c0c040f131030306090340f1044500400101040c400b00e00001c0e50390000004680180c10810706100300c45a6a0340b514002c2400c40c3c0443d82503c041c44a00d0360280b0514030a00c445140c00702c406064000460025800c0b071003291030140d0380303600d10b08228924521810412400c20b06900c1c40d0302c40c0030100311160f04aa100080580a980612030181c0d01500403910920040c44408008900e800c84048100e038005208504074804a508000091546070b500104d440188400b11111401c102500b0381081900072454184401848039a00303801410203000059006244216031581501d89200a50b00f62a880200e00e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 624482931 1250 624481681 624481691
    0x71209080c0c03030f0906310f06050a080f070c06021305010806010804110d140a034b0e03030a0906030f020909040b040c0510081801141f030204 64
    0x2042084030081020340a4007003181c10340c000280801d61207202e200341001c190501002200070703130309054000c1e040900104082031181d4003400c02d030080462820003100400e02060300203201c0034440c1c11a08016220a14000341060389001c03004c0e01c0c1850191440c40c0700306049000505907449425101c82c4035038810320940d00c542130440c100c0000101030150134041143c0000085c150b500c50740300540b00341e4100c0d8103662100703540c1d424066903072440300c82500c4c1705100c0003051940c04410851005400c2c80380c0c0e9405451b4060584860b0103040320884202c0980c1440c800605524958449941c540b0b0413800d507601c80404408103450781000c030a2195003500001c141c5440107900704542100312480354a0501c4000800e0a940c0301b28480c0c1041c5a520042e50804a4085a00300e11616405072203103881601080d29000003074030300403080802d04009a050070406c641034500d0f030461174200807c07030020700044040320003050742c00741c0051200125524140c8940903100038840b04100450b005041044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 624484181 1250 624482931 624482933
    0x30d0b0f0a0f090614030307060509010207020a0305060709050316030b090a211211070305030a060911070302120403170f0d060e06040b090c04090f0f0e0604050f07030804060305071209 81
    0x40303580591081d60206460104c001944090701901000b8400008000d585410b43c40d0f0b54000040c200034210b0722076598240210343c01070b1100c20070840518085c40c002c154510304480002c2142045421250090700022800385500c444568400e0659511a0000c101640c41150b140e1070100ba0703230707000b0301214000b803504405000704500201440032183d903031420394032494101805655402c0ac0801c0100010415240401d20440107140c02c410542c101207034981d55080c80e403098030713011140d140d07680900141031802c0503010040020009100d030106820319185456840340c518403a0304403149030000040e219911171034001220480c04034008104181510b030201140c0044003201d00c0c90050385008800f07161840c2a642c0c0901c02d000ca0399034246490704001540003e002245031800c1c18981b03034445c80c2c00c660300c140a0303010340780c2e528002403013289045d0402074540b5100c0021041e50f40c10610003800441c884d40211000c1d00c41c14100850340d07444103003003125000a40901d0402841c9840d040f50 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 624485431 1250 624484181 624484199
    0xc04020a0c02090c0a090b0d0e010609050921030c07080c06040b19090b071809111e0307080103030302130e130b0903131806081002070203010606030509030d0b0f0a 72
    0x1007007103009458071400c60b5903508501026204240445020540754101041030b210350a0041401d02c4c5068000718521b0400e030140b909488240d0800e200058a420030014810300c10000981c407040010403800c002e01c40100d150b11a40300c0a884003003030300e0340014140144542c003400c6070030590360f580c200c1d006c83c90141407101c00284113071034003030030003080400000c00c0111038020800080e400010351519504c0340d00096442845520413400203a0b0b00e50710015180c1c0043c4200c2c50100d54000300d0681d25410b03184c0007100100c0320034440e6100d480071b0040c407100a40c0045140e0543e94107060050790345c02200058211040c403035211801101ca18400c00002d102204d41010825110380e458040c42d407101d0701d1268882c00340c0e480c604030b14074800a0402c507400224520038059004450002416602d0b525914101031503101900804c6400090705000c5050034440c05c8001c110030b140070401401c2100c40303151648543d101c40c8900da521581d44680320740e1100c50461001c4001007004010a03641d2a1394 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 624486681 1250 624485431 624485447
    0x40302090702190b0405100c0e1002210915040e0a0b06041a120604020412021c1b150806010e120f061503151003082b061e06080c0702030c04020a 64
    0x100c440f03014401140b04070300d0071f600403a15512a00d4803001c0060180e0814440f1020100200303008620030103481a5210070005403100c640c0114100702030b41c5581800c00d100640080781c0041b000e240042108102d60b010368529184c0080b20f07414040352000c20440011920300480d0815a800162099005209215100207180d141c408030b1003010b10b5518a802c00c400ca0150707200341140c18024031400030040c45c1954001c154080d0440040c03028020a40b2b4916401d8000320781095003854441d002e112009241c250312340904024605a1001e2500b580001c00400201e40414000c10030380c142240d0100c2c003446804514202101200c11a01d80346000e0340800d904c00040b0390082c01500300d9680d5a0340c60030071851041580744041c80145180d9541c51129034061241d80400619585480303102001c249240030100c0485580840c0342810b00c507240908005820400c075003880545010410141c20910307035a072040c40380d48850b0310f440350303800440e00b0b0840d06c044496000344005040f034140c0703800541c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 624487931 1250 624486681 624486683
    0xf03060415050a06050f1c090309080127110d031d03010504050a0b070c0615030c0b1e0c071e090510180507170906070201051b040302090702190b04 65
    0x2090101800e580e1004242140c90300585800c01d80f0800d05211450140e0014060148070179111450407089010b240041c00c1d6421900400c291612005402c3c15032299200e400f50070120001c002420203032100245580b24420482080c40c250801c0700203019540d00300504c102c40152804102400a10f00201a01d0070002c00c2410041042180311784c1c0c0c02d05114171881070398480c00410148030540c44220030407000a12940c01c0020002000b000101d9030b014021949444541c103a0402c0d0844ca0724154044043d0400c016100d028007180c00e4001104413500200c00740624071755600e10500321000d060031741c00c0d000407000f241019644c141c8a031032170394030710101c0d5130150080010342c507040d080c1500440300307204074440f04180c6564240203085075444203070000700728145001006800240e501d42c01c00121941070940d0060410090032603028042c0300d9003c2c4611414552000c032a1021030510302442c040603014a8801e030015610320b00800c0101c00452100074481c7d00000c507498000701e0703110102c0d0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 624489181 1250 624487931 624487939
    0x60702010606050703020307082b051b0a08060d020103020c0f060412030603120302160c0803070c050a15080c04050409150b0102010b060313030c080f0703090815070f0203040305030f0306 82
    0x1d001402c81d101d80180e421265056000e140340007165110543c0940001018100410880005c010300010038121010034405405012803d45440507040e0400c018001080c0c0c1210b0003082300d0103240c0e92101215501c90412a5811480700740c600048009014840e0f02090b98400c000f101c0504400010340c00d881284210071028600005c0042241919442c4c0720003490040c04c03420400e5014040d4002d445074000000c040d4040074240e44500e40d02c1810b950011445e0713080060481c0070b110000c07402101420090315600d08561804c10180224a481d48440003003000c0200070691420a4008560080c5001001401483c2c0b00f410250b10481d04014400c641a18001d403c54040d40107004000c0d403044001c1502c0d00390740d43d02c3c46110b0f6080c001c0d4012810802c07864802030000c0d0121014201c0d03803150503803807070b120f4034207160103030144002e9008040d565200954406915003010328540d0b10030400c2ca81403106010210082c1c0c40e46c0103680008200f400081802921081c1e010051841150111 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 624490431 1250 624489181 624489191
    0x21306050f04061a03040f060903050306040b030610091512030503061806130902180a020301090e0106030f0809121c0822020f010909020705010905011416030c0e0301050906070201 79
    0x1c104402c4448502c0780200454011004030308801c2c001014560107801098207803012030940d40e0f45800c8840b1050f0071808504003005000450900380710719403802105900626550402c01c48030012400b0901c42c804259403038100c0311003118041c41860340200004507a42c5255a20b42c0341c05040d03078004442c1240140c16081444d515848075110710b40c02090b000c1c01890040002c1c0f00c17544007030b0080140c180d070000c058030302c07c040800124811922404481c8030058595041051100669a10103041c915980c11705105101040c03c0701c0005105540c003503007103a551030311800414034900c042c1d0003003203050140f00100710304109500ca41c90100c070900c0d51100f000e81d440c811100480500410400c0340003002c420138600600b008100c04248210504040c04082d55402c455400e03030317100d450101e45c00c0e5104d6044100b005024000c44003482c801c0540343c071715032900e00900500522a55074400415403960300e401da079107005524040c12210054020701003403130503200b815a100c0003520034000541c644 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 624491681 1250 624490431 624490459
    0x914030a0f09030b0f1003150b01090506070506010e1f09020903063612070510050c0304021e0a03060908070c0e0112060b1507032601050d060e0a02130605 68
    0x9418107600380e0b6413003c1c15140c80d0319058000c0100c910010034500c1c49510102c004070103d1403c2c0180b0070f02484405020602e468010001041800c2139440039006020500c20381d8006040030417490b041d5104030362103101079034541403a4035120400c5180c11050212101d4003040300b035120740041c0f41c800420317400c40340345842e0120403903680701c0d0b620180d9202c0003440c2d02d91441c2c5804c0090b003c14501012003218403104c400c80382001c0c6948003e000704e0b40b540c8074040090300090716000d4164050440010507003503107015000b08050700400c8440115260740d181c2512416680c444655010b147c01c09001c00186101c0c0c41c00a0703440c2e109510548450703060120000e2004241881c180c10f841e0b4441ca44082d8914580d9400e000d40119001c1e02d03800030228100321192040702d000707000183d004e40c0e56000b000a0940c80c81c100700311042440200c4012140c018001c1c1d0300e80007010f60400c3d0380314000040482405943c41d041c001c407804001d42c0300481c407044503214081c0742c00c20410b071101252a07074814148 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 624492931 1250 624491681 624491687
    0x9040f060b100509060319110c0106150c0311070909110f03070b09190e090115150f0c0602070b190f02190309080408071e09090f150914030a0f 63
    0x2402e80c940e40020020003000301e80c0d0a040b40030303581003030f4400c42c49403030051402c01d41000d5845c0365058a40f400c00204252061500074000c4000030032a504c100c84842582c070000a2004d00710404c094284a00121522049501084208001c001c041c00401044a6603c1e082400507880c01001d48039140307400c4d0b140c41c02e1030045000e401f240c04807540b851030700d03101340c0500800c030202510105d070311800c4020001e0640d032011031161046c003854000150010400d0301140d450449a00b0464200300d1000d800e140403500440c1d9490385c40d01c1d41c01e2050340c050042ca0700202a1040d800001c000e29001c00c280402da9801103424003100c0c2141400f805030302405e00f000c030124014140d00e46100c83d0309100c41290350b4040d0348131860650150364040d1610391a804182c3c6045100d9003d0078a8403000c0da00107103218403800c082e01c0646140031007440400301c40c1d26001b80800240c100604a83c100c1003540003005501c1c0c4c03281000340c0c3e00610740340c1d083c10030100d010384a0f0405980b10000c1904151900c0f810346c8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 624494181 1250 624492931 624492949
    0x40303030b0603190e0c04020c0609010e060f01051e03031309060504150909030e0d050706021b0d032a050f010606110a1e1e0c15020d0c0203010204030209040f060b 72
    0x401c1450184c0c00701c0161050090400700c00c8003051801520b90a490300d441c0d50000704211560300009010a0031700f03071480c90864410954800554004070700744140308482d95200790442d20100c4114140c1c400c400100c844510381800c4a03945840300040344c809030b4245480040441d80714400400005036038109110544080012641d0450300c6010140301c10846a0300140509003c2c1ca4a01407504041d030200b640010002d000782d8103688002410401560b041004c4001c29400c1c3d00300c035803400c102d94013050030328a40800050500800e070b40407111400803e01d410402d401160003100d805501c85c140541c48510400300003945e542041002f05040d0b00440519440c02041002441c901d200c03902c410195603132070355400601c01c0c0c0342e010f58070111700c020425250695a00c010310110713205134a801aa030040c280c0c400c80041080d807400c0c01c642c54002ca00001e41c01c0550605268212082c4006030080c403a17504029440100c4009010521500c8881c460f20350b031140c1d00400400c003c0c0e00400100300703 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 624495431 1250 624494181 624494191
    0x4030315082409120c120406080103060501060905130f0908130806060a03050c090a060e0c04060305090d020303160c1b0807060e060405011b02090414010c08100501140c0601060203040303030b0603 86
    0x10780041500221300303860900510000c2c1a4009851201059649811040e80140e01010018900400510074040e51f4411940102030034202000c001349401d02090004268400e0801c901d0351b50300803a0307880341d87e41e080b105403598041d00065440c088509a4014580c507030007506032a204110004600e810047d40da801a03a0b00400100303080030b80c20007001403985004140d0f40c8680e44070000041e0b90113018900c1d81c00348001c04030b01342d111410b04d8070090407181c008080b81c0c0c03a50700c40c03010784000c5070b00442140e8000e5907001e456410481c1c80f08082d40e90400c80c00000b8100c0b0103d408004201440001d001c096880c0e20094806c03103580e414044070080031070a4010b9001c24104010881580500803480d19500258400390600282e0703000070f68441c00c1280d055407044001c2440385c0c5503100a2241c0144601107040030400340c140300814606a0049015803070610840300a1104070f00c81c1c15081d0740e030301e15442048900d20340c5c685034000d44a80052004130080780c20140c8000d41d40c5400b405a038030032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 624496681 1250 624495431 624495433
    0xe1609050609120f030a0e1507030c06022506060501091d0121080d0507080a1107020d030c08040f08100203040510110405060f04050f03070305120304030315082409 72
    0x1c07118a40401050f0100b40154007014030602c5014294060240b0152440c901151110a082c00c02403080c040d213050040100090104200812000250040a60342c1038607002100140c450010b03203000c4003000010310005944403044140b01c2d04029864100c0800d03101d003079840c680307070f40da413a40385104210100f42c0c03801190002d00c0040c04040702e1440c0c018000e03108450130070640e45054a0382d404582c0b000c01d00e100116141e40c10400566041f644440c0c21019190040104010308074005c0024066104001d11980501c0c020005251141d540b40032515080000075603195601c4400070b014100710f109408140c02a14071500c10304080f0b00c2500d03c10f40e040000f03820740c03d1006020781c00070500180c0001c00860706100201703154481c1c1c070140c200280040e0035241c0d29810007041019016102c5c0e1002d109502c500e80500004402040e201160140c410125172a40c0707651800b50050b040c2001e8080d916003500000042104000030fa080820480700a64641ca02c0b1038084900403202c100d0704003241d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 624497931 1250 624496681 624496687
    0x906120f081e0307170610020a0303090807140f071508010909170d0b03060a0e03041a07020301050f040201080a0614012105010806010602120a02121b070e16090506 72
    0x120740780000030070140d52400d5504908003034104800e4001d400c2a40c0480c00103039820b610750005003108000a0300b090007202d900320a003544100095982c584024010100750300c608070442006a8170080d41d000350b03448211001d040360000400d5640d56801c0308400014841e1907000128a50824441190704045a0b240d201d0380c0c1c20602c0b100050400c2200c05c9803180801c030403900040010388050142880103103004510003454008140ca0700d80041d190071601807820901c10b00d8640004212422503440840d504548000850044403d000d05040030350954200020040c5001c940c450b50b82c0320714401d0729120400d8648140d0041202c0040c0070316518043d501030542c04540c050001130031042d106003030701d407a20403d0604180c01d41e1401c0c2d00050581d800035005024154042c841050103484940040b801c3c80c2078100003d44e1940303d40d02c0403100000019007200070b0100c03c0c540c602d10401800840754003e0f40c482600c0507400049030100328078015980c84a041d0b51003011420210780000b841c80d41 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 624499181 1250 624497931 624497933
    0x1009080703082104150e1504061b0e0d140703060c03061508060904030e030309041a030f0f0601120201031107030903030e151e070b07020a060f05092a190906120f 71
    0xc014000d10f19086e41602c41c00303144440d603102c0420368500c84c0c3e00c44c50002c213140b002d0407020a4100045021107044c0103881400361202c0d200d03104440c1616810000a00f124401480c51500380103081d00048c04071401c2014042c4d0594258200d0400c43d8500c0340000d10480e2000421900b881c8140c5a10740d100d03412102180c04a44101486411480d00406403460004914002000c8900041c2c41d403000085045441c1401e02d024040b03c0c090f6504140901036286122002c7c0d070310352005000d180800071a036001c04042d641b095000c0300714803040510f01580ea60117400d010b814050240310440c00510343d544031215a00340100340a8000c2c0341e0102150805400d40310020184c1980e20307510300044414032070030005c00c5403424164001c01898005d0192100c19050100c00c1c0c507901070100221504041c1130018034a0001010852002d4444c80110b0154442d00541c04500800503031035844900c4051142d01c003070f800071121040324035080d4208045a030781c1c0300002000c0c0d15002c0c0070381031044000c0404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 624500431 1250 624499181 624499223
    0xb01080303090d053c0d060e25030c05070b0108010b040b01030209100804140d091502060103120e030708010e25060c1b09020304060b0f090903091009080703082104 72
    0x1c84500780f040700c114410310802d0383e017845810442d22158034544075181000040a40034403950840d18980c5100c602100c090f42d4030b10b14801d80320401c0105952100c0c00d00b241c52090b0140d0301000c0e401065000d4175692020a103010349801c10080f413140740361002c152203560007803085465950b0081d041d42c90b00501e441d800c1c0c0c0c103d43e00400c01d4492240f140d07002c50301c2e07a0317041c444012282d905468030340c110350078054980d032076000003040324056600030340c0140041551600c44507040005403800c2c00d040c1740030070086030820181360310180503503081154030222100049005040170000e8900d03100090000b40403886500e42c80c2c070884000c50701310340940300869145c20b4504d102500908604003040d40c4c91828100701c0c0c0c000c8405407000ca44d80c0c5030505c0e0a06d4550700d01c05004204545000a03420000d640c00d40f28465140b025201e0001d66104c5503805020384d4224004105410036204c01035961f00b400c22650340440403102c4001106004980c514030543c40103401184c0081c2164000e042141c0300c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 624501681 1250 624500431 624500497
    0x130b0303040506210a06050619031b0801330c020d1502040e011e0608100305070b040807060203040602120f0c100e0c0607080d050a090b01080303090d05 67
    0x1a0580010000401c0030303214000208003640c3c824840d5a0f022025a200c041e030201e004c0e006000c400d0503da801c01141d42d49205403002c1b45014110b19400b0b07442203500390000e00c45405400074400e01441480c2e00c1d80d403c2498a4100c03424411600480b55a050b08601206e6440b01c0c60741c0400849070039080035510820410101c41c1c40a0100951040c01e40c840c012003180c080f44000c1000c0e0001414420f044003040160f00401d40b80884808a065440116000d0300890180d0420080340c0300000b003144c00601902c6000f56048001e903800940c80e28501c2400364043d001c1d03c00240309125000034414030004c11281103070354640c0501803645680408652a0f40601618101e40400b03200e080224201484007000c0da00910b8000150344040342031590602c403500d56054813803081803203400c0210710303450201d59089504080000b440d903510340401c07008000806000d4642c110300e80001c180740ca000001507014101c0d0200319900d450001000b22120300c110042c0001c032851010703034032955031080481c4d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 624502931 1250 624501681 624501701
    0x60c140d051012080307092304050601030f092102030405030a1407090c1112091c0c1212022509051b1c0f0b09010e041106070f0b06090613 61
    0x1450050b0795106000e10301403c90b004140e410345400002c0c880007a0300300d42c1400041c400007554000704e19140105c82c40100400707030094000c50b282c2c000500544e200390b0000f590316540c4a02046a80c501c2c0c00c003003011030400000654038a81c00e058200116000200f924220340d0003c008103a20b040f43d40d2221000c1c80c031041c014069110700130b80490480b5090148034141209a502e1311040c2c05810720b864606188007074034141c001030802221711180c85606c400950048200e4250f0620a124135100807420780950020072242c08180d4128100300f64400c2a04a0313040642c01c41d0b0b03101031030f50827060f14440303040340d0b002e0b0800e1100f40c01c000b41e131001e800040c2e0102e0501d1103001418404a480e00e201d0b400b42c58141c281d22000600d150b05080c1360b100313880389100c4011041068049520104907500e0042c001d00c00501442400282000032080c0c90b02c51308003010304415120b21092400003840088040221603900e500800104141000c800c050b100384402801e0f65a044147d0000000a01c10281 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 624504181 1250 624502931 624502951
    0x60a03031101020d05070804030806010f05041e0803040e04141203010e0402041d030301080d08012102190b09040501171b0d0c030b0412050406020c06161a04060c140d05 74
    0x21100340604d016225484c0310f01501e444010f228074080c0b0300240f8080004104030b040c00300d0881c0301341031107030b1080c2501c2c159544403081e5801c42504091000a813041a40818030b40c0c400000d0120304074030400d1180703000720f1051801201010000600342e485030b0000040715041002400104003101c0d03541d20094100c1d00243c030020b10100d0340d804541581d40300320310040369030f40300000410941d0010480310191081a10305106554107014440d1100d20075040b0051402c50400f090806554542500341c034130307285806596110982c1d80003454000d0b040500414401d9107002c00000f00740f102c46840e006e5038806140a04001030b05446283c2102140d543c441da00079040d104007400080303820303e00d440510b020302e501c0005403a05207080d842c220f042d42d0141041090038481040b0f4107400099040355520201c89094a628000070440302d41e84000c4d001800c0343e00d4030a444601a9400a146801076000c1c4006201c8019285000c0c7c4510548010410080ca0300300028041d1507201d80c4130981258042d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 624505431 1250 624504181 624504187
    0xc03030e03031501111908090103020f0a18060c030e0405041e080d18030807030509100f0e010f05060d02060f0f0708340605060316090212060405060a0303110102 71
    0x51a00e1a0400c6505400a452003280b00c0e4456800060b1110b0481071035000b080701e040302506c00341c40c00354070b400300901821011403c015240c4c003030b8041d01e51000201c610552038040403e001845071401441d50403003400c8001000c20345910503182c0100d03140c0c141d202e80920300e64000512004060090058600f50160105000100340048184d143d00780504241c1d03807910140c0124904440a90600300000101e200080300000c1d0441c7c07006a200d0b0301030400040c0e80e030b03880702d1450a1081d0f00c5110b00001c0e2070300380000180115680419000c034580e10080041c488480343c0e9500300c900c242d66035035203c00c0c0f500d241030051a0210081041d00090b541260502d445600e68280350f03000140100e40348070300440c010880c640400c41a400407200540c558200102500c11003d401e0200f4201402050301c4600203020340d02c2c2041540071036000200d50384c030040e0791005100c00079000000c0000309a0601300c00f052503854980540c5024520052000a1561440d80e00750341401c10103500f130070155024 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 624506681 1250 624505431 624505451
    0x1e030c17040306140f24270a0606082a2a010501180902030c120f100e0706030b0a03060f05151207030308070c140705010905060c0a030c0303 62
    0x2110010480c1403444150644403425440c00700284c44e809511a0422052501007000c042c004501d483e0b04003544c00104201449006044d03401d10fa1005200754100c2d61312070300300326402c501415040e9035250070450004213803079150344081514035034841c1d0400030ba0b854002c189810009141a4030301c0c001d0b40081e040b101c44000d5a0b482c5030b00020322605d0404184105e41903241c1a085100d100e100c140c00080002e58108a043c0401714402070640902d01d9803000300d40e00b1518200407132081020b0080800e0000000c004005035141146284021030703010b200d40c1018469020b0065002d00c40c01d52000e400f01c141800000c0340100303003103207050380e000503000d1000000c1407040c844d260b0900e501260201d564500f4603000104044280078280c026a08106180d81e0741030302199107400d499043c5440240e07a01d0740d80049825070800352000c0c00101d9202d9010500700000107801040301d00030b07261110320340d658038104086070048080c00d03003440e0410101351002a1140b040720b00c0c0e0a2003802c0004180d540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 624507931 1250 624506681 624506693
    0xc01050f0417060402011b050303070e060d021c0b0a030b16140301090c0219030804140f1b0f1f050d0f0c03052406070b15060a17090a1e030c 62
    0x852142c0d00351980004050006559202011150340101076209019885d143d50b9915607a00c8024003a004104134400c130094181d80c0c0703808403050030049040c255160103020880406c507411391003a5202d528913014a25590342010192807003201e80010241810b90303112907644980d04552051002046013a00c1c200070142d100802650180c0076110001804003000d0b04042e260845282e03401441d84e18201001001030b070700071000c03513226610408181195818480213454006480408003060041914240802d07841031000600b003081103414840c0485030f01c052281e04211030030ba215101501e280e00e240210300070001052040a03254001030003400004180d001c890f540c003c0100001e8454050100303050007001407101111303070450400018000c150001e02c0c244035442c0001c0c411045140043d00c0041310b003220300001040500540e82d40c0c2c0e043c2a009200340182010140d04008041c082000c005000914011113580038420070841900c075190a88540b007e654110100040d81c1c0300e02000504c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 624509181 1250 624507931 624507959
    0xa02011a1f030b06040f060c05060a02030112030f030603080d0e210a08090703050a030305092e1a0a0b0403021f0801060318020a0605130504291309050a060c110c01050f04 75
    0x21fa150342d080103601407498020304280000d00b0324201a0300601c010b10010018403030300318102d6418100304d009081020b00a40c0903086551000e442e54001180341110f03827100b0f4020b2400e030b815000c240c0e4000c1c8045942d00c5e902c07800b114010b180c0c0b51001c2c803100c10054003418041e03411040d0f207800c0f2803242d80c0e00c0c4c0e40ca900e458800c2100302c0010f6104c0701400503200041203648498485000310942d1000d54100d5202403107005906501a10b450345081e4a8034042001140007981015100e010880d86600c0b0f4901f20354040c1c40102e01880070544001c011300d4655250210540c85991507544692902800301e0107440e040548a0400300e444031a940140c0d280f54001c402411280c8132581c0341e01203196030418079902c40e402240201e090003184c40340d50741c0841c0b2644940c1d00c0303807140b003004a0440c1d020030108061020329100706464800314009101d03001420001080c0329040610040c4140e00c400c423040c1581070303410100340d806040040810b40c01080a003d4010b2040921410196240d00100c0004 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 624510431 1250 624509181 624509189
    0xa05010c0e0f0d0f060c0302040f032315011a0c1605010936090f0c0509100806070e011101022a03130911040b0a02011a1f030b06040f 59
    0xaa82644110705600304484684105603003120740c00b92a070150746903400c0d80e5000500040107107a41e40d01c2d00494034060740c140d801412510038080400f544919107440034500c4000e00c02d02d0000d850701c21750304d024000120f00d40c404d095201d00c403d1a0340381c00441c1c00045d15440c84a01c1020090004164007801004503c0d40100c004400c264900e18000000d071442c559900091080341c0c0c40b031410a03039030000034010441002c90056815040c12080640b00080c02c21650080c92042101c20310414080d80c2002e013001c0e5081120030b000f6031b03119400740c003000501d140304010981c2c00c08000075040c14010700c10301c01504018101145045441060b0b50f0272644a092100c1e0b4400d41d03c820f9114040e4012903411a0550b480001e51a0a500902401c039a05940c400d070310000e5125121000e55515100179580102110b000094489020110103800782c102c2c21081c0540000c2c0d10350082c80c031310b841340c04000040d4024000c010301211000048002d4001c09408035040901000005245811401148028 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 624511681 1250 624510431 624510437
    0x5012601061a1201050306090d11070f0806070e040204060f050c07030602030c1c0902030703020907050408010507110613080a03020702060405090a20090102070b161401051902041a09030a05010c 85
    0x141248a80f20385100c0044e0801406944882c00308044007800040d0f0030440504c0d4202400c10b1140b038400e0601e80700e000e802022103941d03401d800161612000070035a0080c0901e403108603106104000703201c01c030b0099102c2c160000d040d820032400c085004500400c9282c0004080d1070303406031070381c5a443c180e0380181d030207100c61000041c1d01c20303d100b442e5205d40302070200d40106104100040d00003aa540e20640006446854044007086140d4000c03000c41c0c00a0405500130b002901d0100f00240c9580c1450b030070261079001c1d540008406524410079007285a03072140040f4100303241000218025081600c040380c0080701000041120303a18680b025208560030000440c00308c1c002c609580c03414a41106495a050040c00340c404107130b03004524201920b843d200c900d0344407202c5034a81c10201e100c452020b410305c806080554904401908014440c41c0f00c800880f04c4023201a1548040740324900c50f500d0310ba1010301c0d04e108003000c03000c02009050300040c112070740c000058441c20308640440c0000c41c04 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 624512931 1250 624511681 624511687
    0x7080a02130509430e220506070309030f0f0c110109031e1a09030301030308061305040606060e0604230f060f0301060e0f0f090702340905012601061a 66
    0x103d03580105086010a0005145044045c603205010078404c02c0900ba074104000a01800a4120120111903004a400c001250b2081c200030300f0240052501010590000d104c902541380000d0240c5c80080e0184480ea4a198041e085501c49200c1e05610ba103c446c1041108500007021905008064100340703811003603100501414130b010a000341c000d84015260164140c10400c10f81ca01205480c1100e03010308295000382d407200001842c01012100e240e803a5490403082c042406969070002d03041d510b850311107040c00383c81c030070410207103008a100f00700d9070784580340c14100c0d40075510540c1c510707402014248007884105200003503119000005a9a4001c10210040102c658405d0601540760b03815200741161411750004207046030040300282d0300442911020440480c806c0102e0a130160099600c0c00148850350b0842155000a000601252180e0704011403045260f118440c100e8903800110409081c005ca9407500f4009505110400c1e035503564000200da400c010b01205d08080e80421541e0303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 624514181 1250 624512931 624513013
    0x6150314060f04050a08030910061509052d062110090605090106030203041719030b03151f08060f06120604051002070615150207080a02130509 63
    0xc58000000c002c20101002102400701007280441d040824035086680142e803641d500141c5481e04204858200c0001e1400a000404a141c6582d2407214030366a40c070000b816a8a05c01c00407580c038000300c1c01b81c401d07c140b0b04801e0071505c0c50002c0c0c0b440130009069039080403e41d4680444401010900c603091240c070b10700b0860181e004134400d00103492400d80802205042c174021540c44041401000c0a05a001002c1010310614a1000001c500c0b41c0356031980e50200d20400c0415844609208804030b410503c0d0000306150114030300c0381040c100f548000071a0b03548074040c0102110380b0101003402a80e18801f02e0146e105002e005e21a001000ea80a09810301c041072010203640c440114a240e0445c4040c0301c0010408075801710f404082e88000341c2c072000c071810240c00800075940020702080400e072002481403207025211500c14829026201c6465448649039103541c51108002e40c0858444400050300d4841d90000c0e8000c08040c0407500c1300b4000e141003001c95100d860046144c174450b005100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 624515431 1250 624514181 624514183
    0xf040207171602150307090b18031f0b04050c0702010503070c05010f0501032f01110111030a0f06050a030f080a05070f050c0a080706050d1808072402040e070c06150314 74
    0x11130451466503528510b01c0c001c0801002c4c1c1d41075004022010303d0005a41a020090301041c42c0b0b181c03002400e44540c40e018441c0c0200150001303040c142c2d2241071400c0c255240c03270b1030700c1a18031480310400d00b00e281410399401160581d200a08000c1071110802c042c0340030507000d21450b0f903400440c481c001059415800c04640a03c0202d40c1c114005000c880d04003560301c03c0c0e07541040100001c0c01d02c665800c0c00e0b103d507940504215003080340ca00e40c0c01300400075000400d40002843c1c1c1d0f8541c5003008816211010301000070490b00001d0903140706441c10b0f2001504a0000300b8421a40d03103442410306856a840f80d90380c10940300190b03020f500014410b41d80d1310300702102d0303001025294002c0501a00e02980606140100384481d003e4569840325510b146070304000c480a0954087e90311541c441c01ba00c1d0990b09014036070020000c0e14601d030b004c504010700d10320890381503078007072034040455580701d0008490401041c001101c40a40b07a5a0004401c1602c1d503420001e1441034451000c0c00c15000641 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 624516681 1250 624515431 624515449
    0xb0c0d110307050a080c04080f0c13020702030714040209100e010e0102160e1b0a0f110d0e04090c080d0507030e2b1103030a0e0f0f0f040207171602 65
    0x11282000104140300070b4903046011140c01007154189203015a0741c4143c400c00301c0c0100ea01160301030040a00b0844818004140941c540d2021200746d034144451800300710423409950002509a03100600501049000620080342e01b8001003000d0b10b04103504010272105030400c503402d40803c5221400c2003440da0003030007080c1c0110b002e1005041c05070140d580945401698410004420800000306800e01c5140704142d5400c0b20310b5001e590f480c2443d0000820003005500c0240008418000c141100103010840380075035801943c5940305004070108110041c000c4110840d448281070000060074141407041010760903580c2c85894131444141000340001c0619810144100901122802c819500e039610f000c6402c5140d100c0c918801e0365240c8170011000c05010941c2c51310000c03401901041d888508001c01c6041512900340003000203040c0590300788003041301c50303025410011868031810710750302a2000a001c1c070f0304007803001c1200c000c002c0c5d9070f400b100140c1c8182c0c40d05524441541003040729 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 624517931 1250 624516681 624516701
    0x1807090c031b1d130207020a0e0105010909090507061b02041e110301050306010b09060c06131202030c0c04020d0902090f04020a0e09030d02090111101a0604030c12060204030b0c0d 79
    0x120000d80540c405500504843e00600f8450191040c12258003021356054500c03803503001d070070440c4142e1100c0c0c013800520401d00c52223002075482c0c4008115103000d401036011060b405001028103500b001019111002c10340d0210041d6031554040c3d10160f901e50164032440303c0d2003a4840c100e410300d0b40701d040a86580409001001008100400c110b0718005941070454030f111001546a60004002403007601c00c90401450390710500d820b22036a4895460070030041841010070782030369109841c060f81c9034040c0042070242a0801100000030b070078542c0044c4049400c004002484081941c00540810015114103880d121500200400c6040c4010315202500b600c900c08006490812a501d64034070624407101120340e0007107052042a409201c0740c049003d5910141e8102e10310b072404400060800e1000000000851118083d050400c401213030141c9810041d80b0154a0034a80c0114014903051411104a0350030400007002ca820300140a0040d6466109103030303900503150725030f8150350883e49 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 624519181 1250 624517931 624517937
    0x70509070e032512030e0405060f0901080c0306060a0e070c0201050c0106090e0f070308040b0708040f0b0309150601020a030302031015050a030c030204140f01121a0a0806010302091807090c031b 85
    0x7010404290880e50f40d451b0600200c0d4042107995901c001f05a0310380e036548006421000e00c200128598001203003000b071540090301220403685c3c0d113100300b00b4014141e10545900c01c140c03038081910f00e0311848220507918018140103151000b01c40b0f0003400c44402d580711000181d5161240c045a8905000c0c11140100d0742004000795800c580ba403c001d03100343d00c5800340b0b0100008001d002c000c2c0410a44001b443d4001c088280740350713a1220030380c0581c0102c403c59041d004541080039286a0441c206010300e0041e802040010325641c0d0a60003580060144242c0e150b03c2240041e2101c1c0700000d20201c10f480d5515a45c85d4a440c0b80054143d80803071421030309243c0140418070010380401c10550160328102c07011a025185540140c488140e0180031f041c1c42030801241100704c1e10044540342400e40c00b41c403640c90507551b40f03442a48450081c0402588000880c0100c4e00f4080442088100c80180000343c0321704681e03c400780070460705190010400310f921030b0300d110900c8a11501140d500d10081c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 624520431 1250 624519181 624519209
    0x70c020a0f14100f110a02090a06031a0403200c030f0c15030c07080a210b0a060504050d0807020102120a020109060e0613030f020c150310060c0302070509070e0325 72
    0x70f0b6000d8244071401c0303141c00800100d8071000c0049a404c2288110352900548829014204480010054071305804261900a09196080b40101c0c40e0816107110340d4160752249203a188a492480e10804806541c0141d882451032400071694103000b10401a0030b02c4004001140d00300050281801a01c060b02018890602c01c00c2143c80c81d903011204010303406031070350b959030700c000341c064512807092010b2512840401c207040d0211865a070008040c000e084070212039003a0703a108100c0b114820760160f150814001c43c1c4400000d0451400750280d81d00c1401540d64900304058032402ca908510b40c254010f0307440740ca07071000b401060302c03441410b8494000603005c14a0721030381c1c0324216034440c08010108052103090b144118070a10002002070002090548202140140e4035100c0e0400c0d9001e13007010050000c0001c0c251702441070803030102c2c1e0540290107400d00d040d003041a03010f40204690148407c002041117240c1d424002d0f00c009c403000c2105804482c091401d0080343c040c41e80c0200c0820070310380c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 624521681 1250 624520431 624520459
    0xa0204091a0102251a07080c0115050f0307050607051203041101030501090902010f1809020d091e03120b0d02060712020c01141c0b0a0b0a020d031112070c020a0f14 72
    0x140700c203203050302c1241000c180d040301120301c0c5171454820141d0280c10390b900800c1d490704104064000c059404480c046d00201684c5910401031f540d04a2500507506500c040700c100420300b444800f07400e0203030290341a030310402d003410302005d001d80c41200c2c12a22103080d035240d0066987c25220f590b001d0070660b04100003210540e8000703442c4004044400c014466611200070070b044581110b0400740101c204159150309919a00713070080d01d070000044602d003800c090101c0e82c3c401070780c0518591540541d522a01d5030b480101e8a002000358942040c1c10541604082c000340e2111001000e059104140c103081805590500174140790381d0500060400c075040c0310707140d0180480e20556405618454001d00e4070071122404000608400446503040602e607a80091402031309001350083e40455002e031100624940c1d07044049400d40750396100e2989042c4004284c0050384a081544500780b41401c071f0b03060b400f5400240a0340501d501c0540e0181074a0b00910041d84051180c03031541101381c1d02d0f000103940c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 624522931 1250 624521681 624521743
    0x1a06040302090414070605040f0b030601080610121505120c0f060c0705100203030115030c021002070f0b1510020604050618030d0207080d0b060a090e0a0204091a0102 73
    0x110300c03001e803150032110301040610012000041520301050200c0e01296036480c00a00a03070407030321a44098400b82d01000414210038800c0380c0c800d41050b501c1c4e44242d0344e018104064907244c8803051003040f5401020806540c40d034414011a00c0f558403180003911318102c01c1025103006404045816040001401c0064a68110990100c58202d420540380d620054003140351038066406654440043c0c0d42004c20310384c0100c01181030b03036104c0344031280841e14001d0540503550408440c4c00103174003820a40701c0c03c01d11680504800303441200c0c1c00800c0009a01d40d40c8980758240c65504120310980490700c01c6280482038020407100700d0026000520f010b072202d6032180001800b01865090303e4104034448002403040b2425441a40c104549402c040d080907030311a00a1000224146c1c9001600c2400f4035002c4142e407070724180380d507811850310f082c1000703104192406491401c0e00c940902005c10246038a02441d0481155203414059240c55100028030b403081c4441c4100b00b81d0920001c042071184 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 624524181 1250 624522931 624522937
    0x20c07051c0222021303110405130308040807031707030e0105010503011a1908060c04080717031b0102040b040b130501090806010e0c0708120411030f070501031505040501181a06 78
    0x384140401d08407103c9540f620010740f04400700305c2118413070315101101300300c21001039210342c40c01507a04006682e00c0c0e01030800b0303c65802d034010700031482074030010740020340400050036018071920f0705249a03d5001e041450000d41520f010380480e80f901d05020210b0030034803410f801010214001d012220b141e803807080d81102060000390186440307080c101da80d254214030400080c181001200c6441c6806251402940c026024286d09400381701800901440d420b21040c82c0403030712901561520940205010400c82a101080001c0d502031100281c402c294001500007041c0102a0503274a21190120000c01c4c02541c12032418030403556000d106066000403000c0c1035894602c1c41c6201902c3d10380320b446a502484070020104a400940c500c11040c401c80200d02a501c00c0c000d0702d0302e8203513613020142c491078650451440d0740e000380350810040d8800c1e00880900140710611000d8146c0f49c0c4042000d48101740c01075031948e1200d6800c0d016002c1d0a100e105031160840c2650040c0306146000101350384 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 624525431 1250 624524181 624524209
    0x318010c121104080d180504050c0306040b0117090102071a01060203190309020a030c05040e0c092d15011206031a071209051f02030108060112080c01020c07051c02 72
    0x1596409000c40d078030b44000442c1c0141485004841d2103401418000f010003500210440040e14002030000342824903000c1c146c000c2282184560860703a90a0910000b0a030005000781044006503242c010500401c0d400341c06a04034000150340c0d4076103403c0c0812181c0100400040000318100104101c9034040156000e81c8c01840b00000380c00c118060460140040f82e1020b98000c4c4508000801c2004244050040310025101403054100b10311240b078681c00300441c0c3d41d4001c0c903440005030211071610101e2183c8120f00d17120f140450304611804a100b01d049941003070740d140c06000032600c1e40c0c002c034a502080c0b1a2031003e1050a04603602c0707451100703517401c00481a04104002c11000e501441800890038102a0308000704026428031036075038981c04c0188440900a0f0452502c182484d000701e905942c8683c00400e07040c3d1819003000b440004406096a480c1030034024203110b120203000a1204804110007042c4080c1050204082902c800c1242c600c001c41340f02003000180c5030f0307661050141d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 624526681 1250 624525431 624525467
    0x4050d0905010e06091005131e0503030901141b0613020a171b0114070b040b0c070206030105060702010e030a061a100f0804110d0b041106070b150a050a0b0318010c 72
    0x1b901d01d4031810794441c0540000d45074050700444010030094104150400e29030b003000c24100f4020794540c1490344074402c856155000540e006d2201001d90403500050007203a8442d0a2210303503095001d005070505505440025031401c00f01051403d600d82141c4c1440034240310000081029400c5c940503594960b14066190880d80c913030f000d80320aa00604089070100c2c115044942e03542e43c5480d08590203002143d0484a0550a90200384001d24000035140250b9000d0704080c6181d00700f80030030000f82c0050008a040100e02150340c11152414000c40201c6442800040743d2410661011041004619400b40c01403505031f02c80044c05502541090700011103003010516503c5905000746001c0d964030141e900490103c0040d000c01003051000352185018841070700486c1d00c0070741009407a00c280c4001a0a013103a45011504001c0e4000208507440d1000b00b241303005136910303400301d00900120b92200c0c442420100030040860f480d00c03102d4558880040080050011800d00034081803420001c0c1c3c403074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 624527931 1250 624526681 624526699
    0x3090319050a020603012903130305090409080c030415021903030b0a050604080304081905060712060801050403031b08250201091506051509010206070503061804050d0905010e0609 79
    0x1c1c4030003881a1403110750080c003102d549685500c901c040e14200b200600c810013441481d1004100b002c1400d4901843c204142c14581400b541c408848503045540c3c019402982c1d03100941c00504c40340f00908003001c0c0301c00990385680c50b206a039100341007950440c0056400c06542120502c21000000500076854240041e0750004840840c0056a454020503001400080c02007800c107000170180c412900c0b00c804864039104201c21150014482c004d00070215840f40f000308034071a000d01c04480c0d81c039020000c0010b500d580d401d800f6007500c506031005c0d80800d0b038440000e0802a880c5840e42c0c400e201504041086050026030208403440507080164040e601c0130003100e00d940700b0340242c0d8056800000a000400f844a180c00040c980313440341a00c248a00451001d03112143c0060b2207031000160040d150715034407020240d81662006045c140d1059008006180c070111204046e40124040c400600807203981d507502070250320076038002034180a50080c013030400c0d0b039a41e01215456030003980c544203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 624529181 1250 624527931 624527933
    0x1b01050403290f0624030a0b031212010509060117060402160b04110f010f0504050f010c140d1d090402060d09020d300206061509030a0c030c0803090319 67
    0x20b9840d4906051039a001c141c20305101581000e4400360f80141000c8442030403d050080003004040481300ca25005800c00f40005007400b03500341d02080c8404006015250104180758400019900000d030400d9070886c4040113205500b0800e0341036034400c60030300307042c031162002d610030004142d002007d652003641c0024902040d02414031504102c994840d120048900b450f02e00480007031124031100e800382080071400c400b2580310f0302c1d00e038840c0d4245451340752034507040109100f036211840c41d586050003540804000002c1105220344800c44050001d01181e200861004019420704013891942101c10041d400a80d52403952954200b541243c9070365560580340c020302c0c080d0641c1100a03500001c00ea50f82c0052240b8034907003242000d89811030300c100c00004454001403000a181c02001079100000080e024241040d0900895444080440c02d0140401c002440c0c00035840c8101c86603c58140c00f00704004190070268054143c140255091250a802099031200118500046201d410101c40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 624530431 1250 624529181 624529223
    0xc0316032f011410060c0f0b0f0f15031203040221030301080f15060d03030e0d0e1f1b0f120e0102061006020c04090318080106081b01050403 62
    0x40154501c10206009229241c0c41e00644101c0c0021400103035400c20030389941d0350a07540901807145040c01c250701303801c81c10310004850550010100319042d0762038984020110f12140e400610410a01720120a03a180c1010310781380040c4050800d04600c040f03540420342c6542c010881c0588440b010910540304d40e114000182d0b45102030290b0300155900b1002c1e910051000300066059501c04e00440f0030402c01d02c42c1050b59014905100440740502c030010a46070302e484880e12200c03900910f03021604002c0d0110942c00c2c43c00c1030301c0960208088281c0c4212a00386541c9000340c003803280c0c518000c0d41c0c8010102614810300751559407840b02400610804001c0392828011580d82c020741d805200e041d52200242540300352208460146c41001c00050b5801d20910b0248259080d650180c07580740c540340f051001800c403001f011024045406604c14480d0903036800003000300a100700101d441c6140200316401c1c10050358200340352100d40c4c541002666000022901101d42c081c00314a04920720245c84 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 624531681 1250 624530431 624530447
    0x907090216060606020a0c17100504061b081602030304080f09031f090b0603030a120b0a05040e2d0307021507080d061e05150a1107060201020d0b0103020c031603 71
    0x24515483c104000c10310130b50011b0300070602841aa0005401600c500070b0100d9100f00385055007540e0b011244451604007030b0740083e03801c00d10030840070400004004649103a200c500d1448400240c0b00d100b04005104002e90603015103141340040c62650070b0130340340c2d01c01501c1204500c1c0c48074400022a00d451340c4003000550403201d80142107803610b0f0101c0c0840c9019000c1e104043da40c011040b00030420f03071b1070088200c55004201d40c0320318010140040412000d0550b40450a40c0100707160000540741e111070294030114604807000e450701459a40803010440110110368505500d1206442c480301000400c03039032040e4044500800c0302c03910305569074a512a000e4000c0c5012404112907001e0801a00300000352001c04130580c1301d842900b1100000b1000501c01e0365403250103e465402d41e003214200070030806125140c011400c560b8203d130103181407610745c04a40143c0d400100c0c00885209841407050025003443c0079860001214412580c034042c44916492041030381411030109806090f003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 624532931 1250 624531681 624531683
    0xa06110408060a140c12240d060504120203040515130f08010203090f0c220b0a0303050c07050406270e07060201140a0204120b1b190e090907090216 65
    0x889007180360481410000c0c00f552040b540500306600007040410b03030b0405c2510f50a01c0e03103e65000265a503800300618042d40104190742e10f40f00360900c158151149102c00d1584c5019980100d6181880d251240c41480101c10740c10454000780818481641d500b00044100e418441d40940c81786d050f813200522041c496803100309901040d060003e9110410740140d4801e181c02000da03000120b01d0301c11540c8601d10b075881d4030b070b200c40d40f110151801700403c040d140c07900310792610001e11001c101c0c003c41c4003003040d904190042500800e00b441054010003114018040c00d85050243c50b1a0940c4011600307506510304450900c480706821050b01c1940c03201258064610449004d03036981c0a01a0003006803e06c0c2c2d110101c01600014034066081c000c6404448030841242c0440c400391b1030f10cc655045c050007a00100c2e0000300d920500b004603234041c0c40c082000c04200c51034501601d401500b000d900000c9030b4001c3c01d0340410480c0c0f4200126081017102d400041c007590b9484680d0038014078030a4440 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 624534181 1250 624532931 624532933
    0xf0d0516031406090d08012607060201051b1e070318030b010f090b0a0b1e030c12060d030c1416151b120e0604030204090f0204110c0a06110408 63
    0x11001061001a800c2048105a1541583c04980b1a50046a00ea1001406800100c1d1032003004102c075001c01c1308544a41140d6041e02a481549400105d0a040d455400200140e4594050104140300c0010100030f0321040008c0707d00d0503403011803040494090006400c01600049a280241f6004448240d815006400c0e0604140d0704c034035000140050a000d01004c0c19011680031901856a108400400000600071012907141c400a0401035000d440d242021340b1510100d110310a0558010710f010b504550401d80c0c6501c424078012060020003048107204401c81c0f000e60011030b13048400001401c0e0440e00c610500c13041e1000300351400310009040b00c10000c4c4403000060010341d640d407109003030000b55608086132a90790701a1044210610001d48402c0d410b03014100c0300c0380140b000c9012200c01424040c1440d0b603d40009080b00e910070f8041d00c0c00c1c00c0074074064086103014440e010300700785204412410310307425420072684c40700d100100506071a5122800d115040c0410151401000140 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 624535431 1250 624534181 624534223
    0x50702030106081612210c140a0b13051504020a030b13020f0f180a1b11010f050708070c1703010b0a0806060307090b18091006030e0c0d03030c1e0315140f0d05 70
    0x105400c1e80c40c03a5481e00ae80e441d000030740200b5145100541c160039410340005c01841c1d9222607c44405203520054000c80c0d010900c00400400a044072251505c41da100b206110201c42ca82e006001880c0c03050a1110703c64281c28100301e8042d80e030741d81c19044c0c200e4a0b40080300a1703555150305100811100b004200d5840740d140610310032039403010700b03005102c9002000b0300c41c055081442c0d2050380c40584441e00418104000240242e12030048c0d2004035020f0101417400030741450300c0d02c455a200f81c101c11002c5600048274080640c01001d12600494161242d502d1450150401410422140030302610030b4030010b4010300071030000058a140e074500070280590f5040c440142450030100e48540d0000c00d080011404a0001c08601e800c1161800b90109400b09959a0110000c1040f0b84501041c005150a4800348032851444c0b4030780004540c40000300c043e211034170020700ca42542d00c01045515128114921031320344030089450700c03000b5103000d5000c00701450030600f01500c42805007500c0181d4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 624536681 1250 624535431 624535463
    0x20a230d08120406062304060b071208041a0f06190e0606130306050709080d020706023a080117010501030c050402030c0f030f0f0c190e01050702030106081612210c 72
    0x2580c400e5140c0c6c0300b200d0030080c8a0f81e82d04e0302605800f6011019100781c400c402c41180d000e0160b5652503000b4414101869102801121150ba450b41a20f04020031030b40c203000c004041c00d282c116160908100e4145e1682185824203054071500001c2400d4041c0101262030841c0c007181c94540b1001c2e56002c0028007483c40c0920008145a005100b040184d100786038000e00810b002246488c280d41c444e9000e420700c250150460200c0d1003440d00040a8645000c50301c1507501c0583c05501d00500703566440000d1b5500d010000100d682c07581051075820f9140c40010400105091106011580700303690142e1250340da4a01d41c103050040c554405000600081001152441c10340864401d40600c0c2c501100754440c50560300e23190180b80c1d1610005c4444200c000d002c0d134003818194034030034030524000740b5200540e4007003030030b417081c991081d07410764005156070b9541188044c500b0013502401e00b810381c00c0703511501d038204525028455900b90413410aa105512880b58000110403a008141c1d21000700304 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 624537931 1250 624536681 624536729
    0x10608100506150705070b3402090a0c08181c0c03080f07051b03090d03030e1203071d0604050d0506070201060605090d061107020a230d0812040606 65
    0x102c810328440c4461659803140c1031901001d60350b103550410b0007840c0341030824041c140c103070703001d00c010181a1002d03c4048802e485c1441035150701c050010a610503070902031040c031070300303a2010302400d800078100003c00e00c8099200d401ba1b41d21004144081c0002e4010b40a01c40c10312041059506181e514202d100400741e8001d003100080360700c01c0d555034480b66a8527145001450b4191603003000500c003048079007007014205410800d02c60f00c400c20b40380f4010b8041e0000d1303070540031001c0480100740c4880c0080c0001c2030510140781c00700c40c9040c8841c80d41c0ba02040080c8440b102c0440500b4a040580408030b070303916050161809080003401c0400340020604100d5640d241c1110341d880151b017011008078069106006135650b5a001034540e941c0144560740b5400030b0a803c40300d0009014003403002d1009a50b42c0703020704e0018841160b403561000d031280d40c105420344140c038005010f10703040b400000000d0090b8044848902d8044251f2555845900d008030181000307a00404140700c1d248602203807505 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 624539181 1250 624537931 624537941
    0x30a0b0405070504080d020705010f0f17070c110907020309240706050405161503090503070602041401120b090402090712090602031914041113060807061215051201060810 75
    0x181c00c4046030084a44504201e070b0700d484078080d1b275000441c00703003200002c0ca000e590000701001e00c60403c044005001c1401814041e41100e624000618a114800900c4498200c44280c400d065825410320700e802c2c500a5030301d11440a01d2809102c403030f404001e440c200003801071102400c1c02035090b82c03030f10642001c0b00a01000d60f4180c8090151070f995807103100040c411441181d216039441145c2e03964819040d07009140b001d8040c1d03403501082000100141042c4005c0001c1e110300249212100c01240c0018040806150708110b07940ca0400780c03061941c0c80101c0182d106904a90030b5005a4803100c044800c010f034064840c5c001d034203207001e200c1040b07199005144545801d600d240c0001000c01010402e40d030071401c02155001803100490301080d501c000d85601964003508208129075442070b05000ca4600b0703403014559400004045c0f0216034000f0310075940300103505003030180007070031009040c1e1402786209451060700c41110401549000390091001411b01c002599a024182c2d555400604 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 624540431 1250 624539181 624539189
    0x2030f0d08040c05190501050f0903010603050102070c050105120609070e030d1e0509090417070c030501060801050c19030e12040815060d080a0e040207060c18091808030a0b0405070504 81
    0x240c804100400e003400c5c6207142c031510700004400b54171441d14001c01034510341d0088106001c03c541c1048220801e031000d000700340040d0f1180780010303903800e017500300910800116004917040101c2080070804d00725a0b070b81102d80010040b41c0009050311224402d0f26043d03d0412916054043e43c40020340c20b0f0740084820003a01e0074811a0034040d0080d00040750280300344001c1d03543c07015844000c40d01180f400341c00140c40d0b040c14209113140480e1600d45440c504d000b548210355aa444000c03d00c4000c074280a90354010030140308c01418015200096525100e04603d00302c201940d80141c06804101084a4030307542e024060213550314ce45440c842501d82d0a06216800d12000750004603450341440f03410500440e402c003c0550a281c03c4c20403c50305488400815940282c081c03010394003180c0079200300681e424040d1580d082049007218440c0000030654445901e481ca425414200d203920102c0c00300329141e000d00e8a642e2940e41407540ca0081030480d02958000b85080b00b00b04031036401c180140191 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 624541681 1250 624540431 624540443
    0x280f09060b010504060c1124030405011401050d201504050301050609101518091e0b01080703091e06020c1905120304050319020d0e01020c09040b0402030f0d0804 71
    0x380c0801d00191141c0c882c900c6414000b03a08221050085141c00d5a42c1400f24002485000001400c0d0300101c6483d54902e50003c0c010400001d1000300002403044000c3c50141850b0302060358504400542c00000041c400381c4030502c6031001c0c0b142d203c440740781030101e413000608002c40403115406011305d0390800d000c2c00340650710b441c0110360701d440c00401c50ba1161140f0190305000d203003002130380e480c844840716403c024003640c840044070701d100711211440582072100c0001010380441c041640c50141c2d400004540301d03d0400d20014a0740d10805c0c90780d11001a040208000601e8a82103140400c07841c040890031300310403401030400c0341580050440354403403421034005c6c0307040713030081901240c513050014501da000b00100040e100e0441c0155a06c41d0142e001d80c0e040103000b5103040819000d45203800d0050f0400359204c1c60541d0001204013181100b880100f03940c1c0c2c800e40101c1c603901401341010b001200d821001804550b400c02c0518103010300c4000303580690007400d201401d49007081e20100c1e05 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 624542931 1250 624541681 624541691
    0x1c0c02010f0b040b13020a110307050d030c08091e120c03090406061b0605060d140a2604050603100b070305070611030c091003060911031b0909280f0906 67
    0x1890315010340740840b130006050f0f150200b0241c00b510001c0d4410250002400420008000c114030240043d200c0b550080000c2d14000380b000b400241114102d4440c1028441950b080c041c2c410b0000802000c00852080c2e03440200798140391842c9401c0a15190218880300011041541c2d5004009031024031b209507400d01015454045c255000c00c003d080020b035084000c01607602255070380d0080d541126001c0c100c0400000507859400c90900d5100c20084140e0103080c410042146d0380300c0c003410741c000414254011000c0746100f002180b0642c4540e40c810200400401c030b84140022046004180c11b11409a8504030b510700070706190407031101a9003242c40c0c451130420580b035280c1100d2050341030402551a010f254410050b6001d261244072007019660200030803079070103503c41c00c01016080221a030f02c81c80d100a000d1658050800c0080d0788001c28003100b40b00e0b4171000f50141d0031020148401c50441000645009034001016900841c1d82c20329813841c060303d450768007145415005100c288a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 624544181 1250 624542931 624542951
    0x1502010e010b06030402031b220c090b030c07020d1403131514030f0712050106020a02030f07030f2901090e0d0c0804050f13060e06090a0e0a081c0c02010f 68
    0x8018003017194040e405802c200740d80000565a43c00303100302e8017001000002d4a15240121102c50b80c0c0c03951050805564a40020b480581c00100000050415100c0303a465481c1035040307542c00340242080203000d8400c010500701006220b02c002c2150840c107030b048945035680700003a0000c0d440248900b807039087c0c410350003103400c61081d5944039145035400c0b90b00d895038a9080c036403442104002e10320b41c1000303a00818040040510300596008288990041110b1aa80e0040504080305816101110340c0407079020000100901031103501c01c2d800146101e00c51003d841040481d80710f0007072201640015000101c0c062903580e100c640f00c540e4a1080300c4200c10741c542c05840d80d405100000d00040001d000c02c0042d85044609442490720141c811003111486e58000b000352456600000d07201c036658010000d203820800b4601d0750207696210103100101d26250000c1c1c54640180b4050302c1600001074a4108a031815514400c8031300c2004104188000243c000303000b4028a6007001031307942800d403000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 624545431 1250 624544181 624544189
    0x2191107050d1104020d1410050402120f0403110a0f0b07031a040b01020724080907060f08040206040e16091406030a021b0304031a0105010306080c0103090203071502010e010b 77
    0x606460010b0700a24603808a610b80d411002000032401c1d500680030441400340407524090042c4012043c90303142c2c0142445444c3c6100d405054110314041e91040c451a40c5103400000340f950480400030080c1c002d516107080840c1e8031480704859250921540c0710380d00030402646c8440e02e1040c003a1608109a40301c5003802c80540341c21440042c07462150f2010020213140a0380002101d04050040381c0c0400e5032410f0384495525400b210291441e070819415000302e81040403103500140501c060215035003080006020001109400801c01942d007001070115100c41c400c035005054010614941c0c0e1410100a1600c011400c42b150b0026807484800907407544444440384c260b01c0028500c13411665096003e00003900304416200328203103890080b000e40c1a051008002850080c007558150709910840381d50030f040c040e40080d04144c6000b00c1001048800300e60480c03181700c2403038042400c0c161800043d280c034040340c015085030820008440480c41c0c055004201a18840f0004d101d0420344034200 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 624546681 1250 624545431 624545443
    0xf1202150609160e030d050d06050f010804030c0204060302092e0602071e030b090d0e01050909040f0c09020d1e0e0d0c0822061d01120e0a0204021911 66
    0x3450708aa1504040f801041c107420004881c100740b860a00803065000b40080c0c54103060a6601c00802c000041c80a4101218040e08010300070984002c820003402100081c40524000d1025040000810b03481c005c5642e00d8020300000e6070014423030001800d06408064010390054880728140c1610034040681e99080e5000d20304940d142c2d0040d204941ca03103030007901c110001d001c0b15250f8400705040400002da81511702409510410001c21002c556120043e00c0000300c1e10040d414898184040c040399075540c521030303506c2030344242400e4011034a80340c68203881481d40c01c100307005400130a000204041e690b200d94400b003030718034003c24a0001c0b0701c2d40c401105c1003200c84041e960000b020400e04603002d81c144541d26403085444620303140320f0644c50000980211072005091444207000c00849900000301d001c0780741c0d04150f0042d001c00b4140060030054100000220300340e10703074088a000c40b80601441840c142c000e8010355403900240148109200c00203500b5000c110210850500800c0010391 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 624547931 1250 624546681 624546691
    0x1118040b01031a0d24050912130603090303150e0703150b0304020609281706070e1005040e0109090b10120206180d0b01080d03021c050705070f120215 66
    0x3421480f80c541824402c0400d1000d44c20760f4100c25205203d01c100d02c2d4900d040070b120101040c001303a2810100d10050408140604d040e00ca500300344209801c0c0121803481030304031107507402d0001c2c40b8885440c040d405040380d555290741f41c442ea004005400341140e40103920070740b5956002c0098036842e141e01e0906401d03600404241e1841800058014180f81c8020100c03848000c00501d8403d90000d061402444400c80c05c1c81c05136030005040090702c4404040540042070000600005e00d0080c8000b071007151002000d0780b29182c0103901d004950302607411540a0045c170303005491a503031100d4a0a02600c807800089800e00107050000d451004c5480d081002c0c1c903040541c108200c0d081d0740800546821608a4009a284140400381c3c550b4404054400482c42100b20454642c54041200d007800c46030300032041450700410408520010503808141e1002c5140380004281e29154803c481e42e001e2b4481c010003594100700c511080c40300e041c044400e001040e134200c4486100c055010002c102d42a10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 624549181 1250 624547931 624547961
    0x11010e0c0102010b01030c0e0906060405060408070303080f010501210e010f05090f0109050d0e031504061506020111070f05010b04060f030c06052b0902061309060e0405070611011118040b0103 84
    0x10016589c82d248166540140d8001d280c9800c1c90348880004409a2103130303018070000e9224020030810183c00c410f200390301c544000c10040d21985040c0c006403c2d00480d003008080c5030240040d0f030b0b505904590101c0d0a07424108020000c80e00b400c0d051400a04042da1408401d12403c9003140c1c400205002e1001c02950003806011b0b180380c4400241c0e5410380070a210b030b52500501580410b4200083e91903480399001d43c8011030494150100d07600691080d0b0040e004590405029060000301c1c04110303401e031903114a00103070094203420702500400030008015401810a4000104042c8604894003542d000c3c10048209503640c1105a41c9441008054160035040c40325400c40c40500d08100b514483d170041d40840c81c0101e0b85d000445590010f10500207000c8624800e0050310403c1c4120005030440044c640e40e1402d01d500d81d941c0d111303858440c070303c104804400b440d13841c44403e4001e1851541c04800031a01c9120300240da000c41c0710301c40d901c036000d64034122206010b0340c4a402031580b070b065404 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 624550431 1250 624549181 624549197
    0x108010606270e3301170f071b0b040c1e12060b040b040606051902030705250803040603020d0b010c0c0326030903090a1e090c11010e0c0102010b01030c 67
    0xa0a4400744a00521441a40c81130310111040c0422082c3d210107850103113120080100c0d000d00014002c3c0035002d0a052030103a140301000801c600c102e0b505508811a400c040e0420010060300207071a03441c03271400074503c01d5203405000030001c000d441c48080c0c801c242a42c10b0102641c1c01100007000c42c2c2d20506c10010031170f4110b800800e2079940001c10141020f840481c90101c0c940100301501d1550707010304002100002c03082d10300c111680e41c3c03184041091000c1c0d890036101e52103066072600007560036002c82240c0f511007500711462009100007454440266a00e0f40d0391080050000d4001303003c542d400c43c0c180700058050350311618210306090781c40341071035503000d00315101c5924144c0c94896003082200080d42c106120014040550b06c21000b01c0002c55075000c0d41c43c144240650203038002e90540f00580c4101020078280341601065910340000022101c422590458200d029050054202c3d4601840e81e401c524020805407100c0d402a002030011200400045007120820004280054411 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 624551681 1250 624550431 624550439
    0x50703120c1a0402010c2109080706170606090a0801050403081303020a0f05120705010b13020702221e0c14032406040305150109110f04030b04020414010801060627 72
    0x42d11041e8110f030042c900f08519000590f21900100700302d819042030700c1d00002200f241141d20603420f0025003401409400483e18005020700400a0132500007600c001c0303180060f03000d4590005130740013030304020425080c0ca941d031100b03d8000c00040c0e8068001408081c0020411841d040710034038040e070b260b030082c080286103450340c1c3e0f8000100fa4003160103000d220a040340745078244019005c0c0320301840001403030401040070403455003801c00f00b0410460060003520090303942c0c52601890050102d1a03040c000c00c01c40c01841c020883d440c03120b0504c200c505200f440219860b070100c1044442ea8aa480320105c64079022095800121443c145d5503606145100340da01d2021000f180c00103001c0d050504054aa5640318103251070a000159803901060041210036054000d00380600ea8040d050740ca0036100e003183c40e03050b00c500e01000d81102061070101e41151165400454030540c00011600075503103404001340030f00001c0c450340c5c000413410310710010607148401183d0402c02d0540c14080f00a858 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 624552931 1250 624551681 624551723
    0x30a0e0c0f1003151403012a05180d151a060a0309021210090b0c03060a090b030a0b0c0904060911070201030b0111070305031308010c21020412050703120c 68
    0xb1482e51802095101c141c00300480c1c440c03c1000014041c81c540e44c003645540b440a0508440f0865010a5600041500e4481140c140b1841005141952820540d81d9070580b45401691b80603050040d08000c03010340c28002c1c4440c20b42d00104401504505000f0310320101d0382c2400c4040701f0b110640d44042d080000e440c00e140030b9403041c0e44440c800342400203031510380349071141000b054a460554060329525a0002c0003800000d103079211080502e0301d070850400f9004030b0180d14880c0a00181c59545850000c1d071603408000c101c690907440b4154840a00c5d0041003410b40b504000c0310715004604101003c034105415002e0500803440070081c46041c05415001140034101940840e0f0605c40d01031040c000a5800b80036140c00307075004200540d5500b090700c200e00300301c0d081a40412860b0345404250078081e54414401d0022154a84000c0da090300d160803414028419540021079802c0040305d4081006008500e45049074001d0001c1c01e8065580704094903240c80202000305001080c00d002d55140c50 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 624554181 1250 624552931 624552949
    0x1140306090c22180501080d0503010b2b0e070906060c02090a0b09040803010f12030f08180307060e100902060f0c010f0603050f060702030c21090301020a05030a0e0c0f 74
    0x1c9800c0c010105401040c110f0765078040076400c01c510200c1c0c0c000b4068040d90203402042c1c01000700d5801009840540c040040042c00706001d5640084c0001130100c0a602131805990b85123081c0ea0381c00400e03500c80030030b2130000b05124414140140910500010b622407248608003c40301c090310b0f01d40826880d5800c1004002c0c00615444520b5a900003142c060b8840c164003503c124490310161386d8035410030403d440060000d60210640d20000068200002e900ca03281004c0c03181e050501f105a80c403a040c0428924040326284c0480f44000300344081071154070f0b0008070010005c42c0560340401304441c180700c203031845000c01075000201008003840056040c002070896190240000075085450340100003550244e0b4010340b4154407002000c1012402489032607040f0260380021440c103070005010a807156408014411409000168039004107002d0b412a0408140207000710b596000d6660f020300030390070070341e07103000040d2a00040d8009402c001a00800c140801005454804050420400c00b0a = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 624555431 1250 624554181 624554197
    0x30207020303070f0b01031103010c1715061606151a030a0f020315120a0b0624030f07091203050d090602190306090e1501030b131b0501140306090c 65
    0x1200800c500400b040c80b41e03075003e032502e00c15103801d10a07502d14200040c0290003102000d10032b915110404031096000302e401704175042440340040040c2c2c2c4000c490030401c40d403138503c01c4d0040030010b4044503c51480c401c829099103d800300b041401e82c208907030030444949000300c0d5030301441c0c0d08050352101d61160245912201020001c40d0240d011400481607030030598014582241c0b0240ea00350b82c1c9060b211243c005c2e44e54000800c013107181602d917150180400307803030311b40103d5884c013225a42c01c1800400c201c0000c2c202c2919603580c140784101c0e041c0c42c1403c50301d03600010f11000010a052166060542035180c040d96458100f450032010745004021000e0f040324026801c204201d59000c0a01e80c480c02820284c43c0001c0030703803904031400d00341c8000440d65201034004010074004035070411a1a410351743c000b010380b04d00343da800c0b00000fa03005043c880600f8220000c06020150006040c020007921000c1c0e94041c00350f0000c030ba2030b02c0c0c7c41c0410344589600c06c03038841c0000e98100300305010384250 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 624556681 1250 624555431 624555433
    0x50d0c090c120c0201150b0c0a020409080a020d210506041d07090510030f0f0624030c0501030603030e1917100605060403050d0c0f1e030216060f0302070203 69
    0x440d569244401196032290648020420300c0038080c091100e144100c0301c1d02409800213101d0640f0352907403211010070a004485a250f0041800c1100076001c1101040e03e55001e40100030305070b1141001c44481c0c01401d082001485110240d44003076208100710038005d080f0b40709414101001207181c0005c1c1c10000c0c00941c00c1540c3c1e1082c0c100c035809203504d041680e04400050b181a9003004031034401d4a10081035425880b0410004000003410360103a040c0954120607400c1c003c29141c80c1c844090440351046c04541075250000c90041d0ac01c1141c900103c1e03100b1001d140340d25540c0e00c015030507034941d84400750204144070b6101d40e290410f54241310007440300c1509508804c0d1280c80b441000201e101413011160700c10301d6100c40700c101c180300e0b03100138020458101e0b0400e49960307996503803042c4035070034001084102c0e1031110030000c96400a10742913a01c144602c0a400c0b1640d030b140810411544190014400e299505070140752425124003541e1941e03451407541035240328290042d5102032003c90701 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 624557931 1250 624556681 624556703
    0xf0c060c021603140c090702190f0c031a1e01150c050d030b09060a050603042306040609020f01030b0a0510120c050c0d05210405010e060405030a091e050d 68
    0x5a82c0700c0d11000074600c2038000c2078603031040454007840c00300210001801810750000303000c1001e400182c401c2c5083d2240304180d203204042e180072a43c0140c0d0306030041030b1015042000c002c00111007070f07102101d00882c0c1505407903541d401051180e8104050701141031102480144010200c012409039000c0ca6800c0c003988100c140d948682c9800c0c00c8841160000ea99030111100758a440d400315030b00325400b224011045820240059210b210181c401006000e2516040e0f8140c105108004464800041034603103924203400c10101410400c03008038032411b00d01c0d02c000a298041c1c49240e4a800010b811118510704103000d100d050003001d02614140149007094492421190013568403040307455813501d8648103103881c820b191090091030502031010074041000518525020502141c620074540303000364640303050445c01807801c421020481c0c0901c0c2c1c10001070010000080624003c641d440c2d0807074960300e50f840c0c3c0f00d940f0181141408220002c000b0440c0d841c010300c8175082a0b00031951111 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 624559181 1250 624557931 624557953
    0xb04030b090309030a1103150115080702070f090b01080a1407110f0a0f0b0c0a05180a050904060504140f1002090111060405070333090501020f1204020906010f0c060c02 74
    0xf00d00045c0201c121002c4030f11220016036418140207a106070710311024013000e0755041002e0f100e0001c0c03031150318400b000b04036000540e03294801c11110001b003c070b0045427405542c6075800c25000c1d14160516601150052002c07618180c00c0c0d118000e80c41102444141160301e44600480d840c0c2409141000c03284180705890035114401c0c0012803001d4441c1b09240f602c1c4060b450301002d00c28004001c04001c040621000221341d0300700c0100c60b4550700d6003108444003014040000c1d034501c620340105400c4900c0000300801c00c502544818003881c02034035061310002c00c112200d591801030200d1501950010ae81b0080146a83d070050f08418105040444654400d1001c441c40c00308115029030340381e40074010810030b1005002044410b0900f000c0c481e0342081100da00c1000309540e0601d90f100d1540d4404401041c0002035041c0c44485200211550703480020480e0902d008070265070a03403060040202281d0158064100304c1c02200050300c5024802d2f8940c0c840301c1c02004c460b107500702540542c0500403 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 624560431 1250 624559181 624559183
    0x270d180b0a0c2906030c030f0a0605100909050c0f0f030d080c07051203160903390803070309090207050a0206070c0302090c1908040203060a090606120f140105010b04030b09030903 79
    0x55201910100050480c0c90300204140c501b911a1a2140c02600f04800000c00c0e074001051400c0480e410640100b00b54450340070003407202d4015403008102524200c0c061302008804201081085012a102208500b0400030800030310300b00ca07201d560561281100855050103030b41c003143e01440032a40a401e04101f52907207030030314141d441b0000711424000300f046640400940c2c40c0c0c041d0000c91400c10f1080c1d0a544d0b039000320350b00001d840c4128082c0c0184445c004041900014109400c07813a030030700aa603a405440356690050034080340881c07032250000c210194030b0700c2601d03c50381c0c024000705602c2c07040b030b001e0140541c403645042e5a243c1240070040302585070000824011a0f40000341070356022010b611070740010005080d041000b1210b0140b00240e500018425000100e417507001a0300d011600d005c10041000e5441000b81600b411418002c0c40505580002c0ca18001c4107184881c2580605841c01c07207000340104d0840040c2400144042007801d0941030b40100810308903460b0620a60010f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 624561681 1250 624560431 624560483
    0x3110f0f090a0f0b03150d1209170102070803070320072003030a12050a09140607020d02070b1c020720030c0a030b0c03270d180b0a0c 59
    0x40041001950040c02c1c10569890001030807012a00c8042c282842400c1c8014030010b0003203201040400e9a6942c02d03511510286881a4080103c45101c2d48480340904500c000d482114003900c5401140c0c284000103000300c6140f582d0000c0784601e141d5500030213800030061051585178505584941d5400356150000400c1001d00032080c040d0341d9440814a4008100a048494000e4005020f5410182d4100204c54103d17083c0510208056540c00d800f40002c21001c0300151050340c1e05402400800004100ca81c016801542610703001034203090180d95415451281020303000f030402000c80d00c181c240b60b01240e180140701015242040e00d80f65034107505500b0407100342c1c2c071051504000b0645410170440e0985202554038040360b41ca5502d071494200f00042078014180c030b000000070102000101c0c00c05e01681c10b220850710b07034060165a60303070b0769003110141004501c402c0340b05400e046052110904a614072001d180c50030b40c00b20002c880c11038064008860841c0d02403044c0618207114000c07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 624562931 1250 624561681 624561697
    0xe090c1905031e0c0904031103040906090509060f01060c031808010b03011b0e090615120403030c2f01111605071e030f050a1a0901140f0703110f 64
    0x2a1115035424681010f0400070240020b440b00c01198810b65a00a03001c41e5072604044100e4050869a031281020f65441880080b0300e02035002c0040e012032807004680c0020107072141410304003c00c1e6941d50009590b24002c2e81d000404000d51401049164401d44545904620914011060b00220306980784031480a400040a03039456815022081c14248141d02905078020200c601d540002030014080c0348540948034050310b0842e001814544034015580300300300041d10f0517961002a0300d014030f0841c405407421000a401c00e211801014860300e84802038414000786155641e40710b007603001c105000282d60f1000c554903000e015411001d400042c219401da80d40142d0b4000d4900e28190781003032034940010030400300c100225500310410070040d006503a401180110907030490b0a1117841c1064555006201d02d680603030410117417404107002d900034030f4198001e118458603081c1420802d0300454441c2d41e40200310703001030481c52103a0009800242c80c911241e28000e660340c0b960505500c8106 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 624564181 1250 624562931 624562969
    0x20607111201141512121e0a090b07061d030309070603150501110312010f1d04051f180506040b060603040f02011404210b011e0e090c 59
    0xc0408031410401a00d00045212200811044060080100c000000508800c00b82c0c0322080541c1c1064803082d014405d40000c0000725070340c00362280d0841c44117600c0a1000305280e010f8600c0e00c0d0f0a000742c1403e440c11050f9585075240350b942814962200c6400c80041500e8807a2143d20114000c0750a451640c2d05440f04009595645000341120b0314008250344540d0070546441c1c20748602ca403100c100c1809607002407074200c2101101040030303459402800c04014a01402100000722034101005250482c2d2082802d18036100d0900b02016002d00103c902800da500b0030804045154201000c00706020500c0720000341e0401243e40101100070359010890341c40c0c0c410b90501040c802c54828541d4010b104481c03891031427903c0e603a1105000803d030780083c14031600d2904e060070521281d0549016011a0a64000c0c00d84c0c844180d801140010205480c44080070002245a0808217441060821140380b103440035880c0c1f07074040c00c0c2103000074100c80040c02081d08005407076543ca840d010060804a03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 624565431 1250 624564181 624564203
    0x7080f0a020a030e060406320a030b03101b0c1e051f06050303040303121d0c0f042003180607050304110907081807080d03060806010e040b13050a020607 67
    0x114001d03011400c54005240301c1c0d1000c2c04200002507000300303402c84c042d14001d003a04040c506903400021100d5040c013a4100c1c1c00020468000c271981c0f61740001c1c10746c42c04408403196041c50f0f80030402210300039060040700556000c0940c2100d4003843d10031a25034452012501c0009006c51288103225085404840e0b523000391040740d00300b00c038181c40190121a485c90802000d8034000020340e59100310303c4018240300030300703029189500d40323a84202030341080803103188200c16003400180d1322080100411071064a41c026a80041e0419202d55208002440303000c00d110311010300504001c1c0c10040c07007401d0b00d841c0c0300b400144981d0248881070080000b41c0f1a2034690405103000207115815000b0307503010762440010000d400b43d10507002500100803a12516411417600d6080e81030508640148825104020364a5030080d89a4800c501f151148000c0d070b0314071390302e411840c60b200c98207a401820420310840171912070281e409100c6809482441244d20080155002c5480c54200700c5d016201e0180d81 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 624566681 1250 624565431 624565433
    0x8060f010e060a0c0b010f05010c2d0803040201120506130216120504030c09020c060406020d18032307020609040c180b19080420030309042408030c100207080f0a020a 73
    0x80301711503000d00904500b0981450030700e00002c0c00700e13a41c001d0181c64018a032084103900300b188004515604100038403100c0e8143d650034081013650003a50100e0001c0c0d50340d44046480308042c40b0b514002c0d400144010060003459415202a420090b440403960965545c074000003480d80d071940c1c6540355143c81d6640c44900e50b0402e45900c0d0010307803080300128010031107105050310110341d183c0d00030381c880303401611a9844003500005002054074644216881c00c0031809250700082808803201e0701000f403480e20045034851650b503006440c1d00a420403020b2040407058940b941005204000d20f00e0050880c001c03907110010b0520141d0f0000d140314200040703904080400d00780c121556846400d058202e0708150360350203010b825550b01c481c48103450182000752035a05004a40e11464003d00a1007141503551041e215582d00c9401d50304401c01910000030303040000710541c1c00b00740014000c0e201d625405640b19001c1d5000711000c850101c0204010b20700320350820302030500304806500400a0401c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 624567931 1250 624566681 624566693
    0xe03040e1b0f0a03050c0f030405011b0c0506040f141009050c0103050c09040b04020d090302070503070f0e16020a08070b060406091b03020f0c15150108040308060f010e060a0c 77
    0x40396a071140c080398104510075180142c0d0040b10070704200380c40e00040a075118039071141180100c0e02c10f288004400000e00c0123005054003d038060003080c00146800d41d107440c60036aa01048418000c0054200c80c0000b404500c503540410b806074003460f0010412008007400c242400c8460141c0c072000daa41d40718480a01104000186d8410320a090070080f900b800c0c501800103010380b125541c400c60704d8203802441c0da19103405507201200005e40a0180e01e85600d8040d40361007190184134003d1050450001f002c9800305d0300c2c0421611164031440440e00c4040c0c079140b8000380000510150300c20300c00c040000980340c200404405000b41300c04182c50502e0b004000950b410348e0300c001072003405c0980010220160117080b101150749418010b07501c000003a07241040b130007601314196890007641c062940c00c80390001894440c0c502810070b590a080c0078001515086029240900040e502c000051032508168591081c0c02c241414402c451a41c0d6600103205036100400280004030760740291010815 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 624569181 1250 624567931 624567961
    0x7080f070e071e030f0204090b03120f03060603070318080c010c0c0822030f080a12051302010c051905070501180b120c1306031416210e03040e 63
    0x4100101c201c000e06000c10010b100820034040c40d1000050161100e031164081c0c2d1210940e54168141135464665580ca000c00510b098610a8000e0081c0c40554541c100110102c0300420507486045045840d840203002c09900000d004905040d40c0b0341c0400100d074201448844458451a500365844a10010381ca0943c0c032251184c1013406400b800030340000740f400e070036100345150121242c2d00c05802c0142c204140107085c0d001400400c00c80583c01d09101010005000c1c40c601070726a00b0705206040a8030044070800c968620780300303810444000056106600c60039215000780129140d40c0601e000c9000403400641080303e495002c0c42040066507003049420341642c141200301800245031042c82003039446070b01443c4003095205000a0034121441058402c2e800f188500e003041e05803a0503010b40281401e40c400c402c01611000054070000c1e0700b082000001003103694140746158a81100d4079800c1001420440ca640c54074260310b81d4190410150008041c8a43c9100a600782503048152081d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 624570431 1250 624569181 624569189
    0x1707060f0b01020c1003020d060504050a0c020105010b03011d060402121305010b010903051e011d0d08181c020c03100b0f01050309061f09020406120509010c0e0d0203010e07080f07 79
    0x500080740c000c13840d070358007060f403040e8001030f08015a5504800c1220710040c103540d005250300c6490304042c80798081340f6a000340e04045190f002004580d803100078031203040c0030034890110080b40136002c900c445c1d1418500b55402900242001d8201072950440560629003121021982000ca0030b00d841804000d020b1950f4403002824070040d0f084c1140c441c1038580d01c0c074085961084100c0c400b0103061000941c00b01c0c6c9841010001084000ca003400495141c0b11100c1141001400280100d83c0c4011a0f0031a480015003030001401c0c60242c1441c0e1010341e00d0110249010740c06800c03280c280580f404e0008c460119401c58001a1002c074003010000302e021482c5229040040a004000441d00300144444e00140c6101408429100341003074641c445a20b0f4000c411034900100300050400c0c5c00c000341c0303003048107c00e00c1803003180c2d100d41c185401c84844100503000a490b19079110854204400003c0324540003900100e050b000a00300c480c58000c02c0c3e40851303000e0740300c8410740e4040300051200714060 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 624571681 1250 624570431 624570433
    0x14120a1b0305061305040c15050304112e090b0301180e01110909150604270b03120919030f021504030b0105090c0d050c0301060906080103050d05071707060f0b0102 72
    0xc0e06000b000701d001c0300416544c401610381d40350040b80500144d140001c00a000203050b55a4402060000802c680c00c160740888001342140d00e904424500702c070102d480e014942800c0410000000001400040000010b20034011422804210302156000543c00b8001e01d01d00440710788000744032882281c60005101c0c0082c0d01d880c20240c009990282280c0e0707103400442d4207182c55200e03114450b28059060070f0440d808000058000b0707003051101a40c0000342d81132070361000412100d10580c1d083d201c04001c0154181c101900d005d000c201488090300b01101d000c3c1114100d50726018000e44050410b402c1501e4400340d04e08803c00b1450b00c4008031071603c11501d070890409103951740e81c101400c011b004070b80c400d85a0a00240c00a240c0809481246141e820180820300746202c3d5000360754001e0103980c00282d0f51242c0450164080c8021a0480340c0c07060051802503045001107980c0d81040004585018a480c07070314000030fa605000e0040f0034001c00d40040c50b0f03c0811590000c81d0460903906040d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 624572931 1250 624571681 624571691
    0xf3908060616050f0105040f1118010b0c010b0a03060509060c0f04090c0507051006050f0303040b090603150a0b0d1d0c040e03090a0b0702040510050a0614120a1b03 72
    0x1640741c100035241c40d00990340c54034201552524110b030400051081d40c2c074040d842d00303081005010600341481500c502030544103424401083c02c4c802e8544118981e4000070381844010414040d00c0002807102480003c000900510007000094025804d54404c2da4990b460b0030612103100c0090244c190041d0384408032600d0020907003101c2046000d903209800816550301d14160040e8081c0d02216610395000040c0c50f4030325030118200c002000c49000311030203115150120f00e40b80c14000300b01c0382a200b010781e130035040805c60820031249501c0109006011050350601054030b40701c0481c0d03100900701a081240d01c0b03402c0c5001050448404140110540c600b0390312007080490003084040410f10700761404524045180c072010f166201b00d4022a811040703107040001c40e88110409002c4080c4201c03020721550300e034030410b4400101c1a004440e0321202020027003250a015114030300030940c01356001820f0525a181000c100c003000c940313011810751650790b684001c2e00490400100a0b26a04040003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 624574181 1250 624572931 624572941
    0x11070b0f01061e030507022404142a12010c0512090106030b01090507090302031c02010e03090a06051b0607200d090911090a060f09080a05030306040f3908 68
    0x100c0512803070f5500138180e80c0c5011420140c0b09004200355100141804030704424100c2c281440400222000c0d200c1ca074002002882d03d01022600307600e1611041e1801c0b40d0414001123a03403084503054011540081035400420261600313014031540d416203500d0301c3e52507408465955041c400c0c0100114043c0e4500082400060340703d45d1098151004000c0000f00740d52040360541c2c660700c01d0307007000c1c0d4107204007066842d510b800c8584043c0c8414081d8000e000340081d0011059807401102c102c00c0d808001102c0620985104401409400d03a40c901c0550f020070300c041c0700b1410f0440980d09080042d6021a01d05038031092045aa42c000c240c01000b01090b42000000501c01847c2d030003484a4241c442189004010800043c1e5480d07410040850514503a03810300640168031111250020501060f00000c4840b0b010400c07955046c0c0000103107155a41784410400203101c0d0600040381203680720b0b401102504600034405030001d414a841c3c0c0307204c01100c5400c00d980103c05c46ca038204512441000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 624575431 1250 624574181 624574217
    0x30c060e01050304240e0309010e04052202010512092d100209040b0402030a3204020f01110109051e031c180b0c070c0e010617040611070b0f0106 64
    0x10703130300a0f00a081c0303010000071703840e9954402c42212401042a4100142006204808401020034403401d032501103080014105010954808450000820031480c0c044030741441810600d5151610500d086841c102c080fa04404042d24103a8000c2030300e074081503410740008149207800d001045064402c034021449484280e585000d00c134400100c2030380108004625440e03c2c0c06c5180040c0000300195228540034407500010704020315020390300621800c8250f0300c10b141e00d801c02590003030150301500c99511a001e0100e03000600c60031a041000800e2110a05242032040c109514800c030302409803800980c030740c0000d00c2c2801c415900e182c0c2080248030115112007001700400004100c0104403000d5480040411014503180035011000a008119800030900003c00c44148501070100903951070380301a164000c3e0900030a000321b4080c0c140b500248a08404a56100748a030402140740740e5100c008203000c1d0000c10b001c85506080009111040420b50720060140c0000e180c03824a03440c1e840039403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 624576681 1250 624575431 624575437
    0x207020f1002030d0903030b040b0103090305161b0b030609060a05030c0d080c070f09060b1c05040f060608150603010c090e07020c09040807030e04060e1f0306050907030c060e0105 79
    0x140c0300c0c040900c000c60001d03000344103888940da24420100211105410b01901030501c4605030ba10580c82c10700503032255070181c40740d609855016503e05041c403080e00143c02c0402c4001409072905038005c092590103880941c0c0c2c00380506143c4902c20b4903802c03d10103004e03000c203001d02070341e2081f51001e000707001035100010b188401030011100c030007190245060448441c450b21141c02d907a8041d500e004942c0c61507010072482111a042c0c8100401030780c4440310501e034011110604544218141d03c030403061181e801440d00680103004110741c2e413425960751030888059501800d1141c00c25502502c40440c00010f16601110680007404031085a680081100b10103010301040401d0001c0468001c0307100300603045145401034042c11050405003015200742c0c1241d001240024040c000403d0380d401d0070f0003143d080350020b04580a06403038112018000408504150001c00180440000421060300816019503000800391844038210705200c0034869681e040603040c003001d41514040f59a01c0303022 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 624577931 1250 624576681 624576709
    0x24030c0d06121223070f05032d2107020f0604060f0b040b03060403050a110f0a061b090501141c060509061509010c0c080d03140108010e0a14010908030a0b010f03020702 74
    0x1c00340d52050f5601e091186c0c4d0702981c0c8054660320010444031929101c488026000084484484070108100d0420651074030903c0f00003042082600320040d00904212131075a00b00781035005951008490a40703203031a20790201c030141c07002d82d142c0580c540a00c54510415000c405c0982d001d2182c80a00d80210f551130101800003000c000002440c1c4900e02d11905000d5201d0701d105e400d49151941140542c1e6a6940501042d40c00d54540181d80f002c05030042c400c0300010005444114665142c6801501e1007440201000882c40d000c0002004901d100c002c3d031400703418080c000086032801d02081c03045034079004141c50b0142400040304041c9154803410b65007810024a04140003426915055410110340e500c03544080c41242480703510306070075400181c05801907201480030350380d035040c5c41401d03146911200c04a582000100002142c48000100105003007c3c0020580715913070740e1000c00903401140d505019580d10074400c441580e010b80d030281e0340d00e0180790a5062040d25000036452642c4144 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 624579181 1250 624577931 624577997
    0x60d231f120c0e070905150c0a02010827060103051e120c030913020304050115051003020c0705100519030c051c06030503030a020d060524030c0d061212 67
    0x4100d00304480140d07144082c11220440f01c1c468208103901400344111405814403480807280c1c17425006e407021081d02da803602400300414031042c0580040d030750326034080c00d41100d405244903094082450744401c8010a500300004204640c91810b1890a04048101e2050701c44039411801d040e00724000f4040c1c5920000c603c0c09566041c1c40304c00580303181301c2c0311420340d001002e1514180c896440755014510440c010f400910010140b0194003400c1c81140c050703250300102014a003800b943c4264003a0100c3c10b000d034111424a62070302d0020302c410001059460004200084510691a107061801302d8000b1604003802100c01045000d8081d0041c1c05904c8131040180c0c0b0442d841074226040480110b4201041d250350342000403016010b0b52204040800103030401d0300c001000d00301004d6a4a580c0a0820322548004007840700c111243d00103090021100018441c40304161818454034009000b01010028045d00f0752400f00080c001ca5102d101c10300800302204000295a500c4d280a41c0819403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 624580431 1250 624579181 624579209
    0xf0307030608070e01180e07060c06060306111b030a1d03190c0f06020604120302030403110706020a03090506071104020d020708040b0a09080f0d0c02060d231f 70
    0x14100324020440741d84080c6543c030604000149419a440307445050380e0504480e03da110000c81030386010b41d14158000c00581e8040d11040082c903201f01a4804428410800428420307607a40340d81003034503400c00b0700c0383c400f50000405007443c1c1800c10141841c44c1503400503509040c01c10300041c0c04400321101240f211402c007091020b0544d02442400079a010031120303101d100701c081c140718120000f18056003a2041d541d940220320382d07000140345e91040d41d000c0c1001101e4181d21408070003a42002c0c0c411418008076904100c03010601b44102c0c07010300203950040c0980e030713400e040c028a0b9010607409107002d00010411440854440a003d803416201610007695985c452014030000344662803025156103000f190101c0c4a41d908002040f0000c001d0752503034a1141c50b40f8201d0781755a054a20705105510444203020124001c4030f40d2468140000e101605140300036500506a94001100410340c03c3c0c40441c10480d002c455a405801c52410b040114441c5480d43e2a181c8100040c003c0054001c541 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 624581681 1250 624580431 624580441
    0x818010f1b0201210905010b0103060b16051c0c03020606090106050a2001090809090f0601210b1005120106140a03050907050301021b0118020a0509040201030f0c11210f03 75
    0x90091907036070700d4021144c00041c1502100030710013000958000c454035424038a50861540c4240107000541752000e070328601d098101148481c00b848081002c4405001d81d0007481001c1c4644028001c0180007600c0d506031070070351840c0003400c01030001c140a04c0343e1a20f500511006502100f5101e803014141004060044c600840c095804101007465465600300782c100d000300134002001c0c004070041910032017040e459207581004c000c02c4c2100c0d964000703441446d04220944013035100d1f024121108400240040c00d03200070130340566002800201181c400256080c080381c1b41111940144000e00d4502c01600f104100e8450078415004204101500d9602055040d18148200001010000c000315500c41682c104e15042c40940e4010181c0340d403074010b891040d040d00007604000c0940c010040d50310345091a0810183c8078001e0001e904241c1d0307514448032440294480c034230305013480707407030300c5d00c40f048000300152400b414501343c0b0140800c2100ca00c0c3d401d082c01429542080302d4411603039226954 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 624582931 1250 624581681 624581687
    0x303090320030607020f01051005090c16060630120e0312070320061006051606150f140d0222050106080a0f0903090e0a0e0102070818010f1b0201 64
    0x400340c490b030341802044280b01040350000365042182084800030b200d15614000400c2c0b80510354450150014491800105581d4848000b841d45001c1107040004070081a02c1c0c0b00126005a048025441420807074002c132003200c0c00c496840400e0001f0740c189503410990355400c404c0035003840941444190350b005400d503a0180070301541044c10100c82074403003c850a00400300c001c520021003440003052900b1500e01c2c0b02250152141d100e00c0154504545003543c12912940700c89c481854110003080c034400041d225002d0000c050f1480e00c1000192801c01504e066205540d030700001819011180d0400191241c0c1891984560100c841c00800702e0940340400030300c08401509000b461414002081d1940c0259141e0b00404106204001d00012421064200ca200002c0a80890140041000315440c8401c200d075101c070071900301007085111000814203a0704408000c0710400804110041d40000c20580098480000d107130090350883c0c0c941d005480003000c00041c00707071954542e55200035640 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 624584181 1250 624582931 624582983
    0x11107050303070501091a07021c1403070903020906040c1407060204030f0f1b050d06050a0e100e0114011a07020d080307030b010801051f05030402043c0603030903 72
    0x110141c1a20381d2090140b500d5030082240d0340d8101c525443c070340491285a07004d02c03881840b503403030b0360020842c0300c4050081d0000c2419108a1a08100d018410345a008800b00040d6000b100c0795182d032031105003584104140004001c0c41c40c4d000300d2419010642d40c5074002000003203120080c04070743d901c2840d070034210701074410360300058603e015514491042150080c5440b81c03150003080c42e2150084000312005040c40701c1e1042c541d0240c03c40d032100b0701161140c1c0c00300c1d4004298600000e4841d075985078850400340170701c0a90301c1d2113984106c01c0c1d502e04004e0013900e071a0381d00108007001960400d81e0007050403907401601e5249040220303a02c0300315114130100380c0180fa0002101a282d190200004002e44400080c0d240000d51540000481d401c040303c0358403410034620100c000050710904200c8086d00000e00a90f031007512a6450049a10807152900309031f454400d05c00c1c40e65030081c1610070028072246201e89840d00e0800104086540424000c05a0307600c81000640e060340c114080b1002c1c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 624585431 1250 624584181 624584189
    0x9030a0818030a1407090b0f040b040e06130309080109030f0819140702011404081909050901090204051014030105060711040509030a021015030b060a03080a050306010e03030c0c011107 81
    0x11260070442018400000004c4422080c000d00b290f2055403250074107001e94141c44c0e806604070314881100380d0a843c2640000319070b410003400000e2409504130000c0d20386401500c401d0311060f907126150040c90707413051002d800350945e10024800160250760050040c5001c11215003001480c0300451648120078500f0464000c0b10101405040d5800940550b1800309507040c00c00b640c13a140600d000004000005c61180e174014054500703141005001500500b9224490b82c1007003a02580461540e0351000030700d029108407900140c9482c02c01d424800d00b40080f03004c0009214000d13125403e40d8034030404483c1502d10907145183c40713042071328001d01c00c1c01d001140184d005003031200300806684008050110340059a00f210010720740c2024890807241040008038003580300400902c040350740d481c0700b290400c4010b80385900141d41d0340c13030700d104030b4000480301c00c00100000240400d0b5070744280d024031014801c1340a50320784a003c010180da01c41012008505004915440036a0300034180001f82c010 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 624586681 1250 624585431 624585433
    0xf06120405070b070c0e070804030c02090705070203060406050103060e03041a130924050d080723031b06100810050709090903090e0c07020a0b0706060f0e06031209030a081803 77
    0x50101803814002d20381c2c003405a80c1000f54a1b50000d42003520402c0142d006c0d41c2c25403110741801d6802d03028807600060041141c801e100f410460031005032010040c9a100707a004440c001425411442c002c01a07400c01100181e59510a100a11074074034101c0001a8451090821541c4d400c0503000c1c0b0300045956511000ca03580ca4010122074a03802400a05c01c040300c40b2112502060f10b5808100f80321540920290640909000000c00182d50014482c62020841001865151014205031440d4002150000d40c1180241c107030402c4481081225040410000003030791190400c4201d82c0c0d200401020740f8852500d54010400080c05060ba16018017031100741400800040d0034041c0a0300198030580c0100c0c01c2400c00601c01d09404016511141c0d4000d200036803051a0a1000200313420100003500d5407642c4890020780e000f918099840208004034004810b0f15140c130805041244184000c82c0110040018500c160341c085440d070030585c4d0180803d61a40c903041043c898040e807130f5040d41c2d05 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 624587931 1250 624586681 624586687
    0xf190f1e0c0908060903071b0e131214191815080105030a080f071b0f060305162709020a03060302031603050c09090f0a061a0f06120405070b 62
    0x4100c0d10303030060128400c0c0d64848030040e9684103003040d90780d5412070341500e131508107008030f200040040d1082100340803802c20003541d07a919199180e0742d164040e60309600e030011902c191420084548609599602d03241400b0030070101080c1c01c070a16100b56540c030568003001c0b44aa5165a00801580351070320300844102849944401c0d20880f481c00c0c0b85015400b280c0200c0001034541344c0068541c8906911440d0942400900300588030990818602120488100c040e2a81c240500030704140c0141742035002e004c0ba46107848070103000c494020307104440d881070305000101c01581207050b0410141c0624410781405413049155080720b01d403604581c441d6400054403840d09035258000506071b0b8002c03415a1000c0303803503130403242401c001480002e12079004140c013080c2c07900d0000741503607000384400c0580711902070340e813011410901c48800880e030040d40d03942c440c0c004011aa283c04000382c0c00340ca103110900c401c200081c440d8001d0f0300000c405aa460030000702000414029040140420081551 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 624589181 1250 624587931 624587981
    0x7290403020f060c1002040f120503070813081c170906010b031504022a15011806090903020a0c08030405090610031401030b010513060b0901030e070503190b0f190f 72
    0x400f1f54054410102400320400d00428415620501d140c00d8562140c000e51401906a40311500398101a0f0702004007100c154002501900038408110384101510404481e0300384280c001d412100c581040207110080c030002c2200d0084006682815614660007164582d60b80d044400c0d110319040140a411a0001c1112185200c000c0d20b00e01001d10b003008040e8512070b010ba001a0f03162403224a52503802d011000401201d0b4801f20002d0062491500200b096511030101d0750949400500c00c500590002c9884e5041c44000146000a04412400b541c84d0503d8080000c0d504c0381c0c0540814807403801c48071142c2220b4020f5001021007800e007442400c246d03940b030030091a409001d01c00c1d02c1c01881d040e004107502034814801e40003500c0c1c1c40303644581407040d10f0004500500185011048a1003085e602280a40d410000a203190b036462144803101070917071820b000748940c09003051441c00410b00c140481d00340c020300c2c081c20401c0358441c00104050075048070030143c01c410104803004800505514 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 624590431 1250 624589181 624589213
    0xf04020d0e0a020f044512020d051c05100911030106020f01201c0f0c1404060e13020415030207140a050d0c080c01020c07290403020f060c 61
    0x4100ba4002c0341d04a100c05041c07000d21080e10348104412807648000701e1b0640144400e074080030408403180710b10040c0c06503140c00b00c540b07103604402e05440440d8511581d03160705e80c0c100050319002c0300a2a2050407d1b411000310807054589140450b020f03903d50000079001d0400c5d640c6100240b00100c824803991600d840c100c1b4a03503100b8007500d03006000e0031421406c4940140034083c2c50900151140c180078101c011041c032150402201e462511400c1500d0300d040340d10368050341540c6000003900040500031810050100002402c0c040035001042c0410099070b6000502c2c083e0b1140261080070705600302e020000028031441c7c010300520024044030301043d6074943e0140010611420000964100c44a40c690782c40340c012600030842d501c04510711818034800e0300b60414007445803942d03e050071140704100d8260f800590b40c210b02680f040030708200c40a409a00c0320310b964011003648900344426214003800d031040c0c1c00040c1c0103031030003d032a82460301d8010441e10001075920944003130400041d029 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 624591681 1250 624590431 624590443
    0xa0c02100f020610052202091908210307031509020705010605040605031603080a02070302031b09010e1302060a090506030a0e0f03280e06030f0106021203090c0f04020d0e 75
    0x70006100d20800038681d100c000c4110400d541008041e42030043c82c840c3c01d08a0352003e80700c05803110340c00344803010701030301c0d189002c090b45060300c81c4502a06050007512440c102d020f41d0604141e520219000c9510381040040701c0c0c0100b0145004078900110182c2d10344049030703542c40007644c40e00c009402c105100045d44040241d48080b101403143e075a4480400d0348d00d80e2107030700040c055800d9000410006100000908902d02d05d070045e1030100e0754ae07030002400d0405140e803004070b003540900400c00916003100040e01400c0d07909078140741418440c071040442c6024010080c00760400065200030f241c0190b0030400188030003440c0c10355034500210000702403d012018a1003030700c2800302e08901d501c8080103940d081a04000151010308070642c901c064115031803469014060700e1800707581991034030300055218182c0d011444002d5403410500a10701911045100e41410041c814001c4442c0c0218140000c00c030100d808400440c0250000f400a126803000da03801d0b80c0c50701d00c00c0c8070008000708070 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 624592931 1250 624591681 624591707
    0x4020f010c0c081f0c020c1e06040f1a130e040606090c0e0a061d0d11030d050304050705030604120302180405011d0f010b070212010902040906050406180c09020a0c0210 74
    0x100c2c041c070041e25400051725103e002403409600b1a50600c5040d040031010420301c90750750a200003d820401001c1480c1d90320640103541c0300c1043d001c0602001141d000030303980c81a0301c40d042d2480d001c1254001102e0b0180c0303000d07d0740c4c0980c114000c201801601c0d0403480c080c0607020002c0100312568000601800c50100c2c1440c0520006030000880c41e020b51f015415007016242e500f141c501b0040d08119001014410071205580780200c0c104481d142000030703000c0c248054a42503030f03a003003605040d4902130356540071a119a200e40b00700030005200c07400d546191003017801c0150311010b4480c3e680300104d01c1c070403602c2c0d0000d1500000040122a1601c041c209001c00e00d0f6400240e2102c0f90340082c10038090040c480c0c81e0201300585070043c2001d160180c05144498000a11504503038000b4042d80c5088000b0b0300c070742d5120f0341403001b4403c251082c2c2950500200302c0315101a40eaa803812072100a5201c2c00d0a859404250b0400a6015010b41445075500a0000782c14412842c0040d11503400306403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 624594181 1250 624592931 624592963
    0x3030b061626120702161412010e0307032003030106050d0903020a020d1104110412021011070b0909071e1b0b0f011a04061e2601030b06010e010804020f010c0c08 71
    0x8000402500c1e5840c0e000517102d0000d603864003840860280100b238041d02845100941d42c40c049440e050800344007800109200380e4940542b00b000c41910741c070000252243c0c3c0c41e590001c000410007030b074200d000c90300401c2420358081819a00c1e800d045e82440d05c0008040e40000c900303001e5404200041d540610b010504036030800c02c1e00240704420030381d40a0b6000d81d00f00d0312079401942d4090300d0b04a20543c03070900980b8206002e001d00655003428101c00d0303401628107410216010402c0c0c50402d035660b510414502d44810802c4403d0300400da03280680500da003d018291074046807410403407030031402d090382200c0d0321034050800d041c0d901002c25013403282c5c490001031890221000c0514030200c070110744030341e99403070180d80d1068002e10503c4200020401807001c0004018100341c180101000803c3c00e41c01002015807460070204041107000b800303103041000071945807646070707000462960895015504c2e103081640d42c0006844140c43c90002404074112100c00065001d000159101c1c081c203040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 624595431 1250 624594181 624594193
    0x1c02010c0f150609050a0e060c0d021306090906050105120426121f0b0a0f0e0a06020a06050c0f1c1119030606050703090b0315060f040303030b061626120702 69
    0x201b225049981040349240603070003a10220744c200c045000545800200c2c48001458200041140c241d0030b03525512503070208101c0141000501050b10484000742428240146012000c6c0d4058141c2000200b0080041028886e100124403280f1452301e0724841848143c0e961f55291040500d00400482c2e01401005103002c00e20040490181d030107088641f1210046c2c03c00d07a43d00e00940d1018a42c0d418a004c0215501c40e400ca1a034903803002000900050700a800c0b0f0058504128040c0d0740000d22035500310108104e02e110340c05c2010215034078040d13450300001c4081800f05911019046605111401140c0410000030820b9003030000a0b900d0b41c1920200001543c4400aa409c3e0294a10280124410240c20451406c1140056a100008100b02001c2d009240300090311a013103440c0d0741104001c04a414030815806205404100508884450030080d0281611240c070b0000380e00184541745c0d005001c000ea0024403003e03000088980030550300c40417070030558054081c003162201c0c010300c120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 624596681 1250 624595431 624595441
    0x1e0105100206070503250c150c050307050a02010902030d05090307090b01020309060306180a02180604231801080606040c0e09011715040503181c02010c0f15060905 72
    0x5945246000e039581e0040c101650741c080b000c0e140d036080204002076003c910300c0d07403901103c0600c0c450191440d00e40c44031191016541400d903142103641445841e07aa10f0030316098804c581080c02e407903004405107441662900c45c220224098862490025090720808407480901a00003010700110b24080d022240c030300b03503200398407010307078966042c1c0381d000d031b00101314080490400800a40e4410000780030311802303001c07280c40f01540450445000c04a19804160b800d01c142c00e2992940100b81d080710903c6c00d1a0410840c040006e410320038003079281340180c000c0d0084e038450346444140703a03901111600035076964508190311107800305c3d29070348550b1501408003c000d020785d0b480751003100094a2508245c3c2040007805e000022880211404c5c03083c141400c02558504281c648100c0c454070142d0307103d8690404c400000c4c05140f280c6c910034a2030f060f100414903072105a03207403e00c0d02460a0301c181e00141c1000610551200c03400b0b020066280c0e542d00c001029504902c08075140c0701c008010581c0c80c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 624597931 1250 624596681 624596689
    0x100e012c04150b0a05210f0a0b0a1d0a14010f06030818060d0c032715022212030210020309150c0f040602250e0115090e1e0105 56
    0x400c0740c00400c600301036105203808940c680c3c00342202110250503a0759081d22403002132290f4a41400203443e01001c405058004131041c0056580d819039040145156651035440d1180d0700e500400c05003440e540c4601910204007555414640c0c8010b003800c1e04c0f07081c800c600340819181640e080d082665800c1c0000744030702c1980d9204e014200d80e0004920f90074045600400481d00200000c3c440d84600103002401031542e152060504080b546d840c0020031060300031801d440754185001e01e07401001111080d201043c810303010111f104101c03900060b46c480c10461640c17071101c03000c00901c0c510301c02c2071004214030040364400d1680354080c3d001c989600c11800300000076884101ea1300c1415401c0100351084816411806075005046d000c0624104640c04044800c00c1d0409d44c0100010307486030074400c0000da01c070210264408296400c01142c58140081b030256201c042c480c014500c8809038001d410140b0902281001e01b44036202c14070315042440300030402c001f0340ac03c50341c81d4000300000041c3d10b2030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 624599181 1250 624597931 624598019
    0x1170105090d0e060c07030203030d0f060e010515160b0f15030a08340605013f03050c01150501090b0c0a06051b0d090b130f0209100e01 60
    0x54540c0e81683c0b0b031501c1c0050100715000313403042d0103042c86040400300c010303902030000c3c0074054408000005c80d00b00e08519003007517a2081d4040d500048201005021a8a61810301d03000001c0c174400c03d60b540c145c0102d8003000441c0b00070000e080b0600f0601803000344495400414041c1c00c41d0f05600403803a00ca14105034403651800c4000381718907000c0040c0240910101411b00d0760800e4114641c0d41c1041d8070a4803c01049a0002101e00780e44d03c0c40140912480070381540030030710030290f0708801001d5880100c1caa51030030f084107200f1898040d10103410184503c00300d503c60b010f03100003440b84016031802040e103440c00f07008060200c4c0c001c040100b03094140341d0940307195403003000092180302181e480340c2d0f005110152040144e0000c41c50050910800e0800401c40c0c01d41080c40000d040a1600740402d40200181c02c0e01045800c415900002c1001394850000081e01100c1055554640381d02c03503564446107502c40901080c1000000035903d000c00c404d551007600d2500304640c1500c01c0444c5a442c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 624600431 1250 624599181 624599203
    0x20f04090f0614041104140f10120606060f14040302150702060a090503120a02031e070f150f060806070809011d060402090609040c0e370e07080d030218090117010509 73
    0x9006040012448e80b03080344441e8000c0000d1051410300c5848003241c0603c465520382c180c0301b150301c410007001440d030b01c0400d26000e6a95440c200c80402014120a151846580300107441002c03500d9540d11b6044000b011100c0b00e50f0b00800c0c440c0c1c0c404103008060482083d620400c2d1003409104238140c00e00091108548000003c2d41c082d41c90038103980d581c00203d021582130300d03404040c244010700c0050000c4030320155660150880401580d081c03840c00d401d440d503100b1407000c200d08004042019040010785540c0100103410080399070b9954400d82401042005c45c0103480d0711001c101c0111152010940902550082e00d84a0455548030207119106030190b50003411155824020407000464100b0359420003042d1341d034400b600080c0c520241c070b81c080300640300819800400c0a03198030341c424441c507c04041d50101030602c151400c0e041e503854212990200341490b4001611a0a000142c00c00040c81e0600601100e034a5031142d5010b955410116031059840d071800b008a0958400000d00b21010703 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 624601681 1250 624600431 624600461
    0x9140c031302060c070803040f090b030c1509011734091a120c0a0806041a04020702011209080c06070206090705060901050d06290403020f04090f0614041104 69
    0xa11070354280b040b2036010200680841c0141440800c10510a000174001003482d1180040e05a0800e000740d811511609000c522035030000d22000400c2e180c00d640100180c040c00e101684802d502401a07483c442c648099181c00180308040240c02649204902100000f007805508010240080c0380c000b010350b02082c00106039441400c00c01c518035a806d00070400444a1300728140100c0100c0750190340810354680d0903e1001007600f0001903481211503030b001c201254207000b07a4514440c5035000350b84c2841100e020310b4000a8500c10369005012243c49491213072030401c1036958504000380d040e009203441858500031200800e08a9100040d100d02500300107020300390541c40c080c10484ad541c06107408a060180520110603400741622541c8000d10001c9028041d6560622500018110b80c3e640c90030303000410301c02400540c841d04e99042d90344205540c0050180b0150804041805003001c00400032420310390608035846052400f00c2c0603a1041105140190420080100340c0e14501032820740 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 624602931 1250 624601681 624601711
    0x60314070603090206090418050d2006040308040b06030f100203162c120115060e060a08060d020f06180906181519031a090102090a0b091909140c03 65
    0x10b440c023a80642d80d440d00c0c0589200c80340545070760b03880c2801507c14004002c0f60702e1800c3c0a0002034842604c442503007140c00500141d24090ba0058220000a040500003d54200024080792010001d4190301d0740b103e000c4071a004440700b4030703030003035071007114111514002d440074801e01c503004491000d406000d070111b500704800709000440450001d81c030035690003019501c607540c880340c00388168030b1484c400d0442400601c0c00d0610142044a1040c032250040c0ca04204541130654000e02041d005002160fa0000c401000e0002401390910040700940c0501e0000f1343c441d00c581c4009840d03211060030348c3c0000d2550368480c10400142c10b0541c054402111440004001d451140110110901c008000c0300c1c2a039400c40d411200d400c01600100e07422456001d0382c3e0300c1400006151395001071068000d520703101c0d0040104100c800640b144e00303042a404a400b810a99612103010100b101d8200500001035881035080c1c09401c40c5262101c807091040042200681786000b180e00c07400c09080309000b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 624604181 1250 624602931 624602947
    0x2d0402130b0306060405040e0c0f01020d090504110d050c3a020d0e100e01052d04050a06050c0d1803020c01110703060203010e04050d02060403170403030f060314070603090206 77
    0x100d42c0c0010601c1d90701c07010401001c100c2d9602d520844110048540c010700f06000c4070000e019140d20004081c50541d4000000c0f81e42e519030042e288070a035a401c1c0e4012a02040e03c1e20022030500400e400b0b03004d1a4108010041c140c101d00c0c000d0000d018041c000c048407209042c6900b0035500250b9400d101145d420069080300c2110b0341c004125000c1c4190340020300300e40000a00707040244030307242080d5482c1c0340c5809003071111003400741c260004240c5210758192000701c0c1b0f491200d00c2c40d100d05107908155140020302400f205005461001e504020288140e1402900b403c03081d5004040d0fa444040c80c01d954413940c0f01b5502a20646179a00d500241000d151110042d03c60308201d03440d0081c05d01c1882c0010000840500107940280755600c0f003210107044c94a060790a00c11111f50703020840d0310035410000407030b50221001e50005400803807d14980c0f600d0608902400c000c110001540b400c0800020411000d4030611145500810035603113410345511088082d9545400702070752101c01849044 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 624605431 1250 624604181 624604199
    0xa09050d090f092d06081b102109030305040b010605210a0b040f061a07050703030309061d0606120d0e1011070e0f01050a1805070e2d040213 62
    0x2c1400045131441080880c1a070301e210722940540c81e002403542d480d801d04104042c0c0400c1a155480700800034605900755450201c1c4e1320846a41c1c00400f000000c105100d00e254407440c201c182e1040e062420302c5000550b003000b03400f800003a101119042d242c040001235580c400c4040d42c66215450b04c81100c90103040c0e03440200c0d01c00140840c078400d5940e01e6460a1951503106102080c80600b20120350707246031600d00320a07031506152400c202d1004000e10800120049040d2042d41d81c107003400a602d1311181891002001000c03082070442c134001d140c00885050004080c1c3c4240c0c01221080c1c0040000c40519854104020380b90011426100f1380909a01c0d021440550f07080d01868815103080034180e0313080c03804190341e0003020f451480c03c0920801d103185c0c0e4407160161005403180300d05907180c0f01c41c5803842c804800190300010750f5500484c8a03248140020550240020a98000360103d0800f0042086140840c13603a8641c0c488529691410f15000f5214445400068401d25030f1a0010034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 624606681 1250 624605431 624605441
    0x2030d0507030c26280e010f050a0c0c031401110408120309010e150103121407060906061511010e01090b041407350115090b0a0902030a09050d090f09 66
    0x18134840003014109030009500640907103090760621079103001e030681c1c05420b98107511403001a82d080024042d20b481c070990300064000125460351404554941d1000011941c4144861008100d89101c1130b000042c40709004041d2424003091f00201f10b4106140d056003030600c107600c6590401e8101c10404d0100386800c2d805150301440a00010400640a041041c20a01c0d2041a262140087c0d001803003844911003c7d40380341c030711600f025000d01300245003841040c016007070001c05c05515003180a04224654100b40020141c034804810f02042001001d00340e40070340c4040c03507159840c209100e80f11840501460020340d800225001e0117072641e480740000b004580c2c0d0f0740002c40c8079410000461100390444811200d003113500384500e4900d407025400c048904030001030000d038184164205525410100f08040b04c83c4084000b4071041c0d52030100c1c980c3e00d00c0754402e0070201c0c03000c01000300910490b080300060b02e01c903c0c152580103007900c0094640008170b004507142070f4018034007404004500e40c81 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 624607931 1250 624606681 624606713
    0x1516030b120f060106080a0908120a1b0e040f06030c050108250503010f090b010f0525080301030204052a071a07090e07141c06050a0e0402030d0507030c 67
    0x3007a510321010049075280604540c9299616400680100806980300c204c0503003182280c842400300e0b0381181c880380c010740a0031480c484441045030109407484216800a110910004084900050642009070416480540d4140214200080380c800c540c41e0740718001c1600d42c80340410100500b000d00443c0c0c540402084400d51304004840f241615403080d5080740ca08101e681c4241e56503051102c00348000744c240d4411841941015803040260781c0100604540d07011603c2c6c643d0300c514a0881801e4013195458200e11140030340030401c0e061100d02c10003141601d0080e01c3c2840a0713140d05258559034400d041580901310902c0c12459446040740c0001d04500c0d000b49000100c020b1401d0700e030b5547c0182558800045460503500304072200644a0342540207400d81800212100351941c801c80038461030250102e5100d86100a5449802580c0140c0282c24042c0c09040c074141c03154809410480300351810f9120784101141e54500620036002c8506556040e40c41c01d00c0c841041e907568881c0501400c03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 624609181 1250 624607931 624607939
    0x190201030b060309070501030c30021b1c0507030203030103030c0f02130902010206090c0102070501030e010608191e0309050d1a0c0a27171204030606081516030b 71
    0xa04070321665a04000345018a0401015044242c58a40090220350f0b0700501c41044c040414545001d0065070038100c0320f0903a9421200c1155205c11003840000e1040f4481e0b80c0c0c80c540d8071404e0048081001400c203076500e10a80e010400f410116000b0381d01c50203070120040040e80308100500010780300c1c00319082b9191150040d40b44020305503001800d00100e59000043c0710b96a03860032019503038100705e00d90b081502000600a01560140002d444001070302442c0e06254943c1400940907400b50b0042000b00144c009136005840700004545d0015002d0000307940d5a00320300803030300124a112a9040c2e100303a150b21070b20303002c030700e030106102400c5c16a01055030340000090031004180409040607119078010020035640d000c0d4008090300e03e8001d1002039a045c2c2510310008056256410f00c1d4055a82d0179425400101046408515100458000c110481d6010400004100301c0313412110503584490150703004061002d9280b5582e10041700c0da55454034022508505250280c0d0003001c403048007030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 624610431 1250 624609181 624609191
    0x15080601240c080a05092d061c0e030a02070603020a0203041208070b070819020309030d02070c171506221505090c0a02010b010507030f1b02030a05060a0501080a0519020103 76
    0x5103400c3c22980122041101140c0b00049255492404030400405007d60a81d40d640c000c1c0054400060501103142d541d000e440006035884081c0203045d07001c4d00030610074005003c640a21101c45840b504040400c0000d8800c42c140440c429000e402502c40d0005990b00450800d881d2071508003501c658003d00f40e5070300408003d130002041d07484000d1481981940c9078462103081c8403010256402c1085e20440c0064418414060380b000044200c0d0600c150512000d80c13a02c84034203210303408648590112488075036540342c8400078680455410340c61058800501c80607074912081c0b01901c2010000e042d0100241c502078002c01429034084004a640d00003000d00c45503d40d00402d00300c2c2404d0301c0441c0102e501142144405070309024800e001c420a00c0e080d030900d18159000b6044100c011115010310034000480c4680803d841c0c0000d120a40040480700a0b460342d080068035001c0684141040504203000400c640c0000201410020391103c000d2012560725890602980394031003040381019150 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 624611681 1250 624610431 624610433
    0x40e240607171810140d15080601090507121b0320070f05060108210306030a0b0a0b1f090308130f0f1d0f0115021e0115080601240c 58
    0xd40d000e481100d100801c825940c200f45420042d80461042500d02048102182048030304100c80540e201c4521010002c00d0306084c4031514110040c035600540354a224182c000604101690400c83c0580c0b0b0a031a094041605482382c8801da810303403849501d40000307010b142d46c88a40720b0b80c031010107810321243d5803012840340904140b86600c118800c0e54031090111401040c441d050003014010640c450003441c2081c1030f1541c01c6540c41e14480003038a00c04002c03002aa00352010f0000154003036100d503042c0214a031450b0400010f1549103620b0b40280d5402c1e2119541140310880101e20004640740d0810091440c0d0322907000e9405292142554028480e00103400402080700d400030306140043d02d8a240d00b040c083c03049428140042d584880f1250b401d01100c164104035135030550348064484042c52901c0c0405918100213546400c084031034000107240342c258194020f210406002c5a0040300640c1c9500d120f65a010a001c2e142c03d465480340011601d43d41c0d02000c041d08080b0342000f4100c5019 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 624612931 1250 624611681 624611723
    0x12060406291905040e030a080a05060307150c080708120610021e010905060108060702120310170115030b060a0b190305102403050903070302060a18050303040602040e240607 76
    0x410f004005c0c03141d2001c5680c1e0581900f00320030590000741050308002c240380050002e0381e01e051134403032005d40814100202e510a44900100c1180301d41000d81c00e913803000c682c641584e003688040320015040c10f5150100d480c038030744090541e14403a090b600504000581c2010744070076072030540000300150b6a80010340300080341840958000c1c80610040c0c0120300e080d41c0003038108082a60b54580045041040000301c240035954a0252603518040d400e104192440c10703401072210070407204941088540c0081080150002e482c07003024182c0740c460600b030307984044080381e01816000740750301c0307100808140040d48241e00c0158400c0b121100b2445e000d980c2c1840c801c00055440e54041b1048101511854440c5c26000f0603410102c0c14005628201c1c042c0c030004e4403030201074459a103568aaa1800003030b0042c8402e0b030281d07036400605481e41c0e42007a02c0c00d0002940a48a4015011100000188040c10300d00d2a0190141500080360302d601d64034041110952200908640c0c94152a8402100c420b07 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 624614181 1250 624612931 624612941
    0x2041e09060b0301060e1b0703031d0d030c0219060b010e0d051c090503060a050726040b010609081207081201151202030106050f070602091206040629190504 69
    0x4095100002d80340001400d15082d036000d60481e82014503030b0414404e001e030081039032180341292031103d15100d207800d2800f01c01a09251340c803031410589080d00b5159404000c01c244001b85034a840411a034201c5480698403120840403c42106d61046c80020108400350482050400140351441002000c07074009000c51150038020b9856522245181c1c00280a01140e8000485181015800c02d403910000994a00005150100180c1c550010944d4035000c2c0014082c0806090110103920505901d12010742c07804440c165240c100388000010b065000b0010201a00d207010054910407850301244002d55114407004c55121a0400c04004212030380403007180079200202f610740d0540c0d42d01c3c00040c100801140e401420390700c1000108811030b00a0b04480180012184982c7c9503203060811000a028a81d089504052000c103000b8000304040741c0248102c0c4034103420004228410051000b41003018802000d55101004c0d51440d8541204241c900403800514010a29118000700701600c17 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 624615431 1250 624614181 624614183
    0xa0807020411130305010b041404020d03030b060a02031c0603080906160c090b040b010206070e0114040e0a1e0204060c030e2404140d020a0b03040213061e05010e090402041e09 77
    0x1910300c100138400c00030300f8029410300342d0040720b003072201e003409101d01d20701100c2c060402840791820b0030880040600a400102c162480101100e88880c21910702079201d501aaa541e500b6039014000c60499840d240b1400302600d8005684134100070311402030045d15800054034000818030307001d0260014500c524030304c024003044103001c10304400104c00e00082e264105140340c19500a00d0800802c243d20400c800e103050804d190400f600c81403040440790302d01c200d030024152003d5031010841c0680741d030380145518218268114009130704820501d000c0703000703e01403440010f0308082c415021034400c2e10f1134021080f000341134818522241208102e2464a41260035070100082403c00101c410410f6084404c02d00b03aa20041000030340d800507210a40d580140000e401000c80401d06640307402c443d20b1508030401c0340c204002034440011465401c007525111264284030200803920354490008009130440103020440240c4440c0d0800010b0030403031060f411000f04000f4000c8409125008641d000c0d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 624616681 1250 624615431 624615457
    0x30408011401050402180f010c0203100c0207051c150f090c0806150603190905060a090519080d0f0f0c0801050f090108031b010b1027080a0807020411 66
    0x14900d1140e03001c00c0c1941644260720440c81400900081181c0c95030307070101204100c400c0d113044c00c42000141c64001c0407070406034140c81a4aa40001103a42d5800041c1e00e41c0290200c034805943c4100700807000c80c0d80f600385811640b078417003440001168840c050081d1740c10003102040e1114a041104100e41441d0829104c0c0c0e08507503c10040c042041c0100742e000b40703c10781950344481d0b8450108a252001421803a0160401030703c1c880700c0031550b8044551154003605591541c100b50000c080901070300d850549541c0602496120391812030b84401d09150790100105042c10094a00c0000401440064103030b06520340c10981c0000300d251040303411b1600d49481d01e00c46d0b0b5041c507091000c44140c04440300d0060f40390000500c6804000400e40304089000802d8180345c0000390406405000c00c0e4603200d411203138900040c0b0009400034079050000580712041c05180186c14800c1106482c540710710074464003e0400300b07011451620050190342d0000e440070a0100c40762041580b9903012901c182a9 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 624617931 1250 624616681 624616691
    0x90106170a2109050d0204020409230a05160807020c1003270302070e130203030a030501050112051512151f170c010e0f040e10060e0f070f050c03040801 67
    0x20441e00d80752140e000506451104040c01c00e10b00040c1100c0b265000e29407041d550030000208540d141e1301202c001e8070940c04140040180071301039101c1c03000c0c44808620030742c00d2640041c0c98543c242c81500c0c49240001c0c03049a6026140c070003a01d0380013010744170408500955029070811f0f00c613030150644207155981d001603010505000d84002141c91074581245180c0c25080401003540050003d0a445200036019040c3d143c2c40030200e50411502d40003501400b010910540c00d503099841181214000e03200d030b1001800303685c101c108036007007142ca071000c18961710580101d40c148500f000c042c048e603600c215240d144800798805111042100c024180c0004400d910380720006114000300101b185482c01824481c503041c080361110301480009042181c03c001282c4941c4d203005200c402008003a00030088ac80886000039229600161880700447c00c00c02e0006043c007110500c2803103000030307402d10314558950707020840300000c59548640c00c10034184038280e01e40405000400041c6084800010 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 624619181 1250 624617931 624617933
    0x6070e061c1404140f0f0a140f0a030201050609010506091e04020919051f0e040207030507021903060b0303090603150301150b03040302210304060c032007020333090106170a 76
    0x21170b003004603000d40310507000407800300104100007030407003180d650040710034600394840502d00e464081144c00e141007078400c080c402c070240750f01075020502500040d61045180d030307221001e0050714403800f654030741c20009808007541c0018608094a4031104024800f5140070a04400a1306036a0082c90310303000d05044c1c030000c1040d840c0c0a100a003000104502515000003038102c06003445014000700d078052900000e19400305446041190072560740104045082c0d0082e08441710340705c5c102c1c007084403151310300454500240b400000381c41e92900020100c1d49141d44005201d0101b200007204e9036007540d01e401c03d0740c3c234959940401001520044075170f079460b0302d01403c00a107880364610b0301c1d0440c10340001200303280c12241c1040342e51258021102054100651804400810741e89581400f120701c108508009091110300a084480c000c5046407074071038100c20380351650502a100a0b1040011240d2490003481200c1c5055120b51240000106140d40c2d00345c0c0142003110300e6010440d43c001062686c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 624620431 1250 624619181 624619183
    0x30d1a0a090b1e0603011403100c0512010f05030a060906060302060316080705030103020a360b0a090605061b010603080409050a0c080c03010902280302090306070e061c140414 77
    0x2031411202c0740400c1100000e014040b4a13075100600520030480c500110084c02d0741c0f8100b0059514009061042204950040b402803058102005070104205550000202d130f903e150406070a07620001c010b00900311046d82c5d03000040040c610220344654903814004090703650385e40918400d204a1101d044c5034a2440d400900b81c41c801032104051200610051015849042440c0c066868092081407000001c50701c0c00040000035816034403d01c0044070841c00316407a60088511a00b040d91006903a6032a001d400c401e50b6414000d542d0010410300c014020741d0070030762041c2206c1c50701c030000040c02602ca4440c40032603400b64104070042611007084c003100a04038411482900c5141c84d144d200b40c00c141108149500c4103105403203445401194012400c40e000b540c201607081c1d00b25405111542065010340650000d00042c0d100740100d10016003094010b0084448010000300440d240c5489900c2000000302007452891207556102550b241c1e10b600e1242840c0a03d002c0c88014000c02e280c0c003e89 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 624621681 1250 624620431 624620449
    0x317090a090509070b031f061e08040b0f1902030c0a11010203041101200a0b1608070909023919051009050c030a080c0706050a02030d1a0a090b 63
    0x203804440d01d824100040a43c010038060151009058116a2070300c54403c0d03584250301d110010042c2e0b005102002900030b0700306a80c50f1001444183c40c401c07000c1e410405a500a5040b9005485030000600040c41e40040e54205a8454614401c0491520100005070101d03041214000d90946000408800440d0480020100e1855000081d03165207003968032107035800c08400c5550f0500504d00007001288551505440714000028100c800f20341d2a82001102400700380c0d0300d120b100e403802e0303a2411543e100b034900b03510816098550768180d0f4640703122000250f010007000c0380202141598000e00e00c0842c4160b0076004044440c82c1308402c410600c0c0c5082a8507000080d441c11719503419400029070118811240c07a078000300c005001c136050700b08242024107600304d4a515004102c601000c10039030101034070014025104580e001a100e0500b07a82c9440f0785480314001d0780c0184030115111f0420b41040f03005403807030000206404a10341c04128540d507190400c155454132070741c140605080070006 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 624622931 1250 624621681 624621689
    0x509010504020f18060405130605100f020601120204111620101206030609050d021005070507060507091a0403170301030314030a14190c0e280317090a 66
    0x11403605803911080c20852213000f0729203101d806a40d11030445070740d52400342c1d8020040940300700382d42c502d81d480441c0100001e024140c4290a81007544072441e1107440541081100358006000503420308911030b002c042d07a44400c03a40305440703a42016100c071812000c0c1c5000d42403040f007000e0017080340c40c0403c60740303114080c2801c8207450f9541070700c40d5965600020340302d8032160800c0c628107146001490003900142d08043c2c545410800c41c8810810001108038204500c0d5083d1b984004c84c0a144805464040d0b503032100003242440750340042034051b480a90440442e06180d045290b84500c9280401b1200407000d00a041c040780070014440064209503c580350f12011a14540c103541d4048c00d11940c105592040403400300c0041c00c4100380e9444240e010740c184008454a207880e400c000c1aa201c4201054909800c001c00060003a0049402a1800c1001044c0c0041526410404510b80c0041400352248802e00c000010103d4490708890074201d841d4012244e5a494800910900704003e0b80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 624624181 1250 624622931 624622939
    0xc0c031614060f0a0b0406030501020301140109090b2b060e160803040f09230c0301143703140106062a03030b01031413030201110f1204080403081305090105 69
    0x30400c0c0f203840c810040390f002c00380b90b500244480011012a00400840d040108550310020003c980341c0700581410764404002d90f142200d840d10744440400b035408006e00d0b1070f005071340c2d914100d82d410b62600c5d80e43c00d038600c00200909405115240c2406580c2000210023894100c12030f03441403409908184006440d05100442c07810f8901455000805800d1041d02c1d15207944000049021000094481d0202030f14050240c00d410f08001c000f0450b44284242013450004440c06034041c1040c0d1506950140000e110b41641c440800c003100c03210511f2240b00e42e1748400544040001004503c8050015030040e000081c1507003007c0000e00725035840f42c01441940e4081021168044101085140701945450040f030030003041e0005070060041038008502c085ca007002002807a4402c0801440c2442c043d9000380510b03101714620702140d1050003510b4070440c4080010f2142d00422f0620241c20901c03503a00c0c1c518242d6039444800d00c54220000014018640031820803041c9001e450301400742504403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 624625431 1250 624624181 624624193
    0x40b060a080603060a290303070803010f0501091202030c010c0809060703030902040b091b0d020409021c050109061a0705120708030702010b060f03010e0703200a2d080c0c031614 78
    0x46c0b05030341211010552210030280041040306262070a000b80c8070107070780c040940e42d10395071244804108c824243c000c10b80010080a400209115000d184003003264015002d003149055802c01110782c0c01a0b04825034015104014810321502d69900400005020f0355000070000140d10411058912000340a88203074688414071802d4000a403034403500038502008280d845507941d04403400307030189510040030540b02198040441002c80b0070008841160300c0308000581e2107019000407039146000d821440c02089046800c05942c03030004140450054084a100100911005005500000040301c00c088080140038485409001c3c0704030001080350300d581803020714548040d05000502c10943d00d00c01c01008641041c0c000d61000480004a40461843d054800c0581c03080358051020480000c5019107450150901203c400207500c02260f0a0074503204054011101608042c3c0756403010f9a00300060a00c0315800c000404d02100d843e52411403a810074244580035812414110030960859 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 624626681 1250 624625431 624625451
    0xa021215060613050405160314071b020109180e150f0703052a0429180613080616020a03270503070b03180a110609040b060a080603060a 60
    0x25545158010800d5446680319545041c0c000b241c03c0300c0d5031200760010318103014484c031000503034800d282100407901c09106541c0460b224050480c4111032038000112500c40c0d1030901d441207131a24081c980140741002c2900d84402d10750813401507062040c01200d80d40d1140d0140b69034280081110386042d00c0e241030322484e0541c6880c00c0700c8070040c00c0c0703000c0581d02d000242219500d01801d0a000444100e500c240d00500b28000305940c4c0b150180e100003460442e40c2d00f05140e01d0441c1040d289a012100310f05100d900b010401d0511034074510079038019000e1040c003140302002d03101c02c001454500001c050030300300b07030031850300740c5100b480c07460b04540000580b800840c0d0000e045d11a10302100c0044180000d00e0307103008440c1c4030541c0040d64140900c0200054036120b070340c05507003e035400000c842000c1b02000b48650361021000c000a0240c1c0f071404014106150003c00b624440e0409000071445900e401d0006000303500803014080440c0c80c0205102071750404001569201d28410006c0103d0b90070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 624627931 1250 624626681 624626713
    0x616031d0c01200105070815031f0c03060b21060103021216030f0c0203030103060e0c211c020109060507090803040e090307020409050f0c102007030210020a0212 71
    0x40c0803400e4184241242d9a0703c0c250042c25030f610740014040c00030042d07170502c024020480b4400784c030b626040340c40501e124800c0b0318001c80e0b0000c0341c010030011000340c03038040b500c88000f0702489511603081c9640c038140000d001046000a10000e00d22140c0070705424480b00341e003100f005000c0d100b80d04240c4103001034880e10002c0d6465a82009140c010b002104200e07280450150028204c04001941428003641820303400001441c166480344c801030000d0314106080c19902c084841000d40c0c421000c4040f46d481500302010400c03c6c903101c1c0280c03003010480c2c00b0050b0230a152003504000503951340c0c01c524280300c03051180c42d070813140c80e00c0e00c0c081c1c482c60003c146658ac041d5004140c94814020003150401c2c00c10822641c40035400f0704103000030301c81d41c00c0c10307512080f4000007c800c60190056166452405e2a0240100c49485d15803e03100c40841d034100d010303600d40d540001841d00c0740d4140480541e552807080d0b00800c000d540245a500c5081c41400b01c4105034100205055000c1c0c2c03500c05000c0750b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 624629181 1250 624627931 624627943
    0xf0c060301140310150e0108030c123f07020d0f0e0f120705030709090302070608041b09020903012007080a0c06060b0a08090a020108011a04080616031d 67
    0x21015690400d0580b1100081c1c10f080031020f0042c645072400d07882c1c02240f04018600301c111400c04004421030b0780da03200c501341c4900c01d05800000e250440ca00d0380514081d42ca000e000c0c0b600e00003100b002c6001180024140300c94981c95207602003100c907411001e20841c1c0007a110381c0000c0d80d2010382070340698520094100c1c81c0c04030f03062051080e24110046291160883e04040190040820446842c1008e009132a810f081c0201406801101c1c0c01041288032400741c0901d03164507600a00105280130780403214107a0141c0102c3d0b13240c00c42c542013411042000c84c014090440c507100180e40f00a140c08050031140d4081c007840000503032004216082c15110151290941c010403490b0307a03002c0a00c4100c0e04400310380e0004009a151580104900341c110010348045941522110081d031580102e03103a407110240c000900180e0b103603006002c11010400d1000c203c14244580da41403a417034201440c1001d0701150b02c5140031040c1807000540c66070500400c1c0103010403a030145c11000744100c165440d20 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 624630431 1250 624629181 624629189
    0x1514010816050c0a140106050102060f040204180501050a0e0601061b110303040b04080c100c210e03011a0a0509220c0b0f03100902030705160c120305030403020f0c060301 75
    0xe2030030540541d035004400702c600504100b070648040825a24050074403007640501914070b51b1810a000c0f80380e50000130700a0103012014400120343c4c1c1c49500700400341008401c0c52244e9013500d04001c3c00200d0034002c00e801259032144c0450034580040105107020720592050007082917015054260b03600b0000031030601038110090340341c5002c410011910b14487c55002a018600c000b40000d40f850703022400c900c4a482c101c071814940d8040b003d00307c8007102c00f408040d2000020300404900181c56002007110904541465601300c40311100081c2142d031000c20a42e400d152001e40a40303580390041400740648800c88805159090082e01d1410403100028140e4078030001e607040200b0b001b030b040f1036100209485042c01e0f9079581041010350441c0c03c155400043c0364080840400d081c04a802907a106190680e1160b080044001c00c0010710294000c0a90f410040b001022451010b0400c13080f84103800783e0de8035540c90410b40f800130310f0641503030a40e012039004100303083c0e07580d90b68004482c119 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 624631681 1250 624630431 624630451
    0x17031504051518100b07031107060302030c0d0509010b040203101809050606190302041104061107060e010e040207020406080303041703010f030b061f03050702010b040603050601030b0c070b070315140108 89
    0x40d600d55500f1140510180c002c8105c0c110049043c0d420150700010740140000e08401303850f2006e5458a0a405901082e00d012204030000d10000000301102d501981c2d1015510001180d415035010206040b41d00a5030728101c910b44e02d08003840707011060f9010406468603441c0801401c1119218262148406032070288203400001034448440d40c10000c020145800a20411900640800010b0241d009104000210b03038110210001e080e804a07094085600c80d8440d404200f910200449000d1078152907158070550a10090015807203910070076000e000010001c0d82c4d20b04083c10450318000c1240002c904490b0100010700c1300d45208418102280d03403060b1041c403070f81c039002d0000e10030390f40403540d020400c418034180051403a0305d600058040d590320340007004907020ba50240010b84040340009066544840010000112440d0b40513901407090440e0340d0801a0796510ba08003410151282c1c00025200c80220396507140c42148100141039000314030851a00740b600180046200030318613541 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 624632931 1250 624631681 624631729
    0x1d01030611071b03060e0319110a060f095d020c1212041511060a0501030b0c0301030210140405030f15090721170315040515 55
    0x10458100142d6603a56804000780c056142d90340b07444074009426100640e0000c1c1810030302c0300b079164040100d60310580b400e914261020500074065803903000e51250480c46104500345034001c1640b500c210107076100c0c8410f001c90f25100f00c2c1090004844a0b5119035020a405803410301c1c88105d440c1d012000c0d101860841480342610400100113011400941c9414100e00c10031102d055404144100107000889800c88aa405500d40c25603c012005084400340030030403090103480030800c840100c401007850302c0420980c0c000c0b0002e007403101c00d0703803075010307640d144e0006000300070854042560260282c80d480e4115803643d000a102030090b04682c00c1400031000ca880c454090400449003c2d00018080721500481240550b030354604005840441e4140040858802c01c4041004800c40742030b082c50400c08244003002407800f50381100d0880d03c5502d10444003996903904009103108861054a0b40641200c000501095550080095070b203443d10301c00c5070b407103562003e001d40c06200b0751001403c9 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 624634181 1250 624632931 624632951
    0xc0201030f0e0312010e0910110c0a050f070909080904180203030406090603050a02041401050a210b01110705360c07021804030c1502090a0902131d010306 68
    0x1004003000910404034908101500d407803400000018411515184e0f0b80c030f101c0d603980390340d40030885900351b40c04241e1b50400c0740d001c400110716070020f81100b20880078451900700c1072001d45180010085048915030040c40008902070800c1c00503078010522100180031004042d5501426807103010034052040303035180f000c1c0b8040c803890802050840e44c00740440766600d0311504041e00311205c0b841130100003400c0c81c00041c08100d490003907030203e80e000310311826000c071420019921078110319200c1c0c0401201585d00140a4004810301c401b198100070002100318a600c0010710005080355000c00c01e50148a0401164030760307040c00c2d50614108544029034a9035100d032041342c0011140c4803440c40444505201500721200700a00b402071086030110800c41c020010600b25210440d0007a0210f40b820481401150742400d80c000407e60340c000051400c13880c00001110031b0700300d4104113111980450800090103451003800081c1544e0841400e4450341011242a4441c05000c010042d544032001a1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 624635431 1250 624634181 624634187
    0xf17010e04080a110d0e0a170c04361104090c06140c030309150f0408090105030a02091e04150e040f080702090a09051903020d08071115100e06030d0c0201 68
    0x12149130312003020b99002e6054a08001c240c60491a8450700c1030355003410000c0c65850040510b0040d04540c4050007280700507104000003840160842c0242100100d00c1158044c0a121b01000403143c03c55804000d400c0f41c04e050f007a010001402900540c03510541c40c01041ca070680100c210392041c0b9014542914001c2500214040d25218501520010090102c50300c00864021000078018400c203980e6500c00c2c0d00802e050100350340c0900074540c03c00042c140c6501c91002582d1103d1190405464407203903001040b00c14488000503009004809092050f03450a0300406410b0041c0001090010b410302d44442e08091001d04000d14202e80300003040104420b00055452480d0010407403145803504800c800058400401700b2500d6010b0654514100380c5901107034a10300750180c3c024000400200019225110068840703030500c0240e000403814040b040045440c040900d008011041c02e01c0300d011030500c0015003005004400380b00030070a083e2000560006441070614105007075401500060b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 624636681 1250 624635431 624635447
    0x80a03060e04200312070506180d050d0b0d020a080f0f03270a03080408060108070501170109020d090503030901020705160501020312040314040605040e101a0c0c060a0f17010e04080a 80
    0x8412202180302c1c400d0050201d24075205214020030f00f142190019841600cad25076044103034002c00c5050000018401841e40404000c460240441d000352000e0303000584080c1190f0700c400d01e51b90055500411904081c440d0b08100a03000d0021070502654a209298401c3c0002150300700d22003103c078090296640e68a003000450300000707072550712a01c03807102c03584844d400d004410403803184440000e80355200b50b241100e980007007000144541d0812201030065413180315100e0b401307900c450100c00800c000340003c40c0a2102c00300016030360a0341c0e15000b41003e40150034410300042c14002004a030760040100e9141003014200c4841641d668501914000074454405403e54004540441d015420600900039511504204001030f078070744100b1506030708640181e680c65049141503041003a10342c409008481072140590f440c1790703400008074100350418181c0e41d00144841a5440c1d040c3d41002100b84084040891040b01d90305002100004001c0508000c00003100041c84038402030dc21001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 624637931 1250 624636681 624636703
    0x9011205011409070e1806060402031f09150f05031005060a03050d0c02010306212004050a0b0a0b04080d26090d0f0e1f1803080a03060e042003 63
    0x10341551410f111003a1035650065001da02e28680c82880481d10650074801c01d403110244040080c03911740d07680414000a900040c007800a1540003114042c5841c4000c00207101401c0b08510020308600d80d0011002d0414590313003d4034502c03001d004c00740010344000c111402c40300300d41c240102e103a40311080458180c101580c005401400380168024a040c2c1c0404000d00e030178000d903003c0c8201c030344030f41d2800001c0b03d11004040b041c080808a4400207070b11459100946501c07692031504100200010401b902c0040b103084404580d0340b000e9045914200c0c5165000d810740c03000b2107040905004465942da0000814a0240800514252281401802005000c034003501c024401820070003441d60782c0d6404014214042420a000740d665070384982e901c1030025100070051541401034001f0310300440300544001c010015146a106920401050801c005501c036031030343c41c1d440300c1c090030007003c44800350486d0100c810000188804140d01002e40100c0900c1d20300c4602c03a1162000c0000e16040c00e0540c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 624639181 1250 624637931 624637961
    0x1d150d05060103051806040f05071527030503040e0c0f1c0f1109041d030c0714060a20010914030403020f0a0f170a02031603030f030b0901120501 64
    0x24951629190903040203010340401c0c0c030203100d192903490709281c07114030020380088a07a01010005001c200325042c0020264068015203542503140d6038030581d4030204046203004182c103904082c481c405c110580e0034099200b85640803a580c259030711f440d102d01c502d10580800000d0741000c00d615401e4001103950510004031907560702c1d4980100720000c0d10403081111808c40c1f501701081c042c284240688500c2c000100c0701c680c43c202184041000510707200c2c600c0d081070700f090140c000c1000400c00080005050500041680300c0c41e182d84144d12200e604140c40c005c600c18803ea0809a400c4800c001203000c0105001c0190340c20f003601d140c0100400031010b4240300d0b030ba07240d4400c0c1c80b00200080082e6402514030b0502c002040b4240300380c2d14020f100f0702081540742001002111020030710507452640000640b000c50101c0e4001900c2d10724942d881000e020702d001001c00070190401400c4c0c582020030308040c4848807054000803200e40c0d05120324a408060440c5507000c0242c20741c42444000340042d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 624640287 1106 624639181 624639187
    0x2e06120c02030408010c18080d090302120316060209040b030304030203030304111804050105070801090905280c080304031112061b0405090702060906070f1d15 70
    0xc1812000c41c0418400494400401c0c040c0106c0c012140c1d4801c0e08219002d0740e480c5200e0544d0307001141d43c0c1d2000e0700c01901c8a400c01041000c40703404036054460001c04030b98440c203522a90415001005002511104014442d4050b00040005642c100483c1007010103041c4c1d83d20603800040e5240e40284001000200746028115604d84040c0052008039015601d00c3c01d00b0302c05481c11150303a51075200f0440391030750008000d03006140b003c1c0c092185440079102c441e2103500c000030501850141003a13415680c0e01100302074041c00e5100d91803511165903803450035104c1c0c015000445039202081100511807500f8024918404040f01c05080c0e42c0d00c0306c541441006540d450908901c20302404002426603440480a2044420343c024007054900314072840e041100c01801e030420f2140300b40000786031035031006460440e88245e0004203001c031001000905040c211650113200c030a000 = true := by decide +kernel

theorem cover : BRFrame.Cov 624460431 624640287 := by
  have h0 := BRFrame.cov_init 624460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 624460431 ≤ n) (h2 : n < 624640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
