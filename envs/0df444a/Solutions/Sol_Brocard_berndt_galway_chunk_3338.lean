-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3338
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:21:56.376052+00:00
-- url     : https://prove2.me/submissions/cf3c0c4f-1d0e-4c23-97de-cfd54dbb6e44

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 600179856 ≤ n < 600359712 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 600181106 1250 600179856 600179863
    0xf040302150c2b030c0c0807060e0601060806030c06040b0d05041407090e100507020303071416030f080a18020609270f061f2d0c06110903030327 64
    0x20726900c2c1e029540100c3c090201c1c0414080c5920f6030402e140c80e00e000782c2d1802d500280380c100c289030040304c6691550b4250501c2c6020f400c060344480c09900480c3c001146143e0020303c0d09001e00c8083e011508a00015814042c083c1f04a003d0040103107418065101440603d4000c2a4454441c8403d1f08104850500103032908503140c220151183c0c80300340c0341e26142000c01106040080560741480b0390300b48600b01a40303034800500414200329000e49841240c030b160310300300c030400c010034415001d0080d86070400074070104c1d4003080d8600281d100808111410760310b00030020011181000d0440c1404240d0800849901201035650400f4071441c608100c5407c0603030655076034880301e07081079081c913106c1071034401d0704001406503126000000003c803901041d21001e92004200381072801d01c007900142031a28642035506090304012200e105401069886804480d80a120300300510004400381305840c0e880c013888200a4041d8028000078500600d800e04000a1900c0440740d00c0e08075850f8910340f0b04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 600182356 1250 600181106 600181123
    0x1302030106020a06052202091302100f0f020f0c040c020c09010f1502071526280603080d150f0308041401080403090603110408060109150b0f040302150c 67
    0x15820611640090000130b01405d90710a074440240c4407000d840001e4040c04500b0300d0400380c081d000050004e00c800c101e40402000c11a00142865040203c8c424010029001c2100300300001e124850078281c068000941130301c030401ca08022340620001d107402d210061480040d44030441c0f040627850b588503200c2d101c00501901c080000c0441075030514001004244841080104540c444042041490f4441c0e200d5140d42a2601c3c1000390034845000c41103030000842a464118080030b428061300d190700d00101c00300350082041c0c1c000c0c6141c20300e0702003045403e1403001030032403102004800f00c0e03541c251340110a68040500f00c02c0c0010785907078041070400c8040e0021a211100002c0c2803000311944e02d0031011180003480c0120451410740d40c01464040203128490a040c4c462100c2c15000044005a8002e491407004032005513035681440000707040c2d140201559030302200340c0401d94484060890b0800c080c0002c0c8685014515800e02c03905000f0241010240d010030311002c081903509128008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 600183606 1250 600182356 600182369
    0x1005090105040507081b0405060f040c0c110d020a0e071b080a031a18040204060803071b080c03070b0c030403080f090301050609100b0f0c0a0f0512032413020301 71
    0x180362400c1d2030504c2c94009290050911540f00c40c828200d0703c1421030b4242ca941d8001e031404035181c2c8402000c1880c900502d0262580b117030401010005e801d5000340221f41c50b5006e1805d607400b1000030801e100d02c20340c11f03010103500440340000034001c3c0840e011400350403170034a00d40022a58004842610a400940400c481c40880003c1d0041b800b945802901c5040f01b410304544000180480081e280b40304100d500e420512030a0b00090940d075842c1d00210003004003070166580c0d60054544246102010300c918400307180740440c0030501c0080007440c40d0107c40090014100386080c0941c8501c190445201350041d80302c10400072001407602000341c15949141045183c0303e01d00c0c1c41c109404d64600604840c0503014030020010f1202c1c0c15007040040b03809020400790780d1241d608081c074091081003040c03581803103000304800800c02c20351080d0703040d140070b8400c0d500705890740307025801a84400c0c0c0b0380c600c00c2d605400c1c0001c03195007800303910303401d140e001000f09500d458402c022a05a8000740e002c074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 600184856 1250 600183606 600183611
    0x10803070c0e0105060315180c040e0906010501020a031d06040b030a0f090809061815210411040507120903021c0e150a05040306020304051b0904050601051210050901 73
    0x10030a1140440c0c01a14000c00302c11115030500000c2200c90100406c04815100c2620442c0b00079118040712204110b9a4814102d081c6800b0100c0c1420364064481c0c5c0c9c0e00c4a28107030001c0c44100b000300d882c0b8141e4605074040c060304c0c80d031524115881030241c0f1004804290342da10402c0d50307640f50802480204014561180c803450400402000c5400350010720803070900b41880180010f6803070007292000759007251102c8d1618601c0380161401a402160385821189854410b21032900503409820313101100c00c0e80401300e1b500c801e12204401001c0d40c000b07080c03505d041c2110720689403681081e44c2c070079442d01d4403482c07000411103401c040e40d40046043d005604041241410440c0390300440421501a050054802400402180b0030f00030030800659690310100344050310501c9039003210b00440e00640c0035520390500707042058840301e0100341c14031503030f0341d074840310303840d800d0610001d40b140740c00c01d01401050303182c0b900b401b82e403450340c1c940002680200381020100740c8452250310b001e0b03403030701000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 600186106 1250 600184856 600184867
    0x409021603090806090a02040c030e1b1207210f0519020103051f1406071b14010c080a30090c050a24050f07030203090117100608040f0b010803 63
    0x2411011054200a015401036810025007085c000b4480d5515941034400041c000307980d0401314002e010407000c0c070307030f07036002d04074411a00d4915102c10b41582c03907003182e842c0003850281103116590b201901c20755001d00c100c0000030454000300c145090100340101c2c0e10071092044c0707568040c01c218420344143c5041d141c0c40191410f55925102300c0b03501c1941140c01055494039030705880803000c0103200328401e007003042400c1c2320591100011b0751030311a0b100d4401510345030901c502900d1050940140030400c500c1003881041c541c41400d500c8410307600a9012031404140810803910310b010030b00c0c5100840740a60b50244410121031982780c905141810001d4800d8040c540850340c207110f54041403054000c40014410010030303111070499101a80001d14004000d440b054038036001d01c40c800c0340940c8001c40e0440a049c0c02000400c0a1602680c811122030307070b403000f4100450820b451503540c003110b140781030002c00c3c0103d20080d00940515100b81100e10503584541c2040d10903000200f09420202c0c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 600187356 1250 600186106 600186113
    0x3150302130516030209010e04020c01060b040b030108100618050405011d0102040e0a020315010c0f02040504061a100516030516230604241b05130801020708090409020604090216 78
    0x40814a1a04d26065103001c010000003080e42640e0100740b8803840d0300040d00300c00b844003580010014040e40a40b56106c5540d4401c0404a400901c40c004980c0100940110f84440b036201c0c0c03d00f80c0710200740440d20086121402c81c001d102c000c04c102c8080d0744c0c40e03880085110700b44c81301c02c00340d005020025175a0390030304581010307840000d00342241d2140140140030818010f11a6814030000030301e0034410217809410200d01030300c0b010402035001844c150a01c0184402c81c0c018014084190300159008001002407152101d1000e0540c4002038041c044400308900151b00c8200b020b00070b00d040350401901c40740b42c03038800320f610354200c0b0032160001001d12402581001c3e00081080d00c400340c500c500d8207885542c4a8140c20300b03406001001490510b08904203a84050070216409405100c4000341e5480980300e94815196560210942e0300006640130701402240e6949510085240c1008909001e110240c003c00d041280c0c400010f000204120711548007500c070201a02c84008070b203003520704 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 600188606 1250 600187356 600187381
    0x171e09030c0328020315070206010e01050904030f0810051905101b0b1e0f070809070b121815040c0b04140d0303020d1d0f0c010f031503021305 63
    0x10001c5000303030440e01620700c1d4038400b0485950742d0003082d44003040c4030b03016100007810310410000e20700000007501d09000000780d0019070a8141c078001c10707851907281d0300c590070800da5007030480300100081d840031202d40b002403041106540003085628503842c0d11f40c40d8000140c0350405c01200070b80301042d070f24040002c0c0c580a07042600303421060038007a41504910115034a4440c0311180a085491082e0104580c502c140789041d5020300b00e00d0f09100a401c4c26580c480a0308015114500000c000d4004255504e60104210301100c107012800c0d440d0070403090316010a8038000300f00296240000c60f500b50b042d1004d0103003494080303800315400e089140034603101407144543d41203c900440140018090f1b422001121a03084004a400f9a01180e076458100e000c0d01c00c0148030380030781e07003000032500c0105103c0d6201030280e0038640503154604038450316a5502e10301c094281f40080e1600d0404101240641c2c46010740782405468030340559108e401081c0b0034844040000801580d0b0070400143c00c201d507 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 600189856 1250 600188606 600188623
    0x70b12040b0c270316140109060503100909080c01050106052502061204020a03060c0309110d03020c0d1a010f1e0b0307180f24090302060403171e0903 66
    0x180682c10312190481008840c20021480400002201c1d00c0080e03130f40d010040ba0b0000150508560310641e120f80306664041010010030340810365018002c03038854003400581c0d126618103005120001d06d05452500600350360081900d00250400c0042000e540a02805019116a446440e60f4000129076103001070100541c501070038a0000345030006030b031200129959a800000c0c90060344d02c45000280000340c03d80d01c02000e482c689204203e01d96010780085400c1400f42c20040c0000c0760901c00e01c2141010642c00030010780200344014514986117000402145c00b51984503800c83c0d815901c0c404540d003c1c2c118644020002808026a41030281602002c1d1401d0792040701252602d00d0f02c0c215030202804400c2405084d0741941c0000c3c90b0046844000d0a03031041c9018055692400c021001c000c40360022030300481c2d07007105142c4030301440d01c0200700c84e4040c000510301443c64031003400b810301c40b868001e0303405d07420810300000712a040d80c0d080c068803501846031b960344044010141b07003801c0b1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 600191106 1250 600189856 600189871
    0x30a080f0108100b041805010c1d0f01051c02030129070c060e1c06020909100e070507020111011505040e010b03030403231b151812070b12040b 63
    0x800051140040224240c100e444080e0b8020078041130800014003e0030a402c02c3d140030420802c034071010b02c08150131866410816031aa18060a8038280c80003e50001400c2240c001500041420841d40305200400c40418901045c480741e00840ba5440c080ea0b20030b074484901188210405000c0c0c04036400b01656a5440c0c1180902d06000d0743d4901c10301c0720880c450706042c0148040f01092545624a01e81148803805101e41074490031460601c0007500703c030700107500904540f00010203000c02c1360b5046066405206030403d0594618004503400e41c0b250008078104517652410365042c003000d01445803031403220940c001c0c841d03003040e09110441d052040ca610890b030501d23031030600d15140130007101c05483c1c010881010b9800d84125040b211410400f06c03503c5486245101c4041c0c8060300c543c001407035412145180c0e0750280c0b6548004a0180c0c80e0a5403202c801220a841d1b545050400110720700560750641d0012070f0b60750302070704158003c0d01d503516005500c04100810032494003c869482002d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 600192356 1250 600191106 600191131
    0x13090501060807170f07050f04081605040c0507120c020a081b01030612080702030106031403030901140403050a0e0a090507050703020f0d2c06030a0623061e040306050405030a08 78
    0xa442d0028903d000d005084480d0303000740e01000c40c6d00d081c031582c1107072001e00030420120380d82c664a0302c4142e511a100c0038007080c0c1c04002480850180b0b814010014064410b80c0c8444c10700c1400d4854150404d0305d80c0f200010b10111038210b50050304c442c885a8010504500940380789050210300f04840104414054101403a19a0501c80e4940c032003120b07810180c00c0000aa1a00514130100e4010728a40e01302034004841200ca00110040000081d4410b0190f08001d0040f0780300000c846210400c1524001d012071818000c0c515490311402c0490f1030404000d04106916907101006400c46030140c44010002d00005a69001d150301040602c25080e8001c00802c240105210001c11100b1101d40c00b42ea03081c0c400c0d002014003451040d41c80c1c0312610040c64a547e89c07c258001c0c500620fa28841c07582e0030034a1004410a02d41400c01d40d0642e0800a48072601d0400d0902042a0303418034801091780035001444040003040261007568810780c450300080d5501c24a00d040607201d60070042c1380411105 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 600193606 1250 600192356 600192377
    0x50f0a050c03010623040e0907080604051207020402190509040614130902030a1b030201030f0c21090807060f0e0f0307060504030915091401020c030309060f13090501060807 76
    0x144045a04480c102e00d0064002d10281041e86840070380f40c0320086405d02c01280124114481c1d1002074020385030081118400303907449039030603202c200480300a407071a002800b540a0300d80e8204005d02070f00e03200400062902840b0356402c0d94000003511140c0004402140c204001e003490310540700584044603c610007a41c0d4075001880a8010904003c6441e407990b40400440d20100003201300c06a00011100c19030a80001e00342004680384401d0740080c0c10310300003400a4182d445039601201240e0303540d80b44007656090202d8030703072980c1d040000d1990740d601c04680030170b5420014280c201d104210104009241514a01c1910701c01441c00c0095084442100180d110010448002e1903001c038002c5101ea0b501d04064804c40d040d82e120109500304005150101030340005104141d42d80a0b00701c4414400c030600483c2d4420211000d5074140d0300801c5440c1d481d00e068030251292140381c0070b04034901980c00c101a084640301d80d101c001c101e0b40f81e030010721030140c1002c800340d8804210301d030001d10107 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 600194856 1250 600193606 600193621
    0x90905070510090b0712033206060d060f0f0e090303011701020909090a050105070e0604030209180f0a0b09011e1a1f081515030709030f06050f0a05 65
    0x40c10284078281c401d9509201404455000e160a40c001303225210b90251101e400e401c04042c100a0a410320740000e240c50180d0720328203907243c07074013000d140c1c104800e90b01c0152000a56154400141080d64010014000d2610100706401203001410380c404003100d58a1919134440d82c90000c0c0c0c2c00146480d000c0008221030703a60008140e1703044030880c1d5006040325484028070341c024400c0e03e04554010b5645020018081d42c00103500250920480080103a6035071000100d4001141000c1540e000c04100410030262920800e019041040c01e40c402d401651054117036880c01894140f114461382088041d03c0c144511401301580c4141001c00902c44074174140340d90700a0310f9122122602c45c80d5241d840c0075040550b076040b00b00034840030b014500030b030b202401d184003201c24010140002920f002d001405010704410050240c03000a42041c1240250000c58112034000070300400c20030955110000115841c84101c60b07666009040000d00c60034460108a40344030004d00403000182000140040c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 600196106 1250 600194856 600194863
    0x106030b210c01050d02073314060103020d0f060f030b01061809020c01090b010b0c0d05120a0504021c080307140c0d0e13050c0901090e09070312120e070609090905 72
    0x41c2042443c00c1641c3d10f110100150081c0a019070191141c80017110840951150034007508481910346c1c235500c082001c6503e83c4041d81c504001070001c1950010124110354002c1c0c002c0c2000030010080800c08440140482c0100c8a1a078010981a961484204140051803a003a8054613042c035240071546601403c2c10b0903003a5621070f04a569030b001410010204003940b0070441300b41d010b800e0700260f50f514403006e0351540041c84100d00c1030160000b5020100c0c0640d003166100c0f040901e010301141d84140c3c4c3c01d0014040200140d8110000c03010078502d008100d800c09141900c02c002d215200d050440c8014500e08452030940f4004408024030f081d004800076a92800c4825440c0c1403026850303220104040d098540c1e140500c050905060000d000460005056a80c40070380c2c42c11035155031145550a012000d40d000215904a01010b10101d90852200a821542c604101c043d550f50442c101c0211356040410b080746407c0800d0511405500175001d900902c610704d014001907200391038007903c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 600197356 1250 600196106 600196123
    0x80c12040314040314010e12090108060d0204090519261b031c0e0105090312010b0306010e12010506090f01260c06120405010c030216020d0510050106030b21 69
    0x900c1158801d0b000552603240071038000c0c0d607100b0341c4440303012010500d0901034020070004103c1400b8540c1880e2071448000c0940785541c0c4169a903030030948550042c007039540b52221041c1d8106882d05244008204100800070001803415a10342d0800210304020300700b00c4104d030001c000d2072a0900048052920301040c1c4002e104500d000a0010700040e1860740380d48501d000c0e4558801d103103003081600703900c264810800703080004000d10540e61034614090b01c1e40314148940103d51032000051201c0103004004e03640c000c0c810304200c42d400c400540040d0045a0000c10366890341e44440420890b400c140303403525040490220600500d50500c858859480301108519088946040c45454840406c02c9075062001c000b5010580e603041406a65005001c00c94090b2801e43c203080c010b211085c40b074400c81d4440102d500c071503030004015034204100350031051820380d240c0c0b107442c0011800c80f055103d058001c01981e200088c8003042042805011018074042d1114940340b85903600c0039103400304001c034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 600198606 1250 600197356 600197363
    0x12110702060d1e060807030203010e0312010b21010f14100e012a0503070b01060e0319060f1103070f0c051902011e051b031e0901050c10020703080c1204 67
    0x3a0f01541076120743c040d54030b041c408500207804c2ca8000a07608502169a20550f4020f0780284241c1c002803100581e284541c8003001624010b80e001000014030120260042c070408151301400008695264044010282c200a8140b44040c9040111294031195204da0240503a00304503d80c0d10500c01602c8060940c1c0154140020801038141e40c44000d0aa918002c00c00032048050b140d280c06c19951f03940003107104640310b0111400200302103008101d9406c40060040007001e030369941030714408000d002c40741c04580f00c685501342a101d5100324058040d0341120f81c1c00c1c6a0301c0b803030a1500100499060941d074424091110354410115001040200040c0310000a02e8001902480100d03000c3c100080d04504101040c0b50500500350701c0001410301000341540d8507202304000181c15241d105a801025419250114201d800d0300e505001d0429400141007817030a01040706105400d2101c1d81300e03010421a80010307104100354003d0683e82d00300700103c840c1e5082c04030b450709ca042010710180015 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 600199856 1250 600198606 600198611
    0x190206161b080c0f0109060507020d110a020402130b07110a050a0e1f120c031a060d2303160b18070e060d0f0516150e01080a060b0301030312110702060d 67
    0x9001e440030402130303440406480c40080020840c18205800144010ba0b80c00c0010302494085c0d16031a4411107840842d44a424003070111150940c0c02c00c4002e602529030014000c64481b0001000c0d00c1d22070280021502818644c00e55603958410020151f000342c200c4d6226491480c414040803d0200a01d54007151a07100d81c00c007420440e180b440d0f4594180d07c90501c0042c904414001c101e038000022084903c56954000112000d401105442030100e0f215a04450010414004a160300308075144244101204e9010120040511800c651001d0034024102410505580130002c120440d42c2d40502e40f0301451030005111b190081d2224110720441c881c22101c01d010440b1655180c1405440941c414201021400c240c9080f0351039140c14002030310580f500318400561008000641d14840c029655100c02c0303039400340019100384e40b001e40070107205603542c0000700780f010b14840218082c40c020b40390644403240c80803952007610540b00c0ea41507107141c18081940140c40c0c45060750507214a85201 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 600201106 1250 600199856 600199867
    0x70909050a020d031e030c05070b070c050613051207080720041b03360312090507151107030201050f07020a031433060303190206161b08 60
    0x5545840708100d400ba41c0700c1120f5040318205034001c40100005204400b5000c1222800710081c0c08841c0050964070102d03004000c58800030b041c1c0d02045501118504040f2054002920303502d141c00780c2240c0d41029014a10207540a0000420078021040c814030542468281161358140103400390b20802840b031030548801404007041e10348400020302003d0410000803855450b128440403480402d000428900702003110504190807454030100d0103140d840341401000804030840d0180400c0980400500c0445240400031600500480c2f502a5000b06241c40c03c0128101c2802540c8030f040f0280460700092072806a001b05903041200c0d02400e0160703c6001c102c04d18000340c800d40c0d100a50040c02d0040110800a51640e0b03400e440e8040b508403003089421640e0000208940303020203540000c41c1d07901c2542400846009940040081d007568100300303a48480050002500e660309001d40c011104200807513081d0f9807900e450250600d841c00302c0d00d09090174103e580c5203484002c1d00d1241d00058 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 600202356 1250 600201106 600201113
    0x30e010504020a0623070f0209060607020f0f21010504060c0f0906120603020303120405100e060609040602071e12050a0509012d020601140609030303010e1009091202060a020408070909 81
    0x101018021610005ca41c3e41d03034207441c102d008141d56040172803150100101003180c0c1c1c20061f054800107603000c4c07c3d003985944100d08018602050314007065001c800095050001c40288011035080d800c150b00205d100d00b89854404240c1c3c1140d952402004589641c6030320300c0c1e40c0103e0f6041210501e041c550300c80c11417800e59001400c0560006500b510002820060841148007600e2007140207209079060107906905072020346210608100103036000d82c001c180546011075410b80c10602c038120041c40c2030b409075500c0c00c519480d00c00c0c0d0500041c0d400c4181d070501106881070356901c14145001480c00014190103080d9020707001c2d103d81000b1000500f02d80c0132450781d04101c3c02405240c801c00a400c43e0000003540c65000b40141003040561070b140b103c4a040540556200c490300401441c2181e00b070010000c0c02640080203000c8000c0388036400662440c1500c201640d180c0074040d42d00d0030b100c0808019143c0701c0080d00c40785207240304000401117084041800c1080d6101e042020480e10038604 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 600203606 1250 600202356 600202397
    0xb030c0a0609080c18071d0a12060c030203090a020103020c0a0f151a010c06201815070c0335030105011d0a180f050a020715020306030303010306021c0608010c030e010504020a06 78
    0x700c890f030080007004001c101d45012752100c50b402c5105507401d200c803510f08101101030b404250784141e595400140f403c0c2c01036010b0b0700540030307009400e81260640c2d1010740702c0710b00c01089100240c0f250503009030074402604013030107100c880700f01d086804c94495400200090044801070406400a6615501d034800d02400100d85102e800000b01d2240d11200c3e007044a462003144400d2661048a901c55401c078165a49403e81e00340725000601c02c0702080c40d6868a2148903089002c00c08090941114006840d03500c0164010000c0d90200d5030b07840750b0424002600103000c00d0015010400181402240c6503a0300c00900d013640c2440c1c114031200d10f5040ca0b107402810b12440c00408441c100010084074251682c040c00d0000c0c01401c4190140c0c490100c03050482c2700130340340380750550410801400810320725001040521044e101c4c0c81c808100300d00000d400c40e0200c3d000700e0400c1c3d4448400081ca1689401040d48104041c0020005030820340e0004e60342d008140300d02030901043d6010101c0c01e40051 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 600204856 1250 600203606 600203657
    0xf0c0b190e0a200a0f210c0f030c06030531020901090b01020c151602010c050303070806150a0207030b0a0e07151806080a0b030c0a0609080c1807 64
    0x103007158020342c0d0707500e8800c1242400c40383e07070320012154400040c110700e00440100c040314880d0080c2c00f150343c10041d020070501e070480c2c0303c1022441c25025840006e0b000e00200c40c0141a140303100c002003800d61910f4240c0007030a034805820142440c0070b0040806006684914099807910305035a08000501078001c10440140d02070b5202202800014881324103130440007260310241d0980d91111014010404485030050a8980c0001d061088252030388055000d5110940141480761100340c0641d180e0307196034022541003000076880402c3c0100340c148000c402422880b410307501802e0811041000f9900e8020384400307001292400c000c50940010341c6c0c0030071240c03002e030010355001c203407902400601d042c5c41456040008619146404002c4c02c1c203070341071050b1411591210055116512a04040c1100c00440c56250141001d0022141d8681581100810580d258440e07854549003e46d820b100041c0101c60207034030200c0140c01004800402c07640c0c484100d0402e590090601f03c200441c441d0300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 600206106 1250 600204856 600204881
    0x30c03062304050c13060e0a030212010f050127050402060403020d140d09030b010b0a11072303010507170c0d022a0a02030706120b1309030f0c0b19 65
    0x14401140d0000d005050280c0032081d502440300744c4848241d00745074413605c441d0003405100c0840900c04503204c2c140550001000a0a110010391170303400050102d0201d00c00300c0c0e010381d51180000c03030a180c0ca0041c02d00500701a9511039080d41e41d840101421b80390441401c441d0f50b994000102156100425036010f16009043d0300051a040e280c941c82c1c071100c450241502d44a1142c68140f914407075501182620f0303022500c9101646081d500808580100e0b00290602818ac02204044074040110b10001d00038409046000e0100d0039141070300042c007604c440e0190b4101000c002c00b40c5e4001c2e0b80041c00c0320315910101029912901c80d044580100c100d1846054000a69509030384004403641d10100001c0c60725840c9102400308290755107400120082d01500092400c00c95140600941c0c5400346680002044030400d4a00140c40c0810207001d4820295640c603031081419070002010101c145103003840701612026444515a0007c0181514586c01081048095981a44e0044d0310a66103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 600207356 1250 600206106 600206129
    0x807021c0c1a010f0e04021503040201050c0d020d11030c1c091703031801090c030615030b040b1015081b070b150913170a021507090f0b0901020d030c0306 68
    0x201d003a034450200c07100f81300700c0d200c90f1801400883d005460b4410790740103950040c0b9116044403803504400385500010426414010305108a0942242c00c0c81809114400ea50150003842d815402c060620034030444450056801030208001c0d0301400118900d1084640500710014980c0410072514000d140d04544c01210548000015038800003026600134840300d181c0c14540d44c65501801c1c200c81d1081806002c8816100c410404580103520106421001d00f464030207294503521064440c00742070f20300300d8480046c00c0800c601d4048502c070050140148003ca0b4914800e003082c02452440043e00d03c03a15004d0003c460b00c0c1c00700100713040340d00c12540841c407003406161040442c0d01614052450741d00940100f0b00184405403c03141400800380d001001d840203183e11040e5406035080340009805520032458035010700361020030b02c940308685c10fa0b140348049061080808407050603501c0001187d80038400c0d0740c166a00414458400b409600e0b000034504102c0c0011005030445501c400e92000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 600208606 1250 600207356 600207383
    0xc10090219090e011d0a1101090b07050a1a1014010201061809020f1f050309030f0c060a0e0a030503280203130b0c030417070503090907030506100807021c0c 69
    0x941d403c001c03400c0d034004000308131032200c0c0c4a4000d18101d402c8028616034203c50500400540c883c408585034540625002100648810980c41140d21180f015580380d030291511108200901403c1000741c1c01000c182e40d60b509110004042c0a82d4a0203022040e43d44030300740d80c049910075403180004204035014500d07004010801d0800601009000780c1c016034081000711150705114441c0031540e00d00540c248106034040c0c004440300e07000a010018140420481410000c071410058074180310284050801410300d001c81500f115056a007100103500403169000200340c10505032540158050044040340040c45500c0c0c4ca40c01200c05410f240303510210502c140302482c44207100310079200340010390154a4040000b40103010031a0000d000c0381c40300d01c2c01d10421002d5800313000c07810711560449080800c14030014440326011240c11000994541c01c00c6a03610b0a052906600c0d40e0038107019015041414009454400704000070030210740d605086a5400e110b016a0345021783c0000c1d0745035120 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 600209856 1250 600208606 600208619
    0x1e030807021c0f060912140315040228170403080c0d090b01170d08010e04020d021c061b0503250e09010312141804090303020405061603090b0c10090219 67
    0x4041950080d565540c041da01c80280601811900001f0035500034002d0841ea41d03c1d0740030700180d241d80d2240750429001d000140c40a4855200552503200d820102503c9078402440240884141410003c00040030014440400c6e04522800d0f04a4071858580b0b5407a840d88052201801c1e038520021b2201c46400000200705a854020201e441071060a903074041d0079504088a0800b0217019134803040302c1c11404500107141070072444526610190224440581310a91001c0b42c0c004d0307240a440090b192400b0010503180c0b440d0701a40d48007141009811420000c11404a0440b4991101640c03039465020030000c90040b42d8920301014002d00c00700c11583c403450140392030400e91403008003060003045211104035500c2d0659050210306c031054401c400035501080080e00c0344030800e9003856030800c0007148a407198002031800001b040c40309241244503180080c00140c01c1c0e8041c4800880509c00c42189410110300341e800c0210b0240042213100d0240005058480c4d068504d01a41801d9400010304 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 600211106 1250 600209856 600209861
    0x31008060403021509070807180e030d150905041e02040b03010f1d070b030703022802010e060a02031b210f010e0106020307021503070908070605041e030807021c0f06 73
    0x10350300201042111a02d030170f0341040d40d034a4180070703040c101d0b00551800e00944d80558014061410b4070b0f9000318205113021600e034111380c02032292440940d01c440040303445d03006070710140c4020f00b0320b00400c10013441c01c0d0700c915900080d440c1c509815000c4040c1da100541d540d0b41c01180000000800030032613143c144070048010080d00d040240003542c01d4100c0707110000f010400b2011920140d44051640c0e50340e4000310002c1d03005080078003440c400000040b00c0f0700e8907030342007002c00d004a40002034600183c1038802c0c03a004008042d420303c140108108080040500000350081e0400140c8648501003050424480b0440f842011401c0c101d080c10132880303110303480f002412176a052404040700d0b40c0b2800d0403a220300c104c03039001e0741010b0180715141d550f0030340c040210b83c00785c854500721015a40707619241d030800c0c1d4a9802800041c002046c14080783d608c1180030030711802d409194a503514551f0382c1d103e185005024010341b04000c1803140900e0301030307940c200c0c000099010b40c8000780c01c1c2031889c08000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 600212356 1250 600211106 600211123
    0x50a0b090a0b01170706050a02100c050c0124060e0103060e040b04140f030906160b1602010b03030301080a060e03130f06030b011115150d152405040203100806040302 73
    0x1104112600002504130722441407449141e5040302038070540381841400d403030551103801001e08500c90410300001a81d058443d4480c504016619181d40742402c0303101600795005051045009524a280000d501e8481c04c0e01d44215841401e00441c141178501c01640141100e0384003c1c030200002d4100b00070005040d100c00d02c00c40c440d800c03841c000c0c40525031540d99074900100e4110942c3c002c2100700ca00c0d280542c00f81c46004002c02c2c0c005d50301040e9036500034080c038058410003540041c0c400b84907003054083c0030703140200906030004d504541c982005aa6a850320081c0038140300e42d0340500c0200900306000700d400030700c0d07625003080c1403a6547d4501940860140b042000180c41c060303408c1d102c0d610500700d8046a1060340c0050000d050729030f005442d442805044120354205400d15461a9110100c0500c0c10300d01030310298000760f55030840c44007070f501032240b0a10f603028820240c1c504621196400c5003600d0040d2b40061303ca03a210981009402c1c0c0a0300328690702e104e054104401c145e400660b868 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 600213606 1250 600212356 600212363
    0x203040f0e0603190b0402040f020c0102270d0804290f0903101109210f0a02180609040b0a02070c080f07060504080d08040813080601030302070518060d050a0b090a 72
    0xe100f0040f141a812080d215484000c00174007484021802524103500105521044842c005150102001113103003264088007121134118501507101d070b1a200c50703461030212550242d6403142c482110b80d40342e04041c442ea0064250140260400031400c400d655034030044400c0403080d20350b98040103601004640c1182e42d40d280300b0301c540000340024040740d000728a00321b200400a0703401d0249040030010300c030043c0c811384a0400c1c104000c0188103c1c0070044800402d44401c050501178585005004080f07540f94406e1100c0645407003806644d03220b400949074000d4100c0c0c10401c107038030b411483c0c0010380700e83c481c00341655a2030030b070200c3c070401c000c216a44020f8031101162200ca41d00c00040c2c3c0c550207180700f0002d0307036040356101520250003a21050742c81889680503500d4501034075006520031210340c200ea050766000074018020103404015180241c401103c03150000ca0700d485404443d058000d120901541e0b08480140130040108909008aa03010860030150b25103100655070720308a00380c1c02d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 600214856 1250 600213606 600213613
    0x100b2d0301090f0204050d02041e02040603060e060621041403030c0301093912060e0f0f040506060d0305090406090f0c0504050603060103021e070c090b03010b0102070e070203040f0e0603 82
    0x2d403c59602882110b04940d4007800303000e582000d503000c204c000d02c004010340091260003c50450101c140d840240701800047d10700003900e905001da0541d0311075005280303901805c801c203c40a4040010f000c40c103400d00b0405061811641c862400c403400b114106803100b800c0c4408000d1041100c0d42c40c000d0760503115001030401101ca54410040414880c681c0c03400103414101e40c228811300031580f50f0100e000f165052901400705102c00c40811200541c1c0300a008024120501544900c2c482c00960481c03003602c4180300c03e0919448140d224840541a10720444001e00c4040815000d141034400c802c1c0000d01c100100c3d070341da901032030241071545102511300d49049200c5900900440540c2c0940307001904d85d50a582c1c911005400030b40c041c032001300c0741d034039103980c0c50480f01d011000408002d8411003100d00e03024070b007010b0342d0143c45201c801c05220f6410040f443d9802c0c1d90020340042103e1100c055040a030700c580d0400c2e0f0070340c8216000600c0000810750046500c0500000007405060306604a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 600216106 1250 600214856 600214871
    0xb040204050a3e04090c0e0a14100e1809060c0c0307110609060d060801060501030b0f0907120f0608060c030c180103020f04031a0f100b2d030109 64
    0x10321003103030540080640c10f2030f4402a4031542007035040c0090b401d0340814890b0140d03103040492086068000ba44031002a90b00e0390804040540c1c000403a60008000b51208403056080c810a40c0c54000d04140580c0205022000d4107030f21481414007400c500d101810181c0302410014000d85000c0382102c0c3d80c81d052183c000490b120340d032200201d84155140001070342c02c048039070780c8410052000b0f84a459003ca014005910240c0d40c0000a00381000c40c0c010004071145400c0b11a825203450f940031505040c07030710103017200c0b9450300c01d003c7d1986c0c4030481d00c00039140d03511074068841080c010082c000b103130301e02510a8194001540300c5030035a0300c02c070110b03001d82d41c41c0300c43e00250b844211404103041600303110b65502c0c654070311819181450b05040140c00c01d0940300b540006a0030607032054403001d1000e1215000403680401c1660410741204500c50b162512045881c1031050511030300e0152030000903460319641801540c15800d0000b404001d0881d214200f8001d441d8000b80614400d552a0521 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 600217356 1250 600216106 600216121
    0x9040c08091b01020a0803130803070f02060615040611120d060e01050402131e0e0403080105101107060f09171e0f0606130207060507030f0e1b061c02070b04020405 72
    0xb080180c0007059000f080341c0c5899a440180725000600a1150601810f01010008001c0c00145124045503502c2c007280d00c922010091400502a01042c001d140300c201c6c8640481400040340d042d248139082000c00046107004107454100f0701540000301d00c2002c101520781201c2d0b070300103404603002180a400f0300d92301c0e002040105d214250ba21288000190010041c0146180c02040c04030000020018070307607900c09110045039804c0390110001610f80c0f00500c403d107004020200e040b00a03250848017100b813021031540e140705038080c000a1000d03235440c03401c259116070717500005044580000314031344460742011940d420032403400540302181e00c4072960b102100000c1c5000b0240c12040100080e44611062010034619200800001a000c121942c003194032405020300800d401d58001035100010342107041203032040e140c00f0001d5044140c42c0000742d10300458003030703002004641d040da41d58000d8800260320134081e591204294000700d0b961060010001010344030f0350003664184040e0b0366085 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 600218606 1250 600217356 600217393
    0x607050304031b1d0c030c091306090c08060a2c0a0c080124050d11070b04020102071d060f0f0405100806010801020f041509050d0f0b060406061b0201120914160b0703030e010209040c0809 82
    0x63b03042d40c1012140d10104418141240400b2409440302c01c04c1502582c034240c5032400c00011104000142e80300c240610343e841d8000c01c0d1030b00600310a03241c924030700180a055000000780c4003420081210204442c10000d05980c0910b20140c070681205a0b107501d80d18140f40d14203401c8805034058051402c3c00a00e800c4002012000c0c00c08665055915070703180320030001c42043c3c450380141c02106850120f0040e45484c42403034040d003044030b0400380c414a00503d4501d4030205030024203450340144060440c403807042041e40d0070344014001d03260350031114000807a080502e55002c0da03800403202c052842400545c1c1071507401c40380101d00d124515695030007030005849151060b98000b807086412503201c019002d62000e80c4e584140740c030f6007216461507596402e0303034940ca1064a19800c03030000c1c3d05ca81c04040200705080242650f0340c105c02ca03d010b211402d40d0040c9203015080c1a00c076401304407a0380080d41241d1900e40001c004019003071070380320014040da2080303c1d000c0d40c503c1014015010b00400d103 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 600219856 1250 600218606 600218611
    0x120d110c0d080d051f41010c080f0403080a030e011b0e0d050d02010c020c0a051f02030f16020415081b0607050304031b1d0c030c091306090c08 63
    0x10b8040b481c00603c0c000900040c07000070a19007011048840183c00d00c40904480001004440c1040c5041040c0750b00c900020800e140d4000f50b206407040c0440300c00100c030003040b00404001d0034440c03c901c1d00d07401e09003194031880c82480d01d0140e001402004000003400035001c0d0344108d540401107403151803661400c0359060b41022440031f5030007a000d4040703446510102d90180010f005143c1840007070f600c0307601e03000e210442c60001d40d440e14001d0304010782c10405519030820480303000030084d1400c40490507a1901c40c80007003911a0701805040124000c108a80140501d801c900d42c0d03401100c0004e0703d000c0d114100881c411400c280141d00007200ca421403009841803400a070020703620540c801184000e41960244c1c1206050103c0e074042141400580700540c001e400050544180051702800e40300150481c13001c85c408200441c00c10040000001e40c800c001d03d2510340c0d0394a0745001c440f024000d2441056203c1902d1008007001c0b007070394005904480280e641440071450702d20054030f00c00e408 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 600221106 1250 600219856 600219863
    0x5090109051b01020a060b1c061b0c080d020a020a080a0309150e061f0f120c050a08060c09040b2e031103130c0315020909060a0501020a11120d110c0d 66
    0x1058403040403441c0e513480301d1700600b0020004024680404010542405984409d42e078080e40e40c50401c078211440014030b80c1003801c525003c03141c0060b42c0e840404a000700311108804950104154213810b00801c0515a516000340100ba25080c8441d001009070001c0e62044505aa0740c181c819148601c80c0a056030b07003906140644480d66540b860400c3d04850100b98081480c114000003841224100301d00c8003511120044010724610380c01c10450341d19440d031000d8017171503102d00d04000503034000c600550440c11004c4003642da014041c000601808501c1292a40808101446440d288000825aa051099003484102e0107102c1ca015000c88103c13000810b1019000c00018800791001840002003501c07540d4915078036902c94544800b103001c03500c2e02000055000074030191929102c40312540c41441203401e007004904100000b9101c41d01c002c0000e01405992001145558500e51811000038409080312120450b8100c014125512565a90a0740c0101c11514119041141c490b0307128940 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 600222356 1250 600221106 600221113
    0x60509060306070f02070f0602100506010c0305041e0e07050a111b061308030301170c0a03111309050607020114220308042a0305061e150d050105090109051b0102 71
    0x300c1c00c3d425a140f6103a00c64000442c0503600003c40c1c80c4080f4251040580307002d50040402c44503c0024100308d0f0740150050381480748641850b4006a4403030215002c0e02c0c2800040c0c0030140f04080b100305640802d40206074988140c03402c00500c142d00c00042c001030265580c804400c1030102c3c07201a161800403075513404c1e40c4030b5540c0d4400e0b60f084c0b250046c540361240351414020941d5800d5a5400c64100b83c0242003040c81c00505545240c004014560343c4240071580061900d1070750343e44507409141c6414003405080211400e00c01007066034031800009030001c060b26820301c1e000310001e0081a0383d40281e0080310881c0081025030403006403a199195407440000360002c81070701c0c1618031580060049911883c1110403d0342940c00d04519217080300123000f40076665080d4a441400d28a00510703030010008528000c801c940200c0503010380003222501410300580412010482c01c249017900a003140d8201001c0c850040340541c856015203010344199076404c5130401440c018031090300c16490040e071 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 600223606 1250 600222356 600222361
    0x110705100c0203060403020a051608070501030c0215090303010f1208030406020313051204091b0210020d0204050411040905010e0702061f080a030804060501080109081626070303060509060306 84
    0x181000003555811080c140301203074107082c0e400685030810444049005800030310407481040740810180410208441c002e06038981800e05060fa20742d0303035110381e80c10151030300b585e0f180c814001d200034980341c88140c860a901c2c0c5012001e4642c0c0303910a1141c401742141000c00003694004c40031341d40140326031218010349185c84588800001c1c2d08040d0581c560110300c04130007000a0760401038000e2006002c05415101d610300350b4a20b0489100c1c443c010014003015011010642c0e000c03d0381020942c2164005031141360003e200c038000d000e1500425005860007030070740c0000303016030058800c8a80c862020301c0b960307880d0b000080c940c060582c0e020303026074000004203a183c2c01301c121030b254421600e00c1030702d074443c2d84841c2c407403900b001c20300144d000c240e00c44c0c00d01050003198042c05000d00081e900030b100840075503503480c240340310350f204a0b1500c2c24a01618410894250030030441c090341c800540001c410b40c0d1702441040d80c031804044010a181000008482c1800c0c4040c0b0300c01c800040c0502038a5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 600224856 1250 600223606 600223609
    0x706080103120912030c02030607082a0d0204080601081018060509101a0111071a030405070503060403121415090709080d23040806160207030503070b16110705 70
    0x10b420765244502402004500410070031480c58180302c0c058000d030790300c0c101202180107140c1001c001610702800c1101e000c04100d01d980150380c00c124203c00344910700900f0078640ba50b83c0305074001d0211108100340002400038070b0000004202e070695078198243c903402c1e8400c0d130500e801c8405200583c04080c00141400020542c00e40c041544044081c083e6880300700451b404100325191441c0c41e1002003c044408581940e00001c848094074080000b042c4460810318644000303200050003132a42d03c00007001608000b0240007410061001404661603400c29203805007030382d09801c2483c0300301d40c4bc00d901036007140c0006501e68080c00c10261005c455208000601c102d040c4018064818003030038140001740b0741c00401070084901d11580d00c00305030342004080c0c507220340d005440c03c07101131506020622a803040450040d81004842e201100f00058026040c1d042400e02c0c1c0c8003900c2404046150014408207901d024400c008141040388501d04068040d40e18052000406066903c104800e1020303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 600226106 1250 600224856 600224873
    0x70503070c020904080706050906011809050c0306010e0702060a021813090b010306150503060402060a0503040c1a12090a110909011e1d060c0306010311070204090c06110706080103 79
    0x3004251805a002508503004501903450a80d4120307040c000000b003c03c20300029101300c9400c1801e01004e8846940b40c1000c40c07000c0c1e80d400e02c84040c041d5462038000c04024080004181003080a802d07200150794550602c118002c0407640c15015008110000b40082114400c845040032140e00000c0c0c41c41d0781c01d00303124880c42d0030940105841d541e0001000881c1000c1c01413030085109070310110348a804003205505400250340070764000d44c000014400103036603980507140ba101c550f1070429101d9560b0304241c002201c440d400b9251500c803090450100001c0c9400505d654020707560030a50b0f81d250389403155644c0c2810000909114000b07890343ea62440c251940035003040180b8000b01c0c0e0540c3e014000d014080d8044041c030071195590900d54101000d45002022208030000605010b1914065803400380c8001003496042540c0c0d44000c0400c40b1010040d11001038000c0c20070091000d15180c103408150660143c2008180c034183c1c030720100b0070300117100d00075241c0315643c0340318503440c56032070104c1c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 600227356 1250 600226106 600226111
    0xf0f08060d0501020c060916030c050f0411160c0501082206110a1106090102070b0f0a290f120a061a03010c020709060504050f06010c03031d010e0c18070503 69
    0x9101c05000064004a442400a44a20002040076118900700b26060390b140c00c83c00310045480e080d01c61000c2000c103251001d03a0341100d5060b1400081008901c0008005101a100713401d61104045982e0760000303400c5003140459031180c1711058559884000540c0d200e20112148102c20000c0d042d404803446201c011080c5c494410310000c910a503800a0400d41c2c2e4000d00d407148001f640b941c00007500f1100412049030420850b07002146000c8840e210032103100c500522510103072022034041a075459042e8401040e0b8000104145e0b003000711400380b582c03840074140f92640304801011190b0518a0806220080300040030014490500607a4800001e01582054003000c00380c07810200405482c02c3c0075900d000091640a400c1003420001c900303040314400c1d0000c90003140b901c01044420916905000e402542c00d080a54811300c5500c0c0407800380410310880701c208290307005420480d03d41508518030480107041541c40c812080d00921075802c0113055115030301c080c0c481c0441c07a190301550003580c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 600228606 1250 600227356 600227359
    0xb0a0c02100608030d05011706060118050d03090806160516020411040603050f090d020c0f0402070c0f0510080402090f040203070b0301062c0d170c07030c150f0f0806 73
    0x100c1e007510401c8240c086440d60b902072003041d0000102a20011480d20807240500070160b0900e0702c000c90b00b83e1599403610010841814810740d411018051486814404010007008180341c4540c10140750041ca84850f42c030a10080d4400c9901281a00e81d10307074808030303030303c612561200c0c02d02d84000d001c025841d240240590300b1541d1101035844100c1c484000b00b01030184c44d10301140c0360030700f55020359801000030150400c2c0c2d00b0142c12086283d60215103030a0004084500e801070410000c0018000e1152107401000766460700e0001498a080c84002c90807140c0c07c0b40c40003071104010805a41b801c3d4101c074000d60181c0d241c0005801406207030000c0f130300640043c045440309a251088010741d50310070b82054000c90980c04074101c0300024a8451303141000717110402000400b05c080400c80c2401c0030340e00244a104829410000140b1800a44102c1007086040300e034040d6482c20030012081141c0182c0503000d1450110b103202a0040d0010700034840c032903481045e04000240100d8a590020b84100e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 600229856 1250 600228606 600228613
    0x63005060f060a0e13020f0315070f09082b0f140a14070f0b070c0b0a0f180c15031509110f070317100617090a020a030803011409040b0a0c02 62
    0x200320800040c140c90300c100c1c40a070081c0301180141c010007040c0302e80d05038070a209a100030009c4007161600d0f02030759003100c413504212500301c0c1801821741d05050590404030403446003078101c9041c82d40c925441c02444003100d240b00304079084e40c18102c4188080c1600000031444518a91440c0410707040141250982442c01408907080d0090400080d031000000341d0347071044d5000c0540148511f0409498005040b800c1c01036503011150741c1d850b02020004c048030101a6150302c030000142d06900040048020b45c9d540100b00c203540c0c90002045e090354003a016500190f09809a0040d01921682c203902c554400140142c0d442d00d462079000d04421280c46080040c24800354401c005010090b0451501c240c8901840b0500c04003040020f40c0001c01907100420120410458544c0264a40c100721403201e03003001c0030341c0d0f4003e40d1902d403411182c402908845101400002c0c410b01c200614140c40b5036a0100c05085800400c000c01c2030340680e400b40c0711440e180081902607400303030b006400102d07890065 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 600231106 1250 600229856 600229859
    0x1050a0c020307091508070b030403081816060f080105031917040b0d02040503011a01082202030604080306031209060a2001050c0301150305160f1101063005060f060a 73
    0x701d0043d17419101e54000b0b0075007000c078140400d10017440082e015100c202211802c502d805d8500405514016040c01c030b83d460381201d49040301405016540000240c44008008255156001441220f1240400000411582c00803403a85008179119200c070300a620f461001c0c6200740c07150550658070110201405d0000c2000254601100f0050000144c018000580351468402418256654115401c100390f0203451400c41c0c0b40c1e00f010040380c0004598407036111141502c3d000640180721010065814071403132003007000300071808004501c9114258280c84a1561481d03464102e4000e501905900039024017407004100d1207107205441e0f03800b01c888040c1e014072585030600d007154010340d48403140d00400001400400121f0001a150541e549810001441d22000032003426012410030010042034030042c10300d10303214071290044164200d000b084410350f03c18000c0305000c0800010090402e0f1500e011090340a200f035003c10f25a0004050031315a0b03036112080d44840304c002c00403640b00e081c2180 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 600232356 1250 600231106 600231119
    0x1d0f06150916050c16060306050406090c08040b061302071b05030604050d030216121d0114160f080a08091e1b01020f0703031d030616030c030f0c02060604060905010501050a0c020307 80
    0x5d407800148666140003400ca810441440151499500501925414540d00c09041c1d0390041006a1203500007040c1c003025103501c400141d030400c41801c40030f070060011540200340010a256001600340c0c109030031445030384d070f082495240d0800b2a4080d100f60080890080e00074002c0d00200000b80c407000c0c7c0d03099003000b55580e01c031410004802d0303e070004a80d2260b5540143d5403664590345000242030105c1c010300303107081c141c90034807501603032001c401300108120040158004000100690010182d81c6940c03000320000e1080d20106c1d607003501341c0710310643e030f800324a00c2c2101c00039000284005070911000142420345055245880359046100d0400030323100310f20b41480400007a41c804c0d59080007410f02100b041025402d00c02c40e2501ca9004881840051040360780c90b030b0403100c000d0801050f9034409402c141d00600f141201c2061840c00c00341c0c0d03002c041c2d502080051040000700d5042040b59141d011a40c21100b090103038501084041000341c0e074680c081c041840c045480201114100c070703140c14 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 600233606 1250 600232356 600232393
    0xa0c020c09070807181206090204020f030f04030f08130209090c04020d02090108150d120521012d05060d150b0403020a0602030304050705041d0f06150916050c 70
    0xa07840d40000321070f01d0500000070b07480000d0004100c0400c45907070380c150801821031190201c180c0f00a29069807000309008545071b0b0340544142d00d048040315a104d207448442c01d01021001c65048000403440c1a40340d203118010a40540a0b400f13400340341800c801140c0c203100c12510042c2401c8603034803c0441d0b10000744d446000038030b4030035a440d2016840305a50400540342c1c80d40502000600c0000c1c0750340254980311400c09088554001298200701034038190103969134441c801c544e1480704444500440e5030b201c0e66403482c3c12904054158010320518081c1182d0b113000c09440320784c00040200c030401003464004c0141c07409100c683c4c00010482c6000b400701e940403c003680307c29801e15020404009500d0724010520051a140c00910315600d8507982c3c0607282d01c440c0c05004d00c90f681e00c0458006190300001000703000d800c10400c0f01c8524840200c1207035541c208854005c0103020302e01e0032400c0c1c1c0c02d00300e05c2240240001c2e2601d280400c1d100009441c00c1d00118160708140c403584444c0c3e00e4410b44003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 600234856 1250 600233606 600233611
    0x91d0d0203040503010605060705060a021b030a0302090a120b0c03310203070e04050c150408030d061701090236040b040201020709060605030610050c070f0f09090b0a0c020c09 77
    0xd80080d6611480c0030141403c0d14400e5020500c81c150a00a40d404204c001c124a40d001c11250401139981c0c1c040000c46140d10091504030302c0d54800131690190041d0154000d00d50007004503101c1078607554412a01c445003030b284000800408111000c1181d141d2800b0146400c1007100c500584440c41c0c61040c100c0a030511040d10310f000502d81003a40c20b41c1018442c05011f0096202e02d08030f40d280680b243c6689000003809240160702c40c005922039070300201c0030385002d00b0441042d04ea50304e14a06040c0e028111900500070092512007110405500502c01c04106550241c4010720300045260724100480603640c602e882c1d0b4076050703e9021806c0a078481c0d1403180d88504031010140c280f40c000240707400d407581c1014207828031b818400c1c81450382080030790703034048412501c1181c41d4582c6071045415009600740c542c15403185540214a00d91002c0f110000d54034600c0c105e0400b81d030788001000a072a0341030030141c562022000401c02d42c00c1160003a030424039040c011925138400280115840b11003c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 600236106 1250 600234856 600234883
    0x111803070b070605010f06050325120f0c02010b19050d06020c120705160609142e030b0405060105120a0b060313021e0102030307180807080703260301091d 68
    0x4a50040c071890440700306c0c4401500051900500f1440d00480d05c014a000201410290400441c1c912076001c2c030900d10b001400c1c1075a0810700110580c01c0151019101c40c8420707001650a1001811040c10420b0607141110001502070b102c841c54001031000001480c5025980c0355000c1004a00b070030700c10004d4030301014a002d2000d07550766041c10100d0034540d4014a20861044980c4100415544151940c0587e001d0310302c0c07a58000c48400005140300b00c44904401d11400010440214442d21260071807070700c0041c1c4060082040b00380400086036001c80e645408604140301d48010034800d00340c1e10ba80001c16140000d01100000009001c81c0c10803a000c3e0f6280094a00750411420590200e01d01c405640d401c03140e5407070400001030b40b2408000c10300c108000b4a10765003210440b8214002c4000c0c042c00e406c0d161402e132600310580d201d50544c0010b6aa20b0b8007100c0116562424004180d80c81c040302861a04507404c2180000140c0306242c191540c00e840128075940b001c45c01e0103001c902095 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 600237356 1250 600236106 600236111
    0x509040b03150103150207020a14221a010c0c1401170a090309080606032a0a08070e07090806040807020f06031807050301090305070210021606030606080a111803070b0706 75
    0x342d460b004203419210303c2c179808014014491b400c010b0700c50301054801d03240f41020305501920540d0124180012a0f0344800c106040d04036522001702807540500348048100941805644440006445807080410018620b1510000070400344090140000b113001d4145030990828140300d40c2d00110100079100d074031106585003800020150003110b418024984100030342001c1c9007480000f81c480401c03000444c040030507600b070070645c01e125a24001c0d41100007042c0c42c0304683c07941c1207030b03507544410300030b080c0c1913070510700810030300c0b40105804011681d00400170140e95403650b462030351941003010226000103a205d40d04210345e40d041c0c0030398800c0c0c0440c0441e0041c0c3c00b84011240c40c000717060b80024000e91501c001c403804a58494215500d040d0140c40c50394420015200c100d1521600007011a01c05800c00000709040b51f140d0040800c54280359602c04503612659045821900c41c500088882081008904101081c4025099403607400600340e48245950b1402440030f60f02c509011a8a6036 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 600238606 1250 600237356 600237359
    0x62a060b182e03030215060f03100504060f05012402010213061101110307020307030e0a0e09030c0d0806010504050904110a2d060503190e0d05030a05061503070509040b031501 77
    0x401c074020303210348010440c0b0005103452454a01a4503814040411500c0710000307070028109031106400c40303c810360007070100d41c0d444220a488000401c03041c2d504036070807400e0454a81c84108a80545410f8803120401c000c40381c4580815040d00310058200c16003555000d0149222245291300c0d400e004282c2612604000400c07412242e007140e07614000e0002c000014002c1c000c100394000283c0d00c00c20303854105000090702420003d45446180d42c4005000d0b645841000350800e404005064501c000c442200d000e51070400040c1e807129000c03682c8600050f400c0c00100040c1c6018065030790814040d020021466103402c0c04101d081c02d26400c20003840668003102c19040301460201c050b02d4041500c078071116070611070004c1407840b02030480d80703400440943c3c901c8210a281d000080f5065154100d0700035029042c805003054204981c4204a1440d200009055080070f5600c1c083c139400031408036245540300394050b10070740c00c40031145822990b2101116140c2d14200040d9813034031003d40010f045503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 600239856 1250 600238606 600238651
    0x18070f170727020409090305071a040201140906130e0603071d0610090b0d051e15061312050a0506130c03060b0d0204090c062a060b18 59
    0x6468482140c055101c0c050401c030741d007503260800004240c030640030b03150090740c14402c0b4082e000b907030845a02c0900d4498448201a080740040c480244a41c400d641c5140701c00051408001040364080c4c0030504030385449501d480c45030020000144c004022508101c250702180403545516001080c0819043c014090f5611b82004844001c2094480311044c000100f0701c909410b40c005040b2602031000d141000f200940110007120141481e54012502d4104841d1080041c180070340d52038a144440300d02c031421200d03241c1600352041420210f8080c0300c01040c0240041079010401c0b2014840d04042d01041a0782280c440e00c0d4858000c8000f0f14180c0c1107410000c0c02d01c14080c100411803030091800d240019524104c0b202200e801403800642002e00c0c03408601907000d0210020740c4185001840c50070008c0e80910300060b034020396210000403500321181042d005209895206c0300f0340d0500b203000000d5540e00814a520b101401c1801100802404c5400c40c4030103855081d040c61a5100e1051310 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 600241106 1250 600239856 600239879
    0x7050703140706232203060b060a0824030d03022212030807030f02030702030a021614040f090209040c080607181511030c01060f0506030405030a0818070f 68
    0x701c4034400050503610749407207806840d9099640340d008560b009240310801e07426070307402074486448034080c140891040b0510f282c0e00050303040c0000c42c0c1803490a42081464200340007a91810f1110380c881f480c154440c40c40440302e00045150700340c42030007020341451441c1c45c103210030340556002d41c03005622003402e800d170410340c00d415402c03054080090b28030030440c1c0c9000c242d0404140787c26040001560300c400700e04401420b046042845180e000206018846074000002e0110081a0303095402c2e0b203c031400c0403001a0a2840352070b4010b4107081d0a81c0c03141c98154403040c2a4075003484006004402540498280181114141c5049228038400c000410042c07040f0782d4040c18614041e015130005982140180020f8080c0c0740841d04800c0c0e0005105000e00c0d41c00b0100d41090080781e8850a1600590340a007001d0301501c4181001102d001803181854000d99009030b0340031001d0341c00e01d0f0f081c10080343c2c070510003440c8a03000714441441038549030b000c0c402200948200b0040703000310b5040c407250081 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 600242356 1250 600241106 600241133
    0x51f0f06050d050307030f0207080d0503010e0a0e03090418061401050a17120a2001020309160503070b070c030b1608091504060c0e09091e1b01080c040b07050703 71
    0x1600e81402c400001a001008940c00c103179260034034600541602c00c003289001d61540045025104506410300d50f660403101550403109050840da10554603c00e100d01961000e4040c600c880d40144010402481c10f41c00c4154180440b180d585415905920f8201c00e4440d202e80c50241001e41c940144100d040c154843c50140c036800c0744281100040860959480024020490400c100491101c1805215010040044001004044e101440c102801d0b000754400e03950140613100c3c0c40d01120511194108010841d035000300a01402c500d0f141d0307403440580c04200d00301d078400c0d00c0e042c022000484111000d030041141c030102172050841e020340500006405170550311568008020385107641414115640e1090703000801107125625520103440803100307025020b0f03205101004200200340c0000d206e540703240016510003286800342c40320988401c03c0c000c40003003880c1c4041c4890340550203800026000381d50b00034800d1400d07030b80b401c1520440c0c1105000300c4154002c11010011301110100998 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 600243606 1250 600242356 600242359
    0xb0f070e010c030509010305130807060e010b040605010c02060c01060b0711010905010518151e03062407060e160803030f070305010f03110f030d0c0b070201150b07051f0f0605 77
    0x2d04526281e100684503014010681b81090f44500c00505034144410b00c00034000d621210b081d80310076441c9400702c041c100f48841000b9642c82e01d461000303a0324050150780101c50068552407010764050f028082c1c0ca03805042140300b9903403180e030700007181c0381c15034003c1001c240141440140352501c0d41c001400305841d5406103040200030702804212020201800c841400c0855002084c11503005407030405000e82086c40745250541c43d050484541e1420041d4401c0354101c4050402004280200352103024401b40d10345203a10510142000038440e0348059030301d1450700102c0d5502c0c503620614034051851900104e08680010003030142080019000a13008225030030107004942c106541442c10031500e110107817070034241306880c1c45c141c0c480140c100c07020f10001c5d00b5642800b10180c1c01620b20b40100c1c20448800d410030340020500751062003503405d080030344140d000c4803d02d0a2135161706908140420340c2c0310300078501d1700d0041031400c0358039140f14038a000703000c11a442c5041c1c07440101c942d10343c0401d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 600244856 1250 600243606 600243617
    0xf1406041b0b0d090311070f030203070b03040809060a0225031211190f0209131205030c030103020f0609040e07140a0308070b0712090501140619060f0c0b0f070e01 72
    0x50145101ca041660f89003c400000050403105900302211466660000a801400360140c04203540b84016201015a0f0094085a5001d41e03a0752003224548401c8402500005c0c0501180781c40307140c080005c08500c2d500388110f620184001c04c48008400c090000c55007400a40324081003040781140e80c20700300407a00c0c201090b201c40d54851141e03c400c00600102a80046070340c2800811040c03004200702c268010341107a1451034a5504c0c40c624104030307182a90f18405d4800f14290391172182d0212440380340340d000d4003802c41c0d10759401d01c1085180c0400310781d40f0203402c1c042c494140c0c54074400d10180f240d80400800f103032840c020000c400c106034410900e0140542d0041031001c5280002164180340d40007243c0300c00790b81d9611048800d612400b0350001d0340d40c104041001440415045118503081341c00070000142c4498080200b804a200390151110700d444900b0080f03640200d1144242e070b01c690401ea5042d640c145d442c9400d402045810180180f2034030705002020303900401c0400c41403000e0810 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 600246106 1250 600244856 600244859
    0x40906121a0702331e0108190b0c07051c1b080f0903010e07120213091509110d03031407050a091707030204090f02090c09010e0d0f1406041b 62
    0x7134988201a520004100312206655580c10071140e61007900806058060130314101002d074508a402050001918003600b100081501c901c08a00d542500104070001c00811704569180c0310032440051203603d5442040c0324003c0803c000b401440071546580028200b001d0f400c15000d0948401c0711340c80c401c90403462100e0070003e4200b404444214040e0340420351980c141c00700103800b41129a5010400740201600024406801c3c0c0700c17030710b02d0752085840c00c6800c9440c0d80d2075400c8030f688400242800448140403440304890350f205a110b9809500002d0a2150800100300c00e800000c404400180d540c0420000d5441841c5202ea00642140b40052511800312002061030140d80103094079002d030180f0007900c10204000d000d004560240090000b007509003005502c005a0940a81c000c0301080005914100d06d9411140100c0058403804044502401800291081003a04032090380c464040d4030701182008164141d041caa1034020080c0d450203203450b006d244000000f0500800c0030580 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 600247356 1250 600246106 600246121
    0x30507020a0f180b040e2b030b0105040605030703140c070302060105030c2d031005010512070302030709021b01052802120c030403020a0c0603060603240b0f040906121a 74
    0x140f03824884011000840c2c0303200b0400000e0014030030000ca4100ba4070a2034483d2010030002e0b045000840400701da11008500291415802c0d11780490742c885c0003032020402480214000c0000e07580200340c0d0318000440c0c071080c1c5245140c1c1d28040d00c00c40c050040110319501010390400460340942020b0740984100512140811070840c1c00c0c003502c0404015a400198201e50310025041c2c030080020700712109a40c0c034405d4200200030030f01405008105a1501100d00c0100080c2d020450364040c0050620900e0071035413200a4011184850007001a26122420355100b4000c45000d02c900c1007a442030304956207452405070b15803001030382d821801845900055540c908403581e2044805060541e640d41c1d5140803424407408400040c006c8498a41c00300f41c05034540d00c50380503921182c400700102011100c2c1070400c50003a0b1041c84460840c0710060216121681c003030003c03410f203610020300b007507151604041929031940068030221080403a250900c414900c0c112000b0903820111030302070800b000c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 600248606 1250 600247356 600247379
    0x6030e121204081605030d05011418071d04021b1501030f0210030f150e0603030c0c100e0603010608041704060509010c0213090c0f080732060403030507020a0f 70
    0x40c0301a100b9480459a1840c03620540da10b9115640d2100c00e680c0d070b92403020f0b00000202307030a000d09048080010680300d030300d0629a25102c3c0e103c2c0206800300381caa0301c05400711410b046000d0304181110140e000c03405503032a41d001400b13445404268403540032007400380051420310141103540340d01d0b1401004002156047c1d81c46203080c0e8041d80c003c4240c0c03208003000d1300035018010290240c54945075002d4800303005484c130b0f00161501c080d041c00c9685c0f205810941c0d24010070602c0200c617040314240000c07030303c5d03d085000d00a1281d414161810000100020880d410981c00140400c101c0b03010801000b6040c248128110301c01018541803074103002008002c0c1c090542c0c0325050064140b0540259915454600c0811810751400e11040885180c9030f01000018480c001c06600e0a80000c00d8114010402605444454a490340d42c44d041c910074080712411081d1801c00e0740c01c005200d2400d40ca401e80140007440c082e07101d0307581c1d6540c1032040c060800340b1544440044d28620304240944901c01 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 600249856 1250 600248606 600248611
    0x1701061a030705040e0a20090604091a150307020111040e0a0f090c151b030c15060f06090810060302030304060c080f0a18060318030c0302150106030e1212 68
    0x8405035440303030340e00c4005691a10803500030001010082d001c10001c42443d0b0401201600100008001c072550b503028a40f49018480402e035110760207010501003c5e1080d40310554060014070708100205132000480d60220707002900941030980002040402034090240324014000301c00035901e000c2c03912400d40c40d0030300e01400304811182c43c1d00c0c4d82c410401464205082194000c01584e050710754a2160442d0b0103d00e002c2c1c80049802e4448612018890f1031102c240d0300e4040d11070285a14450396842000d5694191170104c1a940d15000700c1c040c40c014018030003503d095142e80c0e003000e0501100615115101550940f0f07682055410320050710040b050f201242c0481c10704800f06055481c0c90021401580340003401c040c4003080d440703a555846110380d601c00ca140c0000c143c006450300d07002c40540e05115040c601301714982e80710301d0000e031080030140d0043e400b0303206503510548000b07024600500284d0211000a44403013400800c040e081c0607a400740c0d034a00198502d840c0e60500d18a00c01d2a00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 600251106 1250 600249856 600249899
    0x302030d0c1a06040f1508011409060408070305070f031d040e07050103050606040b120708010e1605030c0d05041101020708030a201f060306061202090406050601030b030d09170106 79
    0x1010003140080c4c4881c0c000184008135110280078480ba030700401502e0140341d2080d01141d41c01c000e00e104080b00990422405402d84402914543d03a440d02c44070070540c44071104804101d000c00449010419075035410303210324881d66a0541e0311405034182c000d0110030386081071045141074503040003203c00048120464900782008100e03580e03072000080d107034015036000901e200d0700000e0500080b0a00060b003403046a054440e02a0350740c80c0e554503400030314220340211044c69503403185140940110051548111071721545460000e15140310030070754038162011586003010650700e1010790b0f0144501d07006402c0540045040c0102c0c2a801094054040d00c0c1a500451840103017004640074400c0310dc120f070200c2062030344c030300303003203041c070b00200207034403065689500d01040840d0001816541d01c0714542c0091940c100c64542c0e40720840201400380805040c90380c3d0f02103140044c0c5040c00074441e01c0b5660f0310799803c9a46032141007a200b4003017041143c00c1d41d1620406101c80e2581c5040b09000b100c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 600252356 1250 600251106 600251153
    0x90d0810050d0510110a2c060406050304021f0906110708010216051006121103150108030a08010e0c0301271d0d030510050f01270302030d0c 62
    0x980d492000391a068a4004541020700110b403034040c03250015500301e280050325810401d4110300c031003146250007003224074800101e00d000c142000d48190000071301d09014840c00109940c3e040800107540340c0c4503500200114001008020541c40e00c8201022003180b04452141000200003004000d0034040c004c48081c4419082103400000381044101d000d001300e00300842da6401c3c0520510300381c0041071000c80301403041e1254000c102007075018500c22644060b00c00541d9407030340d03541c8504443c102842c0300e4040c8180b44041445e0151401340038020003404020b580c1c0e0b0b8084d404003c2405105822107515180000144140308141d681140d04640c240041580c07030058200d203da04d0501c885c0c0319003108a05001c05111240f06210688085000304012188081c0d0011000d0742070b618110749002030341c135000038100b00c682440d85003204080014505042d5000c801c1241c0540d50084001c0202018610f01d003d00841c10100081c0703550405c40d08080050b034086955a421021425212641804 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 600253606 1250 600252356 600252361
    0x1113060b040911071416060f05030c090303090405010b1c02070c05150d050405030a121505010e01031107060b0a05011b12030905030703080406050606130308030c0702090901060617090d08 82
    0xaa00c3d400b919a841d620140030b440c15040c428006944200c00079582c84420036a900001c0c220340500171304c005400746234680c2811566070030100e6003143c00000c40203415002c100000840341d5201d101d842c1c06080301c0803010352a0800031407804008109100c0d641c3e0183c1c8100021400305e11500c000c0343c1121001c58010301191815080c081f450302400c0030940c1e00c44d0409007403104110020000e0510005e9940d105800750520248400c196120000800c65003514200140615441070468901c038610605000c1140c000d8803400d00e6103503100d182c1c1079498654510783c10402e03280078070302c0000400c424030b08110341c0820280c100314070b07019940c0c000b49828520807109410310701940224230b170b2540200a40c0d0301c0ea80c007800c01a240c680c08036001ca030b68914000c001a440d18019094884000c45c0482641c2c003a42140c1d0b4201079a40301404424082c101800214016070790f00d0106c922401700c050007c1003080c0b030800040d00342c20340c0170084a02c1c40001010082841c0000520800300f18091402c03074100d8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 600254856 1250 600253606 600253631
    0x50301033e01020c04090f030e0301020408070909051c02100504020307121208010905070e27071d0f0609060d110f0406020f030a090e19091113060b0409 67
    0x9140507141d120690a00705800d031121041d4075810880e00000e03001d8641c460100000c0204403494900002c00030090310139201c001c40d00c5803d800441960160005142c0358503600f00c11324145080d400b0107011030b200c80c2030304101f020620010400401041d1030701030b110f52200019484858003144214040e0740e0780005000c0d9542080300e2001401c02e04040001c41d4250300b85004010b03007154811010071030704000000c0080140c420207204900319550254072018900400019150960416091042d084005400703040c43e900d509001d84595100c0326415101d50420040d40140e086085121744609040700d02543c44000840707076170ce6011240940d031840110304060041a09521482054202140007148400d1460050040c0c981c50707002c4480c0f030f00d00900d245d5603900ca042d407107200150b10a00108584001c4941e200e0304881c0f03515044d84183d607017540c2c0c4802c549480c1c0d015a080c1d00c1800407580282400d01c020308441444020500c01141000e08203011440b5601c02e00f06415907904481c80e10 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 600256106 1250 600254856 600254903
    0xa020d09020a17210405131b080609090705060a110a02090106080609160203070809130f050a060f03021005160506040f11100c0305130e1f1205070306090f080316030c0f05030103 78
    0x200c0656000808e903490200354020038511040314442c1c06840ca94002c43c1420000007502400c586005100c00e1800c000b0140885a00d07417120201803862292084d4000140c1d9000a0507020302000d039143c0e2020300d00b800810100d02c2d009450040301c8070325002c085154540c04002c856105402c110142c0d5580c021401064120030090740351040d903441c0190b0003007030419542246018070300715401800900e0b10b561018650207040d11009600112600b01162002e000340b0142c070b8080000483e0300340c80c280c15110f10341001000c40d0200e0b18060060500420064294442c001c0d0b201c0655403801d1450241750b0240c0101d015400c040c09002020032303041d107208446000040601003041c0720b0031315800d00108031000b10700441c160440e00c803030040c0c0108000e03000e00c074803c181e07641100c001c1024910310b072100e4009002d6200c0c195010007441c202c000104612134019806602c2065100e019441020030040444044072800401c00c50000e4407480e81e107601c003068905481d00131130340d410020b007040b0030100c2 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 600257356 1250 600256106 600256121
    0xc04060c0807020d210207140112051003020604080102120f091e0c1002100e060705040308070c24020c010e060a0302092407051b090a020d09020a1721040513 69
    0x15180344045c0b00c03881080040d04800c0301400b41c0c085071041900e07031580c00107500040c0950340c0000c001416030704074041580c0001350450b40d80031100e1780103502ca80208920b82e1040d00040c00300c0e0b40003d03012014850311100d040d4040ba00c071921008505040f0342c03c603103601d8014510f03000042c1084010001c400d090207500d03120080107155038a4400d41c5240a5243c1c003243d604803810b01d260007000c0081400102e40030340b00384115a40c0c1480c040c10340c0d482d040a41c02c00c07403081d0f4070f06000c0600442c00d01680e00003661000120000030301c5c00312031b00c0c40081c64509000b26080c10004504031400c45a1101c01c1034074000d11440c01d01584680308413000c138085c2d0300011001030f000fa4640d00c101e14140740d0b1100601449000d070b81035540f080e8030780e086080240001c60301950400e200f1400101c0800340b0394050300006c1c2d00e0103400300d401131094000030418000c54118100544444036001071041c0c1c00c101d890307a40f00d000c1120a07444440403901d08640e000314443c0c0d83c012442c0700e203d01e044003050350002c0c5 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 600258606 1250 600257356 600257363
    0x20d0204270b01080f0a240203181e0316051603080408070e0601020706030504110901091d120a03090c031b060f051914120a02070203060c04060c0807020d 68
    0xc0640001c6408651191094402520324100500000c98a00390200341c541107040c0140042085802a0b0f880d01d0740e4080d00851252046813248140c500740c0307010b000950068103041224020f10f210501e2090406061390b001065000c06042c00400300b07003000c001e903859401e131104842041e200320308240781407002d90704080c114643c8883c404020851b44c00090001c0d0b5004c40d04030b501c0d05448001054100c0340c00d07242c190150f0f100c1401044598825000a0350040c810100d0032034208280d80480c500100c280c1040192680790032a101452150004004103100000010002240f941c282d80b503061250807994010542c841e0004028410a00d2000c401103511498200801488a041001d03400301030040e000000c0c507080c0000b8030640b08000b40c3c0e0030034165400d001200030044c00305840381102050010a41c420920000d4140140f205515104040351400503955280a104050802da40103160248240c0d052009001e0b29a02989450501d0703440003640d956440980002840c0f000240d9004 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 600259856 1250 600258606 600258641
    0xc0c06010909060c0f080c0d0b030a03091e05060906030a06080607080a0b0105030144010209240301090c050d0615090803180603040f1a0f0a05070804020d0204 70
    0x1450802560002c0d10b03807801050100450b10101c5400c507605150118410001000703000071841481c040340c010321000c1030100c1c0000b22810744101290400103600020340c040341c00480100001039030070032802450f04d40d8a4025081e2403c082c0054050301892030071030301030640880020012320740703a032101000d0b24000040f40d955103007400e4000d00f1110101c1703800d000c0d141004001e11055010b8020389042c1e846107a240e420030314100c130459030001d0b100f40380c80283c4041c000c001d184610010607110a2008060005a80c42c0d400034240071041e0b0b801c00014850412021000e21103240d04825207042d135540090214281070590422141406000d285030815890204000b0b5140c002c840418403c0c5d680340c0300c00c820f107a88d44a007a030300c0340a080000b440940e10b030b80c0420b00606c0c24400031030380148180103200e050b10079078449004048000200c0900b22480209006101c1c207400100c503805040e881c8144400d18041000420820707010700000d000350b08040810085540c2c1c0c2e0003040b950b90740d40c08403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 600261106 1250 600259856 600259859
    0xe0102030408250f060c0c0b0910061202010f0f02011112041101080c03070309140105010e0601021b0319020616232a120f03090f0102190201080c0c0601 67
    0x10282e80d02c0031030042c029940985aa5446003011084889584e800580d07203d441303441921881c0141c0602d40e080b600704007440d100c00001920002500d8000d16030303400104051445402200c0c00c03034032503810104e01103841c11101c80060307038422030752205030b0002c2ca004000c06120240aa0140000302080b0a000c0c0d80480c00800f6441c82c5808944502e015080a448a07090440151281300060316850803611007080094200c50180c1c2007075184900c540645461040c00c601c0a5003101d40c2a0000300702400d0480c06c0c4a455a410001c0c40401603046038030380036540f4014000780da1610701c1c1240d1007100043d10115420342d070f110401e80c0c0107a1110144241e1980b01403074082c1190000e1480698102da155202e1070761a0000aa81030420301c0c4000d2055000184842a10000bd0b4031a595940081d41d00ba00c800c10303a0702070101e2041c00800800071602d90391200e0800c400240c508400b10304640c010b420381105140b40141842c202c907020308100b02c1c90b8442e545460311030300c2000040d045620a4000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 600262356 1250 600261106 600261113
    0xe03040e0103050a03080105040c080402191a040905010b13140f04020a02060613060f1404020f070f0210050a0f030504081b0c091f15170c0a0801170a060207060e01020304 75
    0x300c0070b04c040e1107a07544c0449a81c80c2d408100c00c60391118001c800140c02c450028005041181421100e0205413010f10101c594a1820012054840c4064041004c001c14100421180748c012a40034082c01c0c0843c40c20015241c1c0c40450b145141c0c841c540308604030010301e0040b030701c56901d0607501001c0030300255500d188011010f591020b0503036099004507180c10304000160840d10503182540e50003000c28400d03d1400c4901011080040380c040d07403295081202c2202e24003040300420203640301d40644100c0000b14010403041c0d400824058091250800c4a040c0071680711403a41c8001e182814002990740360381c2884540c50081e0007010820b400841c2d000040c0c1c43c400910800200d80844140055580307480e40080a00700c003031703410b5020b80c1e0482410b20161100c2038800f1008501440c0c007500d61400301510001411003500c01c84d6101c20005640100303640d000411501400310210706022010b521854a9034030404004003802443d4081902d404010940c0c104022810750340b0001c0d0745a00f002e0a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 600263606 1250 600262356 600262363
    0xf060b0307020f07080616030b04020912070801060b0f071202100c0302041e03050c0603070c05120304020f0102011a100c06020a020c27060603041b0311041d030d0e03040e010305 78
    0xf240340c0814403654000140180d000290188561503101c0e01d0749071345510342029070241000494940d4020340a125208603525001e0074078900d10402e4000b480f41c1d42c40d225000c1e08407141c580018492030b004000d04284003180c1c008445480d50b00c0300c007509400d07599000c102d080c48041d0302413040803814101c40840e2103600d5000780058861001106a12a00020480d2455116484020440e4010035001c1c4642d2a00d0405180c3c008080c0c00c050010380c44603941e003070074400500c0c40f80c880c18070080140030075820034208070100400280020041100c80741140c0402c0c0c80e83c81000c902c20300400c3c054421103480362500fa0200c0e41c2c41001503440d010207900203925010040d0b2030328000e405001425500c91640441c80009119946402440d130310350105214659100401c00d0300c903c0d504c00e008030b03565070301207516000940c0600140320043d643c140c108400d441c0c40000354120f110960200302000c0901108848002840b94400500c502c0c040d02c048d8150700603a488800c904100d80000028400c011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 600264856 1250 600263606 600263623
    0x30c230604121d0d032010050f01060c150c020a0c08070303020f150a02032509030b090a050303130309080f030405090c04290418090611040b07060f060b030702 70
    0x203480344161001c208041d05201540c450f491030384090000307070358404280952058411400d00d00c031028001400281c3c01ea2521040310101d40180d0740c1c4008102e40c80041c0385c81c5038003502440c40c002d54404c0c240e072202610301350120814208a0703900c044c807954042c020440301d56030f2548903c2c0200c6071035a07100c20a84501700c0348016409070045103549a008200850019500c18007000031440d5502c0d0030b1404402908001c1c114503180c1c80c90600c0103641041840146420740c680e9540b1407100b411464044000e00c0301800d00349240e8482c2079900006000401a41c2d4400d00c400d80180e2000f4481c20308503000c84080e40311041c5401500c00c8600411000b200810648100b42d440520b40d071124195014036225522407810700b441d2419203e801400c0074400082070301c00031081300b03003040e440e40504500781000b443e0340036445a8644c10b0400700049406070182c0070100c030421a04052608ea4a00c506104098008000654400ca00480c0d4500d507480b0700054040e41c0700e0340382c07a8588910043e507605a02c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 600266106 1250 600264856 600264893
    0x180503030f0a09051504031202220807060905060d0b190311060403020f0d0218070e011d0a06122901110105360303090a0212010504030c230604 63
    0x341d40003403045002401a5010182e00900901301c0b002100c2c103010416030068012400c01c584611600d010070800e0029003801c2d130400031404043e031440c01100e070b00c001043e0f110748419085400d00b000001d402405c250100c8005944150b9034410130445407005141900e21541d004916101001c0521f540c1450423041c1d900c20081d04000540d2070b030402c0090301403807100175030002c4002820925400c040c03c072134079603e102421040c4400309070019540058070444a80001603040d0700d21090a6074403442490901c004400b005041c2959407001ca10000d00d11701441d000e0140f1102c21200310480e070342c4045250007400c00c0f490460141309441d0b40038188984509070018441c1c0b00100c5d00c003e4103100d0716024103802d500400b80354081080d8101c0c47c004600c14012100e0446006d1064600c043c4001c51049100d84040e00c441d2070380c0c3c8100f225508420b034401e07285a241c5401c100009800218565042c3c0e049501100e13411f120b0041103400c41c080404004050003280240310400c03210300f44140750781e03d2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 600267356 1250 600266106 600266131
    0x102130b0717040e0403050a2006190e031603050d0c0c02090604140f0601020a051c02011401060912111008060a0603140406020a140c0303010801150506091318050303 73
    0x44100d00d440b442e004601440c1d03016a03121000c28000790080008145410080c1407070148542800c404000c810510450002150011002c028122080da8403c40103121a02400c0050340905901e065480c0200c2031510405101002098203250081c02522a4051106014041c0f82c4861400a084c1c0407004000c901074528107012507420719090080c2000107401d07010315011031f5991070020b40503030310180545040d0b0041c07501132404540103024603c80d003204103160384891800b5540007800c503006181c0035040481c500c80148802940401741c101100c1e0300103c0d105405006090003a8083c142c2c0c1e0312698803181c0105240d011581000680b4410842111107012996507000309074140d9038000d4406003a0311811000030001003296000e403d600d600303868034140318000f41c40556036a904c82c03d200710031a803001c0010080c5d01e009015400403207071a801c65294103460100443d540c1d028001805109810300f2288a0495030b1aa0003002e03da02d030040c01900114403030400c95126481075504003007004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 600268606 1250 600267356 600267383
    0x40f0f0b040321020903100f1b03061401020106031a040c09021209010b0909070303050c0a05010c02030d0b04090c05092503090201020114070827011e0507022d0102130b07 75
    0xb0710a101741c9181400c0a8007a2001100d0440c48600070074109500c4c0c1001030b80c032550780b000c1c3d000000c00100c0b5240e4a440015006041224042c040f0801020450440e810300d50140005040c902c45509600d410070025407454485140002c1103d01c10b42003200315520118102189844019880d1700840c591070007040340307240d41824005495800c0311034908136440480104000303480359004150501400d000d40d11401001e580e00c40c296800042444010f0f8000305003280409a14800e0b03011609003240d0400901e26695101c2d00b0520307070340c0305041c8500c00382d200145001e03241c0c810010610f0441410b42c0d541c00070524000c1c0062070700c3d40303041e8015868100503e210081c80040e0600035a90342c0c841d00210307a00c4c0111090450003d06540281d14031000a07800081001d0007500254604a020070a5007a10390525808889006218034210f501c04c4640401d03c00c10560242c07485214080d03c4079001c01460042c40c06807040b074411244406a601000407022140009005c0300e91180e480300c0d2000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 600269856 1250 600268606 600268667
    0x9061c11180711070303050301120503090402120612010905100b0105070f0b0a200d020a02070306291f1d03030c0f010b060c070603050a0f020c0c01091706040f0f0b0403 74
    0xd84c50b500004010481c1040103200c0c1c101201010039600744204122071030000040b0100341030360040e100c60100c4190f9902070102e40c3c41c221107c2401d00d52008000c10406180341c8645070381e07911280342920255650380031070b40320380d200340226850316030006140e004c003400a10b000410b98404442e5403030400d1804140c0e071152076041407540700c1030201320255400c2070401c00103c0700a50020071110b00f9840b5400f000000981c003070081d81e050085865500345039080f40302e520100c101a100000c3d1080200b01c180300550780c510743c4910300d0000c0c5458240184140e191010114042080110b50306201c0803950050180700001c000860340200c10080c081d119445080c40060300a2071800050380c0c005000074052144250300060f446410b29501041240003880304004990105031140d65942001012101c0e558010450f0001422540b48555501c01d1058840d51110b50180004051815005400091203110000088810f030400b42452544c00d0070301d40035205a000c0a07030903060321000860f800c0e04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 600271106 1250 600269856 600269863
    0xd03110c01030c021e01061e030c1a0711220e1b0a0b030903090411210c0d0b03030c030a021e0601060f210f0209090609061c11180711 59
    0x43c0792074005144c800d0300f00c0d070f100c061035250a60070b4641e9035070380d5800122030f543c007104850141c2180110030501800c6050900081c00c1c240c108251900b001d1b0b0b90451000302c0b0380b0456a8050300300da00c29803841400c0002031443c614040a4040780303043e040c5c1c4000c0b4000705502030206214110116017201840f005030221340d01c0b03810b0340756602035505407080201241410055510400c0d45c0242c81c94550034200003011a02c0d001d18400e1441d4011030101003e08000045000e41d180b601c4540c12903290070b0180e04889c1c40f9420b802c0520540310502810700d910b0810903115081c0d01d52054988400040070000d54610b00071700208400242899400c801c2c5002150f107506990a556401605076050101941c40888190402c6014100314001d0502030071144211520356001507400b5030307076603803402c1000103004025222500c6a0001c80a010840d5552078504840300c00c0000e42e0203000d1940d0828100002d1280c0000b5004202d00c3c0d242162090f440a03401e11811a680344e400c00743d4142c4001683d07 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 600272356 1250 600271106 600271121
    0x9050606030f10120308071220070203010b0405071e0c03050d0c0e0d05010518070f0302042301030506010e13020f120f070f060e030d02030a0e0d020d03110c0103 71
    0x108800308102040003140c0a00c007081d400380181c40181051580c50950b001c500d20344c0c42e01900040e038044c003402200d03a4040940c904010300340c071042c41006114850000b02c0069540004c14035003001581000b192020340000401c000020001c028610304250060a109800c5030007100c408a81e2151072046406540045251034140e42d805080c200c0c851107400040800c21402000e1180b90b83c00039549640760b000700710240344905e001040908001030780842c1c0c0e501c01d9203c03001e075030442075082c0a1001143c8a203000c8070740441b00403410070184041c540080b07503607100c03584180d85104000304c140400015002d040340e0841c0901060340d40d40f0852203180b14510380d030096000403080d10104d454542124810721740090304d0161030412800035001031800c80c036a4082d584620000c00104269038020040030f05880050b4081c05c00349100d190029101d2050305d4446007403040070041a06c094460074009404d566015010070012201e03420060054072035045106054071510f150085103510a026410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 600273606 1250 600272356 600272359
    0x1902031812070c2c1f08010902061608131706010909080d270f0b06010e090103151d0303040605070302181e1815011403150109090213050901090506 65
    0x21283da0070207165228a01c01e031a042c000d000c00c80d401a0000d5010340441500032168509001c4081001d00d802400d040859840301a40342d142c00800805a02e07043d040340d06941000d203920215600742c1c42e0450f1180519885140354880e51440401c0400320b200034560028481400ca461981c4ea507070700e82c1c0a641542800400e5040f040c010046055801e40100c110255052484d00708011203981d048001d03804640151000740404203150107220000c0c3c030b90b94001e072003032030a99110b00106012541250041c40700800c80450030503e075920070342685c0700090305c044000b8030564048103809026070300c1d00b059400761513461a00380420221030191088031010010348503602c42c0004200c3c100310318212924a030802a1500141740c40f0160707224115681101c4001035214030a0500e803d800415401e40388402c0e050018545c409070388080020166580002640720201d1703e10302c580012103803020194403620b074071400428113050703203182c904000040d03035010794100c07a15070b903100c100f5000d80381c05071031a5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 600274856 1250 600273606 600273623
    0x306150c0206072618041a27010b0705010b1906050a170903070b0f04020307090c02160305100f0b060f2109010f1407020c0603190203181207 62
    0x1005040c41c0340540803070703030040402846007561203c0c089220700314424031641302c410000340303a24000c00f05801d8148400c02a05e0801c01044051091603c00d5001b4601c58407800c030b0749017414407008581040300c900d0411030f14110160f580d5008624130a801c81c080c00c54181d42010390016080c01d04440f4168905110b001c600d01d22842d2000644e2141d00c1600c00a041298015052240007a1105203d0042040c20011a0341d100c1506003400d50300400b8040344040703203c200601000d41c3d070005052040c0c40c0780340300000d640c0449180c243e140c400c01911680e100c049801000040c0302e0041181c0a615210540030702c804d40070481820101d40004a403e0f900c54000d00030f02006425544c06061085192409440003c00ba000c40c2c424414040300e2000c1503a448204c0303812400e08074011a030b80080e0b0f20405042c14101359401079112085c900c4030703c0c01800c011000078208904400006540d4485110841d036030708014031510158003040030040d0540c4901040e900d100b020620881d2082034005034030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 600276106 1250 600274856 600274877
    0x6090718050907090806011e0803030c2a0a0c0503010b062a01090c15030b1210050402030c04140105030d17150102010f0f02070c051504030f0606170d030615 69
    0x10001070010143c454070421403440004a502c4c041008054064180e80c0d03201d60b800c14660701d40c842c2020703241d0420200b9820501c1030202c112161340540c4c002e80c0c920fa480459103d498006120494881e668071401442134140100520524031002020781d80164000d0082c0801402807140c144074007100a1141100440740c50001006002141c032101205c00000c18a9001c6480e80310644c40160810017a076001e402c5081a00d1b0b406100740d030a801016503045800c02999504107850751030110704140780c5503c0c0d400107002c650b0f0074084950300b2580104108280719010f8800d0b800c51030b00340a024000d1160310806942580101c203000391140b40c4903050700f543d680c1c101ca100d110070350040055040d592586508440d11120f8000d030240340300d600c4001a2961111b0070600508050355101ea17020b41c1d580382c0c1200d03492f4016000ca0301501c2d0005400c03c032305d240c0c918008000b040241e02040d0072a52011600285400c00304000012034202d0740c090001036154903406203c944108006008604040b09 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 600277356 1250 600276106 600276109
    0xd02090d061b020c0f190506040b0a0806010c1a060a170a020a0504090c1712310303020c060a050705071202010f0305061c080d110d06060207030b06091b120609071805 73
    0x40300e240e420701521046c0051542c90000c90b4054000d604121003216010441184580d4000c82c015800700c002d01e4120364059503501c550a030462000c1d90352603544a05d0340064050b46584e40320030024000f0300341611416280d525040c3d20303444518012885200701c0c00340090b0301c0c80c042c02400c40c0981c102500303403001c51078202c020016811100000141c1c0c0103080c0303200541d408903c058550002c844108600b4544002002c801007468404410550b00041030103002081e0300141030701002c0700030340e43e407036407201d400c181590b041c0030700c0740c4c0180144901440070801021446908800d18401e880b08540b5402020095080e50800c4407910f800c1152040310851034161203491718940340c020800245400c140a0003101998003410250800d075100180544818400d4419040200410f1018110450441d550f003030317007014054600c030f21804820004c9601003010451700944400e524007000e59500140700313a01c441c01811140c603845070200f0800100c0a6001e0780000701034899400080c0d200505020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 600278606 1250 600277356 600277369
    0x606070c08160512030a080f090a060609060503011811010311121303020c10020c061e070303050f130302060402151303110910050112020d02090d061b020c0f 69
    0x2605840440c42940002035012051080c00c184070240c41141d401d503420001804001c019148072112550b0040007405207440d404a11550440107404466602d034684003481460300d042401d0142c03010786040400207802d4829403150003110360580007800ba810010082d245600303403403c0c02501556151001c0c15031588039611510818185103083c070f041c0819400e0600b00740004461243c1680e03c0310017494240350701000340f039184000845420701c0c0c07481080340082d01c4a030a03481490240c2000704034804d1780c2c104042000841101c1080030740c0c0301c07526070400a01030581074480c2110f00084d140429040c442900c00d581080d50590005c01090f101e82c1d0912a80b920000c103032500464091080d0003009160641d407600550051920051090b071290400030001c030058450301488407116001c220701d0340c101c80016820480d400d001612051805080b01c0a031240f00c14550344840400d01d03060400480303030300400c4181040050a40360164829042ea42c954071007400a81c040343e0030700c4100c2d551901c103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 600279856 1250 600278606 600278617
    0x307090c09170109021809070509061f051e0f1210030c06020c040f020a2a1e031e05090f031204031a1e01090903271a030f0606 56
    0x5140140d411607455a400105119040740150b869464034110380552410340151103c003075007103c1644240c01c001366644d5444100f407107001d0045000704000380d00355507944414140c00044500007241070407603580c024100d0b4401d400505076001c1400c540c1000a442c10151030301d80e150404240c0c680b010341f02d8030801c0c1c444001c21380c02d05103c1d510780102c0040c03444032074100100000d80040600507503c8003008140c078600340d8903d083c6441031240007030035a4402c1c981e100380e154100900c9884403800c10345440700d42000f54040c00103485250761005600d2010034059103640255600851020b060002d541e00065030414080050340600155000e4504449640710a0600038100c4401034041600c449103a00240e2040d070780340340103148940e80041c40103442c03540051000f01c9403100000204038204403075018022850b0455440001d00e0806001e0130560409442442c2d00c0304400c410540c105c0352042e10741c003900401c0c428042c100000c070703003190058034068400d241403c6199a6141c1c140905600304 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 600281106 1250 600279856 600279881
    0x1104020c07090b10030209030312180118020a09050f0610180308040515070c0603020703030605030f0601090f0e0a0f050a0c09020d11030702060430021c020705030709 73
    0x800403950034003810401d8400500c144a4003040c440010030070044501c510000000c00e060040190812950700030084a142c0b04031621082c1e81601c602d0300c031920318410010750060946ca0b01c85041c012240b103c40e9011264421a00400116140d44a070400e417403080d1100106041e8210220740b1600d003844010002c1c3c1c4081c940701e0032130380740244020f50a114035482626140c10008050125040c501035a144080c3c003039643da484c1485503580e01c02c114080d44109800c01d58041000c508240c802e030803110042c040241124004c8100040c1c1135100e040a100b0718601c0e516020100e41001070701d000d01400002c40c40042c20840d500f60307c810041440501d4101c4c1c05000d140d00140000e400d90b9024006040d0100300103882c1c4020503510801c032041c52150058145082c402c20070000da0000701c82e0f17070195201c02441d660a140313a4a40700c00c0c101201c2700c108601109001c81440320380c0000d98001e41145540803400d40c40105000b646c90fa01035001d00c030340641100c0422b06c08094030f0380024407413908 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 600282356 1250 600281106 600281111
    0x102100b0f0409030503090f030a0f14040f0308091305070207060c0206040905010609030510060b0a0e4c0e210a031e08060906150c0a0c05090f090304031104 69
    0x1000002011502002412130109001000740a49603c0c00c00200c0d461860082c010352034903941c0d4a000c2d00031543c801550042009002400303807590510000e0720004c000681900c85007540f40d180140164012001315800740300c181052010b0312095006003401400c2c660060b10060f400c10008561030b8000004c20380c1c014808100004480c003842c4580c1d0b0003018640d40d9034002c039045103000c604101c00c100d9441941400c2c0340c4c051102c1e4003104100d03a0f000c0d0b00c0742040000102d010300800d0340185901c80c141c98200c5100d030007038a003a041400b640549104007401111511303a0341c80c600b80040303c0700c0d01240000d40034404c04005080064a441d1001c00c803054040d1203040b040c9140349000329041c2c04400066400c42540c207940c1c0980381c0c6d4441c041d02c13400c02ca8180d24001c0049102c84030004e20480c402d098039548050031046c104110307803003c1038440548110075060b0031b1403030044110388502c60052440f080010500108100d4140c09503040030091441d180c90f5450780c1030a0254240c04981c05607 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 600283606 1250 600282356 600282379
    0xc08150d060e1006080d05120a0b01030e0d05092106041e0b0c090405010b0306010c17070b011205062a0a0e061201080c03010c170901140a09021005090102100b 70
    0xb41c0802501c60701c0300e86890045415400c01400b2400c1402d0741d41950184141813200944036203803286207580c0002003010001c0c202c0c0c05a00103c002e00584508940304c0d0255200c00103a06a108008103485041600d808080d1101401c103626164075500103171806403c1200841d0014108403011b03141c0b90500812044001e0090301d60060000e019203000d02d4040c030010f400c44581c1004e000e01070042c0290381c1b82501314038018002030454940140300504103000807042d24495a5440140d40e081608144000540d607158409080c03c524481c3d000d850b944501400500d85060207240000c2001042602524001400c0b104801b150810280c42042c0481200c00001c1c9413a404040c1c01c5045a1280000355549420721407420548041103440c0282d040c40c8440c5503c3c0d81040390700154811104030071150356180072060303004000c810060f62030305810300148000e002c400d8224028981c0216070403440b0010010701911a48952013610340540c014240007a010282640001a00c40d4050410b0038000c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 600284856 1250 600283606 600283631
    0xd051011090928090201020a0f14070b090a0e06030a0305030a060302060a0807030b0102011a06030a1503050f0f07030b061e0306070504090506030c220207080409060303030c08150d06 80
    0x155002c0300c0d0f28500584862510b000c0c006000a00441c108118000304002201c58000035110341981001410359050241c0d140c00b04810b80540c3c41035020724800707407030009449240e1007032140c0c004840741d445003030740803004129114404074a501a120041c000c00b4005083c0d64141c1d125000103145413207065641d003001015884d040c0083c07008005070f5407800715a2a000c500541110411400d80341168549016901405116a40b0140b6020100c404a40b00d5455540100180420420401c0c0c900b042402c00030801c0030004d90b9040504005080d2500c24030401c100e01d50f50f107014070000e402e5400c030701b000ca0242d040c02c00359044000c2d030703c0740c1802111001101007403a140055802d2400120006000c0002c2c0d60644501904000c2c02c4020b00303806c006110010760450150030341034001d49030084081801010350b9048401d00303980310300e80c2500c0e10355504407440140960301c410303400700b4142a141c9202510540003240300d52909529a01c4000440c0140100c3c2001c3d2801190315659515424845 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 600286106 1250 600284856 600284869
    0xa05091005131b030903030e0a0b06040b040f09030c0c0816050616020d0c0512070b12130b090a060e01020a0c03050d1107060b120a150506061204110108060d05101109 73
    0x180c00075440100702c5c000c891800800725202d094030051242c21600180b40021100140c81d41c0145c0700b1036001c02e45a00c001d001400900d440325074519260324005281c0101604010640150342c0940ea00756071880e03072a044a0788416190010b4800c0c07403182101400300c4e181c410007400c040402940d422040d42c0755a404900d178034040810586a007440e00c07104000620302200c9800058a50401800480e0700e0f0070b070002000d000d00042c00c040a00840c00203142544c8420048006a4200040c01140d0900c10905612140e402c4800c1e503d6501b00740000300a08414000c44114949658400b40b003103c440d2001c0307415403c55800800c800c0d03103e0200024044010340a8140d040c0030702c5d40012641401c17410001d80503124401c4c00142d4001e4083c2501281c243c071204402c3c1c054141c000300c0c4d60764916001500c18402d5200000f0381000d101c041c00240440000301c03c0001d50300b81ca641442d86c98032402c100b08029100d40050295000402d0312809440c142c0004403041308410545046c000c0e03400000d80f0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 600287356 1250 600286106 600286151
    0x40608071209052508030c19020d080d0905060a050601080a270c0e0702070f031b15120b01050c120d090c0312030b06031905090c041a0a0509100513 65
    0x113141c01c0003c2a00c5451824507441c200400700c9500440c07400c14a100b81359217a00c0074290022080404600b00f100359143e615050302016444010366940f82c0c4441c210300c000340300495058a42c1d00c100000901c54031001e100c6e00303014000c1611201c0b0560b0b50f440191000c2d11420b448805c00c90200e6801c240075000300c0b41d0030403403a4800c2d45c07a02c0c0020304060202044c590001c2c694021540005002c02c50900e8200080c015039800400b080034480751602c00340649102503110714089850082030a65156204406620310903c02805010500d80382004450a0091510300c42c100c3c0c0202e8140380b00b0a080300b00a012404401802240028140d100e2400340c61041c0e005039001c1708011150720800c0c4d407501c1042031500b400c480890460900c0e20081141c0000c40a00d03e210654540c0411907580d030403c003519600000500601c815080604c43c04e54070210031004c280038800007940450207103402811984140040070512000602d054204280701b0b404040002d142c6680b030366071031450700401c09001c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 600288606 1250 600287356 600287383
    0x2070e09030a022a0d060b06040e04260306190e010b03090d02070b18011b050f010609020705031806041e18140604020d06050904050708060c04060807120905 69
    0x5071910403104002e820070303142015041c136803410094088a500b00100300d0340c003030240546240c1035140c01e81c40c02c08010088100c809034050030200d000034041c200c500007035200728030418a0b101c407c255080c1010092541c2031840034904d006100254403424004045140844130031038072116603550308440d89102c6c10a030014000320100108018a02104200340c20200d546440149203003490002c1c400440d005032500d1040c5028036940d40c240c0e80c1e108200147c002055151b95544450440c40d002c1d5480c55a003040604550900f01c001500f00303031a01c259468a40c104020303601c0c0007a66a0040d1040c1c11a03402d07243e01810501011458154005c044515000c0c1d44040c00441400c1429102403491190040303c0383c0e90400c000311000a42c82503455030040c00a440c0503840700540503908029103095049540c209210070704000c140400012a40200c58040c0107840003130b1100b604101051099008000110f0000c1005c90951481914014488960b030340000607203161651f14241403000b0070f103402 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 600289856 1250 600288606 600288613
    0x90b040f06060608041a0a0e0615040501050607021e041b020606090c0712140c030c0303011404060f060c02130603050a050d02030a020c0114091203030103030e030d050f0a02070e09 79
    0x84007005450312030030016050a040410003460b05a8980f80e5000c942d2403e280c2c5503010002149411816410000315a0100029a0241e24000c00d20100480141300310a2259040030000542e0341402000ca0303107465000b81a01103400e0340808020900e0740340981641e00031756190310384060342c103000c50a182c10125541c041c0c0342c681041001c02c108450041c101072084881004420001051b0604a00c5185954140304020160000c0103003064040d040c0c6029440c0800500401d8210700480114180d51042070701d00728015010051000300c801078001c10424201c00d12003032042e6030013403404c10b40b81807006040c0310440c0010200c01081e2030f03003948120313065880000c01070704020042c4101d60040c074407480118142244038400940c2c40c4100301320b00e41881a25448000c50003042d41c1110042d49004e8a00c10200003980c91550f543e84c024401600003a800082e141e20030b15000c85c1c414441c8520390b50300b6042080c203009403407555000b0602c0341d05500c034891000038503e82c80c21055101c0c81010024 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 600291106 1250 600289856 600289883
    0x914060f04171c0905070806011203030f02070519060204090219030b010e0a12030509090c03071b020321070209010b1b0c1c0c0f080705010f030b030d12090b04 70
    0x1c1c2c850501c0c10058008002803050841c00c02c885a4800c9002c80f0300c1d00003203143d58072420a030303040c000c80d50400c5010340104000403541014150013000018820341c1c0401c608440100b007802203004985008060390002c0360100b002c0c5210100803c8247e004007001450b01d80d4a4140d50101e901c4514241d8101ea040c02d0029400e41c0c05110701d13141483d0a0070510300485091001420f0009680140c559040001a41d1828544603100f030300d08101014001e4030880c204003a040f442c507002159020300081e003001c00840b03c56044019121810b50107001044a105148000c102000300f6940c0c001d0740d0602402188090391341c11751424001c0100100b620b5661002405005009030701c88400000782d03000380c240d1280ca032201c5d1000b0703011182c6401c00c0c00700b4000901c3c1810401d8034540c4507030748482d440800856485004500c02048a00c240c030b03042c55490480c00280d0a0301c0c1801d5030300d0340c0b40d0044c01d222104030b4010710043c82c1800c00c1c0c2d000040d1715001a135800580c1e2500396400c1d5030340840d01c80e2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 600292356 1250 600291106 600291113
    0xc0d020a0f030c0e010c02090a0603080c031b0f070e060402161b051203040302100203070c061119210908070303030f060503030405030a080a030f0509060601141c0914060f04 76
    0x400c400d1880d00c2ca026204c054079000060082007030120024000d202440004807035084680c0100d010b03540c4044000d03504c40a81c0e403441e9a0750040c42184207a40701c2c00030003400b48500050503100c50700c120700c040d0603464a4002840c603c030800825241c1c0090b020020502c02c0241e800051020511804d104213a2000b008491804c000d000d0300100d00070324400c03200004800303000069804880c1c0c1195241c0c0003c010440403400c6004459004001d400480c00105045800c4000040242c0c40c070404c82d040319185813441044821094405448840c4180007442c0c1c8500c1c05924000b00b548500b40f02030380681c0c0e1111035107407901c154000d90001c1da6400c7d504420203a9805108000d1404030300660803e030500002a45503051a000189009400030b8001817142c0640c000c90010405400100410b25221401a45a00301250150300088510b2046000c812011054608402d0044a004120511035401c5001001025419038180351447c1c031050b00700c04100604e030710a030005440d00709541000e10713 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 600293606 1250 600292356 600292361
    0x1e0c0a0309061107090b030c04050f090c01050f090f011107080c190302100c0f121215060914060c2d010204081023010303110f0a0f0b0c0d020a0f03 65
    0x40100c010400345400034501d40c3c0340010988103855049170000b07540c0426100080c94007034421086900141400d04100740c080c01d424210303100b0702150050303504494060004483c0d620481d59502172845090202c803015041800c2410801d46043c141400ea688040460b04c0c5441884d5110308000c0d07116203180543c5040440c0641740d505107407448400058111340c0052172548580b2200007c03c151400540c05200500d00b034904442e40050108003030403642c140092801000c0d0040d070a07501d0810b502d110010135682c01c034404880f0303150398062440f4241016803204404814110b0f900080521000907155400e0082503044400c2c4031510031002c0c0c800101400725a200c6041c0210359105200810026002060307482d014042139000080300ca10740350341c81480112204071456140c41800004c8201070b0403001406a00c0d07807040407101c01e418140d02c1c955581c000c0d071100401811071350411000041c900d00e1241e4004d0f008807002d9040a40100c103138412078000080c110001004144c48070f20254040c03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 600294856 1250 600293606 600293609
    0x3140717090628020c030f10051306020a020d030c08190b0301020903010203150109060203040e0a09030512190510030f1506050d03020c040606080f041112120403060c030c0804081e0c0a0309 83
    0x3600030305546080f800b107c07500c440000007000c070440e4443d00095038090354401d4032100c20350f00203c210f49912004900a60b03c6000011007000b103458820480031a5004200340c07441400d403c544101c0007030003884d42c40082c1000392401c6806640a2001c4000e60341c0038005036200c0c5109402d42c4c00344083e0301000601c40110380c2d21030010b542040105000c0041012100c0c4d9110b140750b44d0100d4098032502d81100d184c4201c860703490074206a00c09100f40c000071b2103c1c94030b03007420041e0140519190712440c2013640080c0d101c02402881c3d0700031003000040c13200c05040b0740c3c106c0c022000200c155480300450b02d80c0b40600307012001a0880000000381c0c0c600ba102d464007601c0c50f864001103510b4144194055500050300217801002c0401c2c52040682d1070454542071440158140c4034403000308a8242c6c22900309000c101c0d141d40c04c1102c41c0402a10910581d0a5501180d65451640e101c42d12460032680c090a070790140403140380d54000900480200400c88184050300a100f030700d04c181801060901c55 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 600296106 1250 600294856 600294859
    0x180a0b090705040608040f020a08010b03010b010203211807080d021005040209040807060618150e0403020c0d0503040b1902011b081602070503010e030703140717090628020c 76
    0x50398188a000c40e441000c0c0c1c2c09a91840c1083c1000b0b842e40d00385200140c210100080d0f01c4250413001041d0f10703206401074600d49000354001d1084030200f01c01a038590040c49290021900c080264035aa100d9584c0e015410001c040440e42c00031407011606400d040701d581011460340e000e0031009000c590b04014070386120940c44c80030002420650f0024100800c0940042c04192021a40c0300a10031541e02550045c02c06070304281d80c0350a40c14105001d0054001c442c401707409130342800114020f480140e14421903169000d000665089820002c1d070520901c400e803880d00c0f0610020aa501285c8000c00d1542007070950b0b00310004006070300a003504d0b03a00b1060002e900c07403056140d0b403643c1c0000100e5044081c9074051a02c0d00700c241412480c00c10650300c03069240d0b08017928905040d10100c0240f414074040d035a03079108a008054091024440c802d0000c00007107000c5100e000b203c0e01c0101520415400070003040c50a00d451035450303101c51400c1d501d0108100340f02d007140c100640400a1000c070440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 600297356 1250 600296106 600296119
    0x8010b0909070c021815010f021203060114040902040f0906080a021305091510030303050f010608060105070f0203060a0501051201061404051503120a020705011d0f0f180a0b 76
    0x10402041c0c800401518002c1404624000f02c0110350f1240700d0508203042840c007041c82c900d403030040103d00030480e104641c04a00d0780140c0385e100500c00315145003c000d81400c1c044c55a121140115201901004c22028448003880041813050b603d0005000074803801000d44081801e150180044407010f45c400c0d000c42d4807101c2c0031001030300e40e07a8440316110000f601c0000d280d030b9481051418104075001031105002c24108201e040301c540442e0b8020b0306e00075981046582c1e01c0c86d46040d0301003820b0085101144d0000e002521544c400e00091403142c1c81950400c4030b40d0240d03030201c1d18141099401c021070329150801807146003001000c04004c03210480c000e01003a4504040c940300c0003840341d240790107561544001190000307150300441c4a8080074084490004100744004825001404000010700a2400004107907100d0550760035901d07650305007004418030005c00c1044010341d103822240c000c51003484090542d40c0303034503003580d45000060030140640f80c00d0001004803181c80c035a8511608 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 600298606 1250 600297356 600297367
    0x60f0b0f090a0c110d030e100902150307120c051804051303030e01022b050f0f16090b03010f030b0903030c030612120304080a030b1f0f090305010c050a08010b 70
    0x181c5501d000750708550309110001d03410400107403c0318203603880c3c80c2e03e140341c0c40303603000c4c0d10580e952640c0f0036039031490018192800f15503403410820a5645154010794800541d400030306540030f40800460700b004c000e043c6001d44100e001100401c2d40c04a040c020702007240030410b0814804444401c01f5030000460b000c0100340780255544000c080d11400113420103035146035003100701d0000d50417a218114111091a415240c440c0f80043c1d20303040c2c504a1611320304000200301141ca001820074000c4e5441e0a044a50f5990611101c14101c941507021042008200002407010740b0000258060b288582c1704540d1507003507050181042d0809003045600e58001c104118070040c59100b900d4101604440001c9004003030b50000d45801130f040c48100c0980310002c00c0c00f0400c60844000d110711b41e62070310184505290901003080c200c0b4201e8848072440c421900707c4000d0362103002c0410203000a8100724501503200d4440d1400c40b40714940142c0803610001d0f80e50001c94000c02031030f00420070040400d1510 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 600299856 1250 600298606 600298609
    0x90f041e020a0e011805040804140a0e3402030703030b0619050409110f09040b010203071b0510030b0d020402030601020a0b1311060a0203190302070b040b1b0903030909130c03060f0b0f 81
    0x70b00c85d900c1074501c03138034008a18006070358807082e800c0300400524544991904003060b2282402020010f4400c480c80c00081e00300541406c258085012122033b00a9800c00c515510207034068980c4242d8294001030030400498070150707012003e0501c601075522640c9480c2400302e0349040f2a40342c010300c2041c04050009000110002e812101920000c1c1c8001c41d200d0307203140050b85503004461008018541007014038480f00944070402c0c0481c3c42c2101c4a0407000c0304540b0650440340240001030b082400070100c0009420a83c000b03503006041032048440703551894a4a0f20307560803d40300f502c441881001040180010300710782c0c0d1070090f000c5445619058528034013a64034441c070403d01d03d250428043d480c00841c0254162610b040c0c01c80d070200e40c035140920701000c1c4500221a1030f40142889107000340b0a05100c82503030075922001e001985024183c108028461000a14011107941c0c0e13054480b000400c5502508000e51069002051010b995543e40c8180c4610f40403681c01401d070442058820b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 600301106 1250 600299856 600299873
    0x545010209031e031209010f060b03010605030f091c02011d0d1b05010b15091e0d080705011d030a030507080403080703050a2a0e090f041e020a0e01180504 68
    0x2c000784404244401c1c11903807100b815801172128040403800000204508028103401290380080721460400556444d6441242070b800300f0300a5000041c03061000408012044242c25000b0702c80004580360802040000325218000032031050050351110390b4509441b15000600c0c411803190009040340810380f1030020108200038244960700c040c45d01100702808400c1d4891800c00d4000750040401c0d0300e8a50340170000307520104880d400341949000c132130185400f0000c1d007c10a80c0040204d44080720907212078209801001c0291199580e918903024000c6120501030444080c0340003842e104d195041c009021213000500e10014000e10b1400c000000342e006200540c0659641000a030540310904228004e1043c1d00ea115040c81101c3c2103d552210569411002d00030705503280c0a2910a940030300294039026243c40008122600c04a0001003039030343c4406900300c10b030040384405011900007a260200da0f034000c0e03c40e034a2440040c4805008282051750f1404c200105000d1818170303a0701c6400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 600302356 1250 600301106 600301123
    0x105060904030503041e080a1e0212070c090624081506030a1b050d0608010209060d020a020a060203040c06030513110f03160b0a020d0f050d054501020903 68
    0x10880c00000290800140c03400010154000714035a124403030a902c0d1100c1180d00584020021841c0f008271924110308001c100210fa07112a8094070362044150981c2c20b25410841048401c1b840300440851241d03410320400d0300429007604107000320028249500c4d03401d003166880c0400c2282400800c03200a01c0e46440c00c1042e002a240f1664070754800710703a500104103036403006854000e107540140705a5400409841a8610b13201c0401200387da5480303044c202d10038003880c0758028100340044280324034180e010b008402c034940142d940805042d918641203038011141103600f08045541030140d40e6052113441e9200b11048140484d807120360f00e40c008024607060005110f940310010b8144240c9041c09100502c04080c4070308005d0b5600d581c0c075003e06802c081c4083d0018410a0b140045842c0b050260500a07082929040e1404800203540e00c06080004c3c040c6d44c1e4140b43c490905c28200b804101002c00060000300e41c484526841c14450481018030040800c80e0f0050184144640d408200b514 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 600303606 1250 600302356 600302363
    0x121b040b040501121112070e03192a03060c14030112020409111003020d11130b0d02040b0f03040201020c0a0f050f0301090804081f02071a100e0709090e0105060904 72
    0x1602404601300d030300a030900a071020040b800204130b071060040b240d9003540c0602019200e080305108a1001e0554566500709040d40034525043d28401146d0a0b107805104101c2070300e98151400c541d03500030300402c00e03280d1003202d07081e94590b140d403e400d92101d501c03929080c03c2074034245035500d40344212125848081c07000c2c2c032071039403a015401000249002d41c87c0800c4c001c0d10039140c019050300090025000301071114101810480303444c0c51805c52074121958515200300c2000c04600b17203c09402150131204800c0307000d0742e08110207d092010324010740024510400d03116a02c0c17515100080c18044408180360040c0b03411a130034046031180a00c10785c01e440f010b03118200c0c0700b040000040c0c090f2503001d0020300102000903001c105140086989a100180f15622414054420014204a1140c044050f004000b24004000700c2031741c925150381c01402d060809941c0c640c80703503101c1d84610800e9400f607010411125080054000074001c541c3d9102c43c503c0204154685140800c030080f2000308002c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 600304856 1250 600303606 600303617
    0x60e1f02041512093e0306240d081902010501080d1407021906110a0803040605090a02181506040807030f0213050906011406161214121b040b040501 65
    0xe142c40f590507400050300a070042c995022070b0010005010300200303d0100d541485207480324804441544104030085101c000c4d0041c5055038480c1044000b06c001c007010415281a020f50203150369039411003101c8041d0094030040d03614040c015040c0c2d0054107041e650740640e4145401013051210105802e50342c0060f9003440403041000641c1103983d4031486ca07000b9800044240c040c41444144149402a0303142c94480910a0322030b07c5e0003d035502c4d88500003c14041c2c007080001c0004d02250009904200c820f400c44e6280d84d4107a00051f9902c9508001e03c0e01180902c003048000903800c002c1e45200d40d01038644902e02400d08928540303c11072030001400320500801c0141c01c5498004500d4103260075440104810b003000d010403900c0c0c080038070424030164030718092811030f442d0001c21690b2680b82c007603e80c0b80510181c1e03612071095510840c4041400a000c151040700015100141064525448800c4151071311120384820540035003072031031800205120501c038048250b81260251402401c00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 600306106 1250 600304856 600304877
    0xf051e1f080307232b0903021806030d1412070c02061308070603230903131e090203040b180a08180a1e120f060e1f020415 54
    0x900c0404085903001e41424400064010305114906aa410210000e40440300400c08401109a0380704032203002c0001c00b80d0510160358140d520466400714001e01c506011a40d5a0750f81c0000c0c01c1560200100b480e0607411204114041c5070502c4407244880150403c44c051178002103048096001d02441d08220188060225840902030424521403560040081e641c0e25005105001500c2c0b940c4107039052481404000304000380640200c1089044d0510601400100b04505a0b441d090241010900340010130040c1002c4d194070041101410018580045003020354a004904d04895030101855038810720507c8001401417045a400c42c29280119000f04800d02d03886040058400740100044000201d2000c501c0440c904e407840114100c0d0402d60b503560b281e00b00714078003113035111900f9a50103200303003403004050316510315002c0c0b0300a403d109040314181d95400c00300c4482c005006c4580d40107084040141c1411400300b01442c0031501c042d0b06080c030300101c443c00c0d045002200b10a00200b07400 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 600307356 1250 600306106 600306151
    0xd0b01052b0b060720031c05090406090e01020a020709090503091002070806240d0201020303130816030e1e1f0c051203010512010519050414010905010f051e 69
    0x1044184601c020241c5566110728a4005541c841c800102400c190100175034085078039000c5150035180c4c1c1d2148499040d00360400742103c03a940101a0341d64071907074807032002c1001d400c02d218030b10b4590820b00006941d0b01131072801915000f403a610052300da500302140c1000041c0080706803459481c0954071a40390a040c150260300b8070b407181d041242580318030400c11080c0e4513604c3c00ca00d03120108ad0700440c5c0c00084081408140c3c1d02180340607000d41c0c001c101241c410020a04899100c170300501d499810f0004002901e07142d16001c60068001819000e10700e0f04924040e51401c0540355051a10106142207038003103062005c01c90400281c4000124003d180780e4001e11600c6411548142903d80010740841c00202070340082c0280c3e030040007000301407d03c0200502c02d003030207070400c0680203900103a04100c401c0500710003001242d4450540000301c0e03940c00d0034001d21001341e200304004240c0c03005440003082119002083e1103900280a02c00194100e281e0364219041003100a840b80d00b50310600c1e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 600308606 1250 600307356 600307361
    0x50f090103020d06500405210405031005010509010f120303020315040504030906020709111603030209191d04030c020f01020f0d0809150601020706031a10050d0b01052b 74
    0x1c1d02d10030091054072500c00750311485c2c40c0110411044007800300d0030f501d03080b1015280c404030ba00415503401204101010001720503584414009071003204d15054448010a04284090904000722600e81005011519000b03035100d01404003008250b110614003084441c405075802005000d155001020815140700619081c03000040070b4020321050510f440c004203041c06038803d40340140100000456004198002e079401c808407100300078241901c10102001c400c0240c1003c4040c103601308180f4080e606e9507100310721f501c00c43d0341040090310700e0309502e1200400d40749100000110300100b0000002d401c401940c14054050f121400e40510000042c0d00d002d0140500e0200f40c811480d400007015400f0324018803900a4209940000300b00b1080f245103c8000d40e010760240e0030154052010350310962000034100800515500103440d8130b004188500302003901200010342c000b48204c0707060f40502414651030340a203004ea03d4003241d90030791000c8402c05148110450300041c04c0100e0303400e094 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 600309856 1250 600308606 600308651
    0x9030602070b0f072f030909091e0c0901180e070902070201110d1b1a0109020c0c0a0506040b1608042c0106050a080403020f0a0c050f090103020d06 65
    0x20011503649180e400c09107001d103000c48000512807000400551080c0c4503100a07441d0407940d10000895241040603803400d1443c46004030070601c014807a0610b80e5541d020290b0148030010050308015402102c10700120301e40e5a90000c443d0700c0080010910344075030ba14a4111409680826880000d04a2002c0070344901184454544225440402c42e514240d0003400c00d0780c400d80b13038051564180c0725455200c5800800c6d03500131441d000e90000d41c90800116510f41c452054912041414490540722455582a0006000d050703004c10a0141d41c00c00b0070458440d0300007261040c1210340741c880043c0c541e01c0f46004000d118074000c036440001c000441b210310000c9038810002900c40da2180f0700e00d00900d0145070385803c0b040001003090b82240d0071b201c82c141030f242c1941d545840c14031094403d0b40c60300f02c013401c100c00b1032042100014400406100910400f0310900c14100c206103081d0400003280c0b42005610700c101010801000181d81d0302c0d45000c2c00546c41000801c014950b41011130104080 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 600311106 1250 600309856 600309863
    0x50901051801110f03130e09070506031b0c060103110306040c1802040807090f060e01031509080415080103050f070b0301031b030b0106030b091008030913150306022d0f0a0903 77
    0x1c41898072a200070110181840d2006c080580380c405035520b02032042144240c1c0c0d00c0c003060b00009800d21441c24220019584102c2c1101d0b001200070b0600901d4a840e0700040c03001000d90002e500510410150380002552101c01324010107080c00c00f5116841401c0d04c0e480364040302302107004009250406901524010104441903950031a43c51070754102600a0f064800700c81490704001007405070080c1c840c1e6041c0c0f40c10030481041100c80c41c3e00c0b40c1c0103024947d41139414440910001900200828200c00d418039150b940e103200c0c0d45140b070b089280555054004c0090380100c40305115404c42c05041c0c0341101d0f00520301d110348285405506008441c03a41000c0d06926111002041103034141d0031032050113200f5036040d052561000412400c8100c6030040c005250410040c5034a0f62402c101d1950804103041d01c0003e02804288070310540d180c241d8412980d10b50003140140c01000311103808907885a200401481420884e51058000d10a1400c419080207001c81d1441c100d40c483c500c01030180d5803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 600312356 1250 600311106 600311113
    0xa0917040e01050405060409030c0f020607080a020109170a0c03120603050d090f0f0b040311030c03010204080c180f07050304030e03063301051c0b0d1101020d05090105180111 77
    0xc807100400316645003406400d0085013002d0201d42c05042510404000b29015680c141410320541e40c0c0040c0c0000503407042c0d80c0100c0034015080803d0154004025410b03c80e000041c0300c14407880d00c14209c85000e4403409103c0d0062000036001d40d08040000726440d030500d8000d8008800c1a2020000d03e415040546544600c4000042e196005800c08064401400fa03811a8903aa1113240c84103110700d00801c4801d8505010400019810916001e140c000040c203a401300c0d500c442c0802d08a03001a4090007407a84020019006420030070b201c1800c0681ea42c0301e60304685400d684952034032001034095010068000f0015040c144103c410080c0c040b801010b50b03e480c1002040100d0349220b807480710340f0302c134056041e0043e5540c58000806420b031042c3c640c3c905201c41013661600c2001c103503040400f45600d50306054080ea44040070202090301c1a20180c08051041000a141515481c0d011090100c03c01103500b051780c01509403900420034400211010810200403a80301ca55010180218403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 600313606 1250 600312356 600312359
    0x1090b01080705012706050702030a0f08031e010f031b03212606210102030126071809140f010501140301090c09050c04030b010816060c05060a091704 66
    0x11000c1842e008440c4240e176800000d081202d60780e07034903216403080000e04040c141c508100047c000c90181003d940020144d8900c80b03400d0715045600c0c0e440440484403420008104a03d0520400361035001c0710082c2c91416141d0b0406540c1c92142c8418000a080340710003035064610b4801d00052140134690140400030004014160601c43d0501e01324900d000c5030020784081c1d07500400c442c01c07030401581044036001e80c1c1c8440040c0072050b0740f2880303010080340f110035503180070304c03400d000860007012441596280d8406510240d0080204003000004540082408212a110300120300001104c00d40c4e00040491103450803d801d0780401040d03045500890040046000d010341c070035412540a8170f00e000640c440d0320209402c86030141c00003006000c81113800d1041c0c4a80c0e038486030b030012144402078502a141d07100c100001c1007d034403040d815400101135410b000701c2207140300300030100c0341070140405000e0742e80c0c161140c90050484070610b82c2c40003280244070080b030f80702c000c1c3d400b240c0610b559503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 600314856 1250 600313606 600313619
    0xc0b13090506120a020907031d0709140912181503040b0603240415020f0703090e040308010b0c1c0905150c0607231b010c11060c0c01090b01 62
    0x1014a4411450010301c1d040c00500d00d41040c4654200c1440e06001401c2c007180558200074a4060240515003059640c401c04041c0d00183e08040c0840300d41203004001c01403900340d12000384c90546a00070308000c040b406224030000c0000318281c0900760410781c25140e104404d00384110b43c441f036405540c820101024108401040c0c00210f0045001d411a1009a5a02018141d0f508010300c6068000404d0828082e240481c0d2110150003c0c400c45030f500c904180c83c2100740c1aa040810994050303000001e84a0802d904030385404000c009888480b505071915407400f0b03200e105e051043d031940040000d200b18040c5420301210340100021503000a60410f9104020402d8100740235060064002410f01d00481c102385007515124801d2070000c1c40c46a460000450780c2c00d03c1010200080c0c0d950500c0f21060192517805002e03031401040032650360342410500b05095400b182c42400038002d0303c43e08451001341c0450b00c50341c82400e01d2945030f41d400428040b140100200c000281c001e107201800882d0a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 600316106 1250 600314856 600314887
    0x120309150112031106010b0f0a03060306050408030f07020c0d0213020723010e0a080304060b01020f190b060f13020310030605011806060f05160c080a0b09011d06040f0c0b 75
    0x24034000c0d13480d8810030480740e03a0280d0702e91080c010b80600030800e01011803100880e4000b0300e583d110514021401507076a47d5a030042d1642560b040700d00503404810030640b00894400181d02828074402008040505400700300d2030b02801c5000b902402100d0348040c40300034260102d03191103a20030556445140c80107440000111801d4456401c1d500340203441a25007000100160f900c6d030428020303491a1107655601c0001d20705040300d9419400340c401444400c0030240069400304410405c4850300d0001440c10441685d0700401080c410301d03c00c1c40314100c9482d03c0991403981e05181500603965100d207030a4005192880d40000d00b06e5080c80000720b14085003040c9400480002d0006000041d20b543c002c1d102c414090348081c002440610011440d80405042c021880d8080d000a00d8002e8640c00040d0030300c0341e101026500341c0101028420000d00902c01c85500602460342840201024604c954403008040e1001d840013280c045244103010340b000212004150301c0b11819664200018540306 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 600317356 1250 600316106 600316139
    0xf0c0414062b0905010f0b0a0e10030f0311100e0c041d010c020703050c04060303050d1a0d03020c10050a141305060705101401030209191116020f0d051203091501 71
    0x113455081c42d0b82c0811002142c018014415030080000400c035041050146403a00000d050407060206041b000011500a005020f0294001c2d40c54481007080410703ca4901181120483c04640c9462144007608001203804400958211808105841e90a2401ea041d10000411092a51920450700c00003500001c1010407a8450400c0d522126801c408000c1107552500c4050b0204000308255211507281e9403000200c15114420305000b0007034a80450200c4064030421005a88080c206060a242503402c14061400300c2c80d04e28a001000d01004201021880d0842031078540400c40a95581c240641100940406451942c440c581c40c1030455070303030a15403d0800e02c0c1d4a01b86140e803414040e4800c042c140d070b4001c0c1514402d0b4640200318004800f2052070310b08441c1e91038150202444200d001041107094244140094100310b00402900045082c03100f03220300b01884034040010070200d401e110300c11a03202c1030742d101e9541203c150b00381520300f010541407001542c00400d002062040121 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 600318606 1250 600317356 600317363
    0x3090c080c04050a14061003020d0c05090310050118020a20010903080f04020109030327090b1203120a05040201050705012d0207110906011101050f0f0c0414062b09 72
    0x71407920b5061181d421241700350114000c0e20406000100756041010103800528030744d00c0c00520782011040f1007800c030340d0f5401d8030340c001920001d0340d41c00760310381002003900441c05d40d142007046500d40a2540c0720f2280b50300c0d80c600e6440e000301d1516a49802941c0d1100b840441d4290007000c0b000da1078440e8002d01d1809411004203d02c90082141131240050b1984140ea060310782e4031351242151010b6500951000350162807941c00d1100c0d4203000788481d00701004000d0001c0200b9148180b00800c00ba96050200310085644288041e18255118088860301701448400c0060143c4440c00120341d684290b18000d0000d60900f40e06c143d90b00e10b2000c1c080614401c01031800c2070f044140410b00140c0c8100103020740a4013070100d1380111483c150a0302500a10141041d200c0b040180b1000340c2507520131104814100030744c8042000d21861600344690040405140b1840c3c2420304000c0241e11f04180e082c0b90094001240007800402140c030b090a8030504032849480741c2074004140c4001e40882d10088 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 600319856 1250 600318606 600318611
    0x1020d060f0312050d020d021809130209130c32091312021e100606030203061c0f020414070e09151309060c0207030c050604050a1503090c080c04 64
    0x1920700307200e4025415642d00c4002c0300b4060241c040f04070744a40142801e0004c0c60390801081107442824401081c1c5a0031a800311884980f101042094a150052010800195030401c000040e580c2000350b07903100d0014168040700d803c150601c4400d103049500075108481c1c80c0101a102810910000380e040740031101c030310401d800e680050102603001510700c1e0300d11046501c0d050300011a40d40c031695454060340304603614480c0c0114140b00d000e040310035a058640102c881c40c49204040d0168501905031400c0c02c3d403460601801080d06248030b004204070405c0705049550030000c0300800c50030030640040c428003080700660f414000e00c440541d00312000c0340c24180c080d41f5500344805410f00c121201040c9070321000c3e07600c00340270408030f00058041c25a03540f40310701c000107030380c9100303681e01c074401039004080280c00d44c41d10808200f42c0e9008507214080a00c4100a1b56660440940030343e4800e450a000700706100e031064000d0602440010302d11143d0036000300d5401c0c00091107a501c540104c405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 600321106 1250 600319856 600319859
    0xc08061314010c0c0f0614070c0308130515090a082106120c040e070503060903090a06031a0120010c020606130603051203061306060203030703060b0c2802090901020d06 74
    0x28a8202c8801040410201d00480c0c04000401c3c0701a24135003050307001b0a0b0125185025040114184408854078408102407013079103001c0c9070740484030607070100032080b981700c0c18060364807586c0e95420841d610300c60001034600002c2c0701d00403d00a0500c1507a1100c1400c0d01c401d0300ca044240707104485e10304903040b5101000040d000d4509060700000c02030f8103070060300110041206000242941032140c0c9030a2203407120001e41e0b07440c1000301d0b074459000c41c80915103601104041202072241c1d68004000c05d81010178680614018000091034070b103090038805120354840945101101b200d15038001d41c0c0d46002d03501080344d600803891501c60070084400369804030041c0d101c1c004603170742800f01900c16807110000c00310122051001b5034000400034045c41d990392401091400f0b0300c4884c1c010070b0060b0804014008841d4140c043c0074040d010203d825410a00b4a41e6469590348181c0241c4071208040c40c840d01c0072110103007400d01c6076074004d00030a46601d00070304480c1c081d52040d0620804503282810 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 600322356 1250 600321106 600321143
    0x24080903090a0b090609090f01031103061b0a1b060603020907260c0c03070f020109061e0305061c050303040c080a031e0912030806040c140d02070c080613 68
    0x1103540703603800141004001401e1604201e1650000280150840c0080103034488680e610704405102e0031012001c4517440d81145028a11160343d001b26134003a6011034184030310000701e11803502c49507041c0904151640d040700070403250030007040c98070705d40741e80081401c00500c10303280c0144007600c3c001d03039181c215501c40b10001c645c0724140c00c81d00a010b000c01c14003000d010300786200d07072908044135031a4142040d04140c070072800c650210703000f00d0741e5854540e9418119600060884010a158208480c03510003a902c1c40c0038200005043c082095030b68400a84240d40747c0c2000719668081d01b1049110301c119280250341c80e4415503082c1e41c14031251000203003070000040c0310640c01e98569a520981183d40c1c100402e42c0201c2004841030204801000c5552140080c0f0100494060b5444205e0f80c20040b0070f10045850103130403541040300000c51642407a403400100c0c1c643c00701d0000c0040e80c40c651800d100c04400c49a40006c80c450042e1400c2c89648219000e030703a8441030103115035122005078680c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 600323606 1250 600322356 600322363
    0x9100c0f0207091e06180608150f040f050706020c151e03070311030a0c1206030c18020708041e1202010c0212030c0f0f0d0c0c090213240809 62
    0x30030310010303030000c0700c24001e01c0110742051680e030b01c05402c1044a40312184802003942c4640d0480c9090313007000e0074018280241030044c080208158070150108840c0303c2080c1e04070050080c01e4180150f100004141000444c9043d90700c4540c1003810342d5481c44d21513000940f00d10038007038002d01c40c200c10408040348401400440312600f1084c9031200c5c0d1850002d801759095000103003144140b40d0390720b001d420f04103034003001140700d00c010500c001200070715582d000d412800c6d10010b0044003031030a002030002a40d81e03040d0703505a0f5880c0c0b0100a591803410001c0c400b1344503108004140c0103011800081c045481150300c1d0003070a00c210050a240c0d07e8036075400c00414510b2001e4009169000800090b045c8488080016070302d440541c2c2c80e141d0603440715841e002d0480390b007800e03981c004c00b280c144542d03040c42030190701e510300c0c607145e4403000c12511303040c0da2071540340220b00029900007404400340845091040003406036080c07a42c2c0483e481d0040f44d07132000c40c0305060700100d61000006040001c020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 600324856 1250 600323606 600323627
    0x3020c030d0513271401090f090b010911090d050109020114070b06010305180d0e0f150304022707090e010e0c070f110a142b080a020109080309100c 65
    0x5034200c0810514019088944c40000310701c250401018515001e01001240541406200520000c2c040c03545013201030000c8414044000080b41d142c00000340000d48880c84050449400c0c04021540341d000b9414840c091040d01e4085920101c0180e10303004101044d08417021490007600c1703400d000320075a5407403802441b4095004000300410800110030398080d52000d070f0090a00586c0081b01152282100c2c584510581c1308404240c1c01c0c1c2001c03180745048030303810079a03110030b48080f0240c580c1c041000250303000148c802881206800034230b095010000a040b440492010f080f14010f05040c44094104102c41c003400000c600c091001081070320912403418000c00c1404641c0f440c116990300c1c1c04090000010044444c000c0030450110b05aa484106001420350401e007011541d01d80802c0010600c042c000c4024150b074408100207075541004241549142c0080203207548900c410002c9005102e14007000700700e80e8010084c445d150000050100341000660820889070794007131070949008101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 600326106 1250 600324856 600324877
    0x2306040b130e0912160804050a06031d0102090a0315020f040e010905070e0a03020609040e010516110a0507050909070503010f0203040629150d05010306020a090f0501050405150d0903020c030d05 85
    0x20415907000044000170b00d6a2140204c854900b41620f4100040b80304032654810700001c5d0f02e4800004800c1907601e4400e07038a0907158001c41c03502e41810b0100e80312110a11001e45000f10341000202d002c05503804032020716000d01d150550711501c1e0100d0901001007030040c0c9854030f24260000b189103004106201d0b0b00d1100410114402c1e2071a0b00704800c951011064a811545611402540e603109008582c05203076100c4030ba01200d002110010480300755499210f88a81c00301440c50085900407031500c0c03d80d2416100c030354040d0b0301d860006e4502a4554441034141d8030303119410040192a03805035016500c140c0013403214800d464000b10004140e0f03a400d0f021480c03024038001461030a82c002051070102c03031401a040160900c0e40000712036090b4405da408640002d0140e20065225408030058405411022813050400c00028818000d40c0251030181403264400041424010151281a11050003d1106081c0c82c40c00a40310344903080344c00d009100300041c0b0040107001d0025075074104c030b8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 600327356 1250 600326106 600326143
    0x4020f2706070f06090b04060b131a0d14030f0a0311090102100c03181a07020607050306150739080c0f0d0b01090207051005012306040b130e09 63
    0x1903e46a11a010541c2d8108803019075407000b4000008050610745403040f0301800300090200380740c1c0c003841141c07a500d040c80507820345000c954200c1c43c1240300034100b0a5009540301528181030349032400080303841d000756401620021403802c1c42816800010100150140d0702030241585800101d9894002c000000740075800240400300f821503541c0c49410103030b0280c074012030341d8030400f40607414285c009242900c00c5560350200510b1340308101d80309900402039100071300c0c09181c034840040c80e6000c0986001c1c440d00120904c2402c403210003040e0341503507070411000303092070b42015031035040b00e001c10990b03410302d00d025074156001c203a41110500403038039140c025003c80b03201c05c2c0402001c207040210030f035404165141c10300041618940e00314060070f0050001a03803683c140c1800b03407910400a054282080c2084010701c0b070316802d201205e02c119136450f40b40034001c80c0900011028000c40d08002c0c040f00c00801c0401c201c5900c261100210b0300b2466030340707049807161450661100c0800340038550419 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 600328606 1250 600327356 600327367
    0x70513060b0307180b07030905030d05130b0f13080a140f0a06050405010f0c08091912050a0908030c1b03010b011e0302070219030615180c02070504020f2706 69
    0x60040c107010041e800107013103c40140b41c54884502c2650000a41603000401210041c0428101004120300180c1c55003041400d00c080340181610303541c002c0c017030314620500c08603d0f44900c0d01c40d001030b1889404014959641640c0381c1078041e549400207442a00c0203610440c150b070008101240b401c0b20044214080e019542590f12000d01030140940211440d42d6601e94002c81080c49100f03181c00301c1d0b03041c2d40e00790b5182004070f82c6038542a01d5610450144c0c0b1424948400110f42c04000c10300002141030054451030815016181c08506a118020901001410103048040425410002c08041284840508a600501d8200e40a0500b103501041200002e4640c09407038298500e01501235103000740c505810796002c254050400c00380c3d090070b811803610920403c5100e0241c049207030111407000c0300c114503011040070100c12030100c8400d010303a694590a0103030710900c1000040c0070054015945c030039400141e0801503100d80070211102c02c0c1d41c0c880511100c800030724010011402003000c1d0401 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 600329856 1250 600328606 600328621
    0x1903050d02030a090b06330f0a0503070908010b0906010309050f1e0106320a18140c03040201360f080705060a050a0302180d1103010b120a0b06030c060309070513060b03 74
    0x140606401e00d51f098205118030100a202440101000c458564404d5100e080200010b072802032180c000e1401a410b0580c905808e4440041d86076100c0400d103800325040805003085414800c80485000c134600030800956488101d03500c0c0c001d84100880e000f00401c07666600c25070400d14801ea034190301c1c0340d801300d01030000d904003c4226007802c1c8002e14040090b96510100680009403050134050039454013508098a00c1c0040c8030380e030001c0711a000c5803862400e41e0009000c000703046948800600d031000c3c0740d150840290501c00b00020f404104c0401142c0f42d040394240301000380706107400780c03055601c0810300341032900640300c0c0c100c11600c0f5a030808090900944c080d400041e0800c8c0c10f04441d40f000e11540d0380300c1c54030760710150081e8440c0c0c0200043c01c06150948810b01d07145030003002281c80420440c0000600c440741c03181c01865511590f111180000c0c01d002a0200707d54cc0900040b0501103119004940701040752400c6480c10001c64a081514058801c4d51080202c0d500301403001901e074 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 600331106 1250 600329856 600329929
    0x213030b0406140708011a191215030b041203060506070b07050d091401110301050f090a0204031a09010509061303180305070801140c0702031903050d02030a090b06 72
    0x8140b04020120b40d009140f10014400c200850780c0c50002001c04004000d043c00381c401d44002e100300301807414500100841c600c0c425420f40c80040c010858120110503001c04035034000c2d0411a68018031250320350740ca0505220303078007040d20b00b980d00100030301001c6a2107010b4840e090407035002030b00050070000300e0780302c081c1a0322008092406010b81001700c900720899a1042c1d1041c00c0c40364174002096a00c0541907402c6071417003110b16490410030801413000d903031402c4c01030101c2c0351700310f550105d182c0e15044000c0190103687c0c001020481098800004ca004074250a80309442500082100f82c0d0b801c0b000d556105416144000101040740b2504040b07072148a2400e4503890302c100710384d041e42d56561558580343d02a40131604c1a59141020302604034406004d0b034003d071880c5200b80c2050820780000b516001074940f10a19407800502450801d801030040d0b035900c0743c200d03c045480b072600c0301e0345801407c41500d04440003100d1b240000c1e080d03d0310400c5028045102e6000c1452150b150220015 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 600332356 1250 600331106 600331111
    0x23010b030703140c030414011119091e0312022404020d0b0117120f090405130b0103060606030c02012310090f1d0703030e040b0d061503150213030b 65
    0x8241d10b80f00705214508a400d542d6010321001e43d1400c0c2d580c40c041c1810003d0f15084c0762448a140d04110448540c840280207640e4811100082954400c084000c191140c580da40d108851201c000d0401076542d03c1c14a1981003201d028540b00003544a9030b49040341c8032401a0054094211030001d0050100804000142d00a10142540c00c1081c80d94680c081892400da01611040c0c10703842500c0040a41804040c03003c000089040e4240013a002e1503039642c1c0542d14400d03010300e5642000400000c1011031006c0044d8202100c1c12807941c4a0502e840585000d0040307802103030602124055140c414401c902d400718032080d281c900c4a412030303480c034482c18000e01070030b03040c0000750804590a40e1034483d00e00d60304072400c0001145600c0c6040300100c0641c00440480c5d03a0000402040400d401c5860500701e020116000101e134100b04000550b00030301c1c1c0e54050002c40c80c04004291380301300b03000c0c3c403001d0301d001d200c0108507122502c1c0914140d12503070000f04103080c01c0c5481000040c400324404c68 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 600333606 1250 600332356 600332371
    0x10b0304030c020a030503030f04030e03070503100903210e071d06040504140d0225050312030901060323071a04030b090a080304030c1707081b0106050a0605040923010b03 75
    0x80c1e001c3d640d4944524682060f40e0388849c1c1d01c0380005110805411a0b010400e10009401a1403c145801d0020352184080411819800c0d00c1d46020b10406100f60011b02c601e02d0802840304c0002c80d00b0407220018140052016070a204101011420a00b074005200d21030700c2040301014181e40d25011b0101910f40034102310b031061410707402000040000d100c02d140017507599004011440340303900c03800000c15800100500b110044007092001e5100400d40300c4c0c98500c0c2030030312991394450615850050080d40e1010700845a0030030100e07003504201640c1d607c03404c1490704445002e40c40f000d502c103101002c52218110580c042008000003103541d17a182c4e900c46601c0701501c6440055489802c0c1070b40c82190200c1c0011a10b41040d410081a8a124080c107120700d01072a0903e03400ba540d2210f00c2c460103d85080c03240c1500d4075943c00c06000d40250300a044050030500303680c2d513600c00180c8150404d00074099101e09101030020b9103690800b0034145203071000819050350346002d1825000358000792205 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 600334856 1250 600333606 600333619
    0x80c04060c0309091a030c0f0904080309122a010501082e0207140708031213151506030b040b130c1404060509011b02031507170901050717010b0304030c02 68
    0x41c0b00b400d944584809131740207440056072100000300f018184891180000e2065520300f03c400700c1e5072a1441d40b607500c540e211740e180d5640d40b108241d0a250454074400c40c02a6500010890041c0e02d01280c1680c1c205e00c41c3d000070116401c2600340c0c0382610000d0050074442da00c541000342c8948550a10400304841588002c01103c030540d4005040c4e0340010740a6420001030800c40c4108130082040304010210500130314244170401d5a441a5450041c00140a0300c1444403440244005280828815040604100142c07a040060703507000e9089803040038003092a0070f61803009400c243c002d0f8251508010210a008652607804000600396094150200102c5606481c0000829002013000c1c2c41c2c0c5484030358483c020000014000040040018403110b44120b1400050b00d000880c40c1c04a15a80d400c69103039a19084121100034111100c0c04560600c00c0900400d500c06510460161002e1f075118021070000313030b444048000c0203201c0c1c4842c0f143e0800005010070f200d803500e17550082c8002d014 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 600336106 1250 600334856 600334859
    0x70b07021e03300304050304080d0c0b0f1b0d0501170a022103090a03062c03091509210f071503090c030b0c1b0c030706031508160e0106080c04060c0309 67
    0x1890700d04c0c0c00494040350745910000d002d00c0115003c110a41909003d4600900144d42d95901c060000320b0180082c48002d450b407022400c42412200e1010070090006d0803952541001400000900703c28806d0650499101c090205420300108000d507040b500030345480b070030f0709003400c101c1c41c07104a00865603501e0001344400240c2ea541c50940740019401400041110900c8150801c0703a44480504841a020301c0d0510883e102c1c0c002c419101d090404441440d00b0b0250b140050000303100c0c290900307900c04640c00103420f8409242c504005107082900880d51481e142c00412995103100d4058102c5440c0c904080c02e040340c0c441e400014400d840340c0e00c1540c80c40d56a40c3e646140d80416500c0802c005804150381d85107401c03660800581501000091441c0500e03040070944442550054608050301c5040c40c00600071110444d10041000501b160545d03010521040c00c8081240268028001c02c400002040e42c41024440c0c01101c20010507854185003100644d150740601204030305001341500b0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 600337356 1250 600336106 600336193
    0xc02030f07180b010203031303260c040e1308040509040510020304060f0e01140105040c030e030c01020a0f030606080106050a1e030c0f030e030a050318070b07021e03 73
    0x11400611211803646008410302d0440010348154203407142c1198030a0042041814010050030395041d0141415508410340b00c1c0030b0f1201550865071741c44455103c03014401d845580600038030440d06030941c01991b030b49a58030140072414003048080d052072000d010030700480c0f40c042010f0740c00030b101d8400c03181410960111042130760011502030300d000f036940c2402c1c1015400d5000708028204040020800c9a40c401c84407003030000c060003264040d80c5c0e64101211000d0007513110900141c0500d046a8880e6000548a8040c1d800300c172583e800160008401e01c1c1403402030103914181c0d81ca40e02c80b00001e03800e108044901e5080412051300b0000c004004688a002030b00481c40c2e6680542e401144642c2c0100010b442d40041c00a00e4041514241c501030070480048155040210a4500380d562501d0301410031005000b0040041010f0240c1e80d000200000020004c02501d482540c99031656581c480b028100201e003246001e4040e001219540780c9140f2402180499102e0b200001007040703030692 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 600338606 1250 600337356 600337363
    0x504151508060a12020a060e0a030501060f03051203090304060f050d0f0c200c19050901060509011d090f040c1505070c080d0504150c0b04200303190c02030f 69
    0x1030980042a00c0e4030502240d410480382e0748001d0000e2480a4080009503800701c0c01503902403040108002c80c808a151603580e45148c0d150055822400034020b02d03031203940500d01e004491008954a2013000a00720303004070500c01317030391090448401139400d007454510213072280d80550010300c081040402c05403208000f43d00c20700238814881000003515640032000504030241000742010b82d8001215101c0d1040b0001480300103010069410880010105500e01c0d80407025070810b41c1e00240310800481c0265102000c0c000740d0409907101c03101c0000341c21040620001c410a0036130403441140020f4000c24101002581044c4600402d03115159201c040202a21403d14003200184000942905201c00e20028001074550800130300501481c840001e4070300c2c4030754030903480c0c15a03400c1540f4801602884003140403d810801c070b0607643c0707094036019240d010320030f2208206010511000f6030500b00001a1030081c4030074206415408845c1c001a581c48000d00b00881e89442609803030058480d050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 600339856 1250 600338606 600338639
    0x9050a110f150304020301050901050c070212120304032a03092105030c0f010b030303060904170d060b0403031e02250503010c0c02010f03050912070501021318200301050415 76
    0x40c0409441c4d00b4240b040500b519000fa012190780d80c1010b0070701551540410440d6070141e4101d402820002082101ea400d108080fa010b6101c8080402000145a04140d800316000c010003152210003103185001003104038001009070004002020520032000094900d956000d50350040c9400c0c44021765419146a10081c840045078005c100c800512030380c2401a001c100f902100914114a490300c00f0840381c0c03100038000f403c9100310480c6062a54034030411900360300b4019005001a0b07403a003240d020f050740b05c0d110841c00182e640c09040034000071a200091803540e0f41e400340c20707036002c40d58070340000681c9001c582407100c9101d175000a0340e690074800c0d044882072a407112003011300103000240c4031051200d107080a0500309020040050300100c0c02c1c4003140c14080800d915010181400c0e40207000d4030f103031120000704105003c25038207140032000e4020541214103010380f540707000120031440c2902d0b0754201c43c50000d200502481c03801e80c0200c040c240d003040e00900c260381d0b10902e06201d02c444 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 600341106 1250 600339856 600339889
    0xa1506020d0207050d020310091a04050d090501022b110f07141005030f10030f0b0402090912070807031404060c02040501170303240d0b15010309050a110f 68
    0xd036200d841682c06201890003800100d803c4400c1c0c42c0d407a0042a01c54071551105492650b8451452003045114001710041281c004a0304119251516120f540c0710401d02000700410b0b141c4900041d01d40c070010310074000301c038003105101107520f596050f01e0812a408a06500303001031518283d601c04010402e00760000002c1000340102440c01e4140d04104100c03158407030140109070710468106400200b2642c0041c480100704025566035902207000c541580c0000300113032925100a41807000340c00145018074001c0b100c00e500d90702c070401541e076030b042d24007940c04d002c800c00d00000021809510142030214024140031070500848000c2c016681e2040d0411350114000c0e40e0003001303504003480f1f07440c003401101c005000b50b400701030b01c8569640401028540b60420000004003480c0a11a03401c04841c000340c0808000800d625003503034210400c80f0005c42d019841c1000a41541c824043c401d4801d4201015262144040e120716160000b41a410368020201d40700035a16502c3d80690034001440 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 600342356 1250 600341106 600341113
    0x120706050604060f0b040e061804062c0712021f081b0306010c020409060b1201020c210a0f0e032a1e1e03010507022b0503010605030a150602 62
    0x40034420041102d03104d40221440001429062004140840c100c0c0d0581e5449060340000e075540c80001840c0039100c0c0f441541242c849014130040046e03541146030031200c00000754040003a00e5041d080c010030f5101505401c0e038006181044409d906000e0081298005000c5d280206a0f12a040958210810918001072851030802c807517000d02c110b60349103411107400c00070b145007000d4000800e10703191501d002c0d01c01d5944142c1d6030100921540500d10f2400060030484801e19591408d6000303400400326140c26001e00200c0000404000204080c4140d89560740340c18615130540840d441c000500c1410203009401001e0340d0696400c102040810b0000900075440b40b50004100180310301e2110114000c030032a52005101c04007c0344001c009201c2550031275940b20403400100d007124111102c09400d5440c0205000095601140e41004152140c0283d1234030103e030141540c004051002040c00178000f407005203c154032403001140c01104044000c100c9070403208042c48446401e43c054000f40e803 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 600343606 1250 600342356 600342361
    0x90e0f1506031c02060f07020102130306020a0318080d27050d0f05090f12011811151c0903091707030302072c280c1209022112070605 59
    0xa020040d683c1220f50b010241010004000d1010390b640801038506042030705a8000288054401d5041e0303888564446d100d030105564a00700b40380250320504121340020300f89030040d40f030340800d6200007039203da00140051400301c84008003c002e0094200d070f0b120180301200448103420b5440340d4030b000180580054000070600c07001c09000c4840740350000c02072103010301208440e55074a24180341481c0c01a5920041003d01050f0070340107104400e040d4400ea840d1000a900b03003c0001c148030b00c0900d066800925000c078440c0c104803c8c3c024412050285406544400c1310761065030000c903a140d00c02c1c1401d100550f224098030034402c280340b501c0c041e149d1040c1400c2090550401c4004001c04207012018452007803d14101c0c091107444c00b03411030340c85d84c82c000b04601c900d0385031104958081714405c8500d8441c035190f501c2c1c0906600c242c0100012044050315541c0c0c0002d201d4540600c0d4001c220002030460203500c005030044d0001c05080d280210081b10903240f06070801000c4442c8506c80006451 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 600344856 1250 600343606 600343609
    0x31e020603191404050d200f06060a0f03080a050d020403080304050102070b01140a05060c030d060b1809060d0609030c082212170310090f09050c1504090e0f1506 71
    0x4a02070f1903a014150291414480400c8010851085900d00c6150071008040409600c1c080120360071007605140c07140304400b210010001c10450f00070240bc82c1c0c0d4001c0700d5a182c0c001c25100226000180c007003642001182c40c00e901680040c84a510a10300150600c1d940f030301c440324107130004c9400342c1d01a500003c81d03104100801c807515000d4248014803c4051503c8000f2801c41c0506000b500d00642000079102da96890410a80708080c1e012501840b5050712402d03006010f40050301d481e428450b9a0074641800d00e44060035078400c450280090f281c06400b034030bd80c40600200070064051009003030110012983e030340014008a14046000e641d20ba58600d90016200380603408015202c4090301c0410000b02c10700d1841c0c5100c1170402c002c0f6125258034000301001c0b4003950000541905d0042400b0300307000a42c100e00318190051082c0e450705080701c01402404004018550284c100401c424001114142e0140f04228401011240c610364400a154500100f0760b00c0e14055005002c1040510b = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 600346106 1250 600344856 600344861
    0x705150322080901050d1d0307050d030e1b0111010903090f0909050c09090f03040f150509030705040e0a170d1808160f05010504032007050307031e02060319 69
    0xa60040d01c40c01d0000101600c44000a01540402c0c034100440010070340c0b07211382a5001030f00d00e8000c80042c4c0303580300301201099075240d000481c100d40a00802c894052958003034880d0310700051504000e806003140071780c0c0c6540c40d110b82c500c0103810b018140b00d41100e03c0d03809104e0204541e00c43e84400030424141218441c2c1074113154051001d4504040303034500040c10110385042402e2007a200b100860319280400c41c208074501d01010f80e60310000c00c1c005800c0c041d0714600e404880041591010064101c2012119485032142d104e4160703012240030440ca05069000180c0000d41c013041c0e41c4c080d800d82d0342c0e03060324500c1180b40010704400030881c4460341210748134000085507285005200c10800c0d665000b2030303001c0d0421195118000001410901131419404040c2660000080080e847e11389006000303031240c1c40c0c86000c000000c0302281d004400000d440c03000d07180010010000d9510f540d44849104400008415404003040643c0d001615407401440c05a815400d15071803016030400c21208 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 600347356 1250 600346106 600346141
    0x1103090a140304051302130e0415201912020729060d14010615020f0111031b0c0c04021902060a051012210e01080105030109030801120507051503 64
    0x5080d041000f04100598849001000c910120940580c40300c1d402071207044082000d610403540e407120b110401c01044100d43c1d2415803820701141c10880741d031800c0400e42010840c44010010100100405c1d000d24590700c0754240f126040b0302e040c00c80b40e06503408201c00e9030408141150010445800b5145c06013802c0c0f446848100b507441c03114810318040f80020b100c0c00b0010380c051b04e0605140c0820b44062404c0d00300c50060a86241c844500d02c00b0888000e5490780500704038500c5e0351a00c4420b0f0001c50342081100c0c010a07404403407100641080d203841d82c1903070142e00c0e14403980c40380000c0508d81c4c5e12a8006428004020680d080b925008044040c0c10800300400c0c2c0030106240c1800c100054908400d0744090b5008500c503850118400d01d0320f0320b00600c040e48612540040c5260b8002003541c4964501006402070303891031541c0c1d03a22010b00d0f00361040c003807006004c5132404c0014040e80341c906d40701550741401403003242c4045a03600003084d4251069002502000400410070508080300901d031407 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 600348606 1250 600347356 600347393
    0x5070c08030a35010b0304050c0102070e1f05030f031308010603120e01031e02210c07141f02040e090f0a06050c070203060f0615190f031103090a 64
    0x501d80325035403038000d1a0030504035441440780290510b40b0201c04002500b50f458440d414a85030041d611041c140c02c3c142c108541c111424840c07200c1c15a41e65101044540c11203007a00c0307031510fa90716101e42414140310040c46040310014000000100c40e40c04011806a181212000d540d481d0503008110383c240842e9044400c049e0b04200040002640101041443e6442c07464103000030036205004901400800c10003448a410502d440801c000c00e560003024030b01500c0041d0000b111618101c1503080000300c40400300003206111003008150380c1c20240070b95070119400c0e00c1d520b40d110302e8842d50b420860f584896449a01140c28000c17012291400d075041011440205560b03628038038019900d0101030401044161258080b9038150603040684a8090b401002d50b0510318141c115900082000c490462103944241c2078403000003102411504007490500c601d40c590800c0c40002c1c0e4503c001100b01000b011f954104a0380200d0092020310300074950140588242d11190908038504005148000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 600349856 1250 600348606 600348613
    0x209150a0917120f040509070e030d023007080c25032316030503120109050103170306010516051c301401030c0905010f03020a05010809010902040c05070c08 69
    0x40c0541d00000c0900c14101c030b8004213035a49001000c505514007030b0741d110302d03004120301090000064005e00c1c00140f148007a000ca0f03c0300f0319400300890740d40c1040d000c850011311861520b14501c00f03810700e8036101c0c0e1910b01183d900d00006a41c0e403292075407003032858a50380e4005090300c101d55411001e01c11a14501d94483c1c40c501030031500d500e030b003982c2c1524001c41c040004282d00c00901c04244028500f4500d01c240c4860101c1d03407402e0164036a03200d816440c40416200001251141c1148545c40c1600c1d0000d00c0b040c005048000640e40a92000d054281442401e0007058145051882010505403144020304940030440204e01d801e42c054212000904c207500031200043c0980003010b08246a4441403444212142d140940c010118513000e80c0c102c3c64090004401e1000643c42c02c4c00300c2d250120b041000703aa82e084103c0204c2e009000003580031301c10200410056104074581500001e420000240c500d40c0c0b98001800c0318280c0008801040700419444144004210210014807065028 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 600351106 1250 600349856 600349889
    0x1505010f0309051203131b0b0a0305060103060b1903060b0307090308070503040e1509060906031b0a18060807060302070c060309080c011a10080103050604030c03020a2a0902070b04150209150a09 85
    0x102301405456404420181d4071000626540e1194002c00c1c01009100e05465481a480305250180d1246100860100c0c0c01c0030000a60361308440c0481e40300c0c8480760b440c00a1181190380300400b0754804441503c00c0d1105010129041251682e0170303026941c1e12804000c2c40c034a510500001c4da0700100340e188642603480c00c100c1030791004030b03008030318070201811840c3c1ca030707440c900148034212903402c0f07042c14080c41c0c0e54050080246602490030394140b0012030322041c1da12030088041c0e2041c41c0d0001c1a241c0d046204028450103608440115449480314a05198901c0340080c00c50b04041020480d000780c1494075061400d012540000c100811302e801100b0390b0468490555a0501800040800000140c01d800b418828030500008030390081c0000b240180300404c0c038000c00010b1042016440e01000000740c81c034441d01c201d502c40740d403000404842c7d9a85840e51200b407034400203000031441c0c080110001a035222140843c521181d903000030340b079aa0308100249900103540110061400c5601c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 600352356 1250 600351106 600351119
    0xa060518091e0c120610021c120c0206040303061e0b070519030806193807051506040e0319030b041e1505010f0309051203131b 56
    0xc000c04080e11000802c0e1540032507454802180c0070510303000040c100a20074550038003c0181810084210304505980300c0c0801c000700e800780b900d030800c0517070712034207210b03a004010b0f660440983c1118101102201c2c01c41c818102642c415424900040c0c00c54001c0104140c0c03d40b14403009811401d80f80d010071825100d4460030404140071312950341c0404100c2f6000c0040c1000302030000740c40c40d030010058100d1454017501034041030b1640d84c80b1309075000301d00e0104641c601d568421110610380b0342c41003403400c1e064804120103c1c07001200029181c000c0006491418008002c058401c500800c2e07881c8d4070500e0640440c101406051142e418100d00294500000040d036800407600056052040301008055005080d08800c054015040c49601c0041203591482e56075400d48801043c004030509401074001d02c0a903004040c007040030007250b007411920a50150900703d100e6000c8965014a0306020b440c1900b0868100c014000c61880b44003c11014235081e200800310315428000b00d174109003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 600353606 1250 600352356 600352387
    0xf100302060306040b040e071404110d15090c0f020c061801051303060f0b031c1d2803020307060815010c0206090d06150e0606040510140c03090a0605 66
    0x1201a108441c04400704601e961a903101076456140240100901c03002031140d0b80c2c0350307807040c4100781c2498078104210b02141440d000d81e40f5505840380d41e039841e100303032500c01c00020700180408450140c00d03094007080141107842680c0c000c0d10240c07114440c030800b02200038a8403603a500594081c80d4103206424000560350303852100e081003420002d40342c0c8010506031686e01205d0b40007420387c9080144d06c0542c0105030307000c0c0001c00e40036419503150504800001c0c2103121074181920002d1148280c0c0c101003114044000401d0b04c0040505282c44600d50a05000201100c44480d410b98402402c10841c40e01300000b0f80107050700e04002210389441030307090301c000000040c55410300c1403e040c0301c800c5684000880c0d550302c000a0040020303a0050a1070002004080c0024030410254040429900282407220b485258010545407030242000240308800b05109035850510214501810910321400041e10700d4144a60096455148050400005410b15407150003401000c025400345a10a01d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 600354856 1250 600353606 600353609
    0x181a0703020f010c1d0d0507290a09030c120c0312020109020604090e0601080d090b0f070807110a05031f0b0a05100509190b180105090319120e01170402040917120f10 73
    0x60483c0d408006080403449440e13003030340c107002718141c0001407400506800110307071001d89000310804d668181c2c488441c035011071601c000142c107420903c2d004000103240007485042e500d80760b00c00840c044c20140d0107c0c115030002e810034801161101c01c840ca510f5010014a40140310700e400034911041500d40c050700c060494080c0400c400000110740801d40c048804803040c451b03103ca400c560f03c508500f800011001074994070351007003000c0c6a00040c1d52a0006412500a01c2c2c142080000416204844004c0c54403400c2240c00c00784105002a07980c0e07800040c410a9901d0f0307251507503664007490810844400c1101c008840748400c0c0c0091083c0c814903c1610000820500b6104001b282c07400140d84900440b070f8034503854400e03100f040c0d69090510700d890203118030a80e000b0b0000314810728141ca40c881c10031555400600e5140e000c18507074222411468002e40007405c000f17030008040d11048a640700c00d00407181d092000103244000c480b11007509690003000d41c04044174905100c0030301113205069 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 600356106 1250 600354856 600354869
    0x10f080a0b0d0804060203280203040b030a06030503030c030a0c081b0a120606090305010b0906030303270109030807020d0f080a0f0212010312181a0703020f010c1d0d0507 75
    0x25225284103580701c40d41100011a0040350a5413207070750b0741000039540c4e400800300701c00c00d514240103440b01d0800e4110440c40e03030b00740c2e4000d141468241008011150002402c038400192590b00c0000800c2081c001075010302c503840102a600d1500e01e400301c06580903441d080c0304000b1181e040011211510130700710140c2e02c05942c010f07501c22001c2d004903250201600b40c458014608180001c403aa0440140e00441713204100a0194210f0a002c001404004588041c0c06030403c10004e154906020300310361015100b00070f9010b551101d41c1c040d508440f4450422004a00040184140d20383c04001c203041c1440e0030701c0c0a10086051040060050101138a600707000360307d8814a00c261600342d015540c0c05c00408044000c55a56401c044444100303200040001c0b40388070350070340c2c1e6806038115a641559480c01849544400c0d05543d5246a0f200d84016021409000520381c610304080c0114a000207890741d852000b4107421025050a08000c0c200728468592982c00724001107000ca0f0703030800c803036070b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 600357356 1250 600356106 600356111
    0x1d03100b0d05100b01120501031e020a030c1508060616030e0d02030f0a060c05030f280f1e18120216081b090613050601030b060c100b010f080a 63
    0x20600811614920654010b206000f07441443d0880500350b03011801401d070903610218101075000b05402103601c03c0c040603120703008901c540f00c1014440007400c0540c92010300720001d815502d071030f03003418903820781c004c124001040600c40d40c44580c0b04e81c107980c101000319091460100100f040c10300c0c602ca80b403402010302201c5100c02c0c13441d5407082c40c20350380c198001e400d850548000649068981100c00c50440b68549801041d03040706100ea403d60f4440c1cac500a0614102d0303243c20342804041111280c4210615480c1c40245d140c004030b5028007905001000c902086488600260500c11100401c0b01d41d8024548110741c40b200e80303012011245140c000816011090781510100e0130480044400030300c005501400040510f00000c98582080100880708400c0902404004100d001682c1099128030644115200e85580d540302d10741105050500240311544900414956006001c1c0c054868006050f145030194643c050007050712004d19000110654546028200d42e1001c1d1281d0030071503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 600358606 1250 600357356 600357371
    0x12030306040f0e030c150f101a040317070606061b0602071506061706030712061a10180503160e040602160c05120c130b01140c030a1d0310 61
    0x7410f500c010829005501030341c2e611508954240c0e80c1d00358400c1000741d100c16120000f215003150f130380c90740d000d40903207541c08604a103807507518820010f06d03035040805210204000400605010b20758411446075110706d076181d01250610400b15505a030100c4148440d800c5a0050707490081041c13403c2e140d01c0719005850311400d0615030346410a0410345c3d0341141c50316002182441e00300c00304040b00307403800c0c03000c0c40140d07154020315442c1d64251060460a6161900500000700035401c030b0a00c400f03202100494014491f40000c08000c20f11354100041800d00510300403110480e808600946800d800514105007000c0300c0a007081914414007c400050002082c00c20402d9011102520721001440b61041c1c9a410101001c0d51684101031003200082010b0380a054081607038100000014002400b99044034504c00240c00700c52907060410040e0051801038940c12400380c1602c860404c0255128481d4002c090410340300c1c841841c14564203112a00815500041c0c81280820102008115503 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 600359712 1106 600358606 600358631
    0x40c0f05030309040b2709011a06030c130b04030303051008150a0213030b04080406031416050a170f15040e0312041a010f0e01051203030604 62
    0x54000b4000c5108915099205d99658000038110b0301d5540d68000440b1a41004500301e40740524107401846540002413042001c1843d20459014502580c0c0001501c140001001c50400b0303280020b00188820700c20449400510268001c240c4503a200c0c50090041c05040369244134005003414002000000040d224050315000001c0da142034440742440806075001c942d0050026038580d80002c0091a03800c4424400d600613100c050b00c95081240040c26140080d40030100554008140046d008041e0074200696002d400d00715030f9655404801e03594a269609200c0d58003181b07004103d00e0100e06100c4610a000c1c0c81122071030000b210040008988524003100c4050707105100d580d40424442c07000c540c01902617030b00c0201040c41196801c841a01c26080200340008185080205890b003041080c054581150700b20301c1c2d602d0f0712403140d649000040081d44074540b07031000005030 = true := by decide +kernel

theorem cover : BRFrame.Cov 600179856 600359712 := by
  have h0 := BRFrame.cov_init 600179856
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 600179856 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 600179856 ≤ n) (h2 : n < 600359712) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
