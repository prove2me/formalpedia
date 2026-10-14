-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3531
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:55:58.182248+00:00
-- url     : https://prove2.me/submissions/607d4fe1-c80d-4490-b1c6-9f0b270521a4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 634892086 ≤ n < 635071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 634893336 1250 634892086 634892107
    0xe01051b28031713140102040e060136080d020708011413170d020c03131e0b03100e04050624010c06050a0b22050606030601170901060812250305 64
    0x1183d02500b114130030024460307000006a03002c0c07a03116400070100005600c4500c0c1c080e1400c003004000d440705040c0802e0742c900f68005803040070306039415448204201105000203a000e03030324170504c0e0003240c914003801421501c035036000600c1c0022504820000c2040390a051000c01e080801560a00d9035003100707020520100e903014001002044018803804d240000390007850089034004100440701d83c001160040008140031403550041031207903050703100b0b00940340e40394024903450301801a001c400800802c42203059030300c000c40508440042100582000d060050b92240c08407904100254200c0010a00040107920302092450603140c03441d1500d070303550780e01d40506001000c0100380ca645102003092980e40b02100807408100d164200c0d096140880d1a070107485d0020300140c0201c404106204450341d0101700d184005501609070384058940c0b011041c05444c0319031016100384a00315400c014441c40d8001090409419503010102c00e1aa10345120031032011840a40410b00c24400c1c04000c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 634894586 1250 634893336 634893377
    0x804051002010b100306080c1503061207030602130f1a030f130c2606160324030c05040b03010506030a02040b0111031201061b11010e01051b2803 64
    0x2004007400041188078066001ca294034400030300880000303444d2241000341d21070500c10410010410f8599203105000d1280300d5080d84406002c00e030103081241040000208140300110144d07500c25030a540e20700100c000701c820a060340c0140c88100460f40b0000940302240c0c03c0e049154800d21f58040e0450742d038410381c9103121100401e00d202d420309c0554400e000034000303080c80020300070041d8500d0310705000c0d440d83e4510482d001c82c100700301d42c0810144003186c031480c00c12840b04526454082445007102c1d0907007200740c01103140d64801d80180384020003007049128482099900c2540e0800c02891090101405d8a400307880301500b5400600c00e00f005414190130a0441038018100038021201e0a803005117507078005200c900a1502402c018080d559001244007094604200080d8080003951119800e0300d04851106041c01031510300312003540d00400690f00f144010740303030302042d001e44002d00f261102c16110070071074a0305030a00c1c014000040034600541c0e240e0585e40c0c191010704071205000301d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 634895836 1250 634894586 634894609
    0x50a0b1909020708070203060a0f0e070509010b090315150f150d1d0307050a050d080702060106050d060509040f02040f020313062c0304171203071b020a09090c050409080405 76
    0x80d130b0402008610050b80301002860302401c218880090700d11031b5100c14000b210119241070245411224040085944602a460540302d00c420256603884646000070715088c8174a991410704410001000140207aa03203056050000943da52540d0418010070080c0b80700e2801e00b0300390207410a0085203409001640541ea0340441d4026106501241c001018a150800c88041b21168005030a03202084010702c283c141c00d0003203041c01c402d5400c041398042d481c0c02c0140a00e404108001ca4803c00d0059070743c1280780141009459040d1074285400d0441290004540585c0224140b052001d140107151003140d10660340418030b982010b04550300c1c04c0c040c100f8010306480c1d120384002110b43e0043e5103804580010114401940d450346450303600c1c00064546070012034203401508400309041c140b02c084961201c440d2400c40c0346192604280e43d48144101e102a401c036080b420041baa14020754484024903000d902d03490003056580003084207a944000300100301c490b050204003c0d50802e42c1e407411 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 634897086 1250 634895836 634895843
    0x2060f16140912030d1a0a0b040317040312080a1409100e070503010c0509120312040605060d1227030512090307030b0f100509070c1e02040906050a0b19090207 70
    0x80310f4684600d0342c945035403c245507182d02d0035078401a800036070b440501480400d20058960324581890814600030502861001804420008403088041080802120080c40e40700d40c00c2e0070200003094004142d49030842d00e005a551420605034519030701244079510501903103004048003035000043c00081c0c980800d18000502c2a0035001c0f03041d030750a0040070681c0e0459903a45841309460f00030002c40040110890070150010003425040b140791149140d40550402c1c0701040c152109800f241c02c50340030710310160801a440d4104020740d43d01000c0c0141c5030740c042c82c0d0b03813810f12051103035070105450500c002001544014103040307a00b5505400780015060003015500403980ea500c2c8d9004010301100c0c44117038007425000300910028011021409450183e032a01c902e03240c40c0d00c001e030182040d00800350500003118000d000003821242c2d10f241131036000d002806580310910303110000c0c1005441303000103582020a448964109090359209952542e28400c1c0a545040c3c2c1c4d000080d40000401d0b0b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 634898336 1250 634897086 634897099
    0xe07051908031b010c0c0b1311030109050114010503010e06010302040e010209030f0a02031203061e0424083306030304051e0f011404030b190c02060f161409 69
    0x14410018030103460381e00f4a9840301240740350f01409441c212041070040342d040c801007200d11801304025003070143e0320148040c149082060f031401c100011407601464182c2c558200207880d41009410b400805140d40304658140003640c83c0c0e02014241c6100341b0b140d80141c0e02c01d02c01000545416001111035610103000145003a1520f00032074180f446008805486030710603d01c0f201141010010b100c8880c810303061950542c2004400249030310040131307040c00312204a05800246940f02c0d4000100c1c8446615000e0791000d410956410407440c42c442c8140c140108000034031080d00c5801824001800200b400b5880b400c51029040301c0c0034060310083c1c240c4030620000c1101d48556904c00c480708003503c2c56280050b003a20400245c50360004586d4100302c1103003c0c00b103040d4010f01c10340b01960f40c450079070407242e5581022002c20041d51103040c0441402d080051a0032034000c034000d80a440c4500d51000039949a0007a2404a020021207030300042c40c900d191042e10f0300c002e010707044640004104 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 634899586 1250 634898336 634898339
    0x1d0901061d130c0303020a1703070c020f03120d14010b070206160303060e0103060905190510020708130b0c0f030903060a05071b120f090e04020103053c06040e070519 73
    0x82200f10307a1035403c05c50140e40302c40c500e1403c2c0040d4260004d0355030340e840d280340d00e10f1a01840040134541e05a00c0240180001007014200f90b44c2408541c0c61222030f013002070703140c0e04007034136001c050b0290b40281c1d14101d81c07990002c240d200c0724204a6882c00cae005450f180c80c0071b40e42e100c0344101000b00f54042c0e040540d66000800e4503000860311074002c5002c1c074400f00382ca9010741050b904001d0501c1201085080b00c20f0080c001170004948900703030350040400140c662b52141890f40e10340c0f00d0000390f800807900d00000841c0c1d0194400161403540920002c88142807220411160b6a2140d44081503250b0700120008828017020b8004540c0318815141c10540c600305210a0041e00c0e403480c0088514041c41200ea00c06654408030a030080466807410178170f10b9280c0b40300000c2c01040070f4406410150bc4400040d106804d0503804585040f00080480e28845401d80101d00d1910843c100c0c84060030040c04505c50340f41a024136400c030785000014107019403400c820000d01d15440304018080d0701e21400d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 634900836 1250 634899586 634899593
    0xf050f0307210c0221010b040f090302120406050d0b2d040506010903260c0f0a03030c09080303180c060409050105030d020109030f05030705131d0901061d13 69
    0x39251203407155201085150710140b4442c0307103562440e200002c000a82c0b8501015030368103400044403c204c1244825814041c0f511580540821701c0441d400606100303203000c14140300e074010240d00703000b642503c1b030540452407055403d1049101d81400500284046c05c4003000a41c400602400020546a0082000f982d9160000c442c45100c0b481007060381e2011041307080c180200e41c0d002d6000d103480000c03241141d440d600c9501c100b00782c0000d002136101614003154140e404607248182a035085455045044454a075514a807140031400203041c4600e44221074001c0c500c000a0b1100340002c1c1d400c50b030321b00c91002c042240311300c0b040a00c1e20035100250400d455044c0204054559204080b031258140000c0c14074040b0b29070000c4003103a1400c070300038010903800903c81e1380c8a4002c1c54410703030361b4032120001c4650b07020348072180214401700c0130002060140394801829503202d400083e00695940b040c2c1300d089484c188078499401e0922003044148802803e0159807096514440c8031040d9902e45 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 634902086 1250 634900836 634900843
    0x80714060715091a040209010801020901140d0908041806090b0d060b010207030803090a020102010605030a08031605042705100621090f05070503100e0a02101e1e02060903070f050f 79
    0x7500404d0301c402c0720180420360404507845405070640400075403602c2c00c02c4000034a804040c103d211110640850381da1001d0341c0540164000d60f03080366205071078644a0030080400e1100c1c2052130071072868840001842003040c0181d0308200b42c010000b0a5a601030746511015080100c055030441c05012804000035070310030007030f5004104c8100181120306083c400a070860351643c1182d807103a030006102c20000ba80b07450403268042d000000340311011013030f6a4140e80e0390207540c0010100210b007103100342c010312174851181181e102c2c00c417040c80340d41c403402c0500c0710920142c0a03010005201245147c205841c080342c501460710341c2000040c8195680e11000506800d0200c100c8054004010412039494200810000c0102c200402c01502402d0200d8a0f543d07101041c0007401100103085070a581405910321180a10800300c0b0705d14503041813080140307903085034010724030030001d000c04540301c0314400a03480d031050000710000c6140c02c1302034840c96007550b0318003011500740c403408019040d40a01032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 634903336 1250 634902086 634902113
    0x10e07081605010e061614010509031e0a090603020a05040b04031104051f180f0c0c0213140a090f08040303020c130203060117101e08071406071509 65
    0x1901501c89801407460082058085034403690400c013800640d443c0c1c542d00d4808665045800c3c440200520049241940940004040c50740d0b0a5213400108a04036001000510b440045038204056032542d031001c040380ca003d500c480720000389c6a00001c1c02000e00a0780100120b020398100301c1c0c149a030710058138a00780e01ca5042240c0107080042e502406007031900681b9040200760008446060412071a0131032498688100320f10f040c2c0591b05901481d42c160b00c1032500380e0004100b80800025944050a4500103200c120300420a00030007001c520b21610a10043e40c0c0100d280303110a44480f0389060250000b00003e4401c1c0f0000c0d12043d0001d000340000380000c51107a0080e040f94943c10040298400c5190001c200c814010010441a60fa1041c01d0403005007080c206058140c55030b0ba4400081c0245030041c8906500c02042401d002070200014012549201c04585441d51150410000c090b8599406508443c090143e100003e140084600408030000ca000520844549a890040088 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 634904586 1250 634903336 634903349
    0x2040f1814070503071d0601090911070201020d050a0e0d050f1e070906050604030b07230c0c0d120f0203210403020f0c03060a1109040203040b0601090f1401050a02010e07 75
    0x1a800384071200482880301e400284011009011403900d4031494905040160300044080c400301c100041043c1c0c0900034500c090718141000304138404246c006000c166103d0b003000d03405482002d40e080c020512500843d00c0a00603a07903410000000c040a10096803a20302040b0707041d005030a203080c00f905041201c1da400d070b400007451404109800204505014a54202440d00390038000e050000c0e468000494044035030007005ca143c0742e82c038010b040310f0100710350305940c408845c42c2c0d1848414883c814080c000c507030410b006940704c10b90481b0400521441076200148070268039401c40c501d00d4061925501e50340c80760b0046d02e1070440340d103441280b800b111906026001c0c240070240403c0c16030404c112029043c1d4140104001c119030000240d6030980200000744c5203844540c6200c400381204191b5459800c041d0042d0b44a04091600e4190b0320030072500680022044200003030800481c0b020750045642c0c0c4034070345c04101c2e00b60004540c1c0790f100d030b0448020340d902c1301030810110700100005c1c0d009188 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 634905836 1250 634904586 634904603
    0x30201060509040503030126030703080c090307150e041b0309020607081611030105070e0909100207062f0703120608060405100507050901081311030313090b06120402040f18 76
    0x600701032261800c4c0300e860030340230015000544008498008219400b154141c10038544582c0c56070803d42c1180f00c0e664125425001d00c2d440014040004e4080102007020340e11119840c01102d0280b1080b40c00c0304107220040c1c0780c0c0c0c0c040303e501385001c2da2103c0c80c143c2c0054107040c0381107425121400c003540007102d08101c0e4020070440d10f00340041c6d4030b2800010081100244410b00385002d000704451840103010380f00c0c0604002240b0415010071a032811b441114106540390a0f45040075030041c8020505203280b56445041d00c1c03203510708070031542d603c801581c400030700700941610111020303105407800c18203956803038802046900081000d9032240c2d1080005108021030350001c0d0040e100c0240c8042e05201007484044142d0ba041556184c3c070012045110380700150b581408061070100d43c4405406020005104c2c0c1308049100140b01a116250410b10000343c1110501c0070f54825036071040401c0d000070300454010319190300440c4402c11041008950b82459151005800f20500c20031a2400c5 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 634907086 1250 634905836 634905839
    0x40308030a0606030c0c021504080708030c06090705031207080d05010311040b060301050a030308091203160207060804020604030b06030a0c060c05010501080f03040302091e04030c031209080906070302010605090405030301 97
    0x10789030051001500f424034051110021040e000383c00c000c0510710003482110034554840300300164905580040510f001100d81a03035588110b1a200d038019002403003103001e984000f035042040083c0c1d42e0101d40026004090528440e6140703062a00801411101300c0c03020007408420b040103010f0a07010714080c28038200302c480c5000c200412505102a009e0048409100400040c0e40d100011001c0303c2d050308241801d80d80321110b0074203010300038480307405400c07000c0300380010340c0c802c0780c3c4030052071410f40c086801058940e00d040c4c461301000c80f0001e6128200300f009100091548407280d41202001d82120f030f50160b103590b0038038140c0319908544001030b40000300b070707042c484240074040c01041d032800500306039411810000d0702c9200d1400046e010b1204880030400080c091081810340030008406d0789000d0a191500421021140400b6400100b00c0c401e084640209840342e5840b0680c0183c0151808000c84148012500031940560544d5038801c40042c03282c89541c00144100d00ca00c018603503070b6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 634908336 1250 634907086 634907101
    0x70b072c030d0311090d0f050303040c0305061023041b08070e0d0b0a0504082206090b12041b030204061706090615061305120d08061504031b050604030803 68
    0x82c0880b11030340c007018140001020046510022108210001d03a03840320a010a070602030b146040642d40200107100c008100024020742c0d822480c190f0340b2800c180c80403500c40b40076800c80d100c0c03980140304104410406c1c191498600c040841445800079001184c600744c802c010a006241891a00000c200e045082000460344008078030824402148e001402c218142c851403150940100b00c42c1c640c036a1040402c0503c4946020340d031491a5128a40080c0000c030704901858030a1031140001103040e0140c003050a002620a6a030710901c0c1d5020400f1580d40c030784401e68108400d1440e881d06603a814001701c00358071140a01c5003e401303031907007c1560282e01a6081c2c946130004050040d5070300305030284466811404820140108125607080d241e1007000c0110b40310140c0c544c022603100c000b41050780801c42d004030b50b80910b0f82c4980c5580e1226940c400501222002c0c3c0c2c144403903004420070007030000444040350a007015403200041c140907510740c40410080e030f20641050300d0000d801700410506 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 634909586 1250 634908336 634908343
    0xc140a0e040e0a030512040c1205070503010c030c0e1003060b0c010b0a06020d020d050903030d020a11150921090907020304030501150e0a0b220b0f0603010605070b072c03 75
    0x7258548001d01c00541c01c0e1314000d02070300840c1a41048051180e0208080c400c5114105018102000c2c4085a603029890850394844944c07294038082d50030072152048040c007912941c0780c0542c0c0e585a034055000003030104030039580e810b01d129040c9a96030700e01103028694540540b100d85e062100000e030050944040081005056018508545c01003a040c00d005602003825010702a141c00c180303868038603500c0040d0540c00380e5508401010b1021800c822038541c0a04881e407110f01910954045d500300700300210a20408403040e841c0c507800290343e03680b2101c0503000501a001084c80041c28018050002280008151104030040c1d10125092003400400e100d0140c0c140c090000000410385040520b4070094002031021142c81d98440c2070402e1502c2d402004400c0c006d025001a69110580301c0840050240802c040d008240c2c44036620502d04042e801c890680e071241e00c41038100151656480c0701040300900074000c00a00390304100703d0008041446490030b01e056210f10742c64050100749840c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 634910836 1250 634909586 634909601
    0xc0c05061008060a06030302120c07180207060f0b09222a08060108060c160c0902041d1509090f0604050d0f0516120e06030a0c020618030d0c140a0e04 66
    0x90091905c0d1007000000d4001601915030281c202980b521080409011030070283c09a0100c0d040300401c6500c051503034215170050101c00d20a24003000369945a420f0b00049401000301d007038000a001300440c403504801ca5034200020310f454480c11080e4080ea41d410202c1c0321078085145e0001d09906c0398118032000107502e4000d020180006c1030191714014805a0b690406890102561070018100c01c494480b412140e21854002c194100e000d50350f001c1d090001c3d4018850761030019016095038210703007054031002d030040c44501130039200d40301281c0401c00361010191161440d0b10070354211069418061000d2072150380501c0191080118a0902901c1420ba940c80c07581005020000c00d1114500c08107c841002c0d0801046e4000b0140701c0002d40350a0448094103030f100c00080b041044d00800b581041c00360f088903909660854071441042c80c908880555020002d400c2440031904588a43d4852740c03507040580340c070107000000c160640c031196009609600010b111a05010360300e0429006424 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 634912086 1250 634910836 634910851
    0x1140402161a090622030c120801090c0309051e0c220b10020d11120705030706060b0702090109020a02011b030507022e0209040b04020f0a080a02070b0105040c0c0506100806 76
    0x3c0c0c030300301c4462101490301c1a203800b00045e000d000f44003070510070307100030301c50f160b00602c1a242c1b00031902c00a8078541c0240305000c801800d240000c08010300c13038022001d00a40c070500074018040044401068482d00001e03540c1c2a10881344d90000d181c6d9a0021501003030b030a01c256641c0c503100d0f05950419540349850050041040f89004148940c0c0000c1070002c1000340d10b00b0341c46440428120358102401c800400403555004603103501400008001055100e101703603020070a19030703142003202d0075000300a0042e600888440c010031000074150000c20002c0708510000034200e40c0900c0a00c8025154030250f00040d9891040189107501080341c807c60700748002c551107141504151130041c40034030814001c12281c0100300c013440c540301c03900010440c1c6002441135441d0315220701c070000e003904500b449800150611001c01c19201441c401c03125502d4001d0740030f81e001c0c0e00b0041840050803080040008101c3c551808801086e001c1c448a40240ea40c880301c01e1050307103403203113580c40e00b0006003112 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 634913336 1250 634912086 634912093
    0x9140909150403120f022811120d0e122529060a08031801020a080403060920030c010e22060807080f030301092f030106080705090901140402161a09 65
    0x44480c4a1000880100ca4944641190511005650454038401231f802ea1480b0352092403023204410100c40040d01e0502800305041081d0142c440005541333a58404407120005c1d000c000782c403041716501c2000000f49d40546111100180c06070b0b1600c1401240005c00000c540341024520020101d2998250300041c048a84951040c00d004003280c50340701340080c01282e2200f801001c21542d0083c00b001c26841d8204600700d45466690402c8000340141d00f500721490f0304540c002192400764118200b8091401030014442140e00c0001520208001100103500c108005040d0410869107001010b898503010070110b0f4544ca86030040d803501c102c5812080d0300741c2002c040314580150010035a41100c0c1100307004610b0311140301d1648000038001d170240d01400d9180ca1204e412074121001103049410565918949581d200c5c011121400f4a040c402da00036600b2004002910140c407000d001c0b084003e00041c40c01d64200a401c940d49441402152407400d074807103001d108001403605a0340700c81d41c140034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 634914586 1250 634913336 634913347
    0x6050105120a0509070e0c120601081012170310050f0d03051207051c06050109050f03030d0e0309220609180f03050d0c030e06010609140909150403120f02 68
    0xa2042100c000708088a525618000290345a404202c10f0b07005260030741900017107007444d15802d0001d520140680191600c40d4000c2040d9500c1030000510a181c2072841433546030074440e2038000c1c5042d03000d06071805c0c50403030341d03104902e0100e0f00294003504a0108000481d8070340030600c00ea420b044591544941044541c400c0030a41000448a184404c0b985020184d030707956205480a0094503022081400c20303195910301c22603144c0c0700c4411b0f50801d03200d03000d405540d1340400c240d032111107000c290103800c24040001c5032001604030800301c151510540381016402d101207580c42061601c41d003d454100d032450500d040c500c5c414980075140085007444100c81c00074010081d403800d04e1005242c4200c0d0349403079041c14492401d03200302e1004070105120300250444000c018040c91090003402e40210400003402601403075000701221a11018082071a408508000340560300030071000700d5014440060b015000b070816180d10981c4640c0b0744401a40e80f4503046421207018600010321117104204 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 634915836 1250 634914586 634914607
    0x1030f0b030a030e0301020c0a030c0c09021908070905030f07181109060a18030c0302030f0c0a060c080f07140f0a0302060408071b1829010e1f1206050105 68
    0x82c0a01c015406051180490400e030010070b009100d401d49204a42c000e040c2c4240401d540700c4103120529015807960320415807030b18541c008a120f121502900c1c10241c50344c80c40d5140c083c1c00ba55078051681c0c02d10080312543c4001007420900103c600030080e40100c08140000c0002c13204031600011803800400c094030074251480e015209280160b8464140880d0344c91000d4450030245840388511003044041503941d140485904c0ca16010407403182c0161445041c1000d000203009400300d00080402c0c1100349072020581d00c02d02c1416090b64501d204120311040300c4d441c0001096600c0c41071103607451900c4410072680c20704d02d00300c0e80da403020b0b0804255140400d50005440340c2040d000400b26540306014030b000c9002c0d14240e20203078501d01da2003900180500000240079190340c0240814400c8031a00c08451813811000c00808d840c1d01c074076076070b00503542d4441d861215040c14003030640c1d00c410301880305a05242c010042e40030002001c0c031807048618105406107100a15081c2400c1e41010030010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 634917086 1250 634915836 634915843
    0x100f050d0206031f060e18060108010302090c070506130606080708060a020d0b0409032c03100b030a15050402180c030a0b01180803120f010b04090905030d1a01030f0b03 74
    0x400703403260030040f02054050504070602e1003a0030503c0a1010b0050740ca80018248990b000a0301d031244280b991039051220181284c00d00c241030595405025030308640c208140040042e040301d000b21414016603001407410000180520742c044503e00c2034800c01c4c504003082e9085a0000c174410740041c6d03c20480301500064558004601003800341e114200c96071100c0080040003105940517092030041c2c024143c00403413016400211b5900c00142c81d461515030110007104c0c010540e0180c0c42502a9191004680c5c055011641d009080d1121001e0684030542e0030401c070340b406e20001d65264140300031460804002c1105414034903a45a55141c181c0c4040b101d030100034070381018540c441d0f2504005a1051881e08014031031a60955403241c3c8480899660b60040102c40c440d520000000c1441108140c0a0340c1c102d4281031b610314600360500c0f01c7ea801900c1d40c00807c60b00c0c0d00c024003000024500901448d10350440c41c56018808070185400181580c0e03480170554403d601d003a988001070344010 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 634918336 1250 634917086 634917109
    0x10612030c1b06260c0901032f0d0b01020a02060313050a0c0f05040506040b090621070b070201020c120d0507020d1e02100503151201020c010507020105100f05 70
    0x6041410345039556040c06207100301d44a60b21280c290700580080b812580141c181c407a08005103c4c40301c4050901555188200c600303a0f60041c4004042c000502170f503100e42c010003140325848500a558032525011781c4110401514507132006e01d00403c1e02100c584c1d11384500c0128903030900c024501c4502e6a00031800e60310016050504405900e11503009200d41000380f01501e590004045071030507036507090700c48851114000d0714401c2c3e0074080494128a0a8000c503101c195000b8010682e0391904400c01103000c40321851f505607202c0310f5000003032011092001000400c00d8095a6030350303440c45c0c0300080c10a1503a012a41c4101d088100ca02418040094000c80c4000681403541d0749111034000200c1044c4103030401005a04004e19901001d014035540c1d01c1c20500c00c0e1703030030400c080c0300401c00c0d5041d000c2107444100280e01600e01940500d4070250034500001c443d8001031a182c1c2d44514203082d5101106d10b203000d41c1d12030b0280116280302e051804010310f900701445030034034240b100082c1d0b0340c01103 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 634919586 1250 634918336 634918343
    0x120512210c120c0a11030403051c1b0c09061707030305031b16170c1c030603080d15270c0e1018270903030f2c010612 52
    0x900001503a6058841c049800b42c104001d4518458a03003084042d00340c1d80310b2402003000441030000214004000000e4409a0360b2100251200c40303410b180e07150218080c00032003410890901c0c40f18002010203c0310200490081d9031645070203082243e60f205848080d071207410b2011407140941c6802070080350000a4a6240c0340c55a542c0d200c00301004201e103880b1030164054200081c800d04e198203c03203642068142310704852040289000e0350000240102c0c945261140c2042e540e283c4250002268201d2074401030070300160081e120388072501181c010060050703803d0f41d16055440d24102a4090000402e0390120405004c200b20800e02c044d000a80e840000302902c0300040d11000b4060b55a070720070343c80301070304000c0c0f02034119034000c02d00807601d010125203440140c00494108100422418450300119040380c40c0100c600218009045290066041585d540c40c0c02c00e0b104128060800b803000c8200b840e11248964080340a20102d2445440f02240c0c90b003201040541c0b00040320908540c5c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 634920836 1250 634919586 634919647
    0x307090b0450151c060e100608040507031a070216060212180d0c060e0402030403140318010204140310090b0c03100815150a0e010b13080601120512 65
    0xe4000105400845540d00f403200c8142c0404c001c030800030310340344030540458990707020b1104131740d92040501c00030000d6442854040c00c0329414400d030390184003030640051082d01120130a580e03035100e03c44402c40c04000740011000c7e12040c4200c4030303810014010000d240340c0286600c00d00c1c00c04080d6940d03443e82c20b9282148008202034068400701c11800c03041c80009400754205ca0b1a6250200104680e8061400828203a0480d02c09a003418030a0706e1203980c0c161200210f080c8100000302c3c09810050101620442c2d01c2564110250207001620081c40c6443c0e60326019900a0201400c01d1a10750b0741d2039140340740412070b40c04074040b010103d40021002c0001560b90f291280c404644094130b4101c0650b5200d0075034040e10854403801c502d0310070201021034030600100e1350204403100c080b40c881c00381d40ca102c0c580184540d081d818000e10000301d40010b1910070594480c410350400d08242d0088040b490740108160031300c0300c05c0c001008002c0581c83d06600e841101d02c481e280550103180309600821 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 634922086 1250 634920836 634920989
    0x4150c030c020d082a0c070902030417120708090c0d060c020f01020f0301090b010c0c06020a1104090b15030a0605100e07110d0f0908010207062711060307090b04 71
    0x2c012000c41b141074081c00f040d904540d48490540e4003070340c81a102203c2070940800c0e4410001202001d4440c0d110181d8101d40940e00d8010741114002c0c0050700820441c001e4500f08100b0b0740e02d00d0255040789128040114814000c41030180c100b820700c06070403540e44d004112044100c82480104c0e4117441400d01c1c0010000508001202c81c2d4040c2940141100306601c800702d50260005505c03804544901e00c84d5400f03004420500054071180304006000c80c44850103d2142ea01e640902c01000c54050100c0d0031401850b10307000143e032000e07074010030409105902409488140c9052603444800e03070600542c0d0403c00b9551541d540f00d101102020094281c00501c0c183d40b094075110000c0c1700d82802591542d0b03290402000406420408258800c500354407403000c0222080407950490f040b4a004003082050130500c02c00ba40f00408035410400e401502090044181c1e008d8000b038400134106940c6e13840c506401c02c090000841c945400d00c6805501100385600744040c00301812144da1401407100e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 634923336 1250 634922086 634922161
    0x10510021507081009021602010c031b140610050a030b04080d0f02220b04060305090c180a050105030604080306040c0908030d0c02150408040e04150c030c020d08 71
    0x1805803100320001841941402042d43d8054100d502a540c400350a40b0816503414000d001c0340f141040e140c2c0710f080b60328101e0f0059800380e03070078035400750003800c003000e52904614440c880c0509007002200c02c1d200301171070048001e50801c24035500182451020103c541048001100c103441488002d049940007070000341049002001e841894000d5101841514403000c040300c0030350000080441040c64000d0783c0c400c06412a00d01c10102c5000d048c81900c2c186c24400214054000201118110f10134600d0102540d1a030380e0161210840c000e00c121101e007060101780d019070384181c2c032581c4284c1c0010180408a02001d048941044040b10001548998000156142c0c44158445060742c040401c80b085440e0194128011911480d4241c419010f1398144915419005482c0500809000c0c030080c00700310410350380180c0260140080b201020941c00a45064861040c20803001941722203245e020250104221312200440d400d03d00c00d103180c444000302c290b210742c22094510b081001c0c10403080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 634924586 1250 634923336 634923343
    0x904030c08161b0b1c0912210b0f0603130c03050c040606021b040b01230d11031b0d060503030f070b0c0c0d14090405040b06010905030309030601051002 67
    0x9660303010884585801402d0b8030030006041c40305054810303066942c082d20b000d43c91503100001355012aa211030030401c1240c01094140e038a03586441e80c6a5540003540040b8050f0b41000d0318480c215561004a00d040c8a641400307a1840f502c030400590511a0303e60b1180c0e900403182404c0c0741d054600d070b51695140e000c50300480c07140010240c03d08824030004401c3c48808106a2001a42520180301ca90b980d1442207a0f1070400108080c080b48540030002d62619103900142200740051410380f003071551101d01d19038801c00a00ca101d041c464001400d44901510380101079074425038040d207905601d01070442e413868004061200c02c80d02c00c0040c4008520107598484005820050103e94880c4030043c1c900c0d6182e4050030003510740a00e0780300029500111503040352030240d07480e4013a040596914100b0b4030102107144640d41402c40500c18000d4a840300e10401c0c0c441e5000310180e0013103051090002d4080c02241d080342c3d01a801c04c20184200ba10001801c40c11600c09845802106480d100100e04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 634925836 1250 634924586 634924607
    0x7030c020d1113050402040c0c0218070507080309060603011505180405011104060c0b0109200f04090c170601030b06091c02040903021c09030f06021e0a171005030c090403 75
    0x380030030b074050b00da64000f00b181d0086106520070384d005c20030100c2000c0261a121078907a8004d602511500140060104030301185400808a040607801c03e102c59595031030b5600216140c50040d0b01610400200d881c090084001040180c00c0c94141903003850080f6699000c1c001d90070034050403500107d02000300941c0100c507920415012070391596203e500c01480c01050303220945002c0c44110020454900501c6808085505621455079000f4918441e100e581c01030003c12a0801e4248000500b80d5401c2c003542074030a01c140c0e01c45c14a41100480041170380d1010f4903050403d0301d480d449003803d0301c5100c00c40d181c555044444c2941015441c851003110001560001c0d0070134203040d1814100354000620000c00300c903910310401d032081a0b072412910743e00b00d444080c0600c0c50341902107000c42d580354011f0429000d04038807aa0700c042c0051a680036680a8281080040d814060054508540c0202182c0000d944600f40100078034104c00280d0754102120101d02c2040540003180c1094016582c40c0b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 634927086 1250 634925836 634925839
    0x2071430160c09060303090f061b050a0215070308090d050301090b0a05101701270b0d05070303050408150108070902030618160e030a030207060e0d021306051507030c020d11 76
    0x1000b00c0c2c3c031803043c0d030041d020520046000c03555410002c03520710220f000300d0702580c45036a190f803054121034001c259204607488050b40d640c01024001c0000d80c0b1854400c48030001010045690355080c0e00d0028002940200480502d4005508982c0c40311b0307212007164111045214082118490f003c0061603001295120951242c01307003200516298100c0c01e8074407600045401d0802c1c41e0f9030341c1114111600200340030000d440502c0f4001015119aa01104c00804050300341c4905480c6039464a24000381500250003150000c502007040c080c1c100189100041110340c8070707141e545410042e555449580c09141c2c0c03103a4005c400201c0740d4542c09000544004004402c046500309406d11720001c240e8881d036900015100294000c8906000a070304c1a8650705078001c100705407410b00c0403100f06045030460f6074041c001d80c0c880030140c5d03103010b000c6031024000340340050258900401c0014807203c000c010b12182400340184404650859491a400b50701030710145c509109911b054100b510301c0d2074485 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 634928336 1250 634927086 634927103
    0x102070801023408040302010302030c040902030f04021309050303041518080c010c0c032c040903200703080706020310180507020c06030108031e0c010207143016 71
    0x701030340c00e00000d44042c506101c0586000b05940d0300c00781d99090080340004d02981410002080103501c240d0007154410000481c0a041c15240c0803424240d920986d401142024100244406e40c44d102c2800c90f0341c40c440142c1008040b205039511612804010000352406000c031265001d0703104583c101c0303941810f03900c00745c40035019035280048003134000600c0040c40358600104001d03000d0280444100080d01034941c0706d54515480c00030700c00c4882054a03032000e00f00410780210941c40f10b0254000c207601c03a4848003100441ca10180320380b00c011000311045648298000c00105000740100c0c0d500036082840541e03290385034a14461640840c1d409842c40700c04120284094420640c030550242c2d4045d4280c2d411110484100091800280150384154000f0003414128400b810f5007043c4d130141c42e80b8a03504101d0000740175800c903002410306542209100d101102040000c1c000c0c003d500d00c03062180050145000491060003134406100c8540707500c001111310103135410318040500c203540203101 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 634929586 1250 634928336 634928347
    0x9090c1d040c06020d0c12020c060f070b220f050c060318010b04051504151d01150239120f0f0a05060606070206040906080304180b0108070806010207080102 69
    0x80c0c40c04003411107041c1c580a885071008256580b004c9000d000010b00c5030788032540c4040540350b60116002c504040c03070561207a0704040445844450180c000440d10600b065121581820079261501e001821303480f090320903002da0f6649505100c5060010750b001060343d5540c0d019444c085144c000c2c10704056078400710100820841c20480111000802d44100003800108510001c1c0030070b90300103892014072000307013001c4000306040c5544207000072601240d0001c2c400c1d03550180d82c1e0f1004903000f2040a0080841c0c0141700c1c54000f0342c03005000006a2004104107440c0d0348141404203140c0c1c03030b009050010252000d0502c103807050445400d610040c0b4100c4010707046003100c1d503280308010504106004500783c490b140b00d07003c6145c44c0c5007500100a041540d580d8000c10415603c541c80403030344560300b4080031480c0c0105114100107800c1038001169205d0070311200e15080d00300c1d0103a141d1320301e082900c48140b50368001243c41c0c0048041c2890800e588940c80140e0500070540c00c0350000d588080340 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 634930836 1250 634929586 634929629
    0x6140417121606060501020c180a02040e01030809010305160c021c0b09060f0c0403030207140d050321011a09040b0616061406181803070b04030305042a09090c 70
    0x40319003010f8072540e8200060740c1d5480040e03880e00d02d040601a48000701600550780c1c83c03504111103600c803000c900018036194450903c00c0c9142003c0e042551021004281c2454035600751080301e0700f240f9aa0404c0030100c1989600030054130390504028041d1505482d0304e02d040c010300c0407100d165984001110160300e0255040390b50307210100c0c4c0e00c0d4216407048011440d0070002d10200c4007a281c26030b000d403a040b410100040300c3c03545868001c541110040001d200403400c01c0c40605079000c1046c00d5022141c00f1088e5071951680180c0113200c60031194034041883c7c244d00012201c2041c82a60b001c280284104002111800384a90b2964120b160301c0e404d40400140d035210781ca00b10107007100c180702500c840707041c0000c004450104424a4040c0004102d1b40715070a4400d04688850104480c90310265941d480028002920f0440100352a8001e100410005804201d000582e46401001519910110501c40051482080301d12550341c0d400505010320b03106c4000107080801c0141068400ca502d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 634932086 1250 634930836 634930867
    0x904080904061208090a060e06181203040816060306060f12090b0a06050405130206160807060903080106031b02120a0905060a020309011209050a12050c010e010507090614041712 78
    0x9040c0d1040b41d004101080d0a03002c0c0e249448c8800018040c50300f480c0c540345032141c09da00070b07030101640a0420001690002c204200400c0078210003405080b80c0841e45440350841469600490245420000280211940b152004894400320b15200b44c1c15000b9100300001000c0606010b01040c070340c03404006402680750031110481c0d80503202000300f9a140d03000e00190340d00e90100294404400c00c012416021101c0c800181c59018242e02481c003021640c40c1030032608004421030124900000410840e5098401c104040850301408a140312424400948400c1071080748482084007184444100748100b42e0070006c2c1c130000e02029a9118200340c040d41e80c0d00012610780c00202e4406100103407603814014250559400b9008012002c1c5030340d07484c1c1c8072400340404102009010300c00d02c4a6107409000d13081c40741e02c480b00001998140f40c04010140c082c15082001401201141c1889850f009012101255030088410b0341c000c00c500d44803800d04115807955001c031000030078041c00a01c3c042 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 634933336 1250 634932086 634932097
    0x51603031b080c03010506030402060f03100509060d02010f0807021905100b2706040209040c0917030f03161b050321221104110301050316050904080904061208 70
    0x401d03a5a420700300e000110b070140012101c05801840c28801002242482809190024402047e00b402d03c000a10301e2201390708200d8800e030000c03107100f008200608203000b04540000003540c8c2c40070ba030355050b00041c0084103030b011640108006000000c0742c0350701c01c2c071155000c41d82c10311102d91100c029040031030740c0e075010720042d150407441c000484010f0720703207a00c560820b10b8050350300e2102950741c4105100b034410010415500b050f000c0219030005d0755144107170034841206440700a006424040054402d1140e01030380310345540100a5480548000c005882d4841e107804080c100c48220100219140200740b03082d2404141c107582c85000300300001c4043e0042d0b201000303a10407135032000000080c103c030042c1d032103490481500b04280c0444075811000010a8069010120880100d0020030215041c0c40d0710103a4a0f10080014807040c901801401d02d0032001141d0b40c6441401e001c00641d4030b0364040c00007080d0484c0050f0884440d107558210b10010203d5502804500549081c14403150f40031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 634934586 1250 634933336 634933361
    0x603130c15050c070b0307090e0901090204020c0d0e0103110d090f08070503042108030a0b150a03091502040608060112110a08070e09040b13060e010606020d0801061e03090305160303 80
    0x18072801040300e14a22046d02d1042c41c0741d0303903048101854001c50041d1010082c0c00500255241c2801ca80941c54600080c0079402c041d02c000c3c0314004a0250080c404844000d400381050709024407200451035050a43d14851400100001d026219203006583d01501500c0200842004104102408030100161048807803542216a99100221090f8101001244010280310b818004035082d420640c1c07041905c480040d01644861201a040109a40018203184002915007031407000f003111081c0000000c2c0700a10055050900709003002c1c20250004003501d0401c00441d0a954604000e40c10204219404a00351030740e8907400100200101d030b00301e8480020540140d000d0700603081003a80503101c1c0307400490300c032610b484404196207061682541665002d844298038122800d081c0300f01c000a184a8004002020303e401000e44040d0050388003070140480100348012800a810300f10701205101c0c5000540820140f8045d10507020f28050300c200c901d480c5003030b102059019440069507018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 634935836 1250 634934586 634934593
    0x81f170a1b05010f0c1214090a030c140d0f03030c12020d0603020a050d0c09020c01060b03130606051e060702010c0f0302070801060801181b0513051506090603130c15050c 75
    0xa04c00c0e50503c81564008207101855030007281d0080c400c2e41e440321807480f030390760340d5150034000780000702d00d4415604150ba0001480404000b00600d080011116110503900e000200142d5114076607036420b0514058145512081022040d603c5018440080c15280d0411500d030420102e0020045c031150104900131240124082000d1410341502200329611a0402101504111451000c2d400a401d1010707a5900c4040208104200a01a5104000d10b428401d0714640c21301782007090300c8044c0d000ba405400900902110400d000120f1980c894040d900c0668031220f030b01c01251542045000505201c0c59034030b1b01d0041582c0411454200c0b605c6a0082c00003130b4540480303500329043e070110310403001031101e0354000082150240303600252031420305061550359070020900d200c22944804000c15500c0e4200207110070366441ea150340d8403094881d0342c01c149100020a03418400600b11440d6042a2074005041280b4031800c000941460145520b0300818030201611503003201080f18018003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 634937086 1250 634935836 634935857
    0xf0302030d051614030c1f0f0c0203030a0903050d09030804030e0924120106060507050f19080c0f010c0507020f0405040201080c0a0519050a081f170a1b0501 69
    0xe20034030039148801d107018005409641c959030351000007150380c001084a1302086c03000e403900200a0128401c07650030613080c3c0f0b104c0200111464202c1c3d8103400281d102c2454444079101320f44d800030681341e10598210002420800310700701a1494019070184507166410205191704040d0301c50110350113144682c071160b0030f95500c0c0040000d0214100d9444400b06074460845d01c03001120818145094009400030441c040c05014050a540c41a0000d070b022850010f01041000420880080d0b809a8a005400104214603180d140200021741c003400c10100812130118100d02441a000500c007880c008000351080d0000c00f820503005032100343e20800d001d0025074110300301406442d00c00c40e03050351800000d664112002d80c0ca40c00c0340b0036101c1017040520030402d00711300c00c22058040c0c58554a502d030702c688003250000c00040000b0014061402d402c041c0718200404007060009940d113103642500b0704600d940502c2d00c1c2885819001e04213080c02240e00c0703401c809078004401030740d6003a6264a15507 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 634938336 1250 634937086 634937113
    0x4120b13080d0b09060d17070f02100306030212060103080a0807051b1b061608130e010f0e0106020c0a090e280507080601141003060e0a14090a0c030209040206040f0f030203 76
    0x440c450301004e840d110101f5807031024540400e00030039180d4490002d8190aa545401080100040001460110382e81c1d20b428000c1d4548030040541068500004050540c1140c1e64419140a10036009040c000c098002c00d691a002d00c0603a11070011036038009a1800404449a035a041210801c00422802418800d4603041140880329803c0c544200e091440781c06035540c11480d405505030b40a12100c0c2d010102d00640341903e02d50007014054010002c1c1030130070602ca5901c1906a1000301550b020040f1000b07540c035201c500c20119600800000740d200c00c0c0140c00c50501d4070110149800304081c402818140e50300d11400700c165805030044514158036400000d540d003500b8058009420000400a40242f4101d20030000d006032518001c1092039843da45e190942205070313000c3300d42e83c0d29070f264001e40d0300b040c005c9294006029001421100880c1d01c800c00030b00060700000c1c0c0181c4100c0001410b6407140012100140341450403800743c140e40b0391860030301c6007042c042242329014403620340100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 634939586 1250 634938336 634938349
    0x150218091b030c03061903030206040b0c0301060f18350a02030307150216050c010206090c010507020d05010b032506031e0b0103091410050c04120b13080d0b0906 71
    0x15001a148040d10b50b890f8030b110840c164100400c8103601403044808440444581c881c4503000f10301c283c005100c80c0c205854200d030400401008200420b205000421009030700941d08a03030790100381800c4801c03103885862071b4503800740d581104d8a240901c1d034192580c0c00481101880e12603012803c0007410708502c501a8449500801c041d6060388280295070124010b010712034010301c2810070051901045410910102022820661b2326800c00a203d650658040c03002ea6032140448000e80103890309440064146e00494201901807151819544100482507020315030350307a801022039000c2c1303c12080c070030306c6049865a80390480b00c0380310f00010090f0180c054103d112680d61160301c2a051245050801400300309052410142c640f08620085205030300c080083c24040302c0138000505a403c000b00a8890181c5624600c20701040704206144289075441713280e550080c1c6155103500c0c5c0321814003c0da43e0003900a080e9440010b242d400d11503945d030110719500e506591582050342c5441c1081704 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 634940836 1250 634939586 634939621
    0x102150c090112090b0a0204060e0a05130908040f120212060705030c0d0f0504111c080a0f0908070b03160206040312110d020f0c1203041104050415021809 68
    0x348400510031021298007a1600b00200b0311400c00c00100e80280741c4134804140743c15902c0e031115983c009400e016060b40310f01a0304075031206940140e9a5403816000c1000c052941e01c042c07c0300d9035513080c00f00800c100e0104079001800180e40f1007018a8540f10700307191031244002d04a203c2c0b03849a0800806c0080403d40a120340355940307c030750a503038904000d030340760b580030f224482c00903542e03204240348070381071031280900403406492007060030303401101400310056169032041c4140110681090000d40014101d80404240d0b01e08000c481c0240c810646810100b40c11080150080c0c900104400302840080c4d442040e00d203a1100b58582c0c600f4040e41c8504003a54043d00003800042119a003c0f200d0f004005001c0001c086540b51059211820b422030b045800c824590401c0014054a01ca00402c42d004450281d50407044c41c6050503510b081c0d1002c0120282e0307000710307140d200040c00e0212032a4048c02440860005641e2035260000644919110a42c5984a101103002040c02c90300140c03043c04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 634942086 1250 634940836 634940851
    0x1e0606030c020a0c1214030307021f0e061b090604030602031e0402060306190803180405010503060105011d1518090c040f03080d0b04020c1614060417010920010215 72
    0x1e880e0360a0614030801001a208180c0d00404202c248070084c2e2401c10023540b041100d076024001c0d9840c0b51659040d2100800030700e1641c5814103841280a10000c01c4540d08000310750000341c1c01845900345e14085005a28040ea0710040c0410004207004082d002907101d00a5400480201c001c1c0404a003a0528241ca010350442c03024070008000d41003120020b1586004030340301107100c0e640d1340030700b6142d40c1c010724800c0d02d802c1280302c1442c05400c0600a003030150404902601842d07040400082060b030b00b400004041c080d84500d560500d46401614101c0076800d060702d141e0320602ca80306d4940d120000500c19024004c45000560b2804041c0159029200410602c2e03003010310f15102c2100c2500604400c42915039104201070043e41c80d032004040791552540139001002e552015490b0318002030b0b01c581c0d07040c5000d0003400781a65490003180c0546a02a80013a03c4070709008103540101161344008014076140c9088001010071f024640d510300303e09074201d440c6031100303181da414160310070b0381d295 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 634943336 1250 634942086 634942103
    0xc031209110402091f0504030c09020c28021c050d08060f060903011d060108160f091e0e1f0b0a030609052a0a050d0302060109020d1e0606030c020a 65
    0x5081c1d80c9071a400801c49008003c2a80300100980c00340c10341c5841c018440180440d0300000d0400c10084d500350403000400010400310b04004407170000c2622030343d0320002010900e28050003403007010070808c91100403e4000e007065220aa80c010310b98510001d00c801a1014461800c50110392481450018811000903005003c81c280080c00d00c89180c0286100541c15500d0b03203010500d004200c000c4c003284103200c8004220310752402c2c01726414610064200500804840e0050144414103c0440100d43c100b042c00584070320203444805440034296001001c032402e24a8408070428000380801c240400c0e8580a0300c140b994034030f0441150003d020240c1c0100b4444003c001049050b803080c00210b009806072402c07002100c812a2424000c1e00003902030461b041c00c20a03e504050040c040501011ba902c91803400c03450700d01941c4c5900c1441004c1c1c00e02d400050b40c4401348480d03080041c40b0f42c00148003820040384510320201810150041d02c00003880c00300c00d0b064a80c4005880d00b034503500900745 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 634944586 1250 634943336 634943363
    0x50109140601170921031e01080309060304150203091c051e030702070b030906101508150a260d0513060305092a190807090915020a0c031209 62
    0x58680c0b600f8010301e031030002e0050000001300710394141d019171811545420215076901e06141e840c405202d054405443d0180d043c4010b1198920000450f0103111048034405d4582c3d0300c524003809503419445141c180f4a0010080c4030040100180d5030317082100d214808001c00e4003c0c0380491b41030003402c44198410060b151412094100100115003014403441590500383c2c44a40000303490740305864502040d4012400c0080c01d0403c0d070035120150202c2400300c91655010000140540009041032054130a034000d410703560759a18400400a003a208465001500c10425419071010340100e450114010300384a142e20b144241c046070045018920700f5024203081c030700100c008103401042113a42d8402d8523901c0405020207104424040220500d0325107003001001880400e040502c8060145040c4141c1403044000c00f00c2c42900750340c4400030001c0c00f5001414100d2001403003408102c901c41c030000300001c01603409000c20b40024000e8030740c1c03008407409482c1c95044800310200a00092030941e035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 634945836 1250 634944586 634944617
    0x6010207122909160b030708060f090703021b0a051203070c0b01090c020d020a08190507061104080d02030c03071e0506100501030b09040b070e0a0f060201050109140601 74
    0x2440c0c510302035500d0403090004419550202a01d4a102c98101c5403450200034002c141040298942d04400038034074203032850030070111700502015050f43c041c09a4003000415981311000c4d46009103000402006032030500c601701a0003075000c940a41c010525010150225550004403403d01175401001049031005c00112695140c002034040410420b51070108001714440d006064081c100e80140002c810054403400b03842c0004149040c0700b50341007000d0391004544500706403a44000100035065a49014150446075481b902a009100307503c0c0609045403005108003410540700910111084c000e50618107070ba483c0a0b004810303403140e00803c104000240204102c4050220082000801110698403142001c1c0125444010142d4402c01003040d9a41405411032054050702c1c40605070405841d09900b03200f00030165001e002d00880c0084042c0c031740b03105260040c400101e40304200d540787c81000380070300350a120706035400c1e00707000b2003018500e4032102d041c4c01084143c4035150460841c0d003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 634947086 1250 634945836 634945859
    0x1b06020a05330a06050405090d08181207050102040e1b190c021f140f03010311030a0209010f080607030e031c02041502160e060102100b13090503090405010e06010207 73
    0x940e2119a00c0d1070b03620004515000c0034070300034119100c0101d400c6080030180400c07203030018203946081e4041e1007100340483e000309509030054103c14170b40810500c600507081c0b504000c0f000c00c80e01c0030b60014040d402e0010640c0900243c6200011000c1d5035103a000b00619604900d100340c09803101d040025400c0400c0c824222403e540c13203410002e28201050300040c2c0c80c0542f9000f0907100c00542c11804a140b5481102182c01480c0b4100550400c60301d8000d805d41400140402007000c01040d00350702455804000403840143d00034800759003076844245000c100b4401c0e2054140f00d124070700c04503a03074900900960010310210310040d801d01413461010200700c0c4415001301d441c01d50810010460003511860111112943d07002013500510440582c08081c4544d440300229680307205c1404940c0c1c0c0c2c0403482c2204a584100042020000c10002401d000203403411094400c0c90408031404000000c00900305607035088030108000e80c0d958111408841044031100d0042e0400b4000340400c1201a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 634948336 1250 634947086 634947133
    0x5040605011209030c02090910060906060e040f02160c0e0a02093d090f1502071a16060501030201110c03071502070e1816050a060c0203030d091b06020a05 68
    0x2d1400200c201703485d40101d01204010381e49144d00360031002401441c1981ea000e403400500610300100041071400c1070043c4244801c100303003803055860b407982111106d15034040d6140e80c0c80080359001180200d260131414609144904c0d060401c8100008484007068802c1c0c404080014044140000200b40f035010106a44070754503c8c042c101001c5009204590300c0080316009242c2c03540750500303003000d41104041565500840d580c15100c1c190208056000c204001118200c8081c28400c1c41c1071780c0c0002c0ca50107003050f54034200d17a010304000240000303500410304a900030b8840ca0801c1110200c3c054a9000401541e509640030510410040544c0411059042460710503100c44680390400204202c0741034034404404120b140144c94500000e00084c41d00a82c24900304419500d40f002041020590344a090305102c94202c0c0901591414401c603001980204401c00c02c01040d4500b444c0c10059103020482d00f41180c100c08540f082c0005121440c481c0c1140c000c0040400183c005901000e03034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 634949586 1250 634948336 634948343
    0xe0408120c09041d030711030a0f0503120a020304050604031b0501090f0b010f0303021506040603120207170f060f0403091707060305071b060b061303110a05040605011209 75
    0x40095481000062461500446121452696400140e0100300c151101380819019003213100200c0c0000c07501c0041281c0c02c1660150742501c40c00c82c3e010001e420003c0018020b000c500340c2e5006801000300c003000a0180102c6581081c50030740b18640424128041200c0040c0a640502d0101d00441d006a03200302c084c602031404024042e0a0b0f588850a5640b007207003c45020404150003010440080c150700c0c0903210001a036101103140da240255100c5c40300e507110710b0901341310001c90403544454121a0255802030505960040d0440c0000c2d90b84009120700b0304286000c90b540f030040328000c5450600320301400d0080c41103803074030503901c0550345001e0402c406010303000000040303004180769041d5901401ca406044160718001002c1d045c0d40000344040100302e21003129081401058203a04042c40d0068400218010b0744d50205001e0322802e8880d03001d408014500104001e4120f11415070304800f65206480a039640c4107210a54696004281c0801e000b00100c00b400c0e000c603407003200001e01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 634950836 1250 634949586 634949603
    0x4030b1023210102030a05060d1203050c0702150a03110405010e040b04061a041806150513170a0201110c0306011809060c030f0b1504090c090e010603020705061e010e04 74
    0x402c0b4003030b01d03298081d06030307500c0c594020082051242180c400c842e4000350a44007a88581c0071944c5000d03c00884003108000d040d515000705c4c4541ca0503805649045038050004100628080040540e40e04910701d96400039040c03031041007010082000355170032240b06850b0800034100010401001d01054480b540d00b0558640c800240c8260401c01c1c0e00c0d2108502502c282c0c1d4038100580c05152030010750f14001d113541821410801c2006071460300944e03110a150081d01c803440304030498134009403070b44003080c1e4003480090107a95440c00304070094454801d8031428000040c0000710794648000740d481c2d540c0b5030050340041103240001050242c207080000030009011403250740b08002c9502405070000000d0b911100841c0c203e00611680580f002c048541104480c90185503205505c13603402103010454964425041c828002d6075403c0c041c15103052007803410740c0c440c42c0003402900203040070303a5075202c3c8502041079030740e16000b0f80100302901580d03810168208208164905c0c0c010313204440030503 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 634952086 1250 634950836 634950859
    0x60f0d02012f070b1e03060a03080c010b030d030c0207060903120810080a0c0515120a0e031e0702010314010e010909080903030304061407050c06060d020a1a04030b1023 74
    0x82c0501845010b8001d00c28a0350311145c50107804aa68184a0801102101c0420600409985030180740048a510941e06a41d8001d094085805819030300b03845a0148510802e001c42a41c05400c03041500b002c503802c4441d056075900c1c00b01c0b08030110b840050980c01041988413141c0d44208202c5a20081014040d800710b03035200c104038602156044195103403854000203000c140b4000c200c0c004001300d42c480c0942003100e0001160f0900101610102c4d503141e441a0003000810140140c5031328040803032101c441d40705281026102540540030490002c2d20300000c41c00009034512809050310800c8400c2031450b800e15803c0d10003480302c0c04c4281c2e2084014880c0c102181d5041004510440c8660070110f802d4071080c0c0040210302010b4001828000d0600c1048003010000a107030390b011200b2194440c1e42c10242c00031030349418898000b0941c0d04425072800a00c1c94081c401841242d1040c41c6205c60790b91008020351034081c181c01041601d00201c030395140402c4400c0311509903250001c01c00c004d00c5 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 634953336 1250 634952086 634952177
    0x10c0b0a0b0d14010222080c100e03011d0d08070c0809030319030e0d0e0102030921060106110d14030c0d060f120c0e010e13031202070803060f0d0201 66
    0x261000d0210f5801a900060700c1b100800d08096580c16a040014819038010300b065106500d550b0400d81c0395015400c083c0b135000b8210f01c503800c081c140090282c000c10800c01340c100101890350b100e0700741c08200d1044c5510600301d0b500c143c1c0031506c034013281e81c4c030f051800f0309998660b0020b138000b141c065414071042c4211450000800c3e44940110070949002445040241040d0304043c03081202c0803d12440403510410b0b41d03000300441304d000e081290840302000010a400d141c840c020014142144901c02c008a0320300c1d085910002c030810080c0403a54071200d0074130212070341030581e414040d4145080c004240b152040d000030300301000310301001007202d9440310001c004005540e40041002c04080414070300380b2540c1250200540807009080c1c90b69030500c0006600c5440c0980700b88882010110721400349031040c03030048004450340070b0070b56480c41c140c24500116001642c1d402c1c840e901e03200403640b0710702d8581000f0304040c0e03045c0c4030300b00040c0c00c181c2004486c0045015450850000d15040f2061 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 634954586 1250 634953336 634953353
    0x804080705071410021f0e010e0613020a08060105010909021c1a0111010b0616030c0602040b0d18110111071706090d18050f131514010c0b0a0b0d 64
    0x50640d40700c0d40e4000c01d03e20340800607410718040003e020364005540c549007110003601c007001c1018030b00c080420342940381d5000f00d0051004040301c00c40e602642b02440310303040051800e020000e0003101d103000c10301d40707a0680d142c56440a200302e41c01303e101000304001814141e00039010304100100a0141200c0e0102e44400780d80300284a841140e4a0365001403156801180800c2c0443c0302800030400c800c10b840105040f031062444c2c1604e02d0f10860601010180302d41c600040e0550720031025074417160385040390342194014111001300e03142040b500b80c5171841c0c1c0725543c240f19a000030103031031401e05480055500b04c0c0040c645101902a1942c04116050401d85620580d409007006040303d16141992905250b010380402041106001507140080942c406220035a03104840784c41180c1c88000010700e500740c0030140c088035a4144204920031002c200800000c030b0314441c652401441c00d00004650582c890344008060505010206020303c0581d4842d02c0e01c101c019000700341d501c0881d19407564 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 634955836 1250 634954586 634954589
    0x1503060e0f010c2f070b04090209040b010e241b0a0606050a08070312021504030f0201060b030606040b2a0a0302010c0e01090303030c0923041d0d080408070507 70
    0x840c1d00c180e20306580c980c001d20440c03000208600d04000c0c442070220107140080403042d041c100300441510722540725007007846900e00600354003220694582d680d10341c4001a42003c2c0500344602d20341078074641994042d007c06a41030700010541000e5008000313619090740ca940c0794008a00b4020701c00c40403030303903100480030042110100003000b00c1ca42c6880d0070020b0b54481c1c2c0040e409189010740801c450000000e0700002d0329440344052502c1ca1501c14124909880c550641008800c19810302042c103411210590f0540d01540c003d12401391182000c01c200e1209640f10f6400c003608120801a041200d000750a500400580d801d00c0401c526851056040c0c0340d810498441d0491034240c1c0c01c041d024031411030349104030305242d007c81e0310080000c1c009908030704c00902410380755481c540b4810b119000010107401c400e20f203c026201d440c04031a1948019400d0a8000c61500c3d100b1050142c0450021031000c420400500c2d82071800c0c80c0841e000c2c00054001c80b203a03041402a80005481800200c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 634957086 1250 634955836 634955861
    0x7121209151e0204060c03121401030f050f01270201050c030301090615110307022b060c02010f0e0d0f020a15050a0606110a110a1a131d0604150306 65
    0x2d002190072010424041e0500108a02c203881000f08018030350f00001d100c0c0d0320ba40c2604208040061008121014122500080000d405140004000c0140f8030b020011032078040c0e021034007217140b140001802c070f07640000003000d043c004540c2030b144c0d146422001f448451041c0360485c1420150b00707950749075802c01c1e0000806543c8a503414849600100640040c80e4564a40400a0383c040d0781307520f80324451804082e0203480002c0c2490b0710300c0f808800f901c86a81d000d210907243c8003030505001d8006c0440c0e44550006509151000003c460240582c51500104101400c0290300c5802c040d60300a9050314400e055024000f50140806e42c0c50340e840244c04107019004c03449290034000300084543d260092814012104074221205c1d00006001580781c0c0d0010040e00951109000203400b4001e540c05002e101081002c4003400100880c0a0480ea4600300704203410b541d2078201c03951004540e2038601d15490707444400206503281c036030004440560071100d8000004d03141d0f1514400e5070140302450 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 634958336 1250 634957086 634957091
    0x31b011514150c0c032107020f120a0f030201060f061b0501150902181008060904051f2717130512030304030206180c011d0901080f0f01020712120915 66
    0x2e84c0b0704040c02040290740c01059542c40c0340110300b11700e5501c0d0040c048080d0203162140d10348480e545172400d5141c0c0d8406038804540286035945080b6200c858900d40c210019403c1200002c1ca10b030303505039460706640d440c0c3c0710980040c8010110040003074804401340c8047d03407503981d010032410a00f8000c00240000e1b00c0701507a14622102000074600c0748454031030040d5030fa40d400b0840203600160080e003001d0220380c40c1c0895250307030500c0c500d090303104080c2e028128487c0c648942d500c0b4503503008400481c5501ca011016482185446244480c889805044d1030100382d801c120441e1280020300000b00050b042815090300ca40115085c10b03245043c10515a00c00000d020900d40c040040b075030b0001c84104815444041c2c8643d450712031005118850501803c1408241c0200b40d410050041090142c03031005250381d40d4070075568584a4500021740c40c001c141200c011228180201c035083d9402801d008049941c901c1d04a0f908e40003100d25800d0303d0b699034020000140007400484161500213800f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 634959586 1250 634958336 634958353
    0x90c0301060215061c030c0210050c07050301020705030901110f0604060f0516050d1e0203090105040c0e04030f1d180601090605070c06140c0a05031b011514150c 71
    0x30b440c3c2030621801079840322000d000c010b440e80d240407200781007030312918918078120068034007039031031007801c500096020303942c2c5018428460744100a40002c468000803a100255628203040c200e01c5260405000c58204009012965020300450f40c010304c00031045407100b095440da000d0908005440c2218155100c0304100b00b11030301070241c1500924071000780c0c24081e90101e00900248642012601d0302512200582018103c80c001c4d4807070811100825580c920b86403030258000d01080324101c422a04440780403501e015400e9249204a40c162107070b003080001480203a51002c08215401450400fa105000c1d03180c503810820301d640389412240f43c80c64103000e4005411300341d0355080f080411005004040101c0c03a040695001c90318039082c01031031108924020b403058414109403000ca88a40710040e03040000000040901d812200b515034100c85011040a007030b2460340e440940a42c99000c010320169041c410b4884059a00900102c00030580000b0105582c0085812003480d4203e11070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 634960836 1250 634959586 634959599
    0x25060902010806030f100f02090402040b1b12220305030c070501091406040b1e0f0705100605130f0e1b090f040503030114030106050d110a0b090f06030c0405090c0301 73
    0x40b41034014100300c001d403408485501d8215031340c411820340e8002d2240c50f80d140d801d2106090381180c952030030207042595680e07243c003290385c29175000400721001183e0703907440107601d10408105554401d290058052500b6110f1142100702c941072101c507524002828000070024400b00014035200090501400d200e40c0b420b80090040c201a03480001e0501072010041c60030342d214021101941c2c54041a2500e5144848801e0540d028615994182850000754050705209140183c01180e10840c100c0d205204010682400d9030081e01c5140c0c2c102501682e0708020304c149400461a0300c6c4442c000040c629180c1c41813a02c0e01405c000350504411013800c85806509214044540c4480c414074500c60b0380c10180d980958900c0140f00c0d601411a402ca401201d540d001c0d0400401040700803c0120000b1440c01c1100c081c19000b030280d40300c1d0f1020100081c844018405440030103400404d801c404c070059000344032280d40003c25286800c00100030110b00c0750f46001429010388051110151298100320 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 634962086 1250 634960836 634960847
    0x4090f0911010912200901260a02060703050307033305041512080405040c0306170d0e0123030109023411130e0606040b0114040b2506090201 62
    0xc4400c2c1084000e8100b0b00868a08004d0209000c0e480940030411159102000480032213281384168000030380390001804000c02448001d00164024003c0402003080054a940d550003501c0207410480900030100484d000b000070f540e00440d40d007804100c5000138031b4a021840801103040901070000d103981542c0441041c41d08025002c1944c04200242d98507000c00640e5a044c4500c580480d0000d5042040004401c01d4400400c0040c0081c480c0068150003c0d0180c495130140407012182c41c44030502142001500200422043e00c80c808941c1441e0f004442d84400c0c0907840488402006082c00d128081800a500903c604800161202850b64614248656201c89031001c615030325814402001d209400c01c0340150f00c00c1808600300c4a150110314801c07200100740c8002440d10b012458500c4000c190144902401c503800c11452704200010345138600820001c0c032100f0000e100c140311140d1041e009101031621300c244130540920f48c04090018441140c0c080711100c1d140c1d00004210358115 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 634963336 1250 634962086 634962113
    0xf0515160908010501121205120406050103060b010c0218070e0a0f08070f030b07030f090f200d0809040902040902150d060b09090a090309080a05060105150909071404090f09 76
    0x2c0284100d5140103901c82441c4c0c031141d40035184032403441c6240c0c49940900111160118050680501c80c5414241400245402d100076200d442c2058000d80386d0f9840b90f00a1500e00b9030050000c02c801d03068941c4880700040003044441489070b0300c0b500c0c440b07a40c3e0f46085800180020f0680302075440c188a2600e0030300314103901076952203d4421050000600faa084654040050314000458591105200c000b0f41081c0310007912229244594030b052107245440400c00c138542c41141000d0f01c413960140f20300284425000f500604040c0408601e91405400c5601d2480c0010400b0a007003609130005002d0200781d90080040000c001801200389006006080040101151407800c0420070004a46200002050315544940e5440c00004140c0a280c407a4050f04001048480d501b02d41c1c903000769960820700440b0300c40c0f54020901d180484924048031442d8001034a241c9030b1387c803001d00c1510061074140d10804901414000403501203894800d64000c002414004160b4503a00e00b480101c02141 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 634964586 1250 634963336 634963349
    0x160b030115050c1203070e090103110f030f0304030f020f040c0f0305070507080901051e0c1e060621030717030105040b0a060e0d11090f190b0108040f05151609 70
    0x5203c540040310002c20300503c410b00d9402019500d40d601001111419121180554080325080011040c0812550508004201525141e0908040c8020590b90b4000000e05403020340c001c1005100050030f103041c02c649240302400612280d07a00b240041e0517103008a40200000c0c1c1a4035003002d03550345c9401890b0b00040141440c43c41d100654540a0b10361241003840c50500500144d80c0747d01401140c0619087c0040805581c0c9070308081c49a1600c1d802c8080c00c02e10506084010b0201c40c0341d020608a0117401c00a0000e54104407842d02103894920130551a44a4042072150001095158103801045e00c00060403507500d6060004001c21544114a018054414920284025500306450806c1c2103022501400c011080e480d0200c600e142840349503412420080070f005162143c0c001860007520f650182c00040b070300f58943c844c21135049a03083d5001490180205000c0f40105c81940032041c0500281e4111410345503800407400d0b400d030740d000104030b00c00b40c03204401640700d02c0d031002804a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 634965836 1250 634964586 634964597
    0x301020c24190203091e0c03010609050906041103160603140115020c06030604110f040e0108030a0f120f1404021e0a050f06090a06031a0402090105031602160b030115 73
    0x4100c41c0388a0075040000089840a07030004c041444801d00b00300300349204c00511000300160b004240c01a484a02c810319203070003982000004100c1c0e0b0464010035114940a100a0140ea9107544981c2c1e03008a8088501c0d40600400d11621603100c45078641c0b4010341260303200410061002000070030720600591010826000c24001c10140341d40c013188a820580e2304640881e00c85d150800043e002309440304004104040000701c0b22010104c45000e44111010751761a03602c0d07607903100f1440b03480740300715070360303180060b24660882c1da0941c0120943e42000f4000e4800040b6445182c0200e0b04807161a00360080004602d010072046240c1405032031041c4821b040580014000e00000c01c10084240c010f40e4424076949004c2d5101c3d0321342d0419500550402040c80b100c0540d50040580201022442c015050061500c1c034601400e140c000c41e0214501a520301c0e2650351100185000b81c121048034204601440c460a07010818000b082c101030103003035080c50307580d501d00104002d180c8051b4904805212 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 634967086 1250 634965836 634965841
    0x201122d290603040f14010c120c02120f0f040306021204021002010614090c1918090203040308042324010906030203070501050f0910030912080c031305010207020301020c24 76
    0x46030301083d81e800507130200d0314040d1180705190201200030880e0880c5850741c600612000050b5000d40402c05080200504001000004008a803a0000f02c4848036130b5043c1000711300b40410f1101d00401c001d08007000341d05c2c10b1a440340d80704020780c1e00c0041015503164550f014807055250000e802c01d000e041c50f00080001d1468a0150760078a80c100030200c0c49405644000313071400c82003100f12280c05244801c3d010404002c54005800964481c04114030b9a41050300810700e04118070071240240c1d0140c03030b003903096a11580c420245550749264040c20b0300070004512440c81c0c08005038146200b507280d000750f108801d101412054101640250765244c285002000980c03030126000068030f000303180981e40c5142c2d4003554421441000b6510350008044100030a0b0b643c0d0503400300072490b225000c1c440009812140841c0e08641c141c1e58100450030810204010340311048080760143d1113a8000b40c2000b6484d00003a0882e0003107024920306811a0104c41228440036885800c81c604203c2c00041a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 634968336 1250 634967086 634967089
    0x9020f090615091f031e05010e13030c050106030309060e090103110402030c1b1006080d0807030b0d05010f05011508010b2d071406010b070201122d29 66
    0x1881c003812885041c0c20001a840c04036114003100464448131040f42515207003074510000d00a181109803801d60400450142c001b0b04407a0180702e0481e00e00d0580d804268407000540581c0880c2d10720120700f44022803848400103402030103088003c0d8001e8560203041c914010010304000d1a0f4071015110302402c0005200081103840c0c0000c082400b510700603280d585010300f1203042d1081c00c2e9000c100c0c0d6100d100d100304004001814940c2da641500c024040d03d95550103031981d80b0402c42800c400300d90b03142d0026000314482c0d07200b10400c04000b0a982d640d160701d51200e80c01c40c0c4a40b004084142d454100522812030f41c9262070102101e10714200c140b03581f5000e00404280121a04c2b290710280480802030103690b40620814600240188a9902c01652800001d020680a145e442a0160f0b1000080302125107060b80c50351078040c0c4802c1c925207555541c18000f024030114600001c1841406080c980c44102d151080804110100081640403010f151801a4a48030301e2082004010200c4446 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 634969586 1250 634968336 634968349
    0x20c270f0f0109140f0c0705030f0c0d1e12020409060b07060c021c0c0c0f0905101505040b030901020d050103030f03050c0703090b13090203191107050715020c03030a0309020f0906 79
    0xf04070903184105c45600d0301d12a42c42035216210340542640700100b003800d0080f008100620307a0010840455950a2580400751004414904038510717481c042143c0541f020f0090100500304002d002c801854252618152403c80b401d50f0804a083d0340c002c103010003040071511039040c0241c542e00040a580d1404114014a0010071101600300038070102030004110f95954403501404420755001003040d15840008014082283e1042007085051400079000c41901c548564981190343c8440c0f4050401012200316400034200001c290b5003004040703010612841003034042c41c4291390b803600c0c031610403100600780c0f070010706001d00b146000c004050001c2d4104420800700c0b980454500e4403036148a8a000170301a05a0042000c14000070070445000f9035410000b1042440e10000c02465181100c2d1100c10301442c0700c0141070381c2c0411010300480d0310f9032450080c1507840784100c500250590021a080d500400503e901007900c412020085161170085801d22000c1541c02c1602858030070009001d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 634970836 1250 634969586 634969591
    0x30803070f120614041b050a0e0f15030708090105070e0d060902030a0308061309150207050703051f060501020a030e010305130c0b0304060b0d03020c270f0f010914 72
    0x14040550426076480d80100b54462001030740c2441044200e0741c510524000f422002e26881c41a850035030501128042500800e4860380c441e6149400c0c020040000c3d04c00905940c0d00302d501c4040d0700050312459840704622803001001c4a80d032500c038100040d0140c165070014280599590410080203044e6a00c41382a001c5540105c620034070011440c2000b00c0140314120307002c0d400d8040c0c0351182c02490f4101c80030038000d4000741c8201c050301212800d8007044481246004016004203031740c452049a0070b80162071024050b405842050b9503980e902c903e0b001c45940000c24030050340412491109252080300d00405082c0040c015040440c4e40c000c000c580c2c942e5000e414946c2d10408110245507120081810301d6104041000607038440085100503042228101c4010341064000c44513401c1c840695000103502d034000300700740c0e4802c20030004030381300703012040c0703100107180502040c0c82c440b9071a07060142c0080c000c1044141000c88110380c103224141c120380f900d00c0c140601320905808200041e0f5 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 634972086 1250 634970836 634970851
    0x50c09160e0111030a02071403030403030c0204151d061c03020d1103190507120c0f060e150f04030306170a110a08070e010806010e04020d0204051519050a090204030803 74
    0x74050500c00161000f850b60105190382d403001080e255041e580000f10041560341101104107100f00200406a03680306a0200600080c11144400c00605081e00039603400302c11b0441c1d0303407030309903c0b000c4400f5010584550501081440018030a603401d243c14501c06e2950003068105038219a514040c0d41d40c61340105071f608000046030601140b900901c180c40340b058450f280244440000d0f00001c2454111400681d01101001205040107000c0d05421908540c003a56030240b0354000e0f241c0c1d00007011655480902402854480c100101034403541c0d0b0711907003800039614054109800d008040714042d4100c40d400a910b0380da00240f20000040019040d41d128010038020b02c15000856805030702c3c0e80c445100340c4141000890340341fa118600c0790503140c2400c1194000c0c1c1c1ea58000f000c00803030595010390040d018807405000350400b03401442c1c2c0144207861010700000c3d0f0001042c43c0c82e0580c181700740083d0700501c1c01c3c0300d24a06185030100411524000398205415900c51000c91b100c00341c01c1c1d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 634973336 1250 634972086 634972097
    0x909030c02060a120e0d021c08160302090303030a0219110c041503020a1205160b160519060501140f03030d05190606030605040f1505010e0a1809050c0916 68
    0x142c4440e04c51012481035a0310a0020b000545204a01954805681110102501501a8038111783c0c0790341005c0f0100e07452980d0355185544622040314901e4003840d86030703403c06408204090240d10100011402946414401aa07400e414100d2901281c02c83c03000e441000704903212180604400507114030010030444002510440359203070303030000c41c0b001d0340003e4000c414006d0008000404208031a0414042c5082e250308007032180e0040c041d2b07051030041e40500c1c04280f00034044145c2c5030160012681c401c034101d0342ea11204040c0410f407245609011a10b003034880d00140f1150100c040740d804170700800d660718440c056030400001d0f12400b4403500c54018a59038000104504551100041c2600129104003d02c43e22101e008010300500d010f010b00560501340311251255891183c51404141c1c0c0b416181d109080030011204012048001c0f0f500c00316a410205080c0285021002c5410300050f001400000600e403c41c01c00c461041c910381b1071002007040128003440c418020102d0f0301c052400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 634974586 1250 634973336 634973347
    0x8011a011803050601081b0109031e110402130810060b0f1809130506060616062a030b04060504140a0c170112030806120c120f010213030303060909030c0206 69
    0x40340003410341c0364070251041c0300303c2000107094800411011108034101e0140c449080d141c00054400148034172005000d4190303c08203090200b14038800b1900c142c0305958010704a62850001401c1c0d0300300210000d90800e01c0c0c40100481c1008000c0b40b915003021043c2409003038a0010805082d000d5801c00125480c000034117032154510008282502c243d00400350921410b02400d181c0310704042c0b0034110384600c104000700740c440c50080243d845071b0075060014440d0107a00c0e6680f03005044440c90340c448040545010143c9607007401ca800c03095003d1550700242105502c4200401e543d071a60126029074030381013041c4602c05d00c3d1000c06510054108003ca881c4001c85401c81d03200019000c4d00c1c0e100784101e0004502004c019510f490424041e035106c1c02243c0780c1030300304038042c070042203007400b264480e800e031901c1820000700c1b011800340002c1c151104010070310311260036070740500f54a24140c040c807135041c01011b070188142c07409441c603031404020039480c1d9540a0480000325a001c2d100f004003141 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 634975836 1250 634974586 634974617
    0x6091412030906040b0c0c0105070f0f03170a09030201050105190b0703020309130605010806040c02070614090d12080a02070305120a0b1e01120b030a140a06020c07030c08011a01 78
    0x80b00c10b40a0702501c030b00e9480c0d075148440b038200d40011200001d0740c02003406c6075485621a80c00d40740b855422100003054100c03c1c1c2d0b504c210691065900b24144040030780265560020307070341e2261180180c200c000c41c00300e2140c03030000d0031100140c201a200b400340380828811450076040320000e90b00d01810386581c0390894241a807841c01815949548200419510246100c0c160412001c5500a1b2551780b115202c000800c001e5a01204201e401039000400410100b031003442000407514288241318501b01c20080480c40381c05440600f41d82c061000124243e14551100381c00d0b62084440c841181043c0c030941d00240700348103404c19196020008000308480c0040c5600c1455132840003000c0070079481e4204502c40000503000301481c0403401c50b0208404280742c4d4011181c00480080191031805102e032703160385000190070b010b0360b440d1069800d10b400003140341c4000d0520854200080905520b0b500e0116101c015507041109582d06000400c6140740c00c4003030080c8480340c24240091404035500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 634977086 1250 634975836 634975843
    0xa080a020118090f0204050f0103020315060d02040801020d0c0809120712030b03150a0c090e040b1f03260c0d0806040b030a0308010509010506070c0603020903010603230706091412 79
    0x100310184184ca00a155246003807980d0040044072070588858014400d940b0040d0200e0000311000341d030904101c00000391038078246005180d075810f440001801c0681368010303a402c90f0401781240d007819585441d0141815082043c007503112268000514180c145800440410b00403524014a8218150f00344030304280650043da0350484082c0840d890504150700c5401305441c161464403915250100c80c0943d036205480010035100a1450344041e5212596032851400e002815a40310a040e0640c8449490f00307200000021802030791900c3d6916400070204a00c000010380a920030403041165821a81000c10860810107a03410800c410ba9580004100907080100c0c0e09031740350140c80400400c142e0000e100c14181c0e40181c031508903e070703254001d10019104030400035001541d28041002914030940040c00501000390000c1602c96a03503503204030307904d80c4071603a40640706030b03070204000b01000b000104020140c43c900743d80d03424905015840084400c6c0030719030142d101d1400d5020f4940080 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 634978336 1250 634977086 634977089
    0xc0f011e0c08031e0105040c0e1302040306020f0409050105060304200d0206031623070b130b130b4507060207030210080c12041e140c0a080a020118 65
    0x2142143c2c0c92030030b42500a15031024902c11031412220200120340e504140c0b24144041c2c03d0381d10b80510701c40e000000c12007090b00101d41c1d51100d517000c0101100051481c00a01020300b840113542c0d0b142d40c2410510416540140c00c050300502e0280308200c0494401980e8115034100d00d50215914000074011411071460a01c0184d005407000081c800c0070fa600e48501c014594242e03030707103d1107d103d0036414542102001d542440b81d0800b0302901c0041482c070f059080e0043c03041181c0c1603014003255980e2100003001c8a1001c0d101d00164000f5051012103003245a00c14669040344401010a51007001c00307801c88414000071000642104940816a0040300c4003c23854200b10b80c1c04d141e83e410f00a6942580d030000301d0043c0e0301c02000d20104c3d40100406401207503011195420031880c4140c01220980080050390700d401414140070b403a444120860310345d02e0081e000c4400012650045a107040c86140324180540718000c6d0030494042d000c074034126880e50900c0c103081a5081c85580f000394420302d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 634979586 1250 634978336 634978343
    0x1080c07080c15071709030d0b06040f0612230103080a020c0d0c03052a061608130603061d16091d06130218010c0804091d0c0f011e0c 59
    0x101c1511241050720f008005100362103580e0b03503a044c1c0d01505802146090182c1d000100e0381e00a000b40f10032120150800260880c02810860501d9a903805000749204154055000300f8070034101b00701d00c41550b004011302500c0c101164040d15003050b0a40c1890310052101030704c3c404010032001d00e401e109100000360017400030046200004c1909050074103081c0c80c0320480e09031040d20340094500c803c0c01000c10541d01c00303010100a15a0150601c5416032040d4040c21030310040b00e1100c40040c1e142c1000e04401c4400c0c0d1000398929040540140450300c03c4d8000600000c03010064107104000340d850194042c071180f0300e0711407001c1d460605880d012182d41104400c086c01202c10400e1080e4501c03054803d0400b11070000c2411408900c81042748901d10b151022506a1103e00311254010018003005078810404546050398840c112001c43e1405000d03c1080701d04042a150811030811442440000c111419142c0280300130001e4413070400a1880d58580031a80941046140140403c1816580 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 634980836 1250 634979586 634979593
    0x1e010605040212010510080c0a030c1701030605240d030c0206070c0b031e010f05010f021c03060501140c0717010e0601030311010516090b0d061205070e0a0203040201080c07080c 78
    0x10888114050700f902400b5050083c68005a01a00144160342c91400317141d100c0360061500703c99050480103000001085010300c2260741c040307010394041c041801c1c025400f801000940d418a49620703c01c03c124241c80324a035114807600ca1840341d88072101e0001c69980340c181000141c600c0e1003c64184e0040300005000c64003c0310001440194010045114075514900e03004283d00f5280c110024540a015103940681740c280c00780584d50007030f000d81603518036034011a078505a140042e021140507543d0074400207a1240e0342000310b960800312107803c54040c51066810b01242011041e0348040310300c103a1803016000c0f007410015100039880b4a2000c1028010b4a0084d81c40b418017400320202400c00490b290700e442d0001d0000040707520441c400c1e4116540321000e403440c0100300302450700441060140359545040008611298104004a49120f0f0b8050801305d464039419015024004210081e214010810000103030390080c0d50300c1e0f00070354a1010301e481c1c459604001c20a406041c043d00403c0c071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 634982086 1250 634980836 634980847
    0xe0f04180b070c050c09070201090c06021f0608150c0c030c0102070209130b0c1803070f0e010f06020a1b09020a110105160c120c12030221091e0106050402 68
    0x281146203511040c01099284200d44804500b214240f042250142c03040e045042c1c813000383e10b00445500d40160461001007182403442d02d4140044103542e2200300540d02220310310103212030000c2d40600c0340601c48030410a66242c80a641d8850110500c401d21b524801030001e40510008c00669000c480e6080491342c654402501c240d000307500c0310030180d100f10071210010b043c058802d0144480a0760080200b0501e031101401044160070032134460324041d1000c41034408d0380d1400c008030300003070107030300c61842509190180e400c1c10000c0680011180070b01d20355050041540010b440401240d002680e000000c0718150032001000c1c441c4c0055458500000c4c0502071245e000054412940900c4000c00058852015883c20600301c0b141800c04a04580c8003032004c035085542d90000010326003062910005a030750382070306641c101342c50400800d9001c83c150300f400011014014042140890400040c10003d500756a00c20201410b000000200303843c4880b101c02c29002a802444060030a54551 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 634983336 1250 634982086 634982111
    0x30a021506060c03180a140102032a01020d050f060303130e07090e161713080913050c03070305150609090405100e0f010b0603010b0405060304030219060515010207030c060e0f04 78
    0xa00c101c1c117040d01c6042e52410100d0425091142c801041c00c058000714503140310351046400c60251161003940c00d0354420010610a00300780001c01748c0002d00780c000501c6243c030708451070305020054901c0d4080c2c0d1040c40303045c02ca40e41910051059401001800c81d40740e031800c200b02c0c1c0c4400395070005054000c0726400c3c0700e07041310740d5a400301c0c60076429150f40c550350b410380d0780c8000312960403505020704405035800c0c58042100f04004020424010b440050f0255100c403580c02550400d98640341c1010300042003040f44d59040c400c0310b800440c0c00c08028a03111850000402c103008003c5418400d001d44004142003003020005104009180202440b41c00180101551034000c82244d220f15542404a419a00e24191089905a074240124103051a05040610200d034000800460640c07044000c116a032a0b400c50703514596900c11074000c00c06140089086500682c0c1d00303005030655000d50402d00000c0e818800041c02d0b202c040c070304200d80d0100030300042c01c0a0680c19619801034074240c0c80c910713103 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 634984586 1250 634983336 634983367
    0xb0a0e22030c230c01050a050c07140114030c0304140a0209090c010f0e090103080a120624030b010c11032506020d0c0507091e0f0c0f02030a021506060c03 68
    0x2c00c0c0a6040149210340f141c0d10505003061100e1407140540010f45079100542c01540940598a01c514020303081031403404040e0728100698000840151099082510351f41c0d102000343c48880f454600c460650400c8400c0101600014000812680c2c400a110780c44074070070803105000c03640090041700d140c14001d010310b0715201c41100300e900040784000800b007114000c03842d03214003050190558040740c1c41c0d034550380d00c07941080041104000124807206202005e5000307200262010820944000d82c440d8165140380030b84268040501d401c0800900150ba0050b15511030a07801c44101c041e151a2200002d0501000141d031800481d604031810585050840e00c0400341c80041e000c4031003004030303110107035000c444011004005a000d464103204501c210740142d1100c0c055140740c02041c040145080056a490004003075016a0351407441008940c00903071082c0707566160014515090000c0b5009448204d1880d2404410030b042000c6101c5484200c102c0d50038200c240140d035100d07c4200e40c0341c0030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 634985836 1250 634984586 634984607
    0x30a050a08060f03100606030b0612041e08040f08010c03060e0411040f0e030705070501020609060a090302030409050903070501050c03070c02060306060408030f12010f0501050a180b0a020c090a0b0a0e2203 90
    0x189c03500b0030381d2045040c00400c0380c1c414520310505c440b003036a480d80d61740074440d01e203003100070340c18200d21f480d10005008401420240c010aa8403400c0c4a040002c41c07800c6810203502e51040506000c0100840c408040c4401d800c6030300a9a4813101ea61401e010402916181c0250030b034082c5401c502c0c042c000004009050000e12500580d140e0907030310001265100c80540340c54103d500300f000440c868682035030200107110b1190040d24240341ea81c080c01000c03a88105c44280d450f820026110040180a100c0c030390348402451503241c103500f4040c80c02056841440340080c090b032000800b0540c0c66455000f40c0b80104403d004899440e10b441a001030fa9070000250440001e49a000118a0300d2500c1c1706802624010781d1154200140130800721100c07000804000141c4490078004264001007100030704081060390002e200c0b6030034000c140440440c00409090000c2d2800ca031b00400c590300c031088042280c0020a4a9141c0c0d02c0343d03010400c041e100d5034107050051a201c01c2520406801103618003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 634987086 1250 634985836 634985849
    0xe030307030b0411030601050f1b0616020f0f03041a0405060d0902030d030606021f0b0904050d022512230c130b010804021e040603051e030a050a08060f031006 70
    0x8001c0c00c2009501a000950b0400d010230003d10101304034040c0b440c09031072a01d40c1000702042032048801002d0400c40103413504441c090745110f5101080d50100104120110721500400c6000d1055440341c2e20b900481c003030108602c0003145080324030b10454060340c000d804c0007086940d441c900711039100014912402c08034024088c01d00b006d44002e00034402c00c03003215a1078018004031034070418011242c00c80d12482a00b600d41d02e0700c00c01c14a46074849060b109d14400d4000f40200380c10160064503105c100b056a1012501d52034403542c0e07540700d407000e080c101c8041e1080f805515020341740544184066090050f0b460810240d043c2e841d60b40010305403d803240a9999505076200e0008107000e9071904c810650102d01181f01003001401c0c403050b200c1150f030000301c2c10380c404100080040c041d00d0350385d48255041e6002e040410250f80300c48051202003890207008500d042c8000300c003d070040c0039402c0f000b4184801c040010300b16854ac00401164488020b082c0c071b101c0802e00386180000c20380da01030130 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 634988336 1250 634987086 634987091
    0x21003090b16110607080402040203060d05010e060406061a09040f110c0c0112020403021c02041107110405060307050a06051303060c050c1608032a030a0c030e040603120e03010e030307030b04 84
    0x1880034540801c03414002c0580351b5401c6138a6655800380310180d80080c0415400c01410051640440e4007031041a40c0941c0c2a40600f065083c01e04054043d0313100d41d0030002c20070282d00101401084240d0445590000680380420910500c0e90010300504000c50106907055001a403440311f4007000c10b04560074a4240c0300c207440c034007440c1e000c0c0040b80a1404001d401c03241d140a00d214200340031080311965880200089642c1e8900c0c824030030b00b80c00c00750302250b01d0003414242c171881d840d040c02403c0d48500180d0003040031a18040c0003840fa10100e02c505801e01100284142c404480030304100040c41d04414288540c1900080041c126880100082604d0080060760700101e003003003180e0b2080310b2800005604222081d84518040da032010b640c000450441c1005400985060010306620304107515840e42140c1c560502038005113508812a102d540ba0003028000616054814041ca9401e8a00583d00783d030000c011034014041c441c0d80c02414031002c0f04004200d949500600c0400300c1c02e075010f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 634989586 1250 634988336 634988357
    0xa0b0a030b011703041a0702121f0e0114060d1e0c03030f0242090703140c060a0f0e0a230402041203080c07080703030203160c02010c021003090b16 65
    0x1855105d0060b0b01400d0403406c4031800301c1e51480c0c0d8840190040500050200310745002002d036540c40c00e03400c460042c10500c22100c0c1134070041d400c1d20031411040300f82e10091220840500c0740c011a0080100000d00c00e40714104a201071140520030541e982190901c800003108280c144030294680c288812400a100c4e504d5540080384042140080d40c1b841d410301140e81014621400c00203010780c421550482c002448500101002034280c0303000703090b144e001d450b0060031810414500d0b2104124014583e02c030101000082c0c94200440b0800c1000703240210364450112000c1790155480e400e441ea102440200c08102030030302d03861340e03008403002190000708080740e40c09000580c01359108840c1c000402e07800c81c00c0428003407080c00c2e60244a4140c0c031481c00110740d5840340513401c17604007900065408001c000105c281c00c24480c00c003d0072414060030070340c2d007030303000a00000c409e0030003d000d21000702c142802d240c0aa00448101948103034001c4042c0352480a50340c0078040d400740a0b000a680d00381 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 634990836 1250 634989586 634989629
    0x20030a0b041a0307052112040321140304031709010507030b0f090114060403020d0b0103021008190b030319020c150703081605090607030201051509130b0a0b0a030b01 73
    0x5220032540b4018010302400c61074101003003c3d8210000300300807040300e06040082d50300014410301100a41021170651141c2c00c0d814410300d248025840d004c01903101d60203080752160070071000140c1010595125689507507a02d4110340404e107110000003501c0385031051119804064001c140b06002c81c3e0341c1080f0a0075424108981c034004134012039003000c0c82c18018002c2c881c000712f40b80522207015046500c0c2c160340e60301040e1441c4006d0010303a1503c42440062045152202020a00d001e4920f0401120300b020080b0504100c8901d449940c40f6940d504072400540301032007618a018805040380c56002010030000e5152407076108142c0c800d000e1030150009a0301c1c0c1809a440d256095aa0050aa9591144000c12180c1c0301240700612400344038041d841e550300c4005000c4184264000701e80d030b0400e82e100030010380054103403602c03550010003040409501d039180042c02d2030700440000c04544505142400400d550010540c0194456030003106012070640b0190403903801c40c040070031180c940d04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 634992086 1250 634990836 634990871
    0x3020406050702010507021c0305070b010e0c0f130b040f0f0803070317041401020403151d03031506040b04030b010611030408070513020c06010e0709090e0309010320030a0b04 77
    0x180d03501007503041c401070b805540300d040a4031030684040d040c14292400801104200e0414140450020790002003820402c60700b02411401401c4034a07409145041c40625520385014240e14a03003002070200e4854400a5540d0209000707000b501c440c01e5480340c640300281250501c4d40100b81320788100c01c200092000c4000304a6020980598604200d0481c0c498841031200020700152020800d08902e40b800c0700d03083c0300400085203d034000116501d074010014065518405500111507010f026030070a8100110480b80e2280b580003050f00b0001c00100000d0f0240115003004040390b0002c40c020080019400a1038107841203a16020860410315100e00d6413881303107005550403600104410005402c080211030f42a030598400507003440e00d01d0340340600d490000d074003c00524803803500780b114040d0051190006000ca084041c811200124240d80d528070401c80914105640c610419104500c48040001000c1d48034401d40e230341e4100740f00d0b81c5003d0204031180f284200d2074042d0700c082554201 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 634993336 1250 634992086 634992089
    0x10b0a050607060e0304090f02190c0308010b03100801291c03050d1b020105220506150301022203110d110108041b030507150e0a120201030b04050421030204 69
    0x4000d41e01e09480c56881101070113200c907504101d880240000305400340c0074081c001001c5444500140c40d00302241041001b072451084030000c0c40320385100240401e81c0088201c1c1951982020aa52038484a02c1c4010340e1060358400040c0307510707000904d944850b40d0a40182001d03101c2c42c88010404901c1e0800000c030088046981d0300e0740780380b03a540c8006400740300608880d07805910000b8032039007000b001e9091003601810340c6006075034800070022640580103000140780d94292001082809943d1041d60302d003001b4045da4416801100c803c030156a00b501207a090f5110015480f142d05400820807050b00024003040702d0351050f548000506041c000209105150045615290b0102c000f00540c0c00074400703001590940c00c01c000700c0700b100c0902071159000318407880c020420075107407082c551021021190418200030819414003090b56030200f1940a45005081c166911842440180d0080c004a000390350441d08003401c00080c07041e43c0308081c0450910f11590b92024560103401c03003ca2141d07 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 634994586 1250 634993336 634993339
    0x3c060409091518033018060903051b19030804020d0b01060c05060609040b01051203130909020111070312050708130803070c081507120f060b0c010b0a05 67
    0x14401004440e05030342100360030074000c801d110404000c91a0b00d8080d20f40c25a00c0c4401c00030980f501030101544052070700103850122114480a440428010201c0c8540c000d1101c605a01c0c1c48511340c0d03418400c0480c0c50b2207039001a0820101d007444c41d01a000e6000300015861007010041000150000450407081504514500a08400f000e0350162180000604140d0300301c001800d4000c00500015040e43c080c05991b10b60381402500342c0b402500e040070044c1901d00929541003404000340302c00f54500d0546008442000803040000031162460158002c00a4070340c0c1000d10014000d1903540c071903ca141d0007030780c07400800a0310000312544da642900c00102005114074a41008600c59400340c28000d110740b20b0145070230000840f0000d80010354006403003d07000041da05017001140c0300d10340014040300000c0d000681000c20b02d8130034000003d0100082c000071016442400342240c0c40300d0101d0317030646801c01c80c03a91944503000b0b99810510349001d0b03e61a020300c418040c9840e145400860780b0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 634995836 1250 634994586 634994599
    0x1f0c05150105150307030f0f063305070311010513030f03020c1c0509040204080d11120301050103020f0918040606081b0f18010b070c060c0b04061a3c 66
    0x905800206013a80002d104104065881d24607041103042400307626040c04111038082142c40c00c1030380c45509110000c08201c8580350890b0032591101c90140b2401850b101c6050840d00c9408609040c0c402d03581010a0982030b5180c0001c11540760758181030158180c0c080c0d52031840200282c03078140c089104440014400e6801482d503900c690641c408642d50755440ca242650078040ca00c1c000c54166041500300d0700042d0003050f400c42d8941c2d03011000e5102c000c01400181074180c00411a90406d2106014180c10150001821649810070904403a0942c3c00a4980b032112800c802500d400c031103060310115040c0781025030010b420380300003d040d102400b40f0a144000120808200000301401c02410754100c003807215000b404101041426008061045845035120032901d080140d5944079040001400602c0040c000490291100c0e036902c40e1344804000b170460b040e000ca04078000d11102c4419400642c0d81416610122150a141c410f03481003040e88043d541c03040c410040e4841e003654074031f42060 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 634997086 1250 634995836 634995859
    0x60809060417091e0f0619032403050c09090d0906111615030c020a030f0318080d0c0e030d0f0f1704080909060901060504141f0c05150105 61
    0xc02415141c15002c031102c0440f850004000080381c40e2900030040381210355489500038400c1d041a00c1d9580c81c0e030310704480342403510842090b40300480b49050500810135035101b40c3c0c4002044500400b841c8022609442c41650f9680e181c01692455a0407a003030050f0070307486c003080c000c00000402d41181441501c480300d003a81003400c212198025101040180e200307007900e00d401142c0d07451440c0d0203004080302d5900b40c2c0300368030700203001e42d655041800215484041a0710100ea03000c2c0e508211225a4500403a11900b20341144400e080a44c2019290003000240c01c2d1032040681c1c441c015848450f120120b030404902c0c2019265903040c4411804104101211011548210400e000640c140c0c00e04c4401341110941c251300801c03080b0740845001c1c800141410843c9000c29074030354468001c891120f510340c1042401420f46c016841000c0d00d038088011040c95a030b5035100b078001c00d200506000354400800500c0240050251401551180511880342454080000d425030580e9005009580010b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 634998336 1250 634997086 634997093
    0xf060c0e10140702062d0a12050a0914161e15050c0607051308060702070348050303030c0703080403140a0314061c08030604060e0906100608090604 65
    0x40aa258111418942c00c00c10f8100503910180580586110319210744981c600c0c440001c0e01e4244001803400540d80c05016800b0443c0e8400300034800c2c680c420b5804203803131b101c010100c0043e1810f00c0380105214014020f19002180005080b400c0718400341ca82d141903581da107c1041c200c03098501000714000c45d684103000f50340f42d94440c20340821003032814a03c0c14184001103820940103498403000100d002615424007240c401c1140d01402d0220041c04650070003400107581c03140d00f032000522050042107032103507004200c140a82c0c0a84140082c492005030740c04c0111142010a80403035a070300c0740c0c01001c03d8074103002040c1c038407803c04440d102d898070b942c1d0f8909903000c0303100800840800c1000c1800ca100100c90740c010300084a141d8601043e1409000031032401040c0040040c3d01075002c42e1440c03c100d0300040f441001d8290000000340c0c3e40e8903417001180240030240c0103601d000c0140d03003c1c80b20802c0f00140d400e10403500300a50b0a01c45031508800c036124401a00c00c180f40c0e6000d200880c010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 634999586 1250 634998336 634998347
    0x15100501080a05060d0206070f15141302060d1509110f18030c1c03030f0e1015080a210311040e100915050f0303040812030c070c030f060c0e10 63
    0x8280140b0b417061911207640000c24580c400b60003241c0303106410441100700102ca03042c0f80307d0f2a0b21104144213038500e40d244410140002003c1da00040b480028040542d110b001c00c650f012008035409110410b00d0850902070001203100d03040c82c542c83e01c00c507004504110004d40b060050080b480e28540820442420700011301032615a5060041a101c9002130342d80c6401c4504580361719800328000315903402c014048921b000130358030180b03040055803002c840b4082030450503550f0388440050300c46244c80c51200d800303040da0030000c04c5120f02c03051030040c0402318642400300d41045540c2d010f000045035040301554082d4009504140d4140014411402c1c0000007590201e030340503001b40d00315610301c0c0e0354094804060b03104c0c480344007011090040742000300c905104076009070000d5180c10f250040e0f070b42c0d5580100b58140c240213404030124002100d40c100f1150066009a4050080744d00d030304000b4011403803000216000c6251001003215180207040c0b0340d6144000401707080d05010b42d200c09950 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 635000836 1250 634999586 634999591
    0x2190809030409021809061e101205090a0506011d04110f030703060e010e03030903070206073e041b110109060e07030c12050c041503120215100501080a05 68
    0x291404140404143c0443e140b000d4003aa50802d00d4121070034140c2402e104c5081d01c0038001d0f90240408551251895a00007925660003a0540d0040412005640c4c101d951400c121001d0001d282014280501400d000400700c003854011429643c030381e66a1400130305011010406000304031440000a80805d0309030b1802401c0030340160201030702c1d20b02600000e06007101904102c408544d9440030181d0300200b480b5000040501c04000d42c6036040c4121600c0d85c901855800a105000000b40102007190b03d08606074402c4100c010542d510002002018403004c3c1c1d1804041e00c800700c00d40c0c513451b51525005000b0607043c1818003807926100540116164216050f00580070340d2145003000004001c3d102d4001881354a038003500f409800d629041403030301181d5008659034650b0070350180c00300e8000301c0d03c041c014004a03000100142803a000104140351a400604008007260103220255000b00303400000022a007101295a41c0d800c0f200700d034a103044c0c0115800a0300c0344001030105040c5901458 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 635002086 1250 635000836 635000851
    0x11704020906060f0c1605060903030315120609010207030f081911190507060c022a0109090c0e101b06180807140601061d0906010311131701021908 65
    0xb03150540454440134168800c01c144911580031082e1511000d0030065400301400c021240d5a16020315100043d40d207001c05801088007a200c4440c0301c0700740c1d0302d00008442c20351100c0140d50203403514401d503600039003000c601580859810191510307003500c02e11100c1d1042c0c060301862000342ca0b80318101d4008110001c0324001a420800c0030000200e032141103a0844100b90340c0d9070b6a1240c4514290050718201181d600a43d80a41069030558004003251032401001104030b95080d24040300490b005c0c503555221407685458440c01c030f01c440b9403080303500301f440b003042e40c031030881c01d5070f906080301c02c6902803506440702e0808280140c00116260803150011014541c241da074101035840b6644940d0008804560f0b400c078000c083d1001d1581404003d0062046042c20503056214641c0f02d28428100d4003141d10814142e400119541c0c0030380d1201c20400045590291500320b16031401d403402e485801801825407207140000394450b014004c486020429040b4048001c42121040d298208050140b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 635003336 1250 635002086 635002099
    0xc070f24051f0f0608070f0e100503010320060a03150503030a08010f08070510110a0b04080d0e0c060405040c0c0b04150c020312062404150e011704020906 68
    0x1200c1140311406a00e00400c0185103803440c10650754407080c1c6000803540480c076900c0e020442040080c2d08010031070b038010340c2070a205a201c0b042c05011281c3c1d04c10f440c5a82d60058107400c031414120740c041c0285041e0b0317108030488001800e54031115009d10300c01c2d00b03140794040c104203c0444450300c250044a1940e625100414683d615040040c0c1583c0100494800080940c0e00410100d41c818010300014000c80015002c2c89060001003600a040024100140a80e01203074654000d010401070316410740003a240344190805141041040c0c0c80220401103c90400c042d000fa14800030940c1000341c40c00400541c5458601010320010f814400050018040218001400b00d51000b0a861240e84209034525a00029039000c60441c0c1034101c0650841d8800d11084401041c1c0e5a082c50300050b041390780c801c070b09c142d0582c0501c220200a41c1080b0000c130100700040c1c0b1504200b0203c07002900e40d122540440300d200011504150a02003c04200c2503d03c046005401c0046030a500500301a152 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 635004586 1250 635003336 635003393
    0x216170106030602070b040506010510020d030504170307020d020f0c0109050904050f03070b0405070b041514160c031505191e06270218060c010b10050307080c070f 72
    0x281c500b245c01c8840255800700c148401c0104000040c80800c1c0501401c8400289403012218000d55510382030780013009059481020071305000d422920b00704854481d400c01d580d070340350488000b91611900e6208a01501c1405000c0300c182c6000301d000b0032410741c10307035a0031581c500d400c0c00c112001d04054000e0315140a5102510300180c018001000070314002ca8090055040c54603043d8904862a800f0400c81d0a0601090101901011442c480007091b4a0a5a8452008902c1500d248100500e1003201456100202e040010300700a031030440f030040c0d48840003140c0140d602016510700720380200300f0350250039030320083c3c00455118400000101c0c0c200e003410040050410112000c0d5085403400c03040a036060314004002200645120795000025428034040184445007656010245445000c020442e004a03070000d5001400c0910000d00e4a02540305030364020708598002e0702c05800040b0700d040002c1d80e1056500c2103542e0640d0007100e5420b0844e10f52580852400178040e01703180130f454100c0c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 635005836 1250 635004586 635004593
    0x1d0105300c030f0604090305030a150e1003030306090203091906060e010b0408060a09120e1c030504080d0519050306120a05100c1e050c0304030b09071401021617010603 74
    0x300c031442201c0010a1a03a01d082c1007140c60f0071048000c103000e1007141050004400250b11000b034035005404100301145040441c020708041517841d4004d4280402100e040200e918408440c01044074002e0f1410400b003511454032209905c02114200206d0b400218503900c4044d00405906034a405800c0c009010390b202d00c5d500141000a07803001a05000101d014024030500f804840c2d00301001400c1084100c0c00f0f6500c00f20010010401b0006001d22400c2c820015101c0070b078919005151f5454079078070015280b40141041c1c002d40a4000c03035200e00242c02d60114080d6084480407080c0d82e400d10b14031030351440f04840550005191035003042d145032a5040d01901080141e005c144a5009030141001001d6040201e0b101c117a031400400c000fa09031b00312018820154580c00700d000d0b01e82582d403071902d0760745240303036209507403009100e2002c0004100340910045140003d60b12228a002c00c0106520012a51210341b2461180080c000c1401041003650109200103003182000010822587d00d45 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 635007086 1250 635005836 635005927
    0x1a040e06162610090b011701150504031502031608091b1203180306060a180c0302090d050c1302282006220b04081c0603030e011d0105 59
    0x10340d84000c0c040400f070300703110505290041c140c00b0b83e0203203440b481a40c140d064040140c10107218029510340c00d000c2405201e0300c60800c56000e1754000c2c0c21894804c4220002d000294000ca408001e240b9003000c84090003481406154090f103d020001e20040c00101d224030446107084010b81c0e48030150400c1d0b1880e900082c4041c2486034800c4000f404800345803020300d41807483c01001d0070311418151000788004a000305ca0000c0441c5014000107488040c018164000c2c49000042640016004c66034410807000040d4603504030002d907010790b41c86511100b44000d90043c1c010048200340d50302d00141c4414560b4248408a481c180741512007244040309002c00d0150b0038120b060281c00c950104410204176500100740f40c070000d5285103c468440e1210100300401900041c5550310001d0407032014600651400c3d0072610290307040044564900d000b40c825000c860752640402d40d80b118005800702c003c01280000001a110350f883d088408088540580440500c01030403501d05075200400340350395 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 635008336 1250 635007086 635007091
    0x80c030717040f030e04050c0a0503192a0f0f08061305070e0f03030403020d0b0a0e0d110c0301091e0204060801020d02040f0806071418041a040e061626 67
    0x844500b10350f1105420010442542118180d02031420a070500c201e6440c1c040c1110384002c6107151030b51f200d42ba00e50100070806080f95038213007401d041a802c1848040384074007201c209078892958a00401601c103041da1865105000c180c089090924160700301806808096031040c001040805200c4142d1078450840d2403d5076020002110130f2041a110309181d80c224403482e808800540c249480c50740000c81d02d40724000014890301807640480d20749105508400d00600305030007544c0d0000000c1400808240c0c4820007011300c1c3c03240c4040035850741018801d8414107500310281c2000f9400c0c1f50818030884a5440c002c90b001551840f0000302c50f0002e2000c2c0980d00c400c0100507a03910300d844902e80c0b00500542002907141c0164050204840c2c005111009219568403003913214840300d40d00c0350800342040601900182411502c8810300102c1e040c008c0510022103040003e0a858a400c07030365100112801000043c0d842c00c580c178801d01414803c854180000e9000710040c1075401d1381011350005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 635009586 1250 635008336 635008343
    0x8010e070e1c021806121c030c1101060608070f08060d120512101d09061f0506030720030403020f090c190207030204050c090915010306091113060906080c03071704 72
    0x4440038018030b1305c0d081c1101d101e4920218018104d40b84140c4050001c2042c1f480544103059450301402d003103c2c0a240c09809032030f8604020480c207940c500001e4040101112403800040694205105070360140c5150b500071030340074107030100c1d601d6143d44218180d88426092020301c841442002507400d1030340e01c103521802880d215001054a0314011001d40c0b440c4212803600703c0501800c0060b242c00002d103141e84843c040c01c00d2080c60f0409004100441603e821494001e45d00004001a680d00f050003201c12070440c600c858502c044800d400c6461380110301000354010f0341700489100600c1c05148103a04006074000c0e003850218009200318402e400f030460140540c202e02c000700103500d000e116055209020800b01d9142031081400100302c044010602030f5110300402240350943d00c6648403501502c040d041c2044242d083c1c80c03400029404c6001e0b401c51842140c500840c6042c0b00701c1e201c1d0308459041d15078050030385400a101c04c0c203410051134081042030007001e0441412000441c035019900 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 635010836 1250 635009586 635009629
    0x170d0e0a050a03142103040303110f1908151e04150e04030e011b0b1008030a020109020a09020405030c15091012202b0204080d08010e070e1c02 63
    0x204000f01307608041488030501c1c04c0c0101c05081400d0025400110380d03100390301d4074002a0360381c030001d608c2ea000d000d403903031210b4101000318003e41840000c03174210101c40c9640d140c9810b2541e4174000548212500d8090356088181400c0303121002c095500014914203004002241000003c82e0500045840b544084260380880c0309100603d9080091000c80000a18003520103942d50b1030b070380c440210203180c020000510f05d40001c500d22150180ca00280400c0d078141c1e07503513031000c1400174080d0140c030030264440c4102c4040091003d4061080342e040300c40140103040025070341004c00980525a401d41a10b551041000c04055034801200703120310011900c9561618290082c2182152481040d180b43d241c1300c0d0000301c84100007401982e0210105a01e510090704c020071a81c0b8002c4030000040f800d0304d0021a02107122500490082016402561034890580e030f980d00c0b07645c50340c2040c1c0f4804045480000034202c14100700a000c002501c54075002c1007400601c2d4003164070310080c0e00700540e0403407 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 635012086 1250 635010836 635010863
    0x140a051201060503010f0e04020402070507030521130e0709181d06040309180b04110406080906100b07410102040614091203040603090507170d0e0a050a03 68
    0x30000120901400300307480c0a608541c100140391184145500401c20503054802c001011540c4680440310155842410384004603a40d29211750b076001351307a4608288482c10801e100341780200780c081c1c66500a408a00910700d6261004102ca90300d0054011420480c02040100c7c80c9050b5455010040c1400900041c0100314441ca080b100c5080427800892600804103100100f50302181d100280c8182d00741861451b992102010010100b8a040710741040c100600d12402c550707600060811904d0644580c0801da4445008588400049504846503c004802840800c00450144c441b140c0310303092050741040c0c043c0020920b00701c5035a08580da809590803007103810141d95142040c402e1018000e60038207003040000b0b800903281c0c034072102a000d00441d05511581c3c80c54850001c1c0e45500c42039a58980c1c541000030b000d013103c4601650144500381c000540001d00900380c41d96543d0000290402005480c021141c6500c441c441d25802440c05ea404038440e039494010070000d501c201d03a4500e802c3c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 635013336 1250 635012086 635012107
    0x1c020604170d1704170d0c110c2e09030c120c08030906070209130209041a0708010f170f1e160303050304170c100518070b0f0a140a05 59
    0x500d075801480421041120700e190341d107006503e240d0404d500c11060b5084100b01803650081c1c2c002c1c0721203903202c1d0b4204030300c00c02c01d070b82c0201c0350b04a0b4010480646441c446407000340117030301c095040b142d0350f10200b1561700701c00240940341010002066181640b0072a540340c50b60036551845421801c8128000300c401002c0080b1340079107000034009600a141060200c0703001800300d008107400a4090304094000a81949030012600c11040c0e005028064508007030400c1c1403281c00c0028140c03500c0b00b0600210740c1c82400350405504031801102c20500035400d000306544002100f844c0d20009124044401201040c2882360340900480c415000110600710410b81c0d00c0d00005405440e4510340f42c100034800300380d000c4100d0307a0094004903460001e500b4056454454840d0041328000c07401081741c0b1175441d00c20303500b001d4040d0030001c81c030b0807014840f00441610ba074124400c1c00c041000401506c5040c3c1890005020896000d007011030050344402c0b08460780360f01c031a40910004000048d01c804a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 635014586 1250 635013336 635013343
    0xa090b2e09270b010b0a020c04050921041a09060d05010b03190605031b0307180207020a0509070f081314070905010f182c06090601091503021c02060417 67
    0x101c050b10078144003540300c2900c48800300e14041c00380c2d841c00b140004841c1d039414020060b000042ca0b01401c100880d250441410303448842502601030b000d1785018100880c080c004042e18195024100c401050550042002e180741d4030000d201d40d00302c2820b00804008540a100d03050003091103160f41562450000c455220055a511091103140e1410109010544000402c59240316410b011141c1824001000a25064081c4c0c0460401c08140c0281d1100d070400c0c0d0013600c0403134802d950740c036400c580b40d00c00c01c0320006044034200300191450207043e640902c5a0096034018a04900b40f4020f031603540c0b035500030030601480341c2001c1e60015504018100e001e114050040103d00c00c40f80c840390034060b040000d184900c4009040c04d840f05950814850119817030031305094000c6408004601445040391103100440e0710207180c3c02000000100c0e80c0c0a40580e1040800c2a80207410361411603081000d6201900300040c2020ba2104040e40141c070303080300410141c1007030803241d800c0302000d00140d4503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 635015836 1250 635014586 635014631
    0x61903240b03030c0c19030503040f150801061211130603140f10030f0804050604030f0c0b0a0c080d110f1305030319030507030e120c060a090b2e09 65
    0x241c3c41042010030140c008504242204421103004140012503002c1704440c51550304068418080000c000071440030780d00401e422200002d0b040354002d202400103455208d000d04c65040070a42018034001c40c041941d0185030404107105003903003080100401040441002d800c2440441d03691a02e0441154a0820320366206c0340e007420402c89480c02e001200c40c400c01603c801492038002d000c100f01042401d200780d80140c840035040790344643d0350707080000312003150100541e8440f03059400403400300c003958122004140e854076240c5032660103a4444090703a20540500b00c109075282c4c142c4000c00c018400800c00c2e4041c05001c5900c1b81344030301c240c8800c01d4080d40014443d90080042c0742c86020701d450919000c42c100e0a002030a40d0365400c060340609010300c414012806000460403810381c00002600348241c07270800700c0b801c40e950f880052003194001e6401074054050100080c0c140018400150004c44120b403044032400140040840c09180d250420045103031140c81343c0000004240b020f05 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 635017086 1250 635015836 635015839
    0x619060314090708070302063a0509162603040306060302100503041a2a03070f020c1f0c0602190e0105090109150908150f07050f03061903240b 63
    0x50f22074640982950765541a01c0000d02548011808140903810750a403100000d81c0301040175007042c0d032803244031052011301d0700004810b07103404c02240900340000303028030f64951000403801c80306041c00c45610340d444104020028008040c520000140e10a101134002588600c2c0c000c1405030941c4100401500703c0401c220800005104101c003045040d0103904031241001d0740018141c459182c40c55000360100d0114040401100d20715801c070344a007004520070410b23030741e691a030100c0c901000c82e00c1c1c00303034a124154003001172260400301d8584d104d00103189121038104030700c21000683d09c800c03d0340c111031207180b149a50b120b01207a00d1134201c0c2c40302d02941000d00e081c034a41008500060503801080c01050041000300c0d41915040b409501139a0251284004407001d0042c0705d044258801421245000382040d154003283d505800780c0142c8014011410a003400d50f51340f0b000740f00d261f9614000c101081d040a04002003c15050102024040d040d980060040300c0508100e0058802094030325 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 635018336 1250 635017086 635017093
    0x60b250c0e2d150d170d0905011a030d0c030801030212070509070909051302060d0b04020f0c1e0a03020a1401060b0408010203060a140609012d090311040c17061906031409 75
    0x100f001810041c007981700c150350f507072001e038a542101481600828944000070400e43c64a0130401100090200341050349004a04403a040f031020b810844180c400000002c0125241e84c0060005103008014914004203030000c580886954200107185540309072070b0240460301101c1c0a00c0f005242d40621503003c1c1076040a481003284642c04141103114001003c00c54a0391a00c000e1020750702c80d01148c0700d440320b2040160302c80311410362043c2c40e254240a4003151002c040d041c1c100c160400310314044825050b402400c582c240940302c6000ca454811581082e9551340c40000c42c81c104030fa806000603064800c0016142d18003813007400b585208907003159603011216510610aa5100e1003140c41d80c003802e207007240c1c4010003e9400181c1440f040100b5003c0042120080c02d030303544c41700c00241143d00030450035000c00161801e20045803048240031000400329086030620800c410060341c1c0240c005040000340701c01e18061103240400b00d40100340040c3c0ca46000a01e8884481c0c1e0f01c1d9004001c0b500503 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 635019586 1250 635018336 635018359
    0x6080906090102130302010e0f130617060105100810050a06030204140406051e030c0d1103060f07020a06091103010c0e03010e0705030c0f0112060b250c0e2d15 70
    0x105a15a5810301c0000d040245803003418000d0341b41d2440503149c240014022049100c0241600805020203018010000d40802c40070303980d540e4001409412990054000d07400000c480008492420005100e82d00c41504440000307800e4a40751320a070700403d02a0350040c1c41e503040240342c0302240046000c0350311650070030303d05100659400c02442010001c43c1c030414082111a808241041445019a60f1204405040c502440040c400c141c40d001012070607140c0c02c0d03841096400202c04141d901c4401a8000c9010b03100050003a03028041540c0601c0c10000c0c44e0110b80300290940310400c0c9600c2c0052450115844e0b5414240100e1a1005001000c0c095250030403020a070b81e074000c200b01a21401140c0c00012841e40110300001006548072000d0240a850302d401c00101d910861000e280804500c001991403000903104081565020801172505403522501088440e00502225004121409a0300c90040d4814008452018803200d480a51400303d02094040f881e51044500032074502c0d81 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 635020836 1250 635019586 635019607
    0x219120c020a1a031033111c0206070503040b0610030605040203130b06180a02090103060f08071508191e020c070e01090608031912110d061403100b120706080906090102 74
    0x40020300702152500c0442c1046d0300150403182c2c1552010500440c3c02040d011031441c0d0911100c00348044030a400710307040c0d51a13001c412681d0780b000b2030b0098204051200454030b1403401c0f003c2800141c00303514002c144c254581f80040c0490340301b621244c1c0c0c2d4020a548034010040c4014089030b020808840180c190061108046035440d8000c0c8550f08550340000c092400d40c2c0281d108001410f0f9403c08001a19160401c02d0395400b03103070288150781d844101040400350700c600011881110041604d6004042d4004901d001d0701c09160410000040020504401911480500410b81c0c9620007040f44a00d80100740e4645c0070103800558107181856800d2021031000011034001c8450f540e042c000e41e08500004584180c42840000f110604240d0744054103070417000902000241130f9130402505540d03000d00b858000d0900c00d543d8050f00303c401c2088030b6030f1841c3c0c00340030005006040c1a6804c1283c8407198104406600035201040c0c2450a0000e80c4008218013a44280700300000c52a08005c0303013 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 635022086 1250 635020836 635020889
    0x705150912030a090804030c0603060816050d0201020a150906050c2107090e04140613020a0b0d150605040e09150c032509060219120c020a1a0310 64
    0x100c40c80754440d001020684a800641c4400301190b0424000c1c0d498988034940504050f05034840c00d800a42003103004200000d000c15030081d0480c400a921490500d0003041c4540742c03040b138406a056014071074007000812008221003c04032001d82000400b00000d1801400b00d440144c001e82e4030301030a000d400319244242d00c0304400c0c60136280082d0102e41d9a000700b142d54941e40e8110850728003680052104010086d12800000040c207803d071003459903901c00e105250038107494003952004101108100c501007510040500711500940841c50394030b40440d81083c1c61040d4041000908000780812480d0710418100d500b100040000e80541241c00c0200300c220a40500304903203040c0b002003c1500c640710307080002141c00100c1400280200391240c06010980b07180f0030030700035002c0c2550058000c0c02c9468007407034899105490107212641c80070116030324007002c54200e030440c207d484080340b01b16040c003503840403051a086085c3c1e24a8801c2c0f07108007000a0358015500340e1140b00302500c4681d03e21 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 635023336 1250 635022086 635022103
    0x61b03110f09031e070e0c0c070315020412050303010501030606050304080405060a030207020319171e03060a050a080c01120e060f070203131d010608010b0a031109130207051509 78
    0x20005039292490707140020304003000005001e420609086480c0ca58140201700c00d0102c540420b26008070355903100703200e0700502c03401510381c41c65004170000703000182c0303056145052041c0c18500103003815102d1a8500b58a901000c3c103840c654130100c010003481d0303031600400c070141c802d40c50003a0660600d40e43d110620702541c0181d510402d4042030003a4160300c281d040d901110f030010b0072568410840e2051030304110110b0003d0b40c0d600c070100c00270108500f003030045409046041807044454840d180410010b5003014002a83c00311101c2000030329039540c000d0b180094a03d400203002c514850306c002425200c6030100c119080ba0a03c10605108040402d0165000207a103024084603543d480707080741175200c0c1184002d50200690f001007190030300c1c0c0c55103003a03022413072140800382c1e600c036074040e191103200b440740c00c19030603040112840d030703503c81e4002201c41e01001034540c0c18500d40000065181c80d43c205401c41c855800300c2c2000901c43d0402600b5883c803050160750b412404c1900d00161100c0c00d4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 635024586 1250 635023336 635023357
    0xa0803040f060501090911010807090918060203070906020d0e010504030b071e020307020f060306030a12030207080313061d0304170f011406130b030a06090816061b0311 74
    0x11001034103100c0c40a0203040c026501c80e5081000e0f43e118440c02c40105803024090710170030381540301c0807100d5000c3e02035940100e20a0301e40300711803441c041590001c3c040c2800001514585180c80c1070000e0b40a0025602554494680c03441b164103107039009250120861200c4100403000081c2040713640c10000303c40035241c1003030340802e495481900649904c5490b0307040240c1140c1500f41c020b240c0c0e03408000740950074401c0b6031001071400a80c00300045800700340c0c0c02950580100f0324640010303a03480d130384070b5820403e408c000d07007015216185c403603e581003181c0c0e0303010b43d90300300c840300040121a10695140381b50030b070780404082e401080c9140d0741c1d015902034944100300c0503040d03001c2241d08001c00340b02e40180c10001e0040c1e103100b0712a5207090006540050241400c26400d5200c0d00c0e0303500404a1180300a0001d001e85411758841c58090030b0190b5040e0380c0c08000f005041d00360301081c040a6412400748070041b581a142080e00c0101101d41305200081514003510380c1c06004251084803680041c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 635025836 1250 635024586 635024603
    0x30c0403051c0909050702011b090f0b0316081b03040b1815060402090321041d0106080a02030408160b040209090106061421070e10111f0e0f010911030a03020a 70
    0x11b40c0c410030b03401000c1000d0940000300e110000700c03030a035903c0307640c01003520f407c00c907000d81107640c030f00c0c0d02d80090006441d102107984510b5809008144104103e83c1e0010718200c0420101c0000c40c2c10601c1380e0310581302510803820100804c041e081c0b0141c0190700c0d00c2607038001016002c6209034a0f0a0021026003d07510890300014920000da81c20070040e03121400c20039050003074401800707211185a2140c03003456280e90030440e6104c140d00390b01311000e0403500030743c44c0d2240d0f661311490703030303038020342c00140100c401c100240070a4181c2816481c4201800707100e03083d224100d0501d80100601c210b8020102c0102d81c1c1000c03c04d0142c030784e10440b9071580c0f0100710b100700d4442e10700400c8078402800600046c910304c401c05c0304105210b5809003012a0900041c1c5000c5c00142c0065421501c0c5c8994004141d60303644040388919118021102100c101d0303201e5040017914201e86000203003402140c18054030365170b451714a014103001c10781c82d02d00c60704d4000b24014a0f41c003805550103922492852800b920041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 635027086 1250 635025836 635025841
    0x3090d051f02090a080313060c03090e010b071a1e04052407030c0e06030c0c0a1202010c02010e0106270209060406032a1d03010f02030c0403051c090905 67
    0x40e0821080c0200022407000d120403207034107950340d002500a00d400c107104400c900000110f00d40c003c0300300c48020414000c000040c900b001c6d0140c841c0d00c10040d08504001c0c0c4041c0c00034100c05102d0445010344034a0710280e6481c2140d040001516101c0318031140a01c211000f40f0580480c0d2414842c130480203c5000003103545c490030140e00b4a22102c1044c40806d2421100701040b00321100160302c20011500c042100320f403110b500712000005010265008113040022a50003290003016210a407401d40440b11400d08554407225907031500d50503100503071f4480c3c45020720242c082c0160324001920600070007a042c07401c0003004102d20040341c1500d0303e210002d6800c0522405404a54035060064443d0340e58036900d4000a0003403540d001d81c849044000480455060140e03d00b5008a602c030f5990038041c44000345c07605c00810f80b010100c6a0640d41d42a1044903009203002552180510080c12034441d803450404070b013051a04506c18483c150005440700c400c0e5045a08030050359580341c2c000440b039 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 635028336 1250 635027086 635027093
    0xf072c06071203050402100f080109420b0f03060909030408060106080109240b0a0201060305011112060306091203040212161403030403030912111c17030903090d 71
    0x10712071140003510034540012a00c2465405030095401240b0a41e0040c802c44801401124140c0405d076040d0005550080100502c40d443d03004a221000d07c440c1e10003941e41c140a400f01070001c968450003107050030050741d80c49980c0c2c0b01e84160040c00c4c107241003843c0100c2000d411080d03210040086100d0341407540410780354201041628040c00d26038088818550b16000b000e44414030074440d441d200c50820b90090040c40d85811048070302c2c51094601104a03042661103140340d0482590340341190360350100000130500074001e1500d4541e80754a210307502c40f00b8031041c1014190041c4468043d51200040c443c9003080026000f00e01c920301100c294a949561000034441d180c070355050034591140600401600d9032050f1603804450701501281424030743c00f000c0c59160f0143c1d100c0500460300398031041001c10a1f4042ca412110311809407426031108080004100440104c80404403e06060000c01045030034080409101043d061482c00c40c0390000400b0303130300c2c820400ca9070b004035000844071040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 635029586 1250 635028336 635028349
    0x20d09120c05090a090f0602071e120e01022e0e1c0509060708040305100b040501120215041203022103130219050405160201110f04170c0a0308030f072c 67
    0x17041c0c0c4501d00c8140417859040101c00f0790800103081d2002c0720f00f115403880ca1700c21a594004c1d2203500c5000901c803e0b0300c481e41914400040052507040d030140509008140c1840411071020705460300e100782c00f02c038980000c0c00864403010b003c290f4580c0b1005201c0820381d00130f09c20300892580751038450b6a940c100404a1036500070100020700d03228020038040300700701010800404039401c8500c00c0100d815202c082009480c820320814620303070704180042c2c026050038282001014500c0300c201f0f14050340c0b4190504143c541100643c0140c200c143c2c0a9101107410312254100504481c1300d034110b04014650340280d035083c880091013030b1460000502c1c084600c2641e64024503004008204a152600b450003178119004100c4006500c0c190b500d02d5000c1d01d44082d40e054601102c041c60030b0a080500d403407009401480803c84900c54a030700b804603680c03000140005144240304803a224148120050901c0c0000b818090500840f1100141040310b100304100000355001d800e03007030782c0f660b11010850303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 635030836 1250 635029586 635029601
    0x40305040305030406080f0f010b0d0c051201120b0c190f0e040c051308030414102003120a0b0f010e130906020703110f060a0c140a020d09120c05090a 66
    0x2c2e4000030500007010707074000264a200d0300103105801c0180e074460101c40c446020034020046420824440c01216100540c0180341c24519414524541020b41c47c210700400c0099000c4000003003486020010490342c40710103030300321240306411401c200c002c50b00030382510b2000292204101031850301c82080c621602c4c0000d506c2c0700190082120309510340e0028900da1001c15886001c125417540004d001c5000000c9400316603c11308010460b803455010401040d040b012008100102110002048100704081100c85942000110350360b0040308031a50300706100500d010b006500d400401c10094071400c04500144a0910303144104c204524002002c10050414891105240c0301d411010425264010203c0303c2c00307500d40ca1907629070910030654076500501d0082c41608600007256058401e6040080c1024aa0401c40382c0da01d20a070001c2c4154200411000040e401403a108000c10340200180700607207428005606170070320948a00c000c803480f45c410a801592540c000a802034140d60042a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 635032086 1250 635030836 635030843
    0x21203220c0306140105040b010903050601050f040e060f0f1303120f060f2702071e110402070b0a050106050901200a050106030305070507050604050a180b040f062111090403050403 79
    0x8000886140ca11310300024068240154036080e0982c5a40d805541c05404882e40a001400c040e0300306018880c54180f04009590001c0d02c540d03540d88580c03010f104140c80391380e01c0000c1c824249400d01e0105034440c0c000d00f07189652031204081c40e002c0b07030703201c1c40c10211484040c03401700d80440c1000e007003401420707654405050402501804220000101304003c546151909c03050385100c8000030143c12480b5141c0b00500c0703140c100c00980d40141c203011659103407901901c2c555140040c1400410166482611308030f070354040ca401003101540742c0b44035180c0501113515101d402d00484100182c40d0301c1807003038050000a4030304144078030035008002d202c0406610074000c0c0300b40c6589140150081d00211402c440c140581200890b544c202602a5401c07034a000302040880c038074207060079503d03044d4040c461032010745840e01524551505d0140351003190641c1c000086c090f16111000ca08031031014511500525066582030100c2e0103800c210101c4941181d0f001503549030343c5000c0d54213124075803009 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 635033336 1250 635032086 635032091
    0x60f29120607020c091e071b06020a0c02120615240f07140c0d0305030c1303050d14090609010e01020a0f1b051f050f0909010e07021203220c0306 64
    0x200319800300c1d002001c04400d80d08020705031241d289505410215140d4224041c0c621320001f08441d2040e0705034044c0c0104640c0044c0c000c9410b4171100d00f6a0700c00e884010214845840f0b100450030100d555181c191802d0340501840e00313000130183c94251402c1c2159118803c030300b407010000780c080444c460194043c079070640e907102d80e039a0071481b050f0414031041e10761005038034103180c50300c0000c00c0e82d11078101c0040216900d009103580a4585400151403100c600c8070500c100c1068400055450b00a0341c0144000c21003150900c4005191003004c90401507040b0062051a150b5203070380050300d5100ba000d0030241d2103c2407510040b8070b0050b03480c10180501ca02c100d88081404a00c0442680c0e128980500c945015120018072100b500540004c1c50a1140701481048803072117680686100340c11103107110700d006c290310000b0f4a442c400b80c0020001600440511104035010010014020314001d6000c1c254500320200201c50402c1e40064121080c00c0440740d020001100d01c0d043c05141c0c40a802c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 635034586 1250 635033336 635033341
    0x3100902030a0903020c1207120c080d121a150d090f0b0402090c030702030a11030d0f1406090124030908070b150114040b070f02030304060507060f291206 68
    0x60142c40d601c43c0075005406100c860041d241040c020b00d002c43c50724100204940b03445c0210b06a00703982d0845081d11844005400851144030500a0070080ca0391566454146a0605500c4c0100c8000c1010029895940203891140b0f03150784079401101c1840b030a001b41c840401042e0040600200380300149003004010440d8204114a11035038045c2d4000d4540500603640d14003850361511080e41d0840240e030080c801e405110f4841c16026240c90b8036035040d0307810643d01e0b5a60798103072107500c10004100e0751142204036808442c00946540004115020702d10b0354501a032089040e1315000c00142e800c1100d20303d45000e180a508070308107461340001003c1d60b4031454180400e00d408151103030345159442540c1544690701c90107070b5200314100040c03401d02d400d1514082c20002d51010b0800c80d28003400d40c6e00a000360303074140301500c001d1001e0344580313594824601d040801c85655114040d105c614009441c0032001b0040401200710701a518121090b0015038006142c1c1070f80082100e03040e2160104 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 635035836 1250 635034586 635034601
    0xc080903151905060109050906121c0306080c100c12170f0105100c0c06351f0311061812071511060402100c06060e190905070b0310090203 61
    0x101500640b001c0208001030b0312400011281e6580e0b6108051b4400345031001f20703400d4a400740d56401c600b0768000403a0790035241c2078089030844074968a0340f000b00b82d854a0403c4911400c0c007210b6401e81c403c9400c45141c1d05202c1001d40001e46151016086400d070f03504400c40c10380103c4e0b050080450210307541e1464035200001d0114a50240200c0380a40d00c503064044995000e040c0316034656034031554151109007460011204403100344c1120680407003007204031029540f40402c0d400c404100044442891601c90400a6900f40c4105a0004c102460300300f00042031001c803440e119603504644481c1c0d100095402e40109064041c880c0d40c0c000008030700701200210004011044401070310681d0921034100303d0903540000d12039801e02a507000040002c0c0145400c034035140c1281003609108000b1001c5845000460b03285030070040c0140c1510042c4a4140105100c18059580d0f21109002e020103c0d83c64a80fa0b5031103206118640c20044045803070243c1e04410280a03040040d0215120b151690 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 635037086 1250 635035836 635035861
    0xf03120504080403110613140604030f0c0302030706050f19090b12010e0604150b0702060c03030901060305070e042001030b1018080601120803190e0607031b0c08090315 74
    0xc001c65403610107445003810f0b406c100c01592100c0c10344030702c6500b01600e030000c10749169450100c001c3d444503040001000054982081c428641d00400c118000c0c9030440c4113051a10b500780e0000000d204052126001c0c40c0c0995040b50301001e0300c0c0564040c12074800b4000d4405141036080b00c0e03c05000814068031141030b03000254121100e007100300100d5100d03241030008503504091001642440030302c7c00e200a40d280d10061000d184080c200510f06050528101d0a582003a25101003a0351901810000c0c00380801108014040d00c0d990101c6901701555080c481c54000d004120b03492070180100380450b8080e5110066140c0c0180992a0740350701248010188030200c401d041074031030010f03800300718034000091540c180c4e00c81002c402c90542c0c0360b45401c00309820040000301c44032240700c2400c0d000c0005014505605c0604e00c014191803c04030300150590f50003d40000e2203500c40071010031000d5000f400c802442c0c0d00541190b603034114440c00720b030a01104100102903140c0b62003d00c4105079529 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 635038336 1250 635037086 635037089
    0x61b1c030903020606010e060d051506070c0807080102180405040c05100f0206100e042406180c020a020121110a0c030210110307082503050907090506030a0f031205040804 75
    0x2d0303013034030000d45d241c00040d20b80d0301d210b8151701e030464420700c10800c0c0c400c81980710070380245a09009005000820300000c4c42030f408008210352010320b411080040032800c01029000e00616802541400343d04980003e0b140c040c0450f042c030581d1a000400c05000d9a0300d1850064103010705080e040c43d004c6e520190001e000507260308014425100011150320700c00942c3d4050710b640c0c1a80354072030b440d0b680304e14403440038070485040d40305410401a5003030b0741c4d940b003020003d142c400e6400584012800d00b0f00300b140d526403100000c0d9005020140010b0780c0c815a1f1841c103a4611034070182c013820350095900248000c2000082c1007000150000c0099005449165054480e50032101d81408a13020281598004054020300c3c040a02c041b645190203014615800203504915a61804009403c000101c5a40f6840c10119580d50180080740b8070500208000d450024002e010504014001c240d40c1e00340840042d00c510000003203002010701c55a4845450300c5c500400f446907007050f0610301040e5105 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 635039586 1250 635038336 635038343
    0x6050108150609101e110d03150906060f0f11060a0509030f0c0a051e0d05250606060e0d11040203070903020a0f0e0a051519091d010e03040302061b1c0309 68
    0x407017081018815080081c828070700c0360241104980142c001e03030250078400b0040b036a4000280c0003141e004845d11a42004001580e2403203184c0e04503031809051500301000160820942e0120503c41010015200f81c1090706458005940d9030ba0225050550007028040140c000c00040d14080b100d4001503216419802081942c40b4240d1050211441c0f40f0f2005c1c0c1400c168000d121f8a04125010703a002d0080344140300c11618130101500c68031465a0364900303044030880c2c1c0d140c20601ca0182d01c5450300c44560400d9030000c2540c0b480d80c5a500d0180017207501c0311304c21754000000400c5c480c496400d4100030356010740221003007038861104020410b20380c001c41c1c08889032100091200010350041d180500a10148004400803840038408608007546c08140494101c81d8006080301d003510400a2000c01005641c0103d00d944030110f013500c2c07a001507800355600a20042c00941d0740d1404503030f103882d507040aa20000350041007460500410f010003100055030340200e40041c03609500f005411a10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 635040836 1250 635039586 635039627
    0xf0304060e0c0a0e0915012315041a0c070609031109070c0803040507080d05070c050a05010912062702091623120709030201120605010815060910 64
    0x10380ea554030355801d0b464400960189507a00200412881c48443d150462240004d40f2041188404260728a0b4000ea00085540a041c03c440740c0d8001940c2c5040044c480c1101c0403281c1280070741e80b01d0658000c50080484000d59081d08001280034034049a003680d04440984140c00d030f5800028215160500c4140c0721300340c1d017070607201d010f00c0c0c15041d940c0b14005030f444d0100f040220340c0f108a0703179400040044540c1d00c101d20012500d074804100740302d80d40e02d1940d6100d585071210702c1c141e2040c400340d50240307010f00d0700804280016030300320142c074003501c80c4590b45004040582c1482d03006012000c03200c10404808281030440c06c07502c030303042c0101d050003621030059546500110724020540d101d640000a40d820300000004095a10b2916116042c0100c050800340c0103101220701e6202582c10a020500180c82001196000444032000d000318000401807286848006402080024410000030350100c45041d030702d540d41002e03101000b1001c0d04541c420b080103140501018103188144030f1158 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 635042086 1250 635040836 635040851
    0x20d1a1302040e181921050403080d090f06021204060e030c25080613230615040609050a0623030c040f091509033b06040b0f030406 58
    0x905a008a404503900c10280412541d95001914004000c0c1142d084039800303205003102c0001880314011442c00e00074560881803049141c1a0030307110310b041b5014401d0081c24442000840c40390001d03281503071032000000c100d480c1c1350315004400300c1031000300038902880450403030080d0240d050780b5481a07228000030004001c503d40782e00d99a00822981510652002c511064415524030a203840e440289841003101500c50f0502c50414404940c0300503a100409001824001613038001401d403040a25142c0100210b10892610b450009010302c2c42161481070000071501d895008900400401404100318140794003840c014054078411110040390b40e07100e080c0381c00e050441014000d40014010241c280301482440301501c1c001d180b0314149982e4507131000110300540000280101041400940e1040900e4050b0007465506085511008840c901d1081659581a84e6420400402d0218070940e480b0000450701d20841d0000140104041a41c9450400c1d850203140a58440d620030720210 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 635043336 1250 635042086 635042119
    0x90a050402160609020f0d0515060616032f0105061201050c120a020f0a0210200405060318032205030c06030f041a0f061903030918020d1a 61
    0x20b00440c40c07030089101c0101c10410014010703500c20140f0910140c440001400f02c0030024020454403001510543c000f0907c44422071100814194046000c484860421401c0b0401c040702060650b4000c05101ca40c00c81d038245411241041c88051020b00340300b01148540320b411718080c00302075900c039001d00804600d00702d0084040c000e191051b070302c400c0900e050000840308034008503070280107034400c16401c212142c84103070804003c0056404540040480f00c0400c0c00c1760044990b40b07031607e40d544011743c03c00703100010040300300d030200c90048491035103a403140019406007808820705407416120010320031072842054450003111605500c0c00304c0d80d180e078600c1816120180c019220b80c0c804030400015840c407071b9116003290024010111102c0701004002140400d400640780c602560402c2e100f000b5147c58180200064101c2e55100690260b00e955006000c607219401032012100074003801c1c0d1036440045e4141c8407006c071465420301910b070f0403500c2e03003038003503c003140b0070780111034001009111 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 635044586 1250 635043336 635043341
    0x12031909140414061903020402031006080f0402091816060906030c0302040e01032d06060e0109020a0c080309120708070b09031602060d3b0c010c02090705090312090a0504 75
    0x301c0310440c99480c03c0740d4940040020000e40050041ca450901e0303800032025071078a2000c0d61184118041e40078240e8100040a02000b90080c11084403c03002c00811005894400415070048141c00380304204440c0700410508011036901d000310003c2c000c01e400214a9408135541040710f801351420006401d40703000803400c0c1e125034054801c4402065004000003a80c0c4e0a04428580c440c40040c0743e1030102c0d0401c0040d04030716003015120540c64200500404546400075801030401450852401d00d40c0e000117096000c03012006002c849020001135488502880a660101e03140071180e43d07603400500c1c20442a40120000b61100ca981e031000511403c00001101d0808180c44800240c1c4013055081201591001d412980b0450325400c4c1074080707821421400b490340c2e0b070100c428480c40040c1281070400000ca00b168003090b42c00f8441ca40b043d42d07004408050340c1501680c400e2079640d5080000c5c2e1343e42c840e4142d081e40500c6402c0341c1c4481c401200c4054040c4c1103003200c40f6072000746c0d160700308000e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 635045836 1250 635044586 635044601
    0x2090d05100c030b1813050609061b0307081f15030e01140903030c2a01020711010201360209040506070201060b120c09040902150d15080a02120319091404 68
    0x200306055126017140702510541c000e40c03001c1d519400d00c80c428407680d100c2c0d04041c020398500780e00307a22074001d1203a40c4000403040c0c050001d140c900341c2d0551401e020000c0002d407002c3e000307155a4000100c80031100d800c4050400c090250103e00c1c2c40108c24400d0014000c000c1d0400c3d00e00c40c0e5180201d2230304e01c403c9103408140214100310045045894000d4400d14651003a00d810f4604190300140c180343c01054072241c40c44403202c41c0016200d0703c1c1810a030b001c151144e4440707411a40741c8050701400400030040300f00b00b01000c4400081d21101c44c400f2280540c40901c0185d0b005440104006c100000002c01c0c502c91661076009100d00e60b501c42040f0140e0007030b01758541000c9110070020781d01c10401c0015108494000f08007185145254003c80c203000d0f00544421101c02c2c000841c180048054000d803248802c8120030210268a4000071343d455046544000b84181400c00e5100d4005100704140c0e1058940010340d1481229a40000382c81c0740b00b00d129030300300c00702002c1410b1807034509886680c1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 635047086 1250 635045836 635045839
    0xf040201020607200a030804051b0109180908180a06030e030d0b01020a150c031d07090b0a1815051804060e071e05010806031b010e0402090d05100c030b 67
    0x5003030f841d0b44030180c03000158640d254030000c060420003850510200010102e050080e1102000c03401d0a003403041c00c1c140e02007004c1400142003c0c55000690b441084a81151103040211420b0b10320900c1503c0648103101e0003070440c1502150f4110207007442d5404021821089070341c0c28141d40e0b100c0058060320404440c03000340d50024410b182c0c41c1c100f02d42020084a0301481902d00c0204035039a0380a080c60b9082c01c00f001c581c0d840e61501a03d98240c0300b0008200301e0680e404002c8401440e00965070250740c0949401d403600c0d1400c059454035148d582c90017401120012a419840743c1c90218020801c1c00803143e058583c0764400216410304481084021810f0b41180c00c0d180c1c1c031610754002034100c44500421a100c0d4500000300ca884148103041204c81468104185515080004001d040c01409444c07103900950600c01c40180120322078070070007000782080d40f0f01e8904040098000c1c010300e0001a00b03c000c220000d010402e010614003030f0090140b80410015403994022000c4840d00c1c00b085 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 635048336 1250 635047086 635047093
    0xe04080403150236041104090f110304060e010606050702090a090323090406080f03070b06010e0604090507030c1d120111120f060d1218090203011206050f04020102 72
    0x1400411401c08550220803590b034009441c0000b8010283c12608404031800d88540b03080c100c06034003581080c18246449000c54060200d08150384108620f84250312560440e969200348840340e182103604400450006020320a84901d054108900a841070485001095103042800b0400c00d0003101502c2e561a006442c80b0a00c0e039980390300710002c3c049401c2c25402d02c00c0c1c580c00038840c01440440d141040d00420040c94403826a2018082665001d0f0482d8010340c0003140b031740d0034103000013060360007190b0413503c40d0004c1d1312040c0050f112031071040c440d03680082c3d0000e400f0842c540070382c0249000d148540c2d000c000404211404903841100d07108405400c2c4803000b608020b038500215166101c0e105400001110240500303545015406030700442e801c14407040800c44c0d05e02c880617059130320034400c0da10b9118a0310141d0b900c1e210030f1103d60740b110038070140d0300ca41c10441052102d60f0000c0c0a48650842d40ca503114245006030003041d841c100c84c950305010014241b1804c80b40c01c50b0090754181c005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 635049586 1250 635048336 635048339
    0x11a070609051c180902031605030a06050a0b0307021b030309060c010b0603040f02090a0504080301150c02041406190305030405011b0804060c1a1308160b010902030109060e040804 79
    0xa06015044040c81035507648603c030249400480e81c058483c0001c0c10399150110084641000d8042c81c444aa0103c41a18414810400e13034a5048100402c100c5403490f11595039036801c401c10006000239042a90403110018001c40d0070141400150f000d050300e80c00301c4658840b4001c4400c0c60b030941c0d8884942642050200710503d08001c0f001c0e00c80304883d50000308074003a043d4041985900100c42c21340e00c80b4900150b04d000c0d070915081c0d580d08000072140c01c1c416403a05071500c40b004c1c803061241c500c0c419140b00d000c0190a204074203540c28603074010014010310345c108001d82030041041e00c1c418461600a0000b0703007842428071140044a40c000041c5003024500001950030ba81078582c02c1e103548000700c0c0d003440050f1070b49000b080546400c0e1100485141c0f5070600070101071700c044005d40c400315024240180c2d10f900d044030b4491150300001d10366690214406a0078a00c9803801c00514560202d000032030492101d03000b4605880030941c040040640d1040411402c200a86010303101e407204200 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 635050836 1250 635049586 635049593
    0xa0e070905100306090e0102192d030216050114060d0b19020702031917030c03060919060303020a12020d12050408040509090c01180b0a121506080f011a07 68
    0x80403000405900780058407507030300c442e40c5003506d4003c183c45c0e650ba5070010707284914900000c40340c460407a40307242082d481c03400d44442465102c0c020391031a841c6d100034200c4000d201e100360110758285648600b04034007441c442c50841e010f05044019891a81241d100107041828150981903405402451079600303515541581c8100c0c100004803140303429002c03c03400c005a24208054060322280ba00c00038032910341410f0030300044070000c41e106a005010024001c51814800030b40e41c00c490220340858103501c552103403c5008640321100006c0c0c1d814080000700b41070b008109109402e0143d01d0020b0203a02c68441207031202c000000c03100115220790b06030041402107a202c0d0707a215108440e454034240d1a41c00185050740115200b54043d403201d40c032081156400b1200c68a285440d80c1809005410200e45200a004a210704010400040b44944580d04250010019090780040940c1c91a8075098021305502c411a0a0044824803400010300301c2c40010448410f0410725841c03a0030041d49a5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 635052086 1250 635050836 635050849
    0xd0f020d030203090c0306190f06060915020124032604170f010f020a0f11060604090c090f0207120219080703172404090c03030e0316140a0e070905 65
    0x2005142c017403154003901840e035203041100c2809189144070000c0302100548030300b025115180311001da0141004403c01095403c02c9a11041e030f030001100c850700d074000c254101c2c01443e0503a60301566050080c2c503d40c00700c14090010003980e0041c030010b5070308090401305804089412441402c60f007410041080300c0c003801c0d000d400c00d80d14460305585c20400b04c411a142034904c4040c00f1000960700040301010309030001c086e0321900580703040c50642c50030260b941c140c48940080c40c0c180260b40321003034001000718186800002c0c04411808000360201d00a02400035000403004450f0f00d559415849c05107070001170507201040321700d00036512010042e603406c1a6500018011424840d040d00c1100c0140d101e03101203845182c104401c5000b0440304e0829018410240c0341e00c5004601d00f030038000100d140e0140445c20340707416040440c00740c2c2e54000460700c1c0c4410b000507030380300400c000c402060707020300c1d480d4840704040d00b242c4250440e030b1210840c0400b81819505080441c0800038100120304144 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 635053336 1250 635052086 635052091
    0x8010b09040605100b031e13031409040603021c05010b01050705060c0f0f07060b030709090c140109050a1805100501080406090c1703130e091009060209061206030d0f020d030203 78
    0x1c0011010003940c3c5da00900613904260744d80d0b04840c05120589880350032480c0215131040c2d1601d100d10203c001e5032809428103080707841d8072000620004004a603901c881d042130303009640c0a41070000c020311290112040520b590f50485095003030a03800b000c00d40c814015202e01c99003000140c281d03502d540291101d5039000003010f0412140500001c20b010030f00c900500801b40c041c64010944007442030405081103440d404c421181442c0c0800700000c52400c01c041402c3c0c031108800e90200000d42001a00c51140c40e41c4019801480b50001141c07864500d203508580030f4105e40e05001c545c0300c11100d8000e8440c0c0f030048500080e50080060045811038002c04a83c500940c1d000d000d05481e135101c180d0f403801071508501c1e16440001c02c49402c02101d11100c0050100d1a081581c60400406081d01c41461803201e14400f600e0b840c40300180005d543c112885884000e240035074403513800b040030f1400c0001b29445031090246070080304606003e0b9680d810000c04c1940500b9400040b44015070003034102 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 635054586 1250 635053336 635053351
    0x20d080402180a0906050115120b1306080f01060503030702150702040b090c09010e0f1014040918060e01090809011b0b0403030b190b0f07051c030c030608010b09040605 74
    0x540c4140d80400d81219540d9000d0072403400040f84031300c500d0a16505580381a4085094202400b01c08403909900c18001c040e00001000f001c0b406981c000c00141101c4400b14003610854a03000d0002200180001d070b01c0e03807200180b8004c1c80302c0e1342e443c000c06841e03003c2c0181c003941012070074020400c3c0c100c40c60010a00903200400000d8200400c40c041070520008440a491364400000c60148035038000c495030b100c0241c1100c0d9400c03c500c0500115003004108910041444014194540c080306500145c50161040c030500b04149a104c00100d00d00c0c08807000242e410519212a12104d40f00c180940009207030803041c0c07580f9180e020030044401450b8071908001c400c8041e4112000180d8182105001e2402f9541c0491410300703040c00c11a8250100c402c1074500d44481c0420090b0550305004c0e50141c411a4450f281c030f0b0b100d1418040e00f00b0420200504131503070301307204000d03910390998030a1031281d00715a0100406602d0300021403c86401d000b041c2c2d0b0002c0e003d030006e0000740303154108a500408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 635055836 1250 635054586 635054599
    0x2030a051b07030809150309030d09020126070e030303041218090f050a050f070c0308060109030203150108010509010e06011a0c1f05060103051e071404030c1d07020d080402 76
    0x2592070060b0704021068004980007a000199407045140c104000c02103080c010701120315500b0804292582d9116100072502219158601d400541e8010b12519508480c6000d41c1c05170380c2d0403100c04c4d100d80c500803111070001c01d0300201e90902d2803d0000c26a44036551005ca50781d0320540c503040942c0c0354800c041101c448685500c001080c05c04107401451a541868107001c100d5080c509090b4040c2c0c0c40c01071080780a441c104042140081d4010403418a25806007045e510035241c46004944880894001a4145c422055603030754140d01000c01c02d0485651400030130903078490300040b178243c6981549900341a0302600c010b11000c080740c6038a00c6c44100001c2c43c2c0f40307013070001180603080c40b43c42403040f40d49904c80f401e40d0f9420070725801000d5100c8402d2038200038626180607030008407460051005121550640000c883c0d0f4080e0003115181c28809030b4064980d80e0724074080d4542ca48034020070b104020316060303500304078440c10301d140d00501154024080e1403c0381c00048841c1d10300200103a9000c40c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 635057086 1250 635055836 635055877
    0x70c02030705040c021f090305030c0307090e040302030c060f07090501050c1006080f010b01091503020d09050708030c010e0a2a0b0304111e1c020409051605010f0507020102030a05 79
    0x40c0c1c2c034403036281d40e8444c940141c40f10698031000c2c2c028407126184074481c400c0c03c010704a000680e2000071a64840200410075440c2e848090088502e0801d0f45c02101452000001344000d0680001c00341002d11207410445081d5521010346021080041e140280400c804a8007404651b0250011b00103d044050403100e400300561010000d0b6403c41d880868103401c0100082c0c00004c00f8000d012140c0350038208000028907001c203c03c00901e02001040c101680400d8844040140b508034011050f081811141529190183d490f01d903403145107000107644c600844a03040010214480800541102a00740143c4007004004443d440c504011303254600c2c40706011826100c05400f4600481c050b00c4400c140d20410000c2c01086001c814035018000c46403090100156500e201ea4144c040b44010240e01040d59880410083d203040d64000f0300c54011f0b101e00380000000015080c040310b0f000d07070b41c18010308003401301620903108110340a40160420016030344818000c5004129020900420f0001c15 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 635058336 1250 635057086 635057089
    0xb04090b0103111002030f040902070302100603030302030709140a0302061b0a050a0b07110601090e01020f04030f0c1508130f051606200a0f020a170106090c030e06070c02030705 78
    0x2100340c00460f40511803e4400340301d810400004144000580001c40c035240041c01c00b040c2c075000383d110341b03020319800040c44000c140c1300340990030070101c0701b0005000c50b50b200e150280107500300700c0308100054201c900c00182800c40500c000340700003001d03000d00071039800d54080c81031a510603803400001d80703044070041429400801c00c03008103a01800161050b0890b515054400440181203d0300b041142080e40309444c1c404601c1c1411a4602d144c00114840f9018002c0c0c0a40695030340c03c5589240420000300703010181480c2d503441132054075840280380e162095110b00200c944090380000f00c1100014008008610303074403500c10301500004246880303e1f82d0301ea1412a1041c2c2c500c968840095042142d207070805544402c41500315014100b070b007c3c82c0280c41e5600f58a002c007605c001030100e100d5003551202250900034050700c200d03070751a01e03160000070740c06000c55102d59070707000c0d10f0035031070403991403291152015490008000c0d0405498040c011583c82c0c0401d10180ea00d03006490001545 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 635059586 1250 635058336 635058353
    0x3070b060316030305093f100506031c1202160501110a051b03040e0a142a0d060b0c161208030a0c090504051602060906010b03040b090723030c040b130b0409 69
    0x34581d1f041841400e100e040c0504288218642d21510707401c04090004640c0c003c40c1080700139402c005038120070f08004004a610b10079030707070345c0c024010301c006066040e0300d03140d8061500b80c500400082c0311039940221102460b104001a4500041c01407014040c021008101002d84020040c00c680c1401c1d2507070254810603505666800400395182c841c4581e007090144140d500c440c0290a094042c07203070548003851981c0585007022048400a05100c001e411035024902400d002ea00503600e49154410480c1d0782c0c081200c001007040e5134044000b814401c80c4986140072680b05641c10304549480b14002c016050040c404400d002c100c2d1004515503e1f2445050b00c17800c202ca4042d001d0000146000e401e04030040d008800c2604104018410040e030b00c800c0380c0d00194481034500103540e54081641c02c00600d41c01001c98115410f0b00501c501c060300002c8581c1c200100c05840036aa17124041100704d40303c48901b1034100605021240c00a1140e90107246c1100d0f0142010820840b1590342844 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 635060836 1250 635059586 635059669
    0x6120c0f09031204090f290a09090c050108180709021b010c18141c050a08040b030a0b01050a1e0c1a090d05030411190803070b06031603030509 63
    0x51580c03001c9810440c1d13000306c3c000c21100d0350140104110440640404a000d0040440c000d05882e400b146403044c2c3d51100100355000749588541045244010b1400d62454400c0344141c500007004500440c813550080380401d00d1171f0151300c00a000e0349240080c890080c2d040510f48860071900120980800c010a024a070a64541903844078020050020031204003160350b0446040c00c400f806c030034603040c0c440c6080300c01101c2d10f0316021072903407015241c03861500c07411890007401e01101040002c0c248100c4405980246501ca106200d88140500115400d0141181103000100010500491881020501512144145803169003078005481d18a00a00c1030943c4a080c1d50070300c0308020b0114000d000c1e6007804807507031400d28610300f402d0326142c1702e10348000803152056480c420a2209041c800304490010b02020302070700c2d19000242021044901e08455043c01b074090903940c039901c1480010101c003aaa03060310384a05203080381003401036404042030307800c00b80c00704040c81402c1150b5034100341c003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 635062086 1250 635060836 635060863
    0xc05060a0543200c0a060504080604150605030316020f0111030702010309060b10090e0c0304020a03060c02010b09070201020c010b060c0a030809010905120705071d13030c140c0f06120c0f0903 84
    0x4c1d608407000074022582030303a5010382c0070030000344000c3c001884081981900103404c9454a508102c3c501d03130744401000b199000179458400060f400c1414203a01d00300c8203000c1d008940c21085541ca003401510303203940c0700c0350114154004114540041d8003d504c02040d160090000150480403880400c2c80800c680c860b0001050441c801044a9540c0c01e40c0650b0101040d6040781c15401c040c0c5c00300d1841c400500005006c2c64545500031103092017544000c0304280700030090703001b86c2041c400180c001c0d4444010b00f92503500302980603501e4106407003224854501c400081042007001d44007140c040300094080c02380c0355207a0b520600403032810084019003030f501c90030341940c2d40c01ca450101c0c50013a607a4849414070b5100120030504a050144881e8007103c03000c1024103070301c99480c048403003003078840c0000c01540c80ca04c00550004000118030342904802e44c1c01140c0700e040c2c9020001d050140c3c690390300c01da445840024032400180405408000030341d801140c200004640001e0030300820486d0030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 635063336 1250 635062086 635062093
    0x9051302031002040e1321121a010807050d0b0d03050c06150f0f0103090b010905060a0905061c02012016090c120c0c05060a054320 58
    0x1015498203011001841d10302e80780452806140440604052000421006550900300d00000c144200d000100001ca1022507806000b00895030010b04041c0440600c0f001c100d00e000f1000d01c0001a1307080c002c0300140141c444103075a549070300c01280c5990201d1301c4141580c0d1152207903d59900c4003240700e2071540c03290702c903d80c4802100c42818a8400700400381075000e100ca21040c001c0341c031108607040700c84806448906c200842280140c002c0d00e000f40d400ad00c065480d000000e9002e120b41e00140c01039200f2230b107000281c0c0e5254003007025202c05440c002d50041c079844402e0703602c2e0f000000491000c0d10604000b0b01240e14501d8844640e0031000c000b64054100d1a960054043c40f0501c0d0005401d8402c0d080088059145000701981c0c2c410542000c0c00e03540da8102c8241600500308211a07507448401c0382c03981d141141402001e403c052383d2883d81c110480d00e054000c191072020503020f03501e43c0d020300813a81258131007101d00c0701c030080c404d401402030310788445412905580f44564990381d542c004 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 635064586 1250 635063336 635063371
    0x1204050d020d0801091a0d2d0c09151203052a03030f18030a0207180908070f0f0c0e09100c050d05101707060314160c0501060905 57
    0x240c1892112165101150050191400d00c5078100050a064078400f0344000f0703040365110140103406500c84819607000e001e44450740304001d40e52002040402d10364814911200c0c44580b0300c002c20300c422200402c6801e8040080c460b000d0a54041010b47c1d034001450303c44a03941c0c004001000c00e28050540c002000004d68009522040414161403008501e1112651a94409440e00d90201401c030000c000d11480200d20600c0c007072a06841b0a000a80035030366140c40350000a580c64480b485080000b00d59810060306442041c0714003d64280c00000c07140c64048160f4800c40c8008000341d00b203030118003000001c0c01007a070440071100a003460030302c500c0080c04c0c0300c01c110389460080704102041c0350405290300e24070b55004040d62082450000c012540c4c0d19062401000c0900f69005480b20b411910700d282150400018503070300303c8400391070402400308240b14503c55a041110f4000074130300d43e61116490188603400d4041254021400080c41c0741c0c5030a24601940c206031000400c0c040c20300d09 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 635065836 1250 635064586 635064593
    0x15060b07140f030301050906010e03150a0903030f05060303190201091e110f060d0c050408011406010801060e060a050702010302090a030308011e030506280f0203011406090a0e13081204 81
    0x20b40010161824021411036142c640040e003240002030110f07040020011420401e074604000964413142090b401d081c0510f0070244150007406603440940000341000c00d0605512070798410303580604c1303000c1d003c4c610b482202111281c03409400d10b46842190f598050950200c0c1c41080c88500e200c80740c9401d041e500b0903038140548000c4000f032506200345443c02511f4a250380b9001190b030702001f03100001c02c2001d44103905a603507003c2c5034070110f100c2d402d0444100805000008462262100340c0320f0140503600c8600032109940c0f05400301d600040c0820006925501074009800c005205240c05403034460b02d503010882034607040e881140415483c10040c00050380800d0003120f03103060707004603210941c0b0316120319a40f082d0143c0010000c14100002c01003c202e103081513480311040c0a42402001c5400040700020f42c803d01ca0300d002c85841d0801c2c074405140480448041d41070007045030301d10a08207805591a101c010b06072060150401e60014005002c4001400540c61f2499240c13010307240030f04 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 635067086 1250 635065836 635065843
    0xc030b04060b030601081504140405151305101a03010c030c031a03060609180a050705090c0406050d0f0b04140f0105090c03130602251209080a15060b0714 68
    0x20400710b07180100b4002c114169900003e82540311007030001440b2014000c81c041002051010803200c40b0b01130b010104028000005440d01041e00440c550300300755075a14000c05249103100c8402800c0d0f03081240000b8010b000c81d00501c0001f444e005101000c0d180070300001c1e08403010392156102094940c85140d09084d09481100344500c0d1403d039034901002d1100000f82c558100408842c4a15101000715050b4075000401003440c4101000700d450100c04c50400030b980d0b0590b80320b414801e0425000103403101d1800010340e81154125100c07507051003070308240c10014000503455468400d43d941a40780c1e05603500e01960b60070292088046515081a0360f082c10914416001580a500e091086c40003800c403030001c0302c0c0d2040800c8046c29102c0210300d06400039109400c80450311641e0b008009180c80c1d00f451701649141d21503500b83d5500c80e119032041d2408901d61241c00c0040e04040c4800c004507016621071011900c0c04680040d07a592100d541810310342110b00c040c3c516100d0010310541e000c4042 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 635068336 1250 635067086 635067089
    0xc050705190302060c0109061e230402040b031507210207030804020105070c120803090c0d05070b0a180608010512070e18150a050a0612080a0305190c030b0406 70
    0x81d07032440003080246001c156040d4091200038000d07540095801801c280039800340e528581c0c081170138000b8420050b682140070030b54440c0d030282c8500d03001e0070264104001d1070980c0d0000885600708aaa40d07a9003c0200038513030007541e680c0500138480340c001311108076544107200d900203455483e5046009400480e03a1211603010105161042214601194001c0c01c3c2c1c0d0b502585c24603100760340e0085490a244000b1003075208000396940480204204070189014500c120500c03012525911208800c220f0003041d10301000c1d02a400c040818088a13808200030710000602c1c0c20310440e085249280c041c3e032103556500801c0058078040041c003052400380150700780300c60f122000340040b034240300c0c82548400c009400f01074082008110030038520380070720203a9105030300c00c036005a040c908140001d0150204403050aa5240f0740900071880c156000354020095400c000c0c0c0a08250780540300344e00034400a84001514059210714001d1064039005140b501d40d0255000f040100450f030520003078030601d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 635069586 1250 635068336 635068339
    0xc0105071d06030f01090c050c0a11010305060d0c05040b0301020909010f080606150d05040317040b15060a0215060103140c04090c03050114040f020c100603021c020d0b07031b0c050705 81
    0x10004d010041640c6000141566800400020040d070030b040103031402e202d00340407441540103444551060010304988600001c6c802e803000c1c80f40356622000c2140c1c01b140d841d8010315050310300c0300602140c1043d61100044800c0500011710304090400051100c0400368003901400c500070308103210810f020b01039240c00c400c040c0c40c0088410002d12a280c0707240559644c45414542e039030b00213028148101d040200c51401004013802d5420030f81044010318108940494024441094445140c104001140c00110f09a0f010340352010407000b0300140344601030030060415844010000080303030404a40e5008190140c806582c45203444a01c009480c030340020441454a42001046400c1000b1000702078410101d800080c0c25030b030300c08004002d006120f8840d286204004a1380b03000c085039401441078900848084500c060f054164416402c80e255009412102034282c9a0010307584455a6070002d001d4100032904001d003c2e080500d181074446100009a0081000c0041c86030602040c00a090b0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 635070836 1250 635069586 635069599
    0x10e060f130504050f0f1909030509010305090304080c010c060b031e10090c12031110090c050d0206040e0c07050d050a1d090c07080c0106150f020c01080a0e030c0105071d 75
    0xc04034940074a05c2c400070280509402000c00140210b5601c40660000d40400c40302000f501c00030f4100103000b034100380303151400301e86090302203928400008241c40403100020010700ca1541004011184641c6103a011280b0648580e21010290b60601c40039a0b6150308201640f905540f1800b951b20b444010400c44108500d0034032134002003040840300c0302c15a151002d901146030410b00e81111112a0144803007407070301419211410a08039500822a414015030807085420b448004021103005100c20095000404000403c0020342d101d1009611110b4190880d00b40800c0380c503214281a10b1080f140c001900029040c0d80d000e401900790000c40692500c00101950b903080800d404480140000701c4c00340c0003050b260100040541119000030300240203202e030380da4552014001c420f644000340702040407111f11940d591301c009580c00c5803240595441d0301c0341d00c5090007a0020709400d485003145000400c00d003080c0319001d026203405011942d40d14104000140340b103081007245c1c28025846580e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 635071942 1106 635070836 635070841
    0x21050708060f06041d0c0409090b04030306271a121e03030907030807021305180d0302040308070602160507060305010f12080a0e010e060f13050405 65
    0x70310548030565100c01c1901086000e0040c2c0c00707010b2402c01d010072103103110540c001510f5040f1900b410118501a240c010b1041951000760059600c070440009003c01c1503414400c0300d004041c9030104038080501d86110044a008030104600d00300c0c0c842920612180300c0c40e00014170140000e0000384d80c400e1070b008040d254035450820f90249a402e031110820548003000310780c4a5480b180140082c9411a540c0e550039030448182aa040141c0005400661141744188ca000c1c0e00b0b02104900d0b0844500d0740b1901d000762481d03501742014010702c02080065809401d0b03c00e200d92010000d40c40f0318031480404814841c0401c05019846603500c00207805405038040d90503103111001103c041a2107030001e04080e0321024004000010400030020003a00c42c1b40e1014000005240200440724894001840351300401d103404101c0c00c00184801c0d0401d0001c0494004140c10f440030312541c03 = true := by decide +kernel

theorem cover : BRFrame.Cov 634892086 635071942 := by
  have h0 := BRFrame.cov_init 634892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 634892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 634892086 ≤ n) (h2 : n < 635071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
