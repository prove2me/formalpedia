-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0962
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:31:29.297625+00:00
-- url     : https://prove2.me/submissions/1e1e1eb5-3c72-4418-ac0d-d91356d14a4f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 172841726 ≤ n < 173021582 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 172842976 1250 172841726 172841797
    0x309020307090509120403050307030f02070303090b0331020f0a0e0610030603140105010503190807111306060e03060c0310120512070302010b0a090c021002091f05 72
    0x100030300280c50410400b14003d0030004c00d81412880303080c1003580804954002080554007542c05540e036102c2c42d050180c900d0306600c0f102c808650001c0c2042001c00c2d8072805000503070765104034565513074031510398031a44074031444c3c0a10b0b4102c0300100d1001400f0451554180380b01d109454000200d001e400402051101da40f140506c1c4503202e90005100c1e00d0700e41d000d4440c400080c18001030850303c94880d6038450444515000d02c582d515030040c0b01c10310b03041024055104041c8a074903003407a001c0d60b504400740103450000305918245c42032400355a0781c241811000c0c1d00c44c1d640800400d9500c41e0001e041d94410700c40507009000e0000450901c00982c01100d01c80c1c0c020303481c4100d80e03a00e0301e010442c0282c8040410f4a0500680740000c08d44e002220041551901a600208600d454002001100b0139240d20009a4520700395004840326004941c2c407540244060006842d000c10034046540c54210080c031000d071200380c00b002218a50031001810007045104540003e01c8403840c1d40094841c640c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 172844226 1250 172842976 172842979
    0x80d0305100b07060e0a0507120614060f190510030903080603030405031f0605061201030210171305150405030408120a090b0702190e18010504020f0105031803120412030902 76
    0x20450764010440ea0341100148117414812203070042c0d10f58859a00b000c0081d0810041503081441900074400d5034001d5682040010040300351606114002402d044402c214850150079a0302c40303103030421100d54551004010242075a200b40142010080007000004001c80100e50494042040e90400000b964169040603006040b90103444410700f003040c440c91516071141d900c170300010410b42c03621030240c9020440501c6d41680d55042d4410001e19904290300002009083c001c03070381440d00721502d0706070004015283d08218501a092050502d47c1a021044880008206000402c10000000c004550412094503c106014403205103981719020b580400224400c6041c080c05040b0f030018a41e0500c014a0f00419050008200580b040154410690140b00c10100080320420143c1124003810740f0000300b220340741c2540094071071482c0402c054100000480014080e0401c21700300f041c8015418101c0f41c503222821300011500104450407203090610321117203c0c0c0280240520380b506c650 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 172845476 1250 172844226 172844249
    0x1110c0a0501050f1606090c05030d080c09150c0304090507050c060703110904090c0504060902070834060510090203040b0a091704080102070c0b0903100207110406080d030510 77
    0x1030240115600e0b000944c80315034001d0200110895458080e112543d00c0d0703c11500441c40030106c2c2402a034504007544154080e03040788018110507079000740c1c00744e8007480300c0c6001074454600d8004100c1d8101c9d44000e54012030000100d0440f2100000041c008840c10290141312940c0c0c1d0000c121454000d8801070005544040c1c04140824060b4100d640c0d1244a240d0b89802e103c0030b0070000f42030b5180404252250740e00910248171311b0400d4010170016111450095117880080e0752043d46d2480b0b00c000d41d00140500760744200d4504510340c015450464401a605086c40c060304100c00105001e80300301c0040e500440002511440c14020b4038030683c2c0000d08440981d0300c0e511400d0280441a00440365420041252011021f200000c0d1024002420005032030b0281450b017444400c4d52500b1401101d4014090301c102c030703940015541c0790100c04c0c1c1c0f0056102c01003407030300c99007003015120303465401814074030302080c04000011161a240340341e0354244007039215680e07a0741001d80c590191500b540c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 172846726 1250 172845476 172845479
    0x31611070b0a20150f04170304030c05010b04110904051e0f07091d04021c080a050c060a110f07080d060e06010201051f05153f0106171f03030302030601110c0a 70
    0x1c0c0f100003e40c01070241b111003442c1c51f4040241d048551084a0490202d94252002d00074000309200755107040c00c090381c003040300040000501d000c900601203001c0c0710310b03180d00026080f410384640d6490640c0f490f010740025420f010a5010260504840b0307440066540c1000049020000c104000f803034941040460312911030b60280315000c44200358181c440134842c4c800328001000080100001c24041e658503468119043c0707441e0074a007002d000089180d0402007030108204803c0101c0d185481d80b000390f5075071601249007410f03440c0074101c103610b0050320b0510f000400c410b10701e503545c1c0308903000d80c000c2220341d661400d010208510840e2141c1c4c0c21020001c00c0c401e608028100070340f00d10017003c0c0142000e0401e000e003252041c1d40180e525107580026252760038507034415610307501b21b4061030b5044034541c1803141c010200704040d03000510144108001c1100421002c00154200486240792180e040e100c0c1000740c041d61003500e0580c005800211421605070b008910701242000040860b00d10b603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 172847976 1250 172846726 172846741
    0x20306090615160b2d07051b0114010603050a05160e041410080c150a0c030302040306051f0b04051f03180c0e0c031611070b0a2015 58
    0x8500c41c070301d041600001004040c0200400c01102d40f4054030481c8140c0c06454014000c80c103002010051440411030101c0c0c880c0d0318900500840d43c01401843c0058551413410401c603491804000e200b2099443c201200382c1340e841c3d00c84107904ce00ca40c2d0700c2c148280c1e2200420f0341d0469108903401041b1f18003c1c180750082a02c81c44403074900e030000a01c00b0940c43d0010515001000d0f0580740b0684142c5440820007000405100700c203c0ca5004907248070341450940d80070380c00d0788140d58540f4108101c06100408040c02941130342c000d9904180c082015141c1450112480705402c810107010340489400001c3c0744008004a500781c40380604400e50740c42c944404003080312811310140c4241034541c0a201c3c18a8510b000380704055001c0c1c1da10414040c54012940d86500024005150180f8100100301009051111007180c002c001d00d000a001c0c61580300c03a90070401da0748c2010012020008550354526031180211103004d02c14040004118a1003458690b02c00c201904284171655440009181 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 172849226 1250 172847976 172847989
    0x807020d0215040b04030b070201090201050a0806010507080c061f080c0105090d14061b040e0708060406080303010605041e0e0117070b03012301020601060e1e0a080c1002010203060906 81
    0x384080c00d20309074002c0c081400d900c590400c0d00154280200410104103129090903540e410841a0000704400070807600003d201d84503064200040c400b00b00040b403002e0f4403c1d000c848980380c00c4803015494020202c0225182d0300250355440051181d12450114441d0880040c01200c0f80c41005000c1407192100540300358005081c0c6e50b0f030144500240c1c0000c140002968000300c80000d0240c00c642c6001d2000300c3c100c24000291200400007840700b44242141c40200c03d800240700d0410314825505c4400140181034103030031a855a00010000288041d04440503100b61200614144007280d0104104102d546081c0310b40d58142c100000100180d10007824031224000c00c1e04180c4011980300c6001100c03a50007039209501c1040310300503120740e040450311100007442d000d2001e003000e9454034030018050b0042a950074450904076960228440d0b22540c802c44500001e40181081c542d03030001d0741c6c0c407403482600c0580070305421414100780c00d10601c00c0306d104d088010715410140d01d540052058 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 172850476 1250 172849226 172849249
    0x11d0607030b03071707150e03030301030602090616030915020a0c050402090307090905030d0501080c10080a090501060308031b0f070f0f23070503010204030305030a270503030106020613080702 85
    0xc043c00384c2000401d00045074088003e401003500024489249055492444a940ca0151004014001100251941d00442109e0440350401c03000740c1c0301c0e11300c440090101d100740b26074402042004440a420035401c600302d5403c54100c004025054030090b0f50581e1210500e03180240607a90140c014840392500f0303805014107400c040c044404907915480e1a8003110783c00c200a8a9550020a80d0740794220b0a0050902628810b00540110b014000108200c0d800c03141031441400041c4002070007824442e0700c08039042c1c0c0c001d0000d000c001e64a0800203019402a10228004000c440300181c0a507000811034a03523500c0300381c0f494074020498580105c02000d0001c2159444000507110000c55030b50715124030140701c80c130303214041401108a40c0380380100e00c1d44013074002e0f40140002c0003c250000b007542e40c028445c100100b0001d1802c907000000d544c00010198031414040013402c00d2007030020240d410b0b0380c1c42e81c0032100135440e41e81040310849188040141040020040341c0018180b0801a45 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 172851726 1250 172850476 172850479
    0xe070e040f0c060305190c021f0b2d030d02120d02070804180c0806010c0201050c2e0c030b0918010605090c1e090a031e060903030603020102011d0607030b 68
    0x1901550715610880e540d00d0795800302000a40391403d001881100814440940101c41020001c038601a0340182d1200070031081e420300700c003d1035aa18408541c3c1d821403d12000c0081c0311540c400c10354242011840c941c0d0b101c1481b40750568500c40c150742400070300000c50384c50a80050112290414034410b0662150900e00c001c00d4003881003500042030340001d400584001e400c003c400c6074000b805501107a94a000200401040f1401c0c020030f85d0300440c00b164141e40a00e03069503a240032300607840c80d1200c0c48032480b00344542e4003041030b1a8001010a0901110f9a0000717005403008013200b201a20741c49206541d201c03100d100860481c000e03170400da00d0b03410500c80000c00c03550764800c00103202c00000c8884402c2c0f04800a8281c20f040900702144400e00c108540907420240714001203a9808494040100070003a90145081d036040c0d0a44510503860340300b8406d0040c1000ba01c2c2c0103000c0c0c0b20b6440201d02541c2411034030208480844030341c204c03409240d8002d084a90760284200d001c3d024480416 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 172852976 1250 172851726 172851743
    0x609200f0a0512040c0302030f0a150e011407050715020405010f0806040e0106030506090d0207080a060e0304030b01030305070b0114030a0b06190b030f0702070602120328051005040e070e04 83
    0x204000f552081c00703200d41d01a00b035003224946540141030a040c81100110300e543c01120680001903015090a020356400460001e0082c0340562614010315940d00f0018001e101d1204100d14a40c0c080c000300031551180d00a088508070701c0000e0416030040340038180c04103941d03050000300380e84201c22281e481440244049041c02e040843c80e800c43d20242c00960365074201c1c204100210904002d0b00017000d20070320061900d0792400313400a4444805000007420306450b43d0448600c40c5040007030720080d43c1c0101442c50031f03594a142c042c00e80c0d0b12081c012100301081400018040e42d05030141038440708050040d0280d0919a070303e000003d040100348a0380a82c212400700c08690380d8007080340c040e000c00c00c1c9803940c07420704504645901000814440840d84015400d0150b00d81c007094490300c81002e11100b5403241c840f20103400d50180c1c4032803040300b02c070140540400d6100d680c0d013081d8004c07980e04065640d0240c81c0c40500c0103451100203140302941c032a00c801c00c0658915a5003961242c091000b1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 172854226 1250 172852976 172852987
    0x30809040f020c0a02010e19030803090f10050601030605010f08041b0801021209070504060810020a0210090302030a0306051903080702030102460804030f20010609200f0a05 76
    0x540d0101c0e040b10034484460b5012491340401c40d6085a062494500b00b00d030304003070440c0740919200c442c0c11280401030484201001081041104002196815051100b43d8250380c100c20040c50040900f00e0b0300318002030030308000042d41d500800f10380520a00940c1d61206a555940f242c0142d194000c040c101003455008001481500038170190113038400101c0741c0e220a0801307014091610625401c0184102e00d4603070b007040524000545000d075103100420141e01e500b400e020507420865003442540180b030910700c205003050390100c000d044036806910104849911402030018044812210305401d0bc903264060000c5841500581156032005001505d0400644061484105442c402d0f00e0b100910003c1c0c1c61700d90f80328028081144005890b103a4001c180b1100007402c41d02d020b080a800e010034000c11040c2e0501c107484101c031011030040500d040b070913408240c07402040c16114012400c0d113410405808404135601610401d5641031a290030400c41c554072403141da0100c1040700c00e01004110 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 172855476 1250 172854226 172854251
    0x1e170c03041109130606090507020303041203020d060303110115051003020c0309030a0c170105040302060708130c230609060f1c06090f0b0102030a080103140f0f0f0d050c0703080904 80
    0x1045109440da190040d0041081d0b1405d54169003041d00202540e43c14501001b444030f6002007520740c015001030000182031000103040e170092042e640c11180342810128040700740b5410032650185144070300c00812078485241031181d00340245024442d884113141104c0e40650381301b50084c3c415550000d09582c5003076018030000e85450800d440c100d820780d502c41c0f0700700b00b0403401c1601d642000e5042e1009000c0c51809075002500c4400040c010760a1180000100c1c46516200f08105071650b400028030600540310041039500d840b95034603d26200a50b0307002d4600c1d6082035030a032501100c001e007882e410200340030301401107034100d00758110a10340c2d420340c0050703902844e005400082c103a0581c0000d1446d40b103070071102034854016603141558010004007071260360020003181101d42000406101c1005e03416214181a40b51201103c540b041c0d0301482c82c0030501281080381181c1100c2110503010302450251410b001e1094a45000c0d000000c0c1040400c015800410b50444014000241207103040ea = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 172856726 1250 172855476 172855489
    0x10f11070e04110a0e0a090c030609141b01020a020d17070609060b0609060d0b030f01020d06170703050a030f0203091c0215181c05010203071e170c030411 68
    0x240310785090741d212824803050004a06480030300d844250b40e00c3d0b0b125820800d050405500c09400002803e40d107050440034800c3c842c0e210320103035910503020b20880c0350710f040c095400720700f0f000440c6c400c0c000caa00d4002400c03020030514500800c1138001d0800020f15400b00499000c042e03c00f50346030428850781c0d40360103011100502c46c02e8490980000c006c005e60030400200c036a200103041c0614010010300b01341d95585401e41e90348a40c1031002003981c440c07940111b802d10181a07011146503001003061140101903401800594103805c04044a11403c1c3d8400c569440c0640f1000d005074004145e40b0000c248124202c007001c113941c0c0120f13442c0c083d201005c521003a4031124031076191465120781000710710f0041422840000038420441c14910143d840c4075002c035080052502c2107001d18038030900360043c408213281258000008540300e181484000d0007801141c003a0304c1900400207d8081918007a80e0b0000d408494440c0c50003603a0f0b543c2801c055154000f0380300356203aa114104241081d41c03090f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 172857976 1250 172856726 172856729
    0x6020a0605220b07080108030405090a09030210060906051305010b07080307020a0f0f031b11010c02030705180106090909120e060d0501080115120b06012105010902032d06010f1107 79
    0x6a800d030040380740c8900b0060007260103800c011f01caa0420802007009940781d42015400c00380c1001c0000780740c031451070140d01d000c40c03034450184228105003000850809981c0400101c1e0f4041d610303807561140c06c1d80341d181160701c2401031401c840c505220000c080307210b080107540d106079203004845c4c103008107845458461401e5030b4200c994003200c4860100701a0710550881c2e80201d40030b0003090010460783c4500d8440d0003221054100040d44c030302c610644d5000c0142e4001040003401e055100c3d110111441060002409000081a80c10000203084a110b118201c9481d0300410311400c40000e050040303800840390341c0742c0d55001c1da052000c01303c2201315200c1d40b8000c0960a0002074040d42c20040b40e64244295806003071144449074500000c641014241d60b03001c402445c015000c2075040c060301407000c010181c1900a2890040040f407a0046076002f503020300d03040d021a407140054089052040e0804414142c02d0400d079070041855940160504205d0310a035080106010184520032441d10741036 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 172859226 1250 172857976 172857983
    0x503070b090c040f0e341202041103010b1218010203090703030f0c0503030a020c03070c080318060903030d091721011d010605070c0f06051b010606020a060522 70
    0x5a50700355541c64507100304003450744c00440c18420b054004000d96261284410314048996009011281481071050302c501c54884460010405580350280c80010340b4129070104e004d82d2034000d0388048400d91400f81d070b0413152149003152800c0e100c840219050035020b0040002000c03500e0b40012162021f002440c40744c81c00c24010210240341d420f00070071407405000000306000746030950346c010550110407240c1c0104801000360380d03482e02060075840c512800402410301c10703000300c01081c0a580400107054441c40c0c11401c100d18000c1e0010081d0521404148a40c554000c2006030051080c0d604580015400380340b04c0036036124003030303524030b0240c0c00980601101d40c2a01001511703481c0c1d400f5000d014040b01e200408070440030b8150706010040600a00080c44030204019003001401c2d074980000c0c02046020042090f81d5000160260304403a01c0c14102c81c4510300340c03007641201485100d00315802a8010680380102d900e6a5000b05805802c81215030342c043c000d1010310712406044428140b2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 172860476 1250 172859226 172859233
    0x4050a0203090c0604150c17040303020f070f12030804020d02090112140303040209010e131506080f01110406050901030f1409240609060402120c0c0106050108040515040503070b09 79
    0x3010425642420060b0308a00d12a1304248002d00648604c3c03c0c4400396075425003024403034072619090201d010501612082070a03500003074084205640421417464907001c40d41250b8000da210700c01c000d1060260f0041c2070403803490003002808280700f0500c0c5130f0030900180c494004400c064002c100d02c00000d07009449480e92880c040010840150b004201400b00840079600714101540068112103061003030b12a4448000040f07080380b040981810805540f20403014010f501214502e0050010361240901c60300814034140740d0b112040c0a00a019880d80c24a58500303030a02c4800d540940100702507904055035114245113401c851b2250480884078410056650b24010382c40310b103002186450b03089084a14000146c1410a03d200c3c0307a001042210070580903514440454002c1c05108039080e0300b0300303801080c0094500c8000040400d040014001d2081c17544810056070030300b4040c0c1d801817095020442d0003010007001c044160b0405c0c03088068920b4a0150744600401007800c0c1c400724150742 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 172861726 1250 172860476 172860481
    0x3090819030c180b04030f020105040e0907050114090d080f1c06051512040b040f0f0b0402100201140a1d030d02090406050f01120903031d0604020306010b031b071104050a0203 77
    0x20340103e0200e41c580d1064031003a414900f09554803913036000e5480024421410f60400c401107a0080d0180c0b0042c02d8800034000e40c03840d080034655a2140240b0403240803d4240b51417240a6000a00701c84101c04098216002500683d40e010001d5002d120304244c000d50520500d00d89041c9581c03141c0c1c400301d16400106100d82004200302803400400303c2c2e80110a010810028480f045100c99544030b80c202045001d2962a820000e403c2c5111881c01001000b070175441c8804c202d500c03007035580504d00a43d045078030350040141c103a00301c840d0f2800844079401a200003d441c04100d400040c0c00910500001909c1e120740d0100d07510b50b820904244000580208185915003001c1c4904d000400c01110b032016031204940018110007498040f80607903a032140121000d15010b071b0010019944165800b01d0110740c454446a120541910100d10a015040000428850326400da9028001410300c0504010b00020b117041a81d01100c003c41d006202074806030451b40d200d200306446a0031010025982c1e1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 172862976 1250 172861726 172861751
    0xe07080708060f0919030c0b092406010215060a050a060807021221040606030203030a050423090c0a0c1704061b031416050703050c0109060e030a030309081903 70
    0xb00005002d890030280c04010400d4501c030001d160326a041e0070402c5550903900b541001c580b49034104c0e0300580480418018460000c0001401824004c94584420401c110306000a100ca90341520190b00590050202070418040c1620164100c0401418140101da542000c20004020fa900030340100350702c002000001c94051264800411807445442d1502c0c03400200ec3d03d6009041c1d8801c6100c03c0c107080094200100c81e44a1005107400508803500d0300014540200190b0040c003030760f80485040d48034403108031518110013046d110001e044030250707601c0c010085030a40010301d0b00707800c026070910b02c1004a102d6800f000001e1111800407940c1d00d050000262106800010748500041c10035042d002082d48a80d24044031410f60040581d00d001c451450410030002c00e8000d0100e0080d80070008c2003040016044004040a88441221569500c01541c9496080e80c220780c06030400040100000d21992194566074495000c5034180800c2c50701203000c0f003410301c000201083d40c40c120388948 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 172864226 1250 172862976 172862983
    0x1c02070b03040c0e06010309051005060f0414010608070c080a080f0c0712050901020a050f0607030506090403050a03020d2a080108031303110a0b03041b0e04030e01080603010e07080708 81
    0xa01800c5405610358145a40c40361105a694860401d03541c0070b0202180190f84290000106d490308041100c1d03000d0415820940184810b031480c9110300006500c0080790304180c00b642501c1600264880501ea02e040b030305542c14500181510b0400444450200020303011310047d2903107400596a60000349040040040c080700c0292150080107824080300d40055009074136158410070754035010b03440e200380500507850541181c0008003640a50707403045500207000a01c0600c030315220780e030030311458a07960180200607809aa0107800134404004040c0c1c1c0ca402a0010701c0744030005180044c00c51880d82d010346503d100017026040c1054120b95400b01158803000150240102c00040d40c40c0c1006119981c208420911000b41804040b03450b8052075030f9409001801001c008080695074600780c40d000000107483d8032a1035030040410004101c910014603080c0c4119071545034411120026401500c100c00000c040507031541d00c070a404001c0217014020500100a001c0091490030704040c00c180c00c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 172865476 1250 172864226 172864229
    0x6031707080306153a020708040312050702040e0c10050301080d08040503070501021c0f110406080a0b030d030902040e0c150a090f0f05090708010b0f0f0c1c0207 71
    0x15100028041000480c109800722030b04108110341091070301c9034048601010340100b120310171490f10405480ca180d00303509859030303180300c940c118002400e982c81c82c03a500407030048080142255609020500000e030103d2501454802d080c02c05909100381035002800b81c0b103e8100400140d000403c0041d091b0800e0b41c04006268120700385241951304180b043c42d0340c0e83d41c002c004003c12008101203400d008040c0b04aa440d0780d04a0005c2d540c502d10f00700c64080b1105100b80340204146000c520200304200c901c1025440d5048043e0545003c2c0b401804640e040b0010b01041c8680359680c0700c0c203085030350800c03440008441c5900c020a0505450040000311428500315401c030b034024826030211a43e802070403041103c00d040c90702e80c8815400204440e08400341e080100110b0120001040c03a6040f4010b10046460468944e202e0f075840c00011500701d0401c0c4184440c5640922810035000e20302c00150500740e0300182c500d810490b0f0306044901d0f10b0010315800040c0585014809a6513030305011050 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 172866726 1250 172865476 172865513
    0xa020729040603390c06090b01060201090c0603050c120601271d0c1b0a0f0b060a08010b0102060103120c06060b03010906080a0b07120e0a03180501030902011704030e060d0603 77
    0x742c0014030180800b6241d66559071381410428540f0101e404c02c24182c1c06400d01d00d4014145d1421580c440ca0080c1c000c201c143c41c140c514600c60540010124800c0c091386209601088503542042d440e10302d4018100e0000d4031643c14416940c0782d040c8506001407000241141244038800304910b00040070720250711820810f40b03070005803800c2045011080003101c01904c0d05c10344104c0c201c056888000d040c6181c590300100780c4000d8041003c00e1000032480d4078020981281d0441c0e001e644d03840302c0f90881c2c009114460168001400400201d14190306a00d00d039411360070300525408030303a0745001c215119900040c00c44040880180003017003086c815400580b08030390050002c8402e5407146041060014100005c2100c3c00080b45040c1004c4c2d08140a000440c10440d007241da80ca10b0702409010b5240c042003000034082e840000d55611900030b400e8102d406031078a0020000d010800004200f008000f03600b4031655052004041e100c6500901000c2c2c6203000c00141c4909601c0d14210715052170342c008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 172867976 1250 172866726 172866791
    0x14071101080c0c03070209040303020f030403030203010302090c03060d0b0405120c01050a0e06061c080d0c020102030402030c04060f03030c050715021b031209040213030b0a0b04110a020729040603 86
    0x142580c150000440b461250101d8407c8000c1c2d0361460224068450320f019031801c3d21001c4107000070182c0540107141038a1088070f00014581d11001920024002110001c0d4001e08203003900000c03c80d81540a90410300800540c0c40c400303820749481000754031900e0704c010642c0d512010055180d005110303030102c00c501030010b084a800d100000400365108110500300c042c503040e400908002000c01214444000340030180301c0da840649000c2d000350400c980680c040e010708102480d4074a0640329810540c1c000e000008601c1d415920115a40002c40c9412038140c400c01b20045596032000c40c2c1c03a00d04008950080170079000122107145001d9030810514081c4d401004101003035050103098401c026010340c0c0c0161902e040c82c0242441c40203562010345248070010500c06850010780100708040800e450034441e4041003249404148184848000182c00c1408180440101084a00f010107000b2a900f4800262110b0510040e44207621880120303564031404c03101042c503012004c08102188401 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 172869226 1250 172867976 172867987
    0x105030607020d051b070e041a04050714030102131716051c03020a02090c0c010b09040b071b170a09090b010f2609010b0307080318040504020114071101080c 69
    0x1c0d50f2080322a0000c41405000b0404407900314060305140303101c0d1045030891310019510900320224450645080d101c019825241c4801d1400d03691227103000f2a4000300400c18940341a014808401c01c01030100d901d035400304145981107a00004200c007802622030005401071100c008540f6108103005184150050060104419600c0004120081107000422005000e25203000ca041031503c010003544500c0d00b00503c80710200c90406000d41204020080002c110820100058082c080710300401444060f000074210078459407081002c80c0c1c1451140a50300c95503602c242c0c4400003800d07094040500841c207041910b9004045500a250785a4100709000303124000810704010307071f410001030200620060504080f04500d10211210404810420b82400301c2c103140079154800c001c500c28070451002103940c0001000300c40300c1c20709220703941d03050019090902000c0c010003031082e81841000401d400309818010000c0c90b449210b0500900b21042c2000050b20f2808041c03c5d6a1410805010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 172870476 1250 172869226 172869241
    0x819180303050307090e070f09090627091a0406060e010b120702030d0905031908012301020c100806030601060207050310050c0714060a1808031305101a0901050306 72
    0x2016030703406207031069503541c9800090711401e20540c070411042094108000849a000480c0c0010000350303500e408000b50f0f40c00030342007075800d94003030300300428080d00400c4035490030740c0841c000a07501c0010200d1000b4041d294031003811800072800107601004030402c0100045840307170402400500303209034115410301a03245600d0060f5581d40e030068486c80301050540d4000c0094a0700080303485000d2150121030318025440c0d40001c40b0b441c6580300e0600c050000d15005080d03c83c107031270b07032140e80144131540c00912510803000880028107502443c500303e4110740311200c0741c2050808a440316841e60800174203051420605901a00c01c5401c04a0140901d94001c44c0c0000c1040c02c2000208080e1290581078445114070300004203030040c0100008011076020840c94443c1400c04000c000d0a5a8000e40300040001c0a030000c0c00710340204002800524404040c0301080d0080e000c403043c041000e04000101c540008040c080c42d0643d03004140780b840c100380d1842c01b4000c10f50240026040041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 172871726 1250 172870476 172870517
    0x3040c050609030a060c0c0201120606020c1005040509010617060a031110031d0618190b09101406030c0102030f2a01060b19050c0607030b0604050a030819 68
    0x5503482101c00049898481c0d9080011501c40c0d80c11000400141c140c51902911103001e0030412408115082c442d00707480110380c40340c01e04550315a0040c10000301c2d49010402481d481d0380c10b42c01809014800456903403503c0549034041c080d503403102c0c80d41d094400c088110180e4010f108901c10b40c0040002d00004203442100c04091405940803a450240060309030041d0500242d142e030603055007100c0c64000403000407460700070008900d5910390083c2d0a10900c0d06c0e002c1d84a494010346a5081c5110b00140030808400e40c0b100c041c00aa8882848075411101a41c48c078034a0400403106100520919281c00d0003006080d0209000031450031038180e8096000307000f0610140c00c00300c680111000ca0707842100e0150203e00c41c5800030041681c44149261054000b400c006030150030030f80444002500071011a1380c030600780c0c0f00904040d070300c84c1d80c224043c2440710600742d0002c0c2d06000002d00e80c0c43da40c03014009541708504503920b602c900c1d00140c1010102074545030401c172640199603883d0340202e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 172872976 1250 172871726 172871729
    0xc080f040512031318110c0303040c08210307050d05091c0318021c080a0504140105070302030318071a070b07080412081b04090903080c031603020c070506210c03040c 73
    0x50817194100302d28100e0b4400101004403c10208560000b021401d442c00032000314440d51103400ba039076080e501c0b8450300c1c3c0e82e001a024800e200800801d000d060f04980c43c8050340d449400c9140c4a07141c03d90410004040e114155000e9100f540144240344070a801c14140c12102003540c58100100c0380c0c1486010902558500003030b001e403400e0004030800f10f8007c02e00500c0d0a42100b21248c1e83c56440750300400323a6019125a2080503041c042c12442580328504450071250107500550a503260700741000205441c0ca20041d80c1d0744607845000030245440450307401c100001c00710450321a4490700300380d800505c005000d0703020001018200b00000e00003250a007042c901501e01074025660b054500d07044a0758071280341214800c00f10b40002c04914580000800034231030755034a050ba032210301440386540000d03940c0707444001140600840c0144070361f02820310031b00d0042c01c0b00c01050742d03500030404651190f90003002d084246e54803c62100c40e0000103540011800201d02c2c80c6187c07a0f01da400c00d0181d207 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 172874226 1250 172872976 172872989
    0x203070201030b040f0213030c050604030f02040c0207180638070302070b03041103390f04090506070206150306043003050601022802100c080f0405120313 68
    0x4482071940a078913280d00420308441c0f0a00c1c210364801c150040c00038000018401212012100c9a0114050900138142e80850350300083d41b55040c855642000050802c4d520000110b11410800240d10001c9030489582c400180e40e000414501304250540300103030705402c1940086025081c0191108030000301040e0700c1c920300902d40c50342481c4c6012400c0444540c00512010400300c203100070b01248404154000004a003210a6420110300c143c426070103085c2c1c019404404407150342c0507407090072101d00301504000d12014003004140000b4084030220300c0140d07201c0d4001d100300021613030100038a5411880e664480c0078442c00d140b00280e91104001c00c010032143c040e2036420202c094045d00350300b1480e1500d410054100513640001c00420003100e116005100d0941c03964000107031611a810400e622007000d81c10700600f034003800b0044110039500810080304c00038640102c1c2080002d444c00c2540b000c1156a00e0313250800b00510200305148010464104011840030000084050400c0398107 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 172875476 1250 172874226 172874231
    0x120706050c040b0a030c030b040c0e060a05040803070602030915090715032702030c0a03020d0605060102120703090303021c051806090301110319020c070e10090e0604021e01020307020103 82
    0x403007400e070202500881e8007006400602042000c05a0780540041095105598003084000c034000c0801c000d4030001d050340c80c0880c000d079100000781d050100080c4011080c90610526043da100c642030724590003505c007541d6071640402032084440d0b0611032504250500e1400c0310281c20205100c0361030303445a2180b140e1070441c1c4601c1c0c44449001e50000080c0f1902848802c40320690b948490781c404070309205c224400d00440500c0b00c01c44c0351882003030080e00d40140250b0140600c590340c0100804028040e58103500c10304003050080342c0791302c0050076100c3c82f9641c1c4078402e51540c03030701901d40000c0e02141e8000c0426200d1045109610030140d0b050a682e419011000c546003502003030300c0d407280ca44bc16400d942030002c0c00e580d6070000c500440c000c06070801d0030003050800c0003e00041380298130f072070b072802c0d00583c204001a02400903400d030030a0440d108103424642c0c540c070803070480f164160411841c0e000070080206501d400c24250f5418800181125501110240000c1d1a4420440b00a05256 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 172876726 1250 172875476 172875481
    0x50f360405071208160c030c121202030a050a0c110603040f14011103040204180501050a0209011116230301050a050f06030d0e0d0f150203090d02010e07060e040227011112070605 78
    0x108011b04001150807141144445c0d880e0103000c546080d00c00d1099844106480700c19070304d984008201d800c40c4125640300d42c02c0408440040313070f03111001c3c401035500610036020341500341e03114002103000b14494810301c1c481624900d4000301400000c2d104029592400146005108202045a61007981158005171030f00000c2a080c1b508070301007034003511540c80c00041040c0315030942e00400d82003c0036212044541c60102169030f07140c810060a00c4c4400c0e44c0c4408006601100c3d00000030072501d801205a107141e50740110342154822960a203840d43c80b1010b00202c043c4d0300d1440c9800103001e0300a090364807003102d030280044244a8000d8042c1e801c1900c140c041c04072101c84160b0306544071003025a038500309621400a9003041ea006022400b44407101d0111500522a80d01c4500d400c10250041c00c2c5042c000317031482446400c20716046902003009400444400d01101e4000c0d081c400b904141002810004004080380c1000d42c52076401070703402004100409080d6003400e6440036021030a84e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 172877976 1250 172876726 172876733
    0x60605030f04080d0c02011a030313030b0603030d0f020304121b170d0603050601080601050a06020c01120f090b040b06060c060109020a09080a0302030d050709050f36040507120816 79
    0x348940d15204c03043d03a180c20522000c55a064024500e110002046000601c1f5500e0030140c5074808d035105a8100d404140c01000016100000765078408401010390341000c000c2400382c02641c0c07d60558911507507000041004100c00c0e85001030601003103182002c661000501e0781e06811403c40b4018061528806003204507541c10300803030b07000d030b030b80c010042c042e05940e40341142d51040280100d5038140030750740021926040c00c101c510308565155008000102d40c000064542c0354520020400c02a151108842044864094501038921580b240d02c0680340500340044015406480c0c03506c10a800c11000070305000000e0070905480e011303100182d485851031400d403000311155102c50f40f107016801641080c1138012002d412062488081440070395138406003200c00c181c035030055651013030425440406030306103220020751440414007429501c2580110b0607480000141903207200c00840c0007040308224090000400400ca02410020405e0040ea11068a07018090841101d0b01000c001ca40a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 172879226 1250 172877976 172877993
    0x30804060f090503040f06050c07213002030c0703020f0402040f06080a0b010e010f050307020f0102030a020d1508060103150f11120f060105090d150c020705090a060605030f04 77
    0x741280020200b00b000d03001d1404a40741c0d0450312511080709240c400004410340a0f504407444d00d105d000c050840d6038202403080d04446000c680300840008490301c41000160441d904110913108290134120040010020181400c505107020f0215041846000c40305100041c10400ba29811600e00482c0000080443c000340140d90103103a0a442e1b402d4000340303040c2c1001c800c50003007100300b00074010340d0b040710019184d5819501d1501d000031781824180c00d080b440f0380080c64122403148141c0320769400311a801c40c00da8005851000181390300280d031700303001d0074284a45407802010210040b0b40501d00b500b0305840707200511001c3c04080c07244800c03610201e03a9030b00510005003000c1040050114070441c90081d500321201d0711101d85000d401003134003c043c0f180c403184100c5059507243d02d040d88800a00041d14203050b001c95200403407034881000d2a400303001d0a01070712003e0307009101080c0b81500708030a080014000c118003900d010030a0164a600c40d04a80d44140b009501540e181c0752460507410f03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 172880476 1250 172879226 172879241
    0x60816030b10030e10020405130911030610050a060311041a071403040303080105040b0d1205040509090336041d0d030608060901111603090b1c05070c050a03080406 72
    0x10b109102c04000140a501039202007010b61003002243c45440c0400c0d4030004910a5000b603580c40102c41080580c0004039410030402079102c3e49640d4528204080070900e08501601d1581c10000284414861030422592120050405140a02040c0301d000103001292049024500c2e0743c803807030003030310000285c03200844010580c4151181d14225038043d00b60340300d40041c0411800151050000100c500d400c1c0034600203140300601c26008001c59076920703041410380b4605d0f003003840310030f100004d1156900201240316000d000041c41d40c80c03101c00010012014145818088115038081240d16840020301021102005039030008080550003603030210110340d2501046144115404040120b070f0640100040303c01c840e00f01d0b035098a07401d40060076900f5047c3c400010312014040c007003041e41c050010484280c081e0900c44c01c07c0c0c0d2114005008c540c015400102da01c1d0b01e80b8003408034828107210b5a640300d41c02e0b1511400d400710f69030341c251702c9480000c0050200300e810008074040c40369a43c80880e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 172881726 1250 172880476 172880479
    0x40b0102190605060a2709020a080d020a1103010504121826390a0e01030803040c0905011a0c10150e0a060501051b0c0918060907060816030b 62
    0x40400a6030b181071000782104440c1e0354065143e0240018824043d501c42c02c10f04110b1107045002c100099030014001c10054900782d0340000d802e88005080030041c400840595015409014440140d04211191221076018503005e80c0c549400c1101007001d03040100805002481e01e00c50004dc1c02c045075070a4003d9400000300500c002004a0304400c1c1d20050950051070601550503d00d5518140b0341800c4d00c001da5802d4071840c1800b1031101c055403901042d21440001c1490032a20b85850400502a40903041203d040c41c000041c0418013160024001c0101086a4144400e42c100007a012a40c642d429140c460101d000c5020344001c3c0c401d2019540401c801d02040029025401c01c1003004c0301d091213000010324005000c900240d01d0b41c0203c0e0240c400c1a12078900d4050000180c1c04013920030180400d0350700030004003400c256540449a4045c100900259004d451810101070500c1009840140c4030351160f0010001c0380d400280701540850a01c111820700701c01c0304000d0b0058440c100005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 172882976 1250 172881726 172881763
    0x26030903030d0519090b01090b010203220608010e0108100e031210060906020c0a0b0a090e191a01120b03070f0807060e01090614090609060d062102010c02040b0102 72
    0x12240042d040d403180b882021040c152050980407401d1040803903045101c0645030072141e80041c000c10800d90418284c920040c81280d28045402c040c08035802241404c46180720b4804100300121907000003814007411003080b510259514000b81d0030361302c488110030200015113440340c403851100c00b8826513000501c1044842403e141940c2a004188070034010a40411580100817902c5480005d815002960284c29190b07000c4c1490303103000f09230700691142400c1040e012030114132148100402c90244100341c001d280e4004105085038180e80c2c10300d1161011001d58007498081c0c0e03a01c00f50f644400013440f180050701103240300100303040004540140f005070039002400160070f83d0004046d07084480c5641e40d124032410389001110504400e10401e800036203040f0320280026280c00c01002c041c2d800405440c0707040d00c1003010940c0340e084502408a11a520041000108801000250004445642428082c10301d50010340395181160303010f40126941d01e204169a4001c00c0224000c00c0300a507607 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 172884226 1250 172882976 172882987
    0x8090607120206090a050601120212070b0d0b0603090c0d0602041a1b0105010b0d020310150e01020d0f200a020402120709050105040e07051602040e0a0501152603090303 74
    0x641038800d40c9000401c0107205036000a100540040398040325954040050500e991a2691020120400d600142d90080b88100030ba050b800c410000f14004185900d0300d01d451303107003922070101120705c483c5841c0d000d00410820840040e00c04a12161680001c9542e80d40115460070080020b0280d600040001d4501c003405440d01030102015111440a81c0c41e81155244034032411800d0b0b410078400d480c00203805002001c003203116500950f40c00300c04841c1c80c1c980305540c0e41c590340c49032200b0441c1c100882c001c141c00700b45c55641480340300326800103800e00c00003a03007007000000e198003600042c0d0030942d10144503100c0c3d40c020500241c0c40d450380080041d515000813001c2c6440201040c2c6036900801d5444030b0018155001d03005850407265015100c0d03000740c0d030710401030714154070620f40060916030b040c0e04240169641e100c0c91040100b080011b10862102e4a0304030300b150304951600120101500d01007108a901010300c04000d0104081d4600c0048000704491a5004003955180e040c00007203007 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 172885476 1250 172884226 172884233
    0x2701020c07090f0908070f11030a0308040209071e140c010603030302040e071b02010503150901080d2c040e15090313060804031e02150f010807050a060c02090408090607 74
    0x6240003650300b104020800080d49003030380d000302c1c0c031491402403503000c0502004021407150301d05069503600a014000d03144200000281c00c1c00a1074500300d01040d40c110511042d81425040749500184506020b00c00c5e1038098054400005042482d2040001a20719440b0741c3d04860259102050707060024022151240341c081c000c2d403c140070710140107440c1c2000401061003040805229004132010100c503404540045030f244e030000302a5002903000240c12101900d0f0b07490700500a000c03640180c0200448440c00502d00300520710180c1c0d488200c0300c040120401007440c0c48c6240a070483e40090301c01c0c0140300d01424940020111800c0c40310001c100700c55102e0110040c01c519443d000c0e490702c0c19496040507101b0710011386003e40010f401c0c4006200e1246d14561034000c03041e140c0105c502003000c0424036146030320122101d011240b03854004020f40c02080183d480981405ca0f094002036040020045c8003082e1020040c1c07040360500d0200d4103000c2000122900c0390006850140d942c5240e0a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 172886726 1250 172885476 172885483
    0x120c010e060a050714070c09050a020c060403080403120b030c0603180f0703050106051516030201110a110c06090108041101030b0604090c0906091d061206100f06080403082701020c 79
    0xb1413003c040f88003d500b84400b41e00100403960101e500901403401942442e09800c0241300c000c0020418680c00c0101c0c0c1d1124008201c0684124803030341d205061440c1a00c5c005003845040c00460a00c81d08142c0e21030203e0340c02089000400348240e03101e60300c0c0c1d074540c00512a41d40c510385002600c0d00601401e02104400800c81d001900c0c040e0300244404c6a42d141441003174580e2030512162544248404410b080703600d1103428505000b4400811020703030001c13005006901c00c1500d070b0003240480b0300c0040c0b2288140070001e94160119081c0b03040142600019105c03070b4006000074406020004035441d01c1e8081d0780203070b0001d0005000991195152124038004003140010300703001c501c143c003001400c1440340c040d8505aa13004400d0350410402c103880c0f07100b440c4020305000d5000f0448086008812420400c082c8100f42d003503c02d1b00000d2510354401c03801d05060300404104418041084042078000c50b005410a044148444a807201545d41d5581c44452178264543c0d5400014000040c01000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 172887976 1250 172886726 172886731
    0x120c090a06020a120f0c020103090f0507260102030f040f0f0503040b03070318020f1c021507123e0601030c090f02040302030c040b0109120507090b090603120c010e060a05 75
    0x201d1403411412401c13081968502030220b84040051040c601d10001548260012035440344140307203d440c0c041541d658075090000c183c112015074810700714800d01c660040041c52441100040c000c500e141410070741226844c000410282400240700d607524104081d800043d4004e907000b000f52a102c0f5100c00d11007003540d00a076200f2000a042400b400c564070029191840409d60040618034004019418405041030a11f0591f00c011400010038016840310440550030350b107000c006680c6d0380390601c0c10800001e000d05076001003002c02480b00754011444081c440403202c0401c01181904a0110002192000140040703001e004010002080188500c1200180d5000042c288850820034080d601280658800658150310008502e0780c0d5003040d07800702c800d40300189070108031a0740b1403040c10303111120068111207991204078208280d01072441210b0003a00d04485d0040c090900000184d9580070102d030365202480c3c0041c000c100b0b16005d40c42048071514001c15a41c05140071202000148003c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 172889226 1250 172887976 172887983
    0x3070302070605090c0a0303030522050d090b04060503010b090d02060c061b12010b03060105190522230310060e0612032109070f090b010e04050606120c090a06020a 72
    0x40002051326082c0c0850514202c88014002205092842d24103c0180c8000740214a100022074134040d20550b5140210000da40694001d011040c03000c103000f84210195802a00002c100f80070910246a00c13504481c11991407041c40c2d9100c640728000030b0644101040d0003940448001001050104c0c0450700a00c14200c6000c4030015140300c044150440c0320b4015420191400c0c030005004022803000950740050061610710f0604000d11854000d02d0940512500802d602042246542c04008a16403c1c21502261b607909146490f818099002001c2100d4041d040000c8609019880c100400c60641c1c50300d05040c00030b581d548080904400d401d071000c070300442001600c00c0358940f002040340c61a00c000510f480055001703809d00042d040d009001d10086010701030340041e4400070505d90101030244900009490f201307003000903004102120190b401282070500700301302580ca0707000751090714401c0e44101d2901c1e1740d0300481001600c64441026400101a180425a540d000442540c40c510 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 172890476 1250 172889226 172889231
    0x1a0f0703050a18290c19061409100605040c09060c03230408070509060d12140a030c110f10020d0212040b01050310051b07080706060b030a180206070311030f030703020706 75
    0x140104009030301c0c841c0121103c001d90017030502c44088032440b0031906c66980a484001207000070341c2e410100380c1c04192901c20242d4403030040452941c940f8403880740241811641040a01c0035400094084801481103200b4070081e4a41e0105241c001e0300000c04d055043c0101902180c035044071203982d3b81007402606964821a130700403906003072503a5100d00881c0028490511b00c00d540e9940806000b240244a041041c21040d0308a0010031f14040c9c00c108009860124403e01c60240091410f0000030492007560301140c956684030398086580d0ba070271060290050307070750440484203401034800c90549011061180c000c0100303012001950b05d044c0d440c12415112154003c1d003098080c0c880c04d40f030082c054194803040388007110a600091030460302c075141d1b142c142540360700c404084441036440b000c030a003000010089000894030500e51016070181042c0f094074000d402180017401800c500500b0320078108160340c0c030104104161140030f60480c294941d246003207030008002c1c0d04054800c442060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 172891726 1250 172890476 172890539
    0xc04111201091b14090603040302030706150e070c0b04030305061507050102190507110d0303092a0603020703120c0c020618040b040209060d0c20071a0f0703050a18 72
    0x510800c4c0c540d0107a0032842401e8200030580c01003084552000d0421000d600c0104283c00000d0068000c82014940c04d82558002e10318245101d08802401008217080100440b11a000a0768880c205a009030f00751900107016511000814000c4a400300c070b041800c0c8000c02c001c01004815001000704801e020060704000721950401c0d80d0038040c0b00c100505401c008a030000e04ca080284502d03446500910303000ca1404459215030340d102410a02c030500300301600b0940448009120075900c000c1145160451808000351002000105141044901075440d420340d1003030540b0803801d4181d11600180b06603a03410818510398001040c41e0035450250307061980182e100c2c98a8820380f254000043d20781071a04112044070300043c064040140103100000c41119411844075808000c4103000400a2800703030b0a01400a100c54080001161101c0c400c201e03901d40941e50034180d8241c2541400c02c1c0780c07a4000001c0690b13070302100c0380c2000b40346c502002000400090042444081d00c205100c41248003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 172892976 1250 172891726 172891781
    0x5031e070b0403081c0204051503070201050105030d2a020405091501081504080d0f020f0406021c020d11071a071103010b090106120f0e0c010807020f0c0411120109 72
    0xd00943c03201414480003031042c0c4240354428400300c0e80794845220018a00303a255400142c5030b010441c0d45281c2100080104a9076980900c2900c2c050407040b4014480078603811030041520706e002d1001ca0011101d40741488141401050040d10303654000c1042c00b46103044843d01d039454207601003405030321400c2000028a088041100721440b42050b03809036503540d440d00d5806840d4401d46007080e005540301b00c842c60004062010704944403845448030b60315072034080002c0c40c1070400e41b48500c400703d81440b403894050b00040e410704030344068240b4030f420119640c812402c0000a03804081500214075803811404c00310001842510311800140b0700c90803003a0b080c1402c84104030f4946422000c003000602420b401040100840045c1c4074010813605d50242d0384005540012400110390780c0314089000030340da00103051644c45207440c0300602d0340e081c021000c42d03540e011000c6914021551960045181c8103440c0c111090305010303080701d00322565a1031014001f0101200b40344205189941c120015 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 172894226 1250 172892976 172892999
    0x302031b1806012a060e1f05060604030f21021e01050f01360207020a0509040b0a09030e030607020c011e0c14010b0907080a0506010804030215060a05031e07 69
    0x585010382d90303039040804c554582070b0200c120fa420903820407900411200000c813a401040444550000941a08000110300c8001120f0f542c030f0f10240b01d1300700390070407840d41c846105940881e50440300e100f0158020781400180c0605909002014658040b0b0000055400081c070300d049403402801c41d001a41d0000750035080302c0c010b4903204030520400d80100032102c030781101c4807880394a00094503035541c80e5444040c5211890110080c1d032540200f40101940340081045005010a440141c42840c1540d20314002002c01813204121659550841003454443d180c10700b0303419409421107140e801c045030065951800e0488090005500a0b440342084180001d48041d8001b191246009114141d9520320362103205603850a6541d69209081c005603500c4030024011312654488010900700201c180d8140c2e500148401d05001c0361405000001c1d9000504510010507071000040c0c5481c3e205c0010038240a5034400c0303030305219030f245c4400d240a0004403020680c00c000101c520300d9966146003003d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 172895476 1250 172894226 172894231
    0xf040b0a0b06030703051b0c011b020a0503031609030b0106050c0c040c020a14100c23070c0b070203070305061617010f0510050c060a020d0b01020c13020c01060302031b18 75
    0x41000003440410301645c000d800060300a110080c0003040b00c013a210f800300030791300500c0c1c0c2003807a69140c4881600001821302c131a00300c0c07907643c4094136264205447d142e590f840007500528a03900500e50f4000218410b1162201a50f800043d40d05196914900180150004400c11b078582c0180c4546505900d032030312689510350003d0300036009900168543c05030841da48030004005000c1c40000b86070812841c400d9a400040586a1441300c0030b04924085444c03008000203040302d0000c00003000424421000e240c200c8440300f4096540c0c2c0c03008d1000ca410f02019a20092161044005118502400b00b00c1490ba1000d03079910104092400d0800c0d020ac3c0c0000c2c0f05042041000541c00c0c440c0742480b1551005145003801c00d946803002c00c14070103140c200101c480181c05a408150102d0409450081e400943c5091000f080b004c45103a00060030400d91012944040798000b44000d4800400c0d040f0200945e001010b030340d0300b000c80060b0f100384920b6801800348070380000000080182c441050290 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 172896726 1250 172895476 172895479
    0x706060302100e150a0216030b07080106090617060402090a030b071103070c030305160f1101080a1401090b03010905031c0b010534051603030206090a0206070f080702090f040b0a0b 79
    0x110b84101303115842c03503503489401d0341c0b011401203892110307030094030703240400c004d5208040c008091724000100030816081030300003904020443d034041100c83e61214800d107441940c201315510a40707505001078000d12498800300d400036503400c8000140165100098030410094450b03818540d544031410741c403840b50302d0008010a801100c1400828890006003001000130491548102450707241e2682c1114200c80840b1020303940d44880d1081d50b40940003e40000400d5000d103d0100078640508410b003050060358a483d50320504160190b070250000c0d200b06800c0400d07255902c03032440d011400081d016000e9450301e4140020003109520420403154803038807650407000c182c0004061a9007101c1001034179280e0a503849031000c0800c07001c0c4000e690f84241000380c01d440764a9498064101840180381c0808d54200800c0d1402688a100880e07054982c4080300112155161a004030580035005e4069081100041006810b030205c0e011070340500d003c2d450785012a502c07000048155000c141400e03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 172897976 1250 172896726 172896739
    0x30709020901050f18120706020d0c050a0f080d0f02180303090102061f0506040e09010e19060f0216050f151b03040201031d01022107140307020109080706060302100e 73
    0xc0913441544000b801e007040340890800168003100f07000401482441c4c0780caa2450b009410200009501000710030320712100d609003c04015215155141c442e4a6074001400442003140d00d40100140c107000c80742801b0440c103080000c1c0b0a031440d02d10003900301090543e5025240b84030740c40075140000c107984a01d04161300130242c6035078a488000501c0340c004030a034499580c034000405d02c0d40d00d110150000c0c0054240e507854900c1c150503078030309540744045203105903000101944400702c014610381d00340b6034005401003000001c0d0103424000303114024503100044005e62540f03040110101e000c40307120241000f1110000d20351040d810141100ba5400319490480315444101440f44c2c502842d88140141000a40910310800f50741d0800801c2c000b482a503540051b820540d030080016a03071507240c2c44000c4c19080d140500002e404030345020212b01c0590000710004003900d100f50410150580d0207440251186458039100d000317010640803c07031140003540c00100e45148103040341644424002c2c02e2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 172899226 1250 172897976 172897987
    0xf0303070b01180f05013206040603180c03050d081006090501030c03020d09080c15010b030a1d03040303200316030806040908030c090906100c02091801090b0603070902090105 77
    0x2514140c03d261200e07501c0c1900d554440300d19031a107210310350080c0704082601c402001c11008040e05c626148003075002003001d961007500c080c0c5900082d941602c0032424001840001c5294003500e104041100401e210b100590100400c90003140c4c9001034030041d203d026440d01c1d0012040e4039100580030750780000d5081041040a580b09400000280c101420014a810319100c1c1c58426140c40100654900030006410f0110750002c014182007a040d0300c54003c280e505202030780740300e4032000d0000b44d00d45071a800d034140c02c400e4200d200280302c8041c000b26035445940e450054820b400d00c2e40c03910b0849042926200442c48003004403018445503104010020130143c3e0f00703659148010300308541103a0ba461802c0e00040c080300080d07000d00141d030303407494458881c2e50411041c0e0744c00800c064010060309541412980e04820141841c903411180784071940c0c2c4000e13844c908081c1c0c81d03400090540c201070320001400f10395211a400342c80c099041d9064251966107500c103138400d0941d842c0c00074404000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 172900476 1250 172899226 172899239
    0x11090f010e0429070206060f03030702012114010306090203060601030603020d061d0d02010b0a0609030b0408030a110d09020307080616030e161e060309080702122a0f0303070b01 78
    0x405a1142400c6015980314401810380c00c511000e01322041c401580c864030034031800d440c00c40411400c804013100127501c3c4c040c3c0380d800200b10001c4454460131b101e1040441640310309003a00000300c50104901c0e8a0041d40e500d040c10400341600c80c034264000c1c0903040c0483d0140d403180c015101625005044102d00e0b40030340e55041d0080100c0241c0f841401401003055416090501664810440b0342e40046010b01c808000c00c0a01800c0d9803140c014000550410000101201c0042d6480344d00030042da0340702d40d03440c45860041c1c51038600d400c08040c07000494440c0000c0503806894401c1c0264220760a1548031081c641d610364080d01c0c0d0311141c04001043c601c106100c0d81110611424032415104540b41d04502e80c8140d0145401001e2a103e204080016202c0d903d40c4141c01010140b60500c541c440f42e84910902d0301c40c500f00613029070701080e00941c0e0020700308020300482503483c000640c2400c010f050340840e042c0e0035100e1449100c400c03003203101500e40003095846064009a04890507481c241 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 172901726 1250 172900476 172900493
    0x100e160509060d060606050c07090b0a0b0a02032b0f0903080a0b0f030304030825030c1203090b0a0204060f0507021e0102070801020d05011403150105130e010911090f010e04 76
    0x41002d41d100030304640840004115000e600e005100940390b594554841a08050a020443d0448101203292081c039030031641d00c2c80c2c800300c12500c0640c81c0d2a661030016104900750b11402203040d501d80e4006900300001d00340c0303d064110f00384000c0c10070081c2c103401d0840300301a00ea9400d0080c00141c200008550100e01c1684003143c0d9a00050a0301d00720303c1202c01007800e58002e50301c145c0d403640c00402c7c080720604281c04d10b1100e48820f01341d9000b03190038070746d40505145240c0318007514908208480b4200315020707078061150035070494180080743c600b024400c0040d60241c040c00000808042c5170060b814002c40075220000d9005000541a03030400d0400c0c0e16492080d2201411889041400500200203200400700001050b001080640c10310b510107400131a4044002d000744d01048418000c3d0b036443e2403070350550b80100e840b03806416800301444041c100005106e0072551038044520100500484200d21a44041d52010140e6451400c00000c12500f4400c0b04d584c0540480000c00045428 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 172902976 1250 172901726 172901731
    0x2010507140309030c100b03190f0f06060e160306060203210a060e090106080c0f1e030705040c0e040c0809060406050c21251704050c030a0302100e160509 68
    0xc1048074203188003e002c05d46000241a1aa40f245580c0c0d000032885040a0026114280c41822052103807000344d0350304d45004035110b10240040c04c010070304d003080080981248008010f007003001000b600b0403402c4091110588221340010034034144000903039a0000c010fa40000030301c150074620340d40004860384420b0b0300060248074160355613907000c16250703091000c0c9806210100d00000e00c0c6403e05c0012490010501909842400c007401c00c402c3c2952480c500101450390030058000d4a450000881d18115994019070750107400c1c00303603c03945590b001c00c0f0011151400c85050122a000c2030707050390a4481500c91305030b40e4018000060200f000354003c00d070031240c925240b51070281c8090802c48035000411064500255100901501042c51600c0002011103900c014040301d0404401030000d1204070036840a100e2080d001500784081405605884040038003036500c0b440c02c9180003510b508002c01001351451a081481100643c0011007641d2180f0340711008240d6410442080300c00c3c00d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 172904226 1250 172902976 172902991
    0xe0f0d020d020d08041703091027081f05060315040c0302150702030105090609030d1508060a020a0206070906080708151e1c0c14010908070b031501020105071403 71
    0x80700c03100c0140c40f0940d102d61114054003001d903c0742d0901a42400e629004100d11020750f10500201250703984424860207184024100007100e00c601c6400e0500781c0b00c0611076400c4900c1d51140001da9000f0210b58020701c10f68107645002e07000c00ba454041c0480320140c40003a05580076a05c5c0c0d4000c0314999901c1500140103c800349030095403a400911801640815034400400100d0442e0441c2000d0262300e801401000160505240000780b1640c1c0e07000c0c460100480e01d0721022600c00682d070800c0144050222030b070a0315000c0c6020b44020b4003a41c4a250300e10014850b90700001d0040341301b0b49845080c0e80c01659010801d80b24490101c1d41400050210b8040c00c020407290500c55594540c090b4007a1140b00d4032402d540d0b841d004004408182603809108042100080710000b03010700401c1054407080c50038065800c50341e000480e9200aa41c12844185c0310300e160100d0880c0300100598403d120000305030a0480c0c040f001203082e50801c0e600d500c082194120031403400002c45001e903600005 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 172905476 1250 172904226 172904239
    0xa1e1509090204060e011b0b0604020d0e0102121005061c0f0e031c050c070b040204050c07050601030f02102f0f01060e1f0501080106030b060412030f0f0e0f0d02 71
    0x881d07001240490348558040700108920b03002c0c1100700c0d40c0003010f0b4170f250141c04150b07000d41c407040d80fa4001c418400400035403140780c0c0007800e10982e0b10141d010604800d5000021921450003141c407501c01a4181c44051820750300b07107000240703458074a04071414409050326403480200b20094040145c030a8581c8049000e4952403680c224000420152101a00c8402142e00d0710801c00365a000316107000d0720750005000100b16030004500c40000c2d0035041681500c00042c10f40d1b4640418501d4054018010600d0007071400000600006c4010b40310102e000b100e448038000e2014105441d4403044000741d088810709000720000d911807540c00d0034500c0c4121070a413011025000502800c407a000d81105008441150512030100303141302020f84900c01c600d002c1143c0d03e040400203083c0c4901441082d003007688030000051107032030306d0382620000c0c040c0c0402c6a5a28620b0701e40a0242113280050200081400c00c40d14081d42c41012850060503024041c1516284071034148200c01111030003d80e08041c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 172906726 1250 172905476 172905479
    0x15070c031203051008120f090609190305010b030102190804020307152d020304210507030b040b0f1017070b0409051b040e340e0a1e1509 60
    0x441e400e020501c4403105641c00602c40ca050b8002810282850f0454204c03540084628083d80e500c103004c4502004003500c1090303d41c000705000403c0e0303129425145820481f29505114071103007407000203040c0d82c468402840120021000c2c54203d004903125000341709500b45810100ca07009207001c41e009400034007580d926544402c3c0c00406803001400351800980e0191203ca0021000381140070a0142110403036102a10074500a603240243d0064040e20300d0f50440c02007520501111070b2404550210907902059034904046a06e00301c100c5d0180c071181041c000203401c8104191440c1c2c0301d0721251640d0203c980c1040e40020455942002075480c078800c01c24081050002c0001600050518000c00b0420f40303030031020781c3d480403041d00341003402103800d010a104c61454940e101d64000b60391020703c01d4083c10500c030340550214000c0d440001409404160038117940c00308051000400548481c0007060742e072202000150582c8400124007041d00350140b0844c46102c0c0380d000710007d103240695696 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 172907976 1250 172906726 172906733
    0x60c0c150e0409110103060602030301050a1e1a072003070603020c0a080d1b0c080a0309060f1b1806050f030405070f06020c0a0b0405030a1113020a081e0615070c03 72
    0x102d50f0f014043d660102c01074541c19056030300d4001ca80103008544041e50555242c5408600ba984050040f800301a0010300e40340000300005001c08000d0000b0b81c1190b06400726400b090700c103a4171103081a10702c2085504000c0107580340055010740703030074050014520103180100481c0250401c400c25982d1b40510b2200c0c0300410548405003041401083c8006090b0b20460002c266000e40344009030140440301141da004905400c06450030f010750750401142c80c6d40f00e0b240482c010700c2e0280c0c00c2002546011110324a50400d0305080c4500d004944529040d03840e004404400300311030b417040a0006d60200181300d00352040b10060368005101c1c0040f03880321910b4002c1e0701d80a40440e00594010381c084055161607260080020000b04a422850340c9454209004243c65240d482805000340d00c40c1c541d444115180d040c1054050b107001a41151140c4080400400171202600c0703400584500d0070085006201c818a010300592008249255646000088040a81042c102910300014034000000070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 172909226 1250 172907976 172907981
    0x3110c0601080f010506180411131b02030c030405061308151b18010f0c0c12020109050a050d031103070c0b0306100906020706051c020a0302070507060c0c150e04 71
    0x400580080c00c0258100034249162400b90205010640e0600c02804401d403241e00e03000382038006070b10001802e0756540c180b0f2007104070007480030340c0c020002d410390380144401d6a000300c11200840b4086050b031503058004030380d00d004a24462a9075041003004100c80d03e0b011004082610340d07243c08002d4596110200340c18809040070440c81401d0b00e208008040001a5007042c4030181c08070950709207141c440c580100304c10b0078080541070004c080c84590199000c0c002101c1c2a50341710384001d24082e1900202122200031000880c003041c0c0b1164003040c90718108292100740c5001a0030212003000d180c504882400c003030902c800c2a4001000864007103600000e006014103448480f80ea43c908007a014020302c01c4042001004001c4144010b12000d80c4c003040310300c01c50f81c15281030364881c15000c10b02e49500e00d41446811840380300103020003503660140c01524156015000341c80000303954040030f03500303101140e600500c51881c4540070b000d010b14401c0c003071174203104510f080d8a0084107080130404 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 172910476 1250 172909226 172909237
    0x30d021018140105010815010b0403020405180f010b1305011406031e070f08090a11060f13031407061803020613031b1509080616020a0203070b03090115060c030c030311 74
    0x100b603510307400140b0214a003040201443d0080301844a095032510060005500450100038800c0e901d890108503071501010b0035200c000c031000207440514045101c1c1c40c0c02408240d40c1c06000d07030790a00240f0480324a51103283d04a444480d025441141900100401544000c1444104585403810f24520800410314144221040d49485007070714001d45010302090001080003210354490191035001481a802d40e0503a0041a5000c680302c940940e4096600d0180f141c802c000d400011400201348510b08002d500c102c041e5009803400540c03900422290448082802c85184810340390400040c14044010001000e0020703414040984981d50310040c8501041403c4540004400c14003044a24141c0003070004500c0c1866110b5a01c0c00361010740b1414024001004001c10030b1010980034024418a40035581c0101580c01c0d4071b0721801d0100c0c03580c0050710070907182e41c600074000d140340c00d1a014500aa4280791100c8038004460b076801c603030450700c1d00001c404050b283c520345110349203003801410 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 172911726 1250 172910476 172910513
    0x4030506010618090b1f03020d020a091401020604021011120f090316150c050a0c03030215070c0804050918030301180f0207020105160302011404061406030d021018 72
    0xf0040160310010007610b9820000f111850455100c0c0300790754400c405030111043e52640040e41c01c860794142c00074094010119007560002030f1651959601408030025900c8142c020507200c6c4207080126501c42c0c01716030094024003640100c41c3c141d4083c271020141d0a086104450101681405000d8030b03402000340e08110a00201c0c01c0140e928040c400160407030055044600700f685001c084412128101821100340040b0808190501c541801007800290300103c000180c0e80c1d0744d240095440c24400c003007442c0020310038049a4030310300c55800c074107130355410641e0982400d003803900b003210041c0040d1000041003186031041c07032489402d0000c2c500a10013108461561405103828405688003402000d9002d48100003040060f1307009401ea5409140481383c86080000fa440c00f64010700c0980f2407a60310078802c40403c0100015600841480f13803a101350031007962503400a05944106912040700960451030341800b03649070135804100c9083e044031102c0b40e0392000f80c0701c00410b95400300414 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 172912976 1250 172911726 172911737
    0x80715020d2a1b050f010608030a230306091503060c0307020d03290a0e04080403020f090402030c060c1905030703030c02030f0703081513050103060b33040305060106 73
    0x1400c40040c0a440100c14448200c07032964041c2d031104001c2800402c030f0303420500949110421800e000c0200801d20110342960020002c3c0c5072121b030203683e643c111541540c00219000f01101d40540300702000111004580d00a6065485160030000d503802d005161441c2c01c6031800307000445940030844c2c0d500481c1e0401c1400d5690403e810700904126041c00803200345802e040040541105210102c0c00c008100310900b10740f1400d410005200a0f0740342d0007180d000880c2c030280014050b40100502c1142e100f210741c104c0f10349841c0c0500030388410440f4080d41c96003103004044c2d810b040040003000c0000200c41078886146010140303a203855021003003602c895001007130110801d9014030508651250600085d81818100c0d544403d440c861a80003d041211031404109194145042251505002442da041142c0201c440394001e200c2480b05683c2c1d18100b003034424450501a20707189004007480ca00c40d0441002c004001084881801a1340002c4400c200002c0814001d0103800d01824095660313 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 172914226 1250 172912976 172912991
    0xc120203040f02012012070201140a090609090902061602060d0f020903060105010315031b0f14030c0f01050403060506031c0f080903120106031e02040815150607080715020d 76
    0x4080410300f805c00c91088080013905000c64200150b01108013009a12032656030f181e6200485402c445401a00400200030404541684e002442d0b5020f60340182d548845083d80d130105901610321040010350058020040000c04032107898159615600180030a850510a000550215607030103d5600345141e010646c01784620741400360a0041909103024410204120f40c92502d03c1c0c000e2100800711000200f1036003142c0203c410310401130000c44050038079266207014000981d100040104d02c64054004c003007003d8a0304002000403400180e54a605260441d51001d00030711001c0d202a03414800c141d110103070010301da0148418503c46507640c0000310004e28002e002008041c0c07000c61140c0040c00080d2010341c20341646030440d0402c8c0780c04075686441580c00c000d01c3c610185e619400b503000080201d003107000040c40040c00c2050014031000c81e034035084034540c101e00d14040a54000300800c132242c04102420042c00c0b580d4001d403400040b51601c44180d0040b40c0c440082c0540e100c0e21004c2d03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 172915476 1250 172914226 172914229
    0x5060f070c0905010803030c070c030b130b090601060e0112020c100213140d061a03060403020d0210020306060703030c091d0f130308011a07020402070c0f0501050406120c120203040f02 81
    0xc003000280600300d803e20295041808281e00c901000308428424040030a108090003002c000540085d90048172104d41400c0c500c0c94904020410310060f21a502c2620118540c81400204075040300c28030360316141d0765004079004540c2c0c040c00c02c5491032030710380900441e58910401d0240e441d0307110381c90744016039880320034940010044090380841d1240507021000310746a210301025805555000f800021300c0158094805900154040e146805101e40750401c006c1503000942103c2289080d021607546020304d00710003081c0e100072987c054000d0130038403050001a006e41c10000c0f8207110303801c21f80342843e00c5000c45508000340000f50528000c92005010307100e00641110303504203903a0300c0c00c0034041441e510050700036041842540c40c50465002100c00c2651410b040d01c00c0d040d4020019569070516003000780e9411964001c0c03080100a00400140c558010300480d0100c0b01a503e0392084901040c0302c4100030040e50701c0300014443c1c51213151488119a200451180d0f104e548165440301c210300 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 172916726 1250 172915476 172915493
    0xd110c01020c0c12030306010e0406150314060f01052a0a050124050105032a0708090a05030303040b0a051b0f030415061d0a14010602071e1406090a05060f07 69
    0x3460901a260114130202e144d40d000c422030354400b500f030924107030600005e80031600810440e801850034181e60000052030540c95005400c80d0560010407010310f40b01c071000c100881c110703010500d022030030070481400315100d000058607000d15124000c0c030352002407684403030802002d1042111565542d20f03201240f41d40c01400e201c100390544048a03869801c01c000a40380d0700c80940406a8000d16a030251408043d030b6109503406042c1400c1035444504a02c0c0041082d004000342601c00c8480b0180407540c0c1c20000180c0e44140c1e00141200c4981d210148000000c1c0400f9161051240b0f02c1181602c8800700c80004045a200c0c0d22103845d500e160604104002d5103c58003500c000340d0802e0010003900352080c60140c001601103000f0322542d00c80c815900e00420001111218608410b4000990107030003043e4402101d0100c0c40b441e500b800249a51248071140b80101c0344000e50204003800e007801c000d00500000400542003000301030b121000070340c054001003107000c50000005400c0c0d0130840800d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 172917976 1250 172916726 172916743
    0x3080408010c18120203010f020f0c0705030a0f03050717130303020625050c100908070c270c0203130305010204090b120309061c0e010b0108070507030807050d110c01020c 75
    0x30310f080078030b4804440610398264510b02c0742002c4903510407008005d40d5401c0d800070060000d40c000c21035503026841084503140d0481c0d5640a814000c2c40400078490801140d0003400d69440521042400a00c0e50240e6098010820507100c0f03140c022071500b80340c7c1141e00109000c0710303401c8010003650303c0c620f0000c0c5030042c011300310000c022100070f1204c0582102440e04202c00418142541c5410003103c00c0d6140c56850520808010b00780b1841034103000c0381c02d000700241800b505d40d0b00c071092384a4209054040e01040c4080340745030503041d49000e110701540510102c00b00b610545e07141401c02c82140044230703c240c10a07206a5030000b42000400d000b441101082c43c2c05032604082d05011107015912402112905070040c54005445d43d802d905c1071180010011402c4401c10051402002c898001c005030b1280b90302040700d80001c903040c580200242c400f041e52542d14a100c13907503480d00843e05600301d40900341300c3e203860303400c40545c42c90602c003c0d00b04007c1c01000144c03110b548015207850541003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 172919226 1250 172917976 172918001
    0x2040308190c0f0212030d02130914070c1101050f1306020615030a0611040810020a02061b09040e030c0d030902030d081b0a020a080c0105190b0303041e0e010308040801 74
    0x141d2102d0300000c3c400c8401001480e0101e8003030348050308005000e401d40c4942036401400510000e41c0187d1003800420880950b03441c94410025446443c1044d01c14040582d0f6280c04113485641c0c07030340000c00c160000441c5003010302d001d5007024090314100040f42c0140c0d0004240440c80081400b84950410500d035000c2d12030312250600740154008030341c41d0b03040807801130912920b4801c0c13200e012440c1e40840d0010041841210f14090545135110002d400c499030302c00040c080d10300820030901000400b02000c0441c1c0500a182030f42c02403c0100801a071107086000340000c0c00480c110500c240102c0310b00205a850100306590688105418903026220034414800300c20240510007000118654989210a02141e034401501000f40e01e407030700c4040e00400342c203000280a031a404040d0004c7c0d008200720786c44180895020341c0340c40140c996420510b03415900a000400c22441a403045290034282480821a61074641c80100c1540400342c009a6112000040130058403100744102038841e0079 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 172920476 1250 172919226 172919237
    0x603010c0509010e040f061a0304110f010e0f03070504060f0504110a1b1a01090212130209060d2409050f01090c0b07080d1b09050d170f0d0204030819 66
    0x32000030703150340348000d41d045c069540d50540052510881d071040c0040c100c01404a81c4403420320741c040c1025401114120341031400d10034000401e00b8510586c07003034810141c5070300102e100c030070040c0301048018030190f44d454403500384006440d03115482602c001d0102448a03440244c1420184404e4440d408034a040003401040f141103410361180441c81080140141103500a596040c4901455020083d91b512545040000901a0700550042c5654059980c0c0150f0903a11082d080f82d01440044000e9000103003540040c0041c0f030710340000800148038502815100220311138081e0105424040c05803640e0791116100d09100341040004680e09a000c02802680d4040d41d1b0300c0c60b9071165104501c6a60b201146130310410007400141e0b01e050fa1900e40030089000d04038820440680b06041d5040421400b03000424107050090b00003c400b50071400b101040f2016805400c0560300000ca061103c210920191604d2034050005100440c050007030b07944c0303071541941c00d80ca1000da10282c203801d104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 172921726 1250 172920476 172920487
    0x9050d020a15020a0b0f01150807020a03030b15040e0402030717070510050904050709030308061005030c03100510030501030309092f0c01060308030405011a150c01061a030603010c05 80
    0x1e55540724035042c0d624003484501000d00e020426894030580e09001085840c8200400003080f00c80a2810704948400341042c040724010001560110b400369240350040c0c10644622010a000c0e0708449808603024111044802010b126034105404c1a000070b50000b003900300b4801545010040302000c2d04528104000014201e0200342d80c55000340321b40740c056144078441c8007141c2c0c0514142e92400074042c000b0300161500400040c61004240000c41c0031824400c0454054144816140c142202945035907283d43c071107550040c819040102100c411002080780420140c4070303102c0c9911440c00a4401180301d504510300a4000350454000c41100c1d840d20264204e20300300482e105480a080050131100b0500741c0007005184d2241000d402000d6080c014000100550000158492401080200011010081d4462280150301d8103113038130000300310b0f1901c03e10705010b000b0012007029000000f00c059549900c80a845281c109150300d074007010040107180d050a02405214000e03600d4001d1810 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 172922976 1250 172921726 172921729
    0x150305010f06140a0f0c02040615020105160c021e12060708010506070b07050a180f170106141201060918030e0109030b0a020903121b0d11060103060e16060f09050d02 73
    0x1c1c09840e0591080049480943c44414006d4400f488081c0d0090b00c1401901d840d0040154400111410080158600000140003d0300f071b00342000f07000955611007024215640030840b80d03c001207001481c07400410540300c11aa02d08003090b125004902c003400c00c03031802c1c030406091404142e025901828081001d10005400030b0f80440d8003d0340ca06080b500c0e00740c403180c11200c01c40002d2044000c3e05400320701040204c000507400c8100c9800416050f1308842c20622a030a030381740c0344100034034010f0b0021162114646031400e1010011720100006141d9616640c0318141d0b00441555481c0d0702c081840c13881032640c0000042e004070001e0800304142490b41d07485074400300c80140380740d10850f0b011440c9840d5550500181c40800c21004109840c2d103440320201c9a40c07000c0c0154800c2074401c010807504414041d105022840c3e030008086d02ca0340e031035602c0f1180a89a6180501058029091501d85d800305450340c5401800990340c40601d8000305400150040603141c10591260a4106580006 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 172924226 1250 172922976 172923017
    0x16080c040803070303020d0209040e0c031e060615070b070306030209011502101d0304080102090406050a080607080403030f0c0e0306070e03030319060b040e04110a06020c0f0109150305010f06 84
    0x483d07810724005a807007a1f400b0300c0500a00502c01481d81c1700703040c1252140100c0001030410b5611404a00352054204082c0a55a085c0e07510001c10f24142c1020000494034a4156001c072814200600c4951401d006960745800340001100c660010980e80c80045c810340c240b100e007880c090030040040c6100040c0341c1001030b6503000350b209103040c01c176110290f0000d900c600340c00c0240720300c1c00c00049a48440d120003810b0f01035007010010b2800713645010720000e041e10b40403c0e0700044550100c0908019150340b00202c4801714002e0003075061646078406804456010300c01e41ca250342c0103170b035107800c1c5460f0002050f04161010348414208400c2e0010b151003070340c020080300d800403008105185507500b01c44240300a01016840180d026902090025803a800303031124074403640c40746103072684c81c151b900c08015508509000f960010790080c5a1000e003801d01139080d81591720141040c404540d074030b8102c904421144a080c00000e520b41c80100300300f013019400301b4050309080c00d107403c038110100c026014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 172925476 1250 172924226 172924237
    0x1e0f0d0c0f2007052106130308011509050a03060f0c02010213120c090204060f0201110406090b090d080301080f011808090618030a0f0b0f010f120c080616080c040803 73
    0x32145010380000201e507104100e81e02c0148005008245000900c00c91602d80395258a150348107401b910300010101442c1c121403a104650507219488181d003040041030224503074629210510401c5600810181e50710405600210700c0b40c0400700d901c1600f030507124161116010500b040d0b80c01070104051403c100c41c0000b06440112281520480f45070400034900150759029601d403510014001c6030b045c0d4406440e20200207541c0092011041c02814407055105038400c4100140c0b00761410300200580b0001071810360b1000340b2040b008009074403505c09650081e032000da8541c4c810007801582950a005504203405003110190344240140c480e10100c2c0f041500c5036100d4131000610fa9000f4002801440d000300020b41118004042c034900701c00b00ba40d0980041d244100701c580001c0c1005204401315042c1c4a00101002d2543e1800021034030035220603408482491f8046804260148204005072107445d040c21040c40410401c40c020b00b0101300580441c08050003040107200720207000049a0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 172926726 1250 172925476 172925507
    0x609010b070809061b120f03010b030c07120810090e0c04020703020f160f1509060e010203070611040f0501020303040f0b101212080907030c0b1e0f0d0c0f 68
    0x19541c80da280b0380300100784184128164000408682c1c65091260f960301c0c0790001e051a0708841ca1101d0b000783e01d10203409600d05541c40300b4400c2005100340d52400001c0c40e000141c48407804e080004c3c0350390312100240020b1580001030302840411850f654410301c030000030b0504001c10000d000d440a540d40d00d4000c948509801103400207011401c140c400c2000510800d2500150f601854030341801800700034503417081c02c03c900b2080e10701040e914423600e140e0480350b0660b00c603a40118500101030300c40270468018581503001c284080c0b0086100307070140400d604041d4880351f50f51410034898a000255130340045046500c140100000124a1140110441d41000302031341b01c1e50f16014200c088200355004120740328040b0768a001000074403504520f4800c0b054031070b000360750780310084075998540601c00a01080d104040401420700b88000a042c16441542805450480c000d441503042d03200c1072030501c00c0c040005140340104120f120f00c0301d107100d43c0d10703141d07040502c1c0c1310f0003c190074440035a69 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 172927976 1250 172926726 172926749
    0x70f050414010e030f0a03180521070b0f0405040c0c0803010e0603100c02060609160f082502250321030605040e0c03010e07030203030a0f0c06020d0506031005060901 73
    0x10030168040d80a0042a04005046030f40c510300002801d91240d80f210f20403004141030803510504a02d230003580b0815a5405400f41940c02503100f109030410180b10202201030180400c01300e000c900040050800d5100f9196643d51546020140f004649003da002000c00c142c04442c00d00144c80082283d0450342c408100c07104a848140c0003904041e185c080c5446142d2078444040446600032554a1003443c040b10703220800c3c2d6445801c00c02d6103145149400014100d072004d62100740c011282e403900b0401c0c40705003000c0d1b800c200704811180002d807001940075074020b00070f110040c5149200d03c00c01c11401e8120000551039039540318210380e0820040b5444041c0b8a41040310180320354003c0b401000024010f0021802c4128007540b0350108a0038680a9400d0a803070001c02880000e03284100c0780d024008501d40781c1d0104049954024002110040141c0c41c1003c4010500310300280140e0b0807101d000103140d051010405142480000c2540681e90031f04041081a43e02c00e10094115004059603 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 172929226 1250 172927976 172928009
    0x10909050c060d020c0601030f33090303060e041a010b12190209150316020102041a1b120d060608060a05040506030c090a0e07081203040f020f030a110306070f0504 72
    0x711010b801080e0502c5e051b8403481000000703021940e0b44407400c05003d0381d00803448190001c50302c1c00c83ca9030680b480c8580a22040cac0b10321121416406030244a000703160025086482d000c00e0070302c002058030160340c5052840e1007400c10040e052529030060000302e030054585180040c100c180c000000308400d020f940d035046440220012601290921440100544071810a900385a1415001541d4403c00c1c4884140c844041a005200b12000da40680001c0c10340c4a03441051115194002090305543c1c06909030313607900b08142085181c1141301038440d82a110282c2c036005108640d401e5201d5020031210206120791074583c01313492019254140c0d00411681d9603180032070b1410102011058200d0117a200700480c0228560240314191a800165400c1694070309d0703803990790180b201201894004c20004900041d01800401c800188003a00c42040c01280500180c2420031081d020f071030303440850074282c0840c90140031072a030021050030484407150050720000c0ca00e02490181c1040018900304 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 172930476 1250 172929226 172929247
    0x130f120309050f060709060212030a0b041103040302030a1206051305041704030c05241b0106120503091206010f09020c03070606150806043e160308010909050c06 71
    0x20941000c2d070082e08491090b4180600996141011143c00c4002081c0040100c1c11500c08641c801c0b1501c035602c00d5a0a40c0c03541e0035448014821000010b504c80c0e6075900c620590f440d14000740d0300c60343c029000741d9201c406032070010f000300c0700040301800c4d0146043ea0500007542c038981858180d0b150400c0008480d0355528043d0040c103400c0060b50802240480c0000402003858040c02c107407401621240000e03103a442da501b40340d02c020040d4071000b840a000341d940308070035110075401890060b000031800742c0c0c0e107001e60702300d400d8080b10607243c0e0380000030403ca0323031309060101e0017801c440c00c402046030798036000e80705040c440c01c0c0c0110000c00790002600c0e14240c10400039030310501c0c0c0210f01001200d5070780d0064800c0c034244501c981d01154003e0001001841c280c421801c541c018a00300d00d404001450b04d210301c0d00b540880c03054070003400d0340c5403140c100c1c006006480541d0710f12807002420b0310a41005070040c0300c164030a203010790030514188006a00070800484040058034203d07240d01c0101d1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 172931726 1250 172930476 172930481
    0x304030b1801060f0b0703020709021602010c050a1e02100c02030c012328050a050913090c0b03060f040510031b0b030702060a1109010905150705100c0206130f1203 72
    0x40c484c10030686841d0001c40d0302e000c088000c00b840d078401c3d000c0b5021203556611400581c001e000c64800c41a43c907141d54009940100301c103040d0903208000340c41c401c950390766943ca0074645034103440c580002c5000d0802e0840c01c011036039002c442c0705400c00418035072031603000a950b90350074120107042240ca582e0304120300c1c0280c1e10314800307908982d59503501d4594850301100c441001120014001c0d9060301801280740c0903a0131a51328049566410380340c12884030510000e030400c400b24003501079840307075000080350600360a8400350181c0b1054550320f0500c1000c00c060030141480d4644603a142c5400e10400081140541c01141c1d8045401004142c0500f010f845107200c6903c40314000a00004100c4460b60115a5510940b0424001c000c020721502c4c644140e030240000483c0030651814003406a481d010103242c06406415103c0382c0307000c425540c1c00b4103040900e0780100600b6254001071150a805000840d40b02c0c1107000380c0704180001da2525081040c1c60103010300504801000c0b40009407098 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 172932976 1250 172931726 172931729
    0x603090a060f060b03090307020118030503121009150905010501030c05030a09020607021305092b08060307050a031109060105071e0204020d0606020a1719080c09180403080105030304030b180106 85
    0xc4026161304e041006c1179181e500c1482d0480c0081c686203000c0710703000084034280d0160303074001c001107041c1321050031030b0f107289400a807466424441d5140f00180f8020140100b0b07140401c07220510721a545003407600c0041d0340d41a00458185402c1c070790074024503580003003904d80c007699002c00425401024008a0041d104200001e03400074404508840300c602607400243c045c001450490300c0d5110465260a038080300200408610344001c8030308420184102d00c1c441c0c001c0402400e456070f00d503a4800041c03044010fa8001c960a100010307400000340f510640b00c03940004282030036450130200e55039515000c4800702c802e804a45a800c2d00c00305540b207a9040d15684c0c201703514108501501e800b0040e6880c81c80b0302007240c00c08807008030680001180e0042c0c1d20400c551007c6a0b0231810101002e0b200404010200c110040301403003410620740d07035000c0111743c001c49040c5c69015405c06040050981c0c505800c100d0007903208100070000107080b401d0407548030070011100d02c07121144461035409880715 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 172934226 1250 172932976 172932989
    0x9090112060c08071b0f23060c030705030c070606210b0c03071e0c0c030606050424051e0a060905210307080702010507060e01020d0e07080604080901050c07060f0e0603090a060f06 79
    0x42059540340c2c147d20300d82c0c0580c4034917021281c1a075508490880705100444e1801c0024006101094a488050015004007446020f000c41e05c02d89a200d07498000d49000704c440485240c081c440418004600000b0340c2101c0c907044414a10301d041c6030083d00440404900045040c2d070031526210807407248500381d100741d900c11000519540d59042c810702070f040d2402402c0c882ca1400b101d028030440121840107900c20101d2003901440d1402c02000311402845500000c1c001090780c0c161119550f003035000f80581129101c10611905210074000620215080c0414000d40b40d030403030030741000000603039828030b03407100d20155100080d10040f1803034000c04800501e15410304070000742c03844042d0090030300c2e4803409800f00700046808401c942e4800561281100c150001e8011801158440e8000d201c6220103041a41c50a00400e21140c5000c007181c1c42500040c0780003c18140b200c2d0310a20000e2100d0080761030904500b08000c2054444192900007002180d64814103a40b00d50650044001070a5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 172935476 1250 172934226 172934243
    0x60105060f0f160b09010c080402040b0f040906020a09050907051e070213050f0c0f1b0a080301141519030f06080f150108060106050703030f0209090112060c08071b0f 73
    0x34082c00c014000c0700f0f0000110360030200800080c02c2d07083d0512810920000d02e80d00c240503a200e039000e200041020103400b6400520900301c00b40c0c10b44070fa00801c2c5000e44601c2005036600403500c40100314500e29081203100300004000c1c0001e040d03000098030190081c25842c80d00701c800200800e10280b0560030020b4001d2031065000040e042c490b800310344240115842e80c400d6030340303104c198034940c401c040c0d5540fa00c80051151080280d240713508900b030700789510200c40700c030b8045c0d0711004243d4200340d02c110051414004d181030b1500b404250215002110070415060468003004010700341c10100005040503a24003250301c0c11f007040d400160092199409480c01407101d03141c440d827034101c0354500031a03085022000147e20034000030058100c03881d595540d070400b0305507a01180034040d500c290321262602407000c003109a40300071500b8020300c3c6c89189103140c20014175040c07040c0c0d182c5544003424880000208440260880e2000b69100c0f070044042550303552915118404044d00e03400a0329824 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 172936726 1250 172935476 172935487
    0x170712081621090603060f0e090102070209090d0306050f06091e040c030e0c0a0b0f18030304060e030f0a0203191a01090c11010b0109050402030a1b020c040c11060105060f0f 76
    0xe0601d40803018000081e030f6280c503140e4480b1001d40c140d410b80e1092082d4000e40340020802c840b01618000e8020f01240001f600d015510380001da285e42c829506e81000d034201c20800003805401d845048001d000c01d4540440d0071500380000f503058050266800d00a46490981d507000d55048880100c0d00c9400400401101c0d2240800a000f018041e0400a04e8421900040442d103040c284000413a038083d88250f01e0120483c2405000d034014441c82e00500300d030206050116034043c00a00080d08072a901c1204048a5000305407520240040b10805074200035001809a100440c2604404594540c4181d04607618640010b052081490840000400c02d0001c01e141e0126000740703034100e400da55000701e4100d0748240035013200c0e1000841c601281005c0c104001c6400d0a07000b0f13540c040c0e41d42c440002c00210021040586202d400107210040e04001600c2d62940751500c50902c1a003210700d401694075805080e060360303e07401801a5071040c07101042d1008040010001c5039101c041c070891081e10351703 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 172937976 1250 172936726 172936763
    0x210e0a1a0a0b0906150c03040911090a0b07020901030206160206190e01050406080a0b13150317090a09090516080a0b07030b0303091003020408010204030b011707120816 74
    0x940280c40a460355818100028401c0c503000c05003074051040107100c4143c405179184d08841c0c80d4004200f02406001c02c0c0030010f0048540d220f9240714000030210107a451160000308200c00005030040c88818800340701460141c1c170381c11161415260306903803240c0d40340e1040b900ca2030310030a815002903000d04005613100700030382c0c54419039001000a4840700c1c11100840c00540d414092400303003900040400000500112030380c0c100b01c0405401916004241d608d042c403500558012494091079000303c1c02c4100100840c83e6060409203044180d07150602c41458001502d40c549e610900361695113810b20101805424803d0030744560300140320300855aa101d6032151207003401c440903901d81d107240000610031406800f840202c1c0a0081c041e604d099003040c104880150038031016410140c0c00e000110f0011001d100a00c05140a502d08601a41c500384030040e41c540c1c0200002410f802400c02000400b01100c015500d0981c0032030742d07544030b030582003400503400710320301010340001070520801404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 172939226 1250 172937976 172938023
    0x1180306060302090108060702190312050403181a0a03200a0206090606030a030903030c050a150207110a060503010315090605040b0405160605031815070f020706210e0a 74
    0x88a1081c4eaa5800aa0780e4028458030b402046480300b0158008011101889009070b6009100500c00d017444040b154888d03020f035003241e0040f40e00724081040040544c0b0310b52400203848008020040d0b5541c0001e10298076130b0765a0080744900402d050b1508580103010144400d104c641c0c0c100003501c203803a1800f1350402940c4200c1a00c03164100d01550011a4403420081065000c440c2c01d81c80700880c9a107195821100110101c4059446000c0c00d00201d00145824862201c801c401d40ca000d0303203610b490f0900080303088800e00c206100d0001044200f040ca13800c5000d4a046a4100e8011030040101d40300780f0000d000102401805241b52004101c1084ac20801d4240607a01540460383c1e941b15a448842280d10359000c5c202c0460410b10014450707254a40d085498003810000f518021505202c00c101840c0301507803040e010816040c60076954270741c1000442c0003001d00d407401050080310208480c807401944917294044640710503a04a07010003c004c20913202e075201d8400d001c1070341c1480500d240d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 172940476 1250 172939226 172939229
    0xe010216050303070807030908090d080903010c021b0103051017070b0304030504091a090411030c090907091103070503070c060e100e010f110d0203090a02090a0204060206101202010e0118030606 85
    0x10600c800041960141f10b44a681c000d25446444103190903030241c100808000c0d0b450003260100003c0040200c00c1c1c90a0007910a914282d400920400d4540c242c071440001019002904052600d4200248802860503502c1101d4001c20363369607503010100a40d08002050300800d1200d00c000040c001015072203001441140c0036108200b01d294201c812654070780500d518160ba000e010200401e0200d84500141910120000d003160018242100869040d280c03c440160701740e00003400030020800c06000d04000c03891141d60700c41c9585428200903000d8000a800300c001c0214402400b800c04c20b05a002034001d03a9a003040700c005205143e03401c0c02505110f600f03c00194203184480700b1305845030040100b0000c842c000541050b04941d0804001d4000800850036481101138100150302d0310f070140e0f801004013139405079480703040400103850150040c0620400c441d15000811080000001030b05001d5424a8188081e0000d5001203c0240585032805040c80060100204108140c0d00400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 172941726 1250 172940476 172940491
    0x10110f07080405030c0d02100e011e27081b0d061e110a0c022b05060405010e060403050d0515060a0309031101020304020105040509091515012d030e010216050303 71
    0xd5000c5080018040141b01980e0002c1d00902d010b0116603509014050240711083c0c185080503010070b0f515000c20000028040581c0440e0038031403441400002c15009010404d148400c611490b031500c24115a20003041d40f841c80018040711340801a90ba54003458204203800100910155510404800828101ca0360720f079102441c1804155a0104220565034140070315210803202d90110340078000c4550381c051088400349441e080c1842d020b1401034000c0741050080c40105824606031910900b160310f400202c42c10b07035014070701300030000764030008494081c0040da42c0443d0549800c0440680d621001c0e00c101d0344080e000c520462000da1540c0422203450099407413002a00c1d00da90a1400c0744001d8a0190000700c080109028504040c102240c2200e4503604403811065180841080340d6820f070b42c04040c031410140340040e0741d0f0303201244080411409100e00c100049034901021001c013020361103004e1548038071802028100c2035040e02c60803405004024007003d521710700b0707d44130751003124a04c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 172942976 1250 172941726 172941733
    0x1b0304090b030f0d02070b0c070503010c0305241005160215030a060e010b04051c0822060206071706011b080d112b06170a030206070e010210110f0708040503 69
    0x1180c1003040064200f04914403900075080d000d04203007140d0701c08c0d0f001c0700b046640c92240940004868800744a40e00001a903a9000074450a0181c840c821210503a0700c203c04043c1040e102100719a158940040440d0490420a40d140e03c5090101044140781d000603522510b4140007083c074000c1c140081d03100b00040300302002955240c0c811414100400c0c0900180824107004c18421414540c00d110303a0a4441e800c80c55a81d0f00d05c0e5502c1450394410350340030101d107056495000c407040c5410310220150080c1e0010780350518014400500092100a940311040650000f01e1013613401220030549003000100681f0504015041c0210f01c0c1d8030100c00c0c0d10f00103240020050180005005990340078429400c50844180720a8603c1c00e0f609034a040c41001c107031348600003d180401f8174025003441d0000d002500841419041c06410020014242030502034008045480350317a010401705450142804001105101101000c0b09401045c2c1d0030410752000080c50018400d80300c02906c100c403001c500301d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 172944226 1250 172942976 172942993
    0xe061c0903021e010603170d1413020103110a0503061e04020d270807060e1207030e0102010e0105011a031305060c070b100e0f060d121206050402030f07051b0304090b03 74
    0x1142222458440944103900d13a0b00e2862405c40301d51f008003030501700c1450102706284401c0d8520382003142503c140610905141ea85400c5503014000d42c1490001c1c2000b050074414821b1000c1c01031b200040245100700040c6045449502450086078502d6001400454072440311240b240002d0641d044000c40c41491180c40d50610002022041e200c07079400001f540c2461000d07604c50000c2c4c00994120890f9005240340b84100005050241841c039000703599012045464000180c01c44411011800b01a4100070042c40750300c8400811705034480500b0411aa65540da0702d41d0880c8094240c00180b141c040d100910034083d00a4001d09030070b234082d154284a13901d5201e030b2952555014410401c660201c08001202d0b002e4402d4555808071010300010403180c0d251383d4034908a4001c10103030010a030480003405c01d801180c82200080d141c02d9a00f18914280202400d0074808003d00c1c01c400c0000004001d51303100da02c00140c14402000000f00e030b40322501c84007050007400c0410450350003845003154 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 172945476 1250 172944226 172944283
    0x1701050f0a030b0702070905070507150501060203030705070204060f0303090e0109090f0803131502040f060311070b06010c080c0d0e062107090512010b040e0d0e061c090302 76
    0x42059605500818009007185960b8860801c0b50004040e4800e500070140000780708092800744601c00c02d03480d91081c1e0b03903881c14a04014104250013260184515050043c03103000d8001040366006207080c01c2c1301c2d803203102c03a2000070b014041d1504030700400d011100c800810140c01080640035070300340901504440c0c2e00d8960180c12100580005032820351108002804242503900458012154800c00c503154166912400c1e081e0500c40100703102d00d640080c00700600b1040013400b40c00382042f40703003d018085da851800803440c05505c00c05000c6a0b80d0b4004501305d60300030002c00103521b512194060b2030b141c0a4003c2612144401250004201c074041e0b48002480c18004690701c43c24603240c03501906080e9200841c24210042000b01403000c641004510342d03544d03090b0b8008205040c03001188100d4030500340801d50300c100302e0141107036100750001d10305582c111214412030301041e00c18a0300c4400f140144900007000085000080d0b191107006811700d540420201c0c800b9001c0801d42112051051 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 172946726 1250 172945476 172945489
    0x1030c0c0302030304030c11100c030e010c051c0207081002090f101b11030f0c030c0d260403060e150609012111030d0801060824012d170105 62
    0x280207006030010400140001e004000104e199030242c0328051701151500045202130f442040340c0001b02d01140024000c2551000f05140249020328200d03e0044483d1368940e641e4441919840c516000003ea44003401d01c00c004860041c038a1800300c4091405890000c0002d40c00110160300691035900041154240702c0c4a0519a109960f03840c617000c1504a00035400401c044011500c3d00c08110701c0c242c85a4041201040a00c1010081c104103201c8404040c94400030340c034682d00560002107040085519511410348040c010140d00313030140b0030151814543e1049420081070240761458203034410400042d91401403803400325032147c07500c44008101c1c07112424400d841101c15000ba00b0510b00c00d14000c0c02c00803074400d1074459a5449040006404c02c03400c0d11210000174586070041245643c403c15145c2c110090b0310b45445486500c012064628002c104501d060041540c003050b1108030213005540d03c100b0403000315003100351240d0010310542c65401200d1280e2100c1c0c002103210316000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 172947976 1250 172946726 172946747
    0x1060c0606060801050f010f1107141903030503060d0311060c0a0305071e030c050d3b0a02010e0f0405071101060f0803160f05010e03040e090c01170603030f0c010b01030c 75
    0x1450400d0b8001c0c6c4d8001183d440380048052000c2050500d0010030242080207814043c05c904850180017440b0f150a02ca107102401c0c882c803c0c9400507800420100741c109044a070005400d5610503490045428113030b82242d0222000c4070303c1d11903a41080f518200446c0170309504003480e0f6050090b6240d280741101d003c0c00c0f40e06560310b034140000c2402c691a0003603002c0c011803100c03420403c1c2040b01040c4024111242c0744040c0781c142c8401c5148524403c503441040110008400c103482c41140d0091000e80ea915140034028107201440000c002280d031601c02c140041d82000700240f10b1071030560303801402e940001181c8240c0d9030274003c022902180080c2d00b0340075150014011418501d41c1d90034560020030703800056400794505402d410202d9000c1c011000704d015a5001103980d2482c000082120f5a001001998150030040502c55140c1e071203000d074101e06504200504840c0c03a420300080c2184160030004440c9500060362807103131a819000303403074244402d0328100080d0540900c2608d1035000c8 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 172949226 1250 172947976 172947979
    0xb0a0b030d03020d0b09240607030e04020d0204090906060f1703120a020702030307210309150b191d090304210516030f170f09040b040f0501060c060606080105 70
    0x202005010780e0740700f64054400c05400307101c041045501880402c41030402907030424826074a540d1003050f20a0200f1903950100c501f0b852031482c04940741c8006142c0c2940e500390502c01c0781c0024a03800c5143e03031501a03c014003d808002c10034505c9518040d00200360a10480855041c2d40900265199220a19807050341c6076402940c9072400c8600302c4104000c0081c11900019801d00900c00035880030005082c10070300c03890f165506000550261a10302d948003695200b01420f1008400018141015400f81f10b4141c0e00007040c0015481c00254041d10440c20092850400c0440040c03040508180640d550b582c1c0b03940784a003070701e946c1411500d0344034034091001900c05844201c440300000e00203405201d40035005545d2031461684061010341c9480d8415200071703a010000405210458034543c10f80603c0d0507503649415004141c2d41c050780aa1501548156600c01d00c10501da25150420410100745442c10841581c503640c01904d07080c10f0350010b480b0b030751400001140321801540041d05aa00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 172950476 1250 172949226 172949233
    0x604031e110f0d0b0406060b040e0426070f0302012d05010519060807050c0304031109090f100c0c050a122604080f07050714030123011a0412050102070b0a0b03 70
    0x3c890712482c2c07050b80003520850321245d8521000030078a040401500180008800e001e2072803c042c03c2c00c148105107040d8400500030030411080040c08008115480c961f48102d827454980c40f1810260300400c1503144134858000c00f290320300c4408221065160a0b60421102002243d03250b0301481011901c40e210008c000d1101142400380d140103100c9143d000640d8a461403614101c8019a42180c009174001c840d00ca441c80f80009591402c44515548511050006c00049641c0190155103d03420000800d400e9960200000010300c114241c081160b0000200c8045c8403903464182c0603800020715004c000389100001100c65404a401c0501071038000c05050762a80b135940360640150b1048010903004841008014009401800040000c0a0708040140101406001d050075a01e521000081c40c001d40102e640710350041c110001d0554041e000c403c1d001c8050b04800d6580b030300c0b90b50421044045e281000740100001500100421880350b13140303000304d13240c003042041a10080007401c0e0b810307003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 172951726 1250 172950476 172950499
    0x14250c0b13140d030207120507020a0b030c040302041118010804080a0e0117040c05090c0a02072d0f0911030412030507050d090b010512030c1b0604031e110f 69
    0x440d04200205801e001d0300c094458a40c0049282d0328000d242c103400000b00350049240c80a01c540b0350031080c00310190b070809030321b0458580c1c00039160345c940d40140c49851b04007001041181585805a40155a0180040081140c0c031908207085400142c0c00148a00768038a44a0407544204070f4240034560014001c0d040c504091401c3e00d401c906440c1e02410420450302144034080514803141c0038034040c03c10505254100380034006180d030000c0440b5001101004100341165000030003008071240700c0f0300000c00c140208196034440c00c1d5032100381d0b5040320381d030804511075501d201c80000305c030f0414404014165681d0303000c0c8060300048038054080140704140411076030003a0410f03a0702600d0743c03512628003184510350508840c280c0d84140c030045002d20040c00b0504210078010084000704c4000c0d414171743c942d840d03140d03115880024124030300460b003075071201074651a050360051507225400d410f10302da4202c111480c0304007902c0103440b454240d051205081c188015500d400700000340c9410070380c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 172952976 1250 172951726 172951741
    0x20705190816240e01050f0903160804090203011503051501050d0533010206060306060d021212031302030c0901030201050307050c0c04022a0d05070308040614250c0b 73
    0xa5010540036640d160700c0a160084203000c01095103000f180d0400001507103000b2008241c211880204a040700201210a00803841130000a5a2100d850780d442e21070241e0704c0346805c40081c000c41e44500315190020001099800030001c80110640169404201c4c954400c02e05031a280401030000b070102e00c04101040c84045980c021603400740d91219562900740c90400c0e0a011452103d08591209110132041001036034107105075900440308074010082810300ca4001035681d40e0001000f48115442e00115200d00ba007842141081e019070b110454a0b441c2500b0701e00350441d03c4401c224070138014100030b032170705140c407900e0107050b42d4041e582c1c2030645e610040d0684a541c8003070005003603031207800301d03855481d640e50000b060307980840007034244c1828441c0c450503138407004003086101c2e94200c412214010340d032140990f0072154040c94444810348560415400805c3c4c88a065410840c840c4100303e10440c085c1d0201441d81c80c50300b4840c00256035070004a51072089600e0052006e5031080114540 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 172954226 1250 172952976 172953007
    0x605100825270801060b03060307062007030506060f0117060603180102130603050115020d05030709090507271802090f101d0d02010c0f05010b130207051908 69
    0x956609140005040c00b6065002c03601142628203440089100c06210b03408007801050010803400500c5030540c2001800203446800a001d240300300642c5010552890306408500340802d8588415a80d03800c2d101c0c20301c50307241ca104944ca076018688580c0d420049500c14240318843d10483c0e03a829080b0780340c08080289030382c0300dd092030390302c142d1000c401c100c000e0700cc3c4000c2603160112100c81c0311041c036090300602a100c05030b02181c144034114003c0c42c0c3d11500894400001d192602d009607803030343c601c04182d416601503000000c52503d4881007160030381d040001c5c0e5107840400d5006101c42100c83d101c003848017000b4080c2e200a902c00c2c45890b5403441441d00a004200c1009080034581c102e04ca0100c0c0008140d102c011000a50490780c0b915201c0c01907201c2c4018407015154070380d6141d0140c00107403881c44140401000a0b814020314001d2080a52103880301030401007150342000017840c5039102942160000b03031010300078080903024806140010b9000e20741c2c0a54201c6c02d0108008402030b0b03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 172955476 1250 172954226 172954291
    0x1060c052d0f06150103060e0c030c1e0711030106060f0c060207050303190f061a0d062102040f0501050f011d03060a090501150b160606050303030a06051008 69
    0x2200c0c50300e2240a511a0501445242e001c07214024407940c070700741c0b0404642042d521282c41c103140c030b0400148004290b4401f220782c044c88480582d503481e1291190000c0601c2600d0012410081c0c3c12000003480b01d03070100504205024038010b0405a0b44841054201c580078420040803800d07052252a00d03d004165031954a4081c120050406116440b1542164400c840782d1211004840e80a00303011194030072815008544e0508018650a05607140d8048180080121940d40003007401c03000303001c07242c0200010f405212402c05003074131001e1a4081241010504a10072801c0520000a02145205640c101d82001b410481d0384003184005403028510210348509844040340d810003e80c808010035030144c1d040c02c00000c0c0c01c10141c100795003141c410174505054101c03540760420010b841641a190049407050710041040401d1510030002c00b19a8405600350202104000e6415620b500103c100c40c000d540885c0d8512145ca01240c22601c2114030300c0120a01e0340c0c3e156010201c090080300f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 172956726 1250 172955476 172955533
    0x316050609011b0606030b01080f03070308240d111503040b042d050c090705180402090402040f09090b06010f120b04090503070b041101030605060405090c040308040306050a0501060c05 81
    0x7100a8440e00e440c13040e2400342d003080d5003003441e09004000c1e00c030040002c00303a20041840a1420881c05550003883c140703000d4030074002080101c0c0b22142441d105144510120001030600c1c01858181c98104a000c0c03000400724401c14002126079101400f0804503882147d00c0009401d041d580d0f0340e50441441802d82e45d100121300c2c440c0c2403078112440011150072060084004015008076071081001072500205404100135042c820403480207240c8984004003142141e02588171000400402e000303020710340c0031900c200ca08980009040c80d440d40414111070207010480d030350341c3e109801501c41d8a0503035002000288444e001c500d00b04100c0d030110000d08002031010074004110b883d528699040710314152549040c0509000400013141041060300000703090030b000d014605800180700e400303984036142c0a0701446000501303138030000080b03d028590005405407116200d04001c0b0080808688841100707181c00004601d0034041d0064591250713200300200035041503030a80c0c1c29100d006400c5034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 172957976 1250 172956726 172956767
    0x120b0c0c030a0914010e030a020904051024060201021c0b0a05181005010206071b080f04030c0f0803031b1b01020a0f0933050c0d0302030402031605060901 68
    0x5803034010038002042c003082103a540c4041c003802c02c10210006840f20142506010b1540f0707070035079191804514952411b80407565070110f69240d040a5007029003070b14804841c41d242041c040c00c1001818905900000076400d80030351a92245802c1c0e00b01c0c401c0c02c017103400c48000404c45000d000603980100d195000e000d803190560035a07030000f051107500c40c43d2031040540e55000401c91270005c40c1c18501c009103000d00c02051603041407074001d0110019644610320010724840782e502807003c40d00483c1c070001c030300b13010465440740d43e410300110703055140c051004c60300c005140003c0c0c5a2000026a801241c2120440e07000280c028000492a400410140c030041345d01094141410000e1012781080d000319200c5102028001e50000c0207403d003500404185e0f18081c100c581c03895114280c0300507540044a4486070a010240c040c1e8050007800303000c170120b20401d10024003055054010f1402240300f58203d95802c3d600f130304000f0801d00203014068000311f051200203842e620904034941103595408a6 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 172959226 1250 172957976 172957987
    0x9040501020d0609051905250e18090607030605011d010e0a03030806040c090e07051b0d090e0702030304050a11040f052a03070f030b0a0504050702010e011104120b0c 73
    0x45050700d101c0c0c4e0000703a94999035402c02031525010702c412641071a00309020402880c124988600f0003421428100990f094207454004290154007400843c0304014203c1e061001c401b10260790002045803425411b00851010480700360080c024034095803016150320f408a6007004c0606040c8a00401e020704116041c0030031003540d1240c01a03c409103003e65200d25061900005000640c2c1c1c0351500d842c20001c4030340c6e0070000b2910101740184c10506c1071410030790350500490319030150450140a04810b01821032000d8071030742c00c01158404c032414000000c0b855540d0510a03a01c2e404125805010341c3c0104030014009500034411010000700108000342c0a480d90500e201111401c440541d460903859140c0c3e035134405111490402040e00c0a800361440c60010130081400c4085030b401801d0588444821015640390b101102c042c0001500c108894580400003c3c041c14110a0704007a9510f081500300030000f1010071035068604800110340311501c203035a04401d45800608050360400f0500a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 172960476 1250 172959226 172959247
    0x9060607140c120309010903020d05010b0307060c0b01210605100f08030918010f09110f0c0102031f12030513081507090509011802030414030309160906080c0904050102 74
    0x441c049642440028000034000e5400d0041410108075110b00d9135100340500a51a81c1c00f161003c00d90380d0554038541c000da020718149014010142100e0b905014482d4085810765001d8409501d060007100001d1507a682c400d5202046041403503d1380140c45051a9200407502d945c002582045140040003e51070f0f446a4440700400703103800015090f040040e882032070b8540840c008030341c0308070100780004030751404151600c0c0316060b00c103680c1c8190702c80020751240404101628007400c00014480d0340d49681074005030003544110341c2600103607440c0004222407150b501c0e034603082d1000481400314440c0c030750300c0030b9070f0030740201c0d06031003c58a05107004a1450b03070901123003411031000c84800d115410540006085503141d5001903004a903804010899043c8400c400c09020020703800060f0b8030744480c20003110003001d00f00485000d120010900442c520001074505c00b01040c0d40c0142041502d80544409980030340c8258a85944240d6150600703107404007103d40c0140c0308a000501e08420b826 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 172961726 1250 172960476 172960493
    0x311070b130b0909160201020d09030305090105100b0f161b0806090102030603030a050702040b2d0301050f010303080601051905090108070e01091a0d060b04090b120c09060607 77
    0x1000382400e64008122921007100c2000044050840c4031681030800b40000c1c04600c1c2440014402c02540c113062403200c0d800d0b4005c0d8110390716407021400900c1007141504020b80508419142c03d54198a07010010f90410006102c11040da0300c1c007840186048103100110020f500031601e8038182c511041c80c02000614a01500c107118070b00035083d642110f141c20903850610302e00410b1904076900402c2005034a40c0c0c013104030b031100c0307005040c040e444030090700100d0000c191f003150154101c13200c54044090023604012880c1e24400326080820007414120615007030310000c0c0e4440310042000340c018000240a030344800e50000062403c1d90515800e0b095107520000940c030184045840058801d02d1560310062407035000126042141b0f45d01300c4600000c000c40100d00c11400c09070300300d0320800701c04080d1804442005101c0c14040c0070007511105800b20560042c458000d0040c80c090002c036603030502c5101c41c500400141c01411480da000b405010065000400e16507000f0b804110120006249a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 172962976 1250 172961726 172961729
    0x20c010e010b030d1b0204021308010c03060e09011802120a0f121403040b0a0c0e04060b1c050606042306070b06010f11030d0207051504050d0e09060607020409031107 73
    0x3400041910a140000d26081460f0215600d040140410a14142810201c0c54070342c140e606580059888540c20700303c00d42c0328017907044500c1650030074902a15840d8140c101c84145c40c00c0d9440701e28940c0340c0d0a001401c91b0f00e100310403a400ea082c4c050f000c000d460b04098002c07580c1034a00503a40300716115501d108807051400c00c1198400038410090440070303070182d189104040201441c0349903042c5a01c0d000840f050050011010f2a2603100c1a928244039161161303003443d029201f80a030b59203a2550080540140031500c40284071034006900d54010f038043e15004000180200d4581828028a540084400682d440c08111140109405078075014010102180601d000c480f84d402c1c034100050164598607840010000303481400d0010b090003200311200e13003030788140059880c0124034015060405103440e220351007100e03100300301c20f00101103200400310b2515503641c44052440020000320b03010542d40590042e03410720800740103040a40c0404d05280c042e05103540455404180ca80ca820070341d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 172964226 1250 172962976 172963001
    0x309080c030a0c120203070b0402041a13060306050604020906070201080702191a090d02060105011d0904030f0212040b160809040509030a020c0f03120306130c0315120b01031401020c01 81
    0x400a0b4018040011100f44c000380051020b541f400910f9200da101c04031010b4006031145580d80041c0c99040042d00f601540c1c0f01000d040e062458144201e0f100003400c1521060719603c2c00e2800107400da180c00d200300c3c0c1c0d084000420850401085400440d100c2000500c010294400c02003061410a40c80030404c1085101d280001210741c203407201e130718062a01425031541a0f224021180c1c00d2600490f900303040d1340c0c080c81c080f44030116a8a07001c01a00c2c51606041c1c006c40820180014550b00c40b00c100001e0303c25408441452082010303005d4244910301c00e5102030a02032109005080f140c42121403028081c501c400c1c10100300c6130015085400545824005500c006031042003a5010720144000e46021035241034061004004203488144d11b1a140101000001c00244141d5580c0320790020650300290410940c41d020a0280c01801c0d180f240441e451036960000a601508036620045541c0c084070710502039203903540b40f035520004a65803070440d5400f130005014440007480348c0c1c1c201c00708 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 172965476 1250 172964226 172964237
    0x310150f14010f020138120f0f0724030b06160b0c070b0c0307030e0304090c09090c051606180b041e0305041707091103040501050108030405010c02010309080c030a 72
    0xc1c00000d005103012400d603c065904008050142022035203200e802481845032003080480020300e00a02102c811070065808480000510324144d000a00111215203150864810a500c20140c2c1da44a01611a1b1049541884440e0032041d03000c2103001040fa0003401c3c0412081c00320000510b044d00100304022110711441c1c1e40301306029509803031680007008c00c3c0d00300d032514082d500c501d400300c1c00c000c003000b00100b000800324001d140b2952240c84100385000c00c1c0c98030749456411000244c0544490780000440760200032902d640c061243c150207104a850b02d43c90001052290341100340c01107003c0d112565200b02929100c4510454440c04a12440c0c0044a602d028030b00205130500001c0d5080c145150304440c0c00003ea003010490301514596191140115001030003a4a000d0090304410720041c11300841038107102540c0f001c3d40c0903a1080b030080c0504e0703885606079035a0303024510480380001e040260350405075020717a200708000741c00f5070340041c603100342c81562910355072011000b4800a0b2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 172966726 1250 172965476 172965509
    0x230c0f0c04050105010f030e100e0601030507052b02030c090709060201060906150503100b180315091b0a0f060504180209010905120a05120c0c0406050310150f 70
    0x8024458840c0e12441100d0400c610350408000a049000032039105092555410b00c0b114458000c0149000403000d89109000c448115441240c46000a1200301da11b4883d03c0004905032401c0c04444000b0744603420b03103c280c3c04900510700400303030742c040c016a0540500036030304d00640c0724100c80c0c1c0c1c0b0030b044585a81a4607490054000c3c2110301607481104070514014040c009022000b4400c507103000c2c240b40c1140c032030f180d111904807070010580c0b104103c29000520042d00c3e03001c1100001d000181101a294005c66242c4414100441101c0030100ca40040390060201803a030700ca0040b402101600100c03120752199140386000203113411907000f0840118081041e0b01000d4800b40058961100640c148100280042c1c02c41c41c060107107501c14600d64001a00c1100200401c0698581101c03c44620041c0b4242c882c610f07038080c1e0045107070b6001d60301c2c01c0c0c8850f0400d8040c40b811030398050014180440500c0c0840014002c83c1c0180030440c0e61204006842c80740c3c2c807140006011701040280301070 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 172967976 1250 172966726 172966753
    0xb0102070602030c0706110f01061d0105090603070509070c0503070c0f050a0e160c1b0501030e07120b100317030f1012020d0503041d040b0106030b060a230c 69
    0x4a141d4482000c42d402042101c0d03a031040890460104e0750242040000e030712858900c68101101c42407014405d40c64004000340e01055000050341013a802291180d803662a5010302130003000849282d605503002400030001401c2c0000c40551161451600d103840d40016580c55046503c080310585050343e100320140040c250f4003082c2402000100c07180401c06281840340c0c000c3d004005c1c40330139040540030310500c0240c02011071408031139004d000c1c1c20703071403540002100140109016080c0005e240554190310402c0000320102600d9207480c0600709a00a076596144000c4000d100105100d101e00300040020301005100401c45034a40805440346000e58030b025910b0303001006610b503007120700801c0107441d4604a03200401c540640307004900180a0611501e14820f60340203118001d10400048c082d80c9000601071701492240b0b072903421a0341c0e54541241036807410081950311440c2006035050f840e000b9081400218040f16108207058400302e03945da001d8100601c241f0141d0007031085209c00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 172969226 1250 172967976 172967983
    0x9031c0e0a18060b090108130201201e0f0c0d060f0c020f0613020a05131d010c12140c0c0106050a030809011701060909020706060503030304110306010909030c061e0903030b0102 78
    0x80e102251109040c002c5d1070000801842014100d08602412801c030213066906c98200e107072009070a4803680c100e800304500410f64800c0d014828401084409580c880c079801d0104a50003c907588100401c0036500200030050100c589680458203559a84092100d2002d203000d0014804455005040c8a2b40f207401d0480c2041c000030301130203040020040340801030b581d596802c81611001c1d070307100f0030070492950200014021001c5c0c0010075040501100c404440541100d58001d60035600c8110200482481009644a00c181c40110181034000039440c242c1c0000500f40398801c60002195040d0b81b1404143c3c0006140c00940311000001b43c640e1380c65800c5410300000c401c2480a2450a40c5080310080011032a40201400c890f00041ca440c20302502e03401101c00750600400b030300e0781c80c101880c20541d500c41c1034504500034001c030800014500388600c980c0700202d07015219803510428541c3d980000f44002e07145000b44000c40c0e0440000544944108240a44a0b4600045400424001925 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 172970476 1250 172969226 172969229
    0x1090609050f06010f08120f071539030b01231809040c0302090601020102070b0903040e010b0a09120f051005240d020609010c020303070807031409031c0e0a1806 71
    0x43c3c66001d5410840890005207014400c1042c1803808c0d241c0c00e810210517070500c28840060140d880e44001c48420000c0c0da0300c030300c02001c0e0b048400c1c0001001d000702001600c0343c40d24081002605080030f44001406030300440703030800052600f0400305818400502c00511800800003a5603c0032070b20004111390315240c4a40040b049a1002c41e602d072a944243c0780c0122400001d00641300070002c0f90080c1d00075019a5020342d44407240c03800510b1701510040d500e401c94441c040310040e050000080072580b4008440b4107291680d0340e007a0543c181f00c0a44480302030804100d031350449107000c41b00818ed041c0200d0740c03240203080002c101404c0540240c900b00c0e01c0078640c03035440d01c0740002c00c1810f0342ea8843c14210341e96040d11810380300da105500585000c0394040020703402d804002000010010407070010000c0721f20a490b07000e00812440c00f41c1180307001e1148030b45e40552140004081223010620740c0d040b40000c41ca04120708846200100390000e802e03502007907018115076038861108405024150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 172971726 1250 172970476 172970489
    0x60109380d0c090606050f0a120b06071a0a0e150403051207020109050f300706020c03030f130b0c0c160f030b012c1003020418021f051b01090609050f0601 68
    0x908040311030b4640199403103074123004c0f0240b0000d0894a44040b02c1c40e04400100034004200750b03241c00190400758540c11000c00d010340310314901c3c00003412001107407168020590310308004010700e000343d0b0a4903992100141041e0305000d0103000810804583c40075880c440c0b50b156001054800f19440c1c010302c0c2c009402d0650800d50000211441445000d07810640e059849100d00040140c0f11038418005109100c00038145c1d500004030b20554210000007980909410741e9004130940d1202441c040d8607180c4000201180900b0011862014548010308810740712071064070568056401c01441c4107000c0d900c1220450481403080050107516080f0714018000146e400c49000c5094081500780200c0c20701034170030808013502042503e0090540311003c0d50f4054010000f244400100009005098100702c2c460000580316a10140311440d400e00b2440003031721014282909504214801a030300646480369660318640f502c041100c1e03000d4141d205008001519183c94007480712414500d0503008007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 172972976 1250 172971726 172971737
    0x110405070509041a0406031a0901050108100203060402120f01150518040c1112190203180f010c08071a0f01030c050d020402070b0414060109380d0c090606 68
    0x42041c0c11804a03400c800c801c0303070001078414400308001c4040180c110480d41080c0740c07640100c100410241681e044c1c0d01c4d140700c11a07543e518140d0007401d9a80c2400f850106810510240c0c620603520f0f00990340041c002072000d0b081c1a241002c407903401c0011244103c44501f140e0042084148247c00c042d00d81c001450424646025141c5801c00030408481560241d940d82a43c440028031482400c82c00014840503521040410000700000313422400d560349a04000e80d414045850000044501e0343d4401c070312000300c05e0307015802c00a03080c14100c1c182d818003624008080001e000038004001c4a40b01c1c400780305844030310744185c1d0a5580000d000700d6010a240005201199214103100100d0300304450b419100345051000c10301038020910b00511114221060104000b880c1480e215102a00b00456805a176507103440410341d02640c1d06441d240c10342d429a011a0a07013410502010b01c1d020481840c2002d040300842d9041e001c518082d0364440d0507250622a80c1260b00804000340754030f240c007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 172974226 1250 172972976 172972981
    0xc090509010509060301200d0c050405030d1404080111030f060d020307030b0c04180b1005090f0d0203120f03070314010320010c05030c0a050105100803031611030412110405 76
    0xc2030000380103014651241441c840040c81d207035030075000002a60080c402d91041d14059556491740c035000b038854400542e04007449440c8080c4904150780440c2e10041c01003920901c03a850559400c3c0f10b968100c13800540411010400040c2409908080d407404c4008942c0c038505411481c0314502c01030325551203051304508500169600296240590390024204511a01d40b0341840704a42b05641c000079000d00d80e550b0003884c607019070340710b148144001d89045542d0386056404840500c240800103900101000c010071640c20300e1401a19400d00c05812141d0b01c0c0c0c02c014202c07010b0b030041c410181d034100001003040400da03414007a40c2404c1c1c4410039a5035142d415079540454501b00c0c420010251a14250720860680c4100700c01486140c0041c2925a82e046500303d407500c840c443c0809480303660130000032030b00756000c200e1240c0c01c4030205006541561600ac1c018000c4030500c1042d07800b00500d1b20001f0141000a01c000c0c801482000c6884105c031000b842e00050740b40d050071801e0f00c1203203480b08 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 172975476 1250 172974226 172974229
    0x1b0f04050610050c0102041e091a010516060902060f0c100509150a1d0609160f05010806061201090c03050a09020a051002190803070e0d0503070602130806090c01030c0905 75
    0x369024580b81070a04070f4882c074507110302d0b90081c006c6030b20414410203030703003481e10148400c08804000c1d41c005840c00c1c02541c5640340c05046020000b03071801e00103101000301c005120708a03039000110612038400410148030035000944076411615010a61080000f000c40746081c0030491a0200d040d170340347c28030503843c0040b2401d0b241d004060400c40d0030714200c00014000b10a42c0e0003034840c00b010388c00542c4e80501c10f1800030313561036085801610350310480c80c0165106642c42c100b40c003199036140c0188140350070f000044841580160010f604688144008040f611ba03024003103006e40506400004c14000c0c205004043c0c503c080c240d84039407458000c421001d030b1140180b200a8400c15a20410341111110f0201c0c90018444544043d0f10f0128403001d0800000500860048a403a0341c4c2254150070380301041207142601c0360040455004110f040009841900900740d021035824000d08810f9035980d02d903003040c100b00c482c4409500441c090f6462580c0600c50000c1510980c81c02c41c601905040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 172976726 1250 172975476 172975489
    0x10020d0905040f0f05090c0109120503160c0e040807051c0c06050405030d020c060f060906060301090b040902060409020a0201060e01270b040e060f090102120a09141b0f040506 77
    0x10707141c01151900c0f01c90612541640007821000c04203c000c0050b80b40042400f61203c030100c040c6030008041d554001742a040303440100c04a1604a4051890310500c074180d001c0b4041030b060115241010b150001400c011003070501c920444c09241110794840705407521900304a41c4080c080c40000c0116a4005555480305001c00b850754824800601503c5506100c1e00e54014201c1d144805400000c0032130460340c001c10721038001c40341d000803800030351214810072030424005c0303c415410160520040140004a0308140c003218030240c400500004c890700407610310b6001d41c20943c00303280c00142ea692600e50911401c401441e0544c00c055095050a080000160350102404101d100886626000045e6070b8031a0f021658020b001b045030000d40c0300c405880307140c21160410b1309008040010921907040c021104031104150207405c107a034501c0305c40b00082a07502c206075840d002c83c0c2c6110040500400c19a0029418100c0381d00e0a14a65004c01c40403020b82c0b007045000d070341044107000c40342d100c40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 172977976 1250 172976726 172976729
    0xf09030305130e071706030114041e121116030320190606150c0b0406090809030609070920040b071b03030807030c020109030c0b0a1d0c10020d09 64
    0x1071a0241e5110b101c803141c070401ea1080e8001a140c14007030000d00c40e1094202c01c0c5c0990700c0c40080d80d0504142d480030105800c8500c05450070903441030315800a400690320046081c2c01103010303141030329203075955154440811929400440440d002c0341c024440680c040105d850311210880b480c00d40709040d0368000703012100c4900c030840105040303e0318012200c1c050040d1203001c80c0e0100041e0035180103040038009130405100b140c24000c00d40000e00041d40c800d882402d5843e400c440950040d4881d980c5000050005000585501000740032005241e0340911155025200d90002440d140d428a050700d0300302c41d030803881010100c1104a10718a104600025102111500400c1c40c2d15010b0714100403000c441124682003441513600d502004140d0031416481c080c0c1d4440d0360411100070341600507030885005020240c04038107030a4804e80003078200401640c2c0400740035000b081d40004100c4d00558060b03102d80202d0588c1000410b1405070400401850421400d4401002c0c8100c4c00b180103005020f1a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 172979226 1250 172977976 172977983
    0x2403010e0d030e0c0603090c01090e071b0206040e0403090305060921090301060b0406080a0b0915040902130c02070816060f0503130206040e060103060b03070f03020d0b0d05070609060f0903 83
    0x31802d00075240f10003480014503140014084903502e04e0411245500da540031190301e80864143c000101e900b0b1184060f2034810b48050300e13a548021854142c0389901208414201d0b4003080400c0042483d060007c0040e020700d01c01d481d80074040d42103141142c10440020004a01a402401260030f60031901a107c911a000d0401da2507898a0100210703000d80515013007181801c00014000452a5000391120f01c11400e801f800c10003c58043c0c104440c00340143c2c0e900300c804000c01440300315440c0c5a4014070101d48010a4500c00001003490107095464102c103100c0560401001080700c80e40520440030b40c00740c0f03c407100d10364504082000e00040d08014980d4104000440081c0741c00e0b884996541d07041d5001082581c40c4c90b500c0d07005a0381100100d429a001905210b8001144000e110a481c00303803020b6252415031640fd1030089009412090290000e03c0c1c40b1031040507151070340e4080004140c09840508010350074160b0140050441303071700c00c404003c0b000500c404810b0b401002c44c000c2c0c0c0e61 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 172980476 1250 172979226 172979231
    0x18030c1509070f03031701080d05040902090d02121b0613060c0f0c260703050316030311040b09010f0503060108070c03021501060504060f020601050d030309020d0602032403010e0d03 80
    0x10782005080c640340c0a43c0050703007030324400701c004414141c0103035036045c1c242c01c40300c1144040da0f29290030319141d45240d51550040344040c4001e01100c840da402900e02800046c00c501c28800c00c540002d903d8540d11070f054942d9800c52100300b21016501c2a80100310442078801d5031070407112905011110450707104076010001070080780820400c03003c0e0302e103a44030b8002145080040d2103980404680d245400021009440302c080d41900307a1011580303104581c0c101c405581010200150180341003e803050480c2090f41e80d03424030904641d46405000a0218045000c0d00d0b03402040c00501405c03000ea500b4020300500b4010000716a0703010342d19a52104852400b03808421751458182c1c80c101e0744036514034000103000c0012940b2035104015004541030b0741d071030350407540c0c050b00c09076194003003070150360b80060103607a0800200e40a070700069603003880900440400c103881c0e05c0710b004980056a1103440070341941d483c80704000102541c0901103904070000c20001506460041c2d4174155583e01c401810b4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 172981726 1250 172980476 172980481
    0x515040311091305010e16150c06020f04120803060102060609040c03060b0d0210020c0a090e06010506090303130806100929010e04060303111204080d1206050a09020318030c15 77
    0x5116203030140fa031980180203114811070004100c0d00c40c03405400d40c04980307048420025080b80c2d200036038910192651160000200541c6034100030f540500c21500721251304000000d013192103625907882039402501c1c0d09441e400d00500083c10108043d11451080300c490048c0004183d0001d032072400c0380c2e032100300041c103815610007060404c2031400b8003a60190384180e81100103038010540d0303a14440c0c00c490841c9030b0364540714000102d654a20702400c240c3e00c982c0040c0308609240c8014003080c01d004046a050401e0318043d041c85141c2501701c0d60442c0c00600600c8a03440201c011440940000c807010b2280d5208503400241100f988080900c050f040c2007170b0440c1e9640106408044480c003c3c0040c0003458490601030031043d10f4004101e15440f5801413008000031502c00d81e0700b0b840511001d00241c00021500704c42d030110414180c44c02c960348400020301070303481c0b00048000307012412026840785040910903142005807801c11006420030842418119400310791000080308071040c600594 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 172982976 1250 172981726 172981741
    0x30b160516030903080d0518030c3403030f02010516050304060b0a05030618060f070e100212032d070e040228030b0a12020a06030e01020c0a0c051504031109 69
    0x1002d1640085d01d66a400030b88803901d844c454100d01d21540e2102c09600d48000c141842c5035581c46030303104200003500400300c0c0a9038120302030441d5076102040c10082d6a038500080500c0854007507548101c01080030015000c8007550207005032903010b481c00d5a01012110003d80107042444003c100800440c0e9941000941d0354a0700d1114020f410090100c03200d51034890b43c640f4a504061100c0c01480c4140300000310034600541c0120302c109141e680f41180d000802c814440d03560703000d8030104198020303510000a1031350320001a5201d0b1111400c452030002800070140d0b9014000d646e081c1028281604202500342c024144110254040d1070059440c411030354100c50841c01c8691100101c00c020034044921079054201c0d44502100700c910200c490b03950200700385041c980580003504802025010403074079000e9840b00841500d034000242c6007001c0310002504040380d4010482c0c851605c51802e00940c00e029000750002c0b4103185186240c0b0782161505009201c00f00e0314a0704c548610800240300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 172984226 1250 172982976 172982987
    0x30f0c0706090503040612020906040303050912010e0a02091303170a09020d0807030e0d0506061e10080702070807180e01230420010c02010c02010905060c07030b16051603 75
    0x18580c110404001c980100c0c90456105d5025229840009029412684060080e88200c0e030441c94000c0c220761134030b1b00d10755040c2e8650b00a54020b641c00241c0c48860200c9420a000302800d600740400608019002c510402401e154042e040581c031001074045000080d40148212114865580315841c0543d0b807070700b07080042c012100000703404c0610a0030b03c10401c103c0384007601c802440780c2c90392098444a6800d00070118401d200281c40c1d6030201000c2000c9003069802c200312440b090718640c40014400002c50801c9001191503800910785004122070b0780d5042c40b002e4003078106000905a2989803c1050740c0c0c00c2131103039840711110b40d540c41004143d0700135805200228085400603490402141d0b0074200340178100e60036100c00340c0750102c3c4d0b4004070b0011244c0081100585405140c2c0c4000d80045a582e09650b400300d05100002c280481e440e035940d4041c0c0488000e40c3d0007040704030b06600c0d00c06030058001d4681080c421442108050190300a416580401c0030100f20803002d64081c181100d6 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 172985476 1250 172984226 172984237
    0x181c2d02012a14091905030c030c06040b03060a0b0c0a02040f020301080c15120c071110050406120f0e0109150902090103030f02070b0d0209190e0105040207060225050607090b030f0c 80
    0x5121440613600d178546060081401c089400403000d454840003400305050f1035002e414100d6070310200802c03040c0301c040045c00c00703590005170240154006a4895840c2c0392145d01c01c04511205130711174849842107190038018004e54140f0300f0429421940350280c00c5d59500300b4001c0c280d00c50b100c0f0a03c8190800d6504040c3c0b50b02420000141010f4107066140714850780c4402020340e6101e1065031310100c02d040c04203071a5195034050b038038075140508d8a10119004112520a400a1601d40349407540e660480e01030340d02c0c000c052200000d800c0650f440c0107507601c4801608034400e01d00f0403441e840580c0c1c80110460440e9014248000f617100082c0c0100c0c01d0100903004160f10480c00f00360b40155040341e9010b8124401c0c142c1e0116408181255141c00e9000b09204880c0d03088000e00050000c1d051980252482a100d420094105098080d50910390610100c0404e0080b0300c0c4d24688060000400080b50801c0c102d040c1241200d09242e410101c0307100080421b0f44441452000c100c148145030103c40307 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 172986726 1250 172985476 172985479
    0x1d100c020f010c0c0302060a0603050c0906010203070b07030222030503070b0402030f0f030403020a1d040305090f180a0b1507020405040c0308070308040b181c2d02012a1409 76
    0xf01445001070a603041e0804c094005100e80000950b0002141c40b840041d01c0e08800140f41c0d01c00b81e00304200e289603009100f0303411800217200c4400000c0e40c0c900701d2402019035440158550713100d1304890007140c0280e80f00880b0304515403810004030b00b0210449403819040000d5650301d50320707400806c0c03414070b02905941301445070b000c0c1e06030102404005881500e10880e07490707410560f9405074100c42209400131040480c404004140001d000b88000d024401d4080c2040d48003000d800d0019038040c10a0b800c0844807004c4c1c1041003001c24680c400c403c010b0b50101d80410b100585213a000314076010b940c81c000e00079556003000c41d0502c6100038001c402594000402030352003e080c0740042080030152803c40d618596003010904101c4c5000340d45001110290003000c3c600a001d800b40f600c0f0b014000c0c54424031110f42103198192400d02e000d8905224400f284a401c03a440314002421101818110b0300c0c1820102d44420013003269802c0c03048194083d140c502000400d603040054644600d00549 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 172987976 1250 172986726 172986731
    0xf0411030604050c03010c0801030308061021020405040e060108120304110901151d0d0602030a1d0a0c09061d0717070c050c09250203070813091d100c020f01 69
    0x2c100600003c8405255078164001d000d1280390b110103840d098400e010043c0828031200000c1c856040002e64550741c084145041400594501c40403100c000c201600201d03003540004003030000d81840d005030702014005038002d00c003543c5130040681e2aa881800c6030900740c040003001c45c061041c81100801c0b55503009008100700d507510000d0440807031841307100c1008540c10740c0c03240d5800c241c0a181c0008600b0041c0071142141d8041e0340c2d5100075030004000100441d0744280e5903d007465502c05c0f07014031402c0c1d48003e182020060810740501449988010300c05030424a06101d80a8504549014001c0d01c0f6a4440c6a480340d107004c1c2c90201807500c00c00781c071031006410003c809901024080480e401001610408807800d802d100d11508200e40400d40701d81409410085a0540c2d0500041c1c0700340c0d441030b43d040c258142e403000115841004030061440203d41c081c400046948511300c0f0802c00060b0307084241d03489980d5181c0310784400421407a580e0f50f4000c03001c071050090088141082892008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 172989226 1250 172987976 172987981
    0x2715020c1507020f09064209011202090f0616050a0809120f06040b040f0c1d3d1809050c0d030801033e011b03080f04110306 55
    0x3402180c0c1c01c00b0030141d1040c1166984103001e41000881c95005030307070103800d00d5144007404220842c0d08102c030000c0149036980b1900c500031400e10b40c00d01a01d03594141c401940e208a544001050111905c4035410094410002c11f01e01d50380e0784001e003841120039100280c82c3c420381e0013500d2450310742e6075001c0c146001b1100c00204010118004000c0d9000482d0b4481180075016081b60352161500c0080d04135078016808900030444840454ae07000e441103280ca01d14040311f039a06e00300740307003154003940ba103503212042c90700415000e490325680006c041420340502c402103511060310800c5134a08a10342c02021410407940b07494001c0c1c1401920150000500c0d2070010481680103040700e41040e074040c0100d003000081c502d00b000320300e1540c6815603035922084e4250b03100c1400780a4040c4603402406000d2a42000c0b20880d220440c10200482000b000c0c00c19814001420360303071140c03d01c4001c91311554850b20000780c02000da1a084000c00040300d0301550749150004600e503c0700e61156262154604 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 172990476 1250 172989226 172989259
    0x906040e03120a0c0e030703020415051018150e01180503120409050a0203041703100306090f0b060f010c1112030403050601080d081302040b01120204152715020c 71
    0x2e501d406204400410007120503000e1040303071a0341c003049400354187c202000c01c10251406030001002040c0e10385032102c941e55a03c0c002810000c0c00340540b4081842e1140200900d401000305078020070380c94400c1e02c9a0703214007034000d0112040c5900035041c00895051040c003100700c01d00f124003030300c1c0c0501183d05860032582128255007003403140b209400e003480c0c0083c018450b07a0094a0081d5849151141d40310301604000c03440303810081c10784a400e400c440c40040403e10302d0040c0015107014103005281c038082030400d21041c11006144074080c9100440d00300c0141d82c003204541440d41c1055041c16a640c110000549080300010340040743d200c04100402484000f01e8a141201d08400c11150700d206880303801e49922004a592091124000c04131401504182e0006180c1d018145403500707032001504905000c0342c000742c02c42d40d000001010665400e0f9002032004405104048054010f15a2001500e4000354a4002c0d40008030056141c40011402040b0301402d040300105003079000104400b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 172991726 1250 172990476 172990507
    0xe01031416080703140c060a050a0e0d08040302031014180715020715020601080307030530060111030f031f0f03051c050a23090406141503150906040e03 67
    0x1550b85c0c0030b0181002004203000079112a19180140415007000b07010b42040c1ea4a03000b0040c5d0206101c41b158051032159502089204858400c0e2640c0b501c41d400d50050500d451f0702400c0c2c00b00e0040c588105c999441c030440800e07650105004007840ba501141e0010141841c80540c080f45040e10720402d810009500440c44400b51440440704c0d056040d80242c00b280d40300400e00c120081134104102810101c0c0c8620000c0c4000104484070b251008044150540e140e110440c3c6500449207220070b104035503074405010320030912014011810b2a9903080111420310000c0d1500d00c10190a010780324110742000f158070020407403070b8032580a01d5130342d04000780c41d03001c04408120209a4042d010749910702035810348041ea24582e544c40410402c0c1c0905004140c2681062245c04005002450641c0d40c0c90150901925048070040179846c502424000c0280440246a070124000c1c020014680d044280c1c09102035000c4030020070640311000450020824551100300038040018151240c0c038091 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 172992976 1250 172991726 172991729
    0x110f06150f0603041415160309061e090203070f0e1801090206030c220b0a0f0e030d05090301050f010b030a02030c07020d030807020c030f0c0f0301060909150e03040e010314160807 79
    0x18191103103140b80381c2000d851361030100c41d01c11702c0c00013000810307e490f8441d0f0f0110321540d12070070000540c41002c183d034420711401e03980104247d83c0c031005c0600460909020400007400509110328071076003000c10200c0065001400418030742c20000a2842d035107000d4200710805d0740c010300030346d030342c0d0920007007070456644120301400508800c2d2008003c4151a008030800300d4500081480c10092030070005c940300514108003204210f0100d00c102840c0c2e5003030002400300122074540d142d0f0b40c2203840506003954002880846020140c000400807503241d0800c5079884500c50400607075a80d41c0f50545080383c02040f80c080c0d0000003c0360290101038115040c0741c010b1880d50211603d04000b1010155188007094881c402a001000300401c141016041c1e850120002400440c05a455142200498111800030f4a50801c420540303100203419210783d030342c2030001102a520f0542420020103440c001031000520b142010340320549481d6062000803041d801594042c0a440c0c1d940e80c0c40ea565071400e = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 172994226 1250 172992976 172993013
    0x803070c0507050f011b0c0513090605060d0305040303050d061a0315090709381201060302160b0414010f0623030703030807020f0607030507110f06150f060304 70
    0x1c82ca400700701032902000d40e40ca0000c0c1651500300801c0014450054045200c1c02245d2507101c180000c0340964600140d002c0d0710850380c00000d950a140d06041c07080d6040500400c9c040d000c0d0301c03400b00200b940030003100c0540e501030600700d40c4d82180850241c000c100d9070f803000c0441007050342d14000c0c3c0000c1e400118011b41d00c00540b10411003900c0204103414406031000c50100781c00705420021540031440c0780308486000300e8203104060100e9080110b10050501c8803103440340024103c2c0c3c1c0c0000304010765000d462185000c50a1201040714507103800d0940102a10f40c0307038980300090420140c1a514200c03405131800170b011a01c003142c007100252003540100790800d03002e02c80b00001c12604100c2c80200c03220080040c0001403464600340c030203240c042c120404600590910300c8200904101320703070140e40c0e9070b500000c030381c64014801002015039000d0510350381c010520440710400b00055079a00030311074001c0094000404000200c03d03081003040e45411990120810090052048a5500b070088 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 172995476 1250 172994226 172994233
    0x40f0906060305010b090a050f040f02030a0203040317090d05090d12030902040501050103021201031203090503040602150f0108032a0a03030f05060303040803030c1317030c010c02030c030f070503070803070c05 92
    0x88529085d1001d029100c1d200f42c001b0807a40e41041a803824195543e0210000b400016990801c00e040307005076842221541c10182e0004140410160302044800031044506424500341c01c140b4036094451102c0c00d86078042020214070b101c90742c0e90b8a080c0d414215441841e94004004400000e805008004410b034400c501e45030000620394084d0013200c03604480400441a1a82141d40c1c141810300c2c0d181d0b1a404050761401080c2c00503100300014000350400b900206541031400c444020310400003071035030600c2c0c90448010020200000240c41c0320142101032007403003a44204d42146980d01039045032545104030f0041400745509584144604255913400b40400d035254801d0581d2449035224007206e95000304006480c0d030202c84003070030881c04401c0d400c04ae0b980e5200004090403801010b404403a805c009640c0d45e605038248100010000c060002d1400c04504020a64907030245010540101400048240411805008940010354884051a12821700100040007952041821030b031520 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 172996726 1250 172995476 172995479
    0xc041404062d0903031d070902070507050411070507091a010e12012903030405010c030f050f0304081c060509070c0611040906080d110714030307060e01020306010e010305040c0e0903040f090606030501 88
    0x11b400c0326418500c0741300706c0200180c5140c25810002540045070640d01c90044441c081410760701c0d4041c9070785e14151801210340310b10890410724200301d5150b21402000b03180158052410300407040c2e102015609080401c809440f40300800c90f07040031524150354552a00d248181100703201d2050320325400d14100d00c4540c2e040940700341607403071082e401040c1c0458005054100080d10801d40300c6095034041ca4028100740d2030641001c03607030b00305450440716948085105c00301d01103c4c3d0440303120710407a03100500055141c42d02080344103030003a202408000c03002c00da00061001d150000344050b501c10340900d43c0da1f40d0b184c0a5074000d0101b8004c06060703001c3c584115034a2482030420203401d1002501510001d403030211000326040704c07400c185416010602205001c110790b407080819001c007080002d81c7e83d2515600041043c42440c101a042c03600d003100340f0003c904031600c4842950504901d035001c40e00c80a603038900c0d5014650201100c001f04400200e00c007a034541000e401c540c025241800b40b80d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 172997976 1250 172996726 172996751
    0x903041e0e180f01060602030d0b040513061a0d050c0a050307060905010e0111030d0c0e0411041a071b03051605030d0c080405040903090302030c041404062d090303 72
    0x6840c41d21803848159080303004a0700c0c84a0850070201031010303460840c2c4001071000e640c0e500f501c04503071000c4056000803403d101500c50500418401f40800c4800708042d1501411181300503081202c0030700081e03555500c08540040802c2d6021000000420403c03240c140c1d40f806560b00e01819884500808041304001024100050744005661075600e880b80d0791405c10004440c22181440500d040120404091020407028001420a5100000c02050000a0300d070301800ca04001d03a9058051407074480e22070944100031b8181e80540744019618402c1083c02d445460090060364809031204604503d4010551100c0c11b241080707038441d41c19209080c4c012800904050325a102c4d07260142c1244d0111a1013501c03e502c045205840344000b90308181d262004a01195907102048012840c951024015450100500a46054200c8050000d0b524030199403440c9500540010300603a1503502090100400c070314480c60f0214070300e04002d020307100c41030303804050b0000c1903042d00801d25054540016 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 172999226 1250 172997976 172998029
    0x50117060606070b0c040902070b060301051b1e04090e0307050c010806210a060507020a060b0402041a0c0102040509190e150c07031206090903020f03030105011205130b090304 77
    0x52980184480d0034841c3c1d076158101c48000c02010603412000400000c2004011031000d824007500030442d00b68103140c084103041c21109c01400c1110721900d0710006214100400041743d60902c201c1c0540c29050034102501c84003030180c1e1704080c03102420030084400650001026101c0940035408032130503044030070015101d011080e544607030000c0d003c0408946a0755260b024a070b0304e85a201c00c42d1100c0030144c035004200d0768159402c0005800035050b00f82804030740d0003000040c03201101c00314901440c0146602021145041c40c0c1c8103a440464200000042176040d180101030140c0300d00030500e8800340980300d50b0f004204180c501450420803400060b000101c403c0740100310425000141c036040041d03552504000011400c100601800250502550084000401c0c8014002c0740f00e0100e441c01074100403c06208142581c810b000401c031b960782c0706000c040c261078034101c0000c3ca5290f05906000040e040030010b00a061031400340030a01d08000005c108454554529902c10079005121203034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 173000476 1250 172999226 172999231
    0xe0304081c0e18040305120103030f02210301170703060501030303200304020a0b0d0225020109081528090b06040b04021c0507020109050f01020309070b03010b0d0b0a09060905011706 80
    0x1000300c0300b20500c003c000080c500c825000360090030803a051106001030409101026002200060200d6a4590b199071701042540e0001080101218043c04142c41707120307035404140300b0041030451090071071800400601c00c00000e1604001c0501c050360312707810042c000e800c4019201050303005c1d04090441c040c5408090b00d01840d401085c1c92103891a064a00005030052482112116800c100c1c8003030704103001861400300c000300c5001000d04a9140009003900410798030208590f08503200c898a03a04520f4582e80e40090369502006882da900e100901e041c2410804000b4014a07219808003880000e01e0303110702c6850704071000d0015002880600c0207900501c1e1444280a84403445215240199000107a00c200244000602c503511078440a1509802d50224030702650f0000520021010504c210300261101d42c1f8003030f14651400001c0c1c41c5a10a00c00c0000001e5a62440c410b1a6503a501401c0024141100e0501c516034850240d800100300030700c24000100400d002e01301e103242c000b10f401407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 173001726 1250 173000476 173000479
    0x606050304260d0b030f071d0c0409060b0306040c0e0d030302091203041d16050a030905010605090108030c07080c060301150e0d0309080609070f0b09040e0304081c0e 73
    0xd0541c0c44a41da4590750342800d007a4000181040799806022812460283c450f18819038070100b4805251001e0500b88440820a20302540141c5010b21240114031514400500c1700c9110100e903554a4007403c001e80a07542100003040e04cc900002012901c42c4083c50183c141203500300204800d42405940750501041c2e9150130140461320380d000301b800307076015104002d00078005406103007040f50a5401c59200360021070031402440003003600202071450044c2d108070b4806080082821114003c1d2503401900c401e1070805d41c1b100102c0042040030341110f001040054020354440d40c407541940d4a9800c8410030325000c0c8241200000c0303401000a0f00c9040c90741c054980303071540c3d007031132588801c0070302d03202411050041400214205840c0e81340b800c40c03510702998418070002c0c00c1184140c10290058104000780d4041030092040307000d0b292070142102c00c0081819911005840414090820348040b501c00d800081400907450402140802c01c008a000c01c050a0350203907031702602d43c0074918a941c3d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 173002976 1250 173001726 173001737
    0x302060c07030c0f05031b031c02030a140106110d03060506090f1503010306061502210a020c12030309011116030f120e0f1207031e1103030f0f010501030606 69
    0x308804400002822128040d1038400400320035901c50010704c00c0c2100e011142580f000811820960340d042c4424401c15209010b03515020584c0074900f04000381c0c0100162265002010810040c0c45500041c100001842021030660f0751791005400c0b1074500b5a000c005004190301c0d400808c4c860300c0780720151000140309600748502d15040c0b00031024205c03907641e004030b408008511107a00507030196008601c02e00c004507190341070107107084100c002003480d4403e40d40102240001541500c0340540e02a0351000f641740c40701001c20007280ba00e2145a01190413203008481030214150100c02180301e0b0111074024040401005003a8801c0e00c6002036145040c00314126000000c1d100b80c40e240048801d5281070f001d064010104401210358071680e5041a50000f141948200b40500441403a04080d00c041814000ca903107029000100640d0581243c0c80318689241c0701c2c03170003107402988550b071382d5041ba6100d103804400d020410ba401d13500c801c0212684800050150310031301400c0c040e0340340c0781d660 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 173004226 1250 173002976 173002981
    0x30102130b070201050f1b0705010f02150a0b0a03050a0203010c020f0307060e1606030b01230f0d02040e040804140a0312050c010912090504050f062b0204020703030b031504030206 79
    0x500c1c500350441034040b810410100085a840481d25000d030441c12205183c5218074141e03500700e01d19001041c0d004c130341030210525200d541c454000c6802e1040d0b0081300903040082c0e540c8901e6100800160340903d50083c0319000100c140440007400d101c0052095000704810344040800340c4e940d048070100100d80703500400820300043d850b50042000c8900087c201ca0020445058070610042c0d0b035001000041e82d68000c110996901c5a0112a80e000d4410040d8042001703484000841c1b00c0d090003940031841c001651014004d0b5030f4102c41c010a038940303410550381450300c1c101009503c24480c01c200340501c8090801d6600c0c040b603000049039800915401d0550350444180c40c103401002c4540425580ca44a220201c0d05400c011810201c19030707900b08440d030408040104451001c0d10300400220749604104440d140c40400080040c801107801101cac00303540d040b00c0740520500c0c400942080c00803405c1130805400d034203d60600d0700110251860020381000b0540c501104460140050380702002 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 173005476 1250 173004226 173004239
    0x10302060c071212030507230702010e0603040308040c08010e031902010b0a0f091a13051f180608010903020d18030605010f060e0111030405090709082a03010213 71
    0x2000010149010b4a84040d03461030f941c550550448410744400c1501c1d0104081d4a5051107010340c00012030a1000c0014010360000e503a40708900d04070b810b21840051141d040d61f0180217072500e03040005146568034541482d0040c9841c500f99011181a00b410401084030b00041c040d5407540a141d500840c2440002e041a0200c10780c1909454150b542e03501280446449100c1d0480180041041a040b868074040c04d0000b103c0c00380d04000d030344000c2d248a081d001e640e03070031b060b00303000000300d6001c606900d6980c02ea04801c1804010400c0b200d11004000445040d501c4e2800090810000200142540c81030142d0030303280e0b112402001038005004094081e80078042c1b05150801c040320700445a40c4a581c0da0084407420707044003c545601920070032100e584001d2452640c182880c10760404c280c11030503e507690169000c1c96100d4410350300021100c03440340f00004c0c003c04011040f100075254542a05626100d4511448008100c1081c40f1031103042c14000c6038080604800d50b008010719204 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 173006726 1250 173005476 173005489
    0x11a0d0603080d09120903050c0904031803152304060504062007020f01020f0a11150d090312050c0d0207050f0d0809070905010e0f060109030203010f060504061d010302 74
    0x4540106059940324080046403148010703101d0220184000500204a4103094111104000401c41006003015060000500220700e441c80e0800644004000d501c4503d0240d4202100108070420a000f5850001c20301450f0380d510004c60041d110200404241680700c562130030b105480110039440c10802140020b089544a5903006009844c0060200d5844e140345092180d2a61219240c050105e800b806500d02141c220000303135000d000919000181c25112a16010546800740c104000d4000c1c8401c9a1603640c8907811140c0700d902c100d076407400700081c01d4009280c0008241c00045031200c844103800310502c41c5038091021804220300f48400c460040d4040e40c0914001c0342c03180110070a000e041041081104041da01c152208541c2d89400781e24070385854600d5104a140b5400c1c40010000d01045080140d004816500508608c4e41c0c0c2e0001600c00c0c0e10568402501036213841c0340d155405403d544024191401105d0500c43c440d6108120900c1035000074941800304407e80041005184c1035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 173007976 1250 173006726 173006737
    0x14010b09060d14010c0302040e130f12021204030804061101060807090c05040e090604050609060c030402042d021b070311040519050a050f06030d0206040209130803091b09011a 77
    0x20f0301404018051900b0b200e0a598448a035040803076004101400155a80c40203940d006110440880205103280c6620003074545c1f80001504944070342c002d0010300c91090009019030380c2035408655449540b0702e4042c1840d44035105840c0003901e402e0600504990600600b4201d52510009120007400d001040000340b50510a500c203020040100044204412101c07a10520042d0081c2c03000b4540750502c02e0915078001d00e00d04c0c05420030340400c402c0103001000d40e07410940540c0c0001d01c0c1288852148141c1e51800000c1d641a00822140750404019400030050404400d007601008e41d840c44100d90354400d1400002c00203007441c6030091450400b90320a40d804100e10f008c0c101648a18400401216000e441c080d10441c0c541c0c0404c0071518221604582108054000b01441d114411001307442d124080c200a11500c00c3c10007040180e04240c20015039581c0101c442652070034504034050f1354030b0644071040004200d101c0d0304074192914921041c100e410340f20303551a81d1070400c6161207596110 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 173009226 1250 173007976 173007983
    0x503150111061f090501080705040e030703080112171209010612051002031312080402010f110c01030f0b060c0604050d1719020d05010909020a0503030405150f1b060414010b09060d 79
    0x3d200001030030f0301c02070080078000c06c1001c0181000c1424081030109032030354101013805a078001c103c46000280e012010504641942e001400420494504800c081140d0500060402800319000c0c00140802c5042801800844001c200c003550b00c83c2101d8882e01004006422074000c84075110004e140d5800441d80462142c0c0c544e800ea143e07580d2142ca420540440c0b003000607254008010445d45c000d03030b854040070780500781806c070321441441042d60340201d0300e10325040503150402958080080d4101680e1b007540208a6a2900803650102e45d403880101c0c2e05603960300c10020b1030b203501030046600f8922070700004030f45800b569481c50100f514080889940280300c4d42044000034003001d51090a0207803d10400215000c03010703004100c01200740c0d0b00954407980040200b080140da1700c02403241000c0220000b0b540307401e002101c21b205801901602c403000c0850f4039500c2c202131004076030184120300c9889040c02c40100107414a00705e0303400001042e081000a008540f2601d407400302c10038440d10 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 173010476 1250 173009226 173009281
    0xa241505090315040c080c0303070c03060b0a090e010c02010b040c0f2a0b060102010506040b060a180911280c080306040207050f01020301060905030c1507020d0b0106050315011106 79
    0x48000c0501c1150400c640070348004820107011b0100c6d480500c810003451004038000c60a0160684450b00040b00d1840001c10301d540d120446090f03616801d40810040c910441c007081206c8000500a010b00740b5002210015403a20790003414515041c810395400282e00e69072070310204d050503000d995400b403160303404108044140c01828250300f10745074800154460324203c0044c0c03c0907000642520000b8004521850825a4400141d1604c40c241e0760440b41a00d0000014400c900341c01c4005209900820b18150074082400c1c44007800b203004265180c01040103c1d080402141c031000d02003000420361001841541f041004900c000018540100009100614002c00303640da83d46411181f40d040034480c2d4003c001080007581101e1030000a200540c0079051114010340002d640d0701108000d0307a12490702042100c01e5480e01e803041d0140c55840500d5002c9035031140f030090310580040380c04e0b002140801500c0c0200794070a01903194449034460041081d41ca40c0450100704e0481071090554500c0d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 173011726 1250 173010476 173010493
    0x3120218031b191422020c01150602030a020a0611040314010903020d0503090604080307051b01090302240a0203070212070b060f0607030804030806030118110a08010209030d030c050906030a2415050903 88
    0x140d440c4001c142c0d07e4141c00c00090040c04170505641d54411580c820350954109001078146143c000c1042ca1050b54003c02c00201180b4000400c02d5a0042e03400181104a4401104981c44815407064007414080d8003210031100080750200c50910040b510040150021004240000d000a02541d081540350174014240304204030f501940350700804c520b0010746e46551900d414507030180902e0445405901080401d02c200c2c001590b841c60001c0e01400c449070340080000c6a241c8244030404c400750405098655910107402c05001088060307419034420005101c0782c80291900c081240d880e10342c152070f58840c035a901d0301c0507106180f000305003075059500c40d000502218405120071030a03622820414803085000130611040003803940213031000381c0c810090690b580e540020000440c140034500401e4100350a101154140034041507150041e90110178491004440d400c4200d0a40c8400c0e00901881c09441000c00d003462180b040d442402c540c0c07500208240c3c0314000500c0080301c06001c6510300c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 173012976 1250 173011726 173011789
    0xf03020d02071b0e07020703030c020607050607050a03060902120708060409020301020f07051006270204240e010c020109090f060506041d0a0903120218031b1914 71
    0x3640180b400321842141c43c040425100c1604007490003800100507040502d25084401035a200c555000107401e004900594108556480040700d03c1698003030107460280c20441009800740e0002080480440d080c0346020a501c07a8910075a41192004840700ea481c0d1521340c0300780c54524023b002c1c50b4005468141c03000c050b80f0240000d0020b180030702855076441200d4184181494168203005002e46e0605e40d040089440c1054503061862070125807000c91303e4100104030082c81254407214038019034118802c82103000c408001d0aa07652a1541020341c0000340046480e04450032000340880c25042040c801451554000310040002110001d00e0a44070400130342c0e25000b40e40a86480c00800894050b0001203094054104000702d005104402943d90040c1410440d014140000d590100d1042584034184280c64501032002c0c0c20b072020203103580903221503180d10041d082e000ea02001d809043c00388229592000311111a104011032000704000c205d5507070f40b050202a148140060f060300d1a = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 173014226 1250 173012976 173012981
    0x30702120a1b032c130c02150a06050109052d0109080a0503031f0e1302011209150c11070306020c030702150304020405100521190b0916050a060f03020d 67
    0x40b18000e4540b481c51000c100e501c1100e030364428690340d10104030f000140e1001e880301c0740b045035200c04e02007000c0703454a44c2a07005c80c9807048818450900700e903540d0611070802c100741d100ca801c3d6102070741c47c48005a11902031100542152180d1503a000d4034502241003862540a55000c0c00414901180034541c1c94035058030300903d0001c00e8411750000030501072080d1081c04010f0445a0b03014074800803518096014181d00002064032440c614803914034000c40e03105000b44070500080b030b00d04120b10941ca0911204804244c1c129010244c41c083c0c4940c0700701e004000341101141213200520300c0600303550707a2501030341103025640b07854481445040c0050307443d1420380b6038105442c02599180d1605004101c10b4443c084c00c014207030480b41c0c03010b02c5903880300300d48910012403640200540840c000851440d02815803940300c61141201d4074802004506407015000f8018801115001d0b40f060524081541152090991001c44d0700381c10401e040c002d5440c050107400c0780c1801801d2802018100c1e05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 173015476 1250 173014226 173014277
    0x1030b0d02030a03080c090604030503190309020a090c0c02040509060901050a0513020f2b0c0b03040b0606070203070503010c120f0b0307031709030703140d0311030c09040603080a030606020d05030702120a 90
    0xb050341010400d10300d00e802c1c4004e044de81c80c113245014804200d00e6004101c0d014002d018009120741c403491000c5000d409001c2c41007050b0780c017600401c502e02d001c403c5030b51141000d0b100450694200804250424503501030580201e4100c1d1801040c07040756403c0101c000c04042469420103d86901c58250181c040103114030a24541c0403015140d80070300d00304080b0001c44c1c015001084090051001046003161210f50219040d12180c2c2d80b11200d000207860445a0752002c0d516601f0302c1880400c0950108110550348224001800700c1300080c112441664088007090f60140c0c8041c601b000802c01c40700c000c80c100002c40080c180381c5000680464104009130b04240c41e465000308903010b03142c500304803103204410f00f45010054250848040d0b002232102614107000d40101050901c129640d540c0201d0041d03501248441c0e9440c1c000e52b001c1c010340580e1144401501640e849584281c0c00b40d0203c0b80300b032160744d015140386d030a046110820b03034118080705410060061810004800076401c0400d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 173016726 1250 173015476 173015483
    0x20c0607111f0e0703060506010906090b0a080405030c0a060b0406090207020f0d081204111318110411040e0f06150702040518031314030a03020c0d17031501030b0d02030a03080c09060403 82
    0x9203848e100f07002405e6445036911070010004482020030030000704000f901d02487c960324040b0032646a030b04010303180d40150f4a01006074081c0c4541402080800c0d4803c04190405403411312a050741c601d0a14200d015001700650400b83c91f001071000380c600445034101c83c6100b04900342c10b10156843e00d00c03030a20100d400300c9920f402096401c066180c448440341c0101c0100303070103015603201c1c484500c0049890306001000c4c90044410380c15166995085001c5100b4600780301a192542c40003070480350b01c415240317041f0440b010408128142411a0320f0383d6200c40f809070051070038100e03909002c014100101140c00a104615060503480010300051441e40040503540c4542400e02d9401d1003860854406140719510800520380026000b2412010070340e000c403100114908142811201241224448140c2850000c1000300035508845140e5a04038280e900308069010030050080303041c201400a5810343c440126100041d1003600c42d56440080543d0180c11714001c403000c54659002504100c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 173017976 1250 173016726 173016731
    0x80904061d07031103090c01080603030c0f07050a05060403051207060213090c02070e1003030507060605190e010911041205210408061609062709020c0607111f0e070306 74
    0x44240b0754140111101c030070003403040f18070354144416200e41d11001501650306108402e00050704595050041c1c0d440c4c2480c040603249401c6041c04c030031b0b450300c04078011544075010380440410642001d00c00d0301d0913240d0000081c17041c0000708030240036580050000f2100107070208010a00c16000080010040c070001c040450005258180a800c1c122a0381040108141407c1007020ba40019040102280d405041c003995801c2c2c079040000c09840c07550130487d00304040072901103c0701415805e80046444801e600c0030103076202c0b11400181c0782d0301040c0003d4010284403e20046400309000101b461084003125103030081c0c0880c00d1481c10f140310005a0200001c201041001818406203070b026410400d0600390301104180a04030f00000e02400c001c0004005909009500404145e0556202d5100812046540e8503101d03029600102082c0301e10700901c0c1c003180f03000d03009079911a02e214541001e041d8001c161820817803103d41b05072840003602c3d00c802140c0710450043c0a040003450007000d01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 173019226 1250 173017976 173017981
    0x3040507151d0f130e03040f030f02090a1104050f01050c1501090c05030c1b191203110702131e060b04300f02061c050108101107080904061d 62
    0x2800b0034620300144042c060440e585000806a0750100d280c078200c000725a00117041d2003402c840d54034600694120f0310390244114000310038007000c0166900d2883c4220f580198a5640e045a001076851282d00d1001d03c180521040c0014901096107014100040c504541005d00100c6103511304403200c0c15022800307141800502c09090b03d802a40c0e00040780e424540d10307506005543c0c850074420801e07910799050b000c519000f5802014003921040100d250800f0030001c01500b0440360f0b088081c41c2660101e0b00c2c2901e280d19000512040d1625503030018140441c240081581c1009403465202d00380340412002140c0e0100383c2c0d688181005060180c2e2241c0d00c45003404003040552031407404101a0384545010440000c5031803282a0070560700c00c400d000d1514040c800309007103002d905800c03e0410640704818031b410a1a038045412503102c0c404941902c424101030301c00701c4180f0451503403240c0c820405140401c41441c010500004003820004040d591507040241300040c034102c1d190303006100e406 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 173020476 1250 173019226 173019257
    0x1315050103050705012f03070b0103030206240904020d03030605060406031401050402070b1918050d090e06030312061201020a050a030b09011d1503070906081608070b0304050715 78
    0x24030060326003801c0c1854885490f411008811b841c62841040350300000d4004032241320300f80b042e81c00856100300304040f9941c40c1d1a0103901c82c5421600100814007110340546200c691030315403101d060020300303c00c0d05034407903070284880380c2a210001d50500d5250380d00003031141c072503000410041c4410782d40002d810002203083e4406d42010390007503120300c1c0184042c00100e5904502c0c903400c10010400700910310b9001001d08082e2030462030000e00c1e07034080305004c1c05011010078405107102c216074030b01180c50313152000e21208a40c02d4842031742651050001c60002c2c51215600c540001004007507a510716120b1400c142680e0103180c0c880c0c001040840e51408964242c06403244c2044100c2da40c40c0c40e036044c20380d100f0416040601001d07295603400e01142b0406620202481141000b405490345076071501e6440c0090702c0315114840b01485140181c3c40d00c000d40f07031940d400b51a40030010308842031400000f85d0158101410946650184032000110720940140000400240d501c410a020500c030740d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 173021582 1106 173020476 173020483
    0x309060c010f090602041502060103050c0d06151517130303020f120411030f010b0a090e10021206130c09090515030f06011e0f030308131505010305 65
    0xc400b90f0610905400070415140f05030b140b400940504001242c2c0d03150248401b9140c0d4202c0480d252452030a020300c0301030b640c001c420114003150710f000c200b11410b40c158800c1c4c0c0b031001c804443c800e280c0d82001006e104911080c0300c01d0728a14100c1c09461790498603000007800c1503070014800d1324034006401650040740385003000c01c1d1180b406241411801e0210303d0480d10910840d542034465080c14010742144d400c000d0400c841c018600030b1030720013802000b0721148560103100320000c100741a91028100300f144c06c100c03005280c2403003030a100312600c060014001c020305000c802c403a051f40016036602101c03c0d0403000200d0b65140035800525598412070180e00d4003a1041180d2010f100003001d906990b0b282001d50040c0303c07050940c042d0451544a1140001340c001001c04c0401d01404a0070362000c41c80514000c0f6020641d90b840010bc0f094100b4001c81d55100014000d021041 = true := by decide +kernel

theorem cover : BRFrame.Cov 172841726 173021582 := by
  have h0 := BRFrame.cov_init 172841726
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 172841726 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 172841726 ≤ n) (h2 : n < 173021582) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
