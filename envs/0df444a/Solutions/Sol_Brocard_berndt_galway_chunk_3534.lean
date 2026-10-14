-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3534
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:56:20.128557+00:00
-- url     : https://prove2.me/submissions/8b995cad-f63d-4ccd-a276-93f706e8406e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 635431654 ≤ n < 635611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 635432904 1250 635431654 635431663
    0x30201030510050a05090c0904021204140a03080106050f070c0906050306150a060c0302010207022d010305151c0b0109050a0e0303090604080d0207020d14121c0209010903051608 78
    0xb0906a02d6118092515000a040e1039a50180c58000e9104801081c1e441414200751596100018815901c03410845c1042510300b208643c207403680110320113107902c07010020032030b9086070707406641d501d406a00381003080e01c1d1750780000c07001c0818100802100d400315191450300c4002c3d00d00d0417000b2440a1810301054035100001e0b007045a585446030001010355202e00b40c110031600e880c1800c404c11310b03850809900900840402a4110103082d03c17218a40005411921142c1114100c000086003401d00440840303201b1121706086442d940301c4000146080c8040b0480302e00c1e0070b0047c6075810519030b504004200b080e44014503098a80081c010300359410b01518012600c640700035801c40c0b400c000e54651b2183c0140028000200c001154106400140c0495041d1600501015810981843d058820208a60907000781c1d001e000c58400c50104d80004440b00a165070030703d01c000c0d01d00f007040c0070000e5000f41c0c0f01d103061020040000000034802d12070030b05003407056545000344074130f842c1005040 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 635434154 1250 635432904 635432911
    0x1308120301030b09060c07150605061206010f0215010909081e03090607050703051608090402070c0302030607090302031b01032c07080102130b09030109082b1107151509060302010305 80
    0x55422110030000110043c4080d035040540008c030f64500e100c400052840180342c650802031300b0100010740001481568200b00c1c0c0a40f00a90b91405107040d01c0404a0303c2d040343c4180038523101d01103c0108030442981d084001e5082c0182c02185c41c0203140f410412903c2c0c6e0186c40d161110720044200400c00606101107035001500d401d043d8600300c95507600804500c00c0c40308128101071140d02003801c0c041c14038183d901110014108540d00c1c101d60070001400c070f039144400c0f446480b4180020740c055118444031021030b58017a0042c01e00003140342802d129440615840d904050703540d8803070380341314810a09103849090351000004ea28854150750b54201505900103014507801082184c08100500c000d01045440da100241c1d00ca44802000038058599400c01a200ea100861480d055603024a40080c0240e41800c00039000603081c80351030142c600100c1055944e00092001e5404580c030751804020031020305200096080000a00010b200c0b030941104d01c02c540e541006104658240c81481d40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 635435404 1250 635434154 635434171
    0x9030c050d0210030510080304060507020a091a1c060c09031a040503040506090d0503070803010620120306040e0a14070621110f220e0f0c1308120301030b 68
    0x22a601c068010911082240c11210101640d860000c2c00343d0300c50540c15030140800a00356940d403980d0703030001480c5810800701a4800c4031b058800180030340c0315201d030116603951140c4100b244c80d4030404010a001e00b008408030003080005001d40000c20034407a621010b040b0b5201c0406281c20360610206482c1d032010401c038051007002c244000b040e40002030302c00301d0b1001c030b90159940303001c1c0010a01f10480d61a000f0413a100100c3c1c00001c02c0010b1000d94103030b41d400e070307251180505034401d40145800d8919044040d5084000702c0810303205d8040003540d001e10042d001180c50002c413641325207007200e05241a9513000c82031048000300740007440148000e042a290006100c0d03041c10300c0050b10038001003c0034120380c1d9001c01490406606054640898900c04d1454680491900d400380310240d001107c143c0c4000701e4030210b035120380800da0a0054803a1241c1d0310455075042110b0500d40c2c000702080300079080d02600051129402c00c1036010448071225050344951540c5440f188000000c0e08010 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 635436654 1250 635435404 635435419
    0x6020a0201120c14030c190c15020703050c15040501051e1603110417010f0c0804020922080c060709030302032b052502010b0a09020903070e0709030c05 67
    0x2026070b901402c2c40e0036400c0310341c000141c000b81000c0107480c10305101000402d030705004010000e061600e20007801c064405030502442c10b08500204880c0b101208100070b00f01c400c200840d1710312061a5001c1c0070828464148149041d500c4600d0318a020903810362400e84030246002c0104004080c05641e42003814255603202581791030303076070120840008004181c20901c51114245440c8a0781025403004800c3e07108031f560356140d411606441201c1102e4803115030a00601c109012903c1c4900360162207203588aa40c16241c5508110301244080e05204140c3d4554010300708014840715520303491071103004003a0383e4070031085080c2c1c2803d03401407402c0280100c2d00d4013000402d0f0084110380b83c2808041e02109c00100b030b05118100403103103414080102c0d10300741c20002a003911031a80c0300d10b01100e14507103180c00040d0f6001c90903120110780c0550030a01181b0100b0015805401404a0440c018190740340903440c2d1404103040360048408600161a0307031801c00511100d05040d01c00f40000340d5050 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 635437904 1250 635436654 635436673
    0x4180605122a030d050f13150f14030606030403030b040f06030303150509071209061b030f111909050402120f01120203030318160b0a09062a0201020a0b0915010602 72
    0x3d451310780c00141181413180005205507203d2410046803200e0444010030a00f09480d00d01e8183c414014010301804540c0c0304c0300041d10f131401a82011000070b4901c0c0e10300c1c0b0307503035030f03c000e000a0390030290084041c0740c2c0b0b400303109403956114003410003494460f40f0300103507040c5076040080030346906654050121209002c14070680e202c81c07030042d0b8040800c3c14480404c03c012143ea0740180070a50f0301604031490441b50b6240020028000100d64039075980910031945181c4201040350b004810014808030704111344a11000b082c4910000600c507410a140641d070744401050983c2d1061200003c4400c0c04400c01c00c0c0c02c0000c400050140c01d40411643d405042c1d81d01081d0b60303200292840c1d1580c03c4881a022a02e4010043d10309031f01818150803c00c1541c480d020740854000c0d00004020613022000410954402c50192010740b140c510407481c0325089a0070079544041c0394000b80d04500403015a10003003164180380d2800391610900400c6150403c0710886420401a000101150800d5413030303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 635439154 1250 635437904 635437909
    0x6080f1213050603131b0905070f080f0705250203070e010b0f07061b0e0405011502060c0304060212040c05030d091211010207051215100b04180605122a 67
    0xd07070580d801a203941d56030b52102000782280400b0400020040a9012020310782c140805d94400216060550140034a0b202e0040507a086800991305c0400102c2d00d0000491415003c032000d0f400010303a080c640d2521030300c1c000d2001c610788010440f80d40c2034189a6001e0031400c3c05c014000040c103c080032080039506003400031046100c1c0c191040300c1a20040f558030148001d41d40112034480403050b00ba141291000c0000c0c20000d900350b025881a45010000103861118032842840801184c0c0540792035500d44901c2e4a01c0e420203030058817155400c0c02070f081039038490140c0601490003000c000d60240c0c580020180f81819200120702048600c00c010800d900403982d480d04803e50000c0018195008480100e1a0182940c0050352050f07200701110040c0030041030740303491344184012804c0700d5a12003014101d180007d01c41c0b030104d030100700000c000c003621040304981d044450800100d01e1550f6580003860071440c190240049821905000f990740f8400102d10680340f0a0b80764240051044000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 635440404 1250 635439154 635439187
    0x611071b062d020309132306180c16030503011503020a0e10110102030c04031703060d20030a0b01180c0f03090201140d3602010e0f030106080f12 64
    0x414281100304030241500ba40d00900650741c0109002d02031908802c04038441c0b80c00307862600c9101a44107282c58800300c0d200c0101c000a880303001d0140141100200480081540440003410080f805405000c9551200010094429024041d40d00c0f90784039410300207004400c2ca4014288028148104030b1070101503041850b0000020b01200c8403113410403a0b22042c1c810030229042004203520000070400080d1031000a401a01c1c0034001d9545440d0400d0000d008621050b60010f40c003a400454074000110410b003464012801519841000c80104c00440e00d0401c6260048560116a00040c09030300d2000d00b00c105108541501440114008500034200f500c0b1100038108164494030420305690080c0300c0c0002d0003003a03074030f03081e07072401041022801880c00e800790400100b0f42c40060f45541e202181007080514004458000382d0a075030f070040d20b840c900056800e0f00144009901d4100d541d080c81010001c2078010068a5a14840c042c0c0e20b0400003011845080c4020920038411084030821 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 635441654 1250 635440404 635440457
    0xf0807020601350304060306090e06010b160c0e0f0f0f0a0c14040308070209060d0c090f090501052505040e0a0506010507050a05071a030103050c0d0611071b06 70
    0x66010180d0002030040b9a0000880c520340c003c100014482810080b00100500844806039010014a5201d65001040d00d1300f10001d00700903400180148540d00500f0014644080a0170141c14068a16512043d0281281e8414041151a10200821400c1c0c20038555448401011200643e1034000b902848100e009085081007940d10400c04034018001c0b00c02041170b0303501070000f076119580c0e440c00b070450f5400003504038095401480484e1076410106051000968400110907a4504180ca188010b0016031821002c07962281806808218203101b194080d048082d040720300000070311511400b802e071246018080040c1000100003010601e540f06070010002807000c40d1a40740d200c0100d030b8038002d48402800c0c40c099075507460100034002881200701c0d501d12034a4819080c011307000f1162404248400342c03540c0c121010811031850440c808500440c416000040c1441c420031120080390043c6104662131160500958205841c0c140d08000402c0c152800e03c1d2003000312060743c0c02080104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 635442904 1250 635441654 635441669
    0x90b070b180709061410090503060a090f0206120f09030a1422061107050d0309140a03060e01060810050c0912030c01050a1e0b0102030a0e0114030a0209010f0807020601 74
    0x1800d00e100ca2041031082c0c90050407107003400e2060a0310364030002d50200007500d41c14890104001c031084a203002e000a5000c445004020b17000b5039a420303010a026025100b0226501198402c07000e0040e070381d42020f403541008404a0700700518210003040041c400c081c01c00c03a03036a8824452044013a6000301d80c01e2540441c03a0280713444855072407400400e51128007100440101601012445507440b9a0108001e04560b00715100241e80300c007401030b80842c080340640018042d0380107205505d182c9105000841c000380243d130056540342c580e14220741c2007103130071003490351910003c0101d500c0800c03652494040f821010030540c105207484500320b2183c034000714021803c5280d10305c0c0d000d0060041d2070015600c900207000c540760080540c1c0040c0028a0008400d4500103901441d0034207500c501c00e605030043c0c0055103403080900065614003c2d28107036504008030030000a000c0281000518040d01d64080050703210301440e000940f81c07001c24030701c41003000350302010000c11a43c0006d1440c1101c800c8c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 635444154 1250 635442904 635442931
    0xc08060603191e0e060a06060c030804030e0a1403070504111206060706022a0a03020d0e0f04090b090c06120f070e04020703080103020a1e1502010e150601090b070b 72
    0x7040e08200107003c1c65041030080200b01c64040183d00d0701500001d008510740e0007078030303810307610f40c40780310200c45a0b4040c3c1000940121071400009005507481a0042d00034180309040b1900800020100e80e0301e0b8100d600b0201a5000e408541c1c00c0c100450000340c40120b50600c085503420600003400d02400008407169005000461825200c0004403520582c002c40150340d1500c0070008074800e16482403250381d0044d4481000d4150340c20110305014102e40c150702030500c80700302d00c40c100c60010201000e50340c000980402c0030000d0740c6610800036460f22035400b20301303a40b07840d142e070504000c0740004050040d0800c006d00010b41c0c00c242c100581c00286410005500d450340d1804642c1003030b42d00226904903200013464400d0640001e00760741220700c00c0320b002465030345400b143d200402c003c0310f5001d50603440b52000d12950241d490084070540c0588000a03884c2e048000c640d00d0700b0a01c2d1700c007514816440301441402d50380043c80901400c4088801481c001041d1744154004400400c0442c0382440d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 635445404 1250 635444154 635444191
    0x1030e0a05072309220218040b0c16110109050a0905160903050d230c0c130c050a14090405010e01140a14040c031e06080c040e0a1502041a04050102010c08060603 71
    0x70700c2c03851075035000c2d000f81c01002140100d16207c0c420103c161020f44a6241c100c1c00150042c155030304070391486018411102c00d589682d6030b446076041d201010315050051040010a0b191109005c00c2c004050b40000424036050512540811941344080041007080d00d02c0f05002240000521901031303020743c504010381c0703007500005002950118000049003840001c0302441042c00051852500d44100c0d44110100900d808400446646145c0200825014010340440354014100d4480c00c1091200043c60080c03880d00050490300240c000c40740b5a410400140319005407031040b036208100940c4d140c5956410011410001c445d00440780b440781c2e88505505000a1003a0441c0c200c40b6050381d206142e51100d81c2504001d032500b8019000c691040310182c000750702d003a02038100b00e5125600501140031203a2503030055070340601024100301d0340070400002c901c500da00016402d100320903000f07030f2100d00341000242521a0920000c2c108850001030101d240d5840741201e070401d80944191f0b00401 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 635446654 1250 635445404 635445451
    0x16030515061611040c2001060e010504020a120c030507020607050a0507060203130c08060105150f040303301a1009090c03060302030a0b1f0b030601050901030e0a05072309 75
    0x100f0030032050b03005400c000400d880070360042d20500c50030440400c5400204885036010307080f9035191240c03546401c1e080004108504069000b00300115091400300c0794000145040010349000c0c0d011031340000d0340c640c100b1800175818410a5000345441c80c3c40340c074240300d10f4001030460180f01c101910040c2d0000208083c0d0440000c1080002c4d408a00b20700080d079601c540700e403070b1a000d01c202405a80b4116146599194180458125180300701d055400c00f82103443c12610740c05082c03070401800d4200c0c0c0c10034089004131000145000c101c0c28001c10300300e00c0703440c400c0d60740b407500b00e0214082c0300b50b42c032072890792a0003000200682e40e40c44000100d00c0e903808405c40c003422480c0e1000e901801160a0b070010f103e910540103220700b030700309000c488500c2c0071822440c1c1c40c106d5200f00a403404050021850030361140b0001c0284100516004c40c460b54100f200300c1c1452041c100449040d80013410400469074102d03501481c1491080d032038078a081c210004140150402001103081c03850b03140050000e038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 635447904 1250 635446654 635446673
    0x702011214190f06030818040b0a091a0105160620070501060e011406040b03060123031501030c020d050d0e0607020706171e04021503160305150616 65
    0x51100040301081c20415102c92403081c90b07a001c07003102800c120000308010454060b81c01140d0380500b40300d15142c103420344c46680c2103812614940c0b1a403949034140895582c1983c20000c1c0039000b4000131001d940c1013032108020119401541481018440c000e07904c0c00d80d8008100350b81d00240041601c0800c2401801c0700da0408030703c010041d4021030300405102055100e00d060316046074040d82640d1321040780301000070b06600c100e46d002c0000c00c070511400300a0409141c0003001070400d0051012300440d5205800c06c101e000743c080724400f20402ca03107081072098918211801703003020003c174400361a00944600c01d011004045c810001980c0c012006036622400081d5043c00c1074410a041020009445540ea48603100c00203601c409028021446143c40c1c1d8065400c819640c124803030614241c0c44500340082060ba403007000c0c50400132031100e030345000310701c1340b04018074000e24007440b6000507040b0381d0b0182618200502e018454040c03070b26003400b152141080086241c5130340d4128038260002 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 635449154 1250 635447904 635447921
    0x72907050a0503180102060f0402090c0c120d02090906040e0601050f0d02060703030902150c07050d03020f1204090e01050105030a02041104081c03050a1a04020c390603040807020112 80
    0x8600c000240b82450100b01e0b8040141c44c0d109a007070300d1250700c03580c40b210744190f0705945c003940c054100c00114001d240c12000804400d0040410b540b000c101c1c9518076112a0041500d0b0040641c001681241a140051600ea4407480c01c58081001d0321200c0309041c0e450005008280c094030f18103122580704d58803403200c46074850380180382c10743c3e5560b14074004002d0320030860100e000312030310710b00c1e589811600000d40303184441c00704c0200756492070304080019541034441d040c0c082d070181c070f4034042c40c1c902d06216200f022024524000d0b500c80ca4000300340c00712084460465216454800103200590300860180d65254045802140c51161020007001a03c200e6100d00ea4610448003100f6419051103c0b5000c0e410141e01e0811080e9100360b0b4041c20b45201041d443d40700e040308140c0350400c2c51f1981c09426206a10740440d5406078100304d00102c0034402450090701000340c20480e103e90240003180020b42e07442681c801d401c0d410a03a03101040781c02200c0009040c40b141c2e0b5029885550380e940315911 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 635450404 1250 635449154 635449163
    0x9030c150a0209041d0105010b0703080a110c100b01270306020708090a061e05090f012d020105010305010606090302010807080618040b07020d2f010b0907050c072907050a 75
    0x1c0c00c041d00060722144100c6205c01029542071000009031204c4030400d0b1840e1a42586038030b0380c10750722201d0784ca00809991101111900e8140840c0789440820488901c0800d640c01c400102044200c00150401030009014498030071490080c0440b003034041024070407030342d1088015840e0b201c0c915100d4103130301408014a4000024590001d0b0035a07114119030041011019035400c040d00b0b805089460340709106442e42c01902c141c00c0700c180d552040c40c5c001106070b03900103030400b540e16090401c0b2160340c1c1b044502005079110030050081c80803c0c4590030007001c203401c15150b020300c1c0d58006850410000e003030000b031001880008486e0b888200044030000c140350010310062801d8035218071071035030035503105006100750b01001c0c4025001c0c0c0140c040c2104801010244034403003502482d6010030010303180d0050354965502c0303020754541403030f507500540780c41d1229910b681c031940780c0614103031080d800060085030050b1500703085030f039142958440400e842c010690320b880504000f458040311200c000d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 635451654 1250 635450404 635450411
    0x50423030d0206040b070503041146080703050601150306050a06050a031409060a020a1704030237030302070f0c0b04090e031c0b0102161d09030c150a020904 69
    0x7035500d503011541c1441940f042c0c040e9812500c0e50a0212080c1c001120700400105031031105c04010b03c1c1c45192485e01407a04149408880d040c0d0425800c90000144100c2e440b040c0301455512018040c1e810300d01900b6440000d0040601c1d545803944e03500410722805103180b000040c202403072440b07030700910003610000c1d0040352504c5e0360705401491940402c00085c00207280c00000d03c0076003050b64003180160f40000007420580c0b01d00c10f07100003c2d4803d21303002d41406580402c1d015a130080d2500c441c07140380a0703005410142c20f441000620106254007409103c80c0d103841110003100544042031815405180040e00d07080c042c40c28800940f020003001c0d06c1521840c40000d1a54440d00082081d0b40b00084180401d240c2d0560156617400b6800c04017002403041e1401c0004d581665001101d554414030444a0401c9641c0d21181c801c00d554100d100f10780b0702d13203503d030350550704100b000d0b500f0006820086151108010007282c13180d0b900a00500132000c1080407500c0500d1940558241d03070700040c41003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 635452904 1250 635451654 635451673
    0x7061a090109090b060907030f11120f090d050a26100501140708090f120a0204290112060504021809090d080c0c120705010506180705042303 62
    0x282902816294144505450400495004440d00030700003d0350303000f07402541c262209810000c4405c03009201d0340c1003690707038100e0702060806409070542403480c602010781e451511002002140c00000c01d1030304d001e10200213000912600241000e030f120000e181680c0c41d91072042084480e4502e540c2e100744007042c688800705000c00000e030030380d0240102c071409076025035590005541c00407802d00c125070070100620281012a05110050406141c0107104044445600000030800c1c0440c031160303003190348940e8001e8210b0a0620440c1107043c0ca14154950301850340703c0c060041e003a111700f420b0402482d07841008044407507821000107000004c00c155110701520031400b1140300e280b0354181c4201c00d8003002c5021004045501c12106200e075440c860590360f010520030b52640720b040c0705503c034070807500403024404000000d800814071840c00401c071418039100b040380b4580d9207800700c550b1000210501c0b1017550043e0898044401125a00030302c40c21248021641100300c0c003030f0b03913054010103042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 635454154 1250 635452904 635452931
    0x120a02150103230d0e0d060b0409050d081b0702010516120203121006050a1d030a0f02090a06060206071b0b0103060e19020d0204110d060b0c0d0e030c150706 69
    0x2841203d1941294241c18603a40c0700031a6079501c0d00903100f0045044288000418203048071114152401181c020444220740e102107000c82e5080700c02569960082da480c2e040080e40704801c203800030f4400200c01043c500344001a0440e01c5440c0c4000d0602c0320014a42d81c103c0c20500300c07500c20a411200f00b0805441c4000080d40781e601c182d5261074040344032030024011060320440c51055031065a54a0b050040b031a00503950782c5a517030204d08005a1104007400c440e941005141c801ca4441d00f4121306807401c030b10511008c0c0f14051f11440149003881030901490346d0000740030764055500d14240074a210f0040310769082d084413030000341c40710030b11070008000d02c001078003c2440c41030b0342411289014000071005c8658030b240600298011141c050410151503c3c0c0c002c8400400f0341e15846280c0701c081c1010310100e5502d035107d00d034a00d00c081880b40161906006070740f07039031000741803640390039004400081d10380078002c82e05c91007541090021142442c41c80c080d17404107a4401010001805035044 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 635455404 1250 635454154 635454173
    0xc060a170907062604081605010f1b0201020a0f0e0f03030304050d020c0a030f0303090614160f050418020f0f07140d0e0916050d0603030309020a0902040503120a02150103 75
    0x900303004129400f0740c08001c00949100f50844d04810a42880d041c0c55590f590030256100031090010112101d1a20002c140288240301c02d8007000b10000440562111025822280c21140d040035648180106004642c002c0a1030a65071094601030514000e0070b0002600011103c00180d050f20001c0204030410200161300700c0074100c0c507000c90340c0010004003007100c50b020a00000744403a90201c8440b002a00075000084a544a44000320301c154030002e10342040d000884424000305001441d040b84545c0000f550f040f609100d15056240c1410079031075031a883c00f031105980038554005004507800048800f503d01190078100110b0795000d03a801c2413014a61810710b51b20090061079401986540204400d00c2c0b04070020f450803105e40d41d43d40a00840ea504014603800b4000300b0406504561280e2080c800550b2203070b100004c28031810300502201d00a683c000003a5140704001c14401c40da40004d040a5180a50807280e694460801d812414002d10740680010b104840002004005100380e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 635456654 1250 635455404 635455409
    0x30f08071101241a0406030e2e2403170c0607110601080c22060f17070510022104030f0b0405010b3c06070b07140c0c060a170907 57
    0x40f101c40d08a4441450103505410300c1500280034100300000c000460007a00a1090303900c840f0140c0c2c21305400e2034030701c1c4541840c0b00c10b004005202808010603441251240348a0900c150054501000626880540c0001a40005000d127203192203100038443e407501c12281e07080e400800340c030454242000044d05030503500c6051121400703a00e00100c0c80010009101002d280000c24140c0c03904111a9150407600c0301c400400f000303545401c008508941a0080c80d4020301c0c0d000c80c09007190001190541c01c1034150341160784a48145802203075015400941200704c0e07156055812041c1d011168600c0c103c0c4610341c00100300003000d10b80c20046c0242440303502d209030b018100900092224004019840703c81508000305002c030106d0449149908581c489000100c809202021404803800280d00e40c02060741180c0204208040004190b48a0f600400000c0301d4100142841d240903900358031080040800ca004040104284d02440e101d910017039220f1541020880881c1003425105131150307a20f0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 635457904 1250 635456654 635456711
    0x60408030d0227010504030809120a08090a06080f0109020a021e07031104020723240709061815090312020604020f0d050601030209060f060315030712030f08071101 72
    0x40f82c1000e01d03800402080000c124169240780ca040c1c1503070340f815500d811165034103401400845070240f641c1406c008890310030b8025101d450722581c0d450200200500032303401140800942109205840e0b00200c2081d064505017000075840c2d105020b0101e151071900d5888903007455044654800c440c501149420a480c050309502d03590101940c2480285d200f030101c0240740e05e406500e104090100a24505001203407030058903010b5080090320401a00e0380817104400c4016002030180c2e041d0411031a5006154a0400981b136081c10700500c00084054410410810b01100c0880d4125100d00b803980007071680101c0612125240040095484d601100e08174015400006c490440346400030400503c940d000004148a1f07007581e0a01031710b40030240406030400d00407040e1242070b507501005144140868a903944044e482107040514000c050341c01300a82c0001d500100002ca544150003d1821040e0f04022425403284041120340801941c5005c19652924850080c0800c002d400340c14003071040d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 635459154 1250 635457904 635457937
    0xd0806101803030833040903260a061401080406020702150406120b041503020f0d1403030f060607020f040e0c1e13020c030a08040c030c06030b031b150702060408030d02 74
    0x960b0b264004122624104003010345c00b04441c1c05251615070001996280320740b03400030300704502c111200d410f0001d03489661013902d651010400280c82c5840b030400100741500464a030000740c28006404a41c02920281120340c0014502c0203540301e40d4a4941e8820424081a94031580c6420007810b0440b00951000035600b0a12402614a8940079159003408451149081e442c615400c0000310a40924990303040780c243d0b400f0780080b60068030b60320050140352010359a01c0c640307141500c0f50f14000900039407044100707210200150b21404103648021000351070006400e420448a24900041c400001e40e000c110625400f25060350702501106200781a81c61000810002e18a04164060204021200c0d4000e21901e207000b8032a810094000d8006c0202014050316034031101d11030745058101901281d290340c04a030641c01d00700007000030311805c035800c1c1c40880ca218001600510713006a43d40700310740c000b1a40c2c105540d2070404131030050a4071360449230f90302c2c0a0307081c130030282d040b0b213102c01d914000c0c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 635460404 1250 635459154 635459191
    0x403060b0918101d1603120201090809060d0b0405070905030c0108010b070314070c03080306090f0907060e030c1206040506060d081c02040e09100e0d08061018030308 73
    0x28002c051400c0c28003408060301880c1c516400c1040188103c10601900c00b201c1251a4100e440900c40c810481c0c40b0b5003403441c4224214102880403550300200503007103a151824003004150b000003901e100880031150141e5402605400501030030781d00c0a2164428502002d02030802e40000d00a82115001d03819038450000c00801521002d03024400d07003061200c10000c0b139000074821200900c803860428685800c060f20394945000141c05034008a90502d00081802450700d010034504d64040f0707190311081060724000d070343c00f41c84592130f01c40e50041c81a850161082580c0a20076508a850701501d5507000c55000424079a8600080d50162014021400881e4050806031000c6041d01c0e006207403030b07141c14403182c0d500f1400c281c0e2404020600307a003800045450500108407501072041c8000038100f0380710301189032040700c0402c44000d200f07034070120410805035000030509134041000c5440922aa8070b120069584040143c2140306400324050003000b00b540100050b8012060802c20320035041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 635461654 1250 635460404 635460421
    0x190618060e09010e0c062506091104110915040911070204050702060f04030e03241015090315150b1b0313121b090b01030f1505190b0403060b09 63
    0x18110954860517422003250441c2505194000300b0312412000c1c92140ca45c0020311030300d00300360035010040302d4180e2605444c000f8450380c0c3c0700d40c501100c8200c1b020440722240701c03240e200c5840b9454909001e2041201c8a0040020301001e48000f070008100a00c285400000740e50070325481040100c3c0300340c1c0b814011a02540c8006181803007000040d0001c07509466039103040e00c9a440e0f5a10565040c410000a11200b00641e8a00c0e0280c000c526101c80041c00e05401001008042e600802c1c61062400c240c035032034517400500d06041700e401c049149440618005a0030143c100f4049081c07414a03009000502058030300c00810808450070305502c200c881c1000e11584a2040e003046c000c0c0260301c80d406100080302e80300c1040b8524803503140c05840096401c02c2c40050740b40d0b035110380c1d0b1055840e9203c550a58060003404507071184041c081101d48442c08003034015a0080c0200c90007820050f42c818003641e404900000503043c0001125150365491400e480901101a1480c1c0038a8211021401c041c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 635462904 1250 635461654 635461661
    0xf0b0301030308060d170703050901020d020a0302060a020c0c03070e0709060c110112150f061403010806270f07060e03010213091e0905030702100f0503190618060e0901 74
    0x280e0b4542d89102c0c0f00d4469500f0040c00340903e4800740d0700c1c0c4041c088041405165000104040ca210740c030f60b20385031030031600060700301400140003405540102d00c20500080d8041050f55010026071070040c2c4a01050304c08031320b04820360703c030380d80c0500c0f441c18040384900f0002806849042280c2e0b60411441d00c8800c119401c405c0e0120040c810040040381c401150301814010712440007086000034900400f20130000c900c0455840601c80d5604402d00380700090340f040ca500340d00750405131560300d5949045c0ba03160740c40c0390042c00c490b0b84c01b0000d01180710002100343d42c0c240c1540590100d4841103e541e45441d240c04041c420340011992407410001076003010300035581c08d20446140318081a25098800d4003404500080d4254140400182024801c480c03007204825401140107584900706031040c4400803080d90900400d101c10340745400c180c0c42c0d2041c00c4030f500c1452882c0700602220900c403e4406480c503038100c0e40ba514028050090410031581c80b45d401c680c0c07030391446d840036103c03000c00d2803c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 635464154 1250 635462904 635462909
    0x11b1a150d200402071e0606080a2a12080414010c081804020c07060c110a0e01120c09050a05070f05040503280606080a1101030c080f1e100f0b0301 65
    0x2440b50810100640ca800700c29600c410300070160016203080c03142e0342c1e91020388030814504240303d6903d52001c2d060000c0d0380705500241512000600c5410703000e8883d000054000a104500c0030710b00340490f812150f241603218020000e0602e81e01001010b46403118164025000c0c0554004001760452220340c841d1072000f810f15013001c9018038002d4101913000000303101c209440e8100c0c5e02000b442c080c0c418200600001041c10343ea404035042028640001c41c5c00601000c20f12558119109001d4882254400360440701c0c10858103040d181c0c0303803400c201170007a84d1303200321001c5290100f0000e030103089410461040038196108000d0f001402002e503054055801007580561105860f0084031500482c00010f04aa074074846610721b81d60354501c070a940e10fa41000b0941d0700024124070401c884c0580221072240242814410110740031001803102c0c200610786500010090003084da045400400384401d0382540c500e00b511450300c40b0306060703a0012071007080c020f0304030502d00040740d4000c40c054906 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 635465404 1250 635464154 635464163
    0x906030c1908010b240a030615030f14060f060c0c0a03110306100807090e010f061203090806060f010806210c130b091305030f04140906041a011b1a150d 67
    0xf0017801001d403400380d90304100200f5085c5540c40e80d000c604080766031052803000d0b82540d008103480c40a08840d80c16250340301e42101c01510082d060000d66610b8680c130031043c10094030003c5d181e64104082d1403a1003100c501254010325029800300501c6081c4042340110359095044440d5500d6564120020507072500c9480000e03080702c10184024241034000ca40610009000803806e00b1040301c0f0b240c1100c0c01a409004015940380c0c80c082055006000d400050007a400600103601d4004c0c0440c10f2503d001c1c44082c10082c031000012103e544150b6644118200f0703803d80200c03042c3c5181e00c995a0303200d07443d44910415450300312868491044c026883d5071400074056400b581c8541500c04030a20182000b16468001071081ca0001c0b90b5201c0504000c00014807400d181006800600c19002c2010340036a003d61305048600408115105440002007070070701c2c041035902002c140b40b001d1401c1408004080040204c1c4803607502d840c49103940c3c0546081f15405100143c200c00300940030380d0041c4000c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 635466654 1250 635465404 635465449
    0x160b0423030a1d0d06020408030c0c03030a1b0c03050d090602060a02160b06061b030403030306120b04032706021501080c0a1a0d020a0309030306140f0906030c1908010b 74
    0x1c2103480b80075401c11200783c0280080038146100d0f0348182c1a03810581006000c1c1d8404505140c104800b007094004200341980903514118441c240206080e90000100c1c0560b03054209580c1049001d01c00340300219040130039110800ca0b1210007d010250922403d070040c410034020a43c014014030880360312000316022601c007c00e0b195260304007140020441f40d0301600030301c00c00060200c0d5000c0c1c1c0f41070300300c140042d640e21415481c0140441c0c51640045091003020a00f40000035803c8900d1a041500340c2002c0b50b0255619071480c0d1203410000c0200404800004001456600040e480c010400c4401e4610803503a2240241036a5000f4090786039801050040c0411015058880031031030500d40700035480c540f54040b144802644c0c440a10703c4006aa0b50300ea94080c954144140ca01800614503003948228840000603103011030301410510501c0280007042c0c05550030008c08642440281000d40001080d01641610b01c00c0c0340b0030001c0c0d075400c0c00b00000c00e0340340090901240e200d1154001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 635467904 1250 635466654 635466677
    0x1c0f060f060c140609060405060a061508060307030c06030f0b0d02090117010929090c0f10020c100c050d030c0215040f0212030307030c0c020f06160b0423030a 70
    0x40b01e140c0c030300b50429100d8007035066540356040b0f0180001445045200c00820b214101854400d2603e078000b00080c0c8828a005020311108a84080c0d0202e240300c14503004146466410020f818007803507031300c020030b065101c0c00c0000b2101d8044d08072105c011405641086071001c5001440221107081800a510481090050001c1502411802c04034510300740005503c0c9110f0399500500541404150354178030465110704108014000c030654007140c243c0140c001400c0c00c0c000700d40c60342000f510f080e21035000b40300c002c01034a00c00c011405600e10003d100d07510540060b00e02401c4480d1580042d95240200740040c0003c03400781c00368102c060440d500600001e041d00f0100180c01c500603004032045003403407000401503503c408850258410714000f540d070b2410054800b40c1251169181c007001d2014003058600036a1362410707620a00c0323105403145540c4420102042c800d40c0e031204401083c0c51507407820302040c807009642c0420b0381106841c03000030301d00959102590324000c0c4401d560000c0d0b10034448 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 635469154 1250 635467904 635467907
    0xd0b1009090b13030c060203010609030210020d020627190c060807120b12061501080a060308040e04031e0306051903150b0111010f0b04060e0c180102121c0f060f06 72
    0x400302c1c3c003914000403130080d50341d90340d0148e9000703034003500000d220725600344151300d4080c1c0b1240300c00e602800184035400d28040c006e9101e500040200c0440c0b03030704a104002c40003c00d211000c480c20b082054408819055081540c0440c0c40c00c002c2d100c083d040e0760045012030290768528010003032622040b02041d41810083c0c0980b80b03165440c0d411902203c80074101500401042d402421400311541c00c061440c0c00048c803e10300140481e100e54100036040010607408822031b820b0340c0042c040101d00f0741e11030606660000040f010741700c14130084150384481941c11746c0040c0940e00c007101c803c0503054a201c2d5000c000300c0d941c080600349801421020b401d0f240282e0024000c40c0c0d042c108000e40140215904c1e00319200d44420150464a42d24001158035044c89514082c106812129000b41001c107882d18403405682400b10350361103c00c10f600c0d6281c0c001c01c08200c0c4101d040d00304075030750001c1071116400a001100c4501c0401d06150618007030030000e01070b50301699581c4510561a0340741550 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 635470404 1250 635469154 635469181
    0x30b030f24240a050406060c1b1a03220f0303140f0c0a030f110702150708030c0d060317041d040321150f0608010b0906180303090d0b1009090b 63
    0x200b41d80c0020715220024254880c3d02441e0000d101548500c0c03590600c40c10716803a180c400b82c0244100c2d01c2d1a001c00e008103130141c03c08050407540c00e0551070316956140414080641030181c01c20a00d4150441c1d030041111600b44074440900c02da9091000700500c0c11100390360a0242c0c0c0b1000104c50389000658051701c071001402100e802c030310300030910f80c021118031400c440325a500c1c0d41640384005a8501941030240f00302d44041a9891050302d841c0d60381d01c994040c0d00004d8a440511071001a240351040c40716003011000d550000c01000c40600401010304141c0d00500c20f04400c0803515a038003a05601107081f451042c0d070551030f175a0b040c040c18140c0080000041c0510001e4541e510701c1a4988040b61070040d028146060300c50b5012030a02d00003030408a0143e0040c402d856040242ea6642d407908800e60752642e16480d40030560082417400281140184203104c4e410030244200e0302d0511405120b040e01400304410402c0340583c5070a409401d40e43c0c40a8040c000808000102e04005100c03032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 635471654 1250 635470404 635470471
    0x510050a021e010608010e030c0c04150810090327061214090d0e1903060b01090803120f070f0203120705040b0f09030601060c02130c030b030f24 64
    0x106803100c100541120502d04a05185001940d80d034801003806070322000d10604840c100740c000154140701d981003c6643c1e0744c3c0030210700380c0140d03220003615000b44000a620005841c0407015a1020618203407500d000300a000001d4001401c0b40344004032047d00061800d07400ca040004c0c1c2c00342ca5044c104150f5002051903901c2a9569a41c4911241c0646401100d03000d2138050020305080600380c000142035487c0b44082038800c074144080041c881d110040c0020840c2e500c002e01140c03e00d03001c40181c400c2c0302c40b0b80c0403a20901002802c0e2181066410456110741c0d01c18000c840103481e0700710b0072504088030a94180c0135038400c0004018081c11005141d51100c0da070318015280548540703c0c008281c11491024864800108500760307545030601c00113000d00201c0c41c200e41d100030160001280d44800e440a40402955428403510342032203500010010703e0301604a480c000c0703070035a40c81d0342c80800300d802c0d106032802d10448150751014080028001c04c08c01c05582c00c050b5003070b16038540042050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 635472904 1250 635471654 635471657
    0x6070f08190e1002030322080d0f0212010803191d06160506070509150304050109020a1e14060901081e010e06040b1815040902120604050f070510050a 66
    0x500000a01c9808100091101a0190b8400107500041c0d0207000c940034010348060309540043c400c00041003010040d80d10700c5401244540f8080219040c80005445844891f0b0350550400a00261280c41600200440d101e40c40c203060140ea43d400d0600c0d12402080ca2710741a103001407030404481c1c3e00c64202e2010b03040020700002e503040023020014a545e8002501c04c084040000a20302c103006045c008503a02041d581041d40c584090280002d14001e203010824004840c080081421f12400f54806c04005901030018040a61500d45150309507400d0b0074966a99a12840c0100b80598801c9107040c1d0040050207041c18000d4000040d112050001c0c01c10081c000c000c0c60446083c5400b10407a4024180540d540301d050800000b404152005a1441800340741c03500d14072002c0c6142da20407613a010a000e40040e6065020400160281c42107800c040d50024030a000000c00400c04203015014500c203008407943c1c01d8011074502d85500191140750352000c500440801018080c00003040c01440d030303 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 635474154 1250 635472904 635472907
    0x9111c060602060a0b030708010e0f15010807060f1e020c0a050301150e0c0f03040303090c0e040203070b0a11070b0909070c24020c1911041103011a040f1e0905010506070f08 76
    0x1c4842c11402c4601c9000400b90a9000c60034140c4014014020b180c3e903025858cc8082003503040c038404039035814151080c0340c00c0124810021014900c00c070784036101080c44e0407450101c40c00401000790380702d4022050501c40d9885180002d00c51405100b0481d0354079404032400d40c018078082401c2c4e14820010528401c4500820043c00f10041c174a004500c80da1198030002030300b0380e007410060481e92150700203022080541080c00301507540002d914003101c15000310309944030710f5540201d07000e601190305002a84909000420b021081c8000360034550825510340c456660307414000c85008084030740140144200207004610b4480c6290404403601e03614001510304000c20313000500d400c0751b100c840d0106803c3c4004120800c0b914082b99403403c40c01b12024000d1003030111008210b4401031281c0310102c4007400014090200301c1017542c0c014200d0904d1a41003542d10384080ba40c090318002c400003c2c002e03090001c6030509091003101d040e01c034068200c03400c0540030380e915605154500c0301600c50910 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 635475404 1250 635474154 635474159
    0xd050115031b0e220c0b1201170303100311030a140109170906120907030b0903030f06040614062b0b0906030d020a081309111c060602060a0b0307 64
    0x4016203440010352150001025080d03010140d400300c099a50486100d0404840503c404c0e1050130b284084010301d1106507803072841d401d1400108030b981a6200d01002c403001b0990180b00d00c81c0c103110302c4c1221040d0888400403031481013481d44030721045490149450385602d046c80443c041145150003043d010303003252100061138031001c2081e034854009810617074540c41c0d80720400090f051f000c805c40155201c100d080403070540c002042d502920400c280000c02002c00602101010000c110042d500711154181d01d0404003426601c9034003c403060b201c4000c05c40c0105495061a229403002c03551005c030400e107003202c940d082199950104011300208001d0300b040008010103524803882018684000040c1003410000744542c2c0080200142d102c2d4110b4491100899008600e0b0020564070840c400d40d500100300080c1515102c580194010501d0141100c1c40414107070002c0050180d81058890405041c28008040e0ba41385d009000c010303003005000c90b60510311a000700d9040b40d00141900d4100b41c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 635476654 1250 635475404 635475431
    0x1a09131202010e12180103062403021b010203090f0304240c05011a10030506150919120c0803130e060a080a0602120f010311060306040b040c02070915080c0d0501 71
    0x88403590302136903c00030380010b213142c003070702000502002805c00f440505d10f8151406413241c00301d903a10170003040d10080785001c00e00c658116100e01e41c00c4100c0c07959114049a200c0d00035001102c0702d1501c0e2144540310513401600006580454a00f903907480780d414140a09408803103d00500042800080c110750b07000124280104c0c1d0036422a059902c0002c50200c00b00445a580b012244092500e0141440750301d071102d61001d81610103c49440344c4d0303860101d010440f039202502071103c01b6850000003284490f1850500d01c09140070300003680c2d15644031240e0039241d20613801c24500441c00c0400411200202a030a00d034803182c010110000c072036440001c03c4c200f0700003000c20bc540b05d0b40000c0460022881601d055000708204010f85100e41c155036640122003594050b10b446480e01000240b01e07540c0c0d1790480103d040010304180118113901c035001e035035810b45010b241030160030481e556503c2c0c0d161200204c1200d902c0301c01454102a00020721841c494400c405807200d540f984220802030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 635477904 1250 635476654 635476663
    0x1b03041b0b030f040501110c1018021513090e06060f0f150d0606050405030615190314010c051306110304360605060d15030203101a09131202010e 64
    0xc051404103044203240900e0f12600310313000c00310131a40075102070208c0200b80320002001245240200d41c0000e0b810100302c3c02d01806100340c2c40003507005103040000c01a41600b0005000c410081c81030621803603848403000020340d20f4000182e425a48044000b8546103040b04501c3c080130f0707000d00718603416a0124040f582e42400c280c00c1011400000030078943d514071510451006081da407030402d05207814880080e8940c2005007c8110f9281100c90007c03496403241e00305c00304800724040a4805550300e2808071145262144100015460803004140003809501280e04483c40070f9070106c50300d070914034165456410a01c400300c1e01e00c418071001c205121400758004446024a00c2c1c401010210940d04040b40d581400d59a59181482002c00031a00d486064070484040c1d82404500da02900d010122040703540d61029501d4410035810001d03101c02a81314448420f0762041d2650401c48103408e01540800c00c3d00c1d5a07407149054000300300402c600300b440e000745211034400811080241c3c41c419180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 635479154 1250 635477904 635477911
    0x605070b0402041b020706090f12140c1009051e151b010204080c09070203040605041a070606062a0f030c151b030507030c0f030c1404030b0f1b03041b0b03 68
    0x542c1c00824180191764121814070010276462200c0c000490034404680c131076a400711030060907540654245480108140b2580030000d00190401804401d440401031000d10355101c0d1a0050264941e10004414031180c8112407240c043c0845c0c1042824100e0075400c0e50200030036a05000c400c51503618520403c3c0010001040c940c0000d20807420048100f2984500103070915043d0340c401c1004122454001c3c0540e0100c0ba013522074400e0500051181c030619200d0360000404192134100c0c0030460642041c0314014840f4000070a8200e049208000300f00500c298101800a244603840c580010703100d40c451000d441e01c2604804114441160785c1e000f960690030004040b204542d60318442c00b985841005d9001c00245824050f0460458010300181c40c4140303100c2c1010f4440c014107841a016003407041d20b05441030702095480303940f4201484100415240e1615041d0705c0c0b0045401008207008480501c1c601440091958480e40d91310000404641c1509121400c07a203000526445814007070342c030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 635480404 1250 635479154 635479157
    0xb130203070906050304050703030e0d06021902010b0f060d050406021204060c030b010c12080406060b0d060305010608030301080d030542042d0b030a1208010f0605070b0402041b 78
    0x3181d0900650141040489030494001c0002c240208004a02c000480504403600760400c1c001440c000404507008204000007d40040c4c0002110400c128030180b500d180d000066008101d10302074a4100f0400c0c0d940c2c00d0b07401d070b442030f0184151070510b40f04d54040d5400912a0b00014985400740140040c81c034400c443c2540d000d956044600603060b014000c00740b03001c4c0c00b481c08150b0380d0100c0d610b00541044100c11075041024040014007005001d50082014040102245480304440042c0801600e180e0004942d25424013000081d518400010380b4144c1c2c00c0c9102910620f007084c14128020000184940400ca40c1c0c0c0c14004031000441c4407020780000812108a194035160f0762881604010703c0421313006d149005081c5a6405100055000c940c59a04c2e9402014001c042200064010703810180e5042c02071090210420403040e0391540300c0001074584031420f81ea90607404020803160b1283c440840d4042200c840000e4619034001d9002d403004100180900f54015581012042d1001031030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 635481654 1250 635480404 635480407
    0x40e010c0801061706060d05090a02040f0b030c15030609040c091109092a0702240702120f0c1315090e011119081e040f110f010f0f030b1302 62
    0x443d0fa540001c0f49403040001c1300c009403840c101320000c1049803090554a00c5d1060b075034004640c41180602180c0744041c0c0048c010700080360109524401425480c1d2480d21030b104840118800e402c201c500d800e09120441a41421a0740d0310041c8003080320014812034010740e07185804103030010544136510301c10f240d100b01c41d9203c52410060041c00c00010740501038400d44880c1072800c090030034030000c1000c2e4020800680354100d03403000c900c41020803190800700442d4590780c242c0071b040f0080580040c5008032540d001180c002d01c941d075105e169060180c11250801d40c200401402c0440c1c100c0c140c0183c419000903102060b44042041340d00540003e00d0b21500ca9400c1072040c0c03000d001c1c1c52084a008080e00d4a400c0d01151542d00062a07031102c90244090707a000112280d4903281180c2e8040190a174461043c6840d01d01110300b800c5c0d800701180c0080c00c9a652030440e0030418942420036070183c40343d0445002048003901d65400c0200d0302030405458085c41d003c640c652045400075003a9040016 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 635482904 1250 635481654 635481659
    0x30601030f0e1b1816030b0901030b01030b06011115060a0f0612050c0f070f0303060e01060203070615050307123c060219020c090c0f04030b06040e010c0801 69
    0x406403214140750348103450800c115002e01441c041495040c6483c034040d2070100610000126044420810108484050682c10805c04d44605004034120003410703a41000000b92003010040030754000e000250003c2e122000520000d200c007003c7c0d582001050501c0200001640b048602e8006ca8828003081c044420052080e241030103000d0f9030180072a40450042c4509101c1c00500c0c1e031400c1d92400741c02070389032808030307450310008000c41b44880b600d010200ea0360603150421980785820b0f0030b42180043d00d0100002828032a0781c80b0681038a001d80e01651030502140c4030200905402501c0d2000a08005d01c0003a99a43c104030b0800109910f041141c1100501d040c62100d0040d1060303034640940d501909807682d034400350b040d12500540746070001404007440c10488001d025111064100b042c141015002d0305070001404003244008890038147e0390744c3d1100740d4805020703c0c40340c4180c8a0041c4030900010301d007244a141c2c09071000c3c2000650601800c03e15084d201c1d9486514049013480005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 635484154 1250 635482904 635482907
    0x1b0f03090c0a0905072a0605013b06060a110712060f050601021e0a020414090606030a11010c050a0503160308070e061207021e1c021603060c02120f030601 68
    0x1440100f20f0114100900c0c03400702c0c0043c10215640c4c184469a4001c8a03800c0e008032400708a485c1c00d550480707420007896031104810030340380e61a078407282c10b8041415080081d52100444801c17091200320030703075545a1501800e010098019400702e401380506a1000880071408202c114000d121101100d60700001c241424411034a5410341402079034181030400160f41d03000a52078440007403124103810b9441410044500342119080000e50040c02d00301c11140300081064900d00856103002a02d6454032802d08141d6100c6050900501c148a0401039584540c0140c92a1075418016000d85096800680d0742c18216130003081d02c002040702040c0c0079028150b00c11546980f140003800c0403002d05220000081c49401a507000020000300c2500203211a403090018070081d00f100030b904803c2d10041200c15031510b19001d140d41075843c07280b008902c0e151002031050005030480420000c0c26081d516a080038040c107001d08801d600c6000c150301d901070034007401440c000d0300c1c1814842c1c60342000c000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 635485404 1250 635484154 635484169
    0x30a020904140a0e01060e060603060126150405070804030806060f121f08030306061b103602120f0a03080708161e1404080a060609050c031b0f03090c 66
    0x14801c41350789021010f0240e0610311601b1a040783d01219400e48a40d15400100c40300000040f00402c103848810603620300d40c126000c41d034001d1000d41142ca6402c00c0103c2031000300c500482c2c4200c0055100c10100d00400c0c02250380e04c0d04524040d0040d440c02c814101c0603001a40305907003070200d0001e40401c0080c0e00020059007145814080c0820b241c0e2407078074021658034000984010b20400000031b1040c9145241c2050910341c4c10b00506443c89444000c0d0340c00c1c0100308807582004200d4130000080310f8200401c50a041000741c90301100aa00c01d107400b03018950a21543c00c0704507108050300100c50480400490540c0740c400d945049031450030172002804a20050030145121420100c1018200c0d000480e00d403500c825000c43c0d104039122060116001d0401e24000301d0800d100090100301c24030003141407041c02c0c1c084c2c8000d00a07039a581d05441700304c843c00c80e008103803141d0a00214141c0f41d48180202c82030000c0c0b0901c1d0b402e1441c0078654401c01c0d44140c40b07000c0c03d1340c07040068669074107282d01c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 635486654 1250 635485404 635485421
    0xf0c0a08010c140a1b081b16090e010e01150f080c13020702010e1002071a18151e250507151707050306031902060a05030a020904140a 59
    0x10000e02ca500704061000c0d110319440c105101c03214001059540078075105402c11110000b9150364200748031400e0030100d0302030f17000c6991250500360301c00680d40306403000070b030507040100f92524089440d450080f164000b015541000e800741d54a41c0f040320b0b444002401086031500d80e94012500365417034889051644402644184e60940011410307078825540c0d846030b0710b01624040c1002d84e80d2038141c40101c83c1800b2802104c2c0d4001484c445140c07070244c0c0051004292190401c4100201c07800c0c074004242401280201038503140003840810796800c0401449844007181092541416260841025000442180f440500c0d0003c114407042004807002d1003e8001c1c40c0041a1800829458954403000300d40101e82c032100b82001c0001185110f442002883c05000e59203407000e0420140080596100340c43c0325100c2e12403503100031035440c443e409200e005030340100b20501e07080d207010040e6000d4000030210900160709020b400545e880b2401031040160034654440102e150101d2210101d55001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 635487904 1250 635486654 635486669
    0x310330f080c0112201b01050103050c030705150f2b0f050a05070806120c061b0d02030a0f1d1e0102010c09050d020607050a140a0308010905160e060c0f0c0a 69
    0xa0707820403050120038008401100846400350740c6d5100080780d40034484c40031113131142e5610f050000018420701168008001204a003501c103520f41c3c0708100000d8464008081450580400c000d1030a401840c004182c0c1d1070503108100c21402183d2400e60042c0300c1450184c1c4050f403103464400e04003205100d55980914609010002824411402440748500401c060300401e000141120300c070350100008180b15200a10031035442c80380e090a20044006030316500ba080c4502805005038500200648140040e242c0d503c1081c0c0c0101102241c220805819100d1182c203014032500298a5000d000800d01d0105031560a041034882c00090841e1405498901080400035007882682c0d21110244003680c1c0480d0000d4964141c1d040031070810364108001000410b0300000c000380c500300440c3c2254000d01a8444101e11381e0384448c0e14085d175000301e070744040401d110100c801d411401a1340140e0741c91006801c070750800502d20360346440c1c5507943d03c03024850b501401c0030020f40e191031488400548000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 635489154 1250 635487904 635487911
    0x2030c06160507060e0115170d0e0d03030b0a031e0b07031109131424010c020d03030e120f0904060b090901051327020310330f080c0112 60
    0x101c00c8010564052034a00420352074403030420120500c07094012001000041281101040e40da0010078030340c129808103103100303004255021503003038098020903410480182840c40d03c949240d50440040c2051341100b5400454007c011000ca218644055080511b100030b04040b52940d0406029084000340038070100750a21417504143d40620041e20140701c0103840000040303649a20742406003d000d2701078480564018100a4003a031601a0035081d032141403445286642d40c440115551a1500d1010b074206c060140740100091095100488000220f025641c94014030140c158440d803103001e90030041a004124078032680703014841c83c1c0082000503001e40c540220040428900c03032052003a1807150076100f604010000d200d810844d004401040080f007651070001c4070106100f0500700a03170007031046c0c0b10045a101b9062051070502c0842d546110100100001e40344500040051000750195070008002480644240844068809c01c1c0150110b500c141c00010a02203114070301090309400c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 635490404 1250 635489154 635489191
    0x2040f14040b0a0f09270c17010902090c07080705120d060519060e0a090f0204030b130c030809040e010513022706130207050a05060406051803030c181002030c06 71
    0x2c01420100c00c49501100104008002d180c07400100e0f030003008203c0303104104844046c2044001c0704440c2c01d990403001005100341400700500e080b9607000f01c009402c80740b1600800c42269150300648010362145005030324000c03440e500d0724240119070992800c0682d001c201e480841895002c1c0e000640303030130350700049240c500d052a54104521403003000305100401d8070320300543d1260f0002001074840c82005104504a1034030f0a8020762280c4816101103005c40c01041c0c0502104028440040d00700484040c42400c0d40c0782c01e035a941c0035910540e80705a503100300401c48402030150358030031140d204461500662a0041c00309005180c400308030020703031049000015000364004250444400ea60f03841203c040c0315001e10003480303140400b82040c8100c2500b1010450001131051089201d04018480707512161840454400854401419900103000181159035500d0180000c1c000340e42001e00c80c411902c0c0031032008000f003080500103030000140c03085000c40410025810443c0c00850020646 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 635491654 1250 635490404 635490419
    0x70f020409061d0a020d0602030601170f070e011d09070509041517060c0a030c1b06020a09050307050609063411190608070903050d0518040501080c090a02040f14040b0a 74
    0x5003907506c0141200d6000c0081107090340f10f0520f5481c0040b2907e429130311414600e0500c005110101e9001c0001400035140c40880d51103102c0205003000030405103800040e22000304a18100001d0041d03042120034407400f55150303603e0040042e1f618140c050384081d0b5003080300c0b1107603038041c01d0405242a840181800501c4800c08200c50307200751145000280c2c112001021104d00e41e160101030340307012185044030180586640100903011140c0c541c0700c1940d0f0380d08241916000c0c18401e680e800710040c80150f0035424848028002c8c80d0300038000209138010305980d180203c441c12000400c00390721050807002c0040c81000d80003071050850f224081c51211901c86001c0c80c2c50741c02407008001040010805040c0204200b5018513402000da03403800c88640c40003495030300032409013141d040b030341003e100e21740c01c05d031107603d0588040801500140e055030081c0221503c000d424041110783c00c10000444503e91603085028001080e883c041942c850000c10007038412001e84103124240740b40c410000311 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 635492904 1250 635491654 635491669
    0x60f12050103030806220c0e09060f0307180f09030f080a150302130e06091b04060b0f1b010501090519140610170910052a070f020409061d0a02 63
    0x120300b1199256900e0405d074101d22008808918041041d003001f03013680c0031603041104a440d2030750944000200b61b03103481c20004130710304441c01e454254018240c20b2081402c10516502c14410f031007804100f410300302d0f030504100c0300b000348141c00184055a00c1c107403a6034403501240d00549414410b1011010840201c01204201d1200900c01e2910104101d4040f40c19041000e09030003d41c1500c5861030010005070f00c036645400042001071010310204258a00751207500c0988580c0c1203544c0c2040c82e906407244580d402500c42c1702c0121807103041614019801d00640b03001e07083c100000710b0346080c4001c1d0502c40454442e2103115603410009074a95124003144840d2b070144c8200e580640c40c0f20042425290054070604580c00c030380404013007001a6070001602c84900c400110100030b030b5521a40e4000c228404488800240c0340d030405000c0c00743c6941409030a060b409212600340766043c50340010100e54030080210381c8a038889044e510303025041c5104003800b18040020740444641c036400603101 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 635494154 1250 635492904 635492911
    0xf03021501030c09151707050a0b280e0a0609080c0d0f030c02040209030706080603061f06080604020f030115140c0c04090807050a0f0c1508010501110c0307060f120501030308 77
    0x3e940e100c0c5a22003089074207030720b10010a001e2071480105102c2c00160b036101d071f489001e0180200a140b10000b0920b003000201c0e003e44a241c60b07010402c103607000c03036104010b91103000b0340e04004901101d20303001d50f1015940e0005054036203450502d945400d003c1e03411b103440041c90031302c940c2990381611f02084d0b4608105094561610700b40411001620000c0c00038001d80b00b0158042c403c8003c08075045130820103003402840100e0440c2c001e5641c2140b840f56400c0d0402c15404043c204900030810103006102e0035811100c01800581040d20f100045034650b00240e0064070310ba5032030380d011082d4036048440044181d0101c003040b4900109921065507900c035403400c540c0502e64404d843c2003841585015640d040381e100068485851755400c10061841e4804400c0c1e40d80c60b4000c00010300321100036540313590080781da226942d19a1034600159139003903240c0c441240b0b0340224243c240240e9400d00010019111940303030f10360360340c40d140760003000104d0407a0300d0005a440e1500502c046074004a40560 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 635495404 1250 635494154 635494169
    0x20a02061f0b070b1b0d0207061503050a170d020d0603020f040507140a090504020f09180105031005070203071a180c0a0314031c050f07030207230106080a0f03021501030c 75
    0x81c1500d507059640f022015007415a2194880480c0030941d46e840c40c3c0040902038010300c0288400500003942011009152000624582c413400a40380000d440c505020b000c0f43c0d035580007074185500702e8141420b0ba032000c240f101c80d03143d03282e005104500d8044c0b00100307000d4042d0707001c100a192058002d404040018a070654400c00440e01070081c920584074040502070151080d5201c08a04001c04280d03080448031512804031004803c3c0541801e41e2400d0403500014010041c00031f088113084014080a088041180420450080410031001c074020404104024400840c0703030880ca0840d06042d20031403150309401240206c4842c0c1d460041c0072042e207400c4140a240c1c040d442c051a441c501c580241301c001001e0400c00c20032002c0c03681c1e001070f00ca840900043d1181d0f5032007910807030813442500343c0141500200000d00d680742c0d4490503408020b1050340f00000c0c4058a94064506d842148a030403103290b42c2c03003d008010154140141c07195401c10b0303501c0441e1941942d5900051080d04e00a081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 635496654 1250 635495404 635495423
    0x80a0209010914190b040906051e1005040509040309170312040b060d0b0a0207050715080711070f0b07120c0803190209060d090209010605040f21020301020a02061f0b07 74
    0x2203180d40d00c0d103402e1250b00b44c0c0c40d09891059903d0f01039002640143c400d068640389441c0c0c0c001043d04103428a0000c40824106041e1050001000c0061244031007803081304001083c040815252078880e8083d0090f406600c4e00301145181014803452890080c0e5401c00d075410a00c101e01ea000c3c00b8952980c0c01c01e50001c1080c52550741c2e44081642032110100185c1100342e41018400055038a5001b010443e01500944502c0c648035079140054640f540b440030b0000300301302c2c000b510903442000c802d4401911002918806a9503100c0c04a4030740c1650020390305a80b000030b4990812600c0300000f41070500c0d500380314030306400395194001c080c000182100c00b284120300c000035181410750f040f107040309d500070f2005864090031405200140042441240295054000807070b040e802030082c1c1c2d040300c5000d4801000079060842f0b58000175511109e00794607a00e00c840502c010394003030002c0c04c1941e42c50341c002d10135494810b100320b410010051074100c580180100c00c0c410020000f080b5009503400c4030b0f00c032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 635497904 1250 635496654 635496689
    0x415110105060f10120f020a08161806030b040609020f12010915030f030203070b0f07110f030316052a16060c02040203090f0a2a080a020d170d0c080a02090109 70
    0x45c0050245059030755402480061202d009a0300f0030b40450003140225041004802008800d6400d21008407001c40c42c1072009000300400781c42600b001941400150001c03401903078400416045e42c0000406803032203800460398100243e00319142c02c0c01001d4440081c0081826268a80728010440c04080d1910030002491020315000b0000ca445203030f17104c040c04140d450070040d05c003e410820b445000c0060071001940f502c021b07002454100581c4c0134005113103542c41e1503c0112094840c1c01501c0240042071011408102a41800b014184aa031084e20340c079081007207409051058624580e4080b0781a2481406825806089100b06a83c140c80040e40d03a02c994007001c1c500000d0202c688540e110b290000010072000c0e0303010702c440b01d0b80111750042601c1342c410f0554408200d40981101e07035006900f084098a070820561090500404a02c101c4488868501d07040d5409040c03e120001d03212402442c16130313480b1031600c0d4420510501142030016581c0000d101c01320300c0c2724000e4442c4181548 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 635499154 1250 635497904 635497937
    0x50306011b210206060109060f12020318010b102a0807050c01030b041e1d2e09200402090612061206100312050415110105060f10 57
    0x1d05010800320140c207120040c140c60315103900500c41080074444103454502603011800060600c3c003d007416140c0740049420100308550340013109940504112068030b44614200c0148000e601400c3c00e40c603844608156040d080d8252900d00c01150701070441c030006800c1035580801104940c0c41d0030030040c0d44684200c0800c540c006034554015000307107000540e1104204000629198081007170b2010701680c00d030182040f00320382d1441001d440f96585071150f20391154070340d07000c1401d400d550f101840c01d542e1030050841c50140c0060301c0b0440141d0381701001c1828031390503030050841c120b04502402410055a10100701e1000c000c0e030380140c0050603200e0611690340d50181d80c0e0024000c0c00c0e05803103129070000629245416203001d4040e154008103051140d401082080c8500107180c811500300f861550341c10003990b00c000c40c4c08200202840007281c003a4801040f4404c0503031590324114660b1554213060300311800608401c0c8600701e10361201c001500c0d50030500c60900d5050522030018072100c0390 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 635500404 1250 635499154 635499167
    0x100f170408091c0b010515090103020d1d030a08160c02010f020a061a210604080c1f060e24040f0603080c0d080a14041e0b01030303021e04031205030601 67
    0x2c1d015030050700284031441c00504071060300340480c0164a11107243e660f03601800800e070342c403001c0110107071010030400189500075001000340400c10500099045403140803442c051240c00d050500306c1d0000101202150b07072140400e600442d8403017440d0280d541840003e45101d4a541c0c00030306200408005d002514002e02200728460f40101003400304100d40d400d45444d00025110fa41c2c03240103c41e0103c4542c0e4040506040340c580060001d0510b40c0707864a603403406400030328000400d44511f94104400d01d02484808032641e601c50f00102d0340904041203150740170001042ca010b08010301028402036521080c518800060a85e00000c1807640301142c0700150546420241207608001050301b4003410016081082e0161741c2d803980c24645608944100b40d0340540390480c0d511140310045030101d00c06601603490350a00303c01d03444d440c1820b41d40313414049000340c1c025000309130b000c61401804a415480c02d0784c1390030703404061f034a4030b0b081d5924202082c022001e880104007001c800100580d01404 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 635501654 1250 635500404 635500417
    0xe040201170603190213061701110412020d0203190b0f0a1b0302211501020c0307060804060b06070f0303050103030e0f0618041118180103020f0d0213150302100f170408 74
    0xb01031005684408c582e040b041150050014698605200441240440403c2e1030640e02d0b00e5003248420000c94080114510400c64160b9240c040d00b2006407103000314000c41c0210034881c1440d0380c0140303800a00c1c3d5a413108001c16080e1110f0408000020603044c400500d00026850305006031601e0042c005042d0841a4100000464613410280110f14020100b8852004000d07401c8072070034075480040c140c40300e1480c803070f80c0301003050705012500041c0e040e04031845110003c0c001500701585516541d0202003040c80030b901081d51800140300341540019400400358040d02c0c1050403017411400b08289101d42c60460100140c01880c0c0c6101e961030b07401c00c1e0710402900c8580740d1517150302c4c92503075004104228580c0c0b298101007891713a0450810020b01c1e0403a60010402d1080050400034441d60000c10041280d1001c0045480358406410b44100001100000410002282184180010362180032401c00901a8880c21507070980d1b40042d46101d0011b5401c13506100340c44510f0614040d020380c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 635502904 1250 635501654 635501689
    0x114090f0f040c1e091a01090603090503120103151401050d0f11030d120f05010609090b28081014071b0206071a130305030606130e010e0402011706031902 68
    0x2e55102c0d813883c010300c0000140d80b20128100800001c03ea401420300c4030004846000c0785000404006841c000e5002e0340059000b02e003a00d01e01002203d9200301e44000f46c004444120300c581c03002c010002284583ca6560000316000034503541804e001402d00c80d018039008200f00e118503031003001c0101d244c850114a0710080c1c201c1e9500c40500740060000c0c640700c60000c078401e2401c0318800c010b1425010307842c102e660f240c0703c0180c00303402c00c13141801070890382c002c02d03411034030b40418025003400d003080304500d02d40c5103118583c60138102902107090922800c1c0c10000315050515440e100430b00f061013581c114140d4204031110084407040c69102055038500650312142c0881c020090044d1240c0154168540b0030007034816a80710740c00740b82c00f400c180c58007800241c01800044c0b041d00344100280341181c0c500c411400030303a41c1e4214281d00c02c5401d0300043d86800c0010300b84021540c004404040d6490841c0c40036009140030b0001c241d0790301d4040401c503103422500c1c0154003991110001101c03180c5a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 635504154 1250 635502904 635502929
    0x1020705031b0a15021c081302060a02011508100f05040b01050d050f0f01200c0d0f090801060f090b12060a0506131b020f031305040e0f070e0114090f0f040c 69
    0x514002035152182c3c40741b0300c111020a11a0002050702c01e0641301d1003501c0c24240f00001015980a110f000e0300030818100c15596a00800d1440c20100040003005003a000000d20f80d01000e0351000c425600e00c80000640b880c100414040000c3c502015207040d40d03425650329680704e8580c24203914001e850300348011706004815150f0148117041d0801c00e807000080a40c41d1a4854030584105644904525080c0d140c00501c111024507108401402000302d280c580a10f003103803100320703490845504e0b9104010b5442106400c001201e014041c00110b5981101c4440d552081a501a6181c0303070000c10000d41c40d0b40c0c1e00f00091301c0350303550303080e01d202c082601904110050070810003d05403941d10115001500c110200c0c044a5100001251481040e0525049901c0e240c40207000290411074036003441406444c0f408103081d0780c1000804003c00d50b0840c2d070710595140900910b15814108511805003c82c4810840c0008070032140c20b8024159818005e215504c0e4213166002e8481500404640c405 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 635505404 1250 635504154 635504189
    0x6080303060d02030a0215070b0c0901021009031e02060907080c1806060706110318010203130f050705040e16211104091509020f040504020307031707050316050c01020705031b0a 78
    0x980005e82412340c441c4000402544076400040c3c0180140101640140d2280b0100c0192844a80000190501c40d05252030098001800d00b492000d01403129001070b0701000c10000d1103402008a08020042c40016001088a10000c948000914031412100040300000324070305440e000704071014240c11010402001d0032001209041e40c0c000d0341d200142100c501e041000c1d903441032003141d00400000b00c410740650704680c0c843c0050b100c03d441c155210b01400000155030740759401241603800079500903151711041368101d0715100165030451610b01007009481c0c000070f25103111181c0002d801200e641c4440002200040151902e042c0c01000304c584006103408206c0160002c002c5244200e0707228404a0022062108851049501079855480880100003140c2802d400c00090000c0c51803952408055440e500c0c41e55101460809034807806810350702c18803406001d8205d0404091002e00b10740e03490030000950742c8042c20384d01c1054402c1d090000507182d5984403481e00420000003901d41065 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 635506654 1250 635505404 635505439
    0xb0103170f071103061b041701020417011b080106020a0308151e030d03020310060c15020406021b03030c06060402220e0414030307020d030507031d060a0e0106080303060d02030a02 79
    0x2800f090268000d11481c0045001c0b885c014901d40e5002c4040782440b4201441c140090501a40c40c902c0001c00707540c02c1001059034155400940e543e1a807010020452090100c204031180d880c40000c10204281d0900604c00f00303034081201c0c1c0d01d0766010310788442962910981c684402010903205540b05000001d10914000c1d06040c0a1110400b14103076014030001c80000c0e4242e100498141240c11302d44542800b409001d0243c0794003040c050305070710400303c0f403591042c0200d81c00754120360301590020300b000c15845200c0340710306a482e200350051424150003503500c560312800034000380d103c4d80e00862a00040c4045103034000d09180c03030850309404599180c1c41c070b00300794000342c03000c1d903040b00401000240c0c0c00c0c0000849001d0401a802801082c1c0e006030110001d102c0588001304150b103440520302820001d0340380c4403111107100c01612003800e04171501022514015800d00945c0d04001c403c20004801106481d8004020303110500000114800030342000c2d038201000f0740c0301c0a03a074418859107 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 635507904 1250 635506654 635506673
    0x703030c0e09251b020d08130e04060b0f01020c0411130603050906130218060112020c012313080906071202030c010b04020909240418110d0b0103170f07 67
    0x1200038000f0381c1590101c0c5004032200c0200309240d22102e00c00b0045240141002c502660180380124143d81c00c1000030b01d01e1500702c540070b0b4426001c90303c21134140810301030309220b40740f10041d04480a440781d100450011b929010540e5420344256911704800c666401c06038126030f117030400038403401202074849001070020102a5113840582c4610800911002503100e003180b261500140720700c41541c81413001c00c1b00303002d009104604110b8400b1034203c0300c06a500282071403607403c00c0007042e29040707103100d510140c802c0c41d00c010701041c920052140301f4102e040c41d2100d050304000c1c55507681c000399021564501c206c1c900207061200704206003560941c01b0010b07080039512000248121190b110800c4268080c001407154014030384408940007607101110740d620901120300074100740c0d010703400240446200c0b4500c0c4d10884030381c0d047d800800103144543c4141241c200d451654000031600c41038100c4005000003040c6030810000c0d01060000041030b00d8031702e206c0454090707581d40d2a14111a10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 635509154 1250 635507904 635507941
    0x603210905090f0c0a031e1407090b0a0c0f0210090e16091203031e05070905041104030209040807050a0302070608071e031802031005060f0d080703030c0e09 69
    0xc504400201e4a4580701c9401d5000d00301800704407005440c0d4000c0103480c1d0780440c00c0e003801e050342c42e1000045611450804d00080c15480300c00030b0607010710400d503821102c0040c026404c20405120074051074103580240c4d5a10101494400c00201461034030111409030800080c0d4002040da0001a8503a03015560009480700c0003e10141e503110002c408a02c011142c05034000b2070505c0505005c00a00c4010f64181c4038021710f800314111190403d0600546c2c81c2c14407061865031540d0400c80e80746e0b0400e00020042c28240c074100030404120391680c0300c03402a07001c024450075131040800c0501c414001a64060740c2c005080e103205600c2460f000e981e6180701c0c0b06080100701507000050901c1c0c091040c009a1b0940780c007411100500c021b02c1240104601241c0c602020710800f40c034000b50310104074a01c400b00c0341590001c1c440c2410010400701014417032800d40b14145a001c1d0340c000941038030644d441107174103007008200107404d140706803601803142c907000d6040b00d2000c2c1040b402a0301c40d50300110 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 635510404 1250 635509154 635509157
    0x3170c1c0b0a05010f17130b071701050d021c032c0301050606040501080414070f090506120309012c0409060c03050106020c060702061c0615031a0a150201060321 71
    0xd002d59a400151048141700c0725040c0400e0105006140401c401e104030340d40f0501c000c0310381300078031201e40e80d000107620141c444800080b4480007101d1540b84031240c09002d04002c641c80380c114006980010890804414840c40f00840b04aa5400301806103848560030b81c01c072905144410125101c499610812051440c0300398207020210740306040c080120381c1511381c103a4071420103035101c2d240e0820200c0030003400001d511400c00c2c00989801c041c45d1362805040002c20104139030500808004451030101190112508104521000c0c1da070814590b0815090140400001c0c4410f882048203c0c440220300c185c100f41045814410810780e58445445090306440030445647c0701c0001b00e944941d6a00102d402036030030802075016141c102e002d45840c0d442480072195828404060748290b42d610343c05460788603071280f10a04804c0d058040c010340444607240c07100108601200003007482c02c1511901300c120b00040388864242e8400c0d08000040c40d00301c01f01180d105101c04d40300d014006440754850 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 635511654 1250 635510404 635510419
    0xc0f07050402030606040e091501140102060c04060e12190b0106030513111e0301390503040303180f20010302030c070303150816090b01080403170c1c0b 67
    0x140c5103030610982e8010384000d003004c2e0070a4100040400e0683c00074001005502c0740340280300700d4100f0500311a000c1d03c102040413040c0c40406002a281c0301c000b0301800d903810ba00f40000d0200310b51244625182a00c12601d030701101143e01d00d03113803e10166004202c0101031b03040a1406000865030792074101d588555080060380c1d6111910764000341020310040c003c41c60b64101405518210909858249840020701181c01102c0002400c691099054000401d4290107801d16182055034407074803450f118440400c00c0500400c0140b040c0700c028401028195103444036107244000c0401e56400300d03444101c0700b0140103241081f111065010300c1d041c009240d01c0040c40015413083c004e60f8090504425041d041101c1c0380d500390080c0c12103c84801071007860090004401004100040b04084d508074204111b50425031000203a031006c1a440c0d0520038407105010010758498a191020f000780d0700c115056848000c0d600065100302c4030340d407104070505080307224011140d510841e102d007000c65078038 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 635512904 1250 635511654 635511659
    0x305040f14090601082e0603140906070c17030f010504060506040308090607060905030d27020d1506171c020a08030a0c050d1d0606010216170a02060c0f07 68
    0x218544440714060354002c031110020803450350060740002d800c46021025085010b1802c0460203406034851488a040320145800308401501445400244a20100010714514005814503620b40015049200304520140c0031400d1013020300500010007a4900c0940d0749040811003440044801c3c041c0c144280d12701200018146010300032101140e62110103e03080500003001c0000640104c00181e40d800c1e1103035403da00040040c40200003946140d440012215003000c0303104d5498031126883d044c1300644d844d0f0100580c1ea480440d400d080c0d400a20201544030002844000d044964041c0d24844010701041f03c0a07240820000920780901c00410344450f80c101040341d60380102e1001a089040c1040407809419494200c1c2103011154101303035103412a0141c02e001150100f0914615406013081c0003024002c05111280d04a14248014041e030f008007058000581c1043c85010121400001d207510074203400e1112117510fa4004010a48441070f40480c1c680310444501910340c18018070001 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 635514154 1250 635512904 635512919
    0x211e0b070e120d030b030c0402030c18030c090a0b041b020a0203060a1a0d0f051203090d0306230a0503060a0203090d0903120509041805100c08040b13020d0c030305040f 74
    0x885503000301280040c802c0383d881040c1a0010000455000c0d018001e41001460546540c002140030b00400c0d00c10390781e210f50700500c1d182200c4481824511a4100b00d1000b180d5680b00303c01150040c504200000300c041c040000540144011031049841607134014524ac0521380104c1d50400d51402a01556000c0e501d103030708181220b00b041d0035840c80919900007015281880c010030805188619400c00c0f10344120b441d1540b070002006e072240201c000000401641d404248180040550203080601403981403800b002910070b2410f12070000c10b00d00020304007481d5200f6000c003000700b50140a4585a042500310240a503004861040003880781c0c00c0410141c500c9040c109040b241c000d803901c0e140c211115400c803040e9218190040d406915001c11a543c074a141502e040620b2280004240d100c1c15142564251128a88507509008000d4200000310722415030f49540701903c6020740c1c4501941d8400903000e4001c481d0082c20201d40c4000210405402100130000c1d03e850f07040761481c003a500d010b17 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 635515404 1250 635514154 635514169
    0x22d0102150c03040203070e010807090e03160311070b04090903030c080c04090c120c03090c060e010c08090303120702071a03013203010903020102040f0f211e0b070e 73
    0x4500e800c1c451094001441100d40740d028603041840101031b180120341d1041213444800082e0000c3c1070680298400f0060780c1e00c10322500c03441d0b003410406541444841c0c4d06e559102e0345c0c990005000c1c400c40300071800005501384a0350014100c2818256103030741c0c441440f0402021400400c80c0441d191500002c1e016000b2690540328405800b480c6191508012080c4090036035841c0510911890810405161030580a1f0f1100302710960780008960030142000741c9883e180f0341c814014030045c03000e11506643e10a1040182c00d070001001a503c100c2040440d185121b0490444080e10754442444080c075404138209c0b04813840440e074000d10860800e2518001d00c001c4c85403003441c8015444086004466a19550100e21100c0038003040f101584c0c0840d0035554580b0341100140d43c00101480031a22a400b0b00000e000c0403590b00f40700300d0800007165008200c2040d04c213100c1200005841c1001207070f0b1144100f240c001c0b55902007080302480d051504400c01e484c0312020032441c0303610307030007a0600031f8 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 635516654 1250 635515404 635515423
    0x91403091e0409141f0c020309011b08040e04050106080102040b0a1d0a1d370209040f022a07140111060c0301050a090e150c07022d0102 60
    0x1064401d00400300600c058070680c1c00c80d01c0507081900c034065400414800364410002d141c8040c0580150380c5184541c074094040700283d090540c0c41c103c052640c284d8004140c1c0c036038810a0800030a040c43c001107481c44103c1585000b000f0440c0017801041000c880c02034140114880c4000f0b02880d034544540d0381c280e001d0f44c043c1e005041c60904c10010321030303c07900e08081c2d204032419103c419980c007580400c218015030307000b00b004c6011102c50340c601140703005150b070b03440701142c0c416441640500f0301003881d200b0b441d92250000300b0942c0da4074080e96030990442c0c1a05400034801c22941d464090280701035042094110124080e5201403030b08650302a04075148540460007600c40c0c1c40c02d192840d000c044084030b0a0b4108442402d10b103000030420000103001c0c1207034071085904c0391700d840c04004c82410141c01c010039031401d01d00100d00d01e04000a014114400e0040958941d5071001410a400c4c000c101003c1d610900b204180c400c414402c000005483c0d8400050281415070700e8010b90340c90180c0c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 635517904 1250 635516654 635516659
    0x403121808190818040e06071205160c1e23031c020a05070609050601030219080706031d1509060604060506030c030c0c0a0b0601080a0507051206030c100309140309 72
    0x55a000014003d48000c1110309018092041181c0b041c4000c03034101c2d02c0060fa6811030381d100360f0600142d540c0040d400074003807000c410140324a140001c862003036178031480e240005008000c5034403001c0200b448550394070f542200510384040d0589062400034605c4041ea110f110480d140710504c99440d022045a1804802100d12800c9503480c2c3e0100780254060002c4904204040c840c2c40c0c000b828501442500e075000d42c00034000c55041d401000881101c001c00203040201003141004a54000b10707080080b00e07d541400505012110b05003054503100030005c0a140c0203589881c40340081401c0c0c898000c68040c4129030459030b07060240070450314140203285c0e0003181030001468662900009513400b07401140001d080400315211289060880710048581c3c024102c10440d055034082e40e050340c003030340803442030005042003140a0700610403500c803494245007420001c0c000d03441c01c029054420801815603115038007060310080080800751002c86101c44821614080102e0000945079001c000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 635519154 1250 635517904 635517943
    0x70b01140d0f050705040606050405030705010302040e070305060d08120a110901020a15150b0315040c1209110307060e01021b010e060307030e070306020703080f01060917030403121808 81
    0x40d62559050b000d0304500881e0b0724803a103c00803d41d92110301030b810041c4200e49942c2c0c2c4980c2480e041500f4840903400071410035205000030001c1207400740600d60440680d09000403d6296131001c41c081e01041e1001522140000401d62183c40016078a02c0c03192010080c100320445e0390048801280c803441d20380300d0060307021f07421840102c0c412200750109020fa0610005199007800001c000360174895000c4400711102208210501461140c141e00c0c00030202c3d800c00c50000752903405002448401258241d0594071858030040040c003a118010075880201103d04281c0c4e1000300414410b0251400e6005001307800c42e00302408844040f4810a95050311034070f14000848043c081d06400081082040584902c48200031040a000050142d401040c001daa0348d001420f02501c00d03880a44154605030140c1c1c010456150710035944002c1d81c003c959901c40d405c0610440c2032550080350800740140e40d80212091550b0341040a81c074540e100c072000e50400d01da46c0c024854850412999411140300d4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 635520404 1250 635519154 635519179
    0xa142701120911061b0d050901080708040c12030e13020405030714091f090e150705030f040b1801060905040b0c0304030f180308121b041404050907080f03070b0114 72
    0x8181c409030100c9144c80721403178010b43c82400c20b14500354210708080003048002446d0150b9591100c20035030b100b11075086c811f40f241480d82d101d1018102520800b0117455100e20103000b094411300c807540380620002e0030345541c01000c5605000a6000e841094400c0c8501107000030f034000d072115060035240c002031000186a8500908903d1810f00c50300240c642e504640c0f0120708003c4600c07405400c100814010561040c50a0140840e2900904884288501030081240d034a8081c6482c07030b40183e021110241c15104c404041ea1102d007a00384524140d400d00c680880c0440e0694000c038030941c003669040308130f40c49018601800d0321050f80c0140020381c000050160250242c0c52614807020414215490b0640d252070703409035070300301c6991692450588024048208500203070304611240c03500310103107014500141d071486c080d030341840340e4062500d400019403108024880c42d001418600103031440680c640050700e0300e91b48005000c842b00039020b0004039011403808070000c4204e0000d04551407507038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 635521654 1250 635520404 635520409
    0x100906150503130f0203030a0807020106060302030408193b010f09140d06050703050615093601060c05100506090f060d050d0504030c05060703050a142701120911 71
    0x4400c3c001038a1000c5805041c400584003003008000c0030780fa80e80d5024850818880007800d50b007044d07201c1c6040500501c103100101d502801120014082944000500c0190040c2036a10945800880001c610000103007548415504100c6101407140c0007031400303513100030005503200e0403880801320010740511420b0114580781e8559200420006100c0c400c01c4031541d54078010360b138044070706400003a00c4009001084c24840e54002000d9501400ca0741000001000b04044601510f450350384012280040c9218001c0003141c0c404115807034030694107642e114580600001019a0100d5040c440c0c40d18015488204d03106290080e038000705a00c1c0c25860700616080034540c0507007015030200581d000700f4001703a010059a00d00026035200c66468900d1401c003400c040849500540c010001081071900085d0b00000703c4d1009440d0b401c18070040c3c900540641c0d0940228128074624107100c60141449401c0d9960b4161420000daa500c03600c607014108503c196600c000004102d8800710703650750b0291 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 635522904 1250 635521654 635521681
    0x8190f0302010b130902040c0c0b0a18050d02150a0b0306130809210f03071505040f0c03060501030b0a09031205090309150c1606020d0e18100906150503 67
    0x501078400850816082800100022492400700f80c0d2169154448811401c2c240100600c0052900380241d040a05840b0f40003010300061060b8a119074445404c10b00d114000190901650860115009103900b990065038079041940c0c0c000003a1681400103800c003503203001d540034103100a0060041510380d803040071190100c2000840e8a8801030000078001c0c0c1b0f5041c44641a03440071450700e4940d1410702015030424040c91065000b41c6c20402a80000c1603030307d80864816900c060700000e5035960b5003070100c0400e0420138018900c4058502c0082130040c0394000505803400b07200038101c4e80d214001000c9c1100c8110034000d010a4440c400315070360b404d00750b000a5009205034103980c50b0401c0c0702c1c001044000b102c440e414007140081045060f1080811250101c010b00e80c3c0180d40c214146070010355215180820001001045041011280c9031702d076a04011544122401019092500d2013040c034030480d00800201c60300d458000105803010700030300d500c1407100792122451510341c1010840b01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 635524154 1250 635522904 635522933
    0x17150402010306170606120109051c020703020a08010506010f090806190b13021e041a0f04030b15040c020105070c031404050a12110d0201140a0207180f060819 70
    0x14075070760f054001100032440040381103698124016200c0b5162440c00c0200e0454000600342181e03140198500000e00c1c001f41040130700742141204a989031100380104e203840c515410003504050b0010000410b103205411060081c3e500b40c81c0c4c0c101302e0071101c034221903030303503280c0719212141d40a0f40c041b440100000040060120702400d02003042d20100d0f010a440184980000c1d2155900040c50b003070591900c040412480d01d0b203808145400d2502094503840d4400013600c800030700340052401d42c030315071060854000b954804a56042440e016198001d1200391001a600460814000300115441840313424030401d001e40b40e60442c0c81140e1811581545203040c42034150b0340c02c00000c105990740541c2040105442840d01e221080e40c0d02d401c0f040e000c1c540300840d020b6a4a80f1070040180e80081e6141032828108090300e4554100c03180403441e05c0341300d520040c0201d4418411445115042d085442108250501032082ca41e540e100315940d1480601038039645a0103100d800d00154940508099 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 635525404 1250 635524154 635524157
    0x301150c02010c11040f1802090604020f1c020d06030b06032401090b0a030b040b18010203090307030c020f0a0b04171614031609020301210b04080309160902070c1715040201 76
    0x1c1c5110441c90120454a00045604041c4500311200c0e02314500b80c81d0742d940c17200007078406500b80040000e4800c007c2c0903150000c0079110011a4203045100c0070b038140c42c201a0030607420322070340d940c4c0d0801c102e0801040c2c40301d034004d00075150b002404080e00c1e003441c0100300e40000780f02e540f0703803901c11400b004000303543c00b03641d000080e5507000000c83c11806159002c3c0d405040e144005040003c1404d425009445505025900520821a840720084182c50382c01d03030513041c0011400d84920004412003074074859654800325041001c90416085c0c00a001581e01a240040c1c070005219a00ca54400c403500314641c41aa4900003482018004c0c41b400f19810320190444a00d1245402d11211a24071038001c40c1e007040e0b002c0010840340251948045d4110260640d96800702d469031240c11707003d00c0c0108080c04400d00000890171510042101d1321050050032034030b42c10141c503228640065444140c0a1341e40491100c80071941c41caa10300f20114040ca07810081a2a1801c0c0003c1c0083c101c00a106a0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 635526654 1250 635525404 635525411
    0x2030c12030724061d0105040b04060504090302010501091d120705011e02070312061d060a05030d020625020718110703120501140a2304090302030301150c02010c1104 73
    0xf4150006040c8111041e40741400c40201c001191011607460b948070000900702c000c20030700300840c154481d81c195001900c010420700c0d403007004200600320945c48150002c1c03070060b00304141641940305606803040c4030014403040702913100001d90301a14041413019a0000140c50110075420001011503d120b80008907000d540d4043c00d10310480c031440c617022071a40005000702055400101447c1d04000c0d484204141410080c0314880c401c07401c0b040d4a10495800041201070340c40c20741c9100207200080455249160b0880000d48411094400540e00e003041c200c00003451070751701180389a001c682d40c02404581c0c40c3c0701e010203220700d00fa01c0004a81c3e40e02c20350040c114001c040201002da010391230b40818515054041803c941050307115500d56070095803a04550360340c0c622400c003100c1c03002c0b001103e5181c20540303000ea004c554010b8a41e02900e4040c041007015008405075040320440e100040b41c1050300482030301c1c00c180c4941c000b0300107080350b41044001078030f030314801804003000340000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 635527904 1250 635526654 635526667
    0xd0918090f0c24030c0509100c02030607121401050f2107060f02060702010b0f0d14030304030309051603020f042c0624180603120f0310090902030c1203 67
    0x1141d100076190000518182c61080341d003003a4648054030700c8201540e1404001c85e03400000c00410b140503072003c840c81001080c1031240a9440b514200803001e400030103650190404400180481101003940ca80f114240804000b0300701100209a0490b840548240715a580d110204070380d10f10121000c41d00240c84002d242d041000170400140a0680c83d2103101c04c00c4090341000c0c2c6400d800800003030841e810050403080d030303882700340304100380b03c0d0b080c1c404081e48882481e184140c0f0701012003001c1c81d4840801004141a415005084040d00540581d044110082440c0d903081c2c0c40c81c000690010b80b405800e400a003066482005442c00701000b040c002020150012041810b550b01c800c40381c0c3c4000c06100c3c0b110101410440c50a40380c0c034448000c4100040410703148410300b0403c0708102c0080000400644060104107202d11144100580d40c5000800803041a00180c840350f58080d60b620f808100607040780301e00c51010f9001001402c1c2441380c00104160504000b002c142e0318002030040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 635529154 1250 635527904 635527913
    0xd1506091109100503061309230a0c05090c0c060a020304020a0b07080403030e060c0a230d020705270c0711090103150f06150203070209090307200102030714010b030d0918090f 77
    0xb105506489800f004c0002209103896080c0c0c127442c80701c0ca0203190440b4400900180d1f409074a030b000c440050700e8000c4555904199600236000c0c030501c3c041680500c4007009190101a0300a52165100b00d034441f21442d01c92118048600800000401143d000c120900119000340d000c0e142a00000381200d280689008100d401c100020600b160383d2416070307191092040549485442c202a03400007071080c0307050040025903850003031258a0080540180e812601881c4050301c190001035900004407a05000031070400e03d900910042d15000b01ca10580d40e82e034503020810030b0403645c00c1864581c02607800102d80c40184014100781d21000d0ba61400060303450014083c881071001c03950059a01d0b9103090050100c620310003429030015402c2000310100050000003c2e43c416850aa10741c60503082e1040103078654850200040d12035000050943c07008201500030307459036081038050768555100040140d48102d00c0380240301d2a0344843c0701d08121071000380c0c0603501c018041c2c101d20700001c03134a132034 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 635530404 1250 635529154 635529161
    0x8090f1225060614090603031303060213050301060b0301090c0503010f03060c0e03011e050108072403110d0c1106070f0f03091b06020d0518040b0d15060911091005030613 75
    0xc00a8107807000404e01300c1c3c607024a4090380010180d014600e0110701c0c400d0080402c29902008142035800300d15201d50aa62111000140c503014001304842915074a110009400900ca403001c0c85080c83e40300a1803510510540e4100d44400017641c0304641140d03039400c05803601c0340c072400c100075407800c3e8812990340901840032004e00b20102201000d18101400703058442c160010903160b03002503c10480b40107070a000d040c1020071032020031002000500d04801404142c82e030f0500015020502540e00702c41c96000c0700b1501c10030f4440c0301030000ca80c0380142c0c44031400c455000101d10f50308561081c96002c1d01d001c0385050380c1440c0010f8010b459640d541614031042123110141e00138100140000c03030b01003102008506450418030f0906040d03c0f000c4e980c1c6000307151018041c0f41c440b03001852684811000c1140164881802424540d010000c4c030000d20943c880c11080078142014032005840120449459103406000030807031071140d4505880a034000780405421402661082154150521 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 635531654 1250 635530404 635530409
    0x50a0c12032c072c1905010306050a0506011d090a020904020c15010b031b090a051e0102010c0f080412210501050414090309090a1b08090f12250606 65
    0x855032501003107205900f880d020840d00030303940205581144415502404480005803c80a10710080130f9444d5101040d03401c0c09260b01c1c84e0110704040c004001c01203141c2107a0b00c60240071100300071036650000112110864150714611310060f401e900034581c141280c1e22640210001000352410580c440400c007243d000100c00c11143d0040703080701051407070880101c0d0050610011260035418407481002d060301c2d640440c200715180004003d900c645514081500505004040603240c406074035a200701c0320048032000f4019444c1054028505008021145061000b9500c00c0c0b0240e42d070799961a503001c600ca60300303020f2086501102c02c3c44180390f051040c7d10f40b00c030745c0c001c205035160000b40815607200003110068030344d0982c04c0001c0440000240e96040034122100c00441c1c480c0129000240034100000c1405038101180d0301c1d040e508603041078000c1401e00221102212603102107501c0b88140e0b003490101260401031516130200441c29003c0d96083d0801040c1d10000e1545c0300000c84240e0ba = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 635532904 1250 635531654 635531711
    0x60b031213080313060309061122050a080c0d02040905030403050d0e030c010f0c0c03080c03040e06030f06042a1403430e070309050607050a0c1203 65
    0x1c11040c0c4410074804200100003010045003081c1131102e000301145990f01072441091703500e01030b401c280802d54008901d200342c3c0300349050340c44000101403a00310020007104464901d000e040003d242c05e20030404021039076020f0141070941d0102041080c0103506d01001d80e0b129071130340d500c54040f800500c0184000d604c00c2004016109210301e018040b1503000f1500d41c481e07084910141a2a60007600080308184146413140e070021407458082e40000c0d0f950400303000711002158503000324a00100034000e541d0311100350a80c9a98841c2016640d03c8440c0045a15401c0240800e00142c0517a8440340c20004106154040180c050a43c602076030b600c0e0300c003812034250036088081505044c0070644498008480301001081c0007003420380300c0e81241c14040e550030750324a1202424100002840301802a0b014050414200701d80c000340a001c000c1c00585941c000c4201250005d40550200c41806489031901c8144100c2c6465040800010201560606854217403000a000d00b118241d80c204504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 635534154 1250 635532904 635532907
    0xd06030b15120a031b031701140406050a180c0212031e0606030f0103171605010b0102070608090c0d02010e0d0f03020c010908031b03160f020117040b13060b0312 71
    0x740380030404a111a8400c001d850b401103944200826032103000148085140e02050311030034803e00c0c08641500381d0f00c41d6400c40862800011890300c44108404500c90011a800e0107840e44034030802500484901c110007100150b0901c1c0110400d0341c0d0054100300340c00d40107403175464101020420b01d43c0c1c401c8585003110341c0c403c807070410030403407a150042d040301003502ea25096150400c0b102107103100c18000a851301200008a03d403040c1070200b21550304907070707102503004600030b480e040d03020f010510b030301e82d015001c1c40e280401c080340715003c49032007002210010495a40140240620495180c405a04104100b5500400354484d88640140c4600c02c003080300185896080007400c1646040456040000180040240507400030036a075030460900007680f00100800c0b075507407540c46640345086809d5030300d55000c410b02110b0031000d4030341e90003a21b900446c6010814a81989042118002d2404410300c1c00f25100402000e58002000d01c10707040000c0c62017a1400007842c1250040540c400c1010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 635535404 1250 635534154 635534191
    0xc0306061e030807060e0115080303010e0f04120302070609060911040b040e07060e130509070602100605010813030306031e0314120c030c0f0f0c0d021b060d06030b 72
    0x1c240c1500321440440c2465441c09505654500e1114411003a000d0025074a403038080c01159000e500241c00c012903180c111998560b01c130410f646a4009114030342005510500140840ba0510842d43c07196500440c1030003940024941a4003e400c08541074401a42d108120030004506100c0d1030401402420010040c0032610100f0060360040712006008600340b80b4065200b00300001d8013010b940c0b0b58100f1840010400020401f00c178072003251146502d00342002d000c1c0f401070120710301c829240c1d03650983d59900b00c401e064130244c135424400c1e540051000380024000001103414030418034801d00e004034860740e0300d031a0300303210222210284a104400207101010550420201c980d00d0880076599401c0c172884a020651201c0300820401d001100000007800c0040c03840304039041c01103030a0010fa150714030301d0650310268000c010301e140340d40b0482c00782e011101d0000907080002200051600d5503c01e030901484042e03005452510341440e1111004400030b10501e1102d0320401584030035000c1a407 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 635536654 1250 635535404 635535419
    0x708150a061d1504050409051207110a06050313060e0118110315040c0b0f130e0709240e0301020708040306020a03050615030f060f0319061113090b04090c030606 71
    0x901d80070b4298440c81a6032081e010f42d060f510251011260304840004110b4000c3c140340d800c144118018951700540000c20074104400c4002419080100756030598a083e124241a80e80780710513581d10102c1d4003401c0c2003030001010f03500500d140c02c0d1580004205190506051100001e800c0012190701c5036440700c01440e41010050b51002c402c8801c500f032600d0412f925000d5004d01c090180341844180050000e40d0000034200310345180c0c481a4440044960796000c00315600c0c0c003034440c0300c00210038050000700034189255441c00c00c030344010010082c40301c0400603603112004c0081c254065409003c2078000c00d1810005d00001c50195102603954051288020200e4030000e00307941c811800031030052030070b6080c0000d0b607074000310030084005651560000603541c5d10410f40d071690306103c0c00845010f071204860241c89814820b08041c0034010754008180603901400341e4443d01806046020454440103802180720504054800030700c0c021244c4581701050f000e0780007690600e031200c60030030844 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 635537904 1250 635536654 635536697
    0xc0b04050105041e0c05040f0b0a0b0301050907080411010e0a0512030910020a031b0309050604121b060e0904063e03010b03060103051b0a0f20060708150a06 69
    0x4070103c1e0004013818040d0b44800d042d00351801204d00843d901d25403906180b0490348003244280d40100007a80d09036948128170f41d40d9200740280ea000e15034075408200300c00c0c01003e800d8041c540c0003032031581c00400000119600d10950001c1540710160180014040e205c44240f6900440c03000b0103150f48065480900001511220447d021507104d001d1410100354814403142604080b050583c0b40421503013011100850583c0241d9030102c7d0001d0005407c9900e100c2079100184a501440c0e8426180020007106948520400000c20010101c002da580b81c1080300603030040c41034000240c103a842d5540d0001d000c1d000c20403012502e503007000702d43300c04c0310780c10243c0c03041c0b45005030307071440d541c10b16440e8040c3d404042e101c0e605142d1180b01041243c00321407181c47c1c2100700700d81040e8503101d50400c010440513140b00d10201060423500c460301c21a101011280140c52104000c09458403220400c54a00c80005c01070400461010340003040d030fa0f510314a50303004089039034a0b1907440b20341a40f000e11030f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 635539154 1250 635537904 635537933
    0xc030513020603010e0c040522150503030a050c0f0303070e180405072601050c0301180e030f09010c0533060108040201180906180b01050f1206010c0b0405010504 71
    0x210044010000160b4515084078151845103000207816100c0b28075110040c0165000607510441a01501001808101811040c100c2c41700341801003028004071001c019641c0d00440703415030002c02c04441610300950042032010300100484107042a49040c0741d00750b4106841ca400004d41b20044200b8a15018840070004d0020b000c20810500381aa655a0b4442461240c10b43c100450030140d001a48280425512200044001c0c402840e003251031070003c1d4401d0040d25141c0b56034034400b1124214510452035000c0075840214640300d81c2a050034020f030060340e021f0341001704d0800300300002203013031001a4821000d104424640041c448012514400307801c040302600c0d2101c0704228107031b0b91011849420903020308151080480825506090f0234007078102e407841500f40040002c1020804080000010780c50800f0001518500d00448a51003a01c9a102c4910803d000e00c0c29188240060303260014414100302c80710b00c169035201c13607912a040b102a220340c0d5598081005100e580711316290b6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 635540404 1250 635539154 635539171
    0x103060b1201090504030504080607030c090b2b2403030e100c02010c020a0b0f0c0c0a0e010b0c011b0201020c0105060312073c050f01051e04050c0909010c0305 70
    0x248075055035503407408a014455070483c1e03030300c4401040c1814012070456002d0702058080d10b949240c40e00f00500a07000c000d507602c0024061200014500d0080030a03154071602d80c841041c441d240c0c0283c524045080302110b0072a0030759801c02901507101d0a103a02d1880d04491540004151860a014080c002905c9955000300c0c49070048850a99100400000065090918881e19030490000c1030800100b0307000011050000038400002808440140c4a903009610071a1b031000441030612a40752514801c0103d0804441c0c01402003a010380040c00c086002e030307000042e181c45c6030392041000811710358a00003d80d50014034200c06000a00406902440680c000c020303c0240f148425561310411030081d040d041c00189108178003a10004040d070130705030154486034600e10030110920806850008450500c540e80a02042d81018081c10788560810320102c00c844080900070641000024403c0b5501e00840c2d44059441c1e43e0805224010310941e00001411402c1202c05012150064070300360 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 635541654 1250 635540404 635540407
    0x71413090b0f1f0909060b04020a18080304080303070507080c1501050f030703210504030f120f14030106030c020c04050a1a0102010516230a02030a120216061e0203040606050103060b 80
    0x4807010301000c140707070072503460f040000340c45d00350341c00d140d00107054045980d80e015000160200e012176001010f1200c80b40c00d9801e0321403541d6079542c2c0582da0301c030303511808150341c10500000d202c003402140a8003001c0c0c0520102440c12070f03040380c01803c00d800e20b011904030101e030394018007950030716006900304400250018400300c1d003592140d608031a10064032a040c48210304072507540a206605440c0150760ac242c01d419041041c3c544010003a03203004514001404014902e80658802c1e1221010718141d1b50740c0c246941d081990460142101c02102815403150301c08000c01511184103c0f88156101080081d094a6062140c100381c6160800b00303045a0600d003d0006c0c48902d8644c1501c00ca106040080700651812642c15103c40c0040c155642d240c0003250010f65a40c0100080043c103000f130303403290400014210b55001b00d0140103024481240d509040b50b001401c80d612504a143c0d2200680042e01c001071032100580e881218125003803500d80004010558141c000c05010304100100c45 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 635542904 1250 635541654 635541691
    0x3023003043b070905030f010c1403070e010c020d1202060402011805031f110d14101401030509072c0109060e0a18060504110918071413090b0f 63
    0x80503a00310b016215104802142c1c0070510290080d44280024000501a6110740c100d841042d4001c03c0c440341d65002103580030707800c1501c168612084a21a030416103e00a0301144440116518141c075002260403c0ca011031002c04503882c42c40f440d5521103258020420f41c03506100060400014520002100703420b807400340700a64010400006040140b01d01d814141424200310001e0400c000003400b41c004000b0302e0a562441c250002d102040c1621903844041e114001745100d4072070349125000d01910400c20b102c89943c801c0c2c1041c1c0d0004005812a65040e1701c41c5910311004000d503d148414441e448400b030619031407420440d004210740d2508000207450480c1194191a00034409200380f41d031494424400390000c0d09100c4401d0b003284d810400c510f82803034a1541d500400c0320a03880366591b000004d602c001400d61030004807003290040c4c84000c3c6451445030b01000d40c0c0742ca26500000360302c080440440c45101c0c20507a14021040010141001028a40052405443d40703410010076410b4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 635544154 1250 635542904 635542979
    0x60714071e05040f0906050c0726192706030e01051b1c05010303090815062d030d091a0304030f0507050307020a030503040603060e0f010302300304 65
    0x107001210010b54010491003070394600780005000d800b074001c100502d050103219124084401a1030118401d0358441c107880414240c00071084007028001c44050800c21255149045244044205c2d03030640c1007840c002d00003080c450044005040e00f05901445460b000c10175940d00d0302030040d0300d09040c8020459420703c0304003032940030b0100ba060003603403d00040800c23a40c50031240301210042d000004100e296120f24000300111240d02c41e120b164070072a6000c52202c0c10b0414224040e5600808669401443c42e40341901c1d210f400c400c2d00080e80302090201c1c0c0544050007422500d41f0242d0303501110ba410544032280b605070580111048100c24020800041e070010b111441c04842814010340310308261500524500c0313005070094101f446140c002041003400006007003501c0701a2820700a99866040c521050381040b52280d624070452401000036051500700d0f50525081015540c03c070000c2d9080c5110201040145440c10354400101004400e01401c00299008150441341c2c00d040c0b400c940 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 635545404 1250 635544154 635544209
    0x30d180509060307091a0f0102010b0310050604090f060912020607050d0f0e0d09080606010c020f040b0d080c070312050a050706110d060803180105041503050403050906071407 77
    0x303480c000c110980100b049a0350812042e0000c150007082880b0301083c41c0508500c0c2003602c034445000d00203000d070302c014075801070145100c050030180c000c0c070b00160840c0d101d4000e010f010b40383e2900a03a4038503552000c101030900313244030796004041c0070562a19924103100620354420720141190841c0c014400a10381c418119001ca41c164040800c030102c60420030700040041d4108031200d17100303030480b9400150b0080100421035191400303681c06913550400545102c031103100000d60001019060440c60710701640310000b1208041c200c5030991490b135456052690144001c0303100c035030000030304000700300d11041c8002100240b454401e00f40401c81c1000b03011303406a40c10040c07009482d89010392810440c44259070312181d13a0102800041d0790b0750580740c0c4070707030022282e154004c100382a1401c10b54052000c540c02c84103400b074405000340940702c08400404010b84102c1c01c2220820400406540346000b800e00b40307002d401000b04020b9060102480c00442d07501c0080030036410044d42c041c1020021 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 635546654 1250 635545404 635545409
    0x2090c07150e1c03020c0c06070c032907020703022d10030f0b0f0105040b131802040501110d0801050d050709090302060f0a18031b050d0201020306030d18 68
    0x89006403180a00e14154441c40c024029450240b03203804248000070200140d82c5907944004910f401c019502c0308001c03410ba2092200c669074130742c0114458441c50600c20000c00740c0381e006404840004d070b1207503240d030720b680945059110504100614400101c0c015188140c2119990005068552840e17001c105d0f400003000c0581d210b00c1a40c00b22914035481070b214214504802070031461403450218005d0000c01000a22903100b42c500710400240b0f04100c0803801b02154161565030a0502d440d0294800754030070b660702e02e05651009000224820740c0c0c43c0b40c00d1107003000384000d40c0756420070000408400000305824112780c01083c0078040f1581114045064843c1a2103442c404000d40c1030107407601a00c3d9018a614601e00518201030590105184e4003800380343c1d015050b0343c1c440041800c180c0b0045c0001a01d89500306004000080c01254192140d800d1040c480c40d01010540b50035040ca080c5140c5030015075000002c0008510b01030040200749107041c104041d001c1c0741c04000f01002003650 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 635547904 1250 635546654 635546671
    0x7120209040201112e23010e182a09060a0905090307080d140f070f0f0905030a0f03020705120c12151005010f090e062211040e01120209 60
    0x2103c8490030700381d091150300c5805c8000428021022041803c8462540c0303409990000e03240743c00d002c034520103c2d903880100b04844c0c0000110b02c42e400d01410f84d00740480602810541502c5c0b50b006203040c4000e2000006800c45824081d101d150704c480b24145124400000500c10300344642040703c0769407444450381c20307584162000503440c4d588050661031840f070900083c001c1700010401840d5400e46410030103800c00d10982c899002c0c0c079102d01132405a0001e07503941e8041a03280342481c100a1044d40c5c000940d204074502a02c00c00d6941c804681029040d40781070f280010341c0c0c0b10480a041d010014500105002d441c01203000b80d08448490b2217040003d0550312641e698800068000c80802248011116980710050181004800c10031809280e101d40c9002c0355810041107100741c0160018821078a0391327158010199211810031000c10010400c0100c12082450000c00300c2a5034403a60b01180041925250f0341c0b400c28800743c442041c142e00003400140b551800d000182c590781038150704003c10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 635549154 1250 635547904 635547917
    0xb09130b01020c030a060b1e010c1b05060f0a020c0f0a1e0302060309030c010c050910031e061d100602030f030406091a0105040e0c0a0b07080705030a020a0507120209040201 76
    0x8480040342020f400c4001c0c0d41d418401d458411042c06003036888a01030f004125101c140d41e1000780000070900c10b0340c0c2c8503907010803418424400401c401002000500b0300844c5454840794840303001407401d400480e03103448008008564941c03100d40402044440352021140110140040000500b0140c0030f80105068884640002180d00300f11819060155600034601900c902d405041c1d16941c3c1c01490300200c056003400302c08610b840c0500c080b900c0c10080940360481108903443c0c1079014280140c8404811071013422441c01e2000e40348140d402031f2191302d52165100b55103042003a9404005405001d031410000420448260000115448581c441c6409a160764540c01c202000301201e0310003400481c03520710005415207003980ad00e810785000302c40400a079250940c0385a80c80701c07600c02c00398000d82210410302040341410080c0640030310070301019140c448039654203400d41d041180c0c4080968000c04c000740030014140004c401516500052141d051456000941d8006000e00040c1c1070010 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 635550404 1250 635549154 635549171
    0x5030906460207030f1206060c0809010e04150801060609180e070f0828111e0613050a0b0703050307200102120402011805091504021308030409060b0913 67
    0x1c040344004070040c0710a40440d1145501c0c10301503c03c0441103c0302000031508442000007085901c1410140c17a00da60701c000c01c2124a036200318290340719034611810701c0390601d58441c080c0d5170760103409240a461400e607140589080a40d1382581c0241e0400710a02040031420300810250912081c00c44504250104101c0071209003142003615580201d000307094019000b1507070500c001201488480903074010306811086000c0c95000040924006000e0007000c004001145041170302e026240a2115905006242040001e0010f82c009040f02410114500307040150303240940c40c240040090002803413a00c10103560007070081c44014224001e01034244001030f2038201382d42c58504034030905ca008654800100b019800907407022101240040ca4032015683c19511400700c4d00100c0f00043c3c02003070f0030b0311411350340038906425030740507500b0541c00c2c04140040e12408030004010141407000d190703200c1c100b106180c10744825400041c84020f0400c03400300c0c0e070788034404521140c000781e01000983c0354 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 635551654 1250 635550404 635550511
    0x60c03140c0912060c030103050c010c0201020d08070212120105040c0c0c060f05090a03080d05010b0f070f0615120303141b03040312020a030e2803181505030906 71
    0x218526000382c03d88120b004010002036042c0007181668014001c4600000e40c800c01150303071184503a0000d006030007004804840d9030140c2e400540082403070068039051555400044820f030440c0a41c910700047d0b00c070040011341400e10680481c00341c0d0b45001c01682c0442d84038404040035600c550800c200c1070194456200c0e20500603501160700c014050310076640d480c10a4000c6030407000c801c4150b0b624000001030418446800c030740c41c0e0480b20340031070700340011502c8000015002c48425290300b03483d060020390000c10005610003810003c5d0510f0850714845c01c00904441c081034600e50301103414024081000c00208125800d000810011681e99445240440d505104d80011050b040d00100d603198010b030305178210f01400340454040300c0194581e410700b0028001410380d641500150426200f0221744200c1b41c04600210404049142c203a030307210240304600c140c0342000002080030040c040070600030b02403503410001040007032804c0074188038118442e100d00454026641d40b506485c09003130 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 635552904 1250 635551654 635551669
    0x201051b10020d1b0c0b010614040503030d060806070302090a1403150906070e0d08040b070c03080705030304031d0a052710170601081b010c0f060603060c03140c09 72
    0x1429640d90a54640c0300d15101030f0041c1c003002e103000e400b92401c80d4400901d03611071064406040d81081c04020b09074038000003518000f01e088640342685804102c041a5618100018021401407070000a0038528280c05c16044c410302500401c10580100142e082c1e5694100b010000e440404900c01c00201681000920b0310300c0b0000d0003500381600008101502d0300201e81c092080142d0345619106102d810104803a2040f800d200911050341480203201001403070002c2d01c1120300c035122641c0c11315181d46078046940c001810840765079200001308807c055004420545a00d95203211640d0440c211001480450040c0202d600609071000c3c0c0080301c0d104c4502e5003540d00071541882d521402c06014030000300c80980558110315140b0311042c40325070400520715040b21400ca0140c508a8240103c608904014030b138110f04001d2100b5603000842c01c03049070721055602c07400c0002a00c92840c80c0c2403060b01c14a0503403c00707262138146401040c56001d500720340e01040140315240c0d201101000180c00 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 635554154 1250 635552904 635552923
    0x15031a0c09090a090215070b012c01090203090705040b0108150105090a0305010f0b060705060c090d0605071e0206010b040501050729150a0302010e131407030b19030201051b 76
    0x2100000503c28805844c1d404210340c20300980300000480c01c0150345040174071030341070018251b03840e00004211006074940c102d0f4001c1c0340f11240c10022040c2881d40710001310207810903c0055800001d01000110070041c203002030a083d1420f100304d031010400a4008203000b01441d0403e401594001d20503071040045070190030000f000d4003001602c80c10f0042c0245150207040e4a81854a800c41c0300a151410a40b030f41550300100034080750382c4004519250350402e00c0910b1304401d40da0400c02c002801070089502c02e542d42e82c2c8114491082003803100c401210f259807003065400801c0180b1450705c2020440d001d42d6001e0801d1070b0303900740ca131030700d2146107140c0003d1070350071207198a103015500c9907250800c0c010f00c80707001f580e6490008c40c420000b503c2140e10000b804910b55802c8038000e420720001d02e50440c2810f00001035910815840720b5072281c000c5503083c0c0002c0e038580c6408101c0c5810100c5035261080c485c00f40c1103090641d03001030407502c24424115a000003041c085d5042e0401007104043d07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 635555404 1250 635554154 635554159
    0xe0d0b060301062301121109010c060e0114070e120606040c0c0f0c051504080d120902031b1503010f0603020c07120f060c030c0c0803060111150a15031a0c09 69
    0x1d0b8801031003924181302030b929600c140042c02c11032110320b0305401402580108030a9a000070300c1c0ca48820010743e861141302c8030854500b0784a0585003500b010a2007440302450441c40c40304058030388110002c0c151804005c031117120784c2c00d520a4181690000445c6940030100351400521040102c06c143d501c3c54550b08001c000510142c0c000b000c001440921000b26039040c0d9100b03943d40b40300d1001145a010314001d800ba6580314100507800148500f007501c8050794078220002e0002d001e074011a0822032483c0010890381c001681140e0700d41005049465038020f03180c042819541070220900350b400e96440b0340c0040503000300b603101d11400140700c0000108802c0100f01c41d00e017540e1604c000020080002941c3c00e0f8948011054580c1c081d01500081d55695503600340849210394844401d904042c103200d0403c84000001c2e01c50301001c224007114500101a034070310f2403400076441420386d1000840d44880e000020820070000d4400040c112110002d88170b400d050b43d644201010281c007070b0440c120f9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 635556654 1250 635555404 635555429
    0x504110d020310060206011706040f03030207050114040b0c042702040e0106120c0314041b050a081b0f0102060c0f090d081b1b19030614010806070e0d0b06030106 71
    0xc1c00c2d0721550f01d0b80c400c41e0000e80035a4211303a601c0d03c044080d4a4400c0700000c1c29000140001e0004001d04002200c16129003001410700009484075400c58501c401c003c0051100c0a0921003842103001155501c91003916806281c00c0c2488a9816614104480d9040c2410048600c0c41c158201d901601c1c05080c0e1140401c1d81d66035030700c42c01400c4042c546418004640f4200d50030100314070074000d080e40d1106400500341c0648a84e900c2545c00806201e4228800c920808041080d6880700e80c0320380180064002011346201305c140700b4014140baa40c416101d0401d0600c034480e2a600851142c1c0e00112909010b616032a10110301203a6108442a80f80d010003c0e6848004109000002d046204910110317410141d01300513007580ea64000c107102d5801e41a00800302c4003949070100143c13900031a010441e4560b0f940d280d560030300f9504d9910035151410070000c014046d203c410444554441c1d45031401d001c1c0c6a0340740c00401d10040e4141406060481c0043c00070384541ca0940000300144020034002c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 635557904 1250 635556654 635556661
    0x203071806110c120a11061207080421050412031106100924030f0602090d0f03180f120302030c03070605041718040e0f06040605090f0718020702180a1401060c0308010504110d0203 79
    0x5021240c1184c2c1115100702412103010030613030104221001c1d45637512900d10b0315080180d200c1c12180700000c11010011b41c0080c030308a2800901c4100e025018a0b1064003c50b0b05103071044058444020440000c17580d01c1c041c0071074400c000c4120408503600049052182000e90400d1006071007202c002c42c0d00715285851050030032020720140508140030b42d4826004503003802c8070a044c0c05091040c007600b05141681481482c0b2032031103002056120340100e03450000545041800c5810104068688695a400308030601c440d4511080110001108403031406218840c0e811020161481da18047e540e28208299512410865080301419400895042d4501031400070040c03c000c031202019401880f01d021b042d480c0003d0b21200751000b42510300c0e05282021019030003074000c005c080c1c1c0c0c003410f46011811008503040006008000e02000851904108080901c03c804180c3c4140c0411140e0600840484e920440b0641542c108550200e0b2404040c9110040b60040144880d012032000052 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 635559154 1250 635557904 635557907
    0x503092b03091401020604051b060d14040c06051e160203101e090b040b040501060b1b2103041101020106051002010f110a09090203071806110c120a11061207 69
    0x400d00700c46686803081e180c0c0009100498903035a0958004008d80e0204c0d40748007160b046000c8141840710058003043c02c103400c03c804074041e10100180046102001c20501040c090500381d86409082d080c1425484c000030300c096602040c503800f030209850710f00403c144e200b0100310099070360a284c004049440004050710b03010001c000c0381280c25175104001a10801141460080005d180d400200c4652260760f60303118001d40c81c0f4002d0040309d56550742d000108a9104650180041040725940003c003001d4035050145440c030049814980d000c0c0051203061004a800c0440c2d41c4607038002d016403100005400180d002d4100fa80005600c120201e081680c0d4990551107034241810040b42445000380c000e8a003920361040700710210014880301030030b000b840c0c0385030007d41c1c0216a61070301d10804070316411071100c0222540c1200d030004000d800ca00c81000030401000c4004c07502200d562112a103001a16030360f035080d100004100190100d40c403041680c442041e12549511840000802d1924480 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 635560404 1250 635559154 635559167
    0x30a0b0702010c0e190b0d021204030c03120b0f04020702012321070c020108070e06040902030108010e06010b22090203040501050f090f0312061f02010509010b01020a0503092b03 78
    0x30040300103002448442c0051170007441d148100e1540628001d1414103081d504012588a44c06245901e81c0810803039404955299140c0d03c194000d0340c8845140c1d10a2074000d11049483c80036410503400e00c490214143e171450304003d8000422100180d80e4030146c070058a2011426101c4c0a1025011248402045c511002007030007900c06c031001d4042e60b040300c0d04a20398010686010300012240311040d40154002c800b072030707001200c0d0708258071201894030024205034000d4004016450700400100500c01007401440440d211040181c07166605084241c090390080c23183d081308491201040c1040344c615045002e015005944041d5600d2030b1909140b4003030701040e11400d114116900000c2c3c084013021403400300d0f05003110061441c0c02d0700c40729244440f0703a000e000e150740003022089240b080e0322040b0488400c0702958001040c0c0e8544144960b08590201e04580d0641d08601000d10004a02000301e5031891000c030b0f10201d500d01016402102c4103118500d04030600e8090b4101014141c2041 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 635561654 1250 635560404 635560421
    0x21f0e070e070210050c07020f0604030f060c03062301030c050408070306060f0b0a0e130f18020405221407030206040807030c17061503030c0a030c0510052202030a0b070201 76
    0xb001c50304880401c0c80c4e840103c510842c1ca46140920074016800180b9000005d43e01c8900020301080c14142c89071200305072018600302c1103c400303a4038140f42c031010382c140c00741400400c6c2d060103002da074010b00d1800d80c040c0e00141048a04040c2e540414034100ca000d076064030003602000046486003034a070310300000106024013440f00c00d00c40c0e404000403020f1030310382120403d2805a039518012240c0b202030019243c400c1c0d0003110850303140c0301041165110b512821400f030080c40302e0340b60300c0000c9006200454401804203403503080e101c0c40c401d1000a2580108040b0344d88001404600068144d0380317800c194580d040250301c03050010b400200a040080c0820650b40900c049040203aa00c0414801703080c8180307000ca4650b0400350004210080341c041d101c8040b24042d094a1a00d005210020306184065400310003040c62480d40b081840400c0040c034046014030b490800440c10490a02c2c1946000c0e81c43d401d03240d540030300007041152002d00c0700e40c02c00c03540320b42c2114042c180000d000e8003802085 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 635562904 1250 635561654 635561657
    0x31f0906030c03142d0c0607200a052209050708030706050709060c0615031502040e06030d0206040209101505090f04060b030a0903180303020708060a0507021f0e070e07 74
    0x4010f4203583d20000b1170b02035010480e10401d480044000350300c61019401d80c5a0b403189600520761840c0030303616040014107829109144103800c14088003243c10f40500c50844890041000c00c02c103020a8071040c0b40c81d00c4c040000307a001819001500e8420700641010f8600400d0360248580006502000001030081760341b150743d09100a03617400c03004070b80e84c4915200d41c50000c1c1d02d144009010410302e6004510050700600791005960b01e03902c0c1d124075298038044000d209580060704201d02c0d50043c1b0603d400040440141c8031604404000a580d0900600f01911036400b10010840d804801c0362a1070080174400d0300d45a442000300805082c0d03802580000d4064100741500c0380c003034a03144c800e000c00e40e101e01101504684413140300100804e1244021001d201d000b09800d41c8241034510a000214441e40c01007030362500b000b0783d90f81803200240003e440d20b410801480502703500403845e03c0c000c4140e44078040d29581b081400d00003600a4483c11011802a1040404c0c001841010b05100f803290f0b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 635564154 1250 635562904 635562923
    0x803061002061005090c1306020706090602011107121e0201020909071e0f18121a040f020405061f0806011e0503010528120b0f070203031f0906030c03 66
    0x140c82059864080484034542001100c0700140210f291a140c403941003100c004000342040004200740300402010703086000981e000e0001004907a07404208800a064148024801071600000c858428000c088008040c0078200e4403010100344203002410510102e0718694802101c13040e00a4000d40c49207030114040c405800025506d64006c065003400003c01505817464000b000f50212201c1c019a058002041100824071140d01d10f0ba212001c060a03480c03000c848040d2203441c01400c00c0c820000b202d6940310818040002081c922075800b441540c05940108256a070040010740c0010000c1d5000b102c0c1c41c2100c04000160351141e40688a003200b03032118060110710800805c45400e0509241000660800050203107043c084010503172000125052200e900c14046910310502040e003014221058900511061042c2250165002000c0b0b42060320316090104009490380707c0101150415070381d5400c00007420301210350f42d10080c0280201006115240e14000701091000c1c0700c145c810201c2c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 635565404 1250 635564154 635564179
    0x4030e03010f0c0203031f050d15051303210f05040602120c18042406050c071e0302091302100201020c01050901020a210e01020f041806030305030604110c0a080306 72
    0x8502c1840c0f1001c1e0503400440c215a100410500786610010317507042c48201c00c001c0020715842d00c034003039440ca070711600000703254274108201c01c0b0844a0040524034030003140c1800e107010a800c001480c605014891a139910034070748100c0c9034003070724580c104035040521b400304100070700c10568080c00011489002011954542a03241520781c000c030701d0400c031100e2402c1e0340c000882c41e0a501000d081050541d81001100205c07d0503c001d0b41e20b54080c0c0c1c041030000550844101c024022240900402da000344072203d07100120803050354180c00024003440395100401c02504e5211001e0280c42da004000c070b02190100d510081c082e40120410303140642c2010046121240306000742e40308074042e543d80700c0c01c04900f244201c032444032001310503a1403540c5012078140d08000380020301500907400da02541e01da180592050503030110820070034140d031510790b00348000380c2e00104480d0025012174002c100201d03941840303030182c031905030023481d1803040442070004c100d5924055881003408503004e140040 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 635566654 1250 635565404 635565431
    0x612030e100311031f0308190908030c031b010b0406030312151211011b060605010f0c0b070509010e0a09140c070302030313030504050301050403081605090603131a04030e0301 77
    0xf84190080c08480c1c409000150007a41c01014558141d5891030020840d2640d9803105036095011240d2040065104010400d040350450113007001040141c1c001c5141421403400d06440340561000c10308010910707124540d03800000d40001c0c8000340018000c01280390380f864041c104550101e0000340032814080a81420062106004125018454600c41e14142aa00e2071b821041c5100071506202d403151100100205408a110005100355000100c01d070801c0005002c1c54400e07101d950401c0300c40a400c0d00001c441c250080c1e00069241021900c440340040103035000c0806104854001500e6207001600403c140c02004e100f103c61303180e100c17541e2030707161106901d48102c0c00d019001da4410004240341c01e4003518441c100900a1605504080e00c0d500000d0a41d03030103030741c103a0024001905200c50043c00c00d0b1b01420800141c24080c0c500042c9101103030031804000c00c05544450502038003400d0064044072170003038002501c002095440c1030b18015080c4050442087d020390310308182e015201 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 635567904 1250 635566654 635566661
    0x30601090b1b010506030a030c020d0201090e0a05071403040305070f290a050a060f031b2c0a0605032104080d0203030103060b0f0a050f03070b0c030a020f0d050f0705010612030e1003 80
    0x1f5a01542c0e1110154265004c1c042c1c01c44081000b24104a07260034000780e070312a034400d0030307000d0980581c01007070300d0922540040c00074080c9a00355449007400c0041c0310000b5082030031101c00c1903000a89000300c00b41404d06003052040911028109107101c5901818440381051092091643c0d0000300f1040d151030721000d0440e400da0250704c03155101d5903024404544c40000407400d0160f41340420b1002a00d5010824811b40756a0104034825210803200c100c42007652682075114614880c108151480c042c00a661503100d222000344058055400d000c0a91a40003120084c3c0b200004445152801c14070007540e0368804d100030780b034076407403c0411060351801c1100c440260713200903d03400c0b26500301002c0110007003c80382480e03854411400e0010b9440c214070046c3c80c00e0403850000e148c541502c0c84d800390900310381c1407140000750030041c0c07200203454201c0203680501d04000005921090715250441c0189143c0d04585c0e40c0b030b0344d040340800800d54401d43c070080c0d1001c10340d044645070f00c03880b500390185e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 635569154 1250 635567904 635567923
    0x9050c1b03092d04090807060f05240609120601030203060a0507140c0a05060118060f0302060a0806031e030318060f01091107080d0504111c08030601090b1b01050603 73
    0x9254108110901d007000340d241c0403c442859802400035403070b00000303011109030f00e0b411220100041446003d2203442d210300c1d000042d00c00000e01551a200300d06180009482c0900d4200c241d10a00700310340c9854020a54441c1c2d04048c003a00703a4080c4081c025a40c0c0c2e0403d00c0102c0c400d11480c000a0700203c10380c0a102d02411150322440400d0340072080c212041d81091084000380c3c0314448859011800030000c0324020071580c0c0e12411441e80c1c00440d202079440682064001b944080020001070f102c4c041200d0011140c1c0c42c4c014550b03203904000070700340401c500038000c20965909040ca10290048005d600032507140104090300840c0403852a142c40e01201e44003440b0001000401c002d00d296001400d01035007141800e8030340189987c0b10300d1643c2183c03107140355440d510420401000501e00403580300d01000c0302e003c0208008494400c00c14590150000c0c4402004070204105900648031300020b030460503030b810345034104500c00707440b9100f054000c2d80056081c180820b60604020464401c03 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 635570404 1250 635569154 635569159
    0xc0b040b01150f090e0613020a0e0109090213031e050d030209040f06051804031e0207090b0405270313120c090e030a050708091f08100605120a0609050c1b0309 70
    0x3001e0f85010608008814014141b0744c00000449102c600100c40e48000e00154005840742150000340704001414404540c00422240d84108400d2545129540480b821260f018440f007036a4611007185030100c443c5007078002d10394450080100f0840d034041c1c01a0040250680f800c118150b84c0e40d040c4015608030b0300c2069003100900300002e851801340c20b000d44c1e0250183c2083c0e00c0c09000c26215420001d4000c1c2c110b07005070801681840031411502642d189070608443c140703d9401c0400e80360f1b10401d440f0008001d40c10a081c3d016002c40c0091080e18881800e40700e80042865540d054a00700b64040c1c0030031200003c160401003081c156601c02e04142803c0c44000358106840d171041036134281d01481080c0d8079071700d05000f034070010b680300701c483d0340f10400319145402d465500711000307408400702411242d5217165108092007442c1d03005065070310058070405003008640340e04202100800f0180c000100e0301c0e05200030404054100d000a1800802c42c10980c2d10000005490f240c4074001c4149095 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 635571654 1250 635570404 635570417
    0x8120906131709040e030a09050a080d0906052b060501080612030313020d020d030512090705370303030605030f060606070b100b071a070c050a02100c0b040b01150f 72
    0x10815060306001c0c040d840c03405000081c6031451154906e165420440902c000110b50110901c59410242005001000e16100a0001817200b5001810310100e60040008100c0f004c5821000b00c0901242040c10500e0f0b4400c0d84002000d004140000c0d02d881d00841c0d01040c0348501042e450709110000b1001245040091815500ea4507415245400b070403606907801208440c40101580d5503900b046003461007611401e0f03171034403d0745404040760f400401d080d02d9500f00200800107070f250071350700c0182d240f410321262030020010042c1810410003034404018007010f6010100806030103600140c03c0d0b40f800c0701100d08110f602c140b040d584d01c8042301c1c031a030040411f01200b0001038418183c02d4000348031a018481e46034440d00003000941040c8010f8515440e82c5141d0600180c5c084c107003507000308a80c81c00d604000510713100d4136560450000d0003406a91000000301002c0d1149a14400c0680d00c2640e078451800c1c50304240e0710626082c0641e40c0c2102c6081c2c1540141400741024007a440016103900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 635572904 1250 635571654 635571683
    0x70324050f0609060c070509090a0b010308070c0e150109090c200a1202010f0606030e030313060b190305010501080604020d06020f0409021207111f0e0102070812090613 74
    0x703081045551403035080b20041c0a000c1407035540310080d09800320f20340000c0192614040030003501000140041c1c143e50010302000300450581c0342d1682c1903d800101d5181c2d251341a00d0040207111203a40110810301440007403024190780b010050040310426079035460495203a45165040f00c2e545c02e0604041007d20748098a40250495140248a1301009455000701140c4030401e20a4800b0f1481c1d005035520346410b0740001c20b620410000d0903040c5020040e00055100040da80d10020305491800e100e60f65000042141d6600880b14405000e8108003041340114049550030035070340011586542810000b06044000040c0d951103950014001404c0407a240c503280000e51041540b8552034900708000705880103580001c090261020030407544502d00f0340401010b9040c0040341c1ca00c0e0b82c02c807044c4075443c14102c4400303070b83c5401c3e5120000786010000d20160300910558070014a070f62000700300d11030040c14840096218804140660300e243e42e89000c040e141100621004018211000b040c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 635574154 1250 635572904 635572909
    0x3140601060819240e1f0e150a080d170912031b0c010510080d0804080a1d090705070c0f03080f0702030a02040e010203180102091315091407032405 65
    0x5241091301a940403d4040f01c1c054140304011800d8120200851429044c8002c003002d01d41a0400b005290585150080c01c058400c40132510140aa9503811018140089a9502c84035010010108401100c100b592042c1c0c5c050304090b06a502d90384404841000104601c45c0810500541d0048075100c1c0e2550303a5100400d1940001b0010513070203c8018080000348a009100303241c094020b00211a4860b40751814107031610706200c01e075a040100074014000001d0709503054607584411030131309010742e4542e428903c440a18403605558811081d20074000407641041c024541709000301c1050960703589401050942d4410307440300401e03811b401c0000c542e600c1c4001e4040c11500d8030050a03602d0591840e0005403c1d214442600c0c5000e0354000240001c2e50440b41c0d51410842c0500c0003503003401d813141300041146020002c011300d06526a220402031058003101c480c0a040e800f40c080000d52030742c618183c2c0c2944120703402d40209141c402005440300b01c0720501000c000c038040486002604050a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 635575404 1250 635574154 635574161
    0xc0f030610061b080307120e0a02130f11040b03040c0501021902010f0e1002010f1b0912110d0503030123060307120e01060b030f0105010c0c0b2203140601060819 71
    0x3c1401e81400303600103050004840a0046018248071b41c2e400102c01c2c084080e480484041e0540e40d05260302814520005858140020407020454040000c00350807200c0c050b80079050128540000c2ca000040215a152070600507500460281a507a2070300e40d00e63300160303650341b581c0b031401c416685850841001503110b50401c01c86903405140188400c94950003080c0ca0101c01507120000d80d44400e15035205506a00c030b400c540c00c4841c00715508050020074068480c602c0d5000e103064031041290305405000d08035050000501020308800700708019410865140e400c00e0186c01c00d000c01002650b040003005004440b43c041c0d0003000c0f00d255484504d0113454120b024110711200580310143c0000118080c0320b1440100843c80003607640303180031408449510070580040f0305000454502902054000704854182d44061103580d9803500c140c40390f548405c1054132594000c0400c0b042c003000b040f20761846245840b030304c04200e800c1a40c0768401030300e07024030840382d00140c0c800710803001207507029641 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 635576654 1250 635575404 635575427
    0x6050a1403030706051305102f090303130e010905060616060e060a090c05042d11360f010c0f0b07050c0d0c030e10110f0c0f03061006 59
    0x404603858800f40740c3da10030a48000b1240106000c95007051032051100600000d5200c0c071003040c1c200305907201d141030b10391402d2030f5942d108105001d01981500d0819000225000210000e046036101d0301000340d0000b03101402c0c0035103107081d8100000062503074128082c003802098002d0003181069041c4500880c0444065000ea54280d02c400042c075100400340034081c01215a17690220340303900319007400000986964130140c007452812003002081c4001240141e000b40964440c001c803c1103600c0350001403d031583c040c1e0f510b40070000710344681c000d0541402c0900a006170500101e00702d2000302c842103901e001e68194115450001041482d07209840d903881d500d2007004040b01e032010a4070344807900f41003110403038046440020540f01d03c210400650b00c42d485e2a1030a5141c0c0320b0281e60003410240101261030041c0c4204504007860703801a0840c4040c443d166080b80c50400012640b40e6480b200361410600540705994400500c1c00c0124500b0311800c2522140c038007461030014201ca048846c807 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 635577904 1250 635576654 635576659
    0x6050708070c06053402010c03050f0a03060f09181209080102120406060f031a06060d02071b1e0e150306010602060402010e040c1e140f1b0106050a14 66
    0x4000c0c080c0001c12804240000d00250350791355840e1411407018005000c0c00c0d440720a4094841702c3c82a00c00c0d41c0380104940003d0f4213107407070307006800c0e6407509a0b030318015005140341d00310f0080341c03d0081d658160b028030304540780c0022049034559160486400c840d2620b1148a00c4e143c0e80c2c141e500810410b61007014921041d2400464081d65401d20307a0880e0000004514072000c02d000340000d024041c0140c40150a0206200a4441c59542d5041c04002c030f00300c0b004001d0f1192400201b03260b40c4d1405585115040c00382c295600c040500d00035440c03100340b11082d0041c0342c9003403010804100104104000b24101c3c44040b486e682804d55203500c1b110020080781d8041c650b0201c070303011a101030103c68000c006640083c40e05040031b2001610901554a140c0d000364a003580c5081056400b100000304540c0d940f42e910701c0c92800c880203e030034032845400e210740720800145c40d10041d1409401040179948580c414801750701e0343c0c03043c0e43c20f89000d481210f6102c04024814003009042070142003542600 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 635579154 1250 635577904 635577907
    0x2c0103090357030804020f090103050102072a03080c12210618012601060b040603050606070f170d090308010503103c05010e010303110604020a06050708 67
    0x42d40d4820b10940c0b44002800004400e80078541d001107107800c40030845030002403900c6920000b982064102d450044005801c00501101040c25900d030194070a03008000500800001d603101e0804901035489190112818050b07130795107884d90458815401c4241401e054009800d5180d41c881c2c01581d044045a84428000c448200144000140c01841e84031080d04200b400c841e4034406100182c000240350700c0c054101c0c43d00c02c0a0800700d54204c2c41c151401070b400c0b45035070b4280c0d00d0400321381084912800c0580d840c00d44085844901640904100c0d0800c2d601889907641e50b40a0228038004c50340002c3c281144800d01e440000c402d050310784140880c0304001c9003403014a1200c00243c414078801038010a1180e030040c0110705003402000380701c0da4100b0003070100d22072010050b2400300c0a400245200c1c4420305004180000c9001c5070500f80721154001d1001d0750311402d400300c036500284400c50100320640f031101b007424800700c1c88030310554000300280c00c110714000050710258012030040313030038100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 635580404 1250 635579154 635579177
    0xc0f01110c030f0a1407061e030207050f06011a04030804060807052203030e0405150f010e0402040906050315011a0a03020c1005010e06150403080a0c020d0b072c01030903 75
    0x41c10098842c654120b04000c04d410700490520550000300440d414903180c100580c00d00030190400000300d00c10090031b115460707805045608900038000d20800074243c0c052840540c4036128009505411780d001c50888000441c031450350f902c0544184e10000341318010500c41004002d001f003812a40c070070781ea400c08614051030401ca0b11443c2e1000c80c0707205941840c2910610500da4030000c0c4441080c41a68200098148500840c120071070140500344503218615a10b00180d10a22290390400380182c019904c4903110030540340905228010203000b031041607400b03103144003094142d0f81207601ea54140840c0101132000c0d0b07400740d03122001344410b1540810040b0041d0f4804c111960b01c3c80c450b08800a101d504156080c034031204003419041c07003495000700100c140380020b000c5404a0f030b8024009951100e0034132040e58908030f10140a54070003070709030380c500c248885114801d206240d036980e00d01501484500f442c0f0392800108160545101d1400c4420995000380c4c1f04081c468002d0801d04c3c0d6101c0d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 635581654 1250 635580404 635580409
    0x70e06060c1204230d0818040609060b03061503040201081602031b010507030501171207060b040c0c030201110a300606050a0e0a08120706060305030301170606030c0f01110c 76
    0x500641c4101c0405007007009a100940442e6108115444c0880701400002010380711035045001d030b80f20007240346d400880d079240c143d03981d0380c400801003a0002041c854a90354900c810f419403c101d8941d4020140e503007503603aa007145e2008a078420380c0d0503190000d007910350103404044411020b0281c1c0039031004114021140d5608480810302c21207030740010500d4a40001e004055030b070180d0041000002c1821030840200d004a03135640130f1100c07115056160b24250609030040d00d090390009410500d0811480c100c150f00020480c003031402900240521200012200d00302d10035903c0d0100001c0d0340840161741c0405084407030000540801c10207482c0d00c0c111903d58200c401c29440078022440c0056414103480c0c100c10300c3d07200b140342140c0f055410f86c82d005c055038030f614005120b50500c2c2c0c03000030303003034100711040d03010b00041d5410038104da0701c030341e190006000700b2005c2d08610340c124454a0002250352400080070111041c1c0034107900314180f06070b0b0054405214440c1550140e0141d02e0084d850394 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 635582904 1250 635581654 635581657
    0x1509050a060524100f030b1201050402030d090e01211b0501020c1806040c0207091e06050907090302060c03041e1d160e2b060e070e06060c12 62
    0x40e03004280c00641c81c02c11550742031a0100800a00c50f07820f041e02003901941e510f410408a42c40b03094240340741c0720102e80100f100101940300312241e11601d801843c0310424815400148158400d40403640180d0800300f00b076412109603c90400c0b2014910010b0011a80c88001d040b10103661048060300110540d40f60808160070365500c070781400740c8003010090345d03904100a5a01210644000d000e0000d07030040c6039943c400041400b4010354403203a10310f601510802448004194071b03902040306000d07440590419540c0c0d00e8401c1c84031801d0500124071843c10320903550198001d5203071403040038607642c28030000360004c201440707540c00300b400b002171039080f19850b498010300780e50b0741c41c22032034185442015800440c22000200b03d01d020200700c0b043e207a10403414004c001d581007401c15404207400265140c0c508a080c00700300380d481440c0040003c011080d2000144c45040140203201d11b20408540c0d0707900d5803186030509103e00e07000c51001d0403c1c2000341a0241c03000701380c0c1c0c084c070030090038440c00303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 635584154 1250 635582904 635582923
    0x121e05060402010828050c07050f07230639030309010f0204060206040f020409120e1008090304030b150a03120e0906101d0a09060305011109060403150905 68
    0x180c0c100c0820403086692044c0c0e0340e0350140580f0720b84480324804040040442c9039802e8001c40d044d550f00086400e81100201b40d8100a40c842c084a0362020182c82040c1c9604040c41030f0340c4442580b0001120015003c40340000405002c0c1c061428101401c0440c0d801d000b00303000c61a51044190cc071909488088000c4103d58111000215928104900404e086a5414190036100c500c1480b00703100140e40031505503001904801808043e08140c0000780081108460041900b1a03007510989025005512008031090848054845074030110050b01c641c1c40c00c81e50f80f07015400401003400040d0501071103540026010302d664802c11180e6010510960340e98000744c4001e520080300a0407980c0c04420320355a484282d03082800f609140d00030525006804420b00705111183d504400800b100380d200c0480440c00030000110359585000d0300300100302a000c166030030b50070a0110030b512202901283c0440c5000341c0b074285880c2ca9a1507101c0150f1006d403040c82030580b45d94a410110341d040281b40b01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 635585404 1250 635584154 635584163
    0x406060e010914030c3c030d0f080a0c09080a03030b1314073501080d050301050d02120f1b09011202010804061d0609010204031202030310121e 63
    0x28040340450001d00341014550140c1e0142203143d0070b0f010503480226484401e2601502e07035407400350042c001074280002c82082c40d08200f46036040300300118400306034a0a45003050f4140e805c4000110070803039040e068a40c01e1070200e031285003c9944001641e20030442541541341031101c180d110250a410010550403d84c0020349880b4075003a14036111201c546801c0900303104001020300b21102c00050040240030360144002c120003040c0c0201810911000500352604001c1d0b8000048141c101e08030081c0580c020a100b48181c40c04241d008034201e9068074001085034121014a508000c520080d1050301042ca000301d1401c1c000140b8200700741d11548001402d4811002540414000c103041c05034005240c107407000c01e036a00982d030000300464109411460101c0c81e00e02c215880d403a0700c0e003200d20f1106244501e000300f01240e2810342c050001c1d28450740c031a480b103000030801240d60b4002624080a91090f6a03030401601280103205110503100300000c0413084141c03d80d24801c0c1c02e00d100240c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 635586654 1250 635585404 635585417
    0x30f0328050618130f140105071b02092212020f011811190b041e0e040303050a0209031b0a080706120c0212040306020c1203010f090b031926030f0406020306040902040606 75
    0x701041c0c28002d0350740c00308034ad2920300390345c08000d07a90411001408001034019507058020610348005c4c0100b503414401c01440000c0c0300310481c54101200d12070500140018028201f0507410b02e0410b00410000e8402d40c880c1507a00b1200d03890300e83c0d04000071300071564031542102c005407500c7c4e4a20083c00c0100b050751200b5440ba841c220024103540064080c0b01750640003e03205004480d0102c106640240c0c00d4a00040d0070b80c0d400c5010f07802071080700303c507a905202e0750700303490452842c6c410100020b80043c0e40c00390601e07a848a92541e907004c0c9018503400314515002c540d0b011089503000000c0d09080d0b2040b24801855064035102d075034006e03003090b01e07034130b400042c07a000c0c400342046800485800844214610b6250005400fa418101d0194141a68440c495003a465400b041b00101c0200110300ca0341150b000341c5040c0b05800c24640b045580c5007115507112108814a40039079100340140e007040426541c442c3d480740000d602c02842c00d0351082d51407039042c4c003603141c5202d80c10241c42144c5808 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 635587904 1250 635586654 635586683
    0x6090303090603050c0a08090a0b090703060e0304211104050c04260705130609050708160804030206060f0d050d02030310050307050a1502030f0328050618130f 70
    0x5001c01d58641041c01490308000c1848807004043c001c45491280d5441d013254241c4a208496081c40340e42d04011303046048002c140030740d60b04046603a000b201e210340010403105400500c2a40c49004d0342c454412136031410705299403115501c2c24002c0750341e4482d4010b80c40c103580c80300002d4101d62040d078000c9044500850144030010300387ea9508081800201d14101c00031150450a81d110400d020300c500030705c2c4c0143c07140c0d01348115400c1000a0714a107102400749280c06600200046001c540d00480c0041414104000f03d0041601c603001320b8040e8007418144c3e507010140408100c44484090f0001040e40f40031020500900800b411030700b0541c00341d50b6a0a040003414034091450b00600d03c66003141d0810026951204c0010040b501e02444030000740641c10001d030f0035030192140001c5114030000803c00380070341d611542070401c108020035441000103118a82d0855000310b5100b82c02c0280c003810b040100305080ca2880c0e018011440b070307650700840c560324180404a07046c0b00301d441c01042c54a4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 635589154 1250 635587904 635587907
    0x2160605090d1103072301090c080c010f0507030c02060f04080d03050906011e17031e040302040c261b13090501080c03060c031b0414040f0209030a0b180706090303 72
    0xd00e80801c401001142800309503240c83c0402c508800c0c1126041c13420b800411007640c004c0d0007071000380f83c00003449d60040c2d50300c04005484200c851541400101581004200302e8050410748070403941641d2030061a402c0c1e5428814160b2080c411285191024000012900800c0000100d002c150b5a00840c09040441d0914a841010b0300801e0510304240141c8000e004030741016402c5a03406440c1140494148c40002d04610505107000c0c02001c01c040e850796111150001403084034400c6d28204494a040d20089445d032810340d2503c2008910070050b020449030b03400b0200e41100907458860503178034009a9030102c03980310a03a4041c00301000042002040c0c0e403482018010589100070b41040100200003d8407204001c0412801160100200d00c01ca010031000d2080203a50070b4989a0300c60b240c440c0401c16034458201340c3d204904080d40d25036402114003e40c1e0110380054001c0000c0c602c00d0799812401d080c0113203220700d0000768881c1c2001440040281030014161a125121010300710f040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 635590404 1250 635589154 635589167
    0x7140a020906060f12130f12090803120112050709150801060503010504030203120403210207050c0f0f01050901121b090b07080306090402240910020106081002160605090d 75
    0x220b44100800d0250103613502c02d0314225450888541c8a41c002582c41203c0c40d11040d4040344050b01d6010f0000b075100030000e4000c000c646030a1291920380c5c440b070303036204900c0e501c5c405c0c0700d20a0001c42c0110010021040d01f103e080c1c02051082c001d81d0b0b080d645402c980c030308403400c0c200401a010074142040205410a11500c0c01408054000340300a1500d03440c01707942c071701c5040c141c18991052800040c00f03040c07046030340103018007802d407031700c40415000160a00a5000541c0941c0c00e03028954614a5a1a01c458040380f0f16101030210300c2d00c6840c51006403016004141c100c2c0c140071a041e101d20540049101d84044d00d02c80340455641d52400190040c500601c5400c20701000c941081010041903c00b003d40c2d0b4410000c55640d0b480765118408110b01c5440700040c00ba10b008800d01401740700b0100b4014100c0c8440a55207900420b1680380124240d44152060104a81100030304039003c05981e001032414244440e0055070b140d40555405045071000c0700c035400e19030440d4150342d103242e90082 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 635591654 1250 635590404 635590411
    0x12140a0b1809060114150d153606080717060c0f070206030a0f1812170c2b020403110108060609220207030c0b010b04030b070c0201020307140a0209 65
    0x201d421100e18124111594422043c0601c101403c2d40c035034a0140c030340c0c80d401100c40c041030150350a503e6407114400d04000d0140b65002c00320712113850a01182075240341041c02c0b180008900c0000c0e40070421112190002c02003104620800e44402010401900c00c001c0b04000301919000144c05504011141d400c1c410060f001c508a02002c21114050011800079580300e10340403619642c0c1e80d111900031600038a100d1030000b1145042030900d020f4641004040421940030b007024040803441a8021660714901e08040101070440f00046943c1c0490300020340021090302d1003100200031200980d48a10b0100c6080111032070f000207013807040082080c8040d03e80364007802e00800300e041000019600c0c0c018001c100307000d1000100121428589800d10034070b1005e80040071543c4100070700f4005c2040c4070031101030724098030040002070251b802030b00300d40840750064500700c015200c0da00b00301c9040780180000d90441c4810b11100020811a400ea0140803180900a1010210030301c103212035454003c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 635592904 1250 635591654 635591689
    0x120306031513060c050403020a2d05100503100b07080403050c03030a0e0f1801121e02180408071a01150c1e06060e012706031212140a0b 60
    0xe20002e515842a00361405501800101c0c902e00200c0e801c5516004aa001943c46242d66200042122400e00040d00e001a0085420111224880d020501d50118800c07a07800458800c1c034460030502ca8005107402030356400074646042c2d6a12aa0700c110b8200300d005407051540000c0820030048104103604888201340c2c055820540c1504026100844900c0b0a902600d83d51404441503a03a60a0000b400030004920091a51f1102031800146c9582c070300c2140c000c43c15800c003100c0407510140340001c60360300801c112495a07030001c8004800f1000381046480c038a003071100c00c0001d407466043c24510014108031131030643c03408100c0080b18452200d40010b0081104040020404001000880c000e080c2c1d51340b9810710f0305203424401441c0c154400d08031042c065001003004004884888020108070750703c00c241c1c09643d12002c003254020b00c8010200f141e113464120300700f4040d1203100c0c40c02140140010f100c0350160000c01074810b0845502e024107079100341c201c6961a2081c2e000c41c001281 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 635594154 1250 635592904 635592943
    0x140f01060f05130213030606231507030507150507140306010f050903031c020309210a03111c05070f2c0607051005010f050d0b060d0302030c12030603 66
    0x61a8601c0a044001d00445015200c450b00d101c2d00d400003501100c244032203110b1500b9800f40e03282070000003080b00d07000d0760703010f44400c0b1102050320480300001102250001c0810035025141c500c40c1009502050303003103052180c1480b009000c03c03194045006450544040480e0514010000400d80c44896044081e4554180203128260342c4c0801e140b001c1384005d0400c6551120303e2070000346140605644410183d500a0060741903100c1900618054400c0b80103d60030a44c03040750b603000070a002203100c1c06040301801a8014240710390040380001c0290403640345840141404c041051401c80182e05442d40c5403010300c0041ca82c81410503151022501d40301c01c18020308000701d09020100000314030400c00403040b00307031550390780011111500e900100301d43c8068080aa0305014050921842e000c1c03000e040e1000409080c49541c21443c00d5001030700203441d565210420180900001c010b40440c4800e03c00501806001c0001c540c03007244054070340307440e4a001c004041c60002d0840e0070350300b04041c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 635595404 1250 635594154 635594159
    0x6070203011b11161202120705060c1b04020903120315060c0d02070b0a05040603091106030906070e040204060c030c1401050c1804090f1203140c0309010c030b0a120503090607140f0106 81
    0x8804025407151b0303411100324007085032070900b09161003442c2d088154806000030f101514003100107480181c241c00c0006114030054240100400c901566016640580002c088051054150402950303c81c0301000303400403a0300003d0201d14150048001d000305d9900c18000c804441c0c0e01007101e40020520403803034501e004511140100a801a8070a81d03003850303110003c03c0d0812240041d103520481015020070f45a00c0c201000654500b010b48410380481c541c82086420f83c1010b008540559059499000810115a4003292001c0750366000f9107640040b01810500141d00b8001c041c050390500905c0782e100c08400c142e05640012180d9001d10680c9003020038400541e003d00000d00c01a00329000c0520f03407803920302c02c1c0d01030000404560314032105041007100350b020b480702560064010f44001c100c00440100180c003210554032440380d2102c0c06640402201c03c840d5040b1009610a0060328244001000807d802d81c22004049505803210306e0401c504000c100f04103580364418030000c0c0b0800f071 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 635596654 1250 635595404 635595419
    0x1003080319110a0e09220c0302100302130807080307032d0906030b09040c03080c1603030206070f03140f0702100f1d150703050403091707050411040e0606070203011b1116 75
    0x4445186c840d0345c2c0040d00c82c45d0024003140301c2484000310b401a2901c0301a29000308020b0082d88903201120013144a400041401100004c1c190305840c8140000c6243c43d0741d84d00c050381c81054514031400d034480d1884050303403540b001504002092405880d2240700130305009000d015105d071820418002c1c0103210030800800d60b0140400122600042e82a0351519010645030a201100300501500086590004200b42d0700003601881030420b9036409080c00883c4604030145d80c889200c10320840549004a06d00446010a070343d04540240110b80d50320b2948a208015114002d080f5840143d403500c2a0850312a80c0841d2440f0080703120240c03621800c0b040c038460710848040c0c4118100366980002404160184d90628054001c104e2691080c800712003c066a800b4035004041c003560400c205010354a0171001039509035000b943c448101c81c0c0e03403c400c2c0411a00204400e0347d00d0340d01ca2000c0003c441e0144841440b180c0c41d5a20300e004130184200c400d143c100200c00e0050390300e10401e0108403a2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 635597904 1250 635596654 635596681
    0x605060d0c140a0203040306200304080a081b09010e010e150405030106060315120c050a03140f0d0c02010e0a030605100312020d09120615060201090b0105091003080319110a0e09 78
    0x708d0788200001540c915111000c1503e4510380d4a00c1031188001060205010b8240044d00d541c0e902d079a24104142d48d500486c002a0f44181800c105605040c000e02d821980a100030b19481d007010b00d440c011201000c0d0015452004101502e15241c500180c113100038202030040030301500c0344d400e003401000d041038503502105106104045801c028200780504010001162038003c107001080701982a45905004c401000160540600c0c1d200340300380d001150302c0104e03600c0030746a665100c03103220101540055a60641c08036030356601815551001c0009146849102c4c02044072500707400c0000d0540c0382940882c28601070300010b66121005009900d41c0c095a030005603100c40300c035405a0702a92034000c0103850000d0b844030040b0316044002c1045541580701c001110b0180e404003081d0703640c80042c00b41d00e48041d900e1440c20703001102c050001c588a0700046801001025080440c0c1038100742c02021038503c5003201c842c660002400300d0440307502c41c0c450b00039400201d82148135420314040040b8074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 635599154 1250 635597904 635597909
    0xa0305030a0b0a0303090639060e0105040311120c120a0318110a0b0306030316032604122c03011e0b091e190605060d0c140a020304 58
    0x200800000015641c1c103854100c085066009030101c0c04082e00c92030301500d03000450050b880060104150800201d000c1e10f40750016250419206000c80323003580456080b11810f000c146c44180d1114003041d0703560400d2290901c40c43c002e0b5203002c108241c3c1e0041d603080c24401c0d0015581401c00740300d0000e600710003042e083c014074108d0300c0c61692204096025006011281460443d00354007803030762020300220140c000071031401251491465030b240ca454041d1800240d5420740c03d40c1c82803081c1710800482d41990a0314034000c1c01e00e5064103d140d00707054580ca01c2c81a20004080c130000c00d0104014260000da03025840b141468100c464200d1000200300040a0b0040510b01d5a0307074010005880a41c8400380140c81242165417101081d0404005442035110590041c1070305000690143c0c80660040340082050003103545a44900300754100b244e0780c002110304016130f240000609aa154001421056000080410401d41048015140e403104201d0f2541203941000b0311035029078080115010b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 635600404 1250 635599154 635599157
    0x10180e06130e0606090a06061202030408091201020a02190b041719030501031428080f071101030501050102012f04080604031806020a2001171311120a03 67
    0x1540d91500007400e1007504100d0a04510700e0000811a0000c01145081c8500002c0c0e5640110f902c0e902140c008962440c411940000c12611301c54650385190780056030001e0160b1403180c105401880058000c2c3d03244419080d0b1070303500244400c0039940620454055440d031004600c26400316132a405c0d50100300400007040d0002d084504607040110001741c882e591a42c203001e00d81d006111501074000c04d420301056820301c00442201d0154600040c206100c40550b0b1144002c2c101e52601c542c1500d04881e00464201e00d040c08503800d109a0003014005c118040c8410104080c8032500260403228103030403a41c11641008907014030002c40b0202d2540c20914006002100300c0c08000e40505409103400c2800c0a005280034403043c10340c0032549244500300c840140b0480e9603600f01c140da59002d00600200b0000d5011255255040c01d455404442c11042c10000c3c0d610704441d0341c141403d102128100d00b913040b86c128841c24082d03d00d1641a00b40029280e44611000c030a000715522461042c0080 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 635601654 1250 635600404 635600429
    0xf0e06150306102f0c0306101a0705031303060e07050918010207020d1212020a021b0409020928091a062718061314120412021018 57
    0x140e072403044042c090002d034001c1c00181301ca224150602c132990015074980041e031041140000c0ca40c03038040381d094041c001352a4004500f6190003510302e102e60202881810600050001201203082880100040c0000410300c4480394114070f0581e0844069002503005940079800602c4035842c0c0c0024181c1080300921503030440300c080c0024501911600c54002d4001084605e00c20401002c004000c44540b059102e16060601c1030042d1004c03401507503071000040e400b154803110350140d001c2e1002800d960242c80825407a41c6034000c0b40c01d90400350f84614251920010400e1000701001d0150f2844040b00303410300120340d180c0c90b0308940055420080c036071549440c02107810380e42c80708103c1c900c4400641d070f5100d403168004071002880c01c007141c2e5580c1081c40400182c140b103c01040091283d1420155060810041e0b03e0b04400071600c40b0482da500e1044249007990020444c01030001002259100c041030140c0e0b105200101003214103960034001c1d100d10301c3d6180e02581c402c20040e140200b8004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 635602904 1250 635601654 635601679
    0x181d0a050a081b03070602180907020c0603130615050109090209010c08280c021903080d0915060311030c01081b031504020a05030702120301050d030e0f03070f0e06150306 75
    0x44420704048032480d00f041c440022200c00300802034010b0540f07080d08881c1d10448034191000e0080121088822100681001c3c0d407000c403a240840196070000c0c1507141d0b0905c50310450307962504444080003102079684c94403404001c00d60340074000b0805401120019414224500c0c0081c000c4050850020314002000c540d041410030880c03240341e0a042d01c07a03040400c1c1104030001602c62554000103070701070840c00d0410400600c100c40480308499000d90018074184004124000070700441108980b900320741419020041410b025590245004a084285d24400a0100740c6003401c1e280603507041c003214804110014a030488003000e641e4036814016601d944904880c1e0404010725100b503882440411960031041d8003030007442c840c1c0c66075021a1000100030502e0611400248545070380169000301031300c00640316803550950118003030a14000c90038210f0000307040104a80020007441d040c400100540003032180010f81049090750110640c401c5004440c4240c4001401035005280c2d03080b40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 635604154 1250 635602904 635602927
    0x1052505150c04030b240904051005090f060a0506310213030506060307030b060d0302160306020717070201020a0201030b0d0209150f37181d0a050a08 66
    0x4000303a03a100c0004240c294508000c003841507400c44d02082d90042005000100f0003c04060b009001400a9074201c2c8010303441c3c402c01c095a03e004008641d68041d0f600d4850002105014481c01002002d019003121721500704481e19104c002825049502e0a040a02c0310795110004101041000c4482c0908000040c800d00303280741413110203961489200281503c0019031010116043e2485041540c2c100d4a8400406540d0310f0b150001502021107280481d5807454038045400303029100780151100400c1c80c1050300003680c2294015500e854001920004001341e0340380c00040102b41229080c140b11940c0c000035034401c02a0b00c001d050650350103d00c0850341c1c40000c8071040a60043c000a00c502d400030b4010352000d129100d040c02a4441e1350b030b0800e249020256440e4111220080c0364000d1405030580080a05254002d012001035090201e4940741c584904103404400140100720403030b1210b004281c0181521040340309800400c1d10030b002445c0400c3d0010180d82082d407098484c200b9625 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 635605404 1250 635604154 635604163
    0xf06010f051b0c120604020a05040b0a0504060b03090c0d050c09100e090d03060504060b0d0b010e03030a050403030f17070e0a15030f06051927050f1501052505 70
    0x31503141070744a000c0c2c0900445800504480759a90990321998010002e8543d04c2ea5403009030307030096002000301028048c90030141e11184000303000034114248660780d080807508440898100161a8000008001c0414800c0020741c00900b0103545003c050b806070b8580b01e403512600241c491007005520042441e2120390b046c0e42c030142c00d0352101e041d0603003400da46140c0e039120f219003020042400c10070005480c0c07a007880740c4400c5580300000c0703500c1c001103403070014020040625000e060100d05581589241c03010805410303c1c400075281d0954941c11414050140c4050380c8040d0200880003002c1e030062080c0b02a0340b03802122900308248a03912280008030202c403150001c240d0900e40700813008516038950051122000c1c403490802c4003540368001d2006160356032480c07000f03c8998003c208195004240b03c02e1920029901141c1040c009400c80000c0e6101074805065043d000d00a10076201d0321000c500b01c5512090822030315280801c0748606d400d901c07404a402d6488a49003680741407050600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 635606654 1250 635605404 635605417
    0x30f040e0a060918020a06090501021209040906020a1112160618153603050a020a0f060b011e08130c03060207060e0f0c09161803031d090f06010f05 65
    0x18140130041c070014104803a41d5040030709911921040000290785800380078508207480040c1d0262290422029903883d1a40c0311b8010b042d000341d6290b540501150b480d10180c11003c2840d501c03803800b004580841c501e1300d0f140407048540f011003080205241c1c4074811405070300607070014020400d507600e800302010004041380003900140341d24001400b0b4400c0b55105840c0d04107626120362654035000c2c21003000c91030103c46903a181001002134000709000d08041d0a0482440c4101d40304458580d03110242403c070000111040c41e01e6601c19615903810031144603240070031500001c241002c3c400d005018020142c00391820419542804080c0281510341002a540110b42950384200d6403034240b00030701007024100389600408004c0c058800c408244c2c03c8200380010310342c512a464009182103185241c2c01c0802c18001094510000c0f01c050304404d20065000c0e881d19640000c0080160141703d4811610500c6109240100208644a006030540200f02843d06031000303508004141ea444c410103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 635607904 1250 635606654 635606669
    0x1721030c030105011d0306070e120703020f090c130306060f05060711061e18040501080321060a05030a030c05010b010c0c030f020d052a0919150f0e04060608030f040e0a06 75
    0x400c44109d03000005540c02c100c3c2680c07156005007801d40d81300e8440c8014007000350301000301802030100b85010384405412404003a80701c2d14200e0700304e00e05021440a58422244103803105070030024001c0c4441040c1c0180001d0f603015151803480d60340e203c00101003800051107541d000c01d880b60f103818400703a6282c440c40c150b40030565030940d01c10038030401c09101c0c40075440780b400c10001040040d8048280c0c1c0c8001c440c940d40e8600032301a07200c103143c1c0d2600109205d4210301d0008000991350342c10030081826a00a0300c13001070030a0389003041c80c251403c0a080078103002d0540321660025203070450040440e90090200c01809880b440013880b003c0074541e02030b1103031040c080724560808c0d102103114030b0f400b00110107448140c07040040c040000780c221034a20003088443c2a907030020f081341d000046007948003945850340e00c3c2c5403441384810f0401608071403103258404081008010300e0784a00c0010b81503401c015401c208001c19603c904c8d200d54014035103130800410104004c0d0506802010207086135 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 635609154 1250 635607904 635607913
    0x70f030b06040b040305190b0c0d142d010510031a040615020d020a02060304060b0a03150c2601030f140129010915181721030c030105011d03 62
    0x40310000152600203000c00d6485024011001891141c0080c1e500081f641c44503501c4103030398404a4440041e0000c003c1d0307428007600c546840301000164035490b4426101403804030301c901c1800039920a5002e903a40000d6042c1c0403240144210f5403420300440e10b40e4400d02d808103d1680141140b544920800a800d41250070b1240110740381c00c1c0e4801c0c075084403201d9822903205910100040384e0f01c60035414042c0d009801000801c020640c903800c10400d050b0003a084441c00c550301e41d40c14114031501d581d443ca42c180d03140f9100e420700b42c5c0100c04048010902c0f0310f5041c0d407909540c5100c141c06043c8801484111806405c40c00c0011000ca2078032240d40103802005035050750b0549841a418103aa0403581c0e201081000340300f580070b44032503000d588060030b00d291141d08101c0b003500d000c10104141c6910690401c400505800352112404041c041c04d8042e00a4440c03902001218505101810070180800d000700300c42c80c1415000d42c0c1c11200c003480c20244802185c2c504d800128900507402c2d406010303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 635610404 1250 635609154 635609159
    0xb0406020d08070309110f010c140c18100603200f04050405130507030b0705090402071b0b040303020d21020307020105041106070309092a0c050709020f03070f030b0604 74
    0x100030810305072248658030780c180180c0d6115401c5048404a81d0014240b040041c01000b8900b0800800f0100800604111511105070745030ba8210803000c4551904980c401040d80f00541001482d0024901c1a441c070400b00d401c00d514102c1480c016401303007404043d40d0b900d106c02074500550228000026014a0301d58652030b04e007041c100343c1e10500520340100c1c00c107000320700030102c0d0000e03003200e0541000280201b503041d42c0d40c001d03050102912070b80c104134052110b10169a960b1005002e403511032003440f800703540c00c000c902a000c201070b030040c0001c61040c00100b000c00e4000c00e4030010f4003401d140c02c030040586424400c2038035084600703000c0128804010095510b40550100780218012000010420212402c1141074810200011f000604088040004040365044041c940306003121060641c00341000ea980803200087c1502c000a25401100040c001d090007003c0103480000c2041d071801d0600790900c0e1840c80043c00000c20084c2d2203140b440260b00c254481d66150000a00140e42d866 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 635611510 1106 635610404 635610407
    0x91e07080601170c190902040905010302130203060a03060b030712030f1e020a06020f0c0102030f04030809030301060807110721020a0b0c0a0b1305100c020d03060503060118060b0406 80
    0x180440c002c20f006c920390002e00301038076160000140301c0d03155004000c401008510303c6507406104200740621740c0c945041030001d9a41241d40070600c0c030210000700c2e00d05001235024100b0000121441420980d1264446100712401d544030b03a00d0040d41c40380055005102a426005640000250000174800b038014145841440310b00130b040105010b581c501360380c8200d440201c174550b0303038040104050300301c0022600f007201e6030015401d660500c08064440d40380035062806100d8608152040d241c410060000130b46001c0141c102c043e14100704802000700c1e1414203d01c503001180c1c0120340518400c06441c0c2c01700d0348100611000010340c842c0c00c100000901510492001200701e100401c100304040c103115180c60100140740010624024103001040707196000b018145001040315a0340000d40506485129000c455102c41110168005015550104d00031403c041000140341d03 = true := by decide +kernel

theorem cover : BRFrame.Cov 635431654 635611510 := by
  have h0 := BRFrame.cov_init 635431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 635431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 635431654 ≤ n) (h2 : n < 635611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
