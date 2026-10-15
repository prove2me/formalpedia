-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4505
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:50:22.273029+00:00
-- url     : https://prove2.me/submissions/38142cd6-a73c-4552-9ccb-dd40d0f0ca83

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 810071942 ≤ n < 810251798 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 810073192 1250 810071942 810071953
    0x90c07020312040e1611060f13050f010f0e03040e070528050307141e0a110109060204051207080d2003030a09150207020a0308031017010501050301050a0c0206060f03 73
    0x1e8001c41c00c1c507002504482d41c1000c0e0142005a20840d41485c80c03840505460041c04084010300f5043c0c6821016240350901c0380725a0018040c1c5640388034804c1803da0060890300e03400081c00b041c40c02405851403030380155041c04103103466001c002043d902030391b00108cc044065101e00d04140c40b030307500c40012000000041e580c081606401c00100808103480d82d10f421341d503494229401013410034010f04800b00d0303803000c1c0240d03c10000908034054201031001645540d03520080010b940c1c0404550401c0d0107036003001c0d010000c2040c42d8000c2c200315202500c2c41e1040c5c044800085031241c0c26070080c000035901001c2155292807082100e4450b003102d0004460b401d41c40b0000c12741c199841115140c4090341c5800e813210410103403181e40d078903158a400d411410b01c08039a000404102d0780d4031024000800120200b484400315039188401480070201524204512505031806400244a82c43c481d500e0b01d00000c00207000c5e4040c0240c0c080c0d45078040c0c002603640d0010441e4001210032001d4052184 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 810074442 1250 810073192 810073213
    0x6010e0306151f05070515040b160908010608010b0a0501030c1d0a0b03090609060f06030c04020d02130f06020c0109050d0f0312181110090b0a030b030102070807030305060f090c070203 81
    0x18400ca080741c001c2c450f07489030b07905c201d01c0c1030092508104111080003c201441048040741c0042401504202112058003a1f941460b0044880b035406030880640340d481e00c4800200854150b0200e100c400707042c1d070030503812a0f40740c0064040700c140c40d80b20300110321241c0b94482c8201411082000d03600008080e005055180e01030b4030300a070021a0480c4283d80050207010181c202081910341c0090031208118151a283e800b2a0700caa15201e9900d02494011580c86509031094043da10202d891003e2600e00340d58078011360103564503500c03850016000b0900c150880d540f0444000b01a29000341210300008003554885082012200381542001040c06c080c210080d414082c51180c540700010072a003040450034011503e00d641c407107591203a585104245005030304140e00e003048510110301c00b611091203041c00d6002e0b10b80d0b1408150f15500c00100071042094003c00f9000345406694100304a40e200d0091240201003044159440702403280010254050200181107040c03000e8203039860a180d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 810075692 1250 810074442 810074479
    0xb0c0304031a06130606050a111005070f1403071d1206040c15090315270305070c050306060d06050a02041706010302040e0313034706010e030615 64
    0x1c000380745003201042c04040c462075203040c01e0f03d810030001c07000c030400901d0f203006000381c61481064140011b00490000c0c201c0303958010b12141c4a89014460300b07014603c0c203a64010114156039001501140c040e0a06c882c24049641c2a42e100d5025030700c6182040b0010502c00d20a2807003503103103651010711032504600c072182c140842030043e440747e0000c02c2480e0a088601c410140c40380212070030086028010004160900d480304500c10380d4440004103807100106440d07181842c500405160f444002d115000c06501c0001009520b01403103100c9039490301d40c000c26484040503076000f0391010912680c80c000c541140d014542041503418010b02c1c0681d01c1e040d660750414400c114004a8002c08010822350030f0a0040860b41e40c80b9601452410000c09800200c110701804085c01a0511601f00e4401e400013007030b40b0810300260941810518001c001220250012500c807004140690b8003240080d4022441400f42007001800b4010658580c2a0810480349000a895000036004c0840d074403400d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 810076942 1250 810075692 810075713
    0x130201170f04240c021b060a08180111071208060904080a082e051201021e0711041407020c030d02070b03190e030309061308040510020c130929010b0c030403 69
    0x4e0194000d000b00c0c041e86420204560340e5080080d025071405c00c12407910590003070328281d021820980461016502c00b81c420b0045c605800c8010542d04005025002c1c030100002c034050f80e100598582043d503a605085c0060200166001084204140440d03400c06000ba4552030b844180000c509440c1c64a003446181620b0704042d0103207201c2c80c103071030070300103818607000400d002451100254900380c101d4003884100101c1d40c040c1001840d0104546040003815140004100380040081c401300381c00c520014800b90050725000b000d441080403410203807c001c10f2403c00c0c5050358001d030860915041d030241d07603540004c1842c140c4c6031030184010700544035886114620780c2c0c0d010046489103800003210b464070784040c00c10b00882c0700442c0f0200004032640c00315800d0b40c000f91241c0c0481403000d1400d030702d0101d41032039159010107400500101c002156210810340c500032203503030b003c1c00450401d44628040003208110b07548420001404004081c1c1c0040040000041c1101e21f0030f60b403a1204520507 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 810078192 1250 810076942 810076961
    0xa0e1c0611040f08012a170a0608010507030b0f010c0c03020901080a0314030105101115010e06101d0405190c03050708241017130201170f0424 63
    0x4181c0450240308104a190004000d000d056008000524400c48182220610f410500022030309031480c0c4c40004e0b21540e444880c0d520040865007090404041d001d001c0c01081c01250440d41c030b00380014001c144a80103008510b20003410246003607103100011101c0e0021140e0682d1010a00c210000040e110210b16030f008210080140041c00b1907032400800c0302a011a60030200c0805000501136659510060152103180c1d0820701c20542c0204a080e060507265140c090300c000341207000041c900da5018a0500c40e0004030341189039620f40c884107644c1d01c503060300140147e4083c190700da8007a0506503c91034000e074125034922207407074801c4240d40580306000020b2000030344401c00d00401680010340c0c1904400d20102c042500c1c500141c210190b03541c0d4a000c54440c40d15040140b1a0714050030a04403a00c030900c1c146d4241d8900385c1000c6004000000040340001c9107040c1100e8280c02250241d80240c074944144000c0d900d843e19584201c440300c00c8042da00180003900440b0b0303040c580c4a0040300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 810079442 1250 810078192 810078221
    0x30301031406072102070c0806100611011823030a0c0b010b03010b071b0503030406030501030219051804081207020a0302060a0e0c060c010902190306110a0e1c06 71
    0x2a0104041001d0924001900030010b00810f480580f24240e01c8410060055030542e03001600c0d00386c2810b0600b0b100d0800e9016a00b907018440600050300440da00200c140c52541d26104e110115030715000d0b00302c80760180c05490030040800000c001981c441001303c0040320143c8080340049010326010f0569001c01044004903202c0200c510420070701c15101c5004000394285070f03042d5850f01c10540c2a520a0301801405c2164168504644d00100509500540009000c03a17442d503840e000080c00400080c0403c1c0d05c42e802c0703408400e4000c01240c402c0c409803180640324030780c404441800075a60810182c0101c44100c07061060141c0c926042d80340c00d01c20040c50340104400076660a000e0b05160000d0f01c01401c060400408402c91100010500161482079078000d55074007410038070a0040010500007548000c001c040070035403002089481c01900d001d25420003110b860304510304107078401d0003110302c0440c001540c2c0041300d14003244070300d0044189889000035103040750f540008540400c44205c21 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 810080692 1250 810079442 810079463
    0x12231009060b03040f1e230c0a03030f050a020309130c0f0309120c0305070605151201020903060420090910180209011a07170715140601120e03030103 66
    0x2910005000c1e610041c5080c88500b0303c0c60410f41c070b516001d6002d822001e0941032042800c02c00703544851030442c207615013014107814800520900d4680701e40101865880600c074070f000301d10061514840c05000c0305d92644030f480c01825400e1041d40d1640281100100750300050084410381e80714281e0b079840d0082c07030721400505081400c40c06080400310500701c5081503d000c0c00e400005a054040320600d1029083c0f140082d4410300d41144c0610490100415003410b001c2405006a180302c14503000e403008440741c4400c43c41d11b1051030700701e0281c14407541d49a4008404103020641c2545d420014003030302d1003a001401150702c00304a08031016104d060456010308200400201244250815807184c440d00082960751900007030b01c1000180500060b0700441d415110441c42100211034543d5407209941c07155038140d111030306407900481415100103030540900c00d4146110720842d5410b508035002254180c03994001150103c0d004186480103a0703072100108881e0b0310800241d4002c0d403081c0c60040 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 810081942 1250 810080692 810080699
    0x230118090905100c0503040201090b090a1a300406050c07061b1404050310020a030902090a0605151908070201023f1b090a030204060b2701122310 64
    0x142210310130a8544100031040c001d010050707900c8006141100d0384500110780700c00105000416817000c99005008480b4003807410f403840c000700b03c080e010030400f16412194141e4021040d0694960f15503d041c50ba058120000b000071700c2d26809150081005044241820140d40d2864101c030354094980c4240012071098880065100c03510100f5013030040105401d10b440d18000c2a81e5190591040312100e03004610308128a101b0303170003003080640041c060322944c02c0484c8194001d14203406514041c00107207004100710b4065904456482c00b11608950f150380c0f0071a021a0481000b40250045540070082c140301e21304c0c98041d2030b046036074011480c4146c400540702e40000820314107842d620048410304100d170800c42d250151a0150781e9094032541d4040b00c0740081e642c40300d41c0d08000e5019107840d00102d24481400050701d0903400e00342480700d49a40c0b40b9440400400900910b5000480d041c0018000d00d015030000350501e02c10304c2c8020b00c035150786074040381051802c64580750305104606041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 810083192 1250 810081942 810081973
    0x80409090b061c15110f1815040306150f0f08060a14010e04030e04060b12090105151512090a0302070f0e07080408090a140a230118090905 61
    0x2150031070b40888040c0d0300d6601c64902c82419201c00c4502501200340c03140c40103821001900034604103440080b590340c1c1c981069510009035003000001e020ba19a0b0343e10030f00740742d0034800309107a08496408103483c18940365a94480282c40613010a2403001552000068000c0d85051140701030810000a0b000081c146080607241080080c0743e16180c0e41800058400a00140d90407810340b011412102280d55a50400341c815000c04507180380c1007072a000000070300050500143c01507210f08850030585403600101c6909031402540c09441c01e030181c00114880e858141c100400b2007445091031400c01c0d0108020b00c0342c08104482e01002c680241c00b0210405d070b810b22580300503016601041c80650f04250503a454400d004101c0740034070000b0000b25007404050010340744484802040c21180685842119000201c1403003014083c0b084890040f03003407408a2000c07915000c00402c6454070050704001141d010b000e001040000c814104000f29003148039000703002a00f4042c0d03004203c1901c03402c1c01c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 810084442 1250 810083192 810083213
    0x1020a170d1419021b0f0c09060619120e030c0c1807090b09060702030109060f0608032805133b19380103020405030303041b0308040909 60
    0xc82c44000c1c07403501045042184030603003018103d0200c1005840c3c16840500c10b400003076a42002241d44074441461102a00004011041140c262440c61007505c4240904c109070042050300020b800400c1004400c107881041c0286504100760b60100c1c098400341811810365100200c001c2898000c4105030301c95080452145001040c10b4042884900e0b0141006190182a00842e0410036000500070896503411003640c15264008000300428192890030a0090021600b840d0b903180c2000030000f5003c0000c000c0c3e50814030340c1011180c980740103002d00100b80c4e1140d415001030006c00e0100e04400c0c10720290b64000741c803440480840f00d41c0d4140c0a09125203902a14880c08114040801038007004040b0282d00510010402c00382c0c040c3d03404840000e03200c1c0e803056039007012441c484183d018188031018109100300d140c0b0721511011000044050388101e00805416a00401c04140004c100c0c080003c01c407062011480714080d00c3c0c0d40e030102582e100d40d018101503511038002405011140e00d5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 810085692 1250 810084442 810084461
    0x100c0c09110d061a0a0e0307051302031605040605070305070c0b0f1c061d09070801021819120f06021611090601030c020d0302070302071e06090801050705070b0601020a170d 76
    0x51414400e4001c60b10b504e000e00c24403140004020383c04000c0e40c1c0d03a813010410f082c080c0c0070052101d401c91010000600c000c1d0421202410012103140000b290f140c02031048906070b41203a607070903103460015241542c0a81c07001760102c0e240d840401e4001052000754028040001c00b00c038816036541440e41684454912031100d40550b40d00d0310760100400d20114900742c0150f200c0c1206030104d5640c81e0107032030401c01c40b0f90012f80e16500000c1d84011951a4940548200ca8100c0c1c124604150409040b04001040e00440191000c0000000c02103070129003841e0465100c0e001c00752520b550951411800ea248003401c907035417180380c082c400b00c0d45802e600550b4400000c0c42c00304150035805d84000d641c3d8000f200c0032800c1c568001000401d06100b480048054007614900300403800c2444030003d46000c0601c030b20400076802d0240884c070040103018090042206544203802c0c1038154030b41075002c800c090304031410761099900f0800000c05501a00d50503600e04196142c8965207016040d040e03a10000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 810086942 1250 810085692 810085709
    0x3013c0609090b090423070806060a08120318030c0d020115090c0f1101060509090f01050c0c030406120f0f0b090106020109050a06151d01140a05100c0c09110d06 71
    0x103110403925100c0c01c281e160311540121b00318216009441003103103081120403140350217015182c400b2411420001e031041c0611002d54a9611a80e0b480c144980c80350000d90070241c5840003007022503c5a0300607a00003008607083e1050317034501501401e14510f851078616810740580d45070b0b021006035030551100c040041014440a0142c1c03068124000c101c1c40e5400c2115007070100c080ca5404c800c1e1403d5020760058840a807041c1582c2c11f107411001d43d50444020076481035820100000c01280c150000d403844044210019030500b8180802601e5401c10803c002e91469a10001403480070141d010742d0b4042040e4050006120450a09025032603c058110005581c1000d42d6240041c60001700c0c1c3c001035400003000038080c49010b452006104041e4000041743c1d0100d025681c100c50400001812240c160412103118411030f000e210a1074580d2240680c0040148c211400060040c1d030030031841e030b02c64100c10030f51944901a0b0800c49a5410040c0608800401c6c010a15443c91040101030004074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 810088192 1250 810086942 810086951
    0x150f0e0303040312110a091502030a0f0f022406031218010e030a0c06050a030f0b1818010c1d0301060308220e070c0506100b03013c060909 61
    0x14100654920002d44000d00308442880d1500b4800d15a5101a40405105044e240d480003442001020350003540500325007149030310305074a01d440c0004110307800b2005035210341034864811a4181c41c540300c540c1d01c540030340c080c0f150f11150500c00303128020349681a801e035203220ba0030071109040c900300403400a20012101001400f000a40c00c441c0c030746500c4402d02c0c0c50f0700d5500b41040800e080a8021782d0082115161100110b0b642c0d4206028220600c00d0b031b5030801420f600c000d0345038241c503141d081154006020b03047c110002548541680ea0000c02003e00c00c4034042c8807070501d800c6815102050000444c072032000d074640e10400b24040341c1c82c4d404800a0202d0b900715180c0c01070a01c01c0002d856074244188006200048685005d0f10040c40d01080e100002d01d80b48402400c05090700340111000d0060000152651a8903007100040e079111101550843c0c1c00c00b0036000f520800da1600c0140181569041104504d1090710301c1c084828441340e0744282490040054040b650075088500c0c0380d81031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 810089442 1250 810088192 810088211
    0x303110c032d0f0f06190203040308061002011d030406232a0d030203010e090307030806011b150c080702030f0a08040c120c030201020c060c0304090b0a080a150f 71
    0xb2104218080d940a403210400c482c1200d0300149040000701a0780d03894028458880510400440c229102c0c1c00d4003d41c1c5143c0c900303442101800c901c0100d0300100800e031580e0100c0c800342014a80f480343c1a00e18000001c0d803890000080c24001d880001c0d0815a600018007400a0f55201038100c801c00b180658104802c0c0410b01d03500d940e07001d6220b40b4440042116196524034a50b0741690316001e80b48029110a1824620010080d41c024080d08004070b6141000c41e0106100004961126815645061075501c07031000440f0880c139071045c000507420040f801140400e0744e500d015a4054001000090507484408002d08504c01c0207024600350f420500000c0d0a1940d510100d520314603240c07030451010303500e0b4600496000ca80350404229500c1020240040101d81d07003503802500c1c001d03000c803440c3c00c1c089010001075106000380740d010703504144820461070005802040c81e024005140907040b6131241c03112441d0600d40c80c02610102c140400c40d0800c152580303d16140301e03001910038452840c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 810090692 1250 810089442 810089473
    0x705131520100c0207030f0209091516030b0f01020d030e03130e040c08010501030c060f02011d0102210606041a04050414010e070903020d11041515020c09010305070509150a0303110c03 81
    0x6102c00203800b42e09d0a00006802075814006008903c500312540041410304000c6034201d5455041c3c51008240b4000020300549003210b20038181c080164001d1600d984640e1048020f07003100117a4514600c01403042c00d81c2c107001481c081016001030350040c452490103007002500d0000e541d0120001d82d15000044c00400c070000c01c0c0b44240c0b90329040091343c804030810100e0061011008540c4030101c0300509500700c1d001900182030034040061400020700c0c01400314070700740e00f040e00c3c019072002e0104010000c28540134131b081d802c64040d8080e28106603960f0081010740d0020511910300d144200014080c0c401ba41224980058162811041803401c540c0030030006904010081e01c540c00000000440c0e03555038011030202c07504500c15103006a55034403c5200b586000d9403110150141c03040390150b03410f001d020f1904880c0c003d40240206460407044c09030140c00a821610703120b050400140c480e4803461085001188203950b0700000c1d5a1003456103090041c003600041c80707908046000c080c10300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 810091942 1250 810090692 810090713
    0xf05010b1207110a050a1103100b1e04020d06030605100b07151a100306060e1e060313060603050307031116030204050601110718050705131520100c020703 68
    0x10018100042c101c0b400348401e034034100001341c0080070303803041d4251002000000301301d040743d00c001a411981804401c25070030342601d03e2150460f070084611041c03004298400756600c50441c1010708010314005c819198103080d03400940003a00c076a41c403032081c0001107883c01c3c50a001003c002011038105251903468400180004181111680d01d035504064040c03581c12040040300c00c010100800d16041d110060080d0085125031400320b6104084507503103080c1100340000d0101d0024041c0b01c0030302000d0420100d80c001034100e811f118007400d04400003030380b2071240601a6000700003c54965000d885c004000e8420003403071003003d4000250b034030a0403010500440503a5070440f4049103d070342d1200103c4240440064004480c880d050340051107001c00c488400c0040d1900300207205036a1998410b07030720392043c010140032010440f0810058106c0d0400700000303041140c034200c4c184003207090b003501840d505c1a0524503d5007054480c1c041c00f804500c07907000e600342580054407903545143ca80f100c001 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 810093192 1250 810091942 810091951
    0x302030711180403080402040b0a0501090e0c09030304140a12020d0605280b0a0506090d0303021e0d0c0806040b0f012604050706080705030c03010605070c0b0307030f05010b12 77
    0x3510110154046503039402484410844984144082d40c0b510f428020f00014080d14280d000381d190107c3c0c00060b051001030f00040d19010303101c44040c2450455842042d203001131880f44001814000541d0076682400200024600e407032444042c0d03200e00e0100104000160300401c91004103880107001600c610314442d0025030040c40000b21962040c0004070720101c0010b00d4510404550702c0060014419400f412205800b40c44260400f611101880101e00c220b16901d40d001841905410020340b1940081000c0c40503800d403c90010326aa51100558108025130301d0b150b40c65600810f44075a2158045038490421070f0140018040000455000b034100c558440c100520300d400e444000701843d2400440c0c5103808034480da10715090411644403a520700404001501c4000450300081c42601a03a004012000005d440c592070701a040d1101d9105140880f400f104d03041d0000740391080314024504c92000fa840c0459580c0304072a15400300e40d0141c00c0303c181c3d04010b000e44007a031540d00040c030350301 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 810094442 1250 810093192 810093203
    0x80d0c1101020a020a0f03051002030405060c030406140a091101090f05010f05040b0c1f050702060703050403020a0c060305010f05150706090311030c07230906131409030306030c0a0303020307 84
    0x500c00d16100407810a90300c5000a5040311503890300140650244030400f044034000c0096aa02840c41e4070301900781e10064038041e0856101c08003080c0034001c61002580c009104d0308000802c03454a094900001c00200d07811000180e41d81c88a00500001403007030b0100b00340900e0007040c0c0604100c46404c0c813052030300840341005208214401c01501400c200da01826644101644407003043c1d002070f90b2007518004014290b03100c00d0041c100b802490081c1c6008003003940103007195a845260850003450000d0040e81180310b145241e40115141d0440c40000c0c000c181c0e00400c2c41c1d070400a208507140c806a000d02d01a5940310010030401402c00c00341c0b0342d0305500c15008241c540d80c509088a43d0704001070f11180c0c50000141001d06448002114802c46a19042410345102d8647c0d4502402e803a0004041d00001c8000c0060340ca0310300421100516070340102c0002d0104010700c00310816000c21541e1580551002041c40120302d01000300788200002112251a0ba900b1954000e4403800b461000500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 810095692 1250 810094442 810094463
    0x9040c031427010e01150e011d130807030c0b0610120e0c03030a3212190f05010e010509040c170c090901090c0e15132003090601080d0c 60
    0x42d40120b007404541c145445a0003881800005441d1034000c00621070356004800d0000c0c0c1c00600044c1801a15040303442c07554400c00c410108422141c2c1c07a00c40100708107840070010404900081e8803802802c3c1d058040d42d240c805c0c0900c2803401032030701e00015245a01c1080101c0234002026400b403022186504111700105450240f9403500303180c4914490250360500000c50032111080e0b01c1a6400d51130108c151084181c036803c08040d0260a041d80c0504104100801581c2c5501c80c05800070368100001d0202e12113542c5e0300281c032404440181004182c9140c44000400403a05041e0b84107000d80720072113500e005801c09079104440c0f5006c030311030180400b03803d80060b1035100302402448600301c40540300c4225850710f5482c01d8000c081c809000c59100101c002c1c081604840744240c14440d1051020803404003000000700300140045094001800380c03500901c2d4003859840341d2000c1083e804408960b02c0b41401812a41004016044006240d10014016400380d5100e1017018550303400c4910700c0e8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 810096942 1250 810095692 810095731
    0x31b050909180c0f0d02030f2401030f081815270306011e080a0c0e0a0902010f030902040b030106080a020108130b060d02040906151d01081e0f0a0809040c0314 70
    0x442050740110081d5040c000c25407121314800000c5603004c00b01210271410181c0001111048220013801e00016004000060400d000203016a009001034030322503101500d0044910001f9800d04103003459400c0c00080401d89940c0450b50170707120b01c0c2e10036503015500c603928040004039a40d800140304024240501d815220503460040f8201005007035402c0548514640c1801c4c542c820324024454501c10482200004060300c050b44102e0340c0b0741d6816500c43c56018180b00b0110060075616005a90160380e6610790041580d0174401c1c1d00080054802401080e6241d00024228040090444000710301c0500311800081c4260905640601e0440b2600910459030000c100100000e102c0208602c3c03070056241b4401545459090464150804001c03280d580c03407074100d161090a220b1b92505074061010304840c801d15407011440e9a403454100c48103242d085604516003003c40074150742c09400000c6000482c149070040c00d00648150405203d240c070b40202c040c13806200104180c00e40c0b4822810138 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 810098192 1250 810096942 810096949
    0x110f120705040305030a1d03030c0703060b0a0f08100506010c0b0609040807350403030504050906120601061d0405130f031e050c070e06030319031b050909180c0f 71
    0xe0b0043c44d006001c0782e880d41e00d440d001a01680d85d4000c8812000c40b40103000304207150020484000740140d00162030315600d1941c6007001303400a6948154407540c0030501180811244580c00004c0940c0c50080203105c1003a034610303044a2016004504002d180d002080100d080c0390002600080e0540d00b0502d15076490034a215140941d89e4010001003503003590502c0c004540303034490070002071582640f0540000450380c06140c49548001070101d038017408204102e180c03120820340c2c407210240109000d440c3d4680300310300b032407000d80000010841a940d000d0380d50380040d601280521069808000508001c0f0600888070213600005004c2c248003c0c142042510903a4515114003a801508040003040d00c0c0150a54215110300500c602c940d2000041c040122413801d8001d400242c040c0d441c0007402d5001211a848540607481410746401422000b02c043e052104054041d07690783e140c950f00510104545150041c0c00309069819999a041e200c59011803810700500046410107007054481010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 810099442 1250 810098192 810098197
    0x9140c1f0e1c0c09152102060c0d0206090c01120b0d02120d0e0906010903031b12030209040b0102120405010309060f0501140910082a1002030c01110f120705 69
    0x2101d81121440c81c0ca41440003040c440303210428403e09540d0319281c2c90300390748004c031100790440440140c40100c04000342d80e60441142e02c0c59654550050400c9001c2c1c002c9080d0398031921440300315a0100c442886103e50600006070000d906402500c203090524000801000c001d07006400c02c03541d1102820102da90312464504055409002203040001e00411140ca80400e910f1000110300030f400c085c181072509010161198605840d030f521054103544080704d5000e207142c3d200141c580c000c0030403000306140e200b1a1095002954000d0b0355118460140002d030380c0c60352400390543d481101b85854280c00281594240c0d0300c2841d001544c02c03032500740080034011100090011901e8000081102c80c0f040750f000201207000d44010704291202d500000214a2030300c00c822442c3c0001c1407641781a00449040c1d210004c010398807180301010340002644888440315034001590000401d251104401c0c003422202c1e01c100c10445040414018001e41e1a00c5407040d107110050400c00002c99a0303004506 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 810100692 1250 810099442 810099467
    0x8060c04031a07260a060b07020a1724060f03033604061202010e0312030105060a09080f060402040e151305031e030a060b25050f0d0309140c1f 63
    0xc101140105400d0321013000805542000f82d040c101000802c05550090071582d0b8264050036000b0880d29144134481b0b04007096410040354091540c00d0f0320300b080042c01c0e1342813400e00d1440c1c130142800c08100300318406101c0300c03900d80a500144040108140394441d6204a40304202c000d400c0d41c0c40c03104042900ba40303880003a43c1e0280c5446004101c4080d46100e2a028078402e1320b4495407205010109070b41d0f00880d180c0c1c0344080408000510941c05e040b40548031401c01c6d81059500c060f1105406410458000c1c4207400d550302250801041d8905801044031260040c000350001c0c1b10050651641444000e0141441400b42e12841007041402c00407120b004114588845800300807041c816813a60054a031401410700b046070100d4000c0b103000032202c40d201c280d00307500c50b4101d005000d4410413014080c1980d0343d00401c1000f00c2cac0c00700b0a2040c10303083c500c80d41d000a452681803610241081c0030300d42010306030b0f001c040c0320310880d1541200340290841610301030107111041601207607070890180 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 810101942 1250 810100692 810100727
    0x9060d050a020f010e062d04120305130302040e0331050105130e16020f0105010518060d0b070201320403080901020f0412020102061e01050f01020307170408060c04031a07 75
    0x16050107d29000003600041381c071b8881c1c0c1c4888054402d8490290340c01640107114510300242e0400d4000b034000c02c0100190007841c6803184079585d4030703000901102c3c00f40400c2155a0800907452440c4c245103010740c42c8041450460494900880000f06922401030080710f040c0400014101d0101110081709030003011003502c1507040303140003a13407494401212081c035800744c4140011040c4901041c0600c506841d80588006101c522002001669150181c000e070f40000c41d140d402e4000c40e02c0707407002c2442420076800215410030340c00d241108249500a2101844230800d03400908000c200201315002505071a02088944501440e01c2c0244109004500801000140051040514614441844d00036000d40d006075454104981c03401e001162020020f00006005003d540b61020004036a645d0600c11a070a01400eaa14000c801b001000c14014814010400f04101201000388a901c040854100e6040c9803a40c0d480001c40225407030311549110180300061109442000c20340200318040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 810103192 1250 810101942 810101947
    0x9030a020a08010e0d09031e030309060c08180106080618031201030f030f030e1e010204030c0906050418121211071a010b0a0507020d081c050609060d050a020f010e06 73
    0x1407590500070000c0c81907400150280011802c005c038060b5408004498000681c0041050f00c80003520602c204008120245980e858020300840c8142c45408a000d40f80c0d19440e0250815030401d0b001c0c0c190644001e801681007030014080c801002c00c0c1c50780c100d010141c000705047c1e0000001405d50003120019281844030030000400d03c98010544040c0074000c2d00d54000c40070030410110f058031100382d01646980e03c03092442c40b01c0c168102202d1a9011b10400060a143d16031303848000059595101e56450307600d505041c0006e251030702c100d03c0c0c1d1031581d003040c0315a071450b50b803443d40c50504420140c0500544103607542008080d60060b004856400023030035038420740c500e001303540b11410700140340c44001d458001080f015030010881e03551030025218a07040c40c441e5801c0082c000d44544048414000c140b202500c0301c99205054134144085c800041814a80b4005020b82e2030030080c0340720b10400d014901107021031400700b0a0003088c1d8043d1221603141e4009001a82c540c40703589806500300d80300 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 810104442 1250 810103192 810103199
    0x51e0906070501060e0c0c0a150e010f050907061814130c0c12090803070f080408030316120204030803060d0c0e150306130201051c11072a0806070509030a020a 70
    0x6602800684081c0440d039145c60b155009100748038041c81a01040350751060804038042090900c01e500006140ca00c00b040307085045400d40e0954090911069a82d61600184850b01905101c0c0720098241480c003500320445171500b8038000170280c030441c100d86003035602d003580c0d540311030104068042c2500002c1c0041b58051078000d100d0008404143e40c510313801c040201015126800c0c031000c8a4007040118180007898a0b078130980660705030b08540d00c540c03c00c40062071400174030245d44110100c0321907090b41c400f0a01e0207440c00601505a40160344100030510009600c007040ea0382140f000d45c1c4004500703e02349440b80c8043c3e0341c0c0c0c00001583e00741c5030030040686660721072180a040158140c8102e42c07140205001804088031000740030074400d1003112030004040841c400038100e0084003103080c0e0203001d010341c2c4961140005588400150b410002d040014403042019030740040c001403999858004180d44819015210004020000076204102d680030071111a178660020040c4e40201e54 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 810105692 1250 810104442 810104453
    0x20c0d15050c210412110c0d030905031204050109032d08030613050412030507090f06081b03131410020f0a020712120806010c0b040309080c03010903051e090607 71
    0x20742c0d664104034400c0181c446150f00c070064540101c0c0c0c010f0a0030712240d00458141d0300514446a060fa0034464440d446296030340d41c1c0344400d8500d001e074803040805c40c00c00341850f04001c0c021050f0800800c0c00c0200300540d0340e009155004aa2308050000020034804144000c02d010702031040e1503120f8041402d8041c0042c7c40002e40c02a501102c9040481620300855030990300122000381403480404002d9001d03500a400042d44005180344c80190240c0303403d1394a1640400790010000140400100815040c0000004025885070000c41d415031030905028041040c9400c1c00a101c0b0000c1e01c3c1490745101c0820203142600009841951074100c0c075132000c14a600000340080c0107209000d4000348500310f4032031020380c0752f421800c092010031540c5426520100050102d80c1000040182840422902c002c910b0040f482503494103202d41c50041454500018400020321a0345485c1c1c0b61400260010f046402c46d40340004a0303a0018180600381030240140b000b0359800200000e0040c08114 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 810106942 1250 810105692 810105697
    0xf020d061415190303050d110c030c0a030e180a090804090218040507080402151c0203040516080f0a030e0607020d030c0b01091e1d011d100c020c0d15050c 68
    0x100fa40c440c1100c0c565070b200041d00070960b00c03016001c80c004000150b10800300e80c0105600080070300d0f4842c0b910020159461031540104101040c0750030180f90442090741c403011f4400d0030101202c0c805100b2400503000001b864005c0c0030b454040307650701035800801160360b050b40c0040040c042c0031521040d0124401e440016541901803240346084005070f50540265901401150060141030300c98038100f0300404240c0c008004100900b40f00841c000100c5074a000551241c1d110300702820049440b010001c4400d20290441d02c5590424410701c40f000c0000681e11032280d81600d0495410b001100c003282151003090742c0a50801245a072030381c02c1c950000341c4031a90621415107104182e0340c40c11008101c4000c0e14410b0301a0b003078103195003209080ca03001241d144040c4c4805c10002c0080b07000304c60855080d00c441003050010021070244010042c0081030552440543c240180303d10008000e4480308140300d800c2c8154010312081e01448800520320581c0c6280321410091030611003510301e61038 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 810108192 1250 810106942 810106981
    0x10e0a080105010609050102060919080a03060510110d0306080c040207020a1a0a080a09050705011d090f180a0f0b0403050c010c081005030a033002072a030f020d0614 73
    0x510550011a00c0c02100180141c03e08610100c80d003030bc41815a1080c0940c0d000c40075100c1003540703425000c42c00f603841100180f040c0305192101c84055070000c0c1507600b410144003105051510b040d81c1006107400c04140040710480440d401660b40d00e003440010b00c1000c2c035070007007440020190b545080c080d10b40002800e072120700f0b807205500c581e2000743d0801550136070240100650464001000954050700031160301e101c00c1d809102d80300081c1e0011414540c0100c404c04001a200700c1406426551484504c03903c0d0401e0b0b000c0c0900c0e0300300740c45444000154100041c2110007400000301414442c405a41c1e03180c2c1d45500038041e000a000000b4146082922285054010f00f0000501440c00190703070303440d8542c15105c03040f02c0c824400c0c0038400310301341c0d00714018000920245102480b440d4401480405c1c81149042e04079240e007500c61104140801d0340c940d10011074041400440c940a5006101550484031802d003035140745441c101034150020701a41d8105a1024805221030b40c0d80f018003138 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 810109442 1250 810108192 810108197
    0x220b09210a02060a030b03010e07091514060306030f0a05030405040b0f0d12020102190306212d06290a1a090a12030807080901090c05010e0a0801050106090501 70
    0xe1046030110340c24144100036018885522440344000181842c03070103401040003a050001e81504201c01090a4030001c800007071280e04494818042d8051078407a03221a5011403040300841030602d108450304000320000c40e84600e401100080d4550740c00c00041000320804070680704d5a894070301c0e08580d0390300540070781c40c407490800c642c0b2229410001c2c1c0c0300c800300100030080300a9803100d440340d543c00960901c4800855400308401040f0894000503204941e41c84d0360300140c0a4078180005111050300c100f110004500240108c002c90001421426040d119000703002c6952401941c8190144070050010021402c00b0030440342c8041d50710b00015001c0706140141c8040c03828400704000145107028014100718102d030382001c103027400c0c0090184190040d144640315030316100c0e401d81000f540041100060101000c00c900140d02680a84d046040000244201c0000303582d030414040032130103004c1c10082c458501071140d54a801040e402082c3e540020001541c6440c0c0c000c192035824082d1502 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 810110692 1250 810109442 810109459
    0x18050607060b06123c040f0b0118050612030a12060f0f03060f0c0207150504050d06051006020102090f01050f1209070501020c0306100b131d0109060b0901020a020402220b09 76
    0x6422464905418178240078070401a000850341130f00f90315000003500590b9001440e000010000f003142c003020b4043c00b41094286010045401e03000d05540d80100150301404020702600c560b1140001130321380706c08440c10260342c02c007000403d0324001c010b00c1e801a40b070020400300019240030720882d0001601d001c6c60342400b060004110030000d031011b5100c40303001a80300d10030400103544138550034040304185250051400d59544001406106c1160041d5178507a52541807142d00036440c03207180c009040c4d60000b90300705050880081d41484142c19a5030600c1070003d11ba070031202060044a406010800e00b180203070803c4010965110650702800e8094400c0051144241c0750001d03002d840b840480f0054030038141441d02d50a40c035003155510b001582c0c40321902003030041c20030205000ca40c00640815071550314145080303003514082e0344100c4200c00100b05502032a41d01140301e0b000e01d6015227000d6510300140c0101030007803401c683d5103104071f1007200c4049800400e020081088400441d0141d0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 810111942 1250 810110692 810110731
    0x106030207020114090f0f0102030d05150109050a0b0409020a050d0906050f0a0908030a0b04020c0f24071d1302040303020309090901020301080a0f060225020a0618050607060b0612 79
    0x51080c0544554454404881900c1c54541f000c1500c14500b4188190384c1807415190004003a00d06c156803001242d810b2100204a03541d10004080c01041c084a0240c1880e24020a44100b44500d01400c2c5030305400003060389003180944101c80d207410311000100015a40da06042d802807106460410b00340c0340700c20110b400f4100901801031319980140106241d502e03100480001404945801c1390461340038000c01d00703110003d0090400c80c002c0c85010700070140301d0900d6419900c400c4450307220301c151490f007400a450ba20181106141655041c103007481885031000034040c44d001d500e14800c0c607000107404030030507601001800c868030050b82c00b1078164540d42d40c0b003400d03130100740500c900b6a170141d1500b40200d441080ca028005014600051810f60b030744001200741100d01c0f041000c100c6202d08203208604020050600410251522600ca80306d080c241c03c0c0407004c244101c2c2d1192801244050074800c0aa0003140300880013400726541c0d05000344108011081110a461203100c80d40d07109 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 810113192 1250 810111942 810111977
    0x6120b0a031e0312050705120613181202061009090507080708070837060f0615080a060f060f09090606020a17040e01030807080d0603060231090519020301060302070201 74
    0xc80c01b402040e11850f00345581302200340b00e05007004200a9002c0040c11001080d00400d200b4030312404590005002e113042c8500304801d58801d0481c0c0c0b082103520100c20094036465100d034040c2525016180450000308174206585404801d41003c3e545000d500c2e00060031050001e080e104441d4400240e9a4501018030300d03075421046c0000b01d0310382110f50b1001c3c0000844010341010664412500003414101c450112411110f030b941008100a1702c0d90303000d61803c2c0e0410b0120764020f010003000c1c030030b9500308203a134442902207100d03c1003800401c011809155009002031400340c50703449000c0022580d01c800007035a034003140e4800d40d01080c40020807409844214115415210351900000040c0d1030b5070b84104055006d03c005031070340302c024849a036508195001e103000560182c0009601c6004d51001aa5504600046203108460740040103030461010080b0504072050040002803a5030740f030b08030314459041c0070052000b891000001046454040d400380040f14000c3c0ea5401e28003006940c803 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 810114442 1250 810113192 810113201
    0x5060a06081506030d05130b0a0504062c01050c0c0414010509010b0f0a1b0b100311120601031205040312080406150b03150103020903160305010e0102030106120b0a031e0312 76
    0x344d00b5400054103040200d00410042840807071207182c00c00c102d5074940840360316402050b250760004000040810090f54482c1e20340c841c01d0761101121903002d00039031801101042c0c03424510f050003004a04c2048545c400d21848002900242060140e10100f03c04e03019200b000b4041d040c8181e08040000c1408819881601d51010402402e2485c000005105684a900e07544140304041031400350000000c02ca00e1415004180c0c190f50141c401e400c618100c0c29040c00800443e006620b2078072a00d086001c00503030281103c0d008891000c0b01d4103c0c075000c840e41d119540010349000d2402125129150f4040280c42c8514007d40c0104030740803d2800c02c0c1600c00c51803150188880060001c103040c54a003024100da00c90050600518101944011034109900d24a109140c500c000303800701f0500c002070203054a00140100214550360401c0000313001c04510f8a042c10041d655a0341081d01c5440d061041c5010b56003110703c61135044551081e40005a164810450010341650341c03105006045018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 810115692 1250 810114442 810114451
    0xf260f090d0531031401110f070219090509031207020d301a041410030b04110306151c0b07050c0106050a090905062d0a0905060a060815 60
    0x80715498640d4001581d40403080a403010f458280207421000300700c1007142c0410740114801c4844d02c0305c5c01a0a02d025007115814400c1035083d8070204241c041c264008003c5442e040e9049404c002d0600c2c1c115901c00b40c0c01070940100c00341c1351414083c0900064000007a100c0000301c940040c81c0da6490b500101e03240c00c04901c0703ea02084149680c200000085d0700681c00c1a01080e5180600b0072504000700305690364003800007a64000600761500c039040c5070150307000003441c0a00b422154107001402c40fa54030094030014041001903030228003000040c3c2031242265000a003142c032242400d440e0b20401d80042020a441032075182c0300304034030110180311207a5040e00441c0101c100d0340c03070350800e460580c0141e0310fa030b025560b40da01c08a40e40e030b103c0d42080060a00034000044100305458071501d4100003800410b0301100024122404001c2945141100d04100c0c4030816562642d0182202a00400c04014210701905007000301c8041d041d8090001ca4000c03500b03d07862400102c0d25100a80e10994 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 810116942 1250 810115692 810115697
    0xf0717300408030a2903070501020a0c0501140f0a09060e0301090c0303080702160e090f06100b0a03020c0307060b0a090b010c0f0c081212070914010f260f090d 70
    0xd000c0b0721280302541e4403155945000c50070014400700c9803032210382550407904c42140a060100c0303600f0b04102c0c0d034001c1c10080c002007031208180c2d11561b10401c4188681d5040090000d8210703481c0781d2510a0380c0c800381a00d02e6440e16001103090190042c5e129006030000070b4650043d148032032405001d445102c0380c00c038841424840c2180c13411102c81c18010704240940c46148210f4030305d50710000c840300047c5180600c00301d09003018085d00b420b0072403030008009158441e2042c05044000305600a049423251300e07034903075030f081d0200040e40030740103035510110103000c041115018070002c0e802404c0401d0b07084429420f40f54648c0c4800342190700c401d4140d400a11410f00d07a50000d0f1450a550341c096004080500140d41d8903080300d0319008141020464110001c2a41c43c00130054143d4903801140c14100030303c00c10305001c0c1c44c83d50342075440c00c07060400c07020700704416003e4010401c123449401940050100005481a001c50102c001d44903801c90003945400101280030100c1d0500b140340d19036 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 810118192 1250 810116942 810117037
    0x160503060d020f030f06060f01030213061214150f04020a020c0d081303051005070c0206070210120f02041a13030f03030b180a0507080103020303030c0f0717 69
    0x9109000d40c000001c1801c030380140c1c444070400010b940c1000403428052802c0028559842c20030b0621000303155514a1906050060110341600c2d070b0300034002e1007500d44526090004008400800020f015601c200080b801cae9502e00b8081c481404500c800c400361000e032000c1083c860b021052108a0cc42c4903245d1300180c006042c80ca208c0e00c0c04149081100b809a54405e00303254001e02a5414011298130449140d400100b41a2403140d2078040c40e548210309042141e0110050b2300419814820404002d11501c0030041c0300c40c00c01d0051440c0100114104810001e0f482040c1d14a4000c2d40140240d601c03002d840c2c0d511040058146e0100e42000001f4115081024a1030740c540a1205141808605053300c1c2c0d16480362a80342c140203030300161003501540c01c49007081d04070340007110000f41420040011840c018030260f20008122500300c2405111581e442c00008100149802090030041c240311b800c1000c172808804580c05000c00d0b8290b503000d080740140503800000300700211060000f5a8104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 810119442 1250 810118192 810118201
    0x2010f080121050c0405090a1a0411040b0303120c040816180c02030f21010e04050a030f02012004030c0e090d030b0406031505010905011203020a14070302130212160503 74
    0x1454284141c54030a03c102c484a120340c000040c16210103c4042c401c0e030703106100d040c051012180701810319984074800d040305030030b20792101e00018030058001400780b07448940201a64034108201d40101141090401d40d60803d441080f0b2130f54802d115070340d10341c415440f039940100329030390441003110161020010982032200c0c504000d8aa200202c03402d6000c00e200c611290042140106043e0300314132803c44001c40c40c22208010f0242c1a0021018a00d440003000300040000542110880c0c150030003c8010030340b84812405821244981d07150101910b1109038500800000b4000796803044a80c4904117861361100302c0030344c004813031460099001e00082d550185c000e9126005002c000380000c10300d2074998540c41e101c200030304140ca40d819501c1c80100140c0400b881400d014007464008540d40c2085524001d6072206c40e0000641501ca0800000900000402000004590141c00304900c110014891b070004c2d00300c2030f00b8504031749091000502040356a50b5080900c50a501d8650030f68030ba = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 810120692 1250 810119442 810119489
    0x3070e04020303041a1306110d110712030215010509100b0c010b210601050919020f1207090815060904150b041a1c0b060d030c0f03030902010f0801 65
    0x20094030603038141c04200404180209004a07000301002d040380019601c0300902c1107140b05000917071001040005017080100022004181e4512038240ca107009032000c0c0c8500c0b00941411603641c00803541e00007403030388601019004100580441e2441c0f0012025a9039001400081c100840d0030100c4001e6404e001c0c4420b1aa0a000c0c0c20450b03c80d000008444050340007103050340d1855a0781614000c1119413110384464200002405410f00b656900010704240210041107076000b10500c510b5a00411600740701102d42c0e042c1c481c046c85d4510641050305107001d000d0401505c0b1b00440a1038020b8101314252a0b42d0f642042d40604009000300791242e4958585010241c101204114125102d0300e413100f9580d100e00862101a01c8440c02c0c2030241450717020449405201603180260050000e23950002c1024415060b51168080e03d40340d4042d10981b0b8121003807010880010b00051080440905140d40350703000e6503c55100380c941907015040944180c3c1d221600b40b040d4800c038000d03610851015070 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 810121942 1250 810120692 810120719
    0x25170d0509120f060118050a270f0515041709010f0c060b150307030c02010e1b01170f0105090a1812050708120a0c0f02030d05040819031e0204050307 66
    0xc4070382e401d85100b500051a032504018080e4011942c8114043c0d00001218251041e95003000b10040c08014030284500070042c901d00100440780c1408c00c000a030801d11411510300d681499211041d1481c040306520b805200311000d4605880140002e00d00182c418101421500d54060503180c0c0ca001e6a0084021900500b1001c170442c0d41c00d48a001c0e0408980b100801c9808410103c00c3d021b49900d02030300014101c50000d010841160f040074141d214130500840c510803c1e01c1c8024820307034149402d00c016501c1001b410f0600b542070f103141003040700030740c1c80d101003e060300c5048a400c2c1207515002c04240030f80b44400d510610111311114031000140769692101d1070024182001428007410303032030b54031207078010317140c120a80758100c0100000c002c20351040150252540c24000d404080010009549000d11942e1442c0103a81c1d030003003130501002c102070b82d0741c6c1140900d102e40c400c2070940d0000c0141251007014003081e4140b00c0b07080c500c40414000e6409582025000f0300d20f40c0d01d0041c0c45626036 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 810123192 1250 810121942 810121969
    0x604080304150902130b040b150d0c110706030609150605121b070c090e030f040308030a06092306090c0904020d140f2a030c03070225170d0509 63
    0x86030f841015030016101c0340c200107008401c511000a1807044001404180c0b980c01d0f004622410081c8a40040e450f5550144d80e0785c1c01032000c000501041e414400d503828481000005410b10a081c400600283c2c150060070a0380e5802c1028840c90a0b58103501111160750b001e0034000c10014828644c0b0306241d130881039404800805043d94120058013400600d51018030240c9010f214550280040f032032902401004021f6000258545090890400d400c4d003e00e02004001c00e030008080703002070701607810050162400c0d640402c05d40500501f01c008031111400d021003850203c030300054580ca0102e60306803051020005d9107180511750070820000754084400708040c243d403554800450307120000c81501c00c4c1c3d0107603400c0c60981458040302040d00385405007003103520076681a26140c2c00d19881900d42004440036060b480b0b456158081c1e00703002d841081610030b083d803510602861148100f100b011a040f07008070240100c0b010015903152003500c0c1401c00482d0041203404d1035810107120703000c2c60307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 810124442 1250 810123192 810123233
    0x60f0318080d0603051203040b13030e150703020607030b01020318041d01090317041a06030307020301110d0c09030203030a0c1a07080a0b060307090b032a13080604080304 75
    0x440116507605042900903440100600c0d40d180c2c814400c03c0400c020ba0304408984180050031442d050755820100030005150303540140c1c1c031b103400300d040500400c50a804032170005d100c0141548001404445500003031030960042c403c91002c1141c0e140a0b20a0351441c0704180d003c0c1d4604840e10010500101e07003c403440d50401c1d922101502101640c1e0050240800c651001244154190400810f48120013500100c0410608113000001d02d0351140c00c01219804885442c450384c070031000034114000c3c814041d4141d400c0c407800d02c170580c001000400c440c04203210100100300602408441c0034206000007034250340200400c1880038000d0310b210441910a40c0100940c64a07880074600c1850107517680c0d008100c4640034000e0790381c070600882c1803c090640b1820308610302120014000d146030310a100c0b03501e17800808111014081c500c0c418211310a8807103000c000d40c21003401d00342a0302c503100001c9103c10016000c03030305450200b4070600803500400003d0540e101d544540c0509040210503113030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 810125692 1250 810124442 810124481
    0x13020a021002031006110303010e150409080a0221090a03060f0b130213060804020f121603230f062811091e03070909020f04060f170601060f03 63
    0x2049030103000031885030300c0d04c04001410514005002d0600c09024810342020f4000340010b1104561060160347d00a201d09021072901c001c400128000745604400034221030070028049a1003900026500d9250f284410300f8005043c18128411140c001c2248039540408a21400c201150381078000925200c4030010003d950304111b0f00054480d98500881c204581d00482c1401c91401aa1070720801030125003004543c91400d940001d2002e003e5400c0c00d8450f00000f1b6159200b06010400c5820814903054815000ca4690070191500e0740410828020341d80d1807104c2c0d9403981408201c90300701e11621402018a51100e40780340751000c0c04142003242015213824036503c81d0106000710b20901500315070302903542d01d880042c07120038081e101c205a603460803800d0380d14564600040c0b0b0b100b20361511302c00140c51440c620000b22901290010360782e00c24200100840d4440d41c06660004070348a10042e41e42203401072440c0768a44001340b00300c0001c43c01c0c5001056040e0300a810009141c01d13809100749 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 810126942 1250 810125692 810125713
    0xc030c050f160608010905010302130f09140c131103011512060b0a0e04060510050f0d0c171608010303140c100204080d1805040e2e0f0b13020a02 64
    0x2441c0616002940a45841880b401c014541c1c1188015000d800400010b008030b604540103d04040401601000107980e192041c500c5405140c0c065050140c0c041321141038401c5018440399660710f041030051203004940340042089006203d5404800c3c0c7c80c500f503c0c00d6a29021031042600400b401181c20700c800c44042068420091241c2000341500c0c0d207266458040c1c900c001081d035045244c0c0030340110f251480600c13265031002c940d0325041403186003159031102c2041c900c0030300380101c200c0d440e1180d0501c000b208040f508142800c07114640d0300401d640e1540d450320003c050311400041070300420009070040c40400d00c40e5003451100ba002d07100c003500c0c20185604e0649052000c20018100950114080c40008000d20900210034081c0c6094002d407220410b00070524001c1d4800c040c4102d60f2442860407044080c0203644003003207a40d51036410b80e9000804003441d42081c1d824aa0400d282003a103009a54480c8207040e070542e8080d1040d482c03402615442c0740294406548c80c025031040301e9040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 810128192 1250 810126942 810126973
    0x4030b0406022110170c01020714061c020a030c0c0c030b040201051210241d0a0e070815041a010305060f10050c0607080112111504120b010e070c030c05 67
    0x390180c042135034545000b910344003011400c0203400f089540036421121914032680c1c0d0015403203003500c4031010000c0013260034600186251243c3c604c0c000054110f60007010840d49542c0c007034a10444291800e0042e0002814101c610aa0048008007140c4220320180040740040e840d40354003a2042c140320f46860071850741203901c15022101d42103d00700c5c03900180030040c40912044a86500c41550240d082035041c0003501c001d25200000d60303003c0d4040d07902041079035142d1410f0b0061006859120796800d004c0b8006041041c11500c00c4120342d0b440c10030801e00d0030036101d40d03c0c01c500c00c14461500d840c0342200441c040c0c41d02034652a40101100384424055907104203c4500d0641074890070b0b5911010010241040001001c02c01030020000c010081c1070103005280660941c40700e034405230801450001080400c03602400e02c468900403c020072000c1003460464403c0303003e0f92290403240e0707880c3c0900d0004c1c10100d0b070500002c2d904190300700000f170081100c940d21520500554909000c801c004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 810129442 1250 810128192 810128257
    0x506010201022a010f0216110a0504020c060916061d0118081f060302030c1c12110c09220c03020301090b0f0f04021c14070311120304030b040602 64
    0xe0143c2c42c080c07218503071034209115800c040c0da90000294102241c035090090f03020071108028120008203210301c4101c0d81c442c55400080c2c0b1b07008008540b40d0802d5000c44d941c643c5d046600351348920815060a0244102140301d4003102d4480d03940d0210402c070304c00a00c00609015900c40d06112940e480c5a00201c0e00900010240c454040145030385545060540440040202154072441c90201c0600140e100404e4039150b548046d42c4200c44141075850050f8001010f07000030700016190100314918540c400015613001c0c8030202140c254424050030003010902c2500d030501300f41d0560009d1500d0b20000c4c103103141c202c3d0080c900c00c2e540c1c9a803034003c83c2c01c3d10b0000c001115819040f108100862486c0c1d100d0b550040e58a10194200f85001d90100741e0002011220051007440c0030407130020002c0c1c068112140300d10741001d8540155482c80d0902c51115400c4c0d0a0344500240220800e01e48030000549003100c0d00141c68102c01c0d2650380b14540258041030201c40454196800010700c0c6140700c54 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 810130692 1250 810129442 810129487
    0x21010e0a08090307060c0b060f06070b0a0603210e0f13020c01020403020901080d05040308033c0703020901020307080f0403240b0f0d0308071b08070c0f0302010f03050601020102 78
    0x41d480d6146001c40070541400c8072a0000001d029216a04d440490340003003040350b0024081d9182c8280104020000d221402840300082c60b07903100a040007040d105a4110204882c4140d0040d6050f000c0e520241d01e14003240c002510010311045c424000600c3c107206044899100507000b11521000c2c0206031007aa4000428a145690002410000c60800380b00d821300403c44907002d0015002d011071300811034807c501c4090660f07000800803824100d48041c03240d07614010340392006032205d28486000c0c038032022104071942c40e0242d440050b0744503000317000325a0b046605901951a11800d5502c5e0082e42c0c10205810102c402c1c1440040000b0b09800800704408a240800f405c902c0200c0070900184d60303908144074024200341440501e00d403122503c0b81c40940e0305003400d03400c664031311508640c880340d07105405948642d941030303400074400c540009020707181c02045194002a1a0140d03d1151b554911000703001840081d0840c1d403043c4281c2c441c81d00700d481480007500d0000d40d0307006182c0c41581d041 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 810131942 1250 810130692 810130703
    0x100906090b270403030f0b1314091c110703141c0c020907030207050a061802090f090604030503090118060e01142208070203030d020a1d21010e0a 64
    0x31582203a46031074241c51084400704039a080b000441545003948486010704020b0034162910090307103402c811070b0880000014060511101002c65075401c034040e11000f0801c4e007890702c9040c0810421a80440d404040785014200038140ba00301c020112403480040c0c001e0700090048a40100006260000c881403100d1010000d06142248504401c200301c00ca030740349400d010400b45003400584421a00c00d0b8050140d080040e03c031501e070b01701a81442c1c490b0100520b114588000e2114540295481501090080d200c4030b0559840903144000d0320702c16a0261141c0c0e00403400600001d20035002154000c0e035081c00424541080d00c1404a141c24440b4110307100d07522081c10549960f0244207803106170b8205a00f8411a00300241080440100440c114100b080c10b0b90070103082c80340c03078022110941c1e405022a6500c10241d0000c0009401c100d11800c000380105a080683c081402903000088a0003424448495504e4a075181e40c0c000501540501d0b548038851845c00f0802400302d10b580754001c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 810133192 1250 810131942 810131951
    0x70b0a17130b0a05010e06010e1809060a06050a0b0d09020d051209010f080f06190b07110301050f01180c09050603070f120e0c0d030905090903040e010501050a021510090609 76
    0x3860010b4a41d54003c08041d1150f280900401c99001100035064010100b8201504100c8090004c10201003c10a2540d40340c9440414030815000010300c3d148510840c40c0100f150139212000c10002c21031620031151084c81c01e0040c143c0c2c2821640c4030016161006200903001c6056540345410616004044001c0303242c04034000b002540c00c1840d691341c00020349045101e034904445202103d410240100f80200b1545030082c1145100d1084040640700c242c65190702c820346880c0000140d8603d8030301e9030095007000040b03016000f0309080d05040c0d807040c0c2c01c180c5090030464030b0301c80206a000f0040d41008507036140003640341c0b1000b008501442030340e502c40090070034014000d401c414400c0e0380910800d00c0c0400c0752104000204000c529100304440d03042c006101424200d41c21496a00303c0da521221150030701542000020042c011240300c00e4280e80c081c0c0c0e944005540301d01a8903064000b41e00a00510071111220780211544024074219082c4a20348801c0c40c2c2080356141e800202c00e060f0382c2c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 810134442 1250 810133192 810133231
    0x50c1014060a05010f0c0305130b0414060c280f140129040509010e01061502010b04051005040b03210a02011503020d080d020d111911070b0a17 63
    0xc8440d641d8800d10640301c1000e898580b83c002895445803030190010449040c021204062040c000c40740121010389810340d24540700c8045501d940d015101e5107000c941c00070015011401c0c40403d550f02c810050019141c080703640081010b00e4480c2010400f8140d41d258000000103501c2c00b10080320a0003003e05444c6070b40d82107011400c41c0e55203181020408580c2e04510350600d81204030340209981594041265200c050b40c1d42d02500c1c0c8061000500e50a040000c129440c034180c4111007103195a000780014540c6c0400c0c04220352054071418500c5560080a02003420103400140c44100302508071080920240290450450841d0100c110301d01c00148140c13959609015034000740c0c0303455040c0454145160300017198000b0140b8010300511011600030280380c02a4143c5050064400e4244440c042d15542010b10ba030000302071000400d5152003402800340300e200c0ca1307181d96150400404885040c070305055100d401c00c14001040150040b9452041292011030f680150741c2101c4406c180040b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 810135692 1250 810134442 810134471
    0x30a020408120304140f030d090305090301060b0a0f050f03010b0a020c03151008030f2d0a03140c07020a030b1308040801021308060c04031709060c060108070b0702090610050c10 78
    0x1601c91005c0c0d11030744200c09400c981c1e0004800c076601d0100302440040d090300c4e00d140079603183c040c60075050ba16520f02403001940300010401070444402c00d90b00d110035000d00c02806c2e981030098a0540d03d03040010700c01030092054642c01801490140d00448000c031200d04002450107102c0e01d144400780503030308103101c800300d01c1c05111000307801800061410220300400905c11401500c0b9120308041c01030b07881c00030404201026281040f06024416a00c0c4500400900030b030400c40c607980d052812810000d80c0302500102660183d9a004150540c001d185444032058044040c00103c1340b0462002c802c0001010600248000c010110000d61104041103034400329100640c00044290010020064400400400c035030941354042c1200c940840c4c8114850701d14005d4603a141d402001c00240c0d510340d500002540360480d8000320403510040e46500410800b07004a01000b0b4002107034201003411498810041000c000f180d02d4164249100c0c0d010103441c01c0785400b0a50b40507030780c0c0c40300b1000104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 810136942 1250 810135692 810135713
    0x807170a1805030d020604110d080a02030a08010e040f03030f1b09050a0f0e0a02070f060203070809070f0f03030e0312071407092702011e0207050310150605030a020408120304 77
    0x19040740689485003801c4d6001c0e407600c2000b40020410038605551070001e07546c0000f684c04c038075003101c0041d80761304040c00081d5482d400078030b03000c01044c0074000000351074802d010702030320071070340f00070004100c0c400ba580982c06442030012a81100e1789800001c4d403070240005660000e0541da42e2010304486c605428012665096003020051411800d402e01000c003030700340e803075070407880604005981d00104e007401c0b240d1002c02034000303040500004c103002403d540311a40f10300030fa18040960340d1003070342c3d140c180c6540032541c483c00e8503109080f2010070210340902c00410241c5800303020f44a03d440081400e0459612181c0215900c2c50313000c90444842c441004030718041d080e4090100320f4004003a18030a81e41441c0080070744581c10f1010081c0031a4441c01840c030360202c100301c200c1407500b24010040e40f1141d460244a0007417080010b548012043d0f03008948019005040100c200390420804030b41640c401800c0b0210319800700400102d917501000300f2400300d81030320129502c0c0d0805180c48400030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 810138192 1250 810136942 810136949
    0x102250e090d020d1805100339051305060d05180a02010219030513080607020c1806010c020616051f1b0806120109050703030206070801120807170a18 66
    0x5501c150b0070900142c0d00020980303214802410002c050b020320094461070312005801c403640200076025620f103040d406030081215054082503502550840c0c1c0b0b030b105041c403103600d40710101c0310810041041081c003910050241c400d04003e01e100341c035112400710307116901500c03c480318580d0740e000704003107000d001a482c20100d943d44040c01d01d0809a8000070b5440c10040b010390300d000151102001054000e02c101c4035a12540300b2022400d6a803020140e803600011034181c005801044c3c000c02052030f000540028000e81c43c000b809080d00c0d9640110352000c0185001c0b40c0000c020407010400305036080c100c507001c52140005000c582401c220341400398182c021211420f07800c081400c0044066101403501c0288249050b0aaa81d1400d00003101414074a00910f40c6500c1d2241c40003d104020603408240c80c040c1c0c0880d4419124511304940d02e882c2481000b410218403210400020442001007409900460b81a1004580c0d000400b42952001d010a0049105e18844400c0b804081301150000d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 810139442 1250 810138192 810138211
    0x121021b03090a15050f0d020412050a020f03030918040f08030a090201030c09081b03030d02040e010311010509030604140a021c020108240405061201020c03041d0c1204020102250e 79
    0xe90b020640a0a1402095810f0406440c0800d01c400340c01c2036239041e6001011407112011511003141005a04c940c46e034a000e80c01040341c414440c1141c00c00104551480d1006052000000c00c609094890f00c4000f0b04102c54492000003445c0c00f1070b1050300950302079039420340009901d000f01e1001500326041d450744502800800170301086140c0d4085070980da481e84250550b01da0031442c80019046114000b07240c01c09078400324012550402260748203050740e02c50740305111082c00b80801900d05014650703140d07515900c10070001c3d00080f402c00741c91500008104c100c881000041c1c0c0010480c560480040c0f101c202003484c410155a840842c0c42d400240c5502c3c404200043c0c0060340010b42c00160185020300d4603074010640d1912650b1340d0040000c4180021522001080d40640d00d99009200d2901010708801c41c271f12800e40c2120940f4001e0644921442c0f034030385106041e0002840040041c1e056000b98130783d50701c07030382018229000f052003040341c20164142040c20128840c0710140c1400745c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 810140692 1250 810139442 810139469
    0x1503010603030e010318150c030e010b03120c0307060612050c090903030a1e06031406150a09090615030b01080f03030f0f040215040803030402010f0203090121021b03090a 75
    0x403e80004110b04008000e01e000f042100d82c1c81c0d12181c0400548000504c1d5035001501f04503012203661141c040c0b80d12641d4240203074100f8a00e100e0030b9a910011495040d0441141e030781c043e200040040c2003405000041e6818031510303840b288211407590348100d50002003504220b0401c40140081da0700381e0021281d0381034609120051035520302005040d8100640d03500341c2c0c0d010345500b02e2101c00e190f48101c9400e01407a074a80c80c01c4000711040b1350010585209190104003002c6004036000301c01d03040501001069498041403202070b1145250a03207085540305510f2420454660b50800174501450008486503d0701c0340b49854543c00000c43d915507081030041c40001110410280d0304800c07054000708268a40b4000100805003154204041e0500054001988070b004130196110764000d803070b5148800311800302a600ca21520100c00d00207440307181c01e000079820000c07132a9031861a41c2c90041c01e0000e210720280981d5603240100d4125440425480054030f011a54000508164071707880e038 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 810141942 1250 810140692 810140699
    0x10060801090c2115060b0319232701020a03050106020d05041a07030e031005090d091410020c0303070c1815060f1814040f0e101509090b15030106 64
    0xd028610440d0f0040c100041036009000501035900308030050200c0b03076010307942c0b41010584040000046c803200c0c2a81c909100c0401e03c0580a500340c0125129400d411100c4c5542c2c0d004c0d111080f2443c00859960361201121400000100b40b01600700300ca282d4a00042a50504902030b240075003400e0701e58100701c0c08003c1484142801c0c0c81c3c00101554107200c090301c82e006031600382c801400c1100c2e00d5805100320940c80b810064a0741000380101e40001c281ca0108002480403241e0142e10b00880384103010009100b82c850a004144070100707a410f00c1541c09500341800040d080d5804228240c803803240c07080c0d05021003590071b45002d1920751940410414454801a42e10340c0180ca48140e205005850403a484814021929400d0201411280c03004260b1594070b01d00e6009603844080d40624030b454140f201d03130740c0030f03104e4a15150501001010941301100c03c4034090465802940080c1c0c140100000705412035000e000c403046e22584004130980b500501540b15001c507400400d1081e81405003c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 810143192 1250 810141942 810141989
    0xb0901020709270c030606060e0f0d030c0206040f0f0503070e070804080c03040f0e0a150506071b0f030519080912010216080c010e01050c030105060c10060801090c 72
    0x2070101d44480c00007192040d428802140004020841070024840604815080044694000303040d60301c01c4000700000b176142c0d10304403048564144125040428a605501185400040205414820310707002c050040e0903030201c2c1207500181e010090300d0301440b070f061104d00e610004400241c40b05400800c0024546141001c107620050a02010702000202160a200b090310448401c900c03c4401c80b5903507036541042441000c100d215101d458500314001c80c541a055010320040301c2d0500c400640b60a0400040002a510202c011200d41911000c00150102080340074001048001903080c10145182085c2c3e04001c050700302c0507640c08040030508000f41040781070340c0b240300d401e880301499181c21082d03090091159240c00f989125400b100c40c4100007017040103241017054a0300a0040040c25001075080e00c000f0341b03280680c440c088c0018080381c1042000784c25400205811a2062880c80b18100100c4d6141d8010104a0b5141c1c182601808100d427801d000a0443c40094500555500c501 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 810144442 1250 810143192 810143203
    0x2070b030c0316050d230f09060105011d0406120201020601050d0302060705030a02070807050105060a09150e070c0b01171b090a1104081f050c09010f051e0309160b090102 75
    0x40c2030403085403010a5090f2403181c3c0070348082c648903a4080080184021580507080f03940d220446669040d000000e014140c01d0041074000c02c00400281042c0e402d00c0015514142c01c1c80b035180c3c1c0940020f0b420551a61940a140020031540032400060542d60000a003000740581040b40074a43c60200c1500003680040d0340d0b684088546400c603101d49415540300c019101c0c090300602451404500c0034103028040d440342d400340340c084406000311955a11558243c980e41300b0916192450154108400b42c000400300760702c41120b01d01428480707800d94980082c61000e03080501c44444c810000311390848204202d440188401c00601d900054910000f840b40000030400804e450300d0311240300e0500103500540f0080c181560540b1070b490340c404c0c00a03007560300313210f000301070941000c0c08039844c03032070900c01c80382e603008180d40c1c21240980240d015184d542c082d180d02a82c0403038440c0003041c0f10762070310040c5014505910240144a50b64140d01140003039a411452000c08100b0000038103030b800091 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 810145692 1250 810144442 810144451
    0xe0316150b030a20060702090103080a08060f0d1716051c0e0d0809030f06070c0203010b370b03071101050f071b03050d0603061d0105041e060b1801050102070b030c03 73
    0x7066221081042c0480d14a021b2840002d400149080001c820028640b014081c41007440c4e460800d1680c4010802420380b40d5424003d400c03c1e00031710315a0104400092040703c001c00488464a00300d08181c405040d418148825281c0303801ca0408205d0b1030a4041040c54840c07503928101c0340841d164000954244204400188083e00004801c0d40d103840604c020700d4a550001d09a810510703000c00082d04030047c85000304d00c294a0522054144e250108503180e01078084e10b803180c806644240c9510743d54030752038913a600c62560001c0014250070300b40000c41c456203495942450b62544200d01c3c50a54502030481c29290301031108200890798001151504a140076001020b40006421306456620641604a120314108140801444460782100d000c6030350031400808604000e540d92030894506581c01400418080a42c58070816180340070110507001c0d4200007101901c00d000544031207000380071204d100b09040010017466030184210401090400030310352540c900923040e007600340700041 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 810146942 1250 810145692 810145733
    0xf1306030219170f130204060806160221070f120c060b0d110108100e0108030306011812060b0a120b0402040b01030204030308040212150f010906270e0316150b030a 72
    0x800141701c40e02015a444565500035208110301915000c034181c8483c403c640d18131446d40401035840c001c5100003161401c4420140c118184007004800225070359204400c26502d40d911140c60902090007000706400d4a03d007600c2301d10104c1c1c0d030345c41c124054802003c28075210b000041e0b090b101151803944901c121900900e4200290380d1071011446031540c103038010ba100c0e5500003001103440c58000008502841d803d807142202800a42c10000c0d240206020b10a00c1a158080d01d4001613203940000e404c1c0003008224250f001d4403000800f0b00c0042c1000c060719203509e240c0c00d20083d42003e1244121400c0d0a2038150f14050468034060400d600281c0000e00036800301d002d408650300180320345546180111180072603801c00c41d9072103201c0c0f5020300600300300c0c610f0410700041c0d14101c17084800c20b0328060080e00b0314035401d00e10a84e00078180321020001e18001001504000368501c1d2a000d0712502c900c4c9003800d6580142030300421211603401c0c181c0690300810390304020031900c5034581000703080b02 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 810148192 1250 810146942 810146971
    0x50f010503130602130803031806070207060810031202010506040f0b01050f1303061103090d020d09060807021c03021b0d0c080c07030f0b06030c0d020a0b0f130603021917 75
    0xf498454024410501881c940031403400001ca020719000c002903001349a1034405501c0c02c1311540180780c0741c0b801030740d014000da400802d0401045000c4e5910310303400020035080c2d50006030b81e40c0302c4041750041c4c80c11020060355100c04011461500303100b0184100c01d240020840c505030203001070014810300c104600820000304081054010030b280c02005141e00c010140712100d00259030744a80d4206858240c594094440480700e801e01c00503e441e5603078601c2d590440039030302c0e04c0020342d50700b00043d03c441e08500501046400d40030074210024403081882ea00141d0798012505501e00c101d1200c40003143c0f980001f0030141c0581d9100012288080d040103180c0c0c1d40345d426406035880e02d2100d40c401400010030000303402c00d0210b8601043d106803400c0d01035071102d00410007004040d141404d40258080f0001d0400c3c4080d02c21132015181406140c804185840c00c1d401c4410300600306603010100091b000940549034103202d20010004e4400c0c0d092060303614084000d40901701400400e40144100d21 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 810149442 1250 810148192 810148231
    0x31131031e0606050d1b09150303080411030f2d0703080a17132001120b040b060d0638090105040b1c0501050102032a030906030907060801050f010503 66
    0x150f02c4100107101c000c001854189a9203040ca03040c00102041c181c001445040021f500225030203044040010a03640e003018908580d4203855492001e0411341e040321010000d11100d8800300314480d00390040200400500040c00c80c1d00008c114003002050084452460800d04600b0024008041c2e0390702640a544481c00d400d0105d0750342605606090b600c1110000b805802c089080c03001880c00d006944810440445c1c0d407280c587e070118541a00e001030b20700c1e9000290603580381c1c0618581c420052000c074840f859a00001c01e0f036004010300302c071682e55901007000394828041491028080100b12000c1d80c0d02001455a10410000860004007900007032000c10b030380c07048048038023a2028541254880a28100f03c0080018041442d40c00030314040010a50398000001c3c0c4030391003050100041c1c20f180d4110000391110074140140780c640b106010b44c0703016554000c09184202f81c2c0074010302c225494003c0c0204462410783c0030f54003034440e0b11070161959902c441140d45c0312100b041148400c206 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 810150692 1250 810149442 810149453
    0x915031203181608150423071502010219030b030307080a030f18050c040203010b0906070503040504052a09100e012109260316031131031e 61
    0x50401c641d030360f006001202880211920001d01515810002c841ca4139421038110600800291000b40905202050842d4501c4055451844074094038050740d40660b5030300c040044510a110f10300b400351350040703a1006241d848005a40c462106443c091001c609220040b0b512449407110142907901c0c000307076252035207000c0c3c0c00039101420040c0040040480c00c2c00104403000911108503500e00504551000d989407034000d40381645c03602d6041e10b1800c1e907403404000e0ae541c002d403821610341c0400c4c40300281658a40c828644280c14031079015040c03070380c0e200c0e880c5500d140c0c03c0b43c2c1c080b21840602c1500e00c103440340010800c0d4032042c2c2c04c0c240000c0a403000140e0307005080e04184d4600c61400345c15081203034083d0308108062442031017501464501c090200d090440207180c207008441d410300025a8140704200b0488400d1a075007400240c1c41510781625000d58040c0c88036130400f15011401c1050407003d2820f02000702c110300e120b0f484150455584000e000c08418000324001c00c151945814480e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 810151942 1250 810150692 810150721
    0x603150904231c0c030c02030106030812280e210d0b0a03110f0604030f05070e01060201140601080615070606060e12060601122304020915031203 64
    0x8024000061071a00e03103805007004116910550041019401502e515800080c80c0001c03141a581054010150b0300c10842c1e40c403114010035001c202e404456040503031800c1c03141c00050341c014030046948080741000c2c0c82c08100040c0c103801c02c20400c12010320701500490b941d0f00000164400225400e144104d0b403600c3c111040c1e00b4090aa490b170440341c0c0e00c1020120080a610403079107002d001a800702c83c2008144001440050074003001184050b00500e40b004506036072200060a0508160300e0380ca030041c0e01400480203ea00354040b94080c868007020304000c500611040c03000384800d10b40070000303d1805e600a40898140001c60000c140259154078048007508540702855071594440e00b02031700507280314881c86010038a800b40007502400c20012a0354040c500f24000d080c19182d0400458041c140c00303010010340380c0c4d100d40d1000c00d0b100b4900f8440061000010780102030400340104001180041c10b04292000c00c002c81c0c44a070307280861300c1e0403114180201681c484c2c2c1c65050107504034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 810153192 1250 810151942 810151981
    0x11413050f040c05180a05041e050d030605060313060e01020f0f09100f200307020604060804020306060103050919050c03060f010315090804170f06010f050405240603 73
    0x8606040801c0740410030104258401c6000e807503041d01040e9a0400d000004501e41d02c02809800858002955400c032030300b0894102c0e02c60131000e945e40c021501000c40036106010210b40ba0b80000060750519903060040d540a010112643d030301c3d41c200302c1d054491460944d00e006001e41d846090404000c002903040d52011310010111a0750b940c03c2003da40019400320144610503011341514440303042c891001a0714080594a0701000410544550810070005034018205484100301e002c0060704d034000a000246407a0322b0baa100b03405e2501c10582010001002c1604140c61300d020800b00c4c03c40003815514024503810900100466402c1c40340c101404a000e15406115000510802d26280d4030381c2030407280201520200c818050304003008cc0d4800c400e01402101c0c0c144018840032081301205180400800c00300d03492007801c000d00b0360810100340d11060001340340709404c0055050a02450b03a224030106203c1d0380104d81030303030210710302c0c90782c602c070b641c0590400700020b009400200a04c5112 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 810154442 1250 810153192 810153229
    0x50f0601060302091e0906011805130c17161b1403091804051b011b060e010c0201060308030f042907030b0904050d050c070b03090709060803030c030114 67
    0x668407014068080c0d885960100e0003100c001039031050181c42c1145500f05040000d000741c5c01c94840c40f00442d04012440010464840c295000140907642c410301c40c01c84d0002000080f075800c2c3d150002030024100351450001c8070614004110f403000300c0c644410100300040c02e02d001c41c3d045034500c0ca0102c11400c0c00041881c0c0100ba5242c24014000010b4040c1d00001c0764411050307240d5041f0030108410940340241503902584032030101e0190591184031241d011301d40300d0480503443d4004180d20548a0303058460319555000220004020b010708148070007240002d1005915690700d0050341e100003000d00c4091740c403070408a802c210b40c208030021500400040420b01c1d40d903a201ca000341103415110000800e141440608843c01d000310542d210f0f6410401070208114085402c1c0c40b181c1c01a0348110301c0380030344135002c141404040061801000360a0042c80c0050030030718124225506500b140580340d0090003000400011201268103444e580d80e00010340f040c2d103c2c0460946400701c040ca0a1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 810155692 1250 810154442 810154453
    0x32a0f0a18060e013002041805161e112a1507060b0301150602010203011806030f060914010c030b1206040506070c050307060609050a0605061305190f0f031a060913050f 74
    0x350f510408d0f00b2860800d0808004002076212588440c01d038012640710840400e50700602c040d2031100c1401d01d0284000e0505040a4180e002261613040039524140d0030913683c181d5283c007500007071a000e0072088a909940c00c041e01811510280260b0140f00c50041c80316403150303250107094800390031005e01d5410040c035030140d0540754400a80031790006d0065841103443d04a01212000701801040122600710303185100c120019100c01003d810006c000391075064642c40300c0d51072044240300e11005425142c3e80054140d8044042012409900350120710561046041c00080340010900a41202c070a04008040d0002032402e82d056000e40710f03000c5d24940c40c0c4403000900700c1e4030340c2110703100c1e140c2503e0030441c2c56151400c0064030b0040700701d9610300280b50707041844542050600c000441a2010075000c01e82d0381c8903d4040e002d07082c0e42102c1d032074a092160400800140b03000290000e407400080c0855440c040007c61104103009000309483d034040030040f418050103112220103c80410160391 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 810156942 1250 810155692 810155699
    0x50601030f03030f0b0a050607060b28140306060915270a1b1d090c040501110c010c0f030512010807080c0402032a0f0a18060e01300204 60
    0x740440030844207402203070800445080d031000e944240407030100300074100c85255042105004464200000c00c484a50f55150161071703d0752142107189009074001e60321032000a101851240303144c525405180303045102d00d038284080e40d0100b070150f400101510440d65a43d90380301e041010344012082140c1044444891130b0501c0c06811420703c2e40741d0121402502c50311000300f510100da10190346c0d800702620341e401031141f41d8031503000001c0d8920700002c0c09801011080016024440c29516480400300000d230400c00d07960800100264a55004003920300f11a1400018141c8a03101c8401406514651038080070140103409851030082d00786181252503840b03107001d81d5200814000c17800c20344621018a000c2c0e14041c02202d01c540803c40f480441070118800d8101c07011490324041c0d0b5100c2060041c030546000000181a1015865540500c80000c501e000b1301c408216821040801448a0014505e03980140d42c4598006030305a403184086540030b0005803801c0008503243e0414000038000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 810158192 1250 810156942 810156953
    0x201020304031115010b0904020409020f07060b0604030c05061e0703210e1207020103110c030a090b09011d040b03011508010e010b011b050715050309060f07020c0f0d05060103 77
    0x440c8560710035120950310b10340c06480305590f00141000001c114801303400600500703400401602da6602c01400140c1826200c00b414000c2e070700080680d03284000007080700d20a00400d801401c50420050b2800d034600750a45d124005100303401e0044e1b82c010300c00003c4d03a8180c00000d49060340201c0b50b40200ee0f0300d88540d850300a00c01d14119814203212005000c1d80f00304a800e43c8510400f5982510041c65062400010f00d600e541110000382e0500d42c0c0d480d038150072008144010140000c2c980f002d142d90360607012002d050b1a0303c1360003004c041d140600601c1c5150b41c000c2d689150b10341074002c6403401201e242001a0240c40b01c2e40c02243c065091018004003d0200c0140d2416038601ca4001e00240c000d51700c40c0d07402c03601040101c2d8001440c2e82c0041d0403450222811031071081c0220241c400300c68031400d01c02542a254501040021800002c0004084d401c0c000b4030b4101d1a680c00c482c000d0b040c0706000a6440e101807820b603104100f0743d42580460b554043c110000150301c1000c0d5000e660750390138a17 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 810159442 1250 810158192 810158197
    0x702100f051801050c0417030d06240219060f0905010c0c0302011103070f0f050c07060c0303150303200705030604061b17040b0c120c0c01150311060a1b03020102 71
    0x2503070081000001d02c1d8042e9401070003018805d80c01002910300701403800141c1c1d2004440c903a41140c450204001245408020b03010340f002614162258100e090021b8901c1000000403983c0001150080f15200f42d031200c0720580c040903150800004900d4102c50010000145130074000180359600e85402e1400681d000051105c4a0b40240c000300900e80107000030103a144001c982100024142500d2a4501409101ca40134185100e00d019424800c04a8605150590b680c211402013181d0403080400c01d5032500071503d100152000142e8803d180d40e030068816040400ca0252801007d0080c14508000b0000c1c0001008010110344150525060120041c40031225024405a03600070700701e1500c1c01004050500e40e00500d44034103644e01c1d41c485072500300d1f01508292a40c00c00300300303c40b1114115241c250090700f201390b2042c0e0b00c07911505854215190b80c464020811006c25013000400c40c002075010341d0100a40c0c119a459501260486800c0300c60018581440011204c42c2300341a4150302 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 810160692 1250 810159442 810159451
    0xc0522090f0204140103050c0c0a06090210110601090e0a06050c0a031d060402010e01030615082d130f0b01030c090507050c100903090819060b060702010207060302030702100f05 78
    0x2081000031820712501079115600030445000c48035132410b105540320340c2c844c0d94032031850001e05003001d4082d81d490303007044d100100548a45440e92449010352030046084003400d68681004c0760b420803407203100c0e511004144107101e07039a0342e52a0398105011084c0020307000700790f2007c2c00b0881e84c030340a224140d41d50008208140040d103010301500f141100d0082c441030420301c030001000c041d81e4940c011603c2003001074032203042644034140003442040380102c030903800480362100e000d81c0c5060b61042c1051250800404819065450b00c80c170107062814a00790480d003149040f0441c01c969040145030b503803107840001c0c0030841c0a400042400b45040724441075070540c001c1880b103501c030054100c4180c060701c69000740300d800c00f010500750f03200a03910007035080d4480e051018040355111703e110f04144d070400c60707869034a00c0c0140d10310410019114a602c0171208980080c1032000300d80000303507206030074080c2c402031503030004c00705104074001c118120548170803000500c48800082c4980020300401e48 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 810161942 1250 810160692 810160709
    0x60f070813210813030f0b090d091208070606080712120e0a06081b220e0124030b04020a0c03020c010c0201050f070201050c0607051b0d050d0c0522 65
    0x200400e0380e056a844002c540c0807a0001c8010044003510784421680c004582081400a4a030b0300100044071b018485050340d0083e000c0710020f01d00740702c110741410310214170342c001c01c81045070a1040c0c00000e0401c1161542064110b512544036103482401000c40d9000b2841c0c610429030002190681c0c060342d1801207120384654074440040200668440c60f98640407a48081810001d0100030311481e039050b408041c4c0200c0c82500c2d8040c0c211200340341c0c4505250541020f00c00707039500d03903010f260191030700500211100b07044d1585800c0203d030b04a40b0041c2d4070038104601103140b4076124400d401000c20441c00920440d80c84030b00e520b0103040803501110440160040200c02c400d00d46c058803181740c500740c0686904d40741900c0b0a100143d00d07031050100b02d051000610544c1c80c0810104a031910075410303501d9095413061590301034000d00c50f405c40000f01c950f1000040d102101e50003415070303242d0200f1100110704019a518182c905000e40390380e4468650401010a01108004081700115401789 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 810163192 1250 810161942 810161977
    0x717030f04120c0503040909050c0a0b0a0314060f210d0804170901090501030c02120f13051507021c050d0801090b03071d1e01080705040c052106060f0708 68
    0x2d0001e0703d490201600241c40c0d50414807041007401d07015040074025512403000c0d1040541440c0c00140a24010b030421a90182e011480001154041c421007115682c1c001041c442458032200041280d080c0c0210f040c0918800d045445d580702e450340400c20045480320a4541c5002c80000051440f907041703400750b640b10700120f0140342d04081d8904840950006940f0b4074109424080151301800c0c40301009030840c440c3c0341002c2104942d010141420101000d5040e6460701e005000d44003000b03031078000c540301303036000c01015a510100c0c3c0200c0300c00640c1a2048140d079a20640c641001d51038000c40540b0314091840c1c6807000c103074440c481d039060350504101000060031550915550300c1103401403149801200c05030100d404404d0100c8c0d40e0007903c5e00d80401c01900304624030b10084000b81c0c000c913030981c0010014080c41c41c203400784407240c0009160040c140380d4240e002c075a4560108200504041407140418000c0c0c0342d1404848060503850a40c0b5502e00d010328200310140c1c08026a0001c24100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 810164442 1250 810163192 810163223
    0x14061c090201020115061709121b07080d0c0321050a05070f08060319060605061b010f09030c120e120309011103040e18070f140f0405011a0717030f04 66
    0xd83c0b80305c2030f200d00750340300070380803002201030900310740c019003151518401d843c00551a602c454000b010003041041d00c001192031948841458031140b0780001c0d94541003240c1351000640c1c81400c210443d505842c110700741c0e240e8194441ca000c52891f44c208a003e00f40800c10401d1441e5420450254a4507900c5041440c0a000f084a040d00140d0700d0070b616030800c2c03291911000600003200b5082c2d0003143e0010700c3ca0b540d480040e109501c640703003400f40322202d040100003103138080c4104548144c84140501010a80303a50080c210700a0309401400c00e00381e41d58040500740303d0654080e81aa02901c428030901080080940d03c0c0c004041082c0002c0003050307100c81c00003000c400d45007203c44082c807030319180e01e03045000d81e001d01c03022258110f14803e5640001d800035000100c40c000348021446404045100d200744504200002c2c929800796040070010014030150b810007950100d91210801c0d2202c85915040d040c5041d802c10456003488040103010245140f0401e99000d40d20544161a05619 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 810165692 1250 810164442 810164471
    0xa030f1106040201020709020c07171509070506041a12010603051609050f0d030c05030f04090501060f09061404030c030803091e03030609070c021206060301060504021314061c0902010201 82
    0x20840e00213005801c00082000030842e07070780142903042c41c11401e490b05039864601c41e041d500082507011600d50310001d0020061341c0013080c440d8002414601500d142c1d800d00c000318519200d148100c11402c150710003502004850308050741d00b0046001d48044103541d44030303802800303400c041d40c0c24810242000f000700c416034061460300044481c00303002c8816010034001003041c005413692080d07040c000050380e40c4001030010720051034000703004081c5503103540c03d01c40e030901120310581103941800022000c250440340c0050900084407810300c1c0c00c003440301c042c4030302d024a4015036200800003201c182c0e0101c10404440080c610501122048400009011041c5845c03400306004600b190340040001c1922818800e030040e9000c0c4882c10040c100340310302d60200744c030460302d000b0401458004806014003480d00703020318801000100d90a505200c2081c0450240401718411b5640b50840007440d04025200c0c5800d031040c4071816071030720b41d02460301031a0704080d08018a089005500c6e003030b00c401c410071 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 810166942 1250 810165692 810165703
    0x5010606091d06030a15150603110304020d170a0509030c0105030121051f020a02331302100c0b0606070b070503060d0c0801150905090c010503180a030f11 68
    0x68080d02c404409030380002c190030000c0409081d0507018024407001c540405c040c190306c21100c411010002580e107464041d942000d26042c0c0040040504002050030404280700582c2d400c84d40440f415910010146071007485e0542401184480500100312020b400360414050441c4042c1642a200f2030050340c00112990300c8240180302c403070f0859820000e03800201d40540304980344103108588044a4848101488081000da018181c03900062001140c46d411700c110100e107601d0051100c660f0750381904080399040921a4014064060400101c007030000341c0d419147d86402500d0720703495031ba140d40000c045c0c10248205030307074000303203040411078608041048861445d08001d0317038400360312801c004440325400030381055406840c0c45031040218481c44620001030400b14000145104400c5211a082d8116448401c04603e842c1c1003101c4050041040703047c100b82482c00d9a541d079680c8688600c1b50304805009003e80c4a054100c03410103402c03040e10b0680d14407545881d0704000d607550301d840da5003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 810168192 1250 810166942 810166949
    0xa02070b0301080a120e0405040602071e03120c030b060c07150206070c0303020c03091203030105040b0409020a150909110d0b030a0f0605101802030f0609092d10090501060609 77
    0x398031404d400340106000140742040c0c0402c81c50403002d0304c4003000c0020b090ba00203a130150340e11980050700404200d02c0c0311146240310b81081041001441c075450180c24209851420080307c1d448031743c0c60100d603200781e00668007010002c00ca2a2a0341c4048547da984040d075020780d0302000075200311800f8041c0002800d03071060a280d03840400404043e5421006501300048280040c4814401c00c1801c1c1d41d071551540c4030603104402161650714000400c01907819001130a03010703924026000300503071921004107042d501070202c48600b0305041c800854840c407003031307006111203840c200301c9220032a41600145070b5204480014400c4105482c101a01c584100000601000d0501061000280c03660002a88441645560018582d890b00315003501d0310300b580d0840751710b0741c000100100304416507009a009402990381e0000e41c580700c3c0020fa41d900540038605085100404c14050500782c0b6500282d40500d01d1064680300b400d14601200940310141c2c3c11241c95003424008681d440c40b80c48050100d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 810169442 1250 810168192 810168209
    0x80a0b0f010f0819020d02070c1d0a1e0906090215090a03020418080f070b22170417060105031b0a0905190e150a020316030b03100903090f09050105060a05030603150108030a02070b0301 81
    0x40e40f030ba10f11400040440c0b4003007200f021500b200c0e00d175040603780304034030110340101c81c04680d9050f20700c10000030001c984820b0241d450b017808400101d4940c112070a096035819900007540e81c49013284070804070403403d00204032250001d41c400b4610000000344c41268440c501c210400d03140c0b000101c200140c00c4026200c01b428007000c2034007103290700e00d105c1009c034404d0500e11302e41920380301c01604c001081d250552081d0301038001001182002c01441840d58400003c041000c40c100303001410700701c0c062048414443d115030126015003c0c811310300580c1c203103921007000f030100040f08040d107450100341780510010300c2c040051030051b400d000712481007149404086140075525000d4000303000b0410641d4042c401c800d402c44608141d407280840071390080d215149500c3c07900200341c030030107002d800000544d400e21004100b07075220030040d5404030805060664a96407800b000c40c0c40d0191410b403507840056010000501180044001c110701c556540c2600c061945404000e14148028862000c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 810170692 1250 810169442 810169499
    0x230717060321031b04060c031107081c05120a05041101020d081803120a1b0216030206030a0f050a0e150915070507080307080a0b0f010f0819020d02070c 67
    0xd004000b001140c0c4000d140100c1c0b5101d00c50300080d02d280c0c1c2c1154000001055180b0900c40a241d08255540802c9049a0041c00014100481c880d21407000e82a1403036160450b840040407103000b081903e40703010b0048a01162490706e031140c500908000e880a50f1071100c00485040c2035440401c1c04051844c440d2200d040d25203440402c044422110f498030400741c04140204000d503122484e044c1e0140441e400041910f07000082c1003c8110303c00042c1c40290352280a00000d000101c030142c104aa80480f032940e1a03a90b1103007640041c00c0d8608450310b00502d080104002194650b1100041204c100212108bc0c510700e840011741440c244c0d032040c500da0281041034008a03803903120a601070343d540307041030030285155500d8405030000e54051000c640c205c1e0420450711558403a82100302c0c0e0403102200c4090050001800702d98600500300c08002d0114001a443c4500b840c0001d061404100d086555140c20140d50000750401c01e0216105c2e8620140080c003210801d1026601c241d01e0480080c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 810171942 1250 810170692 810170743
    0x3070302210709150314180706170103060b010504082a0a030503030c0307020c0d14100207080910091206050f01081c05070c031e051c0f032307170603 66
    0x14003810484c0e141004060301c07610307040101c1306120001c40c02402e40c001d852110b200314060040c105400c0b6003006042024000b440c8091100d001c241d60304594002d040000c0808032400101d40600c0307150401a510311600901401c581c5c0b04614000401c0581c0540c203004048840030032001c1001880080e0455009002003a00035a8450045400c09042c0c0119061120340c01c022407058000942c090311060a1889030082003c018000020118801e80c0300714582440e0350364a860718040e061180c2e0050341050048041c060050b48004043c3c010070002c02c0c020803540c6400000b034901100c1c082c230500300d10800005c0402c0c0010381c545a081113640b480d21140e1600500311401d41200105031804c06c0388007000400b043d00241c046c1c8610440d006202640070300303400d019180451944c4619040071040c240c0d0404240d05c9404500d44030700301e00d00403e8848410741030100f4841c80c2110000c0f49440c107010320011030b8204005450055402c05078000590320030041546075074098800c0da46a810424020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 810173192 1250 810171942 810171959
    0x21c05070311190f05150705030a0b0d06060b0c010b030c1c08070c03031d01020a121215170d0e01020d0c02060c1005240a03121403070302210709 64
    0x4548038034001044030032007400100e00c40407444110000780c580c0e40704c0c410741e08140103091010782c140419034070a04c2c29a0420f001e0084c4148001009120742d036a403291003140b01c2d41d885414108030b6821074130130704c09503032210007840c110780c42464000040c2d0319140d1202050b060110307102e8010100105038240704044524903022a00c005c1200f100c00c1c0000300881800506823280704406507001c0e81d9130140902141800200701404807210a06552007105848005080c1c042c400000e60b0044c50002c0729020804c1208005d071050720390548144406540200c0c262024041c0e40e144203034110211403541d10490401e540380410050b40324016000710450300d100b6401030480f1010ba901c040c140070b181020301c040f00d0f07003401c0c42140201c0c01e080e00c51080c400740300c051400d096160800b410b0400e080b69034800000c0c1500380d17207100c01842480340f5500309541c2030050b6030410f10401c02c1d2140d1030380c0b461f08504c010000d50000f151503507501d5886041082201c10841540d1062145803101d112450901004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 810174442 1250 810173192 810173207
    0x30e060103080d051023040c0c020d02240d0905060f071d0a05190f08010e0c040c090e01030f0312050c09010c0804051503090c06070506070305061c0b07021c050703 72
    0x84160020020001064020241ca43d0050b01941c40040020f07161b07142040169480a0303808030070010204a5100941e40d4000511100742c1d04482e04909901e901c40700c51200001203c0440013806c0214a0209a100369005501307840e02c02d4080d0f4007a80d440f4660070300064801d0b10540c00183c82d00c12515100c41150941381c014030401403010103500d603580b000602d861480640300045042d01c100c2017100032076901c4020043c025010017400b25100600039541d491690905280c4180d44038018090414042c070002e0028181e4260a6401c03980c482c24008000e02d180340c0e007140020745451904a07a00c40a125030f601980d0020301c05c1d841c1010360001103a00105070082920035410070040000c5964400560015907250395041c09c0d280e00d805c040c01400d00000d05d0500c1d003d150204103041c006140860810b40c8540c040c200040c0381d44468020985503180c1d0b0b0140f40c141c00003000050244612054001d00c80d18041c0e0172100c4c8070141800d0f9020f101803605844c008030b64144007000000340039011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 810175692 1250 810174442 810174451
    0x61a0f040e0c070b0c0919051008060409060513030806040b0108280612050c032409010905031b160303081801020f070f0b0708040201080c2107020706030e060103080d05 74
    0x14042c00c0c50fa0780c0d02c540c1203068081d80d07441812400050304000c1401c295440c000801070790003d1152240c03501c6d01050030606800d80860030006501e002840c60750f241d520035001c80b074000e0f02c1008245400319812003940348000c4d069011030100030000700a40341500503013001c400c041c3e66004543c0c444030500313011208000070070400f505e4620f01407441000c0a22419005003000da001c080d0040301401c01c5801c203441c54032001c0c00794101f4203010140045052507400c00350380c01c401040080e900e546500d401040484070040c5140000031303400e044005244400c42d500c40500003500c0c901c040c18015409208124071000300862400c1d80045c0c112900701518943c0c07042e94000151800ca449111520503510943c07048601002c00400d00c0140044440600d90045a134100318446090503000605032240040c14030341100c000281c1010700c00340c00011820709000c1d45070005058104800040c1d15060b030b034040d1900003481d00d80002d103003801c0041d585040301d030815022403804124542c42005080d0040c03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 810176942 1250 810175692 810175711
    0x1003020703110f0c0f0306100e0903040801020403060b0a15020703110a0305121e0a080c090d02090f0108010b1e06130b0403030c0b010504050c0a0f21061a0f040e 71
    0x101401500c1408003070343c08040da8016010078280c102c20001c1c00c510304d8020b40d01079030102d010000f541c0442c00044c81501c050031400d0f1010340d10200342d18034500c0750341c102c3c2900d540040360000421180b07800044104104030b030900d422580310950101c00492101c0640c0c01a13011200400100f001a81c44000c1010050411004103490307447d0344e894102083c0021080f6039000820701a40c4410b800754a00194901c07201c186000704d200d800070054400501b030050708200002d0380c129103036101840320800b03070750142c0000c900741707802c0240d40e00700e80091281e41629400c18180307250390b11f050281a90200d003e444980c080002c1c880502002c0e41012860a040210190010031011300b180003401c01140700e43d5541880300f442d0324081c2410041a1f11842c0600d0403d4184484512450241c0d10701140500d88401c036040040c0c0c04592000100494608454005141a103140c1c45a00043c040d1002c0d00d400d410019000c0c40d20b080c2d18072408200c0010a1401e000504c4941c3d0442c14554001c00c800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 810178192 1250 810176942 810176957
    0x8100515240d060e090c0103062d18090c05010201020f0a0305060409060207051b030c060f2107170108030f0f0705030d1517060705040b0c010f090303090c0f051003020703 75
    0x10542d0200300c44180e004504142c144c030080005a1900304962040402e00f8a8140402443c0c031302c4010045182c0000b0104c04201c0c2c140c400031000302c1c88410002050f07072031241d08901e12055000c1d40284614001511880c1620001180d86c0d40140201c80c0680b921000c110b2400748007980840040801800f4183d109071039066050206074280050540540135102800c82c5c07000340c51005c40c00c1e0351680d4009019421441c445400741c0c0c3e50005a41d17915049071040c80d0b943e20307001111103840d50802d9005903000b01c210207110a481d4800058000e25008961030b10035662102500c0c0d550f40200b0881c0040007104010743c9100011000c0a09103161155080ba820102480b001c4002c0e030b03040000100318510100300800c07600ca800a9081240da01400242109082011000b4020f1041c1d020b50b803c12400090140e001000075072001c20f1110002c0001c03c200015403400801802e04100c05440f02c6007006408036038072640703404520448800a10140b0045441c240c241c000e5002a0000e43c28082c01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 810179442 1250 810178192 810178207
    0x2060703150906080622080403020607030c06060e18031608160c24050324120a050d0e0105130923180d1403040b060d0c0810051524 58
    0xf03000e440d0260025401400c2103240c81c0d10301ca110450111041b88000c105101d054011a0041003164152901680c000d5560750b10350405a46031908800000e184502d458400240728600304645400344410b010404031084846c12225a43d004100801080d19442c82514000038081001030400c807107030000070b0344007000070342b150110560141d00104551440c000007000380c2c071981c4141c0291405608103e81141401c60040355510003200200c2210355052a08814503a41e02100c00300300c810b03100c110f0780e00440d1481e0003901e60b00700030504000b0402c03401034a0304a42c043c02c140d940356078900c984070300030900e4100c0d440050101c1211541f6401141c4c0815503404808a206603c0780d000034691203600c080d2403070710034501003c5400b20303801c11401e01d01905113040c01a04503500150080c1901007076441d1140022130032500c1c2600108078114646001034811000b10b4044551035280a003044160303113200341c42010300c00703901809a001000c004900c000b03070f05058800841c48003602c03009040c0040b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 810180692 1250 810179442 810179459
    0x150f0506031b0f040501030b120c0409050118081c05250e0a0b0909010b250203031612030e0307030801330203040504050c0f0a0503071b210c030206070315 68
    0x1c2808612403c2c0703400202407049507054010f813440a0300640b00803c540c01010b01564440300068046446035448012000c24043c094004140c200c41d202c0301640d040170703649010f254503402480d000c0750003405101c1c43c18542541744a05817040d1181c68001000a00300d5461040524550a10300280a80c0025190303058807106108000380003880655076403040300304204501340324140d01c600d80c603940030001c40e800f0345100d4100001e40070486000320886400303440040d080d40140b2071410008080c02540b001803151300c071010310211a10783c80401000781e2520328036031240f20b045c9001c2c0c040b62010004014203000303154145040300c1500309003031614046102c48581940795180440060340049410311941c542480f80c0c0c1c0d0000b103c00301c1189410690043c3c4003c41c0a14103013141408408400500380380d00986000441108a14503d561001c2914103104d1510234107808004c00308100c050800824021240301ca40700303800d1703001820250f8546404501400003100c500346050307610100082d0201c0c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 810181942 1250 810180692 810180697
    0x90a0b0f04120f170f01030209090d020c0f0303120703060315020c031b0f06070809070501020a020a03031404090905330a0509070503031801030c18150c120c0501150f0506031b 77
    0x40e510b00300d03030070254034500412101227000f402c80d80c1d0b19000b00c3c00304001c50b600041c0340c501414046d5000700900307940c000080e00b903000b079075110000e0600c0307842000201d641c103601c22003c4d240700d400c80c003054001c40703e001400c03402010800e80c240e40c000c0000507403400b03502d0400c0e05240d840c3d404480403018081d003d18140751041d106000890a40e005100c10641b0910040300900028402010607461032b4001034540051440060140310b4041002081501d8060444011b002801b80c18004058580340890362000300014124000845013130840d0b144070700301240e00e4101d104140e1840c0b00e48880c90000700814019043c80c0701407180010000320360b102800600700012400c0420491501c412001500303032183c410b104020088008065414240350b08000c2c025120743d914444c00340c0d100d02c00b0540c0d030155803000142540c400ea0a031300024582c848240340c40144103800034040c0310a40d00e2a000040c4890180301c0850300c581c40f00b400282820000396a02c00c00340c2c04400c001400c02c60945000343d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 810183192 1250 810181942 810181951
    0x110406080d02280c0e04060209030d020c040513201f080a0606020d140a020111070501020a021015050402071a0106020604050c030604030f0c0501060e090a0b0f04120f17 74
    0x160014803088400f51400203c50550b101680c4000c0c00d44800c540c0c840200e04407a004050380000a030700881c050103c9503041d0b036003045002c3e00701d0703080011b00d010284da50030b900c40186109504001c00903c510301010842c2c16400e0f1301c0900013003031004168850310b0751001d4440d8640c002c1e0340107540030b40c09019440720006035006a00d503098141010410701040d03c00b50307013100e015988001c550045065000800165001010000c26220300311900d08034090502400d41c4003040c0d001003840070600c0019402092038800d60b40031180841e0307080906205807010310070310388200700c2c000d4400c01060816030020240c03144955101100d607030368004500010b039001c1c0c100c0740041c1e000708100010004200b00310b1110a2046000f06081d28099034001c0c10b00c1000c1c0c0c02d1104200c490203281c42013001c25048a0060460310b10840c407207180583c4200e45c0c2d100743c4c3c04180c0d1421035840201c0c10f0300c052150780900450700f0a400c04104080e100c2c0540d411442915000c081010300131141c8444101d400146029 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 810184442 1250 810183192 810183197
    0x17070f11070909050708010e03070b150607060c0809060118090503120406051e0c2502100e01140403050a03081906031a0603010b030c190306140709061b110406080d 72
    0x40c00e0300c50a05503c1d00d0300580150b04941c2c9882030230014542c00106486550b5404903d07402596202c06210325510000b812181c4c05c5200403c514040080d10340202d41c5040d00d9940b440416034590150b030340d845100f80b00310062100340341441c190508941d0480c032050f500510031646808641c468200e01c94004540c03e8942039512000e20503145541094042000282d100c00a004e04210880c0d0360b042c460701080741b250103244a000100300c038a2b040c0148170b16800400c1002e00024040002d01074101000c1000d00064002c103007003840d0600c1d10242c0301030b660400014554481d480e40d040c0c80c0c012020704480401c13000410b454000ca0b14034045c0e43c010b94411000ca6075030021807144032842e1200640781c03521036410b00c00141e03c1354500240c0b05403100c2c0f086031030459a160240300401da601342608007800e00d90030b2003080c1c04080700e1480b0150140032580c0d034400f0701558a0004540c2c2c8c0e030014a0919590000410000104042459034803000c00000d00c001403945c1d0b140c2002c0e1034422901700c020301 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 810185692 1250 810184442 810184451
    0xb0a03110123090f1c0b1005060a02070306020c070812071b0e04030c03120c030510090203010f0e06010302250212031c022503080109060617070f110709 67
    0x5550340203101444412400b080c1c1c845903040240052518040c8140303140c002c1c1c0e160680902569118244500034052078a02580c8101c01070500c0f07500c031041110301d0200c20886000004007420005c00f15855000c09501601c03146041d0358400c8040e45c40942c50340010712031208003040c100710a00c0000c14800c11030038280c0d510356041c0790024500c2d0b0040347c42440071403002d01c10440b030800e40c81001c0d48141c0c10726004500d60140d02c0c058406a184a540118051030070f40740543e1581c040d8401ca000d52508220588948c2e0b40b041210b041c6c0c8400d0082600f00c1040311070403c0351682500d0a0b540140d0141405802c045400c00107030580e080861080c0d5240400d00d4002c4294100f0b020005941a10100034504d0911410030000070164000c1407130744160750018401ca0f0551403002121100e585e00240b064180c21942001085040213000d030b10300403403402e480008d43c14010404071040c00301c801c075084c03103035902d103041582d0a80600b0410400c0c480000750341b2038101414002c0f40e024110300c0c140080c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 810186942 1250 810185692 810185723
    0x10050a030501050102030906090108271605030a02010e010c05120a03020301140f0306060d020609040204090b101b0206160c08030a0908151315020309101a0f10030b0a03 74
    0x505807030041e80314034195001049105a40d071522411510f0158003800c2140b034a48031000d25401440301600078000749c201000d540d00c03115201090003510849a02d8041d500c8644480800d43c1300c24000600a000c52103101d801485540039400b079202d41805007050b94903070080ca01c0044030740d40c00f5980b00000658000300501594901f4504110380300e1051b81c0c0880c0100e07504000c40d90f0b0b40350150200303104a20300c8881c4c3c011503541c2022030700103220180003035494a98034849040540356014140344907142c1150403580389442003038511440c0240414800f104200c68003400761039804508180c6410350300c8045d280115641c02075000003400b152000350b0b84d4400000c002828440b0b5a006201590045008a01a8002c45c008950041c1c205000039001c500e2a14154010004018240041c14000b1003001000c00e000710f665416610000b005200001210080c42400210410007640c880c40014030220b5500313001d19038402e40c080c42d0800144450300c0c000064200b50740395008460010f174027010380 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 810188192 1250 810186942 810186947
    0xc050f041a1c06061e090314120f03100b03280209062a150c0903150103060b091e070e0307170a02120102190302070510140609060619050d090210050a 66
    0x4d41c1700d07652404481c8140b00746076030010b181600360301c0040c0581c90010310b0040c11074014825000711500c1d41010aa1b268030000005c00180c10484a4001081203031000241030300090044034032075400c1131284030a14020340c1c004080e0380301020b03001c0207480d800d006040702612644006c1060f040c20b44c0c2c5064144134212421030580b100c044085031660003c441d144070300c82055501300e4200159503103ea466160300808203142c5806c0301040c05a2a1043e00000184102907001582c02107096580d00d80c295100c500b030206254401c2240140300d0724141c000b5440a02c1b510002c003000340000d060741c008503560403c8021000302100c000840e0f801c451485811813030150340314405141030340000c1d410403010410300c0c11208040841c0209168000604500b00030007408042540c404d005030070001c4100c000a18102c440c021035046010720030400200c0c001d858841c0690719009060025030149a12000301100c3c9504039200002519458a01960040c1c2e2840182020164a5621107840b4283c14400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 810189442 1250 810188192 810188207
    0x160c12060f1a0307050d14060403050a020f0c0d02011d12030d1a0f0d0c030c0e1501021b0f0409050102210a060e01050607080904060303050d0c050f041a1c0606 70
    0xc161003a03810703100002d083d2000f003031143c00c40b0001c81d0109210142e0f4109440d00081d013030305640301c80c02060100402c2580100c007801041000358202c402c200b50f48408aaa5917260120190b0301120540754540150b1180ca1243d2000aa03400d14040d0541d4100124944040504900015420124103070501c54030b84e00c9006141441c100031101035040b0340d000f09a11000001c5100d01070b840902c04074041c000d5101d03002c4000e640c4241c880501c180e642c80b00e0088100d081d03482daa101c000c202003400e004d62000426101045064640b100c645440e0004c01002c041c0408540d6082030300c0361001008200280701815445100f03000102e0380440c032032030710910900024841030103240f8242d814001886c61404081c10b4540c20380d446980c0d4402802d14612074003440c8030859020342004404020541d000002c0c1a2585c0e09050a007c214811842070300d0602074018201d10100c0700344800c200d0030920034141c0501e100c495200070b00d0980e10900c2d07241040d88c0100404503d40c0c64403005c001185d0701590 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 810190692 1250 810189442 810189461
    0x2a0204062c01050d030309081c090228150903080f040e130506040b040c0933060806100c0f0317070804050309100216180b1203160c12060f 61
    0x8941d440790706010019400f001444800784c101641c40244204001c020011203c140c1d10754000504000c3c070344210f50001e8680c0200403030040c030380d5140d00998100440b0340580541111081c1c110000e0602c5c400c8200089003601e020b0420a60300310010129490b4401071206514004c1c0c810394481c103080340081003020140040144080851040011031804900917800550050408240e6243c0d4180380c0040d0401c0d82050503010301d02804081d41c0c02c440388000384144185204070303210359580d0112008000c554030450700450051400101c144c900888240040042800c0c80d0800d603180b0f843c0c1c01d00c0600e080d0011004102c803e584000103030074503a241030344901c03580342183c02d51420f5a11903480c2c0c003441c02c03018061001d12150ba4000350003400000501c0b004200c20b000420340c0d5900c001309500e080c85481440354030f06040c16102c2e0a042039071000d0901958000c51815504406d000001e8031849016254050116001700c0c0b00c0c4403589404030164028280403440d02455502141101ea9441c1e = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 810191942 1250 810190692 810190769
    0x6040c0504120305120601050f03040303050a09020604080604020102011d070b16050712050c06041805180609010b09010816030f050c13020408060a05070801180902100c0c0b0a2a020406 81
    0x7401503a85c9e4400c403940603905141c080380940350501d2100151140b042c000b940010080b83c040340c4440002a012320881c001d900a201d44200058103404403040310100790f400d40c0094806015582d2803400034801c0543d10703020900000d41e03903200c070780c1014410f420002200b8404c0c4082014007000304101055810b0840ba03246c5001d18140c40800d165140003214440d442d2640300003041204070b1070f0540181c0034139605440040c82c0c603c818038001c058500c1c82364440c2d180d81c0004071703030800b0000f80d100c10507001100c0305c1842d900f592238020b2210701d040402c40d818498840e11900c55120009801d0750745421100c0561514204040a41409802006d80341201d203071404100000d03610000c04d904407850340710b0960425070100c107560041c1048500194100c6507810203010403507804100002e203a4025052540350319100c0300150114460000300d00c00048000300341014550361080c00303042c0c480750342e0550220940141e002c101508c2c003980c0141c8201e4180c6d010000c0c84001800400070820001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 810193192 1250 810191942 810191947
    0x180d090602100c110a060606090906031a180109080403030908030a0806040c02030706060f05090906070e042307080103110301060f031b031505040218040b06040c050412030512060105 80
    0x10000a6548146620700740c40315844100c0c402c5014080c09004c80080058415280c108160381410310213001c0b0340c440c802c000b4040b00b400107040700e02440303448140d9a02c032a0104150482c040c44400c6030381d018043c0c21810b060350030341c90000380e400d214890640e4402d900554031980385040181030b5078225070203103071140c00800406020650040245d907010404071800500d042c4000740480c518010309500408292510201054001e86450484221441110044081e6072507021060f240c1c0340544982c00441c10740090942035280c10740101d05030301c0001d9549403200c0d01da0240c0c441c4807042900ca070408500080014014402e21007035800a0203c254028020b461821294040d8038219102c0504004040942c1d1150140340d03c42e040010340c3c01074103850f40003c0c6864210f0013400306032001c0740b2842d414840c1c40e07200381e40059110302c141d40025640e1610b035149020300c40034040700407203242004401c1201160800254404000440c000d0b0756980d10342d08807a90b00d800010010302640c1c10300006 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 810194442 1250 810193192 810193199
    0xb0607110f092a1312120905010203030a0e01020f0406050d0e070b09120f070f0e090d12050601141b0618060103031103040306140f0f010e0c07030c020306180d09 71
    0x4820b00b49000b4181850508403c1c800c4507880f01d031600a2407140d1440c9442d01030000b90300590038600c1034001e802004074214440da4001e00307441c1c0840910507180980c000744002a10181694444000d001907a4000751500c520441c1c04030240e40941c0244011400110313414031a10468407031501001e03c60801459200d081c003d00c0c1040f40992501c3c1171140301c4800c10b140c0880e2061258601080ba50301c00c0b60005501c03581c01c5110001c490160a1000d15210b00081d4450000111018078401c1e40e25200c02400211040c41d02501c030040446050100000041c41c035400e4100007070402c082c1048414445140c060343c580c1c00c105010308500c0c60948040d06079802507101194950450b60f0500300840301400700002c06045000303503800541543c1ca4902c3c644282d00e01801f0561103190701520707880e00ca03503440c000301d000d2a03402e0180d00142600c03e0000b44550192100900100380079007444519032000d98006071400d101220411007605c410100031504040801640700c4020f8982041c0c00c00e0703401d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 810195692 1250 810194442 810194461
    0x3030f0f050f090f0c0d060e0601141002010c1b060b03100e0d2303070207080307260304030210020913061806060804030e240a0f08010503070b0d0f0b0607110f09 71
    0x10503007107210f04400450381d000c01c9555030000230912445001e48a140d03a44500c00c01e01300d400c40414034003945011200080312803061280c28150711243e125020403021400d20240400d48600044905d25a40d1002c0006c5a07030400450000c00d9501801288000100b01c009040c0030610300c52000744018201003001401c1d81640c00300026440000031a160b9441c441c04134900780880d44016582c0c0400a281800d11114208450030700100782103944904858800c51180d038402103d020b00185c000038035041c0c0b4076085800800040400604845c88040d00101c0380e004c8440c1544600b8510690201018a01c01e9500454008140e070741802916441c19441c081c100190b00480e9a1243c00c13100c5001c065490040c0d10301c108420142c002513110300800c40d01038200050700b048403001caa200340c0002202d10b0300082d079201b42c40307410b15440d041115024018015020008200300c20640712344100440d5121040038042042c015104c64500741c01440a2000d20b13122010460301a4004004102040b01c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 810196942 1250 810195692 810195703
    0xd06022b020c0a0f06090f030203090901050a0501020309040c09170f010e06100b0c1504031101050115020d20120d11040f0621020a020a0302100e1903030f0f050f090f 73
    0x640000301c94184c449180303002d0b030040c250303035200a00d0300301d207002c090040c1540040604100300080c0d51000b010390f211410008143c0b410f100300d034010391007007100390a41e04094001c206140b10034105580400e440e0000400e00742c68099100100d40e000800c0d85080c51000d00440014030843d5002c0e000b2030038400601081103105002d10500410001150200c03081308000a1556260302802c1c455282000e03c0c0017858a408002010071039030808002054070000003d820821018035002400e107400d403950b042c1d40b400d2200c0c0307200b00000880d2401240203201805861006a46502002d6454941180311011076602ca282c4c0c14500c042400180101c000074000c480640b81a03041404070100d03900c0c4109a62248240301440c001e00105d4100c100b02d4001403040501446a02075454011541700e140007111011030620185601c800000305a080345042844410340c042d00d004240080b541410701c041c4e8100c2c072003030800a43c2d9002080126000f07039003025044851a400b40c000e404019040030b0303844 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 810198192 1250 810196942 810196963
    0x10f14071112040b1902010e0d0c03090302120601151b11190e0703290405130506010b040f05010f08041506080115031209080d050304020d06022b020c 66
    0x1049400a520722194100701e41c0240601011100c0d565503154034800c849500141c01c860041e90034856410362050041c06050700b0103110b0402030103000704220007141c016542100640c14809070280210168071042485141c41060b403000b0411540b48c20703103c401151402c040300d000c010b4080d410351004c40d4507001c0c5039485034002068165a034804000242070300044204414800f141100000c5c10040300e80525128500030380b010030030386440800c034031a041d000888076125608000925560340c41c090344107540021101c2188070480c1c000c1c0d96030304d00d014805c0e0890480018045401c100030102003070b050014000a2a16505641c4619005001001c01030002865041c0c9880800191100c031b0f44a000100114402400704404040d46140c901140340400c0e907600c6040300342c00080d28040c803601d00484605100409200f44041c00890f495080508100d81c81402029918040352940c0007070080b0a41521200c5840400040c9454018071403003010540e4030300503c00303143c00110119904822 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 810199442 1250 810198192 810198197
    0x1513121e03050d0504030f081302061b010605030607020f0c01050a02030a0e030c0a06120501090b0603040b0903280f08220c050a060518190b070f0b18010f1407 70
    0x11982a240540c1c003030180f41048040e25260074104018540d00a0744120100c14030349580794562603803c1c00c0c003005911060040e401000402c100031109600040360f064400540c0000502103072100002414582c0599401c0c006a10072403c921650600740303e450828042420000d00c0c001078080080d40740d009046d560800d100b440c1c0c4001d50f06031001d01c400f4100c41001000c14109503200d00c00600880009443e120384103140074000b189210342032054020740d610040860f415075686a907118803901009004040c1d9010038400d4040d4030f1610709100e0380c20407005e00340c1c4942e094012402801e450f582c21109007080010030034000b414030a08089200c1d11000b20500c020b008140c200500403900c254806504407400440c00617840d64400080c1c26108040548079000800c0b803003c00840c1c40b11401200540c90344d40348108075002040c4010900188100001d00c1d41c0d0302c89481e03850241608580c502020703c1c0c940d20042c442d1000303201e409882008401e04114004440b41c810840c417200910420a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 810200692 1250 810199442 810199493
    0x1104090c0e010c1b030507060207090e010213030b040302190f02270109110c0d020d11010902060d0f0f050702060712050f06010807050403140313060c0b150609151312 73
    0xe0040380d54134000040c41d045400c9601c502c0e614100250342e1482c0e407080042403868840e0407080b00c001802160826030030b42100220441c15030720751201c42c0801810031800e502c500328503046010001d0115544c054000c999154850466005000180581c6141403841100040030b0400030742c180c1c2d0956043d0782617072000003541185500f80d90a913200305040c01510307104003612009034540c001110700d40d03d6025511480c1c90b041d40070481e0b00783e0345427010003940070009000401010700603602200c482d880710303140801d0385042d40c00320808845042e1450001a0403504c208200c0640080701c80f142880507110811091030030248150062601901590422180f400400c80c2244110203075405140c01181909602d620680d010342e8980c050103902c1208942100c0014102d0300a240f01480e294205140340e0030395a03400540c640c440b4100041990007081401115a15203034003040d00616107200d603030241d642c2d003040322400505199500030040b0629028581002501c04020b000b40403807d0589641d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 810201942 1250 810200692 810200723
    0x20109060c0308160c0f08040503010e19031404030f03020c0438060c07170606060f030a0504081306020601030c090c02100b01021507181502210d1104090c0e010c 71
    0x65004200a002402d000b25881b03a60080c015042c00030300484001303d00800000340b00c40c1075561122010601000d00801080328240881e00603050b00010180305d12000d031030991a559060390002d41c054043e40141c0c00b0b12a0219942083d200f00709000304e0072415044840518a00c4002442d142401c0e111182007014001c2480d84881090300c001d02c80310340030b40e41c6035900c4000600340140643c02c5071046126900102c0c43c50f0502004031401000000142c504d5075590f880d4000c0030701780c0944112010fa01c2006035442480d542010103010780559400761096502d1402c22481d2041e403034214000f110316100d00f007140c2c1600000c0038505c0d4100b880020806011000041c7d0030a0802520204a044400100301109030300c04552100c0400100849902c192104804c2e0307005090071140038056400002102d11080701000c440da0180d5102200030f01c0c20040e08411000d94886039100c0d62224004201800f00e0300340c9006491b008006494001c01002080700024140401c1082c09013400b0811064030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 810203192 1250 810201942 810201947
    0xf0516140a0b0c07120f1215030516050a0f080c01120b0301051314010e060106050d0e160501021002030c0406050702030c040c1e030e1e28020109060c030816 69
    0x1000c02c0d00158442601d01e4000c000040c02d9010b40004c41d1740c41400030304092402d00461891184a0040d5140f011030621642600020301032910900000ca03c1c25200100203141005180b03060451410b0260702140f81c00c0c18015504650340004144241500b028000300340c00050002d50003000b4078054880004001040c0001c0c10440055605035003800200141c82d1041810a44d89501c144408086081c0d2003195500300c41418200501541001c0010400305118030060141c2401003500081c0100a01c40d003245000040c40e5100306800ea5448200003968042c070500f000031041c1c1d00d0a52071858011501c080600c030780c0c00b03190305202011a0880135902c04000030585050301410411000c00300c0d580280560100044542d45041c0d506c0c1c10b91032035842409218038051200009080c10101040d08000ca1384080044201521800249d04909504144582c00a4032418500440000d11340001401e05207c0e401107814010346805150011b584114a0342c1d00ca40404500c2c1462880c95804 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 810204442 1250 810203192 810203203
    0x14010903021032210f070806030c1305010501091d0610031b030911030307033c080105031c020c010f09050d080c0f07061209030201200a0f051614 64
    0xc1552a040c0403c0c5615021001c000b0200e81110204260300d44210303d000412504049a035a042c0ea1102c501046402e40188442604030000406440400c5844e5012801c80b01195501036075050700e9100400c03195800c0009400030f4a50b0b122800081d02d036000c4400070381070000d000240200b14000041201901c25400301440b9080c4881c010704801700ba0714020041c00020000352842d07030b50301c81c0c0f46030103150020440e0700c80d5904d80c13201c46200c01d407107000319606030803c00c03e04440d104c0c102c80c443c14140340c81401ca01180f0700c1e0b1140d00300d80d414101403519103152031004400d5107827000c1c1c3c000e80540d000141e9440e0031809181403600000030401c201d03840d032001c1d40015040068000030608002000001d1305545002004490900744205200c0ea074414541c4524004250500c2540d04814001d0b0840700d1039a000340004220b1804c044d24119078103030503203c0c500c4007070b0b07000c0b4450040551000414040c90400d1510300c1c241031650340d409101543d400001442040410b00c11079614100340b00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 810205692 1250 810204442 810204497
    0x415050d06060e041104060905091504050405030403200a1401090305030d020c1c0933031406041b03020705100903023d0b01020a14010204140109030210 67
    0x8007030098507515180903102c09410310500c0d10503410641c64001e11820101500e04403050b40c0c0d140e8086e545400c0500100c0c1c44090320705d82d40c3d07061a151489540d142c50245500039441007006581c0c8a24600309030400464408080d10010141d60401c030456071421030f0070048e208500003074803006040c035005843c0301003260f00040490101141c60103203680c0640c0901000780301081a00c0b855107241460044441c841c2d0800340100350100e0f800c0c003840c00080c41c582d00c90760103081041c034030b0316925520110140044d800781d030000e034440ea00c90981599118003640c0240081c0c5081c00903040700744500004200b540543d000f019804140102131207010881b00c100f40c03001000401910b080c505001b5250052051030100319072600e62038074080c0035103102c10400303812010202c03084d241640420304050703e617401c5003a04610034a0f40503004240ca0800301c0040044003000169114502918541c042c04201409414000315140c00c00168542040044901106242c03110881c0b152002c0d1020490300a01e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 810206942 1250 810205692 810205717
    0x406020c03070f05070618081c050705031c110a020703120201180b0a0e120301030813051c140f03070602031308030103151d0c01080603102307020a0503041505 70
    0x510f000c0c401c0c042804801d550869880006448010b101148034500611404035968000703800e40b4a070190044030401519910310b042403810f07495850f1146550000203194100502c0303c040140076070546d11518088403c141c144d00d0900642c0074010f92903151603c4045d05407840d0840c0445918402c0d400148400050303440041110b065061410742c0345011105224102e103410440d0800c1c890008142140c444801c0c0640d2440e0300390390b580d040700d412001011070301411440c804945961041c641815100c9800000c85020102d8203103c100e04020808a03015070300000d031100c1c80144c006c802c0750416a0000b2006d43da03034807184500c0202801d403070009011103074040000700c2008250b5031440c0f0741d032050b64814002003400128800c2c1c550220820140380360300580082c4440c0d40549003c7d40c2c4844001c041d03c90950880718900156504440e180d070790110404e65810801c6580c810f082d070025101e01c004d14a407040dd544485e035a1080340101a00c0b12000203030072103900c0c40b400444400d40d030501e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 810208192 1250 810206942 810206963
    0x10603570e1207053d02030c210403031409150c0115320307080a0b0903070215030c09210f0604032007050d0803100e010305060406020c0307 62
    0xca0008060405a070042446400e0801c1025100000002c00300c0075510b000784460428003071000c03040c8220540c50658680e8116512030100560000c0191154030f258540185a4451207010f420b401c14200e42e03810891a0f000794104080d80075403100b0b50f070079603506003400b0000c030f0302030740c40c0c500f03a406907207d02d982c03000c11410302103002c03900324024104000c1e9400c000c4c448148900351141c600307540d40c0544040b400c0294070000403200c0d0300e4585800485031406400307407205150003080c10280320f50016080c81c0d03c03407201036080101c2d0704240c03640700b40f10360045c6052860581c000b03002b000c40d100c02540c80e144044003007109141503100300c4000340c0000300311050100c211501244201d100c0031340240940110145014082000f0441900c907541c9681c2d64201501442c000740411882d4004140311481140d1000c80c40d81c0b50000b04045d1940640c41142d100c1c600140807000b008620b070803075180903400781e00402c0020030015031940c0050b444000580c032001103207a031914500501c00c0241c04600e94 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 810209442 1250 810208192 810208361
    0x60a030204030b01080a05030d0903030e0d090617090c36040209150f10090b040810110406050708160204090c210f02090c070b0708010603 61
    0x255009204803840703441c0100e62603998200f410303128141d1110152480d08100681c41c80000507906c41c0d200c183c4030f42800101c6003000d19085260483c004002e0001c5070381400c0c00d101c3d6070f8001c0076860302002c00350005600703490f01d040d4143c1c44003203a26460340118540f19000c118400304001081c0c40200414854041e2624200350100c0700360165005c0e40640900c0012400154002c0340d081e8842d20094000c12810720f681d400d02400c001c4030303504001040381d102d02c00f1401081c40001400140543c2d0000d1100b0002c2850040440c0c070303044c003442c0039a04104000c2100640080558524580001c13502d500c801802e01c00e2451020050fa00a60140c50a0448070030001d0398850001901d505c01c441a6025110340b5941405442030784010301400000c40e510320042c6045400c0d640d1123094040d65504040c00b5075681034680b54203a40500c00f10702c130140148007542e0b05104540164032614000c42801c400f540d1002140b00b07840406000012b80e080741c001c0d12214008040c80061420112480b08818 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 810210692 1250 810209442 810209447
    0xc0d020303010302131815020f0408100606020a0210140421050f0601061719020703200613150b0a06030204031b0b041701180f020306060d030e040c03020405060a 71
    0x240800ca03c00c808000300b00c010f09131648107010301029410801c203541c20290b190b0406140b0984403c10219230204100b074141d6021402400003400814010845503400140346025150982c008204650000c401040503980c4c03131390840b00780c00c210305040901100c50566180680f1580c1c005240d00f0f605a580d6100e030a168111080e00c0728040e0007907c444020401c2e001d616800300707114020006a460351140080154141e100d0741141c4000c400c0004890980440300c244c0c1c0080c0b80c03d80200300c0d003425561a000c6508841d003149041d1038060100ba00e0081f0200e0040e050300c46000d070039170f00030100040b0090b00913440b0f4003010074000c02d2108019602d0300014080e51190004079804241395070740d003007010400c11440041c0e941c0c41da016800c1a0030802c030400414080d65102c0e88031b649800050805900c6281000c004d1170007201402051300d00350060500e00280601003030b0080942004c048040b913440034884200c0307901101c021425424645d0100c01a000c0c0f9040290301101c00601d40300781d5038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 810211942 1250 810210692 810210697
    0x50f090d0c090c1106060609060d0603030302090306070e01080a020c0c0a0828050c04020901090f0b030a0e0307020a05091b030a0b0130020702120d0f14131a0c0d0203 73
    0x41d40315109000d40e01c080300d801c40f80300c18081c0c10600250300103400b01d0214502100030b04085034009e032546040c5400003090800b580c0403030b80b00780c02103640050826113034103060189540c001103030b0034102501040240000c0030328030000c11001c040d40d13011880c0350b03800105004045080c40011310340390610307803602d100303d0305c0b0400780d00060800002c000c600c81211148400600c0459045405440380220304424040a5400301107071904104285a000c039007145c250804001a21040c80c95540301d1400d05040340c1200d85202084034194814040200140d84500f120f40c01d4600507100b50406846501c1c01702c1050004000f4281803402c0031040140551055021001e8a1b400b680c8500c601114078501400035500c0f105000e00500710f58400c20301180301d0760003e12507a0300c0580030382071400041282a0030040040c814100080d4000c00c0e0f580c44640c06102c81a0750910303540300503d801004041d50309000784a1040c4030080c0345172030300d1002c680080d0055800c80030450096921038401100001d403607a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 810213192 1250 810211942 810211949
    0xd050318010e120a080309150c0a0905040506242b0513021503130804090c0207050f0a03031d030a0f26030106030e160b0d0b0609030706050f090d0c 65
    0xd019102c0a00e000c0c80c00412080305101d0100142403480c0d040d444403180b583c40100703240803c3c07081c6c0482c1c007601001c1640303540c8034807401910f60b0344030421140020401d4440d6801144074078145001d021496890f2805041c800700112560510441101c0d0200924020407040b411404500c2080440020003102e10044991403c20104866920032040d2048a02040000f07500015101e0a503030040c900c00700256009803440301001900240ba94a1140c540e005400402c0ca1a07241e103c5142040c0d010040c600107441b045070340c5103c03c16010b002ca230705042d0500c07014040101b0080c02032030100c004043c09500c090f0103400d5420084050900003226103040b18100c5880201c41c030a14190900200d10030300c0d440d005124149541d1078420124041d003a01c0414a0f454003a40068008001d0b9140c6a00300426540580c25103540b401da070000b0440e0f80d0014018020301d0104080422a940030030520b00f0b03600507040c120340b01d000025216440f8007400204980202480480c0e4040c408100081c0044 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 810214442 1250 810213192 810213197
    0x303071d090103120c03020f0303190b09060f1c080706050612060f0601110309040c0207180b06040e0709080303040f0209090a0b040305090112060f03051203090703110d05031801 78
    0x84840d00414400d01400034403015182c108400d40b40d0381c00c1c1e84101924102103002c2e104440803032034100016070a50b441135a5040e000d00700001d40d00400744840c000d00a6248003128846040c0c500180840c02100a10001c94072800e00e1240d103210340c00c41e00c440341040a4200c3d9030503890300c03600c4c501900240300039280240701720b40d4800c82c000429030025420703210f99000b50881d1240d4075080700540c0d00c015001e0001d80540018040700085403994880c07030008020380d60080501510300f801040300c8450081d0114412402c000a4417510340316039045030112003c4014007025a99002d80460b0f10b50340c240c20414044c0400014002807000d2a4054100c09008480c1c0311116110582403a03030300c10320000014000f00c40c21002a0100c0e01440190540b51010305141208a4482034400100c8040d500f01c3e604074845a83c090060160030000c000e66251814451803031420310145440d601c1c80e16120041515008206008540d1102c00c0300103401a80007045a44560210180c8040004c0c0145030f00d00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 810215692 1250 810214442 810214487
    0xb04080a050c070f09200702040f020f03090105070e0109030b1b1303050d12090b0f0402011e030e070b0720040b0d050d141908090a143003130311030307 67
    0x2c03201d98141d50403030030381c591061062404c1f40660a1002900e03041d41c5102d24541d0a000350248a1086001540700d513980d000001054985039034040c0169125200050400010072030900014000500454116044455140182407003217074840f070780d00c54460488400305206034008100600052032600f4201e16848042a1414540006045a03407400c8080d0140c0e1b249404501c50001221140e60428010301d03045040b0800880c0c1c012050502e4024200000e0b903403d0f000301225000e2105002400000180c9032030444503403514800d0201c0301c2e0010b00102c10590f0b5000c0196681d0340700260304140584001c02080c03083c101507440e40003200990022038580807560301502c800710300f1510b6010b840710390019000503955003180c403840b0003041000240b0440c81204d020130241c058038040006482c0c020071107024152181d03c0305504403880d001e00c50300c124440900205607041030703d502c820313040c00103411070030385003011030780a000c0c0f2400800701c0c0000814400c1150380160f80c4201d10800e501c2007078 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 810216942 1250 810215692 810215711
    0x71203020a15020a0512060109030c0f030215210c040503070306060602010e010b100c1a04210203040e1303021c02060105010207050d08090d050f010e100c0206040b04080a050c070f09 80
    0x8040e4400ca100e6000010303c100b184446d071140a4a1032a0080701c10300d0903400b040d4895903207031200c10054100c980c1c0c8000743d500c100210b1409078407101140b20300824050030021034100c180090102088441780415030f100014441b0740300401500c00070a0004c0c00c40700031070b41c0c84c24403400610040c0075140055003400e6540e036280905015060201c0c10207070415800b81003002040300c9140c8840300403252a03080210480718151940d0144d8055405200d225078034207840e0440d00d4548007290301810030354000388010001c9108105649500824100341c0d080c40c0c000320700d022418a14040030794005a00001c40c0400c40d2940015181d0590318207030225411242c0f0b030010420f0395100103000500c4201e0400448241c0d0400c107030710480951051080703c0c408054400d1582c20746820302c600a01c1580628041807041c0030728001c128603032070540090b00d040e0800e610341c0d5002140c018405450080001100241944290200c607041040b1701c003558003c0d0344030141091424418801c1c07003102030900e00e868 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 810218192 1250 810216942 810216983
    0x703080105090424020403020d120e0d0b06061c0203042001022109040e0609282006040f0e040605090606010c11031f230c09010809071203020a 63
    0x80d805150400711a04c4d88444500c030400450110034483c50f082d03034081c0320000050321000d040e064503910518070b13901c20701042a0001c044905a4000902c0f40c1042d00304c03000400c24401c442031f0002c80c151481ca5a0381c0300d80b02c60084072503007500d000c402c0500c000208130600000701440075084510202910156040031f004903a19124540d1000e82e0b210703682a988034040318a001403103540d002810111343c0e45030301000300c1c2c14004100d800c0855900010710300d214040e010b4103000440d010381521301182540c50344460b007481040500c070001702407440c6000e0130913550320400d840090000c0526010740355190000010645000d94080b68000d04003000b1560700d2902041d41c6208a80607513a80c014028941c0303a466405042d081c2c102c0c2c050180780044036031102031100c101c40f604400072000c58549800f1080240c05800007100c140ca1061074020b0000000b40c40f0100e418581c800d01c1c0036455030b01d130380f00c4040c101751030740c1d00940d0503441c20707040c1204258000c00c4c014070950003540340d0004c001c411000ca = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 810219442 1250 810218192 810218209
    0x150a1413021309051003170c0105060301060605160f0c0902040e06100c150e060a1e0902060a1d10020a0c0e0c0904020307020c0d1b120206090d050f120703080105 71
    0x40307101240000c00c00d120000b041e03071041740d010345000200c04030356075280c5443c4012011020340015060b400500721480c110f00b40103143d0442c405400802c1240d05d0028014010b004802c03851600c200544c0f001c00038040d000c000d0b400895080340080074059655030100000b98810b01c2203800c0c8420190020304540b1b050541c804507084662240c403d894401c2c2d407070002c03005400c0258082941e4800348d54000c80c408202103032003000401c10004420044c6040c1a82c0d440340004104c000d0b0303081601d4140149c480718183d43c0001007504112141020414454070100040300390f954000c1c04c1d072502008210f070f0000f0441c0c0402d000b03801c81c0c1030242e00c4407401c44100408943d66203648030304001100d00c1d030406500031944804184140c5030802002000100c1c50015054259825069103020b0b503000382901c00a0b20003040070f60040e59240a00c0d9001c02c407140940034520303119600c0c0305e202c0c0c03090003000e001c0d00e116401980c003903911460300c10703040b51810b0b0420f08042c0e000912100012540c0c5c203001c1e91 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 810220692 1250 810219442 810219457
    0xb0603090a02040203040f3305100b030a111309051b03040803130b0f010e010803130b0706141008011803020616030b03120304170405060d05150a141302 67
    0x1d000c64158903000c1c88080e44c805070084a00c80e016003440c20208407150900c0240110089000d000ba4a042000e01312295812038400603c83c5440107100441320964251401c44007502c2e0542d80705c0c1d07903649100300200744081c158020300000042d0701038801404900c00d810b40e0f0016404210303507255020210001c0001481c0c00040326010400728010030380010181d030340302a18401607844c40100f40c0d51009524015551400281140030050011030380804100307014004100042d401c20321040038507040da4080f441414558540018001c0c03e204850b00100c202e103c2a122070449400c2066845491225070710841d0582e520f800c0f429840181c108841da403815400d54001c01c1c0b2910340581d070343c44600e5080300d52030a242d520400b143d42510280003180e20f002c00b548100d500c07850f040c20100045103100c0c038040b2401d80c0410042c0b10550b00d50080c0c07046c86405e4900000c15984002c0380c9038801e140c4444540c0d00111904000401e41081540c480d2a001c0c00e50380d101e20f948210075140141e005094 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 810221942 1250 810220692 810220711
    0x90507050406080c03040c0308040801020d0c08070c0206030c0d021605010c0e01080f1806010b0a0206090a081b0732010e090a0f0b151e090603271b03010b0603 70
    0x20013042d64480d0301c0000c1e42d0024090340c00710400c181e4a5413440e0740d540c404e0f0300c89281650089441c0c01e0504451041c5031000000f030402485510303080400038194070741c0c914002e20610340440441e00e958414815905000b02d180070442d5100000170070512015143c080c2103c0560a05d4a01c0d00c015208000086040344107841d000328948540d03040c003070321450080c413102543c1c80003410400e00807010000c850080c05110041070b621241060003d080c03c0c8010252042581300e050800000b810080c210b60341c0b41110008100c40c5040c8251131818034401e1ba101d10000394070300858401801c58800c0302c610341040401c3c1d005401741c07001c0064545600c844441c03540050380ca0002601c910950704070140d520040540011925011320010700c240b0720355801b8651582e40406c04400110b02d2140d0042da002c0d00030019810714002100003480ca10004022428650803c40407400b1310564400b070700c2c50325500c103059840703122100796617120ba4402805464071075828440042c40c07506155088901071004c09 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 810223192 1250 810221942 810221957
    0xb01090c050a080c0903010f02180a030807030c0203100507020c01080a0c0c06201201030209011d1f0e0901050708010609050d02300a0204230f0405190c090507050406 73
    0x900090303407600d43c028110100309204014450042d0f90030b1060189401c8002d41c0140c0792240d45d1403100101911404141c020308843c6801d002240c6000281d81045070316140c41c10510307100c4d10110782040600c0b281d4608070390500c1e05000c1c6440d00402d0b0b1210456080e614400070341e07a06440001030ba552003a011000c103865200300c1c5c1c0415050380000036206001e400b001c50301c1c1c1500403c039044d03502c00d6100020710444100140210f02d1309454150040005c560ba100360403406942035601d150703010b42941e00c4e01c01004415000d4500c211217540062130f804050004615101c0104d0707018100448200000845400001c201035000c1c2281d54141d400181c2a02074100d5a5820711401040318100003103801c016044144036441217030302c1c500c00030f14528081c0041031902e10501080d2503a01541c1c0b81c00d030b45015004a412540c0c00001a409015405080c1c0c05072aa810f0040c1442c140000f00d0b2600c12040003202c060081034103441040300c040c078004001c15610010210755a008500980c4001101d8 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 810224442 1250 810223192 810223207
    0x6060314010608040b06120d081605030103080301090e0c0a0b093a0501110301080f0106062604151a090f010b070318050402070c0305160311041a03070801090b01090c05 74
    0x310b80400ba03002c6405401c4440e4002c202c1c40305440c01c00a08d04000010f0508400c010740c182d40c0750115242c03620300b41010750941d411a9a455042e0005001e02c2c021156030703518000c4095000c001c40301000d90083c1c450f600c541e48a0104144030740c010800203001d40e0b50440c20f0480750521202480c030555410036000c2c0d800c440701c141101c400040394015205517407101c0d101c420302c65580008500900e103038002480b859000c10146170a4403074540c801c1c2c1c14410850301002d90a4012005c2108200b40c4801d80071312079035a032400544070400340060480092501070138403035050504c001c49410804c11a41030a656840d6050b10100b03803024000c0105042050044000083c06200206690f1010030b000e40d8400d0b0f203c02c00f0a040381c004d5041502d4000140404000384075040c06940810034651030204801820764540507000090110084e00903a13030b81d20240c1d41b1b0012042c0840c00908000c050b140039965400140d03010700b0702204107072260480280006a078102c1440349095001d502e841d0603080110 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 810225692 1250 810224442 810224453
    0xd050c06090f0907091703040f03140a0f08033c1b0304050601090c020309010f0807140c0f012703080408070f0c0603050112031d060705100606031401060804 69
    0x1542816800461140c156246550f03081c4645103e25126581c12811601d003c0700480c0c0c0034504900b442d10381e081000306010001d0700794085002d41e43c000c1119003461203480351072482d007054a00090040361000e51034100f0031160000550241014640744802600d95803950800c8400015403189025405d0311252085031100612944c0180942010100040303100192822a88212401c5130f40303070086c0006200018482c4113400d1031300c206100a50070408801c0028210902c03216421050204600c00618064440d00120701c8080c00042590745801c000c0301c03420303503441c40000c031030700b455088c182c00c81c2101c101c01c0c05503061001c0441d403403a20110151020744410718080c01c01d035400380c030800010020030032110050348024821080404594901000202214010781080780840249116400800d81c80403103040691508442d20004110f0746000030494400e44400501c01c0c02043c2e20075001070b42c594041c008842842c2c5081c40025503d280d1005030100900400300804e013403a01140c042903 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 810226942 1250 810225692 810225697
    0x908030a171f061701091e0e0102160305041d0c0403080c070e040b04020906190b090301200408060604060b250606080714040903080105060309070f140f0d050c06 71
    0x20b5201c0450459450221990522041a42c11020116071121260305548140e034104030300404000307408010210846283c0d105202c900111240c1c010384542d0000c84080c001c1d03045448086543c11000310f4034a00780703006405604240700e07204442c000050504294030003032421610034090050741d917240c030b807c690341d05010b0703040101040309a2052403004200c0340c0411000038042c03030041e00b881c411441c0604c104101c0030350061080e40030380304c1c619682d40d1260006c1c0c203c01c19a1303900800c45460f010100082401400c84004c0520320300c1e60104141c198813842c100070400c3e200f42e02c003030b0781150782d40f00d05000698105110b04444684100106100794010940c0c0101002c1e10380c428443c00304441d1140d00541c7d030290800245900581c0d800c0051909065400c0240314090310144401101924090a07018052003094010000007000a20b0b1820501049000d840d00c219604000c5c0d45440c1191082400c00c54240d0040b800d007000c2600398074201c00c1084906500c070000f0010b00c000b01c0280701194 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 810228192 1250 810226942 810226951
    0x70305071410090b1302030607030905120f25080406080604241805090a12051b2d0c0f040b04061202030d0513122307060908030a17 58
    0x203610181c03141c400301c0c07828031078101000c8541d2400300d080281420704d110001400f03043c59400300400100c080041e10701265103035015840d0304002865a86174104142044451780310750b104144001244010028210080d02402001c1c0c04030401c480d2103420480701030301c7c181034083c003911010b020421a2034402c035240e6030300c408080d0010a10354a03040c4010918030748040746403444500c81c00c01b40044410300350410072620913203c0038031035402c01240300e6480341380703104020300407000a44040d50141d0295084507110b00001940311a40041c0d541c07001d8950301441c0403010b440c02d1900a00100d0f080000004240c80c0859003e420300307000f43d400300100140c50000c1e807a08680c07100303243c0d07690741c2c2e07188105001041c1d414a0312104061601c1054244039003103224009001c03062140c01140c0c0c96074081003060700c541c44810240201c840c1080c00030320754040c600c440c007850200e05030211034030b0128004048403950345444400d103442e001c109840b400350702007210004070407003a1003c00011986100d03821 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 810229442 1250 810228192 810228203
    0x13061d090615220c091a09090604090c080303091c110303160e1206061005041208091503090a26160602040503070308040612200306010e0418151107030507 68
    0x40b060f100c400800d4582000682000c00c440c02d40421805180a5504e44113041c0e54540390b103071626540001d44034074800f42c852030166507075801040c00c01c050002548050501c60044a44034944030b6030180e500d1a6820600e414401c0d00c0200c4080c40340038410040c0340501ca1009107040d81e032480c0e05c0d0742a9086003960b20b010000085039480c216100c1403208400d03440c014014106034641030081c826111400e080c1602001030070403041069100c4007034581206603001806136034540802c0c0c0018005c400260351055280d80c000180a4034501c000780c4080942c3c460030001403900c030901c298112200300001c0301020b07000100900800e0240a040c0700c0100c034460030005040a803100c01003490072580380c1040340c04003400902441000d03008610340f5807110a500050086100d1454001d214402a524404441c4004000724a49a019aa0040c0c01e12030162041080c01d2004840d406584405542500d8104110754401201a0b4600810399503803010341c01c05242060030780c0c0844695000000c290f81 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 810230692 1250 810229442 810229489
    0x5180316080318060a02070303260a090b130209011401050d02040906260c041e05090102030106030f090f0201050f04030606080606040b040b0d0201050913061d090615 73
    0x206800c09000010180c0440001141c548801d40401e1410005110b0307410311514041c0003644140303038005004415a40d061409654179032186865860084400428144c1000780208000550350198031905280d80074402040040c0c442c412811400100c20601039040042d400041c080d145200060b03c0e500481807520514004000a020b4100d0b0801c0d081100d0554607040d0411213641c00d8908900001c400160004140b40552600c0c0d6a8407030f18005940516203c4e60b80040303118101e00d02d0406662848020b00417460070406190007503109001c2c01e0007003032a010301199041054030842c00941c1d030190010003000d400b90015036442d0842e181015041004010200004009001e000006c21642c2d008281c10f042080800003940c2038000d41c18020b518204903451140c2e1a12034280500e502070a000d03641e1941d0501041c05eaa203542c01d0155103d04080c2e001500c1d114414681250f030600e40c010054544841504c0c6441c4c842c2a60006000c42400d0354034821031809100000c0c04083d000c0c1c5084 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 810231942 1250 810230692 810230713
    0x9130c050f121501050c281506030302070f051305061528050c0c090405030412030e0f090609040b130c150212130303030b0307030803190605040b01051803 68
    0xa410798030058490120044600038420410f0403031001c00e6020f482420994108120000c2e015a507040c8000d18503c011503103000c410200d0a2107961100d443e4005a070603a525290394246009001d40d8030048005100c1e81c0720000b000c00a0b09502c4050f00c000420100030a02220000c90141c00041d110300d501411450744203400503004401072400700700d02441c00c00311f8000200300500c00340a401c0b00c202804030030042841c1e40b20b004207509a0707488049503001c0081c2c0715800d0051940c00b49420500740208441c51000506070072200c80b0101e8030303040314144108940039040c442c140300180c4a5942040240300460005088203d00c0f99001810712150907d8103180d844d03000081d0195801a000103030343c500c0400603103905100c0c1e0900c00036401e8800340303004102c90702540380300e01d07a00c0041e08050b07982c49460386c07076a01808000b00458201c610540c49091030304a881c0041000c44040740018688400001c8030b0800707024200442405031a4241442841180214161203900c403195150180c0c107410b4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 810233192 1250 810231942 810231967
    0x160b0d0f0e0610050f01120e0a02040507022119081312050a120b0114070c0f140a09060302180c071a0702010f06080d0311040824060609130c05 63
    0x21007180d0100d10080c00725040000908a5500d40da4006501604503403a01c800d5030b0342c000414181d040c50036540043d00c541107900e61820080e00140080d0300c01d09160034065107542c0080c1041c100e00b04503e92980315583c448010006101d01c441d0850052048024051038034042d01c52194400322112800b000c0d141aa920200c5801c4000324007000b250010540031a020340c08041c070500000c00703550800c52401c21000192000303500c128107a1510000142c000204004601150b000b454880b0741004016100d0400174441c65000c1d2010340510046000003c00c4502d501814040320f802610400354400d04c22900f05038002c0c0140300780c02d980c4c410484003000801c0400c14240362403001d880761500d0300300400c0080c02d5610b0705032071601c02401c1000a00072108085120034600d500303030400182c2041e0fa03164844d4140034540c4100c00900a40c1548070501105070080c0d42149600c020310082961510b040100c24003401441030742100e0211a141c0243e10141c6c40042d030712200382000c40c00d209496284 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 810234442 1250 810233192 810233201
    0x50c160603050709120c05041d06090a021002150703020a17100509010503070b0910031d03030f1012140c0a0311040b03030901080a0510120503120108160b0d0f 70
    0xd0000079680b2020040b805901607003540c040c0018500d500104807058844106002c140e0090301d00c515610166200002404031800000c807a200d0b041d10724629009076040d80300c00440c07100360b005183c90816108198030100d1810340c01021007c0046041e2071300c1c0f008400030f4006107035040034090030310050300700c1051f864010340c812001d00c0d001001ea01d0501c000d020545206900ca540268030824080c00340814440503150000e5050324030245006034104114040c01c200340c4a08030202000e40d1080f04240080025403003000c0c0c80d888503400c0d485481c0301030074090360f5104110004500c08503400025980c10720030440c02e903102301142c440c0070000c000140800740540c400c581c0010302c8202450306003890301074005006002c8001c0d505180134080040c00501c002003101c8001581c800000d528401600e8089028180400d00e0b03001c00c0c0700c20700d40315070342c2d81c082540417000031000c50000552120000700302c00f04034028204c00702e10750b00d8103041040541020042d000700390303101c000d43c240700c42d002d218 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 810235692 1250 810234442 810234449
    0xc050409050d030c0e030309041a040203090a12171503010609050a020703121a0112020408120c1b06091201181b0806010e0118020c102702090403050c16 67
    0x6030a20718810350014084480343c02c5540c00340952074805d0341199901005880600c40e0a94001c60403d0000055000b00b00a2610090b441480401800058500007031308456448c411a60031091140100d401d17110540384825a0402810b00c0000505a01d4480b40c005280c100140c0007051441d01c0d481c6070011b0340e204031100980c5541c007003021803d050744000b07240700d020780c580310421032440d103070b48001c1100520210080c10f100c0008010814078640f0b0741200d00624a0b0710503250604801c403540c11095001041c05d112502c9104203124506256101c1c1310b080d1300004025515051000e01072001003d8503103030f03030011551395015882103510380c4002c11492501c40d0111003000e40740ba801c1d5105023940380d007040c18680e1000c00140044a0020052030558905024400702120403d540002070300c9490100d480501441450002654447e003000c6440159040d84400c502d2441103d040c0182d815540a0351145d4010045804a8094801400300c0040c01040e21801e21012004409001040c0d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 810236942 1250 810235692 810235703
    0x90d080c040626150f0109031a060d051207030e10021f0b12030d0c230702060706091b06020c03030f0c1e0f0c0f0d110a090e030c100e0d0c0c050409 65
    0xb24918503034a060300011400c400c1c242001042c1504584980d60b2503102c480300600c0400c40309c404500710b41d4a0003401550140e008040390143d18412088000c15003200720200c01040d5140e0035105285440200071159400c10b40c020581e0201c0d01241840c440f0341502d003001c25642c1e80c4001e008a4803030880e8030800048001c003d50380c03040129944022640c0804a00e405c00c203400041c544035141d000000a42050500d82c2e668443d2032900004465100b003500c01400180b5000020041101d000d9200c0800d60302500c2e1080f48a0f42da041c16a01e400c0315000303041d8507400410030002c11148a8014041e01060502207644c00580404d4603150044020300410f0707281c0c4001000c0c2d504260400c20800f00c40d40c2540c2400b8004100360100e294003c119100803c035981800000250b6110030b1260300080001c02400d0224200d031a01090301e0b075000d101c00e80a00e00842e420500c000409000710941d85100f04000c01d880c2c6418a400c031400c01d0310100441d4401032017200000d441d51580074040c3c102c0e0040b03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 810238192 1250 810236942 810236971
    0x30f030608031216020d14090604090203071e02030c1f0e150a1a0109090507121e1803080402060a03020403050d081e093a08090d080c040626 62
    0x1c031240442203825000d04011540028104d070082c6511004442c847c9100c5101540c8410350040020450702030703900051403e9201200300404035034000b80710009441c0281c9580c5030031451080c202d840f48219180940303130f0b0340302e550145e02d004001c1c2d01c0c04002c98858900080d455a21820550070a484078842d41480c16600702800790200042c481e40b9100121898080400340304000040c0828506204020041c0c0d0b44800144015000b80040a0700d003144c80410400300c521b0150000000c003211400300b0110303150100d600380300300a0304c58008485406482d8907009545540c20000c190388410301120806409010000008104100a1400510540ba51109850074a0000c4280e0180c0300b407240020b11001c051180044000c00d03020841c00784542426501048403500e0a0364552255040480d1b1024512103000c460b400741d5018007514a00e41946c0351a1080502260802e13425101d241c60340c40100700401156000d18211101c041c401201031200d10303074541c284103140d601206c5100c03211814 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 810239442 1250 810238192 810238201
    0x13030c120c080706080f0406021b0d0201230a020703020f01051e0901330816080c060a1b030c080309010f0c0c1a0403020309100f1416030f0306080312 66
    0x24100080094001c0b88020300380c19251410051821300060041c2c01070708450008102400941d03012146916017074005850140721440429550758200c101800c01546000c1040c24461b1410110f21142c0b18000c22280300c80d103c204251000350700c01d1a0860952181403c034050f082400e00a15204440880780800340010404201d851580000d20140309645000500c101c2003207820105184032403003482c8400007400d030340d1381c107408620250054481446442c15640c5032041070b40709441030380d0040c000d03944444018001d01c0418003072492644e001c900c0d8151514248050400308000b024000c0c50050220b5065854901c0d0310750064454100c541d46900c0c030041240801e010b000480d02d81858150343c480415180c5c3c45100040d503403100355000301040440c091610810684140e000002e082032588a50b0070005450607003564080b20218020208140f9064000c0301075a4401c0c11600d228100b00a10755030859282e03014140314020716550385008151440100040c020103c0c252042e203069080c03 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 810240692 1250 810239442 810239453
    0x315070503090c0d0b0f0402061b03090a0503070602060f07021002040b070201020c0a06140906090405090a0614010b0a030209010306150203091822030c060203070e0112050403021213030c12 83
    0x10007262180141001c00c42000040c294445d01580120714100311452a00ca034070014840d4170482061004000d43d201c080d0801500c003000a00c290001111800d003216515000c1c141c80712482d2040c42d01503009180007400781a241c0701030580c020003500c1560400c00325002014126002034001e440d2181d0041806402c55804000c020b0703442d9022503502d074070186040030003881c440503540c180100000101e01500d0310303169181940e06a2800a00500c0603182226815503901008502a2000ca007842c2e1648145058200094107a03404401308074038144480100f540070b54080f211035810169160350005244d0756582003033b803140f2400e5015543e17401c02c00080003051400303520500300b00b01602c01408031030558070748110b0f0100c0c2d500b80d0400e10b000c810700301500c1c040300c00007029244a000100700300074141c1c032901550707145000b40ca84120400000c0c11200444c2d4044800030090303800004402c034403500000c0542800f15043d4150000b036030722580d5a0794040c1440d0311000c026407220054104208 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 810241942 1250 810240692 810240703
    0x10507030626070810090b1602120c0c09040c06120506101809060b030f0c070b010608060d020607060c02070b130302060703090801090b010501080a2009031507050309 73
    0x5a8030314040c010030341006480d2184120008442504095600c69038088410501c8000010302c20079050760010b000040440e0050308901200f101c100d85000001400d020440d0094400400c0300e6000b03101050045140a14075807011700b94201d40d21403880c0d03100c4950f448518a0340309070300c2203101070011884d00a02500e002026414070000d0b43c00c00c4208409a1030325005204150713100d00d4162400644901d0340001102c154102400700d0b42030610104104030400002c5014040d02c588404560340c803014546064040d482e401440300e0002c0004228251140c1d0380c0c0d5812000051402c400442c007980002c40662110b4000ca0310540c075a2003186c00310b501800a000140300c0517200e40d24184c0d80c4025490000c805001c000c0c884c2c4000f1621505140c41985900050100c4a008002049042c2490000180b09202e10b82c00030b101880042d80e4803d25020b2000f00381000003101d1804121100c000c511604229010354041c820950090300b0010000c140364005c0c69543ca40e9662030400018050805 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 810243192 1250 810241942 810241951
    0x8060f0d2409030516080405060409060f05090c030a050408040503030a0c0b010f05060307030509010b0402070501050f01411f12140601031d0f010f0501081b1003060509040f0201020105 81
    0x14600b82c8000003194020f0215034115420f1100054610b141d80307403481c124041d90b00441c0e0013800210740400c2d24139540d800042691252583c110740543d0b101c00b040305c3c588003200c60036055102400072030340c041c1440e00801e070003a1080d150715017000d0710307075011074555044080a8030014003421746240a1100d40b802050142070700c018032684141c05e140200ea01888090701d80c038105995900081c1c41e0b00c20030741c050360122400800a554a884906101d8041d01065802c60312400d0103400000d40c500f00b010001d6410407440032400c1801ca004071992074680e08825581d00701c03c0c0e50b4044289107556041503e440c076610300e181c2c0e50781c41c11030482c010a0305034400401011a458043d491440403007280da4141c0c4210b00f464041600403c4030354054200c21740e0410380c0c0003485405d482045240045d0824009840d011000300304076079903840c5036940e81403185018940d00311200306a80b5142031030744405819900c64140824401d80d0780300440c00508048609460b807114880d42c5000b1981c1c2802541d801c03 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 810244442 1250 810243192 810243263
    0x1050406030b1f0f0e04060b03070305101e1404050f030f0717190509030d0e0a05090402010504030512031902032502010608120a030c0203120708060f0d 67
    0xc050640ea1510140d40c0090a501d01c0503000c00701c80c854404408a00002602a02203520300240d40c07054030300380185043d00c00b2105070341001200340300c609000980c1d80441e07400400600c40d15248a28a00007040b882003000c000424000312005003941c18061400401013610224180c1c0ca810300303000c1d0605004410720328158100b004a0002c42d00d40c007054a2446410000d501000104403e02601c07030311454007a114100c044200842c00180c02c8400b030403040d10141e058840040b41d4110403200040040c40c46644070005143c103001c6400d04140ca1a4803d10604100d442c00d510303519940d1401c803003100c0c6842007003400001c004e4505c9a80300c2c0f03071180d10b25480c0b013942981041006845104041c03802002c90802c40d00c414107405200350010b038020f045007420303105801200d01040020ba130081342c17594042802c00311000c110701e10000448410f80f1040000716401e40b0740c00c100b11759030f42c1e018004650041100c021610380b070b41d548502c4800c080c4034000d45005040480050180b02e031040000e28036 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 810245692 1250 810244442 810244451
    0x5030c0d0203030c07020405150301051e070509011e09080a05060123060a0c02041104140a08030a1d010e12010f0615120f0f050906090601090c0519091802040e010504 73
    0x703020308013106440034184d0446012070903558000500c40b42140f0144401d905600701070a01c0920034800c0015902c108c0d206100200565444905980c0361041c10aa14002000c802c2a101c82c20405900303201c04411601d0001d801c0c075599034030300b80741072005802079602e5086000104001000100d9041098804c041c4949c811000140011940e0044031000c0c0140710b0254885e2045541e01c1d4844001c4803518803c0540390790b110940010101040e060b41c501078501d041c0e0118101380d000081d180c407480c0e00d40c0c9883c5092416212000a0180b4000300c1d0f0600144400b44182036540d040c15a100140c42c03800000c51046885002041d0344036a40040700712594008200d000035030040c0303406110007210b0740100741410030f03514120080804001080510303181100b4086812401b244035070050079140304a50150341c0340c2c1c02034000c6543c0040d038140443c404200194405142002d191810340c003500344015040c0e6144000300c1002190f448100e4040c1e030010b002d11000740707140700c0c040c00340005a50411 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 810246942 1250 810245692 810245701
    0x50f0304170a0f1113020d0b030601050409020f1e03120315100207061d03060106090317031e06061c0605040c3f02040806100914071d0d05030c0d020303 67
    0x2550500c05a03c080c008103035036086004a41c50b40c0180f203400c0c6209000840d40c500320400c0380801000365200e068401d005d0b00d4000160792401d40101414207400500c1060580c03400350030422040c0c00031580c80748180c0350701d120b0074442d030701400705485d07092204013155600c0c9420451051442c004982c294031802c0e40254094000781e0004d90030060710f00038200b13510380d0315520704800c9440c641e0030203059240c800c250022449641c45159041240e118034a4024550419400e490407804110f5039041c6800d0465980500e0304928240141c22a03c040c00c3ca030728141503420310300c0d401701d036400c0ca03e214191102d0042096080c140720b0036240c0340f0b051403c10096814015001480e0b16017000b00c064078141074081002c4080b9666107041d0420f0002c40440d81c480d5182100350300c44d07908658250201c1040707000003d4085680c0500c5a40070071070000c2489550306c4039000d5030042c6550200d0424130010500303d00d050303100d80940701d60680c0214025a01c4800c6007070304a10f00510804903404641042c418003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 810248192 1250 810246942 810246953
    0x50108030333030703050705030105010b120411061b010501030b1803120a11040305010b041107242003010312020106050616020102150708091501050d0f0609050f0304170a 75
    0x1120302c0c0c8080031406140352802600080e074031502924855040c082c1c090001304000d00090440101d54064000740481d070b90310400c0c4070b024003520800340461209400020005101400200b06d480c0d8014400d6082888440729401d0f1611440000f003901d0395128010300501c020748a84641c00b001c00a00c40c1c03c0b004d85400100e840f8024294242110791206010034030b40d0146401c640d9400040c00920b0307441c4c035602e080c01406815103549581c062485c01920720048152030044600e42e0390849110301c56890070b1092411001e4166001c0c84c0c0c201d0f070f50825151000e010728407400c90044d4990782c0e9912541103080450060344d100c11980c01f50ba15040e030812140d141e120542d13502c1c13044244801c030542c54600041c2c2c24043ca55840d100a1100902002802600100413500030440082102d443c2c0c66001c11355078081c1e4003030107070640c4038048011100008443ca60804281481104c0c04580c0100680e03a80340f5050141417040c0440c0c0012405000003405d50868251110707030358004080401446d1902d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 810249442 1250 810248192 810248221
    0x310e10140603190c0302060309030a030c020304050609060a09080601060509030115240c0b280507080105060c010906060308030402010f08060a09021812030c0c18131502070c06030501080303 83
    0x183c0c0d001c10300b50030803002031003a241e01100085402800340e40d500c3c0303007099000e5141d600c5284a50046880c03c3c0003146010f200100b0782c1c0903a2009021989049050010090240c000c0c02c809020450a0140031401101c103000d55402803005031111515031240030b08150035120030403102103051150620030040c1d662880701d40d0034403200d442c2c601011604080e00850300c0710708120f4058440b100000500c11b5843c124030784980b0401010b1001450744c44080c1e03080c0d064a806031910800107016500601140c80c254004003400c00c002c6000040303017043e079540d14055819650066810740781c0030041005550f08040400004078003031800c240b07035244c24000603c4c00720f080d00800030304070341c082207503002a0104080c820964400405000c2071581c1100419a01c4c0e10142140540340101c0205030b44900705070210100c07041d801140c8405c59951005040e044090300c200588000160366141c85240d0b1032031008241040c00380034525940d40c20000c010f03040c3c56045c0e04c0480e899008008208002c07003140708 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 810250692 1250 810249442 810249463
    0x1030209071b031707020102131701060e04080d061205060109090f020306160306090e061803040b070c05150a08071112120f01050f310e10140603 64
    0x3503484107a261100d084a1818100e500d030070307100380d1907082101070641280c0c1812940c1507000c0b2000d190303034132403004070300380d000300b60300d9100e00d6034040c400f409035001040d000c10341c035403068000080a50380c3ea04004407800c002d58003035440e070703c000455142012049c0900005040d0754000c030f01c40c01c802d60741c81c00d54231101403280340c91160344c4a910000300850320404400840d00102150a10305103c55102220a0003800340c03c0464588480010440618000e0040e1130840344081c0c50141e4451081c8110000406000000c5000400001c0307040310458026041e40c1d8001d1506080031814503060003440140d80f03008540e507403020302000914035801b00000354403c100d454642002c07407551072007074038044100403018401d04001c641d0240f841c0401091a220b03503040f4400d0002640d9900c01c1c85200c0d404180071503041a030102c0350060208180300110904c420b042c403080354811559108004072000c14104110642003902600100030b10b5000d0000c9d40c4598910046032801e021000035981d400014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 810251798 1106 810250692 810250699
    0x2070335090607090e100f06020d030f1505040207020f030f010906150e01061409040912020606100801260d0207060f020a0f170c07090b10080f010302 66
    0x902c1500411803515070910322824517101383c05200000701185070030035038418005644041503100c580100350a50241c80015140c100060580d81400441e14505080c1600b01c41e40848a80c1c07080c0c102c400031100180d9030503141c03000c84e45001c0c0c0541d00759454080d1030f0f800b03017481c03406401403113995110780d208029130030200500c10a007501502450280c0206000184111401980766040e044030f8017000c14144940640050140c40c1e51030001c403612451055181405901007006d583c024208444d111661544900e0050104105205000d65003040c9064255a0040744042940c0c07004064103030340f4071074806640a965401684604000a0f00c071411113819284041581d090b0543e01c0010090381c4000c40c2c503401c0b508080c11082d000080d00c100302072441000100011001440c488001050301200642002540c0c0c16201000301400810410030020305405c00503541920b6044 = true := by decide +kernel

theorem cover : BRFrame.Cov 810071942 810251798 := by
  have h0 := BRFrame.cov_init 810071942
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 810071942 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 810071942 ≤ n) (h2 : n < 810251798) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
