-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4876
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:01:25.411526+00:00
-- url     : https://prove2.me/submissions/8709c9c5-c1f3-441f-b21d-8db6011bb3b2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 876798561 ≤ n < 876978417 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 876799811 1250 876798561 876798569
    0x1107020d0f0213020a0905010507231006050a0b0406034206230c0a1a04020301180308060d020a030506072001020a0915031104080c0102060a090b0a05061306 69
    0x1c0441c1e52400e600621a16010040c626034040b8810403e454040790031203810402c60303400b4601725584a01900d0220034010310203400b102e450132030b104a030b245440c0c00300c0d00c040340c1d007440e0504200c099a40da0402036041c281d80b0909081140420040c400c80b482500116107031800c01ca0485580e00b0004915511440700d0020f1868810403c0c1d00120100c0384424003000070070052500c10f11540c030802108081c902941400c06603400700041b000100181400390003d400d402c107040001001800c1c0c0f0340a41c0103030844080f44030f0b520707001c50107040420140008401a8059482d040f1582c0c0c0c0101b80034104283d01020f03a413003200c0c6900040010410064203100300c00b07a66501e18031186000c2c0c1101c048030380000464003640184402e0503c6c5d03520104090440392482e6442500c0a001c800a0700184590214a007181d01c001a0210f81014001103288084500380c0c22160360703603102402482182c0208100a01111401000c80d411441b5030300290f4003e480144941c0795041c0000da800200d03106640 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 876801061 1250 876799811 876799823
    0x4200c0715030c17100b04080a1a07020a1103070504090f050d09080d05130806010303050a2627012903031905030a0209030709020d0b0d08030a1107020d 67
    0x310500c24050011980c0c945000141828081031240715006000b14091024180385603014400154902c64020048001070955030405961079881c5d201d4252189032290003a205200da081d5611b0750b01d203581c003103988602001d901420b0301d22030a6542c80c0c1c101a06104503541072160000200326581c0d0b520800000700c1c45500070440d81e182d645401e60402001441d11005d100414804000c003100100c1c4450100101c0d180403540c03140c0080e032a00b0003800c0d0b50400005842028000b00030550040c005010b62565512035401d00c1c451104402400c504c072200341694031100202080c10300120b001d4162079000c880801c1c1000e01150010303242101e10003100303600c0301c5600308059103622581031162007a42e081a405503242c402d000b050314040c1416203003c1000c0200000020700c0e80c498550688403205d90060564101c81d0f5206940350180d040601c42c80f4040b0f2606400001c1440d007030004892007944402203508558030101400b00500c000d029000c061641004007000603540c440407500300512444d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 876802311 1250 876801061 876801073
    0x10f0c0c260313062c1204050a091806050f0114010528090308070501020a2d03020c03040513060e1308030a05060d06021207021207080904200c 63
    0x30404201110507507003200098003078039038038005001407042169846481c4210110341c09615250a1009099401d40c04529541120022003120348008012041c4407010b0308503210308201740c040e082d0511903407180c13607840992081c0c01c00c4160199003041c5c0c4c4031010030407607055000c49911081e0542d003003201c00411450a001c01400708690301d02e1000030100c03003132038104e0415080c07008051441401c100c41c5268117541c0340135100c1c802e00c1000000042c3d580402034940f0740d078403454028040d4000360f01d00e4000c10070000d101c03011110480c0500399266856080d92094a00c607a805500950003a051150180410080800c05845105c0454407910080e840082c0151801ca000f025858000d0880424810341030942c20108421406494100d030f40500006a1750320707140c0000750361a40e1000c00518150010401c0071062a0819240c4d105d40115000e441100041000c19005841407250003800084140b0254089040a600c00500b45010500310b00880c4114110007005030000c05403d08168800703 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 876803561 1250 876802311 876802313
    0xc0f010e0f032d0712030906050609090619020d0903050c010507030c170601031b02010207230714040e0313090c0c0b0a091703070f1107030c0506030702010f0c0c 71
    0x1001111002000c110145051480603d103031240200300040300400104400c0d40c500301c079940c1c0001c90750f0b241d9000c920100c114a5140014020703069076001924800d1408000400358201818800d00c070b800900c01400f45503079900403500744001a80700303e090030f990a20075081c68503124451042240d000380c44440d243c1d0600c0710035500b9101c1c0188810101410142d5040c0710942141484100314607255540005586a41c0102c00503c1e10b407038460301c001c045504035405560194002c001c521b0241c3d0045a6541d114444260b43c1114044040c2507580100d40400030002860740b4420424001000072441e202d1a0152618640101c10035010311001240708000110440c0f2890403602000d003461010a10035480303405070642e0040a085605468619810403c0011900c2d084000c13943d8542e203859080c0172100811240d00f1074060300214000c084540000780000800808072980154450956810001801000e0304080c0582c410340d074840700000002c01c05400b821403204c010f0f0352488184405 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 876804811 1250 876803561 876803563
    0x712050421021614060415020a0507030812090f060c0901090509010801150905060a05060703020c1f1106060609040b130c030c030524100e030102030a0501090b100c0f06020c0f010e 79
    0x240c3d5012200e003400c0544c5400b050b4075410192001c440c2d400c40814000d100c4464140c1c00c1c0a18220b0007415801303405000700401c01c00c20043d085022569603002d44550700c11003001d564041c00d03801503c40d54000d60010b00050032410007010110018035040850304c3d070b41c030302250203110203801c1880965120300450040e05c1208600c44010084010305108508151020490304200c1d80503c030302400c0002409000c0c50300800c1050a4000d024019500340c2e9488120005010b40050480303000a00d01d120303068100710000307030590150070300038a8540b400000c9403c003c001c14001c40a250040340040791074003112858451072900142c071783c401013188088240d006003282c0000305540e83c980c1400540c1101b626401280382403a680664417140c4410650030140c5070222020030301030b45580008204180c5400e29008541228101001444006107800400201c05100c030341039130004007094000300101e2a0314805401d270301d00640300107107402610be8041c0e003072039600d0220050580d142c886030950303548 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 876806061 1250 876804811 876804853
    0x111237060f050f0f040201051b0a0f03020606030a0309090203041106070c051005030702250b0a120501060c0503030403030b1903050a020f15090d05280614071205042102 74
    0x381c01600003c10303103407084881240321400782000e4100440840c2c0500c040101f04008000d42240b6011652690110b01e0906441ea10051085006000304008107586050008060390803aa141e102c10000c241451018402504010400d07034000c0c5070011101d00f65200d040080c0710306806482d6142413242460103006015106810080c00c01500f0420080072a90109005040d42002c480b020400c0c1000700307114000c00015042602c41c1000010b602c206190040380000010b0040d2000740030070781e0798007025034040020201c080d1458204000040010340710390300925042c00028000100c0d00408003c0940c0008281c008444903888204200150315115030700d8140b5030740c2250910164100280f20a483c4d000d10081180030f80240307603c3d502008802c0c0b244d01c80441c1261440000280c070609044c0b45035151007001c0c0e17020380c98282c401280c02c0038179841134400d4402e41c446000c00c0150001c01d00007800001c006a40c40d040f00c0303541002030000005802d105c0075040d801031001c0b80501a003e01880 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 876807311 1250 876806061 876806071
    0x20f1c0b090a08033d0e100807050910090612140a1223310807060509041508013801180312020307111237060f05 50
    0x1511900044000508042c2269070051115085407142c5170310800080c000d04408071407000001c0a00c0710300d100803c48036641e02c110f941541b034850003901c404a0240c030707841c280d020302c01160700072503004d201b681880e2404a4004400225210b1401d584110360011180c03950032042c00c58060118400c10f1004403440c03045114410006050500340079a908400220a03840c81c0c010310051070704802d00070f100200d5040c0f45110034034178259200c8140130341e0002e241044150043d4001c48107407100a8031401810781e002da44000006140060516a041e0303000d03003002814551240d1582494440000841d006000810b50180041034016a01c07a880300035003086036240e2a00d1800c4440c21101007840c40c04140b003c803080c28104403c0a000b8804214110b1542015004c0d0300c04c00840110035a001006090f5035015403003ca09503031200041080c242100301102c0240d601440c80f406000c0c008000d581c0c0e02c001c90591500003410610800382c582803c05005a03044c0f603035501100e41c1402d02d0700846502c4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 876808561 1250 876807311 876807313
    0x714190c14090609090102040905092503120806060904020a020c010e04020f2a0d09080709090506241c110a12080d02160b09010c02030306100507020f1c0b09 69
    0x384002074042000108014080c9104900903c0403680b459801c0d81100c026042e43c0030280401e1408110b41aa1000c1c2103011128841e454086003810321810001c14041d80d500100760003160451140c103e92503030740500440d0380078204004800b100d54480c4010304600d00180c0150080d0420b500002d003100101c95000d5003e540100644031440c107654003150070f001048503118841d5191419000170503094040e2610f0648500c002c03001001e5000654003003200e00400448004948501405c030580321401d45c01001a84500046884100700b460000c1150034981441d211800204000074481c0d12032002d0b42c6285101c41c0d40131b40900c403102c035030386880c0442501d24541081c64480c00300a01041303500701038840400402d20440c032035441d8040751013040014607803001402c110700f044004198140c4014a0540c07074a16181c00c0c0900100549201ba0300c010f1001600b0003220300c040d103240d03010f0f034000c03030780400500303155000355440c0b41c0a0503035014940701040c44c010152418a005400c058250606 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 876809811 1250 876808561 876808589
    0x70204180506150109122006040b03180d0c11012c01030b0411031609080109030906110105040b0112082106180c0d020904020904061e06030605060f0714190c 69
    0x480a160000d0000003a8005258010425081e40c1c201c504442507c865500030000100068940b8003000070f103008030004170017400c0350400035006982c2ea882d4a007100b00850900004540801d00e03400c4410b08241042c10402c4074480c88602840c04881c062104101001c1420200c10483d41e16100702e1040c1c400654040004042520b00c6106a0100400c00119507568681220110b8440d43c001c40080010310001e0100c519a4034018003208440e0103004001031020300079002845050080350b0007203030482109e228030b03400c114502c0c1c00001c00311010346014004105801d40008000351940c8074460100c040000c1e1f0a00c2410006146800241d201c80d240341001804244840c40c0308a5160007003408006940c0d1f440140410042c4c020200c407243d10601c0d1583c005800d107140500520f4070602640c045a0080d12940190215081da000301a00800f01b400f00f00d200100c4c4100030302009009408110b00c02203105c155520701031000250700c190541d8040040200841600150042c0c9011444480 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 876811061 1250 876809811 876809819
    0x510030b3d0f09080a0c15020f0d020705090c0711060a051621021203010b18030d08041b0609050d0606030c080f24040321180c061112070204180506150109 68
    0x300345c0030540103580b00041f480c50039281e1a8000c000815800580c01d06642c407a210006000c0d440304402d200701070107540840001000c1500e40c0c0111040554041c08040002964005000160704059507200a0040402001c9a91402500700e541541e210f044c1760844000ba4180e0300914032100c424920956102080e2030180c070f88078400380c0341940c2001d89a030b43c403049038a6051502e203c20440c040c0d010f000d201a00d03071007140c2c4003039114441c60013070031103400600d02500b81c41100c0300c2622a580000301c004c00103120398070300194815441806200b0120714203490b078550411000d16035010002c164829203010490800c280a84624030308980d10301c2c00501515440e184004034001c00003410040010599009000d01a20b1080e82d41d07651032040180030584401d8000200e0054015280c5290031000050b0840c49010300307015400900300500f0707413519a8a0f41c0107458212200c203e0740aa03c80c50700d9158800d03003103416080c1c0b5000380001d00881c10310803000741150503003003c11410048068005c2c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 876812311 1250 876811061 876811073
    0x100b0405040c171e0115050102030c0a0f080f1b0f0313060e0d050607050915090d1407030b0f0708070315061d09100510030b3d0f09080a 60
    0xb804a610150042d5140c80521001d6030515000c04010881074903404901024540158020200b82c0c40019810b050365850380c006903524081c540042e5442e03400705070014005014042c04152070f030312030b091460915014140b505841c0d000301148001a0320304140c002c0614404100181d8004025406140741100c03004888003907c1c1c01d401048140000140385503107a880c0c8501400d215900030069801c1410300302c00083c19a0f00288820388520b001a190801181040d030171514a80001004401c003084142c1e1100c41c0c2d90101120b6900c54011101e0000c0843e1146009502c0b4a41e03e52181c401032810000140840c68043c00d50740405140c4400d003074102030049200700907101e80f81800b03030b0810355404401c4100390100e0012504050404103000803020707068500360996504451300b000052008a044040b51000285140e0140c0c9a501ea003026120320307844900c40410010a240c2c41500d84020234109440d01034400c0d000a9118140320030260b40060f00c07002900410001c1d1078101040d882d03031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 876813561 1250 876812311 876812333
    0x9050105090a0203071206272a0909020c0c12030313231b15031308090604030b15030709060509190603050a0b01180207051506041805100b040504 64
    0xb58040942c0000810b58003400b4000003000740154840030302105817150202c01c0c0e008901c05010b164952400c5403200004034038080c0c8211024046101c00c18a107410101c520f080c10401c440c03000340141c159002c00d13050300600003004034800f25801004403189050a002c580c440303c903038510ba550400e1051014001041d806d2805254010b007400030a40d1549844150001a000780040741c0d01c200c4020300c5043c698403001301400002100c1d104402e00c0301a4a200c20303484210780c2a001c92420920740b000103015039000e0603c001000d4121404d0680301e56450030500030640341d441c1c0448680012192a107010010390014140310741081c083d0b46e1402020950718003020f04006814845914014452400c60b84920000e5400c002110700e03840603820100c2c0e0034403081c050040602d19150318009005031600849405070790250080c5000c140054259240360006446150312075190320001e03c20701c1115071b411510a009402801c450f052281c0e515080300c00000d00503010310705117000c00010031100c0b940 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 876814811 1250 876813561 876813571
    0x3010b091f02033a09060c0f080112030c0602032403070f0b071e0803040302070503060f06042d0606020c04061a0706110a080708060f0918030f0403050c010206010905010509 76
    0x1940e00d400f001c1d200440c03103001c00e8060b0fa51424450141803500c800c4d080c2c00402a0038000e24003000001038241c0201c40c2441021404000b10b045c02d0010000f10079503605c40401a80649044014076031759559000680c0e2050340c5d0340e49201107642e60311207658100d40c1a0800601b0880c000d040e213600e0b214502c20414440e106107200d00b4400708024052040081e000d60591114501c4c0028214240c80e0025440d00305550980051054103004605800c0025581c0d0144100641c40721103691080c003080040c004e0b80280f8038240701521420002c2c094600d0101d0407001c1a5403000c00d1060410200901d004000c0c40110710650405c941040740b142c10240030b00400e000b4a281c40e0f07451590741001c001600306000740b02c85204000810201060b803002d107081c0205610340d10804d26482e02c004009414481ca44860303400f095182c04140806221411b1407500e0a9190540c0c0c106601780c58100569041a0310030341d01500407106140c0a50703030501c4176601401020008110310750415011034041540102 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 876816061 1250 876814811 876814837
    0x303100e3313090501060f080607120e01020705070e160201050f0402010c170d090605070806030d08070c0222061a0d0207020d0807060b03060a09031b0f0803010b091f0203 75
    0x500010151244400c403110030029100c10311150042c0c0c07070000d001b40100c0c41848000c44c0c400001041200010a845000b001507035550a140350140ea04170f002000b451401c015a50750821081001903010300c040001006c080541420610b40f10207240c401c1742e030364a007420459240004200d43c007141e11202c107800c41d03020310b800c1600c1602441c0900c0c403c1050801d0005404021072400354001440e006010010720034071007401a5150440c0640e603200068421a81c1030f0002d1071f0514a0502c20502564880c00b07510b40b4419800894020814400c0c0c400f20503404902ea41840100308805805908020b02c2c1d240e804400480708903412a419000e601c80b85c415594000480744203541e6010341c55442140c00c004c21590b10235052030120001c207210340101c0d01034064680000c01d22000352281300b1040d50980c4550503031a0300303203202080e54005288112100d0100d90a2000401d5174940614042c0118015565842c0600001c021140001e04145120801460740c40c28109a0200a175110446400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 876817311 1250 876816061 876816151
    0x70b2b1e02071a0601110f0c01120603050a14010204050a090905150403080a05040303060b04090f0606031109093c16170a06051f03140609060d11030303100e 69
    0x7004071139440110181502d141f24503082c25080e4900481ca072040c2300f0098840c0e09900440c140c120042c0c50035440050069000312041d2800301e030700c254442007284241340c0014503254485000a40c40401a08004c026030780d118a1241000010031514030b0700f40c40c0c101c0ba071980341303401d41d0010700c5854020540700c0482c0d1100d010904150081d0020301c090650125443e44440d21582d50000030403004404075049410040c0002c2ca590180c400d412000a10315081403038110b004d800d0045880d0301503e42a40f0b40c2c1c00c030100c02c84815a40007441d0ba20381e18400026212440701e200c1d07403031507240a484400d030052845120601960001a042d140003034141d40d041c1c80341d03504502c030070041210b54403454018010b06001007040500100340000031200b0b4030100460000341800d005900700441750550400712281c01304819161500c0131048a40c4100d0142005e581b0000c042401c0d034005481601480b4408031052042114104215910070340f50755812010403d6100010031800d6110400c0070001d80d10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 876818561 1250 876817311 876817321
    0x31606051c0501450b0a0f0e100b120406180f0b0910050412050c03160506070f080403020a060b12120408060705070302070b2b1e02071a 60
    0x484002041c0140d030101c02c208940e5a1014030824507581d100e600390440004100421a03030300c4002480c0480f00401101001d440c0c0c6030001d0b0000c092448940781d004150040015403509414640005800a00c0c0f1303003411800c002082d642440700a030800d48050005000e034004900c3c12900d07203580103402890105000d004412a0420041280c202030b2400e0284507940d4144517022081074003c0900d8012503584c403a0162101d0104e40c81030f5001400e040d009110403030141d12400240400103004810b4900c3c00d03e00221420425091700300440e0250000d00030003a2240d00824440009410790510200d246466600291114001c60004042a07650452610b8640780c00b0f030282c072080b02c0c05080351140c4003c0e40c203004464200d886507400c148204400102d005c0e210b2400d503452503030b141c0c00800c001801c2c108207401d1508076103000c84034007808400700c00003110a061160425000d40310001480100700541c041205921180c0030300c020b0041081000003001c24032229001c850388c002010a58036a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 876819811 1250 876818561 876818587
    0x30f0c0807123506040504050c03031c0606050f07140717070f0f0e1504090602070303020705060606040f120f080406110f0105240a0e090d0e03160605 66
    0x4014024065070080c18680d1800e40d0000d02c0c044500700d0343c00c944414500d070806001d580c003266415030400320b982d41e804109141425000160801d21640070350f10031141d0580030034950f0300225070784d0b1403056000700d520b0b14901c1c440c4200c602610080c41c1103403400c0c9507540718072110b00c50b0040080071000d414000c19001007050042c0c101400445007215203100c2c0c881c2c3e0302d40d5038041c01d00486001c00884500094025510100002111011418814a41d4500e08003411144110076801d40081d103500900d000104584014140b092107510010380364203842c28480d1412000400c2e42d4041da60030441840b801d0302010034107080354030480340700303919241030314220f40400d49003080103110a82c04a000b040c0b10780c0000601240c00c130340740115054003002070300d4982070362016900f01d0201c034601c180300c01e010407211203021048035001e42000c801983c0c0701c11052a10900315400000c039002912020051680041080344038441103008000716500040000c0710348072940700ba1000c2c03040c000b50412000c42 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 876821061 1250 876819811 876819817
    0x1140a09110903010e0a050a020108070c050307060507110105060102030d18020402030f011a09061204030c0b070509030106080102190f1404060f0e01030509062205011b031107030f0c08 81
    0x10081040c032036681c0d601038040558020100c55442542040e00005912400050510b00903411030010048400316800545038218040c0181d41006607110454011802c20401031104600c50704000450340f802000003060215195807048481e4140703400c4c8240341e139000090318251408058001020030344c000e4107611003081500000d412078004010805400e1040680034101c51040d4143c0c80c2c2d081009085480d81d00c10800b115600c81c2d03091110100c05941c600320070758446c1c4241000510821141c4a8044465048400741e0000c0c100050405940c02d086c003501004020045c001c0d824a031003141c440400e2042080e245040012180c03040e030034240304681124020703001d400226616521002c00a2540c9401038241e808038051200c1013a144d482481514481d1084501400e01074a8480c00451074004110001032081240c20140000c01e00030f2017612804101c5081c4e0300c3e80400c8001002d4103660041c800c080c10180180308440200b0340250304105005d140c0d250a44e6044410710f040e00303641c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 876822311 1250 876821061 876821069
    0xa0608100807091a030312010902090126060f4e030a0806060309100903020c10030b032407080408040f12020405100609030303050411090f07031a0901140a 68
    0xc4242d00700000c0c61038403540301101461801503249420805201415620701c240d80c9041440c1d5494001009449403950140c100d00005250419034004001c0c9480104041013144140d401c580c042030003480d00d40a840841e040900340c541003140c50383c6169402840000503001c88040e02c0c0d446140150000e400015100c08510001a0345140702e00b240460341c0381c201c103150b4808104140c01084551901d482601c0c03140d01c42100420460240c81c8001c4081d01107400d0031030035407203400000852951031864454902d110340d17500040800071042014504525a0104200301030042ca03041c202c100b844040c0c607800b0440782030800742c40d15285002003a52103140d00c811400c0603d09004210150340c040d400c56014000c40b4140090f40b903c051060a01d0308900c0b500c0003296481400300006406500102e600c035026032001034001840300049243d4800031208110000b03070b214204848550103100b03030507003500f2000c100c003d1100003001080011606008400d00d0f00e83c01018501e00c0c1d0b485558980c003070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 876823561 1250 876822311 876822313
    0x200d09080406081b0301180e1615030f0c0c0209150612061014090d0303090b090102070b090105010602071a221412101104152c0a06081008 61
    0x103140d4500008000c440d0645040c0e181e0104c65500b10b1000000134256410394008956003082c0344000b580101c001d01c4012204000f030f02441c50300381c5404251002000040002c1300d0140440c204d000d00050444100500b02c20210f440c0c111484a0240d00c100f0000085a050320b90101e1522900e1501414000c2c880304607a211400103a03004007040c880100307500074101507528414880304170388152018034480c41080440e0034184079003241c500c2c040e040030350300c80e01908002504044680724840c804004844515850b0340000e040030801900d6003006a0201c0c2c5140204800d504007403009442e10000d1045814980c5046001d403425110081118010300100d984018a00324140200c0072980061182a030041d1110b200c00c5501d04042c410025110900303c060118900603803101c01c000d00035000e900c00d07928014400440c4041c0c5002800306038880f192034140c901038820010012261100d603143e40d6460b00a200b01460b901c5160f40401541d850341071086080e915040c404d885603010b588281d43e2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 876824811 1250 876823561 876823567
    0x40201050c06090d080f0f0403080a06050a0305030c060711210c1b010206070c03080121050607090302090a0605010206040b0604180317070f050a0c021c0303150603200d0908 76
    0x76030b4400a131103a1106129280c40b000340d40d646895500340f0303c08992801044411000040000e44a0f0803c0c55010b0700d4094000784081d20340c4082840c05581c0c0c0c2040311254000155a0440d42c820480741e60f00c03880c50700e480c2d0038840c100042d10742c4a25103440d10084078940215a0b200c0554110255401c2442031000c5030846040842190310f0400031401c014090301440010035903181c4a0380340c080840d905915079801c5a480d1800400e100c005604900c0188100c0001440004605100c20382c01400a07907a100352245c118010422000c001420a01d2900d14103a801c0243ea43c002c2070300c43d4400d03006885074040366103280214000c0c129894071180314130811020300c420541c010710707400e600b80d24048040580d9915010296406a004065940410000d2103510f000034821024640e02d02c3c8040c03c80c14104006560403100891515003c401294441026002c8804001c1104006020700e1406010811000803000e80003000e140c820583c034070000441d080001910742003440199030003001c0e260307 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 876826061 1250 876824811 876824821
    0x20090d030f090b0f130b192609060a0f0b0f0f010c0204060b0c060606030105280b1605010b0f090a0929041a19021b0f031b0a08040b03040201050c06 65
    0x41c0d90302c002c044122070440c030070340400c140c805c0400791456280c1e200903247c07084642d640b040c0c441d070ba14100c1240c00b80c8034100c400394021520421242c000e1078000c2c002c00b180d081800c0740906680c040c18400e050a40b910b80b02c2005540d5003184000082400d0b105200e40303192660040b580300440b824069080b0303050800000f0300d400300c1001004c1e0420b01c201918076a488100411a142c482803160303075400326075090031081c1000302c01e68036160350b1a83e01108140310780d40e140c00d140c1500901240c0c00c00b000c003629040d0a128082c003a40355413030800c0f144004d01c042c80030000303090000007800c81e07070030640e03035281e180308100c0c2045d8400d180c1c07000041410f0880400302e0120004c1e50382101c04a50f20301902c0707400d1902d81200300c4683c1c0580540c901c00f460701e081901c180302c02500503206544100c09179000304e20f5090802d002e5a115091000c01a44d0b0b154000c1c0708201007180a008020410392010300c4407004a0305400a45060f141c0001c00c569880c3c8071400100c6150290300104440f5010305c009100e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 876827311 1250 876826061 876826087
    0x70c0c06050a03151823040605060a05060a170a0e0303040521072109050910030b0714040b0c0a17070c0501050702100c0311030a020120090d030f090b 66
    0x124518040b581c060000412030800c070b80140000c1d02c20b011065445800d960411032080e004510240107200000f40c06c0c02085008030040801514207071061641c44082c480c0d5424038a26420190005540440c5090b2070240c0041c0742c003050350108041550400c000c600850680e0f00000200360103801104d1b2a41043d05100362030311024946100cac1400c03072042c10010b09003c9015152203d800084420000350300d510b6040403c4500c040020030849548000702d0207070340350411a8040c0d2444800c04030003134114a4003244d8404003500100c00d101d002400100d000900b4000c0b501525016050f450715089070059070b03482c01c8030304c40d0000c25041c200c1c0e2543c41e0440303461014104c83c602680c0c1c044165070745c071070040d035036489400c0000e0340100000c403050a085008000103851144a483d000003d1283e03c109181103070060035084005035180c92101204d0703107250455090000c11501d00e00d02d0800054002036189048010081c01d02602d00761882c1818002d40525000740952004030381c2c1d4030309030700c0b400d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 876828561 1250 876827311 876827317
    0x2030c060715060f0e15191211030325151410061b020103021309020a02010b031605030a0b070e060738010902131707060f08040807030503070c0c0605 66
    0x120b8828640240003c21000704803484040707490010900420f40c5814102c40308140b01031161b01d4001c6410003942031910032030081038000300499044078522980c50b141c0800e816050068440c440e600c00e10021582d031003001010089050580540d41c40c844083c0381900305035903000b04034520310307203040c2c54007264881012002d403013980d80031443c44050b40c40d47c40c10f8401e8811030061289902e0320300410001540203034028104040f2100c8074040e12030382c1b601c560099078400780e0071a0060351103c100c44d22038102000b42920b10950070625003046810800030a5032507a025502402607180304000c01c05150140022a40079a00588030b01da845800d030400b0900710f40340980301c0f032007000304100c42030842009035213000a4020b1030b8103070f4200342d10300b54030300c0060f400800c80e80808500240c40051500309464241011103051805085502d18050000d000c41c401c90600d00217000000e0200300000b5032040403509480c0d89814600e0322034841c0703c0100e0301c841384410000d020310b44a5501141160700803000d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 876829811 1250 876828561 876828593
    0x90233120115141209100e010b040e010605031c2705090f07090621061d06100522080609010603050601060f090e0c0f0d020d05011a1602030c0607 64
    0x445600c190410b822241e041d080c42c0600c0400e407081c08440c1c1c040c0600298240c00201100445010098000703401044841d0142881d910380e40d81c120000c1d080c1414080c08462902400080051529120200340c54450070035100c0840030080480050141c000e01000d24101100c601d9800e6581860045c8006203900c1c2c055107104d6031503c000600c124025018403440740040b036460340509443c01c0c20a03140141050184610451400d6545e80c100b003a070312800004003d000301080030020224943c622004000d030002c5c2c000c942240c1a20f03109a0020111142e08002c590b41b80000d10b18040c400c12800059088442140240000e01442c50ba05420610a5070b0050003980c01c26669000e0a440c80b1a0b04100880441c001d5101000302c0c6101c0c0c100140d100810980c40c6142400140100110b64410301000b080a07501180aa107010389920465024201992a052500d0102c03503d04510740108107902d000b0b0b1078600201011518184159450003201410958440c450391074140078030395070144 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 876831061 1250 876829811 876829829
    0x70b0f0a051e1b0c0a06060503010e15060607020d0303050a0e06010f0902130b030123180619031b090e03040f0330120b040902331201 59
    0x1061034001148140c5000300c10b0300000303100098500107024100d840080054030000203aa6404011042540041040c0143d0401504024109150010407a038850700b1490007a0300d4108150070a12000a4021a81003200103400d4599070701000a0494031401c2d0009400c14442030400c0205a050f4000600038281281d0901c810601c94803296500d503001d10030b600c130026006004012244003035005000190545112441058441c68030000c0e6a0080c2e10074001c20a5460741d125600400280c6c0141c1440100d42a5030038a00080082c0b040d030b80040d011754819140c10240140701d5100700851001103030300562181c00c41026078a0082205120b00c150003882e410003848400d058000b00417201034802004084040e9030440d15095500c80e8040702500f404124840400206000d2a00800084210344d489040d19018550703030006035200380740100d01850402840a005035038155100c81c01c0047c110401000005030700d204c26131101400038682c0c80000001e071144025288502040c10303180303c04 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 876832311 1250 876831061 876831091
    0x6010e040506060405011107050409080903060a0c0503041e05010f06090c140711031213060f05070f15060b0409020912120403020d02010903051e0d0903030c02100311070b 75
    0x1410300c82a101c04070340c1d40354480010401440f2640c090014807480c043c02e003044034107440e01c13200481d08651201e02c040e01c1c030810205801a41e07190800030280c0c0040080d000740070702c0130f0390300b000b82c494040030b800140b0038903034003500d200040d001259100a29800000130b00613a40011810801040e480c001d2040041c1032a81c0d5241280c02510159000100c00e03056603c1e000d0b041d1100385518100070f0b10075074140540d4a0848400d14550080c00d9040035190340003003018608603020340140391118185003401020701c000f4011901c10a10618600c3c0c12880c49400b000e10508000b0003800c06070041e404030440420080b0b18480641d0280081200907100c000540b04c204e444190780314190034101149000402081c4014203003409503140d01c0e407040c14402e0380c0079100c0d580c035410324190f03034140c21708040502890848400304008560b289002c0b400c0c43c01d265030458038000c00302818075001030300800301600d440482030320030350002c0d120364003d40103d0f442c0c00b03561800c00c40c154801d464400584980f2 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 876833561 1250 876832311 876832337
    0x120f1911010b0a0e06041107150b0a05090c03071809090c1a032707150c0201020d080702030703050f0d0c0c030305102715080706090f140105030a090204060e0601 71
    0x1a82000c010795005548105450382c40c40f01b00809881c1201155038041c43c144100d0001030011048094108640b90003c80c1105104d41072020b4207601c0c0d44030030700ca141e1820503c83c4c0d8017800400c517034002d18285030024907040d980c040d48400c0f8456a02c54503041d443e00711000f0500514102c580b05440d900445051800c0000308512828007065400300340f00f500d10444003500005000e031410044041200703594009640e010300c01811200d5401c0c280c00308103c0b4560404540c0d051141220708003060400e034046003040403009550380100c00c0d006003449400521303440c0d56103402d0250b0301744000c406014030502503100e0005040f001c02400443c04a810803001c9102e00d07070b00d904101d06407180044411a40c401c400709000e1800c114001903116141c0c1c82c0040e41000f1b560031940c001915150006080540c81c10794014040c882075488249540301112043c03103012001c203180341c0c5040003440c0054030380c0c039030740a40030042110240c0254854541440002e01c040c180c00414482c080c2601c4100c00c1c4000f07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 876834811 1250 876833561 876833569
    0x92d0a17031903090804060e030f0105090c0d020102012712020a0f08030a0213030c2d060f090e0906070e1014031306060f031403040305120f1911010b 66
    0x294480e1690814080019096920301e0401050501840c0101c0c140c400d0741c41d108680d0340703d03802001c00a403d035404090541400c2165060f06800403000300440d203043d80700175071a151b500b80e115102d00050342189007968405d412010030049011860820081261a00c00c058003110404071480c4d41e03404507a900c5280080b8200d00000c0d080403103180c1c02c00c100e54501916910050580401e030350700b03000a01c500324410811101940c030070310b0010052070402c486101003100ca0740012694103910500114019080b000c90b03000c44942d410302c0c6100d101000300985041e1345c2c94014141c82c08030041000912200001e1941c040c1d402c9840c2d00c041100d04805202c18440c00303d0020000c140c03200d26a18075040744c4401541d201d40c003070041182c03101e80395030340b1415110715a01060b5810780840c814000d201202000f2000001140011498680346540781500c401101500d0541110007042c041003500480d811500340440502e1010400c02da018030141c080e014000d10340c00e05618203140c442e05810 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 876836061 1250 876834811 876834839
    0x601021507090b370206010807050f0405151002060402010305010609030f03200709091a1e041703010905090c01140f0913050f0106110a17092d0a 64
    0x9410359030030350510b0a19000c441c43d80d00060181c40c60b131840305940d46070003031240060140c07000d07101000148450055070007450080d060b04035079025000130404001e990b41d40307901c11101510560700440c1070358401a42d8801c940094680310740105501c1032040f035459000c13405031700c01c0d4405d072000c11035a40c84081c2110048900e000c01000c15440208000100340901c50554040f80b4074080c440c1c90f1820f00c0c04060800c0035960050703103641d03100d0385904200003c295100070011071510b02c100c0540f909028040c010307034007404c00000242400e00490280314000048141024640d40c80669070350390780078603c0c01004211094001405255010310040d0b110750024400d10380500312040c200000b01c00301c06200d03031115201560000311074062001c8174446015135880380072048092039003907140c00c801904441c00071141180039046003005100103014900050728071607101c0404c03a25030f0b5420740821500f0407124065440c008155503410201703003ca0b20b01050002041c0d0300a640c05a4590320180104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 876837311 1250 876836061 876836071
    0xe010212010f1d070c140a12030e01050a050424140c0901110a05101107060c0e12030c030f0a0509130f0e01140117030d0c030506010e0904150e01020d050f06010215 72
    0x300702903003005c00708142040fa82d50111462054070007072251644c404446604014940c0003007a25070450f43c95040080c89220381c404864403051009140c40d40c0d811049031544024040c0716203a0a0049440e00e246501c0354005079820445108541080001035855030407440c40540080c05801c013101c040c41012a00c0e0b81540d034400c00924a25845d50103100180c15148131080e4071742824000807012a24500074182000324a4640b04442c2880d9070900050070f06e00b1030000711640c810469011140030000494040c075019101c410b845007410038003240c444c46400c10103030740201c1d0350812036401c81c000c3e0b00c0911004440d56003081408202d44a0900782c2e0800058000300100c00801041a081c1d80001901540118019031340f420414080002c1281e41c3e911418000030f03a07074800c0025a5811403004100060121448036680c41c0696411881e0108041c02c803000c6610349103e10700b94402501030340c41350412103800b4841454941d02021000c075085612900504c18003c422080803886050b8034010 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 876838561 1250 876837311 876837317
    0x3040e010807181509050c071e060c0c0b0106140403050f0c030706090536091507030e0c190f0b130b03010605120907170c011815030e010212010f1d07 66
    0x200d1402217580001c0000400991306460304200c808001865448030075810380101028462901c1c00c0d0600c402100c401c0b200300f005120807940030714041101160ba031811100645043e1003072005521104107580100e038001000d42c8101c04010540c09004156203040d804280d00311066199240001c8442c403109110381030700401003202d40c0440d40c101c0219a50002d030059400e14a60503411b0782e10480d8801100c081c03030b454004190b0869050580c68455410100380c0c5810f101a03400902100d0700d03800048400c2d03209541c00614141903150700d100e0200140040d07192500200d50710000c2d0390041d0300524444004500115000c0360034580c01050301d040e25559a2039900f009a0300c4481015002c0251001c03d09110b44440000c031212101c5601c0c0c5d10303800038000380220400c128005080c03201c0184200140c076075212405e04c0007543c2a14031621404040c0384c04100c00c003580c02d24a00910907010b0f005031940b40c034030020400801d10800c20044031100d0345965a00c40121480c2c004800e01500c00c4800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 876839811 1250 876838561 876838601
    0x414010e0105160c06150b031b1305091b0c01020d0b04090f031206050301110c0d0201062d090c030617071203050d0f09150c0c0f08030903040e01080718 67
    0x3c52203030b0090000341c0c0c414400019082c0368907a01c0700098490341c1c81503210641c0001041181112481c1c40c400a8405601140c240b02004043c04441006800380b82d0041d50754a0005110224820040781c400030a6255140d5440d00d681c450740c083d52024180b80c10030350808403d54558109031081c0c00c4000c3c1c00030162103240c04650341c11100308038101d259540041e01d83c400410a5035003842900e2107d03d0340700c14241c1c1c0e40d4080d9081030809078a0031006003507914002040164098544041882141124120f60710440c9050710380070701c048540084c8a82450700c90030a00700c0f6015408081a100d07100050481010401c2205569236500d0040001902d1080340036000280200042c1000710120417011039082464002c81003101c010000503180c20084412081d844040c51142841d04000da1504c0c15a0500e544c076440c4040083d1100180300010000000b01c066000740f0a4402501200d418030301c142d60740d10911980c41c0c01d54040c80c1d240e90549098000800c41622803911250b00e21440101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 876841061 1250 876839811 876839851
    0xd1202010e07080307170408010204090c030501050117010b0a05070602130e16090603050601090302060d14092d070302030a051011040612090602040f0f03050d03021e03041a0414010e0105 82
    0x8a001b80031034003420a01c606020200c0e1a403001e00140c40a00f5200380002000c0801141c02401c1e908103a00075818458028400501c3c0007001c0c1d003031419103e40750001c03941c90400c403074110b6aa204611020305041d20120380c0c41c4010401c00c054800300e821a200f0044142c4804030348608034419484044003080024104011045c065003050398461014144030b21500e03500e03004503503144e014045c9d01a005656440c0c0e200020341e116503180c0c00c880500d00400d400f4401c4010540c248880303441c894000700d0319014050030f10300c0800c0444040c560103810760b00400418580582e03114460030010400302e040c265001707000d00345070080c0c82c1110f01566034010b8421602042c103000b003070340450a940d201e030200b0001c034040203045400c100901c600c14100161900c0c600b040da00704070381e0541d80300030580100520f00000c290000c100300082c9440003040d44e251101d14020354405a07001d1440210519001080700703000c1b40304046210089030000038000c030307090000428201c4201702c1e010f40201d00b41e030b59480 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 876842311 1250 876841061 876841073
    0xe16090b01050f0a2c010512100803070c03050d03141906080607020f10020304052a130506030f0c031f1413140d080a09030c020d1202010e07080307 65
    0x50040d5060420070b15007107442c1842e0160b5030040d80d04101040e62040c00e0748040010441e44040d940040203012034080308a00000c000d40301d081e0600010440400c045010b0790420342c081802050075104495940301d40703147c420040d1800d0300c025074041c001e011505003118003d02440148080c0c449005030750f69115800991aa80803400c0d41d101c099840c6000303d9a41402c000341401440b00340c000b465082c0e4503142c1203180c013108012171000c2c030b801402880001234001402e43c02490400c0c0505203050501f40c040d50b10001d00da0407090740400d48000f015040c110991040f40140b10507400c1e100007810540c085640d07142d40755111030b010790001c0403150100c0e00703165884202603201031010038100b000d2180300702a04801e4401c410780312241c0d0f007500e0030880c89501004100c0c9518015200862000401a0078254024080100951174404101c100362050801c15940c541c010401580410302d4102032400c01c0303084d045030000d507103403c0c074100d50418005052001c032030500004500d4a2096520300d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 876843561 1250 876842311 876842321
    0x10050403050702090708012d09021c0c03090614090a06051f030804060810060504140402070203030711040501060201110904020a0903052406060306030d0c052508010e1609 75
    0x60302004428442c0200590391004661300811091b51192172550602c3c4034104102813400d0381c03404005043d64042d44c20460521008210343c02c5020041c2c0b038002004c2e204500c2d1403a0280d0304941c51401920130030550700740c0c1c01104980d005003410802444168200c1120100645420b140b55200441950004852740c111540c01085d21030008681103101c0c5a000040550f6041240e484102090030b0021a0f4002c0030b10340d0180130240c41c001c1091814001404900c518052074100c0241000b001c0c81c16150f80e0112084079502a080325a031f440e05003002040710340820400780c800e40c104000010810310502980015203040d010075460b003024401000b00940c4185c3d40841480340c40c403030002c0464414440713202200c120f219400003ca089406510303040d4001065913200712018800d0000781c0d1400141e6601080d4507051081c500c200070708146250900103044070030003074a4000c440a007819150140c0c021154001d00910800d02d4003081c198440e00700c501104071070740300081c042099041503001 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 876844811 1250 876843561 876843563
    0x70803281503060e03070b0c07050102130e040c0906060509010302180918010509070605040306090614070f1101050606161718010e0102070e160201021309050613020309100504 77
    0x100d480d00d03880d103403800340540d04007214608100315554070400902045006a00f0b0303c0c2c8a99002c2e51810400d982c0e42032441a01510755202c44c407001c41d2100810109504807030320f91b1610301c584040140c0e212650354000800702d8003207a07075103420007001a08070614004d100072307611651912030801801e0b6004500941080340c44621611200f2403200c01a120025558011010b80c0070b110f00d03441c5900141400d41c1c8014040000e00d52101208000e5150b1103001d880036030303500460110340d440240c10804041d002c0c848000d080c9200400c14070081e950041c49101c0d10100780c1d26124000000588007900b210400c4621980080c006c00080d1790600340c04c0d0309885000d2040d0080301c1c80f03040c800703103486441e08041200c00c0d44000409080b102581c111541f00e070000024402405890304010180e000c1c05d070041d0501260b0610310310384215081c000e40545041c0401c0e0840003000035900c2a401001d000107840050240e11289041c400008950086921541e06403004118010700f1321300b100020500100 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 876846061 1250 876844811 876844861
    0x30604090203010f0e0c1c030f03020c0102071205031e0108060604091e150f0507020d08100b030a1b1b0b1905090a1106070f060b0a0b040303180506070803 68
    0x1e0000300e104002d105500300090b12500405112100c54144000301140c240c0b0203411f5440150940000b90307020101198402d01c3e80b802582b6843c60451950182c014603030010044103100500c400c034964041c1c040d500c200e80b207050344c0220b04210403084240e501e007030107200f000c0c0e000100044d505040c1341d00f242e06681d01c2031140d401000f40c07908000a054000710412150f076400782c00c08494002e094010815100070038801002141008580030795104240410581030100381c10000d542c94582c1c042d90b10040800b641d569541c0d20349528028000d2030264501118900240700d01540c46104585400018504026000c4140d0254680c5142460010079510001059039880c042074005801524020b03a0701c0401000e4a80707041c544070134200950303003029014840900a0f00b002c00d68140e540034aa030382004000030341c0c21100c0086103407076030b05820191074603000080001c01c069102403604032600100301400951a1500c3c10043c5030b11403003401410000d018070203c3c02100130000c1008486000031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 876847311 1250 876846061 876846071
    0x70203040b0c0d09060e1825120518070b0c01021b010b040b030606010e090604140405061b03010620010608070603021e12010317210403020d09080303060409020301 72
    0xe4825031082d845030151407010303045420f20480382504a9088030241c2800d0174050034001a81010401903442c010b5441c0b60394a0b04000f050000f103c160901d01c000e03a1b6030000041d0701041010240482c8400154001c49038507110010b2032402a6101040c81d0390400340150072258684905209a50801854130095550800030070250002c03a1303c44c1c600e081c200b00000300c0d0040b03013002000102c1e954158064000e82148003041400d84c3d0012441c01c80b5182151107000c0c54803007001150061645da6404040c04850000744030500c4800694948508000c110a05c4504014662603009001c2840b42d0303400b18548119903421103848210101ca0b064410000080e543d943e1124039142249940c40b02e0080707540001c195290600508842205080f603048103858031201c84a80540e1402c14480501004d400f01c1411090065400896030f038a040218003a403450504401c000b1070007020b441c12005840b59007002c5180e2402090207404603410f00010b14210358549051001404001200700e81c507560b11 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 876848561 1250 876847311 876847319
    0x2030a08250b0115030b03060a1a0918120915070201020a02030a1b060c050a02040b18011d060306040308180c0607060510060504030816030311030a2405090f07020304 73
    0x3608152030140d001d1603403442c2951400110180e50960101d60004250030314000c0c03080c039240000e1064000c84041e4001820150f04030301c811149030048482c1e644550143c041c0441841d044425800500c80c900644d03800070344841e807000721481a000c011340c01c08500b50102c008011604060914140180151208030406c1d40c0000e09003904500111450b0300c40601e110043d6403184086005000c4074181660601429102c0f07070341d200c0302000004e20494449485c0c03106602d4042d42c4100b127843c2c64000c5032155841c1c203003606c440c1c5c016924491860b40c108001840074640040c000b40215090b440c1c111040c1c0f14640d41040184003d070821600348104164070784952103c0c0f0092035418049e510000300750a00d140742d01c0404c0f92aa110350200f10f401e00042c40481c12040885d0100c142d40c03070310750083c10010310f016400b810780d006541505c00404010012941e100d5080b040300103100611004816000ca80349443c0f45040e4000e040d000308180300010300078411500b080340c0003078050040b0307410300c0c2c0e80b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 876849811 1250 876848561 876848617
    0xd0b01090b1206040317090c0108010b030a02040b0c01020d0c09050f04050604061a04052103040e0702280204110c03040501030207020f09010f080d03050f0606030403090e0702011d030702030a08 85
    0x700380c0e811170000d03a03428003408088252202070b517004540c00c030140402c402e4143c0024554803041c011002c81c2800000851040c11107541120002c11680710b81c2034032001c40c0c2e14003d00039000969070258507800d115880c03071850300c1000303410280d600007461140c04c20040021300c0300420303000b0a0f407604640d60340710200d00100381801d0038001503480c100315a0340c0c40c140320a001c0307480c82c980a50540040b098240c0500c1304000f00680e400e60312001044402c80d95140001c0f890880c000c444c00e00d00c1109068604401990380001d40f206500030b507003d000340039045140d14441e1240506075016504248018020b030361185c0c00400032240014a01000a00140c0003c0c41c5864203030300c552441414000104107021052150f00c40441e202d0500300500d24045503240c081d001e008042c1407080038000006403c2500991060f400307031041c00703000555032800d460007a0082c00c403078102d038004550b0300c00100000c1800000319401d0f1a0302401420381c208540c0c0d5055400d4100d12003604207a04051000e40c0744d004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 876851061 1250 876849811 876849823
    0x10b06072405100503010f050c1603090b04030b01080c091005121203130b0702030906041205100606030c0e1906030c050706020a0c17091806030a06110301140d0b01090b12 75
    0x880ca0034107043c080c0707401c0800d4219040b076880c01c0f811908000c108090813a0040039100c52825010709880d051110b0b150440d4041f116401c019030300303000171a01206000003a460181a203024404a0720103011180820104000480d030340411890b44501c02d00c50783c2800000020191400300c01c9070b10003403442081b00d523585c008072807000700300f00c02c685e80d18240201d010341c65810442d580095454501542c000c02e965108500a03d030107907130215000001c004082103a4100541c01c40010042d10792902c1009024200c41501c01c070004001d0300368182c1d503107403204d090007039402806003000800f494904150041c140d006440c005005c428400200400d1281c0001c3c860303281940c0c0e540e010b40d01146011081c49222040f900c95094061040f1000364590103c0c9041c2e0002c0d03121008060b985410021313142c4200c6030700c01032000d800c00325621741d01d01500c0040c6050f503101d0417143c298540c8020074000c0700c80b008070028160640e21001041180255804805005006801616032121050000746064 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 876852311 1250 876851061 876851071
    0xc210c062a010905070f0e0103060c0e0907020a030e0a0b1c020403170702010306090203040503070f112d03010504031e05040506041e170a110310150602010e010b06072405 75
    0xe5100c3d81c40508102d801d103d80f00140511140c05600d003030803c0750340d44000b101400005c11650744e500302c020b0024081d0041e41c2001000800a40302440c0010b4000d49481d80400c0850120b908035410380700e036240080340001238455200d095414100250050382410420010380c0c2c4000c0c0d0700700030100114080b03000310801002c1c80c3d107031260b4500d03040c40014100e03a00399200882e42071050040c0800a240401280d1481da00300702690b20040075420145e0603020340d02c054940c0845c07043e008450f20460900010002816400c044111949080074103003030310022500203000810206400c852404132424400780080d852810702e04003610794020034040e50040d0401a181d0743c12144501c1100c600c5070b50000a41040c10040c0b40048683e07103c40e40e13826102c08001c0810b40103110510403504e013044100032202d003446041c450f00c038116400708401c1d440c5004040040d401d18440f04072007501401542c0c40088040c1800d0324007005500c6000100003903826889001c5030b054100c004105440c01928020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 876853561 1250 876852311 876852313
    0xa0c0f0f08130f080a030e121510180c050307080c0409020a0801050f040606020303010603020d110409140a1b0509130c03050916080a02040207050703060e0c210c062a 73
    0x19074140040030f41c44003010341c0419669072103010074030006503024a10400803181910600c0c04a03044058132410030342c103500039031302c09080c5c4410882d1040b4580051411141c0c43c042a000f1602c0074204441034925034400c10003c26000c1002c500110300c603500c0c0907072129030f02c00c50354105501d4080410517a8400d405503000100320300014031040c0b03407554521000880131182000ba040c902803000c1d4590205104050030f06901003520a0706007456000110411031108030540d0f650703210518000100120800b444a01c1162400202011001c0c03140701807183d0003a0703010300e4000040034101c41c01c1e801400707115007205411444900e824114050f03500e24062545011440d4075215440c285810342003955034000f0028124108070056002c54482c00c0a50150f60169450f1000c0c100f5501d880003640c80203103003506d0206034074900c40020030741d021038002c12182c0032000c880c03d00044503401088000808686c10014140d0b0240c03600c24000c10f907607911000c00070710701032000c0905410820404004045 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 876854811 1250 876853561 876853597
    0x2131e0905070c1703090a0305091507140d0801180c05090910140d0308010e04030302070804090504060b0a0b090108060f10050d11040e04030c08121504110a0c0f0f08 73
    0x4001c2c803104413409200c86040380b81c1c04c52a001e010291b40c0d100002002d0240700380014510380e0303911041d000303013111030040111035961681894100c8540307501c18121a85801200b1500003620311503401c0301c0c101e90203200c100d207406001070345c40b01c02805552a0b10080c0304007041961201d4564451681c4a401103141c0400c00901e440c4040c01142e003506403881c49034800144010000b500004024150341d041100c4901503602c502d801d4009100d2030102030224803021400180c07016158100c50310540c49120309201500281041c05017050302c501481c1c85500341400348030565407090780c249612200040c01e103402e6143d050301241809140302a2440060710014036100c1356405402090541d1102108007031400c2d03c0d0900180100b000508018204541070f07001700140002c00080d1058407161410305580e50902080c24000100c088030201c7c012030070003826000c3c03910450b05035240804507450300700125055075603569003045003801c2102c0b404802e40d01040403c1600002d8071140d4410310703440360 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 876856061 1250 876854811 876854813
    0x11101a01120e07030b100806270118060c0c140304050f060702010e0112091a06031504020906060d0e10150f0b07060906380402131e0905070c 62
    0x1090903008440d0407452400c0001c00b248060000544004881e080002040c0e80d0701c41904611407030805034041201d0340305080c140072454a00002815105803818001c00548483c440301600f40c1e0006046c00c240250400d02c0b02002c16034a42003104498194500740d00902019030350234400c005812141d17081a84082000d2085081c80f40c0c00e500b40c3d2070100c0c6c0039402c10010790b0000b00742909452000c0d04201d82d84050740440c542d26000103102c190312020480d024062049000b0310524200c0e0f003244240311b500b41d03e0031501141c4c034000740100e8014040500b15500d000070301200d80d0003403108090055941d02105400c41c014049039003210b00e01071011950410b0020610100426034010418505d03ea0004000360a80107040300e0142d07500800226a050342420b040c4e004144030081200301c00b9034400c174191244031842c284400580000d0350940e032514100280720407405020b038200b00001c1043d00500200010307601d04a401504454200380c4103840741c400e0025208140c52200220b511010150 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 876857311 1250 876856061 876856067
    0xf0a0207020d14070f03080304140f0a051f02032a12010b0717030f01230d0302060708090d082e090b100f050a0c02013506010e06040611101a01 63
    0x11009000e055170b4581c41c1d5003540c44941241c8405440107102d00e11140482c40d00400034000b85a0004c505016140c04403000e060032501c5000e0b44c0c00502c2d032030b41c5082c0c27510100c0c406403082e2400384c00c1510000325152180c1d09000c0340e0001d02c2e00c46103000c5005010300320001c0084076801e4040d043d600c0c0015110282440e044400d151604d03203040e680c150500420130b491048444060442d0340c2d01c0981c00030a04954807841d001203d070a0100d80010103001c00d8400c0c1600041d4143c01440180e0307500c02c203641c5012815488229400404000030600e0000c20000a10840a402c0c1c007251140760307080c0450400e0711440c000b041d41e400700032900c0e100e1034003944519020045107180546820003207002c6446000080c072510490340690140215070319008196441110342e800c2c242008514400088105180808d500700c10100b00c04650320031000045c099481081c8001d00b5820140030729040504043d402e4a5005a41102507028400d0894106140b0840d0213000c038002405503100d0090079040d8001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 876858561 1250 876857311 876857323
    0x121113081005060a0e0a0513140124050a17101b090905010e010306020d06170f0c041a0904080f04060c03030e0d120f18051608150f0a0207020d14 64
    0x3c4c0c85061440c0c2d04014003100d121200758412180c200001d81981c80280c89650001900005404c207018a0508601d0080541c000b04031001d141c461210700595100002103210214050700784c2141c44640c00300009050350214019555050041d506800c0141401c5012500d034030002102c2c240141404000c42074110081402926200c2c50500156061007015802c0c094107100040c110b40d400109100940074543c0248080c00000407030709640c0308a552500d03514406003130402c855009140c16402240307028411046401d01981b10750282000810402c880b84000600a0711510010002265040d00d140010710180c0216107400c1814140360a0060441700d801c0c1c0f58502d2948000f07204048542c202c007402800c1c1480a0300070814400b098200809071283c032400b2451300008200b1740c1d04115001c01c4001c0020840c0240e00740c0c0e180d84a05050342e42180000100c2c83d054904041104070900c07031181a80f000030b048000d4500551640421600c2c5031080c000d0710b5200004140d040320141c24090 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 876859811 1250 876858561 876858571
    0x60a08030f1b011817030906061512040c050114280924031d10110d060b091c080a050a0e060c25081b0d020d0501020405041b121113081005 61
    0xc20703040d0311f00820711507a90000540000d00c1030a03010700071040d01c03007103208071040d402c443c1c0411007071400c05160403e40030089010b6907002c208a2442c09513104841e9042d82c1ca4401d0500940350130a160b0700d201c3c0340100c0111251070400618450224051041d039860100c09901912801d25083d404007004088800140e13807000f400c600e4070b903024281d03c0b00240d00c6250350342120000401d600003c2180d0100d100e510b0540f0341d0035041910004012640f01c0c0500101e01081e50200e0f42102e0111404150561100c0002c2000b03038144407030003002e8490070282c4500221820502000a1100c000070703296000000165030300d5201a0700d120010501d4002c480c030a01d1030309403070030403141414104c03629440710224107414520318a0b400c68040d910500d294041940140204000c6881801c165000c2e600900809000b281804408541c64070510055200c0c400e0961304d500051040140a03c003410b500c2c0105c070000601842100303144107070105103a000f00311040041000d414182c0175071042e01c80041c6 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 876861061 1250 876859811 876859853
    0xc060201051006023d0506030c0906220b0d2406060903020603041104060f09230f04020a050913110d020108010b030c070f1a060a08030f1b0118 63
    0x82c01c000079500095901e0b50400e828484941809801c000c0c0c00002007800c902069030360307503405841c0c4605c01503400140109000d030156403140384800700f4030440540c203882d25a000300202c005541040101030700c05512007144031300800c00100c3e8800040b407600041b50143c0e480c581c003141d240c1f10b00c40c652003948049042c0007814030450385450405008081300c0d1001a0090400000040402c0741001c0200c070110340090040140c5a26101d0072880e03c0c800340a254440b6207422544050f8a15212050030607000c0e01e108240695291900c0d43c900b02405041242c01c503030320b076402041c00c9e6100c0405900c03074585200344100325003143c10319092048001940a0180450b1081a1302503644400c0c96810341d146140400c0e96500d800d0b900b19102d2180c0e010181c0340c0d90001745108100081043c60564040c1e00b4070130003002d13440f1403003005511001031041484540c03080244c01030450b40c5030041c203d458084458040d40d640c040107201d0a4a284800c081171808418284c807003081080c1000c0401c0b496114 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 876862311 1250 876861061 876861091
    0x50301020f2214041a031203180c030a0f0f0506240604050d0605060315070f11160314010b18010e180d2313061112072009040c06020105 60
    0x43d004050328100140300030301458980390207054007900c40f006040b900c0000790482e883c0403520b2261803010341007940d407600c1800d440740c5988500306001075007040101c0002e000c0c2290b002c2980d15110400b03000c1c2c00403542e0500c0720280308080b650602c44036200e5806000d41c64070130380900380302403041e40c03220b400e8a115400500050080c0d4580364a041d40d1103502003800a9552180ba000a180503402e09400031100c0c2c4000810505590120000800803d03940f501c00c08981800416500c03030410005692400420280403c0842d41d0f220900d503400001100008103010740d8004102001801508140003070b100c8001001440804a40e9590080012841e440c030080b000e0300c82512a8003008e014400c0085c507080c1c0d01240c81106080d030801d1900403260300e0751214090304111000c2c055114010118580140c8405604004150044d141c001417500ba45001e042e50f0760115444000f00032440800241111216603458240e410350180d03020310760082d040c0b07250040081c00e4450050040c50002490 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 876863561 1250 876862311 876862319
    0xc030f031315140a021b1e0d0501020c101506140306010311040906140310060302010503040f030306120303090c210b19060305060a0b0d02060a1b020406120519051905010204050301020f22 82
    0x14010303c25100c400c4230003000030310b10f5040043c0680151a456a0700d4003410701b40700d03691101507100b5040d414204500d08040c80d03a03404d0584428000754009040c00d2400c000140d0150312a80c4800055901c00184505194a41b02603600f1240d00d5005203114507140d06680a040c54100103035a04010054824001ca60941d40001d02600002e08001c040c1483c0000020401d80660404800391004200030210f0603424100100980700005058070382000342031002c103481e880d801180c00c1041c1700d00800708410002c0e9070780c0324980380e00034424103029010249560a590040c0100002580104024880350800c032180c0303002c8490b8090b586120740556010100162101c0041d100343d1141d5060940d02090400d080b03c44d03002c002e0400a41c00fa203850780100e1842004036200c00310900031000ca0311514106558045856001c040c054007a13070012072102e0407151240100d665451141c00094103046d5030317901190990b00700703001070800c40340c5c046141980221003851182c0341c100d000020000c1c2510b0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 876864811 1250 876863561 876863599
    0x503151302010c0c0e040f06050f010e060d06150f0611210706023c0f03060d050a05060a060e060321090604030803090c030f031315140a021b 62
    0x104034802810711100c66814820300c4a003500d5078009140d1442c2d0b0100c01d15281c42c081154601c004004c50340545010080f890741106818020f0681c0d803502000702d525290701003006440c19034070b2000c0320440d03100c44000d1a40d8000d00c8610005041681d50381c0811410020054803580504259050303a81c0007078070024200d40c1982010341040e0f840354000d590340040d4144000039104a07001903407501110301c95002d414501d0501004203050324850744110089400c1c0400c04c902c210908661103d030300f880880d055192208a108602c5d209100319000788206580b80781c00c20313000b110a4468240e0390b03a0100319000c2404c2402ea80046c00700c0181100102411020811611602d0300f002c1400020501d0303203c03030b00d031a4200ca001c3c41e0800e00054403468134240540d910340c0e0f1207c070240a80610380200e2030f44040041566221800d0640000c0d40c01d050038240d5240c1c10080b03e40718108000358040003401c500b0b290081680400c641d001d048441000054100e00072070b5044030038000d013248404590920f80c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 876866061 1250 876864811 876864841
    0x80703032019090915030b0114130c0203120c1201060905060711040e1b0a09090c1a12041103070503031903020304021215040620070f15060f050315 65
    0xc00b101804100d41c1ca4812280c441c100d402840c1c096140c2540303c0211103c040158003105c1c41451410041ea8860040c0c541040440c10000e4108154003d54a5070000076008010f6480d01441200d06203031346546010b50384902030b92040d003805400207101c641005070b803070042c3c054042410301c1104540b901c4003084040c4610f440c0075190000085aa0f80143d40c2c1c0c2d006085005614030496103860044584100c0080c07c0142c054810b1002d080000f03240e5100340030300204150050310020701c0078901a2502d0f013081d201c0e005851b15240400c84052080041c3d00351600a500440d1505035003103172032007410304d480040e03003000388030344d0052128866483c07040d000c130100428145805078480d102ca20115030300d1180221664090300422541c2d42c507401c41404400d2289010342418004040741d03520242d40d244000340c075065030010800c02800483d803030022200c603462164003c1080c03511001d481d002100d1150300510b03001c2d0001c3c0b004019501e01000048207540124410300558180308002e092000307 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 876867311 1250 876866061 876866077
    0x90b0d0605091f021b010608031207230d0c0c0b13030e03010e15071b020108070e030f060601180f05190810051b0a080a020d0207050a0807030320 64
    0x50345072000250048418400b81c082c2c07442119000e4151000c1890b444041d400c6194010124040713240e080191520500030f003c104c1d5024805180b8000091008581c10b0000500c02800e002195107450000f690340c8070959105051000096156042840600140e40d840450b40b000c001c000b40c0d070040454182c05104c0e41159101c1102a5180841d19003550600c0e0b40c054025415442c12880134118403010400c2d10174145101040d41c00c5641e0342d002a2960b03421b6006002ca00451240554015401040c030903070002501e0500031580720403000080e02d4680034407e24030854101c130041c422256002034052007041c54840d00700724224108071005109a400d44140c40c131415121036103003a03032011041098003400a034030660348080e1046150300040c10f4250b488005600001c0d01c00900e000515080c0c40b0306103080d40d103520b965140c04403250060341020300400c031480e50030000030000500030410781e04d81d0b500c105201616a2510300780503040700c000031440501c004e144903d00f134107284071500b204c101c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 876868561 1250 876867311 876867323
    0x110d120b1815041506090614090d031d0d0b0a0c03140403020609160605090405040203120406170f101517071e0e0f0d050109020a120c090b0d 62
    0x520100e40000c1c09001522980322185032584203210b00072a4a5041454003441594203205440c60f42400003030040941c85600001002d0450910005d445001da08041e26580138400d424800d070741d000200c0c0e5074500324040b00400c5000909010540c14007005031115903003241c4039508120952900c106a420007001070820599031542d100e82c5d81d009030703c500d001c1d0b105032110001c94a01807a001e9a01d038070a9a0b00c15051144012000101080d0b074941002e03030704660f5070142031001d50024040a004050800c0b40e141c011900100010380c520300c003410050109544848600c42c0d982980040350302c4c0030706443c81c602c204100f00702550701d9094081c030882c0c90005061401c81c02c0c0d21411901c0c01c140d240501a482c0c0c84038103001040350f1040c120f10030244c40280c541c0103144900d0302030300c502031241c03c6150080403c070001110b610b400800b541ca014012000814224003d0b40044c49407600d0780c2100f41d06103150708050303051141e19007101e4050200084108040c0140e800012422211f541b401010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 876869811 1250 876868561 876868571
    0x110c030a080a1503141b0d020d150f0b0a051206011a07020a170f0a0231020a0203072607080c0c030d02010b040c02010b060a050a051b0c01110d12 64
    0x4070300b0035a02400501800c2240310380c0d9940c8a181a0444d12504001d040c030510072103120300d1030485e04c2e003e25990020003e110340c502503019800c0c0462100390402c160f6104d075488015400259060190713078007041006900140355404a41003148035074041c3c000d0b0340181c54108121440c1f0000003000350540d5011070a20130a81920040143c0030721031440300940105c001c103000210102880440e82441030590300f81c0b9851300c680210395560315070520010358054030040740c4010703440c00e141c0d04540c1e407102c902d01400004069201481a80c0c01580500c0c0141d10014000f000e000d0580c2c0f490074501c23810840900d60031501c00303590f4014050300c00083c120700704c001108482400c0800c1004a80c00740036003900d030310901e01d143c06030080400561300d900440c1030120b145c1602d803041c444d42901490043c0b1043c10a8400d0208403000c1d0043d0740b440b02405002c104607040100c0800f401000c4203141c038002c2100c07060170800106040f04a138103004043c0d1060720017104080d085008098061140032000071 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 876871061 1250 876869811 876869821
    0x302060d0b150f1806190806120115080c010807020c1009170a021c0201080a0f02070b09070603110301120210021006090504060b100c08090f1005070501110c030a08 72
    0x380c440707124007100004007000101e540c103e94440700900040201810004241442c0c03609002c4180300300d003a41c4030103110600000c07500340d000703096041d0480c2002c0c1800c0c0510064075401400c482d0041c502c000700d11101e010400115400304403604003a1020300e4040801c5c00c0c20a406941c1e50882e50a05114410340c2c210341250340d00c144103010017409080c0811401041d80076411b500e070942c01c1c106a0082c51344030702102440c00c00c0341c1ba19a200380d060b0355070201581d58001d400001d00f10a000d241110342c08004a1010a10710060940100b0014000d03205c003614100000c0d00f210400c0c105845407400501c010030a224000d6940762000c0e4058400000210b9402c42c120705102c4035800c1512420314242d40407070480b0b0039520a070f1003984551020000d00001c00304004258540300c0c858800101c00303e020400148800015245045d006090210302d48458000101c402ea1002c503034100007000450540140a03007400350f02c0c0c8480c144a030042c60803540980d140d4072403041080241c14800c0c810b0100b0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 876872311 1250 876871061 876871069
    0x417121c0b010c0b04030e01081605070204020d0b09012d054006170c101d0a030f03121a01111c031e02180d0807061508160302060d0b 59
    0x1d4495110350304ca09246810b24014042d104403000e05070015400302c00140030fa07060514130181030355558075420f003032503402d50800c406035015036517000e0944d4445a003000c40361580107010340642030740002e1801080400c03419250017042d640d90b0000c81c5e522110104042d880d81034501c144001c280101c01140c8404844031149400d040f4080740c010111030a8100c4440c101da8000d0095132041c0301480d1085699590141e6034080d603407086540414401e402c01d5466008221080c000528040d2050305480c6950000e01c91092561050300c48501d0000c1c0003040651040d00501e09404840041261000f04203840c0f80813807811513603278184007074030300c81800820003041144509a00f80c030f500c00d0b14501c1c000004001d08194084803010303114482a44404210714020350314850300310280d044250340828200405070700070204c2990036403020401c1d9804503095005c1c0c001c0190a2440451440303280c500b03550311700078030003aa0140c2c00646000500040c0e403582c045414100c0da0b00c0020400c060108002 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 876873561 1250 876872311 876872327
    0x90408071b150e040501030c12140105070c140a030f181a0a09080d1202070204060504020d09121d09040c050303030906010305150115081b0417121c0b01 67
    0x1d080c40c41540d010018400101c240c4401c90b40500e5990040010f40340da0500c030a4400c01e0000800d0ba00754643c050150031280104203580750300480d020660b07c0e0380e44403140d00b1a81c065865200154000c0207283c141f212900b900300200120f540280316101d4141c5009280188180854040081c1c0000c0301c00300d030300d000c00080c1c0a4010340240359a00b202d440c01e420016031000c04080082401c0b00c400090b100c0c80460100070982c3c458880940d10b482031010a0001d510009040764850399903580032600c1c0d22140b02071303c040c03208944005054800b07030412001d030b4291200e41504100d87e0014424a840e001402c61480c1e04007036501e240c164032a450700d15a00d54068220a805210200800c01e40300d0f400030302c4504a90080302035804142403a04000000c42090062400440c0d045080300c2d00c2510903851664012082d6103000d00b500624401d400c0982d200c1d034043c01c8a030791004500078440409101030301356903804800d01840c200640111001c0805072501c007034002c580d1465085041d9002d9048 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 876874811 1250 876873561 876873593
    0xa170c0903010c020f16030203120d1116020f0f0a050111030408122203020a05090702120a120b060406090506180d06020d0510050109150207030507080309100e09040807 74
    0xf0f1100e040d008400a580b11a1040f00c060a446001c1401020700c5024020b5401d032a00900030b032041e4400c158a0340c18540c01540030356800b030b60b01c40300305c0b10080c42c0001510400030f0100111031a80150b0041081030826034804a2142884c2a0080d6480e550720070f01070122042820075456050181014608502455002080d1409440b54120070036095000418120f0851002c1c21511018080a020002101d0100a4002201c404244410300d801041503a00182c640f048400000e03200126101a41044141c100400c08a5502400398009030103804500e44050f94441d041524008000380400a03078441d0034000c0100103a071980e011000101380e02940d0f406080c0c4003400c610341c54401c00940c4115a079000052501011501d2600f4403aa49822034030140c3d01d03492454145000200c455460101c08800d502c107000d0000700189d000c0c0540401084030102441d25500c81c1800e103c4540b0345a0300880c02c10900f8000680c055591035012a00b00b60001e07507031925948103140c8108120725290f9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 876876061 1250 876874811 876874813
    0x50c0d2004030c060909111b0102092e05090a0302010c0302121206040c020303150105030916030c0f06020625031d0705011124070504030c03060f0606050a170c0903 72
    0x401009200f41800480119144c981c0d4483d4071696400e441411076540050714441502e0401ca043c540c0c2c000402d4203200074a10708001403506107003900180072602008440d103005908251490b20300c3c002041d8101000109040007840c1014290000e0044641408001d060058039002e02081c180700f0000811103143c50350b25180c1d00c4d64950105c0b040c0000490f5081d104a040401c00143e482c0b0200503240500000408010345514400055405401c018031210140c440c00d0a08441c50058054036001107010340084072800341841035000388100381b030b04070030190340c000400d0041d03104281c940309502c1d00e201ca04203040d8660707907503044001e4061400d40b06144041007010450f101004a007007400c030354090726483c00403442030094588503d185140348081c014015080b60030744156a907400d9000d0002e250681c2783c15243d9a4a003007001b0640c00680d1a6980c4246003440d00c1d5007403042c0c001030905800c01e682001d18641005088690222003200a204c403030f800b04031400541401e0b1068614014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 876877311 1250 876876061 876876067
    0x280305120c010606090308030a0917040e101d16050d050702241e04020d06050c04090e1204182007030219121d1305060306070201050c0d20 61
    0x2000c200040d401c14038a40d901540703030a40024202d4010030000044950042c083d60941c0d880d0300f500d400802c1000c42c15510050001510301649140e0401000508001d90400201e400e04120840c642a56500440d26940364924554011451503403003952201600324207140042e43c0038070403103903406030311a1010040d0a1000340151035030003045410404103000c401e05038127500d02034090b44d80c41c819540d0150700d1052084002c0c4c01941c450303505502500150006854880e25503410084800850743d4801032540802c043c4989112805001c0030003504900400d400d010303424415000784035030320030f810300d0080541103d60b0540e2142c0001c60f140440004000c452400b5010325801c50b88142400c80c01800b0b074012034401003900c801c40303000142d04a100c500b621111210141d0350f5000302d1a0007120012145280103440d5181c2c1014a5150000c51000c0350a0a100d4145850300b02d018101d1010b590502e01001161900103050f107001115520003c590480c624020807100c0d40c12004450100d0400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 876878561 1250 876877311 876877333
    0x901051902070f122603010b251a070203040308090904110a0305010203010f060216090506031207050102070c05010f1d180c033106050421030e0615280305 68
    0x2c5040a10f580e0300072070343c0e078542c2d0145e90521030b1414403030001120080c10a100603c55401d068000e4080b244503d000425511105c008869441c07120407011070f8406060211042c0315480078012035007100c098001141014110ba4507210075019000c22103014650345c100090a205610442c0d148408010b4a50b02205440e0b0525030701039030090040c020803000c142c40001d1074620010b40040c2c001940c0703140c058941e0a081401016102c06412180d25200d40944100840502001400000e1285000503601d40315854120004042a48201d05000d6207010900030b681d08140d0403408130350802c04d0aa55450a0306c0050240c0d201e0151100c941141d08080200c03080c43c074030046001c0d040007031080b148c0d460381c2c0320112043c4c01141c2250b4000101400c0c1c10000a41d075030442078000303204a100e9480c01c540c0000d40030510741c0d4400c000300000d80f01e0350350a8482500b44807864108980840030035a2552200214595011448100c0e5551400101c83c2c00c070251391a0003140995440340c143c500200a03 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 876879811 1250 876878561 876878579
    0xc1e0803090d0809121614160f060e0d140304170705030f0328030f020d02071a091e010b0a060801030c0803040f14010e040e0a0c09020901051902070f 66
    0x242d40080010901c050085920b40500150808100d00003150751450120002072000b40309921400071600b14900088100b11044140300309032401c1091800c036a2450310380400d00d00da00003a5440078061206c2c40c109150161201140c0e8405640c2001f0f04e1401c84580f80d42a84c598841c9034010050700707444011444640034046054400c07500e084080f1040302240c8840d1a4030b0703100c0c1018250300c4011402c0541c044000110b004111180b283c100014080e054007071140c00ea174452019003d030198000b80c26001c000c41614041d08100000c004a8100e01d481c0405541c0d40c100240000500401c040c00069441803d41255403440d2000d0102800141e8030500549204001e00080703414416544010440b17a10000aa40840f80420451500503203003080c0070b92640c5002d42d09904000d02c11071049890f45171805482543c103456002402c0c0d82c0c400d400c004003800c3e616000401c1050040180803440d0303034040c0aa0b40042004100c0c0c040d010400e00050345040b24903401060710a21400c80055020a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 876881061 1250 876879811 876879823
    0x903120606110f06090c101119051b03100207060204051f09060206040201020601090e03070605180c0a0302090c130e0f04140d0c332304030c1e080309 66
    0x8102c01c0390382160407050f007184c8845003203408104a07844040c00744c2042c60041070f039114201160928010302a048880241442c1326032282c00790f4100340d00b04881c03c0203410132034010105604010303100c01380690000213413103020707494441c140c45802082010074803690790704440c01040000c010700d44101404140c1e182c2d601c080e2038100b01160b581480041c29178004100c061141c0d605038064512030307003012441710003030201c00d80001030b92006002c41800510030703106040c01400e00c00d030380d0309c1c00c10848543c140c0341044180e0310500644201310104016181c12010940050b030038a8603030f89070000007070210b01d800056440040e400c41c1c40003e00c005290002c13460f500480c0280c2c5500810355001e064a0b9588000c4607422001940c803492240100b81e10038401c0c918111000c2c0c45a0007081d610042c040001d560900404002d9910b070348050207030500045d40117040740e40041c90358052819442c0a490081040070190003d0103404800400c2d100e61350601e84019449200c1c25242e0401d0500a6a102 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 876882311 1250 876881061 876881087
    0xd090c03030e0307060c1b030f0c03050c12060a020a0c02030d0f031103010b0307082d0118110d0c0201060f030302010b0109140d030c060f0c08040c090615030903120606 74
    0x2440c00d0b61200745810089504015101640c4699014818568a4008030034001410646082010001100041d81ca5404200e12070007059506009811820068140820640001e00c10090070b1b84403003031828007250060340078034014801a158800742c030f0241e400c0c0794100002036142c0140007540080c650421082c10300d994182d5030410400044148008040c8004c2c050540c5441c3d0030700016130501e01ca0082244d11104070200340f8040b211402d8035040d101040c41e0007c19100111005010b40c540b00c5a49000085196400f4004540c110700d00703142c50b01c180d910500303440342c0b526403840140307000b50050001450048084004541d5a080090080c04215942800220303410000030301118000da011008000062045198400986e400e0394907078a8010708481442d02c40658920301c1c00584118000c01d00c4684031010540b03007524194818150b01c0e000013205c00c2ca40310301800303100c440c4c1e00f901a0007480c42c200051550114101524490b0884840c040c140e401c5c00c4001c10040e034444000c440c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 876883561 1250 876882311 876882317
    0x90218091b040507050d33051216150c05070b04140a060219030c080706140a090f08030603030d0c030204180902030a0204021b030304060b09090c030a170d090c0303 72
    0x101d50704004210940d20306684510000340c040c4400c1c02d4444403944410580d24800710b407a154542e141c20f50500d4008008200c50382491003d00401041c20040e0010104002e014003811a40210022114105d089806503808100c40d00d110b2020182c0141c4901c2d92080d0040100ca00040d59220500302c90b501902a40941c6000074503104024100150301c0b00503940160041c00d200c1041c0780842c0e014158001d000d40070407030707a5016400460420002410664000d0310041050f4480100c0311140e444c01a00e4401d0f0b00c0d00e001c20700400720f0122143e41103d150705c00c0380180d480d150320000916501038030b00140207483c81c2486c001951a0954014000c942c00034100385000c00400d8824421a11041c034080d4140e008022203000620b459801403010141504502d4240c60021400c00c0c5941c0080390121501c1d90b131040a8155860312422480c1e00024a00060191016040100c2e486095441c1c4c001c02e00c500411500e4000700e001d4007620b002c0d80554208010407072050504000324180f80c030041d408 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 876884811 1250 876883561 876883603
    0x30c030a0b0f090a020a05090a0801020c0607050403050606061b01050a0e0d090303050910051e21060f040c050d0c052d0715060302151209190609021809 67
    0x301d0400d02d1420118440c0100003180d5a0341e00700400c000380d484112041c0070040200b065003115034403107040001801200e000141c0740d91032011030700d1400d00c020300780400f80703d03080c13001304009080084da01c0d5020308151070b51a1940c2a000156851001c140904030065080c8002c001e58003100740e0001d840c1e540080115032407213150040135110042e103400043c0000350100498401401c1288031414880c40c02d18149203030902c1c80c041c0130301d440c004606181c1c103c203002400800104400b002d64003941030f0360b08034021609000002400e0a01040045070140d40c0721441c00c1a810702130b41c140c40381c41e0072050050001c0100607100030140e6000e500601800c1d1140c02107520800444201603592040100c04149415044d03150360302520a81100031009075190480800143c4840e400640ea000510907641c3d03c0d03a039a4090154010340090000e0010303804600c80c1e01200c40300b401c1c0810b00a8101d10000740345a824000308401c10660100e11315a01030740305c1405036892000502e80d44001030240c3d0002 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 876886061 1250 876884811 876884831
    0xa23060426010b010f0207030b060f033f070f02010c05030c030a110304080703081c0c0504050414160c11090408250b010303111e0106080f06040213150803030c030a 72
    0x2241ea528421749001640205c1d02400002c1800740740303a4000c4001000786411440300e400191608401300d580e5801c904e1115a56060131200016014040f00c0050354000d0308030700101c4d8100c09010313012000c1c00c0448020401010344e402180f80e0841e036a00401503070b50f64080044016900e030b1241c104400055113046a8000402011054405031920070001d0009140b450300e8131181c40c0c0249100480368404902010070082480c45401d003070b400b09898075a00c0e40c0c80c0c41e04100c21140c054240444e00a502c1c020840c80306418000c082d550a09803c1820105c1124140b401d0b4040d049417250303400c5080c12041c030060001038000703403205000e5416420a0900600151038079840722450041212946100510002e07014009291461082c8412140107428011191842400403100019070b40d644003c00d2009010078062422080200d41c001c150600302a80854401c000000003051020f60740c0c010042401c10070703c0c2c024003d199010441e501c90034a130710324100300c1e40180c130744511b001c1c54030b22812 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 876887311 1250 876886061 876886067
    0x180a03061505090603030a050703181e06020f060f0a0b0909060a11040f03080a12090318090b031209030a0b0708090c100c11120d03020c0106050a23060426010b01 71
    0xa0311482005c1c0180d0b041242d0341c01c0546040e00000021001e104d211f01098052150f1000407800034441714040e01c10100c140c2c0341064002c403290704184119004290704080c818400900c50303802c181000152001580c40541950060440c0b001580e402912441441400f03a00003076807501441c1101030400121281c0050080c40e84128440d050640d246600100085103ca2018050806c010304000c404405048820030131205150421001718a03800c0700c0391400f01c01220024040e00c09034508118204d80070001a03070b6074010b000d1849c080b40d80012991061340b0103001580c41d19a02004881c580e0810f01d201134940c0c4400c55503660180325210503d105494585c02240070b410850325032100c940400e0312004880c50788440e201740c10184000d4a01081c0d10108903030a0a0240b55a0042e01c46840d04622420755480d47e109034401c3e0141482031000703083c10007200b01031014440281c0b19951440c408907035140120b520141c402c106e144281620074141c00303840080201010000c01040c401a0019 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 876888561 1250 876887311 876887329
    0x50f0d02070f0e0723190521130b010e1b07020a1e08031809010f0608012606070309050f0a0c05130f0504120801080f030f180a03061505 60
    0xb8900c900c074200304001c42d802d00301030a500700365185004403c10300b1504009812840030000101840701c00199880d460504079074184001c28189400303894074104580032071268402c544030801516482e0081010340760940c1e80d401360241c2c800d0391034005680d03561640703800c038a08445442800c61075624100d074500641c4203d9501550050800007810f040c217180a540c0740c00380030180c000c13080c5080b000c03591a104102901c000850740790341d1002c21900c0800e01c180c1010690028031072452a00041c0f11a81e04544d40340d064a11b00c007102030080c408036500f403080c0c20780d0581043d101d02031030061002e43e60703042d04500350640c091412203000000c2c1d2000e607075858041e181c0117004006080b40902651800c81c0e102c8121848194021407888502a260300803100103407004c1703a0810f0015500103825410440142c01401044050030b0381282e8082034a840348202d4805410711200042e490f044812031040f01110b4140c0030700301140c03080e100e14041d0000c1c10395610307844400f4281100042c0c0c0345403034030304 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 876889811 1250 876888561 876888569
    0x6020304090e030d0509071d01030c0902030402030307060e0606090c1c0b01030f1104030b010e09120304020a031a1b07050318060f0310030605060117070807120207050f0d0207 77
    0x461500740703416001002031580c101094580e0100b00502408415207009031802004090b024110041c50084c81380c0e0500c2e100321503e10800d00440c010401301e02c80041c180110b81d4016400741c0d80756036a200203801c40c802ca00000700481c0c64104144044036001070ba682c400c0c3c0003035a0405498480f03a4440700b96025920000814640190004807071074402e4009171803500c0181030204401c94002a410260b034240403001000390303000301302001400700d0104c8450041050103d0640b050424005550b1981030408041c203008a000005c9411034076072000060045030402c542c41c0c2c0c0d100380c41c07000c000e10000594801044c41052110658646c5120088482480c3d00a00843c540f040c01130300c40c02c8070011a000e2540c0701074240810540079411800462140b0440e02249148a0544c60184129030002d000581041040c80c441c807801d800000d0055049042c03070418000554a892007111001c0d03a000541142e10300114040b070800000040305060078070300b4025541c0110b00d81004a0740c409407442 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 876891061 1250 876889811 876889813
    0x7110a1d1012030e030102040b0c06060f0a0f031e0204060b031014030a20030a050d1704080306240f0c0708060c031614070b1e0f070e040b09040b01080607090602 71
    0x20b0800001d00807a458114100040d0025041c01d94403101842e41342c005d010f502c0b5858110340100911481d199004840b9623704a401d084507500740072100d850b001050000500c900d01210740c130158422050041801796500034014451a61950040011038205071020607150711102804900c40d517801ca44504188401340082c10810801e84441c104040c4440c082108400d58020401154505100384c03941700780078000415642243c003100402d941001c400e041c0b51052042c09000c0000c0f01070b42269003087d030892315540d003030601400030b5150004a5900c0e040b00e02c030004e0901c0720b03100004040c082c020360400c152100507941b00c500d03a46071380088450142d014000c00015402d240016440550032000340340685840e07004006241c156400300350251420710b01c403400c01c001030800340410081d040c0f507181e007000b0509180c0c0002031320100203422401405010104002140c84540c0f0840a204000308035800030309181c01c019810003400e004440c0c941c050b102c00102c00c03074041d840038001c80e0203c0e4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 876892311 1250 876891061 876891089
    0x90f1203030610030615020d080907060e0d1e0606050f040908030c2506021e0c0a11150d021b0a0503220b070c08071707050607110a1d10 60
    0x10040111811484041d0410b040c0d8501000c10340d5011851b900c6080c0000e0703001441003c00b00c65003d41070f0f00004103211541d0f801044207200d05503001c030117510340e6901a00c4a03841903900c1d10306a01c0240400c1a403c0100c080075000c8014001541c1020341200c4040d2072860641c0c224509020a0303900141e8054075030403007080030a641010701ca00401070700740059454401c402c4640a546140c0781110001c8d5159500422070b9224a03c05020342d180b80a04c0036126490400c1900c1040e4403503e079990007a040c0204c01502028035110320b001b03150201261a5013a5483c41075405913002500b0000c2c07040c48441641c5151403d03001c00241040000341c112000b1424080803800720040601c484c20401144140e252000070780800200180990350300c1a000040c0311804c0182052428005a102140701084802e440310391113004031700003040e260300741e81d10390384c0b00443c1c24441714070601c084615400c10034000d80010100ca480311914441c01d002190300d0f400b9100c8182ca40d181310750314010800c002140d0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 876893561 1250 876892311 876892321
    0xc0b010308030a20030f06010804110d1506060c050d0503131403071709040e0d0909150506070507030c09022701120f06030302150403080609090312010308090f120303 73
    0x50700140d40c0c0118444030206060380f5981c040340107681d01001007118207801200340909907040f00b004550041080c60000e2203450191100c08081010600070f5008040500310a03041c0841890700ca00d00191004003444543d6880c080288000d01c40c204c1a0344a014041144c0c05161042007100c1c0103440945009103040c00c81d40b58407a6080c10b26031380b40c103103110401058002422030f0300480c5d0903c04d08010341d44c4401d0040140420745a00007282150394100c03032154405142c112005205980f00d80c040001c03d040084d0402c4084140380d080260310800104130385040160005d130710015288100060448155a22085016401158a003800c2c2100e4400d600042c5450440c2e03009100805251541a01c10309900e0b03c000c40d51082115400c1e107451b100d0a20500d60104902043c210788000c030030805103081d8500074010f01d000f45c6603a118648174004194400400c2060f6464400408400c0d0645c2d44d403494400a03036844580c50501540c0303c50280030032860129500318002402c00c006e1843c0da550 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 876894811 1250 876893561 876893573
    0x801020f0f0a02032214010309050d0f020a020306040f12090501021207060f110307032025060e0705010f11070501050d1d010204030530030402120613030f0c0b0103 72
    0x541e090508520042c0281e0311514080380440c4003405040c1801c00f501c5e801c180c030021201212481050505051002c14000150f00041e484042d182030b1030440b001c0c0403500c1040303080ca00805000ba60500c5a0000c1c002446600d1140e082d11a01c00c91061200d25502c0c0004c0e10105401e10485001da049152601000340c000c100900710184200e074001b0700f440b000c0345500c0c200c41a9000031016014007008001815405100c0c13500610b10302000301c0f4508100c84407905403442011480c444020f04510320245100c210f460f124411076200b1002d00903201701d408030964401c5248251800613505000c6030180502514581070516040b20140040034180300041d541c691140300d0341d000d9155100286101c1580c0100708100c0d5801c20340000d070350f40d85542043d500d4122082c0c14008220040014035040c0e404046941c0301e5a82007000c00342d1650f030f641c000905003881602c62150310b800380e282000030340308950030f007003400c50301c00d07241e100419840c14011103180940450041c800c800500c014808128 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 876896061 1250 876894811 876894817
    0x90906020d020d140c040506030402131b0513060c02010512060303130e150604080601032a06021509031e0c0109021503180a0807060b0a050a0b0c070801020f0f 70
    0x200459015140c01c40d4445030720101e900c16180d40d505166a0b21040100307081c04030001d50090480b2100c941031904140015001d444040c0c00240700e210010074401284225811001320685074590040e030511040c403020f04180c1c0040e503c810341c2c9410084c0442d90310301803410355003030036010380d50203080c00b208501045815102800303690341848140b1400b82102003044c041d07c041c002c0c0c0030650140e41003071800c103c83c508900d10f03403a1003030405010038070124100048d8075044030b41111103802d9125800000150100400382200c201c20b070400c0e404290190000381c0c6076155410514011100c1e40c2d025001d58070380c01003c0e51001000130041000014001e002c01034408a0b40840001079503501590008003d4080010301c803c402c4004810040003511401e100200c08046138058900588559034200e400e00c20458000e00c02540d64441d10b1031500c4e00e0b5243ca020780780107040700d14202d442d031302583d44581160350003031901d21034040041303001b44040c0292001c1d030f03000710105402d000c0310340ca00d010340350 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 876897311 1250 876896061 876896063
    0x61d0705091801060c0506010510022509051503100c050a030911040207141207030918021b03040911070b0f041b0e07090b0c0723040608060601080714040909 69
    0x20040c0b24102e1000002000c10300d000348016211204250103e1074280c0c1042d50503230205114408036072001c8881600030408040140d0022000c40070040303200c024100707200e0241c1142c48800d16040400450640350741e0b04946011003102147c8070150042000d5040c0c45484001e603000503000d020b200c004c94020780248814034856070122a44442c0440450100c0c9c120007002e03245d5503190a0b9580d4030030018080c508440802e0810700740703004441e88000d0504180c4d40310f00c40da4002041e00c0500c5190481d0306541d408101e505880d0501982c446010b030b9260060300034180168038080031010b102114070112440164851200042c2e90798407041426a500b00070400c0c0d810821150150324401d030485500c4000d40210340022015041c2a07400078078407026030b04000c880c801d04008a40f14541c000072003400700c0301607403400045a40c26140c00411980591601d030b800500b040300c04160b020011480e5031060710280c2e00c400c880d42e03034000304071820305102241a0400d80208010b003d048504d401400c420703 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 876898561 1250 876897311 876897319
    0xf1e040204030609050c041b210612031d0111100902030f060405060126060a0c200601090b0906010504090f0204170604031205010807050d17070312061d070509 70
    0x816a65200c04007540e00c0e03940b08417801d030004646104203142502c00c916015204c03005142900820030805040e040ca4a621051816401c003881d4000c440039810002c0030b041c041d883e00002c24844d1a000e0300150100555014040c10751703000300c0035544210a000f0740380c80ea9034010030032900c0c41180e520040c402d558042e601402a10420f202c1c4150800030103000b140300f00020300c441d41c07410290340c144050110344144246124192283d030304c140002d1190b0081c0b0800c900144c45040041c0a40c0e28a509189041b191500c0b0340d02c00322102800f24019040b100341c4141400309034000301c100030982c001111168041441844180700800982d130042c0301030009054014603150715003503000003880000d801424a40d01000800042652007800f004045d00d028400788650350414900507140e4660340106801060152099028040300c2072505102104806105603541a1820010507031410001c04005180c1404400a0442040348111141300301b4071800340c180e62282d0b00c0841d003542c418500307980c0c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 876899811 1250 876898561 876898567
    0x1f140f120603100504121403060904140a0b190b0a12080f070818011106010509010605070f060c05131203020303040b0405150a150e0c03072006190b0f1e0402 69
    0x43d450321034140a50300410840618494040c8000c002c04e5903400c80945c00740e020720030310403580c461044c0030307401903409019400b0720380c0d400300d54520305581d800001c0d0215540c0d20034000044038400508404920b1050705102850f0300c170090102c01c0890b445121545454100c601001c44d080d500034107140b0508401c11440c00c995521181e4054006001e090100303c000700da2511079680001c0e440c5140c607003c1024212039071520000070352040c4148a0750080c007034001030440800c940314083c00c1d042c03588840200800c181c0c5a100400d03a030811401c140c2c100ea500b100119401d1241240c2c080c940e68503600840c034580d107568404212102c05001100ea87c4100c1d65814042110140a18414001d0000006420012240300b0006500c55442481d02d0b4202c08140045454182d048a40c40f038254141081081d030300743e102c6003900340000c008400b9400b400081c00b545084001601e030550025078414860050035100300710074400407091083d07100740562242c039000c640e800300c110043ca500800040c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 876901061 1250 876899811 876899833
    0x3050c0408030c0c01030b090f04060b030312092d1f0e190b0a0213230d142b0c05160b1e040b0a0806030109021f140f120603 55
    0x21070760f0001250010705401105202009580c14401c01002d03410464031800c0c40d00741840d40003001c1c1c00240014043c50b8540c400c0011a4508008a4104001040c4007045a240080311941c50315110700c0151040341180512407141440a2a80c2d42503038540e00160000d0684090480316142d80b0100f103215003500c5480954000b2800d105000c0309102e42007030072801d14140e01d031200704420014078812203107105000d44c841081e00d49441d0019a1880007080350140069164030b0b5400c22a6031403564040311102c150405c004501e001c104e240c078241c3c800c4650042c100c0c1b6104150701c1d0b074465003030178044202503900840d910ad00b0400740694003400643c1c610580824140581180c19000b00c010341600050050f035070150307440000c001400c009070700ca040501302800d062441c0b05041491041110031404100c2d1a502980b00150305a8000e0020700801078038900711441072601d8080101046841c20203440c080b41c1c0604039601c80e2920041c1303520700444442502070030324000e001c158051040c8442c2c21 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 876902311 1250 876901061 876901063
    0x150402070503030f011a0f033715050906090a2405031c020303190f0204140f0f030705040906240e070c0b0112062021040c030303050c0408 61
    0x10480d540168040c503980d240280040c600b0081c180d00042c40315000c2c80b1211445000b440c2600c20456580100301c1e0f0b60784035115a00c21801801c520207c0400320751030300c102001c5141180407941c0c00310200c1444980c0c100700f69108403000c50b10640b43c010010b007002894034940300c10001d42c03100c208400095070860b10140b17503c6400c0c628480380c0c900d520111043c0001e18042200c84041c103c1d0190076007520700c034500020346a000280a11865128040c480300b0070964a4001259002013404110f444580d00e041c40103181035540003050241d00c203c81401c0f05424006c0141c040c0301c001500611a052800301848000c21503500140c400079940c0314803001d03190404141e09040c103459031740c2801c40c9003080b111044115010381480144040f0120b240000368034411a43d0450342c0306101c0c2c00c04000340c2c1c1849409480b814010340208202204a210b208541c40060003066156140b10f59a6800c125401c1c0340e882010b99000d0300b00c0c180e5940800000703200784c221030303400400380240905182d540d40d006 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 876903561 1250 876902311 876902317
    0x304031a19090f0f11010905041a0402210a0203070806030c0904030809160807080d0f080406020d02040b030708010f080a110f030c1c060c0302041d070e0d1a070305041a150402 77
    0x100e42114030380512504039030740955007801500c8225030412038181c082e000b00108a02b0b1503ca00c2c055600031501001400840d0702c01e0040080c0c011405090303140142084000390f104550300c0700441d0030800440c40b9406d002031803401442e8060181035103038585480039030714154000c00e40720031032040c541c01604002c05141d10200400f1458014507803582080c480170306042c0c41d080d60303034104070a4100241003507a1181c00e05800139000540181d5403010800d19002a200d550040c10141400109004196900c980090704070384048120020403503c0b039605a480c0c0d0b100e8032001c0e10641142c0150911458030703a545260965005045035040e04142c40071518040d2114054014100a2003a8209001807402009203590f01171408509e03042c18520300344007540442c00640d080c04203440c0000e8109004a00400c08a100180150300c548614a0300b103000003071800d000d00c000311040300414082c80c041e00805014642c030013010b01c402c80134403a0010b4813200040a0340c10000480d0302580711500c40d0303c01 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 876904811 1250 876903561 876903563
    0xa200402070606030213090f260307020a0201021e0706030b0a051c050c010e060d0c121e0b03071a210a09031b120e030109060c020304031a19090f0f 65
    0x2c6605031550042044c694903441c41000d1b030b2420416624005518084100d400380da12248495040c040d400c01d8103c2d161100d81050001c100010a002007141c00084500900f4805d9003181c0041d180d8620034515840400381c01f038099070008400784034035806500f10301c0d411000908001029591080042c0115000588508600c52080f1501c42880400e0022500a040030b00b0000808582c00000c40d102c4d216009004182541c1c0709503200d40540f2500318418881d17a09101480400607040d6140080120004c2d040314991174200c0c05450340c20701080e400b084810b0f00e1024241c1c030941c0420102e95a102601046c50003c1600c1c0203000040b014141c1d41c02260708060000d080113580c50090040118054a09158003044a020000070648610b4101088961800700e040391010b81c0400c0c0500b2034200010b0540d07051030200581164008094801c4030301408804c8109042d80e00c5c09070ba00a01a10700120038a447e01100900000e80d800010001d8406c40c211001c440685d155a0901094000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 876906061 1250 876904811 876904823
    0xc011e02040f08010203060109270507080901151208091906121d1f110403050313050a03030c0210050d0f0504030305073b09070305010602070f06020a20040207 70
    0x25042c8986856000140d01400141e002185141040070018052022502c80c040c400d005042d161200000e80104c85903071165034031818003641c100303400c02500c203040c1182c58644035031810458040300a64241440100d0361461840541a90130751100c1941d43e218024542c1c01641c2480d540d000c02d0381c0010310200408983e40c65a40d00da050b00c4440c0141e40c43d070041c5084198080ca02c12589840c0030032080340030a4051490102128801c200c031002d00800882c1c01c501c900302243c00001d0060100003030200c4c3d124502d41950154a0b042000061000c42c080503000450700c1d10745c5801810481ca8042da4104242445801d20341e0a004100948404000d5101103585401c1070108064046c0910f9421050604107240c011446a8103a403c03500d03100c01c0d950480429240d11640ba03003045142e100f9031070f40903140020a00d40010081c010300400c3c820a401403003406400601c0c40d120752101000e54405a014160700815038840030003406030710050b00705178024140d1401480c1d40d40d01c020555144924 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 876907311 1250 876906061 876906067
    0x2060414071d07021e06062d120705040e03030603010605040c0203030a09080d110c16230402040302040c17090705010c0602221205100501030803010308030c0d0524010906020d050c011e02 82
    0x84140314042c011017030000e00c1c1c8c400f030300b180a00501942d600035050110940e40e02c1003a100c2120040c3c50301c40181d1085030010b140c0392902100c080c0101c002c0d403051105600a000540e40e86041c802282c002e14030b0400140c0003030006c900005116000710700018007a4403040e051000008a80044424819803036070309540c00141d100310782d2820300c81c40ca01070b070340f001c0d1382c64000d450510180741c1c80514100c03000325481d0000c280006656603a040c1c42c081c640280041260020204025000d00e1760342d1001c0d00112102d0001400302c210000ba0b0405441c4180d55041c015509650340301c010b0b400c00150615203500340309199413070a0500041c40002d050200410303044034003a0421600300705a0002e404d07802804c006c010720100e8220310840341125404411199284e641d041c040c07100340034407014903031402d041905204244100c080f2012000c10030b5209005051b10410041d903443c1d08521803500983c1280c0d6020200a0080000e0100c1e08810000400c0d4015554086a01d803580503440c050003943c08 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 876908561 1250 876907311 876907321
    0xd080d020721030f110a12090821090102071e0302011d1c050306280e0a0510080604150e0c03030d020a08010f03081603031b02060414071d07021e06 65
    0x601820010f13621000d01007154190b56490000c5500c1400d00c418240040101c4042005100b60f010b0349055030000015902c1e20000030440c2540c40c550042c0e0424100e520300400ea00304e60601c00c0382c026950002c850500114104140245010310010070350943d561400000306000a80030540360034459500586000c80d45001c1c5250545800c04160023000428000c020050719400c5122401f14a100c4100c0400410225000e20024080d00541710002c4401d091140702c001030b0300284d006410b100d901d10b540c5521603201e203580726011200607101d0301c109522000d0074000d40d8081d2140188510a40c0d03041d010722004a49168031106140e42d055138000f484020803035005034110302501d8800c500c10a01c2d0300d16111100540074140c519050904000586420540a175000d42200359407c021100c0c03080e61404007a4403090308450543d901c18a50044060300100401c0f03150907241000200c0c4299402440c1740d106c1200002c042405510904a030180747c100005005c2c0314002110005000619013 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 876909811 1250 876908561 876908567
    0x3060a0b030613020604050918030c03210f190f020a1d18010905060a0f030b27070e13020901030c14031c050c07050a181a0d080d020721 60
    0x10082003500c41c00704440c3e99200513507400c011501103030801c40345040c1c0e50300e84011018850a901070b4a00e000d2200003044007101c003002c005010007500764030710009501c1008919001e810401c854506101e0006000074941c5105105a10b0340080e041200090800d05180a07504990294481c00003003071070024003c5000c01d106c010b0259654059840519001c22841c0d2240f440ea0180900801d42da200c8001400d55102c50703802000a1594400880449130b0700e040001e1041030a451001c1580702c1c1c00d04440001c5409080c4c82a040175100c01050031034a005400e04034080d015200394102040c0410340c10150303556801441c003850054030102a070031314042c1030702113910030344400038081d0300103c5000c01000201128a03d003070f10b035800d141e6a00c40b07107054810f0070851280c10440d031200039100080760491a41c00060208654504108912016004450040f644400343c8550007201141c0c2800080e100130064001d5910110015003020020f9880d5419514140382080e800403006038070b482880d42c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 876911061 1250 876909811 876909823
    0x327020406050a0302010c140c1503040506090d0e0d0302010f1d07060f05040501030e0c030715020d0c170906121608160c110111030408010204030c0e1006080402040b03060a0b03 78
    0x21902d11440504e103a001a0090082660207081c864680003c81040d800a102042100c01c0051044c8002c01c001d0125150b950000d40d4141c40a1041e81e00140c0c4c030b4000051822003000d07140e15010340c81014081008803550001d18220115526051403142003080f6005010f91810320700080b0003440c402c616083e192440c80d9110900300310380c102010400703d400c04221001d9510a2031b020500580c80d01c90503181c00d41209465805110b04840010100c9221020070200d03605076080d1101200414422900d462601802034403d41000d44001c2521883c0d40c002c0c580307828040d10303540c104104440038840540045400c030340c0600036158aa07038442d1740403200643c84080c00b1a101e080d000428801400d03001402e50050a0101602050704c0aa004018250f50b658805084964854580820b507010390001d1000311080c0482c054003050f00400c58102e144500c45481400300450f00e800700c121502d05000c0d00998000d941d802d807098198405210807840342c05480004111a0600c00c181450b0807 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 876912311 1250 876911061 876911069
    0x90906010203131e2106061401050315010c0f050a12050304050606011409060a110606010503090303070c06090c08010b120c0a0e0c19110d02031c0c0327020406 70
    0x1400400501c0081500c16000c80306031884074005807550320a078445801d0285071a0040441d0026402040fa0745040c41c00b105900d040c8140000d1010308d030707940840c1c00e03040d001000c40c070b0214405000103100041c0c00c950080c142c0c42e05150100c82e148841e01c80d01c04a100020040d83c1d19005400b07024140480800c843c3c0d0b40752150700d003092070340c034140d03c555443e00000ba04003410091410380307000b03240c815001640c58007040100402d40d9184148009413101400f0301051f100d80c081c40000544941c018000d0300d108540090242d80b850341d85850448507400d8481c0c088807110756940c501d102240314100b0380c0d0b01030f000140000403c0000d410030401541e0003061a01c0e030035806041d14501948582100c14200c030081c11400072180c1700c4595031544c1c0d000302c00050040701d214145982c00c1c1c035030106600c0000700400055800d04801c0c500101d07181e100710005460b40c003441710000085d8850390303803004c01140c6441c60000f80080e0300c40c8680c0c0c000040c0c1c0c8803c0076444204d100d00300662401c0c2c802d6030020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 876913561 1250 876912311 876912313
    0xc080610051e030a080409060f170c090c040305010501060306080f0a0861033f020a02010e01050402033c060f13051c02120706020909060102 62
    0xc0d515060000d10200800c0051903410b841d0800961901e48041014000b00c5a01040d19502c0c2c0d86c42c0e4848070000c2150f442007012004400c080021f80048415490001d0280400a032032521204401e00c811b6841c050000481c0c60380402c000004164284111400303030030b2580d00480c0046c94070000c5803502442243d034040740e802c03030620040080c91070821180c4c03441d6408824581c40c0c40d4002b026a41c00c00c050402000b21002c0841c1e0345400441c1c4180d000010480064210802c06031701c1c40e846856205940140492170161a007090000441920311005500407824000400344000300502c2c0c84180201c0d8030745035004160181c00940a0092035803004243c0c0c000c10151510780c0010780d40702c01e107100da0300360300407010f0103240410304a864041c4011076400d8054440c1179414600355495004440000d03c40400a011818072441c04010460b00d940180003405400d0030000d40040d00c10071341040400354411b81e001c0b8060700401c43d01a191040c010040161984019024081c80580c002c05442c11 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 876914811 1250 876913561 876913591
    0xb0a020901051909052b1103071a0705280320030a0206010501080c12060d0503070804080304030615240e1002071d06011b02040f0216020301110405060d02031e040c0806 74
    0x70306031821b15546068008a011480720b40a0000c079007802c5071504080c10502c031000c07a91072948a104010310202d48200101d407818400403940810048584082815038000d5483c5100460310591304581c0079000f620084418609021149145901c4048210056082040100007540c0c0220b0003680c0081d07203c0c0030070302d4040e200001c9070320044000c140c144120040320b110414044200156103410b644000310566403030311030802d5541e076040ba201c21550982020252203082042ca1809012149146005802c0d8081e421030042e00100c01c00146040110307000105c01e441d6115000032030040d0450b00501170082c207000c3c040d50700e01084140080f00c411f0150074002d0999000f0f0303240400224011104501004501c001409482d800c1e2140d00041e001041258407005050524031220788224020041790381d81c0040c03171506006901c40c05600c03410601c00d82c0c40f0b540d481d4009640c44070482c8041c43d482c1a011032030035280d0b4010f44003540c1c4c9161202052202240800502e504540e0b0b082c91890303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 876916061 1250 876914811 876914869
    0x206300f0402120613061e0e03041e030b01061b0503210a0504020a050d0312020307090521101a030f030703020601301b091b0c0b0a02090105190905 65
    0x680f408400f00201041d587e0070a1001d680c900120400404420003000c1c450643e5400d0090790ba90003e01419281c1607030b61200c607120368110b800c0001269440340b01580168070b440c1007518038104d43c0d012118903c660030988d01c0007810070b000a0a13414020700d40107031707002030210110004500040221818a01e0102480056541e04d616901120806c803001c20020b80585001c032500b1800c0003003000420b00100501003551340100522080c0c8109444164480c06991052140303110700c003000c4026500090010b560000d00c5401035044222100d0995041c1101c0c0341c0030902d02807481440d000b00e5000480e0400070194140060b5006001c04102c030000a140300324460024803040d01003c0d8509492049001002218280b45107050802c6403440f142c80e035558801c00180c0a901107081c140c0411110210085009401140c02160071404120040ea542d50090009600141000781440024003180c0c90260b1400217a81d0075141e070382e84441c606841e203002d11103a6030741d0a00502424184c414416 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 876917311 1250 876916061 876916081
    0x306030b0414150403031a041e02210112020f09040b0105060d14040c080f0d020715031401090b03060c0c0a060f0605030a06020408070807030206300f04021206 70
    0x1503000390308041d0114442c030401c040c0d00d1400c1c02d070202c40c01016100c0350400c0207060b003550064007411001c4511070000e050785e01c10041240d101140b40c00a12000351042202c07100716901500110044034100c4109400c03028010b8202d402c00d0b0310006543d20010b4411086040400c400400c04505440701d490300d09050f591858084414002c00b400341d880459540701c0440c1035001900c003d188882001d1003400c2a04103c48900380c140981a824851340009902d1201c001175400c011006035405003000d54180080c400700c60003001041000c01d61100740c0703681e03108070384074405000300144040007c5001c100000d1500b4050000d2101015140c00d006401c0d03480800305004a80b143e1201c1c00058415400c6071001c01483c094000c50b825128500503801003022a40c024000e5946079030440304040e03a102c0e480b55842c411808007c0d0445428440407010401542071a114207010569000c4040340c00600000b26410482e1510610324100081c4410350a09400e4403083d0b203038050181145113820785200b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 876918561 1250 876917311 876917333
    0x1020304090b15030412031103070c031110021b1218011b050304120c0503011505100318030c02100306141012140412051e09130f02030a060501030603 66
    0x5260294680d04650203503940d40099800c07010f03203851810f4a03410035041400c002d08200031060f000c603142440c3c1e00f6001c581c28080d24401c00240c0d4400355071010341d5a007260004000b8185c0e60315481401c80c048110b94080c0058100402d1401c085070003620006d25540c80c050740d0b40c1100c0c40d8807000304080c1e20003981c6242c2d0f0300c603101c0c820700384143c210044442185e1170040485000d071581c08041000710b200c1c40808a0000080d000303100710703242d180d01c07041014203e070764500184020400e000c40401143c00e2505210303d0607030343ca0400041c020340034003401070f540401d13960440000d030110100008519000000f40c080340458a402c000c5581400d0300c007010191a040140d200d40030301c0458100c1c4601c41c5903802e01030a501081886040c1000c4400c1072050340642e0708440d038480c41d0149050f4103200e04140e40520a41c1d0301240f44001200440504660107190900e4001c00154401d0300c0f804203d000b18403081c031344107600581d0391901f0080c80d0b00300d400c640c005030304260901e001080403642c51204 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 876919811 1250 876918561 876918569
    0xf0315041203060b030c16050105010315060506091c020d06140610031406130e19050706020a0506070c031e020a1b120615030b160f0f05120c0906070c051e01020304 72
    0x6c41980c80b14084058501414004002040c2d5820440044104a00010410310b00c00481c40280b05c1c00e0b072203400300308482c00b40302c81d0983c200c104000c40c20007a0b039081115686007400034101c002c0d00501034035000180c82d2280300c0b10700071400d0001403140034180b41c1a40c000b10601031400b004561540e1030282d00c07104003d406c1c00d21405109040340400f813580d5002141d1900400708503040c442200621908414029032b0994203030003081400200035001103842c1c403d4642c02006000903640700441501c18a0545009504201c8102c1c4446c00e1031000f1148008503404a4000700a42041890415651100c034890f4070703810203180710200002f4080c510f041c441554006c002103401000890800301c0c9501d00c0c1d0002d000503440009200401440884541402c0c006945240720043c05810541e0f0701514061150b0000c0c208010403c803403032480469503080680f810801e850b000328100010301c580c00451043c0c41d070342e8820b0303010015441c00004886c0500416100c0e040d0b41d246150000c0d440380210701c2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 876921061 1250 876919811 876919831
    0x105030a0323041e08030c0d181802030f060301180201081e0408121302010903080a020a0501110a260c0a090504060b0702090a0b0901090b0f0315041203060b03 70
    0x2c0c60003490594090001440c460090140d1070729034811007138000118185a1060181c24500e0105404401100b2540c03d0b0080703c00814000960000c201c8000042450103420000360500c041501010450416003503005588051780b07a051681200003600700203007085110343c0c134004030f4440c0041c480b9140304840e902420504850341e6181001d0f01100c203003c1600314604040b0382003004104103130000d0545440030080d404c81661ba60b021403c40304034a40800313030200f21000004c0000410800046c040001184107507219419203a94450940ba51501c140c040500085060601590b2140400c212200ca1940244901160401061107180f014162201420000940002e954000c01e240c900410018200b04602a51400020840c3d005120228402c1202c04045010f8110600a4000030341d001070800c0364a03440c261002d0000c20b0324140a40e00445142c42e204000e9405103c643c0000c2d00d02e50fa9800346c0e00d010300c0c00054040c1c084c04054241450500709020300010760096903440700d0ba01c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 876922311 1250 876921061 876921077
    0x30706200304050315070807020606010504051215040804050f04062301090b030a0504170c100b1311070215180f06040305031c0f18060203100302030706031b080105030a03 75
    0x604101d086205540100340c040c89941400014603911401142c4034138420b41d106015900c03015401c984400e030a9904c06e001800900040c051494030401003000202709404450090916104141c07441c00c1c1268107840e4004080f0342000a81841210500c4448007100c0401c095410a13841c0e00302c1600105840440100c400101d4100303034041d04540001e0180c4500b001c4d22441e192807444090041101c0481d00c00000340c124403c1410349109951880459802800741000140d400781d0050014450710341d4030480c0e0705101c40e01e50310144035841203500c1e000c5a1940d5800c1c9030060100c540310443c0c0c0841c2c18001002640c9425801c0540141e8000040300d083c141101c05d03e0000c0c0d40b50199402c054514000012100d014400d00b901840c404900c2d0002400040e60004805049030400c412402c2c411081082c8400050349550013180c0c0072052041d17400406850350013003403030311003c0d41115010940e122803110f800d446902c44002c11900324034001031150f040801103520744030b841c0001401c1c0305440c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 876923561 1250 876922311 876922367
    0x23011115010e040609080409090c090b03060711010b15130806011809051f0c0f08091e030d0e0604152a030f0213030b0606030c0a05030705070618060506030706 70
    0x41d410a805c00b0740c20212803a161525031024030010000844200c2d031344983e0200000c0c40105038059804030b65070041c05050242ea55080540e0b682100958503042556a420301d40038940d5075402094a06180c050455120441140310b400360000981110b001907110000421240c2d1180040b40d00302e0383d4624001c10030760881e01c0c0049c90a0307401c2d0718600300c00380c5c14079410421400c80e0307005c050100341e03030b50352076604045030310f0141c0350340c2c800f0303281c00d0455003212550004200340e000c9010501e00803001264900098141c00307408031518507a1090f65504503205210620404144200e04c1f03c2c000502040707103201d2500381c4c105911458201d4994a8001d86031b0030740e11030080c0e0045d000103c10751000d550b201170641c207aa200380c44a000031a5a4001030f07001c06c86504103541582d200d451000e0b0030503c3c02c4200300c5c0583d01604000c0043c0b0070070004009074000034000c1d0003034901054840881940396a003034a000020745200034400d6009502a0302c0802190303074404c04203001081c55100810840c000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 876924811 1250 876923561 876923573
    0x40819080c0106090e060a0c021917030405010501180b0d03030c02033a0908040e0612101e0213050105090a05120705180906010302060d0623011115010e04 68
    0x7803a0010140c0c2d40b80260008188404e604900f040c0085070064030784507540c00328403004490b0034695800043c0e00050090b04d402c4400fa90809603903020340b420060f40010344480d0600c40d401210304861994486d4010411060300b07411030351420350120401d02030781107143e021a1f1010150000038040503164540c104400b4028821100c514803030680a082121651107803940d201291001c5400d001003980b0303842022026031203411034840d0700c071241c6441d0501c0c00c120500c1601001d000706501143c000600d036a2500100412100440401d070302184201550384103c1c41c00f0075901c1403a2049004101054800010201e4681519400d00f000d540b169101300101d1000e0f01c00b80c02c007a40201903880d00e41d10b9600700007030030804c682c411036600702c010505280032600c085086c0c0d0f600d01c50368031120042c401407030a44060a00c45045c00c0f00001d0b01540d5a40135482240c003002208202c082020885106e035031b00c0150645aa485040104250244801504500601441007040c1110004081820000c0f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 876926061 1250 876924811 876924817
    0x30c110109060603050d02030f0d0b0301110304150506090702030a1103040906140301060506040810090201032a0207060f1b020303070203071503060e040c06030e07080106080a05011104081908 84
    0x110940007000780401c1e51034031900501d0309000c00d65040c417411203003002440c400412a01c80740350584240b800d2950115000e0064244002150350654031004034210b404075140145201d42e0003a801005100b00e1600c1d888100c60001c4d0005000d110220100100c4a4001084903107106e242d1030b108101d080d070b1848407419170003141c200d403140905142c0d00051407689102800c6295408400030403050b13695a04201c0584220700c104081d54000700340c814014155503105c42e10060040c1004103400700f00728070403040c881c2800219142481642c011074503085d41008004060426828004e07a911592940a0071416036801203e40d030789110207248085480a1064407102640a02241c2e045da0322100303081c421002034000d190020f032a1800004000d000e11030421b002c1d40e086141d501c013890424101b04e028200400f100f03000f078440c28200195500c024030500000340381c040041d08042846183ca00e0035600714141c078036056401800140070200f030200e00f0420410384480c8450240c1da840c905525070340 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 876927311 1250 876926061 876926087
    0x50303010801090311030304020f09130b0c030103112b0f06090c061101090812071106040b060f0102071410022401090c0503040f26030408071406090607030c 69
    0x10002000015940c1e00540040c0d000d03921a480d840000500815259568001140c003e5441500108042547c2c180320000e160850800c42c2c00000100c20742d140c003103202105940d440d01c8924008010000d1140d402041d440c1000c0c1201e9030391445201e03031081c002c814403603450380c29142c80c00c6085404004041c14010b210325070141d0148200d07070b00303800c2c007500034100d44c400c0c4400f04c2c2e00105412000704062003100c0702181e100c99001d0411000c0901054060801405c80d800d104d1108800040710f1002c101a40c880c510501000303e40e803501c42e0074049a00d1a0071070030340c150b6014200c14402c6002602134020210015a0280c8040010440c12464042406094289449040c800034854690406e41c24180e1b20000404c0c41000318207182100c291104981c0502042c6180d110140011500d03000c1c90b024440d030590440140302d4098041045078000e840840d00c5c400e00003048020040302d0429800d1442c00b02c1e000d0320a600d00403205544a0f00000d050000301940c40ca941007001d4061080e038294a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 876928561 1250 876927311 876927313
    0x60303091e0f03150a06120c0b03180f060105011206080c04020304060902090403020a0b0105010507030f0f1404091401051203250c06050c010510060207030201110a0b0f010e0c090105030403051605 86
    0x1080d003109000907581309840700c1d0754007802e118020a140125049072445c40390f2144429a400e494034207481407a41024200002e07881083c0c090200f001c0d800c1007840b080098405c003800281d45420000b40c521300c000510920440e00f0132101b04203a2401007801d441c018010744000d6507950700e9203060002084c0c903800c002d610101c00d4041c01b0034507038001004400c4500c501510f130f00d16621907005450394065010002d0008080c09854045d052081e40c8074000c000e1a414950000411501410801e400c150441407030955162070740c10a041c82c001280d4010201950b01c0d81c0143c0751880302d507407603100301541c6031043d180b001d0007800803141d000c04c1002420b421107070007141ea40e15a500101704d40d07c0400c45d0040c6608200100d401ca0360304001f05800c440e219002401d50f079144d07a0056441c5042e200015419014850792040491951305100d40b1074407407181840b039907604040d004048400007508072104441d061000d001140d800004903600f00d40c05003003040e261600700da403c06007214554001806 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 876929811 1250 876928561 876928573
    0xb0f030a020123070b100603270c150230070f030903020d030e011205070816020f0106121208091b1c08090f030f060403030e031905070209060303091e0f03 68
    0x180a13200c03980c1c50051a03440d00c40c80c46c190b691342c011810754050381901103040710075000600c1c0c068401144408118400c19029000b40e42c0c0c0c0f0380200310768540c03468010141c0c11888004903291440d200c101445241704200d10407113a01200074244900400b030b001061500b000d00204c040c1800740300c0f10303802998010020030780d1420a20700104011001060030340400c940115070f000080705170294610402203982e4036051551420300002100d20440c642400b03501500004030307609203080c024600582862030860180080e5403800c194169000b101a904014502041c414081c0011680c4c3c0850085480540059006400011202003460204200d20781042d1103010802c01d0110260140c0e003022941809928288400c2c141c40b084c0c80003210416401c4200000c0c000b9009621075140400910304983c00c2c0b00b14011020f1609190102820100d2070120304034046107407507500194000c000b40e014500f04038200010560048500c0500c00c02240700c81e421707180b00c0d203881808d540c900100a0403034072 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 876931061 1250 876929811 876929813
    0xc07170325150c080f0f1909061a011103030903040e070905060a020c040b030304080c211e161401030f0b1804060b0108160e0312031602010b0f030a02012307 69
    0xf46030110801c800b01d034803d0000380b50f0042d021801c0b03209012040020081c0e0b40c0c7d00c419040340d2151486c1100c4002d40d40d195801c0450040d203d0315600e040344110b290b5000ca900c0c40054000905210b07202420b0740300300b0401c03040f508080305840c1190251300070001a40c1713815030240d844c2006904295040031002c59002511076000900c20410316094604000c60f15000c414103440b84164060080c441e40300d042c0403001030400c080100e000404041c4840d4001210101c030138149031500c26918901c441407100b2051201c014090384410741e002485542d000781c549101ea0a010709906c00460505a65030400c40070f1102a80001c10f807160010320440080c070205000511000742580c042e40c2c010700d044a00011940940e0409004a01c040e1200343d10fa51003900c1120724016001c03000341c1501451445081d1100e16601031801501714010107890000703d800b0007400c48042c010301c188941d1a1044540d0306440102e11541d4568080c40c0c44261210968410300d600c20340000030341c41c0031600240c604 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 876932311 1250 876931061 876931103
    0x130e010f0b03280c0f170609010921020a05060c040303020f060103020f06070503190c0b0a0c201e03070c090b06030c25080c07170325 59
    0x2409409a60030410126100d2402d1580d101103040701004501d6500402c0404450609480381c40c603442401c0d2111603070f0312030b06044080000c1d50b0184620314090041915180070030300000e83d000d80d80301c00800c02031000d13440d02c503100f504020b00d034122010750107103402c1d0142c8284412030302a03170003d08035001800c049900d41d80c0ca6200d403009400501815031280e03e072103404a483c5040b250014881510381c0802c40030041654402902114203210401c50305501c00700d414140320754030303141d92a07000c031045450411680d04800107041040b40b52420f05207200b1203801041c90440d06003900c0103408071f00d4030034002038a800814082c80c050718500980e07807046502c0010062249a10500c0d40300324155903220b000b01650001c8440e140d1203a82400040d210082e0345020348008901c4d0400410044068100704004c001100c00c01d0720000d000050000020804010007401400840007104005c80f40c0f143e041d45901071001708202140d070140068801c00071100c05246070700e07041a27a24031082c140403804 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 876933561 1250 876932311 876932321
    0x121a0d080705070806100b070506060f0a081005010e010801020702130203070302040e0103080901030e210901210504110f030a0204091103071d01050609013006030804050a0b0a1d130e01 81
    0x212a1400001c0f0101b0707001f0f503d03402c4c6d0311100d034420014003840d140d00c8100440743c01ca05d01465004444c075080000c03103400810815405201140d000a4194107000301d4100c41c8905800281c41680104071410060300e424449540301030700488016180e46520104030043d00c501d81c08211010700142c00070043c440c0b02d40081c0715100c000d030ac00b08440b0301074001950b110240c060b01009800d040506821202c1c03080c50040103d00d005260005402d0a00c10b82d02544002803204080100d03a42c00401c070070030550800301e80e46580c0841c1c401c440c500c0d840000035500c44001034000d00541d110380041c0100803100442500080d002030903584140d464103208207100403c50750b200c00c0c484040d400001c440c1030800440b501600103a40e41a00351030050402001c0544840305114001c1d003601149106081d588209806075100310b2101780c0c0c0700d2610080000103840e82c1c016000301e001c104900c43d0310a4010144031410309040c00440c441c114014006081c600d22030941075801c604007002908a1481903000c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 876934811 1250 876933561 876933571
    0x406020f161a09180106051b07081b030f060403210b0f04021b100903020f0304051c1104020304080901020d0807020d03270501060303121a0d080705070806 68
    0x7154010705104245140c03500c0381e441228500200e203030186140780c18041c0249542e82d0301500500c50380301c0c41c0c01008280202644007000096011030b1078034103100012480c10070207140c003000749580da0402e84003a80f601800100d4510741c07403400c007283c2510340f000d010100b1151203100948000f441d060802608010303101030034000303009513240c503900c0700c200b04d00c41d07140c0f0b40a01a0403800c0100146003404002d5000704c8808138400410541d0602003007040100840205148201203003415003031070081d1601c0310400c0f00305000e07041840b0602613910350443c2a20b2100c07480041e80031005050500400c8190b501c042d16400c903000000700018000c86400502c0038203003e9003100c448032481c841c21100d0b0141034603607400603045411070701d080303d04c40d030030150719614015200f94003450813549148801500c08070495459464175003c109050f04040340203070b49500384109000f15074900102d818410311700c0d85103510070700c0c0304201e01c0b06005080d81580d006661280c100c2d9529a1101705696a0781c1089803 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 876936061 1250 876934811 876934813
    0x7260703090e13030c05011401063f180501020a0c020a060309152309061609080a02040504170313020906060c0a2307090c02061e06240406020f 63
    0x1c00500c00203241c007024828520007602180104a55408aa015032149000d4409641711580184003d00164110b0300130100d81e1503004040100c0014462808131440a403a4a1700c201d91101c000400c0b94100c805088038413041c00911070040383c204040a00200002502c590302c0803805181c09900b05032444800da00841d141110540d540904038140d401c034550082c49125640003004140d0126085851104981d45005101074504030741c0403038000b41242d0424040c1c2c011001d100480703200109520100e007052401800250400c001ca956804800700024041c0381c2d654005018024507000c4809070110350f810442d40c80c01c180300e04600c651078030007060b0320912140e800f160807460208200e910099803800944203050861b22090f0b41300d1185e101c0003a050300320100150407846c090021001501440740005500380381c43d00001e14040c4010300c00022080f81c4014010758880c201105603000108840c1140310840000c04031468046070820800b1780c0c40081004690507802040711690807030040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 876937311 1250 876936061 876936077
    0x71809150b0c0a0f020f2206060306060504030f080405040c0c03090b030105130218040903120605011b0b13050d020c1314060d1415010608090d090b07260703 69
    0x20745007100e21980714040c2055015600c00c00024805602560a07240000c04011098080c0d00101e4100d410011440280004030702011260460360702c2607402070440740c64200512412302102420310b01c07036800040d00786601c801c000300030090700b80200c2c0d02411003d00141b00c0c0d030301c0c1000302400302d01403104200d0124100b503002081460050702074034102d402c01059a0345005201e1140c100a501070130150107131010000009009444500a180105210b90340c0d040c004142c055242003101c0d9a0b03000541000340310495103e4200f0b030119024810f40d04151100400e13224020f0b449880c600c2e000f0001c01c1401074001c80c0354019004184a41407110548030b441e042c51586400004480d04c0940b160001c4010070085401400c0c51201c2c01c030b40921a2407000006600c00706c4075450b011008d00409015003031500180040ba5102041d40e4012903410014890000060005050b005250040d04620740010484005000c140790009050950391440000702d000318000803905035101000590110b02c2c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 876938561 1250 876937311 876937319
    0x61406030609060c041a0d021201030515040201050f03091e030307170105031507090902030412030605060c1b01120905210f0910030e01020a0c0b0903040e0f07180915 73
    0x1c0f80e258800c8201c8200360713192604080345268034500000402040f4003040c084015202c0c640d02c02088409418424426590314510b0018030781643c50340c1e00444400f40206000043c0d030030105844201a80c0074109480e40e8412580740c0c98001caa40c0340c92900c603062054405a10804801180912255600c42c80d4903c1030192740d00005c0001c0c40340076010380c02030340c03070144a05442c3c183c0b03a000a001c3c50070819190744c0d541c010050fa00103607003d0b11100344010001010329003501c01c10b0014201610306030b040440a1040c541c41e24180c1c41481d082c0c0c0c81410207240c080e8480d103244041e095819804114100d42c0381020340e9104904050620b0051440c0c01030304066513100107444043c1c14201985282000c06000c2c003001e90708420740c0d030061544580c0030f402c07400c030b081c00503000c0ca004c01e9680ea0786021103414101c4100c035001c2d24004482c0c00400c824050300401d42682e643c03141d07242c03410104944521804882000c000e4002c0c940c41c44004001051710f0a0303680004001000010f4010300341525 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 876939811 1250 876938561 876938563
    0x5010207050d0f0507051906031404030e090a41060a0303050f07020604090b0f06030114090c1210030b0709060e09090c06040602030912032d0403061406030609 70
    0x100d40100e55021040d82810000a0352195005a40300d200b0303020ba41034107950703030081030003c00d000030a6800082c22820500c40641d141c481d100049040c410404070b14101510b0242c03404032130380081805280070800180d00704481d40c000e1900c0b10000705900284508400c2c800c1002050542c000310403150700c031700a00d00b1444022015000340d0004110400103803031550306443c154441d07a118604024240031150140e92100003900007095042004240d02281000300043c2201051ba031342c0c400d0704207100510142c580e8100700540c1074000d8419120988820000455900900515400b404844070030010b9a100442408040b82c2c402c14412103151070f4540143c81410490050382c00045600c09141000d14005c2031468200701421700b0303955100d000f0300c0440c00c69402508042c0c09a48009641d9045003080748040e000c1c01d000c00050343c1416103200b01251211500c041141c1219000038401920010002c2124015a8006001c102d007840640e150790544d9011143c8520a0056800042d007000b4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 876941061 1250 876939811 876939823
    0xe240f070c0801060e07050a111906053102010306170327010807030c1e0503160914040504080c07080715180b1303050f01050901180b04170906180901050102 69
    0x6058600300c45c032982e41c0c0d41c0c102d4150f001321501d03800f00b03c03014103140c100760010310071040611940c0c070601918120314240314040d1400903040d03030305080c03070140d40803451034070244e4650804804494408440c0b0386400102e01904658103e80700b0343d81303003130300c41c08503000300100801125101812008101c41d4000e04040382c4540d030443c0380e001c2140280003400b61442584074128035486030804c503150709c00714500354500131801503c140c08034030004240007829495613003440c1c000d03086140c08140182080701075208806d03c09605800b964540c0c0c01300b010415a2000d64005c582151b045650150741c8103443d59440303502e40b160301d660016001410702d8030384c070a05d500d00700e03160a840e03550b00d030323510380010700200da4004a8450f0201d000d5800c04030005a043c0003680103c4100d40021980f8207010784240d08407500000d14541d03403c414044c92001800c2103c06680c0a42c00500840090a600354034961920500300320b5a4011800140707030f00d8604d00d414210380001c0e07040d21903200e941e880e0001640c1e140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 876942311 1250 876941061 876941069
    0x111314031218131e0504140a02150d0b150403021008130b04030e131b050c070b0c011107030c031218020906060c011103180d0e240f070c080106 63
    0x1420000540d400c03402c041c45201d6020407900307400103401c3d50f07080707070846041d0408001d0444d841d100e10500040c0100d080c1580d07404005036000c0c11081e41c0903400580c000803c441e6240c02030401182c0c0c44480c00c0160710941c502440900071a41c5c0750ba00d02c121039110740c00780c00124850300789072007800d401c1441031542522440d880e008005101103c0d844212881c071005104800708010545d01c1c041c00d40f6080180c8500810014011030107829a0305aa074003035960041c01403c100c018450141c20580010303801040359810858240d403121900601030240100c2440c0350841040081d03e10304055010148a4005009503118251150400a18001da0f031002001e4282000c050b017481d009840c100100d903400c0300b8001d102502d0004005119820b482d8401c020f07400100c804020401e856103000d841074075100501c0013804040c511090050403482085150900500d4103030440c0c00c5d20400e000c20324228400c80c500070ba44800c0c8514180080e90f00c8100100c0310038101c4030000490940c1401078809507 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 876943561 1250 876942311 876942337
    0x703020a0518040b3102130e090f060c0301090b010c0c0501031802150a1706090403050901050d0f1b0207030c03080903030d090503071218091113140312 67
    0x841000400d000b19050084100d80d0300075520700851190f50f68450b0710854240b00396580d0b40d14582504405203401c1c0b5408502d20466004001418049a0000110050324501000e406c103030f84800860510344002c80646882c10703c1000140f00c03480c01c103500514120755003404140127483e5180300460300d006101e5001440000703146010310866020750841070790b919000000a031001c0040c0c00203400c100700d0078005018190001110801e259110700c100c00020384003045040b4a013044c901098200c4401800034080110114441c50300c2d81c4101c0c00c403940001c444406003c03420600c0c0e8150024510141050303084c6960b000301e00300003800030411500312608142d200d14820300d15210b100b2280e014800c06030b4140020040d500c2e06680c0ca118a91010380100015519a4400d1034080444400810840c06005040d0200125071918801c03000565084050203303d0840c7e03005d00f800d0a01600002c07070341c0e13040041400f00e01071403065440000b00004500b02c406c60900d008848440d8802c8614101034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 876944811 1250 876943561 876943567
    0x180b0a08210f0c070b0306040606080c03060105030606090603041b080a231f05040c0b0909060f01021e0309190e0103060b0118090e060c03093c0a06050703020a05 71
    0x200600d10006410340e0303580039402e145000e0710080384078100001500702c40c901100c0030090000d6403d180c400d04011303001500b08403405060500d120006408000c00701070401c0400000640280c03540001e88015010150000e902c0341002e00d42503080038070740080c01109203080b050018280100094440c44950050080c031080d581c600440c0c9a07041508030010040e00c1038a00c050f1703070803200301004c40036461074450015450500e03242442c9107108076480724041a070f0034444011244d44807000076421010455002c5030b0080c00d1001070f41000407140411880c46550030084401810201c0180381e00c030000c0300d41c40d00a1540d0700022801000078003030902c02c1c0e201c4500520000c2c5c1c0035803020081c020141000d0104103071200e4019400b4400c0c1e004100b1450b100d994460905004000c0541c0010b001e019080c114a0104006941d80503c00401c0d4070046032401401240440780341030030843e1581031242080000c9400e1901d80d130703078841c0204407441490240020300c5d840c82032083e19200c0540d5900c6600d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 876946061 1250 876944811 876944863
    0x1020309010f0e030a0804061d2403060d120c0b130b0115300b040501050306150a03051203061e09040f11030624060f1210180b0a08 58
    0x243d4000b20101d080c2d0144207108040012900700d034040c10003004c50f41d9030609110007094090780707240810740020380540350402c510354004413042c100c00b0140c142250a95141e82c1c640740011f2310080800d9000d014000c400700c102c40940e50180f202c0e61010702810000c1000e40f101041c00325404040c0a01410781144000144801c1011011401c248245071900107007103803418029284c600603074100e203411680c0d280304421084000e809414000c0700200d408004940c50100801d85031100149070310802e04411100c00c01030b581d0301c0c2c000c0f0b01450b04071084602c03416280403a038203903a0058079503501c108500d81d071040240404c41c104222041c0042c00c10045510760303aa031030106034241d0b90203c0707154103541c1d072416580d1001c000151181c810741c00c0c00301215460210340400114400c61090007a001003003400c840000c204100c44080800b401d5480c43c0c0c1c0d03140f540c1002000d4564000c0c0f4148c03030f03c42115240300c0c0f00c1a00654000703c003c40760b04500d1643d03185050f5880e460a40145116054511125 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 876947311 1250 876946061 876946067
    0x5090a030b0405030f0c0a0212031c0209030f0106140108091c0f030b0d1505010807080c0f0d0b1018020a0c06051012030306170a08040e061801090c03050601020309010f 74
    0x2e81180c07180d01120b0509060912400464118482c00031a540c0000503060552820480098809291801542c40c01c2c40700900f9582002802c103059814035000620408952403c00c00c1e080c0604000008020f840c0d1a0074081002c00300100541d400154000007040c0c0004010940d8041034a10a40181c0031056600702030701c2d0444040001002e1581d241021466500c07000d6503031064070b203d40c1c079451503651101e41138002c486060308042030aa01000003440304120000750b460181d0f0b000c07100c1c140c0e8016071078001000c031180c00314010040401e00d4140b103800c402110070038054031180619411100e071105010b10803805210492400142c0c04811140801c02070b900c0240c1041c2404802e060894640280d4041d00594250441c0029644c01c400c02215185070103448508800d4005056441016103416200340628029010151f032080f010814543d511030380c0190049450307000460035a5a070000d40700400e000b6143c4000f10b070528001030301540c40442165030085058461010100d1141e000b1 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 876948561 1250 876947311 876947333
    0x30f0a0b0a0605040203070e10031a01140d06170f03091003090f0209090c0f180c0a021501122021030903011b2003070627110a0605090a03 61
    0x10010080d03641d080881c01d07031100d0004501c1107d079500c070040001914801d008411b0038291120b820503103013020905000303d03c41000c200c1c1c0d070800d00e402450035042e00c4141c441343c441c2d8032591081a140003c00505ea03004400184260300e51681034860446280d100d040d200d109241c001c039441185041c10740071090007580030070007246c011404090100030943c041050b4902c00c1e594400150300600b10807500c0d140880e80c0c12035002050b2034545030640c80c8811001030002c01381224400741c1c030105000009a2023040707422040c000e5588080b4480d40e407507001e040c0420b00f15500b43e030a4620280e6842102c0c50703001000808901c05088104420f0703189205580e040c414100c0895140030400030703025a0ba80034081c411008030300b1118005404140c0304050b004d0320181001031058041c601e446d00400d500030007990241a00300c0310214095448901ba2440c141150309440290204941d00d2414440c0c0900c08002114003900c020701003585841c4180e40b1402601201036000f43f0358901400010b22418038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 876949811 1250 876948561 876948571
    0x30d0206091207260915040e15060d060b191d060a021f06050f0a0315150803070c0f0b1611190902130b070201021b1201020f03090705030f0a0b 63
    0x9803604da28050480440e02c0d162004110070000011a01c0c000e54a0001d14248904003012899454180b51400d003840418000705040c100541c040c0c1e900a5a80302c54045603c100b028580c04c02000d5192080798450f900a1000c0c100c50805560356441024000c880c005012907039007900a6048544104010060740494603000c214010881c0f101500380c54100607000c00100200c020680c2402c15041c40a41000305403000d2052001400400208100107500d059601c0f500901064120199140035070401c01607020181600c400101d010038012642141819940700889182840c0d03035480340310340030f1702400c210b01294000e920360001c0000c40d85e01c015421910082c0ca41c00220154070130080080966a2201c42d0103a00001c51600c110700c031800d140f001d040d925440c03a04119490b00001d54901c60340e22100c0005407003825804840da01e1a00f0f01401c88a428001e560390180700c01840c0c160742087d2900110f40c403c03038001003458640414000c0c0340044060051170380001c42d403110300001c0c0d0301a007 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 876951061 1250 876949811 876949823
    0x40b131113060b161a01050904030e06040314060402090a0c0f0507060b03030403081804090f02060903010b120c1807080c030721050106021b0907030e010e010c02010b030d0206091207 80
    0xb0000983c0c48a500c040d244010400e5003141002d1420b00f040800140c043c000845040402001030019590343d01c0b40c0780d0825018030346048400541400f003503503840349401c00b40185c01050329810b05a0030000fa007512a600c251800205a1507a00d501429243c0c804209008100c040060a10051140c0d015110f281d014110105032124041c1c08281158004d03001524150b000066006240210621055860030140e03010405811a134a64800ca50f01a0000902c90395001035074107500d40d42500700c401c540d14000c025141c41c4c244401d215541b86000d030741141c040d05140b064000580011684640700301c0307860b100c0303542c40c0d0398810751403c45510041500b402d000c001a0f00007d001c807040000c650000000e000054154140180a850059802280c3e8040c41d180c85412035141c83c0ca4a1a0f03400204504000c5210308101203500e000d01a6400070003119032a111070b1a05417681500052010071065060301d915448011080f41c07540800c0f5070105550740120008521b40006400034940303c1d0243e2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 876952311 1250 876951061 876951071
    0x39050d060902040612020a14060306150d0c200a0b0c0c0a0b0412091202012c060c07091407050403110d05010c0807030501050402071a150909010203040b131113 70
    0x3500140843d80c090300868070b44c01c0f81011940071800c1406840d0060020700d501c50f0700c8d5080445c00a4031a200048c003150240c1c2e10940b100d0b410780424000c2d1103540e8090f40041c010034620300c01c0100100030003120009000310300f41071281200c4d004240841c006410006180460b0780300c41604070150311600d4010707075910582a082c0d010a136401489030160f48180308800c510241040010400c8003190401213421a03100440c02c0140e030003040361a01603551051034810700f54420802e40311101c4104110703400840c0007640007090310b00030072840c003900ca0b1850f0400004007880304880342c50108544541c0403400c00c200034000705000d07007203400605d20010712004000c41660b03a4a0300399038003002450040b07440501413001690300340c01000d000d444151411428014213803034514a0b541805a091190480740011913030003040841c6480c1d021402030820082401c0900c1001e00075802140c0c107840610801001c2002c00184545c2c2905041d0405420337900d0071160701c1000b011444010304204842d071b4039 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 876953561 1250 876952311 876952313
    0xf0111070215071b0b12060111210409060311040c03020a08010e0a0b0d140d020f0d050f070c030c140f130f0b090106030614040903052d0739050d0609 66
    0x1401039014207411741c1110b85031000301d00d00c1440d070440603010320f060296000b4115050301e030000748401d2a0410a41c241414100c903031038141980300302c1d00b00c100002e003080004010310044c5110381003102000d680420050300d8102c0102c0807030044080c05800140c24100404c8141214030520b50418840c800008940c051000021421000824222856091040b9030a10048140002d1500c0174141c0040c0203401740145099446d0244081d0130304c248140883c400516490310000d40c0c00a0b94460b080000c4107460b4102661102045d00c9030b00c4c404d8180d20055a5241001c11440764a420003070300719680f07034010590b00e0000c1c1421128800c0300c04c0c0c2c0c0c2d100703c85169981103a110f0007041380f40c400240c45800d00141c0c01044a028401c107000b14100011607001907400705c1211801218802040f61702c00300610b801001024864400504003c0070561809025160265502c0c01440360008414581200741c0791a4515081800142c00802684200420300300190414041d034801c050001c0c081c122 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 876954811 1250 876953561 876953603
    0x17100e18011e0e010b030105041e051f0905060901020a1e0215011403190507050d1403070b0f06010e10080c09060403150e1b060a0c050f0f011107021507 67
    0x2050008011141c6070943c21810010030700c14403200b5a000e80c000d00c041d2803e5180c440310100304003072075401c002c02e9080c0d0100384003040c00401c401c3c0d01c0042c1c12041d460b41100100b409080240002d480700e0190a0209102010501c2102d020352100c1c1c4031500100f032041d51184810a891206c041940985a50003110710000f4541e60702034102000d00c40c86d03502840d8241450201c94400ca03601110703440010131f0100340006401c0c01194021140032040500616281c0d081c05031140d10240d0620021075020200b006146006120b810222001c3d026561031800460b41c100301156080d812440e016589030a1b0740c400c0300e9040c0d2105e41070308160328010310000030075400d610903403003a40d44904c8030300c2c0105445031601034440740f4156540200502c92500c01c0c481184006800450701c11040042c3d24032a035402541204001500641076401c1d200c4bc0b41c0c0816100c0c05400e00c0c40c00203501c0c102d10401c40c903004000303488026030080c020381c0826007211101c40041c0d21881c03054a07041400030310703145000781c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 876956061 1250 876954811 876954851
    0x10090c12050c1e3102040b040b070609051c0228200319021305040c0627140112060b0a05070812041a010b090904080a0e090717100e1801 60
    0x1322050004080d0041d500c10038403c02440030302d840c919004100c00c101c0c6a05034020b98055803104d12050303944540310310f0008002c0002c8070000f4854060300f000e0070030914008a00200d400c5698090354001090304e89200943c1e060483c0b10b1808502924880d00800c445014003481c8480ba00c090710807418070f50f00000c0c034011428503a4036081140c81000402c44c20034000320b0000d034404800c240110f0810341c0e10350700209040d020f1201084540044415401c42e206a5002c2d11004442050040707502c0354110021100f003410ba403808140d13a440c038042c1c0400244180d1040324031400700c5038240720090904551591080c102600c20391414040e8440030324614032030781e01035403286c81c0030f0400603c0003c007a003070000c050f072010740040d006010b0080c144d100c03c201d4039072050303115114075514080300500361540300b05403004903040700031103003000101c5401c00065022013941d406002240d0f950300c400f01c4551221030059142500102d40411040c0038640a50310344c5501480000c15010182c02c00303046d82207 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 876957311 1250 876956061 876956089
    0x2d020a0c0507170708011b0804050304090f021809100635180f030a03020d140408090301110c0c0f010c12050405180405060402010503100810090c12050c1e 68
    0x1000441c903803009803c2006110001c00f45040284050050381e00f071141c000d0302c4250303c00240102003000408011781401140c0151219000400418020050110007500b140b20012216a032454500e40185000e0442600c10315503424080e01c1c0d0b074141241160140d01d500c2c89110440c4407503a13880300000e00c0900f60406074680803590b0081d03152411003001010f12030724890400360800605180445000710480b40c1d00b03200f40c2800340c0d0320f0b0800111900240900e1144d10700323410425003444200000c0c18020700c0390603070441c000e0000701c404070390341c15140c42100c3c20140f484c1e11904c0c078080755040000c035220001105060a86101c441511050380c040e46000707503440041d80000f0144101e191400c006106003d0068050f861854a60345943d0b031584007500203410b000c0c01100040310500710042c908007610495003a0399482d801c01e800c1e0b1020300700901088444882090004c1410358036030303185810281d0040000c0030b074402c84105001492015a24400070b001c84c0c0c0d6542c1a198440040c1841e2031 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 876958561 1250 876957311 876957329
    0x3c0c0a0501050c0c0105070801082802041802013b0f03070801061d0906070c02031606020c240d090302071203081603060b04050103020903101d012d020a0c0507 70
    0x85513030004190848100800400078482001c006101130800014222a40c076036010700b01280b12280c00c411400c01d00c0c5e84a000f5441410104a165100d04000d01ea405451003a00d46440300e0001d441c2081d0590003070400405881500d210b9842480300e015034039a03192401402003002421103c011a00303281003034001107401d0b9140c520402030081b03401080041c540707000b100300e40301d41803050506850310390282120f010041d0500180b000c0d943e0600c10500b03400140741c154034030580e8514000e07480305400c00640d8800c049004140030118044800c6800d81380c100e0480526000400d58880010084400b0a80441c49400c0c804589903250001004a2038041d4407032040358502507130811174030705404961070704050402400f001040385040a940503201c090030056110000f500c0824940ba408041d03940300c0d10f08100c00390310b01d082c0a03910f0b8020306440900030b1144081e60081c0000303100e00290812180d0074100361450106c440c81e40a40a00030b46498003d140150070b44881d45000010f40080d568 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 876959811 1250 876958561 876958567
    0x1504022101050103050601120b0f030303150108130f0f0303110301030b060405090d090b210c0306150f0a05180916030b091510050f0f3c0c0a0501050c 66
    0x11000940e440c041c0140001d181c02c0c0180d01e00000000e11059039000748101c0207480301000075a660399580d035001c14260180440e03441780f40c52060300d04c10100052100c0c0c04540306801060030565201c2c04a00f489401a40d02400a1150355558200b090a82010341c1015907504c204401c1c050440c1c019402503018000781501800c150042200b112005000c01410303038440c038401c8251541212280040fa05010a451b40f03601070018075080d01c01205480c041013541c49e0041191803040e05002d580111010344610300c42c0301c0707600c00810f018450780b0800c034000030b000c0c0501e040b1248103100425403845902000f461a001c0c0c1c0009c50764107481545c03140c51004407008003001c49039051181c0d4441c10700840b043d44503410b0a81201c83c8001045450500844c1c201e460850080d000b1400c81780b81c0505081015541d40400380c0d64003484d04100d254a07106201014100801106110390041c00030300711090802d83c1c03d038042c0c180d04c0c40e485805062240c2c051000464003040c405e105a5201d117425004043d5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 876961061 1250 876959811 876959857
    0x603120a03050a0c0e090109020a0e03060f0403090e0c160204020c031305040f11270d0f1214090d0606050a090501051507030203030a0b0a030c08030c16050d0605150402 74
    0x8180c4408404d82420000c16142c03041c410740d01c26981c581100e24698006036121554242159101406007880d40c044c4206818407007190203480703400703100303600903030b42c0259158640042c00d14051003942c031031031810f4040c00454042c003200311400c100303244000d000501c3c04103151600343c219086050401410309600400300101e082600076004495828801006680081c00c40f107807141c05504400001c884040828602041c502c1079400c1e000c440061402c5164040c919010340305000750342081b6250111000504c915a00a0f00400d00301034001c402541080c0e0001c091002c0c040081000b030714555121640043c41c2e4403442c0c2a10094074040c0c2c070220310396041600f0301c4100b00315001c0d00304089c13004000300070100394048196904074506890100306180d108000882c01d1314260070240180340c1d40b00740040c2d102c1000000f80140c85140040e01c0d045a846184c50507044034911035150441d000340c041e800001e103d540481d5101d018041d1a141c070500040200381260012503000b403d02a905031408 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 876962311 1250 876961061 876961081
    0xf09050a0506030c0a09022d1b0d0e090405070306050703021b070b040501082802190f050a03020708130f0302120102071a0a0b03011a010311210603120a0305 69
    0x25a0145050f001082c0c16001100840c2241c0d0051060801c016030201d0407090030301200c441c4003060203240035501a100e1207006196842c0d44000419201c84105130350705805034802003229420802c0c66101c00b15482150018442c481200070000c440c54040c2240100006825100f201e01504469500584401503100c182403240c01400d04001594807240341000000003020031141550001e03c1d08603115299030f44207444000074400c1d0104030595817070f4000003521903a0f010b003450991402c0d2040244d00c0101050341c044071110040800580c04100f80b43c40715003c2d40007401319500c24420b40e07242000030400d40b1016502c64110422032091003100b0001d61030b04002e0b0f5050022000c0c000c500e041c40e00d80d242610b43d0b0501c0c0320700315074050303800010324103030302c1640500d0300740802400030300c02590a40c03100c0c103980b0b202a030300300c9c00f280c6002e14501c0b48440560a640d54004199400c450040380070600c0c4000003001030a241d03051050350030f01e0000d0308012028210310040703502c0210305800c02000007 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 876963561 1250 876962311 876962321
    0x616110f0901080c0103230106030207171602120708060103050601080607021c0e010e060315030f0a030e040f1d0d0207050d2625050613080712090f09050a 68
    0x40c610851040c4014030144401080d00d4108400900740040d00e0124201078032420b4107400302c0304803c0c0103494000510240c0580040400c0791145010f290309101c1140250010b0254100e05103640301000d0000c001170502580d03260160000c070048881c00395494100038a4900c1c242c00484842d0044001000129010050340350000d4060016180da000d440d072800c6e441302104d05000c0708100c1014034201031640552144c03e01c044c805070419580e490101c4040d90b203280400011806481035100252142c0c1c00441e40c07408072603040c0c0d10111150418170400c00600070944005d0240c5aa0301c55060303181ca070380e05c107135404050f0303810140200000c00c0c84041e050100d141d1000d4029000240050006414682400b04000c0b40da04040c642084034505055a400740c2002010240041c103400f000c5044401c900c0d5a232684640d0440720300d81d036100b2580000b41001c003c010030356801131000c200010002c10f5401a840e00b035203002400681c2d01c0303007084084d81c038030340c840d130340d941c1e038503814005003046034021 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 876964811 1250 876963561 876963589
    0xf02060a0c14073219080d020f03040c081c2f0d0201061406043804030b01082d0f06250c0201051c090f0c06020d0e06030a0b061611 58
    0x3d20080d0303c6a001380c2c90303c84119410740c1440308071407510242001441c1c015a15a50b544000454498042013a180515441a00c0580c2d212820810015031440001484c185482000c0c1809017080580030041e14029443c2c5220749a5014290412000c200d8031005032010307081240040c01310540c0c3e074501034216121900015000c0002e0740c90000701e03888007801c903012030345404886005041d0700e0301c89000d80d01c1402007044032030101c1122040313008003010140c07013a83c3c0900c14401c02c50340c2e10b1182980e1075952142c59a80b44aa200f03800360310a0079043c04040b048403038401c0c0c4403061103507061a400d01d142107810440d022542820000c034508030200c00d000101c800d041c064801010790f0006400b40c0510010391507685407151031b802c010180e0340c109071807031a0701034107400f81101140340660f604c2c01c540c0202401485074440d0750582c103214070302c001441c02e0701134402440c5454407400c21000d4420305440d6900411b0030005100c503141c98002081800e03000c0c511401118001c04108425400507a103 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 876966061 1250 876964811 876964883
    0x90b0405030615010507020306090c10050c06012106050a0609050f0601020c19080f0709050603060c0403020d240b040506010e1c051c030f0b010f02060a0c1407 70
    0x180100c0c1ca0014010390042c0e000408441c00300c0340080103d83c188070391103000f900b6024860038407900600001e14051a180b040760019a080400c00c0e04888070b0107000e146040b00ea2004c2c00400041411084843c00c80308410701d03007d213030301c029100c401c1544c509580e4801595543d0380f041100c40c24602c5046d0300043e001c044046682031103030001359a0201e605800344150070401da4590024a00c0e401030740104050742c2500c00039121084070765160043c0307209504003c0e04190000350245004143c280c03040300e0800300c01d070405003075400303106201540d6030044236401113103103860343c0d4140144004018458401008a5a940b4003001e02c4140d44024000c0b0381031101000c0e0440266403811034000075008880344058028450341809894440885420181c4d44143d440c003070401c90381038102c0c0801d60030600c1e003408000c41071801140c0c00c01d0400707011401600f00344003107513482e10240c0108051054900c0c182da0138901d800202034180e84011000c40c1c840260842800c071001e030384c49040110300e0304a1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 876967311 1250 876966061 876966067
    0x1005130c080a110c0703050c0a050a05030a060908040938011b060f1e110a05030106111c1d0604122a12050c090702030405150906120403090b 62
    0x38501030510071001d8120115030303854030300e24554070003450140c84000715400c0803144055947e0030b20945035000c90f809140102400c04011605007480021170049800180040c00035141e40e0302c0d00c100500c010344040358111010000010b41c031281e4012002509050104600340300544480300071021034981d042c10410040d0401d0481e541e0b0000721110501c40c1d04c4107a4030200320180313030620041c854401003580c000c2c50060151103940701e071008610500603030701007002000960300710340f0304600940b500280051810801441010310820240c01c00040310000c44032074100d41035003040c0c801403056110000900115100c908400a8040d4020070341041d10382c14582401d0500000f40c1e024004805064002411040b031011030303110019404e1b00102034015003200342ca42080d80c0e0300d07918444081e95180710300402214146010900c0f14058080764004501e0586007400744a91441c0b032052400e400a020700080d40c41e0780310300c002444080d0100c1e001185a14151401401418190708280d04062040c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 876968561 1250 876967311 876967331
    0x71805210d032009041808070c06020604170a1709010e0106290901230d0f0b090417090d05010c081f0504021b0d020a03031d3003100513 60
    0x140d0b815021807072541c03009036130324101e180104024155444204064030f0211259400780182035005d402d03500d100701031290b011580c940040769a2501503501911800c44641c0c140fa80b8a80c6c4001012800d5003418044043c810310042862030410455820b034950351180f06200c0704200a1007000301070b003412211441c0c03590301014840d0358030041602a801284000030180341c541e001d001e168450a91303110b031084502d01e042c19141d00c141c0140004491241c00c0a0032620300520764020242020000303420041c05d65030395120241880745a00814501d440c00300840d40304c3e41ca0304d4a500704140e0040340046042122000020400800180a40c50081840d204141441c002503c03c4080311b20803980541c8645840340140000c511983c1e60380410300c00c0c50110300d200394011600c050214002c0c0c0f0104116081601402d06002c00010101d00c0780d0800e0f21b884404091090307401101031226000e5001e40385900071000042d0380155071554601c00075100400051410f0005040480d1440009028004003 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 876969811 1250 876968561 876968591
    0x60c030c020d11060612070b0304050c010807170411060f1204120e03031803161508061906031a040518061b12090f0d0906080a1103071805210d03 64
    0x4003601703582c40395a603001407001c400700c10001c0c20054003005060640d00e041070701c0d140790342c1c180d410b6685021504610000352483d00580e00d0350b10900c10720400314100d1391182d07100401400c017007401c0c5500120070f1200c3e98480d190320019241000b10f26008003220706260415036110317540f8043c198100605c0699454981e100481610180540d0341e0035004031000110010381401040c046669416403412000155003030707110a000d0000980740c440940940303890003030180694055402075801e580c01002000721500c00d40c46995038107042d0406101ca080c1480c0001c0030345074255000032a8503031084560000343c00c140241500303c405402e0744003401d182c1c20f0310b1914a004200041020810003800115240700500c402088000414140c4410003051140075007086e045000f00000a000e44000842d1001ca81c4903505030f0309010140c06045941d0110212190706089000a204078008400080c061f1614132040c4810700340e900c2d00c0d44003440000d080c5e80c03501803020407520805080803003c0b030710041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 876971061 1250 876969811 876969823
    0x13030507122d0305130b0a081501030b0f060c0a0807231c080c0c0f01060f14030c040b06070b010f090f051b03130803090a1106030f0105040b0d060c030c020d11 70
    0x1606091042d100c5003005070254005e4080e074013542a0a40000c0c9280741c05510050301b6100304d183c00c0410b10000c40b110011000c48ea030150070713190040202106101d071494801d01914007006464122030040342c440d5500c680300e40103c80201c40c030802070002d0b545030440c2c680c035440000031403c0082c442c0516496016000c1c104080700c1e8002e020480d004100c5000d86c2004a03410f0240c40011201c03084043d06000e802440e0920410b6007602c8c0c03440700402d8040401c4101c582c2403a0082c0100505107180782048000c022030100286e208c002000540002090742c0030241c02040c038500300001452038891840e0607030ba104150003090903d8102088561035865408101c508400b40d00e00340c0303a50744c02501c03c0360215028030203812040d0100400801007000280e2060081c42400e25000d420840c005000c0c4900059520204d1010141d00500640c1815807040c00d1f003c0c001040050354100c00c0c0c458004480d007884450700042d40712130340080381d26010050f10b44886c5c1a481c4c689039540c05d450003503031a03103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 876972311 1250 876971061 876971063
    0x1031a03010204091b2a020d02090411010e0f03120c01180f061104030f03140d0207060902100906173103080606040609060804140708030a170c09010513030507122d 72
    0x1411805146e801d545440030417044142d40a01080080e091508091041c010903403019800500180081190f5082140000c29802c1c0054020503502440c1c41142c11250805501078400390b5880c152101030115100d501c650302130050011101d9a59181808002c0d0382089030924a4400208002c1000901510414104035050300e4100000ca0059050358294402e402e4544c2c0703071034000300b070b0401070108682c8035100c0140300312008a001c001d90390041c0d0b001e2082d8820303903010a00d40000103450401c5c10290682c003100ac126082045c002180403206010b03071400d00320343d00400910100f4101500160f4a13500050212075160601d807030088000c107206014000d0070208602c0340003090411174124803408810620a00b510b000d6520754040c1c40e0340340c20008803000010b400c191500c039003031110341c0c0a600640001401c03e20700a00c1c0e074019601540201003c0309801441704000001c503a09101460140c10ba21040c49500380040c03c01041c0d1a1414a803407a81c00c01e1407442862648035004400945 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 876973561 1250 876972311 876972377
    0xb01050a0506041203030f0501080c1e0603180f071502010b0d0203060a020a0e03010f0203070f051207113c06060904170f0a021c080405060601031a03010204091b 71
    0x8581514007200030380004a20828003904000000c51034000224100bd0329140131b8482408410154400b0500071030000c2e074681e0403607020000301c2da092030345000d5442c6501c0c40f00e080300d080e401005c112600c0e010751544141b5525400c2c00b9840402507081c01002c911242c00c43c1c5c00300d05003200d41c001948402002d001209585c0c0c1c002121509640115034211245c1c4005008019840030301d480e01003c2d41c4110760000c0055428a0910011030080050741c12610404043d1509581c03050f6003900d0180c40000c0c007410034807460410038a0205d901c950680e0010381c2c800e500349250b421290046400c0ea0400c0f441c4240d81201701005a0707034540200c595440b0745c00500c490f68001c21031038426114030030080c002c4452900015174000540e00060811880c0840501c012480d18404408031f625100c00c2d02c0040c5660032000200c1d4142d882074110080707450600500c1c214600c404400642281d006910550320140c0328001055802505103400e80d03150403034105501c00b042d1328071030400b82d03180c032144520310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 876974811 1250 876973561 876973589
    0x5010c1505091f0203090d0801030b07081306020c0c0a3201050c1501031b06120e0c031e060c0306010909110702040c0e03070605040b1c140408070b01050a050604 71
    0x42d42c00304280804a0241141918081d100d100020060340c4101d51945142c460030170410b5120380300c2c1c41003504803500403800c6025521044000c942041c0040c020042082c403610360000490316a01c01010040e00178402020112000d80a000000d501a8024265004407030350642142ca036540c60000700340f40c002d00f051103102851005a510340942d5a813001c080c440c4101480210300d07010300a505a1b80160b01c4400c06144407508008040458001c20b0b000900301d003020003502d030080d082140c1c0c051000c0705460b8a000f00d140070070316281e800320500345001da00c00380001010b0000d0003076070b0704a0082d074041881d514140d40007030140c135014403500390242e41d91406070201d1180d40084c1c9100030350043c402d11103040e07a004018403822131002521710a000300b0038000703001809001260b0403942080c84290520380003046109440743c00c5c21003248055102c010040d0140000b4040500c01c9218036a80c4e0f0b2900e0580c10181022031058200c107000d0603400b4418030541ea5138006a8044490140380107038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 876976061 1250 876974811 876974821
    0x40609020c0d0c081b0d03240b2109150901051b0705030c1b010210052814010e070809073b01090605010314040213200a03021305010c1505 61
    0xd514421010790714610608900d1702e90400501081e4801c101c851580d09015983c48c01010200300301c24401203a15040c4460ba081200406510251400388108488400e005000d07003900d01842ca01118003400c0f0f07800201070920940c40440c0510340140d40c0800800140c90508501d0b8040b58001e110002c00110109095081001c00c20440c0d52032213004017a9680c000e031001d000c2c1d20f101070310014a800350003540c0b01d4500c01c01c00f40c819180702d03004440c401d28041d00300340d99050030302905400c41000720b80c030f540480d80a544002d0100d40200b00c40505c040003807030107410042112101900700750343e9030030600d01000130002182070056030303880d6188101d0395614039221544421442403250005404940300011b10044180e02010880d01c003a2014400900d441526460040c01110002d51100d19588071160728120790703110440494001287c0844156890303081202030b04240c0507131001a400168a4940e0703440542c03070310014807007030804004801c425501d2000c5103070010300200e141c82d601d40010b2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 876977311 1250 876976061 876976073
    0x1014070f24140601030c1d01030e031c060b0304030522090e07091a06030a0b01020f0303040b15040c0509010e04110409090b131a040203150c0702040609020c0d0c 71
    0xe4001d181c0c00003180311041403280c0103005041c022525041d5041444002819540203020707119102c07001380c0d50404d07454403456a1440000e00000350b1410540d452034610115182080105070300c49021070b402d03c0200c941d42000003a5034081d0412000140b041c8140800241c100b002c0c2c5020b00c80c040c000003161044003551502c0ca008561205813524101050b00c0d60022000c501207058980c0500c09000c61246100c3c5403d03200300303e002180d0005010800100d80c000030b80d00190720280d05205603900b181304e01c01c0d41031170741c1c00c240c600707603800c20240c41072010169213000b113000c40310b10549041c0890148464007610780d000b0b42c2e10080c1886540b440501144ea0f41d030b8042170740d00030354140e11500c2d036403030b48000d50003030147d202c0c12200c840c1c0070b20210328a0014014052020b96000d9032a803d00d514814400d400b105015000300d81504c500700c0c0c81c1c00d0140400c0c0d100ca01c108050b041b46030320b170690f81c010081552515070103066402d204101d45c0e0070980000c1505000361003d8102645c8500341c1c1c0ca405 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 876978417 1106 876977311 876977333
    0x1b02220506040203090a0209091005071d011d0d320c1c2d030e01020c0f090630070e010605090a030311010905010603050303061014070f 60
    0x6d4001454a4248140e108071908103483c1c8003041c0007003000c2910020340350f030800303e40c0741d6021450500c12064046886c400034600000302500910304c021f0019035402c0207038040c1c444080c040301440300d50300f01c515102104c5012508444080030a040301003102481e1203d503070003804190045490219010f00c83d038040100100d24000941d034070400c04074001d45031010002400040702c01200b10249100c02504d00a0300e07004061508407000a04102c1109000784c03141e110703612070001035140e20304019401002580c0440d00315138184107030610302514030010b0418880c03d61400a0000c0c002c070300c00045501c0e0784500c40469888060a84450040c9030855800c01e80003502080401d00c90202c2a1908035203600008190071a40ca0355130070366120b60000e607100d520000c20300030542040806061210100d1030800b400b4051246101c61031310031351401910940052154800b404855607030 = true := by decide +kernel

theorem cover : BRFrame.Cov 876798561 876978417 := by
  have h0 := BRFrame.cov_init 876798561
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 876798561 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 876798561 ≤ n) (h2 : n < 876978417) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
