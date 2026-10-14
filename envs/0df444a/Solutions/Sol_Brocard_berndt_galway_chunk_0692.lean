-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0692
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:11:01.025293+00:00
-- url     : https://prove2.me/submissions/0bfb231f-782d-4729-a0d1-650c681f301d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 124280575 ≤ n < 124460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 124281825 1250 124280575 124280593
    0x1014030907030311070b2d0705060609010f14040c1103041419180f0b101107150207030b0a090f030512060a1a0901020c0901060e090907060f050304050f 67
    0x6641c4a1051008a010492580d50000c204501058941c2114100d913221450b090001589800035081d14511b0768001c01003c1007071151702a10000b80c404684204000c3c181030916808000c4020016070148102e61891034090050060401244020a20545021998000e030b52000d598501e000030803008648000311300014005c1441001c42200f003800e40703890003603614605075802c3e4840d1500800c0c0d280130036900044040c0306a0f50040740840325010001440744031400c0000c090040e0350340c1000000310400402040500207020110090400c900720900302e5103000400394a07004a884084c000841c4c2c240090031503d543e421442c1071a501c218032648103c105c3c5000b8040d600409001040344500800058450402028a0059a80340e82080001a0004400350159440034071aa81140140d410b500a1521000031050181a080d121445085242400d002416400602c0e43e001c9500105c8100802c0d5004403030200c8101851501641d66070b2607042907480e2100140485005200304034003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 124283075 1250 124281825 124281841
    0x20c03120405090a1401030305130b070602030108010f061401110708070305070807090c1707050909012408060d1b03082206020312060613090f0b090f040f02101403 72
    0x410030b5501c200e901001070703240c40c00c0c90000c48207810030702c038552030740c42c801130002c6800358000e44000c1f450000008201622102d60190581240d807044601540120041c422000300380507500b07180350300380303000c110541c50040080991200c5c1105241400900c4003d034901240c21700c540c4e0050102001296101652441d10300d0b46d81d0020b10911116000d01c01d008514522640225105c40c0030b50f075500680211924030b00d0040410150400060203030030815880c40c2e0702c448030072038020302d514a40e40da0303545c0302c85c42d0800c10a40030035210b074200b084a00c10003c0341d0303542c0c0f41a40c2405402c85400710148100c8100318181031001d4101900c40b89022400140c1450f00d9031600c150f1403041c2119140c1c07240d80e50b1040c0d0341c80c000c00f50302c0c6144415001c0012481e0a0100140144540b48403015200a55403180802140c10400c14030746400d80302c1c400a803183c10320411840c0c100003d1461140d06c1e1030584c45a694031444500000d200e14511021501894481e109000039080003800680e66420903c071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 124284325 1250 124283075 124283077
    0x5090f0405042009090303190e0d0903030201200d0b03010207170405010219030c0b0c13090b03060f040c120611040905040228060507020a090e0a140a1e0201020c0312 73
    0x14040c00d84100f0805403944a04024095034040c1a018004500355107845418404044081a42001d40d503929034826440c0402004004645a01030302c60100650560900a09507810451081c4070340741c0c06a0204900c0c2023840440344007070010326000071441c000d00c0c0060301a00c580070b030291070f140c00c840001340d0010400c40100b044031826006c5401c12086164540481018104094041030340c00f8031001c04599641c42c004d511105103510185010030500315540c0303481e50342d0000a030466a6216450701d44c1403c024094100c0b507107000c1031540f45404e03512440e001000d13029400344404030420301c604101c00398008842800c0880c03540b0f501d03103440d190082c00030314003120140d1040002010540e282c00c0c105682d00e2010340149901d940e01401e0000c00e68180e484010100c2c1c00c2a001d00001501454074460b0101c0007038208060180f80780d0354146610741d80307a80000103130f02c0d170082104000025a02400300341d01d41301c0e0380040350000160707000503401c00d9050400a50180982030150b201082544 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 124285575 1250 124284325 124284353
    0x50a0803150312030604050628030501060f0b0a0518150309010506011d150702040e2a0307180e15090115030209070c080c010f06060e0306061005090f040504 69
    0x380440071600164410103a4071049403a020149030380410100305103081c00d402055100718040e10641000c803c0010000d00b50b501a0800c8102c05030304a8180304201e400c1c000c0301d00602030a402009441c3c28000c1c009024031804d01894103000c0300003203c0d6660226000b0800138010010115503900c80786081c2801940d1040390103428a502e0000000c00d50740c0035101200d60030a803c451024120300b01c1d0140300901800740a09080f881d4203103c5200140e03654000c504285500c180036001c03900b440300c807a808546120020342450003008002102d40d803000500e8104540c4190188528000d4124040c0001c01090440700da1f140101000b806005109004035400b90f182107000700861210580d07412503001031404000c5d40490014003081c06140b18104880015000780185490540191101e508440f444c845024026031a07400070440290000420014845e00368060043c40c54914002210001145054418032a01150342200364980205c0a4031040300508108080c0c10242400d00340c0d0380b46d070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 124286825 1250 124285575 124285591
    0x803012603040b0912030a080f070c02030f07031e05030f030a020712020d08061c02060f1b0a02030c0d12031505030d020c040506040605030312190603080a08010603020f04030206070609050a0803 85
    0x14007400c0340400000040b1015071a0641d240a040c2d01c038012709200e00c0030050416010010300301c0050300503980030320031091081207000050130f4451075490000c082c0e9281100e034403440800e8403941c030302142e17020088600159122104641d03a07961540040000d010300180a00381038000210750710101d07000a0900c00415642e00d401d00c0907a40c140c00c102690640d184d854a0b8008500c03c040018144507014003500804c08505905141d68080c03801c2d920f1440d14291181584681d00410030350600f40030400b1600c40c00e48514150405c0342c1c40e51030082d20010400010103036264800e034121030420039607a000d0305e0024282c81c10110b071002c0c021758441405080500c254074000100d07040d46810310944003201d102502071810400c4445104200610007013551180d6070300c0400302c03421007984d03108000103940700302002c640364002c8906c000e080100581100d01494030410401c1c5140408405850480354100c8a490b80c44802e4908a40a4081c940e4002c1451080500c0c1404210042c0c02541c8a8070b04 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 124288075 1250 124286825 124286839
    0x91a0c0d1d0d080405030d090c14090c0712020a020303041e080d081b040509010b030717040c0b070312060f360b04230601030b030a0803012603040b09 66
    0x180c905402001c50000c840c0445a51140403400c80c840d0050501c142d10500903400d0702e0500c8460101c02003640da1865045035900c045800030b0014043c035200324140500f003a00c07840c0c1940340c00a14202c0300e02c12006e020f401100e111088000707082c03003000b0462005902a05680c0c0303a61f90307071800011180889007141042d030740fa10408268807800050b501c0020186e80d40f00903140c2c440003000e141c51415140300c0034102c10700f0800820303a5204c8810090090489901007a40d91a0026000b0000030034217003040701032204c100521000c20340b444840c500b51440d011032580c0e10742e01c5140642e02d440d1207000c20950301c4e003000360000305101c590081400700d50540c454003007050146942420744540e0582850410740312203100b2003144419901507405d90f83c01402c00142d0810806500c50794601044418090220100030443c00f96414002c904160303800b640101558035072030b80ca4a100340014010400b00202e03242500d2504804001800090100307a02665035a0b5260f0f030078400c095020301200e034000c0032 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 124289325 1250 124288075 124288091
    0x3010c090801140412080709120308040605060103090b1b0c011802030d1107060818060f04060b040209030c0409020105070b0906010905070906020607031109060a050d060801060810091a0c0d 83
    0x300d442d0f00c0d44919440400045c00c040c0d90038040d1141a006060901000140c120104084401c1025220340c940030380c45d29441380c13505192903415148000c01180c10103051074100c0d0b0004000d075401a401c0112507010540381074035481c85206900400700c00310107640c20b00003090079170030300c00c3c5040249500a9080d035680c0e0400d40001e4940109101c80d01045512003101000701a00c5550320310f4015156120b1103d014600c04500c2c0e01d040c0c82610324400d50b0384804144400c000c020311424403059005c4e03500303608103420a40000d841c0c1c49854407007405280c0b07449000003168070903822100c410368003000f0610a41130116219507240000d000d1464224608008514118011004601201d9255000702603541c0c0300441100682203221301c01b01c181c2400d20911056603110000390400380300d207555444d142d4920030b540d07a0a48505500001e420b1340340c598240044035000c82c0c0b90032404d2070342102081408442c50441700c941c42e09200c0902034514807081c4111a00200001c000030001200123101c804 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 124290575 1250 124289325 124289351
    0x51e07050c0303090a12030207030204061805010f0b040e220302150901020909040305130312050a0e040603050c120307122001050108060106030905030f0408010204181e0b040b03010c090801 83
    0x110413611a29800300003918100106941d0440c1000c0751842441134549a82d0b5030b5000c20240da401da0411109440407135010f509560251007400d0040c4090008503042d189840b0b9540180c1c03245001b603415141150001802c1d0241200782e00c0412641c02c4903d490034541400c009403980301e41041003220304180c0010a040b22414000d0300e503c10f00c0145040380c41d0b03c0e40d81e403d4a03d0f078009a958503030940f1a00c40000400c441c00d1110407840c20355282e440c1c0d034500621001380a661508521403013a4500075050001c64000101c80540440235a644500c04050038480c0e07185000d1260003d24000003000c03e0541c8a0f400b403040d14403042c0300002d034922140c0d001d00340c0d82650000d0040301102c1e0f20440c010841d55100750070800d40c690145058070b28001b0038021410039036001780c010840580d00020100281000700025058101d500b030300800142c10155150780f404070701c0407043c0201d151511034002c91692a07501ca00f6851a0080080091040c2c24030050100031380380c800e06200b03510f002060103003c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 124291825 1250 124290575 124290577
    0x1060206010915090902010c020409060b030d0302120a090206040801020a03090b06032b0507020901080f1219030903050f0a030b030106081b101701030303150b0c0a02010f051e07050c0303 82
    0x11014440c8100920744c140000b6400414411209a04001944600d200544c49500ca424103090007410085034044800040c94a440169441001054410080781c0700200c0091400c582049003820302286001d1140001507035400769070800720480d440014a100300b51b80507848050f107948035801c2c0c000140d807003208154561000c00f0309904c3c491003d44400c1100070340758000c60302c0d0000d1810b00e0b80c1030003155008103815850036000072403240e211060082c41041c08000c2a01c00007400c400c460300d0568003403000120705001e414803c0901da1550645010075000d42c0a6031216104680c2e01520784001280044c00740641151060195181080100e4819400f003405400182c03000301181420346c0080c14805002c0520300300c4010005016080f1160390080781185000b1070282c4d03008902415284c0c008640d40f14036510101005008001c03910381c001c00802c8101c00c0640900b0006030b00030000c5802d0b140c0744a00d030b02c6240002051807444403404204800f425101d0300440440b0b150301c0c0d240b03041c1556 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 124293075 1250 124291825 124291841
    0x8010b24070b0c0c030d0f110a0906080a06032001031a0a030f11040203070f0f090501080612010e011b1d090f040611180103050f01050109060e120d0503010602060109 73
    0xc14101003003400c1c0411503a4007042d41040d1035102d41d615251140e44024115004001030845e00c5403101c0034140c071a101401800040d00700c3e25601031811404030f01c081e106c5401d0703105070740a0102e608000780c00f903001035008600968000c0c0c0c00f88942e101700328008600d0a8001c1055010919180c103d0b030160118060050209a01800c01080c4600f15100c006050711042000c4500c00c8291101140544071030020718080e00180e00d0b03800391010316600180c030034640720075110100303d5005001c0086a074019400c1d5000101a03541c1ea81440324a400a40540707100745d00f6840540c2068028003500c1d0f02110a42c002507050340d5601400300140c1c6420284036071600c0c006034001c0540010540d0981903110b0703190828403800c0009441c24030b511700504036401200f403e14611202d4240c8102e41e50301809a070b94802c06003e5003da40c4d41c10500041c200003078500914003002148142d809180d16807075100300c2e404030300d03000b00c84a80d42701902c0200590320174010500140146400003c141c2000d01030344c0b40c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 124294325 1250 124293075 124293139
    0xf18030b07030b190305030306090c070f110d020409050313060302030f0402040b0303121515030405060403180f03050a03140c0307060209041d060106090512031b0c0a08010b 76
    0x10441d00c1d5540300718094901e00300410741c000d002d60320b00421200206180d1000314400c4029580702d1800c1c0080010b001002808448158801c10883d8000740c440e000c8102259032203c03070a80010340010105000d82041080250490328180946092000c004045c0c25a510704111510a02d61503140c101c00b13a01082d202065052071070b5010800500e000e420524040c24040d084034140b400d40d64044442200c19205aa101e0001c0800e80d6171500300400c2003103c0c50480d0f03002c245181810354906945010090020f0100089884411180801c0d13840400040001c03240c200c0c021902da0804035101c442200d4120007040070f8144044c501e10002c402d0350042c48080016606080d01500c50401030350066100d03c0e4415911407050694407020205009400d40c900000c040640c104800a045041c0c40d402c00c0f485441d03050b030b40e0041c02030001b089032540d00c0800160300c110440f041382a840d06c000120751580c400390a2001103103502c0c055212407003045040341c403010303810905688900c604001d400005 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 124295575 1250 124294325 124294343
    0x3040c1221020d140c0f10020a020705060702091f080f1605150714010f02070f020301060504270606030f030804030906140d180203100e01110c03120a0e06070f1803 72
    0x200e926080038025205d10080c0030f0544901603c1041105e00707005203120400c1c41c1540c04500074402e07071303410054900503120913103451740b07003800c0354000a018070002003079000551050b46c01c90420007007014103040100004800c4507030288802c03024a4945c400c2510708044448840c00010f158a40f840c0d04100c0c20254443e020702e024110740714820083c0d4241c03040d134507641d20b640400d100f2031480e1000340521401510407500d86a00e82c4704240c2501c0065001e184154141558003a120b410a000024000200c24011040e1002d034078004c80940140e40c0702500b81e80c00503408109040c1c0090302d00c0c0c0300e907100350340e0149803a0b15118142c69181440807414090081448143c0310200503911020800300c400c090301c2e40c503c1c1194006807810300740510031028a512044002d2507601c007401010841051480110f041482c10303600d0940d64000d4618520b4002408004035500400c2940304040c07815400c015a641c07464501d001801c881c11a010407000240310300300d5041c2542d010406038040da40c0c002860 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 124296825 1250 124295575 124295597
    0x30d0509010f09030b01061e030e03030604090507080d0801080f0708030f0a2001020d060608150405040213050c0418151e08060f010501021c080c03040c1221020d 71
    0x44944a0003010070740305024a03a44040007040c0b038260170314005c2c07e1131750300c1406120382e079403241084a0880d000c000c00d260602c1c075801080000801035035800b10042c0d50002d00722030681002d919040c45548020154002c000000000541c492041c0e0705030384000c01100d03010740340b44013100d40c0c40781e540c81020010b0b0020722115039065044030003071806038040c0ca8460300060740020841d00d80c1a1055032808d55a40c000b031800d0651020b4004c16000701854240354100303292036103403c03118500f402c0c5400c6c03050f5901d0000800315545c8040219503100601c4040003c0d145c5243c0381e11550b4840c1c020b2150803a860100d001a1600710b015031100f001046141018561422860f4115541ca000c0c61141d0b800e010200401c40d0201040b00d24030070080c900c20034009514280000e800c007202240940002e5010740c00c010303d84c2d07800c0481250003261003900c2e590b581e9540c2c01c2c40c0f190425207403c480d00ea0103103403414000340036543d00c1c464624198544043c401200501090340d0305c4c550900d070500887c220040d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 124298075 1250 124296825 124296827
    0xc04030602030421030c2a060507020111030703020913020304030e09090f0d0e09060108040f0308060303040302130c020c221802040903180b0a080105090907030501020412020906030d050901 83
    0x15540041c8141d00000c5810510a24904400c0540020700006646c4040d14405980d001c2c03404020b41001103d65121111a8000103400482c0068054101e42d2258042040710380300354000d180c0580c2d00054181c4a0604550060207540056a43c0c2d104031400030780b07500022038070701c01c0701e000703582c907842c0c98204076585014024500c0000704480214061049104d035091070600690024060355514a034111303485000b00042248043c008504026100040100203612400e00c6400d2641604240303205030f85242c002840d5120329000250000041a96850400c115411500311203001da0291410102042c05000081d145280c0b0500e0102c50004580a050902e900c22040706040000310b40203001ca0390003180594407051002c03000103201d20305140e1621b00050303410000c0c00e0483c40c8145422100c0038000c107118810f01506105503203200208000c080100810402507a1010095440c0c81d55200307240f6084044007000e03806103200a000480610300401c803088060643e41f1540d0509101c080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 124299325 1250 124298075 124298077
    0x2d0d031404030318061802120708190623150904260d050c04030b090c06030106030509030903160510090b0a0309020d0b09100c1d060d0603061a010e03060c04030602 72
    0x100313070b91410380c0e010315008030360903005034681e003e86a0041c19a01840c1c1c4184480a085d01101d15060f4000510500c2110400711f00007600002d000c0343d02180c2c0c812800c4c6400208032070010710b10081d0240ca80401403180803106903205040809001c1000c0090390140182c50200710f0b0000c0c0032040448079071000001401c10242414644042241840c4d142c40c8124201c8e0380c2034443c0107214102081c02c00400010740066544400000040c010083c03401002c52901c0c00107001d05001e02d81c0b1100002c0460720b00f00306a60a80c44d0007011140c10035103111030b41d40300b094680105401011106c90000140d0f0161451108448020710301c14030b00745a0741c00840081440c1181242c0c031583d10b041e128003080c1c210903424000d0803914060300504d28600512070440702c1c09004c400c2440104401407820608841819105c01020388026a59000c049940d000400c41604020401480d10003405200040b021120144040070b80f180c0c014116203038205641c0311022a41017006100400c818400200150 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 124300575 1250 124299325 124299341
    0x1b02010b01080a0203070908010207081306170f04021f0c120f02030403140a02030307240605061602190e060a0f080616030b040f0f0f05070f112d0d0314040303 70
    0x11412547d11303030b00c4482243c2603078446c1e00255001540468080c000d16064100c4000504481c14000c40408417940401c0005800500d00301040903801c00040c15501c44103080c08810303d0000701c0f0010114219000342500450600030b845020f41c800c980b10b8183d0003030b80c00a0000820f5002982440d1555403400c19001100f20400c2507070181841300c2e0010b0f1410800340040602c00c2c0202d42400740c8040e43d0103071101d2030b882c000d2000740c01c0040802891b2900011582207105940485040c013801c1e0010a440e0041042800b81003a1180c0000402004041d0810b0103403c00f02c03141c4805030740d81d04400c84180054016080d044d04210003240005040d64003075001040603040214094050340000750448010540d410b44a6031100c000240c94001d81c400e030320404500000400c01410820300041c42488500e1144082c0f08030101812850708041107241c20142a0740312222074880216005068002902c0d40f01544c2d104555035010114042d004805002c030b500c12107072405c0ea0701c9860490103450b0039 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 124301825 1250 124300575 124300577
    0x101e0e01020c130e0718110f040603200309030717090306012607270c080a090204020412050309010807020307030f080601050c01060f1a03060303090111070f06031b02010b01080a020307 81
    0x15540d13107001d80d000b44218001802042004a0326a100c1c4007410709503051204040400541001186004001c02e0280d5080c0c9072203240c0081c00b281812070031180c0300345018a090780c0820220030020802400402001514807032034503c1003101e044101c126040c02901e04d8168150030000050101c411040b101803440c04880300e14074140c0089134181402c1090540120103001c00e05694100c5030307908280306600000f5401820030110b810305100a08c007510280040441135280c4543c00d0030f65a071501075801400892640d190880c4c010324040c0d94a910480c000f034081056140010540303800072081e40c1c1996050b441e04448485401821200c0b400700600341c2d070502505002500b40d081c400d01c0350750081c0241c6180c2e800c00d54103090510484a41108480105260801c200502500c01000362201c611085c240030324020f2714400da040c1490b03c02c2e00b00d80d4a0075110035001844a0b4903400c0700c0d6484605031000e40e80f02d0704010080382a1000c64032002c0c080752406d00803030040900d0b40d004550141007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 124303075 1250 124301825 124301831
    0x40824010b0a09091a0a120b0403051803030c0c0117040807111201050f04030809030406050409050a02041203080406050604020906120903040f06020304080f0102090102070303030b0a0302101e0e01020c13 89
    0x980007120122014849a5100700740180481301c0c140c100241b08901520360740d001107020a0003a81e600c154214020001010010f01140d5107418020f46003c214986070001d050f039880f80c2c201e5004070750311030203540c45c180092190052001511078051105001d660800062890140243c07282c0e14078400e0080c0d4070b44c000c00982d5401084020a100b058014008241022042e081c0781c00c004204100140105580d03801c200300411440d1b030080c00319400c80c1d00c2d070303080418960703640541078000b40035a5006c074004006078030751075007050382c40b0150342d1150348916010445c6890354404d04c012800b41d50700352504000d0420508a195028082090740121003004a9180584690190b22808071720307400f401c0940e0011409001c10003092110314410070301c02008600700810800001e540d0340e035911000e02031542e40c941d003640c50380740d4800c0e0001554000e05098002e82c00c101c0020b0114000c03110f1140078450080465005501c43c0356009018a0142c0c02064101d03007a0080012044d2081091952199 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 124304325 1250 124303075 124303079
    0x7090b0f04020f03060127031e0501050903041806050609010c020a080d020304080c09060d0f06020d0c090503010f0501080606010509040603020901060e121f021c0e03040824010b0a09 80
    0x2581d40010507410294080c50b544900740200007400b040c001111502d20760120094110800900722504421243c03c082c3c604809501c4001e03071004414100000340065003044100000b100c1c00000810458901c89803800e004018403424504071401d5000c0c55074095002c220341da50662040001407685030004240d0391040f0b944850092030840c0c0e41182001580001c102005506014095003039854001c0d0703015241e038038001c4001590f0f40070200c40141080d411080b01d0080c0502541038030040c1c1480c4504100c004032210000d041e80c0a07030310581b0312940c2004096062031150b4050181200c000f030b001059662140300040d20341c2d402c020340190f0042e0392a0400000340c0d0300d000c4a039000780500d03121001c000101000380000d5001d134840000c0c659118085904420b096601c154034403001b00b60300140c6680e5a900103d00140265910b00303d07050a20711031071040b150120040088414010448941c2e0038140708003144583e411420184801c200c3c00101300e902d0554008041451180ca80030000341e07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 124305575 1250 124304325 124304329
    0x3030c0d0e150105030120042108030112120c1a19140406050906040f0b0c0d0c120e0c010c080a03020906070303090b071704030e0f180f070e0307090b0f 67
    0x1048200a802c060301c103980100702ca0b04081c0b081e0948822020169180c0500d62070f4024018441c40c450240c41c070010360f4107000004040802480700950000016941c0d5940f1641c81c2c5a040314010265020a00d5005001c00340e406080150001603008540a085103960b144482c00c1c410010001c0c66010760503814402a120648150203141d4081150f220b0b5500307160034030310201c803c010300c00c001e554040b409200125203009403109420ba8444d011509070b507600d40f0741358014001d031381401030554141885616007680110310142e10401c1800100040c107070003050f80769903103801041c0c3c5000c2605a04183e010605010007014100814203000d881d110050000c0b904a900000090300060713540e1000d00b0030008000380003034102000b8a0325581c440f8036140003c1083c2005000107080c480110074405954448501c00a00042c0c010900756902505042c01c0316821011940c500c9410200c1000804660007100d00403900c1d100900100446030402c809000100783c0c04072070341e81c861444114000e1036 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 124306825 1250 124305575 124305583
    0x60105130f090606020102070c0911040f0305030a020606040209100c081b0303070e040501060806130603140115080109120c080f0f040306050708010e19020c06100e150303030c0d0e 79
    0x415544401d40324551a1040b0340d012603a07180c00a0302117900401621000c00d110060300003c0d10039000c40040c040030100451880340c030807070748052800344100600000384070000c0040c004816894003592a20740d00d42040100700d10405a4140c3c0c480506a01180c03110b101d050a045910b20500c1820700d0011480c0030382e000081518800d003266800041009605c1c1d901403d50a42564141c405000d103504155001c1c0c26104000d00b0640140c0d40c1c3d442c540450346e0f040d04130308001c60700101b08042841540d02c40030b01038510b202500084584014002031640814801c1042d0f0390b401c10f00940c01590102c0301220342401b0103a040e50442018813900d88400003820041441e00c0301c00c1c601503941d920b1440c001054910040c884410720078a400100b00551084141c5507000b1742c240e80d075611828046840d00002d0007040d42c44a143d101f039100304801001140f1202c02500c1042c0c004506554984851480390950750b00e117140c02d908144040360146424030007600d1103007800440410100307654504039286c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 124308075 1250 124306825 124306829
    0x19020319060501150c030e060706150305070618030c140607050f06010f171b04021309050405060105060c0307030e0f03060f0a060803160807020f060f0711011106040b06010513 77
    0x1c1ca07582c0d9401000081980b80704074110003024101049054860f44005e0405065040b42500680002884004202296000c01c0f41070107540450514030b510f030300341295035800c14012080424610115080c141200d05907150803283e208149504c4035085c10700b8213510b98a0200703815003181c0c003030000702e00181080c0102a00b0088000051101d5890021682d059818a5209003400610032506040380200403501d126001f903016440d00b400000d01010800a1154107445828821142e10100d090022134100c14002c9016004480340740e42c898003000901d10414144d03c0d1154010801c0c900040d0059160500c1080b008103160801c00b8013001103401d082d8122000e102c111030351000c02c02a8400c0d403240001810421005504101805258a011140a42e000382c00440041914811980c1d0f4903050000b6440241105071250029070b0b450304141c218007011654a0126010000994400d40783d0303603502e2141c80002c181d292155104d107868588060305060400000700104d03d2041444008180 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 124309325 1250 124308075 124308083
    0x80702120c130c02060f27010e070605120f0a0204030b0705120709080a0b1f030c060e010507021309020301090b18011a101101020702040f020a020c1219020319 70
    0x3002014008026100c16840b074401e0764246088480c103940365000500d290f10809242d045c8042e0780300c03452061003d81302ea0400440307100c5c6140403910041010f400030001301c40650122404c7c640c40b90300a882500400350342810640b512000aa01043c11802072038014295850041c9800e80760340315034110031400c842c6180420390006a0312068403491841e43e90054880c030703101e40e415081589540d210f0800d0000031f4802e071202000f0031000707020851a108940c4151411031a2141c0e280f8007512024254031440000c20f248500c180d5a65020b801110045607009100b01e9500c414490b010004003d0710304241c0c0c00d07650380d2182d00000b40030350301c40c540a5504030f07001d0468121400d0311035007501c03500700c4180b00b0080342c03414080058a803080c42611b0109141801c118403e01d201e0040c1c024002c5c0d0300c01a510508101100b42c041c2980d034002c241c0800d1b2607007901d01c08142281030000303451070115104001d030f020782000c1106e401e102d8455500944001d007941c032640310840030341410404041080d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 124310575 1250 124309325 124309333
    0x6030609020f040603110409080c0106140114030c0d091b0311030f070e0f13050319120b0a14010302071416060f09050904031e020615031605040908070212 68
    0x651402d840160a95142110306011103070031599044c42400e910108140115142c4002c4003c10000304143c0300e54a88004c000c1010b5662241201441c9a0108816000c208040303030600c18916074100f200e100740e1050030f5280c604100e08113400c0040408030419107580703001c06e0805c42000c01e001c0880740154080c04902e10040002000c0504000038000c54440e10b62050908012010030310409650141d80e0030a9407940366200c120240c000448400010601c0c0800211402104882e0200c6d8810190310342e035452130b40c00203480c1038040300d925034138450b8000581002084070f00901c0707004082480041c9800b60410302150303a141c08005c203200c003e10080d001403450302642c2c07000000240090502c1d00d41b44000000156001c0c0242c0000c1c01400d000e860b0400024040c91f001c0c15910200910b403030b004e1190b8140806e0001d403034100686442c0d00f0110492a1000c0c0d5140000e801c91800b0184001d0001c124074100410000305440c02c41100d1622041c451140943ea50f0501c40e00f80d001e0b590054 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 124311825 1250 124310575 124310591
    0x1506031008011e060501110622020d03030e0c010815090a060f030312050705040515031308030c03060a050a0f090b0406050411040305060c031b030615030109060e010b03150904030c0501060306 84
    0x3c0c200703850060300a5410800724800142d00b040c00010040e4100600c14001c031805280d42d5555800d14140b008084d4001102050007001c040d416070104103450034490a4410801c0071500440f106030042c4d442c0800c24000da81c020040380350080d6010740200365200f00242d0580c0c0c6c2c070140c400250321039000b6004180e0300c00944d02000e01500550350302918629043d4030b40760402000840c1d0b2003000180e6000c00e80d0220000c0d9125400740e400c0b08900c2c2c0c00541d1280c5900e4208410700441d48100d50703076801048094400515810008240e000390340c0700900d003109160801c880800203082c60501e9030b40c0603807503401c0018140c0380c510940031500400d60782c0715500ca0035414544e00e00900a004001e800400300204010f0515032051088a410302210140d81c94841400213604008190880c10000200000010380c1380306982c40281256031007603440c9640ea983c0c40c00c02013140030071159442900785d130184801103032902440d0035a010b032103810501030244490b03c0342400c5035927903002220032903654001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 124313075 1250 124311825 124311881
    0xf0a05040e0a021302030c0304080a03410105030d050d09020604031202120f09010f0c0c090203090d0203091309140106030501050601090b0a0f0305130803090601030b0f150603100801 80
    0x480c1c4c0364401c0c201c0c1c05525500b407003001590f0a10000303002501ca44004107200c001c040c861742011004100549a800d0075580c075000201c06500c0c55505145801c9141c00c50101c80e03038036410300604a034401400f0b07150031031560714141c410364440c0e0540354440e42d60300701500040e034502d000384c000f840c000c241c00c01d541c401c005c0c4041c0c5000728811002c041d01e80b0511000e11148255002c440c15030381e0038a0320031410a54000f040c2d4204102c50801000035951240100c2e0b04a0310780c3c0038601c030781a8071086801c1496180c0050383c4074851030761a207401000380e05042180c841980c11116106200342c00039291240344a51140c211003041d00300725201d94580f8148104e81d07a000e030f0f246c409402031503860343c944486828007410341003000910800781512000000c81203030000110004064000345842da407403178010603090300c2e880309000440f02d10f04000b020481c00010b4201c0303180f041d80c0c038080b8034140d60a0581007000940000746582c446421501c0080340b42c45080c0290b26105081c8a02120b490001c105 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 124314325 1250 124313075 124313089
    0x90d0b06030f0a0c0618081b1306050604090203040206071403090a0e06060a140c07030f06051b030f0a021b0d090504021305040e01060504021309050105030604110f0a05040e0a02 78
    0x482d034a035500512599010404810070744044901c0d90034a480520120056116144174543c8032180a000301040000350301c0e084404002006c0c82143e1084c00035040c09000c0048924602130340e40c00ca402881b090011304001e85c0215041800181006e0400b505a5100d80d42110b00850f8840f5070782010440b0140c9013084041c4001030003219150035040e10f00080410413038024442d0000802903807000d002d1944600f41d0440b051151403000f0f480700c1c0380e01da003008500c0c41300000d400c03070302c141c6008000303014002c941c5a601c01241c1081030652441c0c840c0c5462405201e00a081d540c4660350800101e0343d103410956100d000883c90002800d40c02c0c84040020301102aa50710640c05280100215040da40b800f11200056030303000c5900085800d10200e10314010413054010343d40051000901226031506603030041c0880d150401c00303000507a211418551590b4096074014448a00c000460a0900d0070546a041c41c84000e00f00786a5155150005010349141c0202c071241d90700712448003419410001 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 124315575 1250 124314325 124314343
    0x60f0c1e250317010504051b07110a17060a02070305070b090709050103060b0112110405040e0c04060602010b150a0203030408031906060302030105100306030b010b0901110102121510020606010311090d0b0603 91
    0xda00f08058903045000c2445c100100c682801c0d018400100001003204001001071400b00103407440b030742103407100042031070101002d42c001e8060dc1107070000743d00c0719600d0007215003050389a582c10f400c1c442030390b903600034050300504032042a0141a0011440b45600d10449000314001e1002050f44016140054204980b0354000300360682031035000d034180c282120440d02107610503071b030024070079180304000b5081805070442254032504211002403019415042809010400c55064001054403240e4008901c81c100c08000903070414400030340405e0700f0700c0245a0100015200317805c7d082c000c01141c0300f02c80c9141c00c41c0010960210040c030640c202a18032042c3e05030039003030400080d811511500031000d4144165000d00200049190459104074500c0d140d000100000f59190302090044110b045c60841c1d0300140074000b003201e40e082d40351000c04200b8410064018000a80ba107000440180c00a101016440001000030301c0c207640340e03092415801c90107403001a003039042480805050400d01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 124316825 1250 124315575 124315579
    0xd0e1f09030e1903140a02100207180c140a020a050105060a05060313080f030115020c010314060f0102070b0708041d040c090b0109090e060f0c1e2503170105 69
    0x300a00000c0d400260024090b101200d0b04003003900b440b52181240081c3c1e42006000c0c2010402000b0121000510281803138402c4400c1115600d591104907a114100d205030b101c1075003404100040c2134159800802d2121040c81e06041b902a00842e11030268081458140103a01c00d1131040140003007880341c0c0780c229108442d840341d19460000002d1080c0005490107084603240300c41102000071440c1101d2014904110841c1c50303696407440401034494074440710015024082180744c0641c2b080c482c3d0051180c41c0542d45e00c15840701c0081c0100c201000f58600d05501c1050000704420310140064a26144940702199885081c0141c1036a9030040c6e00c0103040b0140300ca414480090320a224402c203960464200003003980c06d490040321170181c40d1f407100c0c0c0c00500c0c0104a04040304080f81d00c61080f40b03034980c000381a840f140101050f038455040042d481e44040c00354241102e0504000f008100e2040e01e070310a004900301c0500c07082c1880010214003142c2c83c4c0c0c0700401e142c0030003600c0d68014001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 124318075 1250 124316825 124316831
    0x605060318120405030706080c090d15140708040b041704090b0111030408120706140709031b05030601060f09031406040c0905010e07050304081b0102091305040f0210050d0e1f 77
    0x103000c0c0480e56a4146e80241c07818028000c00240200080d0f4043c0c416a60008040100301101740c204a40612007283c81c00700c165042c000c041141006407503560780540c1455840e140640c0d11030b118440544000b82049543c414218081d101104045c0050005029400400a01c00000304000750100b0705043d074215203038005000c108095400801c031040050003030100141c4c0e810703280c07404200901d4503d00d440c1003d04101e0034048011f034851580001c0d0b074419080c54400307018a00040c021555240f250550551010005002051180c0c130700720000b194a0400d50013107600d9035241c89080c00402550116030f0700400401050002c418102402800450030410155041c14060300105200030500b0040c4500000031408100000080799045031256990b150507410180b1268080d6100b2001e0a100b080c441c8840d205584152007194043c59000440c060a44125420f100083d55400407160600c901800314252008a074001c240e112521480079040c09000b05c10039100b0410802d00482d0610702d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 124319325 1250 124318075 124318079
    0x11011b020d080a020f0312010504050c070c060e0102010b030703050d09050118060813021905012a1707020a0807090c0302040b1b031306030203150301051303030c020106050603181204 80
    0x240c000450003026000b0101d03590f0b855503ca002d0345040404d00321802580303c001071101c1801050303c4004c0c142c0700304031420b2000d9201c2d4a910703491409500c00240c4484c1c0f41c10f104202d5180683c40704168040e040c000031441c0e808140000c1d04200da16801910660040c801c140c10703580e030124482002c1c083c2400c005c4e41c102100f1460100c110f0701c600400c81402207183c04524a11450745903139111903402046d460540ca0381c5401f500125009114442c04240851000e0180081c07c08810903410599070308031204145503102c4511120050320281000c1c00104002c902586402c0c1d4504c0c00ba00c07031a802401e90500e0001034004660106011404040c03040c0710901c0402070703a604813043d0000100c0364860038a90f00240a040d441000104550303015040000220560940c0142d441089100c03465449440384409250903130310122841d00700c05000140b84800280254060726501d5460301c000035909443d0380104800f588107440746052010080715500900ea02048180310041100c6a81c03800c0c64 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 124320575 1250 124319325 124319329
    0x30d020d0e130e010e120a02030a14040503010509330c07030201060b1c060504060f031704030503041206050601030e0618010216030f0f0503041707060b040911011b02 73
    0xe159280030300104120a60588220307a01c0c511185400040600d041060340c04080001d402005907030002800c0d0700a030840c450f000e03041502551101c810301d4000d149401c650610481c2d2200e03c20183c1040d0400500c00811207860074880c02d8803655284000700101800701c2e001c05000403500300e0020b5042c50203a11102140a030290302c07500141090151030700c400c607a15051b40500440d400c0640f800e24080345c0640c0884d004841c0c1969290b41000401c134950701c62040c08240c0d08580641a023031760143c1c0301000081e054000c2e4010600801030f01a041c01d449950703041c1103901a9102c8400701028600035070501c902442540c0c0c005400b42000c00c403c49038a1800d984484008000700305100f01d0141c04114048203404880404c44c459980e140c0a656034a400380607564100d8030ba0000844080400b82e2041c0144e013180d00658000c0d0448040c0c4103600580b0a19074021182101d03090303186c12011449454501614030203505c58210405100f14002c001001c801c2c4008205403681c161581d504007603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 124321825 1250 124320575 124320583
    0x10e0402060909150d1b0e0f0c0c07080a0c06110606030a03050c010e010509031209120f090d1505160504030b24030303040305030f0604050106020c0f0112060f050f030d02 75
    0x10000f0b4900111503901c44480090020042e034103d50403d00c80308030341080020031000007180140d5003d0b10340d8010344600c110f0b00c40c80806c03140c01503803460140114401041c00b40203010042113a07000c03166200d0700c2d03101c00e908144c6c050204032502500c080b02031002c29001802e40203608400c10040c251447c000c1d0001c1da841c4600000a004e00c4000030301080015000e4003c0d001c4240010004d20003402c0003801c1079641e0f80302e030561300c01d05c0c485030003c102c541202150820440d030f200c100160809098079008407030f6a001c1001140d1158450707607064001001d0305480c642c1c400502900241c189060603110300e898480d003200000b004030411040c0000381c4100d41150b0810508094070603120a040c1c1001294207c2000e56a40747c4008000c101c10540c2c0b01d0011803184011250b21203207505e0701414803054540a019040258210900500050400200156584005240041401c54030524200849040b80c00484403071100082c00d00560419451541c10b162098008004201444034000c2d15 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 124323075 1250 124321825 124321837
    0x821010609140f280611011404020a0b0d0f0f020705070f180f0b030718060f030308240909030903010506030705010804170405060307050c2422080406090608010e040206 74
    0x200718480d0401c0c2001d40d84e80003240c101c201c9030003400e07500f5986422000d40740700c0e074030b1401d4003256080c41005036030113542d00c00c3c01e4061540a00890360142c2030010008494008511b41006c0603614040d06501100a0003031b264214500b440059450146091450070b040d0303503030042645980d00d44001c21950700d1803043c2604102c0028000102403105410502c0035003003200420394184900751010482454444c9000390100340e20400f002000d99480d103035a418041440083c000c1845000011640990818074018442900d46010194a4038400098100b00151401c15982e8004200f0200900f401d12499401503402c030002c2500034501400240342080082c8001c0c40400d00c0d0003a900d655601d4016540a8180244029140d2074101c40090680e0041619441d00d803158216040d41c10030a1a0100340d18000b40603c0302d015034540c0012014042a0704103010303031581c041c00e0000462040340c080c0c0040e0525988848a070303850004c00038510903041c2c000b6460309940409100c010380e21a000c9502e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 124324325 1250 124323075 124323079
    0x6070917120f0703020c120c0a0e01060203160201020f1608120906160c090c0507020a09020909040b071808010e010b0306011203030504020105121003020a060302120a05040821010609140f 82
    0x9520304042c9022410107104d0404181c1101100010302039607d80491304070203001c0c0c180c4440303200c2607642801c0302d80710702c0c28455003001d0b030810001c2110800c8114111100e041c010b004035280300101401491425a820b0b50090400403210300900c8a84814000302c4402640300f01c0007410140550300080040c4181e02d0000032140c8035001c404204080c0403810002010b55250410000001034805050742e8402c440807803180c0303000000492201064400d8840c404005403e4800070380e141d66426801c0b00340a0300c1e802c24040301e000d06034024031664041030b000e4000c050011a1203e01c8070200c03804d481c00c226a039480313500308070b00500c019200c400c3c01000507501440c0100302c40c0c903a070005071210310a844802d011148481c0800c8280f04040d049c400c2203d10030346241c2d05503951503c00310b00f2805000d8090309240d0020000c01e2201c01c0c2c540107c2d4220b401044a20310300300000400c4c1015180e00c40210b0201d1401000410078280c0000c9194001c0c4411902c20403584607c1c80007078101180000c40034 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 124325575 1250 124324325 124324327
    0x2010e010e0a260304090c09090504051911100e030709061a0d0f020703180603060f0509060a0e090f010b0102030301270603081804180203190609020306070917120f 72
    0x3d10301402d120000754040380034044e240e035281c40d182400040c00842410001003540000001854030091080511841c1c00c24084d00540344407840c03881c0b130428030403c141c614214102450160ba5940c840d00485a03e054950600100c2010280b6041009070784c400b540d25441c001d400c204980801407900c07801ca1100d1009584d444000d8045001040740c40503100401d03201080000806400c05041100002c2100f4a2550141d4440003113060301c8e124052850348032440d00e0208014148007281c680c00040050244000503201c0c0040b180d00c120032100d076155503100e404c0900c2c0b00070080c41010810102840070314659814102c0150b01680904a680ca4403c4811000704c03003025542c0c414405181d1103c0b1890b40d400070103419000f2055065003041c0b042d4980300504842c499221412070045501902070030105c600076101e03002e0100300500c02c0d00c056440300000380041e6400d00c280751042c041612280c1c5960f0605144102d64101c00b08007441e6603111004440209200d2019908652a81d060007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 124326825 1250 124325575 124325609
    0x605010908060c0f0307090911040e0a0b0a05040f0f092f030c06090d020901080607020c09040c05040203040f0f0b010e07050c0c040e03070c080f011808250b090a02010e010e0a 77
    0x1203c109600d1360001c02d0049c5042e84200d0800c103c0f100500c102da41c45000c0145a031a0b016015048404901c04168051960101042141800d811007480540d1a0000040101c4904460820b80e213056904540001039210030310b403508940c52041139000000da49816080e8141c0c03001c08d40d94426414800e10451000c120a20640d4400307083e01c110b194003600000f844c0d40d540805a2351510155200e03400750042035035800560408411241c880d03908840c1d1098800c0c900028007000390b00240041e10001c180c1c98200d004103450405c182c42c0240705400b145002d601d0103840d0369004070007130001010060104010b030403441000801d4140100100c0d0002458000002c03101c1c0703540729425000303101c00f40980c0c0001b00442d010030341900001042c0001d02400e41031144401ea0f40b1540c003001050b45000b4040341440090b10101142e0f514501740c072040c43e03540310743c0300e2100f031480c1101c40204c031342e000080003011940d2044a54030b610f41c2c2805c2140b140b40d041c01c00144121070501030386070911249514 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 124328075 1250 124326825 124326827
    0x170d080a1a030a03020c01030506010320030406062304060501050405281e1d04030206011802070204090b0403090504020c03121308070f03090b0a2f030d0605010908060c0f0307 77
    0x16000401000508a4143c140203290194944c0c1800c940d00c0d01203482c1800082465000f8025058084030b08c2c201c03d2a1030f40c40b54210880c2c1d4101610a03030b4242d64401e03003c41c00c81e60046050b040d102c6c0090f64100440380c1002004140caa85030091410003805010130091501e81c2e216491a0141100314060004e0a5244204484084d544402c1624402d110018006180e050a6105840115007921420b503161911100d12030702c151001401a440310004100c00b5041da1b08602c404585110054a80501500000c080e605003420941c1c02c0888a4144020140c000440c10002e0506890035401d0855007145180c403130140003200a8480820000140d00807076101c1084006079006407556201c410b58280a85640d6178010101c002c52151500411000c0e806804d9074215881540d070000341212022003031403107000014180c10440360301c980c41d000f00c410600140c4248503030108001826440e00c0001405010341d80d01c12140c0e030b00034005001286042d00c01311920380d0454924240d43e0344500758 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 124329325 1250 124328075 124328111
    0x9160b0d090627050c040902010203030c03090a0b25020d14090d02280e040507061412010303020606031009120e1f17070512010315020c01020d0204170d080a 69
    0x258183d11401d80c90f403007501c1007034020034101424010750460310700214100a12044602d4041c0c06400341c0e0080c00090700002c182401958014000000c0cac9a503144290345c0d4001b4003000740c2d48801e5441008001048800040c0c0c01640d2034203041c80200a51810381c2d102500300800120342c3c40c2d8054001903200f9203519403003100702c04985c2c007030b060281d04203007061151400b54000141441c0c00b54a00c0000032004084925180181d03008805080024035054090300d4075880b0380c1542c02165400d0000401204107003592500a6000760080e00071031810300200750911045005030082035181103501c02c081024201d5144036985242800348008081c40001480c0040356074144941d0103400d4044501c403944140a48a281e0b03080121486607103ca03502074400e4041c51061840c425015001040071504c065052083c034072440c0d50051034010700002646c2640d101d1f4004080071900040c0401400c009007155107012103104000e4890503a00800040c820480940078810303aa0719030903c80e40c0c58032514 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 124330575 1250 124329325 124329341
    0x303050a060b0c010b030c010f0801140a08010504120816120507021c050a1d0d020103050402040b0a03050a05150c0d0e010b12010c14030c040b070c03170309160b0d0906 74
    0x42c4825122024000707014043c10b524413050f4028040d1003944152540901d081940300c04460b02c0e00c0105a0800741a141c0c5403001403441c030b40c0803160f09000200c14400b8450310f806070340a5030407042c2d1100b001c3c05c0640b64800262803030400c541356a11000c0029403050f4000d04151249a004c1030340d880d0320204074a05035110a800c0760241c91400850f4245400100810150300030f5211020454000b0000400783c4044091943d0407045204000c4011b600c260701c210f07849031000b0400103c5003004000304200407000e800850740e59004140007024058208600044000042da05802c40d20b46184064041c1c0a441c0d0394410042c0c4440407558040001e400c100c10702000500324030340d50074210113050b0103048400d0602d8040358030361580c820001203580480c1c2c4201d90000c0e0380e62400703140c1010305846074400103060740e402224050200000d030200402d0303116035410401d100c0c2c5905040000b1800c1c08240004204a2000302008100036a281415611448010003000401441c1030070588081d00d840 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 124331825 1250 124330575 124330589
    0x20c060d110a050a02010b040207110d321b031504050a08030f010603050a0b090705130504110309120901020606121507030c0e030c03030304170c01020301060c021305060109030303050a06 82
    0x10500103140b941c014040c0480d2100caa00030300c10900764400b407200f20701c254ac0000d00202080c440911840c2403603040b01011922801c507502c4050160846848900042c08034200f080345080e01c034900310b440800424014060140001030b2824141c00000d5a8801c00c030144058038100750009000d012051140c501c449030040941c540c1ea142840c0580b500880034042c190110b850240410440351043c80703040c8441d00054100101c0b52500d0006441a4008034800140b5480000000c642d50b21503010b0304d0424122051440e131a07042c43c0d075946090a009081002980d5010f01c40803050f40c1c2d000032003941208080d6514040c010a4404541c00d204580e01460b484054080900c11250ba265014140d5403403c0e80c4e480040d041031204050701c80140c440f03041e616074402e20102c0d0101d64100010301c4200700d500ea4003450480b0781e40340b481c2641c0017680020003040300007000e842581007005a00c1c030f0101d0320400410880c50f02100192103640940070160800da03854001034141c5605130b00420245c08a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 124333075 1250 124331825 124331827
    0x17040f020d06180b0705160b1009240512070302040209010c052d120d02030705070b010e01090501120b04030305090304050a03080301090606020303010503030301030f0501110313020906090601020c060d11 89
    0x1600840c21500e540141224410740d11000200046c1c4610260307080a002082c1b080000c1456498820540c100036041d951465004036000500c414584550090207001c10703284082c04100000c034507018102c40d480f490003082c116001800941000c24a20b003501d9040342d00503114110100102d82c1035606000c0204280300710040442e02c00d0301c40612606c2070040c40c110a106070b02646081d5168854405000c0c1d4481d0b05101070005c9c40003680180da400302003031030f01c1c6080105030380b00c03030440881c21781c40003040d0708200c0018020111b86003d542c1c0500b01d4080c00d154a285c60780e40d0320040101c000e0015081582e61004030b0041c2c802813048800802c0000c1500f902c0c2502c0c1c1c2040c001d01e500070300c12138126074609440007031454004801c0e02d04070b800060145055a00e15181d1041284100e4401c440e155a141c50401c0362030348640145014a064181a0107000072600c1400040d501c0070b010140702d051100c01300101c6a0b40002c0c2002000ccc425510b05490700a2040142d0150030310704466540004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 124334325 1250 124333075 124333091
    0x52701060c05120d02040e090a060b041b03090203030f0a0815030102070c050d061b0e010315031e080c0d05030718051c0f0b0103030e0102101107030815040606030c0201060617040f020d06 82
    0x1c000f44038030b001d5002b01340c01c2210215820070001110310b60300c0c00c07220310009200780d0842c0501950041c4840c0e0f001a0540349450072100c045121640264103e0010401c0324081c02541c0d00c1100429202c02e10950085140c90b40e9510342e54884038281c41600c0c4580317a44e0780ca0307204201054212186086526648000c10141a0b1010380b00100750814103000a151070045805814003500712130450303401c0034a1074400748071401074a0542501da201528080300400c00032a1445d010404501503200ca07a894503200d0420840041c203010703140d564000b840001c0d580c1403107503039100b141102e05e011045891900c0006503240c035480382080d04d14007038601000754000109040d080300c40c003480302e04241d0035218400c5103814100c1c100c408111044900d4902480b804000900070740d4081d0300b000009000d41c0c840e0000b03000160030b5502c03c0e080203002a840340f0300c1c012001d8090180102810700c900f4010411450360111240e01e2500070005001104808a00b2044d5160682c0003d00507800c00c81c1400040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 124335575 1250 124334325 124334341
    0x1603030e030d030515060a140a0309031106040302100507020c0604030c06030509030c0a201e0a150509060708071b08100501050108070f09052701060c05120d02040e 72
    0x3404004055000e030040100891200744a449418070540740d01c4445006044400240001900681101170a1000c02c444101c00008500080e0003c80c17107580c3c012854080720b1400070101245040369900550080e0140030000f500030034803440301c1c0594000003506070ba0f449012450643c01c02c00c22500498001004000e114100301a02c013500d10544050040d03440790300780280c2d40d215448522481c0d400103030ba000001842c3d03201489500e00c04008403c07180005400017804881ca60300380800800b001104000b0506101c0e4501d002010105075024185103910310250992143c414064070030107000511908004096085c2d4150541041c0c0100c280e085c854407c0d00700c00c6088c06201d450f441030040d040f52000c2140900c5045c5c0c0e00c1030f910074a030398644034800d8a51441400008081c05144000850180c6a01c42003446d68003410310118130001c0c0000121032410b2068018800b041000b03c024404900c0005110b20441d0744080d040356541540740d0800001e004580200300040290000e1010031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 124336825 1250 124335575 124335587
    0x4060303030b040605010207030f0b0613052d070e0105130f0b07051b0618041d010209120d08010501050304050709020a0c150603110f04110c060907120302060103110102160303 77
    0x600d0030b03201048130b10f4660005a0799101c03103100003404084605e00240c00140420021904001d01800481c5480b01d505858000d44a0884450480c40c0381c104000d40b0100d982d0442c2d806815180f505580142401c180080c010302440c00440d040c00070000782a41c0c0c600505c201d420003810381c000001c40541d210a032680c084c0c0e126240503a04c500c0f8080c2456a403914049000741d00c41c0c0e005003001d141044000c1c08400040c17040c11510b40c0b0030340d00d15101850351000310031103903940a000001641d401c400b404000c0f07401005404080b2603403004042c1e441040c1c01460f154151142400d00c20f440380c3d40c9103001031904826800c503802c46400400c44141030354215014039080e41c89040100413084120001008803000d600c07018100180340e40a00003142014000c40210341c4004e000032840d21052944141564050003e202056002c5420030020200911040015114120b1600104282a10001d43d02d090601001d07240c1c802168587ea4284c0c0200304500c1c041c0c5403c90302296043d500c1c10050a4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 124338075 1250 124336825 124336841
    0xb0318031b06010f080714091305010e0129030a030e030f0d0f030c02030a020a030323041b0f1401030f06080f0f06090705031b061b030301030302070b03041e03020c0406030303 77
    0x4d007440a03074021640510200703581080d40d0400c4900013126035003c041240d0404040c0c00030701030f89650f81102001c64001c3c02203a40038840c8a00101d42c008051107581c240182e80d904681c07584403011100c040350741c2d000c18800b0302c41c1e4051500751100b842e010000381c24500140d052803418410380d0444a03c850f044a003018001c1c41ca514204540c00000000382d80368481d5800c1500143c2010700748200290099000c014800c004941005818410400c00da102c1407090b5410744504040202c01203404880c008498050302c00340c40300442e4245007640003030504088510140c18903449124003141100380c0c0e4441d200400c0410101e9007a2070107035541c2e988408180c1654410703400703618001500c2e9100001c1000440300090300030f001c00c0b46180340012041c4030240e00c0c664441020402401c0865612810b180c4488101001d5a942e516614000c0d103060055440341d07060072414400c1002140c1c4680300b159081e40c200422580c54595032800301d0800c0c40c20319005a005150400100a059140e808144 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 124339325 1250 124338075 124338089
    0x130906140a0e1002070240020d0e01110301090f020d06091d010b011407080c070314010c0206071b0614090114060d021518030d08040308100b0318031b0601 68
    0x1d42c07450f050034000240d1244100194020000060081c4004804030b801c000c0c082015000c0121000c1c400c03461000040051450142c003500131a00c0303061003070107202d100f0030040750350001c1180705404140032205020511891803985d95810924210b05826012504035040903402005541e85802683c030007021010141c422082032003280d40501c450502c0b40c48107030001612028a141020308844840703a1040a0071240034509008001c6a0a02004084003840c07081c1d06291440943d54a061700712443c11802000310350000d824044029000550b11442d010b03ca0301c108003c2001c0e0500c00d0140c0300d03c480740304401c2c02240c10440088010743c03100201104c03031448610991079400c104464403c402d000a540441c0303001413119881d840c070000f080c0403c600701c403042d80182c031900040d00304481d07060000c010503101d02c100010158007001c01039000000c2e034850f007016410310b07010003414080206200d94620f0032a0604003c20b104006440000b2268030110000c0310700310642c10780b286001c0c49500d03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 124340575 1250 124339325 124339333
    0x304060515040c120f09020d0305041a04060905040b1f030f1103060303090603040f1202010504110607050d03050901020f07050f150c090f010903050a030e1c02130906140a0e 76
    0x1c4185054040c1951512113655a000b42d41c420b00041c1d80180041c3c0c007140c0c051a5124100001038844904203503804d4000e8a4080c0c80314a030400e800b404403052605c002d20140700300020b00205800c100d840e41500c009640004083c0346c000049107040e80d03c0c04d10411085500f401181c1100e030705401081405d403000009024280307440780c4411040c0800d80304580d043e0010311408025060041c080c50707004e070195401100320111a01d5001080903d10a5440141d46401c104828040780c40d15080071050700707039811441c00c00161101901c80901030313400e07010161141d01148880c002501a40c620190100301c503035540f016494000c0e511126407080442d103001d007e0404460351940c0307900912400d030680303240d840c004605080004d00c2600004850501409080200c0465000c0141000041c1310b621401d015500c06410801400d200c12024100c076500880c219005031550340391100000d00481020a100743d85190440240403010b0609001d41000d100f04a683c0a00d9001481d02e0203001c0161 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 124341825 1250 124340575 124340611
    0xb0705070212030d0c090609050105180414070201090b010f03050a02120c030d020307020301050105010810120819020c030601080d051b0a1704090f02070c030201080402040b03240f010f06210203040605 88
    0x542e03200500c1c0c409d250101d0010300c41010060316441d030f2080e030004010000240c00c140c281c520034504006540754070040c0c0d9509003ea08106038038200030b001d012500b4803001c4203032561b61050354407410020000d0140c10000031440c0b03520000c000b402e112500080656400c3c0c488103000968a40041000b41d01c2907003084000192540106111806140e00b680d1204806041401d810968071401601700ea8480c1c00b00716040110706020090b4a414800d9800350844c045040209460001c06030495400e0750003944c240c1d141980c21000300e8510080c2400c00c000c0c18061640784034205508594040c21003250302c0c60180f21980c1c0c0000510551700c000008002429402c05ca070400c07400380c0f400c010010704110700c051025601640706180d006200401c0454543d02e501c0110b030802014501110900581988105000703d01211440d4020301c00d80c401e4187d5072602500380000129845000d090003c01c0d08c05011500d84112039441805c5110401c0d03541e82010325011000b050100d980c184110400c0e040 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 124343075 1250 124341825 124341827
    0x605070501061d06010c11060d0203061f08061014030a092114030a2003010807090b060406030c02031e09010f020109150216052b05070b0705070212030d0c0906 70
    0x40c0d8010385042c00003d4559946140055a04e180101300582d1051075003402c50700d0740d40d55200105400740c68900090f889040c0f4005018212403e48010300c7c1d40040c40c4503c005075513001c0d40b00b5900c10021101000001e2003607c040d10040210120500505400820000d03001174503000f8003201846042d0521550241c1031611440c0c20388008410000f5155440f844100000350024540000746440001040404000ca0040f1032018030840300d20580d020004118000091040300010025207034140144003402e000905030342700d0390040d0410725640e910f207000ca00b4800c00980c1c243e0030260403a4400505180101d07540d40c1c10182c0514000741484282e404110b1043c01440407203540700c0c0c0c2d28240e4141400621010350800050400080a611a0680442d400308030031000c0c2c000030102800d0600700548038100314a04103c000701808000c100010000302c9900d81154000130718a04280c8505140c800200c00d543c0c07038528100c0500c004100d12076060307020344c05541d50801c0d40d150054440c0d43da04c4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 124344325 1250 124343075 124343099
    0x115081e01030201080414160609080d0509040f0b0d08090328060c021006030f020f06090a0b1e190206060a06021005060402040807030c03030e0301050c0301060e0a03060501060507050106 82
    0x61104000c0544000410055001d0960660014454007885031180c9034081050b02d8103440742110001c0c0c0040d908108081c50300041510050705262010305122183c1e0400900b0a21618034038078051941ca510b1403800800e0f0398804110303035900500c5040e0012003814032040540000b600c0030321a00900030f90414600d050324901c980803401a0b428859002c468403100011b081c2000300d18154040c0e50007850b031b200d40910910029512410100107144014010b0010101d0ba00c12154000c0b142007141c0e40250341c0e0710051a040b1003114100d56603400b07030f0f802800300c40c115010031140701110104000b050840031800d041c80c3c4982c81d03800c4907444e41c1c81c4003c0003481d420714403910025801039023000e4207001d12900f100e903002802034000b5280507550141940381c802250300a80d00b210004805104050340b0454074162070303404500a0202c2e090030b0102440130300c0188582c40a000d18804410701644032205201c000f55080030040106d9a0b480300058640c0e032189404403074552a10501141d1049801 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 124345575 1250 124344325 124344361
    0x40b070b060103091e1106030702010608011d031b0a1b060807020105060603180703080d0e0610060f0c02040e1f0e0313051c060f06180b1003150509011508 68
    0x175a00c0003403c481c1400c0361088801800c0296242e03c0c82c804030301c41d40c0c1c40c1d80c030041d030240b0308a0740000340a40c07514108600711803500078441d010881c0d0071f50040d5801000415140e0034500348c0d60b0b03070524000c4502001d140c8081c0c070304004c00042c038150703001b0b1440d200c41441500b10b44160700c2d03030140742e6a440b604900301c82080f10130315800340050000c03030302c40b25610f10420101c45101c402c03100c5482d1203454141c0300740c11032240c014040b500c031a120a40034105000c40d0b60040c010b840302c105054184440902500c0c035210300d010401001040307240c10340d03546400c41c0d250754100d10191950020110482200340140400c02180c55041c144104010b0900004030f400f80c265100e001a58941010708114504101000400c03042c0e564101c50300c081403a0344a400314003100d409000815501d0104c8440315016074050390140c00349130400e501450388030f070003074180e40002034900010001050052060b21161640095410074a907600200c0d4590500d0b0704903c0d8005c168840b001c40d070342c1d8100c00f030615807011 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 124346825 1250 124345575 124345583
    0xc05040f03051608011e050705090d050f19150f1811030d09031106031302030f010903090b12060f0a09090c050a08011506030207060207060e0c09090303070e011d0303040b070b06010309 81
    0x101030880f200c1100394401f40c0c12034030074980145070040201c005020744106480546050f00182e442c60034000b41040794681d2003d2910304040742c960a5160039102c08100e0f0094601c2030b0715603c1c902e04406040d4000030710021100700f20500c10701b55041500040003814030302d80c060f1180701d0010342c2c200d0055444904590344030102e42c2030950f1640910100742c002824050540710f101030f0000043c0c0e410300680d41507a0444000050901d16820024030b800046d03403040074494000c1110444008482c10020340c0030b4400c2d200741444464500c0403e03201e80b95503100b4003150345842d484030b0410883c2c00c0302c401103a00c21101c0700c08098580d10854201d031400a008000d00107030580070091180240c016046944c01902c0050800c0c119440c0d50098440d000d00042594100e007105041304d14051074a0340d080441080110304601c1c107040c001d40700c4040311100505100320000104650086403840b031084200180680ea161035551010014542211408407050310074400090a654231a10583e402e036600 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 124348075 1250 124346825 124346861
    0x32f12040810020d060e0408030a0605011e0c0323040503010501080321070504090606120e06040b0105010e12070b19020a02010c060e340801090c0303030c05040f0305160801 76
    0x300b07000c05009602c000041c00015840319000610b500040d00910302c07690040c1046c959919200f5128402c640c15130b00041c0c14420418038280c001440c912003d11500c1203070030708911034840d40c2001c0d034079221180c2d25000884200c040702540c4500c00c9000d0800c0356070a60081c4481d03603e40c00340a0720380c0100c0100c1c0b24409000d01151806081c280e0009803c07141d80d0402901d000d0712045105d055900940140c800700d51038100c0d8000b400624030481ca11480311030003a00130760501c3d50300c4018150041c0b0880e8104640c01c1441c030744643e50344401c0221820207408448105d1340d40e4060031031039080702c07140001d00000c160000300740c140080b440920803070381692032121030702d10760b9a840001c08a508100e0f01c148181140c02c0114806884804819001d8090b8031000b4004641c03a0080c01c2c0d69134009690903414000c0d0840014110850441176903810b00300440c1203101d0f800101c80b64011341d4001000d200c0301450000501c5004070703458103070b0709611910300240c41c3c07500c20050076502c07102c07801100080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 124349325 1250 124348075 124348093
    0x6060708130b0c03030114011106070e030c040204090c1b03090e040f02060a03051009150e060409241109030d030903030b030a140d0c08070f032f120408 67
    0x20500030705032a81c00c11009400107442d0304102d038280d0003450741504070798030002c014009409580c00e456903c80c800d01c3d140c0d8044a85261650725414068400d205000072045e401c18a60b078140204100d15001410841d12a559440c14801522421007402c01003086070f44d0500f503000a81c550b00440da0f415460300b03c0b03e18602000600c18110090043e1241a40b841c6080300680d0358400500c3c00008c00e980200b814142007031813000100311940281e1340c41d03180001c80100520415000821a421a41004400d990781d50205018007021000106000707000840c0c60038188454180e00c808075241401000b0b20900f102d0307030003190703c240300300c00e80c0c5680542150b842551003038002c0d1280522924020880340000400300345030443d00351781115140c03c41e007a0038020307a1b400c106150011805242568900105858000451245502c00380140c80124019001d260088004101042c404e103155926030204480070b00c6041c1e051103845041e400388800403410901c80c642914142c9213020040d04140d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 124350575 1250 124349325 124349333
    0x6020c031b01020313090510080c0102071208040503010e03031e0105010917010e030309011d010b0907052104030302190201050402011e120501030503130e040308180c03060405100b0603060607 84
    0x940c0c0711940d811480104054a0143c6100e59020004c0540700404155400d00c0c0d1698010144035030400441c5912410084400d603a0024446040307404450407d4045840780c14805460320441e004140c1660900804102003c8000020f51144400706118400d6182c10b036060a4044070070f20826000030010082400310708402100103008000300c400019030314000044c0c00d41507410842d40200030340d558804410000a4010405072400c8500c0020803009c401d03c4000b03285044090b0450041000100f0307170715800b51120030100809600d00c83d1502143c82c0130724004000e036008803452809504851482440d40b8014007545010b194140c41c1c1c00440308c0c83c0c10b40d000350030306d03007803201802c000c0070307101010701c0020500c1440d01850007100503580d944116800c20580d80d07000e07400391134201d980c5810000480d5000140603080b600242d800401c2d42c18003a0725516050880c000c80d54107004090502040040c0000c04010b00301c0d040f141404010800c4c4c041040c0c500089840035040075082081000107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 124351825 1250 124350575 124350613
    0x40f03080702030d050f090d1817030412080d1103090a1716080306190608011a190903050f15150a080a03032003090318040f090b01050a06020c03 64
    0x5a81d4030490f4104651092404155101a11042000d010940c18080c03030442c24400003600c5411403c1c1000054400b041704000440c0c10320030940140081303008070340d9064040c000c46004000c2090441550b080c582480780d4907520240741c2282c240d05c4c102c07136140c1940500303050300d03c544d0035400500804400380c0c035624600c01444d80304004158080007241c0304410050035000846029007901d03502da20701a402d2120004418148040030751818404001c0180d0002016054a409400c2c071400e8842910740b82000d40900840000001b80303040d41c50829170f5000241c582268001c02c03c40d54550130b030701e140315103401102412441d21120040003c001d03124511240c50303020740c041c00c0909801d0723035142c1041c10580c0c4a1002c900007a101c0380d0a440040780d03107805c0f1054004400c030707481c0f450070451000d030354070320075030b8901e10441400d4482c441c6180c0c0c841c0d0111200b9074403c802409180000c1c0340246001d41c09008061050301d081768045901440091210803094002c0c0003403500c140190f22200d90 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 124353075 1250 124351825 124351831
    0x30608100f02090a08060604050f090a080906070b2d01050a140d0812180111040302010f140307030c08010b0f030f040f17090f09190f060b130617040f0308 68
    0xa259003c02003d08513442d00c840b1100140300c82e0001d007605040403020031041e2000a40000c900380300307001c02d02c400e0710342c08569114800c3d0b20494181e03450a503d0f020807218094044040c001201140c01c100d04240c0300c10b030000410140000302d55190700e80b00c00b00f00d80d0703680a001c4c240d08174031040c80038007560a17107100200b0202e80c02415055441d01c2c0750748000c915803214100480025010301840f510101d02000540e2004d0703144001d00c600d8200841c050034500451102904024024032000342e00350240f01c004c8480044541c40c10364038605032001901400454103100d000503d02c4000241d01c004d400d041d141e8030341d100c0301c8092542c0c5402050302280705010f04140c1785051114124070006015200115000301e1618000341c407240074404001c04139400c1c2100500401518007044441045618075001c18040c4e0f03100081c0c00d60b00c03070100900626064200d00c2c142c04000451700d0044500d4488001254401e1340c40d10400100c4200c9002c052034141c4008051103090003030040024007030b45c001c80c2c1c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 124354325 1250 124353075 124353101
    0x302250504180b0112080306090a090b0411010215090c010c020a080a11090a0e0a02210708070e090715050706181103010b0d0b010e04020f03060a1b03060810 69
    0x410a9155400103040752464007150191040b9508042c00308080c1c0403265004181c0e0264008000080d40c542c110180310041006201d10186000100011910f030b00c0700f40584e070440050401d6151034500418001d22a0780075501510403108049808856001d49620806002004c1d10500700b140b40150780080800201300d030b11044000f00032840410410508188500840c2c00c282449510b005100050380007402c50a0890306000c0c155a03c0103000607420701d601e9040da9088400314040200c0c45c100c900b10384555041d4041e035130000801d00000240a025960301e1074811203a6110007071940d0b6260001d11656503211503128000d00042d0144018001d15070141d01c009c0350000100d401c1c4103014070300c854101d0b001c0011100702c1086080074800c8082c044420b681c40310f8140c0f02519803002000d014440c991311807000303800080031911041d04200c1015030140840d0002d0030003414041c080d0404004080c01da032102c1d038555050790700c28042d0f0001c45070300e20094800141400280c0c000781c00102a000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 124355575 1250 124354325 124354393
    0x10020c1504020406080f2a01020a11030709020703031b0906120213090903110601140d060b04020c0111070b0606130603020d0e07080a1b08030a051b1515010c0302 71
    0x1840600c1801080014a04e1070090602c580708070003540308030211f0138604654401c1c806a4848241d0300002c41915035500304c0c042e240080f0911002a24144c0c05030864940c50740080360410401d81c06410411514001140c030b4002d00412140440c0c045005100c1e035000200f0f04407241410a2650b0700030b008070307c005100001d94984544242c41076400f00c00c0f040300028034041c1003180301001400b80d507024107a40d084107130400907018000f41404091030720282080e035545503a40b286030707070343e9048452401541e4024409900d0300c1d0346001c115004503001351040d02c1241300103400b0340b420408850000d910f06810300202030a101d41100250480455047c20b1030f41d8070101130284504101d05c0c001400c048004003210300c4c40340742000b0380080c210603940c0300e4030140d8000e100e01c0310003009a07100d400a518003180c07211403110b4828041080c812130100d29004071040c2d82800c050445416215480080400c4000300080f001150344403000350000e00180c101110444000040390030010f880f00050403a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 124356825 1250 124355575 124355579
    0x325020a0308030402101d040c0201021306170a02030115050306030109021203030106030c2d0c0b0f160810060e1201050a050a0c210209010c050610030510020c1504020406 75
    0x214400680c2504260380200010040004602e4a02903039031a0424910380b403c00d003000351043c0d810500714480c0d924412034403521115203840c402d605031025003d60001001102c0d40c1d0f14030150071840e80044000d030541c070400000b5050002c600889040b01c212529007481101c808804a070690005881950b155403112907000c00360b540d000490400300c9a100c0a151740754503054000d0112403000d074200b810700a0180e008903800d0100382481c01401c030048240d170350744240720384200c1e42c0042e01c0380010308c450070310400e1043c0c0e0019281c0381e511505c0c0c09408002410103014084e81c90a0084928814070f00351382c070f814070034103104500480c44844042d2159030001c0758401002d096a0003140d032059429624002c02c1403034400750013550803608090a113455080310000410740660002001d01450321b400042000031079101d4110041016000b03000e591050034580100240080315100548480c803421030350b4090324081c0d10803034987e1190382004004100c855031191803011002401030768416611a00 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 124358075 1250 124356825 124356829
    0x3030c040b031806070f0f02160512120703020c0406140607061e090803060f01090302030303010b0a020a0804090f0b01080c04031401020c03030717012301050903011e090b06030a05032502 82
    0x1c4140038a45075146c0001c042403c400050100703a941c00c450003190b000740b44000825100070444030aa5006440c5800c0c50307060110300c1854407020b0045101104400203890703060603404103911240ca90100c9081c0043c075a5101100c0118080708102588031004100150000c2e09941c4998455801d214990302517420540582003183e1003024265202c00000042100d01d14020781d4801914600f4201814261b0070342d00466030301d000501824640584c00100199820f008100e40d0300764035804030f15290b4454454580300042c00391103800c00c0704135060402c082020b601510060303104a60a046280c141442c40d01d68000101d400d040055013958208001d80c00a4018401103120380034035100c80e0300da884240101342c216081680300c1140c0c903100690403141c09003035045844540400b403070020744491104000078014901e02d1000010010000003194180c00941c00030310055019904507076540da18001456102d012642000713146c2c1e00208191002c0d00320300c0c51117204c4e0500c440f00a901c00b0881d640 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 124359325 1250 124358075 124358083
    0x309020307120614011a07030c0f031d03060613150504020310060f02120a0f050d0e010605010f09080d081e090615040911010807020a061a0102070803030c040b0318 72
    0x801c05861000624501c140803090041c4d106062480344048507661410042190b04001c0c01036882a0720f000042c1001410711070410b080020380c000c0e00726901c4203054640503107844620320410007546276110003124140b9011901c01c1c8258009003090703500e84841d15030782d4010403021070710030441484886c0119054407244080d512900402005103107440c18041c000c1e140749820142c044c110b42c03002c4a014400803074881070b901003502906004480300304a542c103980d58042c0040121a080c580400b4000d482415080f070000c44500b82c0f501e0200091545003125501a035004903e42039215070010000c403441031034010f500a41403044424851000c504a4403c29010341e001c161551040f0140904803500c42041038004004560805c02c01449a039018040705640c0c4005040c0403007900000e1000e4000d01c4004007031684000200700408480800c40d001c9102074030000d006110382c000202c2c40340d400008403805142801c4e00301d4285464030615541d203620041150020304a645e050800440b4108 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 124360575 1250 124359325 124359329
    0x803030a09060e0a0c0302100507050f070f0605070201050f03130804060203130b09030a0605040237060504030b220611120912041233111801030c0309020307 69
    0x3800030603030030362908100055845061180c4110740040710340c0c0e00000e800851810490364161201003220707a07204810358480c0101140684140079012041d01c0340703080803810200382c0303101001c44d40425881c1c030307801c4503e03000c0d009000b80881c004000c0c2c04081441e200242d644001c400300070f91603400315030340c80709400d4006511850241c0d1001c1421603c8400d20f00c0e080014007c0e03082c04a0400400a0010b1f9856060960281455136914049001d40d03d4024100c801d05503d0201081020807028442c10101200c0c0c4447c6541500b0400120f00148034000b00e808a07504020130b944c29855141c44866090007492219100a40340034050780040e00d030f4050703011041c0c40c1d1a002e03520b42a0744d20324040a410010901e0000c2d81240c51142c0c3c02101010985068070f29003c90400504418900481d81c44100c50b82100944a02ca50f5041c3d800350702c5001044900d0201000d200710406d00c1e1030720086001300c1d4418161030316006658a12548a80d00820300344100d8030300400d40769040e401290030b000480d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 124361825 1250 124360575 124360591
    0x2120a0228061e030504032706120b03030a1404051003020d0c1403070320030c0403030f0206040b040f0503120108010501080c090c0906160b0f0f130327080303 70
    0x2601c00d000e0407103003411890000b4261814010040712848400c002500000d600341c3d03051507a42e2011405051081e800c41002c044402a031800140c0c8841100400918520540c030000b00d501c600480f03400322500401c1ea04000c09070065081c45440b06013950403428200200c108038005200c0001c1c550f9541b090341005400c59240140e8801c04508650151540100402c1c1400030220506e4030f8110a01c086075402440c9240004285103040345464001620500d8490340780c40110038422807001c0ca0008008482c401d0f1182c00041c4264030b8240c0e10b5480c1105e000d445240030400003000b0500da804e10b0000144500181d0303103401c1d191038101030031034401e800500d401d079503600052100c00001c2090a815139021908040750f86040400702c0300300d00c20900c245005840100305103002c5007000c60703c400d200d0340c0000103401618140306488030b0344008403800d48044e120074010650144152407103504441d019528030b5184c40440304000c2011982c0140c07509416090350000543c041d0920185001e2003403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 124363075 1250 124361825 124361869
    0x20f01020a0f110f0d0e0a08030f0904060e1b07141c092709060b090a0c03060506090102030d05060a080d05070b0c0a120c030b0409060b0306160c02120a02 68
    0xb11a40041800c000d4040080003503110102c500301201000075014030301602e03483d140d4503d0079190082901e03815198031007400c0348404140f241c8100740010180031444400c0c1c500304401581d400b1143c65208054907a01c1906510040900000440000030414103000e44030380c14119070a501081c0c0b5141104495280c50790f150300340070041c5503200500782c00038065185281d0100ea4000740d0071044071021881505000da80d580f0000800c007103a0842804104020840000d600d41282c00101820300301650f40d0020789000b0b4007144514040c000e44a1390041a030041d410903110780c14110003814007800c0715a001510050008088400b0030180f100100c3e40d680316510b8001c0b6143c4030f1550f284c080d251580b1502c060060003100360344044406107645440e80c020490344400501074004140c0c80b002030360060304029546052290981062490141c243c0c210303a016030343d01107480500304402e0100c9000030740010050303015142041c4180700d105800c3c0145c8491035207541c00141e01b808004195000014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 124364325 1250 124363075 124363097
    0x80f0c01050108032a0a080301060f0f03060605040b07030905060d0f0b0f030606010507080403050d0806030c0102070303021209030f0109060b01110d020c13020d06240201111603020f01020a 83
    0x6000e0044900600c010320040d814901c10503a010064020b01111650310602d4920360000030008224200c3c0450308044020303642d503101d03c401408048203291620104006042c04400f061091041e031084400d61b6840d907003000c3c140001d0300c00366400071005808001103c00003194666a40c0300502e1310748214200051030821101600e07064410144c60f142c451a5880d0214045031130100304950b002d582440c0c403c1e900c80d040d1070201943e0003643c20107401ca2003181205c02c0c42541141243c1e010318030807411180000c1d007460049960b2082c60000074016008041d0038540543c01d000500403007440241034800aa0310709100340d003111641c520540d002c80d142c184104040d604030b03139445001c40005006d008402c1c40c004001e55076405404001340101d504045c2001c1c2000b659043e00c54600d0010350a01400d6983c201040048001c4420a03040142ca100482c007041c0c014400c041131089001c1d00107060111500c0030301040e030340500c03060741507010341100651025420310040c64034060648568540781 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 124365575 1250 124364325 124364347
    0x303090a09020d1a150c160311010801290f0c010f060302090f1e13020904050f0706030e070302100201090b1003120e01120b0406080304091e02070c1809080f 69
    0x307640010304921841034203000701302035100c036041201c0a0440021403a911241302c03484514110105000e08000034000c0d03004000c011150905a044003c01d913250310060741c8a09418044c807030428000291800c1c4500315940c7c85506d00b01400a46001419072030410200230403485c22b40b4011103602c08003543d186070038021032420740c01e06500701138050451b0f0118a00000c0c00400ca007903144401d030070380d180f680015030115003541c2c1c5100280e901900d8119241450700c0d02d50f80c0c544280a4800c9103000b107007800f04d8500e200c1d102d84181c1003000d4000308111483c54080c0440200c0c1d150000085540b201141004a203440394910700030309290780490b50360307491401c20900d0207421400030410000ca68500040d241c0c1c4c00701c402060020f1104c00064600607075400070303004000350740c401c080501000c1800190342660b68005501d00c2105084014500c600c0210a000c0344682e0400170f004100540d030a01c03d1700c600300d40591101900d034400103868151900c47c1e001903041121205d10004000030b14440701 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 124366825 1250 124365575 124365581
    0xf0e0108010b0a0306150b0a0c02100305060f060306120313031202070b12060a030b0112110916050307030f05010b091002010903050f18041107030813051005060303090a09020d 77
    0x10100c010003000015115030001e0a18800342c8400f4200b030ba250002d02c01c2030011142401c0c001e2210702c3c2c04691700c04d0348110190003024a850240d2084900d0303a01000e509009000c0e591280030001d041d84145941c2c0400c00c44290400b400e1a40c008041322060450b403102040149805074000e11030041a13443c5113484403584000c0100d41085402100082108803900700c19189000c445540c1c00c2c00c5940c510002c41c010400c00d501c003402c46400c0c507000140d8941c58500c060400d90140d0060341101a000040c800128000d9540801c14070140c02d00a06c1180302e00d001e90740100e924580460405242521030341556420b07000390301c41c1c0f07400045000b41880c08600d090071180075070009000c0300406803805800750042a1301ea0040e40d03000105c5800342d254002452400140042c010420381c1c400c107a8000d42e64110b090300328042a5040049020283c3ca501c514845540c013000a105900c00d001500c409018060036840c1c06100038040d02c1d441da620450108060a07001100585880240802c481a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 124368075 1250 124366825 124366829
    0x90506030d111216050604030905040f020309030703080402030f0106061206060318020f0f0a09061505040806070f0c020607030c1b032003073605070f0c020a0f0f0e01 73
    0x2409000d0104198031200800c02ca00704080704041592905060004135501410480c8002c040d402081c041004242d00540400103803401074404100c218040d4940700200e20095850004540c0305100301c10009104240c480d62041c4090151078078170f200c801c20107080d201d0380d8000c000030900c110340620000d0924405c0500800e00c3c1c0c6002e01221500b06a00c445242c07200038007078014072048604001d03944440a40b00c17032000b03015141d19059685c60010308000d2216008030b82c0c95915503c4259174903841407040ea41990400d1000e0300e400d0f103c001064a90000c0c0c20104801d0200410740440965620300c09411850b02036140c4580c9880c551808610103007a0600b491980c10103c01c003030001c43c2c4c254030000658001d0020030350340c594605002928010055100e00016591106984070090300060040490ac0d94100408038042d400c080540a8481c1250b06400181c43d8400507160244140900c000c031500103425995040e80f40d002c0e0447d44440780d00b01000700300008104104c039000003221140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 124369325 1250 124368075 124368077
    0x7030b01020115051804081308030306031009080d0506030703020d050105041101020d020a0807110901060207090b01030b1e1807020f16030b01270213030b0622020a020f010501090506030d 82
    0x961810600016150199070010405d520030040c000350412810360219401003e407907010009007691289110780c1c82d4811541c0c240a4022621001220181406541e4800354440c8086092040a0000c3d200a06e401000b065052090000010141e2100020300000354010400850b03a4501402d01c02c810000d046011411944580308000080398040750062006a003c55100c0d559001c909112003035650311070010f40d114051000000302c1640000d0b02c074089603010142484400050f00065048501c2c03101c0c2c00f6008400c030300e5150843d042c40f441c1007c1c08140288200004d801c4807001900b00c2d4012900d0348090391010402d810524010411000591885a107042036a0f041da501d0040081040c401c2c03510740b5120222000b10380458048605101422103000c540380d40b9034200c1d204000703009100544250404c400801c865003813000f6091244c00d80b0481400f4850072074034145c0001e6001280080c21400f40d4003002000d441c0030300030640213164020001ca228104082054108520029984 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 124370575 1250 124369325 124369361
    0x60e0a0302070b0c030d051e0c040503030306010c03050c0a06020d060e01050609011803151b1e140f03090d0215090613080c1f0b10090b0307090e07030b010201 70
    0x2400664000b408005032a0501007042c3c65451103050207156000c0d480092403d541000c040146010021807040240c51b1110303850074007034444825540f03091003107018280e0503800030000180c6a50151850300b411a1003842d20a1501c0e1902d000d072410884145801c036021034000a2008540700c03540a04000b41003680e620880d90351408002403403d114034200f850500803905020318101508801c400c000f543c00031413000b6142c0c0c1505d10440203001c0c500514a407003000301d940441c56031003100074103001084c454514114038443c00065400000808400301e442c80100607040209140c0d001440c01410b400c0001d002401407410080d0900c00100000520201030b40c1c10010011400100e464024100e000e16000c410314a04000300b880c450b24181c03459178461500c420310070103000442c40e1030000030003204000d0350301100304000f0403010f0326146000141100310140303e2004080002c5400c288217040040703100703a07503c03010000804201c3e04003010130303901c034221048c0d56028092103003130f03800c004140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 124371825 1250 124370575 124370593
    0x10924020c0109050108042a030f02091b0702040504081308160b03070c0b070909091514010b121503070315141b0a020c19050102120f0f070305090418060e 68
    0xc02c6e410005001408005941c0019084401806c2901d00c4d11441407144460385d5842e0f00300715100e449003400481c040c03d04580001c000096084224417004100f0701b1203031030180030340c080001800700a0410b4030450b074100015242c680324491030400030044180509030f1070101800c5042001441c0e80035200b0b00a041040208079940300c00c100880690000c0c0000312a100c1803000c452082854102c424410300d8a1108000d014903071217094100601440240f1030f00c980c40d002417036040020b11481040c00020712012012030031458070b0561081c03854900c403000359442c2c00060704c0d00034164000c0d41c400c0c8100085d0f507000d50310303400f511070100d6003280074060303604000750f60317100d8401000c039403150100000c07444180c0386200303004441c409c1c40014100c3c8644154074414845a9850f4800c3c1e0707002d44103c1c819150507171042c2c2d081c0c46551b29941070b514101445414041c51941c0101400c03802c103c2d00b04400402e603540d074412050071f040351103040c156514291508008444039115402c1c0c1641c044200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 124373075 1250 124371825 124371827
    0xf0302031b0d0201050f0d05100905091506101403010618090606050a03050712060305010b010f0c152d02190203070b0402131d030306100f080103020609010924020c01090501 76
    0xd42d4441035082c03804a0741d4180c00c2a0502644c000d189101c16171906101c184944800c00c54054800d44084510130012511200c803c165a5040005106044891480080c0c4d1610b00000b17201c1c00c0380c8045c24068061241034200c7c400c1503200746c201c03801080180401160f100013202081d405000b44180c100304107801c08d50090103d000b03000a100c10507031920005203829104403011807881452010510200d0b8036450800d0292403015002d50024941c4200d0000b41d600ca48099400355410040c078400c045501c0b40d031000a403861a441c03034844050352445140c0240304040310490200001030042e2294040d20030f4010100c41800164210b600a12140000c0350b2588002ca4200d58115040511400c11461003030160035080054075014810356960f031200e080c0032000318400d540031500c00203407059042e01a9110b5003045850030001e5003d00c018001400d0200041007600c805040c441b0700b0594a103900200f980300c1d40c7c3c0c2140800701000c3c0030002c05404001c0e10070400030900f090384c101414180 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 124374325 1250 124373075 124373089
    0x2a111527210a0905130f1b0801030f0503120f1608040221070b0a030e010f11040e0702032512110d05030a020702060403030207030b090105060603070f1205010f0302031b 74
    0x20700119000c4005140741e0554000c802c4a4014a00130307010100c0114404000e80007881c0c02c2070100c480d913040c030700200540d84002154103c42001600e070409541d0840d15041c138a51002c4000f10307002d100400c400b600d000103803c0d110748501488140389040d032a000300031f8440707046070f43c1200043c000244c05020040c0d55840241072444014406007442e61100d614541c40c01000394010b0204030340c0090340c810140c1d8950000c02d0020071400c0240180542c201c040c0d81100d9502103003420300302c8280020300805000c944406d4014010b0b03c100da0400702000240003003c0100c040060f41e2543c60b1810700100142e13107600800d00d2641d400d00e1603501d00203803042074441c3e100e00c01000801c40700100203015115158152103d4503009001030703884039100d00d00030b07584004501003591484403140014450fa6014000c0340d00c64440a0f1001d130458481c20000c2c4c03000910240c3c03c03014000880e0112a070782e000b9101d050700808070303112000d014038594010316041a030780c2a011040c00108078100140350311600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 124375575 1250 124374325 124374373
    0xc0e0c0d0b010c1a091204082b0e1005041805040b0f070504140303070b0109021b010b010504060c03032306150c0a020918030d050106032a111527 64
    0x420000d00595512111710304040a10180c101404004107000c00e52920000300c50701e90305002c414a0325401300c0d01010340b80104c11046400c000a4441d007403480c2034107100704c3c083c08a150381d04159082603143c0d5603131902c1e02e84661088040580e60010070081c4000c01903550380200d4604a100480d00700707010010098800e901803d00c100380080e42040715034404008039130407240c20010400a950f12424010b000e503001c0b2041088164801000121501045c0b26000040300e05840307080c1f80034506801034650307040c60201038040c1640d83c50701c3d800c140551200003421424004101d00307140b501d9002c1088440f040e01c001c10802405103c5a00d40d000300050900c0d01c6170b01101c200c14180c0d20503090300c05030514609400d4003404040b60080c21080a904103034140c030340b9074905105180d86640250700941101c00041c031070f10b000d4000500220300400c1d0301032462000c103040e02c0b03410700c2000d003581070120180d13810828020740b242c05031200b08410200720009501c601c0074100542070044140a450900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 124376825 1250 124375575 124375613
    0xf180b0402100203040810060503060c030915060402251b0e060909010b0607050f070522050601030b100c0c0512030a030c020a0f05030306100306060c0305070c0e0c0d0b010c 76
    0xc902c2215128001c10a1750b0003049000111401034505040c050098001840388600030b105980201d08000e40c0601503038031825a2100610855190300c600c0381c07182101030325190f0055070821404d0036008507088910060601224401c00101c50744c13070428060101c4203001c004080c541d070070134001050f00072034484d00801d0441e80020345459000d513240c01070407008000c0d580014001089020000f000c80c6410402280d6420b8480041d514018440d82722104110b07007811010b404410240e02c04554056600302106240005040740031501282c41c1d0714900280c0c002244440b0746a030100710300650050040d02d0309a4030192340f0a1005041a038078024213050009043d241c0d20b900c8081d80c42005501c9042d0b0300b00b1175120b220102800e00603200e600660b10a40070307145080c405000e081c0a03000344070894030140d4400100300710b07030f850885094000280c2101c03a683c8216000070700983d5140c1190141c00c681c0655a40c2d803805103c610112010745a40c5810701c14820b550307102080e880d040e030f50681060 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 124378075 1250 124376825 124376839
    0xf0501030f0605090f0114010201020703080a1805060a0f0b030114014a060a030c060c06090506090303061306050306040308060d060e0d09060306081905030f07060f180b0402 76
    0x307603094080c05950700880e82101125040100c90342e454003a150407585802d4080000050301c1004a00780c0c840c001000e40444e0460002c510b414103698000d43c42c5507044410306c102070607159107460030950705541c40c4012a45a2601002035070641c49483c0c10b0030003c90080021800202d413803840124140710740310101200310001002035405d03245c00000c100a094418104100114134503820110445080c0d1002e10590002000b5007040007000081c4c0781c02510515520f40fa00804071020b04600000300c9855480d10a400c001030700400110313000b900410040e6450380703403140c01e1003009501500031202c9039040400402c5203417008150a03030880d405140a01d00766480780301280b412082c0c80d8004100078502035500300c1003500416281c1c004540741e610051180e50b01c1c50220140d4000340a000c841c0c0c0c204109407401c821207030160080c150b1084041d64200422243e01034941e42001e0000c1c1d82c9139460b00e4050410355241e00c20025103039400c40702214408541c0d00e902c0c4606400610090092103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 124379325 1250 124378075 124378091
    0x110c0d0305061f080f06010315091815050402121507050a0e0d1104050c07150504060b030a0308060a0b0301060503071d030318030f28030905120f1203010f050103 71
    0x3c0741d001c4140e41c14500703401a8101000560000c146480489040203030003511000704e0103031b600c80d000341d83c481c041e0b0484401c092400c2c4900c4400514075076007003800040e8210090000105010901e1229030407540c000030701e9240078018021091013031040301c001c0d600715900d80001450301001d06a00b2480e24604140c0f03a00440c01e0a56042142121490f40000d40200c050100008102040c0203801c00352801c0c80300d40c843c81018203060054a034001d0545081c40d01c0c00e0941c1000d507005030707401400741340040f40030705006010a0400800020a40000d03120004202841c200a06103000500d101d140541c80d641c0740880044c0b0502000e818030040260350b5400c10030000c0c811091450840d030003000e803036907803c880e50131607100ca008019160080c012040750b80c1420001048129070032442d6000c02040401c03200d01d40d00724042c080022400e0101552000c50326841d0801e21940030b020780801040c9141d0080b409074074014134000c030300d00e0000f001c00043c014a0070100e00d42d0222402808c021480d50 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 124380575 1250 124379325 124379329
    0x315150e06180a0b0f1207050f0f0a0e010e1302100c0201020709020c0c041d0703020d0f0b070807030b04050c040b0c0f030f0405090a020f090616020409050309010201110c0d030506 79
    0x80b4102800000a009000501c00c1c2c8400550200210440451301e0140d40c00c2c5600034000030080004005020b5044100c2c10006400c00e9848031001e4440140401c1080008800040481d030741c0b600109802003080740180121a010080701741c0001e010b0004640c0400c0700d90005150544010740142040424101e240459000b000790300040c1c80d442006541f50100301d4000d5a646c0186900325201e5410040d441d82c2868440869121080204000d000c1d440d003141c09002400c00500f0f011200401c03002048000b24036080c0c20a40505543e030b840e0001804c10100c001c054883c0c0c078056034400c914200038043d0400011049604403044425400d443d101c0604100b414034550403804603460000054201510600c0d20040055039070456030004a511000c10100890080c0c080b0512031210400c408d507464501000548000d40200140300c100310200d40c04a4141c840307044080741c0583c00402c0c1490551380a000e802d00850300300381d440e402c00a9482d18140d45042c80316030741080c542c0e2080864019 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 124381825 1250 124380575 124380589
    0x1080307110f0a03060b0f010305150d050f1b0406090b030a020910030f050a0209070207080703110a05030115170a08071203060b0c03030103030806011d0f06041701060315150e06 78
    0x1c1100289660043d981d41c3c1032000c082c0210b9482d69115110341d84d414100c96000b4403903d4060706040317441c404032007043c006001c0003010b040d1064600e40310f40511525544c1c4100400000c041c607041c8403030000c0c41d40406010550340141c01c041c075410b04100c2c07801c0f00c0c3d403400100402e00b00c0e0100c41c0e0b65a40d071160020705400e20710300c2d00064031054070300ba1b094090140000308421514400d842c0404140e48240b003c80c0c8800c0f460040720902c1e00446820800700703c05818040d03405078001d05c0842c1165aa000080c2150207105500c131152070300210170000d03180b6504005c070100c040d100160a0316482550303203c030716120301d4000911442408003585400c3d4401e521070b1002d0050480120b42e1200003440140c1d072900f00748822000501c6c800000703041541b040b8164a0014a646a0101030540210810010035564102c00781c0181c1c0a00000500016401028840038582400091100e06500740308243d2520114038402940c203000b402903060784019900030031601d80e1404c076032054984a00280c0c031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 124383075 1250 124381825 124381849
    0xd0305180f010204081006031221020a021f0b01020a0201050d02040902040611071e030609051f06030501110708030c16020904060f05090c100509040e0304080a0215030108030711 78
    0xd140718403600d01c04016015401042582e49440440e000d41d80c80d50b0300e4000366982400300618440c41042c50b1440d070b40c0504110400351040c00d0041c05500c054541910480c2c10178080c1800503800300100c00340041c00b07682c0c28a80d10041d1201485605903030070001c0e545007015400281000350001d400c1041d0161603041d1b6000e410720400c25941c9660b2443c00801851410010761114094481d0010704590b528004440800011a0000707e1920b903403100340c001c24401c0b109442c9030041e003060302105040b100140004020001000413102c0c21400c1c03507030840303800e030054901d85401000780c0c82c0411881e0050b250301c518001043d5564240301100f11422403003d01c4005d403c00c05d603105000405c142c41d0412052801c01010400c49591041c0301580d841400c0d8002a4100b100c545034252038622510042c0683c82000d440410688840110186564026840007440340c002c042568214946440c6441c10014250b02e040c0c1194107200d072554481c1319408004044c91003a003603160b1944c445000d000e03d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 124384325 1250 124383075 124383121
    0x7030215010801150b0a090b160b010635040f030c0506071d0616021003060f0e070207080601060905062515111204110111030a050a020118050d0305 65
    0x4001d50351450424040d0880b92540080c20008130000309164180d2801d0710780161503030351001d41c82813030510004003075846051641d00c82c800d91902ca9001c20201d00c811402024540c0d51240f060603c0c40401c80841c21000d0394400c400800601c00480d2541940c0350ba80103504404940391441d0549010348071654401e80040c5180901ea0400c40410b4201d040e80c2001c1d102a89000b0304038150300100100ca2080d008902182480c0c1c00c241d4016040c40e21460140c01040e040000300c7c90f440c0c2903204114580c5034007860320841407004100400d681800124003d001d0f640c001c001c86e506014025000c41800e00905020f2040411402d510754403030712110f51240c02c205511780104609080c06030001001c00b60050b07160342044001014008048110744034030021281001041c4c41c0d9a50f03100c0e840d0710b04501181005a1008240030307110040c0014040c1620b2516090355030101500701a0942e2121100400014884121607000c940c01041c054176040e03091800240396070790800d1980107002d00c0c40921b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 124385575 1250 124384325 124384363
    0xc09030f0221120a030b040506091b090d050109120215010b03040501060b04080c0901060801050d020d050106240311040e040311011b0c060f05010311090702010f020a03050105100206040c0506070302 87
    0x3050310f599000500307003420182d509110300900c00082c0f0090315815140c01c0e8110414500198501240d17075980b03085441d0200d40245040d40000010380032403102402641c650b595801420100034041400190b40340b00d07400a0600488024205070700d01d0740c1403180d02c080a07400030014003000420b600420107080c201d0714054685454060340c540d070301d804914072400f4400c10400410f40300e001e0101c85049540042440040403140c0d0300f4800107160302182154203648801011a42041808491030b0351440005421400d84841070004c0c00d80c0c0c4101e03c28140120108001c1c0030458240950303942c496014145209411007591040b0300422030310115080082c00b428015a40544c00400c0c2451103004101c03c1c0104807000d03062104840c8203202c001c2000b0182c00081e601820120170490f071000f000d000008a01004103000c20a99004010101c0042d5583e401801280303006d07841d401e03003440e05100600d000d192680c1c4a646822583c025280700e050040340306010184200807981d5130f620a401e0034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 124386825 1250 124385575 124385593
    0x40b01031502210402090a150b0a0c06051e07030e030904091128050109152111032e03020108060a08031b0705010c0b07080604020d0914010c09030f0221 67
    0x2040503e5080e0f5040b0b00c20002d0101181c408140c501030340c48004030b8030341031408052a010b450100d5602554400c0d051040d500f045001044062143c80e2083c00c103603180328400320a08148072007a9a002b003041080c54600f00300103002c0840042511006d07102650002180f92103401c00c0c07042d43c0da07081180d80d44015685040404821060061801d40070181240c2e41859100c80c01512940142d01aa110614405504205143c803809120940d28041c0d00600032000c5042189030139152805220481701c80c001007400300708490744400c8901070041e005114800d80300000b08031440c01a030320002e81001072071008a40aa82c4552004000301030303241c112075803901c6a2010080c0440034170507400b10340c001c0c0d02c00010154011381001801c03a9001541d490640c0d01c2480599000001030401da0f00207600340481407002140d841a01c000a00609044041d52000b412090a4910312018202000b000080800024038186011481e09030704561a8a5050180c240c0c00181038951f0407290140c82a1511 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 124388075 1250 124386825 124386877
    0xb0405011514060f030709050d030e030610060c060b041d06010f08060606041802070f031112180103050a11040e0403020c030607080a02090d05070b090f09040b01031502 74
    0x40312048003008080300301c0240d40ca040c20701d01402d0190549402400c04c0003141c0d0400d600c440203590043c624240708641c1600c820100740c0911840703030110040f44041142c5111490b0402c0b010b0383c0584484125101d07903040680041000c0740941b0020400342d121051560b41d940d990b0400c5d49004003800c0d501d0308040c4041046651600300f071051200000740c5103800b00c0d00c600e01044807031181c00007034141072070300d46488100b5032007041c215000500c4907424803007080040d05c0942219241c0d4006c0d038400c0700c103211040c1c0890404000d8031707040e000d002c1c0030096028003103400c240c8580710440901380000d095030340c2007046000d000d5a555508882c0d10004010412641983e122805a4000da080f50568401e001c145603645009548801c08915090001600741c031164004044052002e4074000c10a511990780500d8003240d07402c070010004002c43c58034000d080c940542c1081e80c1c000c6aa00e04982001d071200004010107020107807020500c2c681228400c070450b01211302d111114221030301c240040400b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 124389325 1250 124388075 124388081
    0x90203070527300109020303030610020106080d0302070302010e0607120b0f1306080d0c0c0e090c040e03090f0a0b0703030c0c0503070501050403030e010c080601050a110304090203090f0f030409050406090b040501 93
    0x3c008080102c001107010843e90140300d800400d541c0036004629540b07901c02040119294400707038104540d240c003808a42c0010030303c03071443c43c854070740c501607203c000528000e400d40300c1142403009954400c0040001d855440440c8456082c403105000441140b1072010034110310703002c80d141e50003101282d09645a403859a00242c00c880c441d1050710340064082e8006c80304500703d440d001e84000082c0400348144120b000c801d641008808084ad02841c110101107419110b01105144040c1c1010990103030707904044410901900085600e621080d041c01c0551109024508002d010540d9a202d16000b890062686044054100c0700301c0c4d84414040c030b00540a404103d4046000a003440c08150340c04c101409055841c11198503482600e94a000045078190800481e60041111851540b000f0720010700c000d00c081d0030107070405030780c0b07180c41032000b844c10780b444944594a5000280c8506500f90208c00d5a0684480c9400420b142e1264105400030b44900d000282032000010244410040158 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 124390575 1250 124389325 124389379
    0x150619080916090c0504050301090b0a0b030d020303010e06030708070803030601030f050f07110111070302010e0f160b090604090c0302090a050a06021b04090f0305040f090203070527 80
    0x2a03900ca56079a40c4840190712400040031080c601d07140e5020621065a20350400013100400c0d2401c10f0400c0d554100080c291412a401a03c505409c1c07014018841071500880000f000d0035401015000c2440c40e000756a407105110303002c204220071001c00c8440d075040c810100204509400c0390802912020010340302d0b44152200e90100f4603015026400c80030078041c0d01e22540012500d8100c594415900b83d03110444200080f1507550f8a02000d00070504100140a895010303600000e0211510b00065207001a0501415080c2d0700840b40b02c42c000c51850100c4040e01e0000008648480052002c50442d01490301b10700203d60404000351481e07a45980500301c64003003242c215000598074410300001150b45d005100050b0849105281c0c4c2c0301c4903440003800c0000280c00001e40c0b54550b154910080c0038040d00300d0009000150400444c50702d0014000500031610085145041c80c1c0801352807441800480506a072000c0403080003141404024154194050044000c0340341400407a0230010040c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 124391825 1250 124390575 124390577
    0x81b0d02070806130818010201060306150306050603030f0712050d1a0907030605010f031503020d06050402100503060109440f0712030c1704030809090106020a020a0b03150619 77
    0x1040080c1c13600b985000c14095164004ca00c0b64580040000240ca55074000821141551340701c03c4004001202407181003011010500841101c038110b08c0d048098500143c03074244030784e00500c4008203022542044445555001c0a140f03195140c0041c103440f18001c082254620a00d8418290400c08001c0d00c2030591400032180c03007046a03580e84068040320614001c1c580041da03200240b165060295100b840d80c0c100b19102c40d401c50b0340c0d03035000411503215141e04903201920362083c0000c508207840710b01303829115800d08504620f40900000c00706045881140c96903e00402d030101a40151071028007100142c07510908900301d002d8080b254a4400741185405101e200c080b0303841074001040380c00695001c0f401111302c032080307030b14101d41c046803242c4295130030003200b0b43c40454400d03224001c0005500c15048180c4030001442000340c0050f05030321420654216848140043e620340454200341c400042c0c41580300d8840c854032000690300001200e420880000d003038250301d00c0004d9121145190703 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 124393075 1250 124391825 124391833
    0x1d24030708030d0b090105090405150c0d0f0c0912050d050a11010507170a0207080405040b0411130501030b0a03120305090118050304030501050709270b0a0308031005030d0c081b0d020708 82
    0x42c1e5403c2c2301d41060100c1d4040c107183c010858076021000c0d2144080d400c038496600300c0c0e080050389080c40046620102c40381040a590300c008030313800c0b0f402c00ca1820007800c0445100d0002d2400d81c45058482c01043d4081080040001d010b406150103401c40034408003250008101d646000c2001400390303510b400d9051440a880c0e40010040c0045c1d00031101e181e070b4415501401c0030318140901001d841c0c1c809495a000e40c890700c13035202e25040030000e000840c0040717488442461a04001500319080035440c2801075100c4d107824408074280013115815020f403403a00045d10b1307454030091801004e00340300500b501c0d1651a901018050000301410a0b40e00444c0208003649402405031400c4860b40308800e414490300001000121451000745580d40c9226004111201580001108070286410850301040007000348010b91052042c040d018100a60040c4800820700c54094100c5414060081036400000b4036800c80d04015003c0c00b5031400b112003241d03502d44518030080d40380c40e081d015900321445 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 124394325 1250 124393075 124393079
    0xb0c0316080307021b031b180405030a08060a0506040b18100903050c0603090c0910080d0309031211091c0b0103030206240f0909010e0d0203041d24030708030d0b0901 73
    0x4824903c45d520124014000c007040e08081050340c1d4025021036000d40d00800350301004146260ba41d0481e40f00390300c10b0018580c0c0c2d110702000640074080103810240140c10f0b091041c0721645494040780c1c00d0312482ca40103910341000500d000e4000784ca0303000071a04004401c9034221005d41003810390043c2c074460707003e6032401c46070101804a0703804200c45840c410742c80f4039200034480c02d100e803440390015151403100a40355241c1c0f0103a4035181e01000c0000010703a4540c0c0150516612494140400e21040c505218540c69045401241e000326039540344142d46418030000c2001c0e20041143c1d1459210203242d040d07607980e087c043d440e088121070801043c441c00280b4100b1850400101a035a0802801d4000080406090002c0b080000348030192540da9250500c2c0d0802c010000c08440c81020f6000715921800c1070f181402d01c1c0c50400c2c0189044220405000d10710010f010040303281221404c440340d01e4079804c1c1c000b034604401030740503180c039000004a46803001d42d140c000e210004404d07501085666 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 124395575 1250 124394325 124394353
    0xc12091c0206182e0e010810062001051014030601181109120d0915020a0807170412050d050906090103090c0b130810020301050303040b0c031608030702 67
    0x168088030096020340100004203880702480303400119502d0140010b4420400001800409140ba01243e000c0710f15021181d049550302c44e0351300081390000e280034102c50a19603c0c214068055001d400305100c040f80d00c1c1c0f03074490500d0070392075900000e510007841542440860b03500c0400d0180030765900f84807201031026880c1400100e01d8100c3c1c002c14080500d44030b980b5808002440085075410340c18108005440541c1e9030075001c0040c3c542c862014104181c1c070b1540180c072022443d40b025a00200100e00820859008540b44034055001603109035503440626080e02c030319040012914103024085804512014003c5c3e1003e1154401d2003200c03108141d140003034076180140c403252540001c08204c0b0308843c7d4800c0e0808a010381c0300c1c070b90520301c0d1078075041901201d401950121309600803164013000304810810070031101c2d07008420111701d10350510300425100e01c03a50081c141c0f00980050b0500010301c0c00c1045442001000e81d080ca01c1200324900039405900a41b03400d0014414004108015 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 124396825 1250 124395575 124395619
    0x714040306021b0d0f0c0c0e180114101a2217030403080426010204060302070b0609040314210703020405040e1605040e0c030f060709060e0d06020306060c1209 70
    0x6940e11740c595030f041e00032110084440310080b0000b2075544180900000781c0c8012000386038002c00c014040c81c8244180c42605508403516002c124404000583c248800744d80349041d801d059980c08000000002071039502c002c5607200d00001554580301aa003442c00020008005400b41d42a0a80310310021504240c6c5554a009a01016000003000c2004000507900b03000d0307010b2041d0861100300110a0107281c4d1508a802c1640024080303500010440100481002e52561100c02150031200c103013403a880041410313007601c05014414100050b05030810300008008003444080010b55142464030b910001c0286d08184103040c000c90808010750040c01004c80e41c0d1941c3e0205001800d1000c1c500300810024210804065075280540011280c2c0c60f241408802107000022000b000c4078201004000c1260165512410402100e210004080d0391800440c007000c68006c2c5c405622519007400191a52240810340f914900c16041c000050140d0040031f007081110440d0398803c03c1c082c0311511804 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 124398075 1250 124396825 124396843
    0xb13140a1b05031503010f061a0705100b062205090f06011e03090203010204090212060a060503060607031106100e0a090807020603090c0a09020304110d03080f0714040306021b 77
    0x801c0d051640c10500c1c402c20245074031280d10030a00c501c10600c2000300703017103441c2c0d01d16000c0c10541312070b0244013101007032004500c481a410401407800f1901c0d240c41d5143c00c0b0043c0301564a03502d9484084a40c0e6454050b1510b0300d074501c5131141d4a02110320f180100001500c01c0c0ca00a00c40280010181104050864824034040c0c5480c04803509810100501c125025038002c01d055460140030096202440504003400c1540d10050360742004488560135800028100c61040c000444184641903000b826650491800d503449a114661840d003aa83c0c007155501c1e28010f4840c04080010082d070b4416484101d1b000c0311200704182d101d03c0c0d603e10503902645006440a0740c200240001410910000c0d5400515181a14204211080040d44950050f0b2090703514503004000c1c030050010401494550f56030882c2c14490030040c41d43c024251702d0004001c029411140000070f11040e0282c1214501c1082001040303981d141c41c0c4ca0100020b410000004144100d0891108421040054907a00e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 124399325 1250 124398075 124398101
    0x8130603050a050103050d0e011404181107080f070c0504110a09080d05040519090203041a010503160302040207030c02040c0c05060f010503120307020307020a031101030c03090206030a020703030b13140a 89
    0x5144107070790410750348d2030300002181c0c1c100505500e07007101a0700000c0c00b0300058010702c40c034580402104000d060986141d80b0038001d8002d0104641d00018aa80b001c451040c3c0d585842c0c1c47d191203160a0218030214503a0000d03400509000540031000d2a038001030401c00041c0c0c40f2840400d0311075850316a24900d1402130804140c082005114031724100000e041e5100713100c51210422031716030a41205a070402e9074211081e00150111917840d903403042456002d80000c0e80148003107024441201d5200c0440d1102274000c6600169002c00c1c1031040b080120626000b5005001e102146007005080300403d24065605009200101c1c0070442c00c02090782c1240d00050003002d94401d8809400d0340b07680081c00940c1948010400c0d000184c07039090044005600800b022581c03211160005410b40b100c1600789010907181509690060341c1d5502980d0b001020050b0060301c54000307207000d4004000e03e1100c180e10201f44240740c103144803a500105c44020b0a0000403256490314042d50301500c4040800300 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 124400575 1250 124399325 124399333
    0xa09030909020f0c150924180c0901291602010305090a0b010603050a06060503060102070e19090b091e0a0b041e0c060f02030f040b1608130603050a05010305 69
    0x9519840d00941001c0348603103072640c540f80e8140341140c642449045181003055840b002c0005c0420309110005c101c0d01f0640d0220340c049907011b240b06a14400520002d034810f001540c3e0301c1d03050070400034035100f1540581103410658580c2e00b00ca81d00b49003010a01d41400c00000d02000f0502c680041c0d804002c41c2d10205080780c4640e4bc0150003030507004080e031150384a12603e0b100428030014000c0c1c004c10658900140703d0401c2c0314908251406900800240300c8100305218a81c0d0380060b2040c12548209040c03445c2e03071100c101c00d445070010038048280c964200215070b8207002082f032005015056041c00c0b1400600f03046068001c850500c1c9801d06250411006100860008503203150300911483d5030740c05a090038442070302d44440780d01050758459000c200a20079107820004030035690030342d8001103003085003400ca1101d03a0321850040d1160544041284441c006c1045030f40d40340c0030392107421140c030780e42c1c01107964007161680d203e00000241000b000c202d908096206580c140c0e07030440054 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 124401825 1250 124400575 124400579
    0x20a020109140607020904150605120312040501020d09050c0f0307051c0303090b0c0705010b150a050c031b0d021006030803060108060102100e010603030e060301080712051002130306050a090309 85
    0x32800e4001c82d0960550440020010f8030f0040e0307502445944134038456001c4003600711140390007504031703040741c2c00c202d000d0740300b4007900d074400940041619001d9600305030f12101951a440e080b40039010304050601d086061148030303020844081086003240c10203036090780402c0342e464101940d0300c10510031541c004414007009034174464550303800c080540c017070300740450f5004840c1d6444c429500b0031900d0000107a40440c140041013000c1c041d020034050304035034800d1084031030b65541015100d0b11904505101001820106881050003500c0c1c000714842032085d080c602e00c080854840b8080c2c048030b0014000e841414810b02c00364400d21003901c2d0401c48160850780c1340401544c035600e0140080707055100c1c0c10110440705800b40510280b030350a0500110300e0034650303d070151050310300c00d0100d0b2203104244010701c100c0d4000114131049a2107220004800c04040c14440d0400710749a40101415000056002c8018402d141c0d01c0c0032030384503034001c10042d601c100b4480c040710341c41000200050440300c01 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 124403075 1250 124401825 124401839
    0x6060301120305040b120901150503100b2205070f081b0f0d0e0f010c03020f0a0c0201050c010f0b0a09090b0c0307050d0516030e0304060c0b070c050d1d01020a020109 73
    0x1252146840b03810b115140585071140e07615590401c081001200c07150304104103e45e0020b00400c08010404000c617035000781810300180d1100d41d0b0810440b24199a00700c03032181c50740c1e8410171070104622125110404119200000c01800d011140800803a0000030b181c04114402c0c903000b80315880c1e4541010800000540300b1002d680491503100759400240401410a039840c0704100d5280f20003001841c103109541c03185400e4a040308a854103061040c09140c18204541d0203c40e040b900368a400003481c012031005803051701801442c0c1402d5841e003004145030014603400340d640b9201c11100013108a642d05c070414103446049100812401091011401c600c038071100ed5a00320740033707041030303800e1514401e03640044403000c48121103000104018a2000c54151007070758480c55030f18020350710701401d19801801100107294010400301d405000101502c4c0303d159815042940001a960700414203440180040940051000310405040a5588560000404034029941a19078103820351524070 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 124404325 1250 124403075 124403099
    0x60f090f061c0f0b0a020f0a030606081302060304021002190309061e120c030b0d06090c170304030f061104140108010b131202030a0f05060709080102130509040c05100f02100506060301 81
    0x1805c03201034007400707014000400e041c080c1010207081d60300041c0f540d02d000c030000c00310b810280c01c40e0560301d22600c0080c090303204c4808403075100390140e038000b08c03284c580d407400c9140c21402c1e0040510310700d00304400070404d640032142804480d12a500e07008400c80c904070784064007107121600008220781c00100700140c5416040310490302094200011100c0c1780a01213000441c1d689402c446155440f0380960822190b20096005406c2001c2600380d41000d110340b03140d03644214003001e86030106625038481000410707080341c0441c820b820b0328240c490340e540b082400224144020140410440d600108a01030f040064502c0c49101c0c580c22a07034103190540541007142204000d036007502404480c00045400d40b030742071a841e4880c0c0c00905507468000001065130980740c00112040e40108041c4030f0340703e08004060f042d40d0048a104800d6105d901d0000d6000c602640400d030070a01e4080c0320880150403030100c013941442c54096960780400c40002c841150701c01ca80481d44000144018024000d82176 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 124405575 1250 124404325 124404331
    0x301170c04110a1b14070e0a05090d3b0907080c0a030b030f03040b12180c0405060f0a0305010c170f01030f03020a1e0213090c030b060f090f061c0f0b 66
    0x4540001c50070090b4844560040c200c0b600012960301c4003a00708400f076480711400b6400440c43c1010272a40c200091203c3d1a40200500001000204103200041859a4500d0203141005a0011801c413181c402c4410a842140c46481e214100b86030005402c82c0c0110025441030841180b01498050203105c284c000785144444243c1512501c0400c04402e0010402440500008040117480c0d42031080e0f485207500b0001d01500b01704c418510030701800e120018100002d4641100c0118840d0307108400700341e0b440742c145103a03a4856010400002800010744c070001e0b01d04420756416002e910b1220303424089410546501444424245c010404280a46c001c04582d910a205582d0440802c2d110f03440441030320000001039058000607242145060082840c61000e01002440700031800c1e250407000d44510710014014030340d41c000041c020b95845245885408008101418509248100c0c6000240444110340105035403804076000c06100c1c0718221080fa070054603099929115960700c00b46400c05 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 124406825 1250 124405575 124405607
    0xb0702130f0b03030c0102040510020307030210020d0f09030f080a020c1b0103021606060f05010309050309010309030e100309140c06030a0f0615020a0317090a030c0203120301170c04110a 82
    0x107400d50740b035035901440104840d0308600c0016132590300f4042044000c80444020000f50340c02044088002a0081341c966410103030001c0060701e07404101040303009400c01d407a02c16044d91501c60424201038006000f1a110029030b5240500c550340c10b40d100040340b040300d44000c203942c0001040059000d1161285c2d64035181850013604103040788000c000e0005502074100c4044d80c50300340520401046041c0b11000b0182440d00b03118401c01500e604c1d849205e4034010074101130710b6400782d41c10f25008141c2c01d031203904003034511100e5410814005006210000e001c44142c18601c42a8503c1d403000500c016030008018805480c5440b041c144100070809042e44044107a15000b00203030000c0440c000b0b290004103a0047d00c1000c00500d4010140810a02c3c0745003507031845424271001c3c1e6070025503401036a6060510b4080f0807141e00000345000b102c0075640102c4800000042489903803402c03c0d12600c0c0c81c010071642170400791820041503039254502150020701c1440004003581c810b00c4440220511 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 124408075 1250 124406825 124406831
    0xb0412020609120d02010b010503131b0302060c0f01060504061505280908190302061302011418030d0507020904151b0305061306030b160207120f0b010b0702130f 71
    0x8a5400f05041c40054416202143c0064040d44d0f2075540a0243ca14102130918080b459071405288010280714a0b51010b4458000300c0d40c2a2601c030100d048503009540c00402c0e070354840703030280f41c42903807400c075400c40c003c20f5403d0150014550a06008210541e606544003002c080004202104c054000801d0f01c903454400803001a40300880e0580801100e016030313038007207007503051a940d07500c0c2c648036405090104a02400c3d54010a90100e40d82e41c0050510f5464807440c0350900040f1260003c1010300c4482690000d00012014886910704149280581c19184096400c96041e00d50340541c0502a4024906c00c00190010721b40412542140380d84000026200e0110300001c41c100d0b41006840000c00e94031828400c1c14030740b01c502000920040a401d1210718159038402d440104060826881e80c079140705c036409450f00a20141e0090028080210781c070808a00f080600003a58600544000540e4000401e110701800c04441d0010b4000e001c00da030f2070244c2d0401a00a02c00c1c038883c44200740c0c0d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 124409325 1250 124408075 124408087
    0x30a02030709180b0906060910050a0c0c121202060f0a02070609080a23040b04150207050306130c0605190f020102130e010509060f090c031b0a020d09050a0b04120206 73
    0x48243c3c00002e031881009000100341103020f080c00210403010f0032040c03107500c060068000f580d8440300100003500701c919117a40c0300c085524040d90080d80c030200040901700740c1400800c801d556481240012401800e4506000300c1010040e0389a82054503200d207217818036400a01640d544e0340040c58038030300ca1100010a40900d403140c2c203040e0810400200092070031400a4000481c003507501100e85540300ca400e00d00b501d81400e41c0e026110714401e0441e0274485d001c002805500074040500204009426135400f45030811808070720312181c1c01c0445641070030050209141d880362050302c4010201441a4204101800c0c0030364560004041602c1159002c0001c0280010071010700b40090441d40d000344881c2d41003a04103c01c0340700007000746000f0000241903842070b655182d103140d0000d0105041c1540c03a100d0205403141c0450352409a4080100058600d501036400600c5403070984242d134903441d01940303d104108081c00a8400c4490021b8144014000e4080240a0701e410610003044c03186405 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 124410575 1250 124409325 124409339
    0x14040308070804020a0302091906061107230910080d031a06131a090301110712080a021201030807030e0d020609040e010b0907090f08070605160807050a060f060e0903030a02030709 79
    0x81308c200e03440c41c000e07141d200342642d015505000301c0c1d025242a00f00212040c107200003199a0700428403070310681800c1d0246c03002c0034246001880c10000b4002e40680c0c058501280c0c1c0f100001c4c000d12842074140304800360788000d10300c44c0c8580c9108444072003120384000103680400610390049061111903c0b181000040d0f02c0c42500403000d89a42da100e00182c803005801c0070103003107508802428804220812034a000200425003c0a00c0300c0c0c68106282e0030b4440c100000024080c2c5540000380011400c008001e2298000150060a00c20f0b9528614441e0120510240e01e0788520000c1d0851801d0254036007a15050f085100700350109800011004c103900e000030500442592050041800c41c002403120b604400d10b01009011503030000c115091801b0001441c1d40300d080c6510404501003000030301080308190854035015000310484890002030b040a1004017080031b0390000282c82c21078005141c8106040140c4980d503070a001c1c6041d940d401000760082d5100500c3c1808114255402003185 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 124411825 1250 124410575 124410589
    0x1170c0409050d0e040504080f030c0705010e03030604050a090c050f04090f0b01060828180b1e01050301061805040321060f0e0603030a1202130b0d14040308070804020a0302 76
    0x7501610007000800081c0794042c083c0e0355080e03a580e010354105807c00c03011451450403035980c5007903100340d40d540e980c0700d40a900090081d89002082c550130200480c01212000000d1801180708690400003a21020107000c00c0b1080358000800100e604213003003281e0703d041a08441d41c64009007020880ba5a6590f07800c000760240002150300385100001400004c0d0710000540c0d004542e5501441c40303080e031440303004c20004031088080480d516a90001100d54403912150710b06030b48600c20010a003092a41c010b041a2480c1510301e6404101000044600e0140220011038000130814015094044895030261900410503018041c0455004000c41800d0300e902c0400000c01030001000c60410000c0340202c6c40a5010301083c4050005100342d40c0d0780841100c03139184a41c1001703084030300080d1810000e40240d510801c40407911900004614001c280101007103508000100480e11050b0403007842004241c0e400750014996100160585005105864219000a043e045115582d034000703001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 124413075 1250 124411825 124411841
    0x40209150408010b090402090408030c1209010209040f021603120605030a051b031204051e0301050a140f04030e060c0f01050c1b0f101d0a03080106140f0301170c04 72
    0x39000006000c000500c000c0c402c680c1240001c85280015060580001c0c4001d00060400740800c40000302041180c5a1041283d210b0103101c80e0011032882c000180d58000e4101841c0345000d0740c10001e12080c80c8405201316101400103202d03101a0400e252000c80b1900c200012448403540e0300e0102140300c5d60108000d01c215031282000301050380b15044031250704400280003900a500001c0a02c0d030f90221842500c0aa41007030303ca02a50802c40044a2640e0082e8040641c02d0b520745818401d02e50301d40c1d000350f00403480304000120b164507807a008680004088801400040003502095654134022000f03011062403a002c8441803120b8803101c90031503000380d410603120741c400075000600000141030102d210012502412035407801c810030940307403450140030300c0d20540c0d074403900030211501c801d10750301c842225012580d0644c0c56180180c059203080c011500480c2044564617040050b00c02207407281c403d900920f50941c0d10300407800309495480c1100d10041d00503244450281d0300d551042401e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 124414325 1250 124413075 124413109
    0xe0d05030901120b011409030a120509180609040f0201090e0a09290c1621030b0307060e0d0807060e0a030f0e0d0f03180e16091401080402040209 64
    0x9541c064a00014200c40350728859020243c0c10014000e5213aa00000c83e0742d080c808000d129540d603400400041d081c03100f09070000340580110102c03000820307030001c05040c3c50310080e202c0310030303c1d00003000040e08030301b044072120303840760f894800500003401607148070000510604040c2c82d6181c5940f501c091400003241c0301018140c1d5200e44000b8014980c1e01c000f04c06a0090a10b0040400740b5043e1601c000d00400103000003000003286081c461099a24803c01500b10311401941040d00085030203081201c0c4c0042c00003030a01100c044203140124840d021615680c4540d500302c001c0707a0030b000070385141340e00644114006010140c08030b03031103000e1303190203007584006011440910f01d4098030004203160060200301c0104030349480e0303450700c000044015801c04a41d58113a0428036040f1400041840c0000c2e1002a10701e000400c203180c07074261800390036202d202080fa24508602140d8207000744c13203400f02d1050010004001035000d80c2c16190881e002920140c036000307901009c5054014140c02e810 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 124415575 1250 124414325 124414327
    0x8030a02070905060f0904140d05030f01081504031826060901050606180d0609050304030c05060702090106051b160806180a0b1509010e0105130c050f0702010e0d0503 73
    0x100440d414803104001e020203400800040c1400004a0440160210028081c00c1c0030001b03c0c05014041d80800000340e6480200c800d000203400d801040c640040d504132103502111b1002082907000811000c240810b800e02039810b40da500d44089034131604074504000035491003500454011b20820b0304030241054040349002b02240a8a004e14020000f0414039881e4506024400382e644d44408488c800440d41038106030290003440014504120981c005058078a440c0c05281001408000740c4100e9004044813015035640d242440300e103210340003000303511620a800511146018a02411030446591200d481c01e42c901140680381c17480c42c0c20104100325020004110101003040314550041c0ca050b4840b800c086000c5800303684840e0442c006150041240c0020305001c0d54000c100380440c0010898032403565075800038a8003038401e00406000c2c9540742d541c00054452030042c40d00c0c07018195200c5250242207a03450105810516080703040006601001c002d940e1080d0681815502030301c059 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 124416825 1250 124415575 124415587
    0x24090a0b0301080f0d1b03020c060a0905130603020f2106072c03030a0f14030109060f152304030204090b150319030804020f040c030b030d050412110d0506010803 71
    0x4103142049503542c0c1c1e013440c1e2251184440d0203034411070002d604210041d840710240708624081e4142400b0148107500604042002d0381c400b64490f109004980b0141c4007861300aa410294505442003804043c1d0026203003d02d011050a00c0c1162010003a810a035a4074143c3da03950301d050420800703aa10400107550700c6680240010030088a07071204610750070300b403289001000425240d006411100040c484003541c0031403014010081c0c280180800716a4a41e01d60b190b0880c14003c2c031030760003281002280003c0c0450090845400b0700c5041e0300d20b40301c18a0544940440324210602c1c000e0500e0400c00c28040040162035a028001095201d12179906e080c1c0340c040e14207403500c800e80c0c2c602446a84104100c0c1140108000e040100a40518200240344da55001007030300071244601e030a81103403070f0210344003903141d0603404001c0f070400807800d0700c459002c0020100c90a008030700885182040540b1000001076911018002810000d002129001c201d0f885880c01c20900742c0c01065581c00c00980 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 124418075 1250 124416825 124416839
    0x50a060b04140105090c120a020c1006051c2105090405070e0a140402070c060201051006050903120c0c180f06030307151e050109062324090a0b0301 65
    0x8048080c441640e0030812500004520703012040180708650241c0d00300d10102e0f03140e207509001c0b183d02c4080c0755089061406e1844041c002580f00640e0880300e402162140d0105650714044c01d001c40c0c0009110006400c0c01d402c1230002602100e4040795080000280d60389612440304644d074100030b00b078481d251520f91001c14041030702c2008107206e00300704203216104c0c2644d030340c010880d0a540c14a520701140d00c240c0800702e00280f003521000341c0040f2843d000082e000c0d905401c400c0c0b08010b200c809403e010786c1c615042d00c150141c408016031540180700215090f0208034041e00709054010211a0181c0100000c600c2c1c0d800a010b41c0130341c1509000c104400501c1002c42c450304003c058000b1854514651034210b03844035203200d14241c030b03070300c41d827021451010f448a0440021342581c01080103594444901000302010301c1000d03500342540c013050364268240841c484000c400070300b010b43e22624140c100c0d03c0901e42294904001c040500c00c07001c0d0b5846625010001e0700d4404421036480d410400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 124419325 1250 124418075 124418081
    0xb040501080601080a140115090606030f1b1407060207080301081c020c010e060c1e0c0301090807020f060403060207080301052e180b0d09020f010c03051206040905010504050a06 78
    0x280303146511a0004200040b0001170413210b460704030740085214481c80c00201d001d4000c100c0c030007030000c418110100307403402ca5034400c1b0102c4a40361002c11003c00c0c00c41981e0150303070140011440c08400d01000262a901450517030410041040031a45000c8840c2e5802040340c12443c000d455054001c0b0061200074401c003d0b00740c82d50400020364a0150071703014025555460b550347c0b1410408240b400c802c15441701c40c1a80c040a02101c1600c030a003080c580980469080c9c2000c104e43ea02c5100000d041e0360806119031020590440c031810b1801c0095000d00444100e035000042c0c104a08000000202e01036102405800e031084120703c3d541d52600081007442e441c1c1d8030303880036005040900d080d02c4107041c003129440c080b00340c05c1031080d03004064030301d60030f182c05540701e800c60020008541c8006441d0f5030000c0141803003220342007070042400c1c004603a5403145800c000c1c042181080f030000c0c04091041c2499000c80700900200e007050490341c07500c0c00c0d03400c144c0701180e19a0216000c2400c10033140 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 124420575 1250 124419325 124419329
    0x31209070e0105090103110609040f02030711190507031101091203020303040c0605031302040b120a030230040b0c07050d0302010507091e050f0619090303030c0f090b18040f0b040501 80
    0xa40303c030005d50540c6c641aa400b403400300114031960b80050401c00e90746443c0c000031106100c0d24011505d85c580040050410030301114007603002d0180c800568803500130751022042642d000f4008100340d0b400c5543d480c29a410000b040d0381804a01c02d0001804a01089018800c5119502958490404d49420aa2000b258015070305012007030080101000d00c2c0c3c234001c1605601200c0224000d121140070540a03168024076800c940207070078000f401c0c55000a00c103051401401c5040902c000342c80c0311484900307040241e5940d03a101c200020030230820840050403283c10b180f8140c82030155140c00003150301a0040c011805070351a8820043c07115003040d070f00c0008104000506111454007106402088440c2c00b500b40b050100712043c01460300e508040c0e4890011946c040c26500000310005800000144400c40c006070402d80300c1c0031034920691512080e0710741a03d03414070a034100309290358203070460a0b800b071004100e00685001d50340d490044440750041303040002010501e030390030b00050301c50507 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 124421825 1250 124420575 124420579
    0x17070302070e070c03030f09020a09020403020310020f04120519030f08090a0201081303090305070b070210090e060609040e0d1d120309060c0a0605040b18010e060705030702031209070e0105 83
    0x30703104100c10103403c044441d1390703550306140c0002d68005400240c40104403092002c0c0d0809074880010951019a44c01030080d00e000700c00700c0d0400225030f9a04d0041c1d00c200d40742c0700103c9105200800c4000384540300d44054a120304140c80f11025008031002c2c0b9410b110340c0c181c00150703140d594040d01d15000703051590400403a902400a00800f500080c004400242802d401c1000060318035040c1481000c0340c0c0042c5a010302038403d8a540c41498440a40024130700380e2207502a107819900c0c250080c8402401c4995100440d85140d80700c5080081c1c54200e022440d4000381c03528000801c3d17031000e105c0001140d40c6900e401039038028003280c1c00d41e03040030f820101380181007459001c4280c5200000781d0360389460032a03070a692004d00e900841c3c20052404001400541043c0902003000086041144940da00f41d00380f05618903820f204078240c40506600d454240c10481c041a000b9220308004c6601030568011a031500040c141c0c1400050b80445000c1c12079045110b0500c0240d1251141a0061400b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 124423075 1250 124421825 124421849
    0x50603060702071502031e0903070b040e04030c0305091c0c0914270304030506040312050408030a050723070b070504060f0c0609020907030b03010b040c05070201080a06031707030207 80
    0x585020f9540c00c0c290048051020500e905608005d10030012503000c0c00c90031501d4131250568600000194110001e000e2280c007801d10041803100318107003920b088a00031044e0321800e03290380d1030943e40c2c4105004290100082001008015100c83c1c610ba0054061241d81481c0c0301654102041010126000010490305015140c842890301c43c0c4c000d50000001d44d022811182202c040c85900e4000803070003000c90101007800418001d010500360300c10360007911744013907010103114404221142141e0040081c44144081840d01d40150b0100f0707400001400e001c403d030b13001214400e85161415071004110340e800189041000b046d044256000f2005007002c6007424200070018101881e0401c0748010000c50310360500602c105030300121085a0060281d5085040c51380000b00500010004a80298281922000142001d101d54080406950303a11800c00d10b40f40d00440f0300b4003010740001070441d10b03428040080384095104000c544481c90006a95412900e000f90a14032103500203030a0a003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 124424325 1250 124423075 124423081
    0x2070f0203060c031905060d05070b0409050603070f03080d09020603161e020a030f09031205030105030c010e0604090e030403080a170a140f09010e0f010b0406050405150f0a0b070b010302010305060306 88
    0x640c002a21007405e544002080940d01e060124007036030b0100700d000d0110311800000180203048c09006000703980d403000043c4460b54070341d000e141e0380341224800e845022001080410225540001912800701d02132340108000040d5000554a030f001079401b06000c806104071a9801d41d0840c9945040c42550f107821340300100b24540c0030351621a0000090f09000e410315018282d54403e80354a00075503030218800d100400c0d040710044c99500240660340c000e20440d082d402d0f00f5030254040150090f4001c1581d458641040707400c0d0060018040c500c1c425200c140000320018010034054411141a0381e10389403144200d20400200341e001410310800c440c038103551020341d524030f41142036011300c240348480200d456100f6814010000b07140007104500681e010048440c1d0103403c0700c49004000c44081c0f03c0161500c0800003198400e962080c0e44080b1040314080e075041250000010703110091030300c1c0005940741091403265002c0d80e000c840ca500c1480042c0115030300b5206554101209030024a8031b49 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 124425575 1250 124424325 124424341
    0x301020d0f0c021b061207050d060303020703030905240c160902090405010f030c05010c1a070e0109061103031302030114130c41060f032205030a111002070f0203060c03 74
    0x80318586c0c0104c0186042d40018090601a00454a1a1503425010003070f1315901d0400070740f104510700085002403600440001c513880e04c1c1480c500d5443c050100c148055031301ca00b10104a41c4007040f59611401510f1050000000a0507500c0090250960159907440303c1010030040b01e005801070140317074500403002e002280400d0140000d90f2002e01708404150003d003000c10146c081e840d08680705901d070100f044402c46d8003880d25140043c007030701d9008245072a10ba09071450741e0f00c030b02807000c01ea00030700000306441c86803120700c5070f05030011f400081c41da48402a0140b640004a0300354090011920a6a04111140c50306000628070726a0340c2e2900126000345040e10303429820000e540c607045084c11080a12a0030f2048500341c8014005680d840031041c80d4121504125000e0b540075104100d15240b1419890040318503652007405149005142c0c081616514802d800041051240381d20418007034409200825046018251001218085104251810000801c01090400c0c1481403100c50 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 124426825 1250 124425575 124425577
    0xf08010212011413020307030c080708060f21030a0c0516050a0302060304050f011a090a090b2712070537030c06090b0615030f0c090301020d0f0c021b06 67
    0xf440035192a0b020800c08500060004600442540007491000081c40402905680140c0000659490301c0b4010b640700380090b90100c10443d0b0081e0480c42c4c640340501d00349800741000c804210543d00c2e611004984072600e41c61604012401da02150440c8120020311208002d00c142c442c4000c204400e40f40e040130b000c00c1d4580c05500c4002c0c0240b0002c030102c2c08001d01806000082d41c0c1c0c950017048010050f04807414a900c90f141c410740111401c50203e00a0f0049000e59198960403048601090315588012170440a200080c01045450030340e038503100401c1806080001c13002040d0840e103918103401c0c0181084903c00070a000382c4115404c07070703070700104109404200610302d00304041c0d6070060341800c2e0b032400790180008101600d0726482c0420400301110030740c011001580c8140c0c020300d40091030b41841c441691140c050060842c00150ba08506a0081001140241c00941414071060250058402001a020085899103441c4841d03503410010251084915000c070800d00300e02c41b011a000f = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 124428075 1250 124426825 124426829
    0x905040512031017010207020d0809011805060a05130e090705130b010206041101090b0f0403060c1403150d0f030f08060a050a03020402180603010308070303110306100807090b04030c0f0801021201 86
    0x180044c0b41001c000030840030360603100343c542c000e001400181a02e00d09481507078031a2002ca03001c41c0600d01c0405980c03080300c4419090f19070242c91035181030881d10f82a2615013120019040300032892501040d43c400e0595014060302903c401402e103641802c0c00c014580e0f555041c540c00703d40c40c1200300c100583c0d0005003940c2254019581c460070300c00700c3e80125800000d603006070609020010b00a5007098809008000700c9010350720400c00701003459002c0394824195580030160300d0302480400c40c03409500401001c401401044480d4038829595845160f090707140081d00400c5038000411000350b080a5025480401120030095880c100b00024602b08a40d00000c0d000d1a80030444010200b10b1261500089100424140c0ca1350795a15240036560300490086001a080a102ca0800101c0782c0650307002b001c004040210b03691102da8115022540240490b04001d1030060008130000c41d40d000304061401034402c15206820a40c0074220a050340c0e008203840e038810003007280c000300d17400c481c0b0341 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 124429325 1250 124428075 124428089
    0x50108060409051939090e060a0e010204030c17070e160309051006030f05070e010608061306180e06090a020a030818040f140a050c09060d02070602030109050405120310 74
    0x2200e00541885d100d803010038000c036608250542204600042442034505000d011340341d4031902c0c1d42d1a440010242c07244100d400c800d0f41d02401c0070071070013040da4000c9140012006c0005003025925140d0111a4016a01030303442c041d101141c00c81e070130b502804050090030b40404100c02d14140300f041d18030b400c005001c2250070503984503011420000d040c403e8002800349003100303001d59900c83c14218042d00701d0700f408440f98811700d2000502508030390300e4181212066119900243c0e149000d108082c1a42080d00d0110380c0d6800c00820b031a0242d80d071031002d04074511400904a40b0390f01d1828a0300d04060030360030b203a9201e03a03000300040c6d82d0003080c0010740e94030600c559103441c0300c1d684802e4a0038032440030aa12904100f4140c84244a0303911103c1030440401101e18036031907882010040301c2c4152400c90400c41d0030848620039080550040015052001006280002a0322004100d800a070890748110391182e0a020910600300720550002d40c211140c6407a40c1002a4948030203a40e606c04c5071 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 124430575 1250 124429325 124429363
    0x90105061f0504052106010e070e2b2103021903090302070e0702060a0c0e0d021212070c06170c0412020a230a060912020411070f0303050105010806040905 68
    0x14694803030002d40e0b00404004d840130000341210a01122503040e074900c50b145e10700c254000041d07200400713025180070f078071561105414a5036500c00d100888105000082c5095501041071459041c00144006024050700c850002f80610400000d92896125120801c15005200424003002801e0080070040e440303040000b00210a8502130b814100c0907489500c00c41401c000700940c45401103085803040d4421001008041e103500307015100c07640125540e64000b01441c95010043c24080c6100042946d0042200c2c0004440c203100d480d40d62000c601100d54a4205108121182c0c0000c80c0c0e01315400c14000044a03460100c0e441e0801d4040d51107055000b440c16883d0b482551114400d120251100703120169803400b0311020a00ca0042140a0501600c048200060304a00c03442c031000c1a9a196500c0d040e0300c00f00c6d43c08100c098a007542c100b400c007507000c0143c0d1000505080c0713003504451103031b1000700b80c0398900320026145d400011f020500540c14001c00c900081c401050b50a11f0006080b218 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 124431825 1250 124430575 124430629
    0x50603040204090503070b040203010615080712151d0604060501080411040906090809090121230115031104090c0608071e0215010b07080f0c01150b0405040509010506 73
    0xb4054081c0c43c201624901001807040706010034101c900d4403a9009600074803036143d80c3c0d8894011030b80c42e07108842c000381043c0702140c1e18910400da04020050000004a00000c00681c1d82c1c44092440c0e0101d00c0c80280e680003220701d1011501090f9000c003044a0410100c0d18000c0003814508004100030840c80300140603e1040da00c40c0d00503000541c00407420003002e8401d00d03010900340d102440da140310352072a400000c0c0115000540c62561040d013105a004045240d44204107424240c201021168510a8864078440c4c00d102e9040303a14013a1542000381461400e100c1c1c1c0d4080c90026281c040c0f41410b003504040761000200ca802c480a500d0300040030380c0c0740d03402145c1745000314600301100c40180000c0b451041c0d00203211040c0701a000040c000c0380c0d90721414404c01d4891076000030001c2c003050013008142e2280c00d016102a04481001040d076030540b005006080034a50016500900c000c5010302c014149071180c1540040b8100081045050100c009a0004102400401c20b0320035483c80f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 124433075 1250 124431825 124431829
    0x30c0c03060c0305091903140c150f07080901020a0207030227092802030a0b0c13030b0f0703090209010902090a0503030c03120903070c0e06010c0b07030b030106050103020c03040506030402 83
    0x16500115008a41000400b008440080250105946441c2240305003051070307050b002d0318036481205581c540c0701c0031418030110400b0703103c4d9000082c1d40f80c258014200b2001c0700b50480b89800c0e125000c42030310b011f03031445e000c140942504406071000321142c0c810310804181c10340004083e4156901180c03408003410032080c0c0c0f02000286070712488407d004a000740700710010b000030320150040285620900b44100e021034001c0030032038480040e5055000c40004000306852071603103a001054188090303d40391a8050900c0d60021075407048440b11504807c10070064003e1041540004052400f03101641841e000912810018000c640c0d1480d0700081000460303481c40b540800500011b0f040d81e80300c48100440503240d030818a80c0c040b0164001c000202d04282c0800ac03074588561007000c00802504200006080c030000801c0e2505204484211a010560710040248150380b01c3d6404502900c03410181404d69185501c410b0605006024603410a040441076038192141500c4540d2280d42d5400 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 124434325 1250 124433075 124433093
    0x61501080415020c0703050d26040309030209150a1a07110402300a0605060703030209030c040e0a0203070503030a020709050603030d0c0503040c0b0301051807020703021e210604030c 80
    0x281c44400c0e00e10000b400503075030502141d2001201d0094041d201112086001a260740c21032003001c0100d942020389e100c414a40303007450581c0243c000e29100709605c1d05c950118a83d154140d075241030f10f80d134043d840000d41c80c0000e88100603040099980f00229600070044010f030003807203001041032a011002103056210355040d01c2e0a040d0240701d03004120b042d1409650402c01d220815024400040b00051140361076000f403c045900103404c0500d4a2000e0320114001e40005446541c503000705615007000b41e82c0c5000f00300051480e18003400c80f440036441090314200443d80020700a400a005500d00303507030040b0300ca01c2100c20101001c10fa03a41c583d00024114070924142e507201920701545400e0311580840a9131045104400f0540d82e15280c10071600680002d2050076800000c1a1541c16840e41400149170080803a004840107141c8a1780061001402548810010655522001601d1810600384190300c01b010030078800d480741141030700351200c41c000d00190512264080290420a20070 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 124435575 1250 124434325 124434353
    0x622090219321309060b091021020306040b010c0b1303021006030305040f08010227060c010905030a0e06040302100c02010207090609020a090503030a02060a4107020615010804 77
    0x415542c1400628014040a0f4001c2000b090200c2010710004c02c0b40a150320802080d034210006a500f44004d2a0800c40703641031070708504040049481d50a404e2480b9544440c006418a003400342e104d00e805810b0104035100700c3d820904000e8140101d4000c2044001c146070042c903002d40050181c010750400385c0c6800c1090202c2080541340203c00000c2c958458040e20907180305c3e800a650181e9101411801e03405001c000780082540c0303c179000030b41102d49010040c094406042a0708220704491440d08403404c4040546650704005000010964400c40f070b07e0040e202112006d0809046d50045801e00c4602c00f0700000b400700070f890b800e0540e030017040705000a220305202805050f0b195000f003006500043d40d00070100d2102d41011400780b60210545279034444680c02070410341d503010010405002a603002d0b154502d0b0100840d103100b001e00a03501c24107021400303000e000481d52801070141700c1d00145801c4c02c541104041c4a40004c0420010b40386000902c0c05200540310350401100700d600380 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 124436825 1250 124435575 124435637
    0x40e0a0b0a0b270108060903040602030301060f09081605040507030614120a0f1a07030e0c01140f0703200601050d0803040201030209040e1f06141306050622090219 72
    0x18001035043c28165800040c1601e2040b01038075980e80fa4982c15640c1c9004601600c005a0030510043c40a2072060072000da00800926201c5d05103642c070f00c40c8905005e00310025030707440403c240d028072440c100b07402506d8129039249400c111151410114110b08181e806040d44140030611184068190802698503c0303504441100c1c550301c05460210300c4680c00344100072140c00b0b00c2000486c0032740a8410040d0b04401c1c48040c055400c180801182c0815503009004841d034000d0142c1c0c9041803c14001d05466882a1550b00c4409114040d424a1100182001c0503070f500ca40018401c3c4e440750b4070303405e042682c018100348d1071751510b20040e4041d00076030405940191500e603034102280d1000404218124001921840b25620100c0f81c2040e40c1c0c1c1070003881009041c500e41146241403810101020781440c0c1e00000e011601d0f80c000901a80c0025081c900da10900345110840a0318440d861004003541c2204525020030030100110174028100d290b4240000c03001c0e04c800454800208003111045 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 124438075 1250 124436825 124436869
    0xd0605160e0102060408160c090507020106080708030910050304061e06053d0302120705070c08030319020c0309090103060f0c09030b0c0f190e040e0a0b0a0b 69
    0x210664809805598010040014581c107041080c503500102e9800e0156412400641c54403500110f200c40140714031401f1159078032410780010714460a0320482d801034000398000b044e02c62900c00100e00d04030464001e01c1c0700e90402c10002d41c0650b1000c80c80c0104980a09296031039568a007845401001c64034512900848412111aa0003440d58405c4003a00d004807904140070314405601ca0b00600c0c413207c2d132a1948105120b960100c0071214107060055000c1c5000341c40c00030401400d070341c070f01810748119010400204a2000b0080312010b2100644189030040d410741c64241142c11494010840d0b02040c154005400fa4205c4401c0c81215021030000d007100800d0b50307592410700003d108000d03405214500c1c044100e82d8061042012404498010045910b940c071400b44600996001114200710003204029078034801d035581e10030341c00c2c9031883d844000d4400c100c81c0c10720083e58501c410000c803541045200a0019180031800e030340065103420001901c071000340c007007824041c40110142c51800 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 124439325 1250 124438075 124438081
    0x708010e030406080c0c0c0f0d080d050615120c0304080c060709090b031501151806051e09101d15070c091b0c03090b030901020c1e03040909020d0605 66
    0x2030008010402c550481d5104c00c802d039180003041003540100f03a0401d00740c0d0002d2084201c0792502c0c400280c040c600007054110401210782c2d0300e40300c50744044400c115070f580321010403019150261611440d041d214940702d1500b05040b00c05880700000800014041c0b0002c0082014800440b007600d400d02e0001c000c0340c00c1d5041180005d0640f00c00c5102d040e02c0e26041a50080e044d080c04604540d07140a151025405a42002c03404441c00707804209003801c0000208001c0d1200c50360541c0c9000410198840e5503031412800304240090b45400441003940390201f00380d65154690895140c1402c45c1c0e8581209405441ca4810787d800d100404002d621a480c07800c3c00c240c62071584010601941f04038100c025280d914117544090398003404844044140c45032a09000b2801060241d0781207110303241412540f0b40b20f4403800708030380081d241c000c2e0307503175020031000c00715242000109828001c56023480c00b2580045480360b9244200d01500b54516169501c01003151541881041c0003548610b050140c1c1ca = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 124440575 1250 124439325 124439351
    0x703120c0807032003180906040908130312090e012706080706020f0a02010903020d060605040603060209030d1d060d0f021b0709090c0b0702060c01090309091505030a14070801 77
    0x5041c41340840c100407912103680c0d80b01d01d00003048030040500c4411442c1d44030441e400704100d00b24001c01c015041070b200c0d0345843c00913500c48004c0126203e4502400302540c10f50404143c014081d1031001e013030100151007800444030071107030741d41158000450b69003007032102944001541290091f800303c442c280030021903906804a0840c1c10381d8000d90031103030305003030341002e142d074451a000c00070703010034483c05c812300c09418806090305800e030007010040b5180b580c42c00810112031060348107440719607020848901c146024040106407140a2602200a100d50343d40e0140b02d0420303400e842c0c03242c1000180a000200140c001d8980d21000110864640101101e9200d0154601c0b0a00203580102c540100e03060000380301740648190040b000e40c01c110b040c01100c4407160300081003030fa030205091004002c003071801d018135040f69100c0da0301e007034a862400040c4c03000d95001c000340e4040c0140030601407050703450010f80000c265400074280c0090980f101c41142c2003101d950040c90055003007000d449044e0f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 124441825 1250 124440575 124440587
    0x1c1503080a11151803070c0e0c0712021e0f0d0813050f0309040c05030928050613061107050a080306010e0306010b0307120603030e010f1809090b010501020a03020703120c080703 78
    0x6080b10003110240000b10105a85c49101c2d41e10010003040200c2e400b4411050b6441801b0352080d48820300d240b4203003541e111003101514914401d00181e0250781554178031983c1c1d1b21a5040c010300040201108400491000c4d10340180100d04820003c07880005005d0080c040c02a4558030713000000c0c2c1e00c803e5140c8100c5034907030f8450115603015605110f5089070592055044900c541c024401904400c10406802140000310b41c0d805400b0050303510810700031680900402c0d024011103c4c81c240b0844182c88d20809584404c111000030701e100f4424000400c2000c1242c1920710b0f0b0200034542c5e40d550710001a01e0214401c100181c141c81441d0003c5800b0745150b0045003ea07442d0307201c0216909407151540207694641c04000c0010300b91050014655018000e440d00d0f01c201781c200404844004400c0c3e114103810f0b9408013203000e8032910a00d0038001c01d50292400741c0000c0c03015001c001c0740d64401a680f010b15100040004000e400c0c192481c0344581d42d40341c64140d0001c0d1280e41c1d01035509008140c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 124443075 1250 124441825 124441831
    0x303020903011a030d0f170108100e0303060609120f06040803040302060105090417031b160303110f031303030902030102160302160312030b0604050310021c1503080a1115 75
    0x40e6280081e0b0b40c5080d161183d241000200083c0100380c28002048110b59890751490454144003a030001c2410b10340d007101d60903019160f5940284000304000c17040c081503800b56501054107401c10030502100c1d40700e00040710110303c4143c0f000f084c16a401003d852411030807190301035003401031030184820411610002d40c042ca000c1c0d4211402a601e441c20056032400680300107144444000500d403e1102201c0950340c40750b03a18450101500340d80c000007500758880e00201d80021070402c81c1130201a003621404c000b0303046840d03c1e5810051080c0d5124020310018006c40911800c0d00c441c8804c1510a40262600d50b0780a070080d901c0d070400e4a0300c0c1c100e140b1002002c40245c0039910110305c10302d50b0302e180c01c1c0881785c010241001e0b081305003400b42c00810700c82c190a07810130300801010809071020051a020a00300304801a6925881140c40301d221450329210f554060620701c4010740d4080090112080d41c0e00001c4165550401c1e0400750340c02e4080d010540d405020709401c2c81081d2140141041c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 124444325 1250 124443075 124443079
    0xd0e06042c091c030b04020c0105040c090e0c1003020c030409020f040906060518040b010207030f0c030303150b0906030c0706150e09030c0319050705070806061306060e0108070504090903030209 85
    0x105440d51200103880b143c40303010028500e400f40703441c0d048241c42500500b0721070101400040c0b40c1041c2071221829100b044030241d403152545081004180464803410340c105945001500110181d40002290080d0b5074040100301078021801c0c152036601801210001c040460046550340900081902c0d076801c103102e0501d50616250000800c1802071003154040d040020000340e1165400707041000624001c0c10243c1180725042010002421564071030f00c01c2c500601e00c002c0e070203145103002402d407000c071107420305145101c99040100b01c0706d0f00f00707484002c50115801520707661801d02c00c400c103003e03d09000d45001d0514038803d0400100b0310240d01940c2c03129510b0161652040740440c1d483c418013484500d01da000300078011003c2c3e815946901c1303034042841c0080c6008007036155180380c54400e0300448031030b0700b12206021540c50010508400f1840b109014090b90f403504001a2241c0f021090305414850070348001030f0400e1060044030050514040100294541401c00a00035000300301c0041c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 124445575 1250 124444325 124444409
    0x4270e160911122701021c0501050307050102031204060219170106081302040b0d06020c100e0d0c03030c0309120309060609050906070c1406071d120d0e0604 69
    0x18951511201150034600390f8054485940d22110200c03030300c1009098040c44810070024000340709070001e0006181140d0f1540d0403d13008502600c00004446040e0301c828820b5100c001d0800180c0d8012050710300e50f80d61070701d03d00c000e40d60302c1c18602d02900c2810703c064080524464861403003500114854180d50411049812507a2a51000d03584120140d0b40c91006551b00582ca20051420380c12511001201170300c0600c2d21080f80d03941c90140c0e04203888881c0550044102049003400d280f1038416001c2004004100025040602401044074203c02a00309074031140503c0c4418001d0304903069603580052041810418000000c0041c4401c100882d034003801c9c90000642c00c1c08038000c19004490290180c1115201d0200555000f03008000813110085400c100d40440d400900c5100c1c80351a403a107541003070860100c161100c0d505403091592144841d89540c000c40d40c00012111540300e07080c1411480c06210303a0000f60b15010ba0b42c0139403403841480421954243c202001c3c0c00040003854184 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 124446825 1250 124445575 124445591
    0x1050106050418050910020c07050604030b01081b01082d0106110d08040203030a0e01020a0f050a03091d16050408100e0d05042403020904020c0f100204270e1609 71
    0x2142a503205603025040741c6d0000740d641e0f4a0a14503401000140c038240102c035082e0755110301140d030030b400a52043d9080f6103490010440000c05200081d40b00da461090b4100076072501c0b00203010094003401154160001c044241d0340a5041201c0302c0d800c0c28041c90701380a561752050001c09000050801040764051903040c0d5090500400c001401141c0c010b002d141003e0980004946000102d42c00701e046218401ca40740c04a110b86680800d200c1c080d5000d000c982c0e0031401d000e0240c1c14190f000c9450408051034501c02200440501134100c00e0003182410003c034825130403945809241c015140c14098019640e0070f412080d403043c40403445420a41d12020040b81c401c2d9602d0107180300b0001001602c407514a10030002c090094400c1e401c605005061941010120b0202e07000514081003d501c281d1240c0c0034000100139602e00411161000d61030581055800f40c8401000c4801c060802c4481400c0c800f55000c80c1c000465600003001250800c0e0941007203030080c0300fa10311908403154075098803 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 124448075 1250 124446825 124446869
    0x61e09030905030f0c240403120306050f010e0405090c031203220308010603020d0219050307021522210f0f03271a0c2a0a080c0a05010501060504 64
    0x251813564441c80946810000b180034824a044049202c20f005180c48200010f02c6003400042c01c06107000d68400c00b0244103030503010701201c00e45d8000c18450000c04001869907a0b1148000d00d503400b041e81c000c140b0f501d810720004d00c0c120300344c0d00403541400303032424080ca8181c03002e02440c820800b4100d4281c200000d941141c02e12011244050002142400103100707403800b98000303210210351440700514003050f5011614017044000a40400107030004107101c07540c2c2d8100300501203000c3e01d4034404514188440d11203102c25100ba4480c0302050b402c0210001e003c8019500c4001c0c0400c000d180401411424006040401ea1806003002c00c84e04d074280c3e61414070070302c220303500789450280900100e0b0b555000212080c00403d4100c0e402c200c1043c41050300032044a031140201e401a85a5449184401c05522052086104100c912402c2c400440b810080091625102d50700080c09959807824400d059007010075108018040d503003008000100b503948034000304119101075814650701560619 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 124449325 1250 124448075 124448083
    0xf0904110901081314120d0b03070510030906110c0607020d1103070b04050a060c030e0f010905030306060702011101050c040e09161401210c1e02100504061e0903090503 74
    0x462180003401000000344410040407480501310300510401c0045168081c469141c01e001c402c21403103105d00802c081600001a0040c042802d0084015140d17050070709010881000d00740c00c40300b08058551581001340b003019804215524050480c580da1841d072269210350f035420a4590703000601c50026944a400d201e030501c0101190900f010314a0041540c840c0156000094000d0303800d8040e801606d00003880324496888144a00d803008074a51700e40c080e0150405c143d40c0003103805a4101070107880000c00100440350300c16000c0741e1003a02c07244507000407540e42c4607102000103190700e4001802003403805076026204036121110300b6039884d41d40071819501c031001440056001114040c0a06c040341c3c607104529104401032403c610388660042d00590480100c16041d5152079460120544680c0e022100000b03440c000c000200c0c40448805000b5940c12040c5400c3d45440d503200c002c02e00300a400d80291820f0818020080c41e0a40101900303070041c18440c10890104401c00030001d02820042 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 124450575 1250 124449325 124449337
    0xe01050703080105090a020d0212101a041701020c10060f050a030203031e0c1b0310060608070c15020408060f09010509151302090106020706020d05030130080f090411 73
    0x103502c800c0306901e803509100e010f18024240610503502400445401c100c01e00c00fa100d4030401000c807589500389081c0e1403800030b240e83c04c803a8800c03d00f10301440f031a4041604590440b010581c0b00301e030000745608814028000c43e200a01c0300d00441240d9142e6081e01d800200a40c6e4801508210382030341c0f0420000c0e030071090701c0001c1d0590000e0003050400141d0468040d10f2151078264145045000041241065000c0e080760780006500c3d0010216420100700040405001c02400c0003c2400c1100c090440c00c0b00410b45410040b00303054400410034459005a45102c1074030b4103540f40d039150032500b07480e20b1045903445040f04115000640e000d405000d0345003d14580001303001c040444401005003d940180204000520503072000016150301031024001c01603907003c1c2040d1400e12038000d05042c04044010308000e8140014420408104000382684404182551180c0c007000c0e0300301c3e0038140120010703013200c2020410407880f4040c0c0c402401c034a4030441d81080b14040700200300c40f241c00b0300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 124451825 1250 124450575 124450577
    0x10302090109030f020f190f050618090702070b040605180102070315020a0c0c031103060f040b010605070303091220060906041403070c1202010305160c02013204060e01050703 77
    0x4074401c1000c00c3d24111100b03030704e5002038101c80140803400c0101e001804c18002681a000e0940000c01220b01c00300d09450180c1803c40340070349084075259802c80844005009580b1540c422004035074510700030041000180b4041c0c0e1038030344843d95a170001c1c2058000d1002c000b0100461054041c0b158400300d03646003074a0384802442000464444900000e412120f04181400004401040851390390400d050086114421014800d4075803c1410b08148024110102d0b16110b8028000001d07464070020341502c580e031805944540003800c049001d86080200a0840d1007860050040710b544008920544010524480d0741181d11a946541c0c1e00b004403814059500490003080020b40221641c101e007500031403c0340d040580310346403603c01f100036510504140d50003841480031541c05004150344603804800205501081c0d010150403003900d800000e0421240b103801d29006040c000c1c0110814042d0210494046812144410380ea803090140501160201e00c034180761350b100340d040b100c910340d01d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 124453075 1250 124451825 124451837
    0x4030503100e270705060c0303010303170112020f010c02091519080303130303230a050a0608030d0b0103020c160810050c0f0702060f030a090b010e060105071b0503030307110106050103020901 84
    0x446128140c0e00b0704020707600c3d4414000c180000030039075600300180c69a400a40042e5a0302d515526000e07000407803000c1030b08020350154004100005c0c10660524655070140d515900a0300e160004882030482010006c1d03000d00c1403418000000f0b040e030901144508281c480000010180030b07030944407080382c4a451601d50040001400b64500f451004070558400e06020440305405500c000d540b02e002030300301c00e41c000c8800801c03c0340d46050003140d030401d076224410007000e410aa0226103c3c0f041c808401904c035110580c005082e4444c1c0d040b698050540070941d54588580c6a1003040d0450610415800c1c0c0b20fa100640746114291091900560168590f580b408580d805800785940020300103903401802404060b08401000000314402d80404500150b64240c600c2c117020200c806030482d0f4420a40e060402c00c0340c0c0d8000085880d000c1d0003400d071441e41c050b1040d1030f42c58040140c20040c0c060001000703001203140c110000043c120034400090120030b4851004408a0003118441800039030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 124454325 1250 124453075 124453111
    0x6030f03090f0114040b1209190803070e1906031409010b0f120f100e1b0306010b090406080a060b0a0806070804020d03030e010c0e0a05041503080310080604030503100e 74
    0x801658003030503105071804d0710303802d280da10b50101c206034010b07410801802c0308100030828215410701c648030f4103000141d6100305680c0c2c81d480d40d00b09400000e101c1014000c0c0030300180d54030707541d440340405040d180a03501c000040c0c580300014003400c1c00c004000c0c803002213907010400c086018001e1807000ca4018051070001583c8004101035541940c2c0784196900507074807040240e10040c04032440e008c140031008a641101540c0a40c60050185407000c000c5c0c00c1940c7d601c2d0542c0e07000c200d207411074084241103500c500c24080040d00800d039503480464140300c0d40300034804001e501d420040b907015080b5a0400c4a0741c0c0c070f103072450f1240001c9900b00005582040003e0043c600130180040307135400392030000381400484d0344803402c541351100c1d5840818402110701c0d5030781c50030b0800c00340500b0081d01e0078059000700001500c03141509000090155002000140158028003000d60050524400b1180d8030304250401030f00c44c1d0700a562100314880b0055021078000c2010036890301030041101480c090745 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 124455575 1250 124454325 124454327
    0x4080d0912030f0512010303090302090105040903171012061505030a170f0d090b0103051e0a110d0507030b09010501050a05060702040902031609050a05010602160905060a030b010e06030f03090f01 86
    0x100c0c02111041030220900c83c000e21720750340384002c5010b140700791144500141140100902003d051307124902c51030810107640d0000754045240cac0e0040c010854001200e031074a202d0301c3d88100b103070382207403510090410318241448041d8001c130130b031501a4109010416200c2d4289a20b8410f0701101a0442c0750785560440c452868400034a0350070040c4010318284000d800c1e44100380d03a02468280c50804040c801401403010512031501d000c040b44108400000e03400c0c60954075480c99820144c042c8648180d404c10580f40c0d03003100000580e12901382d03041036489140c40ea650034404d5034000c105602c1c00001240d1410000051170650b08014109801c0c07221a80c2048003504a0800c204c1c0c15014406c01c0c0810841740f0301c5e01030b01a244000340410640b0304503421604990050340684219801a596a480c54201004020646a04000200725561100c01251900c105075100030101401140001a0040020702250107030780d0403410344046100b0008082c0c0d80b801741107803066100250081d006525 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 124456825 1250 124455575 124455587
    0x7061d04020d06080307030e010203180607060e1e01060503010207030512090c120d170705030c0f040510030c0e0f0a091a12010903020f030f03070e010e10020304080d091203 76
    0x90006001600d49400202208140c0790183e1101c5001c4d800071600c8010507401164402e980c20b0203100550400c12501e000600b4030981510240c00707407000045c600140710240c0c1244505c00401002c07100204000074800d00301c88070400e4072190340e51a140e0085100d15045c02110b40d8590183e80f0141008081d05640e80610009455030100d4440c0f00041a25521401c00581c03d440030311005d00002a407030f550103030116043c03e601c6008500f08508014000d0340103c2540c0d0400c1c814a072990f1503110701d10358100380b4071458118540c0800c604a100e0080b991680259112000d141c2c1e450101d10020410301c003500846d26082907004c9040c0030103126021044d403042d1030012109181e010f583d008140820020295100181c6441e519400a4001d05404109103200811900011480c140c1f414400b400c1c0d41c00040c040340101f000d544040050750f0703c1285246005680100002201ca0203408080d64a82c060f110301100c40c0521403860b0180d0b401035400c0411503600044070380710800c480c4c1d004c80315 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 124458075 1250 124456825 124456877
    0x111b03030904050118111207030506030304030606080304031202030c0718060e10050a0509010b09010309063c0606050d0c0302120a0c201507021f1d0706 67
    0x521051000108542d03490081c24002d00b2a8540e5151144401c0349010503142c4e0302c80e61400681040028190b000b01c00c0a4103a032000c200d24002402e40c840000003420b5119070780c000340605050480c04600c1000c0070005000f03ca21460000619100d9010240d0700e030b004e015010041604200001c20041c1c045610040b210403251000080c010384030115406103220036120b40455050605041c01981800e100c220090326040b0f5080d406580340c40c0650b84140b007079500c41c40c10151140ba01d80d0030406107070000002300e0462142820862000150300b142e03280120110b4060740c900968403070801400784078141c256081ca42e02d480c50200840c00400c058219042c0302010036908100302000310481e980031034001d00c1011004101000450001003031080342c803039112200c1d0003100314545100f60000711481c940f542080d51740301c41d50703401d0003d9003412030602406060300760014a54011041540c044890886048034038005541c0d07035144155a0324890050101141010b4412034143c4d12104103110 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 124459325 1250 124458075 124458079
    0x604020d020a0f0f140913060f02090d06092a060503091203040c06122903070b0c10140717190f0203010302010210090809040b010219120906111b 64
    0x2022076541c00302807800c0b80d895031001800c0c40c204802448a1074042d00c2e491407024003199807001d9400c0440421000c0028000c00238003280c0d58050b614101c291680507110b20381c0006045c0705a10251f418900301400342c40304212201181312041c00c4c1c030710002203041d801e100c5c8154884a0f03403d040601c1078401e940090400181d6208100900d50200001001103110b01e1068009100b11854094043c1c4034103206140850381c1810003003110302904240b00c10500a5668056254203c0a42e0340403c0c1070031a40d0700420040500040c4d04da030345000000b0300b04120030100740c0070410030361007030a004000d6109458440026024013580310703e4084014103e904104405440310b0010400a4103208642001208441c02c50b004001042035680500c10014a02030403101407000c100c4542c0c1c4c05141b44140507110384a255116041d070710a920030003000801100400e12103401e108541002440c008008040c0b1000501590000c91307028800c0d0000c0c0c504c40400402072491000c0c107800010780c8008424025 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 124460431 1106 124459325 124459339
    0x4180209070504050607112206080c0301110a050a0207120c1502030715180b040b010f1d01150e190f1208030a090303020f210601030603050604020d02 66
    0x1900c0c6c164000820414865070b07a00041ca01c88601084c900003842a4901c0445d00d40e0302c1e0700c40390507124000d0454241020000800d400d03500012110100ca02c000e0040c210300c07a0284028101601903401929030187c0c4400c0b1000a664500c030b8103585030703500c0c201c04002002a0b42c011282501301840030714640391191315a02d01c004620b42d8840d6001d55101d010910710080d8100190708a584520740311304900741420469600902800340c11414041030a0000707070b081003111210140140080c007440280c0c0382045031030081c54054840740520551000008283c1c2e2041c1300e0080161002404211041c1040007461160002d9081020316210b807050f80c001150119003070700c0d88000a8100451160a5490120041d0046c070440180c000004280d40c0000c49a40c080000507080b00380241c181643d6441c01102562036520010b0180d811640214015080032400f0f0a56107002900c80 = true := by decide +kernel

theorem cover : BRFrame.Cov 124280575 124460431 := by
  have h0 := BRFrame.cov_init 124280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 124280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 124280575 ≤ n) (h2 : n < 124460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
