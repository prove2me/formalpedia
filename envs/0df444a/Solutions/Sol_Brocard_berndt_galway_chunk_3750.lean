-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3750
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:34:10.726203+00:00
-- url     : https://prove2.me/submissions/5c0fb82d-dbfc-431e-b98e-754f2b7741fd

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 674280575 ≤ n < 674460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 674281825 1250 674280575 674280583
    0x309030c0b0114011106060f091b0d200a020a0605270304150512060904030309080c0601062a08030907030c03030305040c050901150f09210218040c030807061b080402030c0102 77
    0x1f540c2c003030010040400b0050400a80882c05446511140009440d5840d002c403000014030045100c80c00c00b00d200480b07084e000c0740300000103001003071504060110030005a030108202103115084040440d036a01c0390102c2d601d80c80d50f0300005000080030351005200c07010020000c0c108450708220120340c0b50940d8481560107104e42c810707031903060307046a0000e501481e00c1e100042d0807900034600003600a0283d43d601c080c961100195000d6a4444801004190b9000b0055046902c3c4200392800c42d0310b0303a003840c00e21a001c00384010700f50980400003802010781002048000c41e003100c03803005400e0b502e00340138000300702c05ea60964001c442d005001c00d441c18206580350485011511000f01c4044031142203500d1070f041d181e070404001d408100090000c02c2110709103841c65030540c0c020340540b40ca104110150203180c0c070711000c844100d13040002007100e080510f41140e40001c002c6aa0b442c807440c0c414003c04c0749160351200b20503424091090140d202c1e01c8603204510a90488894181400041e40c1d6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 674283075 1250 674281825 674281831
    0x30608010c0c0b010b160614090c0a0630060f030b060405070e0d0c0807062606010504291818011a1e0c0d02060c090a03030309030c0b0114011106 64
    0x1000407500401c8030701c0705c0b0390052004d081e160b901981c0c480c10303503a55113080d140043c810b040d4401c0c024091000007042400042203090003260781c003110615191004e000c980c10074900d1200903000c1480003a140c01001040100545c00d043e080043c262141c488080e90b200600051795642107081c009000b90510307124480c00b0b1540c0351900941008a9410018098690361048454140740b0381e000410a108100550240c5100d4546681a2000c600c2c0321900340719034545200013001c15800d126260760820b00300c50540c0c1850094100700a540641030000c40b07004154404501c2d8001940c840701d00e400c0b0b240c1860114101c51540c0404000c0b0032007581c0580078060390b03042c1c0ca400141d10000115420051030010101107803048000002200d14041d6084103810200c80e41080d45e03003140080d81444000d0f88104022384640c14040000049540e1140c5408004d00389680c80041c003041c0b500400c00351641a500c900804080d6845a2000c0c0a0866070f40d50380380480c0403411780c03103036001c004503640d48 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 674284325 1250 674283075 674283083
    0x190203070206030f061c0503031501170105060a021f0c12150b16050a060203040c0608040507050112020903030a02100c050a0503060f0d08070f031806081f0f06030608010c0c 76
    0xc02d64071520b1380c6014004024242d41c1d403141440015136488146881e1100c845802000a1600c900c0e213842c20320a0354442e042c0282c100300c40f49040f42e145d420480d29180c1919000d480c440c0c1c5071a48144140d150011294000d0703081c42c042030a9481e029120f41112162690300d5032000140c1714005072160990b6820b070040d81c0d4180410f8070a0042440c0341d07000d0300200d0b07803008c041c0040070001d44410741071049214090710340c40e4002041101b0b0240c402c0b40100204114500a802441d090721403544400280c0202c0d0304002c04500710994011442d015600c40d008014140e03a6901040140a95a440204c08650070282801c045083c000e003c1d000b6509060000d40760180346990780f04c208800d89980d03041065000382e00c7c5201c180801c0489000e4600d540c480c00c0c1c4a4070340320301420041c04c1c5c40d6002e141080c4010242e2000c0c4880c0c0d44c410140c0f5003144080520321000c450001202d4503294058011005034101d2200000c0e00a5241e0065011103031500001c00070042050411110902d1294001e0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 674285575 1250 674284325 674284327
    0x4061805160b030915040503040b130f05030c0303040308070204021e130f080c0105220e010806090712060b0d02030f01291c0302031c050a0f0e0c010e060403020a0b190203070206 78
    0x11507040c01175510240d01c14415415030f481e00d0b450344500d402d41d80045000e08284460202c06108010010107408050b0204400078010000f0350750000b543c0348524000202410720210302c00b02151100d4043d2200390700c0c4000d80003500305d900003a5640039005003c042c0000c200044c0001140000034030224141d6007007001034618041075200545081d40300c0e0649007051001d4919900b50008001a850302030401d286116009500d4081d130703186045400f80c5455510b400c4004104440e40d00c0b8080c180d195540640f000c00d220105000090354040c6141029405000d4040710100070311043d40400030b42c510300100c0c820350b0010780d460074a140034030410b083c0d040880d44132841c03241d0300020701c1e08810314864411686441401456030003801195038080d44142c0d25101030040885040c011001a020000800c20840b044407000c140e0b2000c0313680c4d0660500910905402080e01c0310000c40340955009005040b0f0255941012406540079079807407090f14440c0d1210140b014800300c2112080b039001400340d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 674286825 1250 674285575 674285593
    0x7080c07020d0c08010b0a1e21050706020f010f0e030714030c0118120c0c0311010c051204140904082506090c0911120c0304061805160b0309 62
    0x1800680c04810140d0b846078840880c1000102501c10f0354015006003000411080321880a01c0000443ca0708010f0714080c2c0d9001c03004074040c5080700302c0200e0f5980521060030401d89407242c0404401c000c8050300c9401035440101d40c59400040d003d85024040000300a81c0036007406920440706503028050940e0020043d100221340c0780c0440e0000c2010010541c1c3c07410720004140b80c219034450305203440c155000b04511061155003401c1071020029404c01000100090742c540d490700d009404010075400a90641001a0340b10b941e428001541c000100c4040f40520540b0300e1103a08035108881072403030403403407007029801c00c881c2d09400b85604c4141c40d0f05243c0340703c0480401288111200d4101c0317031703058942800300741309018041c56240101081c42200742018034100c29144060807281d882e15041040810322039615400307560152064180a0301e81d101c03031404c2c4000c1c1c42d4050f800074030051160007030010302c8400300da5aa00c0075002d21101020b00e44e1154082101c0c00101c1e01c40800381c014250b2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 674288075 1250 674286825 674286841
    0x5151005060403052a03060403020d0f08010608040303090c09110c100b01021002210c1b0106050303041710020729060f01032a03060801050c04030f020d0c0e01090506090a050708 78
    0x215140340c050054500240301704150120740f07000021101500142c0c0f0440700740310141e8200505915141c901c1c50102e000f0360420178080c2c41008080c2c8000e0400d176403521100d091207581d42d60540130b089020f00030311003050140755800c1160030015102c0300d140104003910060071054842d88101000c1038019100042c102c5370300b08000d400c090220700c1e100400314802d091000000003010712035074a00c007940351a000700e4154015001010b2007180da09a151070000e01c010368000099504490b00c00c010100d42840e0854800d003050003502021807158008106001085440441c0001c2500c41d111365000841d10800e2200c0074002c01e54000b82c0000400b503c041c0d040d4429084100c95015604560f0358261200b031105200b05121049803001032380d218400c3c09004000c1c05550740000302090030030b06140c00d54490504031881d4803c024820400c0c1d5850f001000010384421000700301c131504642c402d603541d00000c0040d0208481c2984202c180c00c0c00148048054170032107010300d850785d452100580d0f401e42c1d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 674289325 1250 674288075 674288113
    0x180209130c0909030f08070f140a0207052e030b0a120f0203160801110702100302090307090c080114010503130201270807030302150f0606030a0204030515100506040305 74
    0x30155884400d8400c003180c0100c0502841c1c003082d02c01e583d132030702210341118000c0c002c50f0050640800c00c82c40124040031260b02c48400c5020b5030070350311134a0342c07803140c18001ea280c0b001aa00c6140c10503414084000c0110f0010a0018500c0c03145121055526a505040741100e5210741c00300d611081c0200c0601400400301210503101c1e100d09015480c401c09034000a10b000f003d012039114590403880306108041082c0900404850200e10326424000c20f94002842c007508514030004040d4003240c4a000307580c08002072001401440001c200b40341d0340e00e400501061090140c00012801d24070012100d5105008070380c407030040c111841d032800c001a40110f40558407090ba590205598030140d0101c01d40d44e0046000900800300208102da103036180c040e0602515000d260180d40008082050300061039007446e84c020021a240c6603680d9170454910024069a0400345c047c0c403d0100e106090804481d020b405154480e60304c050003655501000124800c2d030000500e00d4010480310758890f1f480c01 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 674290575 1250 674289325 674289361
    0x90c0a141e030a0506030d02010b06090906011e0207060e0603090c01120f0e1509030a0203180a12050c040b040b0303220302030d090603111204030e030a0615050103180209 75
    0x1d503030307107240c211010303410070181d007007602e41803800b50b81d0b18103120762032070200b01d420b101810b1030009000c1044440b00203240307030280d048090f018100c180b000852683c401e00b84c01380c403140c0200400e41d5090001c030009540b00b40c0341c013444003c10390b25002170718181b4200e016079101d40500402800140d800030011148508011400ca03091500c0f83c0c4d00d040c11740c0050040c0128070807604010404a426107a07145d0600c040540035804c190800c11641d10056030100881301c5c80d01c45422806d10400303004021451109a582c0701c540201d2070801d20004000010074510b18071541100d060105141c142e0401c0700703d4042c40d515a6260f84104035013030006440b000d2169000c00f0941030010300070354030740210303040100484014001400482c001d10503140c26105000c0b0801040c04000d082c6041ca003c41c24034408042c00140c01c1c491018444100342d5003c0001030110356101c0b0042c0240140c100e0411102602405050b010034107015545207031500c01c106203281303c1e030014002c10807a11540c0c1e0100c0c0040400d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 674291825 1250 674290575 674290597
    0xd0c060f02100c0309020f0411090613090504120201051506031909120302030106090b0708070204050c0c070303020106170109050d11030f040b07020405180a201e090c0a14 75
    0x41c01240c0c0d05031080348145900341c3d09540f4040340d40440c51040204004034503030458820382c5070102c0007100198400035110581d800391051542c501d81460040d441003000c0e03011502d401e09100400041098040410005042a400900081c0c0f038400c4c90f0b014800140d03412603040078044c030000711481402c150040c03d061085100160001c81a1a400c801103040700d401c90102e0f800000410100e030740700ba504002414455480f034103103a190b0b580d80003140302e5400c020340300d1a16040030810317000c0d44070104d550070014102221441c965074036001e03021b048148120b03600f082c00c07142c1c1140004810b0060101071540710014201d5200c05034001e5600c440744c8554468188070134007440c034620b14804028030103800392060f0b80c4e8542450784100701c00c0e214002c0049022905400100c0100ca000160a0407a203070710000c0c041c1802c00310400c030100c0035000032516a00183c4440701a00c2c407100000520848241a6444c4405913190240c400ca18411441e404000425440d10742690a00580140610780e0320 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 674293075 1250 674291825 674291833
    0x803041d01170d12090b0c0c161a03060609120a02030105160206240306010602210901020303060f040f0c050403140309011403040602360a150c110406080d0e0d0c060f02 74
    0x3c03501e600750b009100b241c3c0e031010300100182c5611004c6c000c0043c1e14660480342700e10800035081821007131000003035100001c401c15010002c5040c47d03a86000b82e4500080140150390f45036901d6a82aa40d4070801d28144d010394a010042031809074448284480c165464005004e01c0d22072504010080b0015016505001d0b0203030310100013030343c0a02c0703103500034400c50340180f220103082054140032000c2120407880b02c000c1081070301c4451741c022050780d41c0480d08a50540d403032540e04001c10040e0801c0c140311004980340c10484882c10350880080d0080d2800b510300d0900400e0b0100c4640d0340e1748070300300300c80780841c405590400034920800011941305100310809401c00300140c07921180c400400075a1440c6400c41e035901034042d2030201c8640c051500842d20f03408940d140c80d101034015031054044400300040c0e4102003003800142d0104114480025000b00441380d66518955150610916141d00081c041079448c01c03680341200c9150314540e0030048501c022b610305441690100e260036068400d41c06 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 674294325 1250 674293075 674293091
    0xe060c0319020706030e0d1d0d0606092012010e1905010f1d1005010507230601031a06182a0910081b0c070803041d01170d12 55
    0x2515521a10204042d0000d00342541000340c0503040d601300125410303065110b030405600d041d500c82c4d1501c0015043c54061200b00b08003a020840010301440f003c5c1c1000d080010000340f450040c4d110081c110040409a01c0c601020840850240328422110039100350f001c0051101d051480ca0140d001402520704d14130a0110343c01c150b081d00d0302644107000e1513007404c404000c00c0405200391f1220036031020070010503140a2011804a0f842401254104080482c090781000304003010018071480ea800c0264001c020091002d41c1d803070090101321580d01d640204e65451801190340240520b80040160560707003124050710030460350040a098174480c0705145a40d00b103011010751080510549145681d8000d41e401b40300c00303924251400c8040220348410012021001009026090800c07241d440d950340c01203191a143c82c0e2070381c01121590200042c001364030342c1c540184d0000e4540403541042645c2c0d82c0d42113202c0600010340e844909030080c2e00c0c8010300303a226280b9a5403c1400400001d4052 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 674295575 1250 674294325 674294347
    0xa060209061e0a0905040c12110c12090109170d0521070905030d0903020901330903060b0103060501020309040509190803150a1a0c01021204110a0501030203070e060c03 74
    0x28418102616042c4000070b01d0009240d40804503e014140981c1d00f804140500c07080202090850901d41026907903501c3d10441d00c80e510000c07a08070b050500100e50400001039900131040d4060504107001c01c0040000051243c070381c05032040e04003140c0c4094098101e00700400e039240d9000092110f03280308070031000008207001d81c1c203480c084e2606d591418102400c000501d403038a41a5071807502444440b4804200696800a081d41502c4a10703c540d400d01c1d80c18025400740112032030083c640180b0b80019590000d900032004001c4a0280100b8070030000350710015401c644036030161a005030010403041e60300e070070729820154000c489181111100f08044c481c028501c84040000c480c0382d2400010f010380e0b40c0c0500101100140e040350300120700d0346422a4a04c800d80b00f025564140764010480110542081d41075403000343d5125044001c9103094944112012400008035104060382c84c1c0c0801c80354400d1007035a02c26540c5482d90884224008100040e682100c405680c09203c1000342074840 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 674296825 1250 674295575 674295607
    0xb032a030a0201050d181a07080a0203060f01140c032106040911040213030605010602031201080f150c090d1a090f070b13090903030b091b0706020703032003160c050a06020906 77
    0xf0381942c0c40708542074100040000c080361005001d0301c200500500a00c0107996030418840700824007401c00400d16430340c0311030380c08060080c2080090305000c0403070081503080381460020303502c12a030b6064600c0380e91050104012504480340c060300c0e49015201c0300f51581010342c01050079065048007040c40a42c0e966940040c0c490903007002005030808104c10320131000f010145400350803c0341c0a4008600744c0030700ca41c8d41e4400800f990054064040200700ca41807203d08443d04010b01a08040380a072140c205000c82c4200710b14140900e01e6528005084503a020039030601c4004079101820340c076882d0a006d040507410802c150ba24028000d036001821a5041c42540d000380c0c400c1d100425100d039400100108e60b6030051948200c00152009250b210170200100c1c0d2000303a00460040c1c554020f410120002c10f00c1103011500c007130078001d10914000790980a0743c070607280725481c10380703804400c1030445105101074401071450b80116001c00001d501500904000240038040c14282204e00f580300e944 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 674298075 1250 674296825 674296853
    0x906040b060102030c0d050c0106060903080f07022403190507081504060b030a090c0b0a0503010513020f0c100e12030a0207060e07060e01080a0228030b032a030a0201050d18 76
    0x400c10019400d034107080280501c0c001031a95050007020cc5140d51076a503038510511421189002c0005045000c5584401d008100c44c6d1400201c07500420b2040c204010550040d64818081c51400f0404041420176000740c80c440c480650364101d6580303640b04112181e2500002040d4801d0b11880040b441a0908004d14800c40500b940842c920405007003110041c440340d000002c40600400030002c03070541090481e4112a01950f003005051a1003500b403009010b07032041c00c800c03100000781841c1c81c202c00241941a15004072410000002100c201c0e07135541c41e105036030602541041c40080e1403a001036002e030414030300480020071649009240581028201c0d005072010030140e1403400340c1542c3c00110fa44c1d01c120840c80c21441d00402c400c4030000328402040181b240c0c0700184000c0c0b44244250840080c88002030b04a03900300f103010410710300c500d00c8010400031900a50b030b141c55180c517000442801c0540c060710390300c0c0f41200e500021070241c410181c00450100150754a070000a644c400c1c0e07001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 674299325 1250 674298075 674298077
    0x131a090c0627030a0c0611190503070611160609020a080d120e011415280801050604050f041b1a03090615030c010302091305090a050609060906040b060102030c0d 71
    0x1104107144450002c42c2415951401c0c042d0f4041c02c000f90029040601d04401c0e201d05080600644e41d4a20000380b4040c0c0303420007180c00f0244c2d06410307400c201001000c2d000d0300d8031480003409851a0741400002d180104980103071035281004644020440c9a404914510b0020385a021800d072168425490030300040fa007040000c01411020255010302c0c450701c86551001c0c40240310700c8144002d5484042c8003e410800140e48840c81740600d541e0b2026841c81801400004043c48540a0564104015213209585040d401c200c0000c400303160501c9010302c50941442100d4103503c654031200b10707640007140c0040005a2800f000302c1c8000d240405981350016408072641d59290502205040180142c81d020450022880e400c2c00da54000c103072910325000178038005803a08040000140c400103246e500864092504d414011807aa0204000c1000c41c05081112541d4440d01092507070703104219200d40c113540008010800050920441c00c1d08610144104c03070502000c104050f0034225000d10b00c2d0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 674300575 1250 674299325 674299357
    0x40c080c0901092120090c09120d030c11030f03220b04080a0909090c060f05091e0901210b04080f0a0306080c06160b0a020c07060e010206131a090c06 66
    0x280c10005400c5c4010990385400c01c0f417070351103031104000c035040040103001c0d5640d921005c0380d001d400f922810030030702e28140e0507401c8416003011407078041d004050103090000026104005100c1c041400001c403010381618100302407941d17403078100e000c3c60b8400d601c50101c0104054581c003001300301d9020a860199020304034940d80d03015416805405a0515800200034600b03000540c40410820024417007128001e0502c042c2011000c079045805120760a85180c0c0320b0102100741c4641500584074454444064620b50140d0341c0318210f039200860240b800550944440074a0000200441080c0c1c0d0000c1c03098600e00c2c140000d1001411098010701200b90000c1d94070750003042a064108005c080101003616a00c3c609004910140e9008102e0100503200280401c0410383c0c4105650448081c0e490900a0324403281c0c60701801400d40e03210b039072311500612410002ca004001c82048061100d544010341c4503030a1902c0711010b0344e0b00801003064165014501d240803441d12001c001b400c620070745c5c003021 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 674301825 1250 674300575 674300639
    0x20304150806180105031b04060503120c160e28051e011403030f22061101060501021b04050402040b06030c04030203070927050321010e06040c080c090109 68
    0x1c0520181002c0000750f100802000410075520b0219402420034254400c2c07954814211003c40c0c081c0455602c140d4151040c0c0140c030200c44c031510060b1000d9010319054400d82d07030329451404103030030341d90144251709000500841c10344200e21217008440d0f80c004c1c20701b03400e60314520400c02c01c0355422260150f00c0d090482b00c20802050400c6d0180c050300c2241d42e440c15042c1100f0100b50740e40514089440148400155a44805010f000101102e0900c490301c49000e91201c20080080c0482c10400101750b00704800451139600200341e0100001c80c103107015140c10200000c220141801034401d03600150b6a0f0452901038603500008c600c83c006a1410659445c0b0354030516142a400340d1002143c189842041140c07208004003003000d1980c482c5480c100c0302910b081440c25407150741c000c1119034003504040ca20070ac0400007444d04940070040014041d90f181c4003484240e81d1400c50500c009220a40000c1032113000c10302500e4006018902120071684800b1b010700031010650303040d020690541c1ca0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 674303075 1250 674301825 674301829
    0x60608060a050403110f070b0d020d050109020a0f08151017010303110f010203040b04080703021f060302041b090e090f19050c061603030906090213240612020901020304150806 77
    0x1805e507154040310028001c0c00d0031540d40c41d840c0c000e64003841100b460002095440850180c064a502c42e400c107208103c0b9517504c1d0300c040025840402c450000c40c03080015550264010b41050b03104090003401a00308200340720170000d244004149903424001e42c400e400070a07910080c442070181d41309071540d500c0074008000d803a2825400c0d0004010582c01003080100040c420820b01780c0040d40840c00341c1d20790f515482c1c144e08144120048210b0481002150a60342849810507011240281d80811403050b4842044c040005103400100116500c580200a20060a01a03551003038050081d2013107415480e008a0400b46070561401c071358403524245805000060200a403103543c2103800600e45008070025540005426001600785540c40c201142801050b400000c9440d60041c44040c603c01a0881100200304414a0b003030000c1031aa25414000070725503600042d507441e0b4403580c0c0180b1000142c0400303036021a013890f046010078080003603c0754034460f101c82c1e5a5041c0d1515252362501c102 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 674304325 1250 674303075 674303087
    0x61401030c08030901021002070507120c09050a060e1512101b03020a0f030b06120f070f1407020d2303180616120c05030a0c03140c060c07060608060a050403 69
    0x100030050f0304100030051450380c00085000c640300300780c41d0250b203818841c03c00608150541c0e1140801441e076071a17410411802c00207260598192100800c010345031907030303001c0c111181c6024024450b840304011458129503c0d42d203000350000241021748862041c0d034401d040c0300345422528030742d030b0311140524910891005224100134061508500303081005400424100718103226205041e95048801441d0316258203c401c8403034222640d45041c100803410480c44002202c004002a80304003500d804940305541d88a04034444040c503504243d01d580800110a80a06044030342040303580c1001a031244da00200015249684091501d81440030541d888040c64921010301c600c4007000b081c018000060341640d06183c218450f9030342520704610940f01c201e019a0084c060b44400f0808100342ca5101c000211954801e0340c451241c0280c5190b00d06050180307021603022078001c00001442641104003600d4080c0c016200400d155540c0c842d0f4908002e07040c1d440210f82d88d2203900700320605400c80 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 674305575 1250 674304325 674304329
    0x31b1603091a09060c1002033d05150702030d021c0809060a0c0c021504051528020a0b010909140a0c0902090f090114120307030203040909080403061401030c 69
    0x261502c0c8004141c00c1484031442000e45052181e10003041110b0403100400010b01c044050070400c5580b401c150742414218100c4d51002c602074200c541c6140780190305500d62042000c801031101068a061004200030f1039a0b80b41034502c00c5e00d0078402034015030303000c02071031000354240e8003e40050000d0100d00d881d40b20080080605010080c8103101e81c0070000a00140e1145450900040c25040741c43d0803140721049074400781d40080d651165a1141103000024030840d5002c40e218404120f1154403940d0501802c0e00ca03031540c1c0000355000c0340101c6018040b0154807086c0c81034801c81301d00c07a0f491412803c401c0c1c20138245103035506224004c1118160203004484804c50090034038003019070350300c44048014040e0203000c9030045aa828661503c40703c84d105604001c101c03194030b684401e0b800c481041d8040e000780c850b01865403420401c0101004407041c2c150144d0265190500341500b250251142d61800c40b01c41504201c00404134100e0311990202c1444955501800d525500380385a501941e6 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 674306825 1250 674305575 674305589
    0x3120a0b1f211a0d2103060308130f051005160503040b0d020903010b01050712110c0612061302090d030f051e120c041202090c0c070b0703030f150b031b160309 70
    0x44c01c1000e000c5500e450303891504034a21142210b40628105089002e4850380c0c0c030003410f007040030841344c3c4101030103800c1000f965103403030700265070590b41d40c00c003c841c07003440d01c0c1003000c51401c0182c4007842042030550742840d13001d141141c1c6025983c1010010070707804001e0207170307881d40e011500c8000352a00b801f0302c20100f1800d2a0550a1034110b0f260005540b8400114405000100f50506031551080c010f84a550750000c0a854480724481d800c2d4451440c1119034500c6449811204c1d43c0c0800d4030300c01d88006210207400000300e2036060342c040c0e0f0a590403141c80c4046c84000c0c44007107040b00d9219000c1d84000099051262503035070a140710305c0b10550103003507103400038070500c4240030050740004400d000d9030301203540d04420f4803103074a405203070f1040c05490800f5005035000895030010b8030000b050020b10036a001c008140068040900b1074407032f505020b1101c07560880800500075100c028540140428001c0300c00307490343c01000c456a60080030040c01451401c0201c00505400421301d400400b00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 674308075 1250 674306825 674306839
    0x60103050d11120904020a0215160e18041401090501060b07030f09030210031a060c07030c09021305010c02060d0504050717030301080c191703120a0b1f211a 69
    0x220f010303c02c483e402031a0a40d402180c0c045010000e5500c2080303520b003842450101e0b10078600300220644200c440b524104004510070f411100003505080c00107290329250383c40c46440c0b40c4c43e50303561840c400c04c0c1c1e0006003620b90748070140140481c00a2007840010302440101b00c0d95400645400345c5103018950800c2c0078440c00610030401360311100c40c042c3d00c00801e40b40c001041c0f5402c5003804e54004503109a540c104201103031340f26200c4000104241a40d0103803141800d4641ea0b01c2c0200700341e00ca41d00340011034200c662400c00c071650240c015040c90900c0140070508001000c03410b04121542143c09035aa903122410801040cac01500d4240c80325960080910300d150704140d502c40d9904000440140030305003144111401c0065181998007070b00244840c5204609a441c00568030380108454411080c0352802003981407003180b20703202c44d142001c0c015611403a40391050401043c023543c0300d40284184110101c1807685102c504070f030f2080c88000300083c04090a1a0501d01c006041d4206000d012 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 674309325 1250 674308075 674308093
    0x71d040312150504020c01020714031305030f2509050a0506090106020c0306010e15090103080705010506060a021b060c151b090603240a090b0102010c02070501090e0406060503060103050d11 83
    0x645100d11806543c415100541d8600c00c24804900a02c00d003d00948101c0e0200403802c8030000c00b00042010000031410011a25200c008140e140c0400c0c0c00010760035440360101c5100f040321980c4545580f40a85c91180c011951340001a054807411100d9180440e980e004101c0b1074038040123100d002d0106480100b080c6060080420f58641043c0541e0701c0300417007400010300d081c008102602525034080c0ca6054a942c0d24613140900e070300001c02c1106c03294280800a0000c0c2801016078001420716801005170700d803d200341d503001c801d000030740a80180301000b6042031700c0f004000c109900c00340184100b4280c1741c40c0b2000c80c801807090300030f0309140030b007000f038104a560380d4030680e904070f4200107003528207101600e80304490b400d0140c10707540c025111480c0001c098409600040036008207070000e002c000a21001262910b0b51805120b011903002001030190070502840c890f0320610034000040c00c280c448000034513149090b031040741e040c1d2002008000d00c580c80003a030700d5021600d100034014a1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 674310575 1250 674309325 674309351
    0x4090e15010f2709020a080601180908070305090d0530031501050309030c06040b0403180303140904020c071203140901080403110109060f1a010504031a09071d040312 73
    0x42c0d03c05070054954030041103168807041d25032154401950040c0f543c40c50341d035100601c0e0303203130282489002c004140220f10580d121030b090151620b440d40c481c6501e0b261581940c1c0070b4680fa00030440c107a811240c02c2e400140010800c10004260000e80d0701c1110700309800c99130904a41e5180903200c0480394003803082c041d0310941303c19007298054090030706548a6031450340640c03860085988160107446100240320500841e0b5076000d0045000c0c4c0d80700005a14011b4440d1003070f480a10000700000ca042009524900302000600852036004102611300b0103194450380c0307405100d81103004e0000d142402c0804054001c100c003195141f02100d1182800500300c00642602c8000f8406024001c441040120007039081d070000e18901c0d0f120f00308110f400c48810384031006148500c2401ca02c4444030010314019800380782a58110f0341d0045001c01e0313103201c4a903040202440a024140107102d1701c1c101140320704030301514881d1213040304c500c00c44600c1c00e07050090860800c90030103070981d4500b044a150312 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 674311825 1250 674310575 674310599
    0x180b04170610141320270f1c08070b070f180618050402040f08061303170705120f0103150e03091306051c0302010f0b0310050403022104030204060e01050619030204090e15010f 77
    0x100c042380c00404920030703941c0ca42e000d150550b038001e00039900040d5101c204441854128000ca546a130352103c0700250441c140c82c124002c4103c0502013007455000c11103a1304c41c0b6078601c0745801520000c84219070b54404141640c005400008034900c0c0500c2c1405240020407185511027814503c049041c0784549000d0543c400800f50081d10f40c85400000d02824051002c0716255003044071804024500801034901d0106c3c2808219040d45d582105451025a90f01885c404021002e001e50300e406450000c01c881802c05041540507161200d10000d400c0d601c0d52030407a01010100b405111100f00c6d440c000782103034444103542d82c98601d030000006450300c1c0043c014400d1061802c0000b40d40d1510b003810b80c038111480013650203415049400081d804000e0700a801100c0c4280ea003070203100e840d10500c00600c030090041e00e40000d000e1104c60b0044071a205062021405410018605620340d60b0250944000d1000c14110f9800307410701500c091141c40c2450300606c1c0c480000c2d5441401d0040410344 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 674313075 1250 674311825 674311849
    0x308040b36190510050c030f040b1e04060c0806090106051213020604030c0608160503060111010f060b07020901080f03190509040513020916050a180b0417061014132027 74
    0xac40386a000141c0d000d6040003400480e081c8120201c50b00e03d0302d890400050009441e2190004040001042150610080c400c0c1030f1000341d103c1d41d0905541440038410000014504440d4005001e11400581c0f1000000e001860003000d8481109051680160494001034144020540000021080c1d03a5028007640e40000091802c07031560011408640e001d01100c1c207032803c4036440e00000007600e0301d50300c009103030b030510a0720000260380e6140304041e1184032403c41075240341c004001b195128050340b40002c2c00d030f14a90524504240c0034602080440380102c6031800300075281c00200c03082d890b110b42c0342a0310000d00210040f610890300d2005100d03019a940500902001c480c0340346140c100100b8160161101c403843e80c2e26a0780e10f565000080302e0211010050f80102008685070402c504140001e89460b1510103a00c5981d660920020314114a04040707540c1c1c2d5040811004a1000d08440c18103140e25034880d00da007124110b4066500c6c50400409515110580c84489521504071b00c4070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 674314325 1250 674313075 674313083
    0x1b0102191d0f1201060906050f0913140a080408010501060e060924040b0f0a1107140d03031806060f060c150b1c0308040b36190510050c030f04 63
    0xa1081d41c5101041d8041c2540c0f49491095003041c00c04520460554489811200125000d404c0050a0030500c0240181a200522224401c1403500d002c121803500800c240342001c1c00721001003015803150355080e0469040300c03c140e51290010001c0581c801e154900040741103e4171490079502d0000030750500c0301e800e0040c0000c120120601e41c0c07d400c507001d9400030000710b00144d558541341045060a5032088104001091038111000300440703001805000707031911002481c405450850030014007001c030b41c804a08240c0c84242542015201d003109017401c5101d100c0100706503040501c2e554184425400a401300550103800c0008981d4200c0c109516a02c0468001000c180c9000825004041a0700845400c441030300e00d01c0800d540683d010344038a00414440b141c94482501e107902e004804d12200300e842180140b42c0040c000810700916008118008803105003200114100e0b842001313202c00d503444d030000c15080000d0b1105000b540e41c0303c03000c96030607840d524004503913040c180f0380a00060 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 674315575 1250 674314325 674314339
    0x4291206010c110d08070c0f03050316022b0309090e03090d0501060308030117062805090a0b011818170a020106030b1602010c2d051b0102191d 63
    0x1440003503c4000714101c4050300f200c001c403a0900340b6001551282c00304855110803081300081c07081115480d001540d0340310001c1e500d0441c0d00c82030a691110f18100907640620500030140a030000050002c070741905060100d40b20025505000d01a40c00582c02009014100000244103050202c120360444004407042444a0210309085004010a400c01001c0c484c0000021039112255414100001002004c9601f95500c7e403124110b203040071030030300c078144c3c403c2c88a0028056a0350000781d4401c40084c01c440c001d40c1281c64a841c40c48083e80b00080f51201d8894080034203002c1c0c0141e091001c441c203628450810384d55101d80c2420800300399105401d5001c181190181d1007034000d20000c42d0043d10200160500051180140c074001d030940c4090362808a45481c85806480ba42c003034401e415280b00c240221100810704080e9400c880401009410040014042c40c540c00c04010082c1d0b0740001030704c8524032004a8110580c4021260a100862038060111404081016400c0b1800d031001 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 674316825 1250 674315575 674315597
    0x300e030601062718020903070f060c03051c05010b18090c031b040b03071707021506040506030a05100e0c0a0b03070e0a03050d030504051204032d02060429120601 71
    0x80c0c200c090f2950080c01101070078401184c000ea0703d98014103407000c400c4055854250340c038110346840100a01c500c1010900444039240842d004001908400000019902601c0c002550030070031034109800130b0520003004900341455100840d00440c1d80001511010114107018003c0345150000030100c3c1c050469036025044014408402c1d100100f4070350041c04d460341807a801c0684117009800c0345440038070b60703940000c5a107403000801940301224541c0b8982c02c0d40f515000d001c09070000600898161049040c20030000b2001c0000c480351100c1074a00080e10b050100c030381d40c14400c114042510840280a051111801c0e650840e03801900074107000440001200120ba95420194005401030240c401c9e081170258260701300520445c07245081c0c910928000c0703417007002c5000c1d9010240030b098602e981b40e81844ca01d0940c00350480f03c00800701001c1d200e50381c00100d075507015802650b401403101a041d803003800c2044a40f590f514400803d2401d003200222513440d161340042c621410001c1c900e80b2 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 674318075 1250 674316825 674316887
    0x3190b15010203190e0306132d02040b010e1009080706020601080d03020c070b0304050a05071502070b0c010f0203190501080123040201110708010e060117070e04300e03060106 77
    0x8007040150301900351f85081c5440001d05000b0310000300262054251000c8040d00c0007001d440704d540c449021080e2141e90b00c841d0b02400010b00c0e1501005040c8030001310240c2c210356440310390420f1090150703202c041042c100b41c2c0580c2000c0300c80d0f119200f55070010005104035240450070107807681c05480d0040e2183c2038402f409242c0342c21a4003100001800005020901001103142c9414074002c04c04c49401c5a90707040e41d61150301d0201c8403500141c11a100c14015044904000c08034800c290001192803882600c1e0401241c5c0195940380c100d603d4200984105001801440c2c014244503000f00160100360b16a918103e0f901307003510254406e14000201168010080f441c04158000100c0b03607000c1e01d40200340d000b070950515600c41e9100e01e20000802c04881c00c0c2c481c288058034806440300c145443c50341460f116024008840c2d40c0011045412980002c00f075143d8010400c4090000356081c00d81c0161944c2418880640682c00c1000140040f80c3c01c183d1131401d00d10f0389209200603071140701e1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 674319325 1250 674318075 674318087
    0x10e1c08010e0c0d06060509190b0f0703090803310506030a05180d050903010e0a081b0307060c090303121b0e04020f0414090906280b03190b1501020319 67
    0x110030001c41c2e18000020624641c410068629003038146e0301c01510309215840d0b4000c2d00c00c1c512482c821113904120300c11982e42100090b1140e28404d0404218060700d9400c02811500500b04d00c201c3d8003c1608041d2000a0741520418420b103413003142070900c1e041502181051100810400c01c2c1075b1a9008141c0310550508440d6400c1d10f0641950000f85824000034804d83c89a00502c1c07082d800c06aa800c03002002181100c0119800910a45020700c51340c40300b02151942004a0b5090005110300004a45c1a01400c02c100100ba81d403000c10710b0862802170700051800303000b05201703450b00464a040c42003000000c41005a1400d048107407840a0f00060003a12500c1c0743c5050710310000c0307000540c01141880743c08510404544010190b5140c40e50180e0b21002113840101c00050444182d0035820f403070030072500200e01014041544203d130300200b4646008a40ea000c1d40d42c0b00c01120b502070049000d507181e04800080d051000c0108402e000075501d004000a4071385210701700d205103410f00d000305 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 674320575 1250 674319325 674319337
    0xc041d0102030f0a0b0f010c0b04060902030708060106090905010b070b060303160501090b0601030b0109141c140105060307050f06091c030f0e010305041e060609020309010e1c08010e0c 81
    0xa41d0340340f80072206407440d900c050b54809041820600c0004480c0b44c48480303030141304030680d00d06500503000d8442991200006c0d1043d035286545506131005a1010b00c1204040e00d1a800185030a5141c03690043c1419281d03400302800710301d44801417240981c42d000300e401d12030304034007031001c0750b200d91000130305611594600d0b0707420000d24040a803c100040d0000442c041c004d59024000307a403540010b400f921003815000d4002032081105001c680b240505100901034060303c1e5480c482000c001c02600c0d41c01008043e60700c200f400d41d154864003424000c8952283c0281c0261403013501d03200c00724009602071001c031031144a012841840d02d4551201c192071282c03403003000a01c030204905014001e00758500c0c801c00054000c0b691040d01d54064002c9500855012618103a606404410603140003180001110400d071504400a16080c4a00145010720b0105000203400307a9010106d1745440b03a9085810400c440d42e10355080078503003103840c4038110750041d41503a07055134070324031800e070f00d80301da5 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 674321825 1250 674320575 674320631
    0x80912030103140717070303020106050a120b04060609050c03040219182f220b070809040902030a03030b0a0806100909031101140103030306080c130221090307021504080c04 76
    0x2445001c1710b6598001003110849001c2e400821034a0303241c0c8140150140f440c09600b50501200720300e0b10000d00c2d10a41e25501501403000001c41d070b038595100f003080d40c2043d43c2c0400410740200621043d890180303444d80300c07800a410f081c0821860303d00042c10350000b074000da91450b075544080000000e0416103001d0702c3d10103078419054003028034810340c01c50380040280814030710b1807500385030440030350210300800e44807a141c1090038009541d481100640c81800883e400a40f19580c1c40d0050301c1c10001d030040310303100c2e850200d1041060000e0018084207580030701c04581c881814401c10742c81c10818541a9003840c1c1d00403a0106e16030400303a1b024840b070315030106590310700071030a03a500c2120241d0074183c0380f090750306015040c0d4a5a805588081d10b01e00241e00c00c4641008000c81625a801000219a0044c1c4550f020840541010b1011422100404035420024036032003145400080003029007080d03035010b4101800c0040e840d40d6080f2900c0c00341d00513a525058482c01c1951560f1004d03207025a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 674323075 1250 674321825 674321849
    0x121e0c020d20060f040306060e0c07120918050a05070f0806091e01030305090a050a0b03190e0a03090918030f11030d020a021b01030b0f1c0803160809120301031407 72
    0x42e1130014111540140b00a8841e641340041c0821280440c0b442c1601809040980a0520040d41c440e0600708204c091071905221056100003000705294003201c034160301c0d1600014040c58401a03950644000038202410450500000e907049a08101c1154101c8000ea94030301d41650b40110208098010f982195010644040000105940714000300107a4505440f11040c0301d50300c000b4003000e009a401060400b140030f100289840300070018020169208013008180f040c4031543c1141002c0c0c40310010760004150a44c1401003e8150084250512149181d920300300c0c03c8d0b4030001c0c85488416a80c1c0704102c0300c4294005451010030a9540300340700f0f01c1045584014604000e03503214424030030500c50540160410b4070660180c8260845506c000e00202d07068000c20042014500003040d00c01e4405c220395441c5800728030304401441c1b00e11803d49208840381d17000b0202030903464008105800c940d000c0b40e442d1007044004415241100d5001c1d0307210410009070302c00c0c1e50404003641c000b9000b6000f = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 674324325 1250 674323075 674323087
    0x70914060909041401060605070209010306021e0d0204030611090a0b030405010e01060e040b0a05070813020307030510091e0f0b041509030504092a0f0507121e0c020d2006 75
    0x3d4051089440d04c101c100080000f6039445c0819101406078410185d4484000001000131481903002045444038125004840300c444081e2200150042c00200481c00d5000c40c0c1071040049a01c00c80c0d805550111a807800c1202c2c4c000000c84612842c040d46121000100c045002c10209400c2100c60054030002801406e8440c8045102c00500325000e8440b02c1820003c034541141a10a25009955598590a490791038456407010302c001902c040b42c2510070000d000010030414452003450000308078000c034040405082c401d0b00004640c00e044c4120f90b09110000000300301c0540e02c1401540194101a595590704010036112110300f4440302c00c900b042c00580c10581c0c0080240141c0704444000c0140d000003001302c2d401c940002074082e42005a204401c00764900481c81c045000c2e2040c54040d16114481c5d03110400901c0940200010425002c1c0503243c88103464142444130074186842034030080e00e0707000a2129200307484090002c80401041d01c0f105a4450140804040041c0089943d15 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 674325575 1250 674324325 674324333
    0xf0f150c010f0605040e0c1005041703042c04110d120801090c0c0f1103070b13091b0807080c04170c0301230115031404030c0c090507091406090904 65
    0x2ca00d00403911107107860301c0d40108051070180f24148500c0d900380c0080144410381014050380380c040d40e10440503c1014040024806001080c1c44020000b01000d5a03c1e18507040b010001c0082861000212948201c0056500d0380050a0702d640036070004003000c2030030005800b00d000003022040c041c100c07901c100101e02025404c101754504035a007106040103001d0160004450800320b1140c0140284880003049010511101172620700900003001e840c501651600804581c0d809508828440c0380c0300c001c00c028210b00c520130001c0d2142404c40740c0c11740c8688440b000b40000c8c0c0050082007441440d0021503a00ca4201d000e8130007603d860048110600030060707200b9510f00d00c0300d034086c0c4a5030070700850610044a0310b00e0841106407062000140c1d0b424100129003c0040040740810580d4501d80b8180c48240501d45034040d134001d844a0b11450540c0c01e052561019039044031080342d0500081c442e00603030000c25030048500d20f1121480c02c0e040000001c1e810301c5000c540c580e101c403480c01488280 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 674326825 1250 674325575 674325581
    0x150c010b0a090b060906030a0f020c0a051011040e07030b12031c0606021216050d0e01030f1a0f190905100f06020309120c030a080a02010b0f0f0f150c01 67
    0x50404581c04421140c0d079840d00410740b4203041165420030014420010541041d401640d001f4192810201d03c1348800a0314404030b82281d103071058544c0c00811400280402400101346e903a1703c0c0107040c40580701c1c290024105115030b00c41c001414207840d00103002c29100341d12091206c80024244c42c084559101e982c2d0341e9070030102003038030059a10807110028480501c100011264190080c0c0745558101201d50403580104090042c0c1c00d007a519450005a018000c507032110150361600155100050b000400f12021440f6080f1b040d464188860032040c41c240103030b91400c03400c580c40000c90748c0c02c0000c0356000d06100110400400c040c040803070380f0042500a940b00e02c5140b02c0d4880c15035516603642115030424424000544c004200c03001c801d0801a58a0021f0150795007240c015104100103c5d250402581c01076880c01004242c009040d076080c0034400f0914002c59a61000990703040006101140303c0c24068800c0001d0301d000c618030340700e150306050390465110300503440e80386030159a80a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 674328075 1250 674326825 674326841
    0xc0306051b07020315190f091a06180712061203020c1507030305040206090607050d08010603090b0604051509090703020123070212120d060e0c09030318150c01 70
    0x904400c081d4480859074440907100c1e07440c1c0040090404103014001c2d01030144002d0807050038101a800c1c6a00c1020080c0140ca145a2840100080c00541810040008910022501741c0700511034240b15070b6984407070012000b00502d84030004c0940703d000c1c041e100c0c1880c0e01c02040d00d403810b004001030205200140022080d0094081d101264400001c001c00b000585004110295082c0540f00c0030920a90010b68814030103014a8a82034070b90340000d038580c0001d14200c0e01a0301c0039121700301036540100c03030030300400c01c070b04080c03002007525940c3c5440711500400d090301460740c901c00a080241101d00c2c000b5168406401c01002d410328600e525111403c50009038041154400d14030085a00c0781c4503800041003024040e03090180e583e00300034440780b06007044c0ca018412402c0c00e0004290643c014020300e02d07007000008500e0310b00410010301410007407800d0014101400324100c0e54501101720303050440e01c2c078823801900c060000000d0303203402320040c0004003181c0414200d1440105510180c8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 674329325 1250 674328075 674328091
    0x40e07110f3301060219030e150a030605100e0105070c150908060106140409181b180b101115070f020c030f030f0d1e0b1206040309030b07020a0c030605 67
    0x1c8000020480b520b601a020711410300140c1c0500c600c480403003c1e940c2089045403003498440421644c02000403000c20310f101a50f603469100180100c2c0060301807059000406003130703030210301b04040441c010305040400d0558506004000600310104459030014030090500c0b004030644000240b0401040c00300c6500840d40140f1421001260540c000d2440c80c0c1d0710550302e8104c0b40f42c5420035400c41c000d005141c221001d1058600c68000000301c0700c091124003002421104503e40d45010000340316180c0c446540c40390146405400c0364540c8400a07210104d003024205100c00d0881c44006528003c51103900000c1c5142c80018007800950064000c0041c07030b5546c3c00c40e0884680401010746903401c502c0221320581c0100045644900500050070342c0346448100000c5501c80c0742c040300c60a039640c400340c4000a586584030201031030580f04400c10b090301c84009082c1841c003a85c0203800810303540009032090400500103001d803882001007810191340700c11100e48440c3c0e60300c0c2281c050b24060302d81d85 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 674330575 1250 674329325 674329393
    0x2090909031305060a0c0605090319091a03190c0206160e0d1b080a080c010c02070b03010506030621010c020f030a0203070b070917060a11040e07110f 66
    0x151505000009a030760380c100b942c2e004030216103400c0811000b0fa000070310441c00d00c940800506c011909034440c2611510094020359130301d1241d070403060000020421880b0900070b000300d040c80000c80200024518a041c05203040e901c3d111f0b900810014281c20082c1d00d03c0c0742c1080b20500129030b01088480c050055400c4c1440300c0780304001e098486034940c0142c40e8001043c1191400400c0d02c1c0c110091281900c9100948050345a0000f54209000c415043c0d4801400041d82040c403502441030460051940c4040e084d001d081c050110014401846400e00c220b07004404140e071036689801b280e0700514015844d464105201030030a01800306040b048016009100d02c1112b0f161010048070517140b0301b9806145021619603900c803051602600079000c101d00f000b00420182e01c240c41c0c0da060204003000803c25807030300c0d148000580b00c400042c480564414001004540c0d003190b403103071b0003400f1800c000d640c540704401300c589411410440d0f000d0920681c1014030240c40c00318400f2000c954000342c00 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 674331825 1250 674330575 674330581
    0x23040501050411030a091407170f0118030e1801061211030610082d1005030a03050d0507020c06181318020904050a0501231506180604030609030201020909 68
    0x4030346003010240f20711241000041c21006803036000c90b012500c100c962640d5403072002402d51802c5125048482c0080442088995950080200302404076413800207100c0306600e0440710ba9501140b83c6e0003014040d40c002e541107035a0310580c000c3c54400d000c0d08000d0f0190b030754250041c080b61040d40035401152030040712113280000e041c02c50b03115000103481406d15040362141100c03100700060204441280c2052150002d00c05480c1c070282884524200000c903061001c0d59207c040d0303542c1d1190b03100f030f030007a90030364002900311040e030392109000d0034001029541d121090f07041c60780c501040c0d54045400104500814181c542c41024510107850303030403c14604d9002c074003c94455007442e110701651514510010700d801800a03034028890070546403000495078646095956503882d6212500300c055900705d511902e041d1840d80203589400c11000740c04c80c4400314805108543c0c1c800309525840c28508001d407958000c90300215400a8104481012801e00900070741290440c07620400c480c1000c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 674333075 1250 674331825 674331829
    0x150a05041e140102062809050a0b0402090711063d09180213090515070801210b041502250c0b0304050c010507060b09040c0e0a0c08130602042304050105 67
    0x12440c41000c0c3d500b690006ca42d00c14954076000907500400f0300c2d24980b140d80340e0300090310501032404264402c2c1600c84007810644104000401d0007400c00e03007040041600300300d0b0341100080d22500b100544008110541012581c2c0c001103c0b180c000d441c10700c111200d80842a20440ca0190403100004030802441050741e04560146015a0380070398000d29101e160300200789668002c59400f0300c2001105c0c104110301c0c42c40d0990020031100400403c5000c40100040410300c04a15040d8661b03403626404901165600041190b0240c030107010365001420001005200e0747c100c0b203c500c2c8500e01c050080413800c0c07200341540104007044445840e41100059021030840a4901841c3e21101902c9415061401151181c011145c15100c058032103600700c07030030b072680e5201302c0c003550141e40d03500195420a010702d02c10880c083d2040090900e0515a143c000380e0228015801161240e90003000e0707112810840042c4c0150b030003102004041c01c41c1e0380c40040002a1210001ca0b0070f0f103040c0f009030703a1030013 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 674334325 1250 674333075 674333083
    0x8010c02030f07060b030c0a0609150c02091501140c030403050d09050604090f0f02031f0b090f010e0f060f0a03051e010302090a0e01180303050a02030105150a05041e140102 76
    0x4460200700000f4440f060004e800b07034020130100303900a004ca07807140701e00c2d40000e480420b03a40d200700301080300d2550900c01c0b51918260141c204807541407a001044195000c40d02030305e8000e00c003505440e28049010070581c8506812180040841040c64503500080c0c000d940303a074494841160940f0658912401e440d020303200701070448000822241c14079240c4034140d80640415055050601d50394100d84080d8096407028501454080b100c00b401c0c605a501400002c0c2d000741c01c60140284188403202150381c0e1043c13455200700d401e19010800c501c214020038100861160360590014000c07461580c51030403a07000e40240c3d40590703400d20454445a501000c002c1110070704c1c80d280c407160001840541450032869400400382140001c0d42c00c2c2d010400d5003101d0703c9040c4450030b502110b42c0c4805050f414022290412900401145035501d0040015011800c04c400e180c3c0d0030b0004100c4480540c0501c007950001c155000010b002d0510104440700b0f411105c0c01080c55048500d00c00c6501948001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 674335575 1250 674334325 674334337
    0xf0c0c040c090b130b0d0603020405060d0c050d02011403130308010b1303060e0313090c0f1805010e060d0c210c080a320601081305030f3108010c0203 66
    0x2407202c0b4001030424140c0056a48940309107403842d83d03444000180c03d004070005140e000d101c00d070300080741800d610420065800241c40780b44642c0000070058041050701c3c400c00100d400440703410107803001d82c1c40143c40c0c07441d10080070028043d01004108030758102d40340c20480c2c1c0b0701ca40d4851b002daa0326012458103a000e04826641d00701c1c2014170603c0095002e03440242c00d401910f0490b4202500204106421b07074241d0441003040e6221242d2024144d0400e000465860403801d0010070204100414001c8512038421641003009110401c00b140d101c10089405c0e813032000d9000d1002c0302041c14040c00c02102e80e50900d58919203c00500940c0b03856201f00900d80c0c005589841c1ca5444462085c0c014042104c18600e01103000801521604ca00c10007a40103244018a540310b1850400005444c0b140010103002200c060140142d00240f008400c0b6552130b00802c0c9081d4840760b2003800d50042031004081034490380b4030740c0212240d802401c04418110b6401034001d101c044c80c5800300301c3e1640a14 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 674336825 1250 674335575 674335577
    0x60203160f080a1a0904060603030e2b030306050a0806011d0601050d050c0409020408010b04060602010606050412060f0204090227010e0f0d050607051905070c030201110a02060f0c0c040c 82
    0x800080703100c00f20700780c110301c4c115414180c00c414054500c10025402d01000c0c1e80071240d07030303565040c10020550800728029145500325910140700503000d150025140039414082000c1060404400400d8042d500c4003024060140000c80c0c0c3c00d440b0724605603503000a01035a502200f0040c0c00d01d0008840700750079880f03180107a4a0038205150059000c005c0c2201402e003402041e0107200102d081c0d100c61001d032004081b01000460901848010301c800c0b87e825810001c00c590502c1d030f0034003140342c0000850301118980c1d11f240c0c240b240a070805100030914122070120070f500004000404189507005400e901201e0400d070010403c1325410302e401001d1120b4110301017014409c41158a01c1c1c07031300c2c146181e502d0161500c01520740b145c0d07840d424840e04544680100c1c00201e642c0d020051001d5150355004410305101745800001c4e01d039138803580c0a5210090402007010011180c03141d0600c00714035416805441c041c0c030781c0266115030096411400d0b0b415442d00c0390740c142ea100740c0703094081c0140003656 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 674338075 1250 674336825 674336837
    0x42606060a060e06130905090109110907020a03050d1803080103060c090503100e0a050307050607180605090d020102030712260f06061b0a05070e07030b033304060203160f 75
    0x3c0742091114640080c108102c81142001c00003900301d0180c05030900c6207488400019081165244c006004a41003a038180154518002c2020581c5c0001c2c0750900280c060030310513128a400103040c3c020300020300200f240d105609141004168201e84068181c030311904040c0944d107442c1600300d401c105644a00307075041c2c0c014100c070641c040d6682d0000008094420a4900d482c080e9114140346500c03d050490f8280d00c664100036585038020084840403182d4001d001c1403900d0040001d265002d45209a07104001002c13240c0c0440e8001c100310b48003175a11105610107203600b8a80a4068452500c1c0380c108002c1c4089803000405946880a00c103c4055484003d030f070325042c0c103010080c0c000800382c900072481d14142a0314034504100d541c0c101c0d071040c401403908a0030710819494050000c1c000b1800d2609060074240c0650380858002107800204002d2181c1f42c1020406121410921004020a446402c280000d20800c1c0c0c0040d4426001d03001070100b008900c0e041107403151240742c419400903076 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 674339325 1250 674338075 674338097
    0xc03040f0210021203130212030a08011e1d1911041404150b04150c050a030f0918090c06020721020303070c0b090a05040506010e04020f042606060a06 66
    0x150408050030388240b148111081d1a43c030300480c1403958800c1e80c0c0c40034010f08816128085140c02490348040406100c003071420013002c0b0704090040d00041c003d18101465a88404020400048461005081d1500462007603c0d03a92520460b00ca410384410725203600e4545c20130300088070f60003000d00842c021100c1a207841d1414094103445015011100e5010391a503400c102c400c14020010000741100c42a21aa40e920b0011b0010840d2800000c80d400d1181603d0b44030042007001c00c941d040284c150618402d8810300e2041221030b046141c002840c0c56200044a0740020283d40c1304204440c4244808030000d80c50740e83c16642c0c2e500f5840750703914043e083c0707030300288050080718103c0708030340302600f01c90030500d190b66294400c06058001d291000401f00740803040345001c610b9003006000507942000b29007440d03c00200008401407580307000c0c40d00040d5544510380100e084400811007a0070380405c6440800266a9050180a2150a9101d0080810410300c0c3c800750010880c1c24913168000500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 674340575 1250 674339325 674339329
    0xd11090d24110a09050414040f060e010509161208090d03050904050112020f0f031c0e1c020a090209010504061b150e070f0503031210030f0305120c03040f02 69
    0x4641400c0301240568803500c01c80800100d008901c40001d20010103038550740d1858006060806591001c0d10503170400c4848510842a00442c1d900720707400001c2410250040c0c107110000c0c101e8a10365030441e6181204000480c000481d590344420b90b000d800030b80342e550356243d40c81d40040e0747c2c07006850350408014401c99442c0c4100c015171142e10074105903061081100000e0200c440036030140046a008603420800c615040800d420003a6080340c50386250404c0c040401d40e034241c50707101d40072120b69034000440142d004940d48507803024018028071030b141c00350b5901680c0c5048020300b00d0198600301400b05890140d4000d44001103c181d41e01411300f0302d042c1045805c100d5844020b6203210010342c45501081f03801c8a030b42c001300340d06400070071281c003544041c1e444c0080d1580b0140c640140e8910605c0309640100c02c448d00e400e01010804d40c0d5803901c042904401700700354801401c905200199404241d00000502000426600341880f50b41d1409220a0b003480102c900908589040792010014 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 674341825 1250 674340575 674340593
    0x90604051003080c1b12072102090a0c08060d050c0913120207080c01020706080a0b030102130305010510090603020112050c041a0d0506040b0a0e090a0609080d11090d 73
    0x4900d90610703030070666540e074071220340e0350b07000c100301c401150000d0a4201c00d12603014030210002c50180c4110101801c0584419140c13032843c00b80c0d02d420b9908109520703100d080041440360160b002088409a4104031a602000b0140300100748013084241e0000340c800e14145115014071074002c009081e82040c00820811004401801801e03200c014580c00d001088031450380311a40983d9030020500c3c1030811200528240c507a2000d9030440d80003910900166600010070341e080900d503000490901c03d035070300090180c003411404108808400300c0005c188481500001d0180e400b4882c0c2d52102c1c2e44a05208041d281c40c0e01020780803442c01004640564100e6118945c407003214101c4e01d045c5500c41507005924420b9241e40000340002041000e483e0b500742c03290f2a000392003182c01b00a250148070205840003c1071103091188001c010010741e02d450148003114001d58011020000e104052520613240d820080c8900c01d110314007902e0011030440c1c2c001715212070000414810032441c0c0743d5a440e02c4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 674343075 1250 674341825 674341831
    0x220e04020315040f0f050105070e06040807090b121c170609040b09010624080109050709060c050304050604030807120305060f041505060406020109051c1e021603060f0e030909060405 80
    0x7040101c44c9500220b136458500d922843d12400c00450642400a40100240d84401e5014030a100812080040c070100146c26000c0721500d00b00403c42004c1d080000d60440b2030701c8920b1041c0d000f005441300200f4102d00f1245031070045034440744541840798000d114442c200b1101550401a920f000c200482c0c1c200021640c040407090001c40d02a0712052840e04810849440340203000341d00341061011600940c4c0d40d405014100800c103c0341c500b03104002c00540c81c611031007080c030140c18000000c7c403105200304e4010700303800340c45242d07642d0b500d00d07101d207040c1c3c050034080d1079903040655050300d80740c824042e40c3e0007a60000c0050055001d11820031000345044102c0c041d1a016401000450351503250181000700060f0300006105165810801d08054000d06e542c0c0c0c40d050f0800d007031a8000e801000d9104502c03012040c4e4206120401001e178074210b02200d10076410080e868000080250b1900708c4a241e00241000b884018480d40a02e65240915400d4a038031400c0ca00024405062650050354 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 674344325 1250 674343075 674343083
    0x30207050f0607020d08090310051e270a0201030b010f121d120310050a06170a1103090a031209110405040804050d060c030b0904120f030e0102220e0402031504 70
    0x3c81c0040303da00080e195600c0560481710110042074400c107a203070500000c0b034a001044001e00c000d1402074460703104034440141b015011007e00012507100c5081651101d0000d921525041190014060701030380d9840042c0100d001030b09180c0301c0c015551140e200d800440d000b40d121014000601c0c039900d00a88907080d85504010358508200c2c0f041d1804012036410f40d084980100c0d07403403c2101c2c4213214680b03a0342105010b084141020050503900001103a11802c09601a00c0c203604c40341c1000002d40a07030150810b23400c40100511040c0700c00132944806042c42501d62140c0c1020250a801c20348034110805800c4050b04500120181005c0d00005d1b84584280700c4140381c40c0e00c0e180000d0503110003510035182966110b9400d10b1341138040c450100104002c43e65140645415905e80100550b450519401c111441071030040c8030f8040e130080c1c820403418030025074441100c09100c031820000c01000c80250228501c00180c45010020224004c1c0d80203805400d2041d14030100c184c80ba500900211 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 674345575 1250 674344325 674344327
    0x717031204030e0a0f260c030d030203041b1a0f070f0809030d090b0f070804030609030818030415030f110301231f0f14070b0601021b03210c0607080f13030207050f06 73
    0x86a9800384815049c03020b80d0340307005849092a0a040e6071920b8001508401c0b0100040d042c0403914601151040080d0510701c0c1640d100028000042d4900600f1070051901c26000024820030080c10050511a0015011140c600ca1510411541400c0a21409030881802c202d17581603048948010a00c581c05410b44a10f4199030b0f60303690040703070024001070b0f000a01c003106005911ba51000c8807609108007800642c01c050038040300705500c040c020126402c0c0340d03072911803521071000f54201e00104d20740700c07286503101d6030f5407030800440e04d9007122144d41d40315040940580038607100200640c101e0001b0713070540040d0710440c000c0d15a03400c400d070030006110040002c082e00224080060850520410400f130550074001d0029140c442400d4035404d500340c1d140e5081005460000350000050038501c3c1c1000541c9a809a4400d03d01c10510b00c151203010b030794100540b00d0340200c007550180e1034181c2c20400d075070342d4010041c007003001c0d580700200140c00101080040d0300d0302c140d4038400248c0080c20a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 674346825 1250 674345575 674345593
    0x9060303030b0316360501060f170f040f0b0a0b0a17030307050a090e270c0117070c0f0606050f01180e0a18030309050d0903050717031204030e0a0f26 66
    0x22001d1194070050170041e91034000500005a0044000300200e9103410809860000611134030942d0314000c00e0131003c082140005014007090400803030340307550030034206040b40c18800315000180224480880c001c5086802c0040c800e200d600a0260100d010000703981182c8039030030200ea1543c0b08003586000c0000b00707034010403111034010b80b0500074101d1000b24032082c44000f081d03000c08040c1c0d10380700030716412807007911020f40d820461003400011044a0071050303a40e22181540d191aa69002400c640004d106034000c05c4a070764800001d41e40e00b01c0e03183c01c4100344e0f20300459041031a079541d2400c541040da804c0025210551059401a01010001c00e11301d08400c41e448038145000d800303a001030b440e80c0f110001d018043c84084070340d040501e02100d80c130b811500c4040e5114020b1103410145043d61030170002800050059034002003031600c50031b60604250400030050501000181e1068440300000070302a0100d004441c200c401c0d08040160b43c072404503220b042d48000d0405200140210705507 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 674348075 1250 674346825 674346899
    0xd020d020a0b03010801060b0910030b01110a061e180f020f1003051509010f0317120907090b0102150106030e15010b0a0806030a0b0c0f070b0109060303030b0316 71
    0x1d0100a82280c0c6030094a9624001c102c034207640740d81d40405445541000680c046807038220508c051440c803428049990341ca01c00048800080603420000140500d0b2054410031523a904040218181145000e0504e03c1d250440001c0302c140d040b100d82c822000310458400079415901c5030b4001c0e03000500b030104605d4800007060b4240700064003800000c0e5070f1030412080829a182c3d0b03c400700300c1950209007642c1808170705c451004030750202400e622001800d01c3c0441c3e01e03000889008280c402404886030910104e92580c0300c0d8280681c020380c50070900d101c0c0d115403000a0403145074601020011b101e03441d18005900403c50500743c2d00c0382d80100002c1110f45251108254021304144948a41e580901c90008160001c0900924880e80060082e01c011403d040c500c00c1d0480c1d0b898070f400d03603103c0c42c1001e00d400034450080c008120009120000520580d80c0e8410400c40c0e000362020701c600e40202c82050340711005090442031341c41d0421000c1c8003071940750b00c0728407080c1c01204e1480c50750750031140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 674349325 1250 674348075 674348089
    0xe0a03180905041104050f0402030606220603050c1e0901090504050c180106023924070204051f03110f091f0b0c0606100309080c0601030b10140d020d02 67
    0x3d4141c60215883c1101120b5080c144202079005045010607403540c20a40d0020340c80e520040c1206224121009803200140314101941c241e280107000d042000540d03d04e00aa10b510252810512130f0b00364089881010080410341e2240000090104c50540e0a24130794500405000d00f050320284070341a00911076884007400031001c0d98030202502042d40c50103800034a0940101c0900c2001350514101e031440800c902d41c0001c03c0d0708204010341101c1100404940310103403c0181060403c85806920440c0004600030143c050007664180180d40e100c06e940c08101012281c0e20080310180142040802c030b0140003404480340081418203089039180010302c580c8825114504a04c03441070300c0741d5621001c2107608000b440c121482c5410314040d20744890300c4070402014075004081c038450031090309102e03600c15102c1c00d9106111644030094100299540c0000b400100d8200c0203a0020640c031304803000c0d8000840b842d605444102071950400c0c881c60303211000c0201e03041542c03c03950350f005944030740d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 674350575 1250 674349325 674349331
    0x3006033a0e09100906053f120304050d030203010302010e1504050d0623060d1113060303120b031603060207111809100b010c0b040f1e150e0a03180905 66
    0x1050141d085042c941c1c1342007162216070015119062a5041031030110981d074442ca941169901c2d40000c0c0d200c1001c8801240012840201240c0240c4030581c504455141c0914041c43c061011500d0311104180150101d11003800b020f0f002c01d4088a07804141d207030400e510205940e5188103107003859503680100780070310711012049420356150010154441c00703904d80340c0d60600160703005e0441030604a000c1480c0001800000c0d1120420300312680701900c070f02d10310a24806250004008160b600d0900078402e03550455034102c01800c1c0f840180440c074000a50220745404124101d18081c0341d036452100952003e4000c60b854007401c000b9943e80d135100381d0341c0380d8800c50946083d101e80c0340103980b450030081d40e2207925020b1440c205012940b40d900110361084254412002d00490700c45e400d0406409000c031200510f582002c95444003480d0011030681c100c6403103811410041045421124280d40030020407190a901070302030440801d21907000c4c0c0c00b498045401004030962195441d038203440c011 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 674351825 1250 674350575 674350591
    0x21b010608010e1c08010b1806070b1608072007030f030509090a0509060402121606031d12091903050703050304050f0301050613023006033a0e09 64
    0x79015180b510070240050821090418680e00742c80d40c8400e07010f0f0182e02c06000c0c5008014000c0740944c410030105101129408000700012b88034401c0e85400f44d40444100e0340003204503444240701c640503015011060040da52900c0d81300c00762090501e0582c0000302c0008040c0280328220307000000c03c40820b03600c1101406995401c0d80e5a001c0024085031090161a85007030794540010441011004556260400e078111011800d041c004202240303451200c00c00013a0740c003101100010741c1901036124420010302841e03016100c1d030102039196207502c4001d1503588840020482c0e1005481d00e1a40301c41c01c01078081440035001d880e034071a945040b140d500103c4143d40006400d008070f02e81102c49000c209412002800070b40341810100d19109859603801102c2900842c03400900003400d1102601c40341560210385010120b10002010601b060703981c030303001c0d004641c1c0b5023503402c1803c4101d00e11241820100d02c3d80e480c1d075031082c10090048004200c02c00c42841403003c40e81e038a01045034020b841c1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 674353075 1250 674351825 674351831
    0x1204020f0f0d151b020a03030c030209060d0605010219020306040b0c19080601021612060b0a1d011a0c1c0504030b1312030b0a030204020c121215010c0b0a021b01060801 74
    0x60720030801101e40400483c000700051031000300544c1c0c2c0c0081d500354207a904d8500403990b075042007010b402901440749060741c0079001203101d083c9824103921203421207109a0880700114220900b9040c0701c003070808003a42507046800001c0201d002100640d420105111680d071404101000050400100600100005060200703008066a040003000c01d0300321391035844920546400c040413620790100030020502c41c0c843c0110852680c03188d070900000d150340c0d603c01005d800801c0b1480601c3e20240501448003454402c21000889404251860201c04100411000344205514440e0341c001312200400c0090810001c00001c0c003840300c450007084207007000e0800b4a0b01d894202c0c403a4503d18031610402d450a910821035599100300c410440b03805590040e0380360b12910700c00f8107102c003445079403107801c00000d031101c0000c0025100602c550038520021111160120044a8100a80300042c18150700c103004507900180e5640101040e12500701c00101c0d03c0140307810a800c0d946143d01c83c3c010780e55 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 674354325 1250 674353075 674353103
    0xc1b07090c020f160513050a06090e101104300c09050f0601020d02030a0c020609060309060105121501030b06030a060504030504180608061302010908301204020f0f0d 73
    0x340030080c84c42c0f004c5004a054202c18281400b00f641c40c003030400009034064a40b40860920700c0e0035441203024114441061180305030801503107950f40312021603840303d20314000310240711120764400d0701e081e5610070740c10759103d00d844241e101200d40c080da4417007400300303002c03e8074000a4402c0601e08010a1068008141441d2950501003000402050141950070078108001c003180d000c070807540203860350b04207000e4102c1c603030020a009024000690360003c20002c1030100841c00094114120b810885400e6074803126082e0a6031102450712800c409100108014000242d01444040d4400c40203030031500741d002d290300c83c24146e40c02030302c0607030100740005001e100c0810862503100c1003554501c420301c022841d09517103603030b07429004090a0f4525050040741d000c5a102d000008000d040340c4046400305e400380507251030708192008280d52a814400f003550b0004805030113850411640a004003c0c07540c2d646c00340080d4002158246500101b00d8136440c0303070350391441c0c05d084007540101d0700a0180c2c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 674355575 1250 674354325 674354353
    0x4020f12130b01080102070210080c0c070b120702150f0402011103070f060f022a01090b0906070f09150c050c03070806090d020a08030a1a040203070f170c1b07090c02 73
    0x2c00103030040c00c21640100001c0300540c0300d07520700c00b80180480c03804041e10303640c04000c0007042c018500b1f40c0700140101940056100401c0300503000906030351204a085071200394082e039a440001c003003a9816100c540000e4001d41074040d030258894010f0420000e000307500c2c0360090079540580d2085130000c041c1080d98040c010341e846800ea944584540842c0b030141c40d60300303400404094155036001400390a03030000a9950a42000001507031091a030309031402c1c842001921844101c0d0b0440008421115810070b40737109102036000c84140d018160040d00307a07144216202112120203480605c5907424100381a20200716000051141601909032810041c8001c2d0030181440d40e5042103500c10010792010030f040b841102c1d0090080d000000c0e000d40c00600c0200b890710140a015805031010081010017074000c11007072403841c01d5540e034131030f4071800c00402101c609c1d090380d0140a4290501a010100c40d8868400e41c0c0028604115480d01d541da1600d1070941d40050b00882c0141c101184840c010 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 674356825 1250 674355575 674355593
    0x903030f16060b041806050c070c06210204031e021f020102130506030f0c07060f1b1101050c0a030906060305070902090306090f100507170412170606040504020f1213 73
    0x1003200f02c400f03003c42000032601007844000c03085d0180c40b46648002040c05012030030100e80c00c450b4010300c0c1d81c0300d056844001615030b40c0501c900016503284090b91070001e0940f032003200d09584d481601b082444240c5075001d1810351106004907084040548a46502200c1254100b00000954000342c0e803200900c240c048041c1080c3d020900a481c00e00c284000c0410181449500a801044030380d2290291300f004406002001d08150351185403000e80c111400c00807544202c00041c2d51641841c0104000d05203088a1040742e00d003004400502c8000400b5100b500030b82c00c46c500514000c500541c494507280d0a01e681540103c09850780054802142d040910010b5032058400300600145500a040349490302090a28103003010360300d200160712280500c8284141d1041961740f10741d1840d1030f10f08503c048061b141160082141e94044028140507166143e20481025005c0713802c0a1401c410710001e508003640044125505010a0200c0c002c02d41c519882903080038201c0c50300d501c03107003428820 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 674358075 1250 674356825 674356841
    0x30a11040c0c020306070309031205010305100b0d0f021201021e2d04121a31020307350703030f0e1e030f0115090c020d140903030f1606 60
    0xe1001c2c148420016035408142c0e01e42c451500c0c1000f0038001032074541141c3d00d01e01003c2d1400c030301d071500d0000b109008002901c000402c0703007000b041100c8400d1008000c41d846075400c000302a0165083e0700c0b401800c000b07181540c02c510080003d407c00f42486000400258160600311800201040c40480e10444d41d03000001942155010400b61028a11400c02480380d0b001321020384225001c41d008005907070044901c00348000d10f01200c02d040220f07004d03105002402c80a504e00c280d61550b0030f800020401e500070210f900038002d104c160301c1d004c1460582d0108a40f280708400c01c0d464018031000350107601100d842e490740c018024160840c80c025046076100c039004030400100390044022a2103109802426118000050a4a038a49000a8074020342004861619420445c0d0b0b03000714011003128a041d0340c85c2540a00803240300710380c200d035a0783c0051a2400040c070308880303010001c1e54940c01445480d00c054162460101500d40c90750941d4085220007491080400311041840100c1c031035603d07 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 674359325 1250 674358075 674358077
    0x30c15091a1806010614070209090a0201090f2601090b01030507060215010b18031c03020405030c1203190e061207021501032a09060806040b07111515030a11040c 71
    0x881d5518150b9107a075221014003620050041440c0c3c2190f204460506079007503664001c0004801e0b00d403103d000758071b0b600c241c0022808540519000b080850810084405482d052070400000d120200c10a5000c65145003038426207559402e0280040b5048041c80e5010354003e1004160840c03524800918015014443c0c03000030242c040140b001011f0601201c0c011145103031001c10551441d00000e00b080d051170f29030720015500041001031540c251b005082180c00071030603200d5a60048040c8180c007984500181250303001004418540c8a01c002c180988003403500e4550034a40603180450450b03481444070141c5251142c1c00c000c0c09950420030651429a2141071450741e503d50b9495011322100c181c014043e05503261841520300020161610041046c1c0b00c05000d4181e031400d1f4252034600c20b44c1c1c03d441c0b000b03c3ca0001480680140c7c1204003c0c101e010080003850400030147d0210700c0094a01d00600107511000c8100740c0c0d04000902580d80103091600f00640400c0410007203c40ca85501700c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 674360575 1250 674359325 674359351
    0x180b13140a080c0f0d0903231b04180b01060318050d030213080a020f060c0f0105130203010501230d03050c1f151208030702010219090e061c030c15091a 67
    0x1710312644c031948100c101c070380c80014100108450808a40340030703440348880016111f61404070305018603604030907031802400d44080103184124011707800920f00c010806000b4082450041140c05e109600c1031001c0040702c4050305585606a44041c20642080d01da100007a030003241c0a0140054075904800814110004000c00041d81d1f001c540c0744520301c03da4500c2030398082600c54101c070341400004400047c60300200028505490391216003150400264060361a003000450300c030020707509080d01e40e88040d01e1a010a5182000c0040007207460f04110104075041c403180700c941c0410003103102402c6011300284010b607009090f4600300c1d40c151558520b000102c400030400120300b81c84c111005908a0f401a035666949581640a8401c4821803488602c50b441d055000d07680c41904142a01c10282c20b600d001d44405040002242c0404080c0c3c1c51188203143c12000a8081c0c3c82000006100d042080c00c1d6103007004010302215000c600035034003402c600300000c0782c10745a41c403502c0e8801c00c01080320b = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 674361825 1250 674360575 674360593
    0x613060b0f1206090910271b080f030d0e01090204050c0904050a051605030402042d0b0103090c1527060206090a03080106300e01180b13140a080c0f 65
    0x7417a620746900e40c1c1310503041d50704c644584103208241c0c0c120341f400c1c00600c20b454600090b841e024000204181a187c504440c941c07011440d1030012400c9020030454100450510b60032804010081c0014074400a00c0d42d41ca10445005844038000e51344565403000107140c8500c00c10050000b40c1e08020a403817181841c240070043c08030b03c1c810540a0b6015903180c40b50b1a680c82e4808600100380304012810cc1645070041c06110160710220109640d0000c54280045e0400c98015000e65107002802001452280700c02d01000304003125005a2400c0c0385029201c01e06a0744900702141c2101790a94102d820828050107800e404014003608000300f60010603108002d51001088568180a8041000301032031440304080748081441d1403c2404070104413180d002e0110034801008092201c81d5254288000412117032501480001c1094210740c2007140c0d03036101030040490000c080c030300321441c801d00c1c1007040200604100c0742564910a1890384e40e59441948039174507100b5040380360800c56000d4414 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 674363075 1250 674361825 674361841
    0x103061d0316080c191203050103050a02010311091201150501020a02240708190806010c0b0f070c17090901050909030a050a140d320613060b0f120609 66
    0x80710080c0c03000c00d065a100914600c1d04070034522540b00136041c2c82c46082a0b442c00154048007030301159201e000d002c01600c240c040c06070242d480900c07025200c4e8120841d0300c1c0140d40203822004404052040140c80d081c0507400041c2602d1014940c11030a0b9911680101c08102c1c001d40314021300400d00003050b59500d0341d400200c034401c00c0c07604040001c42d9220000201480d01054984c0d490748200c5040c2c079122071070801d8240c009065044030020380035002059641d40116a45000325800c80c5210728103070380d4802d60300b0036500e02030b20100400005a50202c0410148071500c00e0720800c0c0702009954030003030000c0240a40b4181c100307070f1003101c0002c00c0c04441a070000849441a07003070304080743c4030805540c00b0381d40402d008800404e410000580d03102d0701c482076444040e40154090400010300da444506503596907040081141704106100428081c1c5400c4c1c8900b80c240503480d10109070705440d03031210301d80c0390000c00d031000b0703140000705241c150060321100355603215000f603822081a24140030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 674364325 1250 674363075 674363077
    0x50901020c0a1e08040b0c0127060504030926010c02010b060a142106040c021f0902131409120a0c06051b0301060203120c0301051f0302071502030103061d03 69
    0x103002401c68000d880c040301146843e811504400b5001100742d5140c540d80c01e105200e030b0b403003401019465444c1c01050304600c241000308904081414076200261002d0359902402040040e1094051043c0e280e40000e07841d1815007112011000800c1d4009543d81c1000b80900b0349001c807003400196410701005141a468140986412611030700d0308820484040107002114808c19042500642143e0300245000d80903a20050084009407000c00015501d200c08984a440c1c28512684034940010f103290101d000ea000031003040c0c001040c0e0342e101041c40c02e521003100e451390f0a205811914004004007000107109908108400702c0e8172610b0802c410500500109180100500b5950b94101007154901e0142058042c0c51540f15095902c4d41c54840295482d080303602e440202c0500c0c440001c01e540e04502c00d90303040702c001400c0c185075031407103c3d00f040c40c21482000301c500b010343c00d200e00c801180c1c1060b825000154542c900696a50441c209031003a2003501c0c00000d28107010034050070341b03150000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 674365575 1250 674364325 674364343
    0xa061b110d0c023f0d030b061c020f03150a08060c040e070e120610170606010305060d0602070c030c050907020d050901090b130623182805010201050901020c 69
    0x542da031380030014100c08032a03091000740300030200c0d81500b04841804038000b21000d5102d55401c2c115901c524400c0c0044007591010b8840c0c83d00002c0500500341082140c801600c18440602c20260500c4000c0d20400c1d2a030300202d504038110041d03140c501006041c4281010302514405001d0005803501c09d800c0c1c0e10038419441800100710714200000c1106106180030130542100a21809403000f079481601d41d9a036095840400310014841c0001e02e0840740c04100c5e0036244a82d01a080c20b03581d1000540091100811094110120401d17150000b40c0a10041100d94406c1c024200c6540c1541030082c9030a0081c2c01150254451809008a080e000078000c1501c0807140740055840d440710004035100302d256882141081e0000c07504502e9042c02031240000c0c0d80b06541c03248130a441aa0f10040301c915950b2607504112010004826200981d170148811000c000e07201800320300844071905851910309641010168182006102940e82070140c40d4000c107004000f035040120201080c2c0c0c03209191 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 674366825 1250 674365575 674365579
    0x20c2a1519050310170d1b0f0f02061b01020c012003060f130c08011401050f120601200a12030615050306030106081f11031e04050a061b110d0c02 64
    0x4000105001c402c6800c0310050220030b2050313541001c2550b501941c40d14061100c0c0c010070700c7ca14140307005030580c5000000e140c0d080352004580c1c01454982c0b449071401040243e80081c0200021101c0b00409490700107010404000143d69a028855240c00c69030f000121402a600c440d5a08620034800c5041c0d81e04024121014000c80307481c50002510b91241661303a819035401c20083d8000141c000504c2c0c1c2c100d6444100080480030741d00c004490510400140d90000c0e02d0612455101c0f210780c0100503404201030402c0050039048000f0480b100803800568040d070f034001d42e1154200655180544a20a1942406d1161908285c5821101d1402d10301031010440d0100000d10b90303035002d40011000b0320412703082d101e64000c42010700e050200c40d07040f00c0d00b005040030141c4100d10784032001c0740e04c50507003100d602c0709843d2440401c5600040151050710140300700d06407907012441612030482c0040c2d41141d4581071104c1c021004e440140030003400c00450300414030284026030010051040c807541 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 674368075 1250 674366825 674366827
    0x60b04060903020f12060903070203010b0a0308030117010216120f0801050a0911090a1508011d0f0a0f110d0e031804051e041a010806070c0303020c2a151905 69
    0x14140424a03405c5d0b00b14041001384a802c040c010010b00100051840f14000d41c024440f5040c1b8009000562205120040c01d08104000400441c144040c2440030b1200c03080002d03180c0800040d84100c6007038820400d51340820120300500351242c00c401c00c80a034003180e044c038007520340c5014001804141315100d00c50009807140d4101c00c0100110b000c403080088020102840e01d0b440300310300b8558413414084000403407030710000030481103841c42c2c8054500b5101a6480d034150b90700546600003400141c010b100b06622041c8840801c0500d014554014460303c40c1140c0b1103402c00001030507103c121400c035800750000c0080328040341d10649090403080d801d84012504d92502840e80c030324011070425051600710bd04090004126000c160400300c110ba6250b11400d0f640c1300c1c1c048544a80d41515042c01207440410b40c540024025005040506e0005080d40c9190002001c1a020111070741403c106028161070000643c1c90203e205560b1b1110180076a81420101c1410700101e0f004854080140a4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 674369325 1250 674368075 674368099
    0x1410050306030109060615030513050703021e0d03020f1c08010e130c2304060509130c0b2a010608101a06070501140906060d0303090c08120706060b0406090302 70
    0x82c25000802070f554046005c103c183d9a40c1192101480d030b050000d0700003070404011956607001c2c6a410100303207401c600905a0381c2d29550800822510f03220050710203052075405000d8030759030f0000040f0b010b4001d802410701d0f003000c6001d03581000012590900003520112480c04040d5000a0250640da2640500c903115101c2c0e822501079a50781e500d00428000140001041c00c0d040ca0700b4109120744006081c8001a100c2d07000c00043d00c40318001d80b904846042d001800080304038005c1c0b460580104100e1440307940326142511103501c00004500c050300303540908800900014810162000350000030007800342004020f54645500307540c0131540c2916003200c400c640300d0000e01c071500c402000b001155584c615241c45400b0f040e4603000c0000c484028000150203010114030350b88507120090031044d0111160760f0a9000f0303d80b060040d40e00c1f940c0928080341e0614108030010b0091590306046444070218a0000705403080d5400905010400744000c0212a810002c1003051721340c1101d0608480e0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 674370575 1250 674369325 674369329
    0x6040b090d021b0d12050c010b040203041208040f0c0609030b06031c0f02030c0712060b0d0302030a120b04060803040e010614070828090f23040c110a030302040f1410050306 76
    0x200b0381d1802038051680305c00d140b214290171000502c28154050300902205c00d00201300001c9000440e07010340046140311283c7d0840f44643d05840d071040c407500500c0340e6a03e19849101b0900103a80000e070120b002c100c82481030040030f019156000c3c004400802d090040d141d5120306110b061b004140510600b502503603511070003031090b03400d003406010844901070342d550500006901950340584031546000441d44450400b036054441068058000310b141001c188002c4411b0f824001d036402600750340d0703804e21480d030703a480c0120401000518001d5441d05c0c01c10703004510050060b480f0205001e14400111075a51280c030642e001c00f81c10a8900c0d07100d506a01d9416801500b0448602c0103c45501d94800420b0b044001d07101a80c0c03150061525090b200c202e6501c18200100340c5040d40d020f201e0348801daa03e07158100c900043c600746009604d42241440c807614052040501f100440c0c0c01103010700c0180040340c905001088004001c0c01c00500480c0400c002204000c410350400c40c0c0000058829 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 674371825 1250 674370575 674370589
    0xa090e0d0c0f0605190c0512060f0103021b0d020c06040e010b1b030310030611040803071104020c102909061e150c100b180405011d06040b090d021b 65
    0x1543c0000c014070051415031756480750350024120842070b0324074100a8101d42842403003550580c082d0035240c0040c1e0703103d840c200101b5414051115040503000c00c00402d0509502c0c1d1110a42500c0200404164003c500040c4c1403802ca140c42d98040c1000380010000810f41c0c03411103045801189a140e660b06000d441034051425002142c41144400018040a200c0300098201100e0281c2e10030445e02c0c80c1803000780003500c40e601c50418568811b00040b00411440942443c10180040c0300511346844e1001d10f606000b060790b014100150b450300c03418902c00864071410700300c2880c40e034584103035524540090f019140c040c2041c3c0c080d00881d040a142902d0040b2008071324480100007010710b5030407040c100d181c1e40c41907803492824010000360000071001e0703009078040f0f818001c101c80400602c2988d850402403009100351015034940440003c80e04001100384003141d80e40024000900d420f040bd8074602c4800345c007465003a4001e01040c1d80e01c81c0c0c08980680c0340c80803600b1041e0b51180b1500000c0d54 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 674373075 1250 674371825 674371853
    0xc0504091a090c0d0b060907080108070b21070f030f05040201051b0a05011b14040825120b0103060b090402010e0d0323120c03070c030302031914060a090e0d0c 70
    0x2100f1100c4d0204c0900580c481414420720003200d01965541c4c0344181101d2425013880b40700050f5104d2602803028406000240c4603151500c80b000600101d0246112503410041d55071501050008071640051985400b6169010064000602581c142a40000c0151003042100d03460725080d100c040340000814440c1c04540c030f406c04000e10003000f05003544408c903184007840d840428411011012a640c04c90107443c02ca9100501404034400f8403000d11010540201400401043c032a00c0410550b480b4440c90028078012008062598114174001c3c080720507011034ac2e4880d01128080000607a402841c120746045c7c10b942489a28a136860306890131620074141070000090750340140d8036080c03214058100142000008a000d45811544259921094662000051010007a038000c603000341c009640080004a0000d400054001114120740071200f60024650030502480a01d14142d40c04030042d0640c500100101c0d4642120180c1c1c1300010380c491010311a044140c0f00900200c0300000d08 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 674374325 1250 674373075 674373079
    0x31407020f1201023c0928050f19051e030a1b050a06020c010825020a060b0324040203010902130203041e0213050603030d0e06040c0504091a090c 64
    0x1034503811040c540f4040d411525140d50400388884460035041e42960b110165007903403810142061070103c444564543c061000c0e40d03000a22005045401d0083c08a11004c00c00108035000411341000c08110800f102c909100784510140c45d40d24598444640c80c9a0407500116088034900700b50755a02c1091007081d101043d40750103020088030038800c0080c1c0003c00d07581c0402e03260555039211400c12030519040c1c02840010703070024000103601e50041c803010790040102c24010201c010b101c6061901c0d56035000440e401a0004510041013000500585031180b030203c0c040d002030010800881c40f002259a101c19960000201143c10364400391301c0041c8094004e0a000e46070800200c0d10710195209803012210300345821008031103030b039580d0b81a0f440594014682504104003100c908040c000207421554103020401500c02059268800c1001c1850110060011860181000702c0c405007242d000600a86c101441c680c001080075404201700d443c1120011025281c1c03040881c40c00e1450201c0d16 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 674375575 1250 674374325 674374339
    0x60d02130207061e020c030d0902180c0a021002030601020d0c080d47210303070f030e031608030a14010f080d0c02012a0b0106090501020d020109031407020f 69
    0xe1043c03541001c2d8a481010001040c8004024441c034128412809504000c3e001400a10610305003500014030b03250005102c040310000b4912070303c94110381035a07100030418000840c1c00a0399014800c441207480000401c5086107440b00001c0e440303d007080150820482e070348084804202c00c00c015209844070070001008030140541000d403d400f411080404801041c3c0b20741000042c10800c41c040c40d101d9040303140c2070050707104c00b0700580c0305c44030308032401e9092108950501890100080c40c0308000ca90340b00f10504251580c05812101c400c0c01100c0d01d070b04204020301100c94060442090564401d420303035541d03030f101a060380041249030440c0c00410410000040c0c40c0316218100c1081d502118251074165a032510181c3e80407446010003404204607070409400c0071118103c001d00d1405020018600c50302550310707110342860036080764001c038410703480501955a040051051414840c0000c0041041f5038901030f18000c604d0005030220500042d40d5030854441140d003004c0c000c0050901 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 674376825 1250 674375575 674375587
    0x6100c0506010e060a140a03030c1e030e1e030a0f240b040507230313082206050c070312030605040e100b010e0a0b03090c03061305070b12060d021302 66
    0x7020428100713031410340c4124410600840c2c03c64400280c05211307100202000c022070300d1a80c0a0303400d140c1e220300070303146001c04002c444d40006010040303c062070300c02d5450039030b0380010408100640c11004d00a142e0034003036503903468040d02c0000b40d00c1d541036005100040007050610f005071008062403003152058a40308244003034441103030090ba101d5041103500340300a59996408582c00714081c615a201d20305204980f40c0603009040045405c68010080c2640700201501c984103d0b900c00a24031200d034542c030b60404d030100790904840001c0c14051a0251800350062100355841d4924040038200315400d1026500f0f05010307a0200e030083c031003d0414043d904480100580b1080110040c2007868100002200319621402403120403000041443c0b4415007070100c28030150b000200103a80e039110740e01d0480129601000001d10a51001e030206045001c0c0e8034245003014803581c03009035010401e00003c07144c0c01c040d1100c1070b4000c200356006461202540005140341c1b400d0f41d02408054800110 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 674378075 1250 674376825 674376839
    0x30d0209121603020102010c050c0c040e010222090c0509010c0b150904080a0e032404150905030403050709050403090303030513140c040b0f150f040312091e03020906100c050601 78
    0x103200200c81c002d0b0020491b8010500e009d64080c49584c1888180c1d421002c0b428000e40340c036900400f40c81c0081c200041c1003064504e508203d003100c04000d941107420700c5004010540c00790081030002c400b203250803810260000d0000e00340018032000101500604000148100a402c02c5c030a18000b00800032103290a041c2451104d5920070018040060401e0412200368140054818000201107a0591612581712002281010081d0044403480d10032450664010140d014400515004601031581e1703c0c03070340ca030252501e4480e0b4010198141442c04103c0440e0700b0040b158126901f6003004a65655160703143d000c0080d004800514428050403802a06c58002030440c030310103800ea0701007201c0780501081001005e507540c03140d83c0c48800c0391031505407a8000000f6020020804900710305080d244e944010341000c07200c542c000000c1c220503042248031b042410030100c4881c0e46505640035070454010504042d0010702c114019030592848001080c4140403118815800c441a124156140e01c0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 674379325 1250 674378075 674378113
    0x5011b0609051c0f02010c050a0309031211040501090905130f1103060702061005060403080403030e0120011a0919330e01050117070e06040302030d0903060e030705030d020912 77
    0x3c0000062890042410460051061019807142074840b24100662600218068485014202c0c06c12680601c044148503503402980d5105d070035401c0c0242c0f1581080001001c141543c0c1c05144e46034204000d02050341741402820310920381002a50910682c142400d40540703030925503d03905407050f1010840301c590301250050140300701d0b2100908003596042081828082c501016000c92400c2004000090150300100c1024006040c00300c0d9011040c0000c40c4054000340074031080f0707515403220650b001440c2c4051160000d0071207082800e40ac0c4400e20810415043c460900519512607036541c40051401c4501421094884070900c03001c3e980422601c0000d0b40d01c965815070388100c002284940c0204108002076080303a500d00c030b07546d0b0340201c2200c50b00c40c2810f02c550032100412012000d600c003032212581051700c688607020303d40e10b0340c81d07c8000c5901140307900f0b00d01d0f08103006843c0000c40110488041c01c00803280540c581281031300207041500860307442c0300148518000b074465002584c2c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 674380575 1250 674379325 674379373
    0xe0f1909080f0a200a03021b2202030103050706030c0c020d02011206120c06140d1113170d092714130506060301020307141e030106090f080705011b060905 68
    0x21903c1c1000c1c10030313601281e9070b00084c441c01800f6130400303400422542031842c814083c00800901c20515640b06c5418001d2001e00300c1c12040c00b6940000040c0180002007100000420b490710b01044080303030b143c00042c90b00b001080c2c0244203030400401d440c25a031141c02480d405c480ca4420800c401079807031120003d6408049401c407110b107005400002d005001c0c4140e180b85211404407a4500528001001c0084c12840500c0b16100004d11031f112801010621032000342082c891043d4048601180c82c501d0f080b1a08110010040313600d101f0700104848007520213548490544003d00e945000ca903810240c0130b12600039100c80b84031020003c000220442e05190980200180e54040e2158014503003030784022200c030340c0400c000c44c50006003010300030004c2002030320064114110640786800d0018903482a0b0104000540508061050381261b0020000404c1200c5c0100682071078900007812900d40d2404200c0700c00c02d024103036010703c1500d030404860b0a80c050b083d0f40d2080417914070084180c42407 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 674381825 1250 674380575 674380607
    0x31d0a0b031008100609180f02131103040b01031b061409030f030a03051b030411010e010203210106121406150408100501090605030a17031008060f010e0f1909080f0a 73
    0x410070b05001800b1808011f01070517008001402488203d400f031181c0c06a8002c5418101c555400c51002d00c0e0100c00040d502427071180786661000d52460030b0a0300c0088400c0ba940120721694030040185036001030a14001c0c0340030f100090740b00c41d5403400090a211000c00140c416020010720401d01d254140d0195218140f00b600c5403072011031103280c50002c1d00040301d0040110444401ca41003660260782c030359440c00d40c14070450b03180c03141c826003d503000c3c000d20001d144041c0c1b00350014804580c0080c070136109240a80c8041140045011404800e50005410741c0d01421580420aa81900c3e01e01100d01500e01841211082c2c00040e02a00051600340300f0320007118a4070401041034a00414030b44061a0020845640c5289065040c1c01640c4098481c5c4a090011030000400c0e4100b0300080c3e22461080103444419850000035500751000100a130501e92140d0341041150741c492300f51301d44548125000050150381514022141e0303c9822142031070364801090304800d80d5480400109450301d6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 674383075 1250 674381825 674381831
    0x9040506161404062307050a0b07050c0c0f030c1f0906030e030712091505030f060301020307170a0906180203010e031c0e0703020d03020a031d0a0b031008100609 71
    0x1850802c88840b000e000032a03025000c1000b0030031030903100f40903100704c0007125000f4285209604038074942a40c0480f80031620360700700040a9040c03002c02c000c41640000a414a40d29010040240725100d074421420548622035400d40c0c2400307034400b004100074850f03000d401c800038540300c501c40110703402e4820040310005038000341c04660b45200e805410342450040d0000d504082c4d456552000c4d031500c4900d11400c101503005c00051146441e8443c0c41107141584507550380e0b09024070584e002c0c040050420380a40e004000f481003a5500003000e807080006c509a420083d103601180310041d00b0120700242c60941403040c2c1100d40c2c15000304841080e44210b000b00040021f0702102a12402904410000345a40050920440306e0540056410149003070644401c940c40c0d9001a01402c214030068006a21262503402016003110b54234802085a1800e0110f20340d003000083ca0702012401041800000440402c3c02caa02c541007643c007803c0800309545e066080000480010b25071840b4800c840c0b41 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 674384325 1250 674383075 674383111
    0x9020c100504050325080708031b0a090801060b0c0715020307080d0e100e06010501050a020705040606030b090c03010e0621072d0b220e0411040b01020c010816030b09040506 76
    0x4200c040c0c41807503030380031b400c203810107200d40c41e1410660002401700803180c0407540b00b07034951003482c0000d16107440c85495041c5010f040c40c040a0866103142c1044030318903404c1120b80749003030740000c0711310840b203210144580e2009030703500490560003011401005000c1c0828070351082d5545400105001c0c024008841041e81c0100341e03c8140e6007107489240164204ca0014059548540c0080c80800c0715401241c001c544d0300d2000c1000c4581507400f544c0000c2e0345040c403000602c2d00451658208442268150843d414108140440900540468403d5604100c4040030b211250300c820008652070f010780c0c15065a6500d141c0071810100705402018150722004508442d0102c2ea100c10754601c009018180180300d1b199001043c2c050700d00150000c143d10001030745c01a2041c01601c1503100e048401d150f922038800340b10a40708501141c0341550805d202a89090768042d441130fa03ca1250300a1340072600d10710038250700521101d802e80750410044010030050040000d40c0c40d020325240d81e41058500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 674385575 1250 674384325 674384377
    0x80415030b01090303030b150c0d020c150d051e2503020703360801020903070f081b040209040c0302070b0112170a1e030c090e070909020c1005040503 66
    0x1c0c070708a000301d001c11200401400845d01c41e0b40001d44000002e020071040b01c1e00202100300a0b004a445503810341d1000e0490382e0010b5040c4034483d41e1800071b4528100c4010300d42c81d80c5a050040c0403030a010242e036000018100c801d00e01048211450800ca03030b03e0241045011904250760800ca01800314040070002d981e041d00c0781c405c69010581694514907942d00c1c00c0b1010f45070380c08c40b56000b420301c00700c0070110b10b841400189540c000c001c4000010303030b1141c4981c1494100300f0580d0000c444610b111004201a03180860045070030001d105540d00300e10f212100107030080c01007912044c0c01500e480710606429030941d00410780c2900400d44905503a070b07103050144124102010040c920181c410414540c4001c01028007082c40700b6003008140403040d01c1480102c2442d45610100194989246505030b9800500c1c00300034090041580c500d45c60101e0000d0500140762103100503859000500d040c245000380220450049011000e012504060030281d5a94028101641c00a000038039030074804 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 674386825 1250 674385575 674385581
    0x30f030c030215100e180601150e091603020a02070b0406050702130203280917030618060604051e040c080414060708150d02100302044103150408041503 67
    0x1c000203802e04581e24100503071259810005000e10500d401401a003024074002440228007802d49c440c86400c0900f100400140f01040d6409554041c4154009000d100d1840039a520104180e0f82400350f80d42d88400c104900d00b84a5600504181401103000318065074840300800100b4003c42d00003106800b5110800704901c000e0302c41421030450685040905080780d05050071900250000080300076290301c0301e1091400c0c2e806521114040042089a14034001d400b4108200c0c02c0030017000c00e03207880000300701644650b0060700c0c0310b00152851200344218240c00c4080c0560050014071200440b0f200242002d81c054400311070b9560600841480c1000003e501486090340742d46400c0681ca5480700d01010351004451250000a107112100c00358a9050b003d081c5c1208583d0016516450701400399051403012009012032240d40c40324100420404081c180c2ca4030ac005103521416103000f002910b810714880304600416050401c0109100c0c40700098000c03945600c3e8000f240440101b030072402c07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 674388075 1250 674386825 674386831
    0xd050c01090b190f0c050709060905090d080606090d1a090f03190e06041d0f06010905061c0e0601060903050601060c1e0201030e030d0203100b1603080a06030f030c030215 75
    0x442c2443d420200400f61041c0c080c902d04000b42d040400c1c080c4c05c1030729410b04200541e080321400585a580070020400c00d4840c0c2079205201801400c01c501084c00c0044c82100c000d0141803040d50301203100c0380260358084540c0f4846520040c4102a82e101e24240e886001e011201c58009000f0114401c4515502100301c030101c2e10648059240e0180540e425120b0029001e11030740c000c1c0d01800041100d41d0300c204407200700081c10030282081d2030980c940034004440101100d04021081c1c0b003c100a48030340d001d86504010040c40d40d00c60b40c0480103800020140e400907040c035403140d9400007a46035040072034002030307030300920a0b43c425a80390345003540d4803010240d008003280c03240191a040131459201d0340c0c0c40240305260103d000c0d88541816855030f00726860b40c00f405030b4004180b003444a000b921010081c102400390340e0803c099280700c2050003da03484040d0611072210300090000d21640d1052015552024001039281002c4c10010200c603a010022005482050182501040c20303d800601c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 674389325 1250 674388075 674388097
    0x8060f090709020a03060e07200309060d0b0d1b091116030c030903020a060306050307090603170a020c0a090207050115140f0f121f090c030209070e0d050c01090b 71
    0x4000e241c04034420083d4400205941010b554600c00f0901c0d1000807c424004c04860340e849104a821641c0c55503807412110080405a004000d500c5030307030b29070303c00742c800d0003018080029590014002061662a01110090010301ca1000c08a100d0307541c0d0100e1400daa00d440000c0141b02c0000700f0460702846141d1004112840f50315024000a200f02c0280c0c3da10340c801c8c1380008e0040d0b41c1c0e501203001c14071031381c001c1008291602d20510242c181000780c08004c214550080c440b036807442d116642800300b6007044010304400018240307010741c020003805070640c1018040060343c80d600c050400080d0001c42c1d08880c81d500307000000023024616082c0e00182d464003200d50f43e040085c00100018490303600040f5401003c652a4127007980e85001d014688a2550310182540e00320811f040102e919040100d00203092400e005c9c07001141104000c581980d90540341c9100d241c440080a68018182d929a594804240ca60b0b2808000c804518040701490a807540d866003500ca03000700c19207004480e40e90b0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 674390575 1250 674389325 674389333
    0x8150601080c03070c0605070e0f0102010203100b0717030c03040c0501030903020705010f12060f1403120d020f250c080c130c0c140106030c09063206070c08060f09 72
    0x30b404600040001d54000e06181881d01c5000c400341d4500c0150350302182c071000800c07a02d4104900d03600700300100b00c0c41c11500348000c41c42c51900789150b8881046034007440c2e024840124160041000607940aa2200e142d403844d5a280d182003030640c1d8841d4030856007220050380590740040c0383d501a000b4050500e0b070513000f80c1400390400c00111006000002e2410800541e44846d400c40440345c030402c1d01414031000900386944c1404440030402c09e0205210b40240c0c090080e542043c8001c40c191260000d6107070f03002d0394400110401d02d2a80c02400e00b0b40591140d03041b0708890310b48407003407d00c600d54402c1031220304082d6900001c41e21242001442504150070b006d140054100302d50242c0703461085820480d8030b0344242e80703c0070940c01c1200002e0b4040d80d03640740103105200340024440002c0107100740c03d105590401700d207022a141401e490070b00c031042c409241d02c4441c44a0080710203115010780f1858540c0ea290400151110075441040c01d1806100d02145912013110602403168860300018 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 674391825 1250 674390575 674390581
    0xc070f0f0312080a02160503090307061b030e0f100309020906040b010e060c0a0f08070302010f090201120b180a0606111902010c050313030b010519050306010501050a090305030d02040815060108 85
    0x107540d103000c000c207840034066080154129401b090311101c0036880c000d200454403000f4103402c1c14070703110142d0001403e203c04221802250801b05841812096240c984100c4110810001ca401050301b1600c4a500c0b500d11030048008a500d940402e45087c006c0710300001076120388040c0011170b0113174481280025400007601085091240080c1400c4149000700c0300c00d00000e40318280384409626003280c491900103030350018160b0900484140d8032190b802001a40480d6001034050910680e0f00c0f000300c1e440b400086035507620b0313000e80c104180e0701d2050480305207040344c07030701c4c0c0240300740d01600d80441c007910b0012043c604d00040c0c00203100299004000000c4841d001900c5c1c4241da242c088440340710400c00030a0398030b000079034280218400c100300c0840394106402c0041350002848110028040c140382000560303000185141111028200603565400701001101d00c0b440700d40018006201c005a60742603801c50f41d0003402160510b0080d04e103420020301442058660640c0c0c902d0000d00c0040c04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 674393075 1250 674391825 674391827
    0x627080601050d150e0105070906030506030d0309050102090d1b0b0906030c07081c050402090114010c26040e07021203360f06070f02071d1302060c070f0f0312 70
    0x1290015030b00440c060341c80010b01281c8141031750661425070310181d45690a01660700d4000540c0000760070541024801407501d100405e0307550300d803000f1010426031255055824000c00f9411986103440107001600c91800702d0a11188410035210001c400300000d210001e1100708103c284c407890a0b0050070645942c036001402e0005400c5500165031102080109802c100801d6440038002c03411240003003070625050041080811b4140d01c40c411000303108000c04841e0703901c0364500403c15070041c6800e2440c40c0b0140e000703c4030341c0b5500e40320b07900c3d400018010866180c0e0643c1d481c410f901607403c0b02c0740e07444d03d0200101c203400706880308040900301000c10702c88444903540800000c50390381c0311041d9144409030701514040f0703c106c180c02d041d0000c20070710140e40d5211a006c0403045890000380b079028504482c11854610001d41000800c8001c408102000341c0e6220000d8010b030020081b07911840a0354141d41c8820035441400819040001c00284050000740d0038400c40381c21a200030703d04044481c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 674394325 1250 674393075 674393089
    0x2030a29330a0302040b041e0609150f09181e110d090620031b0c0c010315080d08091b0d0305070201030f0f02072d1b080304062708060105 61
    0x2c240f6070203100116440070018058001401c1c98441003441c54648601c406d200099604038204103d4107075400d1169902424140c0702800152500c00d00c2c119082400310b404c2c01860700304d05e5800ca100d2100109014458002104160846800022a00b28402d070070040b10140b11a07030440c1c030411b0190000b10709241d0312000d0b10b18010040818a6201d54400310b9130080e9920000169400101c2440040c000000300710038981682490140b41008c105071065480e051610b0717441c10503480d00080a0481003510042008107014411110101c5550401030204002181d0640c3d06e40300e80101c15000c4900c03008004800368000d130184500a60948048905a006810507810f00d52a03040c5034403030406510440102808100b0010389895480c5401e020001d421400d95a0281d46012003c20f4100c0040703c603940aa840906405001c2400d00d0341d0990300c000d54821005030101040000d07141d904480b440e1350501a034410302103200c0301ca03e0046400056402003041c1c40d80080c0c018016820030300 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 674395575 1250 674394325 674394337
    0x2090a0e1e0403020f03071a0f1506160501020c0a030f090b031b0c07090b011202030c0405011b0b151c05060621010e03072f010302030a2933 62
    0x220550b941d180d0401130b4145164080f080440d00c0c805801c10b1149848c0700445101e800110640700b003001801c00c4040318004142206403184110301c00102e0400c00745176a05500040c4c1d9010f00203548525902000c50780b82e254071141a40031030090015640c1080c801c0ca01c0b0b90988003406495819a1100440000c498051660300c003041002000301c880311010400000004007080c61000c140310800c100014142800e5481e4a141540140103100030002690150f40641e82c00380b9107141100132210305421415400ca8000d84a800b038034080c00800a614854200c0119003a106841d810360b086404039103640c0020b401a2050304100e01242d0a49030000c41f05034405540028403280402010782182100c2e40c418007080240e10000d44241040700001c03000000c1404118882138100205101000e08800d4410302c6041603400800261406260ba10a255840180819041c0f0910040c05508514842044280300301ea1030b101d0090080d940c071500b8201c02e81d0362184160084808002c02c100c0344c0080e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 674396825 1250 674395575 674395577
    0x7030b0a030203060a06031202030a02031905160b01090b2209140d020f010e030f03150d12020109031e0e01052116140403020f0603100510020102090a0e1e0403 70
    0x504000701590701001403c3c0195404500090154910714141e41d1101100300210309641050040000280e000703c26240ca12072002c442580507144000112010700c105c103d01c509200180660b00705021581907011305a8404410030050b2420510801a2161152203000d800d400c50b07107402983e0840383e800c03640c140761040a040b00355043c0c0b20b50a40c108104c00741060f00503881001c4039940341c7c4c424000d880007160144091850009030b0317181080c0c40d11004148c117414a100c082340d0740c11519502d4100c0078654014080d804e91050000c0c1c020302078090f03441d040c0e0009a401c081660081d110b41c3c10200d40e15000d482d41030a02e0140001550160004500022241c8032002c5559480c0c10060350148107d86a03000038861030700b2100050404001c10441c039036840f505000520042e01c0d04819054061405c4802a0702c07a6202420102c0302c00302c907003105400008070907062000d26015006019000c40031281c1e4a45652a050748841c807500407620b902000d81e0922110800e2480c20440c41c0d080390103 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 674398075 1250 674396825 674396839
    0x80a020708010c031a0d0b240607080a0201232e08160f14040504021c060b010320040e100807030b01031202030901021e030903010f230f07030b 63
    0x41c9120aa003190703515002c1c0e00129441c1c0980d090304040c45170700c2e500700000403aa102500e01c042d85078400c03103c00c020807140940210000040c14450044080255060002c24440d0780e810340d450076010039000080807501540c2818045280c0c002d40200c0e240441c1084542c0c519541c0d60211fa0b00792025024001d8581038050300c5d404200400803845080c0030b800140010462220b08000555008102e40e2003a0300a107600f41003440100c01e05002190032030710844000c5041d0300e490001071008101601e5503080c9840520310681001403d4105519900c1c00b600d0400c08640c146081a6080c0008c03114010220801c00c0306010340c410811508d40c2108100c9841c1c20703040e456122451801000e0381098510140043c01003080201c0c1030188488c201c034a02c00785082000140001c1d507107001ca841103858042d030241680c414210104203a41900000034020301c4241100c1014000410305111b2404820f5841c560200341810800c480038060002503101c0e01260761001400c50041c44041001580030603 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 674399325 1250 674398075 674398079
    0x2070b060d02152b0b010906020d0c02010e12060406050a3c0207080f1818070e06130f1403210304080d0c1206090e0d111c0203120702060c0403080a0207 67
    0x19040d0b5100e4013103462402c0001d95550000009050103000380e100604540c01510381703110955006a1041140ba82820400a000484800103204000340c40390b080c0d01784110b104010910910341c018501402281c0801c000a00310221603031030103618100b000a03440203009441000083d81042000c7d12a0a00c00040c101819940c500c900d940c000444180740e10b00200720607020b003075040080025043d08840c90702d00c41820f42024006484000c103003a00307000d64440f0421039a1200c0381110355942d11a41560241e42e110740e880741d03d04a0500400c01c09000881500c08039050004400d654040e0090000c80d51144038040c410303180e440288102d030001c201744007003c0d040341d0030b000c0d0403c075506a4546603003040c5000e400303d040740d070180d002036101420442840c1400a001c07034108140e0b4018a008007040c01c1100300c1525001140300d100517a411fa8541040c120755010004d402802c0c0481108000358448400c01c0380d4401080d00c0400c8144020007040002450303920080c00845840e0041e9100c4913 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 674400575 1250 674399325 674399377
    0x1c1407030204060b120a090c05060702030c0402130609080a0b01050907050418050121020a1206020c1c180506030c0c0f06190e0303040f02280902070b060d0215 70
    0x2400d55030042c80180b40105e140001c01c1d19a01901b07900400c90f00c81001450030646444101065620038a401882c000400105548007800840e100e0341001d0030030b668075162100c81d4000703010644900b10014044000100722602d020071070122040d00200c904200b83d0900c810400485000f400c000c0c10b024040000061982c0312400e20003e4020b03026000a407503142c00e09900004464941e004100c035480c0442d41c00680e03503d200720003520031840e02c43c601d00102d40390500081c441e01e03611604610520079170025145103041020700d010b425a0700c00c200b8050070070062041c00c07001c2c020194040c006100045032180c1c01c101a100001c0288112200c0e40181c0302d0300c906140e0251074290101241c40c1c55103c6200d001c1c0201420080c00300c006602e1490941c40d402501e04103884000d100d002c2001901040c444800d4200050380b400c82c05250307069940d81090340007548003601c01c6420360032400008030070340303481152481c510f80c024203a0680103c442110510a0b840300356805400003114410381c0003070b = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 674401825 1250 674400575 674400581
    0x711060d050a1428020913060306020c0115080601060c0c0b0d0e0712050c12010e1c03050609040b2e030302100608010501030c1e03020603041b051c1407030204 70
    0xb82e44140d400080c03500340469400b82c428801040c407940380000241141e4114044040c2c0a030200d182a4010b031241c04600000c0d1944007006a807182c0c4904089000c410300141d80d00828214060500030090443d40e103040380c10f8940d09200340075141e00444010054507003d860030a10891040e080d0510103a1104400e000541040c4040c40690b0340d02e9280810158042261401a01040e0070020612100d07540e05035032418210b0410b8000c10b40c031007a0010440e8250000e0481500c8402602c0c1c02000440365070070b442c0802030440000078108801b0651034101000607078012038202070840547d03556005a8888034101c80183c21846040c1e41c1c001d00c0080b0340f80010b2020b10302c241c1c06040303490801004601526032030b8200c0400c50b41b401c8010800980c40c051a802112030408100f0000125400c5881807420b43e80d10180d04490000204400c0100403154802442d0501c0cd00c015510748450a03c06000d4000101e150f542c0c4007a40700e9801310f000d903041c0c1d8003100065001c4450340740d00c0768041001c2d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 674403075 1250 674401825 674401831
    0x311060609192d1e050108030d0906060b070f03090b090d020d03021c0203090306010807151d1801210506150f0a060507050d030c0203071401090f150b04110711060d05 73
    0x3c2a0350b100201d00403403c003000c0c0d4070501688500e003840154100329480c2e84920074841401606642c82070701c01e0404c14103405c6840100340704407849403a80d4650600f5400c00800f0017040b03000400d84840410302e00426030644221040c0604a800d40701070703d81c240b05544d0b01c00c850a405510980c40483c40c80080808000e002804d04c0e4040d5480d00b03640e00600d490b00310103070041c8100c0d030081a011b100004009010000600c00e519200c0c581003046498a241c1901e00c480403504028000c6205007100048401c0d107049441590341074140119414503031505030b08210340100240c00c4503011444811250b01900c105041c028600c01c0c10292010000e8449560760f80018086000801c04006114060010b4000d010840c20280704092908100a48912400000401310341c03124001c840d11030425404040701651090b060f2000840c1070500380680000090840101400e18201704a1403c080c05661071002e10b00c1080d50034000b030b40d52040d064500641c0f04035040303141030120303400512150041e640 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 674404325 1250 674403075 674403161
    0xc080d050c0d0e01021e09060c0f1c0516030e03100e0f010b0a03030207150504080d0e310c020a1b0303080c0a0f0e0303090d031106060919 61
    0x41c0d540c0c54100b80c6400c1d00d03000d030307030480003a44184a402130000041c81004103400f20f40340240d039510010750005075680030780c0080118034030482031003089050002504080402e90044003110362009154100d0700340c420902c00c008070820720740080001900550724418440001000c1c1e4814444603103000d0100c5082000d01c45040e445011030001c004800e20450102500a5402c0283c141c2540c602a550780c04510031301d15502e060100003c0007502c0340090318090b00c4540300b07807894030842d40002485210042c046a10506402d0901030707180c480d8a160300625030340c11035007041c182d02d49050200201590414103003580503031411080000d00712000a0038105081448001503815410005c040c142d004041c03c43c0140700308000036003035400a600c01c1000340640380c0403c1d01000700d00800d0135401650011600080c07010310040c00c26070030403a08142c7c840d41104860701507071a2801c11100c1c0b07000f40c891800d11000c1141070404450075030001b402001c0b00e01a0641c45101085810185415402c8010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 674405575 1250 674404325 674404327
    0x206150a0b0915090d0f0615080d39150501080d140706050709080c01090608150d02031608060a0203070f1206030c14030f0d08150a050402070302071a0f0a0c080d050c 73
    0x2c07c202c03d9210f00b0800b0381c08031454845580c20141d80a50340c6501c0794400040c0450603004209840503500e11101e80600c20100c0703840d61404041d02c3e00d0441c084071301112107059811208040400e94850705040780c00060041038a0030b600c9038140c9040c1e01c1e06111031000001000312401107001405218010300720ba0780c0b0448814a090f51280c10501340f03241490402000303100070404a43d111900d2504006068880c00c8400701c0040001c00c0c60400c11002034150040d2a5140c00180b0001d00d50401c84416106480403659102d540c58124441202c00c3c00218801801b0082c400b4840d0405251220302224005021520398885c08191801584103000c8002a1003a00304541001e00020b8424584a4020002100d564401a002e02801071001c08045010300340084030f562141003400040401401c115071b1403a20341402915428940038482d20362034044281400820041d04032004111400042c0c1d0501d0b503102009c84000f0b102d41410b0741c0545044c40420341120f003034880c030380c000d00304181c1003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 674406825 1250 674405575 674405603
    0x5130b0412050f031806030606070204240501020a021f120905030901030c02061005150906162a03061d010e0c190f0909020315070206150a0b0915090d 66
    0xc54900260700c01c1c921031541042c40b50030004d0250711710801a0f90f1040340c0854895840790b020036180d0081050213135200d41098040703001000b0b08071030702c43c03062803401040704c02580b80c5005a1780c3d100220300094012116840d036100c00002200c00400c5244140f41060710341100c103071040155550114190344039040051508010740c0c15204900080601d070014100502d004090a04034112501c038036402168411090100814444116181004d0050401d51030356241c1000c00c41c840c042d81000c0390503000e0818420664000c0306020010006c03c100d00643c482c2c02d5541306805000381d204041c070705902c040b188090030442800fa1006400303001d4002d1101000700810440710010380d80c40c0f204054000d4100b0f10200c019020300300f0544800d80008224440e02e88086480c1c002084807281601c0c2200d024001c8140e404104180946c6109542088910701c050400821146510074807030300c604104a9024541444035141c209103404404442c10032420714085103141011610807981c43c0020010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 674408075 1250 674406825 674406833
    0x90307090504080423040f14061014040b030105090105180c0d090c091406010f091208120c0318010c0e010c1505150423040f0809060a1d040e0d05130b0412 68
    0x5a1030347e8182402040c4015076903c204403102d00d00241401d40144080060004014000c50000500812001415580300c0d503642e4100f0380e68000303000310351090043d48000a8940741460481c903101015450844081d2602400031915030700c88444039140a459155000104181c00074582c01001424000701d00f9a111540010344400c00030100c9044c400c80c800c07500307401e650052038001a10075200f0384c3c0116107070504100c2d002c1d02910b415180b2107200c140c208060347c00528042c45c00740d80c41161048a0480c1d17004c01900b0ba0700d801c3e060310002604480c00d400c0f20362060f520445038500404c3c0c4040c0140c0d0142c00601580c204441b802e040d1160401840c00500780351050b400303d130039a40c3d4890403003030802420346022034010300041c1094002c650301c8000e0000510403103000e0713140240155952003040744007600803a4141250420202c52a5901c080c2c0d00741401740e240c4c100c0c0000046c02c12242940c0080d11107401035180300c65243c0c1030020201d58080086c0050018040070255403c2e11022460 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 674409325 1250 674408075 674408081
    0x110309010b0111190503130303090602161d060d050a060c1b0b01031704080102041202130e06010e070509090a15080703050d0e010318060c080a0209030709050408042304 74
    0x180d40781c100810007105070b010203008a0004483c003803540003541d0240d46400c085c2d1031809403020b04034090703000d40701c00020035800051b0407081b50a075800361600e014201080080c01174952140b007038001080e04c80e402c101130781c40078030941c44040244a01061003030383d150945007244409085500903070343d17103d5405850b081008010641c0780d02688440030010f07542e40c5d420242061000a162a0b0300301440140705071488155006420700304021520340342e45100503811050444801d0f0301a010b405401807100702c060003040c00a5500170018012a40f0700b41000176440e00042c812400c100052000e03003880e83c0c07841400c078040c000c0c0a5001c1801002c1188149200b1180d92156250754410b520800024001142c070311012801c0b41005e604000800c0c0040e801b43c48a2019000386034012100a4100b040d1a802044010250303640c0c0203480d9150031a80c800c9109031005640c1c541d001d4941041032800a0304541c1d4424070520440d03040c03550342c0210020206441a445d04051051503c005103810144 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 674410575 1250 674409325 674409341
    0x2041e0e010f120b0402043c09050c010f1b0b01090c020d17150901180c05090a05040f02090d03200705090f040318090603020312031005061c11030901 66
    0x400030b01c0d05a450408100c4402d1441e2000608034459100050150f42d00c07a80400d81035589041c01804290091225032170040c0c0121128800401d4407851080c55485813090190440c4c1c440c0052100300c10950054440014809880301004014000b081d41307151100c01040d5228410b450401d429410081c007802520380c9403201034119845040054007042c1d01c40080000d0f00b010300007241300c680312840c070585c4101d511041503800c03021103000000c0144600e1000880d148038040104080e0b814440200c41d0303442030b081000d42c422320032582800145440d42c1300164020f1086001440c2c080c50402250f8511084d210903800b09101500340c0d41c070b201c0c076008101800901000501744146c140000601ca010000c1c2140820000b29000103041500440c40309804c0c120310501c0200065403120a00042c0180e400100d0007405a11035030750300a001c031070039a401000d10321680c0716594140b070f051049030b17040043e0700e0001540a010090081c400352150492240d8540c0484e41d681ca0008481d1742560301107 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 674411825 1250 674410575 674410589
    0x9011d011d030a05370807020d1e030e0106030c030b0403080a050603030d050402030c040f150501021501140d06020c2103040c091104030b15030d1b0303020a0302041e0e01 75
    0x401801d03000075880002c50b40c1c001070101e0b800c0007504408010740d000002020010301c82039814200c41290b15040030501e03110345040e40c00c5a000c0c0303403c00303400c94134010103502c16008ac4210128090310240260000302c50581003030000900c0aa0b640c4910201422552040c1c440d04911b1040c042450381c451076007540031110307103070600290a140e008039030b59200f0000b06c0d4480700e941d4000700d0115501840490100300e0010024840706020305508001000c03001010f1701d4124102000007210350010461000715404010304580f01e80c60300e8030030f110b440450341d8050341c49090022000300150003407003d005404c1c0d100000307003c41d000c504000c180b282d80c41100094801d038180308005c0050b000702824025900b4141001c1603c0c1169010030b482d500480d000202103200e4101001080d07010701c040701004403400c8040b100280890002601c503803205014002c000c1c400c1001c1c030400702c2c6c000d4005041d040712600d0700502c0c0c90350b260f82c91500015441e0001416034201c00c5d0421441000804040c090711071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 674413075 1250 674411825 674411827
    0xb0603040507092d060509070f0801120516060e010201050703020c0303041212140609100303140f040e01060e180c070209100803120910060e060909011d011d03 70
    0x10a8840300c1c2d848190748200340e407080c1c07245030078004e0380340c400b0744080c2c2c0c14484500c044a120780b005402002c1d04450050078055454800081c1c0c1c440e114a02113520900581c903078040503400c21812071400c0031200c01c255030510507001310348002d614601c0004024001c40e0f40b580c001c407003901c000a080d030300058031010806006101c981d0f0310010100032641c002e03500411401c5c4481c40c400c4150b4000c0d140030343d13601e03040746001e04c0e02415002036800d607442682c0444a9100365561003940c007043d6021404044c002803040030002c500d52080c2c00041c14200c1c984d204250500c3c0e036500321881c0cd10000d8002e0b200103112003050107120304020078003850002090803802d20601c0c005000c46014001e800c0080d116820800208006100e000c001c0c80c0900000c000b40d81d6201d44180c50024949410343e900c4406220b00a003841c044800d5100c2ca80c2600d040c2c0c09400c2140d2149000c01089000182001025540e95400000007001e11412003c2c03580d0150004205200c1001105103620b240071104512900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 674414325 1250 674413075 674413081
    0x41d010b0a050a03061a1e13060f0302070503040603061410020613060b090a0212010b0702010504060c1e030207151706060a02280b0c0909060f031207150b0603 70
    0x151081e20040c505610b05a40c40e02541c40003100a04410b0f800074520408940c01d024041041c9002400b4082d040c81403808800d402c0d8603892800d2207048006014002510002d0080d58400d140c00c0e140d481e118500503084c54041d45420342540d125030720640200380c0d039490030408014100c09004000c2e20444400070016841c80d8080c0d2668070082c640c4401a100d40f036000100400e41d4084080804060080d219520300500320348003d6003e41a0300c0c604c07540c500000246e40d03003035604940520382c0c180e403000d003440e117410000c0d56852903140f401c840041d03582e180d00303070302a458010308100c86010358000e116080c60256032121071702c481d81c07400d02000040c46a585200246100d07240d040b0b1404d4501076a900e454103c00c9041400c01241c1c01d6000319001281080c80c0c1a0302c4079034501034019003000d0620b45131000001d071240310380ea94050f040000d00740010300318030703104100e1032000c00702800b17450400d00c0d1244026030b40c1e480150100c42e1204c040c01c2c0d90202084034850f8400d019016138400303240d41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 674415575 1250 674414325 674414339
    0x50a0506010f0345050f0705030a0c03061a03100b040e030a08011203020a0c0b1801051207081b121611060a0f1b0314060103061d06060f030408041d01 66
    0x4824000022030107401903540d0103400140b9100d07030361501601c01405005134080c58002d407607941003000b140700342c40b401c0c8010410386000705440000c42e500c403941c103010a01d1691000094010052070f50f44001c8003030312260b1562024803000781c035034805800c0010301a840008000c2186d5a58880c0b034817940c818032140648580120441c3d0640d0501e08007502850402d143c01c9150846140d00103014100441000581030080300180041d88480700d0720000400078080119102d000b40d0310700040744280c4102041d403142c0070302001c41e0403607a14501c18140713031144540014141d104481c4035042e1170000d4100130124200303542d8000c5a140d42d14164000349520309155079078920207004a40801e81d24915400b402c100b1f0f0303100110940b40070b12030100110b481030006e0010000c1c0c20f04004101c216600140c1700e584244104070640340401540703500d0f141102101c841680c00108035076042503013008981c040e86660000355225501c91258555260b061001800074075241c24820a1614054401030080b4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 674416825 1250 674415575 674415611
    0x302010507091e0e09030f0703080103031b0b010b03070c060c0507062307050c150c0a0f020f0d050d0207050a0b0405150903031306140906090714101110050a0506010f03 74
    0x244c0310b07603400440580b242d203080d81c00e61060390015102018000f469100300742c1c000b81110f04a07030203525415040f081522146032814221403000300000c6080c001885202d5510300696004030f42c5107852402d01c186503440c1400c41e04d80c55490320103d5404a201c604001c81e03401601c04a4040448a02940000820400e4442c07000342410042c08000305400802102c200010607000781a01501925410600c003107900c954028811100026a0300181c62406400012210003803d14400144841d14540710112241e4001c10400391209170200701c45000306604000441c0d0440c02620000c285080515000e40f42903140050340c6024800c0314100400f100000c0140c982c41024241c800c101e0b0841454000d00030302c00044d9417008030070600c1c03c0c0300702c00d400007481521900c0c80342c0485024584a03842020145200c2d1059079010301e0200710206058130507400c9000f0804e0140866421103092103818064810032100340c08000c0d5030f41d00f0000d00b0741e0312051400c0880c0c000d060410801c1e204404c4000c030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 674418075 1250 674416825 674416829
    0xd0b15040504200a080105010e040e12160c081608070e15040902030307110a05011407021306080a060c031107020f2116030501141003060b0303070602070302010507091e 74
    0x4925640c6029003560b1200f0214125911011000c1a41e0360b46030901c040c002e81c4081c00b51b940050145070301d41c1c94030305047c81400400c0c4140001400004206844855903032310000d08014448920b10054002074007035200f03040980300f00d41c01340503a10f508181d45102d00c942580000381c69070000608000d5000d01e008582d411512418822022185501c041740103000380c460000d4140c8030002c4c440301403041120201d6000c0000300c2d244401e003941d600c01141c403140c81502d0300140728001c1051600500d4001c0407003440d1844610007045283e9104440c0781480c80101c02034640c07a40302c0031803094659140c8600000d04011046160510040f40c0110326030b0640440d18501032030034888000002d5160014002000e0b41910444103440f01c4019098510142403108035030940c00c2107101a12095a000803920401d0602c240c013500600c0c5403a400043c0c07000d1201160180010420a00410355500080c40740354002c1d0004511810f0a50b4010042d110313960203001780d504405d42140341d040d00c00302d08000b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 674419325 1250 674418075 674418079
    0xe0f07080f010e0a06150f031d1e0f0105010815161b11150d060b0711011b02090705030f280b13090b10060201091121010e030d0b150405 60
    0x2d031135803448440002444c9035001410008010005201e1055015802d51042c070401d0b034050141201e4002020001d03000000614080c0d00011080443d465900e803034820048807032022503051901c1d9030180c81c05c454003030300002070307035007240e15919403202241c3c00f403a0b00001d8814040e841c43e0f00c000b000804146050030310300401c564051140c0f0174021001c12000c03c00340020125a4604c5170303140d5000c0251300040c0d0016196041c080002901710242c819500c0d10b0f03411007100c070004402c0704011690f000070340c03482140403182ca155510158030340455851041c89079455656482c28001c4401d03403510f0f401000800d40004070080c00e0309103070607003d45c10301031603a020b80442e2188540d0000b44280001d980e480384821304e0a11150305021041c90f099000c1e82030600c51032201c0383c0728a001c03426112040e1019000141c1d05942c55002c6c20803c812584010300c015403d10320300e4078500c4447c256001c011445625500210b03058a030300302144107080c0010022102c2c01280005510004410300071446064 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 674420575 1250 674419325 674419349
    0x3070b070f0c1418010f09021b01090b0a0f1505060f1204060f1803051c0209060324030a0c09020a050403050a0f03020d26070203130e0f07080f01 64
    0x4100300300980e04040603988520124002d80d101c04460403d81c2c3e0a1180354032500c0c0c2c000300040403998001006050f5402a80048403450600040e10040d601c0382c9400c1148540d0806044d03001034080c801c802e00301d0320441e0400c4440c20030800c1c840943e81010301940005144c50340740c10340c0c3d8842581e42e60840750251400c0d9203500381000a04c002d40102c00c0800c08828040007000100680c0d0380c01116a00e542c0e01080000960503a03c20045501d00040140852030802c114140e1501d00b12400318490b54100d0058940000a0042000ca80086e1078034140d1034103507154240306a120b24900c3e45441c0069005051081c5242ca40d14203440785441800f804650006004040910460840d00031355000f10440e01350340510b2030080c200c0711960400b5001800303002100d0740310910510024000080d00b04003501c002c02a4841086a01d00290100c011b62004000200c3c001d04008040001008140580340062904000603a031000009000c0d000b000030207010031481000498587d4156001e4103840e03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 674421825 1250 674420575 674420587
    0x6060901030c020106080f030c01050906130f05010609021c060602010b0609061e0a2304180c0c140a02030111030402010228050a201f120b0402030f0702060906010503070b 75
    0xf07030700500d80d5401148460050024120f9554000030042c9000300201000700440c3e0b442e903814945481050742c1050a0008144002001c110034001620515008400024a255680b100b80c812030340038100ba000421400b1004101032007061198800402d6140002c0c0101a07020000071164880c54103028494040400e420050321020a103020500c0341c01e41c2426612886800c01400d154a11031010000c03403a0303481381b07101c41000282035904441b6140c03910320540c03c0d074080c0b0402815410b1504001c20200e908400e000c9000e500d680900710806101520343d0b1a07060041c5802c0d20104007403190003070401c005220050741d001800d5002c1c8182c44840c058140c2c2004060004403114250203805841520039820511980328602c07081544c081d0000e0901c01c10800034000c2001684002188000c80540c2c10524603000d40e41282c0c415140740d6000802d8144500060100d03001520447c41d05040703130307040080c00c0e0303010450329801c501490003c140d9503142c070000a40d900c00d64001d1181c011008901 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 674423075 1250 674421825 674421827
    0x605010e0d050c011d120313060309030903020103020a0e0901182301050f150d1b0c02090408181509150705061b19020a0b01120819020a050a11010e060306060901030c 73
    0x70344500b500780186030001c00c1b40083d10b580d540340c00030403d43c02d50741d070310b143c00080160180c4500050180e154941d070900b21301d1500150000c2d040980304c4814450840c540d4095072b030360b4020141c0600b09415200060401c09074000046a5180c0044030240800324141c0310030400403181c05044650403500042c020084d00003080c65054101000500307040c011400607003240483e0000d80d82c40c0640e5281540d004451101187e40b10380c1118065040f4600f02c01203404606000300504809040280d041c00100f01e00000c01c5040280640c1a5256800810382c1c00c0e00741f4102e9041d034401c40b488600350b81001e60b81c1d168030351100c1d00588115942108584001111020002035849901140e01d4082011604043c0030f1749071036014604035900324042001142a41035024451841c981258100382881d51100a16000072444010a41035114580e00d907400250100f005920f0548906078030310204001000252a4201d0112003502c9000d084c020859241c0306c01c42900c0b0344a40918000c642e00390000c00c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 674424325 1250 674423075 674423117
    0x8010b030a080a14130828060902012102030a0509120a030209010c0f0609020a080d050d09080408120d05060a121b09060906050108130c0608090708100605010e0d050c01 74
    0x184051810802203500c4100e070650100c150104e4404000346c5258400b021092911f40c85c4541008107140310420b004404160b203684400340152060601108940842c041d40c103140300c080c40441041500001004402600d078010181c1040200000f0300c200415001114400e02030325040c0401c140d40810310401c2a80f140a400c1d9070709800c101c202160784030a003040030207005080e8003680160407090300082c80600006084e400100c0725912942040f04420302c80c009043c0700a010b8420301c50a00000c00c03810014030962914078000300119664582c071400000c1503070001031009102c1d08890100f00304c0c404d1266044481c40b42c0c070045a1000000480c007413003503040345400001496241c28004128162594401c100361a02600d0380040b558031800710b4818807004440c01052a543c60004005803401450005c1c1c000b41c0002c180c1e043c040d00c504603149080c82103903502c500d860312144200030558210180c4080c00c00d09681c001110109034443c150384840e03402c4030b1810400041c03250408440426 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 674425575 1250 674424325 674424347
    0x15031005090133211b0302031f030c03030f0c12050309010f0b0d1101021e010c0e040c170601141204020f1f0c080d140405010608010b030a080a 63
    0x3400d5030102d58544182100020320b100340322000c00c2c0d01591a0351452683c00118002160a40c0c4a031410a90000702644680003002c800d0604c2c0d44405052107905070a4205c120751004503a001616450140f109548000c005a40d62a01d004141b0041c40425021030740d01c02900d405007420340c19400c6080381254109a0380364040c0100c00200700d848d0586901500031800b403c5810002d00c00c20b40340c440c0d06411500081d0201c2e5021441a8a14000a0001440f00c101c502c0500507980700d034059454649440c84501103c041c0359548116070452240c01145544a2441c261070800c51000000c2000d0141382580009141026407079001403200c0e8490101c6100c1000c0d42007480386c4034505282c0070442081c5c20340d8100e204005000c0f2007111400c182c5114a20700100304110440a41e980205403665605043c050354019010882114001d400303000e003e540300c0203181031202c0c47c40d01d420710340e0849400307802485c0780340d0400bd224501039034001812100c9a4112007581d55a80d000081621a070020f0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 674426825 1250 674425575 674425579
    0x3050a170702010509070f0506090f03010b0603100306180812060303040f030b0a0f020705121c02030f0f0612250e01060914010c0308070c0c0302061c0e06010515031005 74
    0x650204a807a82e419000130303018182d003401300e030001e6480d02c41c0790380305141901600380c004606002601030791a1101c0780400042e40075000180c040c03220300c0464400d0b03100710380038001c0c091103d0003003040002900c00c101c4a01c040114075006034a031965080c110344150118201c0c040b8090340890003a9a0500858008000d10f00d0385004103030703680c035103003181400c01c1390403503042880c105044202c40114000c803007101340c2c400302900c0e146240101c82c0380160049410003c00725117210f01501d03407090920080d4010070030075086e90480d103840c0074100749010000303000c3d9010300896580f2041d040000584503411003051994100f900f8803903800d4400c425901e034007812050641800009030310360407400f010180e0750300c814411045400e141c015503c604416400500262903140001d841902c661148a0780794420b01c4506d00310740d82c0c0d4000071519000745a5000b0740c040300600000040e0910300c98100b14070f281001802903585004000390f8800c6c0e1304180300d0040b000c00400503103084030030460310003d0100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 674428075 1250 674426825 674426867
    0x7080406090c0e1f0806010f0b0307180e010915080c0f040b33030408030a0c26011d0c0307110f010e07030605152d06030f04020405010b1603050a 64
    0x28a02c41c01300a041c0a0f40041c05507079801281941c00402e01c2410788684588000d02c06143c00358000382980000c0c6910300308688211404020400f01041c0d0005010840b140782c00e650424000034111a0f400074000c80c507003074000c2e0400401102061030044420102c1e41d030035502c035610703012501030b1060191507603001600b4103880340b50411102044844032390454442d002c1c4030342581003000314442594050a440c00a20000700d0340e01d4203030846501c00c80d41e031401041620b480140c48140295030403900c02010b1380880144619800e00c000a0b0a01850642821080c1090f08583c1c810744400b4111030104100c800c803081c1904020401c4900c0c810842000704007642c01d03248a59204d10741800121041424080031031800725042d00034200c0500d0092080c260141101c0c01040ea2012040310710038030320070604001c100c1d9542d0b000614851203155035070b4000ba18280c410030040701d40580200c50100c00500c003100c1091136100c03523440c541c1d5040c10aaa6901143c0310151500266919011070b0005 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 674429325 1250 674428075 674428081
    0x10f0f021e031218061f080f071806050a180213061d0406060e091812040305250311030a0b090d0e03010b1513050d0c031a07080406090c0e 61
    0x510848000c1004640c490b2500d2094104130359094000c200c0c00c0e440840465450060003000307900d0144e011100d2003500b60ba42041d20306103041c9402030742d09a005403200308000c2a9445800500c08500803080224505010015400d42c101d40151880075031120490705000c5002d50486159686001c54a80603c1ea2001c00408004060a00c60000030821010307412350309180c0658011388155441d0f10060802c43e03814013165030b800030204000391035002c41d0038403100014071508000c10110040b42d55a00e04500b4480d00e811069040203150321070707012880848400c000030725416a0b5220303000001c0d810b410b400103841c1c401c19000207817410280e070062040c480400580d84404070013603203542c810010120101402c8804130041130703410074962101c6071851010b1800410300041036210750340c1917588a60100300e0481c0d803400b0403600031183d2941801400001c82042d044810010760040482ca009980148201c0300030380018201a251512803042000c03e039080c0d0090407030800395a03ca4030f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 674430575 1250 674429325 674429383
    0xa03021e0d3203191404020f01031b02010e0c0a060905011206051302090f0d1203150909121211070f051f020315060301050603040831030c080309010f0f02 68
    0x2074000c0c1c0700d40d0902c001c0c280a204c801503030760003908048034071640307807003055501d64003449080000310103601e04144ea1000e0580030400103610511011403aa40000303000c404041c699454100200d9a8504c606555041001a0f542c40f019a00c16502c0a180102c04011050b03e00809032016402c0154004501c840c207040c01d8500398040c148800081384ea01c1001e070411405d120350317255072400241c107455000d450710850760300a030044480302902440040e2100d9440382c0318411540004030865a1a0041c808481d601d544602130b00d1043c01d01c3c18041060407040e0304030b45d0b030a00c03032140d00519481a104410003482414070202e0010f4000e40054400b007100c2d0302d4580000d50040f140c9509010a00c2d4000886081c1034040c0d07816143d0103030103d895619503449059a980080e0f681d4590000784c102c2c0452041355402c00d644a07141c0c5186000700e01410362070605c0c248109500030050300e500910070000a6030380f10b840912403200c6801c001c0c80b42c03001705c5130407404c003950507440598641e07840f82c17030580c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 674431825 1250 674430575 674430577
    0x303040b160e0108070315050a0905060102010c0f0f0c0201091d04140c03060f0a020c0a080703090e0c030a0e010e031c05010902040b0409150e090a03021e0d32 70
    0x1100ca1650070304120300401c600352100c41c02031001a0002c0c2000000454480c000c0d84022614140140d44001441d5140001401e160040d04000c800c01d0310751052100c1c65809004001c10010305061840c40f00451400040c003014000f04e804041009850208042d0390203603100102030b04107202d605001040c0080c940404010685007154003010310307400d034145c6000121720000e142c40018041c4c07a0350780301c881900041c010090701396120349500b0020301141d40780800100741600d01c02d0001c01e403280c999003006019144640d200401d8402c1d400304000d0b54600a0048035031108520a0001c0c03600780100c4d0301801881d14507030032446031000041103069840924980b5010324003503001070095070380f1580c1140a0b40158420701079200300612040c400820302d0b41101c480000b140704486011552440c2910344042c041c1c50b80710f4503803c6003c10314203044e4181f250f40c6aa2440c03004150700c5a901704e5070b1070b40e0383c0909220307001002000d1581c0c0c0c0e18890340300b920b05201c0310082e2200b4020601e5940c400d980d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 674433075 1250 674431825 674431831
    0x31621020c03070503031305040f020f1201090b22020a12051f081513030c0204050a050103050c030d1b21170a0915020708120a0204060f0809060a09140303040b 70
    0x2c24800d01000040703518000040315041c81102003002c2c102032400d0180405400441040d4900d40d40900c051603150035208080d01d01c042031614620f8031540b5090052044829100000e4000c00d02034400140400558a6150b12085a0342c070060780c40f10030380d23412a000e800304109540054148403d0100d00e4550325010494982100c040c0881300d0340d01c11125030740380e0829410910f541310140001c6c41409403023180c0e4010500905104200b07158550002e000c6800464020400981d01c1c001441882010441211452419402401c1820048001038180c4044a00602d91641c05540c66010070079180c0d074428031000c450203801c0306420161070103000e82e030403a030b5810030070343d004000582805528052a10f01e00e0700705c01c1407240701c0041d100c01800380d0b1000e113082e102c20340100849945080480b551520980f5100300c0180c50b2810304070002c002c6202c002620703040104510900c0b1041e4030108010303400070400540080e040c1c071107140000401c0341101c14072800340004401c102c14000615400741c8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 674434325 1250 674433075 674433079
    0x80402011e120e300d0e01051909022107030606030501050711070f05091521010614011b0201020a172223012a050105100305031621020c 60
    0xd504150746541d03594082c10f6a145144003c5814008440e80310101205082c1e08404c00017841c200110f18064291008211070084580d0342e04204103c6024101c0780300f03805d46151381d050041c0032590f0009409901c04180c8800600c01d600c90f041d5034030b0000c105034402154048020310400d03589040c44d500174001110716201041c641c42203c2c1400c580459140180c03202480c0e90a00a400d220501c094804000d14103203520181510700100e5035100e91041c5503850039450261031203442c0700032207801d450300c42c2d115081c0b6038600c0026a01c26a008003040c10b40c40805c0f1040f016405403800101e10f09510030714040d03e07035040841d40d12a001c50b00401008484ea00303a44d01e102181000703840001c00090341c0724500080c40e9545d00e04d15402c4a5101c00488910140341500394104212031104011041140159902c0d0071f01112000704042805941d5004050300b2402d0b800d01d14540703c0c0d5440b44100744c4100601400c80c0080420842039913a040110b1201c1c800050300e2050181c0003940c0c40c041411268 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 674435575 1250 674434325 674434331
    0x30501020912061b0327061009020a020a020f0a0e070513270b01021c0504060305060f030a35040305102a12020d02250b040201080402011e12 62
    0x202d5841d00010041d0041602d8000b540f14441c80d00d1040d0150b0300041c106801c0120b1900407040302101c2c103104890201c4c41c000142c00582010403080280360983e61180300c10780d0041c03040508242e00414606040383e01039403070f9488805141c00003100c408550300204079074410f00061086181c1d000010b8207190002d0b41c2c0c449011900c83d10200c1d0b4000c003009903140c29017189940f8141c5405140c004520843c0d06004840d9a4030600c00d0340360000251042c0f010015101280801485901d80206900400181d440080010300140842d403110081c19014107121709000c02c0c2200300e10030503000d4001c140b1014031441a02038071780c950522640580301c10b9400c0d126003400190310341d500e8231030a003603c417500300b42e01c0014419003241d0718019407294144081c44612034a11810358042c1c0000c140d4191004c40059403403640d812604000726080e0640c07240034550710540b00004140d2094250001e809080030401030ba15480102c440080c120303082d050342850070501c00c0d80150429403901010b08109024 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 674436825 1250 674435575 674435599
    0x14062a061803090a03021513060806010201150803040902070519050703020f04021612050f0c06040b0c03040f062c0d0324030b06041d07030b0106030207050d03240305010209 76
    0x7850340c0c0e00444040c0344d4841e01101d02080103261034032900e0960240c0310051405c2a25150100b042c1202980c40700c404600e8010411000e9039080c0b01d501e0076041031020f40030076203090008059590296024041d80f1170b034009194004d101040020200444900d070f15a401405113140041e2039442da84002c80c01140508280142440e2500039a00a070030404040c6007802c40e00d4540d00c4802e145c01d40c0310400d1003010820f800800d801c5a00500681c1c4025000304100d0038240f511174000b40d070003409a1005d00d014800d200004034890100307448c454200d4400310702c2e0141c9802903040c4148082c150002c4440004401c06c211101190080030004c4036181004024140d2110108180c20038034480902e6815660a100203050610a25002000503000245104200c0400d000751485121220030a03440b552041042090107080c550141c01645010742c00c01c2c5440c0d642590f160800403400c0b0a05886503245041da0703900c0c49507040c1c500c4641d100c51402c81e40d02e042c5030f03000b54062000e55011b40310020007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 674438075 1250 674436825 674436871
    0xf02300d0305070203092b030c1a04021c0203011b02010905071a25060501030503071115070b0717330a030305031b07030f031514062a06 60
    0x42e10b03104010580256103052400410404152a031040140b003200c04005840554684403000d0029036205e501c0e10408040c3c1400d2280c940140b00c61000340c0c203402c0301c0030007005890700b50184442a00c00244040c4641c11480002d014010b04c90968021950802c500304401c0d5054100303000c058080d20550700c1c50b41d01c600d6985480c002108000300e0016040241014003880710980414042c1c044501446001e4655240001d8610a0b40141c031145e04c003040c91420302c4042241c07040e1104003101c11000000b0481e0300320382c3c20b02a07014040c02c1280e110000401846c000c03120010400c142c030030080700c11315148005030041c0420500c25107042400e0303a040044182d940712900d00c48400100f000c10000d146030b40c22240d07503000030403ca001c5203028040304c0001050f074020b051a00e2203500d03003800ca0032448000404540403100490301e9500c02100c200303d1001e1064160740a80c0c0180e911950750900e44004007904d0a004d40c900072201101d84903102c05031808200c0c40e0081110f03007903c0740d0441f21582 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 674439325 1250 674438075 674438081
    0xc080601020c060a121401060306050307060f171305061015080603060c161217060f0a060302090f031902090106020703051f0b1903140304120f02300d03 67
    0x9441e4005808000c0c008030540604024091400312401c0890342045080c0d0001800100780c8c0300c980440c2c0c5a03e404c0c02140303010301520000e050340b0f1070040004214003100404201060000c0c14003005400042400c004401b080d0034000354101c021079aa80c20f00c12446c032040d400324464404a100e200d500c0c2c90201e4403078400f190007034400030001e102648401800310b216900955943d502101d01c500100b002411290003040c600300f1507101d411040203130b0749d01801d1140c2c000303010500c22801380c001040fa907521041c145040d1185490010b88415a00020901c0b003600591142e6061080c40c228a040c92a25440026081c0c030030b882c210700070399a0380016682d40b101400010800e4100400c4129900b407011381c1310710100d420650100d000103208003c22412501c0070030507c0d0301d41c3c01ea0818001c1c09095001c214142040728011b528092401a0a075104101403000030400e9010841c1e1500350355540040c0360101c0600103680300c5031014041480c10700c441413040803800b4000c2e04500351030300d07000384 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 674440575 1250 674439325 674439343
    0x301050c0906030c0a0c05060106020607030605041e1a0604080f071413050403051303080903011b12050a0e1204030b06030703170c0a05010c030c0306080601050a1e05040f0c08060102 80
    0x9001c003415915140704002803600407164400400c61b0b40308801c000b0450801042c3e0082000d6000f5011504015000078261040358202c540a18200303040481d40c0c0707800c0b281c008070a40a8042c006414055005550010190020029449840070070040383c030581c0030400c130340c440351414200d840190f51030741c101c034980308010501c6078405a0360b12821005240c50300131551081c8685042407500f201d08550003100b048a420549031084085081041e908003489403044040847d080009403002d1044010001c1181d00c80019001c0e0310740003c2400e0704d1490b04a400c0400c0b5041c280e41c8140c0606c0d652018035005440296058020310020bd149401c001c03815105403034004002c881e400b403c1601c0c030b500c964088205689140700c1c036240c02003c203d003841070200c0060640d801103500034440400a0035036841b078000411681103800100004d43d6688500301c21a01c030030b400303003903070b503001d58003911100d1035a034080c540150400d01e2800d8000400e84c800e4440204980b00c2d107013207442d524012a50b5403080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 674441825 1250 674440575 674440579
    0xa0206070f0501020f0f070311060115030b06070606060e0102100b0d02040b030a020405090c2701050f0105040f080312011d0408030a0b0d05150708100302060f0f0a0e0301050c09 78
    0x100400c00208420491010708540034030005031500e40311203000c0742568062044000006004580882010740c8404500c900d0307600c0000804c050750400700204c1d141203242c020081455581d84490b00c164642500b514920364211380c04000032070b66118060401185111032030700500601420403540041c1c3d1184881a1a0140026244480039400d00004083d40d046203070b8540b14140f11000107a803140609481280c200d0043e03c10419103405001c4080030a144551501019001d0800c880950702c1c0c0043c112001150502002c3c20302d207006075420701c11500b203c10251004540810394600000c014021440c010488205580e40d074000c40e00b1515001510402032400740001c20041040740c3d0103107402405010f000550040d203107000039201d0b1060602142c107034210040125011001008581e808142801c4c95440d91074008540390103035145010091044030041040900b1114040980c0c14031030b0002411962161105000b804050400d41e070a4820340c01d11001840490348541034501d80800 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 674443075 1250 674441825 674441827
    0x30f09040504060914070603200304120c0203060718050f061c021c0b040e210a09090515040b03010c051602030f0d0503040605090c13051b0a120e0a0206 67
    0x2000400001d440301800640c2c1d0b590700c443c140000300703602c5403560b22900800c0707000f01446072814001034242e5808400710100c040c040300c1c8011003615002c048a500541c0301418030510300c2109002d4810008550004c1d416110380c1c410040c0d00d90f000385014000f000a544001c1d200b030754440800c0204c8502d6900e840c1c010303100344851709507017034040350301c06000603032250141c10440d4202000c607078184096031482485840c1c2c6c180201905192103409d151a11041c05007440050000ba041403071200c041001051010003c1d074a25220f2040c14108081d05034050284414100301804c0108450500d038668070541c6406100340385447c0500c9100d48003002078858900b06001c3c80483c1261030a001c400343d0f01f5001742030550b410448280300003c90b020b0681c46458403814581081011288d008120095581c0b140c0b046020f81d0b915005104002c86200002144641e5127501148bc6403880468500c4d07440300c0420105901c039041204448100451901080308104d03408486964032076110010b504000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 674444325 1250 674443075 674443087
    0x1b1704120f1109061003020a030b10030b0a090e0606060a03231e040c09180204090f140f03091c02040504080912070e0402060a05120408030f09011419152402030f 71
    0x1001f5009043d02007982c1c1000140785480001081403015142000800650350b2200381c581450461501405007107100810407034030443c0c00c500350f9601005014580305020108455004903c6500664804071600340900c1549000d19100c0031650300c103071040180010211030201ca241d614410b0244941e403c42030018070546071280340c00c0284240442220480c0310007424201503140d40c001c801030301d4440c0b0340303030209540c01381852640c003c0420350750301c101d0300010010003a016000040d20711040d4100d404e240c141c481c0360310074540054001c100941086c202001c000511045c80007030003128a0548009044e080c03444145901c03504c4a02940c10b50000f00320110f80541020409814a00d03203c0c180f05142c03050702c1c00507107002c200c01c0300c3c21146032000004000039200c4440704107402404200c001d0040700c13144800700c8a030070b60041c0081414015243c140d0070110040e007241c1c10304861501c0c4401501d03124003a070350102280e040c00080d100c03240d4441c803031458400021178400e036001c0c25030b05007480 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 674445575 1250 674444325 674444327
    0x1f05010e09061303030c120e0601050f031225021815010306210305040f0f0302010e040c1d0f0406030812100501080a2a0f020c011b1704120f11090610 66
    0x329442038907004020411160380c4c44c0340781c548111a044022000103050790742c98441082082000b0333034000e501030341021651a900800e064103403032000d00c0760900b004052408017048110000c0b0404007030344c0850340d44200d2401c15040d50322030f4000e40c140780c01c00c620309000000540540304030788188a1a03a4101c4075a0095001c2142c810040714803900e4078914259803415185442c10403504003011010287c07800f0811581c104001d01c40c00c0400790b4090101140d68a0f000d025403080c2c510036115114400d003c8044c03690766070300c01c1c05900d6004000b044146c4d1241030609403034104400c2e000c036500114010030303046078010204100301e490594429600b81e030352001c0040036240401400c52490000030031401c0100c030642038071444c1d0807659070320004d0142000000f0315010440101030b05200e2583c0340d950616551a40c85102c0320340040d070144030051010741c4000c1a100700e40c0305c242520104210030082000b0302c1102400b0500a10154008400c200c00f00300e002001039991581c003070040c440c035643e13107 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 674446825 1250 674445575 674445581
    0xb04090c030b0f01050913170708040e0f0105040504081603032a09090605220603120e0324070e121009050708011a01110c030703030807030e0703051902031f05010e0906130303 77
    0x390b42c50a4041d0074071849540d901212f070042d800c8000903c101100700300c0e458403064001401403600312428040d40c00c0580310442107204404010191098003010842814000d0f08a05c00c0d9003542061010503405816251816003400901400081d8543c4400503e40ca460702605054845c010a0001b2940c403c000600118034100302d025845503c070308000010a1a141e0151804040340d2140708101100e42e04041c10714200c11442c0a5501200000d6007901500c9100b19601160908000d40f41000d00000100021000703012203580c1c0c45500d01c1081d0a9005070095807109100310112900241c50348011070a03503040e266821076481745098081200c0d84610450300d071400080050f075441840305000310b402d254440e0000e40c0464880320a20203e00d41c035100380414880f4460107050001c0c1156651501e036107400041c2e03952404c29000240944d642440324615801d0980310036200e418101c80c0c1100600000d2185814001803040052030082020441900c610074520040c2040900e070741d026001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 674448075 1250 674446825 674446853
    0xa140303040b0702180c0301091d1506030f1c020106060f0e1306091b08130b04020d0614090f0c01050306132c10150305030307030b04090c030b0f01050913 68
    0x40880809102c0c0d02d05c000704210180140b119901160b529030600610b0019110311248000c001c400340030341d0030420356000c41c0019000040e45d10400490302c80c440000e142812010703004109008a25003050708001c90704c0c4082292540350000e00c0400d076a0b51090f2501c1103010780c40004a170241c50a8000e42c500b00304200356490703d180c40014019281c1c50700c001102c01c02e0714000f02c0c07490b08144081995401584040d44107950020884000c40c003070703890f6845004080c100901038040440400b04021068000c4009054810f0b04010320f4980522469926840c8402c0c00b4a2400340b00402c00041d446441164890340001d41102400d85080c1944001030041d031034145080b441c0c510400c0401c58030071018001c40d20b28540200340401211209008480f8040e80d5001440d02d00002000003607000720580b907000c82c00b03040c001410b11000c80840d01800490500400d252143d04011082210041d1b41c071b03024056412107400c9680e2110306020401400365090a10315508040c0100051071482c80b81e00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 674449325 1250 674448075 674448079
    0x1905010f0203070e01080c040503070902090d0b040309030b010b0f032421010e0105130b0702070e01120b0f1029070804030203190206040314190606050a140303040b0702 74
    0x240e500038144000201d801c00e540000015406005030b0607990707030040e18140c10190f00203101d8a070514160020f981c0d44214403420149640208181d0210b43d580c2e1941e02e0043d030800c0f40c0740c0151401c3d10340107209071603500003210380c2005c0d10008101d145c0414150741960f00704030039651554840100010b0b003070010065155403d8512b9080704415124004a420010311400c3e03a9080d45600c60442d5094503d445001001a80340c075040101006000f9100b298091300300c2c9541c4282c0d01d45400c1282410160740102040d040d03054000216244c04002c0c50120b00d028104000c01911500020071040905036500640442400402e1151602c10726511000c0c11000005a0000d00400300703004441d001180140c683c92400300d41002541400c0c02080c60841051004070303600e280030390024046001368000030302111080558800c0d804410000000310301d5a201c4000040301d241c2c6411340c00707000355014040c0240d02443e80020315400407d003081e107804c0b005024601789810309004020035013144405036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 674450575 1250 674449325 674449331
    0xf0705191b05010f0506010338060d020a08070f020a0309170c03060a0f0b0102070f0306020a050d021b0f0f0304030b060f06070303060602070501050f0d0906230411040509190501 78
    0x8800a80248030300c0c0804c601d10b0501040341e01d4528009011102d501d100c01c030460b8502800c101868200260442c1520581409070007055040c201203a294002c5070303414403190344001094009581c000c1625032040d14181d841540c0f801001c4422070300d41070740c07020040105060000a111105d0754403050480300540204540403004580c001074078040090725101d05140da01d045c24901d01d070303403406103903c8540213000800c2500e203401c00d48007442d1503e1002500469003c1000c050300c0f0300c2901181d0742c050a180707065407600b00d00010082d5800072012600018441d03d00e40307030030700303d000324890700c1000029000d1030400b444c0d40c41c0c1e08003c240007401c0d070381d0148000302950b0b6207544000c05071912074026500040d80a0912034082d1800d5615005141402001d1052115120704102103a0301e0642c1d0030030200708541140b031302201410310701c008150f041c01d21000c5a51800b445400451040e030081072541001e020702000d10007111016519a00d46411a0400030302083c10003410f0060300348658000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 674451825 1250 674450575 674450627
    0x30b0112141006020d05030a02070f120e09070905010c030806181f06080417090a0b0301080307150e0c09180604060b01031b0e0d0311150f070519 64
    0x12208403800c1c51003050481c01d01c4070038030005010809251000c1c2c2910f0000707050307a921140d4003811902000342a900003079000101078003000710070851044a80d600c6420310b581401c02c044090f181000700f40016004203450f50002d00351500c6660381404545041e111004844441e031401c0b107030b10b0700003406950840345544001d0b148402450486200f150750b560590402080c0c5841d480341601c80354002001c218200d414400407038054003e10f00101c4002140954803411100801d5545901c1c8d40008030030840132000145000300807008044891044480c00811810025404121407040d1b1649055900c1182e541c03201d8140346040f55042015103854800045007071a542d0314050007201c1c100e5000da1106400b045550700b5008084203055100c1d240191009042c030010712042c915403120784507000185544051500030062180b9150300038042d03e0314001031a6010101440550300040030b4145600000c81c401d00c90026078000c4452901c0c44070302680124011a00300d40e20302e00e036801d1030031f002081c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 674453075 1250 674451825 674451857
    0xa1b080a020c0127150b01021507030e0714040605010c0f0f0203120f09270a1104051908061f03030309030509040f140c0c03030f040c0f03030306031719030b01 70
    0xf51100440c540c540d100c2a032510302e0103202e907803e0812207485c0e150800080b0010b81e80c010500c030440c00101c503032000f1241d035802c1084000e024951107043c454000c031540071401c000066000f010f280000d5a0901070150765100448200d8061030b0003902d0795882d40f043c440010011052443c11a00080071a003146200102c0000540d01ca08131001e010140000c0c1040142420198aa80c80710660011003902d4045042201000d0f0003c00300d0100640d81e0102040e054900000c0d14007070400a0107840d0004a000d02c01c102c080c400f03000e0700d403003407007000005090002170700ca002902054880254036454a1035505030003a1010a50807024420103010301d2406840324802c00050440c054804108038104002d61960310a01501c5035240b014100300042580a00004503130304440b52074413040280e9290b0508001f0003d00780c011896525410708000103141cad0541040d41600e000e400c4060a0b200184902c50705845106403160f0250b0040010551140c004d60010f4014a0181040c1d0206800c17880 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 674454325 1250 674453075 674453111
    0x61f0203091504150c12142d0403050a061404080406030e12160b0903091e0f21010506030309130f0b130c12020c120a11150a1b080a020c01 61
    0x1340d42c000107031100260b07014412100e07071028100050341440901c015018200ca1114800c01007414540070b1450325101c44140d29400f0465001e280490f02926a40c070780c135100752142d11100d001d40d405800c280c0e0b4000c5500c50310001030701496005580e41e01d01071802c101a13010b00b540500e0b03081d40d402130a035505c1610a00b0801001210039904150f40340c2d0764103203407481c19980c0c007074202603880c0c2c41803040030215102c6003246034600402800f0300380c901da01040003982c41d4003031504158002e01e51030540720542841e103200000000c0307403200a0200d5913810b0181641c90041458082d407081d40101c4080713003050750790301000d00c04c0f10303095012401004610100d80d81040d084203035902c0395a202038149160350301003c000328074501c00038150300d03012100880075610a4034060000d260040000c82c440ca490040401c1110081400142d800c06402600002101c2d5412200803548a05094921841c0308550341041440328490b115055a41c6a200c454002900314013520091907503507204550710007814407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 674455575 1250 674454325 674454359
    0x60909030e090702010b2404090c0c02090114030a080904090501060f090b0604081b011e081902072a0b0301030b0414030301120b1e0f061f0203091504 66
    0xe29a801c40c10094001c1c0481110002c12203411649052a05801aa03403d1900a8450ba0101180c1e4800c482c00f881c1300410300c250790142c1078003031030204400203954104200c0c00303050303008955110581ea40c9254030440d068200b0728155240e003002c68100c0001d1040409080460806040021500256560f060031074201f030700040320070030510740304000038212070043d810301c00000c0d118a0f00342840c0101142d0f607041d8241d03150342d4405841c440007450381d120344a505802540341507081743c6000007800241c03410209461604441a040201d04100d0050f40200c03004594020048070790045c500d91034941108001c051507488801d036140020701c01740d80b9000740d80078500400340110a400c0c42d260083d48400c5002070209140c200784010030800ca6079a00c000c10081c0c003d0b018000740d81d1401c0b0100303010381c0642044802403101b1302c03c2c4070302c00e401c400c5420301c101800c0c0c030b0040800483c60f503800c5d400310100042e9001070340204801c044609200708144551005549803070f003842d80700e148050600c02c0310 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 674456825 1250 674455575 674455577
    0xf03070c0f03110607051809040f0f06051b09011b050304090f0506030123011415030406090201030b1e011404030c1e060302070b0103240e030d0b120c010804050106090903 75
    0x5403c00401880090000030b80003a240d081c0f045c42c00aa80500030280c10020090600c52070808c000174003404001102c2d00d034680e0344014651400f50091800c03030010881a0390500100c084400c2003812400001e084607400c9005840714012441e04104080d07050131000c2080310b1502090000040c59881c501a03000d404c0500003010036a0300d0200700f45800c55602d103009201c408030b83c488143c4140382180d0f200b41520750050742cac1c801c0052481b010484010503028081e10801c000803c2105000c000d40c00101c0c424801d0b80c082c000804808100410700c20b030760008009401c81000300c1d4081b580948402020280380307183c05810190b44e0713118003483e803c56601c048000305184541500301da1901b81c04c1009414281000c600f06281c503110b2841015050200604280e544c020010f0604981000c0e030b12440031080c000e0181c2e001c031031141c40e12604203501c0d584196051000e040003928004019200840c000002881c6118102004441058001e00141c03169583d40c040031400c0c01640c02586402402 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 674458075 1250 674456825 674456837
    0x11010c0201062103090e10030f12020610051c02121603030f090305070504020f1c06090e060f070c02271e06090106030f0e01051311090702030f03070c0f03 68
    0x16011800504090040005404114014a002c0000d80140d00c140c1940c5551b0400310b00707951601c6421802501540014210f0400f032000c2c0c0c0200509801c03100f1042040f40c0c251812615140a000d05804143c05134a070710100c0c40d106030644440011f50000030500060504c000703051407943d0503060200940750046d11180c0c1500034014107411049250249605242c109002c030302c1c2d62203054031102d25002d050f100d241c00094aa00014140d0265111200491242c0200c07681c962a5180109441d20075440050304250017001500c40c08183c4d548104620640703500030360b544640c1151121017804040360b100352040700103a1041500c2094146040101e62201011300740903c05040600074031440300d590508410800030603844002c59641199030350300b004500f03a111245618060201c40501d00c000d9031031b08081003c1050500a8000300500030140c80c0288205a000d0084400e0300b240e804026900170400e012010745260f00455100c2ca03079161050749100c0c0c0340d4501c1e01e4600d031440e0070380c00200 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 674459325 1250 674458075 674458079
    0x1e0307050409091103061e06010804020604030b071701050105040303020303012607030b24030c0d0c230424030b041a0a1506030b150d0b04020f070c08160302090711010c020106 77
    0x2003c0100e5038000c440d50031f40b001840010f40400c4121000103019904220324540070074210f441d040b003641d0240d90310646004103071400060040030701c4a41500240004400700c00040c165014400319015a07806a001d107203540c1c200890300e011820728a441c50207041ca80740313a1040300c010034401032016521811741c1b600641130150b02d8403005040c00140708413400e01c0616001440c0c1e40003401e05010101910f10814903c0e1030304003041e480069070304c030314110400e90905904011070442240309020048400700306400e50301c402c10600620b03e0762007555120041030188080303550f007140b8640c4584940c1c0c4d0510140038486c1011003144050b1082d0306825220300d18640c0b00d421148428018111074902001400d100100041c2500c40d40c01040f0002c0000140041090310f20f0382000c1c41c06203001e002503590b02c0030000d528105a125600070f540d056018540414140b401250482c00801c060408052246c21078003004280f501c080d00190034400014542003050800b80181240d4295540001400d14 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 674460431 1106 674459325 674459329
    0x50609190e0c12010b090a0903020607110309060a0507140109080409090602120106020309011d0109060f0c02040923031213140703050109060b04021e03070504090911 73
    0x107403c40712250a20201500701d0300c00741030300383d51112055881d034501c4c904540b85000001c6c016001540800d2000c1d120340301110501403594181d0349800070400003c0c00c1d51740b10b0041400130401c0840c1c8042032007540d0f84444080401c210003408103407010741e00e03084584980e00401c98440da0f0f442d030b40c10500c030300d5906683e003886250440c02c103103503140c040c0a55203030880902c0710f0003c0c1c010750140802003100704503200d607a40183c44d555403030390419005032020f000a0080300104120302c0500f50241c4d803030f40901c08140c0e006071901c8200304024407042d0012000c079440004150300801501d01d07002040ca5203181e002413148000c001d055228600b00c50000b900c052681854840c80b0404000e005040d8003d0903000e1180c00104004480b40c0144800d80c050b24401500115003070f1070189000301100001c40d4804503d20f04145000d40781d2002e807040b1008071006441210729480340070028 = true := by decide +kernel

theorem cover : BRFrame.Cov 674280575 674460431 := by
  have h0 := BRFrame.cov_init 674280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 674280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 674280575 ≤ n) (h2 : n < 674460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
