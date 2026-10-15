-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5278
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:20:12.597328+00:00
-- url     : https://prove2.me/submissions/6dbad139-024e-44b8-ac9e-9b37e4b17af9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 949100719 ≤ n < 949280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 949101969 1250 949100719 949100729
    0x4090e3715060302090f04060522080a170106110c010c0809091012030c0203150105060f0a090f0e04301b06140103030e010305070f08040c0e0c0a0e060f030c1c0501 72
    0xa00101d00b420304d8480d083e148010000c072b40710402100c01c02c00721116054070300c02243c0c100c0d205070340d0b880340c0407001c82c0e4109292800c03103820040c7c20000200d60f0b900285c515000144001511000c100c1d1000464417644403030b4002d414403009000b120414500842095000021400050301045e520900c0d18240d6401c04005d802180c5081c2d803a606609061200300e4100d406650741102a60500d40091402e01410504903c0b9810201d40761000c14010024040038107100000c51203800d90755000380c0325141088904a500481c180c00d10030035500c5201384800c4c0c003540441041030702200c21400712110520224103020042c2c0941c509000b16200c0c0c85444100006040403807500c0d0306505000e4010b40c1c4c00601103040603c0d000810029603440b02c0001c11100c82450500b005859034240000a52115084070403076245100c2803204041080c801849020080d8540701070318000d410821009000751560100b9440c01000014050160a4001c0c215038a00116950400007410005c008540d400d03004 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 949103219 1250 949101969 949101991
    0x40905070b130b07032f060c0a021b060a0311040504050103050d09080f030a0e0612010603060f06020f06010e07051c02030a0506040b03120f04090e371506030209 71
    0xc032030b450501011050007905a1071511442c00b0344558008014007040118041e80c0780329011010b95042038005c07600e0325104c4081c2124482d003000b401742c080e280d001006c80710152180b81140c042106040c820784081c410001c20813400c0104140c4154090490a003121803040000c00c808525a80e40c1c0c03080c140a035009100074032408485c01c0010342142d0309900301d40d107254084590460030141c00401c0302c107408101e190958202e895100420000e01546582c0005240d0150022070881d40c15441001240c09005016034100d6440324281d071142290104044180c005070014061801000e6050ba0040c9c6945045d92400c5aa510704050010084050310701d22034001007400b40210050240540040c2c0c01c45040103500c04110003c0d6a0b40c842e500ca40094800c01b00e01009028030b0041503034020211a6404d100c00b401d00381d10756465200d90203540040c0c159030f0703000e081c0e22070100707054960400d2070484a01039509103458440b500864002d40081503a111030b00440140c403205001c42c044e0b44881c035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 949104469 1250 949103219 949103227
    0x1707080f100b0108040c03110a050d030309020a06050a0207030b060d080a030c1d0d0f03021207060b090a02031614090a0e180d0c08030604020702220501150801090b040905070b 77
    0x320400a03510b00040351030410a0610a00000c01c0340140048226680000d07030300e140194050100d8842c1c425079000c15804402c191015003410741581045882074801c988211503e034880c0d00540d118020010201c0060380b017008140000b0b00400d8040b504002c0c01041c001c02107003150b550382c615900009590000a458040d02c0540036040065004901c6110048060400380b201c041603d202c181032000c0d05401c08158540306060085c0301003201c8000203840c455580403107003401d10113040280701d0b5a00625a800000f80084000e01c2600c0c01a140b03040a540365542c003100c116401320036a0400c00740d41d00d04000343e40455507017201000040403010024074041c6841c0c00e8000c2100b400c4554421550098020401040e500942c0801c6035948070905d40d480343c4034800480e009005441009410040c00c60495801034000c03444c4082d244505a41800541e88400442c89901c07a55005000440c12240041c00b00403002e80102c20801405400018941d409403569407810000780c0c860b50b07400c01c00003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 949105719 1250 949104469 949104493
    0x310f0f09020306010c08030703090b0a0b03150603070509180109031e020a0305401a0c0a03050d0e1f060f08030702040209120d050a03050f07091707080f 67
    0x40401044000d004505600c0c0070800a00041c1040f00010040f580c000001031580d0300942c00308402ca034122407a41d1a81c07070003454a00c01001140c1e0041e100b80300b10803000c0342c000c0400c00c016216003805005000f02510f008107003d517422001c4e000d2034000c0d5104072406c81d444424403603090114001d6641c0c55541c141f216503c40005640c0d200e01e03003150041d00c01d04011a4024088401c00c101d564481c201e84505003c8800103030005007075941107924824440e520090710364040c8004d882004000e1942911420306c5070213148a41040c00d2500d800070f8407610b006c20702420107801109211600414400010145542058440d000c0c16407a00e03804008440b41d5130b494403500e07010b052840c0e07103449024280800c85a41e400340030300092166800003014a810345404507021003034000c800c101d4081e21102017016146130889103032400045e01c3c0900013a01c1d0015140e00034004c1c00b0903160000c00605100528800d11006404406c42d4400c00d01c00060b4840200209504102814046e0804c05444 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 949106969 1250 949105719 949105739
    0xf0902250818030a0f03050f040504090501060501080c030f0604051e071d0102011509022101060207180b09070e0301240302030d080108030d0209010e0406030303021c0c05310f 77
    0x482c2c01c15001c0e41c001440711001400b008a0a000c10381c250030a20340b20380307040c200031804c0d12854024a030054145070042d01004015000320702951000d0300c85080c20760b1544c5420181d4041200c80d941900407003004030348942001c0d444660426030f401d20091005511108810808034180c90380000602803400c11160f03c101111042c520003800d200030310032038a40454070803002280d4083c000300c499001aa165220840941045400c0c0543e131034000c0c2983e450602035261842882404c0341e40d110020344507080d95841c407546801c03038802003185040ba155030750111108980004c00a41540d070b56018040c03181c6000c003a11011a0b40000380c0c95415003544141404d1101501e5542c00344039074200107200142010007030b45c0c0504a00c12005031a040044012201c2056212000750458900709012040c5a895002401c1c810b46400d200c2d42c0c90400e881a00c0308807507880300c5980c00580c01384041d04030540790b03542c940303100507005004800841c8655500080052198800041164041400c2000d6000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 949108219 1250 949106969 949107007
    0x60b0712021c0305090a020904050d110a0c0308091810030203100b180c121006200607030e0c15071401090206120a02360a0f09022508 59
    0x180c805464041d4402e580c420840740382440107018143ca400028a41590401203c95915001080121207040c01d0800c5522111070920580c0081c2034001040c411800010300452800d41c00707072511001c245192100071960b0407246509911028022081c0d098510310149180145103c102d4044007a145104140c58105160703840b91034507086c885000000d036900c00b80819941e41c0c1006c0d40b200740c3e4549140544a00c12401001c8a0055940c01c0c03180d400b10b82841e000c151001d0303032201e0150200300701d80546018104159508980d00c03510000300c4032442600031004800d0700c00110703a03500039580006000340c1541311000341e40d0fa002250241c240031000c031300b080c61003c02e04001c000c540274640100d00c5a10030000006811485070b0041032413501d0380d5049400100d10203201d58211a403c0c04110300980d43d6042c01c0040b07c26643c0090307064a03008055601310783c1403060300c00903589454a10f6000c3c0d003080d50341d150300910000301d402e07803690402541c90b80e00340319030711855442c14022216800041 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 949109469 1250 949108219 949108253
    0x1e1a04140417070f05010e0123040c140a05090a0504111c0b100905090606041d280b010b030406050106090825050a0803120105060c100f060306060b07 66
    0x100305060101140300d007141c141851410320b0394250f4800701d50402c4801129034003001041503290503041000002c041d4031000c408900c0000140b0154020720f584c520802d0141c8024006c101b442c0d204126144810744101079840029141211440e035510026000a000700d4800e950701e503c40381008200a00e0222011070b120040760001242c02001200c5005210740e424014400720403000130425948000909200501c4408402e1265141a001043e11100d080e074055014a08020207400304a1512024280c03d0078100c0082c41013540e03022804000010138829041050410a605d60103d5040301481d07001e480c11264503651f90034035191003801ca51050340243c080007040e84003804402d6021405101810f007180030710751102104100740da040d020541c07000750320420342c5000151408020019001c0c0c404c0b000c91181301682ea842c04c2c0010380c071406100100301d8118000c192600f682a900c203035200c040c551000103c10780caa07aa09811500684c00c038014a03100403a002041061414180d00301c51 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 949110719 1250 949109469 949109501
    0x181b04180309030f06090807030e011d0d0b0a02040b0f03011503110406051c050a09030305090c030a0b040515180c0301060e19090512190207181e1a04 66
    0x1894079100200304291601008090f0201d210500082c000d094211340842034011422998038400c5180c0035011a481e1402940440c40d2041103070360407480110760f00202e1201910908448405941d80c86940c00000c15410b02e01c0e5007400040b60529400d8042d1041c210b01030034880e507075414600720302904a080590314081504001c01c1c407550201417420b94003200c6850030900c0c0ca45070180c805520124030b40305946065454042042409160780d0002d085040c041c5e01d04002d6515900354194503010356544080c3c0540c4070031006070001c1c540e51816680715001f0310590300022003440500400f01c0c01590341c0f103110201d5501070107040c2e0f010b1005c04c2024174110000c01845241040100692000812460280c2d500b611110124101500002c1d905e43c1d001c4d007a14840045941c124181e0382207002c600074031000103c002c40000c2e000040c0502600d507402964900c03807006a6103030028209041c0e100120b4080442070446440a0f401515590240c0040800444000e0410300c011106071401c03082150b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 949111969 1250 949110719 949110761
    0x30010905010602030f1b121b03091008040201110a05061006050c1b01020c19031103031c0f090209040b04060536030f040f030c0603090515181b04 64
    0x10940000449060312100c40641d611030440c900c0b5001d0031140a18804501d0140850482c0d450300087d0052074503290600030a01c07005081000a03079070340600c40226800c01d1554100e858414040e0400d00d074014414508100f4500500301000e00b4442c0f41c41040303800e07034030850038001d80345612100e050140c030152510a050400003290299280141500354081c001480d0002c2156442440140ca1b5060058220500b90040704009810091548015035465000c01c108012916004c01294030025940c2308c1e286446a000001c00e005045140c01014016610046440143c0395140d00d03170311480c02003480041c10314040c2884010380786c00910003180000e61034104c6030227410070703403410140070711064544084041c038150540c5184207101c00640017400200740040c062010101010680e48200e08158005030f8904055040e80c8000d50000c0c25608900000e640c811107400c100c40e408021940000c2000000450712418411104d0501c04c43c51400089440f05007050700469015144d00d038000300351 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 949113219 1250 949111969 949111979
    0x50c010e09040b0709150c2603070e0a0306090303020901030507140f34050c0402030709090b0409170c01060806060a0e070203071b080d0c2003033001090501 69
    0x4000c030010001001d40070701c1c00218081511070301e5218054120751012000c0103103403280c00342807c01d00c2101180c2000055040e8010f42d25940100e400720038035500180d0071f42d01c4d98502512041000111250014806180040801e505002c0e012080b800703601e0041c1c1c1c820001000506a0340010421018050369507914000c0c000f0300701c12549900300258000d0b80303a0030224094404100c0480310300d0205020080090165800c1d802040503080c030034400c45880340d0344d220034401a40401c80740080802c103410030030007206074286c11030031007488010701c00546c540c071640e64501c1a00700040c0d000c1c40010040f4481c24001d50910030740000e400d01c1401001d8500c1c01d00001400304040d0b0180310a00345849001c181300038020016110302a40c000c0d0b06200d2000c4800e415003180020384601080c42c403402c1c0c80500c0141c01100c0243d83d6903045011054070060400880d550755130601b140a42521003009003440c101581c82e604070380c03230764065115003980054a002410768401a0820118a403500c401008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 949114469 1250 949113219 949113229
    0xa050108030a030f230709080c09040204020d0f060b132403150b0a03022a071a070f0c030b0615090910030b0906071b030903021311070302060103050c010e 68
    0x6003528500407a05551104000000d007440c410415054a03040c00d0012172081004001072050381c403a0780d004542503817030818681e01c490400c0c00b16000351400c00807070098201a00201b0310302c80b1042000c10000000c9007048101c5007250300001c6140e00100c2e556501015030185c1000401c0740c9040710404500d01000c0c002c01224000000050555546001400070000080c000c02403080e1526a6240c201c6000302401039805422151080d034141c0214034a06523060b15a07004143c01d031401001107a042c20b0780608000c071240111010000700b03000c1c050001c0d08803481ca0721160310861040360281d1035454882c40f060301c0500610b104842d803034004840442e00300b041c4c2e61031600860b50060180c441a030841c22102990b00042d00b0b0006c0d19003001240240002c0e4140220f960341e951400240b03072049100d401a02e50040100014401c850400c054600030480351900800c01e41c0001d035090407a081d0b01e481d980840021809604104010000e10000f886040200002030804a105c06000c00001d2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 949115719 1250 949114469 949114477
    0x13150c060c03140f130b0103120305011203021e2e0608010606051c1b020109020a060801050607080904020c0d09030323040b070f1e1509230a050304120b0a05010803 72
    0x50004e080d4907000944601c0c08102940c1d0603a007021008081e941c607405c2c01e42c00d15003007030310102c003003400c000000a603001001d49407050310b900341c0c4c080c0107100b28024035802d51240f211007848061040c0c81411002400403032041c0d900505204140c400410103c6a150994405a029200f035914100c020010ba5422400310303415050303030000031940e0314025281b0340028807446800242c4000b0510240780e140360154000300c01c2c54001c98001040540e901012151071901340070b25508014240030010008101b0790141039a18001080503050003240d500003450242080c42e06000036100ca10b0420505420543c040d0304202100c004103005803941542c054240301d18840c0340751080300000d61400f8800011081d42a45610080c80c806044901440e015a002070a43c151070203680b040259031425120300c80c041010368031011060380c104005420584145440794000a10300810b01180005681403006001400c0b1405500100c900103060513840031400034001116280740c140103100c1500000295 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 949116969 1250 949115719 949115731
    0x504240501180902340203101830090503030f090f0a0905090106060c0b1602071a1213020a0e0601180f03050c060403120513150c060c0314 61
    0x140481000e09401c40c0ba0080300d542c07107022120b2010841e00d10300400c0c04201c98144034502c0003628220b00030382c0c20014100110a0003541503010110000328441190044007041a0032451051226402d850b8450030444445403505002030240340c000c3c1a5000c81c08190b0400d1052034544800d506100c082940d0f0710401e29106112980410600e010380c0e142404c1148480c40602641d2940e5510031407a03000d0101038400c098203500f080d02c049401c0d40700d00741c04c55826030803c00d0082c45031031340000118101c4165401004500802c1004603807005107041600103508124009641c42604030510760110030007800d4850f05c448110b01380c102698681d8202d100391040d403d20104243c0318000142c40941110740d41c2c101c1c8110a5000249030700400884130102c80c02101910350100d006020400e1078820f40c00002d12500c1c0440350f24410521a0000e05031200c072442c8050541d98881d41101713403186040003d040007400380d503151010828107004140d844101d0303040070301880200c2c0b8008500e9409c000c002d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 949118219 1250 949116969 949116977
    0x2b02040f081c1b0222020a11010509010c0c060c1b150501060c050d0e0103021e0d050a02090a0e060607140a020f030303010f050f06040504060f061d010e0111250504240501 75
    0x1d1503044507002400705c1d0034001141411580d400281001500000100c04015110b518140c00101c0114060040612601e45a9510030440810703035070b250002d001a44918080154050001a0303004d11006000c0c6198041c58071802180b8080302030100b9140141c200404001d45001450001207001540032001552414500400390350000107c009000707400e8800480c110211411001c20034030402070104000080d070030f101c560351f088010800d0b0b1180016061b003081c0341000030070400345255680783c0c000000811161801354184c0791000c880c441d0341c9041405030041000744045281540031002c0840c030540c00786003558545a5006848030103403207442d014070440d2001034031603540e010455018100052040090903201d07841074400d0450b0340905000314440054a030f110301180d6041c42140441691020314000e40071004561604410340211302c1072069400850050007081040324004a001c81c616525515200030032042d9444070a0840c0201032500743d5011120038070010740180e4400303081c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 949119469 1250 949118219 949118239
    0x303011206151d150303041d0a060510050a0c170306010e0906060412050307150e0d021b0d1103060702030d1103060f010f020a050304080a11062b02040f081c1b02 71
    0x540c40308000b032208002d17641404001004a81c0a00c214644800c03e40c15140002303455035003081c040c08944443c010550b00c07101c0710704483c0c1468864002004903100c5444c0c1428109001e503a84860703144000c281301d881c107030080300b0040c9550307020340031b8001d0a40881d49905281850000700d00c1c2c0780718a01800390320507000d02010050110410403141e900d03500400142c003c104002c01e1030024101e03103540b056103003d20303800c50501c00d00c0010680d064072400f200c80002800d0040c1004140a07142d08102c5080d0110200038030a07a5081c80428468003054000e141e8602c0480200c2c401c50b40d28840c0c0308504102803050020b180c80311045244803510078248002100c003a40d000380c0c9089041c5a00601c10710001402040c1c000010500c00c5402e407065500644c0c0713550740400c01041d40182d8040e4480907020502c0c1d01c0a04030510400e007150260000c00611303103615040c01c401c00c10400e801016403548120001c10702c07203070102c06200d18440d880c50300c4203a1020301840b0412554200c003001c2d100d103210413 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 949120719 1250 949119469 949119481
    0x220309090b1c1401090b09070303080c0a02030d020318030706050601020705040905190303180609050601060804080a0f0e0a0306020423030715120507080403080c030903091905030303011206151d 85
    0x1510010130581c000004261914041c1c202c0e994070523503800102c2c002402c280200300800d0340c0d081610300d1550710781c0246003050584680c0da0700a40005120307616105e0740000910b0b1503d028002411424001d600100b01458410006880c220250348614012880e02c1c1e042e40212b0008100e40f030072142a000c3c1600c802e445400c048000e80040f00b48842e90341d071116418010022702d0b500c40d045141c2f266003512940d88e41e484081c0c1c1c9514040b50080d011900400101441e10300c1110114540d404030b0074101c0c05400c055020404035480c1d50030403559075500180c144803152071942200f81508040304400361f03001c3c02402081c0c40b140c00e40716100c5065403840e010b880d00b600840a90b910044101000c111916180600402c0c01100340e400303801041050380440c1c01001d0740803caa104100d070000552510143c0320602001c2c003640c03010010203100800021856943c107100660082c244107040412658003410107104a8090031b42c0490b500240716000c203c407000c0d9801002a1041104600078159299 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 949121969 1250 949120719 949120721
    0x306040213080d020609031602090403140f25020109150323060108090d0816020f01020c0105040c0f120618020406091a1c0b220309090b1c1401 63
    0x240c80c1d05009000e160740007181c682d5000502d034440191603800c0720743c580c031441c00e215100e10131080408c4c2d4814140204030054241240c0c2e15410911920304114904560482e08801c0e8014418006a696001900c03070500d000e00903449600715182a401c55004800742d0002e0140c492520540346000c103405003810515009500c2100d42e403424600382503d55401004003062110201e13202404a1800800709140c1d46e00000d13501c03d00100394454081c00e4a400040c0d801e8600f030007216804510800c56400c1c1c6191081c0007030240d0303c00300c1001140070f0a0910302505800700b0341d00102d5640f45010010008001c101c11040801904a003002030340195161000068810324800a07400c00d082030300004510400d6071183c1c013200b008906a1000746048000c0000e40051100000124440c030078941011591540c0929003100d00c1d00d070500a220001d148641040904420680100300c0000c1c041011080a015202440c03074211120200c0e645600c3e0040b0003042d201001601152604102030742c40c13003003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 949123219 1250 949121969 949121977
    0x50418051f03050105041a280b03071202010e010503161d120a1112030417210415141605030c030f04080714030307080a020c09070329010c030503060402 67
    0x107000c20000c1c8540302c2c18018040c14013518122100e0760f420b80070960850081c0c803c140a410358004801d42c03841c20342403008a4081c1c0400c80a5076a6480311301011580d42000305c070008001c18401542c107038210380005882002c40c0590342d41400010810400308202c0311000100040360f500f4491501e1040c82c00c140b20030540381081e150015008000041e02820008800b08920701c240c500c0701c2c11130108014895074040d07024029440d03070b0090205100344410419003030f510700302e00c0c1c0884200e02c0710900e1100200c0e50320064914118000a0140030207001c4410b455600589402d007405410030284804445200352422012400c1c0f6a0140e4010030405008551081c4254011030f9118020b900c0f00f000c540d40300b0700c0340c0000c03845200c9001407001d003503407440c44543c04004c0c065410081140c48810301c1358041042c290860052040c500d090740d482c60b003214080d440540c2c0014150074442048000502c5d01000303400d418405540000c0543c0c0d0188000c605994540f82140d1a611580d000c00c01031f0107 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 949124469 1250 949123219 949123261
    0x3150c09091e06080c0301050a020a120b04020906070b0106031128091e180c080402060f13060e03060a090b070c210509010215010b07020904050a02030f0303090d05041805 75
    0xb00f4058002100000001d1503062818110002c105588803008010b04038800c81c0000301c0070500c5042a201c1910090b4081040890042c2c0b01505d40484800002c84030361060303c08680c2d4524850040c05610b5140c800c14020401c0c0800f91031404403040e840300360200310740ca4140440440c5400c00b010030383c406e0a0007001800320001c0f2021050312105001080243c90141c1401c200210f104010441403078000c11122000039201e545460301e5a4013440460b41c80360405800302c000401c03d40408142064005c0000c1103540ea03a100c81d01131403001c05060160181040d0780b00c50500e148000465000e80080d504540b250508480790821468142c4003400300071010038010807090381580c1c1c3c00e0f070080d0040060039402d84c01e80f41903144003070b220542002c0a001c2c940b07e4450610403a0011f01700107440c190018051012624104801e60020b0710780205651003c0460300040188990a48100a0800c1000765400d0080c00d2a0074943d40c8240b03042070b50211500540c940c000324181a0031803d140500c08 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 949125719 1250 949124469 949124471
    0x1e08060c0703021c021f110a030b03070e010f05120d1403060a03020d1214041203030902130c031a012105220507030b0112110f0114040e0103150c09091e 67
    0xa001c42c8040d458400c403544282080d1b18004001c65168528800d01800741121588542440e402031b104134020000a56940c4d027500c2010804200e40e6600c0e0350b21802043c40c1c4e1301c2650303a41e040400b4010312103540480c411066102030070122203140c001c044a1243c00c0901d1000e51660343e920006443c00a803944084c3d00700890040000600c03061514a003100c07039040e103440f600c142c00e4010600c0035120f148607003030180b18041d00002c00a0320a0304800c2c00c25000401031000d4005582042040b08c0c40c4071100c1020030f030755107030104802443c15a0301074044024289041d0440d00741100e0b8400e55070301ea10490105580b14000344110119910150000c52025a8405d1484440c50510340d00c104900003911403c00c001c0c00000c030b1400d0100c1110369541e01207152444d24103c2414000745580400e60a4188045003003800e40c256a860007910082c4586a00300c01294034500307050441c410480c004001d00d604090301002010b810200d107508403484507100080d240f20000410507829502070f0405005 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 949126969 1250 949125719 949125763
    0x10b03122701180303110606190b0d02040e0c1803011505011b140d11010b010509010c05070e161b0f080a11030307110f060405060a0e030f131e08060c070302 69
    0x1140c1c1c0300d141b681c5826403100c220317403680e207607042040912141c050b00c0c1465800c0100050248841510240c040d907094002e0141c1803c3d2101801c18402c14100c0f5640340d50721021a03036007180304560207061407100040e40200071000e50158000454032250181c00e041c40701074011050049241250f001c10142c10aa1008541070101d4950740c846201c1440355000541c0041c5d00310075410306100c2c800c04080140c4445180005040065070342d2000900203071010300507c4d0000400b02907194602d885141420101400588801400380000d0300c031110030010802c92441140000d0b8010034600d446940000c0161786a205143c800c0729038600f40520a031050001005220030710750405035600c40303440418144d030b112070070260b49107a84100441340542a5480040440e265460540c0001200608075042c2c0b4500304031074080811030780c0000c0510b814691400710411504200541c0700d8600800e00d6240013599160000b4166685000f40480d9218500040c030b14041600800410b040d050103100500d900c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 949128219 1250 949126969 949126973
    0x121207030507141204030b0c07020307081e0708060a2a0305040209090d080f100b0f03011706070509011b0f0b041e03081b07020909010b031227011803 66
    0xe5400c00203086500252030f154160b10700b00042401c03603212110480f15428a071a5440c0d114407054050102e140d070750810841c0e180903803024029007001d0030038500141421019080b5181c2c8000c00c0c0184280b1035006504103100c8803c01042094011070b0280c000304141ca4180074020440d4900c0010b40c2c510011240d00390392030b0f901600403902c514001c0301d03031080d40c0e500c07000d809450340300403111000003d04c840c0000799003000b46224190000481d1130380d004d1711034450181302540c0e80040c0ba541c2680c10080010006900310600340408058110003a101238201440b018019001e48120a4140b0403070300548600850381040301013100e600480c5046081885080c5498050400d5030b06440c1240d12803070708002c0d095038500f50242980e055845168950b82d4007500130034540b1410041290707070310402800000d80d07100320382503015503a103c00026184da4480c04040c9000c505d5210181420710911560101c1c075501ca1081c1c400d403039031000c40440d40c040000100c030380c514418484100d0301c2c1e2550010007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 949129469 1250 949128219 949128227
    0x15021812150f010618030f0201030f0f060b121b0a030c020c0616030f020318060306030a02040207120f090b0d0e01240509010f1a070503210f130b0612120703 69
    0x20403070707904e600c900c8034014a1100ca585000d415000c00340001e01c14081c110015442a80210f002c0d5844140002d0340c2c891141e5000203460700c5511145a0340c0d80031074024450200014250340140a0740080706500c03d001008103030a004d100a07400030300d580c6001003090b00d170090043c8800c0c1d03100144225036490781403c810965070080c500a90004818445800a0900000c2100d0007080a40d0f4001440c004440800070b40e9800104404d80500404180000588481c00035100845c8100e052440000720428010070703105096a05900b005100b10301080003682000464651000b9a40041a5043c5407803007a0701402200c00d0404a00c080e044200d0406118a0200c8041e1a070441e403500751070340e0f500b16000d148075250041004009180150a4161101c1c200508009104600752030425154210024000c3c046071262007a8582501c100f01d80e104140c40c00507484111900d6074050240152201460380e40010b000794061003890348030340c200707540400180f80c04c0c00c840084550740c0c0c540c510f0000c7c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 949130719 1250 949129469 949129471
    0x1303030908011409061317030c070b0c030103021f0c02090a1a0607050c010807180e04230a110d0605040602040501030b0109080a0f0303060302060309010915021812150f 74
    0x15996520b0f10b0f50f00d5030900107480000b40501342a80c020001a1a10005801014155501141d60300b5021520341c0700288002c014501c640c6240c0179480c0c441505040074000000005c0c145040341e00104014401070361540404c00e46007048100c0400c40c02c13000721081d240c84913800006503000200c40b080081c20401900104c50f80c1b40c1040c9680c010405c0d207428000d8a005541000b0420b400140c000003095105c0c0b0006603001d01d4500d000080440002c014182012550b0403404440c40308000b04814000c0203101d000402c041500808102002224040e4950400d15030050192100103480b06003645c51415150009030030810400484c1810328003000294032034400e960210b030130503000401560140c002e000c00c03140c645020303015140b00b65032109503089400b0000c8041c59600c15010003d41c0341d020243d4402c0402200006010a07103040070826048010050110740740100700c038021300038441007480203a4070709a0304850101c052100301030078803910714590b17100c0240b002d04100001500203081 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 949131969 1250 949130719 949130729
    0x1505060d061a01030f20070606170c012a020f120114180a05060a05060a03200f0a08101d010c180504051e090c03060907030c0e06030717010213030309 66
    0x40000c5c19102d50a40e054480030a1203541d1000b6511800e02c2c3d000c03150303005083d078610843c1c0004100d5180c0808000c50700c50034064005560021405103481d5070048280d443c1000c0d0780340c2a42c01d007112242514540306195100a00980641c03404280c1a10b4012188410314041d00003800007a0070140484841607040b00d829001d41c0c2200c0e030643d6040d2000c00d4482e88960480302800e015a03607645040c01600c80540b6071500070040c03600c0000810800c2c0c0501e91644404001443c58945203000c1082c50030025503c10f1007515018001c0000c48030000d04209045101003000c038080c031410501c0d150100403692030f1149942401c005040340c991012200d04014102d07030000c2002902c480901c81241c800711203030050010440082d0400f0180540030341d91028200b011924141c8007000400d00b841b00c1541c8080071584100300900811010344403c602404030f44072240b1f450314019000990301e041038403c0300002d03013000c0751810540c1400c0d01280c4c200721000c041c0c0d108e06036580c580105013001c50f2040c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 949133219 1250 949131969 949131971
    0xb0a0603090515060603070813152c101a0d08040609171009210e04111c050c0c070b0406120b03120906130f030c050a031505060d061a0103 61
    0x2c046120035445003d5400b031000545003904507600c000068940c1d840240c95009180112410f00001941e10030b840005581420804500e8034038510140307200c501c0105502c00300300b017403e10344c01050b40002504501e0341e03580e0801023988192905440b0690504001050700038a44200b44410f0040c108000c008803801d503a41c050b0119602c80039001280c1c5281034504c0d41d45c11a03400c0c160700e0b0003180c110900c9940a01c0c103a84c5a59045008030009440014840d0041010780003900d2562a0510521161b440c0602005141c90b4400d1465102a0781280d040b008181e500c4011414200e0500c0660390441140c0c03048481040c0c40e003454041d290424400e0b403002690032a9103040b400154020203207520009401080c607008140123420080e0000041c0c150404070502c418500350118a180b440148240609120f903141507003400c044a403e190440d50082402403001c200184040c45260625001c081c000281c68880800082c1411072006000c0c0015081214202003003260b85280140c00c2d41c00d0320 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 949134469 1250 949133219 949133233
    0x3070b010e0106080415140a0b030f15011e15050d0606030e03120403050d06030b0405070807030308180c060304050318040c0e090c04030605101a03010b0d0902040b0a06030905 77
    0x25074000306003401480001925040481c000454590605000205000703011486100072001d100300c1c0501210384081003504d034910840a4203042c085441c28420b24030241c09420b4010710290402c00c010300c2030341d41100c0885448000072560042c04030103401020751503040c0301340024000b800e03604a8107210b012141351078000a0014040e00c5001094641c0c20090350418820120850070904014015000d01104002c0e1010800c810b1040c0f00c05107100c0e4a000c0d16078141420700b01d10b04000d5810120483d030148000707002190b001030700e840e409001130102030b24141181c0ca0030340c00c112480c4552901b0502c0482030004200000c000b500c00301444800c428103000740801000301359a010351829010a01c80d055220340303402d001d2105c07684050401002458565079540c1c0f00101e40c1c0480c1c01c0c4910020000040c0a8908082c10440440000e904064215418a840c10645101d800b444e030180070358130700c0d9050464403560004c68640300b004064070442a51303290051702400c3c4403c4229003c2c02408 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 949135719 1250 949134469 949134479
    0x3010303021b0a05060306012a0507090c0905191e150c120c1e030c03110601050f010c1b090209030705030703051e0a05030406020a020a170a170903060903070b01 71
    0x2107100302410b4002000c1c02203840c9860f003400116070014103050304000044840c69a1006610421840d041201568021100075428014180100b0b904541e52140c01c103051803034a10b03407010042c0e06480c1c00b1141c500d000707540c1d090092055501540580712420303014103001402c290364903144044901040010381940c00d1510704440d44200154010070a001c0600041140c40c030405040c4192842500d0608250052a1500c5204510840708400141c40009c0c9802015030000001c1c01c1c02c0c0c1c19500a00703c07541000b000840e1507111241c03240c10400c1e0401804144041800e64035166501042c440360820f44443c1c5c00c0010f540200200303800ba11915100244034180002c25504a98015018282000b0b1070030104403c1c1403107111003841c1e03204410a00c2c2c040368040c00200024102500189000000340c8144000180150310540c5461001080004400e0f03020403d5040e00d6809012480141000784100034540190ba4031190148524000c004c280325000000b081c006025416484440e81d0710 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 949136969 1250 949135719 949135753
    0x30f0a0f020a05062b0f0f05041109091b0402190c11060c06010b070302071502070e1006020a03080718030b0a20070809011e03020310050402040522140c0301030302 72
    0x4586201c08002c3c445e4000840d56002151941030724904640411003c2c550354400c4113503240ca100e41000999284c1c00e00c02000311000d00040c500d18213840b07074821440c20b541d005d612602c0c19404010b1492000061101541c3c440d41152031207090b411180c24042c0e0403400c020100ca140036401c0b5800a140c08001c011440c00b1004e6031003d460441c01002d40b6820201c1d039a0ba250005003045007503200340f10010402c9190129224031201c00755004004492400581d03107501c0e41c01400d00e1121103084002401402d501140000000c3c2d010709180c80d994449000c200e9501540c8402c44010300d889510100822a80440c0301e406511031280511259400115501c0d243d4410031000480307032820454200007801580c058007142d13405040c402151a01004029000c107401203a11000960020130440142003080048025080130b440442c10a400e19000c601c00c0500740c050309031030650807004109035142940143d01c80d00304041e00c0320328508100070403421035082070104a000d030040151300c0c0c8141d008 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 949138219 1250 949136969 949136977
    0x3010b030703060b0a090e06090105071403070302070312020315090a020406020a0311100f0e15070e1507050a111212030601030f150602102f09030f0a0f020a0506 71
    0x14041c0c1540c6240d40d0320103000b040300c100d0440d0030445c42440040c40380e0603441400d402e02219005000d1526100561a0854100400c0d640034055411003034894034001d9412fa0b603101031581001603540c917850409594440d41c505200e40e00500000170000b8100790114041d0402d0002d441454040c1c80c3d1011050070b9016601482005034020041d51020902c18420110091000c40959444d074030100e140e0b2080c2c0e0b01085507600d06548806010041110070024007030000c54075450300d4401e0034124401000b01d403145400c24801d109500008541c0c2114404030b070950345c0d10900301d800e62892480c011080f402c0780164148503152008446030180070100780b1503441d500d411a40e525580c1c0e40700041d070042c00641004242150740c0c2c051055902c5018000b2800342c02aa0002c0441f1441402e00505940518024800116824010b10544030420302e2400312400c15603042c81d03d031101c04020a1605455014480c2144501042c440c28005070a03032910a5900a03078008100c13075203800070b000b51031203 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 949139469 1250 949138219 949138241
    0x3060f040c03020c0709021801140f07110a060519120b040603060504020a1a0904020304060e010c020606032811062a0c0a051305091c092103090306020a090b0d0203150301 75
    0x40419010b01240d80302d61010b5005100e060801420100e000340c2f01070445e0030044003143d400c10a40d4010400385040b800c070700e0091206240040c501420080b54544098400f003400341170140400441c001c21030940c101003644000503000708042a582e00700381001c2c2c281a41c007070340590000d01c004503140400b40c00c6204594407820f01d40d0700d002d0441c0b0500000390300085c019942140d5542030941c280600303000c0d41c10040c929034024407543c20540c00b0181484010039103054a440b260310585410000c0b4981350f1041500140c0c10703643d4402c81d80206200e44039088545c05118110f810700c1d651038503e04800c046114040040320300804100003802210203450041c0d59000c40f03915510f44062100c3e410040c0d03c1203140c400d40b4803401c8802c40c44032030402488010760100d06041c0013408000f24280504040204030440b80300303e11803649014002410900010708070680018540c40058041d100000c02054083d003615a01d40540d40e0b20002074000b61100310403070107442220401403505010b0010b0442d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 949140719 1250 949139469 949139497
    0x906120305160f06060e04060e28231605030604020904200907030903170c03011e05030d03020a030f1e0903201606081b03060f040c03020c070902 64
    0x642c1d5200e403080c0011102104803441103500c401c83e0001030241c05400001c060b60500a00c4038100b40c58004250790304540f02c0fa440d0b0344090300c0100c050713100841c105084001010740c4200d200040c00d14414030901c4120301d40d400440a1109a00d00000250528010b21505803d1001c16240d500b0076498440550300694004a2000860f02140d207400305005141c6502494200320141407000c03d140c1c0300202d4010000c02d640395884810305070403951000f44d1031607044120b85540780c4107180c0c8074140018040d0018044007401240701e0164440b900c2e1014200040c221406c41282220040c0658080341e500f2000904100c03911003035030017074040c0c141052a1032044203034001040c06034000400300c0c194254200545052800b072407203140141864030490300c4001d0a803610760b10041741401c001540c402001c0010440400c02c40305030200300c0520b10031404480f99a01c1c0c40f55000202703500d80d000360680c2d1051401c10036500842d0554000d0462280300c1d800c1d6128540d440b590a012030180561041000b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 949141969 1250 949140719 949140727
    0xc080f21010f0324090c0605040617131101180e100b0c0714132a0c030f0e010c120c120c0206041404060e01090608070b090102030d09140f070906120305 67
    0x9141d1081c0206194405000005212049a103038030b8914403c6e07a0002c0c0220707c00080601295034440c4118000c035180b5a02071005041c2440d00e4001240c140d0405842010001e58107241684182010380c1c617070300584d9005140c95250302190500e0042503604000428600000042c0f4003400c4081c3c030b518011000c05869a50320b04032000310550b044281c0035602c1a0703035030a41e0b050041c03e0312134001c5140c50360704a02d0304032904518055a9207034031640f42040c0321030780807640000ba620040c080f20000c0c1500d02180800440303401656483c2c41c0c2e000c002e1002a080d081c0c40084c640c0030848015680c094900c0e100346d05000c01040c2ea080b041e180300a904000108411301030a06203a0402c520343d07101500000c0c0f1960f503195690040c0c0d80c00c1c6c201c6511180c0b074a000304120300d800c0201002400040c402c251422218000107580e07841581c500c0400c3d191140744030800e1001610030700d44130000d91401d03101d50240726415a038a6038204e010f011461454030b14040380e11010800d0480e881c0703505458480c58 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 949143219 1250 949141969 949142003
    0x5220507030e062707060309021c12030e0c040603051606090f0302010302070503090a0f030c302a06030e030307230412080403021309080a0c080f21010f03 68
    0x200078000607452855141c07040c1d22a4001c01c1041144010311803075071f0000300c1c4960b51040000311440c1404403408131614400390030204502c1004420001c10b141000540e41070105070441c10561860540c07a40940b50440003c1444070100d68255a03141c2d842c203500145d500c40e078081c2c603802424054001e01c0e40110720140300550003035004100190046040b6400d0442c07801c0040c003500307184e400200d01c14040701c1e000c104000c0c01035814001f6104c51018000d84200443c021036015003010502901c00121003800014041d0b001d840b4850110005152650000d110f1403000c6030100324825140000d2408440e0000540d01105036800b42d4400d503111107031802e41c0280101110710f1201071200104d020040040c0024000e60b060b400c140c4103449070380e144c0d495401084940070110401c581840c0c1000044000109840111169491542004500002c1905215040d030242608050b181000003525a0980d81e02c04c4510a1503407071050345025980e01d07091016251403991100038403000700c24400b140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 949144469 1250 949143219 949143241
    0xb220308031b04050a1d01090b01021f091505010f080106381201180b13110928080f0c090402010e0910050a0603020a02030409050a0605220507030e06 66
    0x2c01c81c0da400401c142041d8452000400b00300060b44108590031074203d00015032480c0204140c01001881000c1180083c6280040d40baa1440c1e00800110700421a42d140703048102e43c400208170340c03c2014090b0f904003100704000204402e008100b03441521240c0000d00100501a11060f60001d81f04809a042d104403046031196205000141e29882040340c11a00760f8104007170001146403414040c12545824003107000044e10200315044182800c686000a1710707003405015405680503800901e507a600342c10354815024079505a5442041c80c02800f40d43d03410000c0301c11602d9890310b508400c50313546002e1140d132200b0b09554071889401000851a0500d40141c0441d4414018144105641003001c0054458541140c08a500c410300043c184110f05200c950400030302000d00b011850804c5010b0043c0d503a0040b44600c070003a9031500000b035003026094011400500002e00900c04005484c1560310040698070580b240f170074501700c000342c00c2c148640070301d03d4440301e0b0101030903d80c2c8a80180384 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 949145719 1250 949144469 949144501
    0x6090b0604080304050d06061706041101030e0309090901110c240129310f08030418110c030c010c03151401030b030f0f070b040b09280b22030803 64
    0x26403070380c1d907231400000c010603020321241402c0d20741703000340196240034640490f440f5452500d80c0d040603c1c103210f6002858000048560b43d15003141c1100013a910150344602505042c1a0b56219140c00300f0001d0a10600265083c034074913520b40c0d0825020718800010500c50400d02c2000080312003ca95003008068080a0900095011071401d182c0205c150752070314140031b91071801c8a4003c1505901072441d00300340206001c1c000d42c4440300c11051034203c129650740107078010103a021515450f42040c450322030340044074a0860710601c980314a00891080c3d2245c00c0308440341d00550800c00d04000c500d12078030900781d50601d0315005c0d030480c508200b103000e54940c040320007905040d80c1e81c41200f5196010003601c40300c00b50710702c001c19001d402d4a00090409143c0e51050402030414401408240c00e44c40648544502c29150a000040845840d034480036845801d14083c00380c080c4040740e400f02100c014a20151140714110034a03c12514070f40c0509058400904040b0086c0041013100c4800e400030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 949146969 1250 949145719 949145723
    0x61e03140703050a03090302030f0604030e0f19150f0513060309020118080309010311030f070f0215010305160b1c0b0103060305151f0303021207080d0e0106090b0604080304050d 78
    0x503142180c0383d6980c1031800081a000360301040b0720307030410002c502e01040754100c504204005400e848c109542c014200c041b40406082c400c074074082e00300f0219100c0b0703151040c068002610341400140e5a05010030712484019170b46000031109100b5030017050251080f01c00040468003402203091400c24220003d203401c42040381081180c1a410015a001c00140006860759801559030f0303001c1d4000240403200043c403090300015052003048070681000001e0b607408000e07030600302100c0000381c00490912481442109040007001d0010040c0207002038010300404160700c1d40c2c8045611141d00c04803038052401ea2049020b400c20303c6400304149a040101003250604000c259281c40e80d0303030355081810300840504102a02e100700a052580da082a10380c1d1807012000703039030080c29501c2c000e407a000e403081440441d1400281180800100c14121a030040344008108914070203201f60038080e105900c681d1300c8180c18929941c1d020b10b0000100e504951300e0000031341c5442d19210170320a10000d001d000b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 949148219 1250 949146969 949146973
    0x30a06050306041101020124090c020a02100c050613081c020903150412170106050708190c14030a0219060f1e050a110a08190618061e0314 61
    0x80c80e807001c101c030500480c030804680903100500e8000a086a1803552184074281c214590b48170940d4001c41803a0607120101004155400328546c26031900344200002500116a069501e40c2036600000c0f0b4428140300301b003640d036980c4030720125000e51880d2107c0900907201c2080080c80404070b016190f01200c0d41444094101204030001a0402d01c01c130106082c100894804c10040241c2044a0989103502d8104a07143c010b40040303040c1f040c02c05000d20801d102000680b1000d014481090362110703010310401050584011000800b100d004c0c0c40c2c11221030070211940244000c010042d1011f19845500819076516840200c0700351141d01d5078180c1391959070f0040c8540c43d5032580180711104415070040408100c400603030b01c2c12071724010710000d07a03c0d10380520480401440c4044500011041c40c0071406500e4030f035800121200329029810703089150190002da42100920f00030445c000c450303000c0000c2566591505110039000c100d0f500014052001440003400485483e50501002c5003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 949149469 1250 949148219 949148231
    0xa0f1403013b0f100e0303070504050904050c04021b19080306040c0c05060a0618061206020d0b030d110c1906050a090305012a0507020f0906040b060d0c0912050c0402030a 75
    0x100341c83c100a140012800c658120750880219540ca50281044c0640a40020b40c990f02d0100b0b00188180501c0c0900c510401071800442c06200041100e0155004014070456403048403201c016401c0b54600c08012450003014403507a0f88801c0300003617152003600880340394607591301c600c03c000040a420101c4018801204103000106108025070343c0304102e02c800010301541404400032003070040f0200038410301e040075014040d01041981c549010790340002e000d6201daa140c01702001410f00281c1142d0544942000400140e6002103100b03500d010f41c3c82071710b10a007541e50600c40c189000b5400d0010a94008608201030381c4520010600481c0d140340c60300f10070303840f80e5600b401d4a600d01d8412104490001810900c00303005c10703070030442c0080350411a19000c01b590204501005032803c0d03520800d18200080c12035183c80d00035a804690007880c043c3e413a00283c1c41c01008000380c18462000801c06840868030f0000451030803140b0b5004402885a51403100070040030303500c0180080306040d10344c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 949150719 1250 949149469 949149581
    0x140a2a0209010e1b1c0e060c04060806120a0b01060f030902061e07080d0b01080109062d05190915300605070c1505010f170c0a0f140301 60
    0x10005e46031030703035088155584d04d1031540d100b2415100301d1112221340d504210b050200313010141c800c4034100c407a40e090041d02136841d5400070302e10b50707003d064120351405142000300400141d1455a27050303400545504c410507501403822011902c1182000750880c82c2000841d04000700c941c41100340b0184681c026182068a0383c2e400c805401001d1030030200c5807605507007800c0790303040041e0b85d0150900308010000186400d40c04082e070700096260503848a20040340e24044110503984101a040140c40b0851000f0500f240c0202441e051060040107440c28885c608290782001840c421220b1960040c405440c4018061040703001d410301016400c0103950302180020002e004070351040f40c00303403914180d0311036908109c0e00c0040c0c0e00c04001e0081d46002d00500890300c4c2c2c1c1c60ba200a962000902107040004051020304d002d400b80440c541c44100111b002039044d00c090305200507904241c00c0705003840100c0007072609848019190050494070201d84000c00310b4004c0c151604403841c000009034081c062 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 949151969 1250 949150719 949150771
    0xf0d0e0f15030a0f050708150f10051806070210080705040906030309051002150c0f0409062601090503030a0f14010e15010e061207140a2a0209010e 65
    0x26a81c0c1841d903a502004000720410144580ba00e6918201c0c0144090f107429a40140421001820040c8c0342d0b00401415082d6120140c00c0500305001611460b480220024064456080014544800c40410340503540c90304048054a45140e0f0252101c1e4031000400c2c029140403a0003031000301008000d00c00081d07402258011600114003903250021010b0411080c090507500c0403441d082554410403000303d4600405000b80d0f0702000c84180251a4500f00c0400e809074412940004080c605101d40841c01c9688040e140b49110201c800030000c0854003807115090362043c1c0c1c800b82c035030740041c000641c0c40001e5422803031a4103a24040061001c03030064109090002c01c0e0003004092498408008890021000400d911074090030304000348a0f0a10001d001c40c4203680d00400d2402d5072002041201d40142c50b50481034403020b92403500e420410301c00425205c3e00700300c0701c0030511141300d2560303155034a40021441180c01900c280310903824001500e40050003e06400d208800c41800403844d03801d8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 949153219 1250 949151969 949151989
    0x1908070c050d0906031413020424080c120f060a02090d080d0b0112020913022203030f090e090a0f03110d0504080607031e0b0406050a15110f0d0e0f 65
    0x7545903c0000360801c0b0008089541d529040c3d2003044140d005c1c0704c0c4298811824540c2c03ea81101c01060750095503900d0348005245800c640740148454002069984000c61440030100054820f0201441841c060340e50780c50490b14180280e4001101040b9803500704e80050928203409000705410f2180c550700c0d95400d038490303500800020743d42d11280003d5070b0320103078890210303620840a5003801c0004001410103602800d071880c0390b81d40080e10340354900305425048880030180503824420b0784e980c03e001d000d0b40340c1d804030707407002903d01d42000c13a8146456150b1400b403a003810041c1680000c560b02c14410600000c0180c2c1441720706031042c80112010080e504080040e5039901f5100e5107400d00407444e0520190004040c036080012000c10919000c1080742035a00c44a408100f0044a00c00f050080c000c581009410a500308004120000708003c0b40b00c0d0042583c8c1da00401d0500c00d9903260300d58441200c8540c050308003c40040d00716101ea90281114000180382c0c519802c1203000040407160 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 949154469 1250 949153219 949153243
    0x30f05090907050a110c030c191a071203020301150e0a0e0115020f0a0209070c06020d0212071205152b0c050a120314030a090f030914061908070c05 65
    0x10f00010849a5268841d580c402c01c02442c00051074130089080000c0c1c1c0780c0b5030382001d00d8000c03580043c116842040780d0204e14001c0c01210702160b88044040c0c0b040c8030542c04004150380d5500301710242400544603200712030407214984000c6010302680001140c0d440c0005603007030b90182d0000004207003404c14680d5203000303081c00307006012680c48021029003400121840341180340c1080b0800d1001da00d0f4204020350000407803502d10f4894802c2e00d40940240952804050030a1001ca95550030f01203004101c3e0294003a501c0d5503030000080b01020055800488075a1920750000904150606120002600c002c62440a0448015078201055a20060448295001c0d06e900404000908041d14000007409000305003801c0c440c580c0d10702510324620000b4148541e03000100240e00f4001c035601150880354440d450711000242c9050007040e1008500542680c56010b06184081c0c1c613020046410341000b0110f52860106040819100040002c002d4418850342c4500d00e8002001403000c1820b01c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 949155719 1250 949154469 949154477
    0x203090307091e020c0601121b0e040201080a090213110403140607201c03020412030e03060705210601030605030303040b16030b030c0d020406050a091d0d0507030f05090907 76
    0xd0f03414010741d00a0090140c036405a00e20402140410ba94046566410b440256014200f140705500c0c100c1c00382031035002042d6050718000400302e00c84075080d0001c1e00882c002d98502c030094484a0741c0e24115070194070002d522407d002011096583d158100489213540e218040d81010b03501d4403245210103500e54141c1240e080b080404c03050310f4000702e60b1040180300d260034080a140e600019913584400707041e105112685847e01c4181c0503c42d0b011a00580010300481304c01c01400c0c43e0162014580da440d403840b078040c0c00c00040c0124802e0040d103941c810054451021540c4505540da419000601043d0406840f8240070556840810055000368400e01c0040d44c0c51522840448c2003100d6850031504050600846880035500060724854040b401c840b0040050381a1000600403d10350341710755004403144400054018940c0c0c0701f02546a0541c40c115000c02040b0390880c1ca60078900e0341c06003c141c080c02580c0c0803a00c2124001200101420114a02105000041d01c001c2c000c0b12640002 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 949156969 1250 949155719 949155731
    0x1605010917040e04151d010507020d05030912071e030519030c0c02042408010b01030b0334080a0b04020f01020f0325060207030e091b04090903020309030709 69
    0x7100c1840c151003200d1181d51a04260514442d00c0050801500c044c0281d069280d490481500300d510200210540404140228540240042c044e0408603101000750145142c5403044600031422a889541a440070741910698501c0100698018007030944401c0580c88040300302d0f100c0760300720701007460090311000d81700d0101c3d50408544400c3d10b0f0080013050b041c080d1121121b0381042d01501c24a0f41224046440c0c520f201c012442c5541a005101c444265480000384004042d0311003079041000381d07030a006208140040c16034440d048040c1d0310004600518003a0295910210080c22560007103016580c40c0c1d640c01194504040e002c02a60f00f0300507901480210700d440000050007000a0025003071038070802c1135448d03c0b8015102c000c0003900c403e0300280794032000c1c038501403601a48240c0440d2a00350f170707050040c501c103035900d41c2e43d014900d00404580d44030340e49405000d2082c00050803628003030518110340c02600c2408000c40551009004080e601d9074207005903070240960141c00205 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 949158219 1250 949156969 949156973
    0x1080106030c0b040510080c0c010c0e030f0c0d03051303080f04090b1c11010212031008010b010507120f030605040203041115180d110607060c030b060421020616050109 74
    0x400078090740080e03d100f2082100704226140c1ca8010508421541484180c0d83d0f100ca00c00d5441d4842c070000407419500e8002c000400c0d0342c000c1c503c4c8500303c0c0150100c42d214840c05507950b0b90f440015444540c864a642004400280300304000d0100c00c440300351400e40180e482d958604140c200c401110740f02c0e04080b409000c0e000451241c458070042c02c56801a81d030560b00c15001940400c5040508010f00c52000410280d0081080c3c01542d40d0390200ba5540340b9100d00540491409409000c01c25420f0984144066101d0303015280c00d0b542001c01c124070003e082d407041e1010000050004103268513a03100041a42d102d20185100718003501000b000c5888a800700114103405800c070810380c8a003400503140428110010b071080c1c89050300d401c2030b03070020b500384074200103008a000f56128000161a508001e019000300c135012101c0e880500c80c620103d42042018041c5001d200b544060b03044070040710001000c0318854941c0003405103440c11213079004500c1d01e0052881c2c15580c5a44412440301 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 949159469 1250 949158219 949158233
    0x40f06051e0301121b17010518150c03190608032805071520070507050f060a030f0e0304081b06040e040b04050c0904060c080a09111c0503030108010603 67
    0x20740c112200381d01a00d150b05007a801541c02d4003107003010b080248045c0c1c0d2032181d8500b000000000e4841c0c5006510b1300407810400394040c0c07600329412590303088a80503c0001c801e00003180760a485004668401980d43c0a00c0102c15400040410142c0e05520824401d0101d0511452000c0c0072490302840c0e1b01e004000781c3e00206891503101000c0181c251031a500100c0d40407056940e101d500200d0742d4102c2c440f1900403409044040b081400b4103001608007540d03104818020201c46109205807046149e032003040100e402203d902c910b8000d50100b00500d40070b44290700c002100b816a0400003034481d450340a05196030000d800003240e9501011000600c1404414104a01107048685504d4241805840e00000c0000b800041c41a20340c0070104080250601180c1c500c604050851941440c0506109015000500d00000072641c0d08000c0b444103c002d000d6818a41d4100340b101d1f0300d60500b1010f00c034801009080b00d07510000846000c400240e41840214020b060b02c00002ca0040c0c1103081540c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 949160719 1250 949159469 949159507
    0xe060c010b100c050d0e0a09020a0c0602030114120604020d1e050d091a1603030903020312040803071e200703150e1c020615012a0b090c0321040f0605 66
    0x117040c0804074202c0c05044e5101e1111009072565001c01680314608030030103880101400e08010b01050011001248208924400d001030a208a0300d211003011031681c904d448440076a07019410a49407040d40d804a541c1d11a40360f10042070040183c9810a5915264108803003c0021400241c0f040d00c1089040300740d44510621040c0031030580d10b00903040d004041070101c07510006003030680718000041450f00030b000340e41c85542c50144100741d520301840d00302425403003150b8100100d902100c00300d40304620303944043e40900654440b15640c1c18903030055138510390191910515486006004800900074441c20190728080c1e460100b45041c59100280c201388545071b4444030220981004410300e82c1c00204650403981c503180b801c20385481c0b400101d03103441c52550010100c05511008201b0381003141c00320f035800e50140c07107210155119003e030180c96010a91042d94160f0040d00c10250000421000303050840c6200d101d10318013541c0e001c140d0000d040c0c9501034030100b4004112941c2e8203000441d40 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 949161969 1250 949160719 949160743
    0xf03030c1605030d0c060f0b0a080102070c1d0613020903030a09050907020a02060d18240b150f0d0e0a03080103050c03030307090b07020d0c0b090f0a060e060c010b100c05 75
    0x43c04071604c600500601507080b504029003080e8031001c480591190907440607c05020203481d2902c0320b6100c021a6020350b20072034048424170081c400c0080c9004881c0c620b03840c1d4202d403803407000341511070704100035032a200107549002c1d59a082011051343d9030100000c224111268840401291900c820051590402041e090070354210b8007103d00180c0d1803c1c111680b100315140001042d007140145001117501d600c0009010241240c4021604d17103e00800307414420350240305000d4541c200c000d001c4a4000d6100a0704e034100c003480143c01d00100d0740050100c20030100e1000841c0c0301042c60a0b0718242c0321100079400b1403942d00060051080c01d00164194100584c0110b185041840700202159050722552062403404102442156a06080108620b8021580d2903105840e0070407603055900c9a030465114480d8110080d01e5401d00701004400c4070825280d81011105038030034018a5440303008040c2941d5681c4143c1d520343d039514544003090358400c3e92990000b501d140b8103103103040c0d040c082d1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 949163219 1250 949161969 949161973
    0x6051c050109151d13050115060507152018040504060e060c070201050403020108060f150921060a18080301080309011101051612140c0306011b11040504020f03030c160503 75
    0x8040308103050490715900003002e1540c0d801724040c0ea040441c01090098403404c0c08409070303400040d00350b50202c090540756019a00d40908486800100411902ca00408802e2089601c0003480820710350005400c10700035401038000b042501c00d002508541007120211561982c6107003114003900e00300450b41d40b1036680d40d602460710780c080d0000303010380c081c52100a040084c09000502e5035200c2c4600203012140c05008020794042d02410211a034200f61300c91030084078096481000000c010f10307009402034041025203800e4803413a00c02c0b0080c040c0b201d000e00c0b0a4620081400019254000540c000c241080c0551745601e040800184070a9204d24000010380c18501889042124080c88025400b83ca090210301464280d0204000d0680d82c2e03100b00c0c1d015000d06c104408064200001e51251400740daa0b09205000d811350741c549600c2d198400381020b0011660002d00d42401c1d481a83c005000900000c420880140040d00d19400301240d201036030803034050585808541c01d001406000c080700 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 949164469 1250 949163219 949163249
    0x20d050c1b1f052511010b0f0a03080a03200c01060e01150c02010e0402070b040507051503161e0e01080c0c030f0702040b09011e080c0a06051c05010915 67
    0x80c0c50100a03030b41d009411902e955403004a002e92610045203510070300310b14940d8000d44032401000e44012034a01070b1400550a0264280f060b180c030796450b0546482c0103002c45006400c40e280c1c01c1e9070b83c2000048a007411f941e50032098449440313a00d443d41410320441065594450781c1c00c11801d6404580c46178100c0b0003a0700052003071003c0740c445802590118a0003043c600c54500040b40c80745144034410748c001c2e10010b0007500b130042d40440a40300740c0c040c80845404550b03440038442207825a03161981000002d0003c145501c10b4000038045001c80c3d4505013240c24146420142c101e001003070500080b84102c600c03c1802c0d41c10001c02c0d81d1101490100a050041d840010b81e04c9200d2102e582d9101c410010303400c402c541c0c80c0ea000303030722446024210000341c1d030b155851070b2003001d1030050b40aa5142d030144000f8040b040091910301100002d00404a031030f01e030800035551904003003650380d000a10400c1d9030180d06464030803e4000d081195001c5081900840107004d6002d0729005409807849101d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 949165719 1250 949164469 949164493
    0x30703080a080601020a0212030d0b0f281509080f1218010306120c0317071101080a020d0f021917010e04020d08031504240501030e01020d050c1b 64
    0x30152410948a41450401950f0300d4004034104420158001d5000102e801c010f014000008007404d00707041c00000c100524000d04007005506103e080c51298800c010b0030050348092441a51071120080407440110115103410040004081e0480e861f000240c21003c03c100a250800c6486540f8001d100a05a0000041469959441082440e4102d0404031080007100e034444e5019400401d41c5e5500e013605d0504a20b021004841036100690341c80c84103000c40140c01c00170303504580690754447d00341e003036100c00d0900640e072120b00204000d002c141d00348000c1c1500382c424010282a108411801030344c0d8042808080c4441054040510030020101c02400203000320202c1c003415500f00c100015050764440c0300040c00d140012000401c0703458003100b0f001c450001c06c14070002d401011981440200001d4514030041d020048610644c0909050700304840e500035445188425200030015150841c00322082054134009d844100c04407000081080701c402500a0f0486500c0c2c0850140088003440 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 949166969 1250 949165719 949165733
    0x1d07030c05090a0308090319060204032d170d050a0b0901091118040207120206010527040308180706021c020c09010b181503060307080f0d030e0c06040305030711030703 74
    0x3d4000200300390342c0000e50381d8086d50100b00e0511220400b40901c0c0c0401c145281c1100690001d03c01101d103418003460258540c2d0914488104100002026000c0156103803210481300c3c00703205c03411803550b604100e502c80e44078040c090b480c07040700f8061000c51100702d13080c01d0112a01059000580303d070714080040075441503241c212480104010960b001218544000400034416040014144e408060055107082c5d0040f42c068120b80782117500c1c104400d414881c89c401100c080200d0b6040c5c0107c4000134002900580e1000d40104040d80c5107202a807142c010645071603007940020000d640148051085c0c0310502d542c4418088840c8050301c00e03022400040b442407481030040545000c0e0100c3d00c4100d00d8894840c00ba40e840e4002c10345030071a0030f030a011041743d51080d101d6034068001c0c000e002c181c262000501118000c40380f00109808240102c08800425000b0412001da0003103040710740c82980e41c0780103400514002c0014580e00c01803840c042c6050003400c83e1305406a00000c0c2c0070808070354a = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 949168219 1250 949166969 949166989
    0x1030218040902060903010c180f0f060c0c050a0801020d0b0d020d020121291f12091a060306010603090510021c06093e0c03041d07030c0509 62
    0x35200460b03601c0803403000070b80c0c03409900318980d019840c110001c03050583c003001c0c0c3c251100c0103000e0080718580310001500210303164050001d504404a80420100748500d0740703401d481c0e006148000d0702507210070004180040a071b1040c6132aa40101c1d400d103e080080c8510306a01d402203030811407401c034990210300207188400010341440003480ba80d14160401d09610064460303074000400603000e441039041d40740a560421004040c841c0c0f4108800d80c1800c280001d2140303442c000d2818042a40001140c40040e5850004041170b19a0481301c000b98100588500c042da81c08158055864034109061a007003051744000200750811020704040381000c100100c034a803100c0d10150340c541461a9000611016011007a440d038600440014400d01075400202c020944102c0011810703118500e1003040b01151021908006580d030701c000c08411034100130f205008189090707a0a050b91101c03c0440200403622860800f1310140c10860555851b118821a10781d2908140d0b00f0300000401040030f0746030b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 949169469 1250 949168219 949168267
    0x61c020a0902031b2a030a02061b04030c0e0f13030c12090323070b0a1b1406040602040509010b030c030a090318030302030403050609010e1f02040f030b060f010302 72
    0x58008041355010b030007654224004081e60003041d42d20321407181d80320915526882c030701c82c82030643c088851103c0004800c0b9a030348010ba600410094a0f41d000081c03500402517000610010200400000500c841d9600f074000c0045030718075242071a0130b58803103541c102c0051a01000e0213640b1100c0c030002e60481c0d8524145070b0000341c52400c141e0501c405075150003142e0005402920001f81340d0500058000080c10350380c8854042d14031041c0c0d103501130300c1580034121540340842d05000c2d010700900801d4009055550047e645000300705800f28000d0b0403c1c2054406503030041d0006824000e504010030801c0c01000140802455403078441100306c140c1c00702800d540610703138950000e1001e1600c10000d5840c64040d41c20900b03102a600e10b00a540c9038050b20007200d1501590001850740790f01841900e04041201f40a06148040364403114043e0132040140c08055500340030104d503500007100807401562260155045074100b81d8100404c80241c2004a41054010030280c0404195011b007121545 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 949170719 1250 949169469 949169471
    0x9040308130c090209040b06090d0312110316091d0112051204081006050411040e040302030d02030a2427062409121a0a0b0a060206061c020a09 63
    0x18031101c0301848107401c0000050040d8185000105001002c0c1e4000c0c41081000c860800c40102e80e542800300d42d00403004000e92002001a038040440d000e000c00c88135004030140700140c000180c01d000512078200b0b031108030200304440000c03a45650000c800c2400750220660360b17204a090321401c540008414044c01411441c141504410000304000700d00741c4191f2091156182c984403030040d65078200001d0b41d40040ea0605c02d001401d81810320a4121603080c19034a1131500e0b003001c024000c0782a01400031803c40c0f1041000d0508190030b48013450041e00425008a0081d42c0c0ba01e002c4034003c442028252640301e582c408001c1c680070052181441c81800d004d01600300788de40e04220003080680d00191003c0100700b0b07004131906503031040c440803c9407903d480810945401030402c0c000c4001900a0054044000b0001d040d89420080742e40103040d00400303d0000d082d9030125403681055844080543e0140c4240001031518441100824150a243d8070b129880b40d000205909190b2280b40c03040c03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 949171969 1250 949170719 949170721
    0x319020702120a05012702030a0201141603080105012705011d0a0f3b042909190c0e040302070302150d050a0207150c0203190306081006030209040308 66
    0x40d1180055010301a00d00415108920001d0400c41d02a01c26210440a10074421840f030502e281b145c00f4200807030b034018000300398122450b401512000107170b1042c02280d080501c110700c00750400044485420344030707544070340c029450a40058803215020b803c00c00c100000091180102c1101000001200c2d000d2034600a16680d10542e4030740d0606000b4019000301032001c000c02c809800d00340900441c0c0003540746814204401d06801291940e85080e0080300526111007805da0001c80f00150304070340038114071142e030404248402d2590a154407100e0504010008000d46c40f501030080450030455480b0341111110a1b642c0c98488807114002d40b00541c540c540840c09162003007240300050b5601625403203104480c005007070a19003004c040b1030940b504090029280c5003245c003c0e00c1c01150b101c1e082d040369004001300c200240180e40c07401e0341148814091546040c00d80015804c1d2100980c400061040c2000c040d0380c02c120100b591000801c1c1480c1e020001038580c0360390f295200d80c00d80b51481c01 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 949173219 1250 949171969 949171973
    0x12403020d0f0c08030a0503011508060303040e040602040e0f150901060c0602031801230610050f0702030a050303072c0d0b0c04180b01020c01080f06131526010203190207 75
    0xf10105500000d00034440401c02c50181e5811800031416106000344226050460400c200c4809404a07107560b059041400100701600264110f03d801610a56015007410784032900303590545011621312504203000d00034012080c08120078a008070300180c03404101903040042c00307400d070325000400401c00d039030000016550010300c2c110240d0300d007503020082c000d2000114104420a40c06035509ca556132041020400c1407804a41103010b0b540d80b61140c1e0f042030100b083e040c41c242c02410060360103008006a401c0020001e2004501c40c020320b4596941c80c005d0702090f6401c860a41401040000c020713003404150340d4a07664a11300540e80b20a5048003642c500401d503500340500c1c1d01402c48000203400007400d01c4004c0e0401421104203031b084400d400501c03401101c00d61425551405604050008a40c00d414030007000800640c0d80030004c622030300120301881034442164084850508510348090304200c0481170100e01580d464000d40c15400c0c805560b414201c500f2002e000d80b55400221038003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 949174469 1250 949173219 949173233
    0x70f0204231501020a05010603080316110718150b13050d0206030408091807030504121d040b04090b19060b03070f0f0c0204020a080604050112031e031b02012403020d0f 74
    0x5c4004c5d8808020b2211981c1c07841c0420a0780c200b514540024405403420741010361042c2440940d101c014002040c1461801907410a128040d60707502030899161100d24800443c43e040e114000e01601382d500395030303110604c100d803240b24454008a124000102c0120b001d030340c902069a81107908844000d03681c4003640002443c0c41c103411400b0307100c8518441000341c01034043d84150b1080f4000d50344101000740010b0302301c0305510140203992228400242504503420603900c001d0144101400000d440301040d1103003c0d242c481241d404015290340e0080c41c0440b007260003204020700c090540076003503082946000d091903402c508030004112070300000a10203480780860740002c50f00074000310b580e2409501c0003801e03a01c0c00c683c8140914202000060b4100e22008100700c0580c040d900d040d42681810402004424180ca241c410141c940344601c2111480c07030308030f0b0384625007a000025800080c2d0398840707458078000058280305020100400260b214006030320419030380b01e1118041e5554918010b2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 949175719 1250 949174469 949174483
    0x305010b0f030606062802010905010b041e15080307060b030f0303060d080c07090516030507050c100209040204050a120606050a140105030402030f030d0606020f01090c0e0903070602070f020423150102 88
    0x181d0744004106c3c0c0007550b60b03010340c440110300d4082c40003405030044000500c4262800e25000018232161000d003d600b160386548080c0e8800528403003d04c400703582d18890703861604003c1050320140d40d983c0350780c503140ca41041030000701c90845d000340d4207500c1c1480011301241008000903164500004408206400902c48400503151242041101d0709000a1288150140044020220385008003040e2110300500c01e880701405404004d0032102e0400790403030301941000c40f020380c009800707000c003040927a9501702e8003024044400601350050360500301081680c209500241c02502607000612040c0c10080410304101400e08020303549403614801321b4900817120041c1003d901000c030b2a044074401c00c3e0407120841c0c0140d801c880050310220032803401c9070800140200b0a4203818001c01c8480401003600c0da0208200064074184401c6403202d40c180e0707020020450304074107010042801c610303040c40394041070b207828181301c500c582807100040e903860742c05410001c071640e64201c58002c0340c2c030801c822 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 949176969 1250 949175719 949175767
    0xe070903240216110109080309190503060f0403120c0f03021c1410091107120c0f230c011d0438060309060f070504031b0305010b0f03060606 62
    0x115a2521152509a681c074a54081140c284d9204030743e203041e940c8503691010545206c0d40186142c4009101002815400724201c001c4400c12a94001080c0d074040c040f262003101400d80c040c00529291800a142e20009840b0700007072450004c50011042d4003045450242d4a01e003801a80d900c11413900b01441c002c103684c0c0403909410700f001e030413694110300c100c14080c4800c3c01701244900d4540c0e14807429101465070501524009202c481c000c500482c244001c440114201005844141d03203c0403004103224205030344107401d030b010322030f00e00300d08103074156580d04014058a1000700402c002030207800b06d04012030003030b04450028440e9075242d40c0101c10040c01c10005040c7c01480c4260007080c80d42e0706001140f42940c0203542c03805400e0400c2140c0c4a070b1852000361880b6aa2013a0449c8048005400142007010030300c404000a1101c0d01c410703411004025125071141c1c61848d2950a45d590b5540700c5002d480510407032240380c0c600098072504110100d40154680c1211501001010070038080c0d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 949178219 1250 949176969 949176971
    0x3050304140f0c0a0b1206091503060a060e1602030315190f080c0406030c18110324120d120207080a120513120305060409061e060e07090324 62
    0x42282c1482c00255807100203000e944c801a1541d031040d00d80c089002d4015081d159401d0070002a0052501d10300480d480403c0020306d100b958003100c007107403415400b00ca40800b4256903420070300100b41d52500d80356025036502004450b0001d18880251240009040141c1003c00344072502116036404850720325800741c8286403444182e48140c9040310940c14401c20a440c06031021807180c0c1d09217401030500b40c907005442414214903107400346c040c503602c4503207038200c103546ca900c480c20503000301c33006500038207074540510740c00c02d103040c400365070240d064070700d10720031481d0710000343c41000b007c41c405100381030138104584000c140c0c0003000040d2240e0ba500501030080011502c540c82d4116004c2131078414540340c1041240d03943c0103580300318403080314050404408020b2181c440c500c41d40056070702110151001ca010603607070340c8080a598014000d15501c2600c50500c4110010303502c90320008001d075100c603110034245407034085d003100300c0d83c000680072400c0d5210b81d06552034030119445014040d514 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 949179469 1250 949178219 949178233
    0x31806060619110d030c1209020d030f0302120c0a200714030703140f060a0c1e0309120504061103071e0c33020c0306061309080708090a0518040305030414 68
    0x11300140100940314002c008520007907401c0b2132114240c8207041d143c075405848806100c91a447c10ba40c64142e80d00a0b504140d005c000002e0f11a0348110814003c0e501441100e403034441c03004015011101c00103a148404a02c0300510014910000b4440126040400303100c04480003040400d017802c100d03400c00303810020041c0885079407600c0003803d0340d4007400100503510251943d010743c00540750300480e1074000694228007013081d414040e008a0f01840306040c0003a80c45142d03510800a0104c00300c628010500c040340421029401541083c104900341014500d015066030300c11a09031001800f814030354020340401420444d40d0551040680a01c1d52102c0c1030008140003010306041040008000b01c01c0a104504417900018000d01d20702002001b42a0b1a5590001d2050340180032584442d02038580082e0300110b1000c00080140c240202c1500d582c490000e0140320364204664420360240c6000400c21482c078541100090304158140b03031032540c039200c0f402c080400c00101074200c03040d400703064 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 949180719 1250 949179469 949179493
    0x2405120606091c150510060f082203020a02010f0905031009061d0f0c040515100504151206080a02031905070302120a020411031012080d05010b03180606061911 70
    0x54030507000d4104d0341d0305004d159030b001036110036040c16110b000081404902c1c0d0414441c060700c0d00940c0200150488840840f00346101003810210a1003500543c1200210300b0565031b01c180b1908000c000c031705050401d1890580443ea95030b1420034a5059555201060410041d2239040601c10110b14a40046041c188051068580812030103201303240c401d11621501608060103007510844c580d40d4801da21071110801d11501001d005440000c00a00b01300202e2a0305100074030300c007000e0050740c0b041807052000c05241c08640300b9400c82c11260340b000d1b0100300142e03000665410090201810560000e1541c6041d902d881c0c0c05800095028814000155841400050155001d4000c440a01c40143d0440307003034819220030b98841e9040d00702c0390000d200c1841e003c81d9100c0118441d02005107020302c629005e03021240c00f82c00204864800006005c400d60100e90720640019155002e040302d0300b80440060540d1140304082e00c040b20500e4003081c88580038102841802e01840180d40741c18040d8 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 949181969 1250 949180719 949180733
    0x4020f09040e0f100c05091903020402040b040503070504140103200a090902090a060501020c1c1406070210060605070308061906050a110606030601120c0803042405120606091c 77
    0x400c141000d44c4910500070b400f0704154010900c0001032611031030f02d00881d001c2807110704541041c3c1600311010007400007005844510042004002d507140d51611942404205400e00c0480e070b00c514495030801e000c03100c102d04480103850469902900c03070421207400c0028074804000e640d0003164806100703040000c1d0500d00317400c02c00026200722103070046691000b0084003250124002c950059200c988101404e0500a01403c484562001e40301c1c5680d08a0382c803540044082c00b0780504542014040c480c209404000e405080e544c1240180880b45c140703000100176010b07000c00641006403000210717205458850004010759007444880020710f4454201400c1070340300003141000150000e01e40c2c92240004100540102001406803855910702100900e00803a081d6061b60704840311140060310400400040c130040c07281030341050b0003903000c031034040c1268600e031003c101380402000364103042c1000440b1140d100008645068076040f100340410040501c00d001e42c0d500300300c900402400d01c81c1c5c1c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 949183219 1250 949181969 949181983
    0x21060e0103030909021801210f091101090e06011803050a050109020108010b124606170604060c03180614010b0703050f18060d0509010e06060f04020f09040e 69
    0x43e844a080c41d550b110034443c100c0c0300b2170741c0c120a01c3c028500098100c0d0f01c5180c00428000742012030a6001081e103040304100d41038509441500703540c46916804001c5070b8400c481d9406001d080030311000d8035050702c00740d101c0f500611443c1008030307402c2070300c0402c1c0e4181040b00107503030020111240031903507241040c000c0c0607480069021a055400008845941e10115415500400d120b0075054880c400d0942c44040c000c031842e07580c00c2400c5c0322980c41e64410500581c0b44580070b081b10002001c80c0c540c440c02c44496030000f90603000b03403400d02116081c000544035000380d480f000014034807a0000040f002401c81741c0300403000726403408407031080c001c03140c00000000c0c0d00d61190101503681c0300d012000511543d83c0c028040381c01440f032914040320003405803019003581641100d145080d04001007056211004000d050350351402440344000c1c0900c1b071620710440000c010100d034100007000480080708103407202c0c41550002900f29288010300103581003035201400c20304c05141300b81c807441e4a0740b44c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 949184469 1250 949183219 949183223
    0x50c0d020f03190b01051c0e01111b06010501080106050d0f1b0e06070c0b031003020a0e150909060a021b0703230a0305070206030a0902031f06060503040b0721060e0103 74
    0x440305000440243d024813480041000c140c4820f8a0403c00198000392401c40030041079459a40703042082c0c0442003802400c9058110380080c40d545c00401002d055074030130b003800502e25617003c00010b2007541d8004c900301d410343d282c50a1040c8c68260200081c009894101007240495080c40c008200308034000c1c001c88024000c9407200c00d008144402408010700614801402508020004000b070104040041d50042032403400008060b40703070b40224a8102542e80180c040c10407600810540160ac04460b20700400207c810f004181001c12034039a44450161541000e42e41c0080c50b1008000381c84c0000034140224000e90300b91a940e4101011070448580c0249007614903400c46081000010414014440c2c1c1529140d042c84150380912149070001400509415650395441c40566401c20080351400c2c0440310703124658514040560070740c0d403245c0c07003101401418002d003c0081ccc030a810180c3d204d1203a182480e54002c1143c80c180d80611030344200d98a081c0380481c089407110100d00340070306981c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 949185719 1250 949184469 949184491
    0x190e0f03060f0c090105120403080f01050402030402010c060e01060518010302032103010303051305090a0501080f07050609040b0a0b0f0c0c0f030a151e0501050901060c0b010306050c0d020f03 84
    0x1024540034903403522402c541400001c0d4500c00000d1140390010040e05800c0c40624025090268400c0031140ea0034095500703401007003c9a0400c07074100c2070020540e0241c10251015411410300b075001130640176015000800150300c82050103d03070a000d51001c1c00a12004000841c0c0c0101000c10800021003130000780d019006480e803103070400f44411a42400c2d51101c10700540f542e8603548080f0707000e40185030446004115200005034596825a5890041c3c43c0c9101c0080c19501d00701c19540b070800001c151120301c0d04441803c11aa5036000c080c1ca20004042e2404100201c0103000aa011a02138025815074440406d41c815910000b102070400c140c40c540888d540041c00c2420091010005200f403640741d03002d00c90800000b071004041220f100f0080501150b1050340c1042130919030001d0000ea103000e90782d400100258036041407050300401e02820300101c07180590f00c500c803550005000c060309040d00c4801242c1caa0001c0c900b210581155408110744404605551200e2035000761440c4501d5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 949186969 1250 949185719 949185739
    0x20906030a020d080a0c0804080607170105010c0b06031216150605060d0c120c03141005060f1b03030703090b0708092d03040e090d03060305030901080408190e 70
    0x40c20001010352085400500c0d40008404960b1a402c445d8440c00c160410020403800c00000240c2c0d0401500140a101001c0c02c050302d880e050080c554040d10300504400d8078181c00404c22079803c5800f0001c0710360000c07482c3c11242d4654000c6071406031600005405080d000401240490340c840c0c03450889441542140324010601910030b00f07844181c082d4950040040011042c21600e6078001c444034010b504013100301d0301400328414125480140003e0103e03441c0c16040000e10702c41c0c1305c1c0030362100030792000000715070611020a50b81c0c000d408442104010008410007030f0042004640c2490340d132003007100d660b4501102c2c0100948801daa048520080620214400601030302c0c00324803d01c001d200070800314000d404e076011140001c0400144003460140d255611103828401803029116103030904607941080f0203424030340040f0000319010145415070500000350080103d6980540910f42810151614202030f42d41d48108180109506040c241003129260894140a0002400c661640d52 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 949188219 1250 949186969 949186981
    0x109020d110f1b06060a060c060902031e010606390807110405091c050a18090c1b051c120e060405010606020a050c24040308040504060501210b120106120209 69
    0x44e954040e200a944580320001c10f03c10148592088102603000d15000300701590560003107810319800f100b6110103403010f20640e0300300490901400300102040d1421510340000c11040d031940031040102c00c00e0050002c4001c6502e102021000501d0540200525076542628946040c90510403404240140e080100040454030b0100e0800040740055112070f07800f00d07042d40100c0306544109403202c01c0c05090b000040c1e20155000307101001d0280c01a000601e600700240181c2440291048400b00c12408942e1000141000c945500a47c1e00c64203460000c584009083d181601c90158506156151a90160a05c0c2c00052036600885c0104000c0000d076480e1482207031a000b2404000e455540100542040750410035051441301880000c0c00700c00301001281c07442c41d61b025600c1075908150103d010f01c100e01e494440d030001404242803c02c82940c810000180c5011401d0705040300a590358400c00c45a1201c500f807240e0800800000c01c000c0e80c0b10a40700f41342c043d0820381039009040b00030009207 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 949189469 1250 949188219 949188223
    0x406050402030c0a030b040e031602030124030609170304030314100b1e0415080106031401120b060d1202010204030605150a0b031312091503060e0109020d110f1b 71
    0x2c02200f80503010391400e031025405401800c0040340d02500140d855944c0350480304244041d003681d003281e5100822001c030600425081d0b130954404146029100c04c404000d030b0b1100302030881201d41c004800308200d800381c20032641c5c544550b80e00c0e51100d00004200400c01d03515502003031328001e00e00070001c010307242d880c8084104041406110b00380e110400004400220028007500c0f41c040171201e041c90640c8516110600d03136a0010b1000204a070f010040c80380e560140501d202400e070b8004090b13820340c5040540340601c06050409440000041d02090b455180d0040c0005e000380c01c850506040c111003e8024000d6025200c00d1700c810b4503103030104840b0308e2011241581101c004140c1800c9600b008e13800e00c1254005041c00c19101c0c41c040c0c0000001c0c41c402c08003180100e1b01d8070390354140e5283c40a004032a2821500e100101450400c080c4141c008254116054030641100141c03074289803c4900014100c1004c10410f00b10301207028000400e44000401c13661500c1120040550301c100003183d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 949190719 1250 949189469 949189471
    0x9130b0405070c411218130209090402010c030e09091c03151a120c030604050901181101050c031801090f060503041b030209041505180c06030c070c14040605040203 72
    0x450094010075a02d081074a1040344d01844120701d81600e02102000c41c050a165006454082c2c0b001201d2440740c180b86422000409402c080ca4000e619007000d06000aa24080c0104000d0500c6001e00042c001d01d0f105201045400e41e020b000b894083c00c2032200c941c1d4803008002c03294240d00d1040040c03001c1c01d100c1d0003074a40c8002022850000740d800c1c00400388400d04120115240000c06001141480000f04d0310390340601c0040000035a40c0c00c0200a01064850003007078402542c3c1040040d508031000030021002841c2c20060b03000070b5040c501c3c0101e51078070460380309480c58403002c144ea9007031100100321383c91002c000362074214882d95110703243e05013a032a92045070003190041c000036001c02d04915444117548008100d0580d034a450354000384422005a60544140580350300b64284601c2d58413595410507620304915440d80421102c1c19603030302c1d41e08401c40c02075802101144c40d21007144d0540784150f5200350415800c9071917180203210039010285440c0300c3c6c0e00f4040002820301f0103100712 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 949191969 1250 949190719 949190783
    0x211514090705331603120911130f1401050414060907030f110703020606130506031e010b0301181104090305030a150f0603090213020f09130b0405070c 66
    0x2500914809504030f04103480c1e402040c01950380c5000310b00c800040e03190020003a0315803800309141c0d400b0b4641801440805030f900380c44000d5140c0100240880c48144503006022000c0b103084050031001c0300343c10003512102901c4c02c0294202505c0f0030b80303421010b010070b058440a480800500540f0102c3c0e50101300c094500769088105a008900218400d40048500100382d100c0450149815424200310303a011000a80042e0484014000c2510302800c0d10007600280403001d204900301140020717207400088000307100d8400341c110481100c120a4100340c90995009000700589080076544200b4003a1407007003218501d142c40820102c3c1d2602c2e02c680c0e481700d41c0558420b0b09603500c00e280f0700002e081e000000c003210003901c400000e0002420411401030142c0342da000ca2014007520511004d510007000c400621401409080314104c00d032401d032018220200e5640003038411045007030f0014200c40c102143c001c1d04010400611582111482810314814580d0f40080c1d201d00c008512010048100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 949193219 1250 949191969 949191979
    0x301050a051e04031e03090b07230a0912050601060215070806040b03150a060513110d020708070813030312051302060307090816090c08070801211514090705 69
    0x850600210707050b4201da115202c0d00306081c0c200030300c000c005d8410b600028a00002500d90901200700685a000682c100c00305041280e408845801840034001d041e4010701044600403034004c0c1705a110710000401080c1850524204908a0030225161030003409200050b03c0f40000000144007070749a803c1c40b03194299210400f0b41c5a82c01040080d200d41401c190385031152801c114407040d0b40d14040c50080510440020714903280800380507080c40d444102190300c0e0f20b455900c1040400c0305040300e03000141c00d8001a5070b403000d072400e103020717004650300500000300214008002088101c0d0b6642036a000ba114003110002501d83e032010780d0000c98806c00941c0040140301c0050802e100a50b801180906102c1c0c603e94440c3e8207180b408441d8107003111004600e01041260301124410442c8106151a0071102032070b0116028268002c103121728042182058407038101c000c441c001e444c05895000e020b11000441080190010b01400c04480c001222a00017241d8001c3c0c0019250040301c0e80588 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 949194469 1250 949193219 949193251
    0x90b090403090e0a1b0c020109081f050c07140109020915060a35041a041a090a1505040c1e05010e040207290c0a050d0b01020a050d0e0301050a05 64
    0xd60426500084c058000fa10f0311349000b810340e043c0105480c002e140341c0e66111040d02569000040c00c00000ba4411119900302d1214001e101c0c445030ba904600280c3d507a008610380d02c6680302001c2d94480c00c40040c04401c0500c0110703118400640000c016a40215141d40041d21020b055000c3c0d04d180c10212a48807008111a270a20341c003c210610303400c4807603240700c2911112204850210350300d002000c1c1c480c5540b141003100b00018204400da410200d02d54003101486d00340c0d9003070f50510028807461440d03410a00025a1078008000c0f151815511148040503141d04e020341b08003809041e60102c6e00842a1400444e610803d0030305200c4604008c7c1914001c2490880103503040c002c0c3d000d42c031750030980800100c004500183c50f065040000510109800c254040c088148100b0162403800904010041d581d22150301130305455071002280000540c0182d0381c00181c1c0f40c0403039050002c3c480d001d0266421482604040f5a210002d82038000b0f120a507280324680c401c980f0b04070358034105075244d00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 949195719 1250 949194469 949194479
    0x30307120e070f0b0409060915031e1211060a1a01120b12030919030b1602010906050c09030706080f0106050313051b0f270c12090106090b09040309 65
    0xd0420400d002007441500c860741e840d02c5002c2408001038108120365800013400b0030098500380b1541000b030010f41820018a500c1ea45003601000140c440501541c1314007450001124a05001c082101e0307002a504030151601d440181940070400d020700004d010b075500060880c40c0718064803545007441100f04001544103001518410511039125600d1607903a01e000c010303500d40c05601c1480700c00d500c0040d603c3e5a040300412011046600f0744101c4036141035020400207103245890b9402c910100048102e070072100000f01e0045c00801c0c0058000c0e4140401d00c08085096401001f00354004d078143c8429580b40c100949040c2e0050310f014203240107507001000654813400203950407401c00103481c05032004940b00e0900d0091100440501100308041d02e6003a0301c3c0c0f90440c118611000c2d220300125030b000e61303d4440c25145007254404110092000248444101c008580020140441300c1d025030a010164030700a000502038800150b190101d502210b252880d01da5104e01da00d640c0d45c5804a00b42 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 949196969 1250 949195719 949195721
    0x5090d0c08030702030c1b0a3003141201080d03061d0a1d03030601090e041a040213060b120108030915251a10080d030e0a050d02060a0e03030712 64
    0x70f01500441c0403e002122502509001200c6800c00b868041901c1102c444108801e50b01c0541c0589907007a0701d103580b07203040d40ca00e184a01c00c03450400c04c0d5107850a520f060540b105000f104030002080030004507100a210100342c00c9042e1b82d00c01c0304031200100c41600c203500312441d500a40c0c10b62007051200001e040d0116403100da1180f00f0050100d160102c801c0a100d4004034440c00c921150804807c20a441d640005418010140700d84030103510b050544503a055445400c0d0704412884021000509644031b00c504020781b050b001030b00704180c41d91604400c40d40d802a06422020300110400044ea44c040007082d80d50600000300309000d030600702c191141c0c582c4d020310b0705942e4104507042000d200c54103400c1171198945c010341c2e403808900306041085d4103021004100f46885800e20400384280d410005100b032405256050019140942900307481c548082c240c1c1c0144075125811000c101242d0102c0d126000b2051500280000000d00c10903d491740000c4408000141c150422040c2d07503112 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 949198219 1250 949196969 949196971
    0x312010603110d1a0a0807091107021309030921051506011b03030f05160f0801060801140f0301020a051c0614091504050403021b03030f04270504051005090d0c0803 72
    0x843c513a02c0304201032804a003203001c3c994800c1046070818402003090200724000c00310500302e0070740030924140540c0d0004041d100914510360490359905400820580500e4407030f0050241c20140c120840c01d140440d40300c1c2c40601c030007140c4030b02600c42d00010303125146803118084d002c142c6a41802070b060440b4401d00606d601b0050b004c06440e050002d103074034218410030780240c1c5104005040e503180c181e0081c084841e1000c912040050010041000c154865805815038100903080c1c16010301050000d052410043c0784035605520001d004504150040000c1107455080c8032984a004002e040710300031151548030701007840e880041401924a008040c180e88a008485490700440d5035401040c1168801c6030100d0150380001038a103824460341c00c0300e01487c2800c8008500c5d00302001c004071468020340c460289040882800040d407490107115080307815040c10001c0040d80340c18145180e40e08440c031003800ca40c0f880e00022411a101c00300e591400742404d03496100c0402c0c0160784200710307680 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 949199469 1250 949198219 949198241
    0x7091107121b0501050105121501090209220504030e12100b04020c06160207090c14070515100302181302090402120d020f1501030f12140403050312010603110d 70
    0x50708001c0012240107001440b00300d00d00900c0005001c2d8100424826181b241d0450f00e03402d80d109019448421000081860540b00200000740c0c035081d5190115408014041c02141c829401e008010b5080c122a0710180c4914081d60303411954104202c01d10440d004000109081b58102e40b50980103c0b1031500200b58072000540700520388205600e1681c2080020351b02100c59102c4114506c18540e4100004000340000312020012401c0146c0042c085074100c40c1d00c4071020002140300020b100043c8120340d00243c0c01c501070701c402d140c40072091101c040c841c002213100700111038407401900d0000a68034803840c084c102c4152451056001c003d00304c800100201c0cae0107114280b4116480301e050003507940c0d081098000b070590420380c844844c18610011081602c2c02140700c0100007003901c584000e090550440041c04009203c14000c4526841f1142c40d0041c100000800104003c030000c0200710000801428050b0790742c071030004034183c41c00c1e40c8200611000030321145104440c0c03688440740c000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 949200719 1250 949199469 949199477
    0x3082a030f061507140607080108150901090b0f090706021f021305130b0319030905130f0c050d151a1c0c03050601080c03040224091509030709110712 66
    0x94114030441043e0741c0500012903035910075401d1501000401c010b659002071090510010941c104800203603182e60b5614090b4400b043e6070007140300701c8001c2d80701d4200d40390091030400c094901845282c44149007512420f200b84103181002818500c08240c0d10b00c01e0b007a211079210842c14214000c4040d401c20164410f070324199840009059035100c40c41099010164004030300008031904141c24181001c4510400d8400c90f021100002c1c0d000744000b060702c4c1c04641c00881c0d199141c19031401030545444440f07905290041030841150080c01a14040c514940d05116501c850030000d44101e14520411100808a1200b1800805104094050003e40c50010200d00980400f01d00a589035210b901d00840d07690380500241d541c1c1328048a82c0900340d402079905d542042c0d4003044000c402d841c3d107080c40d401281945c104150415041310a0701c4001000c10920f034401a500d43c0d040d5002414241c401e1140e04400189002603000301c00b140000038001e09d0404100303882d0b808810751070440810404c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 949201969 1250 949200719 949200739
    0x40c0b07030e040e160f0b030c070f0f030206042306070f0e090f06090601090602030702131e1b090308040b0f040e1608250c030509040903082a030f06 66
    0x1500c441c8688010715a180000302845481034280141c500040c0c1c00c1408020042503041c0104447c50048036000400c0b00342e81030351f512290909511031030500c04014281059100390400b81a40001c1395401180580c50518100344803280103d030700320b84000e0340340b082c2d00000d000441e864055210008400507e0529551030407940d4001090420200c036422803003030b0400b081c09005d040c05085241c0c400c5007070a00d00311071030034240c01940d03034011042c0091188286181c3d0381251300040c1c004161850b070401d078010b1821120010000600f440c65010000e0f101c41d0154031003294456881c010840e40c00403801ca25140c144030040085604c400036044c8110001c01001960108100c0c1c902c0c0b18410301c1301000b200c1c803615140104101409045803035145a501d081d000c210750b0301400d2000642d0241001d094007405460f0507902c2e030095103011a03120f40b92185a00607d9000498584960304400c20003e000d00480360b0100c02058020b46005e00701414000988040400340d01c541e00000003c00200031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 949203219 1250 949201969 949201997
    0x10e100509070f09170318032802060d050702030307030e0c06070b0a0212070c0c06021204091e020f040f0e0103051e030904091505070e0609040f090c030c06080f040c0b0703 76
    0x22140040c00e88545c6600004400c5170451281e00c03604500d100444c054490042407901c903601c01e0107400e800c030141c0103444000c00115a034100440d20100b03403a03041400701d460710400203500c9400495805000c281010218152400c0209171008000030082c0722a0805509403140c1402010061aa040041d0700300a02c50b001003a4038036861042d2010383e1000300d05102481d102042c1c07425940300e0f8007598402e251941880c030109003910103480d80c02100144c4224200b55840b0046258400101c0a500c002400100514018002c5c01500c1c2203100044172107a44001da155842c2007448003518540140c401405800500044100100800130849051404c0c40300000e086514080d42110f4491042d105d4205028075030292550203d902e0034000881e04d0002c000c940140f0a80740d0080c07045a4840341220703040b0f402c1c0c0c042c140c020342055481026030707120328207800d4180c040e014100c0458812400505400481a05135104a50000d4118592440d080564020350080e060440500494080b0910 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 949204469 1250 949203219 949203239
    0x1b0e0a0f061a1b010605210309101206170d200601150801090903020d051c020412030206090f0a031d03010e1b1e2103070506010e100509070f09 63
    0x201a19910b4009a56002d8200c2e00500398040804001080e41007607801c21141da1802d040c0100180b16181031740c0740b100310081c418210712401880301e600c1450b02103030140a0b5404100d0398403544100c1c904000c11912140d10050788010026100303003a43c846050082954422443d208114219182c0a8800c40c00508250704080c000d070041d400000000700070600c400d40c1701c40c5c0c00e07006145003502048408402e8500a48809001034480b050010004148011100402001054000c0181e045440380d40f40c5804040003018143c09500610801340445d02d03484010405a815040302401020410000d0303400380d03400327801c10356540c420700b00c18044042551420700480f108000000c020b004484103a190020000d0070031910a8002d0181c4100607901001040308031030445807c90f40000030b68010824099484080b403408a800c0c0004144a0b08003d4000b50303240c185c1352a484461010303545d401c603d443c3d02c2401e01c01d40358008440c2c008106d13518040c10000120790942c2c540300060940301d24510b2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 949205719 1250 949204469 949204499
    0x40206070c0317190906050a0c11101e0f27180902041b05040e0c0c0304030c1a091e0d0b13170301140111010608060c071b0e0a0f06 58
    0x40d0340f0000041c00c1d5151a06415084560605424010340003800d111000340300f0b024035500318080c001035448031010311035040b442c600c6900c401000304124091402000b0f00709810480900c82c0008070399480340c881c03801099080315180d615514451404070310f0f10404200300441c2c000540c40244000c1c0403460125858035681c072013441c000701081c8004244144802c81d005010042c904001c0903c2e4108015804004c44045a00c1503404040c562100d0340c550020303208500d5440340304c1c070001500204111800368224200c0ba0a1a061f0041c00549140e0841c00d10401c404d03e5031100c00301101580da4034050b814100c0310388010b40a8080c803401c96813643c003940d105072121280000808040703800c10050707010b03c03007103481c0b4071400708e06551404003000581107030101601d050140ca000550305c55402517210710001c040500403904207050040d8030100940c081001580c0004503200d0104a0310300c1c0d802c00300200c400101030500107559200922f0000c1441040900b115a11072200013140364001a43c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 949206969 1250 949205719 949205753
    0xe2d120a0509040c110c041b030c11150f010611070504050903120a1d0f0606240a0305070806010c030806060d110c030306120601032402040806090a050d0306050603040206070c03 78
    0xc8961170040001c0c0c00d1800c200220030794410b608100ca01041641120500550201d00e41800315450256110a50f13070310b0600001800c4503c203440c0c490b1107200c0c00141c664040c544562801701c1a0b6202c0400f1544000c601e03000ea030303281e8803e640c101f205052a43c00300d9030241952050f07130300780b40b042d800d0642602011f4513441d0240c1e40701c0202010103e211403401295a03002c1e001001003d01e100c0100d502c4580081c40d82d413207100c0c210380a40108a20a103624010445041035558440120b03070080d00405d000d4030031000240c4070100050f00365004144018401d0b406848601d9181e68039410040a0350140c648842c0302911070b0940c124407102d070ba010300707001103015010b5034a1b40b81c903409005200703610306010205980144010000b19401e00078161040300900a8200000306112211020380301d00e5102c182e0501c114010070485980100e45154487c0c0b08d9400e903400f01c0200781d030480c1680d080703001e601c1e030191042010a0042c40c20310000d02c101441440040001541c90f150a800030b00a8006 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 949208219 1250 949206969 949206977
    0x3040b2b0c08151c0201170f0114010503060924191e0b0307030e0c0a170606041a040203040609020301020708070308090a0c270e2d120a0509040c 64
    0x8007078040b41c00c40302d403036800801410145100c1048030b00150b00c1e108505850030721000c0c07043e03405003035921446200c041d04030387c2c00c09000c05090541208843e440c00f4407540c055201340142e034012942c41802180d001d20002098004142c0300c402d041e00c42500d058200a080c1d04202d9031044064940c10f0341150603407550707265002054945407103e45103001142c6c0801124011020511000702c0b0b81d000c2e203400ac0f10038900000d561141c44040c0c0e207130081c014800c9500c0b02041c0400904000503a000704000c110200c25220107407540c0003400262550b10300c2458001404107d034059a0030700c1d0f409158000d01810b0301103200c52990f004a0300f264800c2c0819540c910300041c1e22030034950803000254100c20801b00800b040c2e0701c02e4458542100042c0504541031842c0c60303401400717100c030700c01482860030604420480220440201c50751820884031800390a5036400d10311021007075031804240c4501d03c5030081c041d21000c50209078003580c071040d000001d10109015507900da8540e40f1039404a2001784d01c07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 949209469 1250 949208219 949208231
    0xd140304140603010605040608100f0f05040e0a051b0f060a020f0708030f2506060b041a031506070c0b0f04061202070f08030615070b040201030501080d0203040b2b 72
    0x4001580a2012101c003800340308100300400c0102c0c0d020f000c44080b220280381100541e00c40c003503a60408102540081108580700c0004906441602c42c1c0030b0803154112000c1120b0b04004055036103402c40701c0c1c0090102d401c45094242d4030105511a20702282e0700a15101100d8040380008082d908040740007001a4000344e030f500102c0404000c14005098040d004501f005a00307a0842c15500c50760090340c000e15003d400c2c107444418945035071110b4540c062020b01c403460316820444407640140c492520550360704850b031074290600400300c90040c1001108124242100d4080c4045680820000c46000400d50000a40755010718040c1c988400c0c48a0015034580c075105000308409660302c00000d00c14130410850700059941644080d040b43e10007500d030707102e54400340005e401d050340e070b00200780c06603000031140104081440080c2c0b15900c04d880411880e41c952451940d0341d00012030820150340704010078440070012801501a007c031210522580350301c48000610068407100c031180031203444003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 949210719 1250 949209469 949209479
    0xf030a050c0f12060103060f1b170105041401050d080903030c0d20031b0705100306180509120c0307021e120d2322030506011505030c03060d140304 65
    0x807081e0721542a00311040740b41c201002c64210313110101840000c5c141540d0b45041c07041c0007c41d8010752003842d5040110480c80c100803202402c001c42c9030750690490a18040003040318a800c2c07040c40280c82c2d882e01c00035250303801c0409120030140c82c1c1006031004030082c4107141e220340d01040240b41010f021b00c040d0080003841c540c040e01050b40d00025600003c68500c000f14031150000c01c0e00e25121000341e05030078544503404064101b0f01c141d08039640180d11180f42c0d280d400e03015005902100e5640860308030f00080e070070101017120000e03158400541c0100780f00e9030b44031504030050002a03503c17005030b030b150003400c0e070018035104d44042100382101010349418100c0e1801d580241d5001c03850b04003400c80f0a1280800401c4000c01103011241b0f02c180c004a0b104c40c544e040c0c00e81e41000b401c20f0003d01c000c45540140d240000491008603610710030300c0000720b5107036120950b0000c010781c103450b803d003561500f014507415904010102d030b4100c45501c03440c1c0d010480c10442804464540d10140d91744034108 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 949211969 1250 949210719 949210729
    0x20d050c1305060304020d03180902040b1b19030f030f0218040b03010504020f0d240b0a0b090a09020702031f0c020d0e0a05060703230a110d1205060f030a050c 70
    0x340e201d207100f208244100b20260701c95016058000b41c1c0751416a03c0c0300d10404c41010300c100540c002c020000e10118001c140f800e503c0000340781c1c2c03140122080d00380100c0b440c4540c0d9551205020038515030100c8800000003402921030000ca040c1700c0c100400d00350f070300741c040c0c20032600050b0f4020302111005a100360103013054410801d2500c02034009001030700e0181c000c40c104880e01e021260107150001000300612500c08003c00145a00803454400801d410301c880c07010b090b0342207440c0d1084a0742940014000b402004990211401404000300c81d49030882c0000290446182644c16004800082060010000c00044140e241010000d4a4080403800a01e04404108668280401035580001b01d5466584003070460304126010380d5a500c19140440d400400c60401c01e000b80002645c1c461000b580302d010b0300e4140300f159070704e21a1101d00007007603507951004054a00492140780c020f802048454200d41d07480303240507207200c0e050312015001c40d140150b1b0f0780c000d9549400c05540141c052501d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 949213219 1250 949211969 949212007
    0x90d0f11010f180b0307030f0617070e010807060507080903060a051b040b0306092508060310182a240507031e0212040b0c0106050102070810090501020d050c 69
    0xb291034210100310f100c0740d0664111031036000b095542034000c000942e04921035001070b918003148038000d108007a500e04464220420100d0000240d004811f0007083c18251507020320f0407110240b005018007468201305503943d0b484501c2c1550a80c004028030380c100d440800c0690b01071202c2c03040004103890991300003c00b11070380d504443e0b0840702c10802003050580c95001d0b00e0b0010811104d42d80641c48038a403c065441d0452540d8480406804a04a60b1074101902070300ca480140c0544045001496aa0007101c0c2c2120412190049160101c80854078504000070010301908642c83d0001c1e44401d01c02c21125240c1c00400d01c1c084401c48540d0300c1d1094801090000d800781001410031200307070f501070451034000c00808007884a60042a020901c00c00811500b05400c02c0c00581d141e071180301d200d03925030104400c6c4e0300541c00d0200001e455403001441500312015000640a00c0e0344616007032000d0100c056066806640030304c0b0801070b0385c00314031440340149980e2045c2551481d01c04441000c03142c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 949214469 1250 949213219 949213247
    0x3040b0a0e240a141b0d110303060a0b03091510060314040b040206070807150207020405060a150c1506080c01020d0c1a040f0605040c170a02060f090d0f1101 69
    0x1c48054000e588620907581445068184025130349401c00004005000340c80c007002503a400e900345001c1c0308101041d100f81c502017513981c0c55120801001c49696a100c292901038214255540c108101400340015540001481c0b003590848500d80135001c003034072015202c00c0c00325100350204100b00c50301407041040c040c0740c13035000c02c2280c505500e421310701c10700041003c1d0250350006050300410190008a400080e449002035100e04803840100f00290002d1504a0003035281001051540c5050300d45e0000701c0b000480c02542c00030003500d0480f00101100001c545c0035a9500e410980b002040c000c1ca0046c00881c001081c06000301000207140c1ba0380900104280401c0c442d038800072800031504495003039401100d0301c0b1a03450368035000c0703a0f40944d814080c0185280005200c00c100a09220008075101800d15004c1e10040c00d49058480340848002507000700108a82029060764501600200400401c0040c00d403101d601c401c40c258254001c100c40900d1302000c40303003041da08641e901d00080c03 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 949215719 1250 949214469 949214509
    0x5160e0a080319110109080a111b0103020a0c02090c0a090608221505040605060909010608100c03061203110d080c0d1a060d0e100504020603040b0903040b0a0e 70
    0x1440c10110729142d00c01c81c504480e00d54070b48210308210074010210001c240b44110002c01c10894941802015500201803482c00503110005100740c0c0030002034900b19540003421414540d0303a91400550083d403107004c054084c4140c0c2002400540d80f86090b140c40b49200d2210300c0d564902d43c03500145161180e800410a01203104180940016a895a41d110034411201c4000500712070420140032041c084015000303500303050810040100607081f90340510700039150145103880c1c2c00001402c1c2d80340f0340220f29440e0700888890001401903003041842c0d50031400e000a186840302055070319645414400c0e004100802607440c521181001901c2440b551881c1400841c1445504521a8407403201d40c8c0171000e0701c41c0146d101c40104c00d00c0f640894480105141d944070f055080ca48007901c034601100c0c1c55070041741141d409100090040b91b116507802001c2500d1640c4940d104c50b1202c4c00544a00c03c2d610003070201045030405000200003640458803180d41c10107561042005e05036204035030490034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 949216969 1250 949215719 949215739
    0x90105130c1a04170d020f0607141e0703260609060405180303090d080a06030206120417120f070e031b010c02060f0301030201090f24021005160e 64
    0x704040041410540c1e010081d249030400c1c5004a48100d40a143c10070400f0b012001d01ca402d0215000400e5a0030761003540940344c0c0b00c5040c0007020380328881255001c01084091400800c10100100200880a404080c001d83c4000c2600c0c00320894100c0038040300030900c81450000f0a2040c034054200745114555110014a00344020801c41100508030601440e00c800214040c003500c1760460b41010f60020849071245040c003416640c0300140000070703001c1021280442c0e40007900f4011081520b4000d05010b1400440d010003422540004006a40001411601c401c203400e00310b00074071b015036035149200300609190180c2030010311301410100505c45807007070710304160720085008071038030104880e419600307191000142c455021280c4003d40c000c0340001c1d07455010044001650503a4001e03039441c0000c40d26607090b800100d40030300952525030090002e5025038040155088010319580c41610200d203903030a000c409441d82a0344102d000030a05008500080d8004800000500c007110a1171316 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 949218219 1250 949216969 949216973
    0x40212041b0803130308071e0c170304080a020f060f040902030f01272007120e0d0c210818040f020708191b050607030518030307030b04060b1209010513 67
    0x100c0452480000e141c40c0c0302080e520305000b12034000501501c02c48504c54029110b5227001203241c4000d004212100c181b0008611108000005032130954460310b0050005460b00d8080003621503440c2e19071907004504101703604103c8005800f4000071b00c000307000540c903401c11000c3c5d03c2007024141c00c031180c1700101c556000c0f80c00d05014044001c03000b22aa0010740c428144141c0ca0741904800e41d6400910f0001503d0010081d0380620015000c0c4150b540000d950f5413101040711070020b00401a02c0003903030350010302504080211003032840340f803c14030030015820355650902030340011200c0e0000e010311414941060078180610028142c61003021031a00c1103660b1086007500510062003c548841d50207894018000d05ea44002d10500c0c004034401101c4616010341d60381d0085901000007800d00d00801d8203458100318100301d22440034042d42c215030320340074210000d11104088551150321000001030381c00700036000b406003100498030344203145010350455003940e001030202d8540c60050b00001f00 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 949219469 1250 949218219 949218247
    0x1308210a210e120c060907030b07050d0b040f020d052802070807140607020106050303040302010816090519031e111e090106031d1218040212041b0803 66
    0x2920441480405841100241041c030041484003420705251181c06948600c2e140d003c8042c0580380030350002c40320b05607900118587c031500c59120040a80d41d121b00415600c81c064030151900d80e03030103040012000b44160001d4142c44841103001e9070150300044403040c04c00b00f405601d5114098040302d403460301e0411800c040a400000d1031803940b82e80441d0007020803034118115407030550482c1504d9541d8079040d04071621041c0a54007240550300c0c10b24000f031203050100c250780c00c40340c0507108c01c061590740000080201c0c00d00c1501e2000c00880c141e0100742541d6840c502e4205d541c020045009840c01d5181c0303500c0034010440015450a4001d5000e40003c49031458040350020a03035101ea00840e09038850002c920301d840b00c407a84002154004108160306910a410304260b07450b00d1b1500c00f082c0000d480d164070078032102c0d0300010b07030410500c10101010582c80030308000180005180640e44a400410040280c404855184480d040c48018072007920541d4060403640c030140d031410701c82c030b04c0c240 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 949220719 1250 949219469 949219487
    0x1804140705060307051305090a14070903020f040c18060809160807171e0c04060b0a1205100503240705040803031f0504050a0b01030e07030c1206021308210a 69
    0x10070045e000031200d03902d2002c0380c441c02c01404044c010713a4541c00c0156203400a860b0200c8070f101860302400000b110140f1a04034402100e402400c2e088414000c4010302000c1d12030b88819030140b01031034482d40649092a4010002442c040c0c0da0141c0c90b0605414040c00c000c200500104040c1c000700007407160480110780c000413a1031000f540d05985c030003400300a0a0035404548040e50010f000b80f070240c00c8402042c195404501140c00b00105030b00c4070700c2040140108681d40000a00380f42c0b07401c401c400c003580595006110940b9002300d880d603400001c3c2c9081007040d80f41050710318655003e04e20340281581141c014800341081402c2c00d080100c1503589000040024a01e81ea01c0300119400b0100c800740c010240c440900140031500c1e0111200300030b03102c0001d945001078544403608400e4500402c514003620351080480da100361601d0030490820303a00035020381f2900d5007002050030348140003100c1d000515801e0007414103401e145c0c02480b450400094400d10718201042218039145c0d105440d0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 949221969 1250 949220719 949220731
    0x21905090a150b0a0f022a040504030201061208120601020703030f050d1509230105030c040f02221d280605190f050d0f12020a0218041407050603 64
    0x500c150b44403800c00400c40d46075000c0301e03010f40001003801416511111004101900da0221200100756140e190481900f25403014410304032101191041c1ca400e41005400034041c0c0700100d0041c0e01d540340d0510690600750100c0d8011f50001c0e1907112102c0150307826501c54401d0000d4240310b840c58030301410f0010f1101d10141000000100031b100b00045a0041c01c00740e194009103800551220000320040010130f1400103020000348841c0701c01d51001c9034040c1a40d00240151901a06030010b00028001810010341e070190240009000019460030b402c0007810100c01002281e49012051010110b008412100115425081040303030a00000c051001000d07801d03080301c41c1c040f11070311030000f4070300e940005502420b04000c10301c84e90701601000c0280c1c2c4940d001d114130f00380e4803000c21210200c0079100a0541811000e0040420510880c1440c1a40d09005903425903110f640044c14000358900e00c102c2c44e00b1800c041c0024444440180404012810700501c001d9013010700041c030901004102c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 949223219 1250 949221969 949221971
    0x1020315090406090804090c1b02060417010f1a010f02010504020105161e08030619050a03060209130213140f010818030d05090304060f1b02040f1b020a021905090a 72
    0x40342c1040142e0744500301560f00902c0441d1160740302d210304009840404a03003800240c0364041c00820000181ea4841d0081d40202030fa4907092034101e4240c4410203056190310155645d049a201da5034013030040c2c40445640f039207035840d0400d0b808009002c0114058100045a00d44420400140d030050304271f5030341c0c07042031030a81c040030100d2600c0e8017031030b8982c011421107906004800c3c1c1084400350183d4091101141c40d0b0292001d5004480d5904401d4410350383c3c000b0520308200007140c4164010312041c400501600d1a403a0111049000e03640a802d100c03d4403628104200003c1c8680103215a0103002241c2c0315400581c5580000c1c240340000c0c0150205403008400b20301c08010410443d240b00003000c80511032450310080d12a100e810900c0750a010031640741c0c1c13125406110700720050300c10140440c11012508103809110040101d8035400d801e0b581c1d900001004010205d016040d080030320342c010268518140705004485002408065580810341030600c895030781da28070554003143c0d10308 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 949224469 1250 949223219 949223221
    0x60c02161d0c270114090901031b0b13080601140d032019120c030917070e0408030a0b04061206020913141b0a140a0c0804060c060e0102031509 63
    0x1640038034600c5003102600c5010f249201800e0200e004000070800801c0907212034840c400100040840d82c4a040490f544c881c00c03840060001600d200e12803600800250304000000c1d840e000004121740c4440340107081c017880000308002c4000c082180501404183c100320b10702a0362800841c0940b134069100506000e40901e400d00c2044080c0303804010f8581c0e10049480021860072101c01d8050b081409030741050b990900f1900040c01011000545035140e90341401140c60b1148041404220082c030500f140980303a40080d420003410866406203000d2441d183c0e503820114104412116000c00640c0944c0c00c000c42002964181c10359242d025800803005a650781140700060070325030507000f1221101f483c0c100c058030180040009240310f015070f42841501c03202d80400f080c026008828a0000150b5500c040035a1010041c010307080302140e604041005a1140c9c0e11980c5c140c00030f410000010341c0c00d100c0321043c08030a01a650742040300c44001c5156052007403280301030b24412444280513090200c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 949225719 1250 949224469 949224481
    0x7020105091305011509050612040f0302070315063809010e04090b09060f04020d03120f060803030916030506070806030f0303040f02040e01150e0a0f09060c02161d 72
    0x10107402500b501c01c1d40100007541e1203812182060b6248088103001a0003540045400d0070401e040b03402c9644004085034036590b86984801b00500340302011000c5010300c0303a00000140300b40780b10f0601c0010b01000498000c2c18031440c900000c210280300036010b4544803d600070034036800301500c183c1603580603103540c07000c41e0401620442100385125030070900d440818014080101c80d014007038000b9070b06585444e1210004842001000c1d00c020350f000440d03408540029008407014149401034100c00b18039111991084012250750364003101c06500000100110140148001d4410301c6035a8140b1484a041d91201d40d40c60354010124020b1110480c04035405950420035404000052000c8982d20f01d041d19020301d210806003412401503042c01803e40320a00c060141070400c0788090050b1841e1441c0103440b2944e07807406802d00d44410f07a0f882d0480c01061141c0540304e0b019001e0080850110800c1030000d103400e0301010342d01d100d01640c84c010702408a40e42000303552800c240c060496651520 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 949226969 1250 949225719 949225729
    0x21008090a020a0305060f010b070c14011103030907030309050102010c0806090a060510090e1b03070807030e07120b010812030705070c050907080f01091109240c0307060f09080702010509 82
    0x8901c040d6001001d05000000c000c0e000909603c601d852151540301c81c0d0341c40850990034002c0030740c005c2c0b07100105034040c8009030482e11400300420051500c408130410700d5808504580c002e40e800d40c1c1c1c0750003100091040c0742c2c010005000804d0284000c2009000603000201403a05c00b0340781610600941000c6620300c007481c0c10a801510b0300a107001c5d2580e030307601c01c040c01b0003e03944180b10220f03010900255034044400c4d20300d000394030f2400f540c920390b6550345411102044000c0c5072000741540e8040032941700e40100b1611018003009105000b280e41103003801c1055040c164000146544008042c1c1c002d12074503801e807a0000041e06246807a8401b6180075a4620240c3d00441c0d00880d00700d081003400d9600c980f0b03c0380038202c00709110f840d0b82d896a140d40b059030806106881907100c00c110080181c02d0844440c581402c168009010319816208501c002d81e100c0b03568001964408100f00092002d24400d81003107a44e444410007241109544030046d0340a0500c1c0a8148900803c0d820580c0d02c3e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 949228219 1250 949226969 949226983
    0x12140d090311031e0d030c05040f051c0516140609030a03080c0d0f09031d03030319022a0609010c170a15080f120301142407062702100809 61
    0x121280000c0ca148801c1d802907417130640780c140782c0001c0d0070000380b140b03014080c1c01200e0a40365422042c200c60ba0602e0240000002d441401500795081030000c2da020400a018202100c000303a00c0b892040e9203441c0c45112001c0c0c4030820359200d5072041003500c689640020701070308a00c0c2c0c9404d04072450f039290600704150f8002c100d40c0e8850203007410310800500c005070f4811400301e846500d44d82000886860080d41c656025003030190540d04c200041035a4250340348400c015140a075801501e0090601d07103200010000841e51440c02c5607400c030300d1071009028400c00794040d1201008016201214400034054800c91082d0982c807114007021030203992031508103408050401401c100456558500242c1e00d01012845600a0044030000342840c02c81c1c1003160f04841455a00d020101c040904021044080d28841800c107110014181e1540078084050945c281c02104001040d0700c50912444401201d0181d09800c5002140c0c6600140c5c1e136018400c00115141c80d222409654a0700d00900d042d074 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 949229469 1250 949228219 949228243
    0x60c0303040308061305160e0a081911060c030f0310030218010e090c0f15040e0f01030c1502030d0509120d09051504050d030b01170112140d09031103 66
    0x108000a0603006440103001e00c1c0300362a54130548514003d00001c03640c056490b0900c1c240c7c49030300140541d20aa100e401e21500c02800f810040d555400600e181100c14041a400c4d85008001c0c0b07800c0c4140d036072041e60302d8541a61414035000002080507140e22850950351105040403020030400090700b45010b0141d40d018240303001010031203621403c4500c0c01d01c2414000c000c20030001d001c410007c41c508050303540252140d0404c682c00e07000c0180380e1041241d08000d0304001d01000030130f00b85006825000c0c0017220444005135046042c0300000c0c465640140703000302400500d8a03442c42e0b001040340d2255900701c0740010300c0e864286840e03013812120381601d280420702013802d518090b102d40c042c142d018030031021900008000d85444880d0507085401414642148801d103900901039080170149100500d02520410340c01144a0700f086801e81210f184181850000010000701d40c0f065000503003074500a010508800000070205542e03404000d0103220100c18202250300c4c2000f20030032040f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 949230719 1250 949229469 949229473
    0xf070606030f03200115120204110f0a26060d14030a030c0905030d05120414060712181112010b03010e150f011206020c03091f0e150304020f060c 64
    0x190709400d004000240c44100380e030325102004013400c0882d038148a03c590004c0104225202c0c02d2900b0110014070810740801e98006403199251140b8003040300091a24201141d401610f031a9103941c02401000010444c03125284485c00c440a40c80c1100c10f1164046800c4914a000c08418a85812108451210f11041c3c0c40080386d1841d5481c0c142d007000c424005256503040300c0540e40e008065841500e02241d10200e6000c010800d09843d48110300d5604c64004d000c8070254000b4806184e2410b00110740f400001a00c1120310004100319001c0d00c43c1d0b50711890a000001c0c0f209840718040c958441c8045849810401c1e00c200303000c5420f4010043c42c54009008002104500790413030b4070307248400c2a800c4c10240d9040020200030041000c036060b204000311501f0200000c4d83e801c4001c2d07022450607021444248101c1e80e40f0f81d680c1103004803030110b4060003113060045003c007608482d2981d0545202e00d9031440f0303210030002c2c0706003500d034425011502c42082213044004a2224811003004c40414 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 949231969 1250 949230719 949230743
    0x140c03010602060c18031f1802090f2a07020103050f090d110f01180210050c0a0609061113030c08070501051e1b010b011b1a042316060e060f07060603 66
    0x40000310447e1501d49680600034040d42602e090403415582d03020f1b5000390701c9070024000c00e02c0900f103080d05d60750001c21800603612445442403070f1311942038094184201c4e82d41c00200c200455a15000d5a80c00880e031541ca11500e003082d640043c0c548094810510801c4060030000724024410031100e110401d500300200141903506190102042018500b40d00900742d80b1003051005100b541242c41e04101134004c3d003105034560f5101d00c0601355009095400f162121000468039030303588010081d004800c41210251859450980903205566004007034513008403000b0409a42c00c00304950380707031600740003004810402c0d4180a09500580c4504680c094604039041c103002c41c1540200c10b000d9090300c0f000140c2d0b000c4043e140021840700c0300100f480b94107040c2214205a071200741d1b9005407080401c002520619103000118005016a10403a81c0c0105c2c809000030842e1245080501000e10701425101200b0001c580c0c0b9205400351860416400100c60701440400d9110b032014503448a80c280d00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 949233219 1250 949231969 949231993
    0x1110a0305181f050406020f030a050a14090316080d06030c0609050910030813080f0d0305010b0c1203090a0501111210180e030f0d140c03010602060c1803 68
    0xc1c442100d6880700c0e094034004002d00c07000c00103030b40003064411880b80c11041c098145404064203000d8011103181390203001d21006c0016036400307103220300c0350210001030529002848606850054003810000d040c0d084c1808010240030044499049141d462004030340e0643c5803118180c4030702c5403440e0f02c085c80c24a01004220014840b102168020307035500d444a0384980411000c170703400340e9402190007250b50301040080c668801820f184d4200030b41c00d00b0060354440280707080c01d1780c1603650407103604903025143d000d5406205007400342c0707011004141000b008562031687da180342d043c00e00801d40013100040035000e08101e031025295001c0020b00011a0007801012140c0041c200b20031030500c50800242c002403d14080400c0f900518040c0c40100c5d000030b1480c0c01081e11021550341ba010801c110145002c00600400b0880481400040c2d08400380003517a082e040c0c041c20340040c3c05000c00040003242d5001490540000305c41035104d565042c80e101d03e40b9842400c0c1c1d03005030140959446654 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 949234469 1250 949233219 949233221
    0x160c0f12020a06110a0618020a0e18010203061008100b0c0d14070c0308030a092109060c1101080705090916030506010306081b010309020d0c181a010e0301110a03 71
    0x141491081c1c0d50002c5440d111001943d0721124100380040d9988141c6000c3c000c03d5007500050104840303548102d2220041c3d802184045425030003070039983c0c070a00309000c3c40100c00c40003100c403120007000842c21420407500180c2656000826942003080305800b063b101d080044000c0300600043d034159984080d0f0101130380d120008001a1800719032001c80036101e800f4600c00310f82007d0761007800c810141d42140d03202d418030b4201805103c1c0c4241d481d100c80000030903242800041586140000006100d03881000b01480541d400c0701e020045c7c0c84280400182c000322410b5400b01c02400c00ca585903880c0c0c0c83c1290140580c002c0301d80d1101581c07007884a01c1d40380ba404120507201c5a80d003070125039541c100540030784d02e807480340c20b050340d02604e102203903507040c021400307580c0105240100d5503107620380006121101302601540e0111400504115441c0031400e111080030b203001080c004075416491001250307844001c118180300f41c003544132041d07580a50011750861424111241c5070204600018 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 949235719 1250 949234469 949234499
    0x3070807230a0303021c12020c03040e0105060f1207120c0507050d08070207060311160b07020607180e0a09120c030908122203052a04060b160c0f 64
    0x7491200304854100d405041103603500040e00d070103030000e002020740d100140d8108449040b40f8030030020b0040c012016100940000c103c07a10040005648030703810300403102d00240e81a4400c0d0f03c00c020402c1039068841c00d003c15619189c510815502c100d50314520242c0e10200a200100e03003681ca4500003104140c5c020f130140040c41d00032000c44800010303109060300d0904050b100407002d40d000201c07c000c00c0f0300ca50000d0103524602074900d410104c841160454100004108440c070b029400d0800810766410403049a001400780f40008134400c90903c07001100d50300f8004d20b08200c1d00b034800144005404c1d0050b080c0c4a6018505c0280e20386404401000e4040540c0200e0001d90b8009000400101c0018800d0992035148609480d0824210402d403d10170300e103160042d0644c00002c000701054090081080d07d5a004070b0742030302400304e00304200c54403038062025441a49845002e100c40702c0000b040e1294148200e044a440300e801e4103166400401c070b54003940b07099100d09800300710716200c20b01c00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 949236969 1250 949235719 949235759
    0x1080c210303040b16080f1807080609010c02121809092103091005160807120504080406080121080f0f04091b0203180928050402101b1103070807 64
    0x101c0c5d203046800700c044801c164107840700d002174444034002c1500c5c10000c40030104a00080002c44244aa0741d0280d141450022a0b41c107a003a5920340c0c00704101501441010b000b8905048085d280940c000c0d2085144500b41e4030190154451100081541a04200c9101d140480601004134444440d40303110a90b4002c80f24070806018030340c1c003181c0070039080c081c0600548181c0500003124240e10b1085907500d0300108254104040402c0300342d411040c5e407254030301480c09041d070150780b2400c081c030140c0464010381c04001005001e04030000c861028100c8000d800390b00c1070849540d04940948800346019803411803502150004000509030b401350300400407071540e504005540c00c41c41c50240c0e240c0c0207641a01e0303406030355505070714050310703090350400d03808404120307102030300003110072180e03c9046000340b40782c480c40d9948184029032510404145942c1d010f071500414110030000040142d07070740240001c00f04611003216842a5400303110075005000c168085441302a80c03103c005070014815280 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 949238219 1250 949236969 949236991
    0x504090507211a01020d0c0803040302030f0a03051b0c030a030e010e010218030601060e030a0b071701060e03060a0629070f051b0d170a02070e070210050f01080c210303040b 76
    0x403c0701c0c03035002040600c00f8100a4a031484804940c0d25007030b40c903900080c0201d0071800104141030f95101608050301000b890b0b550001080c2ca40f581c003214086210580c1480705000030310421114103400000c4812a203d64540403481541d803141403405010040311404507540080b41041d02d00400d25012024041c00b00c0c00c80d0116640c4a03c2949c6580c1038021040e01030308007500b20030200e6032082140c3d03000f064901d0005003070101c0001e0f580494034203800110000c0e0865111181d0762504000301d0340c001d0700100007084110702d05550507848a1220020445005850b140e01b1100c11020303040d01c000d50f820030f00c8001115290f00e0300c1038035141340c51091184c0780303070380815500707e403d02c189501c00d01c0391b00415100c10068150004161600510000c0c030451043c6a00421201d00301e002007402803082d50018034182a01c444145d0039100d000340850a8259880010000c4d0342c400141500c6008059800d4610880940301c806403414848805800310f110000502c41080182400c0034801d0003800301b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 949239469 1250 949238219 949238261
    0x60c0f0d030c0e0d0c0e041a101d060f01030905030c0115062d140d09050c27010608060109091406011e080a2d0207020307080706050409050721 63
    0x1c02088080044c005015014948400c2c085112000165504079014482c41e0103002d82c2d80444102c0c0c40e03400c0f104211140801c17041005160030030500c09820b00400030764030202e441c000010480f003681400c0c2c010b04050301d420030441809000c0c0200d650405002000f40100748003a00c69503542449441114005011000660f260a00c900c1c0d030b001d1884003001d174101e035860544c1812180703215107a480c0e505a0310104000300300f88142d88202208540302c1c00262100e03004034001c00054184a86a07545291140241701d420182d00b40350035419a10281403145191700e80c0401250392482d181c11082556103007001002c201c027400308a5500c240341c02d070381d0f00824030b031080b5240702c400d450502c03040003244000300855039041594003c1020607061030380e0442e4060b59502c4022960b00a0201013004580c0000c03640300b541000d2140030043d20144005000c6140303819030041880c403403031240c0a2903c0c0ea030ba002c100e040784541250001d40c3d1042c0700460124241e1a01c50006104412400004440101c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 949240719 1250 949239469 949239497
    0x9170705160605121f031406090d0825030f0e0106140d0206030a0c021203280903020c0906030c0612060f090f010b030c12011d0106020705150c0f0a14010506090411060c0f0d030c 78
    0x4105507208100c010003089041204245031460cc1071030b0201c0505041d2240740c0600c3e204080c0c4240c801115210300042446031409008500d62009819018018850040000d003d61100400c883e04020358410002d18510440001c80c108001001780005280c0c001050107660550140115105281040d0000c080c20764510350104442e1140340080168208002082131441d010034000d0b030000c00070307090380c1ca42c0c4c04200004089912241404000b0003482c010b000041c104000382c020b00c0001601c000b0080c0c01c2051401403d00c030b051054881100f800000941c1803d5208140c507807201c5940101210f07561581e500c00c1190644614403941041100000221140300041c110308445028200f12898501402e20180c2c951007456550020b02c02c411780c84480106c1041440c8580e40036040c600f1038046142901803d607203000d031080d441111200300740000300300d4458000b030b07041c1c0088404d2540d42418440d00303400c0051401c030110081c0a5025402440c9405400c10300021885036907455000382e0003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 949241969 1250 949240719 949240727
    0xb040303090b1606050702070b19090807030f082506020d05160905120307053f04210203010507260906060409170705160605121f031406090d 62
    0x10300002c820f00301c01400e2103804600143e0010350414a00d10540796078a03200e81030500240c0c40040a14004268202d1121025030303c030000c14094042000580140c0346541c48041060794001c0024183d10720010340c07400c01d42801202c1009218032140d80019064003420524000e4000c925501989800c14001441d200352004400050700c0c19901c54010060902d014417201124a0050600501c03042052202003081000704000c420780b416108040d990601381001d0307890040054150f0144680500003009014900a40b0103a40c1d0f107032525581c88442d0740300031080c0660040302139019440c160074001078591281e03507000801915101c2c8003103502c60907910300c41c03480c04441c1040d25820190102d90f241c0b419410550381c9074050541d055001840102c40c4520ba4030001b000c81d500e41c0310051541d04611380f0350841008013074074200103050107002c0d07180c0c1c0b101110042214083c9101e15000007800f00101d8034080103103800c8108158008203168505540722001c0d1002000e41c410300e40c0914076288a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 949243219 1250 949241969 949241977
    0x3081b12071209021804110a030512030c04050d03021506032103062e02061e0613020408010204090f060801020403030507060506030a0b0708180c031f150b040303090b 73
    0xc0c2540d016801d07070724030800301c0307140c81c15042c601001038030341d010400982d44110b0f610909001c0002c001005080c180303440107040002031281c44c0548861745c0100085800410344c6507047c8011585030341c0c2eaa0b224402600c0341e1085170030803580300c002e102c0d810f82455400580c03108003032a068240b03140b5440f0780b0101507413101806400b0002d011a14181c2c111845140007071034011101030203601d010400070700980c0001b02d112540c10040740d10500611290744d41040015004400c0c0c2c07106040714444211014411200203060900591500305036881c800400c0c5d040b9002459401c00864890703842c0c900c5440988101414a000795041c82e00220301200113100300c4080720f45c1626060315100160303072a40041e20b0001d101680c580940811000821412600d85108255a030745462940c60500d049001c510b00d50142c50140d640000b407018400e44000801c0d0494820b900390f500c0c55070301544800340150144c003641d44005084031400240c0c1340d0900c0b0184c01503d110b0344408000c151250015030b16030103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 949244469 1250 949243219 949243237
    0xf130f0f110a0b0415230c100b180423030c100e03041203140909010648052a09010801090206092b110102010e0c060a030c1b03081b 58
    0x4507102d00300c0200d034051041c05007151001002400001740c840f52802c4550441880f5190a800c180d4a076600308d001449034400fa0079040714440c1400300301c01488056140001d10081c4160206e40c4e0884641180541074429145440704490740c1b949000780d015154400c25002004043c1880030210403090b011041c0c0342039074000d640c07410091000352801c480865104501c00010901009648030b251030300c012403070203040e003612940300c220601040610384030703640f2800280704c17a640d030800012140100030b4002528000c0070b2001c0d00c4c03c03083c2082e03404c101c0070501c00e02c0403030307000191010101000c0340e1a20b000c0340e00b01c4800340660b81c0e400c009402e0b83e14101000f58071040401802410345060558a040d81d500300003c554904500c115044808155407010341e40c105074481429155a4240200440481503134041c03c41c030a10440480c0181c080c17405028140340e00d881c9650361040c42040d581c5081507034076414422100c0780d4100601600030030b4810402010301c00403294045010481115100340d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 949245719 1250 949244469 949244489
    0x7020a0906062318061603020303012d03171213052803182102031c05070f240204090c0503130222020711030d03050f130f0f110a0b04 59
    0x4c0c1c550300d012451400e070f0303069000c1018003401d070241480c0510141480d00c130b42c004594030750500c0840c039902028050204920305080c100c0c0d61900700d0103581c00048079402000100d48801c8811003540c0c50048808960b1310144a008001c48182401d4a018403075015900740c0700d06101c9030303442c00f642e40b10f065100320110800d104c2000000340304049105600c980d071902000100d88800aa02004110307012001c0e00481c840300708001d5150511a18205d902800381c050307020746282902400c40d000d210030146c603055400700d040e014400990410f0310300c3d0072110114451901d250342c000000f500140188511103141518101e03e030390003032085074024150300c0d030205220303110ba50070000302c0300b04003044248901090154032224107090000e48440c0b4811800010000c400005140c03404545030081010582000184004044a000d02a0b00180ea80342c2c0441e902842c1d09000000800000c001000820894034820600c401503540540701e06d011941002c01c5561105071705518021402224403071 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 949246969 1250 949245719 949245727
    0xc0e06060a020601061404031a06040b010f09090e071a0304050631060b0405010f09050610081602011116020f100801090e120c071806081002090607020a09060623 71
    0x4a801208902c1481b082c500d5258901a129900d0b000f02001c00790440e01011014003e000f45d0345050300130100c05e01800c0c81c2500141c074070440010140030381da1052110542c0d8900409180c1801403111102920b803141e14000490f66850042c40150710403181079405028003c003056180c1418042d84075940092001e01e041554071210385000325031841030440d28259241004030160303e503800b80c580202414107010268601d0006031a003586c2c002031506205600781c0c100340010a402200c280d421025041c6084400c002c0503106034010400d0001e1a0340c990804100c100303040b40408030002049109445403c0c9a4140c4011b1000c528040200035001ca0b10f980010301042600340d20000303041008070304840002c0064001d1001d2544400c19000c00c0e0f4100b00e8091081360710240e0142c48a0010141c1080554036082c21151070b80d0b00c9100740c801c400d0b00015007158030354030f107005d40700240d400810540a056a81d414a0b000781041d1084034082030b0200c85040191070315034558810000000406490 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 949248219 1250 949246969 949246979
    0xf050105040320030f0d20210409021617030708041e0b010b0307030501050a0f03020118090e010903020c010e0105070b040c03050a080a0318080a14160c0e06060a020601 74
    0x240030103c1c500480e490700c0030b038120442650b08000c411840045000a402d100d249100000d0500900302042840c0c01881c00070010303070000004585401540c01605050001240042e20036030744165401039034814000b1401003a40c403c01e0803030101b014800c006000d00c3d000f019040440301d000c11124100800c0c1080d0000c2d002c6180e98410042c8440740d407016072a6031520303036100c4110440c00c3e000814010004410400210741520800d40500400c6940035241407400440c0034a04605000007410011a41305801c101c1030b890140002070071640d039050050081c5424214003c040901090340103100d80748003c0d20310350044540c51034280d4103a4a10385000c425884045500001500c1142c0140d8400c1d0000042401880341e090b0300b47c42058402e9485010400040a5410035115000b00da0b8040e0120000214400c04480344420030f414031081c00201020096072a01500c02d010715040550b0f000c400c10410841c0c0428169441d4400140c202c0e206e00003030002d035005513250080541e010b8001440 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 949249469 1250 949248219 949248233
    0x3050a0b090309030a03030b1206040f031412090a020102010c14040b1c020703020601031b121401060b0d0609060911091e03032b05040b130311010903020a0209010f0501050403 77
    0x98060142800c8902d40340703a03e000f282c6010801c0c00d0640000f035541e4060300080c80c2280d14480c1c1c3d1111000141294205901c80d10340400d84104010140051041400c010800800a6486c0524595944482c0d8a03001c00c0c45500c40d410300c04124015480c111001c0300703950103195444400c0070070f001e01d54181414000d80940c994070107124001038050708811030000f0415030004200345846030707003d0400fa516501c1d007a02100d41710700c980c0c0484803c10405000010113042c41c421160b810480911840e18000e00380c1c0c2c01000b26401503040385200158001501b9110303080141100c010290401c8025900d114900460744007014100f401901001400d50324903080450b1010040c0b5907180320f2403001c0b500c002a207182c1c081900800d40c22a00a0407001201e0318054551440c01580800d003e541f829030380b103402240e0000e000314808181c1070145014144101440c1600b6645400200103503001e03810081d540f20100c000891141c1c6403040045100508052030f0000c403801a10b400e81454191f039501d01e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 949250719 1250 949249469 949249471
    0xf1112030a0c020a120908061509070302090d320313120510050f0a1d0705041d16080d020f0601030609060212070908161409042301020a0e090103050a0b 67
    0x40210b20850300704001044450343e84810a407600d4a03440c1c101490850945e00b0040020189c0b000f8007602e4002c03080d01d03181c42e101d4a6009003140390050366040444001810404030f81c41c064060030380c0c40e0aa0444c01442c18000014a0741c10484021408482030000d94030f101e1b8051180c62029007240821103c0a8050120035041c42441622150b241c2c40050703004503042101c407602003902c12014080a07150911030306170781c0c4a8001c0f090400c008034111040c1d440106105160049036200684961850003580b41a05c100d000c030b00360340c50045002542e10400045000e101401d00402ca0028140e41c00050342242254212000d040c0aa1940e01e610000342a481025200e0725001c01c8a40140002848140e1003410a6160742c508281842c8409103010381c90f50568080551003e000d1081c0c540c88402c1410805080320306800543e100d14103170f075070340500c80d41030003644204540d19980b100040d00584440d034029582c7d0090346018500b009400e40081c40003500d1b40c2c000144c104085031040c0406c0b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 949251969 1250 949250719 949250741
    0x80f0610082e060812070308011a3a150b09131e02040815010605031504020702060702030303131a040308070c0219090915060b0318010902040c0f1112030a 68
    0xb2031030740e1100881d04000c46440c00c2c0b105c980c00004d05004060700904814054000036002000c002c59019412605100e4402d4a20210f4150b0030031004d050035181c00c059a0000108440d4007180c074250404018000061541a001c880e094000c60154501020303240d0300728009001076181848181d0000040007e5510719040d400200302c000c50a024a0000348020081d26000b03050a07161a070364400c0d0700c00103800035020041d0420a0100e6440703c0075080e029400e08031001681e8241c0c910001e0810b01c91000025003500004c42008075860010b03240303a0800b0b0003826a2150982c040c000b401c0f02c42c170125002404146444080381e001c512424014407894406454164010700c02014981d000c0c82507407103580c040d500c0f2000034003000410051007060881144c41441110700b001d45004903404000c0c22a0540100148000f468010942040c4490303034010b0000c0080003561140144414007d145580c0800c1c245c0b0075036000c000d40040d281d0303071a0302c0c42c0c43c20301c3c10350f2226460308010344142040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 949253219 1250 949251969 949251971
    0x4080720031f051006020c0418020a030f17090a140303070f0c060905030f0606010e0109090c0206010626150102160b09030d080106081b04080f0610082e 67
    0x80c41410307101084124018415124807804050b481e44486066501c014440d44103003507011003c03c0034540008000003003140c100c501003003081c0c001c0c01c0b40e440c02c2c2502c940a035100400d00e40001c1404018991401c2e1540140248451390411917803001ca14031075900d0290304900c20010800c420100740d074480c0051140101601e2824146482e407200c2581d00220075a0315071136001c0108119500300500400034101a80a0b213445440300c9061919084002c1071541071100ba0f22101059078800c9201c6009400342801c204000c0601d40c1000b5aa00320034015800801d0600703809141800c1101c85020811155408580403075a035079220001006240001d6415846003a0003001010a0302804c0c4000e00307a204000d43d06c1d0f02c0c3ca84105031806604200b6042403200c1c140040c0100307940302d0f01055001084181604070f4580f40d410707090701d620407a4002c5c03c03103004401100040d080c01062044c01121325902c04e0103001d0300c2d1103650743c9412020b50a40c0c100b5803016000032040c140d41004e100c1d40000c0c160 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 949254469 1250 949253219 949253273
    0xa12110403080703120608070b0d051f030318050406080618030c0304030f02030705061e030408072009090c0105310602030c301b120408070509040807 66
    0x19600942e41c100060440103c0c0754241044925440b521031100140440002040828030700403000c8410b1090410860315180c44e030b40004c0c0c0c50309160041c03400704c06a007141040c41d1541c80c1802002d0b1903496540c0c008240d070034580003c0e64a000d0180e07509541c080e0010705240e4440380c0c01028402019026100c0358001400700844032001480500010b41c0541e40403c50305509104042c105045038001611400c0c041c801501c20751600c0310707161008242084216501d03106c60501184134000c010b401004d02080a504080c60144520040c500440c00d032a6050982c03500d000d0789861701d20b18411180041c0052002d05040350b00070141c1c02c211015406254414178042c0300c2c003221707641160080720241c0e02c00224590940801c00040002200200b81c503031703400f60903900d0a040100358901609101d0b2000c121111480401090403a070034894900321390040d001c078a40c10004c1d40042c85142200d00500300300090b83d05100d10f502d131003640d100081da441c2c04003569a100529059007011084070240d04 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 949255719 1250 949254469 949254473
    0x40215030a020901090b0f2a0601140f0d15020a030f1a10080906010608041a090705030c1203030f040503071a0a0606020a0c06120f1803080601050a12110403 69
    0x140045014080d810030143e6104803903800504084000d0b40074000030b100410140c07410185800690700004003810030202c0b0005401706a00c12030000543c120304502584000042100250035801b035101e8080d82d012181d07600320b004000d40d250030102c0141c010214042641c11420b4258000c02c2c40c00c81500700080c0d80800f002d0000112042c440446446c5022888005050324141c4030040840032986018600e0345441c001440d11540d0612901c001e200c40180400e00300081c0350002c0031081c066010940c0186030010029641311454031a040c068040c900403859039007011b2901d10340da480c10304011031a50326000410494000001c10950b8140014004503001407107020380da80c091464000000810b040c0344150b0001ca40440d03002c9015507100032410000112441000c408540840c10104181e822130f680b501d0103007403800206100c140c500401075100801603000c0150740d50190307a40740050398403100151101d2280d8407000021840b80811130300013442c950050000002c168400701e05041c1e482d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 949256969 1250 949255719 949255759
    0xf140f181f060305070f030c03030302090d05030a08010f0f060905120a140123011d0606371106011a0d2909062b0b2503020406050a0302030402 63
    0x204070510011626090200107000041080c00c01608040c40d850b52801c0c9181d94415021440b40700040915401141240700b03030792641c584100c01038004098079030b140340c1c5020090a881090003841003c4440c20400b01c2ea00040c0c410202c1655041d031a1a5940c2d4101810002c110910340f030040d5640c4542024000000d15285881e01201104000455522410f201021500a0302da0a24600d80b2200004210031803400d0200e0240d08107086081200307840303000100c0c0d102d10441c1c103010420341141c954113410b0080801c601a00000d241010344003400b103241d00300c0e810fa8000c415851217601000c01408814a07180383d05881c03401255240307142c6030007a542001a191851030714090300b212503035110112074021800000900d400c071703041e10785441c0c0b4000040100000c20072017100d100708220140550000c0760313101441c09801c080c50780c1b100e18101454130b0180f02910614400301540c01409606107001e40291801c0c1c40c2c50303890745400c200660600320f0017504000e10a0b64010b0075001c60361480c6030b1b6 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 949258219 1250 949256969 949257013
    0x2070302010c020d050f0313140a2105160504050a140601050f0c010f060302010e0f06180406030c080f0f0a0308070f05091302090a14060409020c030d0f0f140f18 71
    0x7844000e1034031819640d00402c9086216480300280205a0288009e1030381c5043c03940d41500d42111156a010440042c01b201400b41e215005000d41b127802035120038256416413000440b1402ca40500003952441d2040701130350601c4c240b4244194001c00130076030350740c05500588494054800b0443c1004a0b80210b9402d45a20f0140b403403020ba680c5009006559100039202018401a0360b501d010701c2d2030300080b4001d84156411310030350242c0d803194031142d43e903160071000055811000d0754028a0f100d41a41d901c803048900603125522840c941804001c102041e8016441d4050703d521500382e4a00c042038407451040504c0104100c2c080202c04107035590703d440058001c0c0103150042c0c44030400d400f03001c5940d43d5030300301c94006503d00ca520b84485e039544048600707032141c00002507240c40480003042d1031402544010030360740e4100b15204140489030b86c000d90728003441c0c0009022810503c0e4bc1501e00071804e44104000120101c00600c1d18003100603051111201e120465100002012541102080b = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 949259469 1250 949258219 949258243
    0x1220070f03021c0b1603020702060f030703060e090d0c0204090609050a0b070504081906090215030901230a2f1c0c0c150b0603150907080702070302010c020d05 70
    0x424403041c010350070302141c0403c030044880c0125150b4101d41d00c43d55403c0701d00500322036540b01c000b0160503456201e50165044d00750701500ca40d4988100026808064004541c0000000e00d015030002d00e06510301d44071801801d8103000f0b40303404418a4411a0085880340082c9d07040364403025402c00081a5214451850340580c0282c0b6000c0a01e10b04000085d81c0586024200081880b0034071148070046566001e040c0700001801d550000c134507202018141d4070201950050794a840b060110b0445001140b26001e014006c020714001101c01744400802c0f08031600c0000c0303003400026a859000e6000c0c440c1201c219030580d64441490303480e0140d0300095040480584800f00e60440c40c000b030a107503081e03031480c108800d00020950074001041204402c0003d49803030707040c402007465181107501c801342c0c07100003400305035503460240705d206440c2075894680382c01213601c3c2c80002c840c0c500c168412802148560301400107503207141c0044500c140c00c01002d0b41e000240b90030020000e07000704000c2013a28 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 949260719 1250 949259469 949259489
    0xd030302070201030c1d09090a1a070909140612070323100606080408070c0807030c080609011437050106021e0a06020c03161103100603122007 63
    0x207038580300040a5507651600102070000340d030040103c138001d9610001640a054400082680d14207441c1481c207284c0b100b028103540046002c1046e540b21542c0c4103441108907448200380030755107109980849603100a12400f101801d00030501603c1c14040700f00e0f00020620403640c42c2c94480e01d034149100309403c02040b1649000080c00644241802001044240c000381000103600d01301c4040c00326040200000d00c04800094942c01b042918803502010702002c80440c3c0303603d17459140550280700d290142e041a4421a00040e01511050003000109405030207105095200c0b010380c90710f205c91506000d0424412480803840038050052103100440c8840c00100d000d516103d4040c1c10b00b002005a10341d2400b85205d00c201043c80020f800601c0d039404040142e407a1203509005003140550381c0d8060401b00810344c0c4800780000c2a14030045100100d0548203990802000f000407a10076210080400d114040f80c032403143d00800d06805400645158040311540c02c3d06180d051040b80d4004070058 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 949261969 1250 949260719 949260727
    0x10140a050a0e09010e1b0708030411010c05070803040e0919030f09032f0117060d1112010911040c09090b0414090619090506150102070f060908210d020304110d030302 73
    0x203400040000241b02c3c907000505032501440d5129510341d444000d1000d041c0f00300380d60f100103603644141e188800700340e0014140c130403094940c50280e8881e4414440c01c0c0800b03600101080ba000000300d01d001c000700010240610300511680d01b0b440700800c10b841d44082c80403c100c000702294242c0a210184803a0441d501c9441540c89140c0072070050500b8228104400204280385140030b100030b8580043d4203e070a4031020301d0600e0884120868a40480c1d0060300140704030703040a0301500a005118881e24001c0980e582e0101480300f141ca82980000020700b040601704666003007640200046940600003191504158009101402c01910080e50f203520002c104441c88606a0081850340c1c41c01d4001d01411010b501c4041d40c586000e800110125030031031010b4480c2c1c2c02000040d0042c40070f01d4038031002550b109806010703901d9903c00e00f80280184500001c81e00320b2a840b801c000e44000e1140d500386040d100040d402500001d01c21a000c181002004440e5a5250003503581940b01c0e035405aa1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 949263219 1250 949261969 949261981
    0x91a04050a0602010e0a14030f12090105070e0a06050c070e04051c020d0e060c010b04050a09020321220801060b1801090e01090c05190e10140a050a0e09010e 69
    0x41218503440b440440e450942c000746101000f0403a10141034100350036244142000a0090441c842c08030514043c440026103551080b080c0e10419108411a4008102e10b580e00c041c1540d1489500303201c0744d404030180070103108240c010070217810184041003c40d01c4080d01c4540e00c88036160b0070380381551258803104082420f0700104045c0340c00c0380e81c070f40702030800800b030307500090f080407018103410f84194404544200401c000b54009001c41d90028424051814010311140040180f110107038041d00444401608415052660700c042190785c055030b5283c000410404400010307601c087e8480a5100301c00068200c10900500015040326120641c0e501c01082d200920407556240250500110100402042e01800802411100d608078007040d905070b008800c5500b8420310180d0018180c00030005420254406280c64058906648a540d0440311110a990184020300b894046503410841115040c1c0300d007000e4241d04c002410808071400034040041c0c0400b40903000311400c401c95400f086a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 949264469 1250 949263219 949263229
    0x70f030b03250f0b04030f05100c0908010e060105090612120a03050a0e0109030c02060d06090603060204150813030f0c02030a0521040b160c12240c0206040210091a0405 74
    0x4010f010804014090b0b40c40c110840e0f107540500e1001902d40d07a415a0f01400303004080c054042c0c1003904000400c18a03603c400d020740107152038003031107900b0b6190030409900702d000018024161030004003c5400c4d41c0c0d4600030440207a460400e01341107805400c1c0005c0d020340001019150381489070702d020400c2e01d011203213002111340064035800300781c5c1091200f0020030f81241010420a4041d240035a9410310341c0100e10160500d540002078a61821000005003c00c56010740b007a03c80740d007401081d020502c9400c0b0b41900d81075691800c00c0e200f4a0120000a0141481d80da0b04065400c0007104004550006410101c161070700f96569048685043d8001c00043c1041248401c0c0295581c1018249078a00041e0300400c1401c00320880c01c4014202840394492408c1b00801ca19803e0b8520200706e45050491900f0b4001c440903158400282e0440004c0c841c09420602074181e0300400260780d0b241c081000c124030f9492400188007032940041504881406810b011103040303818280e4407460503003400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 949265719 1250 949264469 949264543
    0xe040b01030615080907270606082509031218060906020706110f01090c03051203010b031501030f0f090c05060f030c0a110d03090201030b0414070f030b03 68
    0x581090300e00201842000c074801c0185030f001c00185005074607580c40c40d114625100060f00300398055050303081400c110f400a02c100703030089039400005010b21a95840c0550b4180c800344c40007000c0f045c42e45060900c501e51054000e94001507886c10442c0f8035980c1c1c0300d0b40200750682d1450400510045918020301c01c8541c5804002d081a1030090a024500400292078030064002c210402188031540008500b00304420903010000300d008101d0a0202e02d0140c10143c0740348000c40351400b490400000002c4008180c030b040301c007503448551441e91101203110344801c81d510524141907840345005045070b02441501203080c0320b0000003c43c503541d410004151021907008610400041205002c0364443c10f01b501d40203e0507142c006e40b90189042d05540149611040054901c501504602c1c1964140c0100808074002c1e00c08000070b0810b01c0600c02601e13000b14100c100401e208010070340b45031280c61000260750551a00040e85250032000908248460581072500c520b81034440031080550302c009 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 949266969 1250 949265719 949265741
    0x6060e07141b010603050d2601180b040f1a0310090c050103110c060901140a0212040b1e0112110108010f180603081c0b03010b060f0304051c0e04 64
    0x4001a114a8101919038072840c2c2041600008103001400380070800d40084001d50303403107801da409000d44024010081801a14501c080103811303a004054001803910703240c1a15600400200d4541800807641e000d030910301d07651a0032543d00c0c44900048066440750079072a036092401016889501820103151800d842da2070315800d49071107034070310000714441150800c0b90000e003808117021112420b96601130048035034403074840c080c0101704111460190310541403054240810b010907140e800c2d29a08130b001b1300c125914042c00c50001b140c081a011803003242d0080d41c00010490b01807541182803510300d8280c1c000014552105800e004201e1051001420300f135003840d107019035614261a400c8401210301c507152400f0740300c00c0b901c80d10342c4264000b00c014641256076296244050141100e10140d4007100c2d40301c41d4540b5400c100103140c10300560100b990003c140a00704004030f040303013009610180c003c80780761041800c45507020751116000340820b4541d4071740481e0f0302c3d0484107020a4482005003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 949268219 1250 949266969 949266977
    0x30702070312050a12052a19050307170c0c01060b0904060e09100203040807140f06011e0b090a08010e03070c090507050d090309031e200913050a08030406060e07 71
    0x1402840345c0c4181c4400c201ca940000100b0b00d6100c2d00703070b940c141501c1c0720fa00c1c0f42d0010240301c0104500e0328102c01020102403040203860044200b80003120310b8041990082c0000b05002c41076520702d490300e0f03501601b28403245002440c00c0790405200d800c5522960200500080200d65540b507440c00f485610010042603850352243e04d01600c080e82c80e10401041c06072010f501001040900195400392115a0f90102d04040c02c01613448a003a43d480700b0640c1180300707106c3c0100201d0601d1000350a17003212030b02401000c801d40d0502c80c8400c4a6044803007629048074070300700000703003004003400b91514060015001d566035000606004003c0c041740d0300030a2240c1e04103000c2c486802d600c84105e8040b40d011000c0020450411b05d011616520241d001a16030304800c0c421091142c02c80000f0400c1a100d45c0c4031125102e032810300550085100580e2991000f01440001d0500340c1d02d0300c0c0541e1040c45502a0303110385213580d540c1e030160b800a40381540c50680c0c0780814814400d6a000030b41e049100d82c20 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 949269469 1250 949268219 949268227
    0x1e0c07170a1a09070b04030b010302030c010c12110f1506011803020609100c0c08060702280b0613020a090311030f0a110d08030a14010e1e07050c0303070207031205 72
    0xe6200581c2102c0e146522450410400038a02400c04c0c08040301810320841d0b0242d0b600d40d81c0c104151000020b010681c400e0094004108507507000303254034965140e110a0074010055098400d945620300304108071128001d0300f880030521002400003440000700070b25a010ba50a2640006100d11841e00d040000b41207802800c0c0056910101540c200c0700d422518113003400c1c00108200c0d1081d501d1035009045a020483c0420881c0010851621440c03003982100e84075598201c41d807000214038040c003104c044100031050301092403c0d00460380403001420320118041d0040740c0404a03445049c001c80026880350084c02004004241d580410b41d084000b441c1481c0d01050031a15105003450081c2082c2e0303e01c0b0384034042d458207550b41f10701a4000303008607140c0c81c10b0143c0d2405050708030021565001c4202c00805c1c44102c8000302805500d12500c2d11000c0c44000b41951490100613299000344079050115940c0c000d400c01c0154400e0160354041c1220310314600d421071800702c0c080007840601000740 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 949270719 1250 949269469 949269473
    0x61c050915010303120b04183e040b2209110414071d060c010204050906060304050d080403030615022d032a070e100e040b0604021e0c07170a 62
    0x40201c241c05030980c00100002d1041c0001d0040c6023158140c2140513002034100c06000040c40a503866241001c0390440611190328804101c600200409810a94144404116003442d50008180f002c0117000c48820240b40203420b452000003481010035503131942102c004100c00c000c540c660010007550305001d14a0036200300c0b8510390009210208002400c0b41c800c0c010500c410101e0781c00300000d081d96035681003000c0316030f000c0d500500805e4011030406012603e1f5003025011030f88125000005007d0414800c0c004880003000940300340e00b055198400070a240c80c00c003c8500f400307081e527002403800200d01d540e030042c400225078800103548106840c039010710001000311800ca0020000c0c001c80c6a08030aa40d125640710054032018500c101308012522407450039516026040740600f8203c0780360703111000d44220070215001446031314201e01050840c03c00b038000d0607500f4041c8030603040300440c841d6480895000030103144030692001c4c004100305030900d0404151490700f0130161000fa2156 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 949271969 1250 949270719 949270727
    0x170f0d1701140d080307090611030a020a0b040f02040606030c1e02120703030213080a031d010207050103020d09020301050903210f070c15060b120108010227061c050915010303 77
    0x14814803841d034405641c00d4025a030f80070034003150140d00034840354590a100b200280300030000c2c02224003043d0542181c40304020008140c6000031119030040c10320404580c0c60411850020b402101d612240b04c41410042c2c0d42c0c0e001d610f003c1d01c1ca507900003ca4240c80300c070090002c0c0700201c2565a40c1202010503220550110303c0e030700e466904c0003002d95a5001441c00318002d209080710644032606440d03000c5001280460800e803c64007a0703032003185013081141c948183c01680ba003003a015a100d500108403d5000b41c01402801d80102000200d031182c2e600443d00b96042117a03204810b81000401c0024607010200191003050390094407004c070320300800900c00d01000500380c003052099408508040007000040c0754151501c0c61410701c841941c0392a2803203580c01111080491090310780010a04020502c25109807500b1a1109251000b4410300c8402c450791042c40150866420031848100002c00d01c074035900e8400421001482c0d1412019940c1407458052840480b10041c400402c08684c1c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 949273219 1250 949271969 949271971
    0x6061302090d08030c0d0626060c040905070c02061218030702150c01020c2b031b110715170606070210030b0a030f1b060207050622170f0d17 62
    0x40f00300816580d8031011588402400742c030702c1110760f031800e20340d0101b43e0140000224000c41000c2182c1e400c45102401200d444804c03c548074050007000780410815120250071068100c1d82c1810b00c0761762015650080303002a4008038990309404001414030000415075540d0342c02c800f190f80050f5003403004907400540e000c0308501e10003840e800c1c00300308190440000c0d4100c13485000090116600c00761291069203808410759240414400075084040c9401d0003400740c903485190941c1d40e070038005034000c026180c0140920300380000d44140309001c109103070006000456401c49850300c2c0e0700707040000b0045882201c014107032405650103100070001a1180b0601c1c0010030b034281400301d455007429010172a11845076002a060b041c05101c8075050200030341040f2159240e00340c80c00030003900d0304c0c01642d03528041e216207038000e0410400c0e030115440001545a80e01d40b60800c0719820f036550040d00140d040c43c81280400c82d005400411410003007042041129003050900175600607113040d088000900c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 949274469 1250 949273219 949273223
    0x605190201020408070e0c0c071d130c05090a0f0f0609060503012f0f0304081c0b030709020a0311040816090b1309050109020405101a130303050a0207030f0506061302090d 75
    0x1100c2c0380481c010141f44805da516000d10f0034111505565a00036030720b10385440010b429052540c1d0700c0498070558442040301c10294001e01e0442d00e0390b2070072090120b0908001c04100110b507a0310f07055003000c0c001c0d00501c041a418032074040b40003420016030808032a07503540440c0c420b03850408088030041000101c401030035003020000c440e00c0e6004401c00020300c40d82a212318042000806c01040106440182201c01039801d4854a1010900c0c60202140d4070040125415882140c04000c4801c0c0c540003802e6134400e6140200b1100c4000c00d00e5505a00103400102d01e03a04a4402c40d8050f0040c52106001803040c0f09080c060561014041968010050482c1c0452900e03000c0600c00d2007025000170046960141040005207420702040313082c002c047c050b4001516103480c00300c2c5204040c4040c0d6800964240100c05204d10b103039425038559000040c0c61056010f512400400f082c0106000c81e0340501030300190034a490a401003001c82c03500400c0b811845481400660700036100d11556152240d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 949275719 1250 949274469 949274489
    0xc090424121707020d0822090b0102060c0c010204050d2108071202090f03030d0f0e0a110409050c090103060e06250c03230705010605090c190504050a060519020102040807 75
    0x207082c0c004219185e090b49030103003000c50001412440c032000700512400803c04000043d078400c0d00c071112141907450250781030380141d2054010400007003450004001d5440940c0005140585c0c880c0481c528000c0c0c0001500c0c0c8191071007085251028511b643c85906c00726180c65141c6140c118400b03894505500c090a00d10b0360b000c101e001458403610416501c3c090000d08582e1151600d48030100980010185512540e05000420390140350004210860b0b6511410310700414000d4024071006260483d020f1b51a44113000c0c403030805440d0028118060f5018610100f640d04040901c145006005090f440c40e00c540303014070003c8140d0001301041448201d2406901601d0b549c20216116102001da007291051004605402034250b1001880c0162140000344007450340d030301c00c00600203011500c215510b68208040364506401896410152025041c400d0929454102165040d04e03680c02410103e1030004d004101902e03603074100e800050031031009500c2d1034108194242c40c0d80d02e61084000f15 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 949276969 1250 949275719 949275727
    0x30e04060f0b0c0114070e19030b0c030405010b1906120605040c0c0b010f0b0f0307020114040803460b03150f010902210c0904241217 59
    0x958558009a00a021810240e07500a49503030910300203600000d28200a9031a242c40684110a07040c107140c03180b0700985465001c68002e2003404808100c0c00c41c181080322001c8030100000c0d441000d00c5010b000e00080080d2a4901880e201d401c41c0c15640d0b45c1403248000f00a082040d0700c8030f81a50090b988030f86020340c107222145880201402d26504419402810031100c0300e0010ba00c00e40102c00140240200703001c0d80d0740d0340004014000b5a01800d131b085002007124041c0102c10500454000c0b19500c000030382c49000c14000c40d91850305403401c03100c9200000501000140700031001c94070f51006e0348480d01c18542c296201c00b0041c1020030320b07480740d52144000a03103011541e00842d0040006004d4603c1c0b6090700120300d8400c4c8003145c4c108e1141d00c4035400030400f0755140c401d03a078501600380346c81c40e500d1030111102d0b2807a120040114203422010442c4100f9170b1a207004a07295000d44242da00c030180004440007140b06e003680c100c90310382c0816408610124030380d8048005000580213407030f039031 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 949278219 1250 949276969 949276997
    0xe010e0f040f03111f060608010e0106050c0a0b01090b0f010e031509070513020301060f0c050d05032205070f060f05120603070b03010308031005040606020c010807180f091407020a03 80
    0x1003840c41ca900b0200b140202c1640000d10710384080464103202e4084010003540b92a601f0a41c1c2e065028094000215040001805400c2c0200300400014034180221140d00380719540c1c0b0080c1d483c003600700c0d001c1c0300e403204043c50260400315440103010009007440c1d00070034413843c086a52000303411000340b41410300c0740c0071a030141410700c02c141c003601001d0100001244c54541c0750010398000e1162a00141e41075680a43c206d214425840030b46a004002c0d08031b0040a21044038243c00c0a01400e441e82200a454641104c0442441c2440b501c01c40183c035844d89400c0030038040c04a2940100140b104001d03030303420080e9104045500143d40300110040688800010030b150000b903401c08521807400000100912549a02462080c03546080c540c40030307501c03a018882600e07801c1c0301d040050b03802642c46842c20340c0183c5290341c0c0005680303070595628000030070b560350341410740d8021351980c080381d4420b018400050240c0b42c071403246c90100e811607061243c0c0082d501d0601001c040c0400c0004080a20 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 949279469 1250 949278219 949278227
    0x12050316080c010906050402130b06040303080c040e0115032d020c010902030610080c0d030f050307120609151e05060c0c04090b07170f01090905120a05040e010e0f040f03 75
    0x1c0c840c0c0300b181c020007050303402d49040030041805481c160300c101440c0350510b4030b83d802402003402c900c0d4040d11580c2054074540d000d40da0300e10040c04803420713603500b0312001c12000a0490982d00800000a0480000c840d00d0806412500001000d88000c1030b04118400c1e40682c4100c10000f5403110318006981d1a01e000c1264018442c1c01d000952501604007880115403103409003005862000098648100ea400f04028854080a0004020444c0400348114842c041d1001c0c546c0440541042c404081943c02d04104039216500007040040c0e50b0120754804596000c070401c00b504030380038403141c0b0007003841e604e0311111000c3c452248079910005590707030041c0e4180000b0054900280082c00800707a02e1030020b101d8030080f5000400115414141820f0600c1c0f001d469000e07411410603180307542d00309502d0710050600c1c4003040e101481030003001001e62a9080040003510a9562a140c82c1d908091340d01c6070a400680c84103550340060024813200d00084240540c0296008000c1410300b030107403506403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 949280575 1106 949279469 949279477
    0x10e07061115010e162d1706060706090309031407150e0f1504050a0f170a0308130204111305010336020105041505131205031608 57
    0x1080781d012031400c1d40306520300b40b91081580044d04a94000724100c007920742c6d034220a00703c2201a665201602c015040d28214103160307030f41007060001d241c41c0a444800303032949076a2104101018000c05410000b903601245c03488408011294141c1c4650312445980001001c03c2c01005602e03114105400740c5010090040c11031860200c1130090303401801c1140e00b0440030410010459030b4821141c1030090440060401ca080d0928100021003500d00d03881110aa000750700f8a400260014081c5510001466048842e170020b400044c02030a080304c08480ca0703800000314021403804c400b101c1001d40e00c2c203890a000c8102083c110141c0340e24400304100541050615a550580b40d40751054502401494600d04040d264103442c90412020f441c01d40200c0d030005201407007140480c1880004047c000c090403090541a00c840f80c4038420841d00900c41e0328028400b81c20030078603009503 = true := by decide +kernel

theorem cover : BRFrame.Cov 949100719 949280575 := by
  have h0 := BRFrame.cov_init 949100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 949100719 ≤ n) (h2 : n < 949280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
