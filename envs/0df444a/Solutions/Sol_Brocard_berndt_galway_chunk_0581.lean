-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0581
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:34:06.689552+00:00
-- url     : https://prove2.me/submissions/70c33037-c98d-42ce-8751-7b310ca9613e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 104316546 ≤ n < 104496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 104317796 1250 104316546 104316559
    0x501080705071e05010c0215011502060105240f09031e07260106060c02011101050f07031109030d110c010c11011815050918241201050901050a0606090303080f06 71
    0x100f640e180b50944800c0316030200113800809418290302103e00c120b0340940f007481403131000d007030113490025600d1505101d4248a01d2103061407044001070140800403140d41800681da9605400e070300016684d00c6500e12034000d2155605040705070445203030104001140c40050300141d844c01c0561540402890f42040760034201d02c0100c1c1d00315038240b058400500e441c0d254002c01c40c7c194000507001c0041d20700446001d904001c20030051218180311154000f1460500051208040400018900901301e00c0ea806118240603880051741058032900f0304050001101c100c170010b4001110a081c24680040c0300c42d0502e6030b0441d040d070080b007440c06c80c0d022242d03168182a03502d41516412031882d01c414000b0410000f600040c0d03042411155510007880001d110540c05e000c008003019000c5076060740021465928001003d58034600ea1050402001000744a242090020386000342026200d1071022464110009a0f882c001c00c00d0b0400c07a41c041d1540440d5a5807003e900350080e0005041a80c00030 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 104319046 1250 104317796 104317853
    0x4051506030115033e090703140f06090c040e01030b04110a03080d0515060304170d02040902030108100b060d050907050d0302030c12091c0c0b0c0d09050108070507 72
    0x48814412400840c00b030340100320503c0c2c50590300c0c0c2551500c04c1c0480c0d03a65103450341840d40d00c590320126030b111180a4558401960b5416403c400401d00e900c80d80c03051a0424003840000e8620701b00d028060b40043316001019165419070f11007601c110700c81c50b201c00d660800100003140841d18011b52140c082d0602400100340c6100044601d101c41c0c000b16681700000c40c1013403282c05d11384622680807100a0070a40d2620000000030058000244000e04001c20b03000d10654007110712003555a03c0d01a5502903490700c1d01c1e1562003010f50000d0048165901c1041c0d02164410958080d0480d050307400b0700040e00c1c0c0503410101c0c101034000241108028803a8000000f141e0300c03464020032440d03006c0c0d405181c8542440c4241418527081c9d40403c0c0c220841440b02c1840c035a180b00c0c40d0035080d142c009a04840b60818a00081501410707408641081d00c0480c054405e02c80204045034803003419030f210501507448000541e00706d401134603004001201400148001040184855120350340c0345070f02c80249 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 104320296 1250 104319046 104319071
    0x20f0301030c03030206060105130e0901090b0709060210020a1b050c0d030305040b0601030903080a0903091203170709030b0c0d0923010b030a020303220f0807030b0f040515060301 79
    0x5500a900482c0c40344500d000070018194140030403a00090300f403070254034241c90070620400c51400c034001c40110100317410100b40e01e050250b11040031958010904200303881c102d58041c005074000e200e0100580140c0d00030000c00040c0303100304d54046005494810f5008540f00e0001d50701601c0c020304485a2003a80d111801507524038240c40301591003585c000c9020328061a02444100d0302600070381c181070410303044200090b0000e003190351084094000003515a00e504040300c10250541c0824107070496800c0c004241a800004030090b44080c2e5000c141c16141c00304120b4000f4054032001d040c01c40c9500206000c04095030040800d0113202070003095140203a204d0140c45c0041580c4409104240c101d480c41c1c0080a0041000500b01280a0009a201600801c0d120704c604d0301e40b5900105031f80d040070b1161140d43d481401400d202544900c0d0140c88a403083d65444017400181c4501c240340f000100700e1565241303a10310a60740800640054039030105401c21f05000034021a038503540b01c211810b40c1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 104321546 1250 104320296 104320327
    0x103090b220503041202120c0306040611040915030605010e070203030a0f110a030b0901091e090c1206020403170c0a030809032101090506030c0117090705181008030a090303030f02 79
    0x1a10602c0750305e4488011502c100700484a0f10038403080d00e600030003004003032031790045059030f07000e0340000010030440b00c1540407451511441c4c0246000074500001255101c42e180922000d4a120303550404c81c80e41c03a00c0249481000480300b40c070069208000044a800791500011100e20685001143c80421400301008640150800000203076540d6440e0103e850540342181c01458000760400000c1c544500c3c0c0d00c10076422405195105032240ca950301040520142e0a0041c080c07480101d100c48103510b00180603502610003a40d1009150030311400c490100b074200e400001c1940010501c03420281e4068500c00c1006084031420b000074001c80f407134030146418292044064140c044425810044035000f00c0c0c2c00030b00003038000d601c40880c210140c0d801440c080c5e81100310f8140c1c0c0f1900c3e514900020b00d00318207030f0403590300415488102500001e00b9a420390040ca030714100f99101c0d40e103d03911103070780340540760b6103100140e940a403c2001ca4002c4d0b00c03c0ca424011248058581002192541c20 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 104322796 1250 104321546 104321549
    0x312020106030804171c0f030203060a050607051b190315110408010f0e0102130506030a06091107030201140c0d180f1b0b0403150c05360103090b22050304 68
    0x4c40c0c42c01700a02c210500028400c45185418082a00d680c40010707041c0140701164041e1060141903001021541c55561058514001c100003810303607603611060b1402a445110306603404c110260f10034880b149034540705a4042002c100da01d815180d0134556154140301c10621201c43d0a2650b41d59200c1840c0000c2c6001480941059400415200c0c06610b0100480b02d0300d410604680c0d00c1802958031020840203800103c900132100e0759100d441e980e00c1e41005180d41d50004002a14250800d41100c45e10009082024004e800810410b43d106211810344041228080100300c4c0030800200c01c40c200d5440010003100e048105160f4100c0d941d2020039101c01c491083c4e400c0c104100a042da4020641021005401d080748818180391031031380c500c40c0304025010200b80e41603d0b610070188081c03094042d076104c400c030401c03488201041d1100383c50580b01a9804c01e40345116448649610354001d0050000c102d038812a20b40b01270351142403261141c06031112104068480842000c080b030f030104098070 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 104324046 1250 104322796 104322809
    0xd0218090114210703020f030f0a06060906210201051608030f01141c06020304033b010309080d0902060405090f01050f1c0b0406060f030503031902130312020106030804 74
    0x205458001080f07040e40b8115814201d4201030740110550b0b20000c10a03004483d130648101ea0415144000641001508a000601c030302c46c0b104108103000943e0000400c072015003c04018842c0c6600c1e007850104a01041d808079103816403a1080154440c10081894440300078115021507a142d5400c807040c0e01c196009803903644503200500c0400004011035500c13140486100c442546a0b130f040000b43c405058010301100d45c0800003409250240152060086c2582ca0399801e0380a0700c1103030205044602000310040360b000c1e01581e4154040d1180504c00382d004545203003010b040040c207001801c01c0040483e0440014440000e0030780303d074401c3c680038600310404081e06604040078040d403040d400c640e0605c210b1030010303030354030460080d11004a65504010381074210b94660038900090000c5034010080031084480000030f011010003e14002c280342e0000041c02842d0400081c140d009407182d0b00e002025a10041001130500401d021101c100d500022076101e50b251030707680322508568001d2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 104325296 1250 104324046 104324069
    0x1a1e15150c0105010909151a0603011508010e130204150302060a09031e0f030f030e1006210803060603090f01050a0915140109090201091205011d030307050d02180901 73
    0x39000950a00403c0d000d408403c40400c40c03490b0948510504000d0f86000d0204141d45110707280d1b40e122091940c15688a002c0d007883c0d030382e5030f6500150040c14007510740540000d50300030011840b040013130f8010780112044001000c01703030229020000100100180d071111314580140000042c0c541c1c0000d0030300d078001d94946c0c402072481d6007051000c941e90700030075500e0346119545030000240b5007842025201d800d45424840c070803c00c0400e500411703445002030550f214103e0259641d2420743c0164007514408200b00e400c8100b08146a4a03485540078010103001003400003e5050415502a40e44281c1d140219000b0f041c60700121401c450301a07502040054440740108244a22906159400080b50b1010801c50007099498620100c042c002c444e1501d40b83c07148403007075a00c00d842030405000c86a680c08118100d030300c1c000e4000c000301400244440ca00f078913443c4c0c9400001c0207592048906856480c500704403004418020750150011250500c00d500c10001030b134031307007500003400307498042c107003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 104326546 1250 104325296 104325307
    0x172406070218010f080d020a03032c07080706140a030203041a04050303010306050c030405070501270e1605120c07060603050a030e01021006060c020904031e0c1a1e1515 74
    0x1140b408130007604540c000e07a010944089542d40c0c00910b04100980610380012008101d149204880c40c08a441c4a025600e11401c480c149102160700c0c802c075102d070411510742d01d594042c00c3c0d50400c982c0d800880c644030306001e1802076600039001168040d01c41e94040318100051842e01c4141801664180c4172640b000c4014402c1109500c281038122010170085819450503564165031465a8040c0604100d103942000c0c807500c1c81044c140c21900309035070f0031a007015241d420103004440304907a0454000c0007034030f02039109401501103c85141c0e0400c1b01700305030ba940b806007030803e83c450780c000c0710656030307036800000800d800740000c0d807109201c2c0d545d04407884000000286400942c41d01802c25924000d02040f68681144c0306009181d410354106071a503480f41030a40d013004500050b0314025101940c00e6410551240d0043e078440d2040b0080d03003460200500a910071082110400420380d440d0490945511110030070075401000164480001003080c004103c0d1500c100c10030603401c90001c00c1 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 104327796 1250 104326546 104326559
    0x18190f020109051c0204090305090319050c0603010503210f0f03060910080a060b041d060702160620070b0c070914040317100305070f030317240607021801 68
    0x202c4a0007043c0c1202c40b004444501600c0900304003084000070300c100e41d90032403441010700500a03100382400040a03030f181b154020f40000034900501e0700c102c4040c06441401416407030400c0a5a05031000030380200444d1a079150003000c142d411281003a6008014404460115442c1c002420f000000d400810307140c0c24003e052040703120001e4401000c0d03c1e520303070061106201c00140707074500310707040341010480500010104005012500d408141e134602048401345103080001c2c0ea80c00b690341c50382110302441d138810504401401c2c0f401503100089507110011020a00c152100a070141e403001566240e42c1e540f002031140d54009603014195802103501003288103128490364181980c0d80903030000500c0c0ca070b030300186100004010008551000f42c0404c07040c07281ca4401d5800355911600b169081900c6020000b0702a8031352104800041074210302e50000e200007034141d80a0360350441710b0720701c041c2c8583c525060300c401640300d15085142405a903003d40d54681c8280e04400e10301ca01030845504000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 104329046 1250 104327796 104327807
    0x71b060507050c0405070f0c060906140108060106140720030109110109050406050604060309030c0c1d060303070f0201080a020d0f05090c030f0a03030f0603020405180105010f060818190f0201 84
    0x900d4941310303030710341810010344540005c1545c07000b03452480e0150000f0805c3ca13007040108000e91020b03004034500720310500c41800034641241a50501d0f4111030650381d89180441d00c0648040381a0b0510006000120000328544d1401160740d00c06042c4c1010700203240e001c00d00310b03000940144c4904d40c00200011903035030030a924074041c10003510207010260414010818900ca1841a6820990b030f8203c0ca205061143e100d8401c010740c006003800f4025503401050f0303e00c5170303c04a054904410f103070124403c2c1c900042118003c603071124800c0d081c1800380e001547c015400a04040c0e180745c0802900c14410300c1c500c030b1048074a004020000d080d05281c0c00c1c892901007106195030095121a139201d140d10760005601403829030501c0c01003040b21010b1f0044016003000c0e40000e4102d070402c414000380003030000321000300b0200c05008000580c0c1e80c10780c402551000344901c1001c21b60003c0070603120012001840505204074003100c00103882041c00042c08039400b0401d075030016120601800b190f0740030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 104330296 1250 104329046 104329063
    0xc05030d020a120513180902120102030f1806040b0901020c030a0207030506060a030305040b0708041502010209090c04050109170c10090f060201050105210a05060a0b0906030f0a0206071b06050705 86
    0x3c4c901141000d0611000300d4400f8013502820300c0c0c0380060914200010006c4c0c01508403580d024150312080d03420314008a02135001607541900d8400d03480700245400000f0b100c1c1655624a01e0000c01807500c490300c80198021016100b070903a55002c100700840b1003002c1004141c0c80c0d0030b0b54010300189196007007150400340054403031361064080c1d600c1000881d50203020f4405807240a1011581d4010903d4443d519100b80d600020906100d5161301d1708998042d805495a03840988081d04c43d0b40e0b90014401c03107071003240682808180050000d00481c001c0304503460200401d10106d908040c984000101030702450510070001844c1e9080c2071282682042495005284600003132290b541014000b81140007944495044824229020110807008000000303440b6000000c0d60050704000d180b190140c101c3d034500c2d9008040d650041000d60038000340410071507000e20050034041c2c00325420003065500217002912131070319668003020301c0c001340d503864002440903444983e607030f031003d14149041c0a841e = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 104331546 1250 104330296 104330333
    0x7050303030c04060f3b0d080f070f0c0e0612010501150e01030f0509010506032b08060303070b16080f04020a170115080a030801050d1106070c05030d020a 68
    0xc1c824048054040800e0303030195410303800c002c540011080821500c6c82c6100d4400d041c1c44a080e114000c0c1903000403070b0313440001c00f00c0e155420030714600f0003840140c2c0c502e240003c2aa8008100c1e004115141c80003030400e09100c0c044250741c0c01001d03255030050750303c2078002e4220107d01106100c0d0601e0904d0680598041d0070000b80310561411900d1408580210500030a10440b2020f0103030681c0700340d100c11007440036a5020442c50a000780f01e0fa000b48011580e4900900c0780d02141c0710b1a00c41081000c0c4061400c00d42d141c2e542448200880c2d9050000d460150540300600c0000000b8904c022414421020000d1881510303080c803000600808001e0051600009040203100c00f6884001840b410303a40c144043c128038110010403240140500010110042c80c134441c04146980b0104070704c088503000c1d6492102e1644c855082081c0900139000c001c00000c0030741d05d40300080c2031800c00390111500500013aa52182ea81000ca810240c02c02070f0000160002003100d82048a4442c02c950200035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 104332796 1250 104331546 104331553
    0xc020706140d0c0c08030a0510050a0f09150305070308090418020603070c030905030109051f0b09071b0215070c08060106020a0303180515010e0f04080a0804030309170c070503 77
    0x1104518840d02c11645041c8030507894a950080041c05401c0d05408554000b003150b6580c54100c0c040344c0145416a503400f02615410b000081d246400341d0b040c000e40f41c000c14400c0380c442c54486000e000300703014403446908041030000000811070030300902000b1801415015581d406160400c4120b4400654070350040e0402d100002c05a00c503001641d902014601780f96070030b030700c10303042c07d94048019500413a8950708005092040180114038420040c411061041d10686d02e045d0302016a01403003203a40d0058907140020341d0042c0b05203030113080313041c0012243c2007200903a004120b0640601000103801000000c41004005804d01e000340141002c0018003410750411500030340b0351013000301c007400309502c4000205501c000011400c842550001c210b0740041e00c125003404481401740b040741100044500090300e540042819140b260b64808045403404d12070010680340c1e4440580142c04241e5140328a4002034680c1c0c40f03a6000c040001c4119444401d0041d030a0318104194001d14042e40 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 104334046 1250 104332796 104332817
    0x115090302011b0c2d06020a0807080409020d0605031603050d11070b1908010602010501030b0412020f06150a09060e01030f0203101e110c0d080a1d010c020706 70
    0x661010a01040d2642440c203440004404020091079034902100030f0300d400b00710742001403030800995007460074030422414041c554074220301d60781d0500c010b4420400983c10030444100003540d030300028001c072440340b0034460410b600d55070400200e8011a6581d44030a070703a01003d10007443c0810003601046800038800748007070305681d9016141d60300c102060090000421102078075000500c0050081c000c86496113860b0036000c10070412415041c0d10000201d0104000031130000d01c10301038a41640d03046900034060303490302e0f075904281c0412078205004601a211424484d418280503890280b070f52480a030f8064142c21f410450036940c4c5600121905240c09003c000c41c140c0300c0e03409411260070500d991155201d03400030a0600d000ca561a1011600e84200060b80d058000d00480e18160501010804101d803001d961556110355080e01240da0b118141b00401248602c154070340c4000c41100c041071003182c2110000400c28040d01410640e510303103400100f00f40d8108840e030014a05441c0c4440100e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 104335296 1250 104334046 104334089
    0xc0503011a0108101e140303160b0c0c06070206011701020a020709020f07020d03031e09030c020907140c0703060e210904110403080306011101050c090103090f02030d020708010501 79
    0x40048000d042c015444006554a096454058000d100b03209072407141c0440c45240c40030003039440c06a42c1c40c1c6c50b1403005001c0c0d03a00b07000013903031201e0700c0ca80e964450000c031342d860740e8051140080a1004ca03440800645c0307000d5006002c160f00071282c2e5001460254100041540c0000d054101c2080c00d0b84103120b25000076a0015196085550010700141c0e141041800310031644214000a5003102441100303074200741e819400130030159071034941c640c814046445020192501800050002124070442c81c0140c504400b12a400a000342886c0200761251074a03014117812008007010300c0d070401c9004209000745401140303100301d8444007030240c03060242000c00720b20130f1030342c003952500e130010404480740e8403140d21228401e80307030b144450340703465580ca00a115588201c40b01c6000401c200300e4001004814088c16005248044015042101c51001140200074060b42a1380d00049118003101507101400b00c000350140c660701500e0399500700040710382903c206134020041c94a08000c0c0182c0c1c07 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 104336546 1250 104335296 104335331
    0xf090d09050105030613060803220303090504021309050a0209030c0d1707050c0406030f140a031d01030f0510060f0206060a0303030c0509031e0d1409010305040f1208040c050301 78
    0xa0795003d00b05680c070707900d649000c20300321041101e070300e0900b80c41c1200102e1311050001c003500098070011800301252490400002d81599507120040c080303021020284801e24042d00500f02490161410b4400c007540c0b4019402680c0b41525210585603000032107640d182424415028641d40c16184c88030404c40c0d59444200781d05105800410030b001c0415800200034003403011880e0104000c0051120381d031a4280302000c41c400c1a01101d01211200921607101000301d000566550591034200008401a4040d40010070407032a250400d5034030407050300e480d1418800c617405803281a074040070a505008020f0700c51803401d04c0300b40541d4040c2080040c6079450310101c5007580d070f02d0328020421000c1034400b510030b406524032540d418012180804080000d0301141229400c0c8030088800c403613080c070020340364400c2002d503c100c1ca00c01006450f009501a030859500907108250000083c2c42d10f0711045819542011944001040c0200f4001407190ba07080050161400f14006c01208121001d001035 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 104337796 1250 104336546 104336549
    0x1205040b040b06130606020d11010c020d03021b0a080d0518030a0e18070c030206060d02010522170102070b011401080f070e06040306140c0a0c1b1a030f090d09 70
    0x580ca0050b0005181e03515184500380000d024007005102d140d4070b883c000f94603090700d000c0107800900d180c1c0c0c2c280c0e01074405000c1c0790742c0800c45030058203042d00c511408070041d5204240620b2001030051101c3c0701c0d05008c0000c5102540210000358980103444142e0782170302c030050f00ca218446040454900089808812a080c0340c0e42d40c1007000050502102080032400480316480002c0f40b000c1c10000300c02d401c0003410854a200303500340e8240317039113080800c82d02c0c12110201900103901800540c580c0c101a58460100540021006a5042c1d40d003110325150650903449402c165004104c0c0d100b000900f010aa0143c0441c995090400d84a100001e048100c0101210412410b120100f241c1038010301070708402d420040c050300d40c1e6030f0b1a428248c1c040c2208080c2c40031049410f1380018440101c60040c0e4110158569542d0803680603034840e04846e890703c01c0e40d0000f01e003100500003100e000e240d40c07500010000d0350006031a417400951007000301c9002000780406800c5100f44060301d0790b110390802d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 104339046 1250 104337796 104337803
    0x31909030618080a0e180c030603010b1906050f0c0f07031106040501050304080711030616090e040302150910020a090602010c030b15071a040b04170403030f0302072109061205040b04 80
    0x10041c050300ca0001d0007000041d90740706c803003020180511216148200095205090075002440f5003540340003030141a14181d03072001105080c00000340003040c8510002c142c3e00b442000c00d1810f183d40d060b100d07030034801c114600913401c1c0c0c400c803c10030400c06000c00f10025800300300c828509107454a00040e01520001380010450100000c20008000082ca0075252911014044500ca803130002d1501c10000b090995010109403079810021703c0f56074410320300c4d22955141e405000400c0400b841c0c20901d20001d0541070041c0280c0b2484e0304002694405043c1c1a045641c90454161400c0c81c041e00b1144056680c03800c040c10460400200d4480c890003407541c1580c404880d95a2596043c03120b0780300301440c1e50b85032201d0084280070070300500300720840c09280500520801d90034406e100544070303c141d100c010089800d400300c541440e4001d60240800c0d50149429205014a41c82c5107040e007401d4200f9280810210002030010799808030920030f00005e00f000030041800d241e118400c04000c0104000e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 104340296 1250 104339046 104339057
    0x5060f120a1704080708030313032a0807200a03021005070b010e061002030a082703070c090507020309090604050402010507150605100e091305031909030618080a 71
    0x4400354010440c00160a40141004903038401c01c4401c0000c0b94014440d01006108035031011490700400310441b030065500042d09045c220256a0540741c1e10251003525801501d141d0041d0102c1108002c1400158481c860450751050f05180505207880907030191040048401300d0350000b9103032401c59030140c0350115040345400301041c070704555601c10741c0c40c001c0c00c01c6071620000601c4542d506034140280d40071030b180d9030800d0005400300c1e0f5030b014400e83d000001c1d00501c0840d03000402c00d0003040352089200b444102000c3c4400320145594030a030720442c1e0b00b0314495410800c5031140e104190300400c052015510b0100c0e07001c00180301c4500a4802c41c8540c0c1d440000c0346c11a80030350201d0700b0140d4070030304285c0c100d601e42c40c0a200030849403007031900605501c1100c4a040c2e00c1407500301c84e2000014008545034451143c0a040b030005410125a58032041101e031003000d008000d602c0140e072103961107140306400c624051007039500071040b5400c408010541d00d00041c01e1070054035160589032804 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 104341546 1250 104340296 104340319
    0x12050f01120b0910060306060302040609021612050f0a08090c03030c07170f07080f06070302070c030b191a0a080a08090603190204030b060f0d020901050f030304090c08160305060f 79
    0x614146112200465001c0b0f26045c0c001042006c2500040226070089504109139690f42d0443e400b40d108403500040c001410100c0d41c1c00044002c20102c0784800b451601c40d0404021009074801d41d4420114032022542030001c02c00c00d0340c010000c00112030780a601450038141c2402c60242e941d503d50050341c0c103204401020f0b11030031404201d00000504000d0807601042c0d41c4402a58071100180b5080300c0300c3c024a40016180c81c020300031034003000da100f41e10049180c55612018220300000d0408040450b003103040840403100c078055a05080590000c40110241c6d5404000220140303500c007440b140c0000c0303800b0000c51186800d032042000c1c03c2e62210f03540c1d41e9400c0c0f6901c2403401c50380c4900706244041804002d100020030044d10072801500c20703040d4502001c04200214002100081d48a0403400c0140810f0400c0c0d0000c8000d002d01a003200c0c01c043d101c4a80c841520303030400e41000003450507404c01105001c0c82c2c4208a03490800d080401203410454089511200a152050b02075000f1291 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 104342796 1250 104341546 104341561
    0x50c040b041103100303120b030a020904020f12070611060c0304020405060d0804030507171c0e0109030b0910050606120412050c01050709140402160b06041104030312050f01120b 78
    0x4440c04000a08540b1943e80c501114610109056800150300103132801c60081107220301c51042c8001060000e0051802c0e00040c0d08101e00d00340e0042c801c0381c020f181c078107280145440300340c6e5942c803103941c12019004443c1011001044003540d0089048503031701c07420034021801008802c903900560140c50100349030761600045a11041903010007803082c94005000800d0000214590080d60001c4038400144410080442d5403030152601010890350b0309030114641d580502c003603903445101070510b03101841d500d89560810081c200c2d51311549801c449015084640ea9105643c1d0040044401a042c00e44119010010103401003009007444090701c3d04280582c02001603034007030403509009024910304404003d2803c0e90611910700420119015911580307011300030380d003451070300d182c807464080d680340c96004184401406d41038100c1e40d58007110b46642c080b040100013450003600e81d031030b1a900c40c00420007200c41c024603428124405000500280c0b5100703d24403d016008000c1000c2600d80d41c6 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 104344046 1250 104342796 104342801
    0x142209050109080f0c010b010f0f11010e0114010e0a1b0809120403050a030e01140906030417030702060711010c05030601030f0b091302031c050f070501240302120a050c040b04 77
    0x11006050148049429000c2413680e500401010130904004c0c420354031000019240740460190000c041044e4450304c0c244580301e0f031481900441413034004650700031825800c5003164008100b0904030418040140301d030b2101d03031210340d0301300b1045030307040203800031418403c100d0001c00d01e0058100204040440c00303482042021490078501d000e842d5640b1581c914080d80d07145d400840407404103105a0800131198082c4900680c102d40300000645492840f84c02c100075617000404c11901207084004004511480c03202951044105800900700d5090041000d040c2c24248000010180c0c1800710900c00154050250b90b041407003802d01140c8510041e00d00720142102861007600215020100551700044844100503680241e01313846950f40c0b403003d01036241d9007014441e40442c1d0200019614040d410000f8181c80340a0000000c40398808081e108505020b81110101100c0c0103006100750302e400c424448002c20f80100824040950390f882c5610b50580c070552900c255520a09003040e40c0361798 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 104345296 1250 104344046 104344061
    0x4140a05010519021501090903030b030d09090b0111010f141b071203020702150d0c021501030308100314060601030f1a060c0a0605090d091505040504110c0f071422090501 75
    0x1c94020b0203607103a0308240002c08c81a9000c0d0002800e001550300281030104001391000d4032a0b4407411024149400340001c1c02d103441040381008403034409501142070a01c505840e44250300f10114420707801245c44100800b01070321440e210f100420f0540c08041c400012580400d80c08201c845400d803030340c0400d80c0280528640a900640c3d60b04040302d0f400319410080885c01500366041000e000345042c120b9036420050b11aa260a401d0700042c00400d0043e1082980041001e00b0207650340d45940d1806041101c0180088071030b03110f0400d00c0a2036815000300c8460340344584040104071000081002c554055000741c5004240024003201030000034043c1d071002e0b0b80c0142060180382010940950b86401101c2040001401c00c500840d0581c104c8480c080b803540d01780d8401d400c1900700001c000042c03042d0031511b00006010495061242014032100840500740c6026214a030b1520414020329959086010300c245244041c8801016032403040c00303545040d280d00050100300301c0c0750450041c1442d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 104346546 1250 104345296 104345323
    0x30c02030a020d211e231b1306032a0e01030e070503010e030706200406050906070606030302030913200f04050a24030203130b062404140a0501051902 66
    0x1030407091104209140e4030320035104070b089800c00c140c0e0b050080e045003c40032051b1002c00001c1000c04506640510141ea075030070f0702082501880c0c050611121900515030b5840750010a0b01c1e10150303503400c03a0a1b490746007580f078a401d03401040c002c9000000c1c48802c10701c00c200e0516a9030510901c0522040140b64003620025008100c103100f1804100d940f908007a02c220b80e49814aa4504e41e880717001c1000403801c40781107621500b0701e420014262241c0e00300004041d0840c105004880100300c05004040096000e03401550f40e810302c481c00d0080001403400040645400c2c8a0303652004040801c07198954860050150744622000101c048244901d91010354040c1c04c444000c210a08440b09101d2030000820b48505ca480c5441ea09030140e01040350030b4200d00d6000001840852015140d1650012004012440c044808003d20040c520800070f40080701d2808601444183e0082c00f0401d1224400c5036200c00c00e40c54280000d1162142c16a412a07002d42e4003100c46030107000f0404200d03002035 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 104347796 1250 104346546 104346551
    0x7290703060e091212130506010e2409010b07020d17090a15080408031504050103120e03070b030112030909020d02190c1a090328030c02030a020d21 65
    0x14140002800351881d40900a220307103484001c11042c1d800000d01c8245455a54001c90810449150740c1c00c411500034500b01c40380d05c02c208844001602400180d002c0c10007240021724900b80132010b460240c121004011401c402c1042e90002030366804d00c0e00d411907504140b580c1c1c1c4e814640c40881c00c0d1901183c0001c000c0300480350900b83c0c5401c040044c0080d40c00a80e940800c090b65500c40030fa000554246013070204004c640801c0c046081c0f50001e42c0c3c4484450320414400b03003a41c002c14225502684142c54001a03080302c2814103a00112280c00e460003140100f42450500d401015640300604c2651000381d84200601704042c021552400142300035602103480b41e0034030f4111000f0f5170283c8640380c031072480d00585080c418000c03440300750b0840c1c008450158504880040707854484018242445910082c0003404c00158003500680c0303400c1d445210080226036010001e0152503c0c0c200781010354000f840030182c2c02d0707800101d0100c0e2850303a19007406c5041e41d48110341608241000c0c60303110b050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 104349046 1250 104347796 104347801
    0x40f170f030411030d0c031211091012050c090a090b0102210904050a2702040f1a090601020a0f08030601090e04080705060714070201080406020409180506010b0901050729 75
    0x1050781074000b443c00b429001d03144c01d40c600100407074446141450040110b012003415048110550344020a10440c0d07403a4281703003500e400001010301c0f4508a0b00c034001004040f8100942101d4003500360040528040c41d420562070000280e0603e42c503003c0c001800da620101819168400c00035218600140b2400c0300c840c10144502e500300d50f0040c0038060145041201180360683c541c460005843c017440700d05007401c05181903410130601540016a03000c0c1c1c48402207039403002548141500035500507404904403c420040c00306200e070003040d15066410cc08400400710f400c1284548515a010300d81d99500d07600e9038010b88094440c0d0f04490b1010828408000800c52650020b00c181c034040e0044840c1070703403408421201100103c0c100140b0b40400e000003401035000d035200c1c1360014860354001d421300342c031a0ba4110440c0d103c05109040d0546c41c01104041c00700074084035014010031040f0714a00b020602c006841c40c031410b64020040b42041d00c501e40c0c6004d00d4a1004007950803900d8201e181d0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 104350296 1250 104349046 104349053
    0x4091506170f0706081603060e0907180e06011707081e1005090c041104120c0501090801050f0606070203031c0209010e0a0f0e13080406030606080a05040f170f0304 72
    0x22000da1862605a21031981501040c0200090840840c4d460399141c00c4580c1c4d600d0b00c4207640205402091060540701c1d10003113952410282c0310742c402d4401100400d2054603020a011402515060317500b0350034a4100600d0040501058036030541d41003144900c881c0c4a22100c043c0b49c0462984488a68000c0302160912000200302c000e1340b00c440c25044501034183c0003c0001211010786483c200d80c0d006101d50400c41c1403e402490186200d207145904107a640c03c0c1819160092000c00c440c2d0b90812002486a5a00001510007801c02a0300800561078900e0101c4d90181c0c3c050a414821a800300300403086640070401c41d155940c403c5001d140b80030840e20000d001c1d41000e5003650100b010682c5c1c0324441c0c10000307288070454007011103601510b46032440202032440007a0003009142010040b16000c110400014401400c03503990004903140340000041406074081d0100080c1070070001800007140c500b0310a002d40742e42103a4078015011421031521000e109400103e060494003004010030b0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 104351546 1250 104350296 104350319
    0x4110912190807140c100807021011070b090f1b0604030813030501050109201303020303070803011e05010f110712061b050c10050408070b1f050f010e04091506 70
    0x450780708031071301c0081c042c240d000302e600c030003030f1040341070b08041e120b40340c060381c248110006070304100130380180e8541034040325411060380c082a4440c80c2c0e15a001802000300b1450000d00782d44106400083c14944601c0a1030a4442c0d841443c00c40822100e14160300503039440b14120f070010b55005410305d0b941d03000d524051615494030710081c2e605518000000030b04001c58040c030424a10182c0481100f416548643c070540d4000301c4841c0c0481c03990407004401078404100508505006500c015245e6260070580800d200003128440041c0a10540c00c0000e42d03004a1041645400c81c28034181c04001908201e140c40070b60341c011680316198620190a02c42e140e40090213602c940c00695851a02c64403050341d684c030580401400c158000d0002081d04800c5502558200e485091301500e0440141c80d090040041aa100c0101d030700d0000300d400c02c0c205d240050314014981603901480c010201d0300083c09440448a21034000d546640c0284100030645100c6100807480c00c030b04100706511080aa00d0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 104352796 1250 104351546 104351557
    0x307020604020a230d060b0d081305031609020307030b100509120309091305010f050403030e0c030c060a0509040b13020901090b030405060402040915050f070e041109121908 76
    0x68000fa01d011038408500340003048203002107442c40c80004503510a02038012000720f410b83d81c681c0d07a0b90520105949050302082084d016401c0141c4446010017030f44552192644018486d40c040d03101c2508070401560001d0072540b10000042c1c590b559902c003500900720241c1300590041e5040300c40204190010040c010507002903502140340076032161450b6880c8509032056500c10310410001d55401c189002007407010b4800d2002007007101000d102c1800383c3d00165012000b180d02c5410030507821808200c100e060510880081c681d00e81c004020a900d441620003200800200141d881100d44968010320540d21f000b030824810030213200c20030344c025005445154005401503100281004161302580d0085030000c000e05500c0d00e07070340d0801005150712882101d800032041c814890b00c442c10300c40c652241c15410340f00c82d441d10b41140018088100080109d100703a1a103035809000781c00c01015103103076110a51f8010104815181c7e018503183c04541840e00b0341c3c2c481c01102c0200503405d4040c02 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 104354046 1250 104352796 104352799
    0x1407080c1c050f061902040503030d0c050705010507050d0c0309030c06020d060807030507090b060301061e261b0a080a050403050f07030207080105180c042f091201050f0415060b030702060402 84
    0x1042540805c03007050788110f01c912903066005100104803a284c42e400315940c0012400c046240404a5546500707446040b03407500041200441d6071000e003005405000400402440d0410000510396005001040b44075800f41c4410b50120301e9100900340c65000401030700000701292410f40d56413900c2c1d40d40e58202d004000702c1e6410299920792034100310013940e041e105140c84086682c0700d0090080360b201e070556000000c01490410b01e07120541d540544030b54403051403007401c500f89040081486459900102c00020301d1040005d03101c40e60b48040c000380c0002e454171020580d61143c2c10100c5160189100b40c01d14010001118010507400041003c200c0389034000030300466403482e078502d00444100404030340c07982000600030140e10f0030b07501540295402c04100014413044031205403502085410311a900307000081c1c0c0240b14680102d01c43c510150b03a200901440c94440c4201e01c0c5041301070001000841d8030003600c50240d4a903001003000c0c0a0080b0515141d207000c09000350f61724820340b800e9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 104355296 1250 104354046 104354071
    0x40b060609300604031202030405150103060e0105070f090e09030408030a090f0503070f0b030612070f1404020306030712030201110d0c0f0c03020d0507020f04020c0303041407080c1c050f06 83
    0x20b0425001c00705025110f00d0301910340c040c0000040e0a604060f510082081f1800c0c0200a80d0880034409a000640654004c080c009034242500e0041421580c02800740024440d0141d00b503c0c0d0240e0155211f810f40f10380489254050310380030100e5240d8015500721042500000ca5600c81f050340c00281e82003200c40b0741400490540d070307030002c0c10b40b1100c55015405020b04244014481e01211600943e0480d80103426a20601c50070300070345081c4925504002c0590b45903c0701081001004400c2c1075925208071400c61840c200307080000d81c1e80c4010710400354180d01c106101c00505000b94401403030703250016649a60b80c0c92a01c100340003070090340405000f144032003101420303003441b403807801142030340c1900208a82d1402c82c1007901d0740e40002504903030202d40c1504200c1c0d070340c07624000b92101d0b807140c0000b0364580c1401e141c07491110610703e2035540158132580003003080c07843c005001079052200303491000322060440c030707584080420400061301501c110859070410303202c0050885d1250aa00040c03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 104356546 1250 104355296 104355379
    0x20409020c12091f0e0306070807020f061005040b01050706021204020109060513050f0a0503010617060112120305060d0834030c080d060314010507030c0305010b03040b060609 77
    0x40700b003940038000c2c5254010003040820032503220415015021076902c0d081003001d4040b40700010b0f2405904440c0e0b5800204c5000034444800d404001400e0840f0080700602076500e0802425464840380d44219446603031590035898060b4040d00c111100ca41d001034056540d0380020700a004c0d40c000560f012400500c040c0030010701a48100c00303840c80b42c2440510078040c546030000f0001680112560940e02a040c8040052156000d20501c0010159220410480054104014241107050380510600d844402e0000c0000d24084600d143d815414180011180c03030300030100d5200291180000c0000780002420004031501441300c1503803640035011503034205101041d8844c1019402002008900c50b5012000042c1884001e00740106c001c6900152440e6a0b032100d403081c1254408105a996490044c4007400b58540030322140c1101e6420b052005500d4030f603e0301014440103002409207600c0c100842c0b002d646e14412541006402450b42c0301c01180d580c5295141400040c541480407826503c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 104357796 1250 104356546 104356573
    0xc0e070e0112050705070b18010f0e010e21030702030d021b010b010e150702030309190f09050c0904020c0106150207060809010b0901031e05060c0403050f0105060915040f020409020c 80
    0x70513100d403016540c1c99080041a42d0380c20015800034000300c1c0e001041002c5940c1c81e4900748a2016080c094200c046640311100044508440402041e402c26401c0070103100c0644110701c40f030740d080342104262241d4a03501c0d40e07812400c0d8041c850b03000850354000145003050245000c0f0084c40030822400800c030080d0f000f001542c0c1003c0d407041c02500205210118084a64804094035005002a081e2072a080c01c03000020300c03002804483c4059241304220901042042600368005803000480070826400d04600000d514000c4e86070080c030650300082ca115a1001c01e411040082110070900454282d641c44080c0d00c03202c2601030000002d2880300021000c050500501d0640c090140140380c940e400c5441d0704500c01c4032840c0c80724200076440459000902d04111244c070518169030b1060701c0d9421881e0090070035100182c0c4c0d440c9681080d007480540e40c0c0d81010190042c2240410343e10071429040480d0140030b14090a0020500c0444c000410108540003858148242010b59005c0408042c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 104359046 1250 104357796 104357801
    0x302010f0603030e120a0209010806162c061b0d0e010512010302011b0507030308010e06010804020312030702010f06291201030803190509010b0102011503030c0f0c0e070e0112 77
    0x30000d030005070101300b10026810f1020113104c5c810380e9101600d0305074040b0340200c0e414403000ea000310440da014008000c0d0718442000ba000b541d911a18140c4011003140c814000d0350410f4405840389030303030f0608903980031341e441d0421502002c0111490b401d0341000a805280c0341d540189125012942c15101c480c07a940c8508101e0303665074205000d906d0300c0e900315001114002e42040d8003d20101981c41c0c4d81000c90001c0114000861203547e8100b01581003802c42c4c5004400030f05441e05003c108005c1c800142da0110314020315400090744070b40c407561038442c124090500d000c500c12010785171000c041800b880d20a95840300742406c1750b82040e005908086540c0a10504000704c00341c102c890018000a00441e00039600070702100a183e8210313080034503240071200d0a445e4044241c2d540da520b000656020702a00b4200c051000704108000d1031030701d000e0000307440140c1c02001f4004a14030501004a0112604050071240000f20200d02d41850040d0044426100c0680810460002d074040a0400d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 104360296 1250 104359046 104359049
    0xb0606120f0a090c121205030105030d031a060c010b03060c030c040e060402070204050a0506130204080c04052a0403050105090316030507020d15060f080c0108070f03061a04030302010f06 82
    0x545000085036120310000e480081c01420210680f0b4440a80f10b000c50042070001d800340110510751102c2c4001c07854031400da0541100040c00340300050004014540d00410070700d42580345420040b411060061a21b54007218040180350b01050219500c501024158001c55094809908803881c5483e0754440300b01c40d000803607809841d004100414084501c1d40e2a03580e40104001d800581000c9085d4001010768800b00d440c2581243d072030041000d98608280c1c02c0420501c0000110f19140c149442c1648807024030f030580740225192808540c001e6001c20421918240e0310a00f417144c00d080c5000c03c46151311511041d1503d44c00c00020400080000c02100e402461007a0b041c20030990340c0d68261a29004002d0503a03001201d140301030003041e0159503e101d044030f035000000d8541e0030902c0b50200d44803c3e40100103a54014030317284086980003142181c22001600709103407441390b0504224090090394100c2404044040c0d207402e08810103201420540e4440e400a010b070b0841c2d03012100481c0c486 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 104361546 1250 104360296 104360317
    0x819050c0d05240f070c0309140f0303030f0105030f03030709051003021b030301061d03031e0705030c011b020f060601110705030f070801060602070b03150a050310090b0606 76
    0xc1803a864151610401d884461480b45094501d40d5500c0ea107407010511942d00c88000305001030003080f051410002403240c2c40603040c103210300c0d01e8082d5140108078600c54000c8100309a05110800015991078982d11b911100003000c40342c2d03074540001d078005800c00a100f00e40c000e10415050302212100401074a00c0344000350384020b049441e040c100300b000350240c000002810707401c2017548030055100500403e1011941e004540d00d516100000707001403000c0b00310032940d1303d42c6a08102c2c42c3d81d01008071080c0c81440361000044008001114420740703d5120018200d2000050b0415100d0041d04005000602e450350020f1896010406031b03159503940d00030007000c2e0003000010301036600900f10b501705c000d4a58100d84015031580c000c2450500303000080c11181c0c0c072001c0c040150403802d001d2840a0a910710150a82900c1e102105101c1c0c00702801100c00f0744001c172140c0c44907484080428000703040007811035403c1d172204035a030001002038840681c0e80f2051803001900e00d0401a04840c03051b0f50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 104362796 1250 104361546 104361553
    0x1e0318030f0903060c07120f0c05010207060b012c04090c050d06050430031e06030807020a0914070f2102030f070311180a03050607020709050604050c07020d030c0615081905 76
    0x940741c0302110001e068480744410301c52020340409c0480c0092028000360792088000044900c0e03400b0014202612550320000869003034100b4408a009043e0004040281500d000c61004842c0c0b4211260310020340010350401c10802c42e61040c0000f40e01302c3d50196018003030303801d41e80307000c000644016a9002c0300300103501442c21400728201d2290b800414540400b86180070304a034105840000e0f03d0465005864460b00400c1100551500030340c440000e2224440402840b0085040344041e02c2000702a4418060201e1500000303c1c0103080f00c504202480310798515860030181c05038002d402c00d81d40c290018000c10005070f04680203200b41783c400c040000840303060120070400c8a06694802d07a6041e000709500e080080001e10170041640503a086401410359141005188070803101c0040c82c1a200d18200428000d218111100719082d40b41c05a8400e0201c00050a00307682e100140300c40100628900000c00c0d4000a0036008141070361054801d540c1808101114180c80e00caa200016007a0742 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 104364046 1250 104362796 104362823
    0xc1401050f1f030b010e101a07020108060a0509062707120e06010501021e010213090b120111041517010906050310050606120601140d060302010e03031e0318030f0903060c07 76
    0x32680030310343c1f142140702c1c3c52038a50b494411501d958041c2d00e04004030490701150071821583c0210420358422802c0c1e0702520271528010010f104000c002c4e0015004a28071031507001030300a9542c15401034441d668a40043e4141440f00402c10800b06100008141c40d20380b05844021000c14218100d46059004202d074109041c502144240002c03c480324540d400c1003c1c00803480e0348603400004002a4400050f006210130601010358000010316580c0d0740350000a001d0980003200b0745090b06c10401c04503007408500c1c1001e445405181c21500c4100344a031000064210454000805071402030342500d01d1204804144002e0b030b041521039550100c42841211100fa03050403138503601c20f10501d0718180c3c180f54442d4581151744107002019000c0e071201e0b414010b5580004040d02d00705000d4000710324002e1600342034508042d92007510001481c0000c0814421012545800b44503c2081d0a8a43d103041c130030a10680c96200e50140c9009010b48000140911003030020764484c250014007058204 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 104365296 1250 104364046 104364059
    0x31e1612110412080307030e0601030f03050a030b03060f0402010201110f04052e0c05070b0705100f0b0a08030304050613030f0c030c060e010507030501050319030c1401050f1f030b01 80
    0x81c0110103881c54144002e21000418658045526560f240135240300b135664200b070030b0000e05030b9a456000e81065072050004200040300603440c60b01540d09480c1040e01ea4000107001c601514642100990501c1000305104501d030b00108103038040c4d4400d030000c211003c06514401c00d01d0180705100607040d541030008201c10700f04501d2206004410044039900b141c3c90942d175002640c0001c1082002070706884081d002c201080145402510740485e020341004043c1e5a0a41d68900448038000b03115195000d41c4800d2106800020301e02c080200321520135a21100c0e03103076607500112400d071407512800300860292103c1030b41e940b4846806507100d441e08a0810300a44400c6007401d400c504000001601b0360105440c5e102c0c0d011140c40d08400030520741000d040043c01d844041c1c01040c402e40003644d008010011140500a01c00d5060604a109500c54106400034103502d04c0031940325400c02d0704000304e100c000380c0c0c2140300e01d2208205001ca843d105000d07034808051808000d00d1004514014000c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 104366546 1250 104365296 104365301
    0x1050f0906040207080a051b060408070f02030c04020a02010209040b0907020a080705101d1b0a09230403020601050109120b010308031801060608011412060103030e15031e1612 77
    0x860005400585007600641d40c0c5c4a1a5000d00e4031310000402c00b044454141c2d0200d840c1680e0660000c2c01854a403e064695003014030403420000c0c24100409120310840d10140001e46428030002c00031501d90b0884200030703010b0b5000d001035a110301c0c03901c0380c0c4072000d2420101c0d0900490f00c2d030f0300404501c081d651300c3c1d41066020300313001d41e660b00c07400741c1150360036007280100400c62000348001c4032115640c0588500e0402074411581c0181c10000c41080191a2494440100c40001d003011072400c191103201e51100b900b5004c2c8203040c2c90080b00f027105264002480c10304a500a0b40c40200955a07201c03661503502d0790030780c003d0946081c5c50040020030100406960814a84144190b048030907130310240c00c45190345d2041001c1035401004120b011501a07a00c24a4a41503601d01d2500c80c40c6101c060f221141404000c06200004000c0003140d00d0b0000300c0d0108824504500f5501c0c14041100300da0000c49880c2c104502c5403800003e6001d8201c0d01240a0198082d25041050003040040002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 104367796 1250 104366546 104366551
    0xb0708030a18050727020306010c02010f030e120304020f0109240314090106090c0f050d020d110c0604050601090e0c240403030e09160203040b090a090509010b010206070801050f09 79
    0x81c402034000c280d030100304113024400081c26000e07070b44240b1058844400442403000c1181290700f81c030500800038240d070003d800d101810384c246010701c11007810703420507002006510346c1944588107100014001e00c150a0041d806540201e5010101403000c100448240f540e5005526010f0785c010700900060342508050380300704001c1d060100d00400501c00461111608407107103403c0780c0d114802000140c07914840e0301d035522001d28005070348c0c4807000005407042c03148004030384d400d542c001540b044030891039000e400c0711b54a4407202543c440600d00c49554a032020344003900c3c03501807440005004200341c490341c0000fa05040c058445c0034884c4080044801040070b5401c1030f4144088841c01d80145400108040d62080c0c0310b910b400c84001084c000248001010040e04403004104403000380e80000950b01200c81e4095040e81c0c0b00361a0300400d016491687c0502000c602384414454029019040994a00404c3c0d08071910b50396400d0341250044020710803241c02c10300240e05248142400b1101c0b55 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 104369046 1250 104367796 104367821
    0x15050a030f1404110406150f080406020f0f0c01140f04020d0314030a090b0c1e030a1808090f040b1309050c09010312021002030705030f0915040c0f0b0708030a 70
    0x281144002c9940440c0340d1085400300d42246000c2d0300200c45280c02d20400c00500304075001c001526210344000341c004000c40000d1014401c83c2c000150820103141c04035031003000c1c0415141e48801d0040420106d80d000000968210750815000050140b410b02015104c0c2d6204c1c58140c4454840d80c09002c0c550801c0070081d010013803500032000c0302c40320100080d402442e1038940051000c5260502710500d400180400402000410011a8914104a00c4041e02000e6401640d0329240d03603070300d00002c181071000d16a0000d4002403080501008202034080e02800b0b03901102120503590030001281c00a90b030b120b81c44500071081c5507041405d075000301d007218400c20496507c84020703c00140c13581001d9008a4074040f00c07440801c00d031941071080031310306645800c09504500b00300300c0140007400002c0511240d508201c0005500e80001c20a111068215040d1500c00d410301d030800a05010903401420324010600c0301c0000c5c588807107000c41d01d065401000e01411500c45080c4031000d0015992340300c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 104370296 1250 104369046 104369051
    0x60209030a0305030114030c090703180b04080a03050c03190c0201110f040305120a05160c05120105010503060709080712020d08031602061302010206071818021315050a030f 76
    0x50945803410030802200900907100c007601c940c50703c107020a2822215600038042d410100c43d00341c1c9a11480350844d0040943e041c04161222030300070a920700c0705c03107200c050a440400c0023440207002e08036000703007000c14241d40c00b481142d440f059591694072003901d181402d026607116000d445c40c6107034441000500d140c8000710306030351032510b0300420ba00b02d801c0040d00c00100140800410030204860414424502d010a0800c14461302c040c00e10300548001094551a9403502810003545140300f0020788002003498014207420085240240802d001d0140030748502d50110302107600036001c4d0b008450607a00240040343c07c1c9400f90444404182080381c10070f808400f00b0f800a41000051072103a4a60320300740841c00b4444200902d409405000500c1c2888201911310150340c1c0440c0f1140d21200c1410302c0c0759002c11007403501c180300f01e05900160106100303400c0e481042c18113800501e4007004c0e450101c420030340c5030360302c00c20440d03a07040b200804140100240e04440c0d0094000c512102c4510800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 104371546 1250 104370296 104370307
    0x6070609031b08210f0c2802010f0c092d03290601140702011d04020c0106030507050909031207030b060a03060603050a11030703020714120a02060121020d0602 70
    0x10811103040c6030000c0f0f03032240c40880d0410790b129501c07611800e00d1034404111485030402c40120b43d1240c10141489400200000b20300380c4219001c00b00801c030303200c00380203900c2000901c04001c2c020502005091091401c02d01805c4599200c0c7c04410142c4606088441003c2c1c8907018920222101181040f0700030144c20300080810f40e0352485030380c00d01d8680208000031003460901340d0250001401c0f40e0500c00070007201c02d840362803403080e900030301da082c2070024a10100d01e50240940300d00328003055000b0300018030b40a1440040d040001201e00c50402c54222503100c004210316840300b00c07940ca02c164400d1003d4000c14040c0c00080341c11010904002411801841c01b00b94a82e1007400307040007003521101d08100b0b25a040c82480e5200c04004c074104180d044143d0300c945a4031024109204054001c50301d4400d20991044880b446058102100e000074030f48418900540c200740d030381902501490000040c10760326030710310900340c0301411700002124895508101840801c03030720a96046038240403 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 104372796 1250 104371546 104371577
    0x20f011218060525020c010305040602220510110607030b180114010807020307030903030e0f03011a030c060c0a170c011a0a0f03020102060f0a02070804120c140607060903 75
    0x2039950341c80c0603000c04512403402000f4040d5100907010b103112491040c10044105507408500e20f5140e003000d2030301041ca40c9075414030340080d0050305c501c0400ba0410750009908101d00d1800034048810a56a094074480b220b0820341c4c2600714900140f03025040b40f0300049006210358400581c0f0f82000705558008805400c030000703130b41c0f000d80103542135080c804a003840d0f030b42e01721340507603841a0940300442c03500d041c03664024502010f51100170180038803556640300b10340e6175448091442c1c1c000360003040300021040010300f44c22440c20b105406409201c0c20101c5600300042140c0759048100024180c032200c91740c4125000c4840362098900c035405000440364548280181b00c00d040c000c2085910030b10b000000c004141d082c40d44944ca900d2540c0c602040141d0b004101540c4c03180070003220500e50341c6c0c2d60510390064481c03860000c00803140000c0109600404c540c00e0360045001c2c0900803c2e90b42c0b60006501c95030200080b16611170020300c01180020010b402803030a59120380f60040880402c403c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 104374046 1250 104372796 104372831
    0x7020f0d08070602030109050f0123040e0102070305070c0509010305150c0d0204080609070b04061b0501060504110d05100605180a0801150e0901020306240f04030602030103020906010c020f0112 85
    0x1100c40940001c0100007280b080d003e2240c100c0032040009d402e9524145050070b0620080b46416800c8201800504007551144d010b41c243c0c1c410b2000039580c1b031005243c0203040b03502445040340c00c030f0300064000c241400c01d6145a4141c030383c404020058280c1003134050660180003002107604180c10400303a101c080c0140040c000402101c4000c0005040c8a1402810800d49400c00d8806000500c8100300c1c5550146507000740c0750381102c07441440c0d5040c0c00d045002d062240c00494102d0304018254400c1d280280c0100055101100100525110801c001010301450312070303200018400d1042a00080c1e2440c10001d5154004080c1c85040d079032245100d0075130303503024a000d07580110200b08002c2000000c40b1141c0c0711043c84021860f40c0b0f00040001c0da110084840e1120802404a840c11500910011102c41e1510301c901e00ea2503d0340c9292400c041e6000740003c9000d4051343d804a4020b50090081c41e805640c01003005007034041c0d01c001102d0001038084080f80d41501c5000c0c6180608061 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 104375296 1250 104374046 104374057
    0x1051e0a0603080412030f0807080714090603012d0303021b010e1323060a14030f060f070e010206090d05030c1204141615080408040b03100801061a07020f0d08 70
    0x4030701c202041002420041c02810480d801d0802307102c848810440c23038540c020350b40340d0302031581d040440300ba401140c0d10900c54020320184030f41100c170000001c207803402e038420780c0e00404410000c10480c07440010a013051240d882e20008015901c4480704500c100c0040028910000061420038940041d041c00521030075030a41c41141a19920030300940c3c1105c00c01c51001041100c0c0702c071540241070080201e07400a0b803a1154440d51410030102c0c60b0290307824000340c641d5400d0340084a200d42043c0c1540500341905a80440c04140040703032110315540080780282c032540d0314030040c3c121401080e0041e1429070000308000c07581c050402101c2408900040e0f8035009134018000c1841c2c00b05a1f07201d640c5042c0b11500000303031514495401f00000020145400140ca00b10710300303402c4545030f524029000f4010740e0044420400080200110400e07680d9505040300c402a009002c800d1355605401e4620b0005220703450058010480100541001c21240700c0980000e000c503103508400e0303150200f42d80c001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 104376546 1250 104375296 104375309
    0x330021204060605040605060405040506010203120103122309010e01050f0d0504020f09090604060e07030c1e06050301152001050705071101210c0306080706020706090801051e0a06030804 82
    0x800c203200910680b07116100c044c1609a4042140605103000100d490265200341c2d4440e0b80c540000941d903900c00c0c0151a0304503140c02c503507035441d61241380030060141720007140d0000803919122141b0900e807500d41c0380010341e403000c0018940070094004550a032240c0d10b1240c1808010003101e40404415030043c411401c41002c001440d041038410070881241e03401e030b554032038403c0e1070070b019084e8804100640c1183d408200092604102c2c91503a0910310365520240091004110000390030406c41d0784a40700038070b0701d04400041511450140c0d01f500080c0202c030140184e4140c1c08413094040c0fa0092141d02d0f801144d858008000c0c1ca42a00f59501107030740400144011548404002e41c00901201c100130900b4001044000304219021298080d05400c01860f110501541e90038000e1744520050903958095800c0030b0380b40c681c046e40c1c8251a11810001403888000080e501d80103200700ca0141d42d09424050071340d01c40d04e201110b03440018200c0d03c0880e80e580b034008001000100100001d009 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 104377796 1250 104376546 104376577
    0x2010903050d3203130f05030a0e010206130c060f050d1107120801080d1d1002010b0f180606070c0b0a030b040b03011812090302030a06050a0e030403033002 69
    0x410204008441d5241105800360309515003d810204191000744d0340e016034102c040048010325400c255446400046011741180000520480050f40c4156440c40401003a021100961a80c080e6403045e1908524003510008002c1c4052000e980310f13074183c40d03031465545019800e05500203003402c00c5602c20b10315000c061900080c144100314149240040310705c91802c003c58150b250810381a01c4801c084074075001c00c030195004240030012441004885d103005000f80004038100c82c4040c0c0205a04c0315a180f0401c5d031503110901600e0b0005001d0104c50b0510741040b040d449080620503a600184c0b01102c200b00b01c00d07004035882103210081c100290b20707580d0119414240e07405000c2110715006449020764108044c010f010780d202c1508a843c9030380841c00a49148100760b040300c181c8003a810003503040c040e0042180c14410a84c02c070380d0080040b840e0400c54003005ca41519640d01c124030008000c140e05482c80009081000c481d01e08240314090034440c44030015401004030392005a40440149 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 104379046 1250 104377796 104377817
    0x61b1308060105010207080a0b061c0b0f010f05060901020c06030601020106050d11101427040f02030f07020a0302060a0b0f120f010606030608070302060c07030204111206010e09010e0402010903050d 87
    0x11790400c00070000741903c00151030442c0d09038440c001407041c0245094040c201404a02051301a8030000504064010400030160700700f40703040c061049801c0c4035491407015200d1010481e841c042c001c9885940c416001083d07030002207803d106407500300801e12030655503600c1e000246520340d8906540380c60702c00e512003401e007041e80c010000e01440d4102c0349402c00191841b042c0d11540740c60100c1d207464403200f400702d0800c40c0d0802411524901059040d4100f410601803d841001540186004404600c9a10701326641c0c4181240d0780d1464901c0500107a12200100d1141c6005501c00842442c024004c600000c401c40080386a00d050403030205c103950701c050b9034050845020f100d4000644203038642030200714030b04044555264142e02010703210b45400103441311544010000031000359406802481f03281320710448150a030b086070301c031a100c00010300c0c0094400d40c03203a061001c140314014031020069080c0bc007d18140d0350018402c82c10b01c08010b1011000c5001080808403200301a5150f0f440c10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 104380296 1250 104379046 104379049
    0x30914012a0201140c0310090c0513080102071a10030b07051c0501060819020d06120c090c120c0509030a05012c030304110a0902040b0306090117061b1308060105 71
    0x640c403030795020381103916000100c0302000c21081400c4d000501500c00c2e0342c4a884211202008114a9203c3c040c05490050324010080c3c100000d440b40c403465400c08a000c9503a4080c0701d080c0d2107000c0004025014a06410100c800419809a00488100320040320942c80c1c0d600c40d48400b06c00d40c0d080000ca24049101c5802580c01c505c1c121a007012060140240d509d0032502410f10030002e03040c002001080000c040580c5003640c1a00d42c601a203c2080c4140c0c0c0e0385168030010b540b01c1000a940b1281401c6c4c000c42d0a540600407203803c0c1901e81d90300145401020b480c04000c140e00034007581040340c01c21610130195003c0012424042c080c6c400000c9906034030200c0225000042030700700031264104000381001c1e2021090320b9000d500040322000c074440280c0060b11000e05600102c0f00d05101040205a8031b0094002d144a2501aa8900002c0e44c0780c0c10420040c000440001d009a0f02007000281e21104490a114052a0002d0194209103505400c4140b2034115001000b00b5030102c801001107 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 104381546 1250 104380296 104380361
    0x60801060f1401080406051302091512060c040603020906120f01050307080a0302120c150405060108121810120212041707031209051603050d0806060f0a03091401 71
    0x280802060302c2031001d1200e00180041e04010001b800316a41c40c0300090540b030f811761081280f168000c0c051207071b038940690840d210020390b88800c0c2c06608580c541c0100d00304006191402501c0e20304200341000d2030000c00f01c010354002040180c00c01028040490462902d00e065801404400d500480300c0d810001454030300111607005003034941c0000310400101c0d4010070281c07003030310380010710707540d40e003a0610194901502666903102542d810000c10050081c0400d4242c140c2e00648252038100311803c1c006112401940a140340c003800300b0f401d024140c5414002d0000070711071410b0400781003905003020310480c0c2000c01100d8440e0381410802040028241001507840c080d400d5450611141da20010b28807a504d0701000703101d46e034030742403407050100400103110101c02c4100d2842903143c49140150f192800c820501001c109200e02080343c9241000c15503142524211586003000001c44040b406881c01d42c0341a100c50f64040006041c4d04800c2c01100800b0f5000307016032103008143d9010404 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 104382796 1250 104381546 104381549
    0x10b040203060d08030a060b0403030809100908030c0a09050415030506090304030b04120e0409060903031d03030c0d1b020303040302070b04080316060e0a05061506030103080f0a0210060801060f 85
    0x229034030400821074240e0350302e01101119070704480072589070b0f5102d02601000306419002120303083d201080001c06c06511040702d9118032544400d894004820b10079940a4400116009000b440113000052030545010050b002c100e019140524000703a881e004601110381c601c060f10b201d00340725070041c014000204140d6400008950080d8686882c607205e203005c202000e44014000f0b454407140707414681c0325601d164a842002032003040050f425244c800000c0015000c21004241402405611820900b1070060003106010182d0700d9541d036000441c90b680d1010b18141c03036890b607844a103007014000828812007070400d90004e55480c01c0c54280607103000e001e03a0040d001c1d00c9007040144880000072041e01c443c00304107a5a94030354006482c2c9007010b40a0400603540c1031048114000074820005060341c01b81c1060322049078440d9051043c006984803d02001d080041c00304418456219078000a01f40da008900c1030345d0f903c1441502020644060f984111240d80d160305090094500c0c140a020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 104384046 1250 104382796 104382799
    0xd021002031b030c03221a040512030702010c060b04110301080303010608090a0f06270c150201151203021e0106050a1418070302040909030503091204210c03140a0203010b 75
    0x14100015865115924440d440d48640c1b80c41e9074450750102815405000c501505241c01c010350703040401e03811005d146c0c00920800c0c0c850900ca4004019107080401113408082d0103075110100c1c079840b51952405400041d0906d5009a87c403590a6003400c2194040c40c042d0041c500955074951400000601440000d071401075a0307002038514030700003081d00c2d070708a001541c0020040b850411507001c82140c0082c40605412285c20784500c8001c20040039000c0c003d460201c00301c0ccda00356400c400200d00f200e403018002d080c030707071031b0340c0b40501250b035024903445022486441200d03406442400c0a10b8031440c0740410715001d0391218028045490012001400b41015908060314256040002500581e4030103031078141401400c042018240305e5011200074050040061103000410314000b006640102d0304400c8a02841031003984d2000d6940484049844120308102645041e4034091180c100500d01100c1d0189901030010004441c405c0aa14240420024190456850040c903080d502200c1e080c0707 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 104385296 1250 104384046 104384053
    0x307080f06070c051006030602120c040b1602040605120a060501050d020603010b090406030501060b0c1006270b0306180d0c0c060e06160503090114040f050d020d021002031b 76
    0x614051400103030303195100c0020f103040301d5011000e06209051201d44440e6184043c2010b0f00030091200715001000c142001d50044840b80d074521a40700740c0c2c0d010344e00136180da89504000041c800302100b07503807050305400207000180d516a5140000c2500c1c8a02c46041c0b03c6400c8500da200500c0414880c081c0141810366014015a803543e00042c228801401180c1080f0343c041480c0c901030701e440e4001005181c0c030000030045140c03241100c4c5015001b0044203110b170700c100e610b0b540c40c45070140505011074000d0307880628400b00d1080340c88440b010080d503060071300d542e442d040d20059a040044a0156142500480c0840101c041403400d19680d100d03080c0520400c055541e0002d48903034408812074000c0e26040c01c0282950000500c1ca00c141e03280310484108c030101c55400c2c072102100500d0205002d88603080b03e10041e4070403980f503019a100e61880364004080c200420704128082d410418030007800c0c1605540c4550000d090004c4508100c40146d0021603903d540302d00d000303100c1002d2100324005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 104386546 1250 104385296 104385313
    0x1141f0e10030902090c0310080a020a090b151306030b010201020306012007030818010305100321030f022109032506110c030307090609060e09061c060209030708 71
    0xd001280389460180c0900c1d070841100075058800c2c0e01140b82e03264014080c402905107041541c00c0360300f0558032020741031220354000030007900008500380e01e02c0e409000803d82c0c9180a807000d00600c840c1d0407458110075241140b001d82ca120300d0041a4840c00f045084401e103041c01c1008040350000d101681c19a84100f00340300c2c05a0b00000303131242d114003480c09941d202c0002c4212070b00b0489240d100500c80100480c49004111032010b1980c0f1103802a64100100d655681c0391a120b486c1520025000c0b0b65941c07081004a0403a01e04448a407002c1c4c180445c0030019252a00100d0780130219a81c040910000c402c0c100c821005d000c40d404c140c0708401942404950482d10322403081030010382102c034506000d5082006001e40201d810203084500e415250715240c10340300d45941c030444001000170003943c00824014021541c080035030f203850f0f0b0f40c40000341030740040c000c0407400601000d600148845006000c400800d00492032144a25805607c401d209010301d85040c1154010b0366568016501 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 104387796 1250 104386546 104386609
    0x312020a05090409031101020c07090b030a03140c031b0c090601030501050312030a14071d040c08070e0a090204062a050c06070609050a0308010312080105130209040209090114 77
    0x1502d103142d80c02c940001c0d80304e11901e010750342c040250b9155901c9500116481403c4400414111b00310354440c90288544000181055210000400000c01107000700b0030510100e0010000b03000800d000008980c50008984081c1804561001121400b917005441c3d108050401d0018190014400c0c20284a1035040a0000c3c2d1603000d42303025503050503408000905014900e4109000521034040c24189500308034034001c04031541c01071491071a5a03101031845150405200e00303824400680d80300b2400d034440207402c49640750700030b10096100007410301c0410181c0151008000815058461020f242a0030140250004079603c646064484200e07080000c0b072004150f241d42c003903003110202d0350389445140100062034903500241540c4103420152041541200c0c0b2a81039900940e681d000c60740c0c0b41c401c21651910b0901680e500180203505001400e40d25802400810070010009820081440042150000e09034410658100010110b28403800d1100000140c808400ca581107415810304 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 104389046 1250 104387796 104387807
    0x120b0307050d03020106050916020f0a02060307140c0f01020901030606030e1504021206040b0402090a0c350f041e0c0e0a060b03150f22020d020f030a090312020a 71
    0x12849000b90007074a01e0400b01403007075010402810004025514500f0310000400c0c4d00029008500c01500c40d4541d9400c0a90f40058011041c0b6402007800d8550741d60500c00300c2d82c080c0c02d01e6000c07a80305010f00a00014120612411100c060340d60001030b00c03400403000040968005a004100381403a0100b8811f1400c4041031f43c1403000190060034100342c5403840428560b003c2c0c0403000460303014101c00c0c4010006104540740c0154002c840366034454071a650042e0840701d6083c41d101c04103403c000600c01030a20810703944088a9441c40f0b4041144244002052070202140c04081c40001d01c41004104030289003030b14810456050140780f0300180c4d40c3d03400b026a00c0c42c000d4461002c060710018441090f2078000001800342c101081d61a810030203080c0320070761003402c0d0080c03080c000440043c16a007011050821040ca6851000e0182c8480500000081d8044166030040a40030410b41803036810301e000960140007025400540b84215080040200c0e034840380c011a406e004200092200303902030b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 104390296 1250 104389046 104389049
    0xb0a0503070311220608070b090f2e0819050108060f0a0204030c08031b01050603030f030907081c030f05190209011106011e0e0105030307080a020c150703120b0307 72
    0x10742c10783e00482d204030004144400d00d015240f40c44040100910800c1d04603044401110b04400440b52215180d1680080741e0240400080d0004220002405907103000e41000c428924100700c1c0c5030600802004003111011408155004901028107004030300020712080c5071500c0380c0c0c046c1003001d941403101ea01d864502c09404503803418a944082404292154100c50045070b10104401845950321103850312a0008200c0c0c03034040340480806000e407081030003451f00c50310009001c0c40c540916144225001c1e08054180c20b241d10440101081298041084041012265250340703582c000014004094810220460713030b10908120a100c00910460303242125104640b50160711440002c004803641034003642d0b540300a2113500000500f0400d41030400385807003400c00349074024170340703d50030490610028840c10740c00da4410010394012820000141c420314540e4416a0105038500d0001790304e1464030303000705108880c0041c01408150300100701a00c9400b074804248100c80305e80000980301c4516 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 104391546 1250 104390296 104390303
    0x110a050a12020321010801050603070e16050d23070c05190f060f0507020d0903110108040218090313170a02060a090e01090b010e1c02040b04021b0a05010b0a05030703 73
    0x4075010307000e0500a00981c0c0800b0004130084a0280b41301e180a6803000e800c6c440c84413a5480c00e00400c00340d0a0202d035000c20382d141180d612025488000c1000760b40e082f540c610600300311044c13009032040a003a01443c0304a0b440c107408210314500381c0d192500c0580014143d001403201c100040d0001440c04280c8840300b03c200c00d910409128282040840c0c40054036005003081d10b0441c0d4045481410381c0700c0f5000700c00c1c0e582104c00c080300d024026a005100c1e07001c040c0c25000d107990030800540c49000c05940c058806004a04121400e8404580c8404c0540d04211980c20204940080301c455240d0342c0d000b810396004203500025048402500c41b050100041d009000010352000c0c0c203400307128600c0080402c260b10340d01941c2d42e00100401004c0d25010103001a11600c095202c906e89040d040f184080b490149104458159003000000c28161030002e410a03000d2044844d40e00c1d00302d81d0318100101040c06040d803000c6900d4550300315840141074620460b01030320103002c0354400295440a0341d60 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 104392796 1250 104391546 104391563
    0x30326010308090d080307080106082d0402060405030a050607031118010807020102090a060e040f02041a071e21030507050703080612030f040812070213050403032901110a050a 77
    0x101c00f030205100304226580a030500d02c0001c00e10003003550080d1118101c0703d407a9914256511508400840d10018000080c4012980217204501d40080c0e515241c00c944010003261805650300042414400d0321281500c00d034102c031040043c0f140c0c050051030f4610b000f8034600c1e4a44510718000fa000c0310401c2c42c16604111502c0000349a01d4002d50488420340002000040c0c03407960b036400144480109540b49028074280907041040c0c1607540241c4098070b054020140c2041c441000b00140e0340c01200b4140c500c840801480c5809011111144407254000c0f0390101100311480c1104800806011040c0c00f0180350104102c402c80c0e00c5026508490743c9460a5003003910b03038400103100300e616450750a005010006507840c2c942030550091089071700a00648417400c0d07000032003030594060308030040d401643d10740c002d175180d20080c0c0c40160f215209041c0004c0c541c140007015184180754240d1002e5100301c03100c1841c243e613040103a604942803258000c02c000c030025511035403100581e0000501d041c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 104394046 1250 104392796 104392807
    0xc02060123090103060506240705100c09060804030c080316020d1103030112020d050d0512010e100302150c01060b09040b0a0f0902030c07060903050306090c0307020a11040f09080301030326010308 86
    0x81c0c2341c8400d01c0c4401302000c0c0ca10410409041801c280323600042e4200e515100306140b2202c0341c0f00b180225180340314151104020355103001d0702551040d0000700f0480800400354502d500285149010314010003008000680160038423030042d1410102c00d111105208100c6c2d540300e00c1c1000002268103440c203146201c56000f0040c404541395044c10180140240501c240e00041140d00901034150901400107900599030303600404020036005403002015498028000d00150900e1814075000345030f0451402d00e003c5111f10428210b07403054200c030301d6034880002c004c2407030316040c0903000901004965025903149816403106c95a4000d10490100c50340100004140410f014140c038400360300b1500511181a41e80f400825607071003100e030f481c45050960003040c515540481600e21584071500100b01008003601e501004d00d88129646902c90707120a100100402d060003884d50043c411000b89807203504615010341001034811241c51405800f9198400800308000d01c581141d4000400c00d92300c1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 104395296 1250 104394046 104394049
    0x3070c061101060b0f09191a181e03060a021218030705070e06040c0c030c02012a03021b010203090d1103071a0703090602031809190c02060123090103060506 69
    0x52580d13911261007484003150014400d0b044c0c1000300403902c4101c6203202003404103000b0801030101c81c0203520140015002d03140c000c5500704010840254410141c088400d031120018143e01c10403020700102810f0484450340c1810100720013034205035220010340c24600d09109162017603000074155280641000200080341c50203104458140d80c100050700c14154030703006610345000c01034491030302461401c10300d110710381c0c0324050402139a54540d0f42c10450300c945030011108201e8114843c803031400312040360301a603000303404241d0006220307401030b1411140c0c0740f1448141413074140c505419900b00f04000e846658421840703100c0030340d008131025510502c0001181c5841445c1d00810707900f04031962171032201848800a020b080d03101382d45180c03119403110742c12070702c9c0d0103003020300e41031010202150140d42c80d2807031450380e02160030041003500f0310b408400315082c4d5251401800141e00b200b401400800000c1003c4003c1c601c182c5140c12100080340042124100b05100180a03e940d600210749103 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 104396546 1250 104395296 104395301
    0x21008070e0f060d0510060908010b0a0603090c0f060f030605030105040b0402091b030403030212060f061b0c030105070906170c030106030506030c120106140906032812030506011103070c061101 85
    0x2031180b400c10403c0790341b8104500104680c1c00c0c0c00b800c8040b882410700001c6041c41400341c100c520b40060705500e0031a240c803400390043e01103140308842d032500f901d002044e81041030032040002c00079540c903c1b545a004410281c1111056040f040c026410b001c2004042180910900c1c5c1059043e62103080541c0c441c0c09020001442c0c03001c01d002c0711400400d00c800d0582c960041d0842402c0c03406002c0c03803510783c44104040c0020107003059401030030611030341d06841d0140302d01d00568008041902c11582c80080000c0c01c40c1c100311802400300303a50328010f01c0050b0344560121a0300d007005801600d0750034800b002140c035000c14415181003648580c00150141c03002d03c1144180040a401e04500080c8280d07118046c290700c1c040c030703001001c40c084080828a00401d003031b4051103002d0041d0011070b00385824840304503d0351902c507a100c010f0804080008051950660214405580002d0346040ca4000144020000c0020320902c2d03205209000c081185003982204640507424811781c1901c00d003001d68007 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 104397796 1250 104396546 104396557
    0x50f0f0a260a0c060909050f190e0a0602030907060f020a1209150305011e050622030c0308090103110928050307060e040609092409080a020307021008070e0f06 70
    0x540b4081c40d54010200403080e00258141c415a0b100c0d140d4442d2038001000440c0e0089404804440b004000300700c0344e11580008200e5102a200c020900b50b51044a681c41c01e8040d0908803186d40e4000708000034104140a100064623091400e100f0004003484001c0d900d5601c0741c401f81c0141c00c003117154a0a5809115030100030321812003100c01c0300f240f024010f001081e00340b00e01481040b00d4030b0302c40e4003400408100c4007a00c10050440e420302c000942414810200d8802840605025400c0840031030071134510b00005511811103d80e0342c40c100d200041c00e4400c054008045a101030000460360741c0d801c030448a48148007258078000d21950700010f696440c1c02e03449103425000b00303a0081201680015112000c803020346040c04501d940701620811118101030150882602100010400c0305552800c03501c0121058081022005034541540310b62007c3d80302c2c0056800058a1803c50814440040c10010142090310b401e03d0201da020f0280d0412800c0e161003960200c080d14410b80d104800c1d100d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 104399046 1250 104397796 104397869
    0xc0102090d0305070b0906100314070b0301030c0f0f03211709070303110c010507031b02150301090b120c22090c0524120603010b19050f0f0a 62
    0x2007505103814003a1aa5010b20700641c2e0700c0c14901c0018911407800a0001c0c0100808124410854a545c4801c10395001c42803a560442c058a200010500c9114024501035401260321010b21450700da107000c80c19400340d02440740610705120820200380072855500d001400ea080d20600e03655100c00440e51054499500000304100d8801d01c01496800540f40c01502e01c26121100c45004101070355980f92003030b200080c00603d003000208002403113114406850100a0707102c01404c80d60717a0016550200091000301c4100010004020b0308407503020f0780740c0500f0140c1e0381c0740c248407401404a45136044680000e001c0c40511001c7e00c0f100c04007000c44110040c03034100801020400c4d14003030f810390000d84140c40c81080d80d001c0c180c003001203110f9021201160748041d546071003022601d03c0c101006c014401640742d580e8400d580c0c410b4440106214004056034a40b040c0d0303c1c1810304110904424022160103803402c0001a041c5803101000c07041983c0d4611489048101e0b61909914145481c03403014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 104400296 1250 104399046 104399059
    0x140409090819110c1f1812050303070807030902010e0111030f030a0e0c030d05250813090c0201020708120a0902030d030b090708091b030115080609010b010e060307050c010209 77
    0x4100f58492840d10182025400303441d02c0841600030001d01980d4451040080f00a0480c003a285a003c4d03072a90500c1ca00a038140e070b503000c0c0e46101c90b03d1040804581501c60b0b030000410069040d500042e001d40c01b031658201045a00d2041e00003d10025001c00d0140c103200704c8503601c40b0906401c00595102c1c404202c41d0a94a160107509000506580480910a8442e10041011501e40810b00402034103040c0e554074149070380c07060121403204042441d0080c1c00364020200703020580300c800a0101e070f113901c0f4500c10114a054184801c483c143c601400c1164414040d035400162880100d0300816007000d1540095158440110000c1040e07000c000d62600c02c0318240f5090a8054000e204480703011a16040345946100081e98a1001299900c8103030704050b2600a625484d60001800b84102400009428413800080810205160043c0317001e1f41c0907908004990000b409210264030080c41c254509a5002d008100d09000c00303068103050010100320305003664001d60548026500c0200035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 104401546 1250 104400296 104400337
    0x304060e030f0d0b0f032103100b0f070c06090b07081b07030b0a050c040e07030903031506031e090809011d03061306051008071208070b01030813061404090908 70
    0x80c80100b80034100540117000c540d00002e0b041c60040388030603650050300040301e0101003455900e1840e61008081e0405105800f0010a04001641c00b810502918440d0aa940e11950602c034001d100c10390b02c06010041d0610040c04809408003d851805030b00880c25611f9103840a8164002c001c0d82d00506150702c20040f0000510018a904502544408200b04800e451710038508005208a00884030700902e00008503000522a5000b81c028a010303180008070100d14072800d80c00c18005074003071400039444081c044041c10707000c0041c0031003403500304040042c00307103a079611441c07070240f404c440381403121032a51035041c030032100120700d0001c02c0102691103514058503220610781d44503409891040c6040e000404c50000c1e029a80c040c1d92a80340200a000c1c600a040c400d05003c0c090204d483c64000c0c40400002505d613101c040c061803042c903202ea2a01c00c2c0801c0a00c0d1320f2056441141080182240000c03010a40c80c202d9056521120005c0f9101140d1f082c00001031154080c08107280c64003d40 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 104402796 1250 104401546 104401567
    0x3010e1c0e0d3005070201020c090702031204060e0c120d030504020303130801290a050402220f050f09010e0103030509010903080c01051005010903030e0d020d120804050c040c050304060e030f 84
    0x15803e802d2000b8600751144030360100b102c3d2405000030090140e40302c00c0340c504040c0345c0000944d910242504c11039140c04001c40740035400b0074050728110703449503c43c041c6040ea52018400010030f01d4054403030080c404405182940c5d84c4400b49817210915981d440801c055450510403100c42006880300c2c800b049948242c03050003000140560038075a440d4000d041d0702504148254501c42c0001803c1000090078181004029030184140000301c418a0a007503008150242c180c2000308001070081d90002c1ca030200780f0000130400501c0701d1040745054014414803c0111076a03064940616005440305490001680d0000440c0c1000c0c000c540f0100c1c107001880c0054001c1071184c1034040c040403290b030340c403c01510b20142c039000040101e14441c1101d0150b00b001c0801c4030384207000514251150556448241c0003c01481c14440001c83d4842048103200c001c006c065800402691304000081001d01d008101e0f00000e03100502d00c80d141d241912000c0e000b0802e40f40c181c1406200c0c1c6030340c1c584824 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 104404046 1250 104402796 104402843
    0x60d03110d0801150903021311130f0504140402100305060105090d050d140301080712051606050703031a061c0e0d0c0506101202010f0c0c03080903010e1c0e0d 70
    0xc0350215482c035200582496900c40c03a174070b20490707a02078201d00780d940c4007248540140c036449000c45100c036021312220f4030740592690305500518005400c20070040c00c02c401e000a03110300a5680c0d049a001d01c1c00d010045c1c4885411962410003454002010b4071180012140d52003040503099004008602d6075007440b03804a450b00d01502036495101446040314401915404244039102064100d00d400704007100c414040119210311078801e403860385403c0c05115456503c146c01000005102003126010550540300350030860301465903510000b04e00a00040062245480030200c00080080f10304005005802c1609542e9040003541c0180309000c10043c104200d95000342c43c00e1180e0f00c042000140340182d034506603181c924940c0c90f001c1d1250015222500c4a200501c10482d83d080c01c1800700d0381d19100400903620583c08643d890a40004060a6524201000010390002e0070404c0c0c9552090040a8404083c3e00384080f20000f03040c0010758103d0940400760000d80c0a6441881248042 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 104405296 1250 104404046 104404049
    0x9060503010507080403120e030904020301081f0204050907030209011b08091003050f060d020114040603020d06090212010509090307050a0501050601080106020a11130b030a1203051b03060d03110d0801 88
    0x190020010b0743d940c1041219001001d17030b4050007083d8540c3c41054641d00350f4001014411030745003140d00e0050300b40041800c90780242e10032407454028124201c6d151158144941e814506103070b0650415050034001485a04044c0c00f8400740f590020b0b8240d480d90287c40c3c403a02c0884c906009140030359160405826a0f84000000352203001110300c0c040e04c05010b440741e14012109010b04021555502040c0114044201ea041c1e061040c41020302908014020003440600301d80c5d41c016880d80e0101100780c094880d160041e690a500500c2400d500c018025442411035804861141240e156940002c0c01c512401c0e0014056002c1c00c4050400d2040541107070340901303002c0c0e03101c14a90381d035043e049031500e1807a07100800d00400d0340d44002c3c1c0b030724280c501485d006204140006030b601e00b80d00000e1800c000954129080540100c2d1502c1154040c0300713055208540fa54070050b00741c0d000104890522004100c41d200702071001005c0e040c14440c49503d440180c2a508492000241d4200903007201000d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 104406546 1250 104405296 104405299
    0xc030b010f090b1c0e0303010801141e0a1a0406030602030415050108030d05071b0f0201080f16051b0303070903060e0109081602030a120906020111041a03070216090605 74
    0x1c00e4206661074030940c40e25007202e2101c08039604101d0340c0e804000b01c0b00715038000c502105840b41e45505074000f0501c015402080114000a5040d04214414100400003400204c0004a038003510081d40041d80d003d5602009000000804149928074003180710341424003d900286494004010044254002c601442c010600d000f404692400d89070180e400900880c03c107034000340540d520b03000181d00106e0701301c0030764100301001052071100388000441c022000d0b1080c00a0000d007a003035580004d140d41e0091075101411005145c90751050813050206441e0070100030000580046500070030080d40c00c10800d82c010b9a9a07070611840041840582d03000640d5001d01d400e5040700d040c04148101150540d00c603102904148040c00080322618900c8c00680c1c2502942c0008000210f0b02514800500666180c4c240407604181c3d000b0b003129869a190a0004820841031100010000d03600668000020082c0e68070740ea040d00884c20701060820704007400d04001c2002c508000242c1002c4140c550 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 104407796 1250 104406546 104406557
    0x141005070f030612050a020d081207080103060c030504030e0d0602040e090c1c020904020111010902041b030c11100905100609140903070b1603020906030f06030601052d130c030b01 79
    0x440d00825082e940d00c4d118010603980c01500e00758014105011b2051010380180645820b01c02000c421035902c46089810130001201e1301c0050040200b01e100f80030100300b00c0e2804102c00c1c6001e076006001c3d0446000300c14814072407002c0c00420003040750121005000303151220301c42418803108090740c0b61000c009091103528042c0303011041003841d01c0b981d081150010041075041d100e40d0019204080090910b404554883c100e01c0050707191030080320001d05100c03103541546041d001c4010101c0d00e41104080030015104850036031500c00060b500b44c0e9a58050300001c06914628201d86480490400c00d040c06080c000300099001184d40100310400119841d00c00c01e559021449890b0701c50210002d02d054610b40110300100c103010350102c135003181800c006107009140300000d0121340003160310b020328040307580801c031440c03e091107018014501034440d0f4851220106455000340c4404001030b40c0c10804e07030600b9003181d0301c6010348003842c1c0145a0401c005c03541544010003030071b0341901941c007040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 104409046 1250 104407796 104407799
    0x40e09060c0c070506090a1e05011103090102071802090a0305030c0706050a1d01030e0106090203010302031605030613030e10030906200403110f04020f030f070804030c141005070f0306 81
    0xd108078100e07503804a503070001d0602d076410f2a080104580121030f030703107401240c003450203d4141700040c00d81100c0742ca040700c4000c0541c07805000510106014802d03505030b4005011440072a6000181002643c04421044c0d200c0c0301d041071110001d0040004207035201540d0a0000b0900a000c0028509052018161641e01d504d80400360782c18031404c81010300064650208980306d80c200358a50311140c505140200f03140011a91403402d50318590011041964004010000c600e4100310109624411003101c8542518140c0060707151b01e4001c013011003282c0007900200406120300d00e00001c418000740720810030300d24084010300402d01e07411308a41c8240342540d49440484514070122030780412841040c5403030300716901d00d190408064200d641001c0c11080c0d803c0156110b0020341b1212400360310b542d40b28a41507008003443d407805002d4a007480a00c3e4140404681d0000340c0705095508015007071126110b1844132460600c60a4101d450ba500d040e0900c12101d900004900b08100d4503a014490907 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 104410296 1250 104409046 104409061
    0x6090807120503040c030311070305030c0d1211040303050309011e0903021b0a0b221202090f040f0f0312090c0518060d110111030a09030317061003050c0906040e0906 73
    0x3e02c41550040c00342d860000c41080024451042c400900d00b00d0b034255100315a41c1d07558145140c0140c1e84500c0b064120a0386a10794650040e041800100f000310180018171400c804a007240c401d5005c0034040050000008180c81000d41000d000782a840640c150550070782800301c4002c0404000850050103010081c003110805c10318515070b1071070000c1403800d01911b07011084d80c5079400714021050100c520b000780f40346a00c1600c4044010000804c131884195150b2041043c15940184515941d400220500011030030b084c08e5071084a07400700b400d03030102c3c2103030406503902207014100c0e4602d1410419500100b0418120402c12a1800c0c0c4a01b031100c507111b400c21001d1402200d1850300039030030480700408240c400d00840349801c0181401420f0b50100c501450441c0c1c4000c4900340405d4000e03008000301039001014000000307803160000e00500703202e00080c5010300b2510164040544035404034582150a40854100100c0100620740d920380d00d041d00561024101c03031000940c0540000644403 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 104411546 1250 104410296 104410307
    0x18170406090b03150603090109020d050d0201050f1012021503070c0501060504230709170303010f060521060f04020705060f070509061e071a250c1e0609080712 70
    0x283e1310100354004c44a86481c14442e40d84c01c010001d44040d0340312041d000c0503845000c0d0040d01d160258020300785500104001038292407000e080c04151a1612040016400c000c504c0701050301c0f03041500001e01081c0340002140e01e54025a2102840b20000601400940003940401410301c600c00034000c00359980104400c0342c108400d42d00c038181d04031141502c9030407490500c9a000c480c506180c50701c16100c80c003c0130b180e00f031014400d540390b10000050040c1420814500001c03d0130380380040c9008075900ca10440b000120f00c1a040b100c100c0030100f843ca640301041e4800114018200715124811402c01d203030307164001d80c0c42401c0c00c1c4580022458162041e4211000f198010340560b28019264903c01c01d602c0c540000350519010034821000010159180e81d00480580b148084890030711156216621081c00040c103140f5149401d002c1d50700760441310158420750002c1418000300b060b000e003841c42c2e0188881c0102440d141800c1e410400c030b10304015040c43c0d400303131034000304007911803405944 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 104412796 1250 104411546 104411551
    0x601090504020f221203050310090c050403061d12280806060708070b041109100f06030c050408010e030301150804020d0609051e011a06030c03010918170406090b03 72
    0x1c1c0c100081010f51490203d20144d414000e107405100760015a50b00d40030215031051583c124002400042481a1100307040c3e49180603151243c0e00300038002c403044010307000707200f00d11004000d00d4443c120425184001070100550300b0810044e2107055211014086660307100c0030b030701500303c50b54181e0b076001480011480c45844409803540c1d000c40d11442c040003140d03080400c0898a52004202810000d460741b60900d00482c4038035100110116101c0030000f000302c1c02812040b180120101c100040101e010540048814500b4001480041c04004841d03a22494001c00420360034905550704007071000008604881402e6401844500ca141080f034034a1003c1d42c01960009ca00040300d8041803c0394000214644200c0c11190b8a0003410a01c9e60a4405609035001d2a55511070000b94441d0060148680b0070301100c030b4516500d02100c0b100180e01041c028015180c1e503588540041060051042c5440e07038200f0150562030956165468146d407141c01381d6000034500c14000600c040d41c0310150790 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 104414046 1250 104412796 104412817
    0x10209040e0d0927151a0403110f0904060507030e0a0c0906080d02031c1d0601090f020c06012907110406060306050102191106070b0919050a12120c020105060109050402 74
    0x30000d20508401c10180c130171201141c03851420200002038805000c40d90041d5400564291926a880c40c00c21010300708d0074464650103001284149011640c4070b101e0b003075020764400c400007000d40300c0d00b90840081840840c60015482200d44040604c03820308800400c940d5409024071a81791229092501c4195084040d40541c0c028401c15441c0408a0b02c0300d501c510340114001031640014042c0b452a05070340b590241d080c0c000d400103100c101424000c490740807076810343c15860950481903581e40e60783c052080c2c85c046002d46840c510008500015a0105669034920b651a07089506110805680d2074903601d01c42d03484c03e140050329034000d001d04401c0340c81c160098100b0034100c03103102110202a2808035032002c1115190f180541d50000036020f11406100195181e103803002000c1d241410200503000c400440e80130840029400080a507040d561003200c1c0486103145400c10303501070b4141013000b600c03507041000322a1002d90540c85588540026130344c14030b425a4500c140004c80c0300e40c01151 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 104415296 1250 104414046 104414099
    0x90c180f0b0a12031d0603071107090501120b04020301090206030c0a02060714030c18060f042102060f0f0d142502060a090f050f0d14040605030711010209040e0d09 72
    0x2c010a000b940943e00d1a1072642081017410700c004001009680f04543d40c6021075a03011644000c0402001000040d0841e4141040b5039410a16805540e41c22550700038204610381001404548081d00040d00721f603409000c158a0f42000d480e00000c81d045182413000511a500015903803a22841c00444038103030b0350085e5841c5031542204a205075204402e9415001880c216058507626680b0080c05604000030800e61501d05001541c048100c1c41007880b09109440d4103044003580d118800c44804640e0380602ea603030f030b0118441c04065800761541d10240203203807401c0b005c00e100035041e069108410799004016259105048041d403500321105c2c05005912500c0080c0300b8008690084103a82e008091018401d8095503500345400400f024280c0607070001490890b0658200100e50746405c82d1001c00b0f8202800e0240082650100074403c004000609030036001b8203400394111520901c0c0178000780301001c1d01450050340e48100e00400e00024007d18800150491b000c4841c9a400307141d110072 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 104416546 1250 104415296 104415329
    0x1141203090f06030a090512040801060906031a0603071703090f06030709090506010e090c0c19050604030c08040504051006020f030a02060f091c030603030f03051603090c180f0b0a 79
    0xb80400f6400050803590019516441e01001c144100b002c400b600c1d02a1240c41c4e5514140301c61142034403425805030881c0d03410301400307000040310144079038480b8100000c4021180d4031880040d2070010a58044030f105984851010103604011008009007801500c0e01c0d0031003503030801800f28901c000c40e010000560412030074020003c01e6080385070842c005241c00d14019a5200c0044c0d42040203941b01c3c1012000014004101710080c03005200403204c074a03803514550941c0d15800d407200340c014001810004985250303010444004182ca01030000038004008c1c2e46411040c0d040000c846000d00005031152202d0104454000003c40f103040e841c940c00740c00309031034084030050440000341034044c45000700d42c403443c1485c004802a840241032a500404d0b001d2960401508038102050b142c0100360402e030800110844a400745003c01e4401d00c1c00180c031400c80d09056074221016040008905613445051003131030705582141045004a0600b0494074482c0c80410000c03c450303204031840084042030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 104417796 1250 104416546 104416549
    0xc020906040b04020d0e0312090f030415021207030f030b090610110a020d0f110301140f1003080301120209010b03040203060103080f0c070b030f0f090309130f020301141203090f 78
    0x4244050300c06400941400178104003803044d1410391803001180d91020910750540c826034106c064003e00700201034620724207038185090b100d210b00c0c0280d5810120400040c2d800318402c000c5081040d02c2441e1450f102e017418070b80107002c440680006000281010a107800b41d01c1c0116025000e140010700c1528900c000e58416288900201034881003030080c001d00c100942c075004015004240b041c4440da8032000c0524043c15128180c8040600030b80c94003100314000021f040d0307103603000b1001c4501448a42e842d944949400c0c0e0342604014130101021000003024549100d003162114400ca42e45044c50b03072079412400d0b02d40011140658164841e4004201140d24440100304002c0c01d080351614100c2c0c002661458001340794001c1c003000c04000200900910f10740801c2c5d8010000403000001c0e03041c404d90407a90fa00544c202d062241c0980c2d030140780e498105e1390020105c501c4021056450350703960401201001021528980240c40205c20a000355070084221201c40800134a07000c08100e4610 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 104419046 1250 104417796 104417801
    0x1e010b1b07061d010e190509010603020307020307020d050c0a062001181209030501060602100b010807210609060e160c15020f09030f0a0c05040608030d0c1407050c100c02090604 78
    0x11202414040e075000d00d04103a0721a0a01c0c0c0386c1615103100300b20503c502e000280006400305a0000c8105803060060000c185c1c0d0200844440e140c0407206448018198204903040c5070790103200c3eaa001004120006030309401c4508500d81800320034108242214209446081c4d62100c0c0c02d84030700c015204071600024034179503008000c2d41e03410700d40001020341780d990342400c483c407680101d800b42c5c0c030110503a0707009062401108100a400e02c0c0c101118204141d020304050b030752950500622200300d000111442c8075134041002041002000d01c01a83d566420040940742900c5511842480c0c00c154480c20b4041c0e07007202501e5500c803851030f081e841010059002034003d41c3d030854030004100503103425540d003000401200112036000e440d100f804c0c0d00d418034150410fa80824001e9080040030010390001100f5101402c58460006c10404401c80040301d030504410000d14040c2c1c0c0103d170505c284480001c1c4c000c0c0703141d01918030b0346400ca03424200383d502003281c4d00001d600c14120380c001055814541c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 104420296 1250 104419046 104419097
    0x30d050901060503150f072109020105190306080f06010315020913020c160e090a030c0f0b070507120e0a1205120307030e010f020c0a0b1e010b1b0706 66
    0x200c000169075480c1d1001a082201c06804080b08140d200b09000c04e06a20b20700e40c0d60042ca0b94109503008001c8940d041c3c807200c40086a00c4d0700d080c0d0741e52400003036900840803a5400c800400302c40110f4840500701030020300060080071000d1144088818200c000003440e14145d80c0c0001411312141310041c0d10700c020307512061003c0e800c420034840703152414506002800241c08030101070820204d0052003008104030552000224900400a11030405404641101c1c4517401d49840030324040d190034080c0c11544002d10042803400e80908011032144d00c58054401d4500c6490302c03c490946100007215046030303442565502000d101020041d40740b5031220300805034481c000741c40240310865003035102904202e944501094a480001c54004020310a1031a001001c5108608100142110690310408020010f000000703800100b2901b503000140701096a41e4407400f03918540e1514604021500042180380e040301c5260204d00c0724803c007142036016903250741d507155011403509403c3c020305644ca = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 104421546 1250 104420296 104420311
    0x3091c0c020303040902042d060302070f050d03200a0f08180f0601080f010204080706050714060405011401140907200601030f020109121a060105040b070c031e0203030d05 75
    0xc03015003005803024805040184601500185c0b210f2405845207440d030b641c40002851050180802442401403598490035a0010300d001038031040c55140c1038030b40d50f6a80c01c01500e1032007120303403446101d64103801c4034200c0208040c6078250800260400c90050040c200c04401040100c03000d10003092268800550220844a465100c4903031002c22905000915100c90030b2508588014400703008200714460340d000c110402186814541064503132980c01c91700500c010024009410418480380c4001d4611034103100c000e070f03403890410b0300d8024001d1252080303070441d03166908000611415000d46001032104054180314469030b8064040380c0950301c203400082024811101d03156000001c01206005e103101c0d1070350412100a50002604018007540a18102082110b40d10300084100e90801c01407201200e15600549402d401681c041c0503035005540f5000e00402c0400502024000d07001c05c07a8001c1440324582d60325280c0c20b40c20b58400d020044d4042d402084103010160700381d4050741d44101d1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 104422796 1250 104421546 104421557
    0x302121e0f0d1a03070f140f03030f0d0603110904050a0f05071e0f0b0432041103180f03070837090e041203020307090306020c070611010203091c 64
    0x403003502e12030440b0100500c02200200f80c2103803510a003000c10503003001e806103489003983c003440e011512140d50f9040503814000d000041001046407001c00940740c90400980f001d64582c0d1603218035000510003803209031010b0030f10441c3c40015091509400340a280c0080c080d01c000440c3c0e84809000c04e040708400c44440c0b0400d03030006540798000741c0e088007225124404199181c58000440350504403600301c10903001d001c0208024182511412500c811000105a59500220f84610f4601c130000100c0b950082c3c1068446011501050000c40c46906000b803202d0004480c500c1c039a5840c41800100d40f0550b008001c94804a032511000d007403102c1000e103921130541c00001209001d405c5106049184000d0020b461607401d40010700d00000d0302d0001d84861540c0740580b00c0d000f000ba21020b52105065000020417040341c0725209000145030045400d550324480c106055503105458403408000601c2404001e0a03008103000b12030180300040e0003404241c0e5903502e02841c0c020305034010424042e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 104424046 1250 104422796 104422807
    0x20c0f0d110109030804120b06060a1b061103070c03020f0c0310090f020307030b040311120703030c030b1216080303010e040809030708010e03030412080601170a060308160302121e0f 80
    0x17440800104042e00c42078502d0f445e00e60292424008081e8041c1010f48038500c01c0c01440c40c5558071150b00d80c8000d031035107022600001c140c01c05500400009407a020300100010802681c00e8200702409506c034425800c41c2c80710203140c070044d078403103103168034042d030603040422048000c0341540c00c50801c090050142c400c00702c1c2c150740020300d420103075881114103980c1c4200700410725422429084c101c0104074042c1c9400e1641449004d4103202d107000c01001e1581c0c901081507018401d1b4408161808060301c1c00160300b04c440c09803948c1d01c4064924007000a084140802d0707140c4040150f03412900070068222040e1616078034080d10303800c4140c0d420b0b00742c8076817400099a003100b4000c18010722050400b07140d903402d290501d4121b01c962140b82e081406444014040f9036607103d0b080d58030814030100a90a43e8960700d40e02d0000d003216900c0502200c3c408107641c20b03241040014030251a22079002c4070702407242264407007a14001c141011040186030202890040107442c010150048042111480d02c07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 104425296 1250 104424046 104424053
    0x16140c010207111c0302030d0203040c081f0509030c0a020d020f06030109020415030e0606041d030d0204080609060105060409020c070e01090209130b0307210b0106020d020c0f0d11010903 82
    0x81c0c02041c0d00b519802c40b04410158a428442503104452103141129000c2200945010759a4891025202052355000001409228458041c00042c09075102550321000c050003180c8000100074071882c0030701d80ba11010980c40b00000045034500352440b409040c0111554080240c100c5a10b94245d82103440940110700d00c0da2518001c2d0301a00e014030005841d642003900b0141c001c200c00c4c085006051403d88074010300b40c1d00066240c0c0c40301045601191810f260307031000d5106001950000140c1c40085006140f646880d0007801c155031541302121710a540360460959135103002e210741600300f4810003062001e04c85a400070f088a100d00e01c102e8031300d65518461485865002d9202c0403480c0d501060034130f0280313070502d002c0043c64064903050150141031300c0041d441d981c8074031801c040903481c109101004014500b4062105400c10f1070000035694621340a51100a481d0501e0014040c943c850507451401540740301210f000500f5a40c0c440d00243d0300c1c3c10285409030b00071410f0003002400040003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 104426546 1250 104425296 104425301
    0xa05070e0f151219140103060f06030803090d1e05040302090406020405060d020702040f050705040b09010c02060a0206010f0b030705071103010f1a030111040e04120c06060609050f01030516140c01 86
    0x394015644242507038608213100d81880400020300341c80303003810300d07080300c10840030340d5205070540350041800141108040116001800103900091910001204000100074007041c3c40c4141c0d551130702c0313240110002085810440080041038008500140310a07c09403d00d04400c0b94072911681c00140b9098841002414903008000c520706229000141c250440c1854041c0600d05104000d0500450815000280c00da024038020071350184c40206140341e5aa209401116030650040c2c2681d64500c01240001c0d10307203409000e0b0100090050000141c08000c0100b224400d00203680d9241c1001035543d2800070182685462642c0f6648030142e03004004100c0c41510303191030343e01a65280c00800c110505081d00c84080e840c01100105210030010300c1c119003155613100794424414052110f0700102a501c0c04828080a03160914144000c220140c10255600c25140304440490250846500440c00d0356021291204000540f800750034800b0f00901c00c0c140d80c1e03c07483c0d00d640d040c804c88280e25801c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 104427796 1250 104426546 104426557
    0xa090216050a050a030f0201050603070923010b0d060e01061202070c1508010807050109031109060d0c080105040b0a09020d030c150903021b040c0503010303050307090306050109090b0a05070e0f15 86
    0xc0781e42080130907504142d006010048103004500080c4003d01c1c08000107a2207180303520401c920192200f041842c107040151078062404012003256060303503110100214a5088090030989036490300038040b82c200b00b0b6000d024129140c6030f0390300703114480c00210701c806034100701811100c0c15032035400414441d4004442840c8020180d50740b0855624106880d032800d429a803144e03062195010061000c2140300c05125a0360200b44c4400040e500c0d1040800c07040115984058522050718102080c02081904018021806402c0115098559013003e82c225591000000c0d4030079000e01c11040040d015952200940d40552a10342c4842001407140c800d0b40c501580860050b0012031504120118a070495a1100d0f025281001491155034000e0701510041c04050700748400400001e840c0380c840e15038a409194000401d10043d40d442d02c10f000500054582100c05a10341000105010b1031481428130070001551209030300701c076070030500c81c1603117480000c141c01c40040c1d45008100a10783c0300809 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 104429046 1250 104427796 104427803
    0x304170403080a021f0c020304092c0a03091a070209040f0203100f050903030720010906150311040b060a140702040504121106040b010509070e0d0c0609090501050a090216050a 77
    0x80e0501003032003070380c250605d4010034070070591501035202c800c65400001e840a80b040014001207103441452080444440b10704600c008544020031480c0d003003c08203900f00d8141c820f4540010007a2202c18402d699018000a000303420350030312110015141c4034000a400900406604148030b0290b00440d0500c0a1090f1010034140c1760322120042c60000e10030180e001a610010718290b041401c4010070b54184140c1e0f41044000b6030f141901d10040a5000c07040180d0301030400c210000031070440c0074000e441480b042c2c1c0c051842d103501c4082400d040c000c1c1504508020146403601c0000d040940e0112a0a4011149003905010748401038440e4813030305014600808000d03c88007965140241600d1685200c4203094108800344800101c01601d0281036400442c0d50307440e06c2d562a002240d05103c40400307664403105110381d00082c0507036000e1000c1524410b5560004180e1518400c1090722030038820203404c01c2541108010080741750b40a04003101122000c3d60011290f5125607151480d01c1405a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 104430296 1250 104429046 104429053
    0x207030e0301050a05162a0c0b0406080115020f070b0c0a0f080310060c030207141203071419020d0f06060302060a050301080d090806040b06040608011404170f0304170403080a02 78
    0xa242d00715440c02c000718092030034000d0780f000592150144101c0801c0d002c00300700894010408c2001c841b0810010380a0400b0b0941c4070741c0d0741d0f08024010340f03003031240342201702d0f24055501c0941c0c40450404580342621004204451601d1880d074010b0340241d0054180d40140e13103080000030fa0f0315405c03101c4180502d611f2500ca003010f2859000c6010075074001e03030a010716074102400098000c11000101d0f81c000c0081d00d840110b070f801103600784200c2c0c403070000c0c0c074080000d2074801c214411220b208210000021649060021810715240108041c4069840460602403000180b07c0304603d00c0071a20901011690f250b4940c0820403a80101040700b011800200050004860800010349840c545c0c2c80e200d203a0600c1c000d40c4a88401d0080c00c040c21210714000003922a40b0b59810042c0140f4080000f0080c1c2083c40205003000007064400725980540c20b00c0c81380410031a68203980d00c0980c120038244c9913440d1a612102c00200c03407040d008018006000010205d02c564010b4140c1040383d4015 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 104431546 1250 104430296 104430301
    0x703180f0b0c0405090f0903070210030c02010b010224090a290f060d0f0215040603090308010503030a20150103080304060f060609181b090303080702030f0a030207030e0301050a05 79
    0x16080040c000740b10080b41d040a02042000d50b44c0c5011143e08010521040e580c03d8850442e90340c00c40c40f403e08040c1d001000d043d24080215416407181e8140a102d0303000300304601d103880049072a8007080018100000700103500040d07900014000d103411200290440315003074051343c1c1e4071040e41031041001030524003241300c614600718800c40072359000c44000f0190440e450800c1c00074401c41840113001e000c40d41201030075000c54a800562a152100525889454680d900d0004014100540703080300000c41e102d00000e6141400400d031104422252607604160307882c5490503048c0c0e040050700b21a184654814840500002440d81d8042c50040102e00e540f031809081400c1034854031201c06950915200c010400075510038085c1d010b031103d00c1d01038185d00f400c29610310040d00306c2175512252100b40c0d2030ec00304101e401c042504201c920a84660301580d507202005e80e1070b8001d5210f00d030f040060030061604041c0c030990040c00d52500ca414210030403000180803c0c02c40d9030881c0c10895040d980d209 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 104432796 1250 104431546 104431553
    0x10e1507120f12110706060807061101020c100903050d02040e0106030e030a080604180b09010209040c0206040c050607030c080d1d0a02061204050a0b070c030801050a031101080703180f 81
    0x380209403454a0a095034200302ca19002042c0d400d600741d1005106984107154042849000100c40c8895040700d01400303403645409000b80c5500203071143c0800708007002c2c00300345012018002e960758920548098031a031440500090040e0910440031030802c030080000724102441440640040c1c0040014000d0075810640e01070115030f0b1551000c1030301c0d44207200c0542c00961141106038000800c1c0da0115503085c00804a402c00340e440c01004008440708800c01405c0a015400b03010400d20448081c0300d10281210305a88401060f2406030854003142414002030401d1030042002612a1030030080c0d214040e1954281b58211014642d212a1115403c90302e01400e00a000b021240020280603180007a0b40003130361911030b01d04007410040442000409202c0103010918155820001c24600c925020100030504520194110007140f00180089040e041504540c401d5a038481140c08407a01d2007001982e10035001018602019150549544103641980c1650007043c89130001e0002e011440c603 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 104434046 1250 104432796 104432813
    0x3010306060e0c0a0e0f0d05060f0708040b01060e03163309050f0301020c030c031312030e06070501060f06050702090c0a050301060c1a0106090512060106020309010e010e1507 77
    0x9110205049405060018910080c0102c900c2404c00d410b01821400c14480072a46243d80c0042c403551100301441103a0501201048040c4507402003112818103658900040c1d07142001078901601c640046401440142d0140d0198100f1840c0101180d00348008918661001015074200080c603920706101016a4034501c44c4c40d84100008604502400c0c00c400c1d00200009050711555216086000c003543c299103087d81150040041042a256543c11102410f0303981e0f8080d11101211100d14400010b44200c40022464000d905a031040c14102688082045980203110151415542d40310300140c40c42c60b582c5580000c0c0911b840791a1294418010000e00c5440101060001c0740d04002001c4400e034003804607415108a8186002180203900301882518121b651743c40341d9448480001c6001d03600302001504465040b6002e0b00d40e11014031180740c5034102031046c3c0025038010300c900da41c04c0d07001e040345205080d018036003069a40b0b0030800065000c84410040041d003140041d200043c40040b0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 104435296 1250 104434046 104434049
    0x82e090b010c080d090f150c0807140f0a0e090115030b0306041703040302070f0603090c08031603030b040b040204090b0910060e0d0303020c2d0a08070b04020301200301030606 77
    0xd00b010401005661603850b06881420b1100c070a055460304a41c082204c1715814012141e0412140b000020302d14100500600780c0070344441c0400c10100015151b280b04010520071851503510483c2020b0881200101682005040d0402d1200c600300c03d000070780b1155043c50081610b640b00b02c940d4640600c000d000c58150025071070107034100c0b408110104200c800d807002c810a05000103607403036495042c12800c0807115000088082d001400005082d83e143d000b11228a021314210303a2460785c0c80301d98594a00c81e10482c40e070300324038a0b41954086800307940030381e604c01b101030400f080e0010a070f0700280490380103030403100e15582e460f5800403160410340e40c002d520000f06171000c0c50070760070704001804a00b5060b460a00c0b032100300c5078000415100c1e070181c60020200300b0480f00a10400c0c03110f400f0100100c8403850368100c040032000000c1100003a110b800a805c622141d24201054484034132410000304266015074072002030140c00750130040490030068103205c0c030315165411407802c41e0503a10203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 104436546 1250 104435296 104435299
    0x3050a0f0c0e190503070e040203010b030601080607020706091d0601030605030f031b0703081b0c0a06080702150105131104030203070b0d0e0102070b1303020a05070902070b06040603050a0201082e090b 88
    0x20300764103004c25100000c155080e030b11a40040101581d4910021f4054201c200c0281c1c1c2500440c0300000c0c40940000f002c83c0100100e809481250740c6820048996615510a5038010a0040064840d1905803000242c0041c03041c903020070300c50307150340100b1300d03000c0c44205050700d940c00028920302080358038a405041c500c01d40c024004452464948207114040c1500c0300c1c80800c100002c411800c801000300b4410003001610080c0c11a956042c054524070b42190308201500a00444041c60b248010126042c0c8600502d0400030301031009822005090360080382d005c60100300008000340c0e8003048050001e00c0c080000c690385e001b4201d80401038656000782442940c0c01406030034001403d01f00c21301d0b40b10190b43d500001c841006d09049241058000b0090502d00880304089128610f070b40040c2101400703201c0382d4010740c03500000d2100320f070803070f01c400b42c400d4025220745d40040d0b12811502c0e03002100b038808100c0c030b41d80c40f0400849441c804214800242004081045002d0040c018000343d03500 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 104437796 1250 104436546 104436589
    0xc030c021504180912050a0324050f030129010216080d11190f06020d0c030b01180e04080307021f0b0f0f0f0f0102100f090605010506160303050a0f0c0e 67
    0x1581c0d1440341e041810740051701480000300e5000c0d070181c801d50002d0120030303d00b03001b581400660000014042c1e454000c65004072208003030030040342414002c24090301941c0820700103101c40040800203000e07041d00c144d030450146054000f404801e00e0301820103400000007400070a4155540640703126004015000b854003c403442c0340c54110999541d81c0d95940080b00340c0156811440c14070024411800310380f14071840c03e905007000a90552100c14100c1c82030700c48194804410003200048607881c41250141c080390300010300012950405107800c40020700449004801803d841018500d00e800304a03070259840c0075007a414904103112003002001514080d03004071054000c5050340604107130081c015000a076041c1d000d40d100300203106e492480c8410403c0b00c1ca13040e00c82c180181c100d0007001d45007103040c00d00101c2d05190801c115144c2c3c6009041c1d1040da40034554050300900300082c503900003076a562504280d81e01242c050341c03101d0071041ea1382e032a0017150601041280d120081c0b85562448 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 104439046 1250 104437796 104437811
    0x601080106021005040819020604020103180b0c18030a0f06050f0c2a0a030801240203030a09020301090b070804050f060105030d0e060921011406100c030c02150418 72
    0x1500410320343c45054038020003003255919401c04440300c0c45115500c00ba01420480340158041d800f1074118000ea1003668280442e81c151000b4558450415101610205d40b2034041040f407242c4c803004021481c039003008181c1d91454840001e041001c501003c1d60f4419000800301c040000d180310f15940013508003103495003810300185038030940c040c40141503074a012802600d10f10003444038804660924180469441c44007502d0024140a0300f80303e003103034000580d03007000caa0100700313502c412004035217600640c00d40e5506031000015164400c0141c1c0c0555841d405900850714285540d8420f00141d1034803001410903250507864504203000005141e04040014445550b000c94102201c41c02d500d0f01c0e1106480c10400121030b8462810743c140e10604c1c20800c04410110074010b04207600781640208403200100115900300a03049420a41c014828100e03403100c1d0340102000c201c0e507400f03860901e010b58066804600c0441d401c0a00b101c1c010400301e4200708142d1000640300003002805000d00201 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 104440296 1250 104439046 104439059
    0x60921070c05010507060609061e0b030103080304031d03070b0703080f0603060a1a040204080a030906020601051c06020c0609060115050c060a2f04030213020c07060e030a05030c0706020606010801 86
    0x9812034003402e4108400064801c1c203214542c7c02174406000080400c001190b61800e600b021050b041c0e020304400000d02ea4005501d40e0944107490490f50400ea8183ca184e0707503544c00312500780c2e4a001c40204003890640220054604001c940d010b03040981c1150307034a2010741405041000f000300040d000d40018070410183d038801241c20750b040015031a002c91230f2048108000544104050804d8000c0e00c04500054401c2000800e200c0301402500c4400401e515a01c08030b03111042405055040900c24000300440c442c046941880d4034000c0c28014117000c821000d103070804905490010080c0d0103500148110012011f280d9a8550030b0304151b881c100d405004a621a000181660031055455501050000c4400ca00010003d402da2034800400840fa4241e4040c1d00680026800f03249403031842c41c05a0302c18801ca0700041500343c01081a90324160040780c801d260002c070b05405000d60b122810000c1c0d03080000d0045001c2c90300c0503140c1c00303003071070002454100300410807410020701d0001003112 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 104441546 1250 104440296 104440313
    0x4060512150601030b04141b12060607030302070602070c08070f240905130203070212070816060609090809040506030d0906032304120f030c0f0309020d0506092107 72
    0xc1c041a800200c11503541100603001400109400d9400ca400c00100100c01079545c003801e0b2007170318144005c0c622004144240c810717138010310780110031040d00c0340089529880c3c404043c00070180b003071501524001a40d619101a80c0005604881c04026100c0600c0100014041c00f400303028070000254000346480d0300c0c10b450130202c584d03010301e192800102405407845490044054071000e49501c82594800c480580254001c0341e0400040c014051031580c3c04107144112580c2d0303500b22042c1800c20090408030300800f00704407070849440c5e070368110014101541d40560403d1381c0c00b0f400c03950b490762941814002076900c0142030504c01c0c0c122540c030068554200c03c0300000d44000341b03000101d0003103104107090a0715100d24008a0080c0480400040240621001201c01746540d01e042042a100c013040c5c0c1aa80715814103008155015142d414051007503001049140c002018101d11400790748502e8286a4203503408101c40e00540904801141d580c594403003940c0411075500e14000d1340ea00d80801 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 104442796 1250 104441546 104441563
    0x60503030a090521030a050c010c021209042a020d0305090606090117071809060b220b060403080c06010305152203030b0301050f070207060c11210a1104060512 70
    0x2c1130007840303d494040840c10300c620090700b04400c100c0343e0b100c0780c894025209810482030f2201660800c0030610f590f510104420511441146815040030a00c400300030141040da0b6812030341d02a0b642d40120038540c11000300b506a030041d00640700000034140020255038005000d8512a44844280300164031068003050444104499150000143d4000c0a0902c0e141ea0b200c0190b0450140c00803400700c4c665408002038a100c0c0508003e081041030074802d494690f425002501c9510011802040071550001c00595030010f0041e450f15840e41c1d5600c446420a000b070b034805a01c03210040c4100042003120308010b00c1000400b101f43e01e840000641c0c504501440c80281da40c103d4114401c00d4000c0d00300490380400100240f0a514000c0000080c06004880c0400188a100f8001600368041d01d80c0004664200c40250f15150364041800b0385001c8520200c8505100c6103080410404140803c0c3e242038801e5440c1c1c405904d0f0501000b0a589160b00403600c1540708803041d6030780b0003000510790b1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 104444046 1250 104442796 104442799
    0xc0f15070f141b070e0717070305040f02040e0a02031c0201151212030b06340203070915030b0a0203150f0f10050c03040b04030b0f01031a1003200103060503030a0905 73
    0x200c40f90500c00550f07042103000c0d0704c00080c2120001c203010025800404054a42414125001e919580c120049054400c15503014200c03c00c0e00794000058205074000701d940d0415401100c915042c1580440c3c43d00805000c50140160807440310400c4036420b029001b40482c4904030701c2c4506040c0b0161140081151b030340101080b0025176000c04160081c0c002e0846c20b440103005d00c0d01c4e42070301031364811030341e800010240c60000448242003501c03e14009030b408458001e002024254105031110f002004c1c002c42c05110720301c1480d4000009040740000c80e115403090301c40962a07040c0104d4002e03a40030410728080c4101c01024500c0316513281c098504080314403c8840300c09405a01b8019141e910664080d29031078040050081540c5a070203000744100d80c841c40ea59040c40c1d81c0c2180c0113124440c203002c001d260144401c91080c0041011203400e402034841c8180011550ba29521001009844643c2c1031010000c00c03041a212343c0c0611401e8000d0000740c01a40ca0907061540c01480f9410b20b003d5503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 104445296 1250 104444046 104444077
    0x6020105040c09230a090c0618030b04020303070f0821040b0c0a18080f06180307030c0809030a060c08070206160302071514190204050105030601050c0f15070f14 71
    0x5040010b518458202d000495084001350400203007130303000384c50740c10f81c04c0d12406404500014114482c4250b608001914030300b00340c0340c41c1580d980c0b00c0b143d0300150050341d052006003d5003000c5031054a45d0702c03840340304842c00d941d030f0034640350b03101402e200306011074202c0c14030031082001013040c50910607481031703880140070350302c414100d13050710181c1c41441c480d100040020000708085000080c03807030b44c00100808403420340d6030796802048004a400001d044075003092021100080c051001c59101c3c2e80700c1c100c0c56040a840902003840c0c0480e03032105507800303030300d406981c1803440e004110903070058200c2c030240c8201c1c13400500b8005000c2030341d0709081c20594005030507024441c801e0400d001c02851044188004502c0c2009001d0403801500c860b10041800d03a03690444e01720324070131601100c10684500c0c0c11a900c0c40c0c0151003540282c070705031200340508214007000100601120305581029000e0b503400d0f0a0080c0010702140f00661060300740024a4264500c0d005640280d400e81d03014140c21 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 104446546 1250 104445296 104445311
    0xe070c03030203271f0216021005040b120103060b100804020909030403080c010608010b240901030b0607050d1e09030b04030314070e030d0f0507060b1909020c010606020105040c09 79
    0x540c0c00e02d42003a000c4181130103080d0314510003e5010030f0000703011921031041021403040d030100100320701c00c0001005201c00103000950040c100340002a0b020b4481d800c01380e041540e181040b40b45948584451f103002c04020006000b04071240c410070000c0c641c2503854094070040030741d004e03100c618040d0001e4401c1e10810001060f444007041154091540400900d4860b2060704180d4040c0c81c00c1d02401c1401e50030002d682c0b81c01c0c20210000240b454440901c070255041d049103100e92030b84801c08042c101500c0c1c031082a10350f25110010301e5a10f20510040c2264603407094003c007912950a0000795010500308602d40059108803440c1c20340e5040851a00c1c03030f03141ca243c1a001488010380c0d400c0030341c00318030030800a00d41040664040410540544003101d1142d181251149014003140c80481c80034480f082c0494281d41c0150b11440020340b0b034200d414820b0380304200580703803030741f01c94821a000103043e15655402e01070500249840c0c0000c5c00203081942d0340040d881868010751350040e69680301c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 104447796 1250 104446546 104446561
    0xb0402040e012702090115120b040b040608030702040c11030403031d0306090d080a0203010b03012304021c06050d050c1903021008071e02030306100215010b0c070e070c03030203 78
    0x8010720361104140d280c03031243c0116200f02c40c6180c00c201070388242248000016080c2215000c502c9610031643d480c1204001200d54400030b1008004680e085551031030000703901c0c0c40e02e101c0c11b4081c0c4006001141c82c0c003c18030400081c4c6402684003010092800e60201c3d00540c000185c034192680360401264620142d00030100f0501da02d020594548503010034080880404603010160303b0046d07840114594a81002034144e02c4203204910128001300010450500750107800c1402c00042240301d1a94440980011309a800c94440d0580300c0407191001c400700d0703009116402c000c1c80140e4191450b446107440340c60b03e410010309683c2c0204040100d4a002e12002c3d09000051070b8010a80101280140d10050a0305001c440300e10111700950301c620080c0540849030b25010130a035000b0351071a81d0b03000510a0610601600e00107610640000c82111008042564040c1c5202e2428549503a084880d440c41c180c46680441e001c14611018400b503642c1c002040c0800304e0301400c000d69251248003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 104449046 1250 104447796 104447801
    0x203190f060f090203100b0619170708070327021c050703050109020103231503012d0c0c0b060103090c05030d0c0302010e0c06030609100b0408070f120b0402040e01 72
    0x910041001d807408021811126055120000141c002d6003114185940000103004850500401e41c1e40301a0a1003900f07603000407420541500c0085152080e00300340c00c134884c80e0080100f0307114036011030186070400c9440ca50522900340c5400141c3c1e0860745d40440401c0408603c6450000a405068210203012b05090044070010141d54020304685403d80d6a0402c06d008040c0034004900203420010071003e08130b40984202100c2d00d501040808540b0f4031480c0703013690030282400d543c055407105c26602c940248501074000384910a15044410504e0386080000c4810074030490050069500c1e0354800700c1c0c1c0a10615900ca90f0a00300052414800e0410b00c011541c2948030076130610500025001c0c079580034900149051107900240f00136021241ca880d1032b00c058101954100b0011f1000401c28501081c4454008072000c03640c0203142d40782d1010341c605912a41188006030b01840e820800c18240740d2000000741b1030408807010303c0c20580c0d01c00b00307041c40141c00030784203540350007052035804402c0d03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 104450296 1250 104449046 104449073
    0xa020a09020a02010e030c06090601050a030b07110c060d05010f050102030309030301120302070506030702100501052704020423090f03120a09061517010e0105060315070c020a060816020109020319 86
    0x58003107d03126545400000e40d1844219140c0005008560000a2605007aa10038041d00d0384840c515190f503640741022070b60418101320011441c072680c4450b00550702d90500904c0c01c1030314a0780114096040c8400505501c5155208504550040080102510020003500d042d0303142d80107118008a07a07800c0403803038000c03990401d950016001040c07001440d00020342026881c082e0000b03010030381c0d0b1340c410081e40c05440040408200440c40d000310b46a529415210740c014070080c8001000060030010113000c0100c01c4110250140d80c00c10f215400c0402c00c801391036186e1f00d40c021460315015002c2c42d646004080c01800c00151034242c544100906a080b905c1c00c1e884515540301d02a6413298881480b03500d80950403000e5180a0002105860600442c0d100d000c014004007002800a00210814100180140c0801070000880d10040c1d8880b800c1c0c0004018a58800c105801c26a5080070440c210070403031425689010510380c016100070604049840082d1900300440e40c039801c00c0b500180d401d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 104451546 1250 104450296 104450321
    0x5040e33041410020f0a030b01090e01090221010909020315040203070302060d0207060c120b010305010503030702010e06120f0f130302121e03010305010212100605070b06010302070b07030507110a020a09020a0201 93
    0x840d045c4031000030b8001038030070441c41d42d40900c1001c08002c019689288503002d91695000ba10005200c0c04a40350000c0c481052040400700007921a8540300da0341202c00c1c0c1002c0f40198031001c592065242c03c021401c0746200401d601c3d102d505003540000d0307071881c19100090060802003414241c200880d81552917564006070140712003c3c0031306004000d6104c1905c1642da141c58000e613403099520070b211f264180c1d000a0019032401441d60015200c4c00720030b043c1e05500003000c10480381c01a031310400c0b290040c0c412156101090409400c1e40100384401000801c1e440340442100e404250700043e002211381410134035641d10b030812110f588a4046003011101107401c000000410044154010314076407120300c06806603603c54054010002c9031500c00d400c0010302c2400800042156100c80c01c2d0040414140180b52200da60f441404c03e60003202e040002c80d948404002856400002c03400c2d107114001b016100e0700d800350380080c20070384880c0515030040e03502140e05c41103c0c0c001d5204c0c11030b41e0b40 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 104452796 1250 104451546 104451551
    0xe1003171909030b070507030e04020d020408250b0a0c0f140a0503030105040606020c010206011701020d091514070c0807050f0726060c0702011805040e33041410 71
    0x101c00540103650500c003c454988145001501d030500c61820b03988010f62503035032046020380344030401010b5009a90b80101c0558200000210038208000014809041c01d969803116201b070f24240042d0200750703000c20002c42c2c0c1040071080903584103403201d14550784075580c004000d009003012000081c000c080035143e80720f007002c14030502000002071030480e02c040300c0c02d00984d600d07400100d8851010b406041d0140c0d00c000014000341c3d14a0840c0015881418001800c01120007610300950b05035500c00d03203004e260b03180c03050741c20b0311107000380c02c1c40685440d049020703070514038002031035a191041c0189c1306060224070304080040c01d00a00480030400320480780c0164441002e110403c036100400d202c0c0c0e040e000746501d080c2801240c03542c89002c0c000110780c103280140d001552004501407195140094000021a07191343d00e1003620741c6864020300500c2d20b00420100074100940d00904442c0940c246145c0012230300c640780a69610503442010324110102080190f840e00c1e0406024204050 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 104454046 1250 104452796 104452837
    0x60f1e0301090f0e03090906010c0f08120403020c0f130b04020f19170114150c010e100b0603060904020f0a090c051215090705031b04030501020408070e100317 70
    0x1072440c2c0080a00d420b00f038038100010403e24500700c3e902d1140210198000a0400c001181507005007003151801c1e000384000090814541d54102069000703490300314103c8604030522091681c100940c00121400b030358502c21901c0e1840001d8901c80000b40640251921350181da4196155501550105100800402e442c1c00b0b0481d00c440d10f02d07610649400001c3c1c0001c0c1038040344420b128455049608400810302030041d078a0511050800d11440e524111004004240062400344103048a4880c00d00c0030340b810501088404c011707100300803041841598140706008441d5540001c440d00160b045030201814505000410744c100b0f5294020304056107000d019540c01e6400c0002040e081041100d03d041994a81040c4040c209042c1e40f40c50300b07c6090070004070b84a015100035604a0130081241141003140e81d0091500d40c825001210141d4010a0400c148041004001c015040031000702e40c080c54850303041c1c2d00c0181c0a2001400c8612240181c15048004004480b9a00b05800d10341c104031 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 104455296 1250 104454046 104454059
    0x60a020307090f0b04061403040b0c07020604030b07020a0501060603060e0a0c03090c030f1e08270a03080c0c012c0402090603010312270e04020a050a030b090c030c060f1e0301 77
    0xc5d0001d1085101251100e031420070044c1402045030322856011800f4841622030800308039807500054422a002081000040007103214081e90a128282c0d5034002c2130700003040c3c5003003070a44055a02c03079403d041c01c01a06010500341d0141255100003001c000145003240c40741c0480c06130554902c081c0107101c0c80c401c00310500c84088801540300d07020703034500072001a0203e404480310009400262416030207101c94107010031420301024107000440b01c03400728100048006040b50351309078400c170780382100080c03150b134040c0381444850480c40007401c00809110f52206404010100b4a030301040c580d841502c01d000795941c070380c141c41c2c6200000e025aa242d686a00d080c0701004403100c1100042044640c414070100e031907000d820700c0e80401000a1140501c1c05000310f4843c040600b040b81d0120707401c0000300d47ca4980c4440c0c0402140a0711503100f003400d20010481c241810b248a19009402a104100107030325a40c0890706030803140d04450fa902e244861542e82800748691034040c0c001400000083c13035 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 104456546 1250 104455296 104455319
    0x70b0c0703030c050a0921051e06012306030702150403201b04021305032d0a12080c07020301090303150f1d19060f0609090e060a020307090f 62
    0x32203109480070081e8402c2908103a40600401032000001b4400c0c4805202d00e02e8008280000d40f003941101c00c8284849980c1c86042c070402035400c1800c5420ba90054105000406c9014014118a44c803080d5054110011003021034842c1c0c1c400b030203034100002150840b8401c005001200000d000403484038286482c1c01858042e0b04c0807103015a88c9a80f00c945680c61000c90400f0380c071084040860404a001800d00c0045c0d00035890f682035075001184001040d4030180f2410b407042c5440e4103050042113000b410031001a0f407080d80099981c1c4800028000100b0754006803200b00c0e0035041800a07a5070f3380c4a000a54807440c4402034140d42040c490004268243c0c120728110400d25654886060b21049030007840e03c800d01c1740c40d0f5a940c001c40700900716520090840e4200080e401c0308100c80c024981e2100c107890459000802d445580d0004012180d4846000c02c0940500c42043c0b068000c5101401ea5419003e00704000440e03000011070700341030080700180c00416401100d22580c0707586213202c803030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 104457796 1250 104456546 104456557
    0x10030506090c100807090911041a04030620030a020304060905030703120b030c0d1502092701050904030203180604080d030f060801060302030a030f030f020309030c1e0c060f070b0c 79
    0xc2d00c2200c11a09040c1c0c06000304c40d116840c2a541c0019940c51303c03036220080c4c24920340b0300071003980801000c00c0e0514100e541d500d042c4c600c013400c2c507919451850410704450188100c0407480c00d07000c0781000c080d103c2c0001c40c0c0d0007481e29040940c980c0c856042120050001d1140105144800103e0804041d0000d034190b99240403114100241240003003459101c200c0c10111641c08111055504006101031007043d01102c0da48800606001d1504041101400c40c50750000d01e80c0b030501582e184080c03890040501400301503c94003010b04250f50065541d0055038440750142c0700c401e00f03441e540c0d160a403daa0003003030f00104564a2280d10000034004054000b4120a92800c0400116240205000304800c0f240e02900800c487d188545045802407071f4641981304054640c0c07082e190a0f10300340090b42c0640e040310302440d55451148207051803c0ad5003130686903ca8400c04107004046408549010300354800e0b1011940c400766101a41950700c1340d620000d06403180c8000b0b111842004401508 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 104459046 1250 104457796 104457799
    0x1110412020918030706090809090709030b160c02120c040f200c1507180e01080c010309080306040c030e0d090f060c0809060711030a0506060a0b030f0f10030506090c 73
    0xb00c1c0368403807503c1900e581030080c000140c20743c810045840006d08551001c41c820f80141c0400d418040381e0300c000340481a050b030f030b924002126102d0a00a225010014540205056004d21a942911031006d460140c818201034032649d807c560f13000c0105418001c00390a80da0082040155001d03511201c4010000c0303c0b0403076070f20a8508002d04408010808880048850070010006040e160030600d00c5401700809200401180f07240400c0106101183d08001e00120075204000390b04105516103000d602d800081e041500708030a40d00443d501c07100704d03034102070305490100309101c00b00c4d030030790241c4045000c0c966103208203007081109940c4000d004054400c030385a0300103826502c0b5022200d02012a01c00b170318a203010403032034001746007120080c04020b10400311400d00101c414006130504805501c19203d40e04003804100c1c041c5040800c0c08081c2003100c00749810760601129910001400a2042404c031101c2004255100c1046c0000001550710004a40e001d20344411816250811940f209 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 104460296 1250 104459046 104459059
    0xc060f0b0d0b01080c040204080309060703020f0a0302011a01020607120b19030b01030b01051e011b0204020a090602060c040609030b18030a03090303050c0c0a1218120c0b040e04060207050111041202 87
    0x5c3c0c500b441e003402101c0c201d90305134004506101c2c134801000803a5000d00c00450030361268024074400d0304010304c4150348250085d0000289524940c400c1070040005038005411504200c040200e02c40d0000108100f40380c401000084e00d001c1d031030120301401d541c0880c0c801c0d0000b40200c000100030035111181d068074410316500419917079132014400103400610312178038140306210b030f4880154811000c02070014004150700515080540100b8200d901001d00c0400082c0c5841041c40865010002c0c41e401c4412012042d19103450190010042011804020000c100303880c04203104042c0c20700540c5610507100260b0799990170f0308002a00504054000320042030030300000906501458064402c070b0b0321081d018115403c0e8540da80c5c00d1440301c404840c028411802034030b1201c003d141401303201a040490f01262143c060381420b1b140c440503540000e070504d404110520480680760300d103507040350b4054000f40e00c404071485c03c5409403812501c2c040c40c005002c03070300007144c40d180c0e034002c80418003e6506 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 104461546 1250 104460296 104460313
    0xc0d1a040c020a0807080a020703061a040e0f1015030804060804030905010801050a06211b020c040c140c01110304080322020a0b09010c0210050307080f01060c060f0b0d0b0108 77
    0x243d84a00c0c202c280074103042001d00140010034201c00007000c0704a024410707290b4090326580c552088480e500c044510751140d44a00381d085040c5889050348011280e4024100070b03615140c141d035100710184c0403d0312140c40300030110035860240064800746900075895900d842e00c480008100c0c3d0403c5605034000380b402750b40080d217940190443c50603110007410001c0181c0c00e00c441640c451000744920005100134192510240300548507026030407a141c0c055482400301c1a070000d261035400ba5802d445a46012410000350717410102001d40e20303805007800e60701ca201014400307005100c0b00231130807010040001013000700303c684401907104803400700d078424604000615080c2c640d01e41c070000a4000c1c540c00020f010190075800070b001075420501d045200391100d540810810b00340e0b1101d02c0c0100304040240002c80d03800070b82855001000312801c8003558903001004100505c8400080c0a5907590302d0700c090515a2600701c40b0080318040c100d00880100d525207213942940910038603083d030180342035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 104462796 1250 104461546 104461571
    0x9061e040b09040b09071e0509090a150204090c050c030702120a06051e0c0a020a1b05060f0a080c0c0705060d06080303090601050a06090b0714070e0903070506010f0b030f0c0d1a04 79
    0x1105400207d4400b0000d420505190a008946c40c0c0a481d20b0150711035002c0d10300014803880c1c100645c16a1101026845502e00580300040e54151858142405814480c48045510010550301c000d80c04a82c2141e409000751441c40c102682c0b81800342c50301e402d060801c0059400d0319010b51440f0300c02c05224410b81e4484030904168010103100c0d0300180c0106510320041000000481d0527880500c00300441103980d000029200d03030100108001c10f06004c81c0301c4d81ca0319040b003100e540c40004c1000a034605a0809242c50b220201401554455400450b0010b040001e40c1d02c1040504001c00480742d407402c210071890b6031420240f04003072040350b40e0350011035541d100f80b0001d41140e112141035400c0102503601c5520010306803000700d00c41e02c11140700040c0e01d41710303400842c05450340304059a950521814800e08020050708203004020310a2010850200007108490780b201003100c0c9134500340c4401c05090603d00c901d5555624060034542840d03403400444070091038070070040f14104a00d007564070 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 104464046 1250 104462796 104462819
    0xf06010806011d04060b070614010603050c1c020d06091b051c0b0607050a0c06080a020306010f0804030306030b161206080d051b010203010605120609061e040b09040b0907 75
    0x4a10794000703890b900445180007400032a841d540a401400410200c3d142c1c0f40c101380340d4019020a6501c591140c951960110003082710308c1c0505030b645400e211b1844d144130103410501c6004048140703038107a40c40c5010107244581c103036100c102980005100c0141c0c3c5440030006800900115481a2001d110180016010344205d500c0c03404865121044410103a017030b038004141c01d410f0140c002e603003003100c000040c1051040c000703c2442100400f42160038a4001400e07004028144c00d02184100107101480e0b8001d919440703615010328094030309503180e00e0100c021b0443c43e030004240390345c0c0d0020701400d0baa1034041d1102400040c0e40e07500308007120041c440c0035100d0501c40c0e55080d0308142c0907a041d0a10510040600c0d450300000314900c041c0021300c450032a403090740714030000398002c2003440c1c0f800d0800d5900c13500050304559414042c03d103d000200340411050381c40a2828400c8907045080d02c07243c1044180c002c004122810526090a0604940004403004050703070055813401f00344114460f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 104465296 1250 104464046 104464051
    0x1030b032d0d050c070b070515070c0c0b03090f060112110a1a0d11130b0d1104031104150b090d110301180b13020616230102030f060108 60
    0x8005181c07000e8203650301400348103031a0a01201c1d20700c0c050000052001006840b4007680aa50b8556480c41e90341d080c542440704039045241e44500401405001c01c00024422441c901d000d081c1e0082130302da003d03045c0c40542140c03800400042c4e40b100300040e0146084041c45c4245000801d5407204030300c440102d501c4007801d0003006414100c1201010100380d0100d00d40055880c0500500d0301c07280c55052000021080600c10003c0b03100004d070708458205213008201d040b1600402090402c0210700340c5100049542c06190801400400c04150200c50383d0842202a010b242515075515240d04100c5001240e01d0f8a0354000d500f07088400b0310302903102800034101d401000c410f504108115041042c0c010a0520903540d03441003071070040701940d0038402d0580c883c8003250103402e14a20783c030b00f0100b40b0000404405001d1400030340000961980000c880341520403000144e219003d030701c0d2908060310740c60b40440321084283d07c06041140150f0095001c3e0700c40e122507290b9980c80d00300448400c0000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 104466546 1250 104465296 104465299
    0x406050d050a20031b1519080907050411040905060603041205070206070b1501030c030209030a020103090203010603060c110c0f0105120628031a0106050702090c040f0e011401030b 79
    0x10000102041540c0f010b442c80740901d200c070024201c074080004c1e1400c600040209400140720039580c000e4500b0012100c0389000c0d5030010741c1800000303603080c4106d001c04c1c1d1045003800303944400605140d0040c0078090203088001c10800c0441800a0052001d4201780100c60ba400c2c47d02011600311b18248054034801d5a000703c88513181c0111040c111082d801c4070784120780018051000c10f001403444451a88114030724001d091a084140000500b5200c000f000001414030400c038000450300c0218500c443d107902801d010035644524030201340101305551028241c2032030301c0c02124806500c0001007440c22100022a80242c5600701005525851000014042503042000c090040314010400c0d40c00103000744100300800d0302c950950304000005070302c0311920341d02600500030002c00b0b40319950112032001c0038080c217606004000c0c15910880c60040e00c01d0f161800010b50b58580764081b20040d01c00e2100083c0e1031607842c1543e1800075400e00428000c21403000a1a040754403070b216001c0d84540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 104467796 1250 104466546 104466553
    0xa0306061e05241b0d030e0c120606100c1505060a090501080601031401090b0103081c050903030f180304080106050f0108190e010b190302040c0206071e090512010b0406050d05 77
    0x180394203402d800303501044000d69800b000c0c00c1302440703014041c072401114504648010030014520300175141844c007443e0102c1e128401800604404100000d9800d41c0008140e5030041c00002141c01500c841d905940028190514201c01c1e4400003000e40280c1c0c001c40060301c404003078644550060080c1c95003401001443d500203c01000442c00c290b102c5001500ea00000086101664441c8040e40390260001c0c0c40700040060b034401c1d49401e800050070880c0d0b828008201a082c204041034070380c40081e100304042c209400100d440d10025400c5150682c02140482c0d503283d5a03601800d0103400984110b0b403094500c1007900c0101e500422030b01d403044c82251988515401114034a8005001030510001d0b01d42d0b07140ea00b982c031600c40c41c00041d000c01300c211040724558078506c108400da44250b140c00302150803003410f001c201c6130010204038812060000e00d1f0760030f0144070411030f8014081d5000756404004101c504288400640c00104a500155410f00015894000707106c0140c0354041c00038401da0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 104469046 1250 104467796 104467849
    0xf0a03021011070b0702010b1309031d01110a03020c03010f0c020a032001021b0601080a020303030f04020d0206030c0304110103110a030513020a0e070201061a070f020a0306061e05 79
    0x803140d40c40001d001004000342400d08590742c0f1000c00c4c10004446400c0584e6541101142e5450040d039403200c0704450700810f01072040155801403001030f0310340440017000c90000d0b00d085280c0c0151070b95040343c01d1030011500356946a04009660704101c0c52028065407800c011160f54003064000c103005034519400600200c2d01540d0226143c003000b80e054146850b841c01d1003400d5400a00082091020405405441d03111495045082000682c00418030380c2c03003440381000686001c01a2030748544140d42c407008981d9140003140c000b40400000035801000001042186500701d409540541d00030341065042400d5500150308a4203072640100d4041d40a200000c943c920a410450b80400e28000c1044048400d9001c5005050b16410815a004d01d030070410501d117a092180c0ba0043c012103101d051080034142c02501503114254014280100000c880c800755154444180010740d8042d2040000350340e42c3d0440086981b510300e1102812440010008180c6031021810511244154640f403004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 104470296 1250 104469046 104469073
    0x3050a151206141807050d1101050c0a0b040609060f0c1413091a151c02250305091207030203121c090501020a0305180a0312020d050a0b01020f0a0302 66
    0x501060001c81d0b03115100e0420407a0000c00303000203401460504280e20f03515109041c00307405c111841e0042405200e10101c42c4000c5200c0801b050400d110038204180d40740d1410000f2030800d401b81c54081d003486141f41c244805c000007544a509124081c0c441048146400f005203000d842003805004005100758951081c6100d4410040c00e901900c8201810880d5441d80500e00b80c40b0301ca00040c850740b600c0d4100402038103005005003d069100b503002c5290544a4607a840c1c0c2030840c1441d040701503400700e0360703004050450003804101c051032451098100b01c280303001800f039400b05203424091204160640038030038001030b441c411b880d070041c040d00c084418501c50b0b888940200c0020501c0f007601511410460195208001d0304902603000503a035411075071805002e031070000c0d14000c08605040030214000c1c00c0451400b00c0f580c0e01d4607020700e203d410b40080c00041e015004211075820700d01010b01003115200d9100103c0700e035080c0c0940f440c1c450141850354541f15608809805a080360541c202e40 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 104471546 1250 104470296 104470319
    0x4050420040e010501080a02011403130303022113050d02030403050307060b01021203090304140d110907030b061b0d0512040b0c041203020c090c0a02030a0302090609030307030f03050a15 82
    0x6800024100084442c0140d0415080d24820b034443d5899401030f900420a40d6848402c5400c10301e414141140f4504041c000d030020040d546a02404250340400c01c00144414065012501d041c002450500e505141000f40845d2084040840c0d1511030b9008260810307002000740d40480ea00040518101b00300c607200c3d03001030f04c01c0c8040c20b4118001c1800c00400f00581e540610f004d41300c680019612203080480400c2c6032200325004500c036903c07841c41c441c0000c0c8640e160075400c66003070340e01603070030b803201c6038150080c018003d85141c1c4814003203400390403401ca400381072400c82c01e04006c840e14500f0340c0d00190380c00d00c07807200c460380e444050300002070100d42e8003061941c1000741c00550918060755440c00c0d10181114160071070061f004400c4040d030f070b80f400c0000c2d1354019144031500c502e40840290302a550f0f124000f005014942c000c60306428a980300c4003900c641510142c184ca03a00c40c0c1034034008212034801d000703800100703180c036002c80c1e4000407a1040e0410f0304c002b40101c43d5040d0811400c49607 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 104472796 1250 104471546 104471603
    0x20f04020408070305030315030a020a030201030f0b060a05070c0b0f040510050c011a1212220906030605040506070302040509010302040504060e01060e0114010809060109051b03010b040303030506040504 89
    0x4216808010029030302804116403801140554055502c9090071518600c0080800315210701c00d500140e280d01c0540c0e21492450101c1c2e6090038002020b034981c1c59488054100703201503e61118000c240e0554250704807004111140c400e02c01000f24646607940880b050141e44510b07440120148801c1c006403c090f0203240082103141452810003060303000f52800d642080860b0350b0001b52998154044d0705000c64184611984080030781500040c0514452035400f40c0040c017a01c98055910f04046c1c054982d150342c010305951801480b0380c42d1281440320103001d090300c04640740d218071800503c00510038404e2324140e5400400c413658507441c58003000007524000d0b1081d200c843d90b071075001030090fa00740305035002810b651582c2042503142c01000d1251070840e2003241c0c140900c090801900703090203d5030a0540e0000b02e400902500c401c0c110f90414031034074400f1001d5070f10000c0041003081e50795008e481182d00c0b035941400141daa030403c6c4010f480e000e0714000c100e503101c030740210f24075441010f001c01c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 104474046 1250 104472796 104472799
    0xc02010210050a1e200901170405061605031b0702012604050f1204170a1203020c06071d040902010e03010c08010e0604050417090d06020a05090f0f030a020f 69
    0x803a02403940d01c051003211000d40b40c95907950740e00c0c0f25451800e981d0000c02c409032950349070200b2102c1d030303012200c1c034070308411079501035049000049422042c0e00441580c9240d04c85240d0107046840e040c60200d5807010300382c403030050034520368200812840c4504101c0c0d00c00e800441c4001802881102c001d200c90700401000c03414003500829003420312801808016403419227010842e128101410044c1c04c0c00740b0780980e0f0b141ca420142003034407203101e0801210221448060007551400b400030542c2d0521400d00350013801e49003d0440d083c40c0c5641500906540203401059403625295a041550004584081003022084281820000d8581030340710048040c0181000301f1407a90440019085804000c1e0341c8001c1160000144440c4c2012500c4543c4800141c030b0802860601c1c1d21000650052510ba223803280c0d20005107a0655100d0911007030145d0751122003036480b083c4810f0080d019030001c41c0c01070300410100c24030030100d00d4684105a4001000b802511000740d4030b400340030a030381e40b008085 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 104475296 1250 104474046 104474053
    0x60112110909040f06050906130f0204060e1e010e04120315090c21020f040509180d030b030624060d06030b0403090501110111030c03070c0f120207170307030c020102 73
    0x14100e42c482c030034203900c20f078403849203540f0020760ba1500c4800c031400a44000c030142d10403000c2000100055a20400b4690000c0d80320468247d40d100040281c891604404104028901405802050780281d649080c00c5c0f0150054030344e0700d03003401301c0c0c240504880c081d14a41e43c000103510824020f83c05420100541d03c40c80c4141510342e20b4800c10350b519518000000380c10300031100110003842840a40c13303809680c06629010702e1003155030243c0500e01641c0e04c51300070304011844541d122001d00b07000c0c083c80c00c11750f05508869107000d40148030075003909010703006800008108600d0340078240d400d4a4245119120b0001c10340510081c0d8120724a10aa81d690ba0304012005c45c0f10041c000e1322862280d038411050302c2c20140010804600d00500180d01d0f81000e00000310940c0c0c00060783d50205820200359200e94616000300c4101403400005041c5a022600c41c0c0140024a10b00080f020850f408035a00250b440c040b68203c48074050201b407a90304144100d0000034400c0c080f04403621700500c1103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 104476546 1250 104475296 104475307
    0x20a0c110d020a1701290603090703060f0b0901080a0c0e1f3809100509061201061404140609120613060c09080c040f021303050105040c090506011211 66
    0x1c1640a03800c2c3d000074034013590307048028465900c00d01405882c180d440119280c071886507859a048000e44410403881282c002c000903a6080d402c200040046421010905c041c4082d441407000400500191038000e50340d034400400c50701c8000400440d61030703208001106d018030f808880044101b001c0c1c41e50f4101d075981200c2c20804180070b198000908100c40c0c18825102d2020413404680501d50300c004041400740c1100c482d007000c1d450070303a15070250655409a1090f00307140101e480e403103407050050340a00d022502400003440303400ca03617040c4ca00c55110b090000d284090346107028000e51040c004140700103280c050050074070720060004064042c20b0500c42045540e120f40c2040c20483e040c80d462203000080c9801d1105901892a03800d926003414855a420000c0e1641c89083da4081c49014949807148407041d0710140d8120b80c0c101002d102d85016290b124940f0714040c0c00c040e103003a00c1c040074142020400020b40e10850f80214016124166070f00d074103081e050082c100d400719980e45260148007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 104477796 1250 104476546 104476549
    0x13060b010e0d03020105010f0e09071403030d110a0801050402030112080c01230709060c030801060c05120a0509090901050f01030f0f21030e0d0203040902180307090e060703020a0c110d02 82
    0x21036920b41e20075000801c02c0e60400300d160501500a520100642d10000d0a000034102c0124110003590740415200b841c402035100802d1039845111034111001d403408400c0921129001c02074800c00410795240101d0341d030380300e0410082c0d00082c004c04002c0500c00303a900c0005004000148014540c0c5000418000c224406045814181c1307542c080300c8682e05030402400c42d80c4004110302401903410640340e411196140181542c01c14054007052020380030310402404400c110003400c5400078004540e1b1130782281c0008110b5002510101e000d400400041840c4404c1801451322812140358403000036842c50300c8040d0006d00340b100680f540f068090500001c1810f0301881083c900d100400c00c2d02005840d1001401c49811841a41240e007151081c0c59a0301c1e804030854086034005500581c84080c501c07003d058000000710705070b92612610000164000c5c817a000b41032004000d0094442982d180134083d01603110f8481c051000803450800440050303034029410000f2080a8181c2d03020320116070 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 104479046 1250 104477796 104477809
    0x30b0402040f03230303070c1b0b090f06040803031b0c03070803270d0530151807030915020a02010504050601050f03100218060f09040605040513060b010e 68
    0x4000064455100300d041c800c2c49000e0204e1040b92550400f852400080e90050903240d010240c203010070442000c141d20b05101809000c1001c01205400c80c0a4132907076180c050507294003d5440c1400b905199a6482c400c0c40d10350280c03012991481d000d107103503950b0103100388595081221201d805140600c110a40400100040c100d2188038030040307592410a550030820303141069503008401291400000411000460500302a81c0b00d400d0880c2c449021800310349007654110150100c1070840740c18680340d02d20900f2200d0040201c807103807440c1d0400240600101c440340703010020302c0c00400c60102e520b07140310790701c6881d005001d00702c203001e0042c18407054410307a40701604a02c0103079150b200f404207003c000c1c40400d0043c1411140201c140f6901004252281c520350340f54405140d0200e6480d49600f0752950131090a0030003400039691b0f5940481d0b00f402074000c210b0042c0554a081d00c00b081605151141c180244a4404807442483c0ca0380c2c0c4070809000528681d44c1001580c00d440700181d102d01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 104480296 1250 104479046 104479049
    0x81509190503041a040b12190f0b0901050301020a050f0901050d09050d11010605031203061207030c090c08150d050109080a050913020306010c0305070302070305120c060f01030c0510030b040204 85
    0x70005943d550b0314080440d000c1d28103403542c51410401c108802c10806200c08100c41c200d9080c5241e00b0b42c00e640303484480e4092085e80b000394403814200004a407002400d40d00100b5020340484003040c0c0341e601d801c00d0600b00d000d48e5410001154080110340d0748a84d140c030190626400c149001c40c901100100319000b5a4150744086450707a226103a51850a5002559440048800c03402080114070f44400a640c0d00600c0814100c0b052000000c610940c903000010141040d2100807a20b0a42c4e4900d4244942200303480390300761031417a00341c41d200240d202c1c499850068401e0080342081c141d800040003000b8404c9113046504c2c2d9620a083c1c8005140000500344441407501d40c2c5440349101e0f403e001c018003210050f5001c2a2041003000403503078101140121058252401d503440301828603050349041c005400140207442003810290040310000e005090300e110f0704041d10745e503440d0468041d41c03604080c080148640401e040512240c103081d222501d4003c258600411082e64035404101281e00a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 104481546 1250 104480296 104480303
    0x601141306050a020c04110d020f0f0406020d260103080c16141305060d030c170d0f0b0d020d0201052208210307081303090512010c0206090708150919 66
    0x40f9525185540602042d056920103407800d008084910307000b219103114040d500b2410a5000c00e1b0b840840e5651419145603050300005280c0c0c0b40e45880d4041c0d80c0d0151143d5400010303a40400268280e942d0102000c40d421003101091526401c5a9030350702c07560081c64aa48862080301c241948040c846a00040200601d00c40c901c20780800301c091240710b60151030050091400c15045c450307280c65107808890159054a03101c4110442842c01050600b561247d500f92020301107030b0b21a04030401d920140300700c0c1460100700510b41e540000e1180028112070065840401c0500b402c0265000340010591881c002c006100300d407840381d20308425009503800400d580d501101200d694015030380480c1c803d004640c0c041505501e000c003002418510000c0c06440146009001c0b5405c0601030700c2d030701018240c001c0c444031010100c4035405009180c00c3c3c18550041c072804005c00c10310072000c140d0750255400701e03018000c000314801c404140400007410f0705101380b1628007045044d48a088070001114071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 104482796 1250 104481546 104481557
    0x807170c06280f0806031203060f04060f030501051504050c0d050916030f06110f030a020a020102040302060706050f06010813060209030717060411010f0903030e01020a06051501090b0f030601141306 87
    0x601000511010b0010081c034026401a00d01fa6881101c050540c1ea000b442180ca240044103400086405402641d00000d62000101c402004212042d04041e11605111021000c40d1400104004c02d851003940c10204400c0c0401906460507840e03088194030403440c4080b1215040c40c40c5820340c82e501e083e8026101d07003d009041100300942d43c01041d9060600a142038100700c90616542079901c0050000c110071580043c03018a507a0003034050382c000b51340040005842d6003860400c180642000c031028006401710710b0009007a50702414025000e4403541c00b1042080255689200080d8801c5103080d50510940d8000950200811054000003c040d07010708600c3c105460000801503a8004a40c14005c0c03452410407441c2d0f018128408503500341c0380440c04104c0e032900507410700178101c00140845040c04200b0800e4004041030600350a001e82e01d41c40e1203a41c90040706840d0103551a0307102d035010104042401796110b0110849a950648105031070b04040465014103007016510400c0400d8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 104484046 1250 104482796 104482817
    0x17070309150e1804030e0616060f0903020c010311031906030804150206100e04030305180d0203040f0f030b01090c050c030304050106030c0b030f04150e15010807170c0628 75
    0x40060304840e05002400200325242013580c0c0107008620f804842c1c600500003c41c3c560701000280722041d00007a0414030800981c0c4146401c2000f41a50102c2500540304074000910107500c24400d90801642012a00b03080d521100c03620324914001902030503111340c80d01d10100c04500b5503002040140510306219201c10503241c40a418000c005103103680c407680d21181003000074650f5100641c400d500d841e0010701c1da610218040801c41031880e00610038480c0b00601c400b4150008020000d603003410040d50b5030340b5a81c2403c00c1800344280001003503da4200300400000d0103940007403045c2d04090401c603050070030401e08203146070011542a54240c0d1558010028040c0050b0014050103000400301e01e549050030740540c650901401c001d08102075038481c0c0390b481041d98011501d542808041c2c940840454041e00324540c0207008941050040c1100010b4042040401c480c82c04d03085005004400d0a4408004a9810040128460000002540c18110501001c200c0b0740103440d2100c10b8102d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 104485296 1250 104484046 104484049
    0x619110c0706110714040504030504080d0c2003030403060207170a0909050105090402210c03100f050601030207050d030207080f0412061109030a02040b0f0d0b0711070317070309150e 80
    0x303800f40070b1000c4403500722410a10101d070440345503d00516050b5804962900d41d880c0494091140d90f000c000d4902174071342c2040301640d0180c81c1c1e90300306004550548140d00caa02c07400b403c1103444901e96605074005c100410009802c4c1e0080d003c524060b150200c6040451000d0399001d0b402440c1e44400a10303580020310200e4258861280074002c192000c49031481d282c2d02250081c960004901400e801c29038006410b0302c400c00440610b4680030302602c01c2240000083c0d0050640d002e00c5500c482c2c105800601c3e1940700b13100782d1744000d4010004251803032814006500950003217100b038883c607508100046001118078000c000038042208018428101420038808036011485030820a881c20050740009075800500c92600a07012200020f0b511403d000040d030f1140e032103000f150030003405045c8409004be4030b80711512071503180e103520262400e01e20b02d240c1c035807429010091184520407000041c1b0007084c0003800140e03119051030603a441d19034140c2c207004207480c007030240014891060031459 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 104486546 1250 104485296 104485307
    0x11701060b030c0a1110020c010c02190b0112060b0306010b0c0c01170118020417030a02070f0b0f16150b0f01030212011406250c050102030a020619110c0706 69
    0xe01d5060055415401d1010119040e84610140c000400405200010150405014071102c0d6894050110b40d1040c0042e2241d01030251002c20001500070910700341c01c50805042c0c2802500c4d440448042203038208484404000048a0701307541c899500c0106e0643ca480402581d4040d0404c21091603c0306800300e80f2a140a0604001504101d407143e083c0720004460b40035607044d60048c0050034152050384951000a0155910110348200007400c18074608002000600001e091542903950581d00c031003204a0a4003070b03100d9910000c0c410041c1d809246428070182c06142e40ca05201081e4441c1520340c041001946041044440d0b9a814191080e240a2111700c200c03010130300f0290b007040744a00307207596910300c14825281e82540313104107454140e60302c1d030880300d84101842003c00445a1544480e28000382114100d030401000000443c85600001c1628402c6006900401c01c56641000003001d07400d41c8501c0030b180c661180310500c0d0080c64507000d041e07828440340003028070f90704d8024000d01 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 104487796 1250 104486546 104486549
    0x81201080d0906140d0609020903010b010c05060f1e07270302030312090106030f0c06030633050c34030506070509010c060e0a050d08011d040c0b0301170106 69
    0x40503480100348455540d00507032450102c3e2900d00b04110300c24240820f01c20103100d411031840e00c03d46010340c04107100c001940a0141840250020000004030324015607400c820208083d049a101000084030300103860100da49c0848400318008540e56040f00346a03002030107488030340200324400101c40303400c01c82000003000040038000b080320451031600840e0b1244107000c07542c45210240e00014070128000d4000400a41e80300c041c4015201c03490434240280074140c002c00300081d007046000500100300038081000201e960f040303030841c0c00042441403005a542c000c40e00500c842448844690314080c4881241a41c5401c010b072003094000d58422103c034518103410948c41071610b4244081980083c0c072507031200050410704e64074004c440040e11100060700006102ca41401c145610505000c1400c03540c4a10401c120b450043c02c2c1802034401d20720901940301540c1c0301c6001c0d007c0100e00d04200d507410034090200e0b0801c841c0c80b08800c00c01503209170800c003070781810748080814100d02481581d0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 104489046 1250 104487796 104487809
    0x6110304140705060409050411060307090e0a0b090613060b0a05040314060705071e29070e0f100c060501030b040c060c1a040201030b030105010801050a0605090412030e100504081201 80
    0xb801508080c0040c581d406140603425810365a032000038200180340d8055412000002d14641d10f92400c030b07000601c070724410701400c040805440702140c5a04c8640c041d40181010080004207660307079a0b000e0000c030071a0600c440c40c0b030f182ca41e031000488040c0c07840200742480b540e543d030f15540ca0842c1404110b80c5100d1651503260b82c41b9904014141c4e9100e001c0e07400450b071140c00c62684803100341d0007e201c10b00b9590302521f4103641c840c00b0540603021400050b41520590945105580c50340c40949015484038025a0080f107600801c41d030070f00d490389004003034054605040140b0a059180d50040300c000360800c4410000e101c091000b440143c450200060200345006102a400c941d64000c02220403043c540ca0040e1102c0440c0c216802900a0210503c0141c000c004543e90791140c140030340420380d00445c000d0b281100100305410140701c4288119003200d075035002c1001a110803001000750707865500d85401100c000c07940c0c03417980340100c81c02075008104160b1a03891010b0780c40c1c041c84040c0e0194 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 104490296 1250 104489046 104489053
    0x20d1110090e0c03070207080d05030727060e03150c0a17070c06050717091c09060206060603040c030506070207080c01080f040f0201021f1d03040501210204030611030414 75
    0x4010004002862075803114080400d039880b0f490303680381071f4030704450758100302a00c0c01200380f0910040e0f40320000d0b5210b1484e5680301100e09142500312542e00da20010750342f0f078244100c0c0c414413003103010b001030305000f0901408948414001000000208106441850842c280011054079103039003c8004c0503115440d40740c030324003070429040140c0030a226520003010300f80c0320000500d1040c040c0c2e0350366195580c00c060741441442e000c01c0150711030420f030f850085140c50320500f44060511642914040c0c500c0e03500108080e440702d40400105401c0200f04942c1c4142c14071010002400620109000d044503400511190342020402400c00802e1b84000341000800c41c01c00000c2110304201c41e03000364116041d100c5400031400102d0034088a01d10f000440820001072011000043c0d102c4001d2181040c000a200081c10004070307113900c6944140c5000132300504240c911069003c0b941400e91034030b10760051405940ba0b035403109451115030075010000b4040b080100340a051000c0d02304c180e5841e000b4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 104491546 1250 104490296 104490299
    0x20f0901120b0613020a0203070b09120406120603050307030807030609050c0706020307020a0b07020c0108100b09060f040e0f04020120061503150108030403140615010e030109020d111009 82
    0x4103210740404090400c0e08004041501034844004151002d840c0702019980c80b958144065a254002841120003001120010300c03600c1000c03480c500010f086030700ca2407419142c800d08403840c06440201d00043c0355903110000002d641040204040c030b120791a55513191401030409000c440f8598007030014141404208900b0044290456113140e9008400584a880c0d8003402c074508400c0c0403005042c11204000d10801da9000207055034003040903602c055480c1e84142c200e0000c54044e200b014035002081c460301078a8502207010308980785c14500301c3d50925541317030340ca000300358011790b005080303180e4000c01e1100f5941d00401008080030301d0001020749543e8484010b03a6a0070041102481030b104480c052155078081c042c1c0c60480400303e040c40d40b156100d0828940301c0d4050700c01150300354081000300109000100701e139446184c0c050024a2901e0081005503009110411543e070305559420041005235518007032440414003551803401c51034180000d100b03282a0580c040c0040c800c40420 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 104492796 1250 104491546 104491559
    0x5010207030f110909030c070518220605040c18140106050d020903030c032206090b03040609150b1005090a031b0b03011211151605030d060602030403020f0901 70
    0x3004800c03280c2c0040c0d8260b15054a00f03014128900216801d64845400320900000c02c2001002c1d008800c04003003070f560555964010041d02a2150101344810715002001480847c808800381e03041200c11303560201d0303800c0e05580b8001200c0d0200c0d02226075034071004080c09007000607a046106054540c60402c80c0000116402c0c280e6181403042c1e208000b03000034000d43c000a5901690f401c0303040601141c0d11a0b22400040d134884d082544414942545607000340780103400440b080701100c0d0700d0b0715600314440c2403a5841e1f02682c00104151101e40d2108180300020706c074401c1070941002d0000b030000303202e4404010004229580200041040400d004904469940038035081c2120f17480503010740c2641c17007404648180e1403d0303481032800c0c20010000203828010160604042407040c071002c102c0d4803020f01005480d84240c9200c44040205100c440c0c0400c1c01c000c43c03d21424010710850303042070719121282060b01c440b030700709600682020a081003141400410b01520000484500744590304150f03 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 104494046 1250 104492796 104492803
    0x90e0402030a0b0c090604080109061a060d05070e090a0b0a0f060509060304021504030302030d1407080112030e1207180501060e13110304030801080d0905092703030907030b10050102 80
    0x4030060803c9000d040811981d280c030500311880c5c0400540f0040e26141d50b4041d403802010300e05015281541000c15950f0a00d842450210030824010000d50401e11b04980c441d0091400030032000611142504011030f80d503134451030601c40c10075140301240c00d01c100130920511100341d40c4004031518181c1400d1010705d40100c247c41030080251071258680d629400064016540244e46a145110004c1c001c070500d9400300040c14565516803061140c4204590044442d6508a03403000004031008010300c11003025003010100d890092510350f102c2c2100b000041e01c0e040004010b0003585e408000c01f0065004c155400b210500603420b820800b2350303d05000501124601e040c02841401101c612a0b03903044554000750b42814201551a101c0c902450050f00d8850207000d00d50181c428020341d42c1d0450f200d006400c00391340c1d01803e40c00b06171700e502400314000309500c0149100203070140e144082e80c0e8030410156100d0224000180807452440c10301140a00020b0a10440301001d0310043c05940d8000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 104495296 1250 104494046 104494063
    0x4290415050d030207050d060222031104051905070807020c040b0d020909030f0a020d030f020c07051c15050a0518120319090309150c0c0b0c12120106090e040203 71
    0x1c2d40c425105a0291600b02e00745031198124070750022180d15505e0501c92940d0150642d03964426585407003801040e154100f2a40a1100601c1070900c2c030104c080500307140d0060b5411054907042d00c04200fa030700200200341c80c1e00326825000664078004101d6030307a0b410011441c0300d4406403410003d5000304004a4032140015074080d0080481c000440d10b209800c1046404000c07241000315100e00c0f48400c029224801b142c1008006410524401c2c903040c428804c44184d9003504000344020340c90082032200c1085d100e126450440c0019800da03002c10280c072848070710714203140c01c001003520b01400c28908881c1c000d02a03204500b01a072001804007400980441082d0344c4200070754617a503a0307036400000d50008811a030b85407814011440200350b000f41d000002e803010701109010880f03a140c411207440e02140300c0a000000d05807401c02c6002c0b8000001c040c0d01031200705543c0701d81000d2840c103810b58030101c6150140341c44680108134842d40080b814000d800c4080790680542400c1c1c00180d501c0850 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 104496402 1106 104495296 104495299
    0xb1513020301080d03150503070b030a06090608060a0902041d0a030206070206100302060c03070609080c0705040212040312140112030806060a0219030e0429041505 72
    0x103030003a641600c1c03d560050900b40241c10040f80905480c03c030176036813800800e402003100e413020722880001d05402c203502039503401c0812040d4201c544039408100e0790307480c01d0700a00c52004040f680c075410048000000c6400c1ca040d00001c2c0c014882c000409420708420f6001151424010070303910b0350140280c09031419503031000d505a0b240c0900700d6000103c11401c10f01400107160040c060194a601c180c1128200041c40d902c5104850b81c84005a0342c40e54046028a20f01108000c01c0b00517140988080d4200510a13014140c2d20202410050910000c54125601440182e01c10140c00d01034608212203540d50700708040215500d8541680000c07050320019070b4504080d41100d11902e902d500514503001d40c05003541d000694100100c040001e50004c1964590316800781c00440c01c44141d4420281c0c001000a1100d2511601418041c42c28002803603c07850b08561030000f00d070750 = true := by decide +kernel

theorem cover : BRFrame.Cov 104316546 104496402 := by
  have h0 := BRFrame.cov_init 104316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 104316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 104316546 ≤ n) (h2 : n < 104496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
