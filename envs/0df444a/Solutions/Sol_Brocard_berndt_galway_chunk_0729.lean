-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0729
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:27:30.071533+00:00
-- url     : https://prove2.me/submissions/46d5b9d5-350c-4739-afcc-87c7cc8d3977

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 130935251 ≤ n < 131115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 130936501 1250 130935251 130935257
    0x210b09011409042028080d1e050405090106030218040e031b03040807080d020d080c0304030507020a08060c0d1a010c030c0c08070906090e01050702031c0b18010f0b0304080a1b050d 79
    0x4492070000c410300505c0030080c0710b801e005190144260001500c000b5030101c0c9136426401c030f41c6480a05500990845c0d000b844d01500807405980d43c0c14004000350030489d8201440303c50241900d2040ca090b0051200740c203070a40c0618a4181100004d40600500e60750302c20f13190006000000d00120240160001031101c02d0142861060f41e0303a00a0510f0300c0e1800d4603041c44896030900214244410035654006c1d494102156620000c1c00000e24030681944420001d01c1200c003044001101e81000d00f10303c40c084401803148146528112102c022129840d6000821408900010920030040009403c0c060b0300710140481d00d846516080043c0382d0403044c1d609881c0c24040100c5507403845000e2941c40c40c02c1c020020350502443c025140c2c40303066a13003c0030024442501c490300c54130340d21401c40360000405034030ba80c070080c0030a804050000d108a00140705500c038002030756068442100d11403507125410902d410f0704000d041c1c80750810a540e0040c049100660030000601c104441a80d185c00d5031 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 130937751 1250 130936501 130936549
    0x18081002030702060708010e0403050a2304170106030807030813080307020a200102071701021b01060311090403080103080703090b031021080d0c210b090114090420 72
    0x1032400713440e1000162041080203400401000415040d022440d0080e502d03103000e640e05e16558101f225901918002d07078042c2100115603901c2c500c100c400601c02c803040b4005602d812a0010b551700e081b51a07510014050b0030041016100091003a600c240e0b00c62045600f0390188070450725900100d8104441400140e4003440c11201401040c08442d168900e01009098800e03140400003900c6111620030840105030490070308032420020f4043e1104010854a0281911029482580600421304c41501d840407400000046e50400c0d03031500340f089270152181e9030641d1031541c03000b440f9030003030300150108420000045414072120000710b0003075100039010000356080103007082c0c403007040f41d001e910b41904c0c1a913904001500ba00559082200c40100080c444400c0d22095030040c80e0550359504000180113401c01c00340103039220404641c1c0030760324092144c2e00d400741b10b49003001085941d580304180c0800580024500300e103002d41e5050322540048401d1121002c00d021070b0b080322100307003c83c2a103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 130939001 1250 130937751 130937761
    0x50415030f050304062a121b0c090509060106270e18011406010c02010c020f1f09050d2004060e01090e12091f020a020306010b120916061808100203 65
    0x642400b0b03490500d0486c040c0300c1c014078070300302003d5040f02c070020002e01201d451084d00a00034102c0301400b51500c45440101415407130217061101c01c602400c480689000049922a480000c400b41071716610340f01c0c07114180e1030200f20b00554442107540700340c140001401140905030900315034010350070610443d0b9080441d0300c16509403012402c1e0706602c0c00d140010491180c0e030290300c50094bc4e0302801d140500e120705001082120400303607801c07a00405a001070720b06045c04071785400301d0403a056580c14030325520f070310800c01c8200c25410050700301d01c104881a55450815900c800700d650004000280d26984d482425120300c10076840f410445076110075060781c03034105204001203140c03900501c514050307410002500f4a855681d5003000052010510540301c0e0082000c00161500101194038a40e998502c81d01c0a0380031500c400780b100845c001081780074a0004252516002542c11201d002d41000d03002c5850210a4140e164a0b041e002000240814203001c4d0309084644000b000d41d4901d04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 130940251 1250 130939001 130939007
    0x31005060d090c24020d0905130605030f0618010506010c0204050a0e06010816060e090109020f160b04020a06052703011d03073309031103132d050415030f05030406 72
    0x1140d03403004d0542d08942003030242c01d58820401030a44501301c0d12a5050f00b2010500c1e03000b17103003c1d0801509441154404180d1000014403244100c1004181c0310480c1d070800c01d01c60980340b0607120315001c10100c5a01000516060300000d6200d080c00e58005100d009401040b07103090003c1e032098040790400c0c014802881d48c9864403070050115414054511107248002c180034441c14865607015a6021070075020040c80c80d82280c0059090203101c1d000c401444c240b03042154000d68040344120300208000403098041c1080d2a043c280401502d07501c0344da400210304910000c003400b44d9141d5079034103c114010804ac41c25564213810304004645800042c505031030b085417804440110b82e0801d02150984820042002440504250010420800500c0d00b55480814040e405580c3d000200e89842100b10040c0304070122403200070f050700f076140c8010400401c490f4406c0c0c1a070401d81100802d2013941025000411f4402440ca4010b03001a50794603070012024141808544941001500b001075a074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 130941501 1250 130940251 130940309
    0x607020415030203160b09370f05010f0c03030921020102031501020102070807031b0f0b0f07050c0a0b09121215030106050616020a0f0f03021302031005060d090c 71
    0xc2a003e07400c3c243c81c200610350480340034600f40c0d00d01c10711107926200f80c00e808239001030021004101007102c181c07040110040009031580101d2240804603000080e82c5c2d80304200c0307039a074200c851f10350034203c1040d510110044c140350181540d40d10900d40466074507180d90b011700000400c0303541c0010b07120308007042c10440c0805258100c0381160300521401c0301281000049a002962604140785210301a00480304d180341c0d02c081c06013102124030089818054981075440c4100d01d105025216a5030344c8a00ba6014091545050340560000e50b903040028010305010740c100303441c1412900c01800b1024201c44541c05200c80b02d203140f48031010310142d4416035a15044e0755000314002c0c00320a0170480818214010820780180007201d0722008029921414619006860f08840c08610591603000d103100014030f43c80201e02074903400041c0c1540300310a2095a005801c1003c0b0030200a2405080288540000c102c0d5814142d0341e058082c00183c1111005000b45144815100380c50311680e094031003c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 130942751 1250 130941501 130941523
    0x30304090c180303201009060906180c0b2104110a08030a0c0b0a02090d050f10090209010306020a17042301020c070603050c0c0105040609061512110607020415030203 73
    0x78191203400d00c0001c0c5c00c543c402e9410040740b40b24904401000c1141490302641310801421a0b10344102c80301400181c5e0010b80300d41c0d00558050040c0b4800050852190902120161100141002c2031001c0d25a0000409046001d04154590a6030004907000c00f01000d480458410050503900005401c040c000000103001c0c8001841c1003d240207009000341490803401851000d03644001005030349540c0c199640c000020b00250fa01120528166982e40507403180c0703003001d1040d40d07058203007034003d8000e09502aa002d840700005918540c0d030300001c2d400850000c0c050110b0558040c00480c1c2d50a4024820780c01050034200180385002d0101c0b0384581c0c02c0308000303d64010041c580c030710880011120110740c0d8034034000a41da07903200034044c1c1c28014030540c0d0b8415401d210900c414444550002492140a10410030405030502100d01c0c468529205441c21101c07841c02c0030000c01d20b0340b168000400806881c0510344500c0d5400602294007204404189034100c08040c000c0d8182001880221 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 130944001 1250 130942751 130942787
    0xf0912170f04060608031306091406090607020d020d0609060b062104020a18050108070501050a080703050a2c01050906011a16060e0303071205011a0d0b030304090c 72
    0x1980290890321800c0e000500041524071008041810080542d10140c01805400240c98646005c6009840303000034512032280050315100c0041759600100000408070301005120303500c0d004c030a005000c0c203070300b0400c021707039202d1200c5040101603292014401c2c4482e204041c00141006146000f40407a28140c00f0340c1e0141c04244240c0c984846d000d010711b034940c00f10100e01c8040b6600c620004400303598503001030840d407001c40c0464003010120b80055041e5143c0c00180c1c1d0449480c0e4004450900800808500040c00500440c0045002b64042038100c007019001107038141032141c00c0030b0307005c45a04140e443c0011070003800c06070702000e01c2603541120400c0c0c0509190751401d00d000c417109010000030511980c0004078011814104c4001d0810341e45d0280701401490084950961a42c00848040020840080c10f80340a00d20a03c00d140c10b075825209440700a000301c1c050069903070811041000d44950302d0032061030a030760401c0a44001c1607082008526030b400100020b000800c044000012 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 130945251 1250 130944001 130944017
    0x20708070b0907030b13020f031b01031404081c021306050322050304060f020319020607020d091a030606120c0d0b03010204030b0f1306092102061501050a0e03010f0912 74
    0x24241c00c1d1016000200d481e1b001050140314000292003060390031045505226141850101e0304480381480ca060300b00740c80400c030400450200721518081220001c200701402c103c2c0030984409856840c0303005003040001030400000d110141d0b41402e154000801080d00442001040e0303420789084001c1c1c440f406040d041c2c0c407090b07075507040d0b59001e1800303980305001d030011201072068030800a035100507030000865810000d880b0300c040c0d01c5840030b03201200140a03041e0b00c4480e182c003406501040b00c1031030958112910280200000a420181c2070940c050307000c020031204048208100c030301a810b140d81c050350710092100c4550856141da590a4003030b9006100400c0440e2140310401d81c08030741000c1c8642582e40d0342c901e01074070320703480c0c0d4000301268a0850b591040c0219000300c099401044919113031403909020040c1e07175455044500c00024022881e5540e0302c0e51048010300380000850828061141088001138250340224100644040da540291010312244103503030040b09800d4103001203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 130946501 1250 130945251 130945253
    0x3190b03070303030221100614160303091a0702060a051f05090403090305060108010903030506010908061915060e030709051012080f1603080105030c030304090e010f020708070b090703 81
    0x41c403030325140710140505a02144e104001a641d550010304021400700417a01840c1030301d0000100f03189405144000344410700d546203e400841c00301d5483e00100d600e4942c440a6a0381c0071030144c1961002203500c0180000c0c220b042c0208191075500a15041e0081c0030329261155030042105c900405000080040c0940103003844407580c0300205a84040d5021010b55941c2d003001c3d40c0080b01603000402500c91117000082601040d0710108074648030341d5051240e40c3350000110350b400f000340181c4c0d4403900050042002d11408074080f1898100c02003020a603007100340e10030b02001070030360700002c00b061034440d060501d0b2400b0b10070000604100d00082000d406c14480c0b0403100d80c03103806021000a4111702c02000e1200c20801da96040c049468020394415110340241850041544101c000c00d90102c00402c140c58045402030400c24054021802d092030304040001915600c000c56029560b00c1540ea00e400038240000c4c09020300035400650745002130311b401c0c0201c181c01400e848154022600c140 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 130947751 1250 130946501 130946503
    0x3040b2a04030b0604020f04060518041a040c02100f150b031b0304050f07060e01110f060a020a0504150809070602030a09050409050c040c09090b04091a0709030b040803190b03 77
    0x240a880c2c01c40d43c106402c1da1380d140410000d2040555001341550f000c06e0000c0c1c0b2552090040040580d2005036101114242041c80142c5410040c00d0386000502007074540b05003860b0340a95074003002c5104545080115110860855041d040305248564545c40224465a0b0b0b80c542180208411484e652135403030401740c0e1845180001c1d0013140c1e00e09001000c9018040100005002588101c003542e40165131508041c11488801c1200e50214006410640182c1404035242002052107000380105a44511154001794031652451341401030511005c20b610b90400c072840082e880944851880c0c1c104128000d251055680c010011544200205c01505034400742d040111342c025035010502c2000c5e85402d40c1001c0000b0301c1507405c42d1500c018000c2c01c0c2e6118070004221000903c040280d080300c87c0910060300c25026000c0c100310707540482420010700b400d103103a9000c085071903d04041c98582c0e4580b060a0b40c291400d503028070001c4107122001c281d40500e2a10601031000422080042d2000310b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 130949001 1250 130947751 130947757
    0xb060c07060f14040b0a090803120c0307030e0f0109030206160f21020a0207140303040b030c070503070c062c0d0213020d18060b030c1e0a030803040b2a 67
    0x29504008000305009486405030501c2080400000c43d1a52a07544540c01c81303803503401c1580c020000443c054000584c52074044200c035141c030841c1134800390741e58a0500d0f001d1254005002e0f90101036036014007107220b031024000c03560501024400880c80f403070307581070007450168041e01038001c80f030442d507890303290581100340041148210304202401e4138041010340c8500e800d170a4840901800005c005110541c0800c030b16042c0c41024040c003c2d04140035081c56580e001d580101d40040c0c00030070101c1c2c4542c4180c0090800c080c8683c080780d1500a1660360080b17482480e500105c0890603c0001681c0d40e9a1540008441290891021b0720201d450000a50104006401038040c00350300c41d00b2003143c06140c04440590090920502105441904920740c0440030381017a84e003c0d14001c01a14185004034458801c08d10003013900da0b4041407200c010f11007460321640a82e1001040b000000018101000b8600c980c0c000d003003120305494400201e0740315080c40f10414903041d03480074696021030f07410700035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 130950251 1250 130949001 130949009
    0x3070e0f04030c0609150c090e07020d030b040b120307030e030309010509040507030605100e030f030306060702100905031b0f1002060a0207050106080601030c0f060816031e05010902040501030b060c07 88
    0x807400c3d40342d090a0004c0107100c0c002001c0c111415540920701c1c102c1d01750b00004d044c44015a10070300c0c59617840011403840f9506440e488016003150386220a2207210f904402e1181e41c0084c40003515620318030000e0160207100380110095000882d0740400d060300514148a1160150051850894200c000074598442c0d08405c5100b1170b0303201c0c0804c41c403910940c41480a008054400402c00b900d035200035011803100c0b00107034401e200b107100c0003813412004400c1d00c0c06004040e10282c184400c030307420082070180303102c0160100722902e003001520366800c200032a010301c070355110004642003100502c0b83d150240c2000354001c0b0342c002c0c02c0c6001c499001170119801162900f00503102c56407890060b002d0040307a0305c102d40c14420180003006000203034410004440c40c0c442041c5032175a40740c0e0300ba07404501c00c03032310580c81d02c0101b1a13842c0d4a6002e600248070041100c4814000c0e8200042001c5c1284d00a030070451055602090510281d60144200d2107041d030112500e030305041c012141650740346021b0103 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 130951501 1250 130950251 130950257
    0x2010e03030106030c170a24030b060f031006060e130903090905060303040305070306050a1404030e060a09050301020304061b030b0d0f030e060c0102032203050a1815020304030203070e0f0403 84
    0xc01a0440b0340300b595021180b6000b84a12902400c110007540042c200707921146000340d07400840202e8111007904514209c96102d080300b0311954481041201e10400c019519415000f100742c80419060280b1520f07000d0901c80e1503007070721b002d0200203020706002040e130170160341460111001301003500404410221420a000860070f03a07195004282940a10b070310040140c49000008803c00c03160307030450b0784240e001d010b0420880c20414103d4030440c10546028020807140c4174a10841d0412400800c0600c02e141405810291341e080407030308a07842110140e035150361711000c0003a4528140c41d42c8002441c68903046c40140f1415000490898418000a00b000a410001e004250048480003145040200340340d4031070130002102070103984220b504668111110015010a4030602d511080c1d0301d40541e24035060251b0114140d41d141410f81d4181c40310000280009140802540c05c1c41980590754082e6031181c0c81d610501d854081c0135000340d0f80d82e036501020008c01ca10045001340c0e2098042c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 130952751 1250 130951501 130951511
    0xf07050303281a090601030e0d050304060b0a0612020906130617070216120614010f0f0801050c0a050a0e30061302060310052d151608091002011b02010e0303010603 72
    0x717001a80104182d18948282c3d000c2c640c0e0a410944e0448091441140100b105200d8052000200107120380c1c00c2c0542c50110301110503a5003010001c1d4058040500c000c1c048a141c1080741c00703450694261039101000044149448400e03c501c55820140c01110301e000828108000e22005290204240510030201d103407a0b410009020658001d405101440481d81031203584400382d036600310718103014004101c1703110000010b80f1340c01489402e1051805091513401c1c0080614103c0b0598030419651081140f100b80a00c515914200e45465918000101c03040c8262018813a20500c401258410469041801004015a0540c2c003100c000c940c12034002e644d0359a040c001403c0500c5176001140c1003c4101651407202500320300100100b141103041c600700101031010001050030301d0021050030501131150203c056020440c1b02c006500c10b44a850910302460042415050040d0a110051b03456501c003203940c1482d01400000038100d80700902c015400764101d80d98921041c4500c5003096560 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 130954001 1250 130952751 130952761
    0xf07081c0f05063303090a0507060e030c060309031c0209040b01020601050a290406020109031101020310050f04060315090303050601090f0303200a030e0108060109050d080f07050303281a09 83
    0x2d840610144e401c1101e007612810320a418503034a50720464101e490384510b9070007107806409500785d015100d100070001c00051a01c40300303010140d0405072004002d88010300c140740c0541300f030422141321780c400e1410058944803008100026035110b003001905541061005000d6074072945c43c10025a03600606410801c8000e818a4041031940a80ba20304000c0205001c10169410b4112040c03660095640044070884420082d00306d1005450180481600081c104000d051084080590000051002a801d580c0b520b41c0500940c00182880c44295104600002c16401d4071031a07800400c2841d1104c8610300309842e9141191071400041e090000c001d810f400039841d82d940304000080d040c03041d01c17404090703441c0c09003142003444a543d000c1580280002c2c001c3d44142241421660010125a9162042c1d143c588a59210310941e041d078010421120b408100104001c5000700700030540e0400f0182c8061030210180c198072104840c481c1060ba290f0154000800c600c2c80c0c3d0f45048034050a5901c0b2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 130955251 1250 130954001 130954069
    0x702010902150c0c0f2b022b171303060204050a08011e0e21030a0c05090607030e0a0308030c031008060601050301170709060b12010909170f07081c0f0506 68
    0x3c0c1b41701500d00104031407003803040c150b500b01051040307034070a69001030f00b1a542009102e06c010070150203c02462004401c04c042521005421400b035103003000c0d6032800700d01c20070b8051020b40a40041d00d885030002010007070784c00c01503091170080181d50000c000000e02c000c0300c240100341c0d02072040045501c45800080c03004083c080196545220041030203031410383c0c812440d442d042144d400f40c2543c501070400100a001ba411a04130b43c000907e460f2800c40300d43d031b080e40c94111161103503400080580002c0000340f5440e0081d4010b0810684141d22407402403c048412803064110452a4000304280b00b5180d030040203590541307400c0d00c1c850301028600c2860f58600f20455122841c05800c03c4000994200e01c100184100c0c89070070142c0940d0381e03e81c89001c040c1c803101c1c0c1004280f40040c1c07503002801c10b400b201806049a502081c03e2611405485001054100c84512140c68981d880600c6c0c034040e1601c00c1e212600034540d420701891510702c000500840368000c0d056002104800801400b90b1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 130956501 1250 130955251 130955269
    0x50f040f1b03030806010206060102150105010c05010605040f060e1014041e0f05070311040f0905060105130305030d0b0d0c05010e19091b050309070605070c0801050702010902150c0c0f 81
    0x4141c03965031080030340d03034280100010410369029001d4040c5a02190389540b000c1a4000e46407944030b80107416901c0d100044501650002068641d5540e600c0013003481d40d00c9000742514203ca24501145044c00c0071510003801001030a51400c0025414003040501c00b4103080881a1208940c0007032140b030b0fa00102c41c140f00c040700b08203000920380684d4401342e00c0d117a48035034040d52065508021944001540064502c0b0724050820f2441e00c0c6001005410f1050304140d80c400411700d041f070f040c140102c40310f51968001e81c2003140e403038001082c00b41e005101481440c4000381c04580302c845080241d143c1c0c80850a0741e01465040003421081c90b50f03281c540103000c501d84a180c00c460024559501c5045c0300030024410004491801c803020303c040e4078070403025680246036250180104c9407410721700b921554003000c0d0440e0b003e50030071400601c048080c801c40b4401d00158001240468080c4104180c03180901c000103240364041c01071081d68030340000c81000c0c004040d2601000c8401034000182a1a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 130957751 1250 130956501 130956533
    0x10902070303020d2405060a1e0c0209010605220302010e040e0304170a0204050106030b0306150310050a1a0102010204120b10030f050d021501140108040201110304080c0f04050f040f 80
    0x150070a8400e0740c44a186038210505521524a85d060503500c40d402c100c414411101c400000980910044500003000740c00b560380c0c050316042c18005a146680800c070b6145003640104041140820211800040b00a1792403d0000d040440c0d0031140c02c641c006020922003d5401d0300403681c4040c074114240007001214080c0650032030f007012a00d84420040d9580d0300f119002ca01450400d0000100c5030b0290080b100c4440b00140644420390300e851000c0d0000281015655151080341d404001d503204500c6414062030007800f0204071101018030402495040300e40250442e0700c1004100319140b0250907803e0a00da2040e180c003029100d241c2c102c600c041d240c1d00040d1011004100610400200040c1c4107013400d036503001d0310810034814841c554004024820460040c0c80fa007041c684641c400d507038140e8080e10504002c08240f118010303c80c0703540c12541000120760302c000001030051406994a02202c1001c171403c0c0000d2500d0214800e01300d902a200030310001e124200c002c1000b1800000800c85 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 130959001 1250 130957751 130957777
    0x60f0c0a0e031c0210060303202107030201051510180803040807031a0c0702010f050c0d080603190809010c0c03050a08040609090e1f0605030109080a020105090f0601090207030302 79
    0x2c00f8071219105403014554000001342c420745803480301c0714845019140071aa050340fa0046100c400205500c0300c80216140100e40d4060803d00071790304d40448460001c180d800b01c0c901500d9000030b140280c210b507409812416040700f103800484841d955903042c0b0a60092501d8030f07074205144090020306405031500710480d0f0f80008600462940c00024a44044a00074140c00b404564a8852585407020555800c0c410f0b540401c21040075502600340d07600c0a05441c9801417070103009201840c10050361a075940b000640310410721403c2d1030100300e850030030383c5580031405109603075a84810701489840020340c1401200e0302a4810301ca00420000002c0d500702c02074808800d4a483d1486203a0300500900380455000c00c0c012030185054440c0719641c080000003091f030540f202034441d5050300807400030341c40151140d40200d800d85083c00754803003880c1b00d00744454445400c0b183c06820348100521a078007940c000d050b403107030790308000901604454103d28010b903514224242203019109411406c3c003c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 130960251 1250 130959001 130959013
    0x4051b04111c0c05030705070314070b040b01180c020705090c04050a0603020408011104050609040f020f070b06030c0909121e0c03130b0f070b1015020f06010602060f0c0a0e03 77
    0x301d102c00500d640515090840200210340e40c2880540f001d010964055000a4052101100090158104030181000141611705003100c91b941e401a050044030200d80034104000100070300301d03206030041c02065807a642800360314080c9200950301c0d145071040c64800c403481004504688142c00c12200940030103016185039a407650030181c065441842084c0f002e40c0b0701100c440403903074081d080d00c0030b03544000c0900e46403404550801004d06204024244003d50800c26280700c030341420000d110b507621400108001d484c1c200100342c02c010b9026030f550b004a9021081040000300440d05007401d80d140100c05460721420111014051180410300c410100c0015106440740d20003c040c11100500e40043c90340c00d40c07034050148403400b60743c240e4040c100040c005a40011030301e607c2144e1080304200008001a550000f004041c1c40c0c0074500c1026802c0f140c1c010380c08404c180103650161000d800100303598180400b0079143d4410040c40d070890200702088400f40e0b680b0400d505000f103c130050031548 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 130961501 1250 130960251 130960267
    0x14150706110a0513061403010b0d0e070807050406090203010e130303090816020f0307060f0f0507171309020301030203030708070f02030d08180c060304140a0807030504050a06030504051b0411 84
    0x107a074850b10421644c100d5070703000012100d126000b0b4480c01c1d000d5181c22801c2d43d10380716140ea43c680210401d07284960300d5961900c1021800c1000200420050700241500e500c2e15051000b00e4600b9080903416a004000520031a8041e00ea03450b0090090490b06507248034508044005000060004045407400a641003a0b0750f0407100c1c000845000304c44007440c20074034004042e60340000744550004224030f0340a01d101c02d4051100303442d00b02c2c06810200e2130040107649401d41c4450031543d14400d5000498100240c07001110501c000e400024421891941540c000a07070364003450350300419070324000404404100b22262401102607000e0b0032980c108181000c06000d20030220303105000180c4d90048130490340000184000300d081c001d00f00520315125030301c4401c280d02024100107198410250184000b904c40700c01003003664001e03503403181c485043c0010420a1452540302c0c0301007500701020303c40403032008290030f058039440e8a14005c0e21901303400850007034210400c10300303c2010003280d040 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 130962751 1250 130961501 130961507
    0x305340318230a0503030a020a060e031c05180703080d0b04060e4206130e10030203070e04020303030f06030c0a1202040c0906050a05071a070210050114150706110a 72
    0x140385040714214101a01c544c1490740d0781c080e00e5402c2c00140c2c0024407800210750030b075002d500403101c0507040e40d24152038901001e40c3d5180e1903401c5a80c9030f5852040141c000c7c0044007144e00702100ca009400326034915295020316019802c40c100a541c0e503220959440d40c1c90f540000020071002044004514282c0c0509015a401d40d00d021800714420780806500e0302250014442c0e070f456000d0800543c03088805012581d00844e12148001c490741c07002050361000c65003403501c9180c440c0d00144c2e40f00d0440c4145428189603a0201c5120030b80242072000598000c0706403640b050741d401071150710365640000a46481d03000c07160301d5003000c00d03020042905154011100700e103500a880610920f08030002c1194440c480384221400503d00740174031502207106800402d401401002d01c00d90300c002209020390b2400301a02e140005d40d00054040003024554065280100851030000e05840c0c2c40c8404910b08016540440440000c0000c0c06420000254411900384c41c5070700d5032a4807106681c4001d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 130964001 1250 130962751 130962809
    0x3120309060506090c12060609030109050d020705030622020f0909011a061801181e1d011a0703110102040303080405070b0901140a03090f0305340318 66
    0x7030340c449041800142c0d2034100641c98501500c00040300311700e071500b5008000c404540291149501100402c901251035500340644071205000c0e80c050403e04040000c00f900e03000c80365001d58060340012041181c686020450101e45000303450b55540140380504c002489041410a410b9100650b00c0c240801480154450b0764103080e030540c103480d45c5040e0b008028903809203800c1d042007120400c960342501d504c143c1035580c8070a807111b01081d140d600c881c0b45106070584c0001c100241d03018442c04000190402200c0c43d0a020b49140741042e55051440040100c0d80f00d000c04000d42ca4000b451004061107580605c100c22104d4008648540e100d243c002c000e00400da0302640c40744aa130201140341d480c2e174400c80d0b811541c142c544d00c4d5180101c040344443c9400803140c03c81170655400c01d03500415188002e211141740f01c1c0c0e44040e0f03145240d00442154025a00e0181000c414803220481c03a0b40c8541c1340622aa07030181441c1303061b203010381e000c44070295540d08018010a140b011030450b00031502c2d4a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 130965251 1250 130964001 130964003
    0x60503070602030403020603071b0803040b040b0705090a031b0806010e0109060602030f0d09060212090609060711030d0f06170d170403050313020a1a070c0b09011709030403120309 79
    0x103851480c1d036110412a030301d01070ba0101030f40c454420401b1584842c05070a03044840d0903601440d5101402c1070b01d031680e094004a50a450403002a000c00041090b500003030b0343d03c00c3e4030b4202a42010392480100d1800134041c00010005041e0000a448081503106804003c01000048484540c0c5820354400b17100001c0c807a0031061802e08401151950011050b82c05140da80320015081150740010003003e00310002c0c081d43c41c070f0703400c1100741c594941d2030110070720032100b880080003d41012000c80e403034000d005105108004145070800d240d07441c08411144c4681c2560008580442044140c2c2c004007410760000c1c41902c1040c420b200201400324440404000760784030f01071010300400c01803000351012200100014070400010307120000300c02c016480315002034138503520b03280c84110010000791086002064500082500b4080080b01c0180c0c0010780411030b92142042c3c7c51200182c500000700c4070607407502100500051407503000304203031402142c10100e444011803220710040d00030000311030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 130966501 1250 130965251 130965253
    0x204030614010e0412120b04090f210905041a09090f010c0203040620010f06090b0906040e0c130905060f04050c031609090615080c100c02100e03030903060109060503 73
    0x1c0009a020104006144901c0d00705584c100c226550740012070745124400202c0c400d00340d890000c0d0445440301d10035034003164420503e0000b01032681c1810314070040e444184801c14810500d00d44082a03102c4031400c21903400303980104006a86e0103183c1c02e0410001c800c240c0203030500e02000209040047c0c000c148107440300080103000341a5a080b0380724490340c000c10001c20b90781c140c125415100d41801c11028144000001442801c03c0003e001743c2d0321540c001400b06444082a41d010b1511603080d0b40c001ca1301312810060700b1040200c1907211180c42410920450000304c00500c50381d2680c101c10b581a6011003590b082d841e080c2100d801d562820f0303c7c291030600c0b80d003501c400c4c2404d0010300802c50340e40c0c480384e110080c3c1c901031401c4042e10b4074850460380359489001010a101c01c4079400c0c009408414050601054441d051258280300480920200f05941800c0c00140c0c46020518482010324a407c4480408034004240707144140703240c83c0d82602c150b00c00010610b070254444810f88404070 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 130967751 1250 130966501 130966541
    0x90212010510170f07060e21060a0c050408060703150801110d050f1009020a20070603050c0711060a030209030d080702060c04061205060406050316051c0b0703050c090402040306 78
    0x150040c0c1d03070380c004011800344c0c0341e01c0840140200c0d0300425490702d075000010310904240704c01d04441c0001c65480303041c2e2840350780014140300b4010000e01907000703c4882c174a0600d0806180c0504103a4600001d0041c1040c16510701c080c000e40d18060f016500608458030091009840030b00b2010020b91040c21181e00540c40c01c804104800da050180c42d001d020f0b0940d4800c10203007401da80b1402544212480d4082c00301807270758040904a00d40e0000c2c809908400a051614a01031002c1d00307031900200300c039074010402c004180020340640f00441d03070058141c42c040d0312041002410780080c800c41d844c02743d161280e0821917090b50b6001c80242e10400e810350a4906e41e48a100c14442c190240d400303404049411058a10445100f0341c0c050342e4402402003000c12640d50380d0703001c28180138410704641d4000c0d129050074405810301e40c101f00790040c56524680841c1d01d080d200c50824050107802c0d04205074882000c0754030b8510501c00c1d2a0300100080003155141c2d42e078a8140000c1928205c41e500e1041c440c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 130969001 1250 130967751 130967789
    0x60b09040201021015050a060504050a060305090d0c05070308031f06081302240c03030403090f0b09060a0207091805060c0304030c02120f010f052502030409090212010510 75
    0x160a64059039060f0000d1400414820303200740900011a82410103240c002c10002c0e45e90340d20460701c0020140c0d51922136a80f4100f10a11607059515041442031500700303c14010182000924600c180b0610f207400340280d40d60b4540241840d00641c0054200f50000c002e01000511f00d1050080000f1000d14000403c0c0d510305040d0354044c0e017244d05080b03440041150502506290300002d0507403001003400c245107904503941d0b04017a00180c5400c0301d1a840031003004101908600b4182c003a00c0071185100e26146415440d43c020700c0703004042d600512000c41c0451035503008001900207080004014002501302d400101040c1c0040c01d01940c4500c1080c003c55081c14075841228003d0f90142d441341880c0b5841d400340200e940c221030340300040b03225080a5014220b400e02c100c80e241c40d03a548000c1018105042e101000c1070039041f642ca0b103940c11442a083c515000000c50782111131500c00032510003924000515030349028902402a54201010001c200030340050b60b40c15500d20800e104d00413490 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 130970251 1250 130969001 130969009
    0x90418020112021b030403030507020102150c0d020a02011509150911030114060c06070c0201080903120f0603030f0c060105091003051506040906091a0105010c030206012612030103060b 81
    0x506000e404500031401e02202c0304803940051404007803601a086071031640844180c074541c4241c0c001c1e40018004512101150b0741406010141f01600c807121595041c001d501d112180701c1ca0001c02c029070784c00250764801500079000b40c0000c0010440c0700a10385d665501c0c0d54081c005070155001660106940031500c01c0c1507204044071801d50400300342c10340e800c00740c0c0b10901c400c840c00030313580c401c1041c07020b280e50510400125101e01129902c541c0c0c0b2126034800940044c001412404c01c6070401c0c8000c4810210303544c40c1d9075201080e03c40c45420754a80d40003107800d42c80b52000c440c00c000743c0040c4140e000100004d126040790416258a100c96450300100700b0191800d00004090380c201941c6111004121481541c0001c5d004000081c440455510801121b000c3d03502206c1600048020383c0840d125407082c280100030038209500304800302d5a00a4036408140a0a0360190b0860710220113511505842c050221940003200e039800c100c260b0100c1d0759002444115803c0d800c10a0122503414 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 130971501 1250 130970251 130970291
    0x2040e1609140103060e010912030204030c0b03060d02040504141905100b06070b190207050d030e06060109091a030706120b03010216030804170a050403020f0406030c0b07170409020904 81
    0x454200d080e41c0b66400c503500d0a02900d540c0c01e404090750b407151401e802181c10301e000f503000040c045c1c80c0140d41c0c51942c03604140503c043da02a020340a02402040b4641d1910310303560020303a40c11a03001410f41c0e00c3c0e00e041d03503644283c1d00714143c00e4401d005000ea2450030203032000c50010702030021141c011540c0603045081e00d08500346180c0206003030100c100080d51180d1041d40200c02030b40d000d04480350b000c03c1001281c01c411006d50391039002e281864499034040c130895072022040401380280c2d141001c0040c1001819200d004100c0b5540c0c08001d4810104041c00346025800909488040780e41c0c0d80c0041c0081c840d501200006443c02c1550b603241c0c82c0c1442151a407000003c50115600301d02d0b10b098540182c0200203450710040c0b482d06814410310b000041c2078070340b466115507890714154010b000070980e1541186004920341101800810401000b01b01200c00340341202e9542d101520b444010804240d5600d0030f6003d0102d0041103a60709130b00584510300082e1801c211704800c100110030140 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 130972751 1250 130971501 130971521
    0x90b0603060105060a1d0301050a1a0a050f12030403201c20030c0a0306050a0f0501080c2b05060106111c03020c0a080c0304060e030604050d080403090302040e1609 72
    0xa80070003000880c00e004d404080444044241c1c41d40003800c21b40c000c603003510012900540d10554032011a03d050b1403004c01201404003e41c4c60181c0d40c1e00303140104400f0603000180d00e11415020000a1100d44100b048030055640034203407a510a4034490485545a809000c0038800d103100c0c013200b142200d18240465180d60005c2d031814440c00d1103000c60484403c8900c102d5003501802c0005991034890001090066104880004a602d04808102c1c00c4500010100310498201401080000c138000b42601c1058411640a151000122680442d0340c0040078841101c0d4002e0090b01c05001000c920a8105c540e0764407800c00f0b00221300c44890300c41e6001c211580c05c00441c0c2c000040500c5c400e0f401307400c06000100450306810141c0d26103100d82e8210440c2c010503540009030a0211540c00404481709100c250002e0060f800c003035031043c5d01c40344004246010000002d002070145445a00740000075500680100201c0010391740068541c00c00081075003a01052030800035450980d481500701d10 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 130974001 1250 130972751 130972759
    0x18190812040e13050a02360109050106020a0c2c01030f150207080d15050301020d1508010c0206010306020306060904050103030e09060901050a0e060612070206040c0801020f04092d090b0603060105 86
    0x450780a50800900100e2412020074501c0460211840c50b55840740c09080c601060581183c0340d2700d080d00d01401d84405070454411500400004000280442c144005030b03241c040186c0b141700e822980b80d1003128030300c2203503e034080100d000001c2405a005001c898241c026500c0800b403181c20320064082e0f00c00d02d50000c00745042003100580425007a0721014001b0510300c001900c4996a500081c26a0012441e81c2925950303895610f4841c964040300c000141800740c000d201c4c4440104002c0d49645051001a107501e800000040700d643e5110f00321820100010410811561a400d00500300380c04d00305401d015100c510045101342c40e104d508141240c1009000e010340c5824814080048480900803d4101d07200f070040c61028030043c030040d0706c14045d6500804052070f05081c800c86440090340511a43d91042080394040c401c407900700ea054901030b01001c20101c0b1600c02c003002403011710907620728031202e810310303503034030211a800c81600e0f0740c0104941da83c01d0329040205030722581c00784640c581c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 130975251 1250 130974001 130974013
    0xc060b0a1a03060d060218090609060607080a03020706110a030c080f0106031a0306040303141b0a0305070c02030109060b01110106050306150a0e040b01030b07020318190812040e1305 80
    0x20403030802000b142d120070041c2c0362009444196a84400380d0b089607031040844c0009031034045440c280440181d9018a04a4844c4500c0c1008000304410303129241d03000d03060040018443d10744502a0301140c808650080d0f0400c0320000d1002c0244041d0803ca8810001070b0800d480c092189100306052406100000d0102c0003e074a04003003900245840444030b40d8924400340240401e40d002e00800c0d10840c0280c402080c0b1028281140100b8400142410710f40d08079070a1341043c401c0380f642a138182c4455410300203140c0d110380000b41c5120801c960000d50642c06d22403880204051034002c0d5001d000c00ba00c3c0c070400180520616401d036002c500406030941e20900000d101941d04886500d542000500095486030712190740d0080b50f2411601078484d0344078000100108000400400d60040441c030143d8145488040c0360b442800240c2581031242145d100690b201d00506072401009080e41c004441000203109010300043c0c00520400b0b00c507018440010b4000100d00c0301c2440e1407030340035001e449 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 130976501 1250 130975251 130975289
    0x7140f0d030e1203040c03032309010810090905010b03060a02040602030f032203030b030d030504030c030f020f07061d09040c0b180d081306110304050607050c030a030c060b0a 77
    0x30300880c60a1245440351514a980c64083c06008500640c0034040d02c0c0521429400c0c080c2020000e15040c00b0b0b01c241400b0028401c0d48000d041e151030010034a440900342e1100b0040d000b41c3d403015089012410b2804850104100d015400348180c00c00c25019100550358035807207035081380558410301026030410848040c09035410170040d640a400c03140c58598000000030500c4d01050700b650110b0209036140001e210918080001071707460103aa1809020b00e1a141d82c0c01094602c001000500348290350602000890080c4006104c00d108642181c4a5030365a540051100400c12500c113131107680c880440d00384c0d08050100a1003550421000c8001e1450050071000c540e1100424000804044912190302d559032020224070b03e004250035031301e4040c513036480c1004008691050040c088001c01c09003030f000303010060320b007102c02c200e075102e4036120607003016401d2a03031003452554580100750340d001c10550000350100020b40150001c100c034503200e40c281f1080c0541401580400018a04404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 130977751 1250 130976501 130976507
    0x11203020a0816061d10020f04081507091406162f01081e0105010804050309060d0902040b030a1509060e2b08011a1b06190c030b130504050703140307140f0d 69
    0x407001c030240c230407407034039070b94010860400500040d03030200004158240110140e20440d44409054a074103e403190f0140c00000440300c1c80749210b403984503040c1204007410701c45c48408044243c2230346038109000c851041c400c000003c1850090301e000c00c40c800c010a00b07900108803415500090100038a00590030036005481c030000040040326584010820f10071940c0301c1201420461a440e01c001c80d002c0c16030300c10042542c011803005c42c007039408190340f078012442a440c05405140000c00001b112205c81c203080c1c0141814440101b002d02c41d102030035107021500c06d8400552003094107007540440402c1c60444020340284038010100c2c42091401d003102c00d0f850018007910b0707005003040f0710800c6080c0280e41085800c840c001101c04440036090200380035070140040714036607841d0070420380c1c00300c0c40010741e07000310365500c550020b9641000408024041005c100030b15040381c0022100b0381c80401040d130302c0d4032803c0200c560310807040362840c2130000000d000c5a907081000c06041b032007000b20021 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 130979001 1250 130977751 130977757
    0x1030609151e090204031a01080c0306150d050304030b060103050705040806070509061c06030c05040209010c170c03120a0605010e06031609090204030302070801050c12011203020a0816061d1002 85
    0x81c0c03032442042c500000c2c400b03114401400114890100a8000100032012010f80e400c168061403030f54000103801c401c281c1d00412415070198100417031254510340d000108021076444a0000c0003484001004001d00c10840412440792400745e1701400075070b8030060105c0307050245104d03a504a40c003100100d4180c038010405803e2440000d051241040c075034030040400d550b00c02c090080c803035130f42d0b280901c203001c0401004d10181200f0799055180c0042100000d008660401c0082c007030f5510340f807000256034003079022034100b40000802c80b501c0f100000e2218000200c240c0d88041e20360715003030000844d540608003245030040024503040c00c43e95209040765010000c030b50000c080161400000c07032415104d101034005036020ba8000c240c072504203600076084603400381803c500c10406101449a11940d0f108070360544002c4a514402802d04d407074164a000b02c800001007c00708003081c0c0e54640c00c900c450b0044007600030a01444a0300c2003e55603205880b80355110101c2c0e0304910140d0765194506d80003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 130980251 1250 130979001 130979039
    0x1303030507050309060d05040209180309010302220e18060105010801030605040f140304031a0907050d08090a0611010c11120703021e210a020c0f01031503050601050103060915 77
    0x3d5a10301054680000c06661260014103580d540d0796050105500300381080c3d80d40070219101c0480804c140c2800c40e942d0b401002d80171410140c00003868080940103106515003103070b00311100c0604a48440d28140000f070100e4040d00041034020000a4848001824504072107040e11782d16102e0742035403144000b501000b40240d464200215107000019418440c69002c4803160000c3d5031610b04500c1c2400044250790701482c202400c0c103044c00800c3c41e000c141035048034800c40724040c015915241080c01409114041a40301613030300000540d2a82040e401c6840800d99002004626800d2034140c44c0303c414811604026808240d94030300c01c1c20300c0e00080c000107010b40126003010303440041e00200c611865516056a030005907000d80c494078181c0060300d80c0d596141080b420145c4c0300300700035034504070100000d10401070611881e0700b40c0d0290740410403c4808900d101d174590340701e04206554076000e104090000380350030b90018002c07215103d41c2c0001c5440f20180d204140c41c2c03200d00c48001c407070159 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 130981501 1250 130980251 130980253
    0x80c121e160b0f070e0d0c062105010b090f060a0c031110050a0b0a05090f0601030c170405070305060c1201120206040b130305011401080d030c200106030512130303050705 75
    0x11030740c0003188030861024824004404280c1d0149012a002000040131181082c000c140044141001690f080115000d60300d15146c00451500003a45c00c60300c4484a03008004500d241c00000b00305042048000c03d0004000d48403001880c6400c4180b200c2440344006410000f956030319400c0c006441003a8841030041490101c403965100941240c040b0341003680d24110b4903698680c00c500c42d0a051001070018002111003250720710344090040c5080500905550401d0341d1035038066030f42070040d50001036111248114000520301894888d50702c6a550006a5603440341100042c000450401280c910080d5540440781e103901c0c0000c2c56950913079081080382d12101c14400032400000d03081c06030109208007040c032010b882c6503003001c0303085500350300d814080341c030b030220041c0112400050040c1130250b0b180b500003907103205110111200b104480d080d581c82088900700e1825000150051804e4a0054080e40c02c030b160000a0320980340300364482c1001000032528104003090051019110150083e8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 130982751 1250 130981501 130981537
    0x120307020c091819140106030203060c07030c0c0608040b0108010c0c060b040b030334020603160c12090608090f0a030f030605040207060203010303020c04090c050409020f04050103080c121e 83
    0x2c1a8a801c204d84402d071420140e1007041e26105101071322080d9801203030700c04002c100c2c40b811900465181d03440100060f0080e230700040c44a0070144501120088550881d0f84103404a0b00d80c0310051080ca0140c41c295403a00d10304002003000d460600c500b1030709140300d032200b910075042542c91001800341480829845681c3d08440d10b4662003e0005042111540300c007050b41c100c039036801c2032a00080b41541146030408005100060b1914800c4076040042075071282480600da0f1000c8800f1044110f0052085580000d2101c2d0950010501c00954100342c0710a141550b9503d8690317610101c82e1421580d99002d0748808010034000d903a805484400741c6404221584c580b004517003660b01c4040700b02c50300c0342c2c000010000d042d03052114981c1958121030030301c00c40403103440305104a007840c0140391040b50f89500e01c1003159030b1150381100d641e030050000d10080d07a580c100f10741c40e0b800402da0f00d60f01c1e0161124031603481c40d66000700c80c80c3c401282d00340b030b074214102d10100b0300580040d4140c0480a250f1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 130984001 1250 130982751 130982791
    0x2070f051c1a06120102040e01060c050109060e0303220206030703021c0203070c0c0603140a05130b040605011e0608010b09010507081801091a09060c12040e0603120307020c09 77
    0x403050b1048600c400d07906189050400c0310a1010780004488078011a03481400180000180030740b0040c11220b00b031030131800d0329490341015401041291401421039140004080b024580030020314440d054410382e629180f504151003031094200054029030103079003040082c01d00c0e40650702402d44a40d0001d10241249400d642c9a4100d0f032041d150032010503101060803080090455944000d8039052405210b2a480303045c001103039010103440300a002e91200c0018800001041e101e500301504030114000740e0803d03092960080500b8000d40034101061006258440003d100c0c1200b1a8203a80d1103138610f03807911015014640002104904000b030400c20702c0c0125011001134a005401b2714002040c1b100b800340003524002d0154402090040141c2042142000c414152410400c0c20787e049542d80b4442c03050a42400103502095044500100d40491640a5020550311170712007a0111040c002d0b80d401c11940d180421102031005a1041a000409060071021290401c02a0410521031244 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 130985251 1250 130984001 130984013
    0x40519050c0a0906060c0f0201051c050a0b0f010f080a0603150203070905030c1003020906040504050c03041118060f01021204150305010515071b0504060609080d02070f051c 76
    0x4108400c0e151584400000e144500c1c040341c2c0100109440181000414940b242c0a04092660784d006000c40c40504200d0082d64052021500380c9061910b40240001808005d0302c010035081c1e4002403110b18002140c01e440c00c007a03000b040c41c0c0e1f9050316440030b0f6a201040458000000600c0060302d241c6502c0c0000000301034155540d00b405002801603140e2901c070900902d0f01005074030084c481d40c0840031060480e1036000e0507019420a910340075946058042c00b01e24144110361046030440e00c1c26040202c0349070380c07401640c0594481c1c0b1030300d440d03031200c04e0410407003480c004002d031050700d090004900c0e5480d20000c0c078100303040103005542280107014104040c070340180d80511001481d030425440303c154184155405000211401c505102034001c0b03000c4140102c2600400e4030181c810105246e03d8202054001003000070302c103100b00781e104c1d030300144050800d02c20190750f84911100c03900601d00103c1e1030f10940301011040480180b03030000b003105003106040f400f02250342400d01100443c01d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 130986501 1250 130985251 130985293
    0x709020f0703030e0601030b01090f060519060908031806070317180f0604080f0f0f0d0f0c030e06060f060904050a15080d090e0a0b0301020c0d0806030a020f090405 72
    0x2698903050303403100024100501030b101100440c0300d098002c80300500002d00b00403001c9040d141c02020000380043c002c034080380201041d0300420391040d2a9a0700100b82001110210700303032500d5a9a0300e44e540d5840403001e0750b07405198076201c80d1f8000c503101c4a80e41e0a1041c05004585e000f450043d45000c82c44c400c88880c40350a9a5006c074100d40e64003082120314042000c400000d40f60b20041810f071805441c2c818540c050280121480280001c0c901d05140d0702d4802e60f51540140508103641d4410f0014000081944407288880b050030302c254a01018000d10901100c658014060300761030340c3c2e074404c200d51134028400c81c41e880034040c4807100a588035480b4142c4514040031001901c0620b1700c0848102d814246d000d4170040d803102c10285d034410b5002805004854102e4a040c0301a112004204050400c46003510b40541c400700b5070000d400d80018800324180c1103501c0d0990f040d2201400c1c503890f0024007801079001600c0141d1110305081a00c45a0b80c0a0f0155040e103510a002d030f0710070750b2144 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 130987751 1250 130986501 130986517
    0x409060f09031101050711060402060c0f0d1e0807051210120b0105030c04020a020d0807141812010e03041a0405060a110606241c05010f08010f0509070e09070902 71
    0x5482c0e0200fa4002d03603002d1041c01c0e0071042500b00b0010384000520a0b950340c13070005100034040d680c04254110740758020031614410307440c000d096850103900104010095845040e0040540c000041082c27005030003003182902a4140ba82c440c0d1921025000702140e1000c0541684445855030400061089207000c6411850344690580b04603940b4107020145007204001c00f03540300382d20411120400b190002508800301445003841c402e1a0355a50302075480e4117000b421a8092040024034910307480520501c0d07141c62604a0321052800f089520703183c201e401e01c1018410a5000308014130041051490540503c1c02030f00c5058070b01515400407036140c1e00405440c0010075140265800c50000601c5215480081558088000e030392041e0381c200310920301d81010000d0b150000b0446520010711110039094000b0300000c0c003040d40c1d02c6d0342c003a1175419680b056000e40c0d4a03115103048182c24030700030782c3d01034101030000b000e28904005101c0620800503003078100b00d11414200141d1230a10f400030704224 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 130989001 1250 130987751 130987757
    0x40c020c19051306120b0a0e0303040309032307170a02030d08060a1208160515040b010f0501020105151207080a200916050c0a050601030b010303031401140409060f0903 74
    0x158641020f0044440104022039086810020103001c1102040b990007565500f0004044560301c0b40a4403400915050f00e48402d11302000013004280b40d044031000d812a0310170b5962412910085c401c010980c4551100b2100b103410986003002001002c84d28080d000000d5030903101480703403a0380003901e450704100403140450034a000300185460200e64101c01080c0249070310349109459130318071406100d80807401c041c81c1d0b0210f03a510103114040040454880c014905500c40303007014140502142d00074400e0802172200c02102085951040c0646409840050404204600d00d6001c10030485004103055610b40b00e00e460000b04040104102e06415001303c17180007280d08041e1501c2e144201080403d4082c07052082813142d01a5410448103042c20039103000b54a0316030b90320f042410940000000392203441403c0021003842241d181c258101d910a440410401c20401c4030403111110134030600c010700d560158400309500309900a00c940600c60140000d892000082d11000c9945401d0241c0c00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 130990251 1250 130989001 130989049
    0x1020106050628080408070b0709030812220b060907050903070312020d1e120204150e0f010f171f0902070213060503210d020307050c010501050405010e06040c020c 72
    0x901d2850f0800c20320010040c500041c86242c540c03030711075480c4100d46009000140540c00101d0f5a0701c01c030300d810091030344040300554078010842e00d1005000103a9800c2c09030100c00c0e500603602ca13000032400080e16032060303000303c15030f03501c004100750580c0040100040c49010020203006582c10f0102001840c07041030404030103501500000e2820500b03240c40c1007441540c02ca0000c0b0400c1411303428074500b00d0780c509802e20207030010441010780165442516104000c01240e003403a42c12480395007140320140c403034032004ca11403070045903425014024400072580070b85d0440c0c98a01540300303865001030006e601d0301000c01048000001002d6560005418a40c013040700821450030001c69418241c054006100031803c00002984503981041d55148440e25400010400035011095541000191808645914100c0d0014017030354412034254256520302000800caa281c41e00c140d9058039050300381039070030ba035540c02800002d0180200d04d0056225040400a15560307106aa0041c0301c1c1e038069000c9 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 130991501 1250 130990251 130990297
    0x711060c07090b0303090105070618050f0106090f02032a1201120b060301060f092403060b01081e0103020f0402120403110f060606031f0905010603091104020c06060f010201060506 79
    0x440d21100b40c0783e4400c2d04104203241540e0383c80410740b118590010000600107523800500e500903005501c005100380103141c607201840c2c2040d40454200d03410000e01384502034801641e00100d10044443d5410801c444401c40e070045015035485038910b20000310580b4010469054603880c001c243d005021101100705030a04024502c03402c142c004106a0007030002c18200007402c41c9a2840b401042e903625560400b0220308016008144810003000c119041c4407516810024043d000c1e65410a0108036000c0214040000846410005100c102405000c0b8bd0a40c3e02700010814242c650507880b580a00c8001034590401e500180190310a4440d0400e182c0d2400300f442c1480041509107105800c800308104c52500c490080781e0340040c254600300c0400942c500101d4522a040e00007a10b0b1516010010071001d415a20900c0840d018405121010424504000580c03080c1003021401d5048000829014200340b02c8a0f860580c0500010640f140c50710080341d1180c003c120031200f002e02c4011855 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 130992751 1250 130991501 130991519
    0x30a0204090f0216020906060d051e070212030708060a05040c030f0c030c0207030b070201112214010509120f01180209070c1a0438010602071a0711060c07 68
    0x4002a01d0640035800d00b50182c0904d070481050010190042e000c0308009009a81d400e030440c0c003042c8424100f04100c0c180703054100c10740302280041a2841c51500081828180009005591040078001c40c91441d65110021035020501504807504100181c901040a44e5280201d02680038159000100d00d03600548440503116442450800e06242119802c8003980c0450107505913500300380100820303161658203d00401046064210303840011403541c107408056680e51044a40c84a04c0c141365689403038142c408402c01400346400b0030420890403049040c80e80300b10088441c0c400a4519058402c240d96007034a640844103544000781d03001800031882d02001c2990000d1151811440742c500c9541c3e4061a904a20149104000702c003001a0400c039500129943d503002d60070340c000c014201c82408107003e45460754201c100c0030004c4000f141807840007400004845987ea4841c4101b044810092140d52010074260340c1d1445001c1b000f2100c0d05e13400000d125803200103008156184c070b0030100d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 130994001 1250 130992751 130992761
    0x6040b0f010503120304050f060f0907151d04060302030f030a120c0e13021303030818011109120c030d0e1302072001020a0b0108011b051c0c0212030a020409 69
    0xc41100102006110303070b80380096540700103880e2a0b078890703036919282843d03850b000a07411344104522414007000200d01c003180c101c0707028020070400c9608240d04c54030583c01c44070a06680c00c0008990f5105602c1c0005080115201c5540180c00081d10a8803900801d090000e01170703200c08130f03034000a144032030144e114202d08400003000008100c4004c4085005080f070417080c010b40d100c2c002640010080002a41c11241c500320215007981a003545e070b240181007200d04036446d005191000c00440f140704018056520404c41100d4868980050103003044107040c1c0d2590005050301c50704501210700c2d101002551650340950f00c40c0b214203881502004540d40c0329040414940b070050016000180481c125810b501d500c10881c80303401000c0400403450300150840203803560201c103000080b010019480307105240502045014180b400510689a520904c920030061004856006644d92a194440160754004d807040d01d20910704412000b24075001a610030404650010701009400302d54422 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 130995251 1250 130994001 130994011
    0x5180105090a0306021e0c0c0108090303040215030a0204170309031606080105060906071505061306031703040c0e07030b09060a0e060411040b0c0715020f0a060c05041706040b 77
    0x403461074141c81c000801d500400510000f0009600494249042d1500025441300e562030034400780c4d2a144520180342d074420010115a007c80d241c103003c500d1000002c8102c0348582d80280c041045949404443d524980c002080c40c2640c1307600b03000119000600c1620316811101c1080110b403a884204105802d000302c0d604201646a03c00e00100544c0c1d400050311811118100c80d05a1100b9000e400305199100d160f40081c1001d50808841d41c0e50200c0d1f502103802180c098803200385d040e42d15503100084035090300014010742080e62420030009030107001103500c2880703020130101e815070f940d4074140d50701c0d02521584082034031800d0306503081c140910003540c000d408641c5041c80305c3c580f400041c070b03100c00034040c01d0003552070321401e81100f0030f198100d4005006030f0001a5842d00384003281134a0718603d000301700c03802d0070300e48000410902c005400d9910081900c086c0c61103816a9035480c00600a2458030024044c05100000b22414031103900d0440709801b2002d000705282c94075100d0505407000705 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 130996501 1250 130995251 130995257
    0x20c150901141609030206030702030d050a0501120f050109050607111605060702060a0311030a0b04050c0a0512070e06031e1602030d090c05090124030e0c0925051801 73
    0x3401280801d840c40440e400c03141c1203186250700315900f0b40c1141c004038240c00c0650000d00c00414070001950000c001c051030408220200640d4641c0462031040c1c1d01d00784505c40001000725418000700e983d401c01c103041b0750703c610000291510540d841c203040c4102250b044c0040744040d200c0c141c0340c0105202503d81100c83d030480c0c180345400c01d0f001926500401401901500d008108044814080d0b880b5071a100003440c0e002d0348a2810542403c0038058120059000b58140740204407960f218105803a040c6056441d01418007a1642900e010807000400401c1002079240300080c2503114480114005c12032a02403071440030342002542d443da0780c00741610007078004800100d0100c40e4040103544085600540c0031030000c045080c801e0160140ea0400f0b5440f4016000000b80500c2100c100f503514040380c07d598200c0d591540c016001c80f9824541d941c0f0a40201036a0480f6140c989a00c943c0130300314058101d00c0c0c1da42c86400c42200300303c40180501280b4005044a02d00480c41e100d00e50b440424170b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 130997751 1250 130996501 130996511
    0x20108070315060f210e010b0105090604030206030c0706140f0f04020a2d0b09010e0a060903061d0a150b0d0302030d0f02090619030c030203060319060b0301020c150901 74
    0x408000c110900034403940c0108004c04100d800c02034802c00c4581c14009440c0300d44240c480e0460145001030611515410840d0b1811651000c2540605c00380c0d604104000d0446040515540070300407194401041c0c0980307004100300500004500d8415844218026400d02c80f1501c2e08440d89041d00c8000b4008403401d1504c4420000143e541071404d1003522240e281940101f907006003044c44200244007030b4252480d1010010407802620400f600c01c18170b090340e449400d0500001440801e40300c0e40900c0000070043c41041c0042a410303009000c908400140d04c0150722001401c03d03061400003c002c0756840b208442c014201d422500415483d000308507000b040c00580d682e4040c5d0b07280b080301c2d0b1030390740d007500c0f490089421802a41512140790014003410ba542448511000d00e03160100341a030b0110703142c9202d01d10110310920030760340303d0034020300140843c14507a80c4400c1103180d100b00844a00d6100c565071501514280040c00b540d212a000801c4c0340a84400c0c1d030811003a0090502d1a182c0c545 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 130999001 1250 130997751 130997771
    0xe060d02060d090201050c070e060316060903030302090303130b0309060105030309012a051e01050a05070f0c1b090209010219020d1b030b0117010f0c02060a020d0e12070201080703 79
    0x80d00460345070000000b400902900240700603111030084c08503c802c1401080c0e0009110600702e07001e20300c207500c100d050300c43e00001003500d4014050300340540800114102030a10001e4003076401882c00c8100281164148001034180805288841c1c210421090001c001d00117882c00070020603000d04811400307503040800980000744012403640f400394001d04481d16503034000880c041c03140203464110702500c1c4a01c0700c20000341660000079142e17105543c03803c0c0c0064240c5200c1e100e1a03008096559803140f10b101c407070004841c0102d283e001503071a048921002c110585142c0c80090040c60700320b00168540030404000390924078a010b0403030103014501040401070391201c0750050a5030b4000802e0080102c1c860041c00d1032109034000070603030a40f6100104800c000d00ca041200296000d0080c026a099420528242c640e0004d50902681c4840c021502c2e01c4100e8001d03100760303540c03032400040c034242c41070810b440e2090200c1c10b240d44000c00100300066580c4420b809900008c6410309101188236 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 131000251 1250 130999001 130999009
    0x91b070c090c120e0607080c0f040e25030606120c051315021002030103020f150f070804090c0e0a092711010215091515100e0a05040c080f090114100e060d02 69
    0x10044c0b40c000e07a000001103107070001c002c0504ad05d01501051429400310b180c821f80c15084002e220480684140030040c0e01c2d01c00521a0040d0030544000d03aa98181d03101c1011042d1000c1d080c0c0e03041e1482800814080e9505c089040d48040004000407031048c240b03520410400307401d040c2c0078040128481e004100500158a46003400411102c0565800034030b01005840400d03180549400003125520000c0c00d4020701014001406c00c2d102c030400c0070003a20007407110076920005154400ca070400413040082107107090a60060440c0d02582148030a03804450754038100c0b070b0300d441c3d0381125002c0d555182c444895a04002c1020000c00318107591440e81801480d85e5076800252200148076040710780050b80b581c4024100c516141c9024103084039a41d145000500100411281140a205d0000c4009500d1070310b130145d400d82119030788802800340c5507007003941181c0384003d25030349c0c0c150b48520181900c81c00c43c11140384200700c3c0ca60b902c40d801d0b0400315a00040c80016205600c90f65110640f6030148c0c6c1c17 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 131001501 1250 131000251 131000267
    0x20c06040510020f0601060e0a0e0708040201110c0604080f0c0103091a06010201020d1e0c0305071b0c031403180301110f031e0c040302040b091b070c090c120e0607 72
    0x40c040b01c1c842455504201c0407494140c100341a0100340c061030b400014200c1e0420200b1410810417104810941d441c1d1001c9002c01a08481c0710b400203601001040140d400f403d8802e00100c12401a901c100340e05c000440c4e0a80e01c5644031150130384c04503125182c030355404d00040d8100c94003460140101d06060b1158420780c94101c18400e58040900081001c1368003d43c1121088500c2c8a014800c1026060030340010b02a0950031094150a2084600d0060711074420180700310000d0302c845004000015003c0606141890121b80c0c08403601c00100108074003400c007654825064000319a6500d18400c0038440d044540d1007240070b681030122101c1c10030110010785143d11200000907441355a5150f1404290583c9041c2c4151404102d0034010a01c950000404c15a4025101401071000c3d0506210b201001160300486640b42c007000707a03203c03441c1c1c640200001800703101c80241c80c0c1c0c1c403030300c0000c12200110b804c0402300d18090646660040329016900c82042104060500b07882c1152025100e04 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 131002751 1250 131001501 131001509
    0x30f0546020a0512030405040615120b06160317090102070525032004060303080a1109060901030504030507140c090108030a02100203130b04060605010e03120a0e06090915040606020c0604 82
    0x40013005400665820010303607000704002081841559903e1144821040490f20000002400c1002d41c1d4860b503244d0045640059010300304a00c0d1140e00b01c003000301808401c40441c104020007a40d9110840001c803800c0c05038010a000503070310200e501d0103501d001000a800003208541c102400e1b032814030b45241c0811641c11909111507007082c0d108110b1240205d4811a604c18a0310001105040d0f105112074840c640d6078004001001c54080780e1522401054a6207611410130022103140d03510942019030040d1003070600d6801c100c1984d46443c0340130031107600c000c1c10ba4880c0445545a1900074043d41c01400c2000183d807520000ea6002900c8050b6515194101500040820b0302e002084c0e80c0301c040c0503049100044035080516008015009034032696001610140a903041407402003041a680c1117052042440d00b511140c087e24001c1e0726030b008662104003031000e19201c2c0c440b034001c1449a441d0340384540c5440301382c008000c11071f83c0c0303038101134210340c00090080c0c0b40b51909022074040e9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 131004001 1250 131002751 131002759
    0x120d330503120d0c26010311060423030c0a08031312030206040311031c020c0106090b0603040303050a0b04050c0d1a1e12010228050307050301030f0546020a05 70
    0x12003400300140d42c030309940301801906000d400e40d2a50b19213135800601303050f00c3c070a0070b050441c001c03a10202710072809030740101e502c00d5083d4007442c0e12100e0b442c1c044190300480501a100c542c40c40c4000114501c409500c01440f9400c0000c0c0d600040c0c06a28400010302a4005940e0420105407802952500010401001e01c2084080880840e5082091390f541d00d60090300c000b900700c459140203000e03402041d9668420344c00d000000c40e0000c03460143d226001c0018181074156562038408502400b00039110b481c180307540320159280358540703002da80d12803191101b0b02c03503580d542d0700070010031258000b03030040c005140f050701c00346555100344010009400c04100315448121080c0042c0b8142e01010816080390300c0041c009844100988910400d841c03080c01301170a4400220082e00c107031004076034203800a2810801403000810790042c11400354001e60440c0c0c2c0342203003c3d8005460b07001050f1035104070700000c0018070700380070517103052803458038400c0502141d03203016400315a01311114007489201b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 131005251 1250 131004001 131004011
    0xf02060901180b130b070906140901050703122a0807030b090712150806010519030b0105040e03090a0b040f0801140606032a0d0608030c120d330503120d 67
    0x2070403994000d81c0e1310a1342141880c85107060103c80502070362540d1042201050501c08586074005008058071101603042e150701d490302c0b460760b0701140da1000c0c50044411640d40d0b00010380300c3c041440108034114415000080e41038a0805014000003401031888040600380001c035007650700ca0070a13484c0c000d9010704200300e03414048070380e180150243c2c0c200ba00c00c04c80071a40c0014a1840061098101c55040e20000080d0280114944040b0841c6c0070103400b6940101c0100a0f41c2016409500414007202c240d0b0700b444110000101070031181e40c0580320708000880d0038400c041a01403000300070552900204083c012902c1d002c03007031207001864035104510100001d070411400c0d10200c28248280b4141c011020035005140449030441403941890901c1c044004c50350540010172160407a0b00c002c0201444400c40d00202c0055010280d0020480c1d22042c0a0800c6201c0d000404500c0200c0d4800c1103c1d00841d03414140c03c62181e501051096000010b800b40c680d40c0703142100c90842d510305010074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 131006501 1250 131005251 131005261
    0xb060a270e0a060e13050703120e0301020d0b210a080a03110f0a14180d151503060e010605090109020d1b0c0308090106140108100807060f02060901180b 67
    0x201050041e4490000d80c0750407010042c00354142d41c0018140d4001e0180748440c0e40f21a0f4422008424514005046910002c02400031901400110904070b410340f07010080300c5d14400200e400e82c0c12605c020036140c1d40720508c81c44c0d90318040d001d5242940e6540345ca5010a1900e0304165940c2044c2640582484000202c1ca4052442070f0070400b541140391500595404a54411410b03681c00341c01c0200c00905e0b24401121000d11900031242400c1d00c1e90305058810220b0002c21903018080bd000315a035050561b441c5140800d10300070384010182c0b4024000141c4e2a6041c04c2c0c003510420880058541d240c100188070307c0d55064900780c10f4401c07000b00142c131a1815407510008019a0403c034400219411610b6046075005280c0031036503109030780303880d9151948544982a224a40102c80304100150000b070200c4d4420040c896100d078441a00c5401c50b03543d0f6481c030303051401d00d402c0400011514101c0201d02a01006134070740040329800208100780c000c4040b88811005070000400c802e52000200d4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 131007751 1250 131006501 131006567
    0x7111b0a0f0e01060e010503010b030f07110601170c030706050f070309030503030a02180910090902040204031b030c1502060112030507120305150301050103020d0303051f12060b060a 80
    0x80301420018500c0a9025121910144120400d00c5041c00003031240d600e400042d4402c0040d42d040704c0321707000c08504640740e88503c810341202c0140314004001141c12085003244c02001740900900a044104506030340d00c4a5007806e0280310f5601070302036802060b0800240f540481141c0c1d0109420500c6a201c0c1d4007032030201d07103146243d03101a00500c008014410710350429030003052000c410700c00c1d0100f03a84034502401003d84c0101c072501881a60403200300b01c42400c6030000d1200740e01c02032005140c20f450f9500c41c28068901a020346450401000c18000c00c1700d500c02c100041d01040004402142d02843c00941c0c0d000140119180c5065454640d000c05001f001500d1080364803486200492602020040090a04813a14002040300801c1c0b040c140c2018401e403810b0340e03000b50110382d6010745030302d0030350160501401e1140018099541c1030000c0c01c6000c0010302500d0100c04941011035682413960554070305000381ea00c544420403051040c3c03034201d2a04900c2a820070541451815110510 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 131009001 1250 131007751 131007769
    0x409030210090507090b030d0e040213050a0e0601020105101202010e0d1202060402031b06090d0515070201050402030723100201060902070303020903010c09060507320a03030507111b 80
    0x6a9403642c204003881c1c003004004222041942e00304d61041080c205400101541c41d140500700f48003103410f8140e040c502c1d091035002020510400180800030b0f0760380d0004a4540112030344241c000050645c180900c5603428064141c10040000003949580d0601007901e03414603041d600203040c06041d1a54140e240c580d8083d48401981041d102501400803460207500c651080b11308a109005120354005241c50007030300c40a02d05800f40c038031401c2003c10800d0007000d10040781c1c00e8500b4800d9080c10065281c442070650300c1031003641d0010030942428414107140c0403081d08010303c481d45071100b0303104071001041a1141e00c40304aa4a0310400b02c0c0c00001d07401080c0581102401c2800000d8003014141c05070000c1240410640082004002d05103049403824128018080098400c00185010a0748049101e4480c0204d0025a4100352070250310586030030804c0031020320b48c00004148040c950188180d65210207582080e09280300700c000307003e40710800c3c25140d08100d500040ca4900075203030300d41341d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 131010251 1250 131009001 131009023
    0x80a030e160618050301020c15040204110c0a140105070806010c0f05070b0417030f040612020d05070c1406060f04021e0706060819020a0e2a0d0c02030f030604090302 73
    0x1181181e5250140285041004511641c2c002c0b9500d03c00681c60405200f200c8900300c2e9a0003034203140c01c0c060110019a0005041a039000c1c0e1104030540034804510024680255031400a004141103440e0a9101846c4a03003941c26591415007084400c50700580c03060381c45502403908044198036842e0901c80051100070240852080313100201e0790035170050040c01555940400300003590591000d1980d203105201c50400266424041040104c0c091201080320320150030016040861040c000400c54004565100018885d032941e10306003c000310016840803400d001401942c98144042000400b00007462801a030340011190b600014044059241e0701c00320080755034962490800c0340c0a80f415020b0604c0e00c0c0100d42c90a0ba0301d0600b2841d1440b0240d018192003121807400100100800008054224070003002c0348100801007a850542c130092442074525440d560440301d140c0840e407604d50b04605651041211000301c803009030031749030f020408680104001400340346c228102405055 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 131011501 1250 131010251 131010283
    0x16030315090c1d030c100c14010b01090e0402010917160b0309060108071805040c05030109051b010309030914220e0607050304080d0b1c080304020a12080a030e 70
    0x101154800c03864204042c0b02a655880c0300b1a80f45480700f04550322071a01c0f41c258164414601055a421724500701c003102d00e81414112042142903c4041c6500a550b040741210395442c04100d4a40d0382110441e000707001e15500d0308145190aa0001e4100c49290049460072651454010802c1d04200a04040c42501c0440c40700b101d580c4030314841c2181c1040d5200c030b256004120012034807030000103001d0100d4410302101854804c805400c000101400780c000d441403402d0110201e0651424042d12104900c560700502d00c04000040c0c11080d030540e803031583e0404d410001c0d284003195110b00320405682400c6020101844910300150103d4851160100d80c265080c01c03900c44143c3e1540010a041201403c0c0c4038260785121003202c007480219401482840d0500199400d140160312141003e0300c041e102440310071180e00d8000000e030340c500d4100d80000c0000200411070900000390401025040030518441007980e40e012090b0140c10a100b00300365651220044d510300402981e10b280601390 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 131012751 1250 131011501 131011541
    0x9061b020304051c05070902090303040509090631020f1309030519091203111e0a1a01050a06050d0618050a1b1d03030c030c01060e0c04030503160303 66
    0x648041c0d100d82252190901c075240d40d020440d084216008010206540310b40941035160420348010000e40001c1c840d1034040c401840045140d480300d400380350003141688018089450031880404404984c0030038900030309070031081401482003503190040c080da030495000c0110000709010420003005442568030143c01c0c05400c0043c0f5820000810781100050003002649007403d506070703103001040c030445d040403489000101c0460b10507042c1c20240440a402d5513107401c0b064000601545a100004510b07801c142035004c200050210840301ea200480c40c02500d6600d0f0200140346c0c403410344105001d101c0006044952890700d0340c0140040c0c031003805490303824103503607907240d00500d400c480c0c00229a01e00300e00b003000d80e80100e62171009498960b0798240d103000407680390140c0e64499460030380c1604c0b06220a00e0080c03424409820045034030000050020325060480b13030700c0e20014190b0305085008100c04d00100e2408003c89000392035000c091004041c551030110300803c07100c4400445210b0369 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 131014001 1250 131012751 131012801
    0x80f0a0e01021506030a1403070b01151d06030f0408040e0103030f030606020c1302090105071a040506070503040317062805010206070e180604090203030a030b090a0c120906 76
    0x80008109003020b0b42241c20600c2006400c00010006803503c641c540d00060020300040d5030342c1e0403140520f00c4c14080c2c0307050594a41d11001408030030b0300082402a040500c00c101d10b030340a09060948183c51107036078002e4030800c000c50028407015080c007003103c42d244001014030210800700c80050144c000b600c1c2d065a500d08000b0b00d88400c91200400080c10b081001410300d100050800c080403008142154012000009400942c846094941442010300204011481c00e0080481141c900c68082506c1c0c502490424241080102103609000c8241f0602000c298407412110b9050800c44a604464440c0800120b07501c0e60300c41041ca41c2400781c030700880b8404449081c00c0844800fa02101d4035a2103c242c00e588061200e40195040218041200300e1b0b94941c0f04080d801c000c01800000d11359143c0d4020a0440e030050a081000c02c0d12544a0b2409040000c01c0a074010018801007022408450008060706410700c2e4009004d40c90315906024424154030442d0440300d8071100e00100180 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 131015251 1250 131014001 131014007
    0x1502030a090e090d0e0103180b100f18020304030903021002010e0c010503070e010507083601030b0d03080405150907140319022110020c0105070c03020d0c080f0a 71
    0x12616840003518030600040d101c40b00c804698090844a4054101a80101d8040345d62003002c2a01034101502d074414865880f0403403a60803003440c00303007240c1056803410500b1403440102d2a4014400742c1c254040810000420308041450700c204100b0250ba6600c039410300f110310f40e080e0b400c0654080035100074165801d4055004021828a02e000ea5208e440410015580c038002121080c0204840e803900d1041984100d006000b140c0c420100f03182400303918191844040c0100c164403041002c481054240f03040030394076203030300040d0034a010302406c0851404560400707c60030006062080c110081002c100c014003100000ea02558000070447c548001c1c029036a24491080d10080921820282550304010505104200e0088845081c0700000e50074021400e007100c0a005a00c1400d80d20402489028003426942c0c5103412405030711495100c0c00942100c5000d04200203129054014bc00082d8021404007500d507000d08007001c03000340500b00790005101d81c80103126000c2002945001c0260 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 131016501 1250 131015251 131015257
    0x203011805060907050307050a0207090c1701081204030f0503070210030b0414040c030308090a080408072309010603020307110a06090515010b09040c03020d0f1e1413020406150203 79
    0x48403140900054403124144128001c0c00d9503000c000800400025080c5c40c099401000203000740e00c100d070307041a40d03581c645003110319090300d0800081606c002c028600001d40f00c280d01402c1c0310b1000d408a0b50291410f400c4910640c44020110042184040240710003403080d16107130f03034010300750151120002c400240144411180c3d41d205500d0940400140b10010040e5440349038414146c1c100203055407402d40c0c4c64080103001c1102e6120f43c45416000521000c0544000d020030740c020451507080940c50001c3c04000c035500c0285120303441e58010705658400400741110303070390300f80140d4035107841c46d04841440074142242140c0c414412800100505a805152041d00840a45849020f08040c201d5090400c3c4500c154015082c03002c40010b00c1c0c65444120200d480d41401440c25452849403016908400345102c07210355203134100b005501038440c20481c1304990030010462083c0c80d02c3c0900d800400a42485800003281110b0021901e80341d0003c03000c0e00354044043e000c188000d41c020340d658 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 131017751 1250 131016501 131016539
    0x1808030a0509070602011a09060307031703070e0d020607020103050c0f040b040e060105030712150321031a0a2303060f01060f050a1b0501061a07020319020306060108130501020301 79
    0x2c4103c10300020140d1043c850390082e03c40c4682c0d0740d0800c0c110102004200200070f801c40350305004580c000000907621429903c1e1a501201c0420b480c2c4c0f0380a80c019180d11070f0390b801c150080650008141c0181d546c2811140429030908001440392245d041c1020b45004251544043e010000b03004240e112098029100f15001e40c2c0107a04a03a690701e004485d140410b44842020030b407600c030854a003d40d160003256200c02e081040720310841c1d807502c5805c0319040550803c00d07105100c81c00314095643c1070190420001010400a000d540d01901054001703840f8840c8403014100602c01c9105424950b08a10000a00408840e2a0b00381650302200807002840f44e580401c5043c50040315413030081d41502c0c09540a51a01c021500d80b0004201c08012051030403106956990004610060b0804080c00c508045400440c0c0354046481450700d0503511610300d045892070080a01c0059800099003503020b0b0080ca00307504161240090a06800c18404d4010055400440089034014428103640401 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 131019001 1250 131017751 131017753
    0x5091018060207210b2202030a03030204150c020306010b090109050303041d0a09020a0b07150c080105030f06010f060507030519050a03050609090d0315050405040b072d031808030a0509 81
    0x20526500d4035111341034000354001c1849124400190a04801041840082c1e540000c2d61050041d46e5000a0901c0c0914030110701080e804603090010300100000c0000303c0003d070078244180701c1c0d1500080e983c0c02c030500c03480042100c0041d855810743d12491000d00182000303800c82c0c0d00c0ea512448000300701d090b051039140b5021308100c00904e00c1d0101c0d028000c00560041c0c045c0751101d04000c00008541e020311020344085984800c0100f890f0303014450044581940d41e108500b65040100b00360400d120803000c034045d81e00040041c00203103840c0d140b58080322881c0c284140e0726403442c035041c1c40c83c0c0a140034034207030132107000402c1c1001600440240442e04085c2da04100c1556040104000c010003584c06401c650310907030300102814000d40c01070601100b19900f00c440e151713030781001500b56102240e0440b0748612040c1071004030798004202002c91032005112102007460061014042942c5a10701d004060300c803411400d15800c2a5140e03600b440d0003c4c2500d6036071625034004400790500350380640e51 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 131020251 1250 131019001 131019029
    0x909170306220c030b0105130b09041107050a020a0909030e040506220f1d10050601090807080a0b0f0f0f040c09020c010902010f02070501090b1b06040b19050705091018060207 77
    0x45e58499002c540e4200022101803403070f01e007400c042c908a40c12010005401543e45e4207070801d0000001c1c050702006d8030420003408040b42d20b00c180321f4103002c0d40d07100760481d9040040711000a50440d00140079034105035400161503580000240780c8c03882d0743d001d1011580d05e80c518113032030300d00580084001014412051000c44501c0410001e4a03e60a445813015001b40780c00400e0759846400040e04498149040219242c5460360300b420241c0c190b12140c003e5001c0604082045042e001d511703403295000c007190a0b81e02d003100c0c4101d2891030042000a00702c000c100001c081200c5409080094508031900b1511040303400d2009009111411003a40031404030510300000c5880000d0a605580060b52518015032070b111401c5116000074540c3c42803040f03000301941d54018100301c0301f440786006100301072941c00d00a0300080950b22880e90001c004d070030981040462900b20040340da250b94207407012403000700d51503812141c0c01000c3c0a040a00100a00c0008100d03600040382010f4411801070209 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 131021501 1250 131020251 131020271
    0xf02250204180515090309090403030e0106051504060206010902040308030105240a0e180114040c0302090405100e0108070605030f130f0c06031d060c070f0b0f040c0909170306220c03 80
    0x1b03541c0c00783c849240d0384044408005000244a5004400c0d0a16003000101d88070f030300c131070006202109014103428150408102006200e50401050f0300515400508529003419030301c6240c030512050240741d0042150f01166106a0440f210030103000c0940a103503900d07003198540051051004914091040003850076071060201000000781c101c903c010740c1d0181e043c00d178200340702c050512030b070540052640c20300000380c0c2c5444034018184114221707940b00070030900b8600d80c82a1711906070043e11950340140b03003d200440c0c0010849400c1608615914015511903140d031662500107203004160b4000340200c641044107480310b990a4070055102840400c00c890307145a899482080604855889200030074441040b0b400200b00c00360007020400b040b60350588500700e41500a81343c0c442c903420041c0410081c41000b440c6038000e010090b505000106c060f17161a5052070703201041b900c40c09800004200d01ea5110004e448412103032400e2658101d50509101000703100c02031005001c03074200501c001e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 131022751 1250 131021501 131021503
    0x20a090e07090e060a050405010905010911160803040f06020a0206060909010e0a020f240702030d050f0315060d06080c031b010503010902030403020312011205010f0225020418051509 80
    0x610031041e9a503160002481c1c55100200c0c0d0401030030072a002405184042016110760003001d003c0c0c00510004945945440e1750070301111101d40050b41c0348481808042ca003058045001590380b90000206510303070b10356081010140c2d59141004024a200003401c0c04000d80208400e4440c00301110040115500c2055a90070f071040a0018242600700c2181000145081c0c0e0461601c880d0151034080070b03001848401c05c41d05041c4440042c0454042011401c518040000000040c440c1c68100d06002001c0310740800c9010107481c0990040c0b203005e60982c41d0315900241c0301c00b125155000d10038a0766070b0140075210001e4608060080c0194420022040d25180e10000f10300d8040e59868610b1703203045c403840c0080d00701074800c80c1140010080c0414450721003600b50f0103442e200c58110305078401480c00c142100d13005044030250034018001d5802c4201d00c158015058002c11604001503100c0d840050010011003a41d03641c5041d11050714428003000281c540e0000320700b0380c1c258003140c88511840d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 131024001 1250 131022751 131022779
    0x30f1104060f05220606081503030a0e040b010201090203030301090903080108190f05010f061715010f050f2701031e080a0507061409030a0f091404111c020a09 70
    0x10b002039200c121040059040000a006105510300282420001c041e0a1141a5100d5034040702c00188120f040c411420b0301d141074440c840004900031441d00032a0070b0041c0460180c40b004a02c10b659921241110b030b4000e411400a4035030007410b8075030740d41e11150100010030070840280e001403178000010600f10f82c0015140c0c8403100140340700c0e080c040c1e0303980c40701c44500d220103084072203540b41c0381c50411400543c064072014005002000000340100d040700d528129111160f51141c4410000401449140703e0904080d10420359000c08800e140c400400c0d00e503052004441003900190000401c04103011254a0590344201d8a4181406030080000d201c3c000d90034000d4406801080300005041c000c0300180240ba01c9181c0224155800c1c49007040d0b071803c02c8841c101070343c000082c4900e00c00e50184003840104818204161018281010079141e40402d5554034059642c03483c00219010821064440c030030a0b090500030403411783d21500010b500805007000c045001124003040da24000e03046 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 131025251 1250 131024001 131024009
    0x1030b06030604091703010f0302040b0102030336030c0102030103140a1104051b070b0a060915090e031315020606010306121b12050f1203070c0305090f0406030f110406 74
    0x40500316142e82c02000014644a0b07400c85007203c1650400c400604290050340c001c021528200306814038600500040d580000945411900b0800c20130031004006007203002024a202101c030402c2e410f1542042c860340a071034a644251001060695100805400030360580b4400d44001c4030840c07405404036500c49030918010304c07454540450300181d00f4181e000d43c1e8004c050803000c00d070203040611003020590110741c0c00c0c4da1401d0980100104101f982c043c1c20024426078108001198030000002d071810a10701960002d140c59003000301d0341020800544891300321001880400039070b51501d110100303081c0e9070382d200903004032000504650300034401c210881b444030803281100d400a6030340d150988044001040241d10614001c1600340c1c0c0050703140c84103445600107000c882c2040c0d14403454030554442c2e880d101e500400800161640c810700c0402c03003540c1030500c9a2601080c0c8000b0380300e1890800107503006403610b0000014048251055000c442c0180c44485001c080030b800d00080d035440d802 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 131026501 1250 131025251 131025259
    0x7030203030708071202120609090c01021b060d1805061605371101110301080a140f030d0f0f0606091401030b040e0618010b011e05090a030c1401030b 66
    0x70000742400e020b84026540941c90345041520380f03941c0280c4800f20313041740c0d07420700c48240742400308600340c1042d40805030060021401060b00b900d018000030342c2c412000384000340f002200c030209509602d03100190b814a141d4900244510001c03081803040c2c1d2680f0040980b094491507010500c08454000040e0007800103555051034000e03c181395900202d03040380701811480d4241e1080384a190854060305003c6401d640752810034403181000e50079150203040341e512004040004005004000448201490b4400c08030b103600320780601100d0602c01d07180c00c03159841c08006074030407280d140e41d4030100303461000310000c101585440910f1070454580703014080104060340400c2c0700000d882c01c0032902c442d0301490003080004500c0e02244c1940c101e4264840307968000340501ca80804400245d0b54203040e400b00800c1600c08003070000f00403103414035519128501a207481d841080c0300303408980f0b2001c0c0152052040a40e64a82500006110b00c500c0f0340074881c10712190150f600c203010340100b46030010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 131027751 1250 131026501 131026507
    0x1080402060703051207030f060e061003050606040b040308091f020d120e0a0501090614040c030f031b0b1005011107170c12030c010c11060a091704030b10090207030203 74
    0x203801d12070581c0c0724107002d07414801c0500450580d0214a881e452140d02c0955000c10280e40d17500b6070388191040c5070004211101c41004026442d00c1c0ea41d044044110146404111034882001040103841ba5170050340940c0d1000a003c818010008001c117a03075941914902038103090b100410a04110304d603a20380051300700422022105214032502e450880420303c00080c000c240070a40f52030300e44400801c4038565103604042c0e050140c03a00c07071510a0031840450380c4c0c051030700b5641e406400c0c404d8000208500305058001080c144500c040c0c0700000c101c5220009501e032a418608611f00b001c80ea0741040045c03080b00425107502c42c06080b81030300381d03810050195500700038501100b036100c0c3d12201c245108960244583c0d42d02d0ba0740d00d407000c1036540040c40d980c3c40d58008842c00d54012030020000d1040210781d0780c910410009001d03500280e071490001c0c0202561422600002d40503400189480000c10080103005510180d1405071245003000c001c4076603903201309800e81c068428090b016030824 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 131029001 1250 131027751 131027753
    0xa0c050609060d09050c12060402100201061a0c010b06041217040b0a0c050c0303040e0a050703060b1c060e0a02131703071707080406030e0c03010e030a0e04060e090105160509010804 80
    0x1034010f865413501c0351003940c1001c20b0b6003002c0748030b4066032290003090b64030444c184402e5040c100d05150860003944001d014141c01d0004504103802050b4010021000020384207001c49400c2d0300452001a0081000781d85d55950480381c03202c1c440708007041d501e2001400f06c200d00b050010b800c03242265000e9000d5410408401c0c42900d14007002d860940d41d17802018101e00ca544e901b840240050203010110203040c5c10f081103c2003c541004101605151030400705004007825802983c0c40f640000103021508404200d4610240006600001c040300b41581841f00c000403d4002e406884406954001d41075a00c611300c1f6204004014452000c0d0804c00030207020030681c0ba00c1d41b5a00c0628040d052511410799070b02e04c115800b5030300c100b0029581d002041140e445c240491017070036208078001c1c4038021020600325200e10941204006005103a842c04440d51076640000c0014245854040d13410b1030450651806804c048031880180c0c151000c00039132943c0140300380c03542103c06079140f000554031 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 131030251 1250 131029001 131029027
    0x30308070c060f020d0c020601120506010b1b0d03062108221205030d0501120309140f0301060b09030706050f0301050603071403091c230306060412050a0c05060906 72
    0x700141a201e5507110500240382c5140d030300003440308020b400000603503105400c800034207109040e048980d95004824503600404c0c030001d800340c107483c41c0c1d41c4040e650b11502c0c00000c100c00f86aa81014850158224000602d0b4250380b0600032503041e4000d8658408008100c050460380b0b441e4000d0090905208400106140b18081c05150030b641c003900c2c013181d8541442d01c170348680b6002300300c400e03600000c0d11820440d071600030366005000f8254202542030351030703038040c003403842600800c1035244a45000c48001e54410a6205200394050005c101300c94445005170250b80c082c80710b640c000e20983c0c0000403c640b0460854a01d031042021030b50a42e42044c04003c1d19074000b400d40000c220703031036000300904a003da000323502404246c4001c085608809020070420100c009001c0140400101d10070452400040401e180189621519a4070781e00c0c0c10004809010310340144000c27107200c62000c41003210014030054042d02032501800380b15a2082040618881c141300150849024411070f203902c18 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 131031501 1250 131030251 131030267
    0x3030507020d1409060403020d0c050f040b061204020f10090e0105010f0203070b040503120903070317070207090506030307080403051011070c060e011e05090103050a0603030c030c0302030d0c1d090103030807 91
    0x100117040c103207442d5403900002c000d5840c08005407401607003400100074038541040e200d4018042524284440800c550028640340290079214081c030f940c0b04001411555030152f00c543c196002810904a141030100041034900140281e080c259a03903400403419600070a0441144c3c3c1c02603004621f840f10a560344461448050801c442501c424840854600c0e010108940301e0130a030030086440d600d441c2001410300060f881282d083d441202d0600010a60110302c18081c1c5441c10b801040c2a1541004a491485526005800c0ca4404100030040100100c0d25980140380c80000340030b00d0461082c040c10f14030071494000c0c507500740c04d04208403890041c03200c2c2c00c4020f0141813810103802d60640e45440ea0100c41c001500003800007031001c04640e0548903e54124003510400c100f058110f0fa009404c00f000b002010b800c1c031205d10070b20740401d40300b00211920005007810a00c4001c844d800064814650400c01c1c100c01412460800c0325424180d08181c105d9406544c0c82c0031607105c0d850103840c000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 131032751 1250 131031501 131031517
    0x8030d0f0e1f0e1b1806130e07030602030f07081803181309050718060b040324060623070507050907020a05061e060603010e070e0d02100c03030507020d14 68
    0x1510f40074903200e61841481810b03254814490300e85490600c15040001c0800010320011482d05500f050011540721400880d14a0760061400144501c0040b845842c000603944010b0010740000100250b8040298000d4011042074a43c800191134814012080f08003654030100154402c2c818002a0104100491003c010242c800440f07421514651001e4a50051061301c0da03500c650b2080142c440c00c5903610340329080c030b581e042000b1070034292007440c07902c51407001415040000c03d407107841c4190302c001501d04081007981000711541d25079018001d014010362561204203048410054041008125030140e90300601501d016402c0c01d040080f00c1901800b40300461003800171070310001e201040000c1c0114920444250291600002101c140000600c03a83c000c00060004000c030089581c08641c00038614182059203880d10700c08107040d24040100654003202211020700020b40060701010f40354000d50701408217644811003a684c540240c81d085001604c4d0410540000c01c4d23003c0903200b14 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 131034001 1250 131032751 131032813
    0x12070f06150e070306030b070c1a04060b060d0506031b1008070207090e030c06070201061d060d0f031e0f0c020616081903061203081305120408030d0f0e 67
    0x95460301d00504845400f00c0b44100401d0391011706200388200c1c1072000f17a2050742441c00c643d4030f074080d6484c00c0f40c0c4d503500c480302503c0902c007201082c10051640c001428802018010a45410005c40b808010740003d48489000f0f004078401040d5850300c0c000e03107403110007015090381100300002c8400c41c2d15040003003400c0c1c00c601aa0b2404540050540a03514444c10044d00642c4c0b074031012480d160404401508a50a6a1414504225407500140e840c24600382d03900c251200f594882d008900002034102c0e0007401c400001c24480105a0442504101c441c00c0c40d00c0015110f0905805441740000c2c0040d203800305640840f42001442c01100800d400c000076001c010401c00c05035034644254010900c10a02c00a00c65005440c0e40c0e49031140c9001050401c1d2612451100d0b528040c0c080d040c080c002168040f402100407081c01020052444400249207019030703526070392101591079130001440444500d040c80451880e1680c00c0c09a0317030100018001805403100a10310340a82d200d0403010200b40e03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 131035251 1250 131034001 131034041
    0x7030e030c0703020a050f03060403051612090306050615040b07050f0102040f061701060e040207110901030b01170303010e0106081f0b030105090108010515040e0c061303020312070f06 81
    0xa06090000c1c181e90a4000001c02c0041d0861042104003480741c0c128601034081c800d0040c800b41c3d00040c00e10303081901030074025a181d440380f801030009a044103010785a03801c00e181d08420180d000d180d00007103e000340020402074944000304410074101c04581022800140018000000c0b110020200103100c0c0049030080c2040000681c01ea8000380d01003218800e1458040288131b4001c030702d00d214481081041c046540c10b041c006040e043c4008001c0b40aa45d0110740394007000360200b021004039600030405041981d481ca481070404070240249540914800f8405906c03000000603241a900711154406050f0708191045130b9078a4010281920071108070812504500c0900580700039142c1308450b21398075070500d0140281c03541d040e0f101104513807421040220760720000020400346031081300e01003482e070a4071049510700108003203a0f5910003000034540b0310055420b5002c0e001c480c825800e460300505409444d520712f0140a00140420113000700c0f141c0000c50340d6111035021007050010b080 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 131036501 1250 131035251 131035271
    0xf0d0e010c020414070e0108130b130b0a0c030b010c210504050a03050c041d0c13020d020c0105150102060709090b060d0e0610080706091a0903061006030c020111070b0703 75
    0x20a9803d40b030486621a04c0050501c08403540c40404ea4690040038205030525003002c01c50111120080000a0401200640031400e251240c10a540040e9004140d03070503e400c18800d01002848460144000319141c040402803550007034001740d088541000d4041c1200200c4503c182d0411000c0c2020400c1000410010030303155690305020010314001c1c0d005103038500801050104969a11f2450800414170f02d014001c459800580c9240011081c0d900c4220f00300700003da031029018001c888490a4004603445000c000c0540c0f01c1803242c144d0310424207501710a00700690311142c1c2035500000203100c802c0140311a03011500312440944003d03020034506000b0320b000c0c0088508a608400c3d01d90081d5086c0310700c0b50010000b000180036414054025545052000390030452280700307a030801e0080f06c008103030220740307001940c00c908009025903070240340c0f4011300000310501e030250401203481c20b1b20041f00c0510501c1280804030196031664940901d949825003821002030060040584808603e0303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 131037751 1250 131036501 131036509
    0x8030601020142050d1a0c071110020a020307090c17010605120c19050a0e040c020c01030b1201091a100807120f0f030305160507083709090e0f0d0e010c02 68
    0x20800f0746c000d0810501c48000c40000c04001c00b4050f0110b00e40075000e000c0f002c0401c0548455003860041110410041031812405904015400c90065032500489000165906032500b0084011005031394100e01d44c810f04030014281202809160f00040050003e40030b00070507215469005455690300c2403d028805458400c0f029020401c41c00140000c210f052100d904440c020094810494052181004c1800029170365100303400007604054448500c0d1900340c8903014250038101030540280030020545c1400284440740e9410488034068640004c7d1071008080c1100701619106c002520401e49800c400c148a9403818409541e0760803008003150000e0b00c0512420740c454800e0f1008942c51410104039030402c4071840b1440e060120411210b000122188100d4400c40f101512002c0c0740c92008040e0b0740b0300b4141c1480074400700800b00010540e00d4104035003100b100d16001003800100c03c000011500d854008460340e52a40c048101c0b41d06043c02003d510a4030b50041c5040d1512141c50b800007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 131039001 1250 131037751 131037769
    0x40e07050712091703090f090703020d0f0606020c06270a081b0301180503070807080715090b010f14120f011802030601050603040308011203030f090803060102014205 73
    0x1c40e001c503000503c1041480200b00e500c0304016030f01005142014046d0000c00c410004075950148524802000503c1d030074042c0d03040d80c40a501500c03041001032041b40d5054001e2280d03020310405485008410140361601d0b80c1100c0440c100702842d0300d403001503400c00303421481d40c0c43c5026511125440e00800d141404001418915a01000e0307510304000d104149801c40d594101c0c8a00c1d647c010042c2c480100b640042101c1c0b07203980c092031480e032340d11960504501c00d000d41d100051010341001c00c81c230034a6071285c001100300750080d442e554444c5d03650840426800c82520400e040d1104501001c070080c9031000c4445107040c02c1d101991884080c089555003119072900510b400a45003080d890158141045514050042a0f48451850900c0e84001d80462030500c142c1c1155402140190101171194000c1144042e2900080c4030740c070040d1400c20040d070021200f03e4015840c2c481d5000c2c1045204104074440c2c0e03051101e110700444118003820700344100c4210082c20340f00101000903d5220b480203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 131040251 1250 131039001 131039033
    0x22120b06130e0c0901090501060207140f04090f11040b0d080318010e0f100507091502030403080703110f070b09060a14070c18020306010905060706140f090d03050c040e070507 77
    0x103402c1d6032080c0000c000d01c0403410b81000c052141f03410010722a903600060400c0a80d00f0ba840c82e83d010203103c40c0010036840514503c0394210341440100410403481140c100c0c0039038484ca4689041d4503480701404200c1d40215222030b40071403190800b0001c22081c0d802150002100410854003810309500e060a541000c80200090b510120401034036010500038400c00b0420000b06000340d090000004004804901441c000d030205205407804423402001110001e5a012103047c0d12055079050242280d00440b4100c0c505d03006008103200301d00c10220f401c0095542000d09a4140441d003030600c1419000900250305001e40340c07544051030101c00d0040c00b00d00d48180c040e25501410001d00c4100c0c01b000140f1415814010300a0140507078014050f481680c906031209a100c2c6094181140500600440f996045400e41e00340002c000b08480303c244142c10f100c003140c4080c01d09200460407030b030301200c8203205410280000d001003148850541d410600394504203040c02c0c825180c00c1c2d1403820b8188 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 131041501 1250 131040251 131040253
    0x20c0703050309031002090a0e1017060411090f01060e030709060909120206070503010302010c11100909060605070206040306020f040305060901061d16080712020a030222120b06130e 80
    0x6030080c442d04e41000304107800d1580010560420b400131001c614058628041d240c011980c0030000ba10140006002500a204240b9011485540c80314203a40301c0304195000c2e107407a2006c683c0000c0342d080507082c1038001c00c1c2048090585a1030803004513080b82c0355651032685130140071070000e518150b034020240505a00d20000800328042e05c0c04880f130644145140d4155086582000a526000030541e411641c080c20070800112403442d1010759001038040081c0d002540c90074050300241d00c15000810360f607010808022942e1510700544190040501c02948000f080106200050168026281c80841d100e41030342096225074030181021021116000c10340e41d2080c08121000c403003444440c2c443c445422025140c100303d0420b0205540718400030060181e00c03804a014076124580701e2400c002034030b0302192a01e0884000034040e500c8945400b9120f01c20301150f00d80c040b8170141020032601e0b24032842e0f80320900c0707a540c2c00000030006d001356400441c4011580341c9c08014081e2005841c0040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 131042751 1250 131041501 131041507
    0x72102190206011715040f05070306050c0d050f062b0c0b18040606120b010908061e01080303130b040f08030c07140f03270a09021e091e0103020c07030503 68
    0x20000e0310140040c0b2414a07080c5d100250741c0c0c0c40a10300b1111981c2164002e00c1e019039455090510b286000000c2e400200302920f032004100300d9901d01800303070000d990511406d1000d82ca40080f403454600c0180c03542580104488024403000c04140d0411303404014515510b0109280790700d603220031240c5a840142185800584a401140c4140543c80d50b200103d07000c0188a060100003404160308103540c091240e030b200301c0309210341c1c01044c1500041c03101204545582c034001042103c02000d100c203181082c24144000304010300b01000707484c410390081c0c3c8007280000b590740380c0c2103420b080504103441c422496042040451490340095120b001500d107030540d216414540f110172114000b94080c0c00d03400c5010001c146034000710440d44142241d60075140d4550080d0800d000c2400b1080c1e80540c800720a0600140d003100780d030050150614143c1e4450000c402030510750388248241d034038190380542c5030760300700024000748085200308017410f14005091a003182103241c0340035074a4005840c40d44c008 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 131044001 1250 131042751 131042759
    0x11100501080706050412030503060301020909071e0c050a0803040c0e0106031401060c030e1014070b1503031207120b0d0308040b0c040324180f02090f07210219020601 73
    0x401c42d140042502d0302e461860b040c9046c0c040c080f80720703030f02c14010100240080410a01c0e9000d4040d2940c452005182425030f0500007406401084078982e1207020400b00d24241301e060f0b0091038040d20003074110000d801a0600c40d03031003101590008008079520081c82c800441c2c0103004c4545180038000365140041c1d19a400c04034041c50381d005a011008214032280220002640721a45142c480710696003000300200364441518684030040c06400d032194081220020b000032020780902031000310304013000394039407074081c951a48180441280d100d05d41f18040303a029440790074681d440205885000546510b07210000f441e4501460066002601c2182808140260751030703065007105039156468900744c51680c5e468105010f102440407050800415209800707401d8000c884d440b90b41000c1086e03540c21505e050b40d46040500400c0c2c0c055080800019600e02d00070b400070303000784c2c0c49460b0000110340c2c0920f0000d0485180e14050460b6070240200e00312001c8215a50500340071940290800d0341c14 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 131045251 1250 131044001 131044003
    0x140307170429013602070c0905090303060d120320070c0503010e0a0204051509090a0b0618041113020c01020406030e0a03080c0a0c0c0e01050f0307080c0d031110050108 74
    0x3001040100c0398000c074010000c0520480e1340c0c1080c20180340e114801403802c591140ea050168003031085506000294440c02c1044440207842515a9040b04001c0d0303840303a040140d683d02003103802d02d40103008028284045481a0072010000ba2107150115186a0640e1861111480d124004444900102c0c2407800c1100080d05540500400c1e8000c01041c0e03413640281b682d8207034000700039002c0c503075039001301e20840c0c0018040c0c02002e001078a80b005908084110780d0f5100411181555811040c00203c1e000749080ca2401740c80d68204071904699444a480361120f2520700030440354080d12020403220a842540003030140850040d00041e252890b01c10041d00f07507a002b100c64031258114008004c0040d800520254020454445041d21452500700030b480841403641c003c0c1c400c030744203200054402442120103059407001e40e08c00c1072000808060650f6602d19000f280440d40019049050340e0070700702021110b4034000c1c5440040407210724201410f02282458a00403c1d445100500007044 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 131046501 1250 131045251 131045303
    0x503030d0902132f09061b07080c0d02040c120903020c0301060b030405060705030c0d0e0705151903020a1b0b01050306070c0803061c02041b1101060302011403071704 73
    0x202c58409000204403488020502040b540e42e080010200216113250454400103075400c0240c083c11181d030f034107500400140040d00200382c141d10741c813400c0d50209140f013011443e5a0302d0389002d00080c0d0607800c00d0f401c000181c1968074031041044403000c140c40758a1100d005000794180681c0107400140810f0043c5429240d1640102402040400a000014400190b0a540081685030194582d11040e800d81c5040c85000741c0c0d0032901c3c0c14034601e10301c0c80d007000c00c059003251002c0305c0c400d00301d0070310030180d449501460418241c804a41c402101c20680a60003d00c41515a0301e0100454a40b0001d0801c852010070415034a1168410060110342401c200c5140c01202c07600340a1f03000211950399040c24403000380400e010310400100008425440490b129025030b00a00920100507210300d981d07182c2c021200007400158986e6034107130f048403061142c40700390b03901a03644007110f2480640703070240e580c00a88414200300c05ea004188128072481541c17400341d0302c681085445c01d0401c12180f81160 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 131047751 1250 131046501 131046529
    0xb06040b060d020307030b0d0c0806070906020307060c14070605060406140607030c0f02040e030a0305060f1e0a0b0301030807110105120118060308040f05030111030103050c010c0c0503030d0902 85
    0x64503050024503180d450301e0a44049900c0c81c00090380d41c0c0d840d25400c0b0060003060180a412510444494081000d24401070040d00c86070700466286640d0180115402d4926214880150300200005008600c107500300440380c00c0d407420407000c0e8525a4421811039401040c068130007030750300c3c021301801d031406004810050100703e00f0108590411000115a072040c04001170074048060014402c01901d40c1e28800e0303617a0002c0041100483d240c03607054890703004151901c002450980015820301d0303c4040c00684120142000d0781c1910404807000d004040881e29a901c01a11a00050060075a00044d406140b18950321901c070313034040c40d04c07030160f540711010f250520000344911011030314036441c4035045407202c1b042144030741d64124203031006004a8002806a000009020840001c0401d5150885002b50000c00c070060b0340400c100c401d40403e010041c469000715101d500251b100f10381610809000d0103149000580d070b00d001918541c807502003a891140c81c0c021841c00d515003419802400 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 131049001 1250 131047751 131047759
    0x201030e010b1c11040c031a0306070206270307030504060909090b0402040c0c02040c03051005010903050d080601090f030501050a11030403080f090a0c18061502030406140c060a06030b06 82
    0x15403040030028800346149107442080b0000300c0143c6041c4882e9540c0c590068001801c20444100310307450060260a1a600c45517440d00509207a00030350900042c0244102c0c1158041d02c03c1b41c50312a0010307a1311140548044044400c00e406034613802091000307010302840703038032516030303803807404070060031b2110260b210010592030120001c022900f0349030416030082d4112000941074600050686100000311406500f00c0c2c980038040605681562003e409801043d80d8084055a100d00444640a00d800000e050345c10000050300d40a0090039a141c1201050422102d100c1c0c030741d8103080021100343c4c800d0b516607440300e092018486051050720758001b5507501d524030754074090300d010384422005081240221940300004558007420301103541000e9011000003201030b070340c1c540b4030b0311900132181021241e4600700e400182e05014007408000051075801450516140010660380420b0b040c0f011102070380304001280d020141841490701c00c000043c4001b50f01030031410030305044a0028001e50007 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 131050251 1250 131049001 131049011
    0x3020705060403050c13060e0406090204050a0c0507020d020111060c030f1003030e0904020f03010f090b070207230102010204150507030f1b060902030109020a060c031101051005061e03070c0201030e01 88
    0x3091021680500ea000140e411009802050320706c10010301ca9984100245c051820910040201c1e941014180a000321803d01058a940a500c012141c92040030008107004200081c0141820344526460f180141000000000c10010460400000300d0701d8044140e800030400113542c4542104640000d0780c00000035449045540c041c0c03d901d185001c040c03140c0f080000082c11035551035031a04001c40007a0083c4a1101d00700c90130005410507590486685042000003480d1620024070501141e242c201500380315901c1600c010000313a00006014110f54003084080707070700b00041c00c0200084406a0300e03560745480c3c5080c010102d201d9200308000b00501c4482c140c8410f40884612003006400040009504100c0d1000900600d29820001d40001c4403032000154141c009200c800c000e4081d44801500c240d504c50101d00320358040710201b00c09904a40140f256060010280030020400000a03660000c01450400300d5001194510005103110511b442156031602851034000410b0000380300d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 131051501 1250 131050251 131050253
    0x109110708040e09070312020115091406060c010b1905090f040b0a1e060806010e09070b1602040b0a03080c01060b0408070312050f1305040605010503070f030e070b03010b030403020705060403 84
    0x80d9038842c900c900301c001410240450041c0800b88010801968031034000800b04400382d101034041c1100f5901c401031020395400000e0110f110340100341c0e8510380380621081d03a91f10300f4100705241d0050210783e1050742d43c0d480303c0070450b182d90f5803640d60621222205001d00b880d040c03c00c26003143c010314040340d6220304c0050000007500b000040345c00026814021a4410141c0328528880880d00c8030140014103140d0009030110002c15828141d500494007025195160f440c487d81d80d13072251081070140e0200b00720704494140d82020303a40206100500c085000c454000000740c036002117800545428400050140f1451003d21819004001c1061100e0806107440c080f951114401c2c48007801d9801118240d44295202e001214280744000c400301d5120090200f0a83e41c0c1102401024011894078401051640c09038007500e20842180d5206040718240c80000c501904001504400301d04c216500800d0140301800518041c00c040e1300056107a1915090081c0740480580c00b00c1d0185101b08001d00c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 131052751 1250 131051501 131051513
    0x1030e100507020f1f06060c0c0306110c1f0506010c0b04080702041515020705090c09010e040b040603030804020307050406060c1716060b0102150c070b130b090601091107 75
    0x1060450361020006103a030384034031043c2c1c01c0c0038191240700b507580110b00005088001d26441140394142a10007001417645480003030f5240517222034050b000c004048810070000f4035941019030301d441c02d039400500300b01100c0005403900d02c0210b480038000003500d42d0300078003070024420f0950146007464500c001c4409070b19030409403000544007404400703002401e0025521560404c141c40d6000301c0600c030601c0c6d42d07500e4542020911100080045c015610700003010715080a0982c0140600811186041400b0005654100c043d900072900603450b02ea5001540d601c2d0b12450009500a0b10f40075614136140c4100750800445402c07082c0708071b00d009000d104141d0b00210b0020b84a502141c94034280c1103001441c0264040c030200c140c240e2181d2140c0c4010840c1541040d001d40c5400e800301ca200c698907503201416003004071414201c55200703201803000f1600c58000c40360004000e40495519400360f40b00d003548c0c1c900c00c44003090b942d800400100000d8000c0e11410314000c8100c80140c0c20b00d22240d07600 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 131054001 1250 131052751 131052763
    0x510060c060b030a140d0203030106050f181c020a0f030302060c07050304080607050c060702120d0f0204150c050d0305010e06062802070f050f03071703071b030204050601030e 77
    0x28000c1210205003041006082c0d07014860000c8001d003241c2e8038540034a421008070514441c10030460040c0d1a00c280000c0c0000282da05035180d64480e0303030800e00d41c800740440c590003003643d0340b20350b44403000402000e4840710626501c680600c1c0201103461158014042d0071585a0b220340a03101640f0700801c0801c4d07005c68103a4120880e003424558032201828080d145020365000740456000305401d1029040d000001031058003c1c000949402ea698080b0a03a03c0300120100d00000c41010000401c03a4901c0ba0310600543c00b40000c014102a1924400400d0702302c03044110300070030343c80601c0801b84401000004103244a500d800d000303560400481c0c1c2d0203010098640d500800c000b10f004400951205004111109100280d401d03210000700d00956170b207414451402e58020100000c5603600b0306021043d456003020300201800c0d803505040c00700c48480f23400131400c1c60005205001c0040d41c00038010184550010000c940d0b1802d5004000071140050900c50615140c00a2005801c2001c5a5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 131055251 1250 131054001 131054009
    0xe1f0510030602030a02070b0a090c05010f050708040b1b0d0e0603062715011704080a090e07090602010c0813120e0414090c03030304030518010306050a060807020c01030510 76
    0x101084503200c004555110251942004003298004805c00c40c140085034090000c89010f002e44c400c0c1c3e52210034800007110080c05c00601110070007076051010303500442c240d040e02c1c01103241c00d41c6848100d4941d01e00e26042742e0003900440344001041007409003641c18440000d0700001c090b1100c80c0e03503070b40064120000381c1d209501130704c3c0100c00108950340e0340b0b00718550708182d04121448105220320701090000c0c102c6014401804a034640346543d445000d03000245400d400c55005141ca072600d42500c180c10080c00501000164000460f003400544103450144030766449038202c450401c24081d00799030340200c2d04420440041c04205100040c6c03043c1031a0660024008603009000071411a000b513140040c4d00e801600b060810721586824080300e40c415071055050321440d460300420103440388815030300507001810502128012400080341030407400014100042c00c559641c000c9044201e080c2c1c03004d00818a10000c0140c0c0940600c1419040c5d002440c0410640ca0b0041b240212210a406 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 131056501 1250 131055251 131055313
    0x11e030e07030b0703050403030e011a0603041e1a24220c05090f030703021f030b0916030f090215070201020109141e0a05030306150d0c02060106030e 66
    0x212990014109100c180042d60300a6540c1000386002c2c0300244c00750105482c2180020324003010100ca900341071081812807e0304800d9101035941c40820000e150704081c009a03140c01e40654034004003050809150704040c49010030a40240303180c90001c00004000744040c1001a80d601c1d9031240790903803212118801c4048a40704000450328500d4400140c40c0c4200c0601240b60418121542d50000041e00740c00300c08681c41090459a18107142e110007942c40001d410000c0d52040c4038400c81400075088000c0200e25000030850301140c00903c42c150160341c2e010303d503000711411089007030f458096250060b90840c1c0c14003607112698003040ea010400012100320900c082000d10440e0b00c01c1d0005000d25800c1000b20100c030711101e01d501e8544c8000c0208141c500c074521490412030078003264040c403171500040030f0342c155510001401000b081c90246e003030710004100068001564a13200303480c1001425401010b1a606001000c0c0889481b1500c00031141e1107140c400c00300f030f03117a01c11040030460758007 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 131057751 1250 131056501 131056511
    0x4080703150e0f0106050406080721140114060f01230d0204050904110f01092706091d0105060a0b0711040207080a0503100f08060604050702030c0304030c030b06011e03 74
    0x8003000001d209a0b000c04419014120441d150b2890542088055503002c0300c007000120765981865546000a100349180d018051500c003207411440300120207054000c40e1100001007403426413508641038884410030081c0c408041c0302c8035040640710800c0322802030a086013211858000003e403001d06020b2441040d100041d444111030f51342d015a4000c00010b8440c15160a043c948007200c03060b44080b55000c2c10000b11031b11003540c4182c1a01045035002c2d44680c030b044c0d4030349e0001002d0380c0107107006081e00782d16140c001070304130207500c070354606904003c1c1c2c1e4220402180d812642503030310140866208041e0004107022407001c1c24110340d0b089a200d103448405c0000340002c68042e0048031000340100d4804191404e582d50410015489400c403521004002910341d2100302c000851030103000c0d10380e40402d0005103181081c2c1c0c4003e421130001d0048071700b0b005a11104500e107034840c2c1c0003110365020304401001009400b490b00754000c0002d01b0300300e120512208a80c800720002c401c030041056250 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 131059001 1250 131057751 131057783
    0x4060806090718060203041517010308071b1706010504021801030e120304080a0206060103090312020703020a061d060c07020105070314090405040b01180b062d0301090b10030204080703 81
    0x30b902421050340c507070b000203105035584d00301c003944039009441608650170301c0801403100144100007240710305100c03014181c041e9003952102d07000c54006c420301f21941004e95107003c0c0c01910000a2800030b00003403890f200883c2ea402503c03070402070103901442c01940107007c607140194214a84003814042860001185800320310100d242860080881001c00c5c070000500007800350b028024041198036400f10780d925112000118100ca410240141c0000e43c0302d035908480004035002024054017910444000e191503490b0a402c407512070081301e4086c6425507900010581c10701c00268051609201e00e820160310f900041c080c1c1c441e1510003400c001101d885001070006480540c1c00180c80500100914501440d251011850a0061340d040c4145602c081880c450700d4000c502401101400031401d1000700d01e13900c4070300900282e842d01010f5405a0314046c207001440910b00a09030032201054030a05002802580e00b01140210b0030035004200600c2040c3c40054010100c0b944050030f140310900d1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 131060251 1250 131059001 131059007
    0xc0a1a0c010209060706021218060103200901090b0a05030303100e0603030d0519050f070918022b0c050c0c06030a0f02130515120105120c13060f0506040608060907 72
    0x343c07280259009030007003039101c24014564040d100c2c601e01c0003d00d0541e030300d40d00907030081d00440402d203c3d8164003040041c000107034589101403c1108a1035800b09145074070000510741d0714241c020142003503a8100c0d003815490064040e0000300310903406181303141017402c1699600c0220b4012805013801c4200841c3c035646040007110425a18082d040183c1e081c26644554180391880408036181c0c245400305046140e103242180c01100c090b220061400c1c0303800c16601a86440d0701c51000700c02d40c2404007014016014006100c2c0101c030006201d002c00c0e0340314941c006c40b40401c404408101040c807156501c0507001810f00b81c503820850304103880350b9500705840c02800200024001003400421880c05215040e44003070140d5000300e52400072007076811f105120301c0c020070003502c10024107000104424280046508403050480e8166103000d10351002186003440d40e10100c01004d550748004110180d550b00440c00900307030444500d868140703030100040184030050440c034480d400304401300d81c4c4540 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 131061501 1250 131060251 131060257
    0x604170f060c130509011404090c0803040305030318010506030d0336050c01030524180408040905060604030c0504020d0b1306061205040209010611210901020c0a1a0c0102 75
    0x300030032203000d4507100d4980b0070b9681080c1d0005100340c041000100e11441d10461460507640014215904180c020341004043e101ca20000e90302e105c0c101d2004102c2800610003800514000c2009560ba801c00c50061000c1c810400d4640c1c0542c0d140806010072968040f0380e0110039901d624000c00d81280a50420498180101101280299000c0340c180800703100000080007034002c5d416500c010012200540640744229403e04e441003078034000c000c81da1511801141504ea015000c1c0000c0c40c008821906201c005407002e03220301c40c001c10100100c0500c1e00a05901c094151021030a1a1441e81e03201c03102c00035030095501c929000314098201520552020280d181c000b0103104c40c1c402d440c1c00c0a402005c60f8000c200000b0305081a04140070345034043c26008039800b40030505240e2802c0412074144000400c00107150085100816141701d01c403401520038009075072510f94880c001000a07141001c040e114500481e2414020041211030240f0081c801c9070b501d00d8950781c2c0080340718050080c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 131062751 1250 131061501 131061523
    0x1308070609170c06190e1909091a0a020c06070507030507171309020a030b0f130b010210060603140a05040c090b01090305030408030723060103060908071a06090c09060417 75
    0x19102040000443c50202c840485620140d119451b6031031912040c416100607034407644d4403140c0b1000c0d082160030080d44c8214900760090500c18140d00f200c40c41440c00500540e040800290003198203000c2040500030a030b0440c00ea400c020749061030603580031700a0f01540340050040000c1008280700d00928100b01e0b901201070700112012142ca40000600030b4225403c0000000c1c07420060099604202640602d0001c005009075400c080e00305186c0c002c0c2113001d0b03059046000b484d1101c07031101d007035000b100081c020341c2d1008076165806081c00001c10500034070304500241080180000302e481085000b041d51421a404581c03014000d0040c0c035054000e40c07000300729110000300002ca0317610101c041c0407407a00c2048800302040111100f00c011038412000e1011941002004000055180d030125039800e01c28502d250900c01d40b0b4888415191000d800c10217840344213001c01045281030b07880340e640305800c2c28106040c100030700c0c04582c0c140250f0003031882c1d1401d500300c030148200341000708018032 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 131064001 1250 131062751 131062759
    0x3120804020d0212060a1d03090603090118120f03021c090813170f0309030316020103060b0304060c0f0915050c0f01050c0c070605040303080604090f050303010b1308070609170c 78
    0x5210401c50a640e00c000465a076502180b421102808000d00d1f00158038465078940f00441c185150002005042d40c4083c00c0d500305590b0762242c40300250001c410034011240609500c128400402101900c598020030f44481010b00c100595440b15602941502d41400c4204002440ea0140c1c81c0c035074040c0c0304600c190703c20851031200000b6a1400c40d41d0b003150fa0403042090710b156140f81e13044d160b960301521000a5143d00203001c000100552050300255070360051501050700c66032246078410f0b41d84143d50999840d40c64500205c0c0d02e9401c501c0300c0f0b5690b070071441c0444030f9601c0c111a8408a44150000f4809c108002511b05141e6204200e0145001510301c000c00180c10405080c03c91513010140903120750249101c0083c0f141c3c001c0c41528103c80d0503441d912070a5a03542c080200402031008103c510700300708480100812070400c06140608a504903280d40c2c3c2c05580a10304201c0140c0d8025201e982c491481840300365840011402164242a642044440c43d034140303505200520500d039400c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 131065251 1250 131064001 131064019
    0xd05060409050f07081504020102030304031206090c0e040c0810090903110102040609031403070302030f0a05120c0406031808070204150806130309140f13090812010806060a03120804020d02 83
    0x3c4850042001003c4a10040440c1d502e1001c00203a006550000c943c060f0141c1c000b4070000740800d00500b04101000c1d03003814000b9034113031182502c00850304071010101c000f9000c40c1d940b08480c1040c0c46904100001c0d4101a0500d20704590091551882da0140800080e03c510601301018014000b41008070100c0000b5511a40c803068020585c0e0a14130090740c54030ba00c0ba141d400810408000c9441c40b5070968060f5282c54880500040a50700c01103140080007400c014039034203481040340c44c60103003014080e110f40d00c2307240c01001402e84094a60301f9800c2c080030505030300002c558008a62409605980218485555550443c0a5001540300340c545000764820004810319030110b084526201e504c80461864403006400b50303940d11101d15035006403c805111b001e038504801003d4400707017115030104450f40343d995001c0e4681c000109804050081070018440e500081c0700d82070703002c4800d0783c0c6841d04501d03585400c808c0300d000c00e0004040c004648003140540d00d0780c151507507009401521000d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 131066501 1250 131065251 131065273
    0xd0603060903090b21040222050a0501090216020d0201091203021507050a080601230d020d06060c0203030307180f031a01081c110106080129060a050d0506040905 71
    0x241200074000c4000488186010425040d60307010b4a000742d0800d24140080030f100c6008141d408005001a60f22a02c840c076801c00030040004110040d11500070042030505080a1070800e071941a000fa140c100c0c0140900d046040303198030b480410381d4040340c03420b103520b006000503240d043c19504100f088006e090f00c0e01050540004030009030b4464000d5100a41d40d40035011550384c018080070000081c0d802000c11120340c414009118a41541486900050082c03d4021081e52009a42d2440540c002c124910489154403514008049070700300381656404a6000a4480c40700a0030901801012003500c00d041c0d0b0300c10030500240c04014062001aa04e074103081c1d04180300c8802c6060301802c81c90000c00c1411001c0f80c02524a00405644102154030315000e403100003d000c3c0107600f9650ba03003000144e0003002d0080f01c01a00070440802c8403211072440300480c00010003416070140d0300c104400b200c03a070748c07200851b02100c0400b440020300f600c3c0e980005001d0400c00d00054001d104c1c0c072030410 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 131067751 1250 131066501 131066513
    0x1052209050312011a030c0901110f0f070602070503030414010503040311030a0302040311100906030c0e091602060a18060b12070e09010b01081909210203030115020307020d02060d020d0603 83
    0x18140e8090140c01c0310b103c03172004051113161004903105040d070902801a00d5095024080c1ca40c0102e0202c0c1c01e48000080c0b00c2800d03072a08403040b610244540c048036040011f980c06211410150200344c02944c90181054980c1c051318813185e04041c10004000000750900d8418100081c3c5a4241810b403951012422002406134006000c107460078401c4803441c240a00c1c4c0054681c590074020b4072005000f0b4a041c6040d002000e0200c1c0c80307014807100c601c0f81e085941d01e489003144620f4101d032030285003140518009140080c0200f00307065151400107024100010920703400c1d44240d0200010500c0450a0042401103081483c009810720842101180210180c1c00040c4260400002041090030a10044034880d600b0b903011000e548000210318091411074003c140d009018092066216050600811206020382040c0e001030700003000601820006064140049085100940c2420b41c59000103a00d582e10800081c407800c000140c4400c2904141c0680c2e000307600d000710800003141d03281000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 131069001 1250 131067751 131067787
    0x10050117130c09111206010509030c0108070e090103081209060106080f250804140c090105090a060e070305190b1003270302030403020907020105011d040c09051905010509010522090503 81
    0x103003905c0c184520005649501c03840a031030000748006e00074280d00810a0040d0313103800010f040d04040081a64101003540c950b44c9500703009602c903442c0340d0396800010346c07115442000a0806000b60304010010015240e205402c180c01c40520308040d4196103908480d21604078011f42484089405041810803540e009500c1314800c0d8019003280b131000030b050581a489030210362909030311002020051040b42480090350381e10480e030007000034403e0713124000f44c0c48801c1c00310740c40300000c2d84407400c10401240c40540b01c07040580e070b142d05100041103440003600c2c41d110400b02030700309540c50105c1d0402004545006507066018103001c02c030407804d0b0400944039449400140d00426121002c01c07441481407044a040701c1e6442200310500e81c021a140c5141180030300141c607184240704012402c0402841014040c2900b902c0d0400382c401ca24019900361041644003903c43c40b100e01c010070050f04c640b40e48281c88820000000031040345000700750014203503e80301801c14440491018924410303013441e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 131070251 1250 131069001 131069017
    0x1215090103050f070f08100917040e01091b27030210090501020708060f2d010e06030d02010c02060c0706090c06050304050709060b0f0c01020d0e0610050117130c0911 73
    0x11345503210780760144285079000c0c40c8521920ba5200006030080902c680d482006030600c109121140c070a90702c003007201c2c1604150002c0c01c0c049000401004000c17154801c8041d140e0b0032000c0c414010640c01c0380a00140050030b40e425400040b403034803071020402c606400c80a158018441c07042d0b0049840700a080030a20b00840740548100240400c80400004000d482442c50400407000b541d42c000001410b0301d0f0341e802c1e0003905100300d2103050b8104404c2c4001c9005c0d0003d521407110500e04502098500314a0416100135640340c03005002510380d000c40d485520104904c001c2e0742d14061468400000c1075a0000504061003481c00469203680c072100a41c01140600212164142c1710f89010044a82c0391150000400d800c001c041c0d1041500c20140511408840005007030400d00b1503120180c0b00511039942098002c203041101c20701c28601100c01a24003841d007080c810202644021581101070030548043c6c1c100c1d48200d00700701e80300014401400306190305002072640c5803103248003074000c452 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 131071501 1250 131070251 131070253
    0xf0c030c170604021c020d06050c0304031e0c031803080c03030603071d0109050a0e031c0f060e04060902220c0305010506030402010f0f02030c1b040b0f061215090103050f 75
    0xc0d401c0c1c0c98440c0014118003442d00184803000402c00109840c181142105040360410001a0110041030961041d14031031074032485856900d02d007a10b00100f6000100640180300c80f9501100100554014289403400350f05080c40c40d14040d50b06494030340002c02c0d03400241f451400144842042030040082c6001e200180c0c00c43d24100d0715420008842038002012410003861503004000c1080d640d0031003500101d132400002001c2d6081194681140d002c640b0b00d5450302e4071501c1ca8040c030010b42c030450091695684e82002010700701111254241d1780580060107840c2c0324403031740041d580c0d160f40703004480b000c2c4030030404100c0c07500d600314000d442801d0704080444d03d05000004c0f1750400108903841554143d4448400074854801942c0441070040d04c4001c520041c000541c080703908124a0729040503408201d600c3e007040f80108401d031103402072560b0080c811f001c00c046407521140d09a0b1010081a500a64a13590f486035249400021017010303640000107400010510001060382e40e007020f1240 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 131072751 1250 131071501 131071529
    0x21011160503180d0f080d021e1e0c03070312020d020301060908150c030f0a110327160b0a0c080403060e010c021b150d0c0e01180e040f0f0c030c 64
    0x9000c00111408400020317068600280e14000044c042d0401045412002d03500141042c500d00401c150f8110304d142c48040c468000980c019806034440d0b45114a00c50b41d0f5075052410324460030051302d9020b445001000d02c00c00342c3c200c8041400c2d60301602d211900c002c0045491b0342c2d4414000303108035020701c6118586d00034032070365400652094030440e00c2411501c0c1c80c1842d644507858809401e01008000202d16a90b4110300364607000540d0041d4002c110b18001d5403c0d4111001c1803c3c8103d030390040d0602103903c190300c80d075466200303900103070120351000c0d4410f5285c0b01c00100c15541c4030010800105402d400180110402c8070b150f104480b0b07072401c000204800c804103042a0707554801000041c0c0c641c0d404880607038007841c02e111400c8507202145000ca0400005669000c107031012059001d010408401e4010390a50b8001c0000107201c501c00b0a8040e12071a10080c840741d058042c2029100005804403807041c0283d4242142c0348035440b0301000052552400c02801c1c1d80620300840002501750 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 131074001 1250 131072751 131072797
    0xf030118050601020d0806180702010b0a121707081b0336040c020c030a0b06010f050a050406030209120a030206070212040302090105130b09100321021011160503 71
    0x1d104603449240180c00405551580507000d4a849000518a962003c1c2080310420260098a41103014014640020580c0c210740c1d030030000511b46039000500303141c4030400d0707107030118a80c0650007003404511000660707508842d003000f100300d21803046c2448a0254803107114041c540300100038004800e450780e102c080f2440c034040c00030200004400c1c40d1400b081c0440e13005018a4258400d07104070324240121290080c80308086800d00356181c0c0248c03062050201004410350300010f4928130214540350140c6092000c070806401400f41e8080c81040580c046100c4005403100d490005004040400300e4860040c1490000d503903039000c80d40d5900502484100c441c0914807a0300f607405680d07005006030400e070b00341002d02c0b0030070512003c07042100b40c846580103482d84072000c0e80d600802c0001e5040e2960390444c10600e0b00801804500100203000c9694118001c3d40400d414005408503507000c0380940c090f901c429140e003d8406000c1540d50404c40c86070030884d0002c010001d40315104c501e09000804 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 131075251 1250 131074001 131074049
    0x7060503091b040e0a11090606040602120a0c080c030307020f070501050409051909081e250215030703020a090f0806130311031803010b0f01020c010c02040608030f0301 74
    0x3094442841e0740e40309441c0c0312000c901c01040d844140c14081d10004d4040420b00082e40362040c2918140c40d0f80e140060310100c142000c2a15550091080d10400e00c0c00f49001c10007590382e1003a4003c5500369001090800540d88a050603a010a4000d00302c4e6417202d040c07a180342d8681c0d20a84680002d0b10608004c00d00840e0042132400807180141c661600305403078004164090300300244003a83c4404620914482d0078040d101c1c040840c0c0c001c0c001c10b41c44041094649010030300401c40050014000e10840d0245c80303400b54404500130f010007050200c00c04610129100784240030000741c2036080030040207031031039041d8090002407000d59a0442d020f542c44c0c400c1c2c6030081a81c0140b00a40d04200000b5034500075416031098040d00c60b2400100c2c911107121114116040140d054a40009500442c0598a0309005c0c030781c0a007008a0742c1c1c0c2c407501c09010000c0d64414051000606000c0c00c0700c0b4040555407207074010310003000c2c0c40069075625000c024590159600c00d0060410b8840d070b952010b20805a = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 131076501 1250 131075251 131075257
    0x1020d0c05070b1b1006050a0e04022b0213020c0706140a081009021c0606111f09080304050d110615060304020d15090606080318060708070f03050c070605 68
    0x5007041c003606801c0d04200221070694009215500e18154109000525140411400a0310710b45807400062003403c1c207080018039883c50784600300c030307151150900c0003681e503001d803880356164880241010610341c1c411100c1154841c00003e5807005065465500d82140d0b50000c12a0080110564105645810f810b0b54502c0c3c0310640004041c0d820320440034418004d60300e25800908080c00f014010340d80c0c403c00026a4000c810b442400d03c40d2440d812101000e501800002c0d000f0780c1056021005034162003585d07a402e040303038038020582001d1250f888030b010b6030262101da034014880c280d4914080c240300755039007024188900080e21041c02c030645414003040d014080c00d02148250100400081080029080a0411b0b0390064041d400e10340015503e00205110f17605200000c985050303d800c144c8100d586607413103000caa420401500400d41030048550070b106008482d441d449113114140701f0700c01d01440d80004e01d038036918008982810b81120180c00e81c445103a048943c215207500c02112280 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 131077751 1250 131076501 131076503
    0x31e06070f080402090a0908040f06120e1b0a120506040b070206060a060c020112060303020c031c0507020d0609021909150608040308090f060114120102040503030306090903040e0a0b01020d0c 84
    0x42c6502c0041001890318000c04d98002071a85000320b0448120717202c05030726a00a174812995820040c600700a56030b0800daa8a90404507200c0030400d40300901c90b05900e400001c40301c0346100061081100c025615221104068410640c000c07112214074a841a070ba8602030710143e418405404c00190b0440c4001400c0c1d02c00c10f0040d020300045c0e460540305a4004032001d004074180b05485002c8900d640842c81840001e41c001e030700811000048806142c10200006611010031102802a041494001c4100c030560341e4140d40e034060110007401d000b0000c01041d41c00951001980407152a186c540c1c00942e401e9035011081044074070b810814070300300a255441002e0202d1482000540400d028843e001c1e80031482000744c50b900302071840c00504001c026000002040b207440c4c014903140c01c107080102c80c440b0041c0001c52a10741804002a0749000084c5080c1c410000c1c08001012201c0900986004103060319181d445800d085050344007602c0300108007070052040322010142c40c0d01c106255a002 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 131079001 1250 131077751 131077757
    0x302010f0203011d07020102040b0f180f06030c0d061205060105100801030f080901050730020303040803131401090c051c021e0a0503060c0d050c0c10020702010e031e06070f 76
    0x7130820b4030b0380c441103900300900a1003955801d1000080c4400b03400300a04410036504055552180703006c5044881c2e92102181c0303030155600c010070308a02c1e00c9103022248c0100309242400c0d01c4044403460400a4030640d00070319241405540d5840411500080342030603110b045030016100e200074141107071950001d06c000b07002d41c2103038402d400202c0c025500800403940185402c80c07801e40280c803840711040e44404442c02001e0050800710919403000c4909001c58041c0c0301075803450802761112403d500026241103160005001d00f50200300c00c0303a0003400f001804200902031958a0304044a4814807441040c0c001d0100182c1c2d0007008583d4680044200d90027401c1d420702c01d81c1002100820384491549580241e0b01200124a5642c100106d0b8403546244008039134030f80d90b5101d005d003a0380c0c015040c0c41d503824042c080ca000b000b40114800250290000006848980c01d00040301d1905240383c01c69090b000b58900300040381c802c0442c0350307083c03180081100c0d0561501d580c04c40f09032701224407100c00 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 131080251 1250 131079001 131079029
    0x6031e0f031b02040213060e040c090312180602060f060a05060703030f0e011406100e01021b01031509051e0c0708070c0305010e0307050d08010614031e10030302010f020301 76
    0xc0c0c0206914031652922116000701c2590b542e0115040380d0005d050f01d0b118a580020806c4159803103c94281a020300344c1e4141300401054401814490080c000100204041a91640d40c5172103803140c46240100740d291190819a202e0010b519182c043c1d41011044100b080010f6590501244441c100c0f08040e22042c600b00d8141c600300d00400c40d011a00c0403140e00c4086140000809000d0406585141e08500040c1e04069041090580f8603100c2d034024008030b0150042c2030b82e001316113803840a640400203000e6203800c0300101d0040ed00070005240700c425030f03200400d482c0e000303038005403082c0c0740307020701c40d00748022001001c0b040c4c0c200302e4006603528420040300d4000b40090010704180340c45070046048039902c2e40e46032429100c2c0701082c8003e41c1d0003c10003005002040044107040101814800c03c55410080300405944080740c844005510010120baa0000107800074a143c40d4464110032440c10640d0b010441c80035180f0042d4019800c182c4580200001842180d04a0f00c41c0052594 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 131081501 1250 131080251 131080253
    0x1305061318291c080f070302030c030301060804050c011e050c07050d031715030c1203130308040501090f05060904200403030c060c030216020f0a1806031e0f 69
    0x7020000310403884215a84640d1003006007103921002012203090010a0b00c1c01081c80c01c10f21400c180d000400050708a440b450b000d01051140e01210b00b6428130b4046281c2c0d0b03044c1c50905a02e5441051458101403000000001d080c51f440300302075000c0c0384036005440c2101c031220011640b207034042840c02e50020061031a081c0481c000c800400303050f2405d0003a150601d9440c00010f2000c000703410160f02003003042c1101d8030f00d08114140c2c0342d40501625100c60f401150003020135541c00640d005079000741031200000010358030400c2030f01c104c0043c9034a0346601ca07440e8900354500b03030494030034070340420020000868035000359800c404c1030324809170a15007007001442c10440681405010720f4845e0181c2a9045100b2418000500c05540030341c440c1c0191000e176107003030012590022680c80403d481489550300031101d4116100b07280b501200d146805408030000120002100d0b800305e03800c55109145001285201d400030340449000300ca041b0510884c11100440050400c000149142a860a860 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 131082751 1250 131081501 131081519
    0x3090509071101090507080f030a02060712020702100c05010e2103130c23060309060a0b06041d100e09031204111c05010501140a140609090c13050613 66
    0x30741c0c4400185412455908107051241c21a0b08004041e00c15421a01050200300800c00c041c00410407013800139442d05030180c030020740b101c2c03000d06448208135001c544c9215481c0903405444080d50018142c514010849002800d8200301c003000712115420903c14104144001c5112003400100700b0401c5480009451265090707070004007641420000111800c0210b01d200302c0c0d51020302040d90f643e4401c402d034070725181c0b0b1501194401e544149030810130082ca1210121389a40c22804900010400e03409140014881d402a50412041c2000c0c1c0c0414507114110008441d0040ca10124544e44054840d401c40c04201c00884050005502c2044559030801555007039540c028060580b040c2d8000c6c55400144481e046803000781c1d8081002c81030801482004e116840c01402e44503034a1351804108804940000554031401c0030601c510601c881454548808940500e20020810f105510b84070300200304070f400010318045d0001c2800c40c085103074101802140c15942d5002c03040354a940c0752007114 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 131084001 1250 131082751 131082769
    0x4060b0915040b04300b01030b0a020315090613020d0b1306080c01050307020f0106030c0602150609070e04060503060103081c0501060816300f06050a03082116080c07030905 76
    0x9640050340b003441c12000750400c0310080255220300c6e00190903501d54205480b00b01c5014007207c210034410000d000c01c00c0c0c800103070510751002c260360308099036030f074100002c02489061049090450001132051210445076004030505c40c82100d04502e15201c20b1070b040200ca14900030b84090742d01040c11502c1e00d60291015540c0308840d481102c0d20402070413801429280240d01c00c440d8403103400c00c2400b200780c042c0a00e0300002140e02c50451645081030025010380700c040c1840060100e441d4540d41103403150780200003e441c016040b0f80640d6943d01d031890003a400007448a00142e030030142444407000c14000c5ea81282d40f2660349035041d44074005a00c074070303a25140708403040c400d1000910080c40c0c0c0c582e440a02d200c00c1e54401c91390031641d092a2206507851f0300807890f4003a1030f00c0e00603c0745030703521051b98050302d030003019040d01c90034448411210b0794030900106280d410f0900c104809004040300302e22000100380d44044013501c41800840b100e0092070801004074414000c14009400d141d691 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 131085251 1250 131084001 131084039
    0x19030507020d06020c031c020a1706120304121703040803040204050613090f0c0609050d06050702030c030301030804030317040f02101e0203030f06030613060507030b04060b0915040b04 81
    0x218800101441e6120f101326400071142d6821600085200805c0b003803605080c00c4000c0140106500c0d0103030051009100f401d0002c480e0483d06105004508a603c8400310040468890801c60b0760f071b25200c568448000100e10f004849808921036100d000180c11401d4a02031031744080520304588850b0700b0030000e05002001c040d0041e03010f034924403103010503008510015001d40700721508950513040c90102c2040d540c105000f4080161400c021503110080f004e2107094000790001650f442d082422411072140071014060752001000201c01d12004034020000c99103e62180f9440c0b460408041e80b50003000c48000e0445200800108003608048032003100f51001481c01051a0880440003110310308507043c1032006900101c1000f10101000006942001d002ca0013031000e07190160391410750704500366004290a444401142c4042d020b900310480b07007903008005010150316940361071190382001d1551440b1305c0d0000c0c0b5544401c0e404104071000c1c0c03000002690703d031904088032182d50385105a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 131086501 1250 131085251 131085259
    0x71202121f06090e091204090b01030b040606020325021908010f0501050a0b1b0313050913050c0d0c0e16030f06210507030803160f0f08160e040e0f0706021903050702 73
    0x1b030703040b04040038100108041e106540f40050061542000141283d1040c0c00007400b03039140100600c400c0e41c0000941b110390b41c581544201e10f000f488105d20b8558040c48000307410001c001e4040044252001c082c006481000c8020018540404010425150284201500885000018090144044000e06842c8002c00d902281070f9040d10710649540e100c8641c500020030303014414001882c20032405074200c11504405a50480c0e0f54440342d850748403010342ca500c42d00002041404101e0680400b4008003d00001420189494000c1c2c0c44c00320104808030700003900d013114400e01c440d640d108401c2510b2103c10300000d550f070030406440007041000c2c0306482600c962103000001808490003144149403061405255040381e0390040c1500d02070000000501c8401092040869484001154845103208840c045c80481d11016a00c040b4400c1030107401c1030801c4480b2160304000103542490a071540211141150340f664104d807241d60041c00b41c0308400c58449081c005c40d120308058001580014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 131087751 1250 131086501 131086513
    0x10513030f0315060e030d05030c090409140f0109060c1106010302190506070503070201030b03030a121808030a0b030705011b060e190c09061a0d05071202121f06090e09 74
    0xd203e01c800c2a82d5030141002a0303128884002d6810103003d282c400e90b0013810018110b040c8440001d0013801440c45085c056695460203109204035030758032401c0a08640160703449203d09408031406400740e403100366002c5045c4900000411310904481d01d1a041040140a60340d0a40d800c120108140c0020000040d02580c4041000e94841008020701e51050340110b07501c265a1002500741c070390303a0506621035041413046018068102508010310380c4440800252800c440c42c40c61041c4d07140080250104101104014510761258000307c82c0c1142141101d01e01c40e17895004403114503107006070384114086d14561500046003a004214100b4281c41075030345400c49d0394001900f41d4070300e40d403d0780d80300080c0504002d002c0f1544104000703422207501c40d09101f11415002e0381248228035029244540d54000105941d20610324040e98100821055603903c00348001c0400c0c06100345c5070102603421201420781c00c3c00e010848402190310585032000140d16010b404601604018201d40c100c0c0100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 131089001 1250 131087751 131087771
    0x150c05010b151309020913091b180b03070812030a06242a080d0605040501090b131b0f140706020307031d0c0d081209070314010513030f03 61
    0x501d0798419001c00c101800d920f9880f82c070490301440501e644906480c610421010110b034035101c403000640303254407001040f080c0043c680700100d110441125210a80c0c440e84c04540da0b0200800000204000702050100c402c1c140201a1211110b12481c0c440b0780c446850201d107514100c010350b503c4000306030002001955141d00140400d006d404c00d02207513103680f141c0e222141e04042803041e0380d0a4500c420344204014448940f0f60602c444000d07040c40c50108862400381c1c03003034110074042d110286c130a200b80c0d60b482e112040a4210f8003d590702c078024058008014105138401c5c1a040100c00070f41c41200008041d00343d4904d10415090800c01980254000d0f158181c5002400c50a2141030010f03502c1c606004003d0490741e80e5010313400c0c140348102c591a08007100040d124850304003191700a1421820f807070b002c0214441d01d0080d0184600102c20400b50300004075842049a0054021071112841000c01500326a000c46411802c406010b1088020038420121207001b01040e040000d404020 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 131090251 1250 131089001 131089009
    0x12030c2003040f0e10091116140a03020c1e0a03080a050409020f031b03060a06050c0f1b0102060106050715020711090a05060f01021f0b010507021c0c050604150c05010b 74
    0x541040c4018108130b000c3c010b1030341000c2141801098004820003101413400b485400a01c031b13550900e04901c401000d10420720100c802400c440f509800e0844070140e01528019480b10848280702e0300c182c0643d04510220940400c2004411200500b031010180c02c40c0c0d03403014580c000c16503103820414280004542e24103e48000d00403030300e00c070300880d0b20b070300e4110160055042c1d0221a131510040900a0020303d403695040b0030141d800c01d0512b15282c441d400c40b8585480d001890340b42d040d118401c0e100400032001c144682a1071400c1e401e5800507a240c04003907402e4492500c005203900ca9400071400016600c0d800340150b5445402e00060460612001604c07006040c0c1c1c00e000002d5407607050001924029007034803a005800c2c0054038006224051000684100401d075418654403505540100d0303224204581140c0d0303008010700f41480001310f0325101150540b508503030b14402608040b03103510300141079030100e449110519100303280d0f0150444860304489800ca80760364841181494913a9 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 131091501 1250 131090251 131090279
    0x318012606010f0e01020a06200a0320160f0227040501060b0c07060305040c0e04060e0c0405070905041107080c0f010b0102120711041b030b0319020a121a0a05010312030c200304 78
    0x190070354000c1846000713442410728160100064cca401d0001f0040c0f034400001a864a201c130355080a8100340f0b00806001080c0e99400381e9030704c500d04141c044000c07115010f41d01c60490089000342c000b00011a01c89100304075910854003d10b1484d80b00400c1040402e202e600002c0d4041e11030380e240a80c065407100340341c054200c00d0300c0440f40e40d61901200c00404030b081010030503046084400b44041d050140f4003509002c0140a040d000b15103449010303034825040e44c11514401d521002c0141d40c0c060102002c0c1e1150041d00d0780c0402c5500b420070030b800c0d84d84006002049001c1e0b0320249860100c480c0e55101410985d82403407074006071622496040c6002c032260001c4c1c4506651004505084008100b40c10600a0007500849145000348040542c82d070060304026601d580810001c00800c50501c900c1d055200c01080b1003000240041000c5070105401a42c100da11500a018880f0080d4400342d00366401040306400040b21003a44203c1c7e8249800a011000f1069040d28135103511031301628145d074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 131092751 1250 131091501 131091517
    0x60e0721110a051b120318010b030303130209070903170309100e07050423040b090a0b07020a020f030a0b0705030a060306150e010806090318012606010f0e01020a0620 73
    0x14400704a240da6a40ea641010f14203810b0003001e40078800000c6076145c0d5030300010706011102c504c07010f100d5211703910941c000c40f11110700808698132403a1584405003404143d503c02c03402644d5039004550300e20302404040703081d03030f50119040240e484c40c40c408080d26040144041c165220704500b805140701c0c503124007103a40038040d0103400903a00703003400e20003520754109081d68907804295448014410005100b40c102d40d01c0006510030b500d44020451409130000d401074030116a2205002e209500042c20750200c500c03d42d2004201d900000806031240c2c4094405004c04001100042140b8492390080d5441140c2040c001140303030701d0f0b0b00d0b400c04032402d40754107000401030440203000040350414442c0c010a0100c0080c00180740c0403507025140d01500c3c0710444515001c4180400a0303009016503185a180a00100401c0e40000d40c02c0d04900003d88541d404100382e44180361005206000700b1580032010f03002861a6a4203a46500c01402020048400c0c05141489209001a140000c00e050 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 131094001 1250 131092751 131092757
    0x1101200601030606050123070204110c01020405030114060f09100914190b031015090504050a150b0a060804050102040e0106050301150504030f030e180c0706060e0721110a 75
    0x150b0462524104075805a082581800350f1241c0c5241010f5804207690349001401d41e8107a100c803880c0c40840c0107896000820024100b01040f0300ca02580154040e00450304220000e105c0440d040d00c8841d4401c00988840717421851840690643c0c4c181503040b40d0300004000004850150340f2101d6030111280c56405e1490145600c3c1480b291264254504c0210107040c1d004000384400744000a6503001e4141c24500c1150b05d42041e40c1043e40d612000100406107010240000c4c6420f18001d40c5600038000201d8080c51b1204656100310310718490100030f0003018042d41d0125040041c1521072160041c0708aa956401700804903848004501150003003029448058030381d4113007101c14058103240c840c60003c01100303001c208089868a5844030700702d5010305000c0702044662000c240700d81c00c40107400e12403c0c07002082c4844904400004e000c8103010740401c1008070748482034117001d07d078190780d0280091140c58203011022f2580c1090103c0b10203200303002803114030b02e0304e08511541040c1e07194404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 131095251 1250 131094001 131094013
    0x510030303060e0108060115030b03010207030f081315090807050a03020618060405030904050601200607031406030d05130f0b0a0807031803030b0109090f0b0f03060f04110120 77
    0x301500360095002510b149070743c1030181e60419419036521181440741c148000e282003001da49840c0650301062a03441c0c060000c2d540c0f0032040c10045c280200741800003000660f584001041890402034060609500c060b0794090040c0032030007480503140b80c035025664010200070345000582c041001c020442e00c40e030044c14051501b540030240307001819450650303540040301008001070000c01116105c010440c1e000403030f070b11101d00498840d25000d600c000384084002d6402c0400305c000550078811981070b9402e001130104001c5103404114192076054065001e030494208090048002e02081021044881d6510355502c624040e00040e90b84880c84007040004c090040560000229138030078080d09080c070a030440e01d03141e01c100c0f20b074015000c0d0801d5503910142500c0da02c03491401000f844082424400c03200c450011100510081103c01d20460140445d0b40f510704011417181e02c43d00000c40540c80c0c59981c1d8803035a410300c03104102c440c100000d4a008034059102c51a141d42950030300310040803 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 131096501 1250 131095251 131095253
    0x120e0a030614070203120103061805030309150a0603050a020d030527010e0109120f02030115080304080c120703060b0a050a06020c0f010e0a0513020d02071a010605030c180112051003 80
    0x200da42d070064180d030300315001000403d8900d0703404689141125440603000a8582c000c0081c55001100c2c0c01c0020310500000007801402c84001038001c400d050b04010300c020315200c00b883c503001c880d143d1100802c00d07000040d00c000549003004004500034001d051651030552560f8520030400f803840301c0001101d0707010902d6515540c2c440507882e03900c142803e0820100c3d0400060480c1007001c0f030001405026120006002c640302074000c0d000b8103082600f00c1113a5920741e01c02540340d40050040d02154413819000e500c0524003030244410001c07541000d000c03046c0c1191664030280000d60080b54022100340d070005426111184250010100b0364043e00c40f404580c001c00050562001515040000a0610090340e0381c0d00c551400403100c084800e0000704007182c4880020340505440c1c0c2c1c100d00c0c8041646001c1c4503044600e2400b502c081405044c1680e201c100070348041c002942da40b07030b07104801d00c00c840307031109041402400d2000505041850710341d600708031010b684d1300312130483c00e4001d0040100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 131097751 1250 131096501 131096531
    0x130806071d1c0201020f010204090902150403170304030309020a03080904050f01060806010f02010605030f0d020601092f07050601090605040605060c0303220503041e080d020a120e0a0306 82
    0x10008103110740c0c040c01003000c0700c00021541c116120042070030141e218420b204581c0208407842450f9070320002503440d40e43d0303014007100401c1d1072607003a4094070791a0309650007100c0040448090300d40c005880340c0102c1b200ca0b84603003160002002207040c15511050034000d81d03142c1c040340005501c950b007503e548034079901c280400d07508050304142c440840702005201035900000e006030310030402e00c1c14900020000d001240034010f00c1c3e10058040c040c607000108588008139048441481765000c540701030740e07203a0000b81111a0301004d003241004101040441040c003092a003180c000d0b2031a84e504040e00b986449007010001e0748401c4044e99141c2c020442e42c02c25004681c0100411110350b030410382001c0d034840e16440014101d00e1507200301d00c0c9102c600c40800c0a00001d07203804c401100c2d142c640b0359601c600781200e044e20502c550b4406136400a1b268800003203406c0d01c40d80d43d90240001d56541d42d0743c00e142e0a0f00700d665005204039409060440e0b2501d00d0300000945c0901c2011982202d168510 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 131099001 1250 131097751 131097767
    0x310150c051002030c2101060e10080c03040f080c06010503010b030304060c02090408190f021c120c020705270a0908040311040f020d0f060501020d0212030c13080607 73
    0xa0052019035a0000041040403a40559404590740c0160307590b5a85003030500644103000c440007444503130b510303000a03010500c00d489050703e00946030100c0702c80c4d0031820071030400c12200402c00041c00c03040000b1191654800656001403052590170300d01c246903603070414590030025407220320360710400040200346024041c00f44400d4054000d18602404c0040050058110f124041c0c011100c2901003800c01c03209500f100d03402d40d071203417401d8001c400c0d21000610f54489106c0000040c031604071362485c1e41018400307000042c0030540710b11070801e8402688601070703e903200281c0d0540c081d596000940fa1500c5074204011a626000b1000c43d400c0c1400141c2680300c041c04c401d40302490902d01d400090520f000311303000e40741c2140c0c0040300d141c66440041c0141c07802c403440440860011603185810691500402001070404909204c00da4039080120303a104070701905200140c4c00006030b0b0a02940e12801190042c1005908030326094814990540000c0903501c02c0031766a02402c204800b4541c00005 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 131100251 1250 131099001 131099039
    0xe0c030c01030e0c010302090a09020705071409070504060f031517060108191506051e0f0f15090a030b011203020d1110020918180c030102030f070c0201140310 70
    0x1042450100b000f078958035251000000e060581c00100040030742d581140240007813441410555036130020b0718010381c80324414030030301c104503a2550080000b0f160444c00c2d00c0c800c9459544503410140740681c1195440d034020500004c0c19910501010628640b200b14030161481200451080c00101040d501c4e001e07051780540d04903000380300d002e03400510103501106603a030040704100101c0c0fa001c0c4143c0c010507042d48010b60040070805421202040c56441c0c64182004841d4000300c0d01d8558248840504203141d2141d02801458407801c545951a002d400410313000713481c1651341b82e160b903203c4602010030b8201030743c6400800118003c042e070404c540e0740c0010030781c40d107009011b81c01c1e1290f513a0303102c03460750700b4002980129500d0000c0d1600d48541072040b81420541806007484180c0150700210642507070031034042c411849031a41014000c49000700300016030100e00d9540e10804454001c16024124100648c5007a8280d4420f403c402550094132504c2d2a865098a021620b00b544801200 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 131101501 1250 131100251 131100257
    0x4050114030c0a030c050111100513020f09060a0306020c030708070602071b0e010303080c19030f0e0106050a030b07030e0f10051012120e030706032c030d09030309060e0c030c01 78
    0x10041c40080c905d07114241c2159000e007042c881e0a83e00c20503075801c0c091942e124240b0b0038544004c010700030581d1300113486418004e48074108030501d124140a201c800803500759800108041c0304100280c000e500501e0709510000940307060500300d07075860711b00d6400800191211900490201c0502811314045501080d504421104c100e03e032269086600300144400b0b070034006848001200d080c5410110b50300440c3c00e41c0c14a98400d05850040c004014501007006494545180308101440522600050f6030b00140600c46903859540d52170b5028074000c3c100410580c480c0a26201204200041d0b903030126041e020f0b054a01084039204122100281405a1024020340810140780d040c014003082c1d613003012082c105c000d41c4020a85031a81c1c81d214654040c400e109000904c142d240d40140c10000124041f050880e10580511209100ca84144885138004100c81420702381a50700c100c941c03a100e42008507429486844450480750185440003440d00000040081403809014506e1040400d003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 131102751 1250 131101501 131101519
    0x204120510180f1401020403021807270b09040204210b070905010c0f0515162c06180402070602030702010e060c03011413090c0618030206090402030a090204050114030c 74
    0xe112055081000c000c0136101012041928440030000c1d01214003540e0040c2c0580009040000f00c115080400c4401c240010b91002c15403030410752800b030910860140c0c84030500110f00b0041c00c4491540001e041300c1c0d120f0707400c00c00040c0000c402c410016a90315003502c2078944001e00e08141050400081a9004100b0b0181051002c0e81c0c01c85c04030440380d500301c6020b45a8060381d290542c2350400c00c148030351050b0300074010814002c100303000501c0b5591080ea40d911003481144001366805201e036620f2829101480c001d2010382c188a00908080b0030b54100c0403860201500c040390172a4071403803043d10390310b07000020840403e4090040b140c0154100e0000c00c510300d4103000c02089400180a244c080c0c0c40c030203c0c003140d50350782c0002d0240d1030000101d08001c021342600c2c01c82c1c6120b025121f80000b04130350703100b0442d40c0300441d40d160b030480390054411031400e014101008000d501c014030040380c481c1e84030080c4016858178428540a8901c0903c101d2030310b0718013000c051502c038640454508c41c0c9010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 131104001 1250 131102751 131102753
    0x3041a0a0212030406091a15090405101523090906040201081f09050f0421050319060305162d0b0c01090f0303060612020a081306020412051018 63
    0x190180b04018800b03450340d226103072403608002412004002070b00140d4034003000351040509084082c081c0c0c4002c2c41c000710308500c860502c106410126409805500309041614030b04030aa000300004c40e403c0183c102d8501d80f2070750b00403414901100d5550440c000d002c04422103003000712500ea000703101a0020580da00d03259000030090a40205000e41c1c10310440e601b00d442c10000e5031050050120507000b0301080c035204202007031513241164291002c0e0301c1c10b4019021901c504240c050440440d03558545107a56a500c1d800055410010f01c0030101c3c4c1e6406d00001103041444076503a41040a4800003000e0300c1c1104480c880d40e0900c803500125003c0c542091000812a083c2d107088585001003030782c880b40da18000345d00426290f4006052418001510000c165250344624140c80407616194901c1c03003c180c00700c0880c0140c8201001151a51003c581103003d4422408040c5202d58000b42c540b54076000710000c1d400509404031415804480341d110300304d0443c0149034052000c01c0d24010b0569807 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 131105251 1250 131104001 131104003
    0x20c19050d020d050304050a060e090705071a22050a12110a060b04020d0501030f2604030204201305030105090118021306051005090906030601030b150402120903041a0a02 75
    0x1c840300003441011120310301400c0007004d10984000300401043c904c1003a643d000c0141140103d480c912f486003c0b424000b8440320300070b2081e0782100d0b40101c500840a25031705405040c413580035140611135007035480d5509140c680b0021554000e4464005440d0002c8103103044681d03209461404d00034001c0070503d100c5041c0e400035130b4810701508035401142e25444040814024800c117a0100d1005052100200601105042418425208280b1f0401050301c03040d00d0081086225994841700c40104400c00140c074194029400c81c400d007403400741031044200302c8100294850045500d402a41d9042088589020703c0345a41c0407180400912070045094899088900f98800003442156011001c070314803240c690001d030151501404000300c1c401241e070301070030b10341054110a02c54610080082c54a0034082400c03070481c3d61000e800d880a84610100c580340b041600c0c5c0f20b6401a90078446103027031003960202030340550140000f1715903590410582440080d0a4032501c2442001005040d2070b00b94 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 131106501 1250 131105251 131105269
    0x3070509131109040606051f05041a09040c03060f0b130b0c16030605060f0607020d0303020f09030615031212011802041205010b010e12060c03041b06020c1905 70
    0x1400d1210425030071a289000e80b0030200801c515500040344204100030030420f070740440c040d0b8400303ca40103a544a8590403030001151102d1900010b40148410000041c0e85480414050302d4042000c0c10300003150003180440c1c60070400000042d407030301c9080061329000c8a400c0040c00180f4550761600142000700e101020003842105501070001a200400c1e0b0030501181d6600140340c0068004c1c25070340c0c14210301800e010340d81e44d0721590118503210607501c1c03d00700f110038180c0e02600300403114089440c2a8004e40240c0d8190445071400c201c12401c995060002c1403050418501d00c48580980c40140741c40c04454000450f8251010000e0300070310058812440e0440c0c40d00520303034000400d1407020343c0103401990711500341407581e20840c000f0800107422901d007160007039903007142d04020541000b0b200144002c0120b0340350010004070725054400340095620074050124080101413400014101304459402540141c100f220990410b01d00076054440500801c4a01c405842c00c1400140841c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 131107751 1250 131106501 131106511
    0xb0403030c08160b0103030c1101090612090303020d0213083315060304060f0b04020a1d0d050f0714010810050108040c0305030310060e03030f030c030c270f03070509 73
    0xa02080b14401602030f5100000c0b00c980c07008100440f542d4074174000e802502e0b901022aa00310000b000011349504c2200c80c002140e890b81d41f40c260403030b00408400010b08500c401903040540821820465000c1030005107000e0107000d910380305003491700c0711003810140c1d48028034040039002e1130204800c542548a02011100981e18000c43e51500540d03030041d1501404484c2d04130034040100018404a50300000003820042c006001c0f4400e04404c103c00c034400c01c4403903000320352010310000c003c20255544024410780601031002c13589564a8003880d21208200380c0001d40c1c0803060a0003091100708042400205c207080105090a01d000380f4210032a15007c0c050420490200050078404800c10080c021500141035a80c1c82c20502041911000d03a80540310101d200342c100036045080000c100c501c0754040100050941d01d0302c103c200d120f0b5001502c0740c42c8501082c0244c10100320070010800c05144449400020b1300b07954001d010080c034940718003d2081e0081e85040019071192005035070301c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 131109001 1250 131107751 131107763
    0x1103030a14030c04030209040f020306130b0a0f020706020d0203190204030c0b22030c08150103200a150302030a06090b030a1203060306060b0c070803040803090d0309031a0a060b0403030c 82
    0x290354040d40c5904601940e030000c2c2d0700011f01e00901c000d002c00c1144a800c5030b8025415208a0354071003101074070b000b00055005005401d05000078a10805c50350041c028120410300161034404240c464100303a0300959480c092030b560000901c40b000b81c07804c1c246001181890402c0d07041c149151504120441e0784e00c0795205040700003900e1a40c4010070f40c020700315442c06154221181340c0b68240fa85181d000d07409140385504c02d01074440e400001c0501ea0b9812641d00c000001103000801500060b00c80d080880c56030010b41003040458030f884c2c140080707084420555401a10391030200c400105a900540c8035580140ca400300c03009080d00c000c103c0c1c07403c1ca90010606055030029180440007460b1035400544036900e000d401107107505400c002494001038410489440644404003623131203125501c184003480d8010020041c507030410452558886010b82003501c052aa070b9100c540800c1450300c000201803502c5001c00664010702d01c43d000150560181e81d80c1002c0c203658029042c000c0d01000a401 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 131110251 1250 131109001 131109007
    0x13020a0e0909030d110904090f030201051e0a09050c0306040b07031a1e13060303030e0105070302130e06010210020f0307030c1e0e03010207021206100503060c0904020a120213031103030a14 83
    0x41d0340c8040084510486c00a40100052445820100b5400702c1508044005508200c08074400003440c00300b03040111080d4513600700d281c8496400074014268550100c07400d001d075403140c240c580c2c0c050119a02c500c1c00f940c2c1819845c0361401000b002c40322800147d90140d281607291241d10b84800000c0480c400403a41c405898100030400164170541c03030070304403c005062000c00b20030076a244d0407060f0303107020020090045480305001601640a00c0301d81d80103046185104014030b00310001c0c80c41c2c000d6018010f584100740d04034208405da0b80026040c01c004007000061003a040d41c580302d0301c01c0141080c0b80400505000d000c0c4d6151000d40c602c852020042e0300310a0740c0c103d540a44c11945000da000b048000350800c485e40c0d80b52905030031121100c1c2120180b0001031030f400c003c10b045d44070301524003101c0c1c80c02080a0800c4002e402c900107443c1080b6007010002c130313203101920003010784030081210108120300d98601507a01c4019103180302e0082d04180001075026800c4400c09140c59415600e25071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 131111501 1250 131110251 131110271
    0x311010605030f0102180f300105040b070f020d0503010504020703020123101401050f03130605010308041503180f031e0302030f06120a030e030c13020a0e0909030d 72
    0x10250030300740c01c4903505000d00078414864510550003461404c1d40a910b1641002001e800c01824040c1f4000325030304008a001d60100006820070704031440b41c0d00c0c070403400140c4540040e0030308495044500f2034450450708240610180c020485032420f0600e40b0044c076610141d400c0040c0f5500040c0300f0b803401250003003440c1c42014000c1d0050f99800e074181c44100003010906e602250045015104071014440c207104c041100680d01000d6081908181c41e402e180c0b00105030701c4020f6510007003214402d600680018400280c0f6400343c24005c60140007126100e5007464600b4401c6c007281400300c001c0c545081e0b00c11061848981d844120a45c06c50f021081c00c1c201802c0c1581c4178095801d40c501c9242c03070701110109540d0140d002d50f00904000000030301c0c0e60b03503034000d2048481001c2c00080d56a4010b1006d100001d200d00701c0d054022501400f03844540c100900850f508946002365151350703a40204d1003100342907001282c625400001c589000650400001203620380c823130005000c020719140c000c408 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 131112751 1250 131111501 131111503
    0x80f070f0f0507020d060605010806060703020a020616150c020d0e030c130603140f010b010e010c020f04110703110c010206040807140111030a02070c09050c0906030603010b0907080a0c050a0c0311 86
    0x10f00000e4010340556a05030003840c2510040ca1b8a01030385000c00ca205001ca045030030074406403052035038107400803c0326546540812846401c0400045102014038028400090f0480140000d108941c240881c040c800a0b1002c1d007040e81e000010800c011683c1060401135400155002600703174241d600c07040307050350100c14101400c2550070207059001d62030785841c4020800108010412507100003000b2145c2200700440c0c90103d030b0780110380001d03031400206002d451300c01600b520581e0b004100041000384054010b0060b00030394002d4010954010791480448000d10418141902c2480600010714080c0e444140030702424030094001400b4003001d400c619825070000c9000c10001c1150354903031600c4440103010303500081040303640c0128200b000402d0359050041c07a0180c81c40717240f030314200f842020030301403107400c0102615815900d80000c4110f5480740e034040c50040340c0580c5d5608041c42c0a01c109416141a80103e5041280400c690795180d40c1c068000c142c0c02d80c0c90f25000601040c1502e1003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 131114001 1250 131112751 131112757
    0x30609110703210c02060906070507120810030209010f030c0b0a08071835011109060a03021317070602030301120602070218010806090c190302010804020613090b01080f070f0f05 78
    0x402c8070113140004203210b041c1c00007605449a2884d000302c0d05a555181401c0343c0900588600400c46010181440c042d02d008520340c940c0808a09242c600304d1340d4030740009185400c01c0c1d000403050714507268103106011500410801528120100034504201d07002c00520b0700308000c20f200b0402501941e150000b004200200008256903205401c1091004001e4060480b00b0b40c444e500c011412400340e095490117001c0c0d10100e4182646607803c200c2000300b400f909070f10a40000003096420003882000030620035a00f406420b03200920180140742c00700052912009070055801c2d540240010082c2c110401401c01c1e00c0c40e817241001d600e0b0b240ca4804200000080e511050040d8910400401c101800041251003003000404883c600345500092145180b080021441020201d140c184050750103110500e80007480500342915004002e40c001154503044e0b0030400200d92503202002036503a00c0303800180c04c46200701048426042c1003030050078204101103110300340b00980040800f014040c80075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 131115107 1106 131114001 131114057
    0x105061e0f060306030a1509022107180609050718060e0603010b07050309030a080a0306150806040c11100b090702070305030f0c030706020c010903030609110703 71
    0x280946540f0081c015605881200c0da000001102441c401c8150402c01307000280c800d4584c410080c001101032000042001001140e0240f840702151180032a80f6034001c0d041010060114000030701581d52040341480d1810040007840340e040082690144090200018070030307140c080680c0c0b00d08200d5a0a50041800c3c0300601001038003000a00f6018003c108503402c1506890009240842e611000c0300d0860f4081903210110b5014019140903005a94000000500c0c06a00912034203009107103038421900c0f0f0000140080c0104c0c00c992040d001c00096480e220703072401c0d410011304030314150f00307003c1d0305a0340c0050102c92000c1003140540b0fa202e800f6500c0d01812407540300b000d070002c0100c1802404104200400118541f0040c40209800800413500c4060b0b03080190441e420396000b04005030030083d03110b420500c4403084800c030036810f04106100302407204203031142c0030426403 = true := by decide +kernel

theorem cover : BRFrame.Cov 130935251 131115107 := by
  have h0 := BRFrame.cov_init 130935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 130935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 130935251 ≤ n) (h2 : n < 131115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
