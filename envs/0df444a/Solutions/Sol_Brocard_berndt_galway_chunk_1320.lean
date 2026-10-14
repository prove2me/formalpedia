-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1320
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:21:22.750371+00:00
-- url     : https://prove2.me/submissions/112aa584-c111-48dd-b6b7-a4859c5d6d72

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 237230215 ≤ n < 237410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 237231465 1250 237230215 237230221
    0x204060905041d1207050607050412110103020c030a0e03070801110d020306040b0d051501060f050a08090a1b0320090601030905120a030e0111041a212502010501050306 74
    0x7001400000c0315848201140d5251407a02c02d001340008400004003c8009a442038240341c81401c0c032400920032014445d0901003005915500071800141303a40c043d25071a808448900160024007407286102c90703501c0702141032881c46400001110045500b14211400d2542d261a51070a9840401041c5840f070400d01845a01202c540c0180d900404000d00125030800c91401040c2485020b6000381c805a0020091800ea080c0d103100380780c09424245407003240c2101c0a00054824850203000104000306000040d001400503c48001c40702e900001c07055800c02900b41c030340b405580074042900c1c0c808250041020710101c0f5080c90f108203201516800469550300c0040d0011710700c0040130340d2240548160b51001170f050800a00c194201c9850001e0f05041c0301c0d8016003115000e01c2d00c8030407060104002e000640520b404032001c85246c4203003550f102070b242100740040d0303010003010405041c0e200034840c074420030745810002d958852914541d01841480304030300742c3d1000c3c4151500b603003240004c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 237232715 1250 237231465 237231469
    0xb0d0b04060b03030720030606150a0201060f091508010c17060d0204050702010e1501181d0106181119030218120703031b08040909150906060e01090204060905 70
    0x422984039020305000910480c1000c042400c581c001541250700da800b800300f680005c90803841d0b03c181e15100f5001131085141c1007010420341c5168941c8180701f80070100302420028800d4102d000907110200950382d281d907440420601410780303549819201f000d01200410303103034414450751803241b400d42d071020b450210109500c0703050381001d072026401c51199030040c4003580701c80c05002e00440700c80e40006443c3d84901c031900d007031480c1d035420600408000c900410000d0290000345106001c841c40010380344490401407220b4112041c104134665081c500300040004030711100040382080030005001c41c075404103070313120f091203910410b04002c4d503c0680140890310aa000d400c0460704035951820303901c1d50030b00050143e4070341641c0300c100d40e22204041c0105540454050741000708244486420001981d4103a4107020364058a0002a41c1d0340c01141071081080186401c1d4000c100200222040c90601901408041c01042d2741030003100000038101e40c0c030b0300c2103e00311419a030300c2c02c190504002c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 237233965 1250 237232715 237232733
    0xc0308030402040e191b0e10050f0f01021e010902030601031406060405090d0e040f0f1d0613030810090c02160609050105180f060307050406021b091303120203190f0b0d 74
    0x103020a1b0f018a5043c085280120044001e00803140715419058480c03400c000c000310180e00b208024090a0500120034143c1d0b000a06e448028001040300e6103504080c0108a0042200f030304040c1d803520030200004180041400da00150000c00d0040c0d400a41d40c541c280302c02d5500c143c03140c0c5c806900c250b200685079440b8140d041c20030030307004001003607500000c0c04200a4820090101c1061035452100c1d50500c69812801c800850740000549500d15209003050f0009002c03000180c00c0c01285c03c0041c809030082d8002d60301070b002524042201300a680c2000355030303542e0442401a1141390100100e0594024801142250b5059459903e40300d9100380315283c01c0c00095000b07401401500f0710b503655940307182c0514450302d002d9660b00d0b181e80c07404500a00e440342c1c2e071001d001040140c02e500b00315500c03031011490b408a508904004824210b140c2103420024442c810b1582a102006202c5000101210342c00031081d00742d400c1c4108000e1100d900308954184207800e50006460900c1000140814 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 237235215 1250 237233965 237233993
    0xb0a06050a09051f0215071407060e0d030902040c09030c090e01091a0f100b0702010c080903070e10080f070e040305070b01060906110109110118030c0308030402040e19 74
    0x210b0100d0000f959500450306011090321440e40089182d11668442541089041c0b960381c1c282074008041d09208001900400c1c1c8050150a41400003d0300c0c0240411500301546400307004040754000101043c0c010000c03c02d406e0200d07c11070500c16000ca100b03224400c0001540d8004a0314041c0514000e5150000e003442c41422a440d500d40d0b1030031000c1403060345002054940d001c1640e00c3da14040c5012214948018400420700d0716160f07050000070105001c1d01d446a90a081005000120b0304242010703001d5100482d52611503010041444000482540d00a001c0c5043e1150940d460b20120b58a6580350314414049521503c1c3c2044080290452940c200303019003849841e246140d1684811580260811804912054820008a64000514000b91440200802c11261245d0710711340c90240c9104007504010160351039600d84d082540c2d10390300840d440020701c0100350782c1e4900750302250411541070744198605840d07401062004101c1007000c1010409a03003000c081c60b40c800c81000c00d10 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 237236465 1250 237235215 237235217
    0xe0f09090109080f0a020d090812031005090a06180e2a0612070e061809040201031d0a05010509010509071703070c2621031305150702070503010b0a06050a 68
    0x150080c940403540d0f65006251500c6002401d60b642e10104101a2404008117040c0c0100018984c0401c40307207002107030440b003071000c100b01107650b40c036202046000c1e5842900b0655001c415482880f014030740b0380c0d00120807100b6071822203041c4000798402e10125001c50401e032025400900395903a81c4114464071030f080c4e50b40c40d80040e501c1c1c100c0c0404500c15400003108510b00d055030b0001d000000c1c0e000a85076843c5002115040c3c43c105201003080c0fa08112585058000d121450110b4210380c02038002081a1002c00354403260003c41003040d6a40d4550071034103413a19482c2901280d114501801034502c41d44030440245078052030200f041c000c1400703419510400f40014041140024031080e1500010140d18842004000921070b007401c440d4120070180006070b0100c84c10040b9004001500000069624411a242e80e9440c21401d03040030b00c8200203003280204d0180d44080303000c4107915400f45d0704030f900b142d42c3d5a40703850501d4200ca0103650703411ba2203015941d0401205100b41d000308160341c45 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 237237715 1250 237236465 237236471
    0x206090402071b06080606130308032809030e120d0f12090c08150106020d03020c010e06070201141003020306060918010c0e01170c0304230d030501090b010e0f090901 73
    0xe0b40c0783d10242c0185110f48a02c40200081c0800105501c2a4496040542207034850310f41044000400300402c41c512005050f100040001920000103174408620305040c09018211509103282d40d400034286150114049026202c41040d00d04159069a410090100080418841504040d20036082070564070b41000404440700300b4041c3c180c000c4840080c810030340760801906103a4010700f0074002c9264520341d40d007000010065141d0000b007c1c01120600d040043c1e4950500c10668003502d421035004400303208000a10204560540c002c3c1480c2c0310281d5078540c661a5408101410f084034400030794542c0c091008a11986481f104164200c150108a4540c506814030403909450050315110701003286071195510a582000054880011030146030216245c40600144035002c05070000d000c8013545003080b040b80e8007000c18800d6101c0c0ca042194184418031400074003800003401040d559508012010201d540592107026056000070114904006444141300210000070302c1a0030941d2 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 237238965 1250 237237715 237237727
    0xd03061a0708300108010504030905150f03010b031f0602030703030f320601020a0b010308071a09010b01021c051204060f090605150901080703031404170307120e0a030206090402 78
    0x1046018802004070108451010b0a00350701100140303c00581c450b0710164100f03420000026401945601642d5041301c0c01c2d2180f00c0c07001c50054003401500c010b040900d600000204001c00c0c000042d51144200f041214507401201150340c844054510480015070301c2480b00d44002030103500a601041d9000c0b07000a94441204000300020039060140e000034031a001e404404c0c40300482034258004020f000600308054079507503803005330005210250002e04041500c8040040a170443c02d00907504000440190030311107083c9008103400c803034031070141c803815020b49181c506808802d0180343e06ea13182c850501d100c40d4144138510b10010000ca5405d83c0d19004072642c0301a501c2585001e5004030720000d920b24260800c0d0321070714600c41c0c465100e4460680100081100029100c064aa140c42c02d0b0000158500c08440e050160390048500e034030741c1c054001c17009003000024001e0309008074041d00c005040d5040035a0b10041c0b00f01c00e07981018040304288054140100100010341015000601d014 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 237240215 1250 237238965 237238987
    0xb09010509040216200307060c05030f030906010e0703050f13020112060807210c031704030b011203020607111009020d0519050f12030a1d070b0406020d03061a0708 72
    0x640a00d255039091052007006609100070b5003c09a150010f4500c0e44405c4040e0744002aa02c0c1c109204180420075541345003803c1290031304c00c0d0307617040c40c4c11141d894072401c00340510b580303998007405214807082000000804441c4039000b0036020720a0a042c0c000152103802c420390f5440503940c02641405046400480d828116100b400c0007014840007070b0940c0e604040041c0d00340c82805414044110005600380c010a11a88141c1d0440e0742c0f000800381c801e6814002442a800740f944060b21034543d51000007441110510039400051090703082d1030080c1d8600005849070504203840950a60100002c00311132020b43d404010050300003000c0b61501c42d160760300c103860322800042115940b50641c1075030f420010101f10030320714101c2240180030850784d41a59011b090000070601d2030207603114000740c6440c6140d40300f11800c40c1c1950003901c1e2010307254118202c1c41c0d4058801d03840103105840011101c644607104020945010b6696001c01140100c81d440d425001a203003911102400c0103107031896 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 237241465 1250 237240215 237240217
    0x405060613090c0f090e0a0203060d120201050601140a0212030601020a06020d02090f01090b03060d08121f060c080909040519060c14071110020c1309020301050106020f03040b090105090402 83
    0x105424000030444003c0c00a009010060040c80301d02803001031117041c80400c6c8082003545d40004003000050b240c1d9a6074000510a000340400a00101140098045602e9041d0030152144000ba2141815084010680003a0b40710303802540c0e0041c1c220002040c0c100a066008540160051040f035800c83c2c241d49440701203a20600c0b032400d06640c000340003002400d25211042400710242821051325203400907140c143e10006241b94481d1982c44c0c281d100b0040c2d004169100104a01050303043c5143c61041003404031408407066500700069800045c441c0e200b28180051594807945d4181409441014044010000341c0110b503e80a15400036107002060444d0b241c00c2401000003045c1e083d60b0f5140908042c82035034100c503601d9410031508004c18503000410314a150705803250a166012100c00700d00b0400852307040e5600403807510903c181210701c0d80000039203d00813002041180d99440091341e039211520301c40c80c00c43e082400308104600048004d40044141810860f103001b0303800e80040c040f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 237242715 1250 237241465 237241469
    0xb0901080a1d010b190b12091501030b060406080f030913020721091410050a0e041a120d0c030507060e07170609010605060f0c031312032a020405060613 67
    0x10b981e541d544090314510700400001c0b03800c28214841005c56040c0ba44017a403034842c110038084c0c98907814011800b80101048070544191a4203c000902c3d6124030300a001200d056500a10039401c102020511440100d02e492207480702e01c4c021490b10540c0d100307014101e09500b11f420300046d400c0c011071010583d04020008581c000c0f00c61005140307c008005000f8500325041162840c40c08220350002d03483e581c041c06000011401e207940c0344c1c00003000844000301c003441584e400600b44040340425a10301e114522601d8401c464070345c054035a0b9548140d94032030180340800090107042603900400d0189006209042c014440407030350081811400d0701d05406640034182428035080d8003c5910002e0281d5a00b0555580003403243c249401c0010340d0502849030810200d500000c1c0082245104000b15900c0510b40c07640c0d50119595232400c400e580e409504180d02041002d200b40c010a640c005c0403408940074070180d042011815000d00c402041c00510540c0c000c1810000006000d00113800d500c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 237243965 1250 237242715 237242771
    0x9260d0f110a0b04150e010e01020901090b03040c0b0f0d05040b0a06090b100f03140408071703220f08030a05150a030c0306110912030a0e0a0b0901080a 67
    0x84060380c00c40010070400c4800c81c0d844440d0414035021000541e80301c103582e0425000540c41d052801070702c3c8503074010282204032008562078103060400039401900034145504090f00d44500c0e6607565510582176100449000300903c459040034031007000400050420800b800b0a00b505003000b44800004480003503d080c0d0384640c2842c1046020b02c0075000c0e00001d842d00710424401b581c280c40116401592074004002401026582518107504c40e034841c01c90402c0384034501647d41041c1c00c001485501c049002d844100c8282d403000c00c0c241c40c000480e80078181907244400c6817403c04100ca441440c00f01d41c102c6ea40c4038001c100d10086040725000c4d50080300014400200b0303080c0940324a12040c0c2007060385006559402003003020504215002d000c82e500810041020405400890124850f41a8456001c5c500b03189071456404004098490040661642040840c5110410840e010b06100b11034400e0020032100200c1d51080a280390048002800403c0340c0e500700050301c44007001d0b04507000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 237245215 1250 237243965 237243977
    0x190506040b130506040e070c0312140901050a0203060105341505010602011a040b04060f06020d090e13020d050106050919060e0405150903070501060902030105091609260d 75
    0x1a8100260b0103001c0c014031045808500d403030b10b001c044c882d910800400007024452000d90241c145400703514070a41502e080e408c1001a16040c070700d00b0200341425981a441c40d03207000c0c00104411568400c40b0b008810585659041103403102002c1e41c84040104881184100c0d02c052480a039250351640d90400e1040c00f1000c2400c040c84c5c08c010880300168805c00031a1f041c0691440f84201101c2c42c03603110074094901240181040300810b003e080254000c4949040032200040d5031540400c159004041c5c41d62070440641d910f03580310b00c603810b0540f6014030300e601c0316242e07800500e400b032505c1d40c07040e1040300007290080d61032000a0700f41c0700031240c0b00d07204071000e226240f0484080c8980009016001042e488604060f160103136500400390b000100a00000003103200d860080050b2128107500c00c00a02c4a545c07109800f001030f40081c810240900c00d00000714800c01300014003902072410780d030386002c002440e000302011701841e0080d500306040d00d5500004640c803c14008030001030100d071202 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 237246465 1250 237245215 237245227
    0xf0702040b0409021e0409080d0e060f06092d01061e1704080306060c1906060b070f030305100506041202010e09090d0804080903010c1d0d0b06190506040b 68
    0x31106454010000c1441549402e100000590726a03102c03111418000ba002c0c013440281c68041030041100c5070000d8030488010403400c5604038950400c501c450b20007000ea5080c0d4440c00b01002603950b0554200d640700e00c480001429503000c81c00244640c12054145806c12680f41e90405030615080c0c200303c0000c2c860810703001034840d20500c880d09407402807610070f0686151041840c140760002d4401003000d0300c00008110242e44e01030540708005600f00680b4035001103e19504d405565010085864508201c0000384055451b02600d0001d5004081e0007201282558110001d1500401c440da11005c0000c0104143e01c0d18009813003d0102c02500484429890002400c03803003500480c0d601c111040c0f02040142080451036011645150800c0d10442d240da140030541802000001030f0550f00c1e10090034642d590164000103c5004034010146c1d00d6440020302c40c500c801400e0240000300d10402142c80b1b070400d402100080000c03003403000c074000c1e00c0b1300014604ea40654041c40e68170b00045a0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 237247715 1250 237246465 237246469
    0xc021e0301061409010b070f1707060605150910031b0507060e030415050708071e02010905100c0209060a05120d030b0102070e010603090f06020c0a060b09090c0d0f080f0702 76
    0x41d5002070610f14040c41c803c6003000c070000710542014001c4100210f40403d8400400c0000c0c030720300b40490ba0188880b82d800c80050380c2c00c0056003082c101690b60a040c075100003690704101e07203d9184005078403900b516042d01c0340c0c01e01c81680c00e0303403840000f010b07513640890404510a00a03100040d03066a81d6a5031254541052001c1da0003040e9215581e800401081000300205940d140d44080c071800c000b51200b0044c20b004400340140d403000b070910001c070b1031800ca01d0201d003044014114401d88031500b80d15200c0d0240000585140d084101044040002c8000352070030340313501031b8402002445800450b0711203012a641c100c0c0d02c01c4800b515401444540a0f194060042c0000403100b0310041011510302041917240725018030544080c0340d620000c10341800000800016195006142036540e000c1c1c90701d000c1d070f880c540c03414151036041c40d144846441d40b401c52f0182e400b8170030080052202000d20020006614203c40086804010744280c8000080c4044040c203801061080d1441d26038940d401 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 237248965 1250 237247715 237247721
    0x1c030909060e07110f010c0c0b07020105150d050c0d0311190b04060e03070c03260f0a030c0c05060a0903080a0e100f0608030708040f15020601060509010c021e0301 72
    0x40d840d00d81008000e1000c610220041a400500d41c9807020301c06407034001107403e0080091001d1515402c107201c0c00e078100c3e04a40030700503103441501d94035010f642d1030000b01c0c00c944040e603420000e00c0000403100020b250840f4100e001038016011394107114060000104503640f10042100030891420142c4a000b2050108004541d40320284c03814080039030342c600140e020000c00c000c281c117581d0340c128050b0300c41c100709032040d5a500041c94071f0210349134286480323465592404014442e4200d0381c801300007411a02030b41d0801c0290329900782444040d0310241c02404e1840c802e501004405030000021520402025000f122001400034481d2001d050041054000800300f0341c7c1d0034106102c01800340000a10000c0c5031038407040c009143c07050b11414401074900c0da4070104407480b0105984061206000082c4100c408990440103003544c0c0302c000c1600080041c641300c4c0075030089001000304034014001082d00740e4051610900c0145644d0001d040280000d61801045109092407030301c50900b48 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 237250215 1250 237248965 237248969
    0x180706020607050a08040c030b090105040b06120a02100c0b040f0521070b18070e0a0e0a080a0302030403030b040c03050a05060f0d080918071e0503060901140d021c0309 74
    0x4030251016290156001d002441002d52900400110b100040d0601c0001a656000f13568000f81700c607402e0030190619400303000f041d01c09030b8541340010041012890850158840038900401401e007010442d020800031500b1015902d0500001585c0080004c44144900d48160b100303040c0410000e5690600c1d5240003a0180c2095890344c850308441d4105042000f9914190f6000d040c850f280d0752005075810790310f881c040e01c03030869114241004c40e0300d1619a1042c0d200f100d45840030070424411602c031999a000001c00038203480b004004507024944a9001540e015001e81000300c3c050350101c2c01329080707801100c04d080000b40e55806010700500c4034003030960042ca085410f1108070129070006000450703a00300050112000041040164070f810b000c0c0355402c0911084076413585040c100141c915070201c903692088003640840c009840c0c3c051003d803401a0400b9120720b14603030038001441154185094030b0b40c0e00c0701c100000c400060703890110135186014074101d048520503091902400404440e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 237251465 1250 237250215 237250217
    0x5060709030b01120507080607051b06040c0e0901181110080f0a020d0e01020703020c031e06012102120705040614090402010c0c0314070e150a1503060509180706 71
    0x80001040402d40000752141518900f1204040c598003501e003091400c01c10358801c240701d020303034400c01c9403254101001e8261003004d009a1501c02800441341c40d16400300b00c40003010010180024070280c48001440c940c080c41030000044d801c01c1c48a02c0518074080e00030221003900c141003000c0c4003070400000d01c0552270203a051000403800d00500c203c6800e1001130511500c81d03808600340c04511401d030403040e07903c0d8803503000310350310384e103c0c10000c0d00c801899070654041c2c4503111031659103c4c00c80e11030114603c0820040c00c0d940c2d0900050a420144a0817070009080d10500c040009da9204203210040189500c011718013545458140400e0340c17169071000c0b1424820640d5000a500c0b000f43c595030043d42480e25010356032651420b10f0740c500300c40d00050540880a08906860000029081f068403502d05001002c0ea039420300058242000d070422640142c0f03590404c10420048941d810014006402d0202c3c40039100e01c0031408a8604551071441851040c000c6040f130b002c18480705001d0b00c21 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 237252715 1250 237251465 237251477
    0x180607030e0603070c150203070e030a0b06010c030c05011a01090501020304081902010519020a031205220507090c09030c1401050f030a0f05090c010215012d0503011107050607 77
    0xa5140a000e0079504041c541c040e942c0040000d2000d0300c6007200342c810b00c0e401036100f0751150b40c0c0721042c0001d42040b1680c0002c80c40512800102d07142c0003480c40d03c4c840c1d0150030203a2079a02d00004403010314103481c04a003402020102d003070000d00c00303008010381e0302581c000361001c1e002c05800042240c22990300990564008000c1030200301404207030141000c001100c01e030b40c003111910040b1024821180c000141c48540030001eaa41c175404155448518003075604c00c0084400c0c40342c0d00f001c03210280e5105141c0340d000b00d400e8000c0d8682c040d800201e10b0043d000e82d01840e59402e00d40d001c1e5042801d103100018281c003010700400424020520241144081c5c11445041c0400064410300c500e14182a20001c00320000c0e403c1020f540000d2040d202c402e00501903410b0250f03019031340da83c510b440700b03015010351502c0e0b020000c891440f60f4101d4807560044515880090996192003070301008400c2601844400030549032801d0090146d04840e045803240d8400c41170900504088000c0c002c2020400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 237253965 1250 237252715 237252727
    0x92d0306020708071a39040f0e070504050a090506031c0c0201180b0906130503010f020a0806220c030e070e0412030c080109020a020f0607090915080a080318121806 72
    0xf400601001c6130545038940555105001e2800c040c00c46d05000d01c2c629141000802140103c0010b98180490341d4940f007256645c0c0344c50b1010b95050143d40145c41d0000c200800400c0309400603000340d0340001c009019546400e1030204540c0d804035a000c80c1c200800c03c0d02c1812821544d00c440310614070b06642034144c0c4041e0170004059190302c20314480301d1081901003506203282070815003000041c0001402007005a03030303001c3c040020b50048840c0ba03010034142d8002400d07900384190b040e661804001c1c00004480d0030382d1881300c010002985400c04142e6551840888120200700c540041c00d140c24030461315150529119184140094000301014180001100c4140d000407129054541e01d0b10050707103807400207008030310700080d8401405003803003070005110740150030401e2141a41c04c008018002030041150088005c12103201d554013a50000820501062440001d0742e08001c040361000d252120005120340341803401c081403420b000340000c070f060901001d40514011548140c0d03c4a042c41 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 237255215 1250 237253965 237253981
    0x5040b07091a07030807110313051c0209010329040c08060705190819050f040c081501030204050c1b030c0709051501140c01021b060601092d0306020708071a 69
    0x80a0f8840c000d06010240e00454130700c41c000d43c0560704c040c4500c1c2c21240c65420300f40c00581441401c3c42080d000d0f6010ad1001200d03061601000400349801814a0445920310307171751107203840c0d1030a0302100d240f0100e0900501c4d50810551081c02640903000304002681020207580c00d00c0700103424901071000800240720020712074420000304a80c241440300c0750740c0d20140b01c00c054140b81d10b4850300c014602010010340d4030410800c04d0049002d0408040740980715144199941503403600424400200401000140382a810666224841103040360400407541d80700204d95140b40c0c403400c0c0c50b07003000c01e0840b00e0410810260008202d50b80c0c0c180300302d04000c03070a011000214400d6504001540034075a03091300800c42200c0041801500840d60340182e6142e1003100800c09030b5075401c0380a80f0011449a41c8503000700ca00b1756841c181c40907a5041d46038006001d41c0340c2501c40342e0400c0710709032002020070703000e10182c808030740900e0400345e0b05c1c81c0d203140c4200000c2c04075010018240c5070405200d090 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 237256465 1250 237255215 237255217
    0x3070b10050603190504031806110d02030c15091e03040915031709120d0903031e0807210c050705060702060408030a02070c050d05011d07050105250605040b07091a 72
    0x218413100001c1c50303121070600301c500402c4689003444c008108840000c4040c0d00c004d10007039040205041e81d00b02c11140c94126102c3c4a560099549980001c40340000108100c440b00d410400090071a1440084041100140299104144542c0e040030404110440281c09210010624421500e00b183e0a69884405c1c0510319480340101c0c100c04284115640c6603007032141140b5030414110303000d0b540e0100008219032a03601044001030203941803905969030300b00d182840749541e503e41c840207545a080c122071001c0140912070317104400501d000c501d0803592003040100f000ba6500d959540d841d60420510384407019240c0d1086520800402004c50785045c107981e0800410040907903282882d06100405c1145901f1041c0d2000f5010b512000700b010540c41000304030403038851f808001440c1e00c40280c96200600ca401d0210383d00308200008003070703040111143c0a00320008c1c080301d50b0850307c0354821250204d030115001c03a01401480342090f00005070301c2c010407804000a500200010501ea55 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 237257715 1250 237256465 237256501
    0x30203100203070e130b01030b0406150e0a03170a140306180a02041a0d140c12040c0b18090105060f07170f07050a061103060105121803070b10050603 66
    0x1031107034080040703206180700303004842042400900004180f4001c0c10b8400003000b05106650100c0e16002280f201030410740100012603282e68030040c1c4000801e44103272001d881114005a110551500c080000b41c2442c0717080c4e4003c490400340ca0340701c1c1d80099024001001d44d2445505000d07082c0708106207540c8450800d401100e64258000b0f10b0348904000002038080d036040070720308801c00900c403000b99000e6009406000780c441001d0200312500008c8040251080c0e4013010441802c1208400d00300000042c29001446501130480c05ca0391000c41d001c00c0d4010302d81c003208548600404c03684900d0301882040c098076003100c40703a180c540d105948481d54401c2c41c4000300810381103000d41000c442078805030ec250800ea04c010b20741ea01e5071071802c40d86030a8010341c00c131081031400e0081c1c0c0c2140e03590700075280b00325010386076a8a84801c0000100d00150f00401d55030b1215003038100410407010500213407c11364032501030440c580c140300b000a090915590061030046201b4810400203448000380e000c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 237258965 1250 237257715 237257743
    0x60309190501150501090b03070e04021603032f1608091503041205090303040512010e03120f010909023316050631060603020402040f060f020a0803160e0d0804080610030203 76
    0x98032b13804400c0072a010b4005c0140d084210212210041c0505400d60040002d03aa640c070032880b0b80c45c2144400100b04000320300da042e441c10050140c40b007001d01da800320500e15802030405d541000e809400082c074090610b82c880b461007001005010402c4030400ba0408403131141c1c1005403c0c840b12401207a41e03402944201032094103800c90042d60520290705c0600101504800e42c1e50304c2e4954180b00d0080007041d039400385031012a0000041e050502c3c441c812015900510901061001d400b8401140700024982030051250100c1c1038011100c0d02d00400120000e410841010102410725500301a4002c00200b034402901301c514102d142d4001c8140c0031340001d1481c400c02e100c075900f0094010314482d04000d4006100150100c0d90306c001480a4003203901940d02d000320340c50409000c0780c0703680700c04000606004041c00030a0340c05081c8080c144103130704507180070044040090001480c010006000b5122083c00140034000c1507000d1008a50000740c004402d00e41b14655800b09994400b0300110030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 237260215 1250 237258965 237258977
    0xd03090209131703100320011d030312070e0307051e10170a0b150a0804080d0b1806030c010203191809090302010e0c0a03020d02060309190501150501090b0307 70
    0x2000125540f410340d40e19001000d030348a241c000e0750425100150b001c1a64121450b20038144030242c1c40002001181c0107942e080130810004c00001c010380c6c0d8005907140d0600050102c1d007038103030303440d06000d2207001190784200401c401c1105040c10901e058000da80241206040c80b0074440794006c088402040c280c85245818100072170844010000c400701030204444a014800c2400c15070308000a950300884a51840302031f00000c0da44c0345e110780344410020500c0e141c006008640301e640901142000803d011685212410000d40380f02c00b4004083d00082140090045900b41008491165202070005600d4030700340b0b0011740d0003010003950002c100a90410325440c0b0000c40e075924030080400c50340501002d001490040d01130135143c1384112103841a01d014003540e01d0032003070340011a41c01030180404002141c090002660000300700f20711500c9024044051803090345954641d00e40140b000140d61041000e190150750f02035400941000140c12040c460034641400722030f08802641014 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 237261465 1250 237260215 237260251
    0xa020601090e010b2808060106050c010c08060d030c060612080414120604080901032703020105060108160e0303071707110402091305040c080106170606030d090b0313230d03090209 79
    0x100105c032055801410550041130000079540340c01c00701030010303c0e00150091154448084003110190812220243c0c0450b010303001c00b010a0103605030b0510300e406114045011511209900c019540b024012118008001000c000c062880c01e03451a903e08200c8840d01800711810000c3c0e513075103001d88050485080012105902d80c0258015102d4030304080c8240c0150001200d0440384010080040e0302650815002455940c491040e42c3d1145600107210121b03440e2210301207418100b99829680c0603c010846040805c1010803004541d0841003503840da20001403810800c441c82c48882d080c061350041c48000da055070b0b003542c8000f00e8a509800055a030740c642c00d00b02c07040000341d440303460103520b400000b10708280561540382442e131841c012501701e0f440e820113040e81c03000800741c0c4000041c0103400a001c0c010b2248015604068a0403025102202d50740766085526240d0800c143c1116020000039001d02c410300c00d1000c900d100d030030104040c0b103643d00030039080340c1e00030408414005880a0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 237262715 1250 237261465 237261529
    0xf1709040b0d02101d100c0b07020c01051b0114010b09120a0b01140d0204110c15060904081612020d080703050f040b090a05060f10080706021005070302070501020a020601090e010b 79
    0x101180b0000086c4541c0311030455100c05403031013441100986043d440440000c600354000038811a1904041c4d403400e203001000d03100c03020003007107130601d241055480700c4520001032020b5864078003034a0746500c001d46d00c8156030f04107e48001003030103815150b00002e0070180862405141d42d13044130940300d0700d81e40303114205000405a4180401c0203500c28070b0800310300c0014460001524645007139808440113803113645011241d02c01e0449140f0392001c03018001600054084014060039650310100805550903560b6050707003150000902c1006030711540d01140c125600070f2945800c0b915908003040141040305c8204c0901c03400600c080c08000000300480d002d000d04008a40c4415040010b803421810074441e41c08626030b069410981d48900300101284440001c40c01000f150b0407500104004a104060701c000f0f001d00902100c2415424403c58010400031300061410064941c0a012150704208008089442c1d4107001c0c02168589209070f040343e220040000100700518034402e6000f804160 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 237263965 1250 237262715 237262757
    0x18081b0f060703080a0606050f03190e060109020d0515012c060c03180f0a060c030203070204111209160303080406020f070f0b07050a0c02010503040f1709040b0d0210 73
    0x105881d04540000ba51009160307009010b40d000b400070039024014241d454004036200d02940e03084600c0d0410800c00708012041d9180c400c03803403034262200030031224458a030b0b80e824910260f1102144a80000700d90885c05e0940c800c0581c40174804003000d0036079801078002030211040505c4410b0140f10301d600100c2e4004c00b4002c1403121903004201551f20702e20340662a4807900300e00b0503942c03401034800c48a4668905490050b102060182400400526084045030450b000e20b00a40550000700460405a11140100c2c404030f500c8081c406d603110350344421402d038003400800c520801d130842d01192910a449140d91022603401d0700c0c21121907280c6042180c0203110b003003004580c074080000c66000300091056036040035406103210811507030b200003055600740301d40f260202c0010302c0068040d00542c01000619003140c0110003882e03000c41c182c3d446d140116403034030101c92200004100454a4070b0720b400740c1d44400b43c003a10b03841d0b4010742d0b690104149a06116454040c000004c0080e900d0b070766407070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 237265215 1250 237263965 237263989
    0x901060518030a0f0f061d070314013b03070c0503061b030c0c070906080d080109020f0405100e0a08061f0e06010f0210020a23070b0c180301050c040618081b 69
    0x212a000044028809450b948e503920700c02103500030108440a8241d410620501c0e02c1341e809003100d40f0a00032424080344203003003080c03c3c9101110807446031102c140001c201400f4500d1240d03420320825410b041c201450824014490800001480602d9002d0f03d0a00306617504160b2514201d6101c82203a81c003181081c180d074120801907490034a00080c2e101c0e0020301c0480c28222a00c42000c1c41c2d8990081d0402e078882c2554000072460b00b00810041070030b00e200c1c180c5a42c007a82c50300040a6101c940014100720303240e4071062071031780000c0a01c000094031401911032600a20040303c42c40346811502c0807904802060b444c140a610200501c000c1e00030300c14489030b2440358008654074150080042c041100550751b4001d403036004000d8002100404044818158202e20031207180c1e0f481d5a0080041d6200142409904540b0311ba0f034481600c0c01d000f082e0040e0040e101d650784036810090002d10080154052000440880e07204100d407132000302d0a92800601d031585003850181c1000420441104c00e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 237266465 1250 237265215 237265241
    0x41413080310030f06021b030412110f040524010c03020a141204230a0602061501140a1205071b12050f0d0b031c0203090f0409020901060518030a0f0f06 67
    0x44c0101040205940c001c0020200305800d11803501d101081ca60fa1b0ba002d1802400304110076003201c3c1000c501c4600e40070041440040000d402000200702107803c1d103100b9102d20010291550511003500ea0384910890741680a2802c0854000342d500c1c0295038516802c03000e84160000403030091103500034400c42c0c01d10111054040e0b517580c1d0f5100c002e0300c406514201108a02e907500340c42074440c80d00e480440c04546c15a0700904d00c54888440d940060ba161722a007030706002c20301d100200f03250300715000f41203404c260341c41d103c1c1d00c0445134a942d415140c00500400c104090ba0004800316070480c004070194940006010101074075100c400d9a6034440c1100c01c600d5a0b401082117400100e65030821150080290b00360703075416000350020300d00d400244500c40c0c0907030014481c0e00c803d0b0030b2004070310454400040c80800c54680c190041074030024282c01800000c0c00003d040d40b00d0010001e0b5228104034150010170204855403515204155a01c400070800c941e40840d00042c03100c240c11102031180e031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 237267715 1250 237266465 237266483
    0x19050313141c17031602060f0105010909020a02010e07080705030c0402071205030408090301141603200a030b04020304061d06041e05011b120f1407140708070605010504141308031003 80
    0x20300400c04105c05410b1000061060f000021458020740e031742d0328121001a10340320011402d284e100006900450356000c2151740e10041c540031010b04006000c020640507019000840c2070900741814501d0314901d0f94001ea0040044100040034000c2a11101095180581d10b0361100d03e4115013a04c500a0900e80c1982041d8072600d0403032858041c40e0048648804826000d076000b60140c1c140c840c407d012854110b071054502c0500c0100d10018100c1407058174000580f03c0159000a0480c0c1040c0c405039100f9549807251803894000c030481d24000400003000b071505d45030642e20031690301603000264111000e0520343d601080070940205444171010813405660600c5480010907507055807080803405070510075881020140b902c2160404401503003009103e90f01d90900ba02e182c8204072620b46101e2041104a02061000c40980358480c412400860300c3c2d403400c400c10095460b403141040c00c981400d01070005041c02091a440c426601000b82501d95a450201c1569050b0030b520251103564 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 237268965 1250 237267715 237267721
    0x2a0a03050a020a060212071706031b011403010e010609120c0b07030e101205060d11090601140301090501060314190e0c0303040602150a050412030e19050313141c1703 73
    0x2c0c0300b149941c8104103d2391400d40801504003030700502c520680e502501900804201e5441c041948441c8400f00010b0518041c00700c070410403003099030b1003640803580810002005000c1c65a002c40c6000c018000a10a1140f5080d070703403103210001c00709214021030700354000348074420076000d0110120400300c020300030b100058001d000502054004103111200a1410000400c40d2070b040d10700480d1540c21410300120080f8004c02c0c80410840079008a040c040346800034900302116100440c080d020b000707404140b0b5454954040d00b510001042c08e40e000641504118024001c0240b000940304080e40214500c1e18216250341041c1c1041c00c501e8140c000020b0109a03e038001810902c000740c4641c5280d4a0f5882c024500c04441064030003e140c0900100382d00003d038400d4005042480100040d103030703086860a942c500841902d10101d0b0640c0000c074421200c0c2031480c0c4080f000b0301c1074603000641c1421010005071403070b800040c44642c000030150702500b0711a240d40084d50f0326035020645a5242 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 237270215 1250 237268965 237268987
    0x8030f0603120a0203070317130311100e0d020d0f05090105130911090f0406030c0e090102130e0603100507050901050f04030602131a090f0409030e13022a0a03050a020a0602 76
    0x19020a0b42640451004101c5a2300c229151551034412111109030081402d05139404903000c40d06058203844a00c544400d800d000da00c684160b02c0480c2c00b50303004000301a80c0c400064244400d42030007200b07025800340c03080c40d010341100482c4c000b102c013440e0045d91a042202c00360204c06468022480300c51510a580c044c0d03040200080c0801078040f03c01031054070351101040b0589006000c01001c0100b9600c0800030200c000040c00d130040940000541800c00f140c070503151100041e03004250400b000c1c42403000c05d0a040c00f51400110100b8014022841d185101604500c2a00600c030304000b4006445101240d907441502c0155034003603025580d60340d0340401030a84605900030301981107907180308004a61801c070200c4580c01005000d0013141c0082d4000c01004101e208819424000b901d1142101961051000b40c401c024280d801610750b98600414083c90400c00d00b12420111014008a0942e0001809003400d035454a841607231458900c8040303040c0b145040e00182031030b0020550710401 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 237271465 1250 237270215 237270217
    0x9100e030901020f16090b010504150e09070e090103112704020a050315060d06090209070c050105060d0305160501110d06090507080403170c090303070b040204050f0408030f0603120a0203 82
    0x185000d07400c881d11340480394845a120f449500411044038180315003080043c0b040e8100f0381038800141006400c0941d20450135003002c030001e504100003440d2685104072840c1001200d17800694507e090b034071315250403006c1810b0581c180805800440030140080d180d5442d0b445680981b035030102c056454a0710301c4ca0450b010107054808078421b8843c402c0c041070f20f060004101106490301c4001c50f05545a030780c140080b1881c510000c3c2c030785648401500c07025840703140008d4050342299a03181c1308486a03051803421258041d040d1481400c41d18918004280d100b0207076081b140740300340c030344a40c4181440d0050040841c03207050100354802040a0b0500402a4080ca040300c1a540083c8540e0384c9003c4126100041182c00401140c08110306242c1c4c89004511268070510311640381c0c0c90281c054000034a142c0000908a840800c4102000114100b6001e401d40022800d2840280d500b441c3d81e1300941408001c1964950501d080d00080482d035003040310802e02e500d054015603850395040320003074403 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 237272715 1250 237271465 237271477
    0xe0118090641040b010e040201020c041a0103150f0b03060f0409080304050f120d0e0f0102160c0e13080a091208030124120b06070209100303120506010e0909100e03 72
    0x240400e1460300902c00c1d0441c061040d503100000ba042c1da82003480003003034503030040c00c02d90446c450b44215125685840c1b09901c038050400071425440c1120500050584003c16580c0c401e42c48090390070042d0a600d0800322003511100720649881c0da41d4203011440c20f0907155601c1d64841d05214800d002c0c40f62071002107000c0c81c025004c1d9100e6240c4203040036514071404140a01c0450708100003509041030b40e008004070364603002910141d104180b051826600f100001c04410200ca442c100e042204152542c0002d11141c00454410714100d0b91010309600701601c0980915030024955408034882c50361304010b061038801101c2c0c41043c60074500025003013406110906140110324400512814400102100d55651180403991960340000041d1500785541a00104140700c440700507034503400107c0c8210300c0b500c80c0070416403171810700402924642d074a042130140f0740800e100c06c599100ca01800601001c0e500c10306551160301d690392a100100c0303038005d041c5185c452203400d1040c1c08402050 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 237273965 1250 237272715 237272801
    0x1030b090c2511010c030c05010f050603210f0306030a1208060111010b090703021c05040501091101051c050c070b040308070f090506180a170f0105010e01180906 71
    0xb50b11000c1503640b1940c403401000180025540c4400d0700ca032903204001e0605070034400c1c42d00c11284491650780a0958980148250006403100c00700301203428104449901e10341c044a00d0500400781e024200510701c03030054071900000002000035880e440c104060300050340e11490040159449090040502400759481800201c00c41c01d690400c0005000784a01d2400080c141000303510340910940080d40003000100b2091082101c0d001400e01e148905441103010310000710f828003c0789071014520405d85401414050140200a030aa03034807440700b150b401c840040000d050311144401d403134901645200403c0d19000c0003c2004150b070004945014149544454010041c0040140c4900c107080c01050b80110080c406454044010400c8001401c0b0280c131012401d516911255115040c108813100c1c03541c410311005012600c244660f5004003050000c070351540d41088124014401d80c0f000301505035032039440c032209125072030b4001188280c1c001d10202c4039409000003012884070030781c030b081 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 237275215 1250 237273965 237273997
    0x307030501090915050a06050312090a0b0c0703030e0f04050112021503070f03050a0e150f0906150405040c0b03011404060803070503072004020d021801020d08060f01030b090c 77
    0xe032a1503030f015482c01290b1161300b03030711100103040c0e89000070719004040e00e5085484400c0080c03107490603c0190038100c9041e0040f50740da038000e810b010381c03c8a107601210365464104413414001401081010a40fa818a842d501002d248000119081c007040781c2c080e03006103860000950102041d44c0b040800d032080e40e012124080041e450700c09404111520400306010b00140042940300e0b5001d15404156072800085805140c3c2c45140303011a5110000252410386041c0031a0707901c1c0100059000b2000801041c071460104e2500c07012a401101c2c5038051910b03503000c681007043e50040d40029000d00c03207115480307603520340001456002c070350481d078042e91903c0001300f1542d20110480d00450381044c025413621a080e076965424904440d07290002c00c0f00c00150140c990307101e00041404400340a4050703104d500d20320000030300c00da9203544241035602071001e84190b0381c0c015034655841031048071246884004080140e01070011499110703400f0144804011102c00c803c4054041c0385290501c0d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 237276465 1250 237275215 237275219
    0x806061507121d0409030207050f03030408060a1d19081b0a05031806180f0109080129010f021507030603050f21030c1903020d151e03080f0a030e070801020307030501 73
    0x10000311000c05c280500141c000c14001c2c44607040001c81c00041900180440e0714059564100504084003552606640c5460382d1840b071401804002c4208a100c03280d010f08842c0310244110f090240b4001402404c581d00850007030b0310503410140841071b5a50b007c0a60f121101e00b490034946a900c6480c1001c410140d101801001e410503400707641c0710b00304411403580740743c1940080010701d0348240c803054104000d2000104240d00203020303003e02c8240b1101c80540c0307074000b840d168240c2c84000c10b003a8101302000080d0020980e00040071003001c2c84002c07010289850320761040b00a840c46400c01b801900c9000e440144411001560710b0660390b801d1580c1043d204034841c9402d00303210984104612038018483d42502e03d51258180138241e40c2d40c10014134188002c0c50b03100690f24404548103201030f00d50320403c80e925170b000f22110046418001030882c00c1c01c5a80f014000c1c0a043c0346c2000281020070086100e80c080e03403010072100120002c4542540d603414425010350700840d24400040d00340000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 237277715 1250 237276465 237276469
    0x30f0629120304060c0809150d0e010b090601050703120b03030a0203040e0c0703051803150108030304120807050a1107050d050d0306150e010f090923100806061507121d 74
    0x2550107441e07007980c172030400711081e03107994416030444a4615445403001d201d512074034203054020b00d1007003500d00e00032680c2007402ca800350854122910b1540035010031810400f10740e07400300454050702e516082c0290182c141d5a0100c008083c85c0102d282c041c400020300d5162103400001820840750540480112503450040210703442c0101c0c4801408101c05010100500c215242c02003510b0304007400316050008066030380120b000080e4040c610315003001042c0014003040841190102c0c0113800c2c00905400e0500d4028210b00c00c0714480c00c10042d0804003080ae80c0010b0010078028400281b0b030485100f41e0b810556140c0406002103400300c1d1509600003824883c00c10182c0d512002074507200d02c3c81010100546400241c01c0321182002a200d0b07002c90400d5a500c90030f0b03150340b880c424a01e42d80c0102d6024480c664000742c0038013806500c09078100b1a5a8000401950240c01921180000d141004011003280a000c1004240d0100100c442d5006544550a440321111a2071020300030500941 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 237278965 1250 237277715 237277717
    0x1202091003050607050f121014090106050412050c060a020312180d030e0a021302040504060902030f0c070201020a0b011508070305150f03030708040e0406050906090304030f06291203 80
    0x80002c200d600803600054405008001822a01004104c4d29260000b081c110320030026003140d4000b11741c400720070140101c04403840c5840b0061003c0e1200b00241d414881c0103003c0703001d0b9200340d40303c070702184000c441000f43c180401c0000d10005009942c48180c0070101035120780104888a15048080b070024a00242c120003da1006498001810303105d1032118044000e810030014402c1c0c1846400503100060700d540c25034000744844a034006842e54101001c220039603405a00017001d890040c01481090321581264a410a40540741c1130b41d504124070060f414a60781c4003015000360f48410000685040e204030071140c812140d5900b55841c3c1c1d42c550182c00b20313603042e101c208810308900429811414005100c21440b1401002c49080007400e544113030855015411038001140914184420003071a40075040d0018421400b40890740345c28a407180d9240075910028001044030004d000610065610800709039040440c1f50003881305c9900c201c00402e221085c00d5020700d0b4401800085c03500040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 237280215 1250 237278965 237278969
    0x10f090c081606050307030b012001050f060a032a0f0b030a0f02071e140304060e1002070803030f060402070b0c0318032104140d0210060603090b071b060612020910 72
    0x1c2c8845046440d180c2040f8010230802c200070b414040d0030032000ca01340c40780e0111000962001d42c00401c69142c00c000e01d10304880054412030284522040030300005884040d030f14080c0d160072403402d008100350b250044021036660300012450400c05408a03190403040029449001050782c18006032480aa50000700d110702c11028100d1041030300b426403ca4030052540304414011080e011082d40401400c41c11680030790b0007000880e0b18110b030210181070101d503032051851a80040c0c0f003124a04841c040d00d903c4000c00007051441450001070f250307590356055410300c5810000150403880c0050100300385510545a00242d944005440180c2000001c02c407564800b20a2204603a414841005100d0090140c0111505104032540e1522980c00300100c10a1088550003080105000e0900c50100ca0305500300a082600748030380000460482c0004542041703041c80d0021040d00a01f4070b100c25907030720000c0280a2030070804000f031140380d645000a01c0f07500031260014a0381b6400124004241c2078 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 237281465 1250 237280215 237280217
    0xf080c0403141c111605240c151504110d0b030a060903020d080709080c150c1209150c060c0c070312021005090c010c06020c010f090c081606 62
    0x400080c800128151000c1101c004844126500c00601541504030440c0c003810300000a0652050201c11040c1005848040581078000d800480d0508000c130f161187c18519207982070049a4034058405032010440310412945410ba9003404820078505200304400c0c0e85110495200851862084c83c151181038114001e1050052070041c405d9440c0e805403880c0c0b004541d050050000d00004601c1600075032001038400e5014200480c0f2709c80000d480e42c4000342c42d101c208656484c0c24005003500250005c5804400c80e5a402d00180e003001e601514440d1140100c5180a00a40c02c040cac1c3c0f010307a024251382482120316910316902d0805000f114050040403014642c028008940041900700080107441244802d4030800c41d240c0e08d0b01c0803056424504400160b000d181152044a0203219464029080740040d14071802c4400000340070420801000c0c01a075400035240d0700002d02540310380c44030b040c811403c5c40300980c05c2c188000728180a1040d030b003541c083c01d070b1815902d10300340d82410140e52035 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 237282715 1250 237281465 237281467
    0x408070c052d060f040b0702181012141501060806010203071505101a0a0201050601081e25030905070803030f04030e030304031a0610080709090203190207120f080c 72
    0x448248035082d0200381915900304404100e100621100800140064295216017907a40c0b80d40f48103110314862040029a029440f60050041510305c22751a00112a0726081c645142d501a040520601c0000c06640c1014401d00200603168001d00410904964041e20381022594980c4010ba850740318204006040c2c41890002c8043e2600f5988203d030001154001c4d030b91142d803100c2d42001d2100f51426949010b0301c0105689184585c24014542e202d0f5081ca0000d00b0350a0854850000c1c441c800b001801040088000070950644402800d81c10400c80e030b5109400c5012303910180003090380c0340007510103010380180400e040030000104c9002d1a480c2541c444240d41e01c0e2402c0b0398204d110110958940410400000801c1c00100e103102d0001100f04600031030f007420301c00c21181841c812608400d10202000300118650400320407c01c40790160009641c035070760000110888940110354421041c1301107461400d2103c802011304108082d03442d070104055415406a4464000b10fa500412030340c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 237283965 1250 237282715 237282769
    0x6031603080d0204080109050a120c020f01050703030b0405011d180705060d060b180915010e01110106030b0408071205041404090201230c10020711010309050f060408070c05 76
    0x800410b14840507100050130243c0340c0036040d0a5400241003681c0662120301400c06008240348440d20510351800c10b24030324050782d8080381a0902e0191007505004010940c4801d0600035081213440c080003e1040140e5a100c010085e04850b445003460350403101341c03000612801c902c1000c071480111303d100070029249020f0800605074408610307031883ea91902c200191085c5803602400703010302444052905400440d00340480f03100014886130781c400381681250f40350398000034a100480c40030b1038050040003e030703880d1502421540d80020840d0007400100014055100c01410440d4462043e14481d0589070008660501507405404201a518001008a0300d81a800580e140b031040c1041440304403120501020300d69001c1c0c5100c1c1c003100004204c9984202403001c4849096515000c5080c0300c00394a88030303850f08218540394149550386480b40c0c00e1103805c0000e5010310b080e0508452803854549040e0305150481d00c82140e0700d0741114402320701031a0094a8000d81002011304042602c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 237285215 1250 237283965 237283973
    0xd0510140f010e04410c1302031e0a0605100f0f050a120e060702070506040b040e040809060706020d060e07080a0c1e090305100c0c0b06130f090b06031603 68
    0x100c0003400403078003842007402001d14401c0c114591440340321840703000310209107200c010390180d0160617400340a0382c21181c411059542c544601034407100c030a600050f1a5901c00e014148281507090f44c0e0070f034520002003040040c0300507810110966101303a6801c0c018001444054441d01c80400e11003000c181e0394200c6480c0309100c0c0700903103803a506a2428038022142080c51004540305160204000e03004041040f0f1016010050040207040588405e46000e1070a903928803140954002d2400040c003410204048c8501b800c02d0702d400d00f40050115a540304c892506100039408005240583e83c20940006120300c100c84859110342c0381901c400d25256500c440d90002422151044d10600140700072420316080c07035a2242c00700c0c400d991529402c550840c1030441c608070140000e201001d00b45484411440d80c032603010405150b201007441c605494072000640e0002e2011800c4820600e003c036090303402c04a87d0400510f141c01281903035015200d0741c081c161a9049004c0c00e078100c20130f00900308001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 237286465 1250 237285215 237285239
    0xb0c2205042d0e0a0206071b06080c0a0309080c0105010b07060614010c12090306050c07030228030f0e10030f1401031709010c1e14280602090d0510140f01 68
    0x8039180800307070340c803144c1e095000528503081024143e0361102901035020f09001c032034031440b02a0207181800315203481c00e018001c4041c89500040f000700364480100e1010001c010b8140c1d14210702c0c2ca0000c1c451980c50b40f00a06141c0c06c20740d0181c03410350820ba000190707800c0792038003040200c03410394800c14044a561a01e40e926244031820b003003049001c460005c0810b826220355405080e104000703036035030703012820000d1034680451117803c03451920000d002d012414a0f50340000035940750815102140317040c4070aa88040c0c49a11141d00401001080c1c0c940c00d40c513900c0b41a045410190420917800f2545405000c00c4090100408070304002c07681c102040d583c58050b0000f020145090585230780242c1d62590112007440142c4150302417000b40000f00846e84441d401c01d0b481e80e10062400344540d6446003030700026031040d60192920140101c041c4040c81d011140c40300c80140100f0124425458440e5950074a80c3c00030345024a40418420400900c9079024042c220000c0e003031409034204808100b035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 237287715 1250 237286465 237286481
    0x507020d060906020a0f0e090f0627060a090903170a09020a0b0306240d020304060e0d021614011403090106030b0a15050d0f0b0c2205042d 61
    0x448440c420032400014018018038032040e00c21a000768580034402c0c0060120400d00c140b240910600c0583c1032215100c9083c1c0950100380403a44d844141c46010100c1d5485500c442e24190300039000e03e51010105078800240d004104c180c0380c0a030210f55135400181289c9081500038005008910960030702c01913440001c0d00305045000c001508010b56002481428841e40070807541c0300c1c003000b0080307149840400f00b00b6107540c0b881510103052074500700158901c141d039094407590ba4003001007810b01c803140c1e0201d502a805841250800c4001e01000783d40e60551f80071594000c1d4104c072012410824060300c42220b450180c4400c0140e014136581c00035a82c00007003040c41c95650f00d0b01c002000c55a20030f80103004007011000014056085654044a445e280c1c11142c020311104190038001907010550f01361340b5401c0781010505460304800b242042c810345e45140668003c14000c01c21382c007001c0f81d0880890310203c034100b240102d484440d904101c90449150481c843c0650100340c07404041e000000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 237288965 1250 237287715 237287719
    0x6080f0a090201140a02071404020a0206040f1a0408070501050a020c10090215070818060306010e01030b0103150f0603060e0606190212070c060305061e010c0812090105060913020108040201050702 86
    0x401131600354160b041c15000001c443c001130344170781d104201450451001c2d010500c0107035010362419007500d0010b5920311018000410000300c04c1c2103c02440200f00c80c9144580b800c44100265080c02d00f88880640c0103503600799a90b52030800403801c07400340340c1308882d040213190000c2e094034507800e02644000c007108030041e038102007800d242104818001005210395417041d885903481e4509218111000c501c06100c190061804109001041c2c1c2c2092040b081c0700800d00e03000c902c003c0240012405070001c0d180c0040307001142480030803c40742c3c0d00500720540e0401da508201c0240c2e60500032403200000c1e00d0041d0000342c10084c07040e900c00c0998000301d0810090049880040358410644a85c1e800040103603080c0758490700c240805540b5004450300000300300e484580445180c200b400ac88800b580b002818809404031440400c005c107020350700c28004620303c1030300e6494000d0906d406404100d645510842091001030040c40300c40c403410141503010ba4544001d641c50b6401503071541d00602080c1d03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 237290215 1250 237288965 237288977
    0x7140411030106030c020f060f0c0f160506160306030f0308181b090a0b01200a1b1d0405060103170705010e010e061509130f052506080f0a090201 64
    0x300d00c80540402140204420380d00012900c06500e00203007011076003014120160010000d020010305141500b80c0c100100c0345400360364820301804400240705042001c40c803c01c5002c205810300030081581d03845800302805c107c5280d010000102c040764070030700000708850154044038002c6803269035501da0007000c82d40c214401c07130200764096140c010011803485800b40c9200841d00c0e00e040000906402124080b028820040c03000001703012103540c0c42080f00000d03500e00200c0c40d5014200000c2d40580e1b0045880c00c400410207444002c011002c0c055941140240300d41d41181d400c0d42201da900c200e41202c05085241d086030f845a5901210350506240e2030000c0c05a0404030304284101e8005032903600000503024135284c017550500c01e005040c450740300303a502d0101105850307180e00300d40e10030420554540c00d070342c6514084074120381081780500603228a240c1203d150740104606043c40450400462941d40c0c0d6440490303c0f010b049481c0c1c030301c000144020a00c903611540003001c0c1c440c8141044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 237291465 1250 237290215 237290231
    0xe0709180c0e070917070612020406050a0e0303091e0a140d1209031713050a0b0a03020304020a03060e0f061501050a0e0f10050a030510080705010c0c05180603010509010905071404 79
    0x807017a012818000c40416404c5204104201d035004010407181e00a031940950406e031078500003a00a00494001c0ea0521865100209050750188110380c0c0d1014028407c111f061001c0c000340140e01c9a10521038018600030300040303101c6210803107010030705a0040050030050409d5654a10000c0241344610500100d04004000500c100041c2c1c0741740145904000c1c0c079401507000c0c5d002400300d650b2180b401240340b10740900c0150041d0702160a20b5140e4180035940c3c1d00c0c3d900c0480c10080c10b603400a0901440d1686480c040200425030014141c030b040304643c855202c940c00044110350700701d00180419801c02243c1e04a50182c107181c0140403005140c110b420141d00c020401c40d10484a0010000300005070310b0604507058802d55401c4000d55084100050031b00400b20358400c001e0041c1d038107120340601101c08006400c101440170301409444000040d40c40d01d10140070342000c1c1c1e241351081d42400005140548140b143c103c410360054010b0210501c4c10100590b8030000d050300c1900203480d2048 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 237292715 1250 237291465 237291479
    0x3030c080f030c0a02060f060604090207031e030e060f06090402090402010c0204091514010f1a040b041401030515100f0302221415040608070e040e0709180c0e0709 72
    0x1440c8190507500700c040e44c82c014060000e0034850010040240c00d01e5000c02d11180f5190442030b90140d8048440c010384e141d40c00d01742900c1070902000640142140c1000301c0c040207034107406c401c00e041b500c3c01c00c5401c10b0321144600c201d024412200150071a1190000038003515107600d10540150040c10020b8a00310140c0200d41a60a014000d4401510044081030180114420020003250401e640d02c190750622005210074200752003407a20407080150710a10380e042e090308880c020210441d0017942c0c0c51360ba5901801c0c2040706104180172a180500165107071100f41c50305000d045000f4440000f03905101800d540c0c001d25202500c08159090124800c6803100b4078401180c0c0f0f00754880001d1242c50f1044803060014658940e031b0280c040b00e00d80303640c4250201c0981303054907124100441d891b643c6e088125800d2414400a5170b00c1070500d070700d4001416010452005650120005100706603001d5032191841030101001000040e90308400c111182c00140d001e80c2100c80ea14004a9859a03420 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 237293965 1250 237292715 237292717
    0x115080330040b0f07050a080c071a040f1203050402030d141312020310020901020a1101020c280605040605070f0c030b0108100b030601140f01091e03110603010f03030c080f 76
    0x2c04070b0314991600c0501c07424280d05490345911400a15010345400960000240000300c040c0030840000c5d0003103680e400300b01e40706071845a480039040e00c2c1021860a410040c2010f44804000c0d00c1c031145202d1582d050074828090140304d16005001460340411480c001c03144003411400700c1140b02002d00a6500302113911820740018102001c0c1407603980310740c1c0109410262122114004140704000e108080c1c5d170040350a40880303410076188e100840007800140c1c20308c50480c0030283e0001206425039111015072507005c2c42d03e42408200101d040d190602503486208601032040031500500080001500302d503080401c092280d40c000d8103107036803552000e1102c0b80c280c210407031310380024942c024068250310440d841340c1004c40c010000307945004408103005044003851800344860748006802640641100310042810409020070191007074440341b240c03881f5000c21210908103007410070580ca80142500d041c0c2c8e820315040000280b80da074080d178140c091701008880c0040300780407080d48840a41c3c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 237295215 1250 237293965 237293971
    0x313050708011a1f0e06071e03030204030b090c1302090f041518090b0a050a090506010806100501090e010504180f0b010f051c06020306011101110a020115080330 71
    0x1a01d1104120300040070810900c90000840f0510400900c0700c0c04d0741c40e48212008045213054038511380d1044242000042c0070070b15800840703007110648000e001c0640c0750b40188101c0e070090900401e41d854500440c0d885002c2d4841d09a0300030a0b0302c1412040e031555500902c00510700410042c01801060041401d60f146a00c2901440046a4040155020b80b4005003080d180340e032000c120340f404a0303948034400c080213015504a5541c52000544004440d88900d1103c0c4d04202211415a9660130181d641d40c011254000c4824144000003002e50145094405541e11031a134201da683c280340c1400000c0c20784400032070202000e12600c2c0c0c0070440f100007000045e4018149c5113104e6051408c005042521a40110b0042600706106100c40c0d16481c40d8280c61640400c026a603600e51100403070b281c008003090342d07905501e0000e2401801e03000c40024102625140c0091104042c25000760700d0307a400d079215401181d041009100c400c0c4071560b2644c0840c01081c130103414180c1098500b03403183e040031 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 237296465 1250 237295215 237295241
    0x19110a05130516090317030403030906091b0915090b01020705061b010516020c04090311010606030e1c0c03050f1306020a1704060c0b060427030e0a0b031305070801 72
    0x10002d200000003d41c080fa404810320303041c0710a06902c0c541c1d40d942074400008180348500350200201d03003050701c41d8104068182d00940103110706141d5082000d0001d003851915020309218803000568042c09000d1000d03010b00d90803402d640f0710f10340641080035240c0c995240c1c2c1180034000c00403030786640300c001914000e0002e050030001c0c1c1c003400403144e085940c041d14034074140300a03100d0100010307030005a1004d5948260350110b090780c070600d003d03100900d042d11918869400d00e000407034a07030b40c1944516000c401040403101544001692001d0b035600185031000028581c0c440000840e01030030061203240e42941c40c00e441e08207164010002c010170b617084040160024880c4009015100d42c40c43c1d0040791107075800e4034141c1751407800341c401e1460807002014042c910001402caa50b0b40d9020a0740c0c88040702d001c44c0b103c116419000680085440d0807004280c601110f80389508003480510191982d07500514070b0350319030722064026950421801c80c1c1501c28401c2c0480c07a81000c0c000c2c81400c0300c2e4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 237297715 1250 237296465 237296471
    0xf0302030309010e03090d0318090c0f031104050f1512010312110601180905010905010504050304061206150e040f1a0406090b06030403050f0c070605030103120219110a0513 76
    0x405090340c04d541c101412421560b005000c1c603d010354072022021403075641410400102c0c1c03480c0d116040386144950000c585507150201140b0002e4000c0c0100c51203803220381c0c080140a05034240c0001074011801400d800803081016190030342410301002a20f5111004954140000c010b80c40905e0b0307000340c100300d860055110140101e1500124010961541c0a010f01000d40c14160b4040d540070300d041241410a480740c03d0380c003c1c0b00080d8851003005d034202000b0b1115152a0a25a960703034410f210300c1000de101d460050706003440501c100030544100b4955201c0a0848440841d4100000800d90303a2260b034410328031403008078900c11104200b2910f516400c1d009401d0080000300c803845d07802100001e040c080c45060b03940e681e074100d0b64071681c54100940c4600340724407016410b0141c0b20b1203e10602c0b506802050740340e04140510304807031156003035004142d20301404030b8580c0401c00303a040c0c9106251030040000b07500c042c0040b401c140c2c054040000241c0d9000045e11000f4041c55003004c49039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 237298965 1250 237297715 237297721
    0x41a0702150a15091802010e0f0a091505060a090302011409030f0c0f030703020109120503040314010641120d180503150c0a02030f0f0d29090408070f03020303 70
    0x31842c28900d005000b220300401c117a03a0b5195000485205c00349009040141014a0781025914000c1c022141c441c05001100030603101d0b0340304d00050424240000300000000c5001515107050b07400c0b20820b40c810355812000700e195034015111a40001c1300480f1101c4188004003198800f048052056141640140160b04118090040d50640724845c2400f0b600540c00901c00b50341c015040c0c81c01c80d084030303c2d0034840319000d08049055000d00e8000600929202454050b9107105400c0306050711003544448140341200e00200c05140f00c019000700d050700c141300c08a0072902c03071161408810344016286202102900c09510308104608a03520013091194488050721500c01101c40c001d0442500102540c00350481050205400100030844079140025001d007001d1003441178880c900000ca000603102d08081d4a00c0c1015040610544d24141c40d2012a0b050002c0e05007108888501d106450351900c010b203410302c080d11b00020820341d40c02004106100006002c818412240d40c001d07400703151641 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 237300215 1250 237298965 237298991
    0x306140a0606030e030414030c090403080403110312010b0a0201060b2109010c080c030a06050d1104240504180f0b090f0309030d08090f0709050a06060503041a0702150a 74
    0x221240c00160800d1300e0702010100d80c000000440b01601d0100e80340d50080391138030001031710b85440c3e41449600001480d090204158015104602543c801e4a55240c16841840d001b560390050072400100c180b1202c1c010400f0002000c01899844d4203840017092041d2200240107040d80032842d03a00240c100c0c920600c0107081d4810f102a0041204002403200803500c200080042c040070b00f500510080c0000441d003503a031039902100041402420b910343d01c41990912503204040380c1080c0e801141040440000000000d298102d4823030341340c00c0c0014a80c2040c0a1000030484502180d12217040e00c2448000f2407400c56003814440d20842c407540f5903141801e0441c0c00c150303444410440b1039100348401c0f0195500421982a5140e481c58202407680d83c0c0c145c01890a54908140001030085140129200e41395410641c890050032170280a0070f5641c0e003044400d40700440e8007a0044e01d0540c0c01d4440c110340c0b540340c982c01840030300c100c46c01c0107000e4040794010700302039540c04d0300c240d99001106420 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 237301465 1250 237300215 237300221
    0x100507091503020906120606040305060c04090c08040b011e0b030906100611060a09062304030e0a0503030d0203070513060c0b0610300e2a030a1403040306140a 70
    0x711a05203010360402c10110003182d0107006400001c41d00400d10b400291840d01d032002990002d6030003408841c2c1d00d080801c2904400c0d8401e010f4104114100000000780d540103500a50286900000c450010303840c0c861018a0810300c903281c40a820700004000440381c080d940a1401f89d012030016000500f0100c500d03400c1e007015603000c1c109002510fa03080c0c040000205913141d00030441c2c1808241c500303551404800038420080241169500c402200c10140010034000780308901c25140c1a02240720101088082c031a948141b82d49a0f10401004090341c090380c01a50b042920743c00d0040c281284911602481c000e95080680041d032850011400d000c034404081c0c0d0094000d6a4075000341ca2032031401440d120005e49504149603900c1c4010740400340690300d0308160581c4013010000d0a520b15003994807401d62401c031a11010603841c1042d001c01e041d0a0708030a00c01c0c020000c003001c9030300d40e441018440c50080d902e5101c0c042030000201150300c50245016000f03041200c0c103c03070b11300481c0060403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 237302715 1250 237301465 237301499
    0x11040c02010e16030c0603180605011401030e0c0607140304030f081306030203010f0302011b060510081c0c030804060b061c0f111c02040b211312030e10050709 70
    0x860a088401080800c000800300403d0701d0003850041000c850710b04402310801d00179400245000e00c2c207000020080e00d4014440b81411090b078082c48180e03416038a183d43c1e100155103140d4018801c110360400141038100c140c0000440700152404d0135584d03292117180030580042a900d440c0b000840b429103003405034a0304003600280c203046081d5410a41e040c001d20f2203e001c000d042c070041c42000744515038941690050a503121200b4082d80c640042e605d4000d40b4036204150341392142c11142e400e080301b1010740300e05811385941e4000e4400031039101103a0a000240043d0354041d540c900311520350329814010a00051151815400b031801c0c0d23110142100c2c03060304640c85140c94460501d440a200c10200c0d44007082d171401e00b185540030b00400740002c1c40303140d01045911100184004c1c0c032888542d00b4941b50295180510902c0d80d80d15952102c003040d085005103250307601c1c11403001583c0280e01a81000400504640880ae100700014086171401c1d680140401d084240c1086185000c83d45030103 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 237303965 1250 237302715 237302743
    0x30c0e0106080903070c060f051b01060f0801050906060f0d050a0f0308091c0f050d0504060c020c15120c04080f0c0901150804080f0903070e06100318020d11040c02010e 74
    0x868015186c88090a820880c000c0c0002c02003130420350741e05188148251098103d42c020f6005030048480c0405009041500c80c0600c0001802e4001482d0700e810710610380300d00003800c058000790351100100a103696107000e000341e000440403101c0012503010010210a1440b0314101d110800e0076080c0a081d0501c014600d4a5039442800100c8180c0030440400f4100c860500f4441d001e01d918601c1074440307018185000c06c44a2a001c100014000c0640000821071b07003540035038a00710180424011030030340e400c060201c0e10604005911500d400003016940c41103da0b2091420191942a13940c00c2c80341d0354140c20950780c8441da81c445107240600308a40142041c5001d10b08514443d40085c0100c400140046c9c4290808240246481585011921110401004e5511030381c0c96031219172182c40c060360a02d0096440380c44800c1824001c0c454000c5440b500415807400344a00d0307081054000d00c56074100c0d020b02c10b0341c07800701c03554a6030b000b01112100c42c1d80010920100c140032507840c244e0410510b40c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 237305215 1250 237303965 237303967
    0x307180305031603110f0303100608070804031805040c030209040c03020a0f08090f060c190305010605180f1509031b101404030b010b18030c0303031f030c0e0106080903 74
    0x30001e5000011104550810369214240079a5400d0039140d041030422031030702ca4003621010008000002c0011441340125216103210503880d040203d6082c0300c11245400492580c0000c03c1c042405058180c0d4490b000340ca49510603078a910200c0c00755a000d00701c3c8001319070041840704e128a0103005010300642035140860071310b41c40c90700081000312020b800d1402d002e180b03008122000014400318007540700c03143c12120a0305003c3d413811125405146125410310001d592441e0961007401040c2c101c481540e00e0350300700000ca4031201800d601040d003056003c0b908403800d005903240d2030054695801040041703500c07000e107070041c1418507071034080c1e004042e0108484888103a41d00e1032290405009803506c90000750002c0000c501c9481141c1000d4682c0c00180000a4003210040081240000c64000c40c4501500711003415a62020301e1a207942c10740042c400983c22107a194444545602c52400707001c5210b6582d00c40c0c421a4800d03400c14a807840718400140a1140c200504941242c1d4a400031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 237306465 1250 237305215 237305219
    0x10f0309050c061e0301080a031b111e1302090a050405040b0a020703230a092c06060d11070515040809010302161b060206060102010204180e010603051002030718 71
    0x658451500000795441410042400010702030b452808080b41c10513414019a00e50310303100a030350b03141001c58007103000900480e10b50b0700310084040e001c0a4141d00140020000030781c0300030402009001201d110042142c2460380009640703000e0460300d2a0480031005903174000c0d5030240021341d1060340045010340d04000902c40024600c1000b141c6c000450f02005071160b5881c0fa007184c0c5e4401c11050f503070b4554081d48042d400000310800070032021076107440f05c03461141d8802d0240c4085060030121048820fa124449a0b6040d04450781940554010842440c00e503000395400203c844407080e040116001003911010860208070010701204a1040c2c0320003807415a40d51130b003e00c40c43d884c4504040c1c010174141c00140b00419445245603110a417400c86480c07045011a4424241c410f030030040c8100c1e00401d16550040c42114180c071644249150701c07005105181e0090b04c80300404000070341d602d800c0000440c1c024004105a425001c4d00542e99080c030490003845920b0301d00004a000300c5034281 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 237307715 1250 237306465 237306473
    0x1031d030313060e06011d0f06100e030f0f010603050105070302070c090b0301020403060906021c1a0906030f030403030f08150a060318050f010903170721090804060e010f0309 77
    0xa0380c2c2e0145110100752500035140c58403c1c0036004461540303400b4402d98001280d00110720010300380c3c201501400030256618040e10030781828042e6849030308200c101a10f042004e104501c0f10428400c0a81100d140c102c40280042c5800360304111100710741d54687c014401c10000f0700130180c21854618042d410200281c51300078402c0014032800c0441690361051b5030744c0c0c0d2403e4060750300070760b0071210400c101c00090600d4006980b00032410140488540d0603015009000c0c80390181e00c10307a08000300003080641051040050010305425030500c161016044144410401400907500c25580d9090900c10075002800600000e0312180c3c0080c464000d00540b911900c40c546e00301d030000c0c507000c00c41c0f103484c2d40244510201d00c04090600e004851f1900c10000e0150081c60280b4480c1d0b03503001403641a11300d440d04601003130392003800060022a00741180c00f10340d900314690900381c240015030380a407507440c07071003a600650040012845900c20604c0c2580c1049003440004102c0c101402084080d41d9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 237308965 1250 237307715 237307717
    0x20d02010605040e1e010f021b06060904031e0908250e010608040602030a021303030809070b1303020f0310020706050618070909180204090b04020f030a0b1b09090f010501031d03 78
    0x281d45c0303c880d071007001c5001e466100750041448000c1c07d48045640e1074115081c403031008107200d0300c15142d1050314081526824081481c5215641596a01220402425040710f14001c1d192a101c100201c814010031507240038801e19502c448101c40d1048150070740048100b0100695000c554010b8001c80100000b54000f60f40583c095800b40e001070b6a50b4030300210714002d0098441c854041010754002104141d000303854140242c032100d0803034401c9507607040c1511584c8280400300b41011084101000142400346241008040c01026180c0e800010203802040340c01409060b100e07142c4800c18002c290030002207121010048245210706440e2829015001e084203208415060303075104813980c00c0c1c684041c558034146500900c140703c07080740d034142009201c0050798241d120707209041e8076108510380010404010350b4803c42004055442803100c50300c580004143c80d640301c00030080300c07800c1e80c1d401c4402441100c88654490444d41004001011140a400480040503a000c203804140308000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 237310215 1250 237308965 237308983
    0xb180c0909100b12060a06170c030a0807020303040b031006030606050315010804080d060e060906100f0e0a18090308070504120b0907030605090a03020d0206010506040501030b1906020d02010605040e 87
    0xd0b4003003680e00746000400c001c0300e041800c0e204540601014802080d8003a04850100c0303200c1d0034034403040040310000035181c0c2a90313075145902d98051080b8000080424024000c4c140c001004d490500303a40c4c5502d0b400791707401107480c80d464007101041400311540511500020b810341d8a002d03030030743c5030180041861508201002c5d040c00340f2900040c0401c0384100860788032140d00c1e102802241d039140702e0100c045c2810364485210f0384851001070000d0a10b005a450903864a40d12410300740301001c0195902d01004510700d800214503000403903003240312040000007074100031002515080505004222180103024502003000801082102e01c1c003c410154030603070060009016600e40700e08141c907099840d80000c001c1414201000b800c01000300c0c5c030f004424041c0c0c00351a0f14501048040b03072034900900840c1c2d07000005100c284250f52080d0302400d108003016000e900d900c80196031480c404e07205070b4030290040c3d02c18503400f070388c0b59820700030800285070903a01801003458604071107407113034942 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 237311465 1250 237310215 237310243
    0xf0f110705300d0b060c100b0f210c04090b0604200301050f06090907081008010c1d03030903100f0f11030a05071b080912030a0207210b180c0909 64
    0xc43d10110400782c6a001c06100c040041c10560344070741100700b4940b07030041440800b03001407a01949100030b0804100b80030390000300030b01c0742070103407150716806070640030580d041240b84c4120008410705403520b1007113101260245006002c00c0c501402040141c03204801005000b98031a2421066124040c0969064480890301c0517038040b00f000204244d40505614283e0040c400814000184d0300498441c0c0501518400f6100c5251510581030036030340c911841e10b0000304c50001e1080030b03102c01c1c14242d01c80c003402000e0300e162043c18000a071401c1701c0302401d601665690441c101c2007900511031a05603101514080c00307200c01d1041951640d020041c100741d0410780b2207000803151840f0b100e03007150780600002a6203040c3c03401e007050700894001411260240d440b002ea02c0000300701c00015500f444090741d004140c5c0380d0405c6031502c0104003082007911350900704000c0304000340d006203240d40305403100c0d0f0a002c003035000450103d1500c2d640206860044002506004010002082c00340c481144 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 237312715 1250 237311465 237311467
    0x706111306140f040b09040e0a030203180d0501020c0f0708010b130b0d0803040c05030c010509100c02130f020d1103130807020a15020604060e120405040f0f11070530 73
    0xd54400b01c403a446581403440b40c020f40018040740e0030b81068003820494a046d9000c10050a074880000da170365408407009000341e44248150440300e00744900b00223441e02d02030200b082c40345160792040d0a80c2c024007500100340d000f603405110b00c50410081c0d800104000390080c07040ca0550070204a80c403c403081c120700c9081c5c032000720301125255515020007843c4e00c0303200c659491401d81001c2100007168041e45220340200c03151329007250711480c00e8a03400d400c0200b00c070303104010008042e50400318602040f6006403691a15044401c80c9210ba27824070181141c015039640444101e00c0c08a49040358500e50150091003402118101040b01003c102e0f8051551503a8205c5800055010405ca600c0111708841c2d9910f0004016404190a405036110320802d114548a100e1002d4844020310b502c503411200c2031000308814500750300406210b13480c0b0000019000b2802410b502910709400b4201e100391070024085040050812105001d201286240c2d4145c54142104a2814504490410000130 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 237313965 1250 237312715 237312737
    0xe0c060d150b0a021f05151c0615080f0105010f0b0307051210051c15020d0b0d051515010e120102090d03080108010c09080c270406020706111306 64
    0x31030715180740e0151818104064840070000740c029600c00c2a044084d03042c9071090110038070001c0394010a40943c1e4038008519400d0525414040f4955a02c03050380c0001c148560104040b0700540b29080d6403903c001502c04445060104461030819002d08a641c16803420300108144010009a0019100310302c8016560743c0f00c2d242c08461034000d00072162a4103c042c02031050a885510103207040b00c005540c004600e135541d24182c51948a80b850181c110100740c611030841d402c03564010940c459008000040704030103440854035070b41ca800d404869a07848000081c606691081c0c6140e800301b02c88041c80b595130540b0000804a20710310005a01900c803280e00c1409100c800e40507210741071000b80880040d843d59040040c0311250a1090078219480c020580a10600c50041013003034a0aa1006104146502041c05403c6622403030100b511022a8100c01e1040c0b04d0074a01c5000f1401001e016071100c0c142d0400c2c5003145c0f085070020421034410401c20702054482c0c1c0c0c1c07120403261a8107201340241c07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 237315215 1250 237313965 237313991
    0xf0c0403060501060315050303070b06060f070503040b03011406190804020a03050313060906050f1e07081c061d06010809330c0304020a03110102010f020a02010f0e0c060d 75
    0x201803504024106030421001103150707a4194401d2180c0390280b440d0442c0c546d41c030030625440e485503540241610006200051080c00c000300145403446184014a02d001b04603101ca60540c0c2054101500590000004004004001694a6000d0b104450107880e015010103004200d40e088800ca80a0108410000d800d42d51040c03006030055802000f5203a9800242c0600740b008880750191101190354542c01081180c4241c00740c0e80d514006141c06860a1444000e043c26402d070030681c45e800c0e28082058a0004e03940001038400460900c09641622440c09080004c0d0740090f0401e154003c48031000c00b00c82c2841c103940d02c0e017000f0300b0b0030103404070b84418403180e0825000c060b004d071100e0510700d01043c803110502c07070b4400c5000040c0c822011589840d0140000c0d848180c40180d4800285c0c08203002040c48000040014079050000050030100c0d090688166049680740b83c1c0507035034608102d001d1114502640b400003001e071010b4094150942c000031420702603040c41700a04d6a41e680b1f025005 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 237316465 1250 237315215 237315217
    0xa0803030121020d1406090d0f0e03010605180109050c070803041e140a0507091107031d03240f041e020d170a0215060604030201050304060f0f0213050105070b0f0c 72
    0x841e0040c04e0b240c80700c4142d0600c4114001040c20358031440c401e41c40002c0c010318010610307841245466445031140040d0410848011050041e1991b040d566130000050907920840f03615a01204031594621643c9010551800c454004104080c240b00c200a0100001c503030700200ea9120f41e103d0485c00042c01c0c1c01c0356040003140c0080c801440f440c1c0d4506c0800840c00001600e0010a03c980c08442e0020744a10381070341030311312071085151201014804100028051681c0750000c0c03002030306042c141084a40000c0c0361610b42045451840e000d110f8603c130b0046607a064030340c0072040c0c80381c0200700d040964920303040400d450390030020194690311580465840d0b00080110780e801c200610400c401c0201118015400502040054424a440d110010031020700760351040000070b0000c5d0800d4a19001510980e00090040700c03080e507a6402d501141d4118031545c1c10101081800503158034a102203504020704a0f04654180542407000d0350001d6140d00c5020303031002d503600c500395890301c51140455035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 237317715 1250 237316465 237316529
    0x13030210200304080c01030b0d030f020a0b070804140a050d030b040b0d150501080d0203040b03040c0e130c21201e01090f030201080a0c09080a0311010b0a08030301 72
    0x58200c8807202010300d600300001900c1030b00c07000825603011510703400040d000c43d180c26140c180c00001410010001c64082e0002e071b200346400380196a030440d25680c8404c040a01101c212021500030024801407058580d8008900314660008050b85681c41c0ca807203a40d03407442d01c0424101515402e494203035449941100ca8588005844910340010500e807600c1581c040400c0519210314003c0001805140066890400800768000c0d510340717800d22a00c0fa64543c030081c0141c802064035071000941c140d61109142c07041040c3c80005044a459242298045599030f11070002004842c7d206802030610010410703071198465000410b90720104090080c1400c124101075018540711002d0030000440b28202c1c50194090341e40e06c2c0903617110040b82d90402c540d4000680065021000070f04051547d6024688024550400100065986615500d000d4808004500181401e45822202882405000c0f07900d80100d460500081c1005001962030005100b0010038019607110485d07200d0414642d009 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 237318965 1250 237317715 237317747
    0x2060709150e100e060c011a0604030b0a050c090901120c1520010b03060103080304060609050c070b070c02030715080a1a061303060f0501170604051b1302031e01060513030210 77
    0x10b141d46c4a07000080c002d1501150007041c428044003141c050b86001c4e411941541d6000c01c07003c0d103585030009610000c2c4801400310141c2c1d2010001050180e541e4000c1c1c6009021045480f641d000c1c5910300090402e12a078001c80700c260345107505c0c415441d0041d40120b02c1003034160100903e48030010106014200404035150503010b4540040240054080194070480c01a002032101684c3c0c2c602c1401158021500c4031071010041c0140310005482850700ca410451519001d080f00207207400003410001c40340c0c8071003031368000b580340d03051600d0700840230590000036101c040214041403000c81d1100032982202502c1058000b070b5884c031051079004118042c5400500820030008400b1441004080a004004250f030100c04000340b6000c1c00110300c0c0c800d903405400342c90a0305a5024004501d851481e0345544002003a91001203003c0078409907208904565020b103c0c0900004807401c80c48043e00044204441007080007e106050b80c1c5e40801c884d81520300303d0340c0008406c401c80d52410440f040034 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 237320215 1250 237318965 237318967
    0xe0a0c0b0c2a100c050307030311070506010605030612060103080a230f0409050a021318060b220806280f09050705030118050606090a0b1002060709150e100e06 70
    0xc0c0101440c0d0b4000d010405540f030081c01c5880460584034664100e6000707040d94030030803007840001d109401000c20080b03161540c034104603040d07840a007400070036000316002441c0270081155524200903200c4080c40e243c0007500301541552110a41d5101c2c0525140c24800c2c2810110f500f05c203070303c4901c2812002802d1880c0c9608104403c1c003542d500600c100003007142040003180003000d8510859000940c020900d03542d0718907080842c80c0c1040f001e82c0e14480396507103440004458011b54002c2c8055161409188503031981c05505821a0078180c20800711540b1140422100e00000c80018080c441d44190101c505c1c601d4030408070180c0390801d41d1421960803d4400c00c1005000150a004d58a0803002480b652600c1d50040c0c22040f030000380545150300c00b01c007081403801c010000d50b0b00a4102c0300c022a2034103005000c2480c0c0509584a0310041c0e02003820881910750060b440e0010340000e1440703d603030030001c0700000d040e0700700000028400c10540b803c41d04058019101c02c01d503100081c02c51 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 237321465 1250 237320215 237320263
    0x2040c0e0d1a0c03060d02040905120d020c0706020708030711041104030b0711010c02030405091b2107030504023106080c1e01081b0921010e0a0c0b0c 66
    0x70018182d642c08201a06180364000c81c00040420003a01c0c03103800c0c058945a11010140c0822000d00800c8005640c14003480e65006204200b00009140c0060071210143c0d4414000072040c3c80c1c41d2840d40300a045401000050203001400b0048400954001c081d07840592001e800160080c41c61001c0c418030201c0003d40002001540009507201d2000b81d2507228800c0401207815007039130038032a403480058100b04000d0101e45004604590007403540507402050306124055450150f02c5184500180169613440404110a071000580e00004e030745002d0010742001c1d4081018200700810011080b403c1000500441e400d807102c28925005c120f0301808034990310a0555181d81514040380c1c0540031240c40e603c24150b841642c20700c01941070359038680c0c940d07410803500d4600c403000003000350a442c1045071400781e50b106120400d4190210049800c912101908613084400141141110341c214401400c0402e540701c06603003c4500340d002540e9601614040c003030904116000c0e843c4090811222 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 237322715 1250 237321465 237321473
    0x8070303120c020610180e07030305120a0207020a0b0d020c0d030c03060608090304060503100317090a0608160f050f03090106060e031204050d0204060306050f19020708040302040c0e0d 81
    0x7011409a030241070400c030003034881d00204e880303010855001203500d41d0000e08104c190102220300b04011041d10000480d11002c00b002414808030341d109500042c80840c00614125480c44140e81001440f1011843c0280590105485401d14420601745110109010741c408a054040b54a200420410b450829580c240007030010807000c0b00e610000f034070b03151300401e4050082940c01d0249192034000e5081900e407901c01c89080d88001c01010403002402800030020702c40081c40c00c081c018510044d91113107903030000c1c0201816281d03c0b050400c00c1c2d000500c0900d01030707501000601441d6240000b0440c11100040e1001c1c415030362413445080d8000200007200c5010352082c015109960340c0c9540c41054081056914040000052100c9004000030803032440e113803c2c920946440548007186460340c0c0e44502c1c08586c4101c6042c0c07800740003041000280b20b80c0b21504902035610324800c50500704141c0342c00046000d40d001c002e014680c0e0b0f0a00c071441038002e4014030f10a44000702200201103481c54 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 237323965 1250 237322715 237322727
    0x50f011a21040308010305070f05090c1e0a050406085a0a050f0903040e04050c0405010806090d050a02100b0d0b01060f020c010206240111100605150c030f0c0708070303 74
    0xc021f88180c000e17040c000c11104444440c01c0c0440300014009101c07525032a4078010250b0285d086030f140d0105100740d03911040c00d004013524034402e160300d4450b152807501e030000d03100080042600700c5403050013803415038414403244000861b194145000c1340085010540840e21520800c40481c042410b0041d06003400035241c0c464851326100780d0500658983c0310034000d1101c400c0d6244a4039800c180700901084100b800f015034011b0145e07089808506070f52011408a580a170460500c41c0c01010810805100070401d0741180031203407814600c0c1c00079004000713489046003071800340e0664480401040582e41c001d80c0e40710194104840c5904c1c0d5948440c080c2000d1101c04596008d4055020221015800031603028854181c140721140000c049210814004221518080c1480018511107510f40c004000342914000c0190340020250304040c20850351400d04450050070b15000c02042c0f144c03884c003009031005400140b607010789840010940900f440840d802600785449030ba1800014954400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 237325215 1250 237323965 237323969
    0x91611010216031403040f0f0501020403020414072616031b030207170408060f0915010602060105030c030625050409110301140f0d0209060f0306011404050f011a2104030801 76
    0xc0c8030540000f0108a9609490204a801401036841030250101041100c20030100c02340c07013030000515154403940010100c40007400c1e002800003503c0200300790180c01c0300348224608600c0c44c509140c45880c03070282d891078a00500d0744060200d5520300080d072a020303030047c0c403c2d40c0400030158029400210010b0003901311800c161103a500000080c940da0b01c03c1c60480b401d07030320280045d059035a1402c0702c2c0701c1d0160300a0308000c1e1910600c040280490420413a00740a040d85a010341510f525000c02c1620b00110703025078a00c250130100500107110b04001e100480f0740e184260004d00316200c0002600d690140d40d005608103410a624030347c4c480c25040013103040e03400b503290800311440c841c0240281e0504540000c0d4201404141d070502600d0314074009079200800801d00c0b420215100c000c2402d0000c01e85c0080000301c4c48650300885468140543c0d40c0c000c11002480701707030b03605d0b15840014000142003d44007001d00010f00c4400525003a00c00b0801c000d501c07242100c2070130035150080c05034100b4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 237326465 1250 237325215 237325217
    0x30a060b0102012d051008030a08101806050a1a0702090402010c050d021f060e0f040206090d080702030d2607120e16080c28050409050a03030e010b09161101021603 72
    0x80000c6e4003164890030207001d03160040011401c1c01d141141c15070b030148018050b0004502007440005100d680d0000159643c3c60390140030601929101c14811642400c0e08120340088501402000d580c0c81c030320580e03010640441d180025070300c40c0c0c001643c056007600d50141440c02812494a440c0fa00081c14801d14000c0d0b803c102c0520700c13150b07400d004031001030150214510500d0302140c45280c034400c0007a000340c001005a80f40800410000d540548640b50403a0301c0718012070740e001035246c14400e00320440c4050814581c0c07462002c44c000400e40340c0d02d103c281e05c030a406001c900000d203d111402840c0c00c9c1c0800410000e220030104a6a610072003545042900740b8220109141002182403444040b014002d04090011200d54010072031a10508584076a005030001400b0703035403400351022b21405030001c1c113000343c03450400500f0340d84801c0c2404800d030304055461a494682c600b000d13500c102d00188100608aa1040803209054141943e0b90150300209034000d180c01c0d440070205510740300b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 237327715 1250 237326465 237326471
    0x70308100e040c090f11040f03021c020904080a120204031109130302030d0c0203070b04030f1b02060403171207090f08010b060315030708010f0209130b030a060b0102012d 75
    0x203600d401c1c1c031030070381c0490b801450707250085030400c0b58000681103800411600c0102060307020340c240b42408603400c260301c03048841c0c105500801c10b5003407080920603092035120032480c17504c2458000c0b40303103030501400082c950840024490b00403403041003401030308070304002e056540c2c82d44c0341400d10f080d0148600c02ca200306061004660351230302c1c50420483c0c00780c0c141c014604000038500410000d0031030001210560004000c5070000400900382d40b0700c214425103e070b00c2d0515528000400300c28052102c40303840c02520210310b000d42d681030180c41c100c80c2d2102072010814180d41001006018242d10204da040c0081c0030b2108275504400d0300707000d55650700e0305c0c07207000380d40c40b0112400c0c1d03407040b884180c220130b00304086441c144000800c00c2c0048400780882d08551f6075107900900b100da180c01c81007900c0c0c3d8040359206075072401d41c48400d510442e58906212540510303002980391440f00c10000e00c815075980280545034002c0d0000f00300f900a1005074840c1301c01c20500c91030705080320240414000e10b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 237328965 1250 237327715 237327719
    0x20f0103020a0801230909010f05070c08030402040c09080319030b0f150708040b190905040501150c210e040606080403021015261b010e15040b07030810 67
    0x11181c420341d114054555034184080e440d0007004480e21200c0d80010103040f51641c3d0f140c01d19207411072240d00648650f000003689520f000e8102c000c07120080c0c02d4204000e03402c1071000101c0da66400780d80d00260104e07000101441c00b100103942600d0075034005905030100ac00c801c03496201803415800c44c1e07100358406002d13205000c0204100300d40d0111501b41d001090044810b80f2030401c0700585007552244100c2441d16886185040c40da0f04024070305808400c5503900c0c0c1410710341c03005d2160004c24003038030248060350401102440348941150b200c41080300c0007078241c040c040645d807414508a41e0700c2c100c014084510000811000308001070602803030030801b0025689200345007003840303160503502400da41c5801d0b500d60070192040000c6441d10508450740030849580002d007144074440740e002d1040b0402c41a0b4029410140d04040402150040070720404a503608080e0650303071040d00b100c035264a1a611070b102007043c0510381164140e4100425104101038018100a0195031031000c04001c9503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 237330215 1250 237328965 237328967
    0xa26060306250806030309060c0a15090b070c020114131d09030304030f0210050c19020f120d061805010812040810091406070203041a0c0d0e060d0204080703020f01 72
    0x2401c551040740a40030010300c0b10640744500c0302c59801c040028180d0b85400d2080d0b0000d04282c000d0b01e404410341e0401c40d556800c00c542046d03000c030203214281050080e0800c81c0c1740e003800c0c003200404003001d0004c1d0360700c200c0c11603201d03038240d10484002d110502c1c2c0369000e01391800348020040c0105007000c540c02e41303c030a12740001c404441c491100c13580110301e569981e0354210303420301ea10800581540b05070900b0401e0303007650340500e0744580d105900d41da4884a144030032a0341302e8544040f50085d13420100272002313510303c00702c0c0740c16801d404540c100c1e94500c0803d2045005080651000314404003001400d816501382e0740015048030031503403c0711115403a1443c0000948a80d21509810f81d120000d46038007a0301c203420442803503004204010a07186444c41c401d080c10401c89100005810000b002d000c10485200e9552920800d41c1140e130a01600d00907203540c0d07541842901052000180e4980103540e00e02d41260300c51600c0d20401e5480715503c8452550f904c0150000b20711034030031600481615 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 237331465 1250 237330215 237330241
    0x14191107140a0306020f0d05010305030901082d0705070c0b0c0c0603070807120b030109030c050d0c030e12030c0a03022a06121b070308150f13020a26060306 69
    0x701002818038035010718550f80c1100940c08059481155803090000040600282c030130540294000c401542d51520b07c1e00c0014001c0c3e000510702d051403851050304500309044010f110044c81220911005142c840b02c2d8185c1c0c4038000c4420040c005181c3c4007000c1071108850000d01005010b4604480101d00c0d200204203240c0030869001d0000340b040300c0007030700840c424500544455101e0400264460545020a01703441f42d810007a0042400c1152420421204000d2240b0000c0f040c500081020803594008160110003442c03148202d0615041000c11841481100c07135090320001207614055192401a44450494074044846113203a144c10420b4400540100740410b002441603150106140f40b44070981800703000b25003128075034441d408696141c00d0003088414045d4a801c1030790f140100d0340700030700d140c1c00c1035107070103110007000700320040c2c130343d408900c5c400040702001607110150010103c550f410f019003407603039004144564054486031000054040c3d10290300352902035440794008402 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 237332715 1250 237331465 237331499
    0x50a0b0a080c0322230105060307051207080f06340c030903050607180801020918180a03030f0b04050903040605070309050a090b030f06070c020114191107 68
    0x100e84590006400c018414000b150b0284c95040c120008081c900d40e0f80c045280240401c9440c60b41d814000030407007210241c2ea0b4010000e0f10000c0c041840c04401203912100c0610419002e03c6c0e0324003642003076101c18072290f0301401d009000c94036001c280d00c49880c2d07922415510200c5400a08000400030500c02110960b0503400c580710050007040c15800f181d00070907504050b0100000d104022000900074025180601c5040c0d88201140950414800541545a02c02c070a2684100310003030702601c44a5245600c0395420504c44000d54881c034000d030b455040a40400a94040c450030ba10801d5019404648502c1c0025001c00c50b1001010500c4200c0b5000d503507412140e07005010800529224100801c2054440d1800c0100c00b86d40c2e101041201180d80c001d031b680d040c1c6540c00b00150342000c0003450002c2e00024020490707424080c07006005582c0590004c0d040140f9525a030380185103c504031210f91580300c403802464102e000c802030140006203a1107041d4096464001100d00000841e001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 237333965 1250 237332715 237332717
    0x17030a050601181406090402070c0602010c120510120c080a0302031207081b0f040810140903130506130506070f0b090304061707140a0905040f020c0c0d061d07050a0b0a 74
    0x440c00c07802c0c0c0d0400209806c050700681c1c0c415000c01603840080ca07200740500081081ba00046050052030b0000341c500c0302d43c4074425442078503203010082510b10ba201035108031a080002d01900485a042410007042c490300a2038443c812242d00c401003580c000010300601c54640d03961800303034840c65812520680c0c00d956000c1c401481e00340e98448100280000c20001850306480b518141c0d60b61180340c1465403541c4004c80c81565009012010704058140541c80540c01e000395241803081020f0300c070b54890900519014602c0882d4240c2034503101d4852601803c1c0c02410a0b40325181e070b1074020303120002039900b180d04507440008240581000030584090780d03215103500c00c0c03110003e00584040c1e00c00624900400c0352108126092000140041042c2e069503910b8551050902e4240010361301d8400d160b0545510400540c144c040340441c42c0111810103d994140246050419201829201c4c00e07803111000300288220b84108000b40e1903045400175240014040d41d102915641d44c0a440740c020 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 237335215 1250 237333965 237333989
    0x207080306100509040c0c020406080c0d2009010b0714060118050a1103011d09031c0513061b030e01050903030103021903050a120e03010905030d0917030a05060118 72
    0x1e40e68680385204041d4141a40b60860600b14182c0005050300d4008025402141040c000501981898000d40014040c00c1008041c01644000400c042002c2c0c031002505401000c00c1100682c40d42101002c14210700038061071465845400c410000d41c04034804840c004019120f4070840400030410904840d03243d010a41d403420b00c00d6640340070301002003400c80c0055541c500c3d6015043c0e8000a140601006030510310f08031264007481c0341120001d8031040983e801800b013502d080308c11281c4421880e520020100301511400481d0980c49491400100a0b50415210411189200307484035107060403075506101882c0030441280c01c8840c291540405904100018405410701410180b0041141d980103003110399039440d940d05100360032200f204c43d24a543d040a00c80b80e4404049541980118001c120424290b07540e156a4800c50351341040e40394031080010184400e12086407800c00c44005007035582d02e07000300818004d240444402d0301207640412100007002d400040082600c55a90842d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 237336465 1250 237335215 237335221
    0x31a07020c100e0d0c0b07080a0207120b040303021c05150a06030b090115020f15150603061f0e030f07050424030602090409060f0605090117190305070b010e0f060402070803 76
    0x111040c503c82c00c3d13080e038070320080c000c0028112190400403c4414002d030503154483c00d80800c000d00b407582580c032400c158006c8403808000306144022880d04103605003401607840760001c55606054144805900c00b0600d0300781001004001c00006071010001190841c54207034035070100780e0466860156158025420300014003819521124802e90712985004990740c0865034068903240c0380c0302942c45c600140712981441000b03481c030230411000510450300141180b50030070208880021030b4031981000e4508c04c0fa1030356140d018030800c829400b400380540d00100840000180c3e11034407803207010b000b41c5c035154a20039480d44103444a880d1000605a020000346143c55080180d04107004031948295100e8030000021094810343c5103064502001140b00c03403411082112a0005034420140c0300030b40d94504803000800316403000036501c601c40c004101d000034181100d541c00b4002c1c3c0145518030780070000c074680c1c00820300075101e0a00041c9000c041e644100500007640140417004000ba0741c18404 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 237337715 1250 237336465 237336469
    0x110301050d08041503020919030515100803040303020f10060308070311120403060f1d0c011d03030705060907060302040509060f01121803080c040608040209040606031a07020c100e 79
    0x29462450b0142c070b00542019210f103108031042c0c1003c0d155002180e8001010b500c941082210b102000a050701c01c09002440c0d5110f068940303420005a00d10081c405001414503101c802e440c00c0501003a10880380c03910389914000e903440c0040c0310031209070303c1240720020801219004103020399038000c18a5041408981e400d8500b0b17074401c03920403440d005042102196101040141000f9030013094089410811701081c0c1c030880307002d03140d400030400109801014070b907030000d50500400d40c20710f420712074049007040584980c10700e400299498000007031240188500002c036030f80208402010368100d6036584805500320301c21440345503000904940020103920f00342d66115524141818482c0040709014441c1046990b10640c0e400482581c4440b8414107500480ea550b202c0d5052603c2032070141481c034003808031721000304000e10520004000404100258012100555004023030150070003042c42c0800402008550440042c410b0000d100c40500e05090401050201768035503642c15242601 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 237338965 1250 237337715 237337729
    0x7180e0105160c1202070803031005010e10321306200d0806040b030a05030a030612050c04050c0f0412030e19090213031b05040501080a05030f090120060a05070311030105 75
    0x2132141075005048000511400502c0103512a0050340d01c5869928207200016190116240c1c01320702565460310a00001500503800444515202d00c26225007150481d4400b00050607410360079800001040c1c10f10051070148000302907820300c2e16002c4042c400e02110700c5030307010720103410038566015540d1000083d000b2030f1026007110001d0000308510202c400401e24001401200321169070002440c44030180d4180305410181c1100c0030001288000c0c0c1d140d0742d076689805000244280d5550003c9002c0400d036404450102d183e10840300d4403241d84e041009207901d14410241c0101b4840010007819180134400c0000c1812640900ca00d650708004c00c0a0080d0130805a10990a54074140440400c81d0301d01410301e428500080c00c12002d0411052105950041c0e000e08080d501c4000a580094008404c0c0d90b40281010790f82d40d100c98010b4012942c0c200b00e805c030580200c041c01001c102240000c80c103d032003014010024001c0341c850080c104c0455405100881400b1400d000600c064500b1078 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 237340215 1250 237338965 237338993
    0x903070b180f0a0825050307030206040b0c0316051f0e21090a08010203160e06040b0a0c020628110d140c030c0303070f02070b0d02070507180e0105160c 67
    0x181c603c0038529107030300e0510718040034505001e10b11401c02d1031000c00211302c0e21455015040513800f810400d803444c0c1c00f180740c0b40600c0c0281ca8054102044034000d0100800c142d40d41e01ca162070b1081d644510305c2c01c1840d25001d000035005000c11080229180c40c0300f250003042441000f0703030002c0c00c2c001208100041d0074403001200401110341000001342c0c903030303130f0449009c0640004400182d803403e0034010014880f261012103001d001c011501d10701260350b00010340301143c05495031550f90304503921007210104840b00000750701a10104004000481160703a12144001e071000780c1c0c1d250400c4040955102d06440304002b102c4d4132583c03032461f0080c400c60400007100d0301d00141c0c43c1403d40030000e40c1e003103801c011200d003450390001c030030850b2043c0e10200c454207149541c005030034468181034000255128500f8141c261a40015690007000800c00003a801032420041d0492444080018030014200c40c2e2183c0300d003903080c540852400c41070000040c802c41d101d034076005c1403901d0590340c40000f00854 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 237341465 1250 237340215 237340219
    0x20a0c0306230702010e06150a0303140708211506090616120c050d08010e012102040c050d0f060f150c0c0602060601090b12041e080706020903070b180f 67
    0x5000c4003650b03460518407450003104941c00100c0c03410103c00c14170345004002842e40b41e110703041080203010750302e038000d440055075094031300445022801e0440306018442c00d0320060041c3d10000324050a07000c0240038213908800d102c440740c4030351202040720900700511b00155922100c100000003042c584000180b0036194058000580524191504004040d01600c800007040d03910102d0000c00c00244081c49055482d03050014a43d4100070079400c071000b05001d080304140803121101c907014146034000801950040c0107201d2800403e030001d10580080d00e50407030050411180c068400c0640c0540d0f415250060f4913100c00c90f24010348440043c084881d0502400b1520a0100c042403c2485060207042e46030020405400c0680004011040540c040c908041c000d00c2103d25a01c0301c144215001604054034511525001a41d00c20901008d50001c0401c0c0d40010704004006035a009070841410403001e84041c1c1e65100c4201c8054410007009a8144c14030100b400c1441c580524641162000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 237342715 1250 237341465 237341501
    0xc07050121060b070308011e210807230c0607020904060b1005070308180a0b040503040b0c0106051806150d140f0603010b0a06140705100c0903050607020a0c0306 71
    0xc1c142801d01200c0054101180c2284006800030070301d9007000586006151143c4004c0104996058440b0b81c08098020107143c1c0302c100860542140796440c215080301d8011400b01e9640c0801c1c030300340c2e401c08852055250403100411a1165030240820313203103034190313001e80402e01d00702c8035034200480c0c080014002c80303d4a41e00c111121082d00e0f403400d0700040302ca00b07441e6160744622508014000d08001003d80450b495003c0400e625214080351006503951f20445481c2551181d107805401c4d4044d60304000407251001c134100c0440501500172400311501030396142260101c2c01c0c0c124a031180c0071500b00f40c002405203908005c03020801c00515854aa103000013501118019078000c01c00c4090b68003001c015014010b112041c5000e00c0350035074800701103813031190b4903282520140c840c4031030010f55400c000c40481c6541c2030202c1030101c00b403c2c40042c20f0070420003803400c5000d00510034501095503548140400510854000a109840daa411141200000e89159140809403441d040207140b0318031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 237343965 1250 237342715 237342767
    0x1005030d110a0f05060406060b07320d031a040e0c06160203030f030a1b021b04020403050708060403090602030408071802070b0c1b03041202010804020d080705060117030c070501 78
    0x80c643c800c25035244520003900190500c2d041c244151900f42d0080c0c0c00400301044080001410034824040749003800c41d99040781000d0180781030360010b011800320124000c40d880340d4040c541c950300580c040e50a0a8003100751101da10248000c6404001803d0382a0303000c8110f03c201441c00c0c038050100c511141061544900d41a4046411600310040c19494240048280300b0741c01034500451500e58010840210040715500c4000d50701d21039008103150b00e00e408601d50949458940440e030145400c201281c0751aa80c80004036514403080718294009203071202c020074590b10100c1110100e0f00368200510b6000e003001910030b0000071311458078400395420054080021380c0165164494680b040c54140c44e142d00700c201c03031100d46211400e06840d400c1000280480e0080d03680740034100c0d40a19007102d4550f10f41c800b04010360301e2900302030040d11022503120f040003000210f05050340d820300c500d4944802180700840d43c0740650750130881c0c41d0f00810800d020f154861007020090940c44448295191 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 237345215 1250 237343965 237343973
    0x6080c070c150306060c0506010b0318010513140312010302010810180c02120423031603140c010804020d140115031a060607020a090f0605090a0f051005030d110a 71
    0x20309980b0603000511a506a460301d203800d4030910340249aa0708280c00004c00e50340c1c1d866110340c414002c516402a010010030002c6c205507a001b08070400e000000c00c410b05001c4c80165a010b0100030494280c0c440d0922412100030103c2a5009000800f41e4408540d0031070b801035030b80d44001020001402854180050049204001101e0304a0320410020f0700c0402100002d003441280f0510f11070b5090204401c0244d002da0001e01d5030041d603400300440b24541d031304000a041c440c0c10135260f2058480c50b040402480307449801001c1030100b5000326904120701400641d03080204807006540580c034640e002c80440c0c07030b1980070350b2409600383c00016806440000100801840e420903107154084480c083c020104100d00c0b6a0400c0381101d80c10704004d050fa00090b113411043c007030406807603200d80d5034030f5050340e075904000301814004154688a25080940e94020700300020940c41e003d04181c0410440e40b0307000e01c034905545001d005450100c844a4041e203580c46078192110741e03885485000000300d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 237346465 1250 237345215 237345233
    0x21030201020720010e031f0213080d12050907051c06060e0106020f0f0c030a03110703080301141906020322050303070311070b0c0c120102070609060b1e0a06080c07 72
    0x2810200c0000f0403229902d000040144081070800c40c001ea214000c0c09030108003500c024100d07035041d4040941d030307210080c02110030950503500c889050302c20008000c0c15142c01a5030081071381c032206800c00c80c6a89500e0f00a54522030b601c2005d40000d881180c240d641c3c0b0705680a10b42050080c640401c00981e905490040311009031700c003c0042e003003005440c11340c2c6028080702000c0d075061001400143c5a020002c1c0d00d03030542c4400241030080221400a02860500403d0b000b075400000c01c80d12584d580180051a00f244891240316074001c0c414200f41c40c42c40382ca010291415079000758245000c850000d0b106501d03440b660301191100c4803002500e41d404100a0401d180b00c3da071094001d00000c6009813030407040741c120070040345080c402206d6440c40080c0c5a614400121034181082e032030018040e00a200f0340c000501410b080c08550f50600006030840c440184060750032140c40e07640d840c540e403200a0700b01511135011729407c500f081014414a0f18541002011078106d10300001e9903245102 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 237347715 1250 237346465 237346493
    0x3030e1e011d1b0a0b040b0901030c0201180209130b15040b0d030e060d021b0c0907030903080606091215040c0b090105031906050301230c04210302010207 68
    0x1000d54204450808000c0c05400ca200809050319840080803014064490380340c001c40c42109000b110000340c1513501c0008a100801460140607929501c40c060390134542c0c0303c400f0190100c0c2c00c2c401c4504e50700b03105100300c2e9600c2c1c1401504840e6900207078200050706201903d070b002051054810500030403202103242d8001c02c40b1048120381203840c4003d10003600c80c0e50815034407800b030505603100070039040703040c0d1804084220743c00c6d0f1382d80e0300b0210044020301415591850700a540c0200d02e0310300c400043d2201402d03800b11034610b950340ea119411000d0700c1c4510340040c0020b0780b0700302103045410306001030000200001c00c41e1050909107414540b80102da00c040c8032581a200c010301052041d8a01038101410601001c14901001140068040c2c44060315080154040402c01f4103410125882030303024200042c000c0c44250011007247e140c030701000d03080304241c1d03142a001c10050102d0008507030440d0315040c0b10034000e00d07504d548240c0d096002c04c415030544d5001c1083c00001000010300e0b01c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 237348965 1250 237347715 237347743
    0x150f0e0411120a0e07060801060e01021c080912040b1803030d051009050c070807020d0203010605060c01060614130b0a020102040b070f120c080414010c0501050907051c020a030201030903030e 84
    0x525107454032250381520349201031318113150895801032025a60001c00d860564071503007048030440f015080103d160100402000d01e0400c501c03514264043e80c003400460180040e081100c0c1805a461301c01111131043e8401c40f091000c0411546071003001180d1900c41680004042d2418451752420b0710065031811107140c103102d075100c002400f101c982c03407150a4000d43c001c5505400e211072981d800320a0301c40c44101a01c0744c5500d2142204540d0250400005443d01808a039111014942c10700d018001c41c1c000d600110b103041070f0001014a101e07042c1c4040b039441c41c5c0700b040910700c2c1080d00d500c2c60b808000d64000310b540030400850509900c1c0000d04e0018807030481c0e605848900c0c1003000501754460384010030400403d00e030b01c2c082003810080d40e06a88401c65246e074004507090058801c0c0100507401480d41d402d000410880c0400070032104229002030b5080c4500040061100000c2c2c1080356000398040c444101c01d00165103e40c0c84a0310700e9100f810000b0b440d400d04441186400e03041c2c48251 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 237350215 1250 237348965 237348997
    0x1090614120f160e0604180207150203090c010305060306060420030403050403060b03010c170a0e06040f020f0603091203060109091b0210060b09060306030118030305040b01150f0e0411 81
    0x8034440b034400305402c040300121315103d00c114019000080f00c81c031462203a0594804088041c030105540d95040703031481c95002180320504251074501c0c01c06500210b500840f0b030301500074180322950003401003e01c0f17844000c02400c1240da1b1602040005c0681d000c060f04020a03040b410603607148054011400f0768080d848894445103580744c2241518184003040d40641d040c03880751100180c21850500000c034441172240e0080d0346012a520041001007405500c41c4107460a110a1240e4007440030074481c026255000040c4070303c02401003520040d141d0090a0b8803000c101c00002c0300c060082e581101d01490202000c1e669058100140c1d0b4084e0b0480b1071071030100a40000047e010440d2041c040740c02c800501a540c60303e06100001d02400a186000303500000c00206103540a5100e0150f09016003640c1200d035416040040085c03a040301d080f108401050b001050002940c001c04006080c103580700d040d00d0414290464003c6041c1c041d4540094550305c0044000c441e580c0a8101081a040c2d81 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 237351465 1250 237350215 237350221
    0x4080607020a1514040f031206032102070303020618011b030e0607080c0d02070f080c030a17060a06030e0a020619030f062103140304060203070806030c01090614120f 73
    0x1d01c1c252440d070070910700c0540c50300d00e07803203400000c0050b541d0b4007a400641c4a4904221030600342d801d560326152344030b26203103001c5001c002c00c101050300d0809080041205c0039080c148150599840742640409400340e4484c0002500e9114900d000a00e4a0001c800100e01e000304005c1d044501c1560400401c0801d0311028809540c0d007041004592003045807828040314242009140746504c42c1c2000202c040790001900418050394101f0036148940c0b0817000c41e9208230000c2010740f00d41020380c843c0c00048189103c4210f038440c07810100d005220041c05c400d925071500205400802120170340d0402c0b8021041d0305005a074442006c1c000c00041d912404580d54540c400080841e1500a200f040702c5107089014448108004150203c5004a00d440304407030069007800c1e2942c0c034004102c1000c29900004200810402c0d4001d50700401d025103409803e61035034010544c440b000340341d035180001d0801c0410843d0310311410031002c03015180c154542c07070a00039030143d1040d4001154402088401e903824 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 237352715 1250 237351465 237351473
    0x215220b06030c01080f0a02250c0609080304030b010b0c19110a170a110604030c0f0509060d02030a030815040e070303080903040806010510050c0109050606010815031002030c04080607020a 83
    0x90300d0440f54091814141c5441c140100c0078000002800204080780e010501c08503150392201c02085005060400e20902651481c10002c0310341d0324012100052032041002400080003c140d6003602da0107442c0d0b892503820000c030640640c001c010240c13403500c284200b25219000d07946446801901036603815880c7c5000001744141001c660b0b20480e8100c5003400101c0840703a021402007011130b44800d01541010401000602600840c1c102400c070135144070001403401403071000a4211801950000700e00c1ea118400c1245248500e1000794154111a4a030000a48100d94040c2d0000544810070071440d0f001c8003140888004004455150340005414000e05400c01c0007a40c3c0910301c0700c0150b141c14100101503881c1c1d001886007078041c500103031001040364050015661460803001c02006007000c0c6050030340c0c0d25201038500c0f50100c0c1c02500411051611000b04481440300a0002c04280003c108148000e41c8001c0850900030810311000c42c0c104014000c06000c2c6401e079005010b048101c1c10 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 237353965 1250 237352715 237352723
    0x4060c12230105010c020d11040b060c070306050601260603030d1406040b06281209050c0907090605041806120b150108060109030b0406060e012303030a0215220b0603 73
    0x10113414400080030f01e200581d03030b19200842c0103502c01c041d032440030f040d1000b1038094188100001c5e805600401c1340703201e0200005821701103d0242405000a0722540c00540e01c08904102180b039150b4056800101d04088060060b0072000250840b071621a2483e50842241c1d0150103c400790541801484840e203014000d1100c0b07428100c401601c2c154001501e0748000c0c1450300c0445000180b100c4588401c7d0003441804007150b0f0600040c01540e603149016900c07150160710051107107652801069820340316240754010b0fa0324a0715028074040c2880d040c1e01c06a848032140f040f200762214408500040e5049500c104544600d4041d1084c1c00c14078103107115101111086810019000108110340c1c3e400303c6004105d9030480a00d8816440794104140980f20750b070421803804108200000740d500b6508201d180003040c00102a568160305c00802d80c4a2242000c070310300581c4091581d0800107a1070b81f505800c281040446e98171811503020990040e64546020307a181c0c5203650802c0700504080c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 237355215 1250 237353965 237353969
    0x620030f071101050a020c0705100e1512040b0402030d090302090114060409020a050c0601090b060301060509210f240622050703020405010905031501090e0a05070b040302040c1704060c122301 84
    0x2184220311103071440c401040c01d0079070f85c0783c141705400030349100032000401303021a1037031440388080c1500d618081c149030302200301c180c5049005e44210075084400610680d11201980c1d40100b861140da46010612000842d4506001e944144108000564485c40b440206081e001e681c0b226519884440c5581c4d0501005030f1000d51070500b01902c00300346507561022241902d074181842d0791503400800c00b107104a02c4401d4001100340c41541c01054000c1c001900100003900801100c0648009403480b06400051080100b0f2100d0008089441c0f4030703001d400030030343c641801640c9598521080e6400d0981c3d00640e000130210fa4001014017041d6404480350014241c181c008043c01c6a6004030801600414460f00c1680c6507650b404550042c414407440140300c0d041011142015100d02c1301d503450768424070040307100d54a0300a09900550045911555200247d030154081e9511511340a01500c3e0919203002001000c1904200c40703401407180c0108000f100726144100c01c80100306103100d000c1a = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 237356465 1250 237355215 237355219
    0x4030f1205030c0f1e070507080706020c0a05151207050405030c040b06070f0c0b0a021b0414040f1505090f010c11070b090a0e130620030f071101050a020c0705 70
    0x200b0030403a80c04007400855849488100304543d880c4110380044502c00070b00c000c0b2080b0310600060302814070000081c1002962105000d40314201c1c1c1d03030641a65a400c03068205c5401089440f0304100d01d20b41181c041c0480a001b2200c2c0340b410b60001980641d00600700d420001185011600707204504003086007034144c4000351000c0116891443c0043c11034083c01030003c001d440a503001c80f04025910817458002c1042a62041d1542c54005000e521036010004090344102d0001c150511850319001d0340c070f19445003194074a000d440d41c0c0c072103410f03c0c0d81c03441003610050b1564420007050811403107038078414003e00010313003240354a00f00f62a095407001258601003040e0305400c402c00b0f80300441c006080380c080f800015907402d40300010903407161007030f400b64880d5513a4a080084202070202203c0c00b86104a1040000300114400000d02a0032700035180c80240040c0001140b40b401c5c2e0302d0a5411030070750b01b4007807101c0b002c64403128203440d0308950f1852410b801040c90100c51000b042898040c000c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 237357715 1250 237356465 237356467
    0x512030c2206051911010608010207060510051f11060f180706080105040b010311121807080604140309100905180c0a05090d0506041a0708070806061e04030f1205 71
    0x14204000b440b9002d21003265018105075982c2107144d60242030513210001d1160000e1002580d1207003141d001350050340d4140c039101e0070b020000b02601104600e103029180004c100c10f500c071223490300c890301030151100c0d03080a1040d02c00c0d201d1311844080003500e105000c11807110400c3d10b464410703c0c130032103c600c80d0301e4407a031300c804024020703140c03c003c0d028196102a10700052045100d0012000740c8124240358462842c001141801c0c02c00300c4007803130311400410313045000c142c00c0309509a80d600035911400c400f0b07400042c00703d00010f201d111142d04800e00c11017128184604280015039034601c0d00c20b15800f249000800701300c2030400c1900c0a00038500600c40c5031091800e1012818a48281007001c000c00c50000342d680700740c0c0c0e078002c880300d5500d40260894200746030524201ca028031442c41d0084410303071950001440d0701d1061074101c0c42a0025500c004254039200103010701e5402c200107001c1200d9072011649003032614000a00f00840c054162010443c48034148800314404442100b810818 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 237358965 1250 237357715 237357719
    0x406050f0904060c090902040b090909151302060403120306031209050108010302090403020a1a06011206122d0302010504020f090405060115210c020709051506070512030c22 76
    0x148265446038040d0f080680450600a101d6084800890513044402036501c0410041251640c030409003821002c2a24021825150400810382c1ca00c040c0400782c1c0520360400006140c0d550300d03c001c1494500c05807100342071944943e2480e000140303200004c400295610310070002e1000690441c201c051860803c0d2a455042000003084e40f4814000a40500d4603000071504040c0300b000780300045500301208a4036201c4500401341c1902041c0c0d411400030302c1e03003500e0318104a842d118403001c80e41111b180000c110280e03a81e5504150380380711182c0c7d6000000707010318402d910804258950a1096000191510300b42c410001c1a1801d54002030045c00e030f0307408000c00120000341540c19035a032101c402080d0180708800b202c941c5080519001400301503403c040e4007072041e4100744580303541a020340e2220394845000e0003c41fa0b0499000e0b02c01c680c098581c6001e03007041801441c155004c1c0c1e05442c0715010400f800015548180c0701c83d0702c0030900080c0b0a59103002c04081580a060f52215a05014 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 237360215 1250 237358965 237358969
    0x20c0703030806190e04030206010501080c18030f1605040501080d0e060708270103140f0601050702040906020412020307090204080a080c0c0d0506011701061508060d1403090406050f 80
    0x94060200405100d12180400e100d9a42d1542c0d10921142c81804103c46948408190400e928151003c502600c0b8282c000f141075801603448500c10b6610030304c041e00702269016900c4034401c0c10f040894042c014840d0000003014280b16400041010301c10180c039207071400040c0030449a05a005000581002068501140e407004040c4080c3c2c03000c03075042d52260707503a0030300b43c00300d100320500300710303103016402200003000c020340425001c00000b41c03010400700c5692038071440d59000480f0082094281440028115806a00501070590000d40001580721084e80d89100b01d0b4800d030030580c0d510500000d000e0440c035080200601510b10380d0f0b03041d800c0a242650700c9982d0100c6a40c01010507074007181707410000c403003080344002c4205c000b40701c0b42444a0f581091030f15444203008d03480384107154024050030000140a02021180403440b201c808403c03207402201c61440240c04c3d00d500c0750b145000d410220f40301c03200041045121602650b503929241d01003004889242e80807900444c5940c45a0b2615 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 237361465 1250 237360215 237360223
    0x60c020a0e07110102040303120e03070302060c0c0304030c091a011403011802070203010c110c0f06120703060b0f190c08030f040c090207050703050d020f06040611040b0d0e0105010504020c 83
    0x15003150308403085603240c141007034640c640c000f00100300640c40450000f040c160700c85544600604a00c104016a1038240b281d47c1d100d215107003010b0050f92120303001c18900c45e4130100400300c070140403003a607051541301da0303904014041c103900600d100c546a49031035aa4190003c6807941400c0c007401d01c40480700c0b00c0c0b06034040c0e40c0814458070900c62940c07409546101d0564048900d4264020b00070081200a24005000c450700462388505901c558801c2d0303045402c0c0481060621f580c010305072401e08020028025400d43e00070120002c040c1c0360707078000900c00514009088481c2c001e07440291280c04600020110f03000750503440080152540004003c01c01450460b40c010624104003e01582d842c10314403045000c0780d016a2881d440081c2e0340042c8600864081c0642e4802d8003034a500d0246c1900480c3c2d625030309002d219458000c400031a0010314194840e0040d40c0060b0b03800b074102961a0840c840d1900f201c01d0001c171040e243d0503190a101d03400c2c40b80c54003401c003c46046080c01e41450b400c84d5a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 237362715 1250 237361465 237361469
    0x6042a0b07050a080a0302071103010b06040515070b0115080703050f0601120b03070605042123010905060a020406021e120d0b090103050c01090902030f041119080313060c020a 77
    0x10100005100c070207220b401e00c40c0920103500b10343c1d602d5403081c244400400945c0080c40c02d4810188981301800186018098400d4980700104011308150a000400100110103180300c1d00c0020104034040001c1ca41100c028024000d504046901e0410b290700038020380002008041010b140c0f100708545107008243e01a0000003e29000d41c028240b1089031008046080100c0d81c0340c132031a80001a002da100005106443c5a010821032114810a2100d5900302802c4010302c224810345d00399550100c0503001200441c594000450801d070b0b1611110304000055a100b01d150382c00090a001040e010071500082c0306500da01c07080a0210040d4117038036004100b40c64045e804001500002104042c0c00644500c54010444030955a4914060b40c1d104203940d48e0302e02040340c82a0014004a8902c29030344507455001c0928007a94440c1d803003007810180303000710f150700501386040a1039000203504a0360107003221000844e41c88240c4641e290381208154440800c1000381d50038800140c0b152040101 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 237363965 1250 237362715 237362729
    0x612060f060e061c0b1c020a0909150f0f0516230919170706090306110d0203040b15030c060d1d0f03031e0c090d0510060806042a 57
    0x1c800491540000e0305449400c41e502214180b0b00003000038008154405202c513002224060601070601182022242c00741a002e9803140310123204009080071600140d640501c520381c0209100001d046540484030b41d826038100b10381d5036202030902d80c2481c0c4103550300b141600e88500040800100014002c0e01c0c940f05540044040d5140303550003584200503034180210003080ca04a04804413000900c2c02520720900001c002c00c0303215442e0745d110124943c01510340903540c2e400190300750345070705c40031307002503840c814035040200a80300c00c0c240244091402280320b422002203c0c148507a5038200b403400900360503c00e0b08941070811040d030f500f004440c00710548180201d40c1c00c14005800c0041d191030245080c4030701682518154081000c00154800c2c0301c04900c0030180c1d0b6020005007400300007141c084034070020411807610140b07044030131003000e18410303400c540300c13a080181104142c61595210812507031180b4140b204001c46141010340250135000c0040f42d582180c2c070f2000d00d10b9010b01c0b03090 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 237365215 1250 237363965 237363977
    0x40204140f01090812070c0e010812211f090b060a0809010605030a300906050904061e08070803030c03060d080f18010f090e0a1e060603060612060f06 66
    0x107415039004000702001032081506640b0b0038621030b040c24030940d116445c1200c4e010940d01c40800c400700c0c01c4d01014140c070b0401e0010441001044c0315050b40354454820055084620100c03d080c241c1c42c005040e2181c1003c7d140794a4206460141c1c00703d10480350400b512017400c3c402d0120198444406031030030018a494055910b0b210090460f0051a05030402505405103d00800501c514203401e0320b0744115074861401b442c51581000071449a12000d50800240100800c210a0b84958040c0c40696801000000d0142e501c820385510340e42d200c026030305001c131400e1040000807414815032005202d01c501131b51031860700e03408000b0305110040140f441625144641c070107108038030081d1072215030070248030340d520101d40c9104c1003101d529041460002e01e088500140351880f80e68110110b40f003109140d10592a02580c4201400c0861401103c4070000180000c40c18114007504004040b60740300040c0c1107003081402000d00c2c569041441c00030b42084410000000304601502c11203980d45001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 237366465 1250 237365215 237365239
    0x909030d110d1b0f11030301230a150315050d02040c0207090507090f0510080415020d1a03061e0105130e030c070509090f07051c0f0b04020f04020414 66
    0x30612034001c031110b02d0100e900c0d2111140e414049420311040400c00d548451031140c1c04940210395484840d00c0301c0e2000c0d0020300040010340100c005442d100342d03900c81c0c4c91510083c2030001c21480100c035802807410017107507048004003c1c1c02d0720410f07243c800351403450f00bc040e080c03902140001c00791040c0240242d43d01d48110074503c2c4284034090180180c054180401d040c031000003814000d0138011000c0c0407540d60000106031a14580400d010b001c1a21081d18a40c0c0b00e454504440c00024103d441094007041100c2407402c3c41d101d00c04004c10130310b4403000340c88150420315103814001003042e0100a041c5008a120b0340e0344c915454115501100c035034151007840010403010300720001c2d00206900c004161800020008114441038800a441d055001d41d9021611540c50054100f02e000b01d4009100605c0baa0900c650101c070302e01e140750006522820556a1042c942420110556a45520344244011890044105900c42c001100c0640c141801d00603110a1480c02031070f1207200710000010 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 237367715 1250 237366465 237366491
    0x20f0414010318080715020a0f180b07050609010c020c061603020718020702030c10050a030518070608070f090609091a15040e09070f1a0c1603050c0909030d 69
    0x85880760240000f140c0341d415491501081540001d072041340e11590303241e04240300301d1592086c1d890080311366440315800b4408190035034100c00ca10082a0301c140b280c0c600814403401080080005603c00c070000c0c00d807842c100450a0031200d003442500b04541150310f001c20103130b031940c3c01d03a60a0300000700072407440c440500d026844c14803aa4400c1c0350030355210102c007240381e402e41d010f03083c514020381c20344400840440420109039500056070300407880500001c1c442d548643e00c40c6610462000000820035070300d00c92249080350660005001980000401c800300c0d41c00090740700c4031555820101445820007501802d054004c0c054419072542d10701d6461100903582280c2803801c0400352442e204264840e01e01c0034964400d00950f141d142050001c134540b88000200c002c00c07030300341e9025259a2800c110010041800706c101030120f6000074032002e180c2940902030112000d0f404040d06110501c0c40c0350590403c0c1800410522840c1190b08205400d04044101da03040c00d054100000d00e4125040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 237368965 1250 237367715 237367721
    0x3030905130f0911010e150415090503060408040609061719091a01060f050702030c040e100213060e0618061c02040b031005060304121d120a0201030f020f04140103 72
    0x2c1c14025a908050040e0184010480c0500e102e0900b0b0f80d8040805000d02c061048402d40302d482811400410071007003101c070385c030039070581141d00307a0746040c0760079682c0c80c0c000a1034a5800d07038090311201000102006002e401400d0500280054180340351400c80c2080c04031201100101459100b0150008254404443c1d603c050342a40c0c0c801c510b127003c1d0240302c0140d44515024018000403442a0485010840c0110203440c0540c0e40180184800d401c00000e2001804591081c0c2c8418890bd54031a0300c903010a0001d440e9441818015543d040e107414001045600e2524445d40107a008108200311120641c017090804003090b60000d80d101030070340c0c24004450b46088801c000714400b00c0c001c111990300e0310085003d4940c100340031030426240c40070410700d480f05440007004101c0b040324540910b4040d074040442041064805100004280007103000c2443c0003000c04042d130449585241103603013500c2241c5100c1d504d00011400c090612059050a00c03417401001d180036091801512181e210760 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 237370215 1250 237368965 237368981
    0x2606040b0c0d1e050907050105040b0d0911091302030c0d02060304030804022404050f030f0601030b060105070b0a0207021801050d0206030c070c080703050d08070804080705070e0118050f010303090513 88
    0x41200c000c942020f8181c0c0000344010740e22007419001d00d1000254541c40b130000c1d03a00350b4189007001403402c583d070300320400248200141210b0854103c402008241d4039101d076a48140c5400e9001303019202503104140c20319400303005151081c2410859907026803100d0081e030750b10030341c1400d10100c241c803907000040305103180084000113a200710141c202485604070203002120b005442031f01008543d20101500d400005000c0d207100e0b40042c0040022550880189400c9481070501500c1c240c3e858039400602101107640341b1032280c002465604500b040003c44804c130800050701d5030f5550400000030010044184064401c07800800820380d0003900340100c4070400e50040c0c04034145a61102c031107403644000d11050f1483d006050010700e200c1d002c1c00702d2501c01c645d03940d00d2890340d03500c0e5640d200701c2e904500e0782030344c0c223110303206000c110003118110a07406400701d02100c55940c080c61201000b6100d004048882d80540100104000798001c1a440107a910895078041c0c3c0d103c400001e80300030071603d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 237371465 1250 237370215 237370241
    0x9050906251e0207030b1509040330020702010e1219060e06010e0702210d020a030b04050f15030a1203020c19110405070e09061c06062606040b0c0d 65
    0x200701c2d02d0b6582500003440604a138400c3c2298034140d602d144003414144042d0140c290410403030701c00600020b02c20141c1007080c840e04130024005458110f00510701100c0e4060800886500240a81c250340e04540162203210341262006e134400c070500400c9440300703040492041ca01c601d095440c0100400f0703402402c0c2c8103956004960456945210403007021500303480000141c002c2044103007040c8242032104200c040d205081a1800462440c1c0d140290300c803d40c2d88040541d1646502681d595502566020780100c0900481078108070240170400784440381802e100c2e6002091104c00a1502e11a074100401d1038200140c43c1e80d0710300695820f04941d165078040701c86c0394407214005c024181c002420001005d95040000756506a03090300d80c64004a40544d0200311407001805911740b00d0440e22490b907203c0c410128000a070350703406041e55603541040190140e444099001e01d980c04007180070489681e001054a8101902c415004003000703020b15069500002e1010b402400c40c0d0402030010032a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 237372715 1250 237371465 237371507
    0x60a090e0903030f071704111c0308070206060d020a140d050f030c1203010303081810020a0801090b0a030b0a09170c010b181501050705011506090905090625 69
    0x5a48400d0300ea91040303440c1820016a440800c0c1041d06c44c3c412002c2d241c021040080702511a52a000b003900200e20089500000680040c40b416280030a94200319119861381c095a007002c84019080802c02849540612920101c840c0543d1759000c60310304440c1c0c0781c0f404a40040451020031401c1010359806809403140350403e400401d400401442e03a00100000d4452940c61480300300c0b00c0744401e12001d80050189408548111500c441c41d01c0c480c10040101ca5041442400250503a042210184c011424213801040b800d070081c003550a20810448041c4403a90465540301058007000d04170b801a150b0380c240c2d50040000c0c1c1040455550725151000791201d0206c2540d40c01791450b100242d0103065001c2d0f501d03140ea45c1c00013400d40104c0c1041400180440c0400044449030820364007078805648644841d03412102a10004000d8210307613903030040281c200303034010065920141040e809980140100a00e0401221000c55541001000c11060300d40507a011a0703500200a02d00540c1c0032 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 237373965 1250 237372715 237372721
    0x1b020301060b03010306050a09080a110a060c0c0b010f060f0503071205040b0114090106120b13060f05031b030304031104140109061d040213022209021e0306010e060a090e 75
    0x81c2d860090342c12a88190001e1142e0382d155520350f810303106018801040c0450074455404014043d1a01543c46900342003100c1041c10244c80300001e40c1c4045103401c0104c0c40c0703241179000b0b121200307600a0140070001c20b600815454258010090903503981d40004100c3c1c00b101085d440c034814514001c81008080c403c2c00681454145401d07028070030320551001070b000440b088500d080c2a49010304950558481d80c10443c00319218101514003490000e41c4201c0300e1070340711111070b01482040081c000d04043c0031241400c0c8800d048c039003414000b480380241c101845290190741d0000031101a42e920440740e207c1c0c00800ba000c84c5c00f87c441d0400ca00790a034000c00c00841c0712030301d030741c0020304884940107a0001a40e040ac250b21058038141c801039009544484100d12041c401d0b001008908008070440003094005000c6400f02d002581200e00c400303070000b074890503442921400000f440d000701100782c554240b1000203400008240b00e103501500300429035810781401009200000d0030b200442d81420301d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 237375215 1250 237373965 237373979
    0x3030e0a060213061e0e150705190501140f160306080303070c02010f030c02060f10050d030e130b21030d060f0f06050310090f061a0d050f13031b02030106 68
    0x38268024000061258209003c803003942140445007000140c45a01c0345a8690f402d00c05000007120300c46030360080408c5800005801006040070401c41e5411a0350590090700e400703420760f610b02c0310031001c84c003400c810700c64a043c80326400307608030390145500c1003802140341064010b0001030380426000c5c00003008104050b6000300d503c40a540c803da8a800100c2c0864405804139140d07802100c00691000d00000d401040410a032a000310710110f203407403851340c1c07640003a803545102101280065055803032001c0d5070030503c0051030401c1c8041002e21405d5244404284021040d00d000301d881036150800d1810150140100c42c1e9420800c402805040d4454101e041d285540d84210303035281c0140c200c00142e151140c001e40b03008441c2148080041d514001c003038400360141c00d00c10b0b0400780c0d07034800010344134201541c2600341d02807907000c5c0ca45440e190340e04c3c001140c1c8005d041c1c0384044100c0c030405c010200c80040c0101c4456040c2002507030000a130f182e4051461000c2002505986000b20100f450 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 237376465 1250 237375215 237375247
    0x70c0c030308041214120c0706091208100608070516120c14032d0c060403200c3015011802070807020d1a15150309060403030e0a0602 59
    0x5a0040c18070b0508441010000c50303041000c0d02c0d000c8417505c41070091044640003620410341001480901d1401d0110540700c00f400c48034004012030b090240c00d000c3c0c07140039400c4000b0030751101c080400b940c0701070324007100a000d21030028810703410007400241c3e20740401c001c000c040390b519030003a01002d6600c03800f00015000608c030510030f0f030b0307400180c0700001030070307000003040381c01503550002a100c1e0350f40081c0303080c0e06d80300c0c1e0341071050782e1b0303400078890785109010400945100c0c1c0c1c002ea42e088001c414101248440b11040180d044003a000320150242c2a114801c05030700c009403660154052180e2814600112803010070811030380d010750181d0703c2040d110301c41c2c000c0c103071264000c0c480104011251070804900c9600c10003000918248642c50241c54645c85150b0380314003a2140c0507000e513804030030900310780040f45d10800b5070301004114070250500710840b5101d0700680c1c075000d02e1030030804c0340700f42d4842001740010101501d60110060180c1d061200185540d4403080030754985060810440740307 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 237377715 1250 237376465 237376471
    0xe09190911210c220c210912120207021e030f0f060109150504090311010b010e0609060903010b21160528080d090509071e08070c0c030308 61
    0x304420000c400d0942c00e0b0910001411031020000401543c6803880038403085498103a0f4410034220010308600509040740100111401699110012490105601013803815010071060708285031840e4000094006142c10302c00c3d0400d400d16042035007520f902500a8403546600a402c01c001204850100c03000c1d680070380708a5000c405481c441d5011408070761b80c8603211007900429910440041103520040e038840c01140e000000e0040550380c4641c0031500b40c1d8a2204110005242c0d291001444070082c401c01c0d06440f002d207446040841c4910000e6018000c809031075100f4000010b400d00141c0c3c095100c1084050007503c01d0741c0041c80c140700d40c1444610024401180d0045400381441c0300c3c01045650180c81c002843d40581109031003110200030f250039404000300c80c1000012031100710802c20b005141c021555000c0081d824803051180004002e03140c18103010f22280f607080032407000394002500c0d0f45645408075540ea42d00504651640b12481d010303041c0c02000d8808024142e01c0b1400c0e500c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 237378965 1250 237377715 237377719
    0x40b031b090c0a0815010e211608030703030b13111905070f0b07020a02280806060a030b0c25050105071d0f0303070203010c03020301051306060e09190911 68
    0x5007695880c003025506200c2c42c00d40700c00007850301d00050082d50031030000130000d110614200d002c4c040308070301203002480b444044805400314121111200c10007000300303940019052815007051380c13070412003d5480c01211001003e05881d080380710583d440e90102121001030301a801d01404407160785002e00c50340140740800841140c42e18100e01c0c0360060741240d0029503c003602c48002c0d04076440d100c580c22805412403085005140e031100c090b940300a4035000e601c00960f003458000c9503585103291400c4141d80018036541151003080419510008803404407500301c3e070440107565580601455500c285201303580010a80c82010124100e988603054045101da0000c00641d120958203680d102207203411203401e80c0580d0380c480000d0800505404075003401404032410140c007980000e09407411100d440000950200041040b450400a62007003a10301d104208550707410921b00401c509640e612150080181e0346c0401d0f80301c000725140c1c22260114040c20000111240b800c05011000170303010328 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 237380215 1250 237378965 237378979
    0x605091206010311090a14040b0a140402030d0c03050417070e01090b1e010e0310140105060c0a061d0114010623030a11090901031b06031a040902040b031b 68
    0x10198000001c0e40c036041c1c0e41c0290200c080d6841e808200211248003c100911039a100c00c0820120070300c0c0c03007040d40154841c2d00f880f00180b81120301c040461301d00c002c003100141514414040941c50102e20510702e000306150900071a03101d41020340b864801c5601007642d45402c0c0c8820400d91101107680000d6400c0088400040c2c2d980c2c14001c1d007030f01c440510701580b10314100005110203200400c07803060880181460068803540c90002800c1c5107401e4061040340c3d03101c1482d2031042d038440322000c2c0074200466101c0e040c012081a40c0f507807000c2000004001030b170f650f06004e03e0004200150110403003004020301800d407154088000341b007001c0c03182a0118030a000700c1070202800c0141c1d45128613890345054195900c2d0503440c000390140d0440403451050801a140c101d44802d04082d01850060341c03805080c000c020414080042c1603403050003018941051000850240c107a0914404400c072703008143c0010500025008001e80340301c042c1d261041c0c1c0200500d0216040b081501c0050844d111 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 237381465 1250 237380215 237380239
    0xd08010302090a06060518010207120c050316060c03030e0a080d0207030801051c0809240714030a080406090c15030614060903070e1308031305100c090b0904020c07060509 75
    0x1240c240c2d1031398090080450024000c4a801907100c0343d10000343c000c1441141c2230680d80756400c004019603002c0c25101d0039070201060005007020000301d4503001d1502c80c500180c0c2d00d031001c000d11005050b80010109a12900100c955400c2041b1860066801540181e07030303004d80c1004a4002e51108000702c01080010000003000d10b40700d020441407140014058080310000d566118403548588240c9900c903140b102d000e00c040081980407607034075081c110031507620790075800c10f100f0b480142400300c5500d13401008003010103544042da45400550004003c02e01e0107003132418002600480d040350000b0140d030104a4400756041e00041d0495401410250076020001b06112903481201c10080d010750010034204000900708000e190f12582c0307403a500c544c0c16075658a80e40e0540c000e071641083c0658142088017840b01c240590150b810380480104286080110050555000e40c03207051501240030441d8002a03c894044440400d10f02050f60030042e150000540580c02841400d402030108001c1c1c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 237382715 1250 237381465 237381481
    0x120b0702060601081f0e13020a0801050103150903020c12031801021203161b03020c01080105040e0d05030a020906270a060215151c0201080901090f0f0201110d0801030209 75
    0x95500601043c0d641042c203a80d00091707424840004d403000c0d50a52074841d80029080c07406404140282080301300e400015110340100514921b19400840190749810010400641a1142a502c0343c646c0e00002c80d0140742d0b8141603050290015046420140c43e5a00040008020005000e56400c83d0b000e110380b100042c00490b42c8514016420203a400d0410200300e42100a80410100420529010b0904102000c41807074195401034100c0160340110007810a80da0008040c0d405031000365010042c2d0302030541c12960303800c50520380c0814000300001107000d89015404a03180304078040d0045541c0c14111642c415500031080d440c403c4140000c2c0c40d460f1500c0d0020009048452540c020b10f84440c100e82c2080540502410500c0c541503036203c42c041c0340d03d40301c01c86e10704051071510855001c1810b0001420f08400240302c0017a0764034000c05040001c00c512069060280c0250245900004038801a20000440090b030318892040880b01920790ba40100340a060741d109489100043c1c42e1102 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 237383965 1250 237382715 237382723
    0xd0c0908070b1204080306120706030204030302150423070f0b0c010c0503101a0d0905010203061905010c030507060e070b0d0f09031b020109090c030207061a060f0c03070b01120b0702 80
    0x142c0704001c11a072004900801c205da00130b10b801040c01803100d11400d401012491622140c0d500100119402107420001e054060240c00d02d078601c85071244480c3e140035070700d6607202034002c102410113451903007494070704040410800c0003406c1d4400c0a020384944500041242e0b4021a1089101e5802c101c1c05242e200d20800950b4000c2c141d802001c01c207142071011201d101e1200f9201c501078150117007d01e01c0c260400d8003030171a08901440006a40742422000e00c0141c40303040000c042c80068980c400c00c42643d2150580d900c00b901b6191007521840e0724600a405410318a803081c0e0940b054420104a0401c02001401ca4039a0010200481d007100b12990301500c030f4070400680418200d0401d0b50140812521102d0301c0c80c030500d00059032613101c40e140710407102c0404444001036030124109080009038403030b03505040344040c1020400072001c00040e10602c100700c0c0ca16640440403e01c0c551081040003034501459000000801c1580c58a007091546040c04109441400150000c80e0500b40041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 237385215 1250 237383965 237383977
    0x7141c0201080105060a02190606061b081c0209030a05010509071409070503060d0f050601060e1e011b06020f070204061e050609030a0204140901051006080a0b060d0c0908070b 77
    0x307100d20b40c6503841c1c001041240d40182ca000c0040d4001c412018220114400519050902c9084005511410132200604c81c201c10b9000c04801c001003440100031968a07000c2d100070301081d0850f0102d003018258800082c0c0031346440d007509441680c19000802c08190401c41c0300d000b81d802281e60007030b03031103041c0f071903450302400b07500d404c01700c40e0010418251099000b544c0c4500060543c80000789a562005211082d409040d901604603e0050040c80e0b44416040c601903001c072000881e075901c154120707240c0c132a1031030704506000c070348409640c1e40c90311410000f1001d90804003c40d2507110303140006000350b200520485c4200d141c101d010689142c5044601009400f41990341c0d2524103002c14801140c2c0544c4139503600d03101e50b05d520001a41c690055452803560918031110504080441d40e09442000c0c0a80c044d41840c107134180030305c0d94030028a80d0300842c0c1400204243e81c850012803104d05c0b429031621034013402e0021710000f03e0b8000b6034403011a90014101c641403aa01d03030b500030281c0141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 237386465 1250 237385215 237385217
    0x4030905131103040b060103060b0a0e09040302152a0c031918080708010c0e011d01090315020306010e01030608031b010b28060e010c0311070807141c0201 68
    0x1480003405141000e10894200d034030070300030000382c44400d4070480c081038008943c1180d00d052683c0400040f035074180034681c000c25220020034109500e4030400303041c1180460a00b801200c511000230b05040c400c200504025110b02040b20300d0f4200088440e080d00d0300c1c8808981000d100002410744c4a50043c21504408e04c40030146061400e0550380c0310b654250505281c0420020380d500420140f80f13450041c008202d004010400545004025400c3d02c14a81d446030500820212400281e41c000501d440340341010866041c21001d0b501c0107035649046604050f00d500c00044c925a07140e02594002d40c0510402d890f80c00307101110500440c141c80c0355001e0300c2c10782d82052140981c40c130380640114844147e03150001c18810030603c04110b814007481c0010000141003400ca510000124200c3c10240000786443c15022403142c0001c1c110120f01c1c07400908103e90362074044181101071240e40041d00140c4152150f01d03a48054801c00c0505203504280310b000006141002a000268020b1507a030381 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 237387715 1250 237386465 237386477
    0x807030315030f240204060c0308010b0922020d02040303030b0306090a030509010507110607062901020d1202120f0604060b092803150212070323100503030415020c090403 75
    0x20340d0348001d13000031602c4034065014020010140c0a81500151019009960f100300c20380580c0e007801400c050060b40301e00b080c00380030440404075450b01d0070650074071541d5440300e03c1d41507002d14000300240b050080d0105042d10108010040680c5a000305441c1c1c0320407021641030381c483c0240e0310344640c12318074001c1c04242d0400002c4515400380014050060040a00310b0341003000a000c622554010802103400a0350380c1d002d000014104904107015850030101008001403c0f40081d59031100c005810051044080d00a880540d803034040743c21501c1100304c0030210f0b007001000800031080035600b0900c00d0382042d8020600303401010030303505074101c02441030f581d40c40d48041c41350460202e4407000c8010f0011690110100d4002011400d8074004040f005136030b88144090000d0280024003800c0415007400b2900a441e034640b1900d009031004807100d5442ca45917510343c84640c500035030209405000c0810300142600000130580c80aa05640074bd880d402a49010400c458004480090202c0e83d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 237388965 1250 237387715 237387743
    0x9090708090307020a0e1602030c0304061b020d0605060f0d05190501140906040c170a020906041d0115090902130f0209040f0f060608010605181804080703031503 71
    0x1100d00c0c4410703048195034041e24502495600868841d00f269000100c1c1e0001002c203200707500101c0741c4008144003039407000d90304108101d82e4190310b911842c0b082104001d290703c5000f08012a0100b1a00020b50040004030707440040e25001019280446005104403000d400000c0281000798000d1003465010300a400e54100c1500e00a444200810b02901c0c0340d9a64032088644003d0004854018842d4400504691034585044c10500940d40c000140c401c0340b8a030065205200091080145a411a0700200716980c034404103004141c2c180702c54040c01c10801c0c641800c1c80b010b501c41c05035a001d124001c1c2156032100c03500c00540348542d00003500400710000d200c1181d18140d000300540040c2c24005460058078800080a995100b009100c030b032507964440110075006071040c1d41c010400c40c20035106640c1341c0325002c3c0c01c41c01100c023045009002116840d0440d500c0354070184210000d0405843e9900305814580318640000300c080300400e140c810703c61a481007e11545044991001180c0d00d641 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 237390215 1250 237388965 237388967
    0x251818150803250203060f10060309080909040510061d0f040201021510030605100e070201111602040e070b0408060c0301050607110f09190b0f210a0f050709060605090907 75
    0x209003d140a0908000c0741548016582484403900074500510710411505012840804003d43d9603c10801c2c14070381850040041d0000c019602003000455820b859a82c403401d000e4204402d000007200380311b103841c8000c02ea0880e40c64640c03281c4240d0414002c001c2c1d8900c90301c91502142507502a000d0381c440006642c0c1030303101c0c90600342c3c00780d49020b1440444e9525582c900a86000362030902d1264102601403016051071400b80d980400c00b840280305480c021324041065200b141111107425101d00d01c5d003025034466400200058100e40110f5822640da800c0c2e0703c2e4181c2042c0135032290b501446c1e0210300d5603100241528103a69004000314034112081d500c000781d100c081d0740e100c3c0c2c0201844010700700d1a80c40b032074501c0c410503941c01010480f01032105644111403401564500c01c0c802c00010b0340454880308250ba0108551202e805119800180b0151420030b022a0080c410611550b54004100d030200d000d904568034210140007594a69078240d800d4000e124040b134020001000041c0b0f06 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 237391465 1250 237390215 237390247
    0x507090507050d06031113020a0c0305090301060e090105010906080a030909022a06040308010f030305070b07030b060d140609040b06040f0e0a08040e0f251818150803 73
    0x10512a052061400d00007004901c10344842c3e40c402d80b06e5201c0c1c014031000b607042c40a4188802654610218980005241d005e400c20032141e02c09420800c020900c0f50241c1c43c00d40c091400380c2215416091146003285180e400b0782004d0146c08011800c2c5040050840400a03880c00b0160b450303210030698030305010034a0001d4102800d060340c1c3d01400001c2d0968440c00f502030801c4030079103070040c00d41d615007418064070002c81a8410011091003000400100e9801401da030070540d0b014040c001c003603c0c0e0702401c81c082d100c046651070b40450b0008170712207401c0c0143c2c080901c1806110010a05507a818100a10441d04880107030040d54a0780000c0c030a03251683c000c820350b0250f210000361040003500305a10f00514007034110740701500000d0912002d000d1801c056403098091061007850701d0002c044104089480d0183d40f005042101000c60443c0a01920a40d1240720011b89259640d0390b005512001181e03400602001e107449080303041d80880c40110030a81c3c0c8414011898420443c80203400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 237392715 1250 237391465 237391471
    0x1050c0f09030a06110a0921060213031b06020d02030307090b0d061a120a0207050c270703050a0c0804030f0e03031e03040b090d081305030904090606170a05070905 72
    0x3043c0601c00700c04002465034844c1107441d00e40401c21584512003644058002c00c0680c100600d1384000c0c0404000140c6480c1c1c40000c240d602410160701c91142100300803000405800c018140780080b028488404210042101119010b0b0308880f40c140d1910801d98803072000313580310780002d651064140315802c1480010884121052130000b14035030b88000f01c0c0081141202074082c2d054000414046140b110000c1d590408144a03046103017032015512199180d0a005100780a6419940c503000e000c08541c801e800c10024506071844d1b00d240045000300100f90071100303a0f0340c00c0c1c42c1680f0381500b43e10401300a48682e41c503854800c0a140402e000b030f240c164050780e41c1949440100148803403046aa1040c6080016209803a500d03424540750019a00000401c03a0f003281c0c2c0000807200c80c19903c102d0141c1c00500e40c0c0b803903045c2130f401c5080103400c511032000040e40290030207802c00104840741c0d2080085411444020030712040d440c9100340c54410000c000740c81c1c2d5020100070300c0490313442e500580d0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 237393965 1250 237392715 237392719
    0xa020d1106280614040605011412040c030c03030513060201050702060105011206120507090e03030c07170c01090b06040b0307050607060b010903021c1211031605010216050c0307060201050c0f09 85
    0x84404010107400b029078405812410790342d10310280f0707900c50342098016000505400d08000c4000e41c00083d01d41018024aa0302c280316420f190080750a0041c41c120401c00b65401c04407424049807070782005031141d0300004145401441c0444005103062040c42428007904c5203a028001c1c1d64030b043c004440d070b61080c100740d01f82d140e560500000d04684040d400c802c10b43c0300d0000b501c1d07020b2a00d1150002c5070841701d5004400e40080042264401409080b10234076684081801c200c40b6483c04140041e014022516585610f01100002440b40145905201d514112424061070201c00c2c1456103500c210b2103000d4002c03600703010301400202140c0214104ca00e0601d4015201996034001450f00004491042a505c24a410040038009009008005c182c40e506003116005c45c02c1d0030f41541ca00c1030b04c00078440c24020030244c408210080d011904030020008080000010900301281c81c1e10218818a10900c0341120000d480303030060061510034072402951a0800312203c200c00e081d81c1c042c0076451307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 237395215 1250 237393965 237394021
    0x51206060c01092a06020d2a350a050717120403020c061327020c0d020606030606010c02090414010603080d05060111060c131701020a020d1106 63
    0x1280071000b4420b41d00c68034014500d8035240584841c841c50b070409160810646a10b103610107111705031300054080d1420120f0f140c100039103089102d00230001c1083c0452100014480d00001050082c076045a0300b1401d0350541c42401c8440f400644551700720040001c824a050911240c500070b40104081c0201c1401014008103101000740c020742c40d54000c520402e0a0b0b90041c051006240e81088441d0305110241c9900e0703c0e05040d500c0d80349903084244103100c1e85042e003681780050a40454945c1058840c0d4200c01e40d1907061419043e920b071003881845400520030100001d07414a00050000c0c02550180c4a452003800303240c0074480e00341001081613a00000b0240005820042442038000030340c0078010071911035440b884084150340740a450241004105040e034200605c000c20708542140e00805d0041e40c4111194190107115401d61180f0007290074880644207030101900140003280b42075080d03410781c4000c202e054401a5402041e0512540301c00001600e1903c0e21004044501d42d0002c10 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 237396465 1250 237395215 237395227
    0x160905011b05010e0609150703050c030c180301110903160e01030f08070b040f020103060803130b130503010f0203070801050d0f02040f0b0306040c03051c02060a0c0c050303150114040605120606 85
    0x142d460208190b8402c6c40d00da1103403680e040642c6003040d00070740000280c5803d01144c200819000058000900344030030f0660000b50740800032480c50004400d02034040c00034441c00d0144184c0e140310350016000345000340903400e10005160b07603188255003581c00240c0185a56400c43d110454110070307001044400080030071028021a0384d00c3c80b2103204502c03c01620701c2c3c1b95014800107007942c1d510380c4034507103d5009202224901084040040c10f0703600c500b0f84281c0f600010401c01616420301c2d44440e030103510305501d05501150780c1d0025813080900391a080b020340d036200b0900c10029600080581000d01c6c04082c3d00c01480d250300500792410600c0004a60904d1441c0024145042580d084503205c4c000d003030030010850103101d44800302202154003c1640f0150360069141c20f070040c0000255659220040341c0140107015a454040d04902240d0f00c034a400340d21005440c0103401c10b1804a800c202d4004404602c0e001200c00b55680742d501e480c2880701448481683c544040c01d0154410028891 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 237397715 1250 237396465 237396491
    0xa030207080d0213090207110d17070303091110120507030b040f05091b0102070515130f06090803040302060a0804030c0615090b06040f050126070503160905011b0501 73
    0x50203095902c203000580d100f4204601103074140040e404074441c58014850900429084469800920019681d0380300494251400c604806465840d41c2c0710054007166060a2651550120072618841c00340500a04014410030004400103054000041e0780b04804000e10b40c80c1c1d411154100c27410b0308011806524110008003038628118400404030342d10f2040040c20442004807804006260590700050080030000030748035041805000c2c00386845800010b180600142100c002e80701c41604031900e5a102c0b40c0340c1c40844000d109001c0056600c010200d04160040211011254010021460100503003c199441c20000f4020780c140503e0301c0c04040480c1044c000c0700c0400044d00d0007000380c6420110181c045840d08009240030b488144010301c101080f08031184180c420074241129116105058111040c50202421310303101010414425460303044400f0318010400c1c0369000b090300f81c4005048400c4180c1784600750009499000d00d08006441e81300340c4140d51701420010422004400b4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 237398965 1250 237397715 237397717
    0x1110115030303020c010f11041a0405030d0306030314030c07110607050d11120403020f0d15021306140a020c040e030c150106110f10051009050906090105100513020a03020708 77
    0x1c01a0042a00001e580c81e072640c0c01e01c01c0e00020383d0260320800c20740d102402008198000c0380a443e071068514041c4c05040c0003503100b52001008020100c6940340c801e090002c02920181c84210041007503d1070010810041e94140c1c0d107c0c2c0d802d4042c0700e041130120f40b242203036904540300c00c6400a00030030503040482c0f002d105041c0140c03817030b4441201340044031407018940440352040e0101d41717009020038401a62003000c17080c024207048a541905520300e0070020030a40e003c030740019615200080d01004412804ca07100201c802d9a11444220010300c108002d0522450314403c0061700f015030042c0c41071034541c2c05141050700b90003c49007800500300080d86012140600388000641d03007401000302e1503104000c5e2802e565068082c0c001c507200703c400c10340e4030500c01d1805603d00303489600080d410a41d1114440c018010444280501d040420391103481d0711040c0ea003981383c0d500b84000200d812100d04800000c0f50383c007030b04044008000050000c0203400981d004400c1603001c12009002c0b0305084 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 237400215 1250 237398965 237398969
    0x1d0f0a150f0e031b0f0303160b01090f091e0503041503140a060b0304030e18040336050d0807051e07090504170711030f1005010f0f0501110115 63
    0xa110744005500341400581103112005165200ba030021004520001110f6095915043d081e60350380c03103041c0140c000034154002c0030300d0b03040400544070600040c031140c40b41d094102c80c20324a041159000007101981554244100500125046840d010005007a522034014540c05082a24103107a1989103c44420300c1d84240000000e0f00d510716413550242c0246042c0c3c000b07800d4601004181e280c0440d22009000091000c1e0501100e01c0c4103074040d031202803805064540e51025031805190a02c0d02500300e13004421304a4036018000c0c0c10a84801034004141c3c04c0354090300412502518000810051540310f5504407500320f414481100050340411594008001d00305070054400c0504485500d810043c1d0301065140c1d0400382844041041c50310303900e810302d6030601d203944c0c1d5582500381248078504d0603030720540503ca000c00ca90414000410142c8169401e400144000d076a00c0510062003100c03401100c3d0400c1118000b08400d600501c95010366009903070010507241c0b511600070b0202901a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 237401465 1250 237400215 237400217
    0x1618140702010605030c0d050715030906090b01180605030601140d0f03020f062d070e1009050f040203100509040c120503190302190f1403190501061d0f0a15 69
    0x3440148103501d01849140c56031b010030748402543c044a0344580d66902501c0c800d00138860800400e108a0b01c2c42034008940050f000b071018001030405140405104c403003407141251701c4040d548101c90480040c00b80c2000ca42008000b00211390900700440c60313403581c003040c5540c0000c003c00c1070000038201c443c2c02c8894500917005010b02000c01c414039410040b000341014407140d141c03400c0028601820004000010103008411015542c525040d94140e0620310305681c00210249900e50f91907100074003000f91842aa641c0341200101e00030700c003e0780400e9031204800c82c4100c5050100c0c0c24030440c1a1751050052840610959491900f55003441000c0c100356900c2e0400a4021150303240e03054011b42040961504500e41400034400c2000c8222440b400410000d1000003102c106100d10f208101417411800c51550303d081c003044c40c0010785805400751035243e0801e000010300da401004e440e4807040c40505503080f982600390801100f11014294594005003481e4007040803020304a055072601c0d131fa = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 237402715 1250 237401465 237401471
    0x15090209010e18041e0209280204060c0609020d020a08030403020103050708090c150c0d020c030d051204030e180708070809010605030c2202030705040e0108161814070201 75
    0x1088000524200c0c40e01003140c00f41d200814154490500c102029900c43d80054025140031803400861608400c0000080d5006c9880300911140d909040b203501d18211007110108070002c81101140d0590180384200c0c008984010344910200f0219042031820920080444100e003245a00056201c00e45400680741d82d071000c2000c0c001c6503014410650400c2c1b0f54149800c903490305a07c0551764260081c042801101125180b8003648801015100c20701c01e80000e60f00c3c10000c20000955580751240d00381c0c0f05e48290320340200d0381c600600860301081990300c6405044e50b03c644040c0c035580707000418541c028010541f40c08030418400c0d812802103c0c1607071a8002801c00d020b0081c01d640000e0034140840e45401b00401040e9400590114140c2060360240381d480110100c41e164202880b101818090002003003010b00c5034000000c00c2a20520750347d2117442c0e40c0301e0f03070a581d8408003000000f83c0a1403600090003c000b200101c0203504440b090041101d0407035001c205c0307480300203171801030160391 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 237403965 1250 237402715 237402727
    0x611100e0a21030f1404060b0d05030c010c090f0f06180b030721051501030c1101061203020708030309061b09180a0606020102070206030708040201020f071e060c03170a150902 77
    0x740c14051300140340b204031400d201001410802c00d01250025000510b1103030744189040b56904c4901c043d200c0aa00481507a40b00c1640ca030310b40b40078000000500001440d048000700704440f818951105403840b24900c4500c003410210142d503614a002e4002001c41c101c94000104041040011740c410b0000d66113522511407988074091031080f030100340038060b41c1004104200c0e4905403442cac602e001424607000ca20318030369503000c2d0780607550790004540305d5003803810205402e40e400c5600e0546034800c2c0d00300e460b040c0d640d00b0320945a0200740d41c1135210f50401d001042010443e42025590958101000c07860700d001c100010315145a96403020b80240b0a03803042100039985441450002c084500096250101560020303883d48002046101403000080114056910800200c8010003410007140c0e035003a01e070751680d07403d5500d90541d9158200401d401140744c0303209a403c464002d03850384402e44040c030707140c0b142002c140008100f00304d255079652000c100a03150741002e4005150116005903260 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 237405215 1250 237403965 237403967
    0x60c0516120e010f08060108060409020a0e0906060a030309050609060f0d06180b01020703080705010605060a0e0a050f0d02090406020c011a0a05060a051606180510060611100e0a21 79
    0x10010190f0705000c1c0510341c800c0d6060300088030341d030310000910346800307039541c2c03030000038014089100b01a411602d101000702e900707408040e000c1d00402d80f4404403502d5564070810090040d2490000800064020383c00f00400d040642c0030b0494141c00504160503c4140c80e15036150741c2041c0c260601c102e4450008020b50408109484a80c8400300c0044c8010383c01d00002079690852840000d19602000035280e0500000307500420103404010047c2e5520f07400642e0092002414002e003030721a01200000050526041d00605403560025010000c000c11a13000c2003000381c80240f00b540c040d03800304915204d0300000c6c41910b82848081c00504440388154060120440d143e401041c0101010814043c00d5a000380c1502c24034118a101c0d800c0001c10303132609402800403580701c0300c9828a84010b8000b085804180503c51211408040050303175070744c8208594505138012072039440e4000300401e41210007503030001c00c801660801140c46804055954036841e50150a03044080003c2755810209a = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 237406465 1250 237405215 237405227
    0x60a030c08160215040203190507030b060a0e010303031a03060c12151c03020a0c0e011401030515040207020319030801080d020703051b0f2812080403060c051612 71
    0x4050560516208040c5940c003035030724040000c0c40b1410300c0b07124002408554003040740740d0182202236094440c0708141d240503582d6042d01d00045604442c507a001504604000301c030407049a0216025029603480d60310194024018170b1103c200f5070380c84042040c80c98030104050381c0030b42588181d26580e003000843d04071782007001415040300e007500e001004000d5030380e031041c0b1071000411400141f2901c245280507031600902a40061032502c1c41000010301c47c0d001c0e03040364100d6908142414085900c1801101120300c100e410707094608904403648840d04183d070242281d00d2028007201da1203441e047c240000b80d03101c54002c8001800400040c4545641406080640e0034030b4001000100d00b10707a92140c13950140003442c6032414000c0c840240707030794461903540789542c4013031325605103401e010750f007400c0802c20031408180030130300d0110001d40a90000d10890005400c0358010f03042c142190f49030b40103445111082c20800106204449411020b0118612860301c5064400e40383d20031a007000c0c0030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 237407715 1250 237406465 237406471
    0x81611010603142b050c070801110409060e060109030303150b03090a0606060c051f060e16080c13050607050102042301020610050907121e0614090912030405030702060a030c08 77
    0x81c814550341d01044541c503d080c801c0c2c1c2c3c1c02445c2800743d22080b420441901e400c00319840890158248441d103508040c807030000f841511801081488a6920390849440c00f4000751440c030700041241c1c9040004c280719a112885c400484190403003856900c401850440d00241c03524005500000c2100302004400d10403140101003030300b0f000c5c002410507241c40703803034501d48684d14101110411500480d01280e0340890040c1200042a00290800b0340c80b038540c1c404001d0030300c80802d0001e40031a2490400c0f00c01e41d01e0b40401401c6c0c03c01d9041c01c0c40305000180d081030004840f01c0d9005e11001c565400e2414100f400100c01807d800340c9101c0441c0024a030401c0a00780022b1b4009100c418043c6440b0800700c1544401c01d414130b03840c00400c030b01000c0000c0620300e050002c0280e14806410640300705812010407141d4112681c2505002c01003080600c940030b540012341640300303101e9642c0d101c0c0b1600185da80280203206076070501e4844d402081d015400f08240400180c0e4030200340388429084190150 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 237408965 1250 237407715 237407743
    0xa0306021b070501050406030c0c0c0303110f0c060a0302091c150605040c0507080304030207150512180307150b04060b1b01050609060d0804030609060b0a06020d08161101060314 78
    0x2c1000d00d000000f81c82e500c0385d800740380101a11100211b002c5809402c02c0e1a01d00c0d4410010b40a046d074a040c01030020b1210b400341c0f000c2e802101d5501d000441c0c001820850200c00a02003860010f0003e4290001e61242d1002c5801000e0404c0d0800d401020064140c8207030f005032020034000c61100140c4048511603044148641d142c000c0504000e50701005964000d544464090350701d80343c42c2802c0e407510401d5071005030703492190b40004050a6011001e8450400412400201c5449421140c1e021b6920310003039010b2a0b105203c04008107814000c040b042c240300d000c000404100c1540882d05840e11a00800711005000801e507185000a25001c007002c85200b00800141c2010030001d508114050308051040d40b035000f0f6201801042d0707003100e0003590700040422240c0303280c2c80c25a01908052176118410058810002151800405c541c041c0104960360042281e451491070510114940350301c9082048405c2e0080c0c458a0912841e1302441c05191621034440361002c01518051155140384 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 237410071 1106 237408965 237408973
    0x5040e16060f02010f0b0d06050705040e010b070c05030c01170705090d1407080d1707030e030705060a0c09030c0b1b06070309030807030204032006090a0306021b 71
    0x10b481c10b011500240184140805400120780c056008103800c1286030f0328030340014a09900445d030000c0e803400c01a007440d480307540940350280260401408400001442c0090101c0c540b0383d0b000500d4110014041c40c40c440f0002010a8803007212404840081d03c0400e9449002d10240d41c1c030750358081e190f14440e03000780c1082e40d0340e85504100c0707401174002d41e90049261440403036464030054071900c42d6402d1010849600206610007040c801c1015a124584100a84103000a014140c0071b6802000c00b400c20000308d80c2129061a02542808914002003001039000e0000104403884a4400ea46a00304030107210803c0b5942040640a80200e100700001d04d81c00d940507241482c001e549002280c0c0e40d141d0180c1c200d100d00c0c00040c04480d000710700003210781d0a441003405030140242086090544c030301c1c00b10b00b10f40403a0b00103c5100b900803541090303c01203e0161400e501142d0020 = true := by decide +kernel

theorem cover : BRFrame.Cov 237230215 237410071 := by
  have h0 := BRFrame.cov_init 237230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 237230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 237230215 ≤ n) (h2 : n < 237410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
