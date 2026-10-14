-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0669
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:02:26.692124+00:00
-- url     : https://prove2.me/submissions/06a1b6b1-3b02-4027-80b6-22465bdc4ea5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 120143884 ≤ n < 120323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 120145134 1250 120143884 120143893
    0x11030c030703030c02160305060f130210030c0c0b0901150509160f170a0b13020703020a1104090b130201090605030106050306101206090614040506060f07030c080705030a090b0c 78
    0x70707000c0c0e8010f20304d01c10588110b603400c94046c540b912441e840c036042504e1683c070460420141c111b45402c0180d001d00c80c10320010490141364045500b030300c20f84e14404240354035161001c10702d510441c202c505054028081c41200d0400c0c104560003403440a4410b190007600711004030305418204103042c013449140c4101c1001d100e411401300c0d28180d10511400400000e600e40104012030f6540b464021103038081c0c0065411100c004003d002e50010000d11202d40c014800311011a4010903014070709900240c082c4041042c0c4000940107048080c4010801d04c0c0410901c480010b080d51000040d51007a02c0345084180c9514040c0c2c0e45000034459000045c0e01040017034420305000a01d2040e02c4100c1c207284504105611100c01542d15603081210601d0391450108040000040c0310240d0307001c01e581c1003080703041400200b1880d11400c090035614080019460041500c541140140c484d080818191108a1850440d403660300400a000c00a21903440c04170304000e904c8100c4a032441100020f0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 120146384 1250 120145134 120145147
    0x406030c0203040b030c090307051203070f0809060703021e06011401052b0f060f0303050714070b120405010b040608030a1110060f17010b0f0915100302040611030c03 73
    0x118040c00034285520300310700091200041d611940030295000c1e0ba05511180d8562241d04189890800c0d141d1050307100305541a003101c40e5440100444032016004602051012110306004550344201e00c0c5042e000f0600260250030700d0760100c0c6048000c60f000d102415516040314080303545050031f02541c10400580c6000e00c0c40e80d07018100400e181c12803014100351401b0b40207540a00094911030084042d501c50a0f1901c0031200d5215440c050b04051010b04c5a850442e2001450742c050340c4001030010400646140386480104540701c02400e4a241041d51440003d45620020400391421511982012454900341c40c103401004181c400500086040200342c10084640d4400b12088109600461059403003001c418061500070306090f560320000340c0e191002050468a00d101101c055901d0a6a00d10403030f514a80031112080c0110394030013640e100e08990300045010320f80d0702c40c1d010040b070f00300c82802c64040d0007a104441d130300c0c0c40b0b10b2040000e90899586034401c25503011135540040041 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 120147634 1250 120146384 120146387
    0x20030d050703030f05090d020c0105030c0901050310030605040c031e2012060907060f020303070c060b0a05060a030e010e030f090904030309020303070f150c170a1e06090c140406 78
    0x905209030282c03070081020a44c801000d0b0845406448a9015401108100310440e40401005e1514030080c030b4114910300d00f0f106c400700700340207041996042020020124a000c404040510051f43d0800010469030030145040d03c0c5081140c40100c8140e02012000102e0420050381011420741107a28815410303510b2010010b00442c038104607034420100100031207081410000c581c8030ba01a00000d1802904080002c0e200c01c4c00124030b042158001c2081280a942c04a04441100d40c0b01401080c0141c4510005c0c0c000040e0b81c119581002001c41e0b51042c083d4150820700445403404003c100b40303a607000c0025184d00c541e01d490035455904124002880c10080d600c954080e0082c64001400000c60380003a041d075201d05c0707054030591007680e2480c0a00c10200e491b0203400a42d030000308400c0c0500e48000e400c1c840101c004500d86507400e800591445141c2d00100e140705607841803c107041e0000d00001e802865a4040e5400c1545420201c82d9001e000781d054001da0b82e0f003010f00c1030410786001c00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 120148884 1250 120147634 120147637
    0xa17030603100b10121b020102070209090d09031203060312030218040c02190501021e131e06081b040603230103110915060f03060301050f06060409240801050420030d05 74
    0x180482440d40c0d03031072911580002041c032906c0003001d0343c009a6a90950300420283c40d0001e8842542c0e9003242c590301c0492604441c0000869071b101181c0c1024685003402500241082e9001074403a01101001c0304406070301d6030040c140314407040c0c41b89080350320f84418801212213900011003da8089c490078841c1030208200d01c0500751080c0000751402c004c1c015040b094a50181d404000f20078041034040c05062801c22050240c504215609400503020108140450980c810a018050181d01058501e865841841c0c01030480740c03417060b41c51780d98000050040c0340f08003805940c3c108001f60341d541c102c604000c282c102d94020760310702c10f0384811504200380e21101901d1904c00f20043e1400000c1c540319003000d413102448450b64180c03030317141c520700307050070744400030810f003003106403075041181990b0388200703a03025a209034600082c0300f01d90503080f060481c20f240071100b00c8051640700048101d815002184941d11410311228146e10608005000c007910119180c0c1c1034108c0c030204044e0b02d11480 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 120150134 1250 120148884 120148907
    0x241f1205120703080709090e0d030c030213030b070f030204050d06020a021f0b041107030c080c0f06040f2a032d0c03050d0c050714030a17030603100b10 67
    0x303495448000c4050310300c075503120034011404140364000304034040f80c002c551400140751038501409546075255241d41c507100c1111100080c15522848006118401d605540100068441c4805040d40b0f078140481c4803c0100c03070300c9002030b480e0040c07400d000d032090080c0c80c2102c3d0090070a8000244d5956188040d4201081c2c0104610680110342da1402005d0f070000301c0360030320720780004090882c2c00a100c00d46400c44d00c2e900e0600e008116000010b6800701302030401e0354003c68020344803100c0c1c99002d82400003d2164410510545c0b00780000d100218105500d03080c4038641c20350030b1482c500800e030709040d40600000c001c0f0059007010004640e050040160751003192544c5035600380d07070204040e2543c0c0c41e51416940585c81c3c200c00c2c010800100300c031070b29594243c00d040e004c178903ca41d42d9070750b9451103024103076105000c0000c0c40c2c52a01c01b08000740510764019440030070300c810040008007170b0f00219a030368070920889401402c2c02030345204142e20004041c00c1500c80280010003691000c2401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 120151384 1250 120150134 120150143
    0x30f0204021218120f220f06020609010b030604020d030804060209090a0f0509122506050f2401050301060e030a0204110901020c09130209040302010905241f12 70
    0x304001c00241402d8080c540c8a440800c07082000890b081031504d00e4200700c80040d00c01c40c2c40070008100c0603085403003070b02d0305190a04103100c000c01c075503480c044004a240d44501d4040e6800007022a01c1600030414601c03440e8040020800c031080c410805581e00c1c7c0550700690850452250304010a10841100394002d018000140c54001c0344000708011040488880440f150b488801c0c82e4410294010304e034102c1c001600038080d5018400c0290900e114411800c02040070003000001d04005c2d040005820507003100b01041240f400049004010074200c9a04051a0300d2189041c2c541d0034002030b00c1c54040060750b48500b180c1c20140191984045041e01c994984100510700c00140c1e0f96000e9600400040e5000a49407183e0400191401040120042c42030b508241080f8000c41c2100c10444440e13012034400d802900d81342000c1c2d00410002c1806409800b64103444580214080140c01c0d0041c20303540380d983e0710381c1c4803c2c4504854039046e400120220600900300310607030784900c6114825014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 120152634 1250 120151384 120151387
    0x1303020a0c14120d2c09011412010e07060c060f06090618020a020a23070902040f090b28030b011d011d01050906060408030d0b030d0c121d090a0504110316030f020402 73
    0x417040003c600180903400401511a90744812400303003050038a800222846100074050002070f0500d550720360030240141010440141d07092410f0010035003011090010722001006025114810744000c1c100c14003503107885c00c06000001c52500981c0c82100e01304202903014280e440d5066480914134265660782c10b1142d1509520004c24110500c00c0c1c000800d003001c0016601c902d412801202540c41d5031201185600e00f481c540d242ea111140105a0a4000c0f0007041c2444020448001210065000900030401080c000700c3c403003020100308442c0300101d8440b003805030703602c4a0310b0801d0700c005041e1006e180c48060040120381008641d403608400c00400789410952182c1c0c104c3d281d038010b1400b03201c0090315032220118504003401021000e02c0c00b441c01c040c07140101e4031118901400c01002c2e43c108840c25144d07a2070300e0a415040a80c29034000c01c0700d0050308010f20b048000d0102500d05817031100c20f188650401d480d00142c86c02a0080401d10201c00034996100c0f02c1c550b1720070701c1e016a00240c0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 120153884 1250 120152634 120152717
    0x110d05090a0504021614010c080a2406090509060616170c0a061a06031b030a020405040c05030a0c0801080a0308062e080603070e1303020a0c14120d 65
    0x30b481c00581a40617050144240006003410452080c10304c4504984d0541d24001c84106171550000145a20100000010940d551110394a01000101200f207a040e01d03280c14022070b00d00d40c04200e80c0d0840710203c81c142c031240c4078401080304038402d5038560880d8be5059425900010101105a900181c210503154142101c0c07006003420408041402ca42e45552503807003007000c0c9011241d602034010141c2d051400c1d07103013100c40c007010090800b006480641011000402165264040b1809024003030400c0c4080300030010082d01c646c1090b50f0b1990041d00700015440100d200b103e01d81d040b1040d41000301042005d0351810b5481200192005070040f4800c1806800c1f00c0a003c010700810049035102801c15031031110080141501415a0f4030a4002030340400042040210441d080700086521000b0401c0924080c1c0c5820718a18008001480070100000d081e214401003c10705c1a041d50301c0704484005220342a1640011541340780418101d0912504607000c40030000c0d28401152090340c113482 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 120155134 1250 120153884 120153889
    0x4050f031c030b1f02301603030c020c01121e09050601170c03060a051e090c01030f0b03030a140c01050f15030109031d03010906020c0f0706110d05090a05 68
    0x3000d05075894003080d00c4051605150030a010342400c183c518160f22034100b10950341c000e44603010040220500544440c1d0304614540740e46800d490410710b504c4040c3d440c4880c2c201c0054540c8001f209802081c504107100c0c9401d400852042d01c0c480b4140e65400c40956001c140b00010048280103c4000369082040b0030004403078400c0400d40ca000b00000d040302e40c9002006592035120184609080d0440317580452642c90005420303420035000312001c20700e980c40f001902071400f0040060b907100c01c0f150f003e010121102103070408600900782e030103120940b4101c9480003039880349858143c1540c420405090001e114140a01c030880c0f001c0e4040e40350010041c00b19003945c0c001da6405802c45d61086c1484400d2030001c100e01c1d0b01c504140e009116495154501800814000702d407254121000c403c5003c3c0c41d03401394000a06c691380407204640b115107000b04142d90399131840c19900b142c0700d100004150640240517032601e051012000b86445c074042c15088485810020480c0e40200c40300341c0c080b4155 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 120156384 1250 120155134 120155173
    0x30b090c0d0507050901080a0c0e2805041101020f0703151b080a0c03091101080c0c010204092705100b060403060203090604020a090e03070201050705070f1d010801060b04050f03 78
    0x10b4014402400b03150300340001c00c145004181d018800607840010b510002030039030000e40c0c04880c46440310540554880d0120780c4030f600381c0e020880740c2c00303d418440f12120400e81d0101d130199000b01075101702c540554005aa0703038100041d1018203039100d1482000007940712002415080c14000c00400d101000d0358030031444884141c0e262004ca4038620070401000d4540c0310340c10020741c0e1480d003400a8440d0351075410f05d640064070824104451a030004112a0000341101c0100901d10300071907481d552001c5100051034140c003140560f2440d005242950380090440e100c031a82c1160203440b203003002c050402c00130490f04010b280c00000c240800000f01d0018070103944111050400780803545030a104111091180b034009038001d07417504041ca20140400001d80e00d1080e42803c140303540d91110b040943c500422580302215103050010701040405c0c02541c5044c2c940042e009144641c0d8075191464241d400c9030250b01000c0700144001c005034513084450f6041d42c8006400d5803c1c54042e4090038446 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 120157634 1250 120156384 120156409
    0x81015080f03040306050f06150a021f02040303030501081203010e040f1b06030e0a080307050d0e19021c0210050a050d050c1b0303011511150403020a02011101090c030b090c 76
    0x102d410101d8100240503490041607800f0000d054802c02914050b40020440c80400c0c420b100f0410000c940480703100c0c0200f000c4280d203210320710100f480c240c82c820120013032360090000b140000d09050000901940000d0802302842034480403d046070f0030040e502040001c020819620801d9a009440105400541204021500c032103690030f40c41c10b0500140c00d07a20191041901f6602030070304440410941e109a9412004501e406507461003440004d05c046c0581d0a00700540740900c0d581d849003142c5405d040411640300b582c081d001c00b89100e4688903420404040a50010100060820400e07c2200200704083c00350800c0e40c11704481c02c0e040c00484800f15050b1040303450004030026010090000d12403a8030071900154950344c104001400c4008404400c142801500550201558424082200404d110490a070000e01e001d0400a544008405050f40450300d0440100344585040c041d004100b90000b03444410145142d80d00020340c82c00628445141c010848541c44c203648e0801e5484a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 120158884 1250 120157634 120157663
    0xc02030f030408031b090a060f0c021203130b03012115021b1207170a020307240b0603071b050c0d2303090306010603090c0504060905090d05030108101508 68
    0x8a03032a241170075011181c950302000d84018814009060a590b81c10201400e4410707901d0481c03d0110b40d800290b070380801021000703510021407101c031400d249001003d04600440713280854010395451032041d200e480207000d00d1100d001d540301e000c07421809090b00d0100c198800c80700d460700d15101c0c1901e64200d0304080c507043c01081a4461a82241408001e071698891003102040e1074000d0542d6840c41c06100740d034410482120104000304924001d1056401c01c50b00b01d044e41000312404441c0c01c80c130040306600c180c541031804181d10024103103d4103aa2144002d0b49420b104e000c00e00281c0c13a42c696141e40708507082e11905c00f80040c251104a08000568030503075181980101c440814036030711080c20b815422550042c414403115035000030720301381144e03818103001843c074200d81403500c2c02c0e01164000030f8001e0b00704900040ea40030030ba404140b04101d80c0f015600404211841203805100c00c0c41780242a0340044205621070365103500007800b8224401c50006400d580c0d0900c2400e26014500485c03 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 120160134 1250 120158884 120158887
    0x1a16060209041103070c0204180503040f060224060405060f0a060906120b090c031b030c0301140307030b01061101090b040b09060106030c050d1d1006150503010302130c02030f030408 80
    0xc20505041c083c0403284010001814210f107000c0d4001004640b40f030f078019204948410a6a0b00c02c6880c2e080114441d8002c400c0d03a0703841c3c3c0ca43c141d1081c010001d10410b0300510a08100d8403000300240c11844003103a181504443c561604410800030344400f42180b90b03c05ca00f80720000142d40e901d800c01000301480d84507070b5016858800d02908800c0b0412004030441c2c00c0a4901c01c0f10340c1c610788415070240c41110501c0e01c90700d44440f1407440c211000c50542c0d000e1000001d203c2802c01c40e0003e941220203451103804414030705420700d07850700b8061100603c0a00b0701e80052007450300840c1000001214000001501d62564607440b014410954003620140d0750b2805101d50b86800384445409071021f810240720785107486600030b081d485000d1003412241d41d100c40b00786903e04075045442040d54074038103e90b07800303402c030800074014081071042c03e0451145004001000d409003060b83c0c103c0c2d0f0002c1c0924031390618048d0b80c3c40030b4410b80594404600080000340c400c0500d10b4003a6000314020740d5180d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 120161384 1250 120160134 120160147
    0x40312020f07091a0d08042106090f0b0702031306030b040b090c0a03110a09090b3028080703180b0712050403052d0f0f01061205071a160602 62
    0x2070f42e00c4c141c2c10783d01405000c0301349a030030118050380c0454044900c60b403100b4280d103000908a072074201c51080014821810b04491380706200e449006068002d01600b04000540c90b89581642e0320b201e660101854025121010802c0b80e0090340721001506000d40041820500c00c2c0002c0c0701d21004032100350300c1c0c40000c160144070070351500ca40780030410016481d501d4607070303440300c0907203d21403900c00c00c82032507195410303c00503403102c0414101c00e403507100c8072890603041844603000c248981c1012403000d20590400b103031211031801210262082075201c107805200c0713549900b031050388140000d8041c4140b807007480091281045c0b000c80142212900f4644403840f0385044050403031842d4a841c1005000d01040c00460004516411482c005440503205000c00d44404007055008412000c0c0724003070707081c036201251408a40800003041d002e0003001010b84460401e05a18907884010300741ea03000c500e003405071020307004850070441140384000e414010b601c00040c0204080c180100c030745039008640c2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 120162634 1250 120161384 120161411
    0x120102041503140a021c02030405060601021c0c0b060a0e07050a0f05031e04060e0102040602010c02070f06020c1009090501030f05010b010201200901090e0903040501081b040312020f0709 82
    0x10719010246180900403040c0b10035500a0303054000d01014546a80081c103d6800c000c0c698070030075605207040080d91680b601c0e040040d01c54104442590150040e211900d10191000f41e0901d442105a1a40e24802126498400050000408484c0c0192f0b4540780450100e0201c05c03c58403421803035582965800100c0c000803d9004070050300c0341481014800d02c6064a20704003280d00c5601c0710000001a90349500300306000d8034141e50070900d19480054041000f9506410001c124540d1360202c40032580e8440c2c003082450300703510445005811413410265a89010741d0550040c0d801e91608404081d00e030348482c01200c40aa1040390f0022038460322100704042800b4445801b1004d0008002e44214030b081c0c41e81c800580541e01910300400a00015503a003c1c08034440580031807490041175180408519a699002d80101804100940b0003d04a07038a98030b036485000c0070f40400e86c0c0c186490b40c1d550a11503249880c0c0e80c020350049041440880790104421401061041004613484070440380 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 120163884 1250 120162634 120162659
    0x90f011707030c0b07080904060602010605180c0a030c020a0c080a06060e090607050901050d05040605010503011b020c19120303050a05060a0605040b09060f040816050907021506030c12010204 84
    0x38040c0e903401030541080030070101d01c1c20004441c0140c41150344c9928034944840b080c4280b0894540c0f02d03190840c0426402d9055000006454040d102c6140e01c207110003402c80090412a000b0442003400c000e4044014883e2700721801e0030590b80102c1d82c0d040410354510703035144851b400441c075640c44045d0707000078003410b4005d440c010010010111000e0511095003600c1c0c950043c08001401000510300300d02d0b03441102114014100080108140d0801d85843e20203014203100305446907003800807140c0b070310110710503200c0c110342541c00410072005110309001403482c000a1810705185400380003e6407a042c0c3d00c4020440e4802e0740c0008180c58404e1007607003182c0b0098001806010040c40500005401000321020303228060b95040d00ca20009001400910407000411040a000300c4c000800c1c43c000996000c43c5507d40382040c00250702e9009220117900101d805000680c0216100201803000a0b50280c1018014003170301c0b8001e050902051074500c1c5039a5090142c1c1d40020104410f510701903 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 120165134 1250 120163884 120163919
    0x30510110405011d0102030c03040b1c060e13060f09060b10021c110309030a080a0e0411040e0a090221011a21010e010609020306011803080a0c050309090f01 69
    0x321604040c2054002803283c00e4a8000d9100310b01c0159107030109a000700282c07002c00202e0011241c1e12901c13504c0882c141d0700100c041d085003c140c6450300e02c1ca2030050060b602581c2c488143d0903025603c484c40414039950341241500c3e0030750b032921040c0240c006c50103040f14550044c82d001c0b4103d00c0303c1e82400190160b13650114219000003030409040610300307408110202152a0007c40c00303510f0140c0905601c84e0440c415454070900c0f519004000038038018010038211902c0340103400031a44140720036240d4510114904c82400c02080c03000d113000554903500002003003c0000c0c603072541c0d4081250302032170344502c000c10200356a010003081c400b4054441c52103a44000340c410030004c0ca0210f00050420026106c0400403010006100c0000b50b0204ca9240038000c000c0c00306a0341c0395180c2c0000c0d4025501140060400034100202803500c0403440101c9502401c05490300c0004d190858a41a0071442103d85010400803e00f0981c0c1d03052289028a2603240801000c0d450159400c00030b003281e5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 120166384 1250 120165134 120165161
    0xb010e0a0911060a03020c01060e01081002090a05060f16150f09050c1216120b07030b0117060d150c0e10020c1905030114071103090f19080601030510 66
    0x8900c201c0002e070303000c4507030000300401d0300c00c01c0d168041c40d007041d00a40104007a00b00e040d860410005401d401d0340d40310354121080b203c1903803880503801200c4426440b03020101d030b0f0440c3c0c130810308108909000c80106802590702203920b050a42c003028141140f24040d10030740703e0381c90311525005807099a11803d43c42040d1400304121203121942c1e440d0b141c0500740200c6104038005900326900030f106024400c060011020490388030f070385511443c8070306100d4a1003954620380f44000507001a019102d00a02c9200c161901803c45100f038190f0b800001c00103110320382046111181c0e400186070b40120b401038194550001c9046a048078006010078a0100c0c0c16100e41948402c5107901600440d07000410705056a00180400101d200400824a15400503400d0340c42d040c0000442d030b80707442101c0d016807015980e41070141402c51800d03a5a006041e0071503485400d01500070603a1905840030201249004a420803031581d602c002c03818020240e10030b880e40c1e0032060600e0f0762208903200300e2083c100f04 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 120167634 1250 120166384 120166391
    0x312120b0109120b040206041a0309010b090f040212030c100608010b10050d0506030c06070b0a110a0f0509030f0109140105130b01141f03060f08070b030718030506040b010e0a 77
    0x209855941c048000000181031001301c0e402103015501c60700c0c1240d0162900d400d1070414140030403a038030441d6200b102c00c42515480e0410000e010310344120228014403940340041510b44a41e001c00c0425004141c10540a110800807020034440901901e0804944484006005441c0034080c90030364904034070151042c1c06c6500300c1d060490300305060716107a010310280095603a4540004c00c0c40d00d0300900c000d079440302c0049403207010801e484134002e00c54100f4200500440e400740c036180c0380b07900801d6009404900e01d0450300007614801c4000d8041071350004d00320703070000641251031421204a948280e0f80c0003d00d5168500810007402140c0c0c0005078581c20031078039140d03611030b003030744940600031680f24141c61002c00312036650b40040c1d180014900000000c01800204014005040c28404d8440d1540c100386d0000380031802084080849404c600410b14540d5464011105a110401d010080b01d592990200200e00c042201a2095206140301d0a855060000c111b2031110001c2c441c0381407030f04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 120168884 1250 120167634 120167639
    0x13050103050a03140316030f0f150f080f0d050c010b030a0803041104090b071206050604080106030b0f040507030f1104050907150c020a090504030c0501020301060f08061f180302120109121701060807090312120b0109 94
    0x4001842d5034ec0071803517103406a114030b040c403c0705001d04240c42000b507251040e512500140700e0f0410084bc01a4403424801c90700c0c2c201c420074001541c80b0f541001c1d1443c514a030000798072501038070703513203000c0c180b010000501e080d1a40000346081c1c1064020240e6690345a000740100030985000c0341d0030800110f42e140b02d03440c1c9691100c1d40e5050354080203080d0712103000c1c207504118960307506003180310005100f40301e207250119960750f98030484c0c81040501240c80c10b50808050107162061060340c0c01420f00c890507420240310344040c04d0040e1040782000401e03208040498400c1c40518040e2440350380d542138441440400400341c180140206110700150b138405900a0078042420005c00321a00f442c21041201811880c1c90b08065403019410403140075100c014900198824442c030381c803c05040443c910114021903455405107070050200d078202005000e581d0190755100da11142500c0c200d0000340d00d81d40d0303540d121b80e10400c950b008a51140c00c0140381c61024000d541d583c210038030700b0300340862 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 120170134 1250 120168884 120168913
    0x82208030409020d0609020706150609031a060612100504050105010f0507060e03090d0602120c090a1211041803020609060c040b030613050103050a03140316030f0f150f08 75
    0x41203202d584007180e80090340804284140e00301d18024207000c1821912424076041c01e40180c0444415000c101c9030b485800705903d8000c00003001031b290001c800c604023005030756042e001d001000c0c0c5001c0d444081448205500c414541003144074900e10020054641d1400d400e1006982041c1c01030760501910701034002ca22540142540c4450b80c016101140c4045004482d60542c416603e00c02d4005002c0745068040c030083e40c00a20001c0603003401d15459513154141742c140350003019030195100c6a4500100303c040c03a8040d2035802140a81440305808110000280c2140c00c8003202c034007041010f08582c02416014010280d0080c215406803425141603c01c50300305101d82d02031640814008808039099403524100c0f40c0070320f14003900030442d5585908265545040030441100003070340c02c0c64103400e40ca03066800c0d00d0061080c18107270111098140000e4000c0d00300c061f00c18a2040d86d0b0b80d640610350b8100c1c080d5400ea1400f10200e426581d080601080805507503401c0a1040d6100c850b5240291 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 120171384 1250 120170134 120170137
    0x510120f090b22080f040e0906010f0510030212010905010e070206040308071b0203070e100b04050901030f030e030d030f0e06091207140f060618040201080c03060d08040308220803 79
    0x26048109010004007807141014045501001404c03109010175159505402d08005009498a42041c0c80341c1d603680801007a40c03540c090051f9040b1500d0350b101088942007425500001007854240036090000029100c9488a001d0b0701c102d50860b1501e004102d240514810342d038100301c452020303003114541074402a20002c0c01800000c1086241c00340d11800710f80050102c11281c0d802400e82d008181c0d540300364044560b0555102d8036405840b03074002810103030038044808030395010b45002c00985c80d5840e0b0006444003030a0540074000f010750540c88581d8180315a1004100c2520001040e00041c1451021103912090390701c15503205905000e8a0035002031041601014000303d603540382101c0c90280000140e0194600280c4a14460858508004558a44100401d40b8200c048030b05005081852170f805503070180c0444d0000010a140810342c400455101c00090030008401d09030303688810300341c1e001d6070058407496004510003101c1600d44820039201401c13403070400541418805c0a5459 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 120172634 1250 120171384 120171391
    0xc0f05120c0d09020607110a05060309101a0402071505070e062502090106030501031203061401181d0a0501120503030a0c0306030b090a03090e0c0f090a0510120f090b 73
    0x110a008680c0c04107498083c2c100350f40383d0381d0150506444038442c2c600340320f2551200c00c076240701d2145008081024106003045ea40304804400082c990705e080701c0036840c0200ba6414420000704080e00c3d6124043d217450004010b440d02c5203c1c281c0ca642a01000801100d401929420811104010003920f90ba5000d054031250740e66003207070720051030101811042c898181d0000075003010300000009017a43d0035078032440c100c0b40601c41030400b2103154801202141c10278080c245984080041c088890f521420302c00540a400d00c2ea8504800d49070154170300c00180303801344c05a618160780c0c06c00034114406d0268038014120040e01040c511a00c0e90740d2600c5c0d010042c1262038007561001c603540c0161094000800468101e25450400d08181205689682c00e040303080d408141410000200442a00c05141c4100e410b05c40309414000006404c1020b9804180360700c0d40122080800300b1903640d00c403580c215101d0b42da295402040310703041490081c1c8030310001d40940189421098804510719052082d032 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 120173884 1250 120172634 120172651
    0x210051c150501080a062d150f0e0d0602030c09011d060405060f040f12020907080f16050f12011509080d0809010f06030b0907140a09090c180c0f0512 66
    0x1c40d034071585c1d001c008100b0fa600c00410004802001d4440349200300e00700c1d07070350400b184192041c0b545901d50950307003072000301e40c01c0005048242a1600030380300c0c071501c0c1e0250100900c0c2200002071a16020144d800540c0c00404040001801c07032025a002043e00c4221b000742070542c09038035000f2000403818083c80c498103000d03140012f40701c2d4500340d10004880c06811003400c80c0e80c8060700d0b886110400c9580d00d908a0003442d0010100c1c1c43d49000302e00c01d9208440b45800a82180d813550800e94007100300140b01c10038000c2c01e0100f4501e4000b504050000c1d00554044940298503142424005122540259062162101d41440446008240e2900386c0d02e19080200250700d030b102e0114010702c04e50030000c1089240175030120800401c90740c4140106502c604941ca12611501100d210304031072110140d109038041c0b0f0070040c8803440d8000301f401d20b0080c4003480f90039603112030410707402e01550800784400366200805042c05400602d103150740c0a040c681982403d84031040006100006400c0c0c41 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 120175134 1250 120173884 120173897
    0x706030b030a080403060b090c03040209180f010f0504030215040305090105130803030a1508030909150103093305150111010f0903050304050105010602060c0d0207020109030210051c150501 83
    0x4003907142084034540b25588803120035580c594a05105000b0044803c5c40c40c890207004021a0184e0010020340340507980007001d100d2030703440f2b500300d041c0900300c0a84290700a003e0440c2c807208d003900a209480c40104551808103c0d4502441c000303007852000c1e9041500c40c00303401d040c04046070f8000d0075202e01400a0134240d41d60340c1c0044001711100150351014a180c40008100114010640c010b10304403d0b003031041d0000c01d41c80c1c88980c2e88078090045655009848000050300851045200502c2c1e541e040c100010129690789800003c079166140301c10f000c00b03842c8480c2c001d903040710681858074202000108498100020504100c0c003d03404000e0400c07107008014120b660080d404140c0f0000880d03002c1041101034a006440ca0f0070072a407e5420f5403800c070001032000d0000c28090320901c2c2180c1c03024508a6028044030082d0006901641040750030a404801a01c0c0e5000c00e000801154036416103c4c980021280d41d030101c5c141030300182c00e0501a2080b100c6103042951002e50b0380909006 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 120176384 1250 120175134 120175151
    0x91a03120304060504020d060204170c0a0501170406020f070b04110303070b0402060a17090a030e0609030c060c0a02032a011e0309031707050c07060c170304060e0607020304050f030f070603 83
    0x40e80d01f2000d54002d44110301c0014001103400c09035200344080c0070b00101b6505003064600400c42c20220750b100d50750105401d08800912084143c565590087c45803c005081c12541d80c000d6107560000c0508413004448c00301804103110344001070800320780084000b18038200c0741d40e84120032648081d00003070088a0100300b440c22513000e9800030120702c038003050800b03071480d2400c0e01130398540540c0c5003a0081000c00a5511040c18044111000d0340d01c00323002403032510081e00600105900c030111300d030030a002c2e2a0151006960a100c05804107800f00c4800040074a01250800701f942401c01082c144550070305c00e0240f02006250b400d5841080741400241e40000c2e040580ba400e0f40c1c0b10481811801100410940326040400f030064604101c045075120354030b490094840d00c00c00c06010f80301c1c01c2d8a5014100d00c0da2204000c40d40140b1400d000310b4210200c44007245044020b6035040090703000440c0605c828107150500740d1034084120020301d01c0720030f25140e082d122085401190201a141c2065 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 120177634 1250 120176384 120176389
    0x80f0103120e12010e01051503070b030c131703030402010806060a0906030510030b0f04050607090b041802090402070606090c030c1202030403110d03020a0252091a0312030406050402 80
    0x808148a460f00284100c10b00c294a0900910007258070a00da507500030383e0b000311820300041c0030040d00c0a00001da86951682009028140c204a81c1c011045241903004600528058140340035904071038000c5880e400c040c4005001d1b91001480540107050078440500040c0d4880c01820480c2c5850400141d035480344601c21080121a41018008040792020b01840008811250303221358011030a552468a40b5001110080300c02d2041080000043c4800d1050080440140307211921240c4010f18001800c030101d000d0340c0003078406641d110750320b10301000b43c40454000c0d20000211449c0030403104c0c0134041c000e80440110040c841905a01000040405004407450040c4118005c1140c0040030500c400a010b5844840818014000c6410085829071300403401d849020012086074249860a9207003041c4401e89803440d006040c1c5075101d2107500300e461100c0c0001c0e00d0119004503002001c04409070411460300032031030080d072240c00c1100d400c48401080c0c80d00309078015400714864485000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 120178884 1250 120177634 120177649
    0x20c0915240903030c1c020706020d12090b150f03010c09060305060f03030f030421050706151505070c050604050108130303022b0b3f03040b0a080f0103120e 69
    0xa890b01403000140c0c1d05c41130360002403214008942100701c0c08003884e021400300d8035441c1d20300c101c40c0941e0112039180c03500d5005403401c640c0c16090a400150039000fa07141c01500000682e2020f1116050030320790100c50800006411100b0b506400030b1207808001c0000900c50303441803260008041c0d030b0310702084041e56605002c1200c824014101c2e41c60300354000c5080300e6640103403003c0b117036001c0c0c940c00244070312586030035650b490b0101e480300341c206440d51321003078050101c02c2118024140311903004a01042c101710110340c40e200d2b0b951125102d01c1180b62560141d151908001d100b0322082c001044136a0780014200d9012250055800c0151490b141c00d034042e009055051000069244020349610030383e0081900c40002100180300b0440d004c0240215051400002500003042004940003120901080400881c003c0251150301d00d10705000e03811030300590424829000b0000381224042c2d0b10243c1d00e600207404408420352545103940d814a424003040d105818011041c01c44640c9540310f02 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 120180134 1250 120178884 120178897
    0x20312031609140604090f02121005010201060f051c0f17031006030e06041202150a0c0807020706090513060b120a05070e0d1106040312020c091524 65
    0x35120708144608204220345154140005000700c200060b51000d0031405190221000c2d0040e0720b01820510302c2c4000c0c044440f54110125001c1140081400000b0300d01e078400d0710550360020403241800002829200158801c02103058900018802580c2d0703043c0c40242c229920103648a200c0300c515040240002802010344085c095261000384181c001005520a207499151179030f0346c58403410250101d0f61190041499507020310005000980c265002c409a002a40100c0344840b4480407142850740e412550302440741d848500590149800ca004207030031400c18009048001d0601000802c8001725210741c51041d0249224482c5135103446d40904080c05081d11082c0e51036071b0316800307201005400d44036648540e1900b00001c01d901d1203843e407800000b00007080f00c844290a900e5003120503401058859100e101000000002560b0810341800089036030060108401c1c41030822031030380c0d001480c542061401408000007030f61643c40807400c00e40c009501c07005034610f29020205902511 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 120181384 1250 120180134 120180163
    0xb0c0904060803041404060504090503070605060f040e010b120105070203070f080906030405010e0d090501211407170603070b030f070e06040f0f0504180b0a09050102030a06051008220203 82
    0x44c08101a003c0c03003651401c4813001d4800780422669142030108076018448043d0135900705010003400100389401c40d0307030480c400900e03d00d114141c400020302260403001c1d071700490340e650700324011041c14200700068003c900724000f0003061410240c003a4403031150340e20040264a80e08400780402003c07034191801c0d00d20103801180c07603191524082d03009060404265509205200510590902c0748095109403401030752107080003140010741c540704900d0650120b0076181c0b512080d104040440c0b03c0c0c5c40c820761480d1b95142100faa0044035107411480501814002d410000003031199032220000c403600080c0440e6011200d544248003102c440c1c1c00320307086a0f03000100240000d404143d109088080e5000c0c44803c4904139918010407084400c82000041d400607a003000d800890506203603140d00100d5030a000c10b00300555601c0600320703401201c280544035502c04090059042014140c01c40c81c410b410150a6420289400c01020080400303440c0094040301011045440605c2072001d0080c44 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 120182634 1250 120181384 120181387
    0x40b0405071d270c040f09080a05040f0e060d08071a0414070905090a02040c05041e0609090209031b0102030c030310080d0207033f0201060302040f02070b0c0904060803 74
    0x600e055800403440030349581d00d58408000a014814003d1001c016054000390300400c01908880305000141600440b004817865841c24000b000c65807290040000043d943e681980d140d041001c4c080184605801c06c4040603c0401000003907203c00c2a034021581d00308448544804091500d003d0700a424844101f03814071580c144010851408440c1c640c1603801815290306a03201c0d01e0200840348100c40300c414a0b40300128002c01741c24103034404039044407249026850191030b81d041080010704a9040c0d01c0f42e40e010241049902d90180c05a80a007070344079015450001034070002030369486081e12224100d002c41d904404284e00070805c6035003c1e01088141c070b40700d19040710712080400140c460358447c1c0c0580101141194408201c070b4040ea41e010120002c0307240341a41d905d0000c000a00f10352040c109000034134004103184a41852000c042e60700108429041d4814001510840c107a0005c840e4014005007000070070025000d41d2009007020010303101e524400009014040660044456000 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 120183884 1250 120182634 120182669
    0x30f0106080406020721110111031f080706020d0314060d0b0703020d140103120206012603070c0b03061e0607020103020d0b09090a1403040308090f010306090e07031415040b040507 79
    0x1303114030314103080080c980707501030700c540c507404038502741c486000f00c00f03800385002c00c00114540a0342065401c00850080701034551a150f6202a10340480c64000c600580e010074102070a031076250145165001e803840442100d82011404244a8100c1143c001c106100c90000200c01c58860703416038a06005601007400031705414210034078042d00c2030000707441c060801000c040b2803038000106c5904989000800c20392480242d8016a54200300c81450012804100b05000c045102020274074003800104041507542e003400c0c810400808505c0604a0105c0c0d042c804072402966144281c03401c042c0c080c02c02507940c20445003807400400710720300900d60108101c0c0611012010024900f4002880b401d000d1170700c60b140292180e42c078007440c44000d02a407010043c003421820503c404a0703840c44181008035017640c6031b40d0034006940e014602c6801c160b120340810000d01000801d51240c00d5031000103408c06407440c490303400740c401d0010000b509803d0b0020120301000070070080c40c4010405154611216503 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 120185134 1250 120183884 120183923
    0x3110a0507020429010807020f070b0406110a0314090d0204060312020613020a05041107060e0303150415031b0305010501030305072f090916080a17030f01060804060207 74
    0x200301001c103a025130701c1c02e4070000003c10352902c4484005060340d442c032146800c0e41c00444004100404c2d000460041c003056480107041080014040d01010300c3d8542c07a14140480200580350140010b1700e0b990160b800c9101194002e490f2803044040c0001540c1c2e81d00c80c1101003030320216144030007504903240c044000240503000c00d02c403444c060786500341c82050300c0d03441c0f000d04058072840002c2d51020748948100410700c2c183d80700401d00c3c511006000d091044648806c011600040c402c5000c07504000304100380c000100c00c0d81c05250108071020000d00d400c64002100c125041e0000404860104c40141e1386a450000d001008543c031000a00413583c607490001e0090304955800c8035802c110452881126400e501c0b10503d60822100d04194442c0100c10000340d200090700c1d43c655801941400d200c04006845203102801d01200200b4001c5428070b4076a02c003804a5503000310303608050091007030f004001108a41140c010f032610f41d42c01e13100c0781054002481200d40042403060561606810310 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 120186384 1250 120185134 120185137
    0x16110705030313030614150f0a0b070302250305060103060b060403021002010f0506060903060a0c1404060305180102070308010e04080f0703080a0f060b0d110d090503030115021902010f03110a05 85
    0x81c3d1184a003400740d81141b8140c5038803520192268001124000f12198050900840c080d1030340c10014020070703a0503541e05036011190b000740019170040e000700089100f8280c2c001030810000e52030052010b0300d81c2c074546071235440741d0040c00700030300c2c8546903d0080c6195076a030702560080c540040c0b4503444400c1181c0c022380241541010f840c00036041c1000a0201d180000070b503146003070007801400701039071003040007401440ca2940d200c003400a89107982c9200744a00010700302074a519100061a41003844190101c6030020354000303113980c0108100000268003172560f504490382d8490541d481d44680c94030080a0050340001710140f14003042c12018503a02c4081075024211000c41000b240c140c000040d002e40300c42d4094007000c0e09040014202465030f90781f00c8860429815550303414006405250402e0707800d83c240c10b8503280d00120042c0034000441501c1c100850b01c9000a0a840c038035480d241054242c0500d0290511030100c0381e41c51543d000307803c03504c4208942441180d540842100c06450b5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 120187634 1250 120186384 120186389
    0x1110050c0601060c02010e0103050a091721090304060c0c0306050703050610090501050f090607080304050c01021002030106080714070501062c01030f022407050a03110616110705030313 81
    0x58030550700001030301401158540700441e0103a445541c0102c901b001540909005041045110356400c500d50115081100784400c01100c41542c907907605204809242000100400610051906052100d0311034004111000c980403810150854042c0c8c0c14429252074250340060b09072402c0c401000031060341035024a01c5180111914004480700a404a412000034055103001c00e00c200441c01854107800050885001c0081c881443c00c1c1c0b03240e69010300c5800594040741c00d81e04c1003030f1120242d070701807100d584e414119803000c43c01c66161410082072610701900007420300003200b5910f0800040f00f4219583c440e0410000e000c030942d50340714800001001c0c0c0c058020003079090210300321000c0200280303049a40110841a503500540c0801c002c141c480c003805201d5240744481800c0750710700c0d0b0001d0225207000d03402500c0b000e89241405010300104080c00a002d42000c01000240e0181451280c2c1a00c0c09142c280d10310a50800d00510340b002c0d070b810450f031500c07010882941c00c0d00c0001c45e0000303 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 120188884 1250 120187634 120187657
    0xf02061c050f1f0603020c2a0a051804031211070c05030c0307080c06030c04080f030715050702030717270a0603060509041e0b0c0705060105030f030901050304111005 73
    0xb4660f070308141840358100400d2011014040c500c0100000703031107500644410040e9a0035144842500260840c40da0040180a5288110086002c400c1d24100300c0800040005640d110804088104101d4912000078402000c0c40010a07812601e550692f100c50741e820580c1071032564501c410308103002c0804c028801c86211784143e60181215040100d6000100e601c1c0e10010104144550100805a00b00030010035800005000c00649030904109030101c084c6040080c5a4964241c00e0404250740c0f80c47d880e56000b420001840303106503001080390000c81d000034681d064034241c070500d6546445521903000700c4c07100c5044490790301140d41945044a5008641841070303e5950700040c0c00b035422501c21580d00082c8540003c010a4800315500c8201e41060b0208085146654901c0d0408806076901001060045040420410300704640e50241030210014108049001074940d928848c1101c01c0c0c0c104000400480c00700003140900188050008103010100300280364010026000008100c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 120190134 1250 120188884 120188911
    0x504060908041d060103150323010606090807050402120114010e0402030a0212060405040515180607030c02010e15070c05010b06040306050412080606040b480304050d0f02061c05 78
    0x10032560080c4544051100c0d0100003200302842c2d500c0c0c041c84402000c43c03014441008600e5032710040020b05c219406091a9228500c0c1030b810020100d141c82c2c829045540114410003004031640c080c5d0b288181160040c0200c0300140c000701004854824081b20300c9500940044180001da2031990003403c55210401c0d030307540d03069070f400b0301300002d40741c4c02da034003810319000751904a088141d0441c0559215507010700c0c01035801d203803402c241d1a003d01211310500199580381c002c410784d82c0c2030050515233595840100901d035090103081c3c0d1294005800f400500034200908010407070213400c02d4104080c010005502c0315520700b4982e0203048201d4048411592340c12038008a40c0c01218454012040a050716003400d0829451803030a5110515405010103400d0740d042008a02414644102004d01d08888029400c0084400c41518000d103010a0ba0400c1c0000d0100303880c3c18000c21441500001c2401c00b5043c2c500100320303141b1174040b03039000910000c1145804d00c0706941105026180406894 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 120191384 1250 120190134 120190141
    0x605060d14010e0c0a031e0203120711090105011e0f031503060f140c070807060e0a0f03030606020304060e10030204030c030c05031b011b0311190c09050601120504060908041d 77
    0x3c0321118175400b0051004040001c002c030010080c1a4941e4003500c0070f03044038007015505500101075080300004844961105040601c94240400d03824018038003803c1480156039001c503c1075041e40303651007410802c07402c05254074189100750000d0182c0c40744003d10744111030701d904049000d41780c3c010561180500300031300720541c00c00c2c244149100304210140d0500300503c5a561a040764007129050703811503180c800710301c080b1406102d0743c001c10f441907481700e5440e140341c0b0b000350a458066001400b0354100f404100725881e0041c143c105020411a16480980c4d090002500203010b2604003410b220420300380401000b0300d01e807001c01666000c40861300c050610781044042c80d00d01060290005964029000303102d0441955602181d1003420414642d2141d400d0306441e0a2105480c0b41011140c4050768080c8200c408421014188503c41441180741c0a0000381600b0003076803500340c545507100c0029003070003450343c0254001d90b0320003a6255a103a45035890b083e002a5600070301030807280b06020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 120192634 1250 120191384 120191389
    0x90903091003020307050d050a0b030f030c0d0e0301110f0d0e01180308151002030a030509060103050303040201080408130902090f030c0f0d05150c030f0106020d0c0605060d14010e0c 80
    0x5844400e0401402400e2812030307140100c001c0c2d003028200c44203005042c011040d480545019083c45a0a842d40c00188140030004051070141c05207802c5032550800c010f000150b540100d00545140c030f450500050b003d03004400309004203230080100740d0002c0c0118801002c7d492006c000c012110120005101402c808000b4900302c1e00e200d0403044c01001c0003141000084e0050703002070391203800400481000714080010540080c09410040c006800c0043e03d12829600361280981054408000b054250304560b0343c00da5901c4060006414800442c00050402600004664a1121440120200c19070310280706000e90051400d69120716402641d40d040c0e400e001660b2009800c00401a2001c00c011400f030150005a0b0441500d250003400403c0428030403455507180207141500e051a60783c90300c0030f02a241c4400c10780000b0115003203064817440803544841c404040c150800c0001525896404c002030030001e24400051035250a071510304494681948114035034605102546c081c24004001c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 120193884 1250 120192634 120192637
    0x101b0212040e0f04080c010603060213090e061b07060c08180c0108150105090402030c030a0507050f070308060d02030a05010e07080c01090326030901050105011b03080f0403050d060311090903 84
    0xb1803a542c8400c10004101c41602c3c15140d4004d800b5046045c50321920401c8207096406035042034402a80008102c1c5c0b0a07c2024034150017049000c108002035018511002c1d19150b024004000c0164002420011240d100e012920f455500500c20000c402d855040034203a2401103a4101c2070841188402c50304140108003440c44000c160340385c0c8440ea48610400c40110218010541009400d02160f0b0544d00ea038401176020310041c0000580700c1c90710714404825240e0081c002001c20406000080030401c8490581d00030705e500d0308100350103564440124071520f50701c9401071742c5071091000c03c0e000c0c080198421107068004000342c40c0c041e80c85840380c81d07850621403110360000e42c51007000c201141044607030404588440c100d040d02c03020850200185d5800a07210255543d41d5407004100941e0060005140b00d80540d8651050340047d0310b025207501e1008101400b000d01c0000082e003094440c1c2c0444001900380c03401000150b40b0707424415001d1054191403801000702e200421003485c0c0010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 120195134 1250 120193884 120193889
    0x5060115030b010e122d100606050a03050604021303030302030a0b09090d0507170403050708070e0105060405060703020703051002070516032a03120c050c180105040e101b021204 78
    0x2150322003134065200034000b00381880c009141c024000c0d040091301c4954450082c1540140304103801001e0034030508040e09100c0d80e102080b030950303d850003c002868100007620421004c9082c0080c0c140d40d42c1020a0181c441d094003403e4201c295900841010b41503030142d402458009c1080005942d44028001c030048165407221980d44036480180c4031605c188010940b03a80b00b503104640c40d08001c512603005401c2074100702c916800c2103400344032420081141000400d1509900501940f42801040c1544a1405a00d0265500195083c1890700802c00c50b402940c3c40030807038152100400e841c4009402445041b01ca5005100901b540724030000702d4501680d40228164100c401c00742c4010078905034115011000076402140000460640010440303084110b481e145942105440c1013810f01c0741c000c1541d031142e00c001c61605440d802c1d15042d941580c105030740000381644600f01c44c0d85043c00100514041c01c1c141540c0c40034013100c20300c2d503c0640c80f2135000c603004e80349040b071800303518004c90 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 120196384 1250 120195134 120195137
    0x60402090c09060d0c050705060a0c050714010e0d090f05011e050c0f06040303020301090501090216060b0a03060e07030209010e130308040f0605240321070c0509010305060115030b01 80
    0x1080840c0c001d0341c0500c001c0c92034000040000b40f80c0140481c1c808240c48852407404040b910105000040c400d0920226622240c002c0c8100701440000e44081c040703001d0302c2405402540c1c40c42075801c46400960003080c1da01421005c44a00e00c0c03114200501104690243e100c03071084c02039000440d17501813000000244090500d0b43c3c105c43c201003040310310703070441141c51180344500f040d000f19000c000e118283c0994041d640140c2d80c2c0d81081252000c1d01d0041e4005102244100208580d544611003030136107546c1d01110105a4102c00c1000600c02c00f040d0f000985413500c1c03d200802c25001c000381c810700312442510403ca85a9030350480b21040c010481c0e8061011120079007000010b031090b500c26500601c035a4034544040425220710040700c50882e82040303040784002403140d90b00455010344c00032820440007440110610408014210960a034182d400d01d00410800f04000804007064054030014003a18201d41e524104a603852800384103c0d00e43d007003080400c491444c402e001d0340c003909070107 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 120197634 1250 120196384 120196399
    0x5041e02070c0506040e0a2901031d0111071a0601231c140c03010506040314010e0109080a090b091e040b030607020a0302070b190c0c0e0103120809060402 68
    0x4450512020794460441140c15401c1d00c240810590341d40c82c0948064144d20203422210324010606004450350041ca81e03502100500044200400011641140f40001e18000c1043d02d00650b11808003140d03407051001030f50918070580c0f0ba046a0001078090705008200b130011628015400c8800c02905450450024104204002c90075440110300c40c81d880180c421035162034180c02c0400c0c42c8244103104196140c3d00c03181110b01c800c4040403a0743d00800b507400113503d0f552509001409611580c80010001c1040d101004081c14003136101440040c2c0400007070160181034509540b445d4482e40301078010800d0000003003441c000d000b042c1c617884d002c081c01907810b00c0324541c1c1b010301c0240008501c40c2e0154403005a42500e4a007400100c0c003500841e0003c0680b0030070703460007034201016a0810002045d0610008800d0044805841840c0d07800d130900c10340a441034104110b685515800c481d684a000000010403c201c203c2041c2d1106030301d0341d440f409034031141c515540f20b000954020790f00000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 120198884 1250 120197634 120197681
    0xa020a050412150204090e011508030a1209050f0102030108101b030e0109201c02030c09040c0f03030f11150c1b010614030606030a0506010308030c0708120702070504 73
    0x1c0c002d02212030070740110104104211001c500d90142d81c880d40103000000d03211891244900c0c024004c542c0a4104120008141c0e8106101140c1d01d000c0c4030a61310401c041c0800070ba0045420b03611400c9100d03081000d0310211030144407041d0103584284201c5e140361068880142e0b003801d0a02c680746c00e02504188181150303070340040c00c074040c0020006000c41d9541c1c840c2c0c1d290000c0ca1003003030301c1c02038031002048140c0d840720303281007141d010010b42c0403940700b51126250170016030f4049003074511603408035202c1d140c986a40c24115040e1100360031011070440341240c08800d254200c4840984c00100d03030f4039030014806100c40e980e01c54100d1003a407202c0c0d03410b00c00070811288a0030301420b4102d460303a201481c0c4080b070745101420346059a0103210016015241482541014001039600c140250000c1140d41d4596031440c1c3d807060144005000c1003004004980c1003005482140d9100f81c0080d9450b0302c4000503110700f09242c0c000e42c0c4c2440980b04551000a0605041c05010205c0d00b003003030405c0c40210b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 120200134 1250 120198884 120198899
    0xa0509010b161a07020a020909120d09030201060305060712050105060720220b03070e01050d06020901020c06071211010c0e090a0e120310120f060e0f0601120203060a020a0504 77
    0x25500401220b00510210303c403100d20b1800c0b101248641119030090100100340d0060140303049002e030442030182c11410525a00a12000440b030048041d01d000254003c81401e040b0b00400c21500000d100307000c3ca0045c8421994060050080760302c3e02c0e4000c01c44c40e40c2c0e0f00c0820059110b030450080222942030351141e50500e11200344020300f00007030103802e040d00048080f000d0108003c500100059901c4d0240085403e0420600001c0d02c100d0b000030112b5410200081c0382c0100b0440001c0610f6000120750b440c036482170005c0f00f40c05502030201b60b00d40d41d1510342065481c0501c210799001400441c1c1212601c6c0c4140100c1000010390707210460394103000400d1054020b40142040101c90720740c1c0600100300e40030402c1540500d001c41c400e0303131030f420038041130700848040398001010304000e405070f070740850340300c01641c61641c1d8014000a82401d021203c203081100301d0311820301034000c910001aa880824982030fa105100300d064403007690322050144101c0c0108004200003540c280818084c06 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 120201384 1250 120200134 120200167
    0x2d0103030e060d06080304180f0c090b0717040e0a0c0305040201051602010507080d020415030b030309040f0b030607110c01020a0c0e04050f010c05180105070b07050904140a09020a0509010b 83
    0x112280c0b001013107064403040c1d91072640e0322942c0404503000e000803180d010002e882c410560a91040d980c184140445000018a07074059800340b0b8075800c10000b102010000d032101c0c0c050b03055804401c015144c503600d40603072000d10390403644140601d06181e0b41c020b0040c40303485510b05c00c03541611000d05040c01c00e4511030035a070340000100c3c14400100030580200d038000c0058400740860300005a60765051400d82c0140d005035088900600d81801c20744251603030f0201c1950807040c000d540c005401c920803644080604180ca00907a094020304003805055035004820f01c03903942c2a031044a920807081001203030703907801d48080500f8038101001d007482018001c91110350040c2c050421194600840104070342100d00c0d20030141c000c1600000c184500c0f00e801c49071000044000d080c058148241a00c0300c2185081c000c00c40344c00c1050015001c24030365295449190009085515560580b5000c00b4034801010302c90b0381a4032030309102100052a24180340018180c41103519000e00b0241042e0800480 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 120202634 1250 120201384 120201397
    0x607080a150504050406060302030c010f02151b0c070602120f030402100c140601060215010303081602010f060905311e020409030f0801080d020307030e030c092d0103030e06 76
    0x481c1845800080d0540c2e60780a090701460140800040582c036503c101807401001090850610025500c040f80445c2c01113000d181611f0b0300c0701d02c00441d966045d0020200d40b0300803440c400fa8400407828480c200d80028140c030a69810f5022034031291103c10000c10300b0300031400d8a02010030104000360060521210b000c3c004009400c2c9040c41d004650b035034280e03184e030f00c400038040c070784c011001003049076810844c44540d90a100440d43c969411601c005000c034000400801c0e40c4070107140d00403c001d2003503120712040104000100540754030703030880300082d140642c0d48604c401c4000398110100c503e859000c038a20300c0099103044510802d6a03400c0c403080704019030215040480440c0380c025031283d000c0d8104951290b500c24014152450000e886e030041a0000c40040c1e2040a50001041d000011540b05c9601030501c4070a6080c08130000740b4064050919036001110882404400c1c00081c88250340c1d043c01006001c02e01b40f41080c0e810901c00248000741c001141c40400140d103007841c5008068 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 120203884 1250 120202634 120202661
    0xb030606030a0f060612120e01170a0e0c0316051e06090112090204020403080a020607180b0f0c0f0102031e19180b01060e0102010e061605031816030c05030607080a 72
    0x209144d88402e1b282a00c000c0b00c600b0703180d1845e4603000a0080da84046d0070110b01c20242455a9500e0f6004450b09102c0001041d07008460303907850780c11090030802c001d200c2882c20010200c0301c0302c0454450501c2c20100324800e83c4d0142101c1c00303820342076040f10300e0f1015460300d000d01524101a201401121410b08585028507070300c0e40c640082c1c0160300e4a00080001e5801240001e6403400c150724000e180c4400100201c00f042510b0800c04040c0a65544000403295010850368a411402c00650301e20f02c02c0e130481c5000d500c41c101d090400303588190040c40c0700f01e2041d40800d491a40c406121090f2410071034007001524400744140710410034035800280300c0041b190040c0291041c039501c3c4030040e202030f0040320200b000c0c80310a841130360b8240030b0307200088800c40c090300003418130760601c400500800042505000001c4009401450500811884010700c10300325496003100d078440a1880701c1c10b000035680f00d4412a0080380906000a0041c080d1000d0b58484800399039043c0c06000909441c0441d04c2d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 120205134 1250 120203884 120203891
    0x1e08060a03060204080c1008130b0a02210402010e01170a020d020712020c0406140d060b06070506040b060a090204060c14010b06040b18010903050d260a0c030b030606030a0f06 77
    0x4903840d84080c2000e0450a00103181c0c0d20032036410003088001f16801d0004219641041160304202000c61122240d403200008184c0d4980703501c000080c0c020782c00003e8100b210b5030f006884c20301c060b04085000324001e0301c588540d00a203034011a01d88002070f200c44192069240800e9009000341d00426030610440d40040c103112440d40d03a103060541205949005034044511010703689468481c000c005d1602240800307a401802d0b0101d400da000c59600500429658042e040203030300c41908035072007584d0040030b07502d00703282520780280c1100d010303500301c2e00868140d03d020910300340d240b08503410340d51944c03500307907181c40565543c1c141140e01c090013054035501c0340c00c1441961195005440a030099510031a194030b107a4030700401512940e020141000f54424080010400c08600c03400188091314146802c4c480c0c0c82c0c03040200718504d00201c0480103142e800c1250b41085948810000f5a460354207202c4054403004040ea65642500d40c554942c02c00c0d103071000000c50f154641040c0c0e07446081d003c0b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 120206384 1250 120205134 120205139
    0x20a0512131502030603060705130302010e131e050f04110925051b0c0d02090c0c060408120a0b030613030905100918090b150616080d0c1e08060a 64
    0x352034444a0304030b80807599000720902c500c914080c020302d40e005540e0303c2c2c11400c2801c0c00c181e0528003d40351202034140284000d55400796201c04c2c82c8a00c0340000e203d018088440701d801c0701207695580401d274000390b40c605408120352584460500d401907421040030300000420701c0030818111000781c001044444450010b071100800c0f010b050b0221003a80d26641d868080c280b45904c1c00309040c021131070700c03074004010070700351540c64451400c0001d8042d0344146256848101803460340c420a0fa039807150340300740402c00080000b5a03000382808003d0000d00101904c40b0b0141005407403050409a50641200c1c1c006542040d80300c0d5203000703542c000d00e00440600e03500d00124441d50422464000003a91040080c0a550ba9a0084a00c00c10007180704028003c07140d2100351044c240581544083e00380c8042c03501c7c0c0c0d96221001d03100c4554100c007880b500c0001510b424030b402da02080301403820505020680b080c2c60300031101c2d64030800c04c00c001640d10390f030003507801c42c1e01d040010b1549602ca02d504a01 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 120207634 1250 120206384 120206393
    0x4090e0a0203100605011b0b15031f02090109240509041413060c0f0203041e0504141605161b0e01080601030b0606031905071202070b0a060801020a051213 68
    0x50070f50b041074880080d4030b9007414001040c000344031806c603d03004054503400000800200116034001141141d078904e4101940000c0c2c00c0c0010503071400079803141003040e41c400c03941d150f0042c040100c0981311f000b00d6035620b5054220010441c2624800900040e404011071802a0300400da02c02c001040004c1ea000003c0084024690035130340011003c041c01001070810809200c0c0000450035801c20400b00e289140d0000c0d500e00c101d0040e4050000c3c1c0c3e0311421078038a0b48020316405800000d0041c01120204041c610103281c0464a02c4024415000d070f20019600480c21103043d00442c0d0344587c5681500d071078840143c40b5202d404940011009000512000b800e1502c6020b0810140600000d52460621000300c02000e0708151141004000f41300d1043c0d80105242251008038101241c00d41d180c14068800e104030030417000e1542d000003200c808003c60240502c3c4540304840003040341030b44a4119a0030ce0042044000214100304180b4512000c0643c401c2d50010303115040d90010304a0f03548 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 120208884 1250 120207634 120207643
    0x5040803040801050a050c090a060f0314090c181005150d05090303070216060e01030e070506030907030506010f05300a1505060108041203020a110f0d020607110304090e0a0203 77
    0x72480b142d43d03420600808442600070950031110744000642001c2c00301d000580d8001d520f10410040c0448445500710041c080e4214940c5502a03000f6000c00c0c0c030300031011a1320344035810300c9944035010101e414540e00001707088644c080e810380c112900041d03090500307210417101c2140c10f90795100428044420b404e00280a40c034450031115018540300e04009030007900e00550b810720044505c0030780900f84072541d032003071009140c04000d1a000c0b40301c03100c00100fa4201201c0b83c2109401071b400004001009100085960480b4814003c648483e0b80e204d02011041c15540103507039111040185c1c80c4514584001c02403240b00340c102011404001c48042c407480c0c11003a50b000c43c0c42c000030300d8080d51407001c58855680d21060030f0a020a0902e0a6500d12003218090711418060550120303001a02d540f00d080b01071a81c41d104800c40b981c0766a421403440e903444480c1d00240041c4540c90005160314401c80c011000410460021402d2a06014540000d0310b00384280210b11f129861529015076030800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 120210134 1250 120208884 120208889
    0xc050703030e09011a030402040203071107030b160228080415080103021305091216020a090603050c0a1401050915070b01050901090c05030609100b0a02010b0415050105090409030504080304 83
    0x854503802e0310005818803491000507401082d0440440312030281d2554000d040703d80c460b40c1180c0050740e940d51400b0554281f648c800c440f8199200b00760021040012544265014034040c1040080341030b031079903041380c1e9103451541041000c2c900100e1080725081c10340070180011320aa50403400c26031200c0f04050201c001012003400101408010820350405040b880880d010044c400c1c0f14500e454510356130742e10786071607890714130b180c0003c1d586d0010001c15031002e01503640104202c500d1566045100041c2c20329000965203806855406641850718801d01011110300d0313048400a401c01034010b692035001202000c1c1c0004c421a241c1043c114880e0052031064490488900b10b54140820320081190507000082c3d050b25180011805540140a9a03400f52084425440303d940c5c0c2e070382d102500c0481d58010b001c031a80114407103128076010340000410440540b01000620740348150b0b10140300480c8030f440c0c0482c10810921045080c00c0e042414143c0c068203100d40b600307907140c0e8101d1940d4000d9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 120211384 1250 120210134 120210137
    0x2105010603150f0b0604030f020d0204020c03070b04020f0405040c031b050d120e04060b1614060702070806090303061e03010e0d030e0709060503030901081b070b152209030c05070303 80
    0xa0550004100051040c46000401030f1740203400e05083d03984e5070038003001104019114042d111184011951560111000105403c0a80e600c079241031405444190055038100d00c1218030a220303031924180303841500d00c12500441c40e441281e1440d115510329070781c0d01c83c4034a640007100d94046425111105c0c0c0d6000742e0300c1001809075100350796100602c040c0b80148107910403401e00030300b0426034895000b918034103080841c03580055155450110302c03900280744070801500581c010031241540124200c0120f40806041d074080f40e5500303151a4070b81c841201e2413580900c0c0341101224a42e52000c4034203001001400001e803008085011510f089050341424002a8450092070001c3e0001d01042c0018902c82400703018890414002a8490003402001810025140300007080c1031290034410152840301d058280d07481c13881d0b00700b065286104480c0c5404000708840760202c1400c014450762049150381c01e10603c7c5000200300d0001806d0006003e800300103e150340030000c41c2003400480e0045209 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 120212634 1250 120211384 120211391
    0x10b070203060703050c0a05090103020d0c0908060a02070203031209010b0d240e07140d141608030703080604110c030c0708240a09020103060b0310061107210501060315 74
    0x5441010702d459002001281018102000e00065807001000d03a00300d40321500b442912001c101004034000e01440911806550605000350703801e41d002003001055500c3caa06880c83d6a940c1e8080006900c00c4000003034055000b003191505003880c1026046d00f10b040c074000403420030000c03800201031766900c00c41034882548518100da0801000340c2d40002c0507240145c08d1010204416400f52200140c1c441e0700c0b43c402902022148903034a541396040c115a00c24401d004100b0b0b03a0200743d60b5099101e959219186a940c0c000c03034040800400c3d41d4503a83c2c1540d845904e580c42c042400090240400654100c10080c0702c0c00b0410310003400a003030050b40450083c61518a010102c07032514007202e02000802c80c034504030034000c111080180c0d92100c02131001017079610541c0b0040700180312035402030520395070100a01c9000c60703140b003142e0102d034140d0b500c0700c0c0b10039020549640c440c0b000b071180c4104240e404080313081c0b400384c00482ca411036010b04d0000988603902d80f5000090243c02141500381540c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 120213884 1250 120212634 120212647
    0x5040912021603020d0f08161a010b0702091501090819020418050607050a1b200405100e06190e04050d020d0e040b0a081b1f02030a080408070b010b 65
    0x40c100300700c072002d000d826a0100b40b2480c40e00840e0300b8400981303000d004d2906c0601340b01c041c800743d18100d030162505103580c80080510390a10120021010f00d0290010990b02c000007503442081c0141c9010580050218003e500c580340d00f00004030070040c4180c1448288100000d017110240102540d601c1800f80b9041d40318101d104000c1260154010403c3c1801c0203454600400c60001306c00e03900072642c4c248103960301c540300000c0d03c0000305004c02020780d4210750700e040108903d4290000086042940c1c50318598900001c220664004440e98040c0039000c140802c5001410b00e040c68105401400407151403400e40c181d03401c00d0865400000d42006054107000c2000420045840750843c544064200c5c0000c4660041c0201c100c0c180c5140300b252110400ca6051340c0e030300b01100040640c50704940a8100b2607800307403d4031a040c0c3c4458031070080854039001780603245406100c00a031176805903280c034258503000c2d680c01e035000d00180c90007002400740f10000307503031858524040e000403000c0940b100c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 120215134 1250 120213884 120213887
    0x8130f08040b130e07140c12211302010f0e150d050915090615060d0518010609020903070603020304140313030b1e0606030a090b150a05060406050f0d0605040912 71
    0x50490b446a911484c412003001805640b21080c240c1d168449144031b607481030001c10b8a490080c0c83d118644800e2800202d00305001c14255600402180560100d4010f503140b4500c440c0b00401c401c0c0c041e01040c2480c84040703582d0300c00d04100b50a080024610702c83c0c001903041d0184550072400d444050155101305100740740d0000c114821038885d0b0350701c3c1115103207000d456103619090b000c1c04001d0402c000700142c03c0c950340d075202921030a10180d581080540303410340d010950029400000038095203000c001140c0d01d080c3c1c1c000c581c04000013800416640f40f8140c403c400941c8000d02c1600e5103a81c030a284a000b010038002004440307400701554111a0075410280c003c4800506400e100c1d0340c05800b24150380448100160f407122048a005460741c0d40c40d002d042c003500782d12000800f1460050704110b0702003007584292a580038142c0362810b44607100c0c4248660303845180980e60108200b031100040c034400c16401070059411040000c955a0368850124054440c0c40000700c03000400e503540d03030030400d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 120216384 1250 120215134 120215167
    0x60b01080105031207081602030102161209050d0b060d0c060201050709090203010e040201080403110d0c120c0c090513020a180f051603020c03040f0b130e0708130f08040b 75
    0x4000440142c480ea9241c1400c0b05090f00c03e071721000782080e0001c500b4100001000c0c0420b544560050300a44d5590000312003400389003016402241c803110420683d201441c030400280080d1031010700200a80da0b4240c4454140c60070081210b5880b100c0501c40c240040c031000242401011140c00110305800c1801000e4030350300003a0003e0010501c10700c0100094003141c40410b03001502030810380c115072100e00f81110a1f42c072012030400b051160204040c030b61540501d0344c001950050a0301c4c0c0c841c164001088611044100c8080d060641c00c0b001842450601e5000d0b0760003015014039200d2000044d404111016003590107100140a8000082a400040c0c011108140c69401c02000385d8a00781d21405000004070b000c24041507070110380300071000000c00c203c40180800300c88500c2040c5d514840f04a9030350201d92200c102d40024000011143c084a511600402180d00c1c2c01005540b5607040440c0345002000560f06064404294004540814010800ba100441c0186d0340c80c0716000020190 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 120217634 1250 120216384 120216389
    0x24032b08060d0c09050907091802010306240f020c1008060102191e03180806180604050a030c0510050f06031b090f040f150203040c090c12020d02040b07060b010801 72
    0x10034100d0001e030b00203020b4a0a83e07090ba840705200041c15150070b0017092a20740c0355007010a556107402c9180142101c662100d1000c0c2e40f0076a8240245034a03985c006008003180200c0c201580c081003107454103a406900d040104403107620468000c00509400100c104400c04000c0c40442d20600510600796410b100d64000c0031900004070500e0900e90341d80b28a04032040c0e9075050081c020251002c1014820700981d0707440c0d2082060058840d0f22181001c0e181e28080d600100c051040c404101c1c1d40c80000310307545104981081c0980610005510b0594507440140303003c89840c0114414544108000d110303013400780e44440e1125607907181201c280b603d080100c26800d4030a04404c030130401d080d92494030081d40712094500c0807e5507107462a0044001045140c010881107012003024102c008a82c0594441c0d402440340006c12a0b480d6898801c0743d1034201e0075000501c082c4503104204113160024840c0003e841401072615a80d0b8034100d082c3d0300b01c01004c54449440302c20408142d03134401c1c5503501 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 120218884 1250 120217634 120217639
    0x20a0c0807150c0807020a120c05010e01050a060618050d0f060c021e030c0601050d140a05030909060406080303130c2615060307090f02040b040e180624032b0806 71
    0x101c9081c400c0006e503680e41740c880010300c651243d4400c016a00e101703c1400300210350020003441402c040305522030182004950101c00c0358070f0400001042c91090500d82e0020b201e044240c15110b0400e020302c01064a018001d03145c800000040c040007805600c62880090410b501814100350b1511024242410b400c250f215942d1060100f600d1401c0081007460440c1c10440743e10a82c1e0030246080c50358641d04016800182c0600000c110034460040010f1162400c00c8403031640c0d41d07803100d00304030403243d060096000e59171007880080e10080c02040c0d43c072034072405a81c511040c4e55480414412804045011aa00340c41c24101401011010080c101101c070390220010760f40c0c54804042582e0390383d07a21512403995111118006100031a80c12503020b04213611b40c41b42d072581c880c8e80506961000741c07020b550042d000b81c4101c1107940c021980c1401403800315501c4142c071005900041620103c0d0191950500422586005a201e012007501c0c198030200c00258200c495210003074605a401882d050 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 120220134 1250 120218884 120218897
    0x102010608120901030b12060702060f0703060b0306010804140d0905130204050f090c120c0901021506030c12010b0a151206060c0f060e0a06200715020a0c0807150c 72
    0x45024000ca070039283e03800d6081c0ba00081e20a15640010a061010b041480c0720b406a80c05000049602050161040c0d9031842401c00948854100300c0032196107100e800f910340f1090000c594070f5846940a6a005405001146801c15012042e50f0a002c4651000c0000c01e0303142c4c004024505041d20190b00c40d40992401310b0806150601041c002e00c0c90303040040c4100012000150740c030300307060b003660680310b140501049a442c28170f02c41d0005034006218540940b085000c2801c001c9040c038001c601c1424054023030700c401640c0d24103100d807030170700c51190310403d5480e42c2d01d00c20903442d103030149001885042c070a0030a0b450120700182c135403016140004042820039400340b24841d00031760040c91040c0e020744d541c103008445003410b000402c4a013003141c4003030085110310002c1c000c03907800012800802ca1014143d0300aa0481d41074184100503000b44406080c0b8044100d4181c2139020b0010114542041c6120f0009075031040d4042d8050b840841d2001902000d8820800440c401c80803910400d05146 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 120221384 1250 120220134 120220153
    0x90506030c040302010e030f060a0c0809010219050a0905030f0604060e0a0f111216090f14011721030f0c070f110f03070303030509120a050a030203090705060705010b0102010608 78
    0x150301501c110700000c0c0c14040d00d424003030011f40301040422843c2000d03030b0941c1d1050600d08981000b60019070b0b0343c00006249900440c0c00d03a101031080b00c20113250b44011002400c0c0c0c075401a20150400e0340c0c5581400411240081c02c0d0f2014000c219503216940045d215030315081c41e04600321142110802e80f5548545503000004201419500d655a00309029654810304035002800e030314460501d42819000da0140c1c41440d80c11100310400b0b640e0f8200041c001c0b0511683c028048a03401c0c1d2401200341e154400400c922111682d030f8400e0f40e0200026190000c2d00c45003000525140f0403810303400c00358000304100700c681c2e10b450010380001d071b0110a13074505040e0f502d80c10100990711001900100e1541105601c907174408030404441c550103003d031000140d50307050184c014241102c03044214040c1d0301d04000e07072104c2c8508454440a036601e580d414082131480c101e000303410003031070301070a440f5080f400305540e0b540c140501805403150002003840180b001c002402c3d21150f41c00800a9480144203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 120222634 1250 120221384 120221401
    0x60903030503071202070218040614061005090a0e0f0103110a050d15060807060f09050301050903120901020903100606020d031a060c010b0402030c0703020715050307080601021c0801050109050603 86
    0x110b981110007072400103d03084d250340e6800300a1040400003503018001c40059102a10b00d15032952081f03000340400c111138040b034200301c04441c50844090340d00c400d4015024a1079401800a4201c5030409041c084606840b50284007901105444a03030300e0b41c852200401c20800e001c5814606030005030741d83c4242c00d01c1c10000c14044e12440e00e00a01038030784460f0540e1640b0803a40803030b004100000803140071a6968101500340003002907660001000010041400d0905003c0c190184200e03c0003141340c4245130f640005028409403940400355020001d050203a5410480c0e4580d52901041c001204e40c94510041d00e882c501c00004001e040c24010725004100803451000d9a05078260380d250303907030008040d015006003020840355500034030200504c04841c0f8868003604501d4842d40803905070030748503103900c40c601e00568106000924204001042d00b40300d41c0707100d40c002c0c1c410300456400203c02d0120509626800b01c0c81800210300382d004110079a4450802030041c88140c48140c035501306141d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 120223884 1250 120222634 120222637
    0x109140a0b010603020322032001110405220c05040f060305090d0e01020313030f020a0501080103080315011e030e0706180e0709030213050402090c0c0a0209041415100609030305 78
    0x1c1e03034003850f174044000382a00400ca03c886440030038000c10900b40020300d240240002d50042c00014000020314281035441c40b052142e5210b10982d810101d040c245880b0401104848002c4100d504040403152802c412025000742141003865480d002d0711780d800c007a545016502c065018108150808080c054440c5010510825082c12403408805504403040140e04e18481c0301c030101d0340c00c00c21941c00018800f02095000d034240c822503000300707141c0e5113800440c1d1a900070702001d0b040d00401c00205010b103600d010b0a581981c0181880c4404020390201e194051010a009501007600e43d8030803580c0f40d00601840014000c43d040c881150f4401340380303603501c5010a0045042c0841100d020500c201d014480c03040096600400004040c001d8034640005414280c408034000d40c90b10010569040e5000152a0341c40b60190013825905a140c0820450700000381003500e450144101704030720610188140f108581402075028218284109508061305059101c00f0801450078002c0c00065800360 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 120225134 1250 120223884 120223889
    0x80c03060117040204061707032102100902040b0d0b06040b030d05090d050c120f010e1b0616082a0304050105070803090304080706030902040b010305102102090103050109140a0b01 79
    0x2c80b0600c0307580d81d84080703030003403140e03401441580c0e040c94000c0800c8440080c4d814140e91082c030040c03801c415006101d65644812581d83d0300941c00107104c15003000080ea0105501500080c00400e1503128071000c0707840311640748001d0b02d000c0700c41380400c111814076000748040040d0940080508503031807800102940202a045da00c03c1c140c40303a8610a12400700400303851000d006002c40b5844404144181da03500880c0003c001c15428036045000d0709801240307540005605c0c80f00c8401a078190b00400495501120021400614400c050070116141c00060091507540d11080900e8801320744e076202d060b0300d400903690044c0e03000700000c1c4901c1c0da002081c2e071341c0ca581c0001810703120384812007101d0030350146420080035842080d00024446926402c40300e0b40c207000307131410065580500c0044080d51012580084070309658038042198595540781507042401a0201180f040c0c0d86600180444d5003c4e401503625039115100c01f030a01241c584403a03030500d91400100900e8074141e46500307440c2c6c07051 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 120226384 1250 120225134 120225167
    0x307060503160903051b183105010504030518040203091e0a1403030f070c03090315020904060b040e010b03040f0b07050408030714010f0216020d03030b0607030f080c030601 76
    0x10b50710240683d00500d19680030316032203015200c20b0b2403500040b46120b074010340024403403d410100140503c0b240b4030340a00603100c100c100d6800c1c1c107030700d41c0381c40d041c0251103881440c00a4607028140403900c28411140904e11950ba0a652000c41100400700031840100c071621951040050094108000600c2c00c0100140145845c00f1a680a903050070300d4610000600212014919041d21240c04030043d0b108001c8800400f000383c594000441b542c215045006001c510319203401c0c0089a41d002c2c1c00d22545909600c00747c60a01e9100100c0c050b50643d601c901d40071180403c0511849101400d024050411819682d0071441c0645410200c0580000c0c040e080030200404074020500c1001154064101c01c1c0031295038078400e1808a1301500140660240b42d440c08200004c041e883c2d0089811888664003c9800c45000f5000c1042a840130507044081c56691901451a92030360000740c1075040c045cac0c0311004103070071a1030702609580c8024803640440404004200103aa00040c1c003400c65a5203 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 120227634 1250 120226384 120226411
    0x301141807030b070c030f0903050a02090a0605060a031a0103090b010e060402041208070b06190605090301060312080108010b04020405090103030e01020109140d2303010b070309090203010909030e0307060503 91
    0x1400d58090800d05107401c0542082e0011003000b0b41e80d90003840040c00c0920a99030101c46820600c421180a0301c00c7c000141640c00c004aa030015103405600e440e0002d42d0014000351450b0380d0400106140e21504c180000b09840e042c81a0b9641251500c2500908080c282403040544941d0740c48000c00050040c54a007403401d0380800c06580703669040e1409403404485800480b4102e0500341e1076604000700c21985840081c000070018100120242c0c13601c0c5a0001030380d982402e1203003d0301c0c0e50300002c5040c0d804d9980c445000000c1103903070903090b094110a459a001c0c55061004e542d00317649002c0342080c000c84c0100f00800c0309454901050741100d4140ca40401d0070081d0f00e0040380540542c40c800380403107141403400640c0400102d513804640800361900081003800581c6600003401609480034999000c0c40100481e00b00c00e0000c202d11482883e00c00b0815403110408c130300303d03002038220f074208594500340c03502090b402035000190b20700110010b0010301d191040007861031000a0003810446903 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 120228884 1250 120227634 120227671
    0x509030f0915070b01180509010b06030c28030914060402011d030c0405180c03060603031812060405010606080c1c0f02091e0f100c0b1312020607020705030114 70
    0x3100c50640701d803d540050315407020f5948a1040035090040310344000220319200c04101449414450b001c580c06014050f02d0469440e000781c0521a0807030303200202004501810f02118049000030500440100d85002031a01c10904014a180c090119003201c1036010809002c09030380c00201c0c0711101c4450b8040f800e40c544040010030308121140780d09580142c00e10082c4480c40b1200f40c800016580751200b25542803084004243c2d940c0c0d800d80301d0340e8068004101203403004030701c61800c441140d07001d81b0a690a0520f0182985004e8013103a040e0703075036590b92509100c02c95000c0c1c40190040a41800b050800d0101c034414040491101140019541d407480050340415258050310180701d0001c00c140181000125450142c4411201461058084d00440711071490410054500c079042c075034540200c101b41f9a10450a80405071600611080e07012101e40082d812100009681115a0140c032141c00c115030f0180c038107591900300da482b90b41040b014040c1004581c0c19a40e110480c2c1584c0020840c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 120230134 1250 120228884 120228919
    0x16090305120714190b100b030406021b0a0602030709060905090f0703061e050f0d0b040807051005011d06100e0f0f04061d0a02030c07030c06141005040509030f09 71
    0x38200d44141d50f107030286000810741142d01900000c0c4041c040c1da000441ca6880954a010304600e07801103403592103051000c1004030b810795000d490002403407101c1641d2054031a185606e088204041207c3c10380c0c0000c10000300b03991000c007000041c009810410411400d00e00010442040109000a19540c40c40000d442c54800d4000310014006c1450405548000c0e008003508402c0b58000c1d140602d03144080c14006040c140024920182c10101c1150540c850382c0c0d4401156001020036076082c81421044000c00c0c000d1b10800d402001001300000c1d91403400104111004001030010340b00e040a9030600c0c0f8100d030020526013200004036803441c0c1c000748078000200700189030b54401e07402503d027400106100f00c0501c29040d80055038031400601d5502d00d424001644801c071000001c002d0b052201d00c0000e4041c2c0e0b0381c80e01451107002c0203d142045858242c0f035809088803081e45210308a2010446401c06125082e04129428040c0d840c0440ba0100d81320b480c801d2940e0a8051800e11085012070b4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 120231384 1250 120230134 120230153
    0x708040219090c02060603030301030f0b070c02180609070e03280803040b1b0a0c11040e100221010e0105061e03070c0c05100c020112180b160903051207 67
    0xd4102039444610b03190040071008061002003100540324290101e104d5140003c150381c101ca51100c4081140071b1a55900200c601018113001c0501c40d00e4484100181d60b0013030700c414041c0780d943d2000c7c1c0300e14007003041100c4204c014043c04107101840c1240702c05500d002c1011a8068030954408414014400e0200c00c00e100d04c0101400340320001c420300c010040d070220f09500410620014100000800d010100c4034841c0c1d00506021a8045aa40c1c0001e94285644c0b00001802440000c40f107400700f407080e042803c038002d11324143da80000e0028610100c07180c0c51200329800d100071011581400300049400030180030b0603201c1c1e9808a1140d05082580c5160046400011204c540300d0601100241118101c1d0108454042030340c800890309040060726201c00e224140e48040b1400050b8005451401008012600c140c1e2210a001d0841d15034903050320249100e102003242a24180200b40003110041003100100302003120208086640040c8064030340303e40300901039403806c0628110300702 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 120232634 1250 120231384 120231409
    0x10905040c091205030a030509030f070b0a0e0d020f0d210504050c060a0207030b0f070509090a0f020a09031e0206040314011508030a14041a07080d021204140105010b0307080402 78
    0x8103280d180f000c0c0100b000c0800079120011082d05c007804691509140a512401380c01544002da40050002c2408038240054140c1c100ea40d0000028440c505ca440d200d0404601032210000b5030720400005100c072604205001200c41d0303038507001d00030382ca0302441d0300b08003101361810902c8180c403040440c0a00800340864404440000c0000741d840c1e400700000703034840005202c01c0d20304d40001d00c006443e20181a6849114242a83d42c01d890229035504000b0440000b03805a100555a000203001136002480100300403038980d00c6004000e882c43c80c1804031200242c958103904440046400010380710041500c098a42c0800407414400051000a00400061002d4030415582180010b5810004801003031901410341d80e10407200391494944149105510801419132040070194280d4280400a003076818844c11420f0316001e07101041c4c4082ea004840000c05c1c561a280c203110420a00b43da1500c291060240213024661600d6940c07409800010b001030140a40040040d086503100d2100ca0003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 120233884 1250 120232634 120232649
    0xc070b070506070207091404030c0f08030c0d0f020403020a030f0f020607030c020f0307030b181005010b13060305090307060207020d150c0f021603060c02030d020c0318010509010905040c09 83
    0x1114805414080d580c0c400c01e442500c09401100030105100e06e0318043d007004c02c0d490304400b82c4682c03150303130701110300c6a51a20b09440501000b042d03c070014401d003009500414003021681d850744e8845042d0700c201c42510300c64a008510402c01000141c507882444e0048076080140c80c00c40e8465414400c002d04403100000354410310001d441e50070180c001c0f481450590090ba04105840f0a5105148d40c030b0308c0c10f02015007178800710341c0094000c01403246151b181c6c080da481601da00e0003034000c0c0b103001d82d40300781c2144000c03910214801c101c1d8144100b825000b003000c1c0c50b05110a09100e00d00d10b0300d038803407141d000d00351640020741d003800c0d900c40d44040680b995000e1840740c3c1d03c050250300078006206103203902c00001c00c1d00c103203401100c3c40010b17280c0035440c034056200041071a41d6204e500608e084008441940418499228040b41d00d1000e070441c3e06c485d03809169504080c1c022030007030711030580007103041c81024003411072507917070000031001903134002c2e03d0000d981c07000c3c11420341c0c180160358401e10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 120235134 1250 120233884 120233887
    0xa0507171f1a0409020d0b0901021c140601021501050108060a080d09090e1b0d0203150c0702010906110604023c0307090b030d03091703040506090c04020307140c070b 73
    0xc20001090307000038580151400b050840300080800c02c015103c62030070203503100c405101c0c00000314000c040b8007900070074610001481d02104280d2202004181d100d501c0c490742e907500142b071943d140c5440309517029900b4405003840d00701a100426106006004450400c00e02c00f0014070541c0f20b4800c3c003406000e984085506020007102d005290841c0e44c05452055818207818000c1000d00107485000c0c54408a11405000014024041e0203c0505400e0fa45445800d5198050b089160500c03801003002c0c0c68611b64071025400003500b0015180d020314100b01000c4940d441d040d402044558205904032075503035205410b800040e065240c07001c0885000d41c3c1100348841401c3c62008101588081601550042c580e100e80401c2120061a50030303030950002d8610070b1700a0311a40c804215184500018500e0607004190345082e5081200c045945034899001c0c841032078004c01100c220700508076001d50c81c62a289100610070850020103030102200840e41d0418400c3c00d102c80d5000c3c042028115 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 120236384 1250 120235134 120235183
    0x213050c0307020f0d050a030b0f0405130302010b0d0209011215020408010209010306050402041d0a0615080403020f0c0a06030905030f1908070912120e040908030603010605030a050717 81
    0xc600d500c107075080c10152050080b021042103010030304900d81ca146480301401d040101d41c0503070240c8400d0030900e6000080d0700c3c0d5500d40303079100e1007818001c00721000e6203d42c2402d40d1038060b00f100d4014000324420007a00016000603074910b468a8152403102203056800e0790140b91031a03a64040c04864103000d400410701107101c40b4154040d0040030800da8041c0804c0d980e40c000d1000324416401040c0c1100d41d41801e001140060005881c1c2218071000c00050303090b6180c0d0424419000640d160000400010a020a260b81000303401081005007010380002c2e0002000230b0005103080c807411051544800e220707401d1050600603103803055580100d840d61003401800304081881c42100403008503050b132011403141783c42260f01d80c0279180d000e0340140312504c00c0d8503111802c3d240c41d070360a0200018441080318948070380c059441907620a0051329101e042c41401c050035510303550490782c001d80c041809031021600021302c60b01254030402003201c0c070340040b003c1c2c1c07804c103031001d1900d811003071840484 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 120237634 1250 120236384 120236401
    0x60912010504030e0a090603080d0e07030c090204050108010b18010f0905090c0307111f09020402070204090b0a0c170f0a06030203120409050c09030c0111010b28060e0616021305 78
    0xd404d45007100f150322920f80b545458001c012100940800307480100c0c2402004c13458503042d030000003040202d40c00c40710383c15520307500c000496405404c5800c2443d0041410480c558000c000e0702e000d840900005400c0c086103030130710030050042c55080790410440f01d04003a0114001c00000c80a050098040111464501c0720134400fa03106440d468006092008005449000421021144000100f00040d0744c821600300f603001e40f81c0c8800c184c0e4015401c10641c40144d0f500e10a882000344924031719416032405141c03001c01c59100030b0108044c000c2070107140400d90b04404145900c007403104541d1007262902e2070218000d00d0b81c1c0c0c000a4251085a4210507190891000741c01158001e45050203d0b981c2d80790410018043d003405d40317805600881100d00c03031350b00a030802413245540380b0001544400140016890300e044042c106200a001d499035203961010b00382300d0015112070300304103d8515825011604921407140c10b1580400049046d10455594401000d142514018148114108000c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 120238884 1250 120237634 120237647
    0xe03010603050a0b070905010207060503040303110c060a0605060f07021504080f03070606081b090403020c0301180201080f0609010e0a0623010f0c0803190204090212091501050d0206091201050403 86
    0x64421010160010341001e20901b905400e0b00c0701030b0b002e05859454040709841c0c50304082c00031024581ca840b104030301c21101c01c02a0001c0b6601c50300803c1c060500c1c5810004848454102c04c0c040d4608121210100c0b420200b01c032450b69040e1000c18207400322601d10743c840d0065400001050140030709003260040b001018100180c092070040050303c1d59402070550b206080c00d0340345410704070410158100e00d0101029540a4001d0040d90031440720540000e007150070f206100c0000c00521031a078030565074485955070f401000c1d9440130b01c00e0300b021000121180f805110f0803c41c1024080003600c0f020841e0000340080401351001d4041111b00858007103002c0340b050340f0600103081021240d44540c410030180000941000d120307032443c0c03510b40040c220400d02c8003410520039000c1000050346001440200440c0405400130341ca182002c0901c04d040488010210f6a004404801801980c0d0b816594042c4a07038100e801302e940f6140b4002203500d800e54000ca036586541307028104002c2c10380100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 120240134 1250 120238884 120238903
    0x51308030403060b0114030709051203070203071e06020705091602071505181804061a130903170108100203040c030f0b090709140114060739081c0e0301060305 70
    0x6caa404d0392544101d01070030320340000c07103480300042d8684208110900780041c010841000c108141e91800d10240c012a00d400745641c0800301080002c0400081c03c0001490702014216600c060701740c0700e26000000c0d070428800750451b9500b404000d850008213000300a06070092000780d00340d03a20305881d40c02c050401e40041040c078041aa140c1100505464a10084141c00c000258108060384858a0388130042419004845024803200b103881410741d07440131198540c03900040b004c5600c48140c0341c014182c000030485510700040c02c5d40103005280001c9861a07016040280041c4c0700d50f0340741030130b05490f90140c0c03001e0301c48190703c01d05c00c06014261403114402d8200d5022a13650340c0d60346000d0000c440701441000b04100721390005010b90304641c10443c0070301400400700341c10706240f52104089404000c0108061401400c44401511f0300c4814218804031102d04c0f01c080d603882c0c04036003a1920290089125a82c80840141000c05c1c002c001503603d41d4005402000b045c1c0e12850402c1d512034694 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 120241384 1250 120240134 120240137
    0x1e0201020c1e03030703090809030106080a0203190b010603110904020a17010b09060702060304060b18040302070b0f0f090a081c02010b0a031106030a180b1602071401051308030403060b01 82
    0x4040381a510b440c846072140035a040e4200840c55643e40901c12401020180303400c50301c09200704561481035909000b04000740c00298040c04044090b44109032400310150904140744440000c0d01002c5141600054111155070a0214104a1031451b003d068860303006040d500a03c080f0394030750303007035440243c1429010f1010f450701940d98031540d1540e80d0380a0012019400013040283c0001411b007800a10b070030a22610000c1105061900083c0420b001940010120145d6008000038964100308400080c10140c0d2840e251400c158a00c510034440c440e58a0210710001604100c2034a079042e203000100131b103405036440d450041050414048107400804015801c10059030b0342da203441840142101c0e0702080d2132400a41d600203010182d00300030081d500d060350341d8026504d50b0782c41413024903d03540304440741e54a5280040301100300132485074140381107500c440c2c0c080c00304d40b000b02c4a000b1054024240f49407204003155400320001c00942203405940400300d0000300b042050f4002c000001c009 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 120242634 1250 120241384 120241393
    0xf05071b1e050f01050703091203110d0806010c06020a2304060e040213090c1b1505010b030403120b0d150c1b0f0605040c05100804051605150a1e0201020c 68
    0xc010030000d40900a0042d2540400b10707a014051541c0100010991103100c0e06101203074030380c0c409480c44821801001a40070078405120b0b96100341c0240105400e082903030411115034204800000d008410403000204510390003d2a180b0300d40c0078800e80010007443c80c0e4a1011800c1101d0700700e5581d04a881445c0120305c1c107600138200ca16280c000e484001c103140000e030708200c0c5881c50001c09004110550801d10a121211942174600c0556410010b4058840742030300d2195100f5480c201d4205070300081101505000307120000b648204400c03404800b081d40401d130035428400041c001c44002000501e24814902c4194590440b900017101c1d1810b1915425244900300b48071211104e00100e00504800041aa540018100764002034000303010300c0884050b030b92144c0206145910364600d00780403d21500400c07040140070001500d0007007800340480e041a26060100300600d940340407500213010045840a0002e120788865081080d5100c0024081602000007a00039031006244101d24010b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 120243884 1250 120242634 120242669
    0x4180201090602010e03121005030a06090308010905060d1104020405040c0309060b01020a05030a110a020409060b0f060c03181c0326010f060e03070b04150314040302030403030f05071b 81
    0x18812800d11750b00c254040c5191070750000e5040e4994400a02a07111401103000c0850a80c50412250780c0552041e00c0010300044642005082003030140d0016008505142c1000b44544641d070149000a40c000d00344c0724410954800940640216084687c01514043c2030b0700d000c903456080010158081e010812400391541700480e244d1052007805403813a40100302405e14180300d6900300030000518015a240000c2c80e83c0020b00742c812410094500315101c02c1007440034540307411212940d0400300d4649103059070740d00f115612070107401200f900e6016010400045611507641340c0c100b209200542c80d110001529002e0185810740031982a448007070743c501070040031034451581c10307180300319607507421185052012144c00765609122505809003046c00500c122801c0d01900140c0700950090210b1502d03064018120f414400e0131144005a01c001d1102190f008009c80702640d4040c030b080100c00e921100d0a585602c64490014500c41e4a0b9a0510301131080c048802c0c1600c085200c240b040c0d04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 120245134 1250 120243884 120243887
    0x620120c0702030a1e0803040c1d0103020a0902070804030605010b12010909050606040c0c060606030c030c031109010804170d0504030e010f0e0906150f0a0e0306010f06031a041802010906 82
    0x2441d070003d416030720182503c0041503000e0b050038521001108007034000c011342d42e100710700380d0030950b8219544810500141300008c0c00000761f10700c8038660101c41e1000d6245030001001c80d801c138880d00c002d041d400500740c400e0002e000b040342c01071600075009200e42c0d42d41e81c410501c9940719186030200c94918100104462020740103140942d07411070024202030f2200070402c0020408650030360180036150009000049103401010010a082d03100041d80600c0b40c400502074034852503031441050b03e0100b01d0815400c0030022380d20314500c20b2910500aa8643c0303010482a6150386920000b44008268002400d40390340146114038825507810b59008003440065802d000e41586043c0030445401242040f4100810290b52040b80203080d002c0c13114182d0300444156201403000c085011002035400085a04407921030059502a00103280641c90140900482d202e103020303140406481d0382000030700745a00129401c8444004004106827800444600800c00d80c5031802c84c0824904a000100746 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 120246384 1250 120245134 120245137
    0x130f03110420070b100504230601051e0901110f03070c0608011202130213031109010b030f010b0f19051206270603070e010e180d09030303090620120c 66
    0x2d070414480c03508101c101da85008112600030006200050354880c0000d4640d40d0340618400c00b0035465a0242100f510300c080741043c40000c05a506000082011001c8003849000c00700c80d20b2400140561610324220040350041140c028032881c078031600c00006012a004001850700034401c20f81410301543d544016a0440001d10070780c0d103908000b041d0707072015003050070503031180954100700140780903000008010590607a030403da54031040c02c1c280c088103060201c8940e001d085ea440d5401e0451401d001131f8822010140940080d882d00840c001c2c540038000e8040d01d00b440d410341c0b800071280314109801045030304031450520640c0c0018002c030350302c1d0500303000003088403e00340303010400c00141000d07465401e000034105581622034258001404410001c5030f50183c8102d6210b824182810082404003a20b500901c9030103801240c0f8146080e40c20410460440e82e044c180400d0794051402c04000a19a00b424900010440c00c80c000100010100600102e00917803110003207a20717080701c1081d55 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 120247634 1250 120246384 120246431
    0xc06020f120901050304032304080c041404031b08071505060d08040605091f0503040b0702010c1719050a05010501030c0203031303080603070305010207060903030c080f010b130f031104 81
    0x7003004000c0425154450402035074424080d080c40b940c8015689861001410b2029404498040c0410706000040040c00284003a840846090218151005045080c0800500300500340b01140703e1810003114a40b80b0780e007030305400600741501ca400c0b504299a1200c42c461b010f0010703900c0c100c0040d0b414034002805101c1c10350490310482c00d2500385007080d5490380c03080d042d241e13100a0f00341901c1090b448022004180c10f1140d5a03803512400d0030700e0594061040586481c0559041c8402400d10300e40c4a841d4003140300450300001580e840b90340840e081007a40a0303002403100e0500b010420600c06580100d412940d00380d80810011000160481e101e002c00c0d50b902c030b1f0550312003408e003022070b00c07402082c1d800400082c00e44400640e40d540f283d0881c1d00044044030003641b102c03084800e041e014480d21101c82c00381c1c00c09004c9450007003440217200f0014050410141d601042191000e840c1645031800b404240da00462056100c0c181300017805d0246860300e20450a0840e03412000d07070b40c40f1401c2d45 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 120248884 1250 120247634 120247663
    0x714030a080a18020406080102070506011d0c03072606010e2e050c030307020109150605061204060605040c021614010503150d0204050a0f060501080106020325020307030c06020f 78
    0x5950311600ca001020300b80004240098541d00450240565034606c103540003005070100060340d1b0380c443c1c82c00c542040d41c140d1000803066070b000507204000100c128550ba1001503121400d66940d2541c50680c0d040200b001c80444002031480e034a00594640d40b04035000c0c403c240c030344090a01e041402c0003404856010381a24003143c1155480c0488202c007564901c240e800d04200307042004410206182d50411a22940140c0d12510b00f41d041c400c250b060f00f6003215036014184030450804000c10718a104604108050312030850001d4103001070b40e0b200c800588402441030090245c0480c009544a05560b04602601000038000920102074140203508e401c0c1a181c0a013186d0759078542092032018107410581101c3d201c00d10b000140e03558407890348160f10380100007c0d0081202400801c403141c0d038010702c0c1401220b00040c41407030f07000401d403503140c0040e103859903840340701043c0805124040344000b5010700c00d0306008410044545911020780380c0c10340c221b03030203903034141400c644c0c07030a27440c01000 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 120250134 1250 120248884 120248897
    0x30c09030c04020a090909020a080f06010e01140f090a06050a09020901020f030a020c0607050708030a05040602010b09190e0a0206040b09030f070513020c1e0c040f1e020913110714030a 81
    0x1000301487e800604c5103a0000300b200407070940e900d4000e030a0410110394a80c09030400c1c0018000241503c40007405005075600010041c0b0550000c6166103c90b010b11620520710880054410603003030b08a0005010040c0c0541c004560f5001200044c2d0000b0081c14094050440e0429280800006903445030085900802c62520088240700c4954400f0000361020f004514001c01e500f01c0070401002e41c501ca55903a103541e00d1402d0b100a00311002c9114452140114100340810500e4000c100c03402e5503040c040c0015011800700c00d40e8074200c09030f407000703401c100b001c20000381017810070001d0415483c01750180e50700003404584040e201d042c1400744d6544080042229281401300c1e5000d0907140340500200c4182d000c3c100c1005600f0206600702c15540c0e84440100407a6040c1409a62241282c1800501c554400c40b045030540d42034002d010103041d03a01140d40e404c0c030303a541032031402c0761131403414204242c40f1882003100040e03001c14001d480103960708074000030a4400000b1190700f50460340c0c800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 120251384 1250 120250134 120250139
    0x3050408070809011803030206060a08010e0c12010b030f160b1c050a0216120f03020a120c020102040b0406050c011103040201050a0c05120d060311040510120c0308030c09030c04020a09 81
    0x380143e4019201c8141002010146a80016030185141000e10f0003a0010469440c013042048410859500460314503410728035008003000c0300203026081b60904031514190703d42e00d0303042c0f24010f04002a200358181300310340007801c4807200454404411040c030004216100d443e020380c035849110300b410840311000200444248181030354046900300c62070080c05481c0c5143c4440719948240000300a40d81d659454503a566800c0d000b0910320456412420250309100b2403172005005403507800c43c103900341d036291080c4c410740e076100398111000b500b4103005241d203c2d81c80d40c038000c0c140c0d006418103041561918904480d003420501c02d49224a81c141c1d42c4034074001403901c046401c490111700c101c805100e00c01c40b580380d2981800c00750941804000d000244035285007402c0680c0103440c4d10301c500035071408061104412501c0240010b48883c2d5041409049243c50b00c0c41000c44141c0c07001c1c01c14800401800540a11000101307429041203048420f480100030803c0b04074460f00022001040301002d04 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 120252634 1250 120251384 120251393
    0x8071706010b07020d0b0703050603011a0a06080405100507230906091c0b16020c0a03020d021011030301140f010e01211107050601081603051b0409020a0605030a0c0305040807 77
    0x280403c0d4406001a400501556100e5111000c144c0302c08010079100c0040029905091290795020400e19540829441c0340c180812140074860183c44100800c00d0b0003d41401803c1004d42006003040d40d04206514146900410040c80310192030580c00c00000000c6124140030260b03803400d60006e013014130389024602004081403401001c2c1e101080c260780c0c031a0200d160130551034410383d9190032200440b2180b200003424100312000244c401c0403007150a00140c1c581c100c1040a869042d83c0701c110f00740034944240d444030164a803240c00e034407000001007200c010440c0c08214007101500c0290358061031400540d004046080c4d064001654038a940000d4510300b511149001980c000025084030714010100c03042d4401c81042e501c41e40440010850381204000e0b1108000b1800302140c0d80905654070142ca40c203180703107403d0680d940c03403940f03401690380c0e64404030410b50700408201000c1d5940002034090b0700125509110303103141c08801081c1902a0052a1185510180035490100c0d1680c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 120253884 1250 120252634 120252637
    0x13050c040b160f0c2c010b0a0512040312060914041b08010906140f01080c010302071a090d14070201090308070f0b0a0b04060b09010c03030506060904021308071706010b 74
    0x2440d81c019500c0d0802d030300c0418541c0040e41e640318013510342003a241e03050291030045640203001aa000041d056030800540f4810f2103540d05640074038000c0c580e1860241e200321500e01030900c4d0f0f110107402040600040540020014544580103101489001d039180030400403500f054681407a030483c0c00d00060002680e10340c1d049100b80000040125180d00e8074200c41c2102c000d801c0c1140c50300d035507254274109100342d035100315488130210490a10b10340c14600c0d0385448001240b00c04d8149038000c602c84081154000c01000320f040794201403401868080b0700c66983e001109441c4021400000344400c1c03000980c411104600c3e0180c503450600d070316581d10030030a40d110b0f00382a070300c04a584125030001425401c0050095054500228051031550100421a5042e03800b80072000000c01030f198040e60404141c00080350541000074265941f080412098492190b0050340144005480f810890111440206407480300b000c80f140d544d02d410003241070010701054045c1307540c0a0f20042041c05280c2c030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 120255134 1250 120253884 120253897
    0x190806070f09090e031c09020d0b0c0d0c0c2001051e090909031312021f0309060e0d0e060a091e081c0e040b06030112020d1202070513050c040b 63
    0x15007080a140d5820f5640121048050003000030b0b000040c240802e6042103102e4004544400010000b02400b54001981d48003154002408240100001240c0c001440c1c1612496a40d83d1414400d59a040d40020104080060111000084401c408040001c902500c20141106860300e51400314800704d07003040e1851040c2c400464000030003406c800c645031907100e030703020300381031002103486200016007900300c066950003441c0141c0d410905200581c0d02e50005c2c01010341007591103071008900d0401100900008038002d03080d2401c00c00c00009414000070300403800d007451b69800b12210703c88805c02440b40304074243e40000504400003070022900590228441e0300d032007009095100e80d04c2e0383c40b034240000041c0000f1808503220584071341540000030030b405900c046604001541035440002c405000600500d801108814a580c04549911300307071000258016100e5000e0036045117000303540d000301d80541805030010f0300c507010060009004280c0244036070036905041070700708801062640c003c00c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 120256384 1250 120255134 120255137
    0x114030c030109050a0c080d0807050c0a020301050103080417010501030807032601031b05030f0d050a05041e050102070e040507050913060c0228020d02090406090c080705190806070f 80
    0x21148112903907800d2140009841c4120003074409021141400c180c2040c1e5a4006034180e04080311461445900140c415800b010b00c0c140b080c0c82c0c400c0380b4116440c0000042009425604c6c00c1c00201c140210340000d00111650040700b0030900c0c00080e201c50a17500281700042020600744000b0001a006001081c43c024500b060221a01000000c7d40480407007070b4000e441c40c1e00640021050708100c40c0070321001d410b055008180d4241d0400c0701035503d0040b900d400e4204000410700b1003d461081d422a402000f54039504041c036240202e05100a00c42c034440c2c58003612840000181405208900320702c100d40010140c040a842d01c2c090000d8114020580000c03c0d0a500d4200000340302803007429101b030359a60040076015205c0316000301d4180000000b983c2800060720010059071100000d800040c0d040d15030055589072480c0c404080e01c0c0c0000020701d2980e082c80b0100301c841c000140b16003182c00c01c45c1c0e9440d5600e07520b0450750000e101d42c0928031154111000251095020300305000b005900b5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 120257634 1250 120256384 120256393
    0xf0c030c010621020109090e0f0d0c03120b060d1a0d050c040e06010501090312020705090411010f0509060421061d011103042f060c0106030c0b04080c090403170c030a0f14011403 78
    0x40d140c4003030800102b203202c440441c064400071000d00d5404080803280205480003040700f22071000c0000c1040c0180d012504c003868540280c02e050004600e4400380d42d80e00941210754414451600325211038144c3c4403240114a07050803200d9400001682d42e040380d8040e1544494141591180a24240003200c2c040640c41103580005640e155040010300c564003c503000380a11080c0300006060b014001822410810103000203a0321707641d4101124100d0703598018123601d8540007040c0308050580c0c5800030301080d1402c8051100c5401c00340b40e509540a40b070000b002144000031950841d40810780703018040c0c40c44042c0790144c0c1c00c1c1802c415070312002c0c1142e0340980800d40740c001804550200605030b0559448410801c104801107620a02501c0c00019940c10541010140d80d501c421281549201716041000700302803500661741c601d2f07600c0007000008498076101d45100301a5000f82c500b21840d0f490481c880824100c507100f80104007111844042599282c100380c1d6182150904040e50706005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 120258884 1250 120257634 120257653
    0x1110a2307120905040f09030206061011060705070b010f0f050d110a0305030a020c03281a0c09010e040b0102150601050f0c071a0c070302060f0c030c010621020109090e 74
    0x400c040b039503140d107410760359400e6030ba080c441030000380c030044188020345604040d50307030002940210345940d01a1040d60745417080385240364111160044400282e150307010300700074000c0c82170b440b00007005804c0c0907541c94481070366030301d03501c1005000a01c00d64142c4000050140054581620303c0c0140c1409000d465101015081c000f580103020795204031140e500004203508829014462091201405c0b0040c00c10020120180000c0480b0303900003115004200b00c80c241003050318070802c103421505643c9440a442c19801060041d40141a5240451800c00082c0b40918241c040c1c441c0c0080c06a0181503c10451021203214141c040c2c00d890500005010440b01e030240c0c00e0103070002e880c501c001460f85038500b05108503402103109004c071007010200030118020000141d480100d903410707104513130361343c1d105810949580120304042e6014000002c1d003c00480e4150450030581c1e0546144426540c4070040300d104c680d015040003408100429820850004103505c03410b100c2d1103c08c00c0c2c0e83e1000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 120260134 1250 120258884 120258893
    0x903010507120b030102070c0302040e01020f0d05010e061020031b0703020f04020301150c06020f03090a03020c01021b06030c07080f07030e0409031d01020a0209010b040801110a2307 80
    0xc1040310721500048400000d00e0a80030940104114160141e0003145404541d4440d00c00300501400080c3c0110746541c07082001000c01d50480d000a00f02460050f203c2160f6103208010308801c1c8600c0c5a00c0440c40c01203811841c20504844c07113501952119072800202051001119512041c00e00003404240710891b840c030640c41c6080f010320311200142108500b588108442c141680844030300031441840180b141d0710210280c1506030340c69061400c2c1104003440c00f071001e84629a9900b0310b4602c0030007842030400c000110311444911175026140102505001282d03203a400364550f01504c0d2004030001c0321402d002c0020368002c0c03103410845240651989400c00a9403080701c0b840c01c4c0d80c1c8001081c01c241a071183c03400c1010102190700348605a45505c0c014041d1303a00d56150220304445802107003007680200014452b40c4e50207421070355203603511031003440640c01030b12455017954200302c1407804003280c6200301e07004103200307803034085041920004001c0382c0b003151081d0303e041c0d074001c01c4040d0104 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 120261384 1250 120260134 120260141
    0x30304090905010518030a0c05033a05060915011b0311070605040f150c050a05071a0c06130309030c0e06120a030906030203191a2b02060d02090301 65
    0x40120035030214004109151030340c212407004041001d24a0308071003513400c19501108446442a162500e1030a945490038054114810103c0c4848804202132000035a00c0304901d00c92101c0703d1030020944170039081c82d00541914821142c1e9130b8005a944001143c4440030110b16100c810185406218420b40111442c103040c1d11200c2a004112402500741a540b810003d00010303200307a10b445820030f440d11041c2c0e01d480200d03000b54400d07112440e480d00700187c4520480c00c500340d04141107940d090032600f8010b4541407140625100b1a0000034440b100440c02c0040311001004240180041d54961590f4200f80080500440400c03842420000c04200048120809404107200703014003400c0c0481008446c2c00400c410008a400c01908240441d07088043d1400b1590681400742c1c0c0c81c0d60300d543e20380303060300440c460b540c840d89003103c021101d103c0c04c1c0b102c256604050340d15a41c4400c8882103e504621b0380d54034200640d07003445c1c1043c014200700d0050100031030070650242c24840040000ba0a4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 120262634 1250 120261384 120261389
    0x305030309060907050a0e070806040f0207060605101d0906120604050f1006061d060c0d02060406061a1e0706060b0c0d0509030d0315050306010308030a0606090e070c03090302030304 80
    0x342d00c05010700400380c80c1840f504001305130444411858510b07242d04180d180e80c1c010a0310f000d0102d40b8000a001b0f8540386c215121030000b01c0c1045681d40c03180d02d0100000c0c03405001d400d00070b07001d00300f105e01942e001c1c18004030955500500f9507107005009007000b000141c000e10641d00840240180210f10f034040100311302841c41789001c1c0100703d995040103480c010103000c0d01c9041074104401001100d41081d00c002d0440c000c8411141d24910301c40c003044041c45455890311062180c0100e10140907408680d41d40104e220f11070034400140c0d142d848000300280b400d0b8401d4901001c1000084504412402034030900c1082d41c690304118154031200b040703800c03590042c44446e400003400740c0c00580a000c4480300380340d982480d604201160011955480c035101c103074014596152a510070240030603212800070a00101181c04540e181e10340250290803c0d60015030306818808080744289c0507008490688922000100e902d40d0740c214100c0304449110f00550038001340c49000b1000d41c90520040c8007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 120263884 1250 120262634 120262651
    0x60312040305280218071404060e01080901140c07060e01060b0a02010b04050405120702060417030405010f050c0a0f0602070c081b010c020a0303050a200109140606090a1503050303 79
    0x641025005900d518103001c01d410f1010000c503281c000d006030360310703443c15079108218101c0003529640c02c1c10503112130044041008007c180402c3c0066246d81c01000308028003400c2e61500d2075500ca90362190300740c40c013110594806401d11000100a0031040c3c0103454024055a00851f00c20021007100d400c40d10580c200e182a6200098080142502405120b11000065408110b17525154841351749841d0702c040c0f242240e501c00030f2041c06550300c3c1c0c002d44024001d11401d40b481315080801540c0d0340d60042c40b07400d000c40c00107041300040601840691f0326414245000d400c28020f030f0b83d0b50f45e4840001d00030407144a9420302481e00420b86128680000e171001a0040c00740a0300c1e92021680d00c000518050b040046641a00c0c1c010b07219609224101c03035040c10800e807948101c40090752040700c022440d0040380752402881681d000150404c3d26040d0180b0001d00b001403c4182c0d1b19141c1c1c0046500c0341c0c000741c0e0b20020504440d440c0d403104041100c1c68486220541e01c1e0340d00d16040d540141c481e0708 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 120265134 1250 120263884 120263893
    0x90e0601050103111c110d020d0e060c03040809090403120510050909011125050a0302030702092211040605030d09050909060601020d0305040609080a12060e060102070905060312040305 81
    0x99940c0522540510a404d40912410248200c0242614900c4010101c961a446140d00901846400103803896000c00c8481507444041c0d00d60748100030015140c2c02e6134a03102c0d00020070030100031001284e00541d04520b13058605991101401214040984114200141154101c0100050b072140700d002d00e81008204106034504420480099000340a002142c0d241c12103030302070000000c0894844021900c805410850f44a0a0503540004000c01078164042c864400040560100003040030074400c40b03071022252a4080242200c48420001100140034451210040b445808101d40307128401040401c07002d072114082810690888040c10206803090340901192500d10002c07540f20b0b14502c0180100d18010340002d64420f101e000210030305556002250a12003160008101250040759166940354800d9008001341d0564800401c400e152000100d002c1e2440e02119004060590040c048a420000d80c01c0040002070b10702d691620503c41100200786400014000550040d0003a2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 120266384 1250 120265134 120265139
    0x1b0b03040308060a0906060c0201031d01050723070308040209181f060b13170703061b11010902090c0a05090411091305062b050a05030310080f0604030315090e0601 72
    0x1300000f5103e4000400d0300b810300e6800e00c89107500450174501c00e0340901e004503014490002e010015075003401c144001c0d50a1008206421750800c0140903407441032603240740c18000303154040041d8055031310300800184600b8041405454400000703a000300c490003003482c0d01000301400900c0d140508031144c241104600f44100d07800740c9482648000c1c0880c58400d45000003070140c55039040040c3c000c201c1c500e01e03246c00044c40c000081000c01c1c00b556020b5810880c000340c082d1a80d00c00300490401c030000a108003240e1880c40c00601544904941c0030300000c086441e810000300c420707044401a0400c000d0140003031384241e600d034015050006180d5901903601d900b40000e2080513240070b00341c400110700f0b040601945172107101d4011440e24121565540e9210b0304c0e2504000c0b980280b81c060503d00c01c845240c03082c05000310046008280205800484507582c0424940701c1c000c14241c14203070340001e80040c002c00c1c0a9000211000c1c6000c1150008a40310005901140c01035110480d0360b40c00000103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 120267634 1250 120266384 120266389
    0x306040e0f0a140c010801031110110609010501141f030507050909010e01081614061c020703031506210c09030203070602060f0a090f0f02040609090515010b070b041b0b0304030806 79
    0x135150082c0080c45c0c182d00d65810350329030520071401c21800030f0240c5600850005034512a80c0e0302d800780603450054a200342454000a80a4042030086a0f0303142210340b0a01c1c55454a402c1c83c0c501a80c4848980041986e407000a0380240b030028000002d000007040058056601c025856001c2c18054606d00743d1541415070302071520b00030680508c42000450021301190b040c01120341040036040300c420707a0724a1081c0c60070702501c01c0c8100c0081c116001080d110704060701030b045001c04070303c201411047c080d0b03100011a0301440c07021640c1101000784868031036108860300882c52551240c10044440b43e0b403980400c1c039042c1a0780c003d00040e0000c1d400d005211884100741c13504826045014081400c4546885405e0b0f007c0360402070054284040403400c6445075042000208100315040040f00c1d002d040550302c41007000510110781040c3d034004286900c24600f07983c1c030507801002160403581c0f10307540c8401044410503000360004802070300003018940710300114410340c841e60b110a11810400c00303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 120268884 1250 120267634 120267643
    0x6070308091501030b040b04023f010b1e041b020d081003031715040f0b09101208070602040b0d0e0105060108060123090a0609030b07140306040e0f0a14 67
    0x40b20b00400000010408035000ba540b540d00550040b04c650340c15202d52000842010040c9440080109004440300d0310300500303442c440117554403000d50200850600c28503800c952051540350780c480c50103001e014401d100719030301ca40c0054000e4000103591001c50441d003024044500d0030300051f409100040c025907405410340350001c0203000791016481c01c507507015228440001181445503050700000b101c81500310807240f000340e000380040240001c680b9644000c0c0c074400d90503902480d03014011401d280f115840b2881110038148070f58011084036580c8860b25032000c101520025028840805d83c015490001c0c00d42da040070000003580d07207051084600703490740144018184030183c0100803081c2d8000d0344041507814450148081481030a0b81d100f9503005d4102016002800e02901085090300010020180d0340603103e8280c0c541d482e85c0301181c40f085540005623000c4006c0c0085205030409401c01c600c203042c03500540c0c0c0e04003040b02e440751500581c0c2c0000e0710010000c5c401001c084c0014003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 120270134 1250 120268884 120268903
    0x180e0c2814030d050d02070b01031b060e0603180a050d030f05010501110d031d0312010906170714010c080c1b0409050712020a0803030f070e0d021f0e0607030809 71
    0x41107200d19050980080e032100700c1c000c685024030100141c07030341d0f01c10801d50480318032031360000e80b00010b03503141e0500766182e104101529001404084020502c2d40c041c5a208800e030328000d0034249035585110004117012400701004000b441032a251a000a40500a02c0021050381d0b40000b11203601805a100ba40c90690001e0305203e0000b1100c200401c0104441ca040c2c6014100428146c0041021a0706100d110074200000c2c040071030f0079000e5052008045048a040000602030170b5128400b44051118603100c4541c2c550100800f040030700c1540c48000d0860b0414104440c40d0400b540b03511907240e00024144020703402c05010f4850794802a00c1000920340e0030b450400038071409076501359488180e03001d00b1241c1031b91002ea140440d91004403c001810079201502e4482c20150018000e001c016984580415007208600150b42411003200710616001007825140440005442030240b80b003440000c02c1041c451000c1e0029143d41c8000c1455512070b582c2c0c143c49113020b044450802c1000c8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 120271384 1250 120270134 120270149
    0x100c12110a030905030f0a0e1003050c041e05060301060302070507060503010f090e01021b0a030e030c0901090b01090801062309010b09120c03070303080103110406180e0c28 76
    0x3490410540a018050340c504a006081c00034480c3d40c20f0070210319602408641e901a06000285030301d04a41c8801c00d81c0031150240d4614109070300300742e01501520000ca403165080e2806204c10440c00c0444445246201610180040360541301c50101711960f009030425400b080d0009030402c1000400c000c06801000710749090750665042901a120b0f10b01c1c03078820500000c0c0c842d0710040205200307504070f54001847d404040907003081d520b010750300d401c4208800e601044100020014508020030359140c40c440003084280140c0c00e010149008080c2070b09a0742c1003082a90020542074400d20602d0090010b40520401132500c0d108000d414501070002c450140540c00300411042c5e60542c10303a209107034100d600c1a1048080c0040900d0b160b410614140d0520801e01e0000a00d40c2240009041e00d001d00130005016582d02d00b407105840080c8940c2d41c4030b0400c1104503090071510342c06400c0304658a419038000e050384500003498039102000d040c50081001c041148013a2101c2d841e00010901d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 120272634 1250 120271384 120271391
    0x40206181e2103040b071e1a07080c0d020307110f1608031303020402070f0b0a0f0501050306090703021005160501050f09150103080f0919140105161211100c12 70
    0xd00207255100d00403481403104040340406d858081040300304100070054048524224030924504140e69110090400c2c910030703000d10301c04a2245032081440c648070381d601c0400c580c07134002003000e12002580010036450801c00960301d0240e0b00b4005102c50190600e90b00300030401128440c014400c1c51a11f1f50041c4100e600400c440c440c440c0c10a030410003180c1d011203005896185a007401103100450031002060700e903840040003846032150f0300c10196074008500c2041aa070700c0da000e160780c540080e12850340c150301101040005242c00c10f13106d29014a6450301030f04107201400d0342801401054000c403000e035120010044c08411040c0b40e6070744211641d005051413128407000389403007181030101400d69130000403001145c0811104032020000d020b4508003203001d05036801c261070311031070007860b4084544034400b8900750b1181080d505440c1d00c1d9140345d101c03004981d60302d4014081c4a5490b0b01840017140850b28100d20600c9158415002244081000800c00100620203290690100b01d510314 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 120273884 1250 120272634 120272689
    0x1406010f170c031f080304060315050d0b061c06060e0f01030309060f20060f0a0e0c01201e0708010504081204060b0406081509060708040206181e 64
    0xd401c045400042c2c107080203a49459800c0d5800101082100b03036010400103200020380454004010001c540066504000c1e0021a00180c8150006807044a40c0000e010440c0c0d400304141e600d00c2900002c0040803101204000c40b1400300189081a00741c2e1050796442041248080c0c4540e8664405604141c541c1d441d81980d50160054009028a008001080719881c0945002d510301c480040c1e45190340c540d03450100c9c4d400c00d6943c0d1085503840c0040a01001041c523419a90003400c02c12a8040040c1c030400c4c0b003500044801c2e0001c3d15569210008806042c40740365000d1002c452000d1098a01d1507480c44c541541502c1c00b40c159000b00d0660703140104000118070924140c4018040300d240340302e0140c480c3e0812001405807000c4060f44203282c03020003e0780747c1e80000c0b1007008146201c1e01c28650b644010300d241e1550806ca480c900490030b400002401407a21742c5c010116010700500030341c02d400c0d050011405400c018101c400340681d40c20607582c114136203089040394446210084180252 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 120275134 1250 120273884 120273917
    0x20717040e0f0703090209190f05062211030a0b0102190c09090201020312010f0f0f030c05010e13020c07031a070c080a020106090f020403030e060406020c1908011406010f 75
    0x107000901118082807214045501180b10b0b410a041403070b0020140002414105607104240c2103800c0b01e01c3c101ca2900c4039100c004c0b2020b0090314801ca0b40141001d04075012004031701007044400c0a01500740d6664441d0404041c200d4018501442c006440001c03004052000640342500c0b407160000a440382e110603a00082102c010842690047c2c90085502651440140d19601403007100607403202c41c420011543c1c1e00701004200072114030301403040d03203a50383d00300c94007200806d40406800d6801c250340610842d4081c0303140412800c405402c1d800c482c100c000e00c101c01c0340c204401c40e1802d60071004040052001c0c906800150380000541e12029081c1228050178019007540010911180071441f8082c10b8001e603c114000c180c14103040c0000c2035025001e000030350150000f1400b00c0c480c0d201024060801d48255401d848054005025004840f01044001d1901103a00c111158000001080300502806520400c030b0a2940e02c1405091400024050100d410782078030810085030740140c00d41 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 120276384 1250 120275134 120275159
    0xb13060207030b0c07021813200321090307081b15090d0302120d090c0806041203020d0603080406051206030c030a0609050106030204050c03090d081501030e160902071704 75
    0x940081c60290b0390071203031007c01c0c500003c01801481292504c0104043c0415510070828104d03c15108021100110102140d4545102c503000d9010f50040b0b0030b116400340c0039100484101e10401815040011601c0040d00e0210107420494080c0c000100b002d00310501c076103030201850000c4880c610442c425a1408020340501844a445050701031215000e045c02408414510032030504039a41c1c60b010b0307041c9c00c400750489100840b840c0481c00000140c000000c41e0b01409254480e040704028442d03420100d01a4220600350340c481c50303440380f0020002e289130000384003d00d02a11166215030150083c4e02e4001c1000742043e0003600140c1101300999004260007a0241e44004c00281c0350040b40cc1c050b0040590f0341000303404c00c0c40c1006111018002c0c8015610401003074040f00c0c022540a442140c1004058860b40f440420300f00004910758040d0b0040134940200d1821500364031354411881c180d0319030a030300c0f0481060b40000d80106015141c810045030104089505260038074011320b10010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 120277634 1250 120276384 120276391
    0x1050307140a09091b020f0d0203070b09100203010f090b0d050c01180905040c03210903020906060c0714130b060406140409020309060a0e0109030e0111010f060b13060207030b 77
    0x80d4440024042e400718081c01c110b101800502e4020001c482640d40c4011040140b800e00720094821811107984000300028910201072484d8081c5003099034941e40c8a000420150031100c4a01400420345003000e400d1000c0e600804030742c04403401c1e2270710b4001c0c082c2c01c641e040341c0380d075000748000103c03000450310000b00031034504020328041e1264050b1000840d0000381640220388030b40c0c107144c280b209110450500000343c90052100c01040c0010388501105411801c0749100415040041080903240000707116a0255010707081d1032034007141d90501410150aa0484230301501201052510f0f030612034000e4000e071203800401c000903048000002d480c0d001c1c0740310300420080c000b20811481c0180301c0c151001001c128901799243e081c403112164503000f0840b101c960007841c2c92501d481940050041d52541c0341c064487c0d00d0001203030710044070032600b0300d41031019035034880c006c0d0201e41c0380c603204140060100b1120302e5103400351041c030512001d0b03442d4004401c41d0300429061001c6080001031540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 120278884 1250 120277634 120277667
    0x1509030a080a0302040503070810050c0c1506010507021315080f06060415080303240423070e030a0c050a0b04050a060c0f0803010308120a02040b07020d1403130f0501050307 76
    0xb10b50003141c070101c010b80302d103400454160180703140000b10a0340002e4080d401e80801c0c1ca0a000782e030f071002034540040c002d40b48069102d80c40321540031844442500d8032900002e061600c035187c42555000b04114900411410300d0040e920700702400038921058030040503001d414003820010a002c030000c0d0b03907408090802c0e03100d55550176a408070402541011401840301800380c82e120301e4207000443d0007605030300400d250345004072540c0d2454501849480b0340f80d03a085240b03070018400e034550825000c8000f0200f038240720700c8105440c1a603a0070400d0002c3c107441103007002c07d0513041000303214501200b988803214528080c07000303218a59440c100b07441034411a07d030203001401c85081103180780e801000046c21044001001000303001014004040345170032000414580d4668540070f43c101d11030b0744103081e1010024046040103160610783e034940c0501a811031015181d580311004d040d54045511341d054041d02d41000c0100d14540c41071900108001d003055130552030401005020142a08050907 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 120280134 1250 120278884 120278887
    0x5161109220b1317301302040f05010b0403021203031b0f0f03100821180f060c0a030f080f0a020f1c06090605090114150403050a111509030a08 63
    0x161120940b50401c4102604500702c449101d410071025071455116501700390b42d2540014100445081c0c10003100d03055001d41d51010503581e11101d08030504038260300103d030b010f5101c0a20708201c1410f8000d950180540c2c50a96545070300d144100808c2515060070000c0a81080c13041144100c8807440c428511440041c00c1d075540e072503040110015100d5401d10043e11440030050144e4a03444090071820384070340c001210960320784c90310202060006d404440307100d900d0401030700145a01c907140b010190400a0f0941440c00c2c1e5000015000da008000c0d00c00301e607800544041c05040d031102c11810301c07824a041000396410f100e5441d549010000300b0000d01642c001506140165104007101e6004000310f540039140c1500d580594040d000074801c107020b050500c40049402e151a41c1034604996040e06800e4580c04d0f10410300107140c0380d1910302e1804a105120020100c1c40030300490030fa2911900030a411804018100442500b10f41c9584069032003d014400898a0002c0c02144440e00000340030b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 120281384 1250 120280134 120280141
    0x6030207020102120d06030c050603040c092c01020703170408030f2e090f0b010806040b03010e070b091c02090f0402120a0501140f0c0d0c05161109220b 67
    0x50b85405140c051003410a030300002d8044505c040c641c0124160b0b0300c5440290300c1241c2e14000c01440d40030507a006070000c0c1400e541006107815541c0030501050109402502600e02260b41305064940380f41c2800550b500010050101030b44401104010ba0b140310a581240c28140c4032003c0d14000180300041400800c00424940d003040f591000c14922218200150f02c148400c24640c1003601d40b16500703c0c68204072100d0358000203409404070618042c0d40b0000d10303550380d10402010708800c00d09030782c165594001c1c030006010103102100160609002550743c481c554814022540e04980011001076801800d0740016521108000e810603004120b01040c1d803074900000b82412401c0e0481c100e98400d81c020201084019001300300b1801030010761480c150b4601031640b90b14801210070280d402000c02c03580c501990207a114442c2400f01c1c0c5405130800d82e0030655441d56115421069809001c07003d22401c40303161130004554402d01e80c1c540c004001c20080c200c034100c038200ca48000d04d21001030000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 120282634 1250 120281384 120281387
    0x207030b130b070201020705010b0a1401180e010b040609090c0504062019050106050904050d14040807060c050d020d1e030209030d050301050102060f01060c03080606160b0901140c0301060302070201 87
    0x1001c141580101941c0490300b40210080d00075405940101d40c254284a0180c1e841c0c9800e40911007103401844840c5031000317010300111805d508412845400381500302c800b01d691012410603501a206070400f0554480c204280540b80b0b0209610881d901400d24120b07020b10b641c8081900d040b03a100b81000e8040b9030003040c1446c0e4600341d0007018646403164030010585465001e240b54103140c0500000c00c0f5094441081c0030030386000301c90182c016440483d85514262081c03595007106a0900481d0741000d488500751401c0c0348140e800540000c488000c0001171144c28801008892064001454014030051001c0c05510407041001062107100720103580250003501181c103d0a001070540381031820800e030107022900203005035070042c415800058000c0c121000c856041c1c0700c03140c40380b810000307450f6403c540c440001400c0c01d42140742400001c10781c074000008044058070170000e8001c0b03032425002e00d03400c4039482d00f03200000fa600300083c000c0e84440c09044a05455251601503910341a9000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 120283884 1250 120282634 120282661
    0x80c0d030215070f14130b03040c03050d0f08090f060c130f0b07060c1103032a031602060c0403081603050f070501050f01090509250b120108010f09030207030b 70
    0x4003990340c0b14540040009196200f03203c00702585540d12000c00030914414100c5440c0600c2c3c0e8001d110480b1030f9814000000681c001c0c641c07141c440c1440e41c000644941c0c0740c1d0f0170045d40d0001080807461040c5440a91358000b0a43e42e80501150300404d040c1412043e00c0d035450b003002e01700002c8104001201174180e11003144410141c000141900c0f0460f984040146443d8412001940d010340b400b081c2c13102d554428508444100a403500550564903980306042d10202d030490b85030700c3d81a0414034070040349440d801440c0708030400710505001203017070300c400303400c04900520800101c20f080100b40002400c041c00c0c1c8000011540c0b0b0428485010300e01601d65110340c4079000e4040c44041039510030000c0c1500500c0c0b00d5070088840e0180c42e607a50360b5501c1503c40944694034070342c1000f500c0b01100c019108691404441e2214048002a52050405820f50040381c2041000304114014400c000c2d09004800c0b00c1c1e0003012081110310b0b03141d20002d44540351400001d01c20303908000841c4000d0007075035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 120285134 1250 120283884 120283903
    0x40e01060f03060b0f060301030305160f0308040c0e0112170409050c0c0d1d0405040c1505131202060a08091609060302010806090402060a121d0708120301080c0d0302 73
    0x1002001203a40329110041c0d010758610085440c01c1c1000b030600d40c0781c200401c00c40032071000500580c0c216401c60394180c070140c102031085502281c0c07036815000800c2d11a1458100a400707a140e0243c0380c1000e042c042c1d0382c14040e800a0311401d1211004008200a503404441d81c40e4200000205020001e040c500c8180705030f03444a07440034100780500c1101401e0000500000080c0c00460740c04281008080c4d07501c1c000000c15034181c1c82c20301c0d0f103a03040f81419040a0b034814070940440d92525161460000c0da81c5c1c1482556000403004641e511102d1202040b0304041c00601d1148404803183d030340040c4103440b0343c518040c01c200c603003000309505090400104d408034444100102000e0703103030002c401c02004144010b03030028408401264503410030340c1c0d400d8007403070b00038040324940340408400b65031513070700d141c1c805403d140d440384c403009420001524580c42c3c0c60080c2c01b030701c003951404400f649011200681034102d102c04100400254030005400c0d088030500365040c00166241381800e81c14500c911 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 120286384 1250 120285134 120285161
    0x2090a0911040f06020d050d0b010c02030a030908070906080307020f0a0807061d0603130b060303071a060906061303330b03061302010909022203030f02010506180402010e04 76
    0x4820811054072480151007540c06894000c40090360350314040360b0301da6404040c080411410845801c071880650085060b00006041c54a4030003030715400f0031314000c1a11300650004056400502901c1c5040c0540da0042416407010301c80541460312103502c922503104024450003d01c0f50100c0c01c0e40b1740158010041803480d040d00c412554a90020f001c01521502c0c0c0503407410366440858840ca80442aa40070705113040401c100c110003a0b403060f03490b00025107520b9161109008003400208000c43d944060a0400c1c0c8801c40f80c20003200b88181860003070000c41c8030340b805110740b1181c600f00c4640710003100d03080f00180f001c09004108801094104041413001c03200c015421606024040c1c218201c0d84406601f250565510108218040b44220700c000b0b000a095000405c030210b000e801500b101c00014039040303101040603512411241e1a1307442200807800e2400c014203196028401c0d568000415502c0c504a401c0d441450134042c0da0050000b811b00c9010000c01e01c2d9038039194400d281e240c086 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 120287634 1250 120286384 120286391
    0x14010b180307030308160c1109070203040b0c010f0c02071a0306010c0812040c080f03072003010c09090f050c0909190507020703020f03010207211413210308070302090a09 75
    0x1203041c0108442802c81e480307040c00a9000007540b441d44640c50b0b1f412102d410154040107440034004025140784040c1c4081d046100134000891b0384000080104001c40c2080c0000820104c03950401c000d40300690078510564001d010108209800301c4c204448200c5680c4045941c1c2da25100183c0d450801c0042c042d00c06600410303420b00d0358100361b4000e8021805207024600082d070758200590b98040d05200b83d00d03183c106000b40e0001503000003400c1e40128014200c85244c0e41d4100c046400c480035843d032000010500d540410a00d5000d12601100c901c1d995800d100a15210304404068400c2d070a0090054086e000000c07034141e1078010080b405100e0020a101d1410800310003956a107a0340802d0b4420102090340301030500d030500c00c894001c0ea1002040241c60091b466502592403816040414842032241400d880032000e8002c2401c03811450f56184c199003018280352903003c00f403015403001c40e01d032001388011a4000d030841d81d201500c0e00c1c001d42e884074070002140b401c0b07050f03a1200c3d400504 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 120288884 1250 120287634 120287639
    0x20c01050706020c0304090501090509061504020a0c0203060c03010612060b090f0103150323060f0103020f030a05010c0201020a080606070201020606040b041103010306020702040b0d260712030c0e030114010b180307 94
    0x450b178108c54100d4100c400f06000588036010096202e8809890000140c1c030000c15601a6081a170054032900030942000902d400e00c43e004a810b00b0300440d1441d44003c0004014050980c01c070b00c00c11310400c00380c2410000c1a04040080c8010710400d002c1c540304a01312040c103941c0740c0c0700e5044814426035a40b03840480075500d207868071840d82d82070442c0b40f005941802080c060341c00041e030305218250411709640b980e440c5409001c8002c0310313003003010b17018024010400f010030781c240541480c00c2c0155000507510410346c0c200801051001d41030304c2c40b80c0c000b0410744001d40e90028445410441c200d80c0010603050141c000740050034409070000032424040000014000031340d01801c402402070782c003030060303d02c080d0400c0b140709001c0c54010001d11030301d11010030f072040b00e00251150019000280b03150003071030b465202003440440c08403c0040e032610041c4c101c4540c0800b90320347e102800d400a101c0000d641e11540701c4c1000500030240d000c8404103403408071a64075441c51a09020103010f4034041038 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 120290134 1250 120288884 120288899
    0x902070606030209130b0402040926040603050c070b04060c09080a080309060c070213020f0d1d0c040c0f03050603031603170c03061f022109010207080c01020c01050706020c0304 78
    0x341d03510040c1d109518400000b40c01c3d0b4a181d041c4108030b603000710004010355a070380c2048010164204151140008803465041c040f509400c09013a901e1980a4140c48034600380b0000e082d60b40040144d2140e81061083c080014071402c807850700990300200105908088202c01c407481d10060b80704900620640000c0428402040011400340b100901a1145070b910000c98154a00c0794400081d0481040c2ca00304081800941c05403620607224001c1c0ea10348583c094040d02a0b4071a0484000c0c1d01b41c03103900c04418810108000410312509480901008106c24406807102034050424414140c03a10005106940c041c000c03036001d0f545100302821000b00344e0400810000300900040100304807030300231842440c1d035101a607206107001444440922844019140e0100c06025000254800c51440c681c0d01300c012003250203601e1851071907644403820350b400203107803a5242c0e010000940001c50507a070b03281d0707010608041011003800c0580c0d8401c081d00e0020001c0c4500303821403240d070101040102c1c508 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 120291384 1250 120290134 120290141
    0x3120509031c112109010503070302070b0c04090c0809030a0e010507051e07090e1b120106090b0411040503061b0c0f2103072102040801060e040c0e011401051309020706 74
    0x51040d90701310b41840d0b450307018802d00d00303880d48018030040c2018458080e0541c07040008591151003803070050300781b48140d9a007060040c016250300d019002e000c2003c3c0700261041c4110000340f086841c244021341081c241090301ca104400c4c0d40402c1011404120300b840c2d00400c112441564440d080b1000b900c9043e400011089038010113400034000e083d030000c2ea40d00180540b1941280000240610502d50380d01880c00303032107184090340c100d500c24250b1006c010007841454010306070314102044400f031000800080b11011920501d000100b80803e00140c0c400003280e07580b040c41c0341412b8540b034010102d054001d010f00880141248102c108019510340003045800207600c1d190312600810100d403a000c07550f8082213a4400004403450041c1d800843c1c00b000105020020ba0001407400791120b44080c203503406900114000c0030568140700801003a60300800c010007410181188035418003818a4a80c030005040350f0400c00d001c2188480c02c0681002040100040b40c1c0440d5035110794038052001d07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 120292634 1250 120291384 120291407
    0x5150306040c0203070c060e010318060506040c18030b060d080414030c06040605160c0f030c0f050913060504030509090103050a0b091207021e09010b1801050403120509031c 76
    0x9141080307030b01482d0600000546018a9220b94800c0c1400d040c850111f85040c0c5480c05070781015110010400c041c04501c0c040401c850181002042c02d1402c9418007050392600b0b0501c2c4208020150000800700c1503542c1e032420350358841031554054070348600140300c0d0ac0c5001000b403c59080020b002a00401c1710162480b0260b00b9016141c072001300c03c04110450145100b8140410020090002800125050041061320486104d00c00c03940381e645024507891150408c4901000344a010b0002410a104102c024501215202c81d2460854900d840c0c4104050b0010945501ea80120301018042c01c103642a8020203002c030f40f095a500d080071503480641d02d030113544000c090000f0031040d200200d1000c100403da0036001d480e144803036003400703103201000f0040b540003540d951000132580c0d10402c04a000301203880303c40b504d665040303452030030300c20008100a0501004010400c0001c02000d244510b124090810b140c0741d118044c0400d0030880102c0803a46254014266071840070b4005100011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 120293884 1250 120292634 120292639
    0x80c0303070206010509130f0302071e050f040606140a1101051e090f07150903060c0504060929090f0907050c07060305091005041703070c021017010512010605150306 73
    0x3c03079a942c0e09000c0400810f462000c550382e5001c00840c0402c501030742610055201e0310445004075600d130300e0b500c500e4400710b18402210715001010021440e1043c60920b0380d1200315000c002d21480c06501034207000400d03032094900b650110b20b840e001342c02010540d01c0c0320100740080c000c0b491b2010b00c0070b03106801c80c81780d41184904100032039007020000807946032411040b0024802c09041c10b030800c05c2c4540b07190f041800c01500ca9800700024441d401100d801d409143c440d140c541f41400300250205610342c000312006040407007004040b401e142c042e0964800d4400c0d84640c0c070005e02c00842c087c2c0b0340350284250081540700501c2501c6502100030502d00000d5000d444020380c441000320300b9510142c0c0c811400303500c075460b010340c181c050b80d101c1a04203120310341000707203144001070411041d0070031122003000c034110103144410750034101907103828960070740341080004c0c803940054400040c0c10f0080300e005403522040d41600c8103003503011002070035000386041d00c400343c034815001403030f40100ea2890 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 120295134 1250 120293884 120293893
    0x606030609140705030c160b1503060c0d0c0905030a0f0605060f130b03010b090405062505071103010609180203010629090a0308030c030a0c08060a060516080c03030702 74
    0x7070311100c42d01c02c903916251000c08164460b101c22030211503540000e8140002c40c4403c0052042c00b801e141d40400d25a48070b034a918400b85001c0c0008140c901d54911854080e80041c82001040618001281d82c8000200c000280708404103608903000101c07600059058446c480c1d415050020140c40c1682040c030880085c089a500c100501c07582c580d44000854020b04180e40084070302d01c440e0400412600e01800020340d9485d407200158078a01e003a6825504c582109003400b00b0480e1821800000c100c02c0c0408128090754114000d04c0c0340306820014120344080440714a440c0e03070a41040004148840302480b080002c08011083c00c010300c00704a00c00d618118000528150310422900d0302841c0c010160040c00e080304110705281d00000d8501c1e84040c3c06c0701c012001030f407154041d50041c809114141c1c1c2f00c0c900f00b04900121000c4041500900c07641400300080c543c0c0b0303c41da04080d40d0a44c68201d455483c8495082e880040d00800100720f1100864092900b41e00000a52711500296088a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 120296384 1250 120295134 120295139
    0x121e0307122d0c0b0a0f09140d0e0a030308042f1804050601030209250f08060a0509010b0703020708100902130204030b0406050403050d0c0923090f06060706090606060306 75
    0x22400b12089102d82e20110307002541c0c0f100030032560300c0100e070301c8542c644d00030480e0070184402c00c00b1203600100c02c8680c03140c900f24400154808000c501080307071003400e0101c0181e2a20b00003900c084094400102000070340c1002404000d0713000074102150243c015000c6080d491a50880148a9101d070114040c81c02195003810070040c81c00e46500454010000c1d1509900b180c080c000d03803400040040c85000001d60707241c41a20607500300500103407501e03501e048240f0983c0d40001c140341c1b0090595413041c0040c0380184816954604424112000101800d41c2c40410f858140e040452035801000310f03000e210805184501903400644402c1c1c400c82c0c24103d00d0f4940c02c6034000328001d500000d0080c006e176800003000508540c0c0320300d400500034180755042400449010781555008184031000501d03054040294403e4102c22600b020641080b080c1142400404114042c000411b400e404007071b000045060390310b070300e42190000d5402c000d05002c00109401d0880144c8141c0c0f0400c0006854000c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 120297634 1250 120296384 120296447
    0x20307060f2c090405030f1801080f0402010f0f020f0a0804030201030e07060903120908060703060305060c0c06190b060703030524130902030705120f0c121e030712 72
    0x8005410b0b031000c040d411560600301c140301c1c600700c000b001110948000c0180c89440c00c0568043c01c081c0a0381410150f5880d92000010200c600140c080c84032140a4018400103030380107401403480d510645025003803655000d004900e849011001003045024044160042c45141c400420640303000703072028007041e003c5400059491045103c1c2d1030005501c80700a10014103161100104088146400301c3c02540395640541000d4054403000701081d03030380008004000702482515805840342199504244840c01c80c07940b075540003020040c2940601f811060b10a440794454040034801400c0540c85280d2458080c00614058403c0005c00d0340604080442d05140804003840200190540e5065100c541052000d0001501c2c1241e260041610100b02c0351551001c03c0134501c01d41c8010b0440d90503210b00c40341440110301425010f00004024a440000f0010b0045003000c448480b01c0903105441020f00d055003d803150041600d80b0442c070707210411b40e0010f4070300004081c0340403030300340c41d03020a00 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 120298884 1250 120297634 120297677
    0xd0804030203280311010603061d0d0306050312090301021317061b09061c110706060e0606120709030204020d0b041805120d1d0f06010902040803040b03040f020307060f 74
    0x240e040000030803803200c80000c0c860030800100444a07000811065141d82e2071504ad6013100c9001c4884081450303000d02c1071a4204151703003468205040400c402400c3c00080380d100e01d002a0a6109010001383c02d1030a52402d50440d1444010641040440364450300081d11030401441d000401d4032800c800324068415420310401c101c1c0320080c9081c40d0060341401e2001d25000064082c40040c5000150020781e01b00d03004103180c5d00030580354560baa0303005143c518200c4100c1d403c68107000d420750f010802d0316201c2d1822a03298ac0f04085503100c1e10360310008100e441541f1500300a4015001189030078000000b030300b05051005040b1000c0c0b0240d0601c40701c01c0c500001c404006000d42d803050700d0008003401c4c600d0050990b030704c0158010598600d0040c010a0b0226041d10380f41007540120352155614209200c1c803405482040003e624192500061594034000d41c040c25050071400000300d810070030091041620b10f6400307000c1e00c0708656140006881c14850b0700950f4003103011a5a8010903140d200d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 120300134 1250 120298884 120298933
    0x200627010c02034009060b0309060103020103180503040303051c0504031e02010b0d0b040b01050913020f010332091f18081902010c03020c0606010804030e0d0804030203 74
    0x1030003141403004904455180c150308442e2000c44c01d19a01a0455204005001210030208407154860b0203180100da002140c003158810340368030900b401400700c00140403c00ca41103e40903c1c000c101180417101c050102d0b81c0c1d120008140e440001800001c25401030080c14201a07451034910301d00000340d0110041da0011079004000480c2c4e04214512001449403940680c4a503200000384c103408040455185848a50207a44d08001401044104074820f405175001d44015182c881903814010003004c3c0402c154000248074409006080c0f1043e4440da10101c03541e60448080441c40c0b2074008010910b003605c18054100c00b11807c0021814080010512501c4140c4001c2d051145040f0707040300e0080402000c04000d030b54007844200007042a01c1d010742404802c51190003602d40c01010044d00315405000c00009050041c08408520103000c9a240d40c00300080c28101515a00d07803508036103a045a0401d90780c4100320500303100510000c40060070030b41c0d10940c00c0710100420803148044a400d41e0 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 120301384 1250 120300134 120300137
    0x14060f0402010e01081e220807060e0c0a12080d091109090303071706060c010e070e1b0403060e0708031306090909020a060c1a180d0c080a200627010c 66
    0x10706d0001c1488076140a040e50107140020500c3d20b820204484c2460005464020750702c01e10042404024818107104140d100c0c1120300080a044108a01044004101d8030070150003800006060080c0244241260601401150b0030003e4150914003080c1400c0301c001c0d014000c452603c000798008a00200702c80c0078011030f807140201c0020f040700b00210a403004003a80d030805401e00281001510074000c226401c07503407070094402d46080c0707409660041001495075035400541e895002c504410a07003240c0c1502c0d0058008590100d83c1c8464502c3e1802c60350058100e848001003004003071402c40b00850940754590b440d19070440d03903400c1110a0790500c890103540329015040800c40ca9001c0c003004084944141c0328007031034113081100c20080010455004500505500c2881c401002c18000410426001c0c1806c1651404640b113040c000e0150103101003d025660700080c214803d0321240e9250a108030003101c0c05403511002c4800e680041804078640d12251450303100c4403c00602172a00c00c050795 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 120302634 1250 120301384 120301411
    0x60b030606070c030b0f0f07020601060507020d060b0d0b090f21030717040503121e0f0601090803030c09030118050c04050709030210030522020307050d14060f0402010e0108 76
    0x34038040042036400582c086404440800d80040090000350310640319040c0074140707005e00c0c5813100b80c2106003140104034a045400540c0103019070fa030040c0a5840203034054912020311656460400c000745400588240c1c40300c5440400410441c2d0001100d21030301c00c2c03509072100c801100201980e1025a10306c91010052006401030703200b413481014550001051425103860704018030760058140007618165050f0704000b44c0d00c041040c0c1500707001d4110b69003011328103000117103940a48085502503c088882a0140049210b0307a11480e0344001800740c40060b0786d52402d080780e000110703034800f140340f0b40a5400c0c078140d403800c100b01000b5010a9908480a480c444201c20100320080500078501020300c10060000320258660310024030ba40901d41d00c1c00199820710705058801c40309940c0940300402c40c44034a082c010707140803c01c2011640c00740e52010006c0940d2400f8440c000098104401500c200010450401800c90440e40202e0003030704d8405045080c1c0380116160720044905c400505207 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 120303884 1250 120302634 120302641
    0xa080304030f03020102120705120609070c39030b0912071103010f110909010906080a08030606090d03090614031e040609050d021005090106050a05060c0a021008010612060b03 77
    0x9a660b14080d924881e10005251030b038120440024a001500e41c54005003010841004140001034081c2d0400f008aa048400d0314041000a00e40303007038200001c05a100d4800d10002e12005c00b05001c0409042e00d03881a108401d9440c0d00701d41b0341142c0300c29103102c000c0c040803030809240403484d0309403010000843c038902441c0c1c2d05d5050241c6100b0390116050341d81ca0f948554444c481c0e2150212030701c446010b00e90b8500648003000314542d4107800c1101c000d46440e20801c009107002aaa5a10640c81140913440e0740d200d10018440d40244061103810041e001080c1c41010345c4110701000341c03206600d41d04c0c0c035400503803441c0702c190100b191030312070b0300e2103443c22141415108215243e11a11601c408214482c2c0b50b65545d05285800b2051030150f4007440d02d401d001005400303400e600c02d800c0f000810696113040001a030110152240501500700000c1c4000341c900c0c1030109509880d000342030b0121803040340c680104140000d10689002825084600001c1381035030160104403008410850b04545 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 120305134 1250 120303884 120303893
    0x20711010f020f07060507050d03051513020f0c0a0c0b0a0801051210090b0601020705030f0c0f120f10050606070c031b031b030302070e040b0a0506180a0b0f0a08030403 74
    0x1e078544500415071240440308881c0202c02c01c04000a00f5480c1d6880752a00d000740b070514500620b441c0c4840a1504200400901c140002c2e000700c5494401c9480c55083e1510480340c0300244222500302c01c0140c00003c4e0500741840000e03030440200d2160900616890744c1f0a200e4104d802000307182000a0000c0d00104040c1c94140c21080001d1215020f40348200d844a80f92030480f00c02d644200d9058600c6e60402c0190741e01030000000404094020703241c022000c401c00703a01c6d04040c8503c1e610035800d140c55403115444141582d2410701c170b548129100c0151034814aa690400440d1920740603003041c1c0011001c0c10208151005280d0001c1d00c4c40500d811036450040820450303081d00c1c070016400a0010100300205040c4c03116051189010306540d0450500906140203904084600c0824105010004200d0186180c0c00210380e9070010344c9441b100000344014544100342c44440f0076400a20a100a0766400a8524034044aa00c00b40b1601941403180d10b0391a0300c60303285550424401000071a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 120306384 1250 120305134 120305147
    0xf05150d020f0f0c010f060b0a1202250f1712060d29060306100e1603180506070e031f050a060801050c0409151a0702030a021512010902071101 63
    0x20002e6842d0281441c1c3d441d100038105030481e00f0b01c041581c0d140c0c043d800f4110380501c50b54000d000410007107403414510030303809080c04e5018a5032401c01c40e0300040d800d203010102040002da00111081152030a00743e070500e4130308800c8110050310340b000c6004800b201160188200c800042c503550021040c0c0d0703030752800c010b0300c000c0000040c1e44070405c04070442610410100ca200c40024000303000502c1c0e0400074241403030190028031103919607550a070140720150003910055404030b200882c598007500c1e9500d04070040c0c0400d0344000b6007142c0d202e410030704114020131080e208048964030360785500d071100209607440003240c4d6610410784003242010600030507a048030354401c481c4c2c8000f05180c0e5a910000d42100e0049034400c050240100301809001e01a0013598407031901624a598500c1c100024141d500042407004489540001446000c544040c0a44070043c2c1c1c0081500f82c0301c510304c1d44c0c04200e550025242e0711031561180004a9000c03850301c01d5440413a008040c030f0b44032548100064450 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 120307634 1250 120306384 120306397
    0x1806250302150c0a0201050f0c0937050108070e060f0703050f160302060f04170319111b011a010315150c030f0c05060601230c070f05150d02 62
    0x314040c01c51202c44031000040c945001d07180d20890382c0d0f81c03207107040b40c000d00b180c80c003030440c400511b0340c8000e10990481e800c064942c0080111451100c0801842030f5062649803011850200c98008103903000d46181080b1650417200e003030302c0720040c95540c0041121883e00030041c1e00d5003c03009110714246141c0300000b40651600c80d0a10070701c3c0200d510012480e03900301000200c812400340d0603440c00c240e03040c44500d41100304405106a0303418281d03900c81006a0303500005040350808000108001c1e0410600e0780c070b202c18080304000b11070025a103202d80380d106a8030f071200c2c035816104208828005201e00c0712035022802c44500781d4a610780044014003100b4011000601480e10041469000503214001290980e118014009420b10303015007c1d0728130708503503010b009010920902040300403c51307550290b0300340780c10310362003090007000b1210400c000047c0420b54808144002000b0002a1f0741050702c101480803000f80f9545c1080001c43d1580d26105078014009000c000000300468003c1c150 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 120308884 1250 120307634 120307637
    0x60203130206070c06020d090e0c030402130207060c0206090a051c090e1306060509060906040905010608070618080102040b07200d061a060f090f040b100518062503 72
    0x5411456800242c1d450b0090f8006032151203110504108050301001482009405800c00d9181c03d460080f42c2c104902c3d000f04141d00c440f81c0000080d00315640d04a25020a03030b205c14046445000d58200440204801c07941e08001d4030881c004903240e00d20010707603000142c3e80040101070b2443d89061803443c9006145100e0240071080402188a02c941c0c4001072144203a50442c0340b40107004d04001041c1c0312180c2c03005000e14030721003d009194a4501120340d03c040c1c141c401152086840c40c00600501c0181e0186d480d6009800004c030340035a0011742144000381004038441c12a442d82d15031800c17882180714400c043e600c10080f1400103600440351240165440d2411000040000c010038203050250400300d40d450b03075402035508600300b04843c151004030207540190030060552030b06100780c17240c540c18a00c5500c000a4006007503955400c020b14500001e8110400b103035109501410681040031240e410030607040c40d020041c10650b081d100e00b941c00c15224195514102483c0c02d005441c0d181c16070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 120310134 1250 120308884 120308911
    0x60d0201110c030109030216120b0f1b2d0a020616020319030b01030f060303090605090409020d030305180c060301091d07140f0301090b01090e03160b0f06100c060203 73
    0x1c0c034556082c4200f0741c45c40e0080d005401c9078860300104c103810f50010342001440031800700210012402d4249802e81c895401324039a07400d9120100705a0840d002440300c85c0160344002000e00c04007100b221144061402d41c0080007448601c5506050680641c1c0f20440041e07010500080c0e060512040045c68021240107032450001c01141d210802d001e0f840340ea0b00429124044040c107540c2c50321651a2801e80d4480400a460071030b40c0041c041025813140c02c080150200b10181140d54641c000c19407203900500821b5907140510340034000e004101d9100a0140547c060200850b4000c21101280700b07004002c179107560f0901d1004002002050082003002202c44100f10752140c081004074040c0c084e0007214441c0740c3c1340508200d4082000702c5442e0007641812183d00000d44039250213410b651402c10040789030200700d01101e1442c082d28000b902014800d404400510049041c81030141600c0340c2280d42c1a035445003801204200710080700c00003007420b000b0f51302207440b940c055a00310380c1203262031 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 120311384 1250 120310134 120310153
    0x4030209040f0213050109270b071202040b070c0e130812040309091d060108030c030d020a11031602040b010e010c0308060406050310050a0606090501140c0c040501080c1503060d020111 81
    0x3c0c0c0c11034100747c024a140c159100d2120212594803400c051300f14081040b040c0030342d043ca540c3c00d82d5940d0003500c10018000400220100ca22581d01602c000d410144c2c840c0d5100d003100d00b0700d070303000c1c007142e201c1c20318071215440111b16104006800c5085064110440a144c00110300c52007070f19400050003903040290143c1c1c0898841d040f03004101c95003203980710b000043c1659100090500c1c906a01070410b561080259901d00e03c000f205888221048820050b101d0b01e0400040c1d0b501c0481c100e82140d0b501000800c150031344180180d40c04001d000743d50822444410800540d212205c10140301c3c08160310102c600002482a650242c2c004005040442e02c2542c410110746031243c0118101d1486c1c0e00c504c1000710f081200e11491004120340d00e004d6110a103044006006048034400403050346034005503102e46a0340404c070b0f0810102010f03100b0041076035140481501c03040451042403080107401014050680b8003000d803805442d0080610745142c600e5030054911807011031440c2414061700c4050f = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 120312634 1250 120311384 120311419
    0x8070c03020901080109020f060915070204091416230d020a03080c0c13051e1506070c09150b030a0f0906090c06080115170702010902030a0503090f0604030209040f02 73
    0xb00c40c02007622600100d441c2c0c442c0d10400c205582d060340c4180c0034a406116030700c85540c40c480c4100c1c1006c50020000d9603900c140c00481e01802e05141e01074660009211041707056500000e05007981440d5a184143c90360311040411050b082464a070400c010240e42480154030b4445c3c030f0074041c00c4c070003402e0740a003546c0c035529440640c110b0b894000c2d803a04a40c0ca491041c1c00c0c0300c1d440340003880e80c0351b60800c2245800112400700c00c00d0944040708040380700000601c28484030300c83c605030420040109448000342d00d0700801e540510b01505e2801420140c040303004004c003c1c0444103031408004c001d400c5a4800c03181038002c00503051042d0880d520781038114042080c1d40b140c0881d05025410802c1580c0c24404058003116040c0e10050f00c940030061520781c1c10751b00209900080e110680c90303d545842c2d0003801c9024154400c03001c0d40c10b004081403482007040000050000c45e00907540c0051a001803000c02c006400b07544070194000d010710001500003514107661035102c40c4010f0002409a000b90300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 120313884 1250 120312634 120312649
    0x50613050106050a0905060403021804030c050703150f1503061104180207020a050a08030a0e0d051c120e190206040b03010308070201020615130c09080d0201021b0c09010308070c0302 80
    0x41600410000655590150317401520360340600010745019240914590120381040c1e00f0814407a0004c0c01a804101010322410300343d649190080700701c440154681c28080c10340e400a0380300c1080c980c607004021070840b0303490250302480310079403a100c044a4510341382c0c6402b401c4100e035201201c00e01007001191070418505080401e0402041c01612409584180712940a032a040310f80700b40d900b9402080442c0b4008111004040750b4501250300042c40404500059106800207103c0d0180484603c094949103183c0700501c1c840e0355170142c03025a1468400e045810701204898182c0004d807001c0000f132003001010040c01d1003e04200d280590f200354281541d00281c108444004001415000b95039042006035080386001d040c005030840c01d0400640c103110340710003d502440d2208002d041e41d80c0180c0720321004001003401d5541d44509440000c1c001d40c061117801135240a02034812550340e10000e800010182d0103004009140d096031500781140c0c000b980300319003210303400300040016240da10703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 120315134 1250 120313884 120313889
    0x140103021e1908031305010203070b2a0c0f0717030405040e0c0613031109150d0309091b1404081e0c1906021014070507170a0c0302120a050405040506130501 69
    0x1800346450741c1c82d9105603c05e403201070740100e046600502201000c0b64181040c5500450704049581d6888101e030b0b446ca00c4440c034004840401078000c41d401044841c0440d00ea00c195103904107841100c0c1d01c03a01c81c0c03588003a140b042141a540144000d10003030901707512034000300c046da0003202d81ca0381c0a0300000b051a4802d00444000444c441420810070051a80d42000f170101100c0360f1032289013400308090480c501c100c065204031030902007801414080c40c0868081c104901d8140100303004d80c02c0005100c00031054010001d004e0982400020b338070001a501030b104044013070000d546802030655200342040d00034020340c0c01003804010742680c0d0605810700c005111122140482e2a0900c06410801802422504141000c10142c04440c40c4401709038003c0362030405549522440c1007030b07681080c1100692100c56000510261010b41256107010007520035401c07904282092008440180907610b40040031030400d101c140320600d45034100c02d07803004024000e030000569a030351a00980e035080c0d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 120316384 1250 120315134 120315149
    0x50106030f2006070f020103020d060e0108070e010b09040b0a270515101b0c0b180303070507030b0411090a0506120102041415220801140103021e19 65
    0x2400d6004002c20202032449803042c40c01034030720120461002c00c0e003a101e08100180301ea14105003900840e806a07040d56691380c0c002404001558446082d119810700a0142d0b81d200e201d11840001d85850800c922810b0341d24004240d0b007440032840070301010340007020a0aa10400f80c820219221100d10403404101d480d05901c1c1d1402000e0b0a03240c021150054450740121144100421340f0f900d80b0303952083d40340380c03a140020b04400b0400000030b203880903000040c84c82008120002d4070304c00c030401810b1001d001c0903d10700c0680d214010559a4407074840d004049400071b510400c0030514001d1040c0d8428055588118032000d0100003c070364801c12582c13078114641c0c07030007405000d003400140c800990b24900c00841c502418180300060140001e02d045210b84c0f00d00c030034418460103903015506030401801c6814400012420f0010301e00040e8082d2540795031070001c070140e041148225150490f50060000c682c0000d003440d108034a0010035401c550440d802420f00044907013060019001407409 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 120317634 1250 120316384 120316403
    0xc070203031c0c032d060b04030303150e010e01031115030906100503060c0409111e03010602061b0904021b100606080c040303020c06160c1401081f090209030a05010603 74
    0x103400003408840f840040c10080600d40407958651101da01120031540e000b01c5401c154a884005070100504501d41260040301c201150010800d41c06800c40c45031338105002450400780c644515070700b016824421855480450401040800d6231591003000380200504080c038001c511801100b91796206640f8841140d01c41030801c8400c5200c01200c0001d0329046000d0103190512200303440617809140124482d10f035480c0c0080803e01c801500f101d402e07209009440035400c81482031404260424401c14001d40100310010704400c0080410303040307030344042c44414142600941880000e40049000f9454604561204440c0540401801c8050305500d003020400c0d6007002d030010241070001d0490b0300d10040c148421f2001a80200318110600d205607005900c13048480404141030704005406000035403c080080748052091b04008007126003038807a0112521000c1101003104803150604140c0b503881700080c400881c4580007011000c10080440d569045151203007401c44940d980100c400441 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 120318884 1250 120317634 120317677
    0x18050604030305040e100503120d060513050115020c0109060c0503090415060e011803020d0c090207060501050a060e0904080a090306150306052514040b1306020106050d1a0c07020303 80
    0x1491740551010f0b5003d0342c0c0111078689000310341e0711b00264050b04a00c050104006090120705e07406070000f010000c0031071034200100301500005103403e005680a00d5110030813003c0d05400042c200c5881d00041e03650700f040e10300d0050211004220b03103408544500040041e400c899603207000311154600c0c10104408085d107046c4d409401c1c0005895810f0500c00304c51100340c2e8403000c400750b88080780c0e01611000a11445407810b9034500ca0250828841c1d544045007413020710490381d010034180e03001510700405458440e0b0041c0c1c0c40221519000b54044c00e02c80c0050000307200c40c0c020b00355440e81414180c2c8455260382c0c90006840c080080010358280300070041051006902641c1e410110340e0344900c12028030200c1d20f5010035850002041480300f8010303043c0c045100013003124002c02e0f650b0b020b50b07240e03004000f90641c189141d1103840015801d180c4041f070385103000c083c034145165101e43c3c0301000c0c50750a0802c1100c02c0000303081c04400c0c20240100005a10140010540e0307080c0b07071440000024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 120320134 1250 120318884 120318899
    0x40b0307021f06030b010504181502040e130b1b0d090f0c090204080307060e161401080c0c0c0f13020f0318060105011b111f121b1805060403030504 65
    0x20395103060707442d01d5800c0c51000c0000c900380c404061305541c426500401c0001d9440708201d00401e40c0c050040120b2a000400303a0110308940c050700556544590b0350080b40c444074035210078404d001ca0302030602400e02c00882c2d450071030000c1048042c6c8410040380d00305070403a00c9040803220071401c261160056001da460030010701e000d0900c0600020070085050a00f0888802d94074019032400500169441082d81084102002201d190400191303460881c3ca480c0c1aa07117007046816003200740031549010200310f0344042c01c419a001001c5000c010192107510008100703140310489422364002203c0310382030b81c088555000501900c0700d0501400d80d20b00f08510500d158043d0168200e540750001001804113a80c080c0b10964110210407409106510a0030a03c101c00c03d901112540245e603079000f907480c110007010810104140303464851b501000d030342d02c6c8000d0f5000740a03085c02801240392404000d90046000e680c0310004000720341c09045d202c901040c0c0640c010f030800d03404a14003280030041746 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 120321384 1250 120320134 120320173
    0xa031e0905070b0c030f0a020307020a180e010905190c0503030f04150203071101050304020f03011b1404150f12020d0203041e23031c0c021603080a080c040b030702 72
    0xf8101c111419190224000c1c9040c0c80e4041c842040c51120400586810741078806c000307132201c041d00140041e0890356687d041100d203100710711411241070700313000c0078000000d81803040d02c0c1c0c001e400001030400e002c11036041201098100b0401c0350101d002c000e01007071a48040004e0702000b11440b04140e9218148096000501030a954180441d8010050040040d2280c502d060007641c080c20070903201d40715440000e40c195101000d458140d03203444200d80c0300c1e84140c010241c00c1c600544510309080d44281043e642442079005201d00c280000010616083c0320b000990b440c00f0f5589080c10140c2ca0b0110008141d07800103520708020764010080c88144070445150800c001d40e40920016050a90340e203070140c45000c0b101c065203403d15410000100e50091045a0b80d80002e40290041087d00540d10b200504036148400c0052144100301e00042100446400a80350803040d51307820000c4600c42150720344002081c245070207200341320001e0326104120185014150036009814240221030000301e14 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 120322634 1250 120321384 120321389
    0x31206030f030307090b1602040c0f0f0c0b0c07020105090901030516090212130c0503011107110901030f0b04020105070b09030c0f011e020d0603020a03081207020d0807050a031e090507 81
    0x160300100203202c0c0d030355000304001c5c04a440c0c040d0309545500c0d030315400102000b81400c0180d001070400a02070750044d80000c00a81c0318040c0c3d1034401648500d40d00441e684100b0550041031a4a5600070a59100000018054403881454240d00c3c00c038100d0080350400300d007a44111825402070052591104113544500041e140300c0e0f20450503c60002c0c00301920400103043c8190303444c00c03c3c6500041c070207400b0a06014003c007800038002080907020a001d59400f100f02610414606e083e030802c2ca24100b0000c6e8100c07904910310f40501c5180d0b4551600c154000b5104a05100040004900140000010521a10a100c003075621010341104050502c0e0340100e85036002d92500358458010045491194541d812001c40141c6421440450300b0080c2442d81010b58001c940342000000c12503000700500d04408491452602c5447e41178050360f0321110041100c0c04662045e0026403100e01c51005801d40c501c082c1390114480c0031300441d125100f0b407155030310306c0c503251501d01c00000c1c8030081105400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 120323741 1107 120322634 120322663
    0x905010e0f060c0c0103110c03030f0a02130905040210033b0f0304050a0608010509060103110706050108010f14040b0414101817090d0204110c03120603 67
    0x9a40c4200e41e00160001e8100781f02c2980382088042500c6403404031200860035621030507484420b694005140003400c540c00e1001040c040e04030903943d00100003000c400605402d02d40140842da05280e85103c042c50304102d400380200d0300c485084d0314051742d4403010501c01c0d1a40e5002c20150307000c900c071908081c40703290030940801c00c01100810448404460b89009940c0c0e400741525000e50911810740e0282249001a0240d402a0409888060040e00c0309140803040e6540700c0856000381c001942c6a9510b83c03000d00c84001c941b1608100d100d600c80081c0701840d0554a244203510010002009066044940c1c4803110040040b4003109141800900c21001480000c00901e41d24000569101c20300c842e407110040c001e14202d8100f001c01400840701003140380c0901c80641500c00390700c16111010040504002003d0001d00002a100c901917200c504000e010140b826002c40303c2c0c1030303 = true := by decide +kernel

theorem cover : BRFrame.Cov 120143884 120323741 := by
  have h0 := BRFrame.cov_init 120143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 120143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 120143884 ≤ n) (h2 : n < 120323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
