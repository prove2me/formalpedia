-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2917
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:07:41.783993+00:00
-- url     : https://prove2.me/submissions/a341c6bc-2577-4e97-819a-f4af684c8414

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 524460431 ≤ n < 524640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 524461681 1250 524460431 524460463
    0x70c030f12020c061f06050703050711030c030a050c01090e07020a020909010b030f031216120c030f05180c03120417031b06160c1e02030a0203030336 66
    0x500d14407000e21009005a00001c9010310034a010030640300c0e4008040701000e5000ca86013880d10740d56810485583c420090018000380f424416500011110321840070080002401c1d43c451061180c0403030320704058108182d40aa0020f600b140b019600100090083c080d20160905185480b00004e0b54905502100900a044000010b404c245d420f41c0099400034000341900d0f00c5442d4414410f40d41d4011014403c1c00030380308004034460210b0240c8446038002031f6204e058000c0031524514000b00502c10b4041e0505407034008954040e03110344922440b8039461145485141082c044c1d5915001040c100e2074001e50100e41030300d00042c0381206035002c81751000c1050080115180207682540556110321003401200041c6a50102c0c010406c00d10848011071003000c058020b0904850112544201801c0905d44004010340c14418000a48519001038221040300f0340c2503001c00c1c59944112500001e91194122500295844080d050880103001c1d02700c20100d079001d0303001030b207030722a0700620703050 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 524462931 1250 524461681 524461697
    0x3040f120215090d1106010e06060a1404121b050906060c07050a151b150c0216140f010224040c030602040603060e180c01031d071d070c030f 62
    0xd8644200310b4042603000d25040380d42103041c103000d0750341c0d00c0310444660404510510044007060b5000124181200c2d2440c40c0344d13200c3d40741c1c1028408294440401c941c01c0220020106402030182c40c02040100750b061044420095141803072282e84640000c07100c800300d230070081002250381d5041e9050300001d08640c9960b9550820b8802803800103154881a0400d9071604006009881410004e0400c942c82d116404d01240100c01c00744031038208a0f000342508190316401c012220365038059892010940111550345907c02c51001c0740c1201a0300450100b14981c148921a0070201c03036800e40da46081c002001c03c540d00203c01ea00035800c001074907001c42d8a42d030004040c0b00d04014041c0044d03070842001c550311070b02d902c0000c000d80380a01425050105040c01301d4010400c110700e64008015000c060090108000011006842040d181c40c031490f21040c0038615201c0f09000c2180100b030300c0340c0c0d6400c11154440c001c00d03084100400b003005010074800c01102080c0c002491000c1d0105034540105 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 524464181 1250 524462931 524462963
    0x1a15060d0f0614040b01080702060126010e1f09030905040b041e05041b08060708060604150e090705091c050a14010b010e22051005040203190f0203040f 67
    0x925aa00407140054284040010352280e02c0c800048605000d440c2030050000b988015034045c10156081001a03104a004121840c240405000500307062000441030420b990061401d4401381108096150000c070402003031081200300440c4440304164003844402d4140d18017610204041c4101400380351289014461a60303103a00480c1002045140e004c03800c10141400801050101d034101da03078203201c0e2000700610f16414030420842d51004020140c548c4da602c0101ea4114010300f000c1d0b04808140f2000c0707090a16081d18140a42c4240e803010303c8124031030704020300030b60003401703140038041c1c10003251025403035032088801142d00040d0348a490078500d10340685007090901c40a0b0040c00c000340c460708440f03019000f207481c80c0380c00d030b8820b01403141440420040d003401540c1c40511454000703c040b03140c017840d005141d0008040b14410745031a0b590011409036442102d051a1440e80f010044400f43c50b5407060120224042d0400c6003140340594603a400d00035296005000701c45440e016032 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 524465431 1250 524464181 524464207
    0x30201200129010305011a0901031d1f0b0d0b04081e1b010e0303130f060614030d0201020c06010311060c07031202100516080c0f030c04031a1506 64
    0x400310000400802154100c180c2029440410490035160581800450301066210b0f02030701e8161400800e513403580e0484c403440341c21554040c0c0003060500d5101c200a00e9001035011044d4800c5088001521a42400340c2010b81d00c061400507002c0341c280341950902c40b58a892404102ca21350060302c150301034031281000c0403507010340203070146102c881c002000c165403240303401340914800c4411111803484940c040e1034241c070005007604410358014000901003140e900016101c0390f025801303103030320501c0644801d010340f01c4a03000b141c4034207000c001c400c0440c10b040080301482c84451008606204580240c0c60700c910741840050460018034130354598a547e0a012108a08020b0f4216200780782d8901c1c2c449032110001d08030308098004e041c1308c0305000c500b90060600ca0742c1c0044040b02c00202914056422060103003e44000e1442072280a00f0f0204c0719000b103009042406030503840e5031440c50083d0016081201ca00c18072540c0780144010040030004002c64070a044810584070001c0340110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 524466681 1250 524465431 524465477
    0x9060a020705120313140102160b07120e01020a021603030212090112090c0311042f09130603020f040e030a14130f05130203040309140409140313061107030201 70
    0x1880c102400414442ca883d4014460f824070b40c401c6e90000000240000c03442c1c00c03401307500200b2003e103072000c2c00b803c005528043c440d075110617182811083c400d4146a02c4003101c40e000d141e1001a0340c001011340303072260104480e80c4010014a01c240e00c90382140c4d8025226100040604840031010841154603802031149000c14183d46c1c10410007003a0030304000306200c50a00c0244e4919842010700041810980140070000345c0f10302c600c183d081041c0d00704103028560340d101c4001180d8240709071702860b510b41214055a241e4184040390017419801008058108501d10718811450034112410980e000320507614000860b09000080d00e00341d441c5003055100e016414800311078039000114400642c2103d180507601c003500d41000c8407166090201c201d11041e500603020a00250040084950200036206541005800402e075205159518182c07404140e5041d00700380c0001c9183d80c1011001050040204164a00654039200409055490f100c80d030001a04000c482d95030a01350200d140702c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 524467931 1250 524466681 524466703
    0x120406090215031e06010e090901060302121f0c0f0c0201020c030d020f07080109030806100509031b09090c2b050d0201020c0f060708150409020d1b060809060a020705 73
    0x49001c0d086982d000003900d9600c1100c00100710350a0802c1c100800c4610302d9072600c0713180c040e114604884111070070001c007a01d00400c00c0c4503545d00c401c0c01000580310a815144810503030300003007110100c0400b524407400030000f141c0000500d0f10f0491070781d441c3d0001c2c10403502d103031034104843d19004500040b82409003084a19815110310b540801900350b00040030403600a200013070701d500369242d81d8040d0030382c0d01c10030020300012103080225005190090803401c040c01c040c200305160042d094041790078526000640d900d181d4151003000300a0824501323195010740c101001c1c0c581010044005458481113852000c03a03942c840328084000240c060840c076049802600300c564404884900034083c0d8085242410704d4020303c018014010030010b4030900078041c2d07032280011070b6602040001002181d0350a264800d446030b6140003d40c6641c20030b468a5070290005401c01c44120302e0000a00e00c2d268418020003140c40208144202c000c9112608800300d00030250352500c0d11b04105241c0311158403 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 524469181 1250 524467931 524467939
    0x60d140907082404140703120503010f05010c051b122a1021110a0801090e070308030c21010b130b030105090613021e030103021509061204060902 64
    0x2809824580000c5540c01c6942100881d0f00300c0fa004202d01e0403610300050942c950000d08400303d400960a5003100c617241c01c21404035102c0590340e4898040c0e024a9404400100d0400401484409405400040a49400e0900f68614841c1d030385c40590b07540c1c070030300c1103500d0801014803500241d403005100744141d0003079022230310680d0700400b000da44180380649601211412507101089420b00e20f02d202950803094840718201c909041d050840803594a02140140d0b60324152040481c402c00301516082c082ca83d921034066050000321012504000c0c40326803641d00c848410400103a00da400c030795200500e00c0440383c490321046113200703014084421613007500d0190000402c0b900d0480010340102c1580c3c80c5901102c40d61018614010f1100b07002349a008a01c450000710b20b070900340c050104400700394800624020400034000100100000890a0039400100400652500d1444070303810360213001c1e48603c0c060440c40001c106116140c042030601c4030500c0020180802940801446034002e4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 524470431 1250 524469181 524469221
    0x41d060a0b13080106080c061602130501030303020307091a180a090507021b010905010903020616080a0c060b0306100e0a09020d081909060801050d0c1809030f02060f06060d 76
    0xa9007002c0340101c9004500c4250b01c0c0620001d16404001041002e1b010b0281040d40ba0030b1b6441e4150404804148080e608044080c0b150081407010340316243c02103009603001a202e003001d82d4010030b0198154846a0700c9100d406650100344410011200d0049242850350303052036880010a00803501075000107261803800d420842421380118400f840c41d40741109201ca032004000040d203030342c80d190107080c0c0001c940300414001070501000400318184016614007000c01d55640d480c2c12035028008600008010340606000c01502d03010755500c84074110042c1840d440c0000d908580d460844c412000c1040c00c820102c3d14a84450b4030450020381c003c0d007255030121039821f0641171a030000c06030110400300c0401c06c40685120340c0502054a22136650310a90b41d10300010042164045141500d00c43c3c0400302c000f82c1c8e501c078032804000303a910b0014082111075142c1005440c0354180800c3c01c0544d00500c003000401083c0700f040315401907088440d41d44881d69200300e6002086103d0341b81204074215 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 524471681 1250 524470431 524470447
    0x2062215090201120e06010b030c07060606110c0303120f06060d0203010b090a080f0d36090c081302010309140d18060302091c05011104090f05060402041d060a0b 71
    0x81d0800007501e4000e0b00c60700107040c58042168100d40420121003a503030880c40050015004030b0009540001d6000d00380d504112050321080101d684685c0000c001c00c0d105c0c9041481c4407818400e4441a400031005542400040d03501c0c03400b0b450004010501ca0080c1c40002103080e9540c4064035000c041c071368011510f039030f118108407545900070410a44512524140060b03101000a03507110341000c060064052455401c034256005660b12415510b141000050125413140300c086200b982c6008214624000d441c02c03000c0c1e03040719001110075040140290800c40e00a1852140362407196080c80d00180311031050034040c13940c200b01d142d001210300030207501c003c0d041c0c1d01807001503500b245030a0b0f41132000d42d5058150101d106035811076030070171414051124200c00020044001900800c00411005c849881c400c96a61080e007044a0443d80d4424083d401403081c4201070744203505807011031519007080303490680c07403031448241c000411100c0c00082e420385801c5140002001d914003038980b40c400c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 524472931 1250 524471681 524471723
    0x507170a12080603100204061d040f15050405090d0f050904090b150f01021c0503100801050403081905010605070204150e010b0d23010e04030c080f0909100501020622 73
    0xb003580e803a0310030710030160540900d40a510849003212100e484610020945c22a52002c0c221180c1358a030380a07580d2100400340400900035615203601004105030320b642000200002c44002070107002d0264000c80114010319000303030b405a445a82401c086459200a00024018180520008050715454020310900011100e56030900e41811640b10219104003001207a980140002c444c3c03540749810f50700c0c1050780c0030b000110b03007103218111300c0c0d007010fa03c035100740b402d40300140e80440000f00c00e082048a044c0c002303003d0303513032003441036209014075490150000c2080c01081e44c0030b0700c229030b15051081950203e44d0501c0013000081040c0c022507070354503a14803464120502050b907060808554540200356180401c10840819403140400e900f01452800400c80041c13045040c010b070741e513008002c261258081c0061609a10b4950b0b07441c2c1d900c1051002110b80038100c5007011141c0380081c0110380e0042011030340032840c40c0324031401c13001e9042c00e001030318006032001d4002c000412002c8201c0b50 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 524474181 1250 524472931 524472947
    0xc0307080a031b02010510061404080303040c0320010905040e0a0515090f0606100e1801030b010306140402010f080a0902120304140a0b040501080a1d0109060501120507170a12 77
    0x10f5101e064261420706114280d0a903001110039041c105070407801488020702a1520102c0e0340181d541082c10b098444940c10300c1e5a0050320207031807040c07415404000b04030410424a00d2a00c1400907100000e94000028100400b035000e4548280d44905003198030b58010400d504440b90000203d84214a0750180e11030080700036038101140740509417000c02c9101c4001900c5006c1e80014020900d205510003081342d0b80e01900c000950b1040f080a01c80d02020200116a400f031401640c00100951440c50004100c542074400c1d0f03080e01002404201c05030b07030030030404c0111070203505103000b0303079034480110b08028200b4000007513204104500d84d000404000000d0016243d00542240c8484124400c0010b04070181c07183c1c00b21028104018046540300c1c030003c640ac0500c1d240045070f02241440003111a440d840f201a40b20f81d902c607940d50030b01005002c2c0500401030040716440d044070940740c9503100c15160054500c40b00c103407061880b06110030880000310541261455a0408208200a001380c0b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 524475431 1250 524474181 524474201
    0x50105161203050a051509010506030403200102090f01170612030904020403052a0d0f060b06071b05190306090807050f071a0f07031b170a170402030309060c0307080a03 74
    0x9441c010001b40c03101100f007071101c4180700003405600302e603103004100f0407162301c000c000314100030082d00c2d02d2042c80761444542c2c11900320780c0000340e1960401030034000110305101403281080428400c01020721202c039051500f28001b07941031001c22402212152446c403c046586401a00c000b0b400414444082250f5031503e480c1201503508802000f00501465103000516138820750454020001590541e40c4110042c03007150045001507a58000403205c6d007010b81c056a49100b40b1504108a1143d032000d50050501164075202c11220302034540c045980c0c0c0e0000810f52a95544d0240030b2044d40c00030341d15010f80c84001c4564402045640e2038880c00e181c86004441004205180c0b40c0f205a4401c0d10030001560445a0030301f400c64504a030034059200b144081c4c203c1059003100411083c00c1c06c20300500075078103501e0380d440809000401d1700301020740203c288840c0c10b06020040c1c0e4013008031842100111401a200c50040d007155049d4480d00d44001e28070240001d494002e1501504800e03050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 524476681 1250 524475431 524475451
    0xa020c01110d0e0d140a141606020304090e030706390509060a1e080126070302040c05040e010801060e0f040c0512070302060d1b1805010516120305 65
    0x4060325030440c555031502c2c140c1c12004910400b0a5405500300001c0854805008000d0524070a8030710302c1c0182440846032041e9407810070050080030b003903410014454145140d0541900c0285080e4000351a07014500504903041e803103c00c1c000da80d42042083e51503958005208008441907144044054504491600201030104420032243c091071042c0c2c81d0140030b030380c603001c0c0380444560400a182d07000c07104032000c0c00123034038581d200c0725242c019644102c0f005407607518155041038500b1017514100084176286070041d0860f04401c03d8040740325803c0366410740c4c001c00c0035040894190380c580201c0e0000c0d201020b1134000000c201105402081c1141e007041306009507a102d0345039155078004210b801421112a1000411450500b150b108000b104010281c510081c1c40703500043c4d25a0000342203180164580302c00d2483c202c044900380010420604040254001d805031410300c0480d5803150905010000c103041541910040d90f40d08440c2d882104000016417582020b00184804c0d2454011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 524477931 1250 524476681 524476697
    0x5130f12050708131e030f111503090a200102030f1803030a020a1e03080609190c081008060108100e10020d0f060605040518060301140106020f0f070605030109050a09080a020c01 78
    0x150081c200300c0c4001b600d40000112252640c2921103460302c0000b0206c150300040700c030b95440c0c0504002d80165000d1a031140c01360400003582c2c2400d0140f1000c141c840503001d4a01281581b81d6030700042168190080b00c42d0451321a07804c4824682c503241103803ca0f0340c02d400001108107250b94080782c20900d0622404c40389000b012240590303011100041001004030707c1400c0440e003185029400c0c0b036404580310382e548282881103c1d02606403400d625104000c01e402e48203200500c3c400070349200107002c0f04401007000391315000041c0c0c1d8514040030b0003040a5907490040d00701131014807800c2d000114407a001e55413030200030391850007400c01048854009140c0781e8042050b520880c03c071000c0f81c0000340f1105a451911f174404000400181c41c5652540d039402184401c9111240c1d001d000b0300190700a025900403200b101800d215840c100789801d41c018401c2480010f8104040d00e05640e5442d000095079030b1080089030050800b02000707800428040742030340e80c0c0703540054582c19010342a030780d204c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 524479181 1250 524477931 524477969
    0x90b01090909050738040b03040f060603081b01110c0613030e1504090b0103050115030e0a020d1a0c0708070b07020f0111041701060b180d1b0905130f1205070813 71
    0x1005002d02d020747c83d116203007040890301140010139440295030060000060440da65900d81a099100b00044008070484c0311062034960030031b11407d0782c06042d850f0014a8009500849611041f0040c0f00042042043e482d000c1230610840090800840242c00443d80c2011241140c9403900140710315003550f03007001c1400403194031a0082074100e9031080159103c911007800c041d40034145181e004851440307141c0c581800b42ea036102c03070440c4080c01000d0404614140860403990480001d00d1003c450070304000740000680c61104441042e80c00402c5180c05440e150f4080b400c006902c014a8890340c2032a42c900704007000f11004004030b82c0c420296141503511300301d85600365245441010030081051050201c0c80c8640320300481040c00c001e0494800c02a242d03941c0c912071400700101c035500134501005120b214101e01c035044d002500394a9076100215613a98550940210200007000c031580301c454941c0180c014019550182c1d4004441511750f0380319242c41039584542d214034041c1410404500d9 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 524480431 1250 524479181 524479289
    0x10b0310080c0d0b09101a01090519050d03090503010504120e030c180a1104031103011104050d0303110c0f15160801060e030a06060602011401090b010909090507 71
    0xb0002c1da001d01003020000064407840c1d50507000a04903400340c00b50007424032084c41c080c800c1c08002042d68480c01481040b000004094812a81096002e814032105c040911103411640c40c04031001102c0c10200800c00d840e044a81c900c50b40c0c03045030550300340f009110070460f0000144a69101e42ea580e060b520582070308042c0e03112418080150010241141c0840c50601056650343c0b0001e500310208401046526003081c691040e0b005590015560510340c0a500c3c0a000b03e00c44222203888071424542000009459072074400e80090a0581e00e00c042051550420150381902e40031806030f4110300d030001800d40d144c0f2070445005444601c607000054400600d16000003000301c1990b6010320070b038240442030310000104004540d2602c540a030050001e585806018094840d81c0d0020400040350941d001c2d2245040e0002c842060601c40540d07a180d902800400c100c40401c0c202203030303250b200d090080c10044240c00140130b80c03c00c040c1c03001d0300001d641e4401c80418860a201031a0107414640e00c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 524481681 1250 524480431 524480443
    0x3110a03051f0b090909120a050307080105010504050f10230705070503060c0301121110090503010f090224040305070e06090a02131701020c07090e010b01170106110a0506010b031008 80
    0x807810790300c05205608142c10a800780340c0c0d010101d03130112007c010f000d10007000c013508829014400a24008208511240c1c8075040da4018a030030b0900c9800c00c0d0905001591140302c40c0d000600a07540c0c94040500140b003011503044d240c801d01c50100a01c0c1c80808014040d502c2401c0030754031849101800540380c200010200d20500942043c24156428504140805c0c5c00e1054255951141300b1230700344e016a03075a40c491101514a03211120140d05e0002410300f50344520015074400d928009800c8056140e001242c0b849503101d01001f840300e141409590518000c940001c1c040d4400c480e008100d511907035076128029041181c10006907510914501d051344148040000b5444200e42d003000507070140001d050114a900d40003600f130110b0f942c090341c42c4c1440b903407024021a03141c0e19501104803080c4603050040c81c00780380c4110f081d81740c4004203181c1c91061081904003d0351046041e005841884000c0f802544507050750b100b96501c5103000520340054903500d1030908081000545c1a800040c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 524482931 1250 524481681 524481689
    0x10e0d17040209060607061b0311031b0a020a0f0b07031409030f03040614160905010f020c06030901022502130504110d02030106120804150f051903110a03051f 70
    0x5640015a141da00380303e215500900801d8004005002c16000504030b405001d2407001a1000d10351020b08945004003900c2e1902e0101220317103420030500a003202c00b5000c2501080080394010780d1049030040c00c82c6041d082e19006044080d962395400104001c00003040d01580e40d0740d070280103048800c0d024103804041501e1445c62580204018640d48400300041c50b8083c0c0540000580014880c04850340441c0456a010001580446540c0c109412aa401c406400c080c0385c9040b070b0b0034404002a54a81d041c0328030511441d008000030b0400e2a0035012544094120070004490420480990038610107210080340310303890543c41680000c4640c8111840303140c03c0700c03030203507807078401c10600604120080050343c1554940c41c01090500309448988001889150441e964516003222141010101c01c0300004000b0f01070580d00805034070500380c5001c400c0105d80d040719511010015401405140c503603c400203404115500141d030075a00c0907201d00894000c071040d50401009100c042079503400707 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 524484181 1250 524482931 524482967
    0x601020703030c0809040608060714030606040e06120a03112a010807120515031207020109060513090c0c0201030e0703021302250b100e040b060904061409010e0d 71
    0x80030400302c1d01c91007010031024020300c0040d1422281d1400b00302901e2542d0402d01a0f5844a02801845584071140740f010200005002d811402c1c402c0000301684140e01c581c4072300b8900d4101080b1160741d01001c23806022032075802c03a101c0354903515001d00300031311441164955010321b0304c0205117001d84900781100901181045459030001e04015194010050321000804c145240ca02401e241c26100702d6000c4c1080201c02601c3c4407500041624211141121a031143e034280460f10044c1d0300320031000151080c9051498480d40c503444080d10240140d407180341d00e141060f090204554001464042080c003e9038140300e080c000c000340303503602c01c1c461100a400840d0010481a0f454160380640140c01c00b6521a000480c07244000201c0540082c4050b03403040600024003080303140d001c140c80020940d4902d000d4041c58a615030b021102d00c01000365010356030345c400140400006a04c0103030a4000540c003011075080030120b4500074142100d201c40a40319103202d0a00c058002d000c070769020f8000003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 524485431 1250 524484181 524484193
    0x3040305060103060e0115060302030a061a030a05061305040303090b071805011101060e090304141002030d050a02190f030606110a02040b01051207030b032803032f070515060102 78
    0x36850700020818100c2d44041c5c2e550304c0460040302081a1075950003490941d8001d80c485c200781001c0821610151f1040b40080f6002c00003188030318004050780d0713100c805403000150329035030754000c42d200a0f0070704500b03100a40342600b00702c20140c043c0d000700c180600642c214641c541d41c96074107942840852400030380550402a0802035503103d4040003400914a0b80085445a520344c40803054900a071120001a0400300b028000600a80549600140c04440281400314056030180d01c0344981c40807211940d0b11400000c207181080d40490340c0000b8014007002107401c00c94802800c0c040c41031404400241800000500d09103d0210190441c240720040d0400c0101642000300404039004030505114080c815103046014860f940c070b1241c01951001324155680f28101130074a001250300d14552502250000f44000301c080c0c06803001540340c100055840b059a40e950700b41000102c0c0804074940214208090700300c0000640340b043d214508617802d00c0c0840d00c0701021a00c0841c1c1c070340d005074001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 524486681 1250 524485431 524485433
    0x1290d050709051009151b030315030b0106051b0616120f0c11161d0423012403080f1e07030e011e080a09030201020f070b040308070203040305060103 66
    0x55211a8001100d41030401074190f894010880c014548038031107020460703214040104e2416605078020101d00742c40d044400045414a05603a0488030401400305981e0b204c0c0100c40300c1c0300c501020060f6800448420030341d1b035070321001495179000c2540540e02c2410003a8170407113100002045070080c485410005e200d88821882220603038405d04ca0a41456121458004d4080c4580700d20900009036550309840426a0000d03180780000d0090148144000c10b83e00300030760311915510711072040600d007410b40305440358140519030109081031041f54116142200c1c0c51001e05500600e001b141809500044503000e10078001021300134031001e030400c03004014007000002900c00500840e02000502c0c240c02d404d03000780348155040400c003240400c11600c0000c40c99a04501c4824000080180300b00c1e504d0227030000146844000391001040c0c035111f0b680001094000c1d0140d80030f1040b80c40c005508e891950915040c401003d84098003c20084808520003920110483d401e81360400d0040200b0391131 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 524487931 1250 524486681 524486707
    0xf03030409020d0209060412020907020604050606011b02040e0c040f091e0311151902130b130302031002071403030714090a0b130801050c04030f06180b0f0129 70
    0xc036490043c0c2456007040000107036550000944080d189542003011030b180d0030f105000200f07c002e40756409540c40700f007c10000440004400b039004900b0f2800c4480c006d04221103d848027513041c4000c0d8060b00b030074181c40700741800150b01200303e40200e50510a1408184441084550103c13000e010710f038443d1102c0c4903920000d08031041140c824900200910b954807685810885403a4100d004190140c06110010141d125980303160300c29040110724010340c070400c0400d0740c0d5491051107412403001c2120600c0480c1402c21000954010301910b14800001b44140000e6002e00021201c1d00e40c8151010020392002040d288184495120032401d84ca0b120010381040c0c00002c2010391100c034184001c5064030f083c84c05484d513105e41e0f00d2040300c86800c00e04510f0031b50700001e1242145502c1480200081240c104001d140907030407503000201415224080d00200418001c041d000d031441c0c9051059542c082d200c101c0c12900d00d6040c40c440358840341d10314940502c132000b11041c1203c082c4145a0300c809 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 524489181 1250 524487931 524487937
    0x140705340b0f07030e15120606122a0c0303010314070810090804180510091e020c101506112a030a140706081803220503011107050c0f0303040902 64
    0x80a402d00400b10b101202c0000d106d02900f8a0101c00040c011404e50842044010a1904030104a403a907090000280c51008480c0700102085002c500748000140c16a00051200f4140500712030349503900d4079494184ca549138020300c81103071407a00045006089200c003040100594410700d02900074905080e480300b01030407039940c2c2614000030400001480d00d0311510345101003a0342c07510206142c1303003421075080803d00c0c40c2d0001c21814109020180b41050800c1040c0e920110035400503103c2500b0051549480701e0385100c0c010b4145015550f601c00110840540c04490259680e03448050b80d61048a441341015030344182d0030b200000c0e40060140403c004051011005000c4034202d040d19254150411081c540025094000040600416510040d03040c2d00402d031001c000000c02105205ca65280f040b1601c154508440d440051500607248441ca0000d000083c001e22240e202d94440791800d5018260448181c81406070a102d54144103e4501080718020301031410180f500504a004e58 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 524490431 1250 524489181 524489183
    0x40f1e0521031b1917090105011802160210090e07050a020d210515030d030e0312091501090c080702010c0c0809060d020d05040c06020609030a140705340b0f07 70
    0x41400c1c40312035505001d008150304c244009948540035030041d00102a0741010103843d80c030042c1d0404c40103008142003002c030140c0010b22104010380e00d418540354010070307240e5400020f41c03040c031810081e02c10030340c0311710a1010340c0c04112904200351900304003507d991098409050258100081c4110250b0003201010380b04614085000e07c5550001d503190100e500031a0342c091030b5541c0900b8030440d814104115003400d01c2c0c0c0e040030040c940c900700c56140e690042c070308440c0c1c00440000004031003034818041c4a440b40303003216501031a541c640d4800780140022501c0c07480064000303070011741414414081e080300f010140e21840407100094542840540c072644015401c090b04004505002d042d80c8010485180102c1002801c2d00b014a010b0740d000c0b41c65070155007154008014441c6913040401100c043c86018184803030080031811200c0300d0781c0207448016005000d01100c90003c00d01e488451000c40b011b80300c2c0c248961001010b01c4114130144d00032000080d1081c04600d0558244c18002d020301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 524491681 1250 524490431 524490481
    0x50324010521011b0f0302092d03070e070e010f0e090903090d03110609150a1802040e0d0921061e15140d0b040803040f1e052103 57
    0x41d80c41c5080302404e45508034098003060300082d0281c403c0540c0320801100c03a0f81c81d1310301035150413034032000100c1d003d11016448a0031088450007034588401c4a041e503200400280588524030b503036040c034003660003088514101007400050599115071150584030010400f44d02c800b154100c041003444100d000040c0700d1042880100b02400484d9540b041c5194003a00c2a0386400d154555100014240007001d042c3c0c04003944100d00031004141c083c1112503001021140000301180040f020450b040c486100c06074109181c095082d80001020a00c4400c1110303a407211150165904580da5400b4961401c4400e80714140440c20002025070700400c0203a1101d0708020306941e80c18900d803040b601d00901d280b05611521604000d109070105440700004004c588891002c919a1074005040c003004000500030034000001404200742010080030240d005400c81c5a0410320010000e540940c2142c181e07950b01c00d0400d680c10790481d138a107918040440a0845d821600c1d1030080100c110400113218600b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 524492931 1250 524491681 524491729
    0x304080a030510030b13170c0604021201020d1406040516020d050a0306051305160e0307060c020102101104051203130302040c1b050102040e010602010e0601030326040501060503240105 81
    0x80350348041458003411001c00710103084112440c0288815100a008007c148401d112007035007071001040e2940c0c803680590b01e0b91000b04a0103983d0340207115200840403c1c4d460019982540a004501c0302c0c40380c08156000c01007525018004280c2d24202040980142c0c842104800094460009019022054100411220340b5800003d01c031503000c2c1798030340c40305a6a03010000701c280203010502000c0300300c0c1800c10343e04078200040380c1c940080c1d004550170f21806813138030342c11a44200b00f8404601e030b41b001c042140c80c09800c40c1700001c1e03006d0b01c50326104896015882506440100c00c486220070200d1030540001d15550034400034110f100d80007414000c6142c06a29440e000301a4510b82d01c1c80740000581e0b860905403841c01091041c1c102204581c508210289a81c100003011070549416013030401e1156002401810424080390558034019100c00501082010542151060310030440503156005ea16106221513804840414014521210010082c40c1451100c06550802104402c10f03 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 524494181 1250 524492931 524492933
    0xa0e0d02031b0f0d050d09150203030105092203020a0b0106090f17011b0e0301050c0906030f06040e010903030f050106180b0702011404080c03100c1202031005041503060f020304080a03051003 84
    0x101c850f8044c0d005907025080400b00303c00032903001241c1009011a1503195182e100202c000039941c4c08140205070240760b0700d0000c581500c403010500d4048450706e020451510317506150094440b05ca1010407200030041c5000498554056500e032415070f0801c3d1066100c0900c0d00d210b01d82a003a09064006a655896039103020b100c11001070405a0442501e8055200c079801c0b00385400c540b00101101091402801081401e590b80c60850f6003020036122400340b0790711004001401001020b01c84139940d03107851010300805801d50400c407010b80c3c00c0d44081001e680d94000546400cbc02401504000d01c810303120074001c01400c0006400007070f0043c5880d00d62005203184422181d4020340200784a40d00c210181452458104560f404c010000c0609021075140b1401c09030a400703203a0741083c8050340110004030003c0e56500360000605000384184001c03503c04c403094502d80d03a1303030006a81050400440211600e214004c0303d00596220b2b2009240c0450780100310000c04c8040e100c0a12407500c0d02c0008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 524495431 1250 524494181 524494189
    0x60d15030c17060703050705160201090b0a030e06010807080703021216090603110f0306061c020901030b0601180308030c031807090e010c03180b04020d1203020a0e0d02031b0f 77
    0x407000e8a61204011080002142c10900c0c107040244a40b04040c140801c00984075030000554030300404400d18106050380358170060f40c1450540d0400c000d424030100701a01c01c02d0b490b4000369030071406e40043d03c0a076600c3d48402901d948030350152089542c0715010810050408070804030308240c0c10310694011000c0400348024840d02da9000301d11507600c403a024418400c449000f8032002c14100c8001c54240340d06408680c40312801005075210b000f0007494195901c80c0d118000749503039070040151201c1d41c1c4a24064103450b900341d50140c0000c14000c0313440400891100e038081941e4100200d00d056585200b070208099200034011203880126214010418100304401000303011204400b10340c408004c01e007682140d00f030b4a02c6100301400c0910410010800e0101e0031809608a24080070603504c03400070940001c82c1d150001c1019522102085506078154058802c0400b50383e11000581c0c0110100070811710002e00c0a0b41c5130700980f492000310764031600c0740f201c01c110180004800c0b0002c84009 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 524496681 1250 524495431 524495453
    0x10111b01051522060311010f02010902011e030204030b04080301030b010803040b0d0b061612080c250302010b03060901060810020304080a030f110705210301030f032105041103060901020405060d1503 87
    0xb101c01003d25001e220842d88c010b01c2c04115400c10f440200403409090300002c14062181c2891180154481c90321074949100760121005950050700c080341d5400c0c54513080358a580709100541e824105030001141a420110407201211140d002c444e040440403d44440100311010210b03030310101c00c00c0016542040c0c01510b41c01c2c2401990ac0d11100061004003a00c400002003c909030f1b0801004403424400d010352040904102e4564109242011440c1c00d90042c400031120381d40c180304400c20090b00c0c1304150032580c1074030966003d903400c400d01c02c0c00d0001680001e5500624802052201c00c414034840d031310180e1982980d250100381c00390021855103655200c0e0005462540046110b2000348410b0341e007484070b182c482642545950b242d40ca544207030342c28444004082041e01d0085442020710035030043d070300f040c07814420095130a240c500328100403003800b00750b070203401940005400d660040c801e8130121ba60142c08075107400c443c0f030010f40050030341007250b0118892519010010136104141 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 524497931 1250 524496681 524496683
    0x907020a0605060303030601050706020d0b1207060212070b01030605060310150806010f0807061202220315150b0a1e08061309080a0c0510111b010515220603 69
    0x182102403a03a0600c0c1d0300781d4a00400c81030013540108203004941e6440b00840b0707417040e000600140c5441c2c164164102070080c40d2400c07948440c07100c20349090360340003080910440d402ca4084a800c0801c1d4229800c5501440c4402341004145c4001000842d40d0780c0c00941e489800101030300d0007200150552811602284044031035024507030307020b00c040da10402030b0034090301203107549400183c41c010300ca558500c450b00a241c02c0200031189a5114902501515082001e280a0100c00781d654103102480315070912095501c148002006101d50709039100b1282c058585201040c102410603490f561030f81d005001300001c2001010f15030b01c0c003d1148407090001a003d9a03092301609243c0304001514541d40b0f00044002d24200e8080001800305045a50840f1107082c140e160001500342603080c03e00c40702e505040581001e65001d8002c8448000f0300201d0025824290401c0052003270a08071601282c02009170500b8590b0020b203883c00302c1c40a5402075082040340d41521944144509550503640 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 524499181 1250 524497931 524497933
    0x408090907021b0f03070b0c03040f060c030e060309100506010c02131505100203090d170d05060418240e070e010f1a0a03110d1104090501240f020705090702 69
    0x4441143c0b0b60341030b8040a8100c0c003c6500318034400b0400c0010351034829900c501c030300c1420002059112070344103005075001001501c40c0301d030303855607204005000c620310744800714000b900688210b40c00785801c2d001d1700c1c000c441010051020103036030032505004000242c111414000090380440040e5144d610070409040a11004900f0110154401c40107a900d90840c1d40324440304542c80e95541d5001098508440084800e0300c010f0b10b95003031070500c440e450741c41c0c890007400000d2078134441c0c041900014003c2e4000c0e07500b084884d00307122040c00b5850203960014007140400890403210345074880c00d0f900004071080d0001e840c0700542a45450078104d68085100402c0901c010050003075100a20300c0240848803402a040441022107030f2a403191001e40028540d454100120304400c02e010756010030403041c000c00481e0709082c16a8003d8210f0700c00c2a101c40c1c207000c008140c4041d0a0030941d10034520807080f807100c4030316038400d844030f0524042810841c8210000040d8035a54a404980a061590 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 524500431 1250 524499181 524499193
    0xf060b0705010b100203070f08090612180c100c080f0c070303030e010b010f1b0b09011d07060801050d0503070b0a1d0c0f120f0a06020a081518040809090702 69
    0x300d405401e40b40f01d40111885400361503004080d1603008400c40f903003182d01200d282c0107140c0c286070815007406851380c06ca410610204651194200c100c2c102d40c05407640c42c3c1c140440359003030740c10240e680c48860301d0a030300200900340f4250280c4c086d400c80040584100e07402380c14940f00da1000b21050b04510b610851a504c0b0075820418141c040c411084405040c0c0004c2c00460f072000000703818a25034074001820803e40c00c1e11414015034000d040030809070300c518044003500707280c0703070860280a40041d08002d4007609405c0d80180d01c0f0001d00e4004866007a240d07408545c1c0f070002000405036182034181c0f20783c0810040640041d1003480b0151140e007180790000358240c013424850060300d5980c0e4460007154030145d02c1180c3d580d15200151b5600e071049664112403c0301140160400d904034100004c240b0814500700208030494014041c1c811444d0303030302c41141d0349074556100c0018034519181d40080968071550445455440025807241c020b0602910301700d03c0d0300204145100031949600103030802 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 524501681 1250 524500431 524500433
    0x6120103031b0b1b0d05090106140109080706050f1b031315020c130f05040503120717060409021203120901110c12160c080102030f071d0d060f060b07 66
    0xc011140c95a0b50311010080d042d10b64544841200180c10b00c200d00010103940c41e00c0d0342980040350600721460409000034100030141a001e0b11007800b40210020303031141d40d0902c075403181554404880c8144000c0400c0d03450b00d40d0503030711603010381c95014100d241000f0012412403098448540107a10100442c0d49800c0402a10500b141d2a040300e03c0142d07284010a04159001403c1a04904111030503100c0c07184041c00c0c07a008065420111014170300703041c2000148040030014002504218104000581c1c6101007110f0320b210040c00c000e01c51480002103115400d02d580010380c00b03480541148000070100101ca0707c0c58200c4442682c510f410708013080015a001c3c010032006540c004121400d004107441c04580b1507036401c541510702040806c2045030450b0721840c0140a680150300b510b115512031105501030b42c400c0720020344451901c004039022078070507403000c00311403800c42c40900655090f000b00a81c01101d10380c141c0340c076525091441b504414a204043c001e288540005a0340d5080d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 524502931 1250 524501681 524501687
    0x180a0302100614090a0b06090a0807090c020106080a1e140d0320040306021606020415020105090a0f0204051005040c02010605030c030303100e070c0b19051501090b16020612010303 79
    0x250341043c0c0300d03040d10040401c1c0c1d60f155425030315000100c043c0042442d182800c082203850003401c8940342d000700003034800a4400e401003060016141d4128050020030440c200503800e8540500c50345456911003120400401c500d840580ca00d001420360300310000c0720644801001c007582c801340741c40d00d030054081e010140760103108010b41070301f090003065404d140000e4182e443d4003e621000d041035800203640c0c4001d20040000044259002c501151159240e00f200c94034282d0410410000d9071038200400c503070280001c0d1664002d036104400502e181c4482e07080c00050a4080c2052940c00d582202c046099900c0d805141e40400c8942d000045403860b0000b0140f4040600d59210b02a420402c18490920800e0400e4400e46402c01c00d4003c454407a0b40f0122080f503d0444090705e0480f260060082082c0000c1180808400101081c401070b158050006451b50840c40201e01141d0020020090048aa8007911000010000c1808040b8840c2c02241e01d5034800d01c00703d0042d410307140040c010160 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 524504181 1250 524502931 524502941
    0x212041d1f030b540d18080d0e0109120b0109090f0606060206090d090b04261b0906010f020c043c06060f0504050d11121501050d0b04020405180a030210 67
    0x742e0401c2c030350a09003045807076035120720140506030200701d08001b1821441c005101c0c6c940042c42080d00301c03021054015001088012000c03076841c0080c1450b4030024040c9134021080c02c010307402c020b81c50001e910304111100204001101181ca103036504072010042a52407203024000c04850300580043d1a01c0303c0e0841c240f08940629030140080f4010511500381180e065400340c841a04100c2c582840741c0310f41c800120300c030302803894141c07040b80c8a09502c9645034000412403070082e0f034100d4140e22030ba00151004203900086034010f034002d500c45030503843c040c1c02202c4503007442812a518040c2d0348a84102d144200104489005444140312280d42143c4c03003404010701e054038110b245407035452001001791246d403003024861160182140140088101c1c60520b095000346105241a61001c24a403641ca01c803200805030000b20000007160f00b00003201ca042540c5c40049500780750740d143e0802000301000307407070350000d0b0856601d074440411041020704156030280c3c004240c414a082203d00075a0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 524505431 1250 524504181 524504311
    0x1903020702040f0f09050c2403131b05011404060c031d13020309060f010602030406031e061203020105090304060c0b1009090506150a0e15010212041d1f030b 69
    0x40c522050070015490825200f001078204005140e0789c0b51a4520200070800b04140041c1004d00350040508100035040980d204070390080c0c0368203900e0b10101003540c0944c0560b1103204046140b031440b040c0041e1052020302d0404201d0142c5440440c1e02d180440c85501024940380445640001800f02070700c400c2020031760004e50900c618206d0341c103000c8000d449026510500042c1070300ca2401d010483c1c40301103551032309814007408105140e0703a00710b00c0504054061058000d9480c00000c01e1080c500801101c06440c06034841103a03c1e0107954821880d078500401c810030120f100c80000c550104203003d00d880407400b032002082e180c10500a11484c050540c0010740c07180d048110204880d15442003030503030200d0b040d00c5184141002030300613401c01416101000d43e081000402282c0c01c112070b040101c250540c1c1065000070740c0e503070184c2c1d614000305122040c210074041c7d4027000046c1840e01416485024407142024194031115030510540d46010b04542003100c01403007909070b400e09640e01400ca = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 524506681 1250 524505431 524505439
    0x5040e0f09070e0a020408120318161509050402130f060206070c060207050a020901150905060c030f031306020304061a010827150405071a1903020702040f0f09050c 72
    0x908000754159901c5100788201180e10203410000307003a030211070341510300622000095441c0101b400c568080c103a40100d134425821035108540b00100c290000301400c01d0b510041035410110f08040e49001c0401c1d807942e45d041001407005000c5182c2d1a18000b40c144a0381d040c107541560717428000c0c402e518502c1e941050045501604c00c1041c0d49034032034101c00b4965080f0200580d0f5080504202c1d00300001008080e420015003000005e08001c108102c404413811507840c1e01301284c85d9010022203104211000c441c41c0d00600c480d006c000e40c01001940c1002c3d600a000078108150f5031290280d03007013210309171002c1d035440b03002a07885c5614800c10100b1541c00d180134943c078a03100c0c041d4100c041e08110820000d032000b850003d4a10380801c240310008240f40c4c003245003840c0034581555a030800b40507003410a200301c5001071070710100406030f9034101c101c400b140003404102502240250400700e0142e80c0300d41c40b03814038a040511817248812a901d032110100308103180c0d003081890401d500340c3ca1409 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 524507931 1250 524506681 524506711
    0x20c030409200a05030402010c0804030609050c0a09060311060a021501030f0308010f0506190504081b030c0a0509310302060708060f030c060f0f161209030b0a1e060605040e 76
    0xf20380d400000c0720340c030650900704500c40b5001401c285002e03028a0304000c00d60340c5481e0043e000c3c000c00041c52108448101c80366018582c0f100c0d0f0b4101a6459448020603071a400c0784401003e1501e0b01c0580101c05e0b4510484550400c0d094103201720a600381e0060320420962080e460a050303202008501400314080540e00700380ca80800314040e03208140911240301040d00290031041d03c01d4007280d0007084000c0441c2c0d844010b2a503131070740d4002c11180251084c401c400c08004c40d4200010900d0448a0081c040540d5548109101c0030180c2800d58102112010800c0d0040f144030004080307210a000f98000d142c545401c0d170015103c4800900181c0c424250a40034a05a0303400050014898406560143d11054800314070300c8680207013003d04c0c10288000c10340c08034650300410300b036006500842d01074138035003d03820b000c1e0b8a00641d400041d005c03a40450000d6006411500a400f02c2000108040101e83c048a60f40b4100c440b1600309100160340050308116420141c1c0025030014108180c0324a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 524509181 1250 524507931 524507947
    0x30312160f0e0a170c0907320306060c0a1e03030b03160b07021311030609160813110409080301080706022407050f0d022a0703030e04020c03040920 65
    0x550307003030b1600c5821013400900c1d0700041c0106051200c094101d0000e04100303001d04205601500c00780004242007502c0c90146890507042110500e0220101c1d0345841c2c540c6540c41d41c4040c00401c0d44000d4400104d0f00c9003a502c10000b4198a81c0340c22090704000c203030400e601183c50018181c95244007070912a5004101140d031024504000c0350480c0d01e40300740c0b40e551343d1a501c0840c140294545030454018942488e00080c01e00d0032000710710030802180c031030805036203141d104403491001140002c001a40080011070050b031052541030b1081c080ca520048041640c1c0001c1d0995a4030501260301d401e0110041200b4181007100001130100c0f070014281c0b81840900d50807842c2d8901c031a20fa415010b9201080e03185008500722004000d04000c080e07070b01c3c210244828065840503480305c98182c00b4681042c0c203180140340c0300d0b507101030301000745c4541455500c084407154080b0140c80c3c0e00a90820420000603401c00042006103030410021030721f2441440360b48081c1005c0406084030406c100705041d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 524510431 1250 524509181 524509189
    0x110f01030915020c0f03040b0c0d020a081e041e09110f03040b0a020f18090f130b070e0a08210a0f081b040902031f080c0d02030312160f0e 61
    0x100ba4015602e001601c4105804d44e284c034189400408110354040042c01041062040c001410300180d24000c07202c03a005000703012030b541c820155018143e09402d00201480a000d0f141031000800030300b445a00705500c0f02a00f000002c0001c0c1d0300340b0f96000d104010440d0b2105400352a00d4044d0480c0118200007860f0340c0d070f02240c80000c0c0002d207450314440003d03064801950580d200038000301c079841e0304c803000300c04110406103100088620407072300000040d0821807101d12082c414060001311100c40c03021541c5081c24508050b06c05410300c803401b124240c6c05d0f00c4103840c841c01010341c8802001001a008050902d02201e0001044424000c10074030314015001341230841c070340d2428a0610031540e69002180c0a4180f13041c0d2220703032020002130000b41000f0a801440c0035642c0b41800c40b0a1a00c10540c8280903603442c800d0b44e600c0d80160041041a18240d502090401d00180607a444c1070905410b008800001315080100d4bc010032090f00141e0342d1101c05c6000403011401c020560400d030078001 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 524511681 1250 524510431 524510453
    0x90f05061e031906140f010e1510110736020a0804020d0f02210c10140d0f090303230609060904050313080d0f03021801180305060103110f010309 64
    0x3d0380d03141c10200c002d5040040a0b0700c07a452000580300341c02040c1c1401020904080400c0c0b140c100486481004186004810354002500b254001c10b080300c60340c81e0300c1060341c0301020844984403034010031000064084445508440c5c0101030300c81100750000003815003c0d020314040c0004103031031040c080382001680080440b500a0b07011100d42c414a10f59180000050700b410000035040524890700e2070f03052900c00c00b0b144030442e0104c1600e22120703421041c84034411823400d4003400219141c151410022040d0018030340440c02010100e00c01105540e081c0582c1c59a04044000941d110000c4011140c002c0340d0140d1198548400511400c01000040610030b024005500c01c034007041c04642084020011500b403400c440700120701c6940e8400195460348041740450000c22505155801070f98880e100300c4100700c04461260715642140001110366040e034a4544a003558400000b201113a41040142e00079031040340703c01447e50381c220510141c1660718240d28103040c140701000000805000700 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 524512931 1250 524511681 524511703
    0x93801021b1c0c17070e0105010e090c0904090611041d13030e01050c0d030b0a1e2105070b0306150702011209050c0d08070b0c0f0d0213090f05061e03 66
    0x214021900711030030054070b41001075100c410414411101c09091580126a03002200d02d0300f200464140c1e2380e8001541d18111011030b00b076100c200c001c006100447d5000281040ca0070140002903c10310070703a22941140e95409103494000300100b8200014051500f1403048030744014032805460410030145011010f80e40070050900c03801c4080300f4001e03440791041d07a039402d4008003104e51001e440700c00075000700180444a4000c05600e180411354052801842805504c58820034140b540703800c40e00d0844480140040c0201004034403400c003c05e02c2007104402401a180e00c243d9242841410050801c402810400e000d440520200c0e015070781103c1c40d0b20210012810120307040043c2e14005050a0042c0c10705640301400c940791405002400c006020303100e1207543c25070f0b900d0711601403860076070207900300b202001d03042004910044010381c0c0152044041d01c540449001761110322941c02c0e1802000700441c0155600104029890901d508a606403054030810000b448420301107500c1c2c41038080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 524514181 1250 524512931 524512969
    0x61503120e0423040c05120a0f020a0f0e15150d0f06030501050a0b090f01080d051303060f0c0f090810090804150c020310050603030301093801021b 65
    0x1000e010562900c0c3c0003101e0303030a11489403400348044000c8680c114401542d058070840301c407030360103c0c003403c0c15040307440221218402007150304259526104e801c030141c20b0482e0054880c0d8400a0b11500301c80ba000041c00f203203d541c1703002d8a041e1a40301130b05100070900c58850354080e044050740440280468038060110200803030442016880c0070081c10480d40001c110b98030744020444000a9907110007182d00c01101c0c00d201a484091600310200028000e2944c6900503c002651b40350195004000b840b2040840d0350300d440d56921034038103d440c403402c0d49982c2d9407505890480d15500070003440a15115080c5000064180301d2003507541c18034916a5501155500341c900700703001d40101581c0041c000b81c8a20442450000002402948022022801b910901c41420700f03d4100e801580d21070340001d0015800c580c81c2c042c004000d400820f004001807040c16121260024100b60350515005108542c9401c02100310002854065085810040342035401081d2003e5540c0d850080042c1040032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 524515431 1250 524514181 524514197
    0x9041406030d090b030106032d02090f01030b0a0e0717040309050a0b03041109181b091015121413031101200a140304030e1302090906040905010608031606150312 71
    0x6140301410b42044c10001c1240c4024109c0c0030070100142c00401340c622041d01c004507480303030907001501521040d100c030a901014070030081c8a20411822034581c403a0300e81c0b42078550a03c06411030348540c0301c140c1d021707000144060707410300940c10b02c0d0f010345006100501c450740c84c0d40b405840745408000c0d038054207032041504001090f8500b0602d001d10032501071079010360b00d03d008403100c00c65822142280071802030440400180c6940d400e402000c0445520200740344114034864000c0380c00d00c45024040d4680740d51007074000181e4011090b0207120791180d607845010304070780d401c000e005d801e80882c0c5110b107603042010f40301143c110921a2070701ca00c2801c100d9074982110341402c1e2010b007954880000091000300c100000d143e44500d036001101c0f02660550011390b07254034091b00b41e204003900e25411100d0540072502d00d040039405080500c1c081c800002c0e900d80c42d004140d0650380612406c040b46940c0c4035000b41807018a22604041c1000d0380307401e5000e20f145954240032031a40008401c1840001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 524516681 1250 524515431 524515451
    0x7120b010906060e061e0c01020f0903070b1309200403060209010206090303010f06230c0619020723010618150e1026060106030204150804020a090b030309041406030d090b03010603 79
    0x180a95004c540301f00002d40d1100640184070041c4e400c217540c41d40c40391280442c0051405000004c03107203822810700300320178290709104041003e403101b83c0070031000c50601c0030800b0100309024090805540300745c0026940d64a02400285000f4002c0e128803c180c2080004002c1050b000e460380080f10405d0815900003882d482281915521251110344011000140c5000540000c01d08900c07450209a50b2010050360490ba6000c0b4001c058005040b400e0361445005280740150001c064441c0400010450399205c488490a0102889a58015a40740c1c503814400900101540c0d003d41b41c0f4406440e0a8600411040640350b09071040d10800c108805147c04401c030250501d5203c90b15000480741954fd6454001f0000c2d4000e21440407900743d011114004c540c8146102d1740620340041100340001e0a200c501e200500c0800380340f035031500c0100a81c064644580c0108a01c0100c0b00078441d2480c07a01100707243c10305800c00e2850b41084140c03030080c01000c1d00801540d041d24510702c0c000030100b034a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 524517931 1250 524516681 524516737
    0x50f150a0c1505010f080f0318010302090d021905010318050a02010e01020a0b010b07120806101b0203011e0b0105030c27060c0703110114120907120b010906060e06 72
    0x982c03114030071103410b01c070020407005800111303d81214811001c8400c4040078050b402c3e224050680790006041c0300302c1003100198425005441080401000001518003c6c1d0004030b000130700b0340540000b240182c508100035a00741c07040c0102000d0700b8585811074012540c541d502c445112200a050000403001141a03900c01c01001079070719401201c80001d940c40e145000c80640060b4021074100c8070b1002c048680741d200b00c0800d0300031003001c1d09141e484144014191464030b84400c5607040c2010503c0d81c0740140e80c0034058036180301c2d10a005002080228016041540c51031070f03a940c1802810030600c04c0d620030080c100c4001f03080703100700c0341e01104000020074481e90901c140298041c01c0440d103060040700110390700d803c50307125403900d480070058000195041400d0800240380a001800f202e10495115035206920844060580d24a6911010000740d11901480709031180000d040050044101c82c2c0710f044003400e0742d0f08011301b0782e0300306c40300003030b21032196070b1544411420060305840b102c1e40d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 524519181 1250 524517931 524517953
    0x5040804030b0f01080d1b0b0c130b0c1005060603010e06030c0a0612050615040b0d060e090312070801032307051302070c140d1e12050301050f150a0c 66
    0x20340905401c2050800f0040b81c06005001e000c2e0b2482405101110902c0e5405024899240c2c0c0810310303000b07240740450b2104040d100000707210f000607200421281414820403526103000c0e080304800981c40d100e001d21205c0ca0080c0c2c82041d080e55900d8801880065070320b500030b890442c1c0c000751101c0038a41d91200402c0c1401f940a0b41e42da0010b805020226089401020342c0401103221301081016584403810440d1841c00d110100b074011000300014000c04000c18014201402c6001e40824007558881d00440c0308001119000d040d41c001141c1480e04248207045160058010700e08071075594116220402060300c003007040c010b0300b0b01141e0007200e4031074280703d5240100301c024041c03828604645e0701f40c006588914401c8030703140303407090006c51594106910820f48030000b805188200a841c2d640700322045120001300c0d0781400c1c0724800c0000685010241245032426a501501c1c0e52408080c0324800c011170360703850b2241007c0c0d2a14054907508005940d030307003126464240310009050070840c03180c01c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 524520431 1250 524519181 524519183
    0x140c030705090d0623040b0a0b0612040311100b15070615181119081b0a02160806040210030f23060306060105190323090d030506031506040504080403 66
    0x10f60100d40602406419444070f94040000070102850301c40e4140324665500088600030510f10301c55002c03a902d500280c1c0310480b1608041c00c100c0c60b00c0a071071400d41c0344500403102100015214480480511030600405c5086500d640c0c0c00d1109114100c00206130450502856200c01e1010401406000080d0010300507210039151250700c0d030313494036080414038903e4603a00f919581058000c250031083e4000f00c91a032a5aa44150102440e112049440e8000600503d41c0c1511081010808280d01750050019500d282c000740040ca0041074260411001d55000f071415402a070708200250700d80d070115600009580c5000a109508584080020101c10381100c4401041c0c0c200d6054800c1d03a041c00078051071044084400641d103800045405101c0c91083d0400c01203840d83c0f00b405c15000f030700500c0c4074840740000744c0d81c10312a8001c0030b0414407040300c01c8051503001000c401030698051040e507070006029800f070300300c003100b808224021140240c0414000c40e0b03150006010312188405540c069 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 524521681 1250 524520431 524520439
    0x90308090a03080a03060503010b150d020f040e090a031e0507021020031e270f09070f140c1b0406080a14070b09180405010b040204230301140c03070509 67
    0x12804c01030000e0080283e8041c3da8020340c6440b00a61291521164104036003d01c1500742c0d28011074a003405000c0e4000300c0220320740310028407000c10b01d10b0b0002e0015100300350407002020b801c1d01750f040007091960fa80d4180810044602c00d13441c002940402204c0841c1e4040c0c8003e441380143d032400300c0706d0259003150380c0c8100d0740d400c4003029a000c0c0400245070b8928110000303101d059804025035442e11403a0320401c42c42500205860241c1d0314050400e454450042c400301446031801d02007024400129000b40019560070340034066107400c8400e214105004081950a00480c000e106950300c142280740140002d000311031000a40d6290802c5002d0201c480640d03031a02410b1600070441e000d0132501403004d0003110030120b61100590f054405040e0014034080300c12401108103102c4400140043d542e95403210103400607030b00d41380000c3c00145900c1b80310800000e183e102500d0a9024002c01c18460303418614460040d41291b210650000d01c080e980f08e560751650720b030554183c070580a4407600 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 524522931 1250 524521681 524521687
    0x40b0a03090c08010e1f0204050a0302220f021c1103060112180606080f0f0316030e04050c0d0c031103070305190911010908030a02150613090501090212030703090308090a0308 77
    0x15941c804a100f4646c803104000c000c603504581c0c1900d80030f074051405226000909803504001518184030120508540c040b4040031140700c0d915a1030598280000c06a180d5400095201903a002100802811900641c042010403000071116503284005442d16041122031580240c42e85442d030300015400c6010440030348008428980031024144c203200b4601d03140940e2040c800b0600e008101540c10155485c0a9854100000382c40154401c18840c142c042002d5545c0b00d282d40d40703840c403401c0d000d40082040d5640380c000c0c5200080560764000111002c1608004d101d2042d000d81c101542d400400070700380405c0d15a00d40c3d0300e0410b1140001090303131400381000d6802c01449082d80311091004001e031b9609091a40b1200b466a4a100b101d00d80340c0181d001501d00c150000d0003800c0217030000402858009030210381304060341520b480800c19103283c1d544a00c0c040840c604201030340d018050b980c01130f40c20302012703490142000342c0b01e2102410b107500005501d0f0b11680ea11502c4405160302c0020162 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 524524181 1250 524522931 524522951
    0x91a091f0c0305010f0b0a0c03050c030a02010b100e0d0f030e0d030504030b070503040302100f110c16060c0507060e01020a29010503120a140405040905150c040b0a03090c0801 77
    0x2020341000042a400310f0b29080010038844074103c1c211050b1040c1c81d80c5149054000309007154050742c2c0341029001c1080c184884400348405100400c428012035001042d10b0016104201e00700411881640522680074020101c6c1d481e00000f40c0707006600a25000c403508000d040039140102030a0314160f1110582e40400e0405030490040c10a0300d0003080180600d6030307980010b85403444151006400740e4496605a0816403898010b428825881500400e040348a40404c0d00c503034010040480240c0c0222103c10391880d0442c21403002008645482202c00d8042d4452f03a441c0d1910780618010890116184562a4000c005030f0f800b0342d50000c0d03059001d2045806903000c110350002100d031a4107540d0300004103454005070001002540300c09091400e01c40313610071368683c1d1480100300c8000d08140300000e10766440d0300c103a42d40d01e03018401920f01c3c051144a01244550300034038068090b0801c1c0001d00518090106a4040711460304000134001c0c807508029080d01c3c1d155011992540c2408844c071 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 524525431 1250 524524181 524524243
    0x1a46030f081207080112020d0c0e01093312053315010f030e120705150901090807111f03061401030902182505030415091a09 55
    0x121214402c0650840c140e19648070854403100700b031141d81d890b030640c501d42e500546021040b8007034451042c018011069130f907200307800000c8000da008180d103e036202e03c1c48499010720040503034480f070303000d1003070600410b01810601882c1c40381c0580705070841c69600c441c04200341041180d184c12508186c140c00c0400344420072044040300c00b2809840702d503400100702c1103400c85640c600e41910507141c48180c0e1051040c110300902a1070140b060b0b5124004030125110f4180380200800c03400307103018000ca58603d0a00000100b8080c1089680380c0c5016a0030703011920210640c1c0d2501c0d40201d120300e41c00a034000081c40e0401c0248010b081d1030f01c500c202c1d008190164000c0045401522981c020008140d005404460083e04c010390807045041c4880104400301d08800c0c1c3c080301d412203190080450042e80d00c119040259840b010940010a00091150a0200d0018145020410720603000c043e5900e20070543c06411010b02030300c100d00031a0513100107002d24820b500c8010903590008450301225 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 524526681 1250 524525431 524525437
    0x510030519091113090f02040e0705090a0b1c08120613020d0506010210060509040b0a0213060f080604110912030405031603110f0a150c061a46030f08 66
    0xe14401c1001c4c6080d2501c0240f24083c0344441c542001075400d003c000f60b0280405419605006219800703101004030342070780e605001e00d0140c6003150380003504042600c248500c1c0c920204800202c490305031208000506000101d6080340071110100450351100000f140f1240f51304424040000c2c004986054094016030140b882003009a08a5512010042c0d000d811542d07640032703680d00040e4500005000c0b6402145903600b0540225006140100781000041d8880503900f003a0006010500381d255103552142e04c458000c402110200407400301c0c00340080181c400c004044c0c0c010078a000700014019400d20551300242800780079120052408454892002c10f54003003240c518001401c0e012060610444609000301d002d00400409401c004c1007803605540c2c85040d0040256040711800092018000d01e8000d6080b002402c1c43c00c0300500821440c40002640740e009002e8108100c1d0300300c0c3d010450110354001402c5003482c5030794800c62032035204050b50800703048190980242c00c2000645802 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 524527931 1250 524526681 524526713
    0xd020105010e0c040306050411090103050f0f06072c0a08160816260d051206090402010f0f1205010e04052a040b06091e0118051003051909 61
    0x200240d80c1c0302c0780031903200581628401904607081c801400060400d80c0166002030041803040041c10751440000c1c0703401c009801c01c55143d085058040e0f034800b000c10003c0c641540d0350012781200e00e02194010300071503441c1d03041000003155a400c280380031103054200da1980e00c041d00300184a501c40c82c00702d580d050b001c4913014200d4004040003840907400b04a120310011400ca0040b83e00d86801c0300f825016941030718440100c507c0c940d41d02c0c00508104100601e0071095100d172a240c041c4040e054004c60b40c004d206a000780b60300c404200c0141e902c50440c1340d54815500f042005c8010b000c000315200b0810f4070588202a161400214168100c481c04507c15881036044034050000110003401d444c0310321135041005030040070041d415240940000b00201c2c4041e10107800c003200e80001910708910325281950208100a1016035075074006441d2507038100074400b940c030003450900420407942c620501c150416644001052114450800c005518102e8030000d0007003030800d0030725401c180c610002c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 524529181 1250 524527931 524527933
    0x4050105010614030912030601200606010314060919020c030c0a022d0402180324150d150204050a0e1e06010c03030c0e0a06050c1002070209070f0905060c0d02 70
    0xf1003260441d49045074801c214100191490361070140080c0c9407600040c2c00d02d0705200854068541c025464030084402e901a01c001b441c082c2448000982181e040040320105410048100800d54a4808025402c003a0004001e0f00a180201024000340115102c4e148140800194880d142000081000600c6c0c000c0341c05400703405518845421207454418000c2c10031480780012443d07890f0640c05406072404601d01c0d8101e02c40d211000078149004042c5c0c80c50008031314011510301c00200c0c412281d00c10084130b8103801070178091000888045407503000901c500d50340d0000e070003a506180c05840c01408080e05984505d600c1304018034500c2e00855904110b0b00182c01e9004001d1540c19032036000303c0c41a1103e454604041d201100034107803c040c028240030f4906030345611501d80404200044c401e03640d0b031a4540f41220452820400310400340b03d007603801480602c0142e551010080c2e0000b0040c00e0103002d0008446013a125405550300c40d075404540030a8488260f84c0c04150341500c0384d00740e4 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 524530431 1250 524529181 524529197
    0x11d0c04060509040b010e09030d06080f0c120c0405060a030618060507020d080114150c0c121c05030a06030605040b06030d0c05190602130f03120e01120f14040501050106 75
    0x503083c0011140c0444020b450500303091300411070a12038184d0580c2240c0c554054904d00800c1c403c01400751001a40491000d03800540e481015503402d01420000400807074604048c08400319009683d829080d64541c451540c6c3c4000c10540d03643c0b40a50b0000359404881440403e00146030180c3d20100e0600c01d580c0035007050006140284085610900e001c0d054480c216141d00707004c07484124010b8214120b401820b080b8000c40e81040000c054a0104124002800721041c07070000e0000740d480b90003c17201150f1050216907800c541c280d4120149820605c0c1007074480c1c0e200521080540915400580004c0c9410240010700c80540c04407031040b44280e00710303140003014440c00c8504540005014100303410114500600303800030310000f0825406683c0c0903092041ea00140c0503141400d5007d02c0002e100d06c00304004106294861642c40840c5081855100801500280a00110140b0910041c2d0b8401c0101c100c458140d01c0981501c1e10b6103080903440c0b400345000c60082c80207014610100303070380b2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 524531681 1250 524530431 524530439
    0xf06090709140a0c0210050f071107030b15031626030306090412031d0a031707050703030207020a08010203130b090111070213180c1d06030a0b0405011d0c0406 70
    0x76004861031190350204111032a80d400000c40000e28182c854070046001343c007017503044070a10b80542c6009140041c0224175508014401900b0211076010360400b40c0c0041508002248280303455590004d1241c5940d100400c00c0c0b00000e0a01d02c0c010800c405d1032490403c040351040c0e42c1100a0561141d19102003058004150642d66038001290240d40c841881800240015080144900310481c11b00313002c0f0341811006400e071102c07a900710401c0308984c000125070050542c03100e40d4940030030580f00100210308003101d008055118844001d0103150700002c44104640302c1c0c4604400a12072200219264223022030550110f01c1d140d00300b9140741200e140800c1188a0600c520002844240041ca00e890103903401d011503400031070410710f0240d80d0b40103040d42e0b0310001d0907000c405901c01e94110303501c241032240c02c8590320b24110764010740d50102d500b08002901d0006002000d9038012300e0350543d96981e460000d0242844005580038803441c1d8041c00580007000070340300200a000c44040c1f0503240c072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 524532931 1250 524531681 524531699
    0xa0f0603080703030903031104062304050315040201120f02030604060503030405010e0f0a09090f050706080c0a0810050a0b0d0b3001060504110403121806050901030605030f060907 79
    0x110301000d04698810803402000034080e0740102480d0303129040c04140c00009190501858005074403a0010440c64002034180a02703403940b160314511803480c030500305400c0c02c020030b503940414008460309034416404142035a002d81c035030850b202c08018041c004004140c07174a802940040c1c50707040c015030030824080f9051401100707480549030b06a4529221208201c10007100110060910790440424000450002d0507405036820141c0210a602280030a030f103000d42c90f1210552000c0704220000080c0045040c601040340e902d07041038070b08000c0a8842d00c0165614142c95070207103900c0b00c0312080000e1a000507034043c05a4006841080200c1c03504c030400c0c80038101c001c02200142d85280d1203e00700c1c0c031850b00d80506083da4040000641c05403100041801c40d0b00d11811001486000b2400b00204107513002c42603520b8aa078034002c00e990b42e60311005001c1d1a01c80c052881806404104410943d10070340c41302e0010100102220f42c07140060316801e40341d08090751070f0401802210030100741c4000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 524534181 1250 524532931 524532941
    0x209042f1801031e0204090f0c17030f090603040602090a030506010503010f1b0318060f0609113c040f030c05030f0a0809040603150605031e030405040c0c050a0302060a0f 75
    0x141182d0139608041d620b44580e0480401340d07600b04d0b0311580e501015804140c0b00b140104076030b4490108410014100362403880704122a82c007800e0240d2080001e0403000d55004183c0d803604d102581e1181c0c480e04d480c60198064028407102c07541184048000000340319000440a040b513105800030031800c43c50286107800d9070700d030b40c5500025a400c5c20002c07048038402d40c086c081000d01000080701c46101a5a22000e03215a0314104200989603441404030b542944a80038400024001c80e500d0710b201800080c85490a203008542c00070012410200a200e00c0405900400c219250490342c464407101e0400030351a15000c244c030607091148001c1920b050004400c1026920344009001d08400760f40d46500640c844005a40c0154840c00004002020942030300e00c800613002000c00d006040c6028540303020a8014071010410f00301e01c0c80e2103000717404421038040d6502510017066041200e00151100d014030003000f0002c0c401c0c0d00701c84003415808a6043d000d0206410207004d1030140c0004981030325 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 524535431 1250 524534181 524534183
    0x40f230403120c09050f030f0607050a030609020901080406090212030a08040b0703090506010e04060b060a1e030606050714010209091f141f031e0209040f06030c030209042f180103 79
    0x10000c0500740210306e005034412807203500040840381550250302105040c00c0c401d0b0344000221340c000c80c00410305078050050300094821340d0011404c2800020009060241c068009030469980f00f4145055445108000072422205400c4a40d0b6000240c3e004001990484050303908000c001d010605480c800e004400c4500c4d000070051403070782d0901003603404ea514090002c440307159444030350800e6516900c002d407650492645500900041c01541142c0c68200c50b0410005c05140010901040c1d401c01d0540c0c1e94a030f0081c0c00f902e2513500c01c000281c02840381d46881907110f5280c50801068100c03092040d0705101a42c1d89a600d501c3c0c0c0c0300003000b007855981c05802c0d030010603030b20055002c0c1d50100385071b2400e0055180100c1c03000459841e1400038a080c12450540c0c0d0b40007d40710340d003030500d40921755000c4081c00c0204030309031540d01c8030310601201e800001d22800c03144000c1801d2004420a0301c43c0c4c0d54081305019094a00c5410140340180d000c4003031401079514400394034000d1007910b80ca03412a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 524536681 1250 524535431 524535437
    0xe0f010e19030f080306210709090203030f0d1b020303060319021c050f0f060411150f031f0806073203010b09030105130f02040f230403120c 62
    0x41141a4100460840c1c00c00c200c101d2422260400808a180101c90103202070094012907640d00b0302c11306024180d448200f810364080001100c0095421000030b442044a582150016651000c2c0c80068194442c00340c2c01d884d031200c0403501611443d4241e11140318a1403501007202c002c114410141c2e100e010403038609a15401c03001c040180c001e1103161206008e403004000410f8100b041c682030440006804e01681e040c0d011444110004c0010059030100300140c4004140c503151507542e10300403140664101c1c2c001c95400c916080d8254584094540180b11001c4081d04c0c0e01d07142d81c0c090760b600051002e65060042c40d80c000158038002051040c000c2e0000c1c2d480b4004002088560f00340f44055122801d081004034801400c02c1e441c200c043e40c080d000c00c100c426a6080c10008041c00d40c0c801811480300b4511501d001e40010341c20040d000409035040d01c2c0481d0191200014800030003004002c0905a55072000004070710b0b02d001c110500c1240309480d00f1018025841005007242c18250254000c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 524537931 1250 524536681 524536697
    0x50307061b020f180406050916240509030a03020a05100606050d0b1f0302040923042d0b061306050a050904020310021303111f030b131802010e0f01 65
    0x942030054001940700f801501820300a00b506a44450004c01100d003540c1e1aa40ca105004801ca0148070031074034008440400c086003030500a11680c046140e90f071100b0100d0401600740c4115004400ba0390308042c0060645d14089510705019464200710002181d00c0d00940365251405030140c030428094130055031f105420142401d110500130206084200e03880200308445201402c0002142e4150706165940903031164a005a10001c0e04e40c800750740319000c203010300180c02000c4510000c560280d00b0190903100d03002841008905040a402da01c81002550750925044c4020710591070f0180d03001b5514040c240c640c9816a0040700c8040c01742c20b42c0941c4502d000c02c118034203a090640c00c24001000d503185081c1c3d100100c001c0381d000300c40c01821074419040c2041031004116249a58440589110141c6141c03000741e0000300000d0f000f914245641d03049a24a039455244500d040030300b44a2013004506078501c09500d002100c500c080303000406500c102c00c5607041400780300b03000f21010385800e82c2c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 524539181 1250 524537931 524537933
    0xc0f080403050714160317040303050324190611010e0d0e040b06030a3602100203130311040b06040803070b1b0a03060e1305060c03070306030b0a0501050307061b 71
    0x2820750700c522404c1d9140c4030a850018000c44060108420303200d809519244820f182d031510008a0300303c2c0c00024141c5009210410100ba0040c0480c0d034000b42c0070504101401d0320507460500031180103100354000c078910800d6a01d01801003450002e13100291039060020a10116080c00d83d1030000d0807d0603900001c1145000a0184103001c0031640014804604847c0220200c1c3c0e60b81c0007110f01103000ca4071010a104444440e45072680c3c07085a2a03500203400fa045410080705005400b4000d00843e030341c0d15001030083c4207009564100d00e80f0f4000e62001ca9981c01c080e80c2941c20388840a1040386001d007004014a8464215011522030340f02560428503a621400c088900c02400180141c1d010391448044174003880081603011351503200050071a06028032039032100001000d01004040380e810346000300f540001e5103540324444180c42940ea40e1500802c07000f03403070160300081c500244042130003803049207a00094140c90066041720030042d501c9208440b10340040d002e00d040b28401d108014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 524540431 1250 524539181 524539187
    0x902030c04150816031118010b07210201050103110607020901030809060f07080c0105070507082b062d0e0a02160b1303092301120b1002030d0c0f080403 67
    0x3851020b0803a00c00e070003c1d0386000e0181080e04118440c48450034004050040003000d026192005034191024200000041079000c0c81c41010302a5801a00700490003030100201c1050705884080307242c45141240c94584c201a0181ca0203010454a5030004001240b09040800984050310f40007007200440e03900e10b44503106907520010529400100401c01c014410050030020007000d0700c1101e50740d0341c038019040d03110300f101c001800c40c60030068200065008684810242c4880c400c400ea101c00e400b41d50450364160480384118480759481c201040043c0d0603000c00e403090b145620318514103070b481114020701a03003659540034458200070003001288ca0401154081d0070010800550040502602e0b2220300c101c031422a81c4002130411074070244c0415910038480001440031700c0e50464010411000300140d80c010341280c604000040c40c041580990341e40104003600303030290004c401030700b07011002512030b0301034803011b03507031506140220200e50b200781420701d02d5800325074038080c40340c4566800f1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 524541681 1250 524540431 524540441
    0xc0c120903010905070f0608060405070c08030709090e0f0609030a02060403080c0d06030b0108100b0a21021905031212010302270c0a030f02070c0306150b04091505040902030c04 78
    0xd950076650340d41009000610400c2008040c2680d002c000700c00710704e002401062100c009003101e02440c24201440409500a8050b039142540626940c1d1a643d41100c102d95030b20b0a6880b14800f81e042588610340f040b4081000c4180d0212401900c816545458429035240b1540c5045001a0311860009000ca441001c1c00364002c140f0a5681e898081884683c505480041e0002e407144004e590040210300380c10454407a00301500070050061003c1c100020b0310344002840b541006d106000d1a841e03a01040000481c017031a4000c00c4400802d00341751244c40c040400e401034600074450400b8952800c0024010742d100484034078540c04140c0c0c00c40c3c3c01e0203003007014903000110200300307280d44601258074a007a10344100c1139169460344404084600500b9200b440c020b2124580c8108104004070320484014003c1d03c1d002140410401c0c1003000344440340442c3e500c464844d0341e01080c08294140355800404000c6204114030031265118030030002141c500c1034000303505611190102180742065002 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 524542931 1250 524541681 524541697
    0x203100e130b0403020c0a0e070c03031d0708031e13050d11120a030801050a0305031920100b09061003111e0403060f0204080601030f021c0b040204050c0c12 69
    0x1140318020795440c9100d010040c0c80c21805a0004010100e1904081c031150001f040c16550f40180d40c2001c20307010b8804031038010003900305a255010330800c91829050307070a0f51040d4808079100142e403407040c161260000d421514030540c0000c000c1c0700f01081d40341500c100410425a4024103440d15041003007440110008480b98030000301400b12035034400703200c0c0200300140005000b201400d454001c0220300140c10503403044440c2c44050011a10010aa481d01c21121200281c0840000b90075150000340c04c003171910080c0c10741070382081500b02150320b6081d410304800502088440714100402a0f208807070241e0840541c00402d5100c5209400604800030381128281c50000558201d40c1804529440a440b4a000160410400020b031007102404c03400b00710114106800e098590761a4401844041c0c243c200d403903409000d65591200d00caa1031100d810081134070649600c3c104d4031a200803070f4180d100302e240900190b010b01030302c000c0360407098500c0c0161040115490100103507030007543c1 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 524544181 1250 524542931 524542951
    0x902031b07021309050a1e0c21020f030712080a08060d03141b010501060507151a0909102d090201051b1c05120a150315020919060e040203100e 63
    0xa0b0b42008580b45549084500e000200b47c020f040240b8145245107001c0c941c070038025828050050b505580b00780c40b01c4413500364120303030f65500005882d00280c6000380d203400910030716490701456802c204500b40100b80d81c0c1815101e2180a40c0c8150410903d0004100c0180100340c0070f40081000c15245401400c0c0103c035110030304031500d85034619a0841e9000d8200300c0124000040c00c1003440030903010280070f8000010203220702140c19101d60081d242281c000c6004a882602140c0481801e100c1e2490b4032003880f00c1002040307a0034440502d0f03a10072860851040402404400765500580a160356841e01a11540d2404104101d41c102501804c60000224000d1140080c0070070449480c88110b50350703681d60b03240c03a030284920100c1196400b9211450541c82d08901030784805407412500d00310382d00044c0800c88000c000ca2040040d125056200e23030310504080d01005802d00b80d4881500395102660740ba040140120203100032031000362036a80f4035404151080100b50500107000d60300041e801 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 524545431 1250 524544181 524544193
    0x6050a02030c0a0303270809040908160b10050603090d0f030b0909010f060e0702060a0504030516030906031b0804020d050c062701080403080f1f0902031b0702130905 73
    0x42400b509000c02100c04500103500c81a104290450441070001d04050240c1c80a000d002c0c06d640d2459503115542249016907103d2240e50b003809002002d0700e042c90700e500d0300049818072a00d01011100b000b2a01d040c44c840c0000d60100d180e007440d600741c911a07071811000305000c0c90240010b441c50b40c08000301208054075080d082e071441d1280500e04c0c1c0500f44107800800c4bc80d00d14800e81c000d655140d0000b82c1d1501182040014042d40042c0c11900551000400107240c0c03903600301202d5512546001d141e02c40b00004d01c400c2010360002805040f16505e50301048076000d0b20186814088014500340002106440420054900050b82c2100d0070b01c10800c0b01c1000046901190340d9402c10b140e15030142c0d8484a004802c1120f0a00600c5d043c0d0003468030b1606440c040d07801034001d11029000c602c881e00000b0000e032030f2a41081030380702009c14010040310915a43c5038580c0180d88226070f020140400380101282055032070342030740c2c449503000304555040c503041150300300200340109050315540310351 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 524546681 1250 524545431 524545447
    0x30309040515042901050705070b131a0c16050f0105030a061e1508070c030e0a030204061e05030609030304020112020f28080420010c06020a0c0218070906050a0203 72
    0x1441080c960302082003140204021a450900138403c15102e8641404001c114600010b00040f48100a40b4600c1410544401b00d01603141c5600324103801c0040118181604141001c9242001d845403500c0102281e50341e1441004c1c40e121542c0c5841100c0d00f11400c82c80704103c540c0030760091070340901c2c40c100000b80503035200c1d4005070303ca481c1110f08084941840042c00103d01c50441124543e03c1c03401c2c080607034100540002d1005440c1d410141c01c221030790300c100e882640c0f490100c0c001590005d000740103e540384c103503400c44a200301c205000072002c108000192410040741c43c80c407903c81c41000c0e40c1556210740054070f00b02ca40c0085039442036400c0240407a2924000d02602d000d40c0d040001110a42190f00d803000312030030010440e024086090204000207070190440c10800c51815840070242c030314840161024461030390000d020030b001040080015600040b02e1140358000c0300d091034140c0d9031404160880400356080000502103050520581d4010300c01042903c11610440b450704602d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 524547931 1250 524546681 524546689
    0xf0e07050d21080402102c0d0b040302030d1a18090304030b09030714011b050c01020918060405070918050711030c1e0d0507020d06060b0301030f060f020702030309040515 75
    0xb551800d000402c61101c1844294180b0200e814250f01a03070520105403040006581c0c01e003508080360072007815280c401d8481e1030303e0384800c641c0800e9014a0700a00d03030820385806503c9401c81084008550310344200542c4001806419038101d01001c2c0401ca92000815074000f03030640024035030340043c4001c200000000720b48410140c851441440510b40b148064030381442c000000000c44019a07061140381c1540c052085541c003603072201810915034034012100c0042c0039000310809076a018074240158103880c05038a00c21445088222001c1005595210b8107942004c0070b805100b440a02d0701c0b210000050160703001ea1f41021302c50901c0b080000e010f42102d440c0d40d01c10540071f103854108030902d0304035030901c00c45505c1048103e030141c0700c0410140741c000c19a010f900b0703020b48a00c103a00782180038492568010f5014101e40c0c51080e03560f6031a420710100c600c0d401402222240c0c580142d840c501c050501c00e50b11a01e5005018615100000d010040500b001422070a49100e044000380d09a0b03403 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 524549181 1250 524547931 524547983
    0x102030f090906060f030c09041103011518080d0801080712080406080603030f0f09120606030a06021b01020415020d170a020306120d0c03140f0f0f070c060306090f0e07050d 76
    0x2e010350b003248e82e600380009010036201e40060400820f80184014413030342254050200403468149082814105690403d01113450294010074040c06441c41c1c108000c0d501c600c826043e10242d40446000654400091a002880380406042c3c1e200c144418010301d40320300d040326001f14000b4203c9003801300d0114500540e902c40b0030640c4190100140d142c41a0600d0440303c0c00a21420300903006525018001c41e0b290140302c00010311142d0b0018245080100c080190103440b044000219110b98980100b00c20b195040b800c110050700c261a00031015610a103004030b0803415511061581f40c4402c1ca400005c1d4002a007030992150f00b041c044000c00302c007005003540ca400c4580c1e402d12601e4007424090201e9450750222940000104400318588041c2004c41d10805581000d29a40300d4442c0c030002c12034000c10700010605003100e000052081d505801140984402d40d00130041500c500034a1401c4a026207501002e68010300d9007007102c1c1c913014202d1020b80340140040300200740d4082a590740c1c10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 524550431 1250 524549181 524549191
    0x20111040b07110d151e11040302011701080c060d0207021008150301020c060403050702010908060a140a09020d2a0f1508070c1707050604050105150102030f090906060f03 75
    0x840003140c40c0051001c030109850348108240c81c003030f034440b90b2516217000501200d076044003502e40b0341030058000046032550106009000208010706809402e08408942c070910099001441c46500c05256402d10262581243c1c4441d0046c80081c1084042c030149400144084041e5170782405010056140c0000d1350a07804501c3d80c5e251141d00c0e10480c01c0e0301c0720a046074010300981c41404042075600d00000c0464010350035007171460304d0b81024030040f42c001c2060340142c000b9005842c24021102c031035070050310700c41e008104d4800782035940085000c125082c000c40694400003800d40100411300c88407201d03141402c0c050750068401c40041800611007200d81c400c04d448100c40004000445081c0500c0d080385450386040840c03418080e1000b8040e440b0081e02400d040078024900d1642000203044518866005041d04d000e03161900307081d4020401110b071149250068503040e00903600c00700480d611003403e6840d07142001d00d030105101c0d905900500c81c03504000104201c4000c5099403014612034 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 524551681 1250 524550431 524550449
    0xf11030d1d0a03020606092805070e18061513170c0d02010507060203070c060f0209010e0907200a230d03060e18150a140c040602070e0702011104 64
    0x11014030000301c800c085215003010150040b8644000095000c0380c083e40040c8101c0381c21301280c40e000c2c3c0342c100076003074907411403102d04554041c01d001c030a00d074001d18880d0b8004e0710703910b100c01c810200703008081c070b4540040240000120000b40c5646454a0f489070f0740803081160324100720308601c08641c0e501407604201080002d804031a0329203501009036819111003900c1c015410720380790b80060618000c0c803200414141c1c0100001c2c081e14403603240300c18042d81102062043c8000e03000d501000754000c41c0100e000410300c00003a1150700b44440c45030f008000e0b0360f54a26212803004042c1c0306201c000d1000100c24000e5071410b1022580e031443d900100450005144010000525014035101c07145441c0b405160400d0b508004050003590303080e84c4601c0501080c001030090030101344c00c0100385c0095640348010f40042c04009406035120b1030307615a03281301d01d075001d44402c40032040c10701075841442c00591001d4010711160b00041e07000350b0403d60500011900c1d21a002440b84141c00039001200b05d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 524552931 1250 524551681 524551691
    0xa1506260c21070b09030604080703021c0e090901050f0c09010306030c090c121b0c0312060902041505070f23030403150b18010b1b060c0901021c0801060f11030d 71
    0x81d1075051040e039000300040c045070703440e05080c179020a840b680d0061024004000100d03501d424035009020b94142d4040c20704064090401401000d080b4088c49011540228064000a800c0100520809010303500000018407d540c45204907105a07000c009010f0415807112070000016610500d07007c0501b040000c0485d04200341d142c000d2102e07100403280d441460071f00d0201000820a01501c948000035854240500710541c01c0075500c450f008107200ca040c42c0b8008000460900e580d010740103507100007038400c1000c62000c40482c3c4901503503201805004d80325084900203002c410600300c10039035004054003e540700c603004904581082d031045d41c0f55084041304180990040c402d8590300c0780c04850314240c0c1280004628084c140501038008121000548400c0c43c10310100102e1400c22404c08840c50307846c00244506070758209401183c09031003508200424075000d00c440c032035010703490358564489a10b0305130101c80d800b5142044900740040701c000d250340030406200402204910001c0811 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 524554181 1250 524552931 524552989
    0xf020c0f060709030b040818060316021603080301232d0925030b061303050d0306030503030a0b06120108060f07080121080f0a020a1506260c 62
    0x105020700100848100041c0803014000510000c071841d8115800401e01e42e190903500302c45c034800020000705079910080100800500c140c50743d03159011215180d0a40748240811511040c0032150360100031f0101105000601061040088803030000d1070f550300340007070322003001d0100c1c200100c0324006502007a0150034044e0944191084000851815591014141ba0481c070720740c01c0715203500c28520100c0506560b6440f240c841c2d0440702081c08002d02c219655010745a100d01015000d1100300d070300e4054450b074014030340e000344980c6c022030b0f0300940598503695981c061000207104540503168042e5081c800e00700001c0201c2441400303070952034000c10460400e000a1145000c0080c5a00101322404005000c0603201c80c68010003801740c14800340b80300441d880c12408500a01007001d60583c40401d0041042d9800601c814080c0d014000c2c41601021058180d41940c90602900f0a40800f181b45000700b0748070700d281f40380314070743d100d003981c01e281d80e90400141120000000000c8990508620746 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 524555431 1250 524554181 524554183
    0x50c030a060506040b0a031d0d1106061519021005010e041e0302101515091a04050303092b03090617010f060c14120304230604080d0f020c0f 62
    0x32000e070800320f0300c941c1054a02078900000d8441d07480d404d0101a202c00020b200c107000d513100016048150001d6840705041388900170b254080d5904a412242f042c1004103110b130808503a12640c40c19045940b500c4c01c02c9031319000c07080d05002c498241c1144201c0d000400414a03c0c803545e8080c0400c03400c021134034100f40c145440380186401801606820304440b40d0006500059402ca4a040081012a54005201104030560000d43c086107400618400e40c9803013652003410b80041d110515200084803052410140d1140154000c098055104012200345032902e01031003050355007190204524400080b561035044c42841c0405c40100c0d03c00380080c04155040070b111940c0d941320703098000f01c641c5001e10054150140c1e200321028400b98105100c2889440c4c0d52507a04101a03000301e40900c038a182000001e98000c840c251207040d00710404512400d004085a1104031122005001d207445e20b44580d449030340300310603911300c40350b40f004a0801c2159600103800a540f000002e00882e0340518042 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 524556681 1250 524555431 524555441
    0x5011e0c05072c010e13110604030212030909091c0503130519110103020f070605060102030c0703120801090c0e040b01020102040f030c051807020714130501030803070f050412021c06050c030a 84
    0x11030b80c00c0305c007508100c0101c8000c85400b0415422410f41880d408150300801c085105a40029410000301007800c1b5031f104001000302445801915800301a40d101ca81c05519070304582c81408650a4540490f010745210300701031a007218044907240164a1b0503507039a0304d40340310b000e480e0b1900e0124803006024081c0e1000300a18210080c2801c0d45411100f0b81c851000e44190080182055603400102c0d0660740f00b0070070307102070f6010340e0102c4215545900313091030055004109280022041d9001107014056400307122080c1a070380c0c548d00344188840042002400303850350013504541d4244400907095858100a90055009043c4400501c0c00d10f0700740700b40228299003048802000d50140302c0c0c1e440c3d002492000322005010fa8803071403050b4200080442d4002c1c0c44101d4104d0400001200380b141580003503000d080340f9190440c0560309000e090f40c40303000c1e5129441116610454070000340c18044c1548042d01a000c3c098115030001c0d0fa210403c07110107483c003a030706010210401091000921030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 524557931 1250 524556681 524556689
    0x313050106151e030627020d110d060b491d01060b040308031009050c03010816060212070f0b090304150203030105060306010e0f121605011e0c05072c01 67
    0xd00285e410b1508941e4101400c1d445950048420041010100703001c0d411f5a5a005001d0024013944800781c0007440141c10025029002903c0e0000000b0214000c104031900350300740390f8085410340007041032101003a00c1a82e5118081c0c0700f040f1700c0b00c1407100d840480a08a03124500004804650000006510000c1103e0040c0c980c9811010710004d036030076047d18116540003490300e0307885c0d5a44030400c40c00800e991003c1042c07070401041c002c1401568001c1c505803066881101d071010000150140000b00707a220312409608803000c818201d46c1c1d8040100f20f2503000740700003111003c042e960400180821034072400d294001160911a43e1071000200e1418080c500c011804c55040c07000041c3d2520003d0042c40c1800210401d02d286600c80055102a0980c01031800b444010611541629a4100c80365400320b80300c500004035403903008004282400c0742040c0500e58990320108113940004280b403050320248200000005c1003e40d44100384400750001c5984640d10780c10009000c0c2410060700 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 524559181 1250 524557931 524557937
    0x60507021203060d14030d0906020306011214060f0325050102070806010f0e06010e03010e0c013504051c112404060c030e030406050903070e010b0313050106151e 71
    0x82804100d82c1e03445000344409402801d0340440b280c5040045d86140700c0d41e24940c0526040c90040d0341441345c242d014500c602000c4c1c0350208032813030030744116088850074244042c403040404007003210b40c28040040800f81c1d40280884e6038900c0c02640300589050316440000d03001c60040001d10039564184a01c1d1b0085c12008000c2416505113a04000c00d00801c0c007400010810040020781240c0c8500292560a000030b402005030310200d026442c1c80307580440405007c00c0076190303040b08990300c241e01d0428a88010800415010407009207448042016106644511868403034030fa410036081450907100c0f502d070f181c82009064056840d0700308a0700d522000c0706491003020f4015114110160144d1141d801781001840e0714103140e05800401c884100040c1318400890086155a044802000c0303c5d50100c0490380310903681d10140070182c4090213606072a00c418000318150700100c0881d4803050340304100202d18a42c50f600540400d00300c0440040c000380708003081c0a40580341d40b960801140040ca = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 524560431 1250 524559181 524559187
    0x406050910090b03070302090a05250210050c0d140a0510141002120c070914060121062c09011103280204031a0709060e040b01030e06040605070212 65
    0x2464440c1c051024492640c985480f000d00b0a51650184580000b07107a009001013181e06085420744000c1030212141524034201d0000039103c4032861050b0780e810402c940c001c0c120a071114040c00042d04018103115201e000c1403246410088541c003500e0070b2001c5801c07210542c0d140180d0b50780d007a10405481190a40103103001400b07440d07009030014002c04002c2c1c403009546c0c5a006800c038074061211344041d01d5101e0100d442d941005011131100204c6442ca00f0521403104460200d450fa160107540301c5020910340c1203030003000d4141d44903024040503942000140030360340c0d00032680301c0d01c4030540e00391200560404d0300f800406649900c54104404800811031b4411505081c041480094100502130040480801482a000c03154000c0d6900520007991200d90b2403402c0c00285804600404421094100164400e4803440c5040111542603541020b04182041848014200b9091050416403903001d408170383c040410403503002d284034a000090a2402e064020701f044213040455041200070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 524561681 1250 524560431 524560441
    0x21306080915071205040b09150925090504030302120c0702010c110301090218072a080703111b130204030b06090a09120f0306050a030812091009060b04060509 70
    0x201e4070000500700810011a03126000f041e52454203100d480c04801c0e0806042008014010001c0e500031400c0d602192821400d50041c0c2850342c01c21541030007598060481520b80440c6500d8582c0c0c0048406600540d41d0746034039111054540444042d004680c0020f4155800c251104034503500030050f514960078140c840e4002444003100000c064540300c000c0c00300005903507080d805005080e600501c1c41301d41c50103030620b1011001c030465016000c03038007034140004641d4009521604008a0301e035913140c00d01140d40c61190580188009808005990905078003940040258001a082c0d030500703191441c48810400692590040c40f10408900511040001441d04a882e50f00101d044032041c0725981c8285d544401000380700c0000d44030b035280700e000040e919005000c41344a031f55169018000551602c0c00d12901c000c0c984001081c402e010029a10900ba004d00c3c21600982d0440903030316082022418442503d04103842035503000c2c1d48000b40620380c94144541da0040100b91081071082c509 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 524562931 1250 524561681 524561683
    0x210020a1b110d05010605030f03031e04050102190c060b030118020904080c07180506150409090c1a0a02011802010806150409090c05040e160b0a020f100213060809 72
    0xc50511408140554035101d41000202141c4202d22040688540390721640d07420420702070010f0f032142500a000300c0601c0b402c0504007008482c4a401c00c0c0c8007000c803e620208541540c55001030051751555400c2c0660959441000c00c2c2020300e02180da0b80c55549111400c0140880300d40c081014480da00d0500241e104214481101604c4c41e01140c1c003a910b83d846043c040c3c02442030b07080003246400340c0e45001c20810201e20702c0c500364070900c41d01000655680c1003480303000c041d06021200c4484042c4020050700e54141c200e21600d9205104c4103d01c541e980750b0302c0c0a1800d410340704210307030000401c2103441c042c0d091040002c035003568807101c60703030301e8003a00081c3ca0324501a260303e01548110080c0780418401004880041c1103840e804c01c03010b0914108080c05090382d0194031b201d82e00740403203e00d40140024580741c1c5541c2002c1404029880c1c030100b081c03141d01c913001e0003084d4003030f0005461881405006000c40501d00300b6003d41c1e1070025400c3c2800000e40c40c0c1001c01801104014092600c81c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 524564181 1250 524562931 524562947
    0xc18090b0a020705100204091d0309130209030f06091e010b0a050f0a1a09100201051b0904060b0403050a06050105100203041a070f05280305070b130b070504060210020a 74
    0x10307429005070703a0030306810050300742001c05080303d101600001d070020310b0303045942c811411800344e22058061fa07550154030365260b2080354905a0701560128005400d00c00e240d006180b1210018100c40c0400c0d02c84c8441810818121030056880d00010a41c500c02c2030303000c00b28400000d0002c0200460020342001400443c85030127490301881e0504071040007522002146400390043c0410700706014070b90280d00c00740d5481444958001c604140176042131500500400d801075070b500e01e90016007030700d034000001190801c4507030307a41c45915031000044940c0280004c0000e54014001344c0f02401d85c9050890a1781d42c182e01c06401682c088080c80440340e808010744041d5413803e40402d02c02c0780581c0ea200b07018020904084d00040c15102000c0802c2030010b10403c011a4030450200190041034400b00d2072000ca001c084c011480400c8080006040c60800c00c8d030011903102e280080c1919174070741c5098040c044a40d100812400a000c1c0549a01088001d0359040601d000358900403901000800d000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 524565431 1250 524564181 524564191
    0x60c0405031b030a1704150c020603072a0f0c0614070b07020c0907031b090501210e0a230c01050d02030a0608010213091d0c0105030406020c0a0c18090b 67
    0x1402416035288641e030103101c13441c05141c000c1081302c41c4035260480120306a1052281100710018540c540c0c546500644010040540041c8064150340c0c038444250f900605000d4a0962408103001c14401901c1c1c8444041c4041d004201c405c0d4454541c0c030f400c0d01c401c5180c1d080030050191100c030089610200b00f0454403150741c0030b80000c040c0d454246041e03140c54980150641d20039069000c016559034141d1080c1b00070b0202d018100c103490240502500e51030014018140001c0c170312000740005441c1161100c0f00807015030380001c2c40c05d003403401c020300701004e44804552410849001c0250070b19055071000280c034041002d4144900e8030720018042e4401c0c00c2c01d4442440d000b10020365a4112580000010b0801800942d620b05440305081c1060042c1d000d4401c1f058a030481c1031003540741d000c042c0110705003c0302c014812088883c0055034250030041c4201c413015000c000c3c05409a00621a000759540300300120041c1c1d90820341c003c42032079031150740201c10502d00072010340400c03080b680041d08a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 524566681 1250 524565431 524565463
    0xa0b01150201090c060c02040c030b150a270302090f0609071b02030d02070609090902130e030418050403110f070509090a0b0405070e0c0a05120c07060e010b03060c040503 75
    0x1242000030903409000401d00c00b5004507290400010b40c2e503040140e005441d4802c6074100043d000e119019000c42d00e440c0301e9a03030840d4001e00306404d42c0703000a00034080340c0d07058144245880e43c400d00000300240c00c040000300480705151300300708605000c00500d80091841c03244034454504000410f01c4060010200780c02c1051a013400c000c509c00f010207031050247c000d17098610900010310702030b607a0042803040300e000482c0e840d400580407007544281030003d9802000601400b90360b9402c10090501d84502810a001c200800107a01450342e01002201c0b9044001040c81d00c1d0a00300a4a403410302080c0c40425000b164460038880d03000f141c0c200960b00308603800340b919140d91030365504d04414170800801d40c911410600c801d00c103000901004982e1804a119000d41c1d40d280140c000d4086c2c09000c1c0003181c82400300e9071145401401c1039034400c03041142c203030030031001d51aa0020798240c0310055804c0d9654240e0307440641020f20015501010002201d45030034581000b183d900d51242d0560f1001c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 524567931 1250 524566681 524566709
    0x91e0f0606061c090b04020109080109030c0813080303010909020114031521010e010f2a0e01020109150209101d010318020a0f1706070807030203040f050f0c0f030a0b01 74
    0x2c10348420316440f51814100d07000c002d64082454600c00803001030381c0c240d000c84c1d06c072000001c01d0403050264280c0d044e450343d42c007640365820b5900c002654111240108e09102d5554001c17404980410296000f001e08440200f046002c40c00054411b44003511070100001040007080000c00740b04469003031004043e540c09400b031a200659aaa1020b044212051542895101c00c86003005400c500000d00a03a441048a09030810702c600c40c00c0c0428040c1c0318028040c4030f28642c1c0c039003d99402400103e040c00085000300307041e9901ea0006c3c15055000d00281e501088003100b03410f01089200005215062440d40c100d0b4403419001320004040c1c2c02d604064481e41a80342c00040f4440f01d282c690307030183c07074030000035215002d8070b00d822400e002d140040580000010240300000998030b020340701585500310903480d05c00e0708038040d41c0020419111018034000a030000b80c401c208100f040280b80c40603004095600301004554120403040ea4425071249100c1c1000c207071361441480c1102c201030b107141c1c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 524569181 1250 524567931 524567947
    0x50702030c0405070518040e0d121b08010312081506070314120105180606030f130212100f02180904020d0b0112030806040e06040b0c0c06091e0f060606 67
    0x1207804206941c868000d8209824000c07242e40201c0504100041240043c070500b80c05000e000486500d01c03d905c405078003031509081401d00658100c610206510000b082504000341c50b103115071100301b0403c0018000c04010028400c8034200713401b0761606407400b078a55080243d00ca01070240700c540200c7c410706001801c1400c140c0503810010702110f0f00540d85d602c1b0b000d48914680310302424030846014540d02102400c2000c40355404500c81d007401480710b801d40d140c0540c500e046100041c0040c4038250a01042c20260781c80311481158008010f004001d00c5550a17a010265030719420244c10240c01400101000c900c58040104d0341c140c1a5403200b950358444c00018184200360034050461a800400800d440c11001401c0d8031840c042c0d1a03005240d211322080c40700700c030460b04840c01c268100001080c0050110340c030103608112034a0099091480f010105824511f040d50714001d20781c8610510404ca0f0100d122200c110208940070b4032109602d0b10000e42c4808005180038460080007030400 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 524570431 1250 524569181 524569183
    0xb01080c03150709120c03060b01020303101e0b1b0c0f011202030c16120219480f050402032503020d0c0e12031e0702030c030a0521030708060105070203 67
    0x40010704117040f145408007440d0804042c03d0703856002c250b035494201b103501415940000122400340308022912040700b031031f0006643c222138a1081150301d4038040300c800111450120003801d8010042c0903104040f04008103280d246c03240e8003240c94040e05001100c0190b0342e80001c6003410000d83e10f00c01680d203560b400c50740940c41c4541c50503c0004000082d6509c24002c26180f03010031000c0540803506051405214441101d400340c2c0000c0808e000180c17821039100741301002d0600701c400c0341003140c622888901c1c00c51400b404c85000442a0785441020001a440105910010407003a24210b01d18102004400b40c20f0850300044840c800c50340600c1c414140c0b00e6412a0b42401d411581008145d104501c010000182c420b46c0a1040e0340601c58400701d010088100e1304240c9010128101803003110000c10100e40015038103a030701d40a0364161080c1514248021824a480351000d0304508088076840200c100ba41405c9900d0700c01c080c000c11103510380003000f09070070606c2400d005840d22044d20001e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 524571681 1250 524570431 524570447
    0x912030402180f0a140114040c090b03010b0702010912120f0e2215061e030b060c0109050f010c02060105010e0607170d06050303070c0909050a060203010605070b01080c031507 77
    0x24440c40c5100e508000f1180440041c3c1c40c02115000420301c008000700c20b80c0c5050702401c0c043c540022806030405440d0307160a0340319590714502810721000741951283c0164594000f64004515410006100c03400c560f404080c0c00050200365802c02c041c0605501c07152488101c04601d001480b10801010b2034030340c0900c881e0000410020002088006042c2038100c8203071100740071840842c00c107010429405c285035101d6044d503031742d551076400303d03000000d4100c0402283d07203800c401e040d0b4580c02c107411a120740d80203040f818940c000102c0d0002c8180b5085203803074911031902420b03074903001424820a501146580c1141e0342442c02035030f070340560000285c543c4039040d4020b0040342c40402c50f08100880e5006061040d0112604108843e03541d07060546078800c49000501c1c01d0001d4406000c030a01c41e0f4401c51500303000d2000c076000f00b006950f0b510100c0e403003a00301b400130a001082038400c201101c680703640580101800784c84c06592040120380c0d0703030312301c41060040764101c4400241414840e03500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 524572931 1250 524571681 524571709
    0xa0501031401030f2109030614040b07080a180c0303080c070b060f0411070b010609151b061401030c05040b060901080a0b130606051e04080d0e180711150912030402 72
    0x202510184580c05c0540064120300c8200c0d145400d00e9982440a0a40d501d5075101d9038108180601c696110b040480d045207004203542c501c255503540c0c00082500c80c1c50702041d100d20805904000c01d0070760070007501d03030203004000c845090010030208000500001e41150040c40a84428007c60001c00008005c1c1400341d100c3d00011901090038018803045540c024102d80050f15030403041ca4480c5ca18918100b4110a003401040c41140f4031216800b052407800d069034091200003808550b240306860201c0b1080e4000d5640d070703541d000c01744440c3c640303442002804c0c03104841481c540300901c00040c003540310050100e80036669070080c8032496103440c01c91880d80c401946c2c1c204015a202c00000c2d00b250407000001c3c1c1408000c4224203c201d60705421101940c4c4a040285045690311504964213410f111509800c4030703c0c5640b94043e0048004050b00519444e11541301060f885540a882e20140c40b514455070030102092011040001c80c00d40f13001d09924030003d41e80e41d00c600105a607003410401c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 524574181 1250 524572931 524572973
    0x180714030325020f092208131502242d0a0204080c06091f0201150f0602010b01020c0f010e061308031308070302131a0d060b0a0501031401030f 63
    0x41c075a04030300903002d580002807007110100d10581c02d400c00c0c005103c10071504a01c2d180c8422080401140c542c07941403045a02c243c80007842c140c6401c2031070404146070350040c001c840d40407036a00c0340302d5014400300821039103491040362201c2c5d5187c000d2080003030203480e00725204010580340d003048a80d801c902e8000c0240c2e0160103642e00b4152148802584a40326096071030265480c21142481c00c0b1007115034014009190f4031492400201c442e491003100b00140040d1340d40d510821245083c030110100c0240745401080600381e1034a64040c2c00c0d0b401030340b9654110740002800d6141030b0703200d0144d0707100c4901c203103083c800c3c80410300c011419520075030380001118403030140000760500c0008001e101c06c0c1106220721803425a1685020b698403210b01009602a498420300c110060007588204040036080d0310003062228403401180030390521500666445840b009407507002e06000300c1c03580042c175080c60104400d2a581c01c0444d2002d03010b02004160034a5061180c05100c0e003804400f0380d0301403c02d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 524575431 1250 524574181 524574217
    0xd050109050f010605060c034f270c02010f02191b0f08030a0b121509030c0a02210322090203040308060907030e030c010203040b1807140303 62
    0x10500c0c0ba514600680142c41c00e608025010a5608045040d01d01500070a0015814007150380303840d4864590b03660425a9005101001c09640200d4040e181c4042e5410041040180b0480080340c4401255411100c0c0c1808414071440c298422582116490a0304903800110014070041c103c0c050011740070803a0200c1c3c008125101d903c2002c01c0b12000c0d031003058845064154040c0c48088801100300b9020703003807080f4001c200000ca0010001964404d0030a04001400142100007501404503246806401d80c005910700d04c1d41d0b0442e0070b003181c00072200e10046081c8400207030340310303520810290004c0c0507171079004440d00d580d0180d4081030184c2c282001603d8540f001108000c50070003800b49001001084114002001040361007100d004541541c1c503000c5540d120000d01c401c0b003202a014004255135442c0c4c5104a00e0300744080c01402c1c01c000c002603900e00701420840c047c07210151017540b54491002c080d01c00d00e1700004081c002c4912040c0940e800d415a20006401c1d07015080b50b88240d00d0100d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 524576681 1250 524575431 524575433
    0xe031002070803090610030503070b06130c0809060a1503031103070828050702010c080c2d0705090606030402131401060507120f0509060d060302030f03031008060f150d050109 77
    0x64043c501c0350840a04807403441d900c50007100b517000010310018143d40c00800030900407440d018041580680b01400d000041d102248070f001c00c8a0009040e440014054818002c0061080c07065641020a44905025180301e0604c3d1203041c0d012880000d05000c0e03c0750011f1b100317034010f00654502c1904880419100e00b00056a00014441c000041c04111080310384810054000d000b46c1d80850380603500c0c03203407003070803a034030441c8950082d102c4040c544510170703034a402c42004089070340741045000c411041d84400030407010700d000b180340c101c28401c41412041008035198442601e500c144c0403191560000000c88000c401000000c1308848240b070404008601103030442c1c02017689a00c5004862400442108101c1d0300d6000810208002a0100003841651802c030b000340040d003076541c8000901c6540d0f0b6000900d03142058201014a4201004218805101c03240030401483d0702c0d0044c0a0a161070041d102d500213000b005c00015004101030440e050315280001c140c011b42c840001c022400341 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 524577931 1250 524576681 524576693
    0xa080703080601020601061d060307170903092103251b03020111031201050621100806010f0803071506181a240c1f0204060e0904030f0e03100207 64
    0x82282c840e03002d13100729400040d0280c481c141007101540014800da981c44132103400c00485034006000d400402c224440490b40e019189070405000340d0602008584e030340c01c013006001401d105980f0310050240c0c00d600d00d07401001c02000321040e91030100c04c500c605041d80c500802e64010350040103401a41010241406004850400d00549000340c803203500355502d4800990f6a0700c16864030790f890381070803801000301c3d05090300138000c0200130703541000c0380362112810108221030490b0740711003822010b94200003001c82400114090552400c02117400e6050084003036403445442d03002031084c48124045501c1d40c400e680488080d00e6044200b12441c1590551310010340610302442c5500108001c1003295407070301101a5088400f04406101c140803106c1c3c8408154110300b4043d0f07002e00500b00100000f01071404043c64222580000507201c50034000020070182c0b602561a008100030402c0c0408a6004035000b100150780c1d01d8801034040114010a003048219410001d081e400403602d0410040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 524579181 1250 524577931 524577947
    0xb010e0607020a0e1e0a0504021c050f10051e0601021203060609040609020c100b030c0120030705031207050304030c0f2a09051e0c0d020c07090903020c011403180a080703 75
    0x36099041c1c1c00c0c140c40740301c2d1660441e4808e4070025880f4180380d0500c03601d0745104011005640c000c4046e1a204416240550304015026a687c1c0040d80d84104000402000c0340d500c0f05003100e00b4104420900d0b00c4800030359a040d80a100d014910001b20002d01903036120821210081030140060001035654134040006e50031641441e071860150700b50340307000c0d054244100c0b84a10700080050500e140c2c0800113540356440c00c0860101c000487d01e00c0301d44030320b041000345051441400107644d50b404411030b41c168080058004c03030400c41d04000b4440460783c07000040050942203203202032080742d5898400c40d0150340580022280340d80d01828148013592a0b452070881d040d409003406655145200e0760100e81501020780000000c060100c0c038540344080103010010901e0740014640004101b00c5450007035664030044e50507448540080402d40c0c1031100c982040000e00b0704075141000007039680c141d400b0003810141d4100314401c43c0b94050008000d03400100790000c801540d44d00d030a08006000741 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 524580431 1250 524579181 524579221
    0x31e0f0c0e0601030f0c080703020c01020712050306010f02160303030e0313091a0d021c17070804090c180608131505010305060702160e04020a09022b0b010e0607020a0e 74
    0x2e8a403408422082c1014000c0210380f039407d81d609a13450359591401e500a401c4480c000711313550350920044000840707909007a200f60800f51211078a81c9084800100100220100c510454101c82e021242c3c20b94801d034680156039050402142c0040c00d002c50390300e1402185c01004400c1b00f0107000040051080d48408408984200f030380c0d01d001c0c807003000d00c08521055640250000e040102c41005800d1031988040c94501ca42c14074003070215450341c83c0400e0780001000381c8054400047c100061070040c4603400001c2000c0c200407440e402c6039240507012110030701c1440d05100c1c40318005580075001c2c0110300950b59000000b07400044460b12268000c000034001100d8a00c03580e004114568000541e0721401c0700c0542e142d041150601601903800c25014004070307080010b910002c80c010380d140c009400e00d8081e41c3c10340101d41042400d10454215242035400c045072800d17000c1c102c266407009940001c48800d0fa18565901d00c0c9102140c20000c8907413010005414600601c1a06901580007451345 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 524581681 1250 524580431 524580437
    0x21031d011403071110110409050603010b03061602060601032705120a0504030614010b0301031e0f0b040c0b03060315091c08011406030c160516120302070807031e0f0c0e0601 76
    0xc01d0144110101c034650506c041c00c04100740002c2000c001d0030340200d5480b80000d0000b0a1501c104400b103886e013102560001044150f076408080c1c6d0702c1d070420116511101c24039060115411045c02c608030320300f201c0380b5914555168502c010600104114070018600d140090a0784c622084000030220f0304980011901c050400058004503102c4150007410b840c206d611184c030b9030346907554503400c0e6500e00344010500d490700c122002c00700e4901864070454500604942580d490585040c0d10b4480064200603c400000e1040c8559600c000800c0d5481c00c07032003c41c420158407100d1072580b50003031004c005056a0111041c140f10b032a40403c00c14100c0b07002e0941026030103641401c20003603010490301c038000c0e80e2007409200000c000718050111040d01071400d44001c0314100d40c8055042403280c0242031000c1445803c0c0c800c140c2e0400c03184c4002c01192014100050541d078840d44500c4802c182c3e01190341100058034140064500c3e41c000041e8070441ca814026a03c3c000c44140c00c80c01c071038480c04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 524582931 1250 524581681 524581693
    0x20c150705060a0c02060601110a020d0305091008091c0309050703030201090b13050316030e15041805060f04090302031b1b4006030c21031d0114030711 67
    0x18118044c054407100c408142c000d4905540d03001c00444144000380d160400034070961090401507101e00350001c001d24000e03600c0d2555600c80509000489000f0a229020005a0010003241040100d40240f444c66401c0c54022440c0c50714404a024121085010f0f0a0b80a4100c001081603015800604900c0c403c0c01030407543da50b400c201e020051940c803c094100d8200f0003581c0501890070304d41d01c022520038140304441c1c2c590700011a000918042841c1c030407510024052001c44809025162402100101400715150040128280c50801c9821a00807902d03000b560041500902c1175414040e04803000c1103c03802d804000079520751060301c0f456420003020404c803419023080d24244240581450304406114101c170801c0704003819810b5401424100005a0702d19080039020751401180200c0c48206081d007400403141c40d0096800024044501540c12800060781188403d4600700798000c0b0701c69104850401030310040000140125a41800010403030f809801034454003901130307084101c0702 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 524584181 1250 524582931 524582941
    0x50315150306011503050c0c0f0a0203060114011b050c0d15050c0a0f0e01091205010603050d03060e13111c150c0e06090310090b15040b090103020603040201020c15070506 75
    0x600c80000b80038000101c181c091301104064081d421283e000714021004a1510090500c42c80c2448018170040300c080d00010f1080095103020003000b4090302c0711441040e10458a83c0000c4c0400351040e40d50754190041801d02c000f0311070127103c1500c1c40803001e022106500c0031440d0416516059a000070308543c03400700807039050f901d500160f660110b410744400c0305040200c40150740c0c2595901d4550304022aa07140410340501c001d8030005c1a0f445100080380d51401c6213841da0501d04604c4051b400c00d840c00904001400428803403980115081c561032600d40380358101101c0300700b0038a40c0690001040c2c1c190781c00700020541d912100301e0003140e5051810420180b11401e6078a002c04000c0051012221042189080c800508084000408540421030300d502128142c83c3ea601e01a03a6402010342003013604503d903200140301d60303402c840c10061903201030001800d1082c10700000e4096a80400000c00b164001c114a2203072240050051640205d006018400355000300c034121518050800851 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 524585431 1250 524584181 524584183
    0x180536010e0a09050a21110607020c090406020d1e1a06030106031d01112805030103030c0807140d0e0d0b01030f02061306080a1d0d030203100503151503 67
    0x14140c40300e504181e00c1940b64801c140700a4098804107039240d014002c07040e0300107503d40c521034558002500c00784503914180400a005d0144804003018141c0240081164540c0d000c0f81040070f544044504015031f40790740c105107009005008644015500d00711485002d1a0010742c05031910245040c01c0c07015030b55501d4480c04814000900720b811080500050203083d0080d000204402c11078211610341c010101850703806d40350040c59050b003e43c03002800746540e11440f260040c1c44c1000300780e00b191405180c0c400130501d201c14400507040044c0c0012950410001300d0031140d0031600044401850300c0d01084241c1c40303080d48089030003c00d070340303200c410401c0c142941440071090300b000e1856500e1b8078645620405160844080381d0080c01006001c0c102600158100003034895680e41c400369141441da00d83c110788001d0b00d020400002c240140e03260003400501600141614900580c50341c84450041038417040f950402d941c14000d5075414003444d04001441440703070f064092010f0000102900745 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 524586681 1250 524585431 524585539
    0xd05251a01050d240e03030a020d0501120305030c1303050d0e0a17120c15070c02090601090311100504150c290708040c050901080319020f0c011805 65
    0x4081250880701000300d20344c9207103801c0000720b03085004503148102c889a5410359100300c42c3d10700d1056010481148049141c032655000d070182d030b41010282c0c040c03924054460b0100a00c2d03d580c0b128006440900d00c904448507400460740001201c00500100c10090000034030424054010360390600e0010b001c2d5103240c43c408140400340b000c1c0c52582c400382020021036015480341c0c541440b403d400c071401d00310364804440c801c110507503590610070281d20401442c0e0302c000d04554100f00003208280041005640350203c0300c00c08407880c01607604014415205030140b0f03408091012410b03c0762500341d5410211040585100d41c900d5100b01c1c181000350480c0c8041001002daa00c450340e80024203240c00340040980060180c03500901040d562000601d11400c260841101500041044500d0604560104400001f1800a0101d4845055501e5610003e0500c0ca5040140019007101c00c003900f503000c0c001516014181940002c50f41c4c0c0001d0401d2070500300e403d148000806d418411911000d48 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 524587931 1250 524586681 524586683
    0x2010b150702130b0a0e0702011107150b0d060501090c1202070c05060d0e0a12030b0a080d0c0212060106031b020703020a1a090d11100c02030d05251a01050d 69
    0x2224100349450702405003039540e503154070f00016542e1640c1c4000303981e40181070f8010100c03404220894074100034000e083d5500d0519040d4009000d0002900040155035410800c0700c2140c40050352400010000d42c5607100140b015280c0f500e448004201c04400d5080103911741406d844100381c0d0b14111003900d040703104500003e8010740014006203d07526020b03005000d403015004d00406c104048000c1e00341000c0750014122010340044511390a016058010301d402100122107400c10b02d490807400c40d8460101504645c104084110340200710b603035801380d50342c903511030504803003041d0385882002d4004c01d05024400f0408002d1407001840e24030004108003030700da0182c80c017050340740f138054034840490071040c07000000c80c010b018001e01c94603001c1c5a82503490007800481480c06000342801481100554658100401c250500c409a180041c00160690983c030340b00361340342d01d281004100305030101817580d4070241c065940814084e80100b0040244040b010720100c0341d81e14001c003e40030406503c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 524589181 1250 524587931 524587969
    0x10506030403050f0706020c0607030b0418121421180304050103180b1e0109020f1905040305070b0c0d0306081b0130050105011b060c090f031202010b 66
    0x10700000d12035000f84c0503122556100c9810f1810f5984c6182c140d800aa034106102ea1010040000300c5a0600418039081c0741610300b0010924074403c00b042d88418400c0c050401d041c0020b01c480708500c541d40c6c400c1c01004150360540c6450400401403522482e21044c2c0d6503214190707010540c0b00310300022510078141d0020041d80382038a400c005401400034140050307940707110030300c0010105211004441c8507141c600b8000d22140c2200418441201041c5c10001d0303560b1040c8a802c05140c6044211103100b210342e0843c0440031028007048401d480360381c00081c518018001e0002c4c9000741071001d030161000d41026202c84109030703101101111058464010701e5481000701d0784084040e88003040601d081850455041c0d44c840e4010446111540a141d030800c101049441315003613640302d06030150009103095010080308540ca08084d514104018000c05ea807800392414060091040300700412072a04e80d002265176a0404d40000441480e008000d03500300148035030286000e0f01c1201022060ba1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 524590431 1250 524589181 524589187
    0x2070f02040605010f1e02070f08010510291305040c0521070f080a090803010b0a091a091e03060c07020907020c01120c0e03010203040c0815190905010f0c090f0608010506 75
    0x401d2006d103c0d001c0350704140560003021008190152a414403602a001e003400104d0181403400000e1824022540100d103d21640b01c400101c82c0d100c0c1e0704d204c0e032460441020076203800340f2006a0703030b40e41900c5e800203502c2403808031030f56007440d000301c0a400c034201030200001c00704402c0d0710140610300c4d0848804000498094400080744e00503142d01e0740004010a001581e9869a51405800c0d442a0441d106140001ca21035450300d07800304510006c0d0004092005074008400d42490300c0e801005c03c006d109800303000d207494181d007520141e114140002011a40039080214500701150b010076010b82c085c25109000400440c000100b9184010062f519400d00001e5841244020103a4044240c10003680380091402640c090010718000e9004454a04409142c48030080c5402880f0080080c000000c004010140c179030441010b08000420310b000c03c03c220b1130324102e4010140050002d0303030140340c21201c0110303552110b070030000c0d01c4028a0040403141c42c0c00e01600c03a0502485650b51180c020 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 524591681 1250 524590431 524590457
    0x17060d0f0812150a0f1a0906121014061201060305090c0a0e0604060e0c09100c02030102070b10120f020607020a0f0312030c03180b090c0402070f02040605010f 70
    0x10360015044640102185820035160348440001e00c80141c400c0f184140203905940300e0b41c946130029100034058403000718640d0f8a0402116074200782461121a0007201050030000786e11494201d400b0030b05050756100030780c07502c0e0f400e00340c451000780244041c01080102c5202c0b40c0c01c0071012104007500008242855070301e8250704030043c240040c450780d5580581d0500520070f4555501c2140a0100101ca90030303103207081d40a11040791800d0f03001c840061080c3e000d0200c22400c0c201201c001c1c903420f40300d0036580720309440140c5607544c030341a009400d907200107070740410b001ca0003070b005000b2841c08222944c80b030394071170000c4076520504801800400c0c0b40d24085d401864408024900301d8406441c02c46441e03911503040c554007040394011303030308a0a0244070303001c45581f5100d10310700302c03807141810003240f0340000034070301d2030902481c0c01815000e9802c04511751070b5042003c805d200c100100250340e100c2c0700f071800c1d420262001000304c0c0210300703101c004030315507008540b8017280c0380450b80c642404c0062 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 524592931 1250 524591681 524591693
    0x605010e093903061309120507170309030a0e031612060603060617060a051005240d20030103170f160c0320010504140103021309090317060d 62
    0x4002e410948400103105001100d450700c44150900080300c00544030f00d4102c2c2403200d070358522040c07203026620f02a607050010f044080d040800160070301d4030359160ba22900d80b5550503080118500d88042c000700801c00441300000c01400d58109903a2442d03000600e410a059a8500c05240c1e95101c1e46610706c00e10076440964019000707580603160200300d00b41d4a4450300c0489803a90800b801515000055000c500f9080000d1a003264940d20200614038007582c50b5681062507004651141100c0d8500c0a00480210000c10b250403010005c41c2d651320f00f5592000040402e0355a844100550f11948001c012084003942c0c100c9800442403a10301e040b0056826055011880750421100144035601085403c054549901841862010850b5085003482070145441070400362000110380469110ba076803050542d07089071449146290740c20709100040c1c0c064080e801103404080300f020000100b080c3c07039410070301985010b80c842c60100c3d0007403410125000401c580140d044030724800f0300270000c0c41d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 524594181 1250 524592931 524592961
    0x12070b0f09040b0a09150f0e040b0618070207170f06040f1a15040f02070f060e0c1305010617071d0d06050a0509010c0f081303091703030a0605010e09 66
    0x1d00000d0701c203c07540c00260010b100ea4201143c03103980c0e642107241201d200c00e00742c0301401e0703c0c40028036018a0014049040100100020400b0242502003610b5455040801201d8030039844a01183e10700080002c2d13440c1564070500c0486004c800000f6601000414503204100178407015000075615500e0b29000407001410440c0d5850300003403d01d40501e0f5410b2140d00555054081799100280303001088141c5005001c509900c5104010b140002101c402c001c5007544d6000030045040340d1651140c0f420900031aa800386c000d221900c0012000010350b1043d8181c46040d181c9848502e000120346564242c205c44007070102e210f94144600341c1004200d0080380b0000141203200310030003552541c0030307580b00780d070354010341c5440e50140410b699080c09140e141d000315240444c07119034000c0e0002c0c0403402c05407503259191034400c42007003031610400070074020b42980c85442c01c074107245010441d502c0e442102c048800c5860004049400c0d0721401c0d0b510304081c070060214003180c0302d421002078955 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 524595431 1250 524594181 524594197
    0xc160809031204090606020c040e03090d0501061a0d0c0e01050703120f0e15060306060a0902030a0b0405040503040f0b13031202010e010e01060303080a050112030c0302161412070b0f 80
    0x481640d50303191a0900d200b00a001405614001089282c03520340c0c068988940301c040f01e44281c2c01e00d2030010700481c0000507903030a684115003004c62092142080d50041403140c1040c21082111246004128a09402402354940350300042040c58450a000c0751408074003450180000c00400c41d103008a4421040e48007144810706002400c5280110707000122507004010510704c0e04828030b03040c05203403621005503000106a024085e80d141200000303103c40d0305405008000b03503000c000f040c2801102c1e4004080b0103400b81003002181041d00f0095640d4200c1d00c2a40d501d94030340180455294141c0042c0c8905400000032650601d045a03100d10b181d0b0042c40c11081190342e0ba0f410707040344d00c20900a190328403204000005115040d401c008110745030003081507011500306001002907122801c10313151015010b1a00362111401031400f24204003021100382c50343c1d012003c01003070216001c810169011011507107003403600b90349060036480f21054400d940d605c072401c0c0b1198108010030b400070842e41d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 524596681 1250 524595431 524595433
    0x20a2001020705060d021315170601080105060c0c0a030803010810020a080403030c110a06150509010305030d0e03040e01150e04090c05150c030c0c030d0c0c0b0912060a0c03050c16080903 82
    0xc51f00c40c060901d81400795102d084201001c1100b14881604540700d0102100300d205145845d140c074100280c0011018850380d8040c050009a600301050144440b05c00044004e1000500540c2c038200031100e60820b01030203195000f0105162010700702442118940513131500d80b0b402a0b03075070b610140c00070b200c0e524000050008144601e55159014481030000354481c0300002041100202e240c508103145400c000d004120190043c001300742c0010580301d80212002c40820310100d20540d56055000e20b900102810084d00004034115112948041e101d02c0c01e69510321501140104000680b1180c1d034020303010254001c010b102d181442c50b01c4011843c40722000030314080c8109220f51070755101800494054000e00c212040b5441d042c0250715100c1d58a103405017410080c1c3d242c510421903144240f2100300000540884c980c1c440d81c46c603d040310f2110003586e805280c40c1000d4805081c43c0c003450800686014001031046203000191021062148040030701a445565041074940c8484101d42d49 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 524597931 1250 524596681 524596687
    0xf0b0f1e0607210305090f01060f180b0a0f03020321071103030423120703020901060503060301060302331c0906021210080d0527040b0301020a020a2001020705060d02 73
    0x14810140f880c10340b0b11140740c0c3d4001010310b88646003505012480c114000b16904142d0708002e490022580781060380c0e0254a07000301c07201c001803218002d20030702c1c0c4526007040c00354100007860380c014060801224000d8050b940004510400303a6401010130501c1300440c401401702201041d8102034050103450b018040364549601c4600c0001e1050f54503180202c10708030240301c0a4242081d036003025030ba428010003003103035505603030000d10301e024140151010001c0110015150b640d094101307a009540240c001c1d2101494428542640d42d2007069000d04800010300c0c40c00301d440040d040391800c000d1200b1045030340d03265040907000f604004030305940c02c46c1c0038014030040b01c0502000c036002e403031510009502d041c90440890b0500501c0300c1c1c0007060010600114046000300c4c11018028440c4502c0c41849250060008000717062030400726800d5071021864071101c50300060914070081c01400d90340d03240003005080c20b0140c101521640e00581101c5010002e50510310040c1c50225040c03840541 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 524599181 1250 524597931 524597963
    0x81515040b0913050106090b06120916030b0403170601120e150112030210090c17030d050a020a090f0810020a170f0106110109200a090f0b0f1e0607 65
    0x8118001a2041c068100340e10303c51604001092003000d000304140c01080c030000619100041c2c460007000b00000c900020140041d02c4481c0038018600004182c081d0003000e29181d00702030041580454048000ca803101c20900d0b00f81e00b550442600c1040161340d840d0300d290140407240b000e0200701060342680e102d40816407240340ca0030a000c038003a051440792158000d029083c0286006045448400071307a2410740c0c46008195070100c1c100030341d000c03110035500002c1d66034030143c6148640c2841c20401441c2031705210004107140c0007031510349034554410f908161250354080d9180180c2c81003241d168800d25610501000c640c020b030242501a0a01009002818030a0750308000101c4400100c01030081c018082c082d0000c8a000c0516030710340c001c209004642d41ca00002000800201504070b000c0c0c1c4000c140d0f40c0d20b42c03604234041c0c10103400078880380c00c0503114200a0100c01d00000c9c800c1c501c41d24a582141040c7c02c0c1010310306030000001484c42e41501c148402031b441084155250b2000701c0c0404 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 524600431 1250 524599181 524599189
    0x2702060a0315030809040b0a0e010b090109080114010501020d020313090c0c020d03020d14070b072109051506030d050415030609020f03070306090203072007030203061609081515040b 80
    0x1c0010350290702e0482e5174410150400c400c0380c4c50704501a01c941c4003288284802303822580003a042d03860310600f2650752003080340180c89241c880c6d40100900d40c01d03c400c6c000070401440849048403000c0c0c013220740c00f1507100c400740c2c0c403402140c20380c071303552103185204000d402c0240e004070f1840c1d50242000c00101841c0c0d004980254172805090300036072b10000103c00300540c07103032480c405050401000340c20054503030384203550044060f101030104a8020b01d00d00c009444006824240c05c51030008010304203680c505151100409404004014034400008240e0704004c141c609522030542d0340c00c1e103841e082c106001440c100c1c80c2d04807400c0542d0307240007240e500150320061000c243c501d04529264035100b8002402d540c6140c201c035940900500902041640100310100e42e0b0340d41c1c4202e103103005440140b1901d450304982c800b0758544510003c1c030000c014002c1d00894a808070384c1d241d2411035225001c02c0d07540c04140c2e161400c1c0c2003036103001604c90700d09040d4114200c40700500c0801c030b40c00440700203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 524601681 1250 524600431 524600471
    0xb0f1804061a07050d020307030e063103060f02070b06190506040e0f070f021f1803200c010f050c010f050a060f1707050402160602030702102702060a03 67
    0x118100100001d080d40620500304480081031210781b0055180005640e001040207903078810b0940200d80c00703d20784c61f594032603032407003c0345050705400022054940fa0b11100980d119100944030585408a48035a200c140c7c021625078981001c5031525031b072158400d000a5125901c140d403d400034190b8040755556030080100024140180c521070503092112120008420140121040c02001c00503c68403a4020400030020010005803041c1140c2c004419801741c00e00803600420041002d540004040d0170010045d55084990480a60b0440444145613208103003405c140c080780300d040301000c0440c400e8000781440f00c101000440d02600701c86102007aa1010750306440e02c2e84d01d1701c0041c0805c0b2003003030025004140040111601c2c014502e10355131207020038054503001d00d400241205024044d40c07820410b4541c0301504668070320702002c0c000e481c2d000c40c2c0030300c0341181e0802d40c02d00c03503171035150300d4040c00327001509000145d040c6180d080151560212446009160b09c80c0c4260200140105003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 524602931 1250 524601681 524601719
    0x50d03020301060801060c0c03060f020403050f030c150f011517070201140c1201210f06050103110f030c011107080d09030b0106095003070b0f180406 66
    0x581c40b941030100c09403055005800500401c4400c00c80200800c0806c00c09804483c0c0049000540c1d5800380c0c0e804020b8800da400240141c40340c00c50f41040c0b01c00010003011a646040c040d40e0002e580d1003184142d040c000c1e603892610031f511078014008101c0407840306401c2216820402d0801c40d8a01c81604640021070741200580d5503180c2c0e41180340301710051168480c600a020314933060341401e005030440700602030240d1300064500038040404040007040c01c256002000085010340628140c0c01902003400100c981c117000520151450030000074032044554000c01410756800d05200469080504070905040b40c03203030100000b40041c00f0700c40d500c41804150783d940301841c00c0d400c29244060040e1304c0a030801120750000c0044201100303d140036030048031409140c50001181711103140c01441005c6a0b0340410a8800c000c0c9038444110301e8102400303505440c2d580c1e94071040c0d00c00720300031583c43e62414101004480b00ca2214244900c80611006100045040d00c803440c0c4103111550b610 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 524604181 1250 524602931 524602937
    0x207032915090901020306061b0f01050408030a0e010b1f0e0901060306140d021008070311030c190e0303090607020a080304260a020112020d0b040c051809060d1e050d 73
    0x184210707450424446095016107028000d44c0f0b1414a000400d510f846880c1580041206100e401c0b41c4030b100600410303040052680081c4110300b814189151154025280301250030314104c0600f040c00340c107001340d9201c030320700408014a20403130f40c41d1060403040806225007000100c3d001d85a19642d00f4400c94041c00150390001410760508200000c244d10700b0700854828090301c05048010380d1030210868900119203060324903030300d591a064001c1c1c9040e00011500510120400004042c41f0000e800702100c0000c80818180c500d40080d50369095081d0800e4140d001084610102d08008004219051000d081c440020342e4406245007190044c0d048207100482441d400148aa203621406c2c0c11512114060006000b0950020703045400c2030704c02d511940d0300400c0020b0001015800041208406070052104950801d40201154007040304c0c50100c095503200c02c825802c102461521544025001c269441b200342c4440600c5003a01c54601003c00c2081b000c1030000350140a9908260000e403 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 524605431 1250 524604181 524604211
    0x170c0c0109140111180d1b03030c0b01050603040b01170709050f07030b030706020a020f131b090b120105040e28050d0e030a1b080706080a0b0105040602070329 70
    0x4000e50079540d040140002404c0c050006510f031180800042c0100f4000322403200000400d85081203040d00a421410442c0520b0b04c1c5c00801c0c942c1000700d0001d02c5109182000460782c0f5070b8104551400183c4000d0044d0b60003400600032500802c00700049070705140102e0300b043e035031a00b060301551400c89203031083d5a200818409a680c050184184800307044010b8860316041090003544c9440e06172010b8403803104c100340950710ba190b0101094805580b140c0500030385504800c0a24868800e00c00c10780010701c100400100310524606a400c0d030941400c1e842c81c90792800d81048040c4c1644541024180620a49580d003015042c000300c0b940014081e01c11140613071801e1190600515221181c1170100e0703020740e86113a540100365a1259071303000d091440160310744502c40c11078407010f40282c03540380300c0d2030000b203403ca07040040c4602c52400808140155040b13000119864000c602c22035000d82d0100c0807d20004a0030321119030b07903030f0540c070421150b04580000102140c02c15115072001c0c2c2501 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 524606681 1250 524605431 524605463
    0x507120c172106040605100804110d050319091406030a0e070609060201061a07030315050a080c030609010b060a050a03020f04090209090f01060e06130810020417070501170c0c0109 79
    0x511410341c4072030204c0d403c1000d9490500411a40c903040c0d2182c000300300c515030014041280b11814640380d00c0014005a2840b44286401c03540c03540200030442d144d0805030f040304581403195840704266400d13070030020383d09a00d0000b0700115400240201c04640d0b1205110b58051304104511002031006039a1070790086d2a103c0041e0845060350860f8003032103980d907842610b00c04040201c078007980d407500c0c001803200301c0e902c1c0e0892000316541260351f20103c41038001070100000a0024840c0c1406c0301584c00d80d855001d02182203404078440c2c640c00c540c00b80402c000040c0228042c00c040c0d16541009031803c3d070303a6541415154060f800c0342500e240e01050242c01c3d82030000d0210303440032a5111109140d41044030150100358040d02d85031080d0000030390382000d0303140d090f1110300808880c0c017240c1c0c182c50014000b0300603400902842000c0307820100c00c080005400610402250b9041c1c4666440d60000c04e401c1146d41c00c003e0a10390000c0b410025400541001d03c00d0302c0b0402d000710306040b41c640320 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 524607931 1250 524606681 524606737
    0x50606090a02030f060609010509041e0e06100302010e01110d0503040b010b030603102f0d0b0a0308030a02032d0a2009040207030e060301030602030609070507120c17 73
    0x1c1c140040030703441401040240209a801c00d5040b00d0111100c1c2d84a4201c580100c0300c40c410054a43d80250800841441003020107000c0300c04e0841c485d5040c08207229a608255461100300c9000003c032110b00c0c0104050b500841e41200a040185040b18050107807469051900c0c5200b0302c983d0020310000100400c3c4000c90101d5409020025804d030704e14101080001e40e90907a640c5c4040c1c10564542e202900396220741d1000c5210700100d40705a0410100012103145500000c6000e9800c1e070420010744400c1c9032101c00034003078941c08a00581940c440c00e51110082d003006143c800003c0202420a007800d081c0440c28030401281c418240c503a04e02088001c0981700004030303941034250320f15545c1e4060502141911059001036a0041c0c0302c104604044900082d0240d55a8000c0c9000001000b40802600190710804055600380c040340c50700c0300d0890303080c881c40300c000d000108000443c00e80f01c0d200b02a0300c40a680140a0082c44056504000ca4070360b004008010b0720010389904008a001 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 524609181 1250 524607931 524607949
    0x60906070804113105150301060f030b090106030204090803060406050a1401050705070f030f050c060403020607080d200909060f010c0b1f060e19030203030d0908070609050606 77
    0x8452800010740c0c2080c2c0e4855800c003101c15a01403082c448058048126610086035100342281011010102c1c0c0001d2203032802401d0581714040b131100201190130240c01d050051303804448005c01f100d080c0750b04d9915005400e95015100b400b2554031404000f01682d078030b0094651490040032102c0c0c3d02d0a0150800007100c80980c00540034400c04041000000e02e5440d250b6440700e400c0c01c02c0c60340d40741c143c5041d80c2031100c540c000c1100000383ca071002c03041c0300f240c60030000c44a2050003201e103072010000030000c09000f1444001d40c4000c0c01c01040380001c003140c016040454101c440819030301000078000e030252046000c11884940080745910040c0b8144090582144056404102d0a19020002020010030351170140054000da4049110340610700582132480b0010a83c2c844181d4071640010300000c620031005110f503146c0060a1224800845004112a070007402503281c0350001e00d02070054813030554203440d031503002d014120105815009240740584030308040d0056103081410030580038 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 524610431 1250 524609181 524609191
    0x71b0804092403081b0f0f0706120b0d110d061e1406060f090102070f0303020109031e0906110a0b0103052407020d1b080a08010503010b010e01020c0d020a1502060906 73
    0x14440700c008001103603c010403191011a4070f00c0c650307003c0085c103440a14181004010780c01d5480780301c0800d507800d800490510250344155446400c00c066500364a401e40d03400c0e070b00855200302710700004400200600ea9101c070306000a414200006225101d1004039503100c03003401000203070064842c245203094802c1200300c0307003504840c1c4494249003010803840d000c1c09086507069500090300c800aa80200482c00061000d10300d20000c064903450001e0180078241000c90129400c059018114240c1190001105003160703a0f4200003441c0800480c0d646003801c03111000f40c090f80b40004d022441c141c1c0114040d40c0180300405401c1c080948007640c042d03d5807100700e004180d0701c0a1010355540454a15040210b51034000e024001c845e0071865641c042400c000c0c0784075800500140c50319040300c10300741200c1d03048008100303036600b500055400724213519440740141c001c07407404d012a1600b4004569030b02c0c00038281c1d040454940007180002190040e40801591051003000032000f82007220682c0301c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 524611681 1250 524610431 524610491
    0x6190e040f0c110c0d17180d1505130206071205040f0b042108190306150305040501051f090203130816050706090b0301090e010b0301020310170d08071b080409 70
    0x5e0789651580d103011181e4110324190403400041c080811034600710f04620b4060020300100c1460080e151410307014201c0c405c02e029090821000441d21204c82c03a0307895880d900030341282d00e00f0400f0394503c42196441d80d030304814810140b00100d542ca11b07406280011388070b9000d4055a0314240035003203480242810317204c003458184903400000151148103070b40f40e805042da11110b1440d0102e000354041c0c80d5a4200549510042e52414080360b0325070016405540640000c000035150500300e0203040403222502c20941c05d584204000142c0c0b241d0042d0f511400c051040c0f030703030140d165440c40c1140d400140c05000700208610108140001030000d03100504481c10500083e83c54038803000e040b80414428180207560720001c00054980c00e4104a4030020010021540c03031a0512440c2e04e40c001c540641102c0c0c440c007106040095000041e0110030940fa910381e11210755408008899483c10310040000b4208a810035000280f560006400900300c10b450204400c041c510585440c003107014010548 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 524612931 1250 524611681 524611699
    0x20103061a1b0601060207180605150921060610020f060c071406011a07030c0c030b09010b0102030310031e060606030c0305251d1302030f0606190e040f0c110c 70
    0x8102d40028001c02251805400c200040c2301d00d86034000184004d5000b42d80090300420081d603d000039000508054104484c0d0b941c08a280707021102910a00302c54000d11a44100003154007842e04c00c440c00c4061080344125005000c850000c2030500000341c030310405403400803038904208210840d80c01805101d050050850703624000001000300d41c060551100040000751950a15200340e11010319140c014400b13400c9141d80f4130b00f01c041808100c1d50f100c0365500e0055180c095620120451740100f020700340d0035042504585520350140c01a10106540e00d00b500d410b240020014003c3c04010b00040d20000f0354010742e0400030b01501c00042039040140034500d41c4401501c08c1c8014160141124a0302d03011094808800b440f41d80e00040400e640011130f16a01c010f42c44030b1341c0046106007039650b0150001d440d11414400d6500881803400301181410400c0d609040c4112010b03c03415034010300104030008840341483c00c44420880c2140060380041200c054802c0c20080581611401c1d542c1c1c041e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 524614181 1250 524612931 524612939
    0x60403122006040f080c060907030c091e020921060403020106150203030f0621030903010606111209060f0403050120030c0d02030402040912020d08060d03140304020103061a1b0601 79
    0x1d141c2c480208010040e0b44e4461001080c81307210429150000c0611080f0b07421800d1452a0950394922484200d03412858540d0100b0004001d00401190b0a80550a0000e08070100c0d8401c0c0690050801542c21500b2900034502d500c00c00e4035a03810b080805005401a410103040c024203640c034a4020500102401031054044c9600000f1640d00a40015010400307803101c2002031503000a8090100000c150340609000744103001c801001c94050440007001000d41d80e050569428144840d0307602a40c00104015003030240f16001080149802041e5070b01e0010b41d510008119005174005a132107a541e20303220714884110780b109200b1002c40700344040c150300d054100700c0c15510440034440150364001c00424211340701c83d000510165030008800c0d00180c1038100003507580503465141d00000c0c3c3c51030045012800c04031402050b180d01a80c3d04402c0200d0101d5010603a800940102d041660710900002c032400419140c100c2c1c000c81c581c481d03589101e4482c0f0b0f440340194800440d00c660308401300401c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 524615431 1250 524614181 524614183
    0x8011107030f0e0a08030c030a0801120203031603021011190c110d0f0f11010f030e0c0108040219081f050618060d050304090203012102090a0f09020604031220 70
    0xb03065416103086a9503022000103d94100382c16408034a15110115030003130f42d0ba401001410030b044142e6600820707a82c1c0c0e54038030715004401000c044c4d0160030420000841082e040e890040d458083d0044404081040c1103400448420b10082e5080075408103030b002281400410307090355a400361400c41e044084646500c0d10810700300d400c0c2e62080e810300315890200b1031080b00900e540d03a000341d207000301d425103030134035002d08400f0044640c0014948040b00030707401d00910031400700301d00460040101121420056a100e04050801daa000d41c0402da080c6c032b40c22920103003002920700c02000d80840b00740502c00c08000c840d026a0314140c1400e10041202503254900c44c1d40c0e0042c5034540500c8142ca94002048180c2008000030302503020006001c515030345140c0045040750400204440c1c81070414040b031190f0000c1ca603000f0740c020842d901003403407400d0a401c005161400c41c40300007440c907000d41c0046d4482c2d0103688111111811100d040c80c8240e0070820034410700415580c96031284800903005 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 524616681 1250 524615431 524615447
    0x140601080f071218030f0503100b0a050c010f060602012d05070c08030a05010303170c12090f240901060e04030c030215090307120201110703050904020f130801110703 73
    0x3141280d5514000540b04900c42c000c2c1440000c440c5200300414002d1100441c2100940002a03000c01c1c0d010061000301b0307101d03004480c45038040c10a88500a81400764240e003582c4501a00e1040120501c110b50895000307203e044e059114420002540c0c500e0003102074296041044256800701c52000380c403814014500d50800d0110010301300040640da400381c2501d40181c1c13800080c1c01c03101c000c01004040000760b030219040e07900980ba041c08150540c081014014005c8070348280380b903800e00596202e281000c640759003107a48a01a6a41c2c000e030340010700d2070100304103041e07200d11003281c10051061a43d84c50310381d00010701c00000c0c0300541c1000e1510300d04031801307040101004003c92404060520902030800c0052408203031891a0801a200030b0b0780350020241030b5008031200070510300e400d005200700840f1134205043c1504080c860303141510b06400c1440d075590026020468408001d240d803008000c003602640c41944003c0c00c0090807402c503580f145c100810040b00b004020003103900a144 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 524617931 1250 524616681 524616691
    0x10c0e010203090936100203071706030f011a0a080c01020d12020706020d050906060409052503080d061703160f05030c0f1015050d03200307030e0414060108 69
    0x441031602e80004610b1010401707100c032003020b4041318082c0004501e070611681c9002c00e00040324604a45c0f00383d800220311007628940003003024400390541c00c0c141441540d074054001426241c1264486111034203503403140ca2000004020340c15840700324548189850050a0104028581800d1010020b50354406004103042030104290600c401601346404407900180d004d0000e64642c583c22540c00c014200c1074841190b80c1c01550700082003800d1510443c0340445d0044014402520100800c01400c00000c41481340e5080c01c83d804808641050000c015040d00f1050001d40f5603e8225a4041d0141d500e061000b0341c0c0040101d540000b422581c9070f2806504540d258442004610f81613266104100b03c500c03c50042d03001544502c10049040400241c2c2ca680030b001d001980b00010f00c0161880c001c1a5000d0610b01c0c508020a20070308c40e20182500032048503428804041900786590021a070803400104006007071000b41c02e10707004015240d203445801c1c2011341040b40c0040e20040d80105 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 524619181 1250 524617931 524617939
    0x90b01080f070e0a020f0d090503070c0b070c03060c0311040f082e1e05070c0606050d0507090f02070b01082104141e060a03050a1409030d150e0a0e010c0e01020309 72
    0x82c44551002c1b400342241c0000302e48450400014549150468480d0000101030350005424040059481a00e204903400710703922882c0c0f1100c09007075684590050181c10640b104155549030360f031032111700c2c40b4003c001420708490002c40c81890241200d14186d400b10700f81014001c03802d0103280d041080141c2c2e003402100403c001c55000c140000012445000d8840344c1409802c040a02c2010307034015529501c0316002300010f20046440300b0500c00c0680c503010005080f41c2c0103100412001125511100049810034409454003020f40c481d451118005e8000007600d410102e85490300900c124004640d0641f01e10046080520305554450b04800c02c0c0300300750040e4031a604284002d80c01008070901400010a555200c00d031803000200103150403141c464030030380307042c03208810302d0610002c06200321440b20003980381403c560940780140014203032803161030400945c042007035a03142e00703450712482c00c095000600041000b802400c5d41d880c5941c201c1030220190b400003250343e01100300c40407030409503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 524620431 1250 524619181 524619187
    0x131e0e030d3b03091807030501060e0f1c0506010f08060a0603030c0803041401060b130803070203060106050d020c030430151517031b010606050d0b030f01090b01080f070e0a02 77
    0x18684508611a0621013a4818021140300d001c807071a0143c917902502d1695010000d1340e0306c401c0d040c0c908600c06981aa401a4030058980d80c5241c00100040c0801c0c0f114141c603440142540c03400c0c5001801e800180000c0710189050055580c00c00686a011b8980d00c001d00c00d0034a03685015040c0d111a2130050500c0034000001001d0102003658170030314401c1d8400800820796902c032003014036006550120501801e2070070000708944000140e88100d50001c0c0031b01000d0346481c10680c0d0540c01020000440c1e50240200c0c2d21030314090015000805104504c0500544450211075054420025203052507404a0943c40482c90001002003440c118290010362043c1c2160051010340c1c041e4416005906c60780b12502c803021000c0701030414002c0310403d040750481d0150b030301030913540940111400038000f80003900d6509525040242080c0002e004e980c60510000c480341c0c2910841c542c1602c400762050b0042040e6503042001c20103180004000d40281802d0010083c8032900240c40c0d24003943d004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 524621681 1250 524620431 524620541
    0x8030f0c0705070e06030f061b130e0403020a03030e01020313120e030604050a03080c160204020a030e010216110103020a020a120306050d050607080105010e131e0e030d 74
    0x184101c480d219045003c0b14029a600c0c01c03e121945002c81d040f0b0700a00644e24a01404140012424025800c0e0504c8030400f8665900e00d2002c3c0d0030403803072800501d1303c403500042e01a0054901e107024070b000713070701829540340071342009010340d500c50000b041244c3c070420170080c070b2402011864403c680c1c0609a02e101503108027044032036002c0d20f0000c030b6040c001c1c0e00601007007041c00682d4072120f61198a0342c880d9552600541c00050007104d140341180900441c40800501d015802840004540c1c14000b60601429128a0032070304081c0003181c41540d8906e06905200300c00041290400d42444d0540c0761410b018070003034480004500041284081c000004d01070341c000d41100c0050030000c1c040039003440c0c01e401d0040d0b8621041c3e4107100421070040000c01c19501c00c0901c04189c0034090000f0a031101e40300411001045180a102d044501c551079101615030180110141010050002d540360720701c60000000f110007500000000c60284c8000703d040310301220012001d000110700a44a20b610 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 524622931 1250 524621681 524621701
    0x114160b100801181401020304020306150a03060204060315050301020901120f0f05040308100501030c20070e07020714300304050315071e02061f050d03030203060114040308030f 78
    0x290040c2d0455400d20110a291a010441a440385802082509002094900010b08074403064030082d4041d0800b60014100c0030340d6040044840602400c00000c0903581e8482904a8115800c824002611000078841c00a804581c01d0042c0408900031403a00d814840060301c40e03000203444a0b2041e4907180701c1d030582405079104860380400020240041e240038a4001d1050714100c800b40981450240c0100c0c895209108240c0c00300030f25122480c85401c900031018170740800a0990382c0c070348509000410010391050040c0e000301000c0c0c00600794103082070400d5816050400c652070282d189000212505450ac0801404070180b00c0d440d019011b401c070b90300720700b103100e990807594152003000c04030112210754030100c038442c40940d80c038101f9103aa51400042d4201289000c071005a000d007003c150f03103101003001710603c103283c44190600c1581d1080440c40450030a40c003680480c1d40802000700c1540c11051502100c1d01c02c150b032a05d414103640c1d0300300807804068425074151003100001038030380348 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 524624181 1250 524622931 524622961
    0x1060f03060506032805060307030303021b1c03140906010b07020312210708040201171f080114010e1012030302070803090105010303020f0c0612090304031a060114160b 74
    0x21010b0b10056682c5800003800300000011003444034245e00d00380c42c10354030036001d20540e809220020007503c0e0052a40d20110080d4001140c1052118800b4903044a0118104113803820009101c01613072280c5044200501140c51468039010b9004404007000410781010840d113054643c845e41e41134442c540390000c60302e4071008450140300d82e4000500381c80e850741c002d10703414240316a50442c04010b5545040480324804203a40c000e012420700c800c0c1c0301740411071128a60b0301005001500d42c10384020380d40105041c642c0d03400143c0ca44d540710805074200400f0901c40b8090081450b460308541070414181c0b000e030515200d5007540c559940a51130401d4400d4040344c0176150000c01c819105d0408460302d900030300e400c6c4070880251007000c121100d1281c1c042011004200000c05a50500c280b1081c0411000b4000301240c280340020040807002403800c000305104954840d0b40c000c1c8034034100b0009485025400c100e410400410f01c160001003541181020466900118908254407a2000d000c1004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 524625431 1250 524624181 524624189
    0x20d0b100f180c110606130f0908030907060908030301150216170c01081e0402030c03030708120c090607121e050c0c2e0509031005150a0e01060f0306 66
    0x20841000900d5151524180c00d10102461042164007103805040d81c010f5440c01c4140c4194205c00000340d51407034003598803c1e00c0750f021100460341748160071070340b412540107540446e0000000310911444030020080d03038024207918280810100e00b00f000e403594a001c144246518031114004401000c0c0c82031008203860210304081e248410340760b11401c4840b0010240541451103242c4403030100350302c250100350088290003582e9032082c00100701515000001001a6018420140c00d04402e84040000380310b41d60142c02d05a4460810039071081c50702401038284d41d030111041c89107880c1590740800f01da004540c80f00c2d4910344103840c0c04040c0d480300c5c2400104c58401c08424080000c40d60808020014500c8880c140c2d41070700030680c100080303250581803158070801542da6080501c92034100701001000c0d5170030000d0a120b03458000910740500b42d0b40700c40c0ba16032280140481d03816445200402c490085a1039000d25041128110218105126010070041e016002030080750180c4e000c40054 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 524626681 1250 524625431 524625449
    0x8030f0a18031205070f1e02160909021804080a0305150907030c0e042306010203070828030b031510050901031a1305060f07050c0321070903020d0b10 66
    0x1a1110b040c040c00b0480c0708a407051030542000005603005219004280d01c89003152501541032603002900410a0300140a000c00d61140a1070f0709032510005c0051002030425404c0415030010301c1c41170004149415000940c410104804d11001402c2c00d419102c91180c0e518000a6a55070365056070b0000810111154020b8401c00c24800101c2d4103030003413000c20341c1689600659040d48001e0004844c4503502d0446050743c450815031072032401c0d58841d174100d80705204980c10b0a004e626040071650000103451060400144256030306a01c00c4200001c3d800e00d03040030410400b4904c0800d407680310380c040c0400070200c6800042c002000206011002c1c00c40642002c3c4250b8507031420400c041008800d003402c1c4146200003440c200140400d040300d295104025050b10f85880103003005100f4082c20b0001406428003642c210164104040c3c000781c0190004100643c0740c150201c1c80406000e04000200b0800c00020710140c3c81e0b00444c11405a40084070710b149075107510f10381c445100550040da0032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 524627931 1250 524626681 524626721
    0x170709210f1220070302060f09031b0112020906120c1c09210c3c02092409221208010e01140d1103062409010308030f0a 53
    0x500004842c011841c42082e201c85598869041101e140030400401811480c2c0c071001041c001414804090142501d900e05010309090348000081e0801d201d010300328401e110900340c029040e45e4083d001610340110f03010114601070306000840c171644541c0c0014169180150007040e036000d403100c00c5a2052400720100500c505030150f104000e04001002504c1c824900440c001300c80809200c1018014480d0705c1d04109401079a40b02e00200004054419030000242c0b0118842100c0142c1906d00e9280000b0585182506104020f00c1f80c0001d08450750848011040000b14410900544403428045824030003d0ba550b074240040c0f42100c070488254040d001c0d940344100b1030103141c44400f550031a2520f4507140e80b285502c8151480921a140d01524000c0d129221401c05040c1c84036124020329400342110041d10204c0c0c0340100907074600c0c01e507581100800d8000441c40310241c00c5880d04841c10b00040d4510b4982c02460f000181105420030354940100d007440c0300e180d01100d421004011540f00d = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 524629181 1250 524627931 524627933
    0x2060a1a060406110a0602041d10150807090e04060c02010c030c050f1e0d0b0307060503040c1205030d050106050409150e2806091a040c021b01030204080111040303170709210f 77
    0x201178049d0454800c0d14100340c1c808681ca1844840a030415201f251110b003a003142a448101c0e00d41c01d01602c08014485041800300d221440c041d40320344a0360103403002041440c0c1c9410002c1c01c60b00b490201138101803900354207019031035009048030001c51000c0701d45511034254001040741d0321230b49a01d140c0e15500000303490704404441d4019007007040d811019244116a500c5007034802d44000c80e8000c144407212034050140c11a41d480b03040030240164104d81c1803401c445220130484200b03030085004074002080410402245015001d9400107842005000f285014100e40481b02c01400400c8400008100c0722042c050080301c00b50403c443c0d403400c1c4262613031942802d000308401c107480340c11602d580001140e5801d050007001d10440640e4000c2ca11000c80400c115001c003032008160341015020440019800c1003405030310001c41c4645240f642d00c2c1d14500d005000f0343d2102c00c0307110080c51903104101c44d10f13421010840031a0500c0d0040d440e4a10200350010031407070241401009142c0200301300d4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 524630431 1250 524629181 524629199
    0x10030f060801152705040807080705060603010e070e0a020a051e030712110304061109060d0b0a171e0304030b0901150e062b020a030302060a1a060406110a060204 71
    0x21140945582440840c50b4644d40c483c902d1110850b0b0310012454215000000036825601165001d030040e001603081c1142036940001580c05901c060fa81a400102403004170b1800703100702156010407600500c038003481c1240100d95000020002d090855000c07540e0700c0211300550031036440106040c8039115130300b460025400c454005540c420700142d0728240500c1500014407400d1914030030100604c1c1142d440e039481c04050400000400328600c020312168805889501c06040b620b40140c1001c101c10561405000c03901e0700d180c1c0302901c441c1c030924265450f07200102d1202e26000c20804003152000c92500350514603c00c81c1d1004100c100c410381045460b00066009199034a286000100300c560f035480c0c980010030080d0f03196540040e043d00c04000800210b403080340070848856181c03045002680003e811680b051b8825009a040300f81005101c0c4107138446c0d0f0359035440074082c410140f0390080114020f4000c0c0d006050601c85400c070700d084c0d694010481c1003403991380071034299503454441c581c40d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 524631681 1250 524630431 524630441
    0x1506051504060e01020d0e0d02150309010209011b0803070c0c08071d0702150a0b3f0a110607021210150f14010c0c090c050a0905010215040210030f060801 68
    0x1942c00500199101080c541c408910700f2640c050a645000385400c62004005400c256400100da20400704103c2c0745444540601444c0300e171903080b0006854a09401c0098203500c50291080054915001c0e0000001d0310402500d41003030032403510701190710061400b04411b05980d048040e0714410315500003541c01c1da5011060355209145600c2d8403e8a4100d401d90359003a120065071407559a44c400242d07502d1640d0304c00c0070903c10041200107646102c00c9095140800c3c00307027a403080d00e4034a1102484042207030701424046041c1000740328445043c0c0311000c0302c2d140d40d006d143c0300d07003400a0481300b9503840e2503040e00300900308004d13151000b05007010381e40240081186540250040c420014a1041e00c2806200310303102c040e010515111080300450b019456208115000410888041101c1015110b20300d22042d440d202e160355902d5088004c0d281050030f600ca2411503024050703000d4045081c00700790b074005a0644124140c0c0303100c03202c2580900b03090480d01c41058034251000031501e805401ca = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 524632931 1250 524631681 524631689
    0xe151201092012120d09080d05070f08040b0c1e0a0c030e0607080d0504020105160602091504050112090c051804020405090f12070203070e0103060b090c090d1506051504 74
    0x1e480041c1103605009401c40c0410540e4583d07089030a01c1d14400743c4d15401090880111a00010400119a108a0150031005142a240e41d8400c00c00402e90703009100c404070240d0030b04004407289002c0d034509030300340c100400300740b410b800c081410780c0101c00481a16148a40b000882ca440b00c04010004141e818141805d900007a481e12642c010307800c007c0125403207181c2044009280a94524072070001e010f014000720304128040101d804d01d12449400808000d01c6264096501d08003035042202050f4070b101c035003180a0041200300580e0782c20182c91080c0c400703221004254070701c0604150207032101c85d074040c0303800551101c4174150180740305103003c0c82580300b00d8040002c1c0c0c6550340340c59540c4540c2582c0040b6644242041d94101e030321103020b404214802030448503141c2d00d41c8580b074103012082e80308039500da072901280f03911860060f0400d5403015808d25500d045c8040240002c8000040b204060814540b80c4580f0181d106250091000384c000a00183c018035114100100b1541c00b91103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 524634181 1250 524632931 524632973
    0x602042105070509060f0114131d010906050d15090606060f030e03180111070317040305010b040b03210909040b070206100302011e031407091e0e15120109 68
    0x181c0880e140c0303480d282c580c1c0241000351000e96110000401504c5540382d400840c40d00c24400d05c05030113420422464940a402080c0e281180030340030103090301c1c0d4ac00042c3c00c42041c507400d082e0140140d840d6066104529030f013150024031008003501610009224142014081c0c078209030000c20010703000151880d84038001d41c1e0030480d01f45d8444840340c0342d00400b01c0b0642c143d40036458100c030540c81511440c0d030718200c5000303549442d41c0d40e070342da48140d806900c041c0a02c00b00108040041c004284940c18966209860910206149100190325524145840140e0024070341c07002c064000300209660b417816026010b55010308083c24821010007080b945540144a80e800061401d1106207200781100c0e4180c40380d11b5a1401c680155200800602100b010140d03105c000010780290124a180202138a8440d40105424500b05e400c90040340719a032110303a21110b0041107404a4150038952000c410700d040d8008045140005100800d19142440306608001030002408441c003011000d1203c0c1f50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 524635431 1250 524634181 524634193
    0x18140606100503010506071122270510050a0e060f180304030b07140904051501180e1308040807090f1b080a0914032107050f070305070602042105 64
    0x1841c120b586101c03d02416401100520400c0d000030610402301c4c4030440300800789c1580c1d240f801107030042c01c6100107020484603101c81780e00440b42d5072005034010f00c40b2440744841c10141c903610340e16959165814030003000d95035200010342d9803c181d031103000794003019425114141061000e641e8181803d80d20030407880c0e5000f1612200d0b020001c02c6508881d40303d81da50220341c0c2c1d9900266110300201c0442ca820703880030070012209940d54030035a4403400400b810080031940a400041101c00c29807800c0000203030300c04061003109604036500707900201000c0c038510010110702c1c2c00354180c0120f0348000c3c0180f28083c40410981c0c50f0341c210b004903006503141004416244c3d40c003825082c8615030044081494403011030007007009900000c040700d000314100d0400c2c0e14188102807650f80008044411000f691040d200140b0900c050f01e9007003d400d1401034100800d0f440003003030610503134400505010000070750b1000c0000e0307901540e0080840b901011804518800c29480c09400800100d500d40101c0d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 524636681 1250 524635431 524635459
    0x503031504060608041218031a060f011d03101b1101090f0f1419020a150516030e100e2805152203171204030318140606 53
    0x1038800c210888899540782d101644483c2c83c2c2c110202c008002c0d98007089800001c56251a840947e050000d40c030030782c0c40010404494a0343d19130004041c280a11884215025016907a03120091a10003111803000e5030307841c00301c0c0c00041e19046090060720403640c00c1001c80c10b0102c0d0030440c1488070841d40d8555058000e500f04140d0708841c08010000e0074403610a21030004550031a58228441d48640911000340049031801c0e4501004082c04601e80816040244c0442c00c103010440001c012202806610442e02e20010705103008510201c03c0c45403400302c0c00c406040c0b01c0c807101c4080c40c9004e012469440001000200002c4155501a0041015011805c840c9883c41c00c4141c14862041c0c51513062806c0c03400704444042003841031150120103005890900716031111070f0700184040c180411115180d440d04420350300148800550103170040c44012010300c02c0c40300040e0300c207a02d03150002d030110000705488160291201c01400000c80c202c1004024800007400c9409228201d441c84c43c2c40c100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 524637931 1250 524636681 524636689
    0x20903012c060106050a0c030315030506010f050901030519030c0609030c2d1205210f09030703050a030504020a1d07020105090a080904020d110315040f0e0d181205030315 75
    0x404e1140d500051410031522941d1440f6003480070030709119141c040354a40030810595a901544e4000743d8490b0041d5004002c031180d500011802000300781c0c0c69000300c1d0b145468242c0c481c000804014171151001054a04052060540140c0303607034004410000f0046030308000382400c011105c1110001142c40d40c0307100d1b80c00c0603c14001180c2c1000a505400c0d00d03241c1d540c3c81481c00c40340da08824460306000d00b030440c140d818030241c502c4000003c0c40c04a450300d0f808400603510013134042900e942003003190b8800300780c0c03080803071b0802c2903d0306000c0348588491003c80c01d070410b0f56000c080c44c8a118480d46100d501510882c50040358181d00a0015880300602d0645441c1d806000503d41002000700d5842030929401030301141500c1d4200040d80200200a0862640112211a0000b02c5280b14078040d1916100d800020020004100140d075143d2180c0b61b03450a141c0b4181c0207000f81c040900001200450500c4064180038015000e43c0403d450025643d40060321460780044400d01902c0441c18 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 524639181 1250 524637931 524637943
    0x512060108060c1213060245011220030106110c040c0c060519090c06020615090105041802120102041d16080c040506070b0103020103050a11041503020903012c 70
    0x45840c03e503100903110802c1c0a4002081c8a404841c1d042d002e1141407402003000720040c169423920807100c0c1420000340c5020038104503030300c08401030301503404e0307400c40c0740c0d90260f003621709a04203140002e401003c8182018613051841c6c3e004800080000000c11403c0c2e000700b820b541c002e6001c0031120341e1007a00301000241c81d00407260700e0003d55000725910210720181c0016800c1400720038981c201d00e07413940c00002920b52040c002e4520003d009410040f05904100c0d499100321004107407201c1c0c2780c1c03500008034400f0341031082d00d2085848109099016600891000c08264002c10a107200a04007104034041d400c6403203441c00000c6043c4440307042000c0100803510540d001602101500d196940036184074001516060742c2103000d10000c00c05440d90001811464014143c0f21840d6155100040a60f80d005182c41c02c1941803c030010040c0c9046401e0324180c541c0d00044161001580c03c04400038010510401d0b450760a2200030404001e09a0001c42003641d208242c48401603e01c015a0b5510 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 524640287 1106 524639181 524639197
    0x2211024030804060f090e130201030b09070305011404020403051009051e161e05010e011404030f02180c030402041a0303070303240e16090512060108060c 68
    0x10382041c41c00c000b0b49844d02e441b41c1e2060a110034a0300041010b4a0401140942240c0d10f04580c02a0400c05501d580a0310100c45450000c45c01030140c0028858404030201034800142c1508260080f1416242c101c001040c0100d17401d40da5000074810410251a180661a407201070f50b01000c402d0205020500300601c200403030400420061800c43d8032034a00c1280034440c26100b81e10220000301180c3c0242090f141c448210740040c2d800542942c5442c100036000540401041282000001c07041c1c0256244007003070b02c19203e08801840103a070204030306002400001c0051800340c03c1003840700c40c071100c004800c141e17030004245541c018500480103c3d44404001c00b060f2441d9507111110b01c0d43c242c0c29981140b504e94000e10310200981407000300080d500c1da00b40d01030b0160006800500f40a048078850102c04900291a00c20038062203015009030b0001c900255100c5084c0d038848 = true := by decide +kernel

theorem cover : BRFrame.Cov 524460431 524640287 := by
  have h0 := BRFrame.cov_init 524460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 524460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 524460431 ≤ n) (h2 : n < 524640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
