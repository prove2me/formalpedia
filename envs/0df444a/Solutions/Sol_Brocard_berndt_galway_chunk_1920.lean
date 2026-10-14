-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1920
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:09:35.846016+00:00
-- url     : https://prove2.me/submissions/b153fb88-35e3-42ba-9155-3041bacc2858

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 345143884 ≤ n < 345323741 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 345145134 1250 345143884 345143891
    0xd0c0320030d0510150c0501022703010608160501030504050a0c15180f03030503100b0a030b0f03011515020307050102030106030519090c120c03151b030b090604050a0f 74
    0x1201103900001528109103000d204101a445080f104070a104580c81200300300507105280c0000b00788a020029507851040c07002506003842c3c8010042d11065842c035040c002c0c0c401e00d03100c2c40c1d146424040d40004100c802c000d8600351100040588003418036024060605841d800401c0410a0400c24590b00540003059400556103d400d0707200b400d0148410f602c006101c01c5060003a1454015144086501001d4200c440314656601a202508010074201d0080c61601000509510361002488000c2c01d82e5400101e101d2000b040141115541d04000e01a0b807610440503a02503065114805a810307a111801140461038812031440c81412401400395001200010b680c9402d5044607014a40182c920310b003c50b04290208100c52120401400600c41c10904000e0440354100206855001e541c010640316101e03183d1800e1038098268821503c0c4c0c0e9004c4c0504541d000201d622101c80c0308d480c0510980003450300084144a02402207031090b60789101203004041d07168001c5100c2c041e500002d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 345146384 1250 345145134 345145187
    0x1815090b180319020312070807021c02010e010f0b04230708131b0e09010e06010918140c0406122f030d0801051e030304030f1704030f0204110702030d0c03 68
    0x94030fa4100506c00c03900448000f0100d510b5902540a41d03104010716401420400444140ba44541407000700000540d507a0710a14024240c0a02910040c3e1105210100c2d2080709082404100d0302e1008c20300ca40030016940c2808050714502c035954001600d80b1303000100e0348404a1403d10101503400c01000c601182c0c2c42304c42076006496019048ce2110242c0703c85981da001e01203400d0b00c3d2042031110258000e4401072240d41d0203030388460070443c404c011a54420f00300f5540c0d10303002903d21200282d070780d00a002501640ca0980281009000161100152103203981c6d60311100c500301c1407550810000058001c0c0c0c5080646500f0101180d0003070881d00c4403450090007a00c3d0620a0180394001c114030040d1904883ea0390030080e421030800703001149054034603195506512061034084441d4000403004481e600c01480181001e14022840a1100e0665104100c00c844050140812441c0140000c201680e0b0214600380301d80124101903400340114a011260780640c1000d000e0b410600c0d2105 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 345147634 1250 345146384 345146387
    0xf0b0d0b0f090915010608040f0308040512120105120d0f12110715050603010203100308090d0602040602030307090503060402151303081b010e0609030f0a11011815090b180319 77
    0x1e850201402c0070103244c490362180707403c44940104442c09800d200c014400200000d10642e0350550003400782d820f9030580e00c007040098005600042a55190080c0d42d80148810710340301c1780e03420b03510b19032000611440000501c017900a4000760751030070034807841e000d8441c81c0c60903541000c50142514040c1c0c6903294024904500e102c04100003182e030305803030a80003803024181403003124004c07100c10354010311461942d035403a02e2680c4880d104682100080381c007030000500c14005000a082d030794000c1d540303e1070100d10007410604107500c1071b4440c0c2e014900384400361325102040d01e0f080f0384003685107a40741e84000d01b080002500354001484210b0014507445840b0741c061103840340d503c904000303010b640d43d040e942d140c1d5910103850000c1a9041048100390f0503250f0130041004042c5403c1401d015104c40001a0071607421925810740c1c03200f1a20f5450802c808003a00e101d8403813000d2020440d1900c1515403085881c0000d1081241c10034a0807150204107040050350501c0c0301e203015082d54285104030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 345148884 1250 345147634 345147643
    0x1f0b030118030806011713020112021209100c050306010e0409021302250803070818010c020c04110316030e0102041e081204030b1f0e0a060305070f0b0d0b0f0909 71
    0x1a0002000d0f00c010070030b6503114940303100c0300b0300b0031031100b09081c0c4440040c0c0d40300101101d0100e06100c0c09041040c0111014000b428440b443d6081d11000c0e403610f6030905040c00301780c0311806400703403400f00101202c80d08001540d412503000c0c0380c00f605045074940404c00034444880c0c0030f9840031005000030981501c507001402001126005007880100265094101407948840107000e0340f410300008891521440c141680125212600008a0a10b001c414210f0301c0c00c031340304401600908000c0038942414041c2d90304003c1c0499042c0d2551610071004c8403030399a51508901010380b90000d07080315007001d405a9014190f491420700c04801c6510081c0344058192103042c01d940500b4001c44907103030558042c1c40c00c894019032008000c0c0c0d04c0d5465140c1064804100000307008210740e0100b02c0400c4414414402c01c48600c4c002040c500314140385182c046554040726044400300000d011a1b8405004c0d2030741c51403e00b4021905401410008188095501a50ba0428041c01c1040503207400040c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 345150134 1250 345148884 345148931
    0x903050a050d090504140c09040b090a09170405010c0b09071802030a0f060b0a0e150a02030909091606080414160f320301060506031f0b0c1f0b0301 65
    0x4a039090707095520303005c1c171050783d01040c000411840b154000900708040d01c3c00070070220030002c00010301c41d24140c000803013040d001d1351043c030641d603102c8214003008100074001507901e5616407813031700301880c06000030141000000c000f820a000000403e0050a0822821010b400084180c0403000302134251400250030486860f10940d00700b0111880107002481104281c692104003d441e010196405544100101140c1c44d000102440da0390300300a080b00180149422550185582c0c4400b44108050310320050904403c6030461101400040c0e088501601201c02500346a441c550316810a03000e003040c0c01c02d804c02203002c0d1038850780194101c2101001544d8050b0388c482111600c1c0c40642a50148104c40e8900c0d0b002e81c020800b03810381158101440c080801800410b01c0c5481d0808500c803500180d811024104100c50589860800504074801601041c2d0045040900ca00c81d02a9504075154070811440350f07810039000b0b0701606400040d581c00c0054000e201c1000c00c02a0340d1400328100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 345151384 1250 345150134 345150137
    0xa050c2a0307050d12050c070f060c020906040605220609050412230901120e0d0815030c060d15030f1212050402031002030c0d050f060a0e0919030903050a050d 70
    0x80001140c80e15240ba1340d070b28201c1c0c0040142e800401d805070144e5160b4440004082d00d88a4003034005039008070784c1e100c01e001d40700300c2e42c414441007480d206000341d00f500a40401d1085040910600003078032a9620401c1e100300c4240840c400d10070000c1103c00612280d0001800241484104400e002032030030080c03140042981c0b810007000c240c0d10001e070311103d150f0b0142030700034080048807074541c4100e11050140e900010002004489034100c0d519104c1d2036512800442c0c03045e010401410361060081c0b0607014140c010704168082032000510301d100300031005d0082d03076450010700d0b44952001981d02c080c550100750120100341d070f414003000001700d5003039400000e604144814000300303140c05818055940030b40100010851941104060b400040402c100d082d01402004d03e03103450341c05414050405a0018192810320b002031081146954003c0e0300110240800e1106002c0c0c0001c0711108041240511000d40080d03103012a1012500c1e4000360003486040034031401d2000c041900019042103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 345152634 1250 345151384 345151393
    0x180b0a08070c050a080d14161b0c03060f18060506040510050f090a0213091a03070e0f040510140f06150a0302092107090605060f0a050c2a03 62
    0x428808440900c0b05101c0140b0903049a0000030025400d20080d0034041c2940700040340301449100a0140040e0869080c5402c0390108e000c01d40458015801d410208401554101c1078801c0351542460907000d44802410350360f0f81c4c41c1c8445040c10340c1e440354400700501c20000840b80e80301c6c00c00202928003550381500c500d140c0030214500c0148090680c044038005041241d07500850020001d10900080c400c0f100150200001040070b59845084400b07070260900c002803094558600030710180700c603040c0074000c0c1e1000070140200c1c58003550325036001e50104c0d02092035940314074003281082023400310001018140b4522616110141c0b004920031802603840341001c0d600c14080001601c80f81d40324004c500410409034040320b1107034000f040c5190000e000c61822204000c40022924400203c0450300e801c220810300a80c8000e0040c4001401700300c801c1c900b400725800e403182076442100b44100070b0200c0040d4102c6000002d202d0f542078401519031707030070b54880305402d010541c0d0800410103109015 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 345153884 1250 345152634 345152641
    0x905010b04170307150203150919140c1903060b0d020c010b01020a021f03061a03010807092306040b150901030b1816020f0f1b01030c0c1101180b0a08 66
    0x30000f0507100c0301130700315181045002440061344c00a50000d0514005105e800355828095100c0d0004075015202140840081a541c0000201190307003808200d80241000018030050710094400e5031181039104000558440e4814000d400600300c9074042c071035541022603525054021940600004202c1c00020b00c500d803160001241c507500d0900340254420f01800303175068911459800c0c0c40d48050070f42800904a41c40c3c403446000329101d02d46070281c032540000180210a014850b000051900c4c00d4280600b018000c600229882003002d0002c01d11903645c0050340c03d81c0c503070708504100d90028084040b000d80004110141d54030245140380401d05142d0320107441e040201801f200104041031108503925146009014400200c00304403c40c0300e1440e0b00700741d162050002c9504044900d0050500b90501d0b041c01c1c648098050540e414140317401442c1c100c2e50b81081482007815482030386000d0032114040140e1309211050400c8100507003800300445c04c00700d05001840d40d200c083d100d021407542c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 345155134 1250 345153884 345153929
    0x14090d0e220f1b021f02040b04080a0519170703030f29101d010c0b0703050a0606090501020d0e21210304050a08030621010b01090f080c1203040905010b04 68
    0x40740b409110005031311114030481c0d070b41ca82030120740d005c000ca804050b1605076601500205078100703400540b5203230000040001002010408000840e08414690f9a00c0c0b4490f2104030641c03512242407180807000080d010200340c401c0e0300120103042610380820151030305526100002118200c0154452166521001c00d41743c80c0e07004030146980c030340d00c4034041002c00c1401421201640c1200f810b00801032054000a002a1020b901c580c2d007507074000545152005400d03040d988a507003c0818003800c180180b200780d0780424025140f40e4503040030a0312030203010108441010100e141540c10368071641d510501500410030418413610010a8000401e111a4603003180c802910020308a0703002900f0000041d1500c0051544030030028203410b4811858540c00c030001c2224041c03940103955035104180e0715030308224400090000c0255041e1024140100155600e822025041c8503840680b090480103034100300b00c0d000351414550500c82035a444110240c1f41d0000d0044401c4001406403401052 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 345156384 1250 345155134 345155171
    0x307060201151208130e0406110f070f1704090204030605240907050f040e040614150f27061201140f06060c120c0114090d0e220f 57
    0x4030180d1000240030303240c10b940c00d0343c10610120450b0209414021103501c01005004140104200680300e21949040c0c60100c2c1110011000034880306c2c0240800b000080c040c00c02d1f40c2005900001d08a0003440c00e0401035070400c17144480d191120780015022a01c015160040c104492094006000d15112082d90f51810600c00704620020004084010020b20300100060341000e0300e420000c1c41c0a000d130300301c1e10040e0310a4116154580d07040042c8020426503205260024a030f44102d40300504140041c2084412100754a601c1010740c4019074100b9903d0b01c01141000803400170107562954070000c40d4035a0b200454580c1e2152030140034841c0c0404040c0202c1c002e402c10403d01c140c0590303444071400800c51018202c1900002c0a10035400007103c10010030300410704d41d400b61912803c20a0101c0e013560030003403407082d2070b400340c1060002e00b03800014a0340c032401f242c0c14041070100b034070b0001c01e4030740c00105240c425021074044c60442d0340c0c4040c0e010b00010070801900b031000400101108906 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 345157634 1250 345156384 345156401
    0x2805091306080c04090c0b0c0d08010801020a170c090603090105010501170c0a0f03240e070c02030316021f03051b040e15030708070f050f040e0304060507050a0c12020307060201 78
    0x2c540040c10000001e1416900007031501b88941100c541050315804100c0564004c14609522a4000c07040084a1600081c103280140310841c000d501e4541882c04c02890102c103c10b11201d00c114a2010031070303510300c1c401681e05002c800303860070380c0300c0c42d0420005020f090213106d84d60110f100042100031821814400c02c1c400c0c2c0400c0603840c509401030030304030381d5000201e040004041c0c2d00d0100800c039001c100c0400640c1d0350940c40383c851043c2452089046c030311018203481d09206d024902c1e2030040e100442550a07200030303102040c450304143e00110b002c0c002c1081540d000c007240340940c1025550194042800707034039008008c00747c1c04122288034000e032040f40a01100954220009410342500c549429170319000501503d42c4680c0d1440d00c0f9103054100d41091000e0f1141000c180711904012040c0720354598120707020710802c101c0300600c0382c91384203a005403c20451300007000703400c1c00000c01c11100c8007a40020310400542c0e4681002c0000241202c08034402c3c050700400140d101c0c81405110384 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 345158884 1250 345157634 345157649
    0x303091032030f150604060302190504060e01230304050a0b06090f160c0c1403011a09010308031302030307060c030f0b010f21020f0c0d030e060103082805091306 71
    0x1640d00c40001d4920043d50041108140c0032044004018945420001c0d00003000320b0346025844880801c00f911208c9000c4032450300f001003d22040241c00c0c4d1004601c0d15002d400e0034400c050002c070031042c00c1e842001c4003213104015400800d000400c080001c1100340180142d0790501161181001c025035114151451404210010040303280341c040440d8101d602d894a003081d191030840e5640c0c4502c400029800ba001d0740c2d80181d404080e42c2070030301030244420190308080700500e0485001035251807041c000500030b131038040300080321042c2007044140c90640040490b03071901d01c64a41000601443e00c40300340001d0402c040c10a03984101d00503408283c005031a9080b100c01e549000b12061141d90315480e0390740801072291244101544000d00110101740c01c080c0d9160001032400d454908115210410107240c45001141c2c800d000c5030003815a40e202ca030041d52008404008051340284000c41619000f1000d210005540c1102c02420b440b1010b880003001226142400720072030341d56100d400c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 345160134 1250 345158884 345158887
    0x80406090b121801090b09070807060e060307110a1506031a13060f140f04020306060307081f0e0d080a0f0c0903060e0f1905160b0d0b0303091032 64
    0x35586200800f50890182c0300368000241c0075500d850b200c960200070380b040300e074a8001c444244051070003030103000040d003452308086100381c074231034081899403000030702c4002000300006540c4400f001c1440100e48081d0082100c050885507003040d80c000b01024030040302c003000041c6901100810b541c40041c4100e0618020980708520b07034444c500980300c0904807528150703490115003a00104006040e014110032200030300e00b46414810705140500280019200342d000e05000c00c400c0b139002640c1101d082003904031818040d442c003803100180004011661803809400624180554810341c00c5d4818045940d06104c80b030704c0741181d6811980c0a03040c00d000120034400900201d9525048118400b98503021100900d2000c0245414810b84412100078021201c0400b02480b1003001240440e42d501059a0392581c9008500c00071445200700c1d211516031142e02020141d034061058450600d00603003041984458950002c11480302d01d18403030a2103240140301c0402c00d00e100440b000c0802508000c5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 345161384 1250 345160134 345160141
    0x1021c05040510050601210e0106060305101514071209050f0f010c022b03080a0606080711070306050a0e070b04030201021e030405060d0b1c02060a0f050c010603080406090b12 77
    0xf103024040040c007040c180016aa124642903441c428000750b03420a1410020304041d1075015942928a0355000c01c0800d410030080c0009201d0700440c800480d4000c0c0758216415560b2041602c40310309282840c8000d0001181c00c03010300c10801902d80c080c0201c0da45461940360cc810801107081c505c514026004402c072048801254003d020004043e40001c003203144c0d1581c6010b400c2c101c038585040b03112030072919413005010541c10123aa40c0e0001c03a03000302801040e0421310b0042108000030526004c1250702040b0006034502404040051600207601740618506104030714007a082e40928000d1504c070740400083e1004080f01a1002c0d6035059014000c440c141d044030200c44070140030080101c0c0000c100028456551100a01c1c1d070380c0c1192000700705070740c02104000c56400d500500360446011f1090000060395413200b00c0380c04082a0914501d14031191204850602407810411042e40c40c02d0408418081a0030190084615035900d28002d00e894001c0c40d5610302400c4003044480c9407041c0071 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 345162634 1250 345161384 345161413
    0x803180301231501120c170a0203041104020913050709050f01020f06160908030c0705010e03010b0f121006030c0807240c1e030306090509010908180f060301030501021c050405 77
    0x1001010302c0f05241403d0122030b40c903584002c54907044904808501d13907208840c0c2d01c010060301d082c1c0c00324001d0030031411850715403201d030715080216400601c166400510184c0958581d90780c440c0e0700240d01030802c010708d080d15014000c15600e000d014400e82040340341094940c800a03d91031000a201c2c0030748010303101c900c0c042c3d41441d40381e00070f002807102450000c0307101601003018141404001d00107217143d91500b40050b0560b00310b012143d00a0b41072403450385007921920702a200041068507403904409501507650300741240c2d0004201151f0801c0300002c2803100710720301c0906880c44c0030251030104da501d010201681034201b081d6501c58003000400320100d4094488009040c0c0070b10a210510004048100000c2407401c0b800c41c0401d0385c030b030400d00c4107140342d200302c0b85d100407504001c006072001c0343c0710b4010030700440105541030b0481d00203c207019107032001c2003802040040d1902e522541c5034641a8080e4010004040170340e50711307843e4106403031040d00032107008640110142c1180403811b9803 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 345163884 1250 345162634 345162661
    0xc040b0a03060b0f0306100f05040b100c21020604050114040507030308040302070e0109020c0106050f0307031401020c010e0f06060f010806060c0c0307151d0f090907080318030123 79
    0x4403d40e002c051000700c09155101401402d22440341b80204940743e07805e0203a000081825034029501551070b007415208651114441e0751240b1029040c500441a81854449100e5610001c40d004005081d551501d09a400040b541d0040f0b2183c0700900c204030080e080300c02e80040c212005000c640c000e980400c0032a0041341030980181c044d10594901da600d81c400359a030b00d0030a80c00410612340c00107008040e01400e100b171402501c021540340092002c81000641d58251902000e00000004104062405c0c1d0940c11580e400c10043c000b849000b003041c1b000c3e40c80303140007440c403c81802403c001414500d89400d03101134001c0140c443c0000c540b103403414400e9035085900c0c02c068502c50301c848022599402c01015008240510a1694008a03903c0c014004c0f4070f00700c0210020000580c034048684d6610340c00c0910440155003000d00c59592041d420b2804481d0350002c0d0440c00000b450348104060441d011440881c1a80240050381c0c031070850418401034846a02c0c041050440840e01680c21480b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 345165134 1250 345163884 345163901
    0x70920040b161e020306091618020912011e0204030803010b0d020705062701020309030304020438150316031a09090a060506030a03232107020c040b0a0306 68
    0x501c1041d988a042e511022420340195a0700203080f1501d81880441c50200b040950000a0760060401c0d03591380e148584140758607014411722442d81c00c0c40f10b1003506c01a410f403607101c48001c102c0410042d20b501e445000b40490382c89450024140800c0b405c1c0181039008503000c5990010701f040c50b50780b800d41c041c05540c01c402d244000b441d400b0050131012032030811919004414802c01003052006409180000c544290a1182d481e401031003080b000480100650b40d2058045c0da000c103401180d142040921176a210001c005500a20703200b01091002c040154a9200240c030b5109003044883d040f090741d80021244091161030741071b180d4024502c80d030001c0000c0215020420049005040010440074044641090580c06130030200140044c81c01050780000c0190003030f10803010b881e20000e2000d0f89410301e407801d4211000101c002200300108944151080c40d11303151402040c0000d10b02d4899069130200c2c010301c610b2180d1020340c6010700c142c1c602000c0c0100a207590503d1a5212000350040d103 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 345166384 1250 345165134 345165157
    0xc07080d020904020f0a02070519030b131b06020f1b090a090606050a090b040612020a030b1b070303090218070e15091002030d0501120b150d060e070920040b 69
    0x30700448051105e01d4016080c032880c41d801400055081c0000c0c492001044648540314585802c41000880c025640407134110744c0d01030800c40303104058101101107500244400d6141400300d60009012580884c2181c200c0903040c05a8508006092170340d03103082145026141c1c41241c0002280d003011250340410b0106100d0100492166502e9001880700c1042e580002c00703464a07059408458503103407081c640600f10b4070220018401e00740e004110784441c1c0b80402071015203524040750f01881030018481c5910350103400039540303c0342c6140003005041d0018040b4001c0b0105d0789440c05a43e49090814410318040d61001e41d500d005508008528030080f00000c0c00000030030408200c1d46481000e040141a40d800031582c4101c0c0c8101c510072107070b05a0004592641d18401c0b80c1c0007c558400702030304000100c0ca02c0c07048089a0001030f504407500d030303802070049141904841e61284003061060813280d00c0b280c10009440003400c0c405992a8041844c03202c41000c200030300c40c1c03201140141c80c0c1e60000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 345167634 1250 345166384 345166387
    0x611010c0f0c0f0b07020313080a050607050a12050c092e050906070213061d0f0601050d0b0904150b06070c061112040f032001080609130503030408030a050c07080d02090402 76
    0x10780f1340788034018080d9450030040e0400101d54082c0145a840314004050f480014241050f03035803201516544050a04010424005060f0f1121441809a5500081d8511040001e41404407060089600030b9400034000e44e2040405500008822000c1c41c071040310128440c041030845200300c076144e0010320010b5011000f8004440981c44440c60245281035105001803103070706101030320811081c1040740000d1104024100b1501d00da48181054001100b800c1c09625007004000e070001800c00f503d2141d411002c050100004c0c03028007a0741c0d078804003880720200a912a103806201951080000191a0341e064403020040680b29001001c02c207240f030b0003500c05c81c190300384000196034020f5000d588414900c1c0c00900500c01002043d15140c0d0240c055402800406400a85004002030015229200b6200080d0402c0c40c00500151101d40c40f80035a652440c10f031504d1a000d800548038001c020f4680300c00207061011050444a506400c00803680c1000c203240c0c402000b82d400001290b800c680c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 345168884 1250 345167634 345167663
    0x10801063203101203050a0810081005060a05010c110d06060b030406020403030f0503150d0302010b03030c0703060b0a050105270a0b071a06060403030c14070f0611010c0f0c 76
    0x31510390003820500c4007003160740b41070482810003810360a80125001040d01d041130f20009030080115440c4c040e05090000c801d80d540c4130084840c140540c04500c403801810312801454609a00c43d900c84e41003203914026a036207840044548840014000340b0800740140d801c0d00720f02e00301a2503ca040d2081a01207581915020380000700d0b042990101e560302e402040a00c1010b421081c1e4020131030182c0340c05811480c1000d00382849102051415002d040140460000d041c0300f9044400e0403c8040c3c212660f40c1240c0d03009980e520000d202c207a88461030000000198600680740d1b00132140143d6031107052003003080c0c4130400203405240300303100c0101c5040c0c00c00142e21190000c03c002c0040d140320030740b20380c0141848541210034940981004044c441000340075a00c11003550f040c0c1e5011b107020b0580312500d10344944c15103164030400304a4801c000001800725050104601524070590300c1065840640d02803a00b84c40118014a0204010301c5c40700d00107074030841d00002e4441c043c140c9002d4101 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 345170134 1250 345168884 345168947
    0xb04050a1202030a05010e070602070e0621010608010c050c1e06041202150a140a0903090605180d050a05070b07020d2405070305091e120304020d080c010f180201080106 74
    0x401f100c0c240441ca41107904d040202c039070180b10030001000c1c4088a0802c0f0314050001842c0c0c003030054103450681c4010074650161500951107540507001c0d410080240c9080319802030711036041080c1841c3c8074403460050051035000c0d1381c0300c03a10340b10324680145040d403200e5441070030f500105100311046114440d503030006034240001d4a802040c490a0000f185241904030303004100340100a1110303142082c0440c0d000960085980d011601140303026600c1d03000312071040708803115210a081d40009a03190480502c1004200c01070501d100741c040300d402681d00c03420b006050040303080296020700c3c02544600400d6241a914500e01a4854901d0354061101c4186c03003202c0b0700790b1340000061754074004c00548110802c88074035441c102c03404113400b0702d1001d0b41c607036034034041c02013140f03404600400440d0031502c034400030103070740c83d403022903961601c140020483c000c1c840300c404009454203001c084000208201e0a0400460701a564582c0c03a0b03007402020b40f0b450031004000c1041c2690303450f1100410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 345171384 1250 345170134 345170141
    0x1b0501020a03050f070c020d020909010b0d060e0d1701090207060204030803090106090605030c03030301140d080d0902130e0c04050403121a10141804060902030903030f010b04050a1202030a0501 85
    0x11400c03510700181a080c0020344c41003c083c000d1003001440742081c40500560f03500344400e1500ca5040312b160170f243e036a681c0010302400141c2d02c84c3e07030045200c580c0c1d6803c0088541090381180c40f24801c840800c2840c0303404556040e2003149600030120040018000c480c40d5400500499004050151400c0e644e6039410b004d50784106d07441d205a0359907032030074040710410340140801010124010301c4944060000280c80784418400d0309001020148218015110840c0002416411556194aa000e1080010054031214400303d02c1900145400c3d00c2040d074900c0343d9040020000c0041440d90310100a010003008060070590910854100c12095004e841c01494044a480c44581380c1c403403131110a00a40702c641184003400c0c008000300d86e5500c545e0070002d071032401c0e080c010408004c0580d500850000c02042e08200440340c000020060b014400000940c020310515207406c03c0390780d84000e08016401a4020070f60300c0400d1800c1085084000c1c1906400c4500080c01d480301c1d822980d5455084 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 345172634 1250 345171384 345171397
    0x140c014103040203061612050603070b03092b050403030e0409060501090c1d0105070b0c0906030f1821070c0504050106171005030616210609060b040b03071b050102 72
    0x2400d0004200411401d081c85925000400d0b50301081d0100079158010746100d004101c000f1035075507110000f0308070340da00300a030300010055a4102540c03800c6c004040c0b911803071000c00310900d01088500294000b810300000303100b41e84065a5942c1000c2c255a81200e0540002c125141d01c20389809a24001c61120301c54a4020301542100050002c43c4d960040c06c80d0344000c00903202c285200001e180903903004070072a000c10354003200080d05a9181d410400880c000c14046613007225011042010300d02c14070a02c20b018280000c02810255500c400c520703582c001e0700c0c1c030000d50000081c490340300d485225005030466500c1114002c1d03603a52580040380480b50241e0214000413560061507440c24000242250003d111075066803206042c0804260345010141001d1400354400340b84120341c3d48100380042002180500d1014003012a0354080080c046078060a1f43c561310340385000904200070411103048560000e480f030304540e030307242080d500313644003e040764003030351103994000c000410a01c020444c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 345173884 1250 345172634 345172757
    0x804050312160906090e04080c0a081303061b210605030109050d08010e040803011a09032407020a03090e0c070b04051005010f060e1002030c1207140c01 67
    0xd2450042e000802c8004684e1040c1c050000d5101c09002503000740d6002030307005420071030f039546d503205071701d0302d14034100d1a403101624040012130311343c1e0004810a600001c481c0500713814440c1000c01200a10201d15004015000c11400d13082040c42c88211241220041004180011030710b0703544001c2825503021020480d2241c200095080e10a03070402002c50141032142c0510071180b6141c0c2d14103c5034441070107030103aa988400111034200f80715004841e00140040c0a48540d0ba41e180035403914402404d2126445915034400980180e2000a6001d0304039055590142c0752403801014405d034a80c00f60072500d05100801c144000302c0c1c200725000340998490001026078080904c4220111407040e00b0aa4522110310340c100b041076445a05481010070440b014485e1001c0443d0a82c0b6607c50703034a804229018400c03100c0e83c1040158003400d405800b034180000f20303c4040d090580c91703045e0b124685001c141c1030301c0e00c2c00d01c06140c182c1c3c1d402000c1150141d118050601c2c00c24100c16000058202d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 345175134 1250 345173884 345173911
    0x3050c0a0807023f04030201020d03110403020604080a030908190b090a0803190b0f150d06180e060a051605070c030c0e040203010b10121a180f070806100804050312 72
    0x1000d1104010340403480000c2040740d1400c5c030341140e0000352144095142c0d0000c00d80c0354100b0300c0003900b064080758001c41c2d0041c081070782d076581c40300b40c15114100c83c4400d0b0f001c00e159041c00501d465010803029100b041c0302100200307454040d903e0661800c00500300d1821841600a19400900c50500442c0200b00400450f0800c8040c26665002d8074450300003107006000c1d1250300c0700d0780d4666003008052020100003042e118244103100d00700401641d801444400c0160443c103000511799071003001503074600c40950b112130751500344071001d032001a1803002d6100d02c01046509114403580140242c2442a0681102e40d5920b07100c61401030040d0700040903000604042c002107203824403c0c00740c0d100003070700c0784c160f0b0680904025100011100362800442e442c0c2114660002400c0c0c11070081c000001c1468141c0c1040d0a40590200803c0b2030404010800340c0c04242c8080c0905921445103100610101c0c100d00070510850305804054021242440140a5807906510829030944904590700054 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 345176384 1250 345175134 345175213
    0x1b0b04182007140f030304060506060712090f060c020303041203020a050609011b0314010506030703060503150a0b0d050a1104060306090506060a1a0f0f070b070e090703050c0a080702 80
    0x41c3c02c20300782800e0300c98282d1161051150452011040d070307a1098004400041070754404011901d24420241c004100384405c3e042c44041c2500f02c200e11082d0346580603003016144d03d610342590f0a03404400040d6060b0300610081000c900c40e01c481c10b02042c40ba2041d5180a5101d40d905d5107040c400b901d6052701a510340e00748402c203a0401b04990890b840f6444e0900c83c400b01328074040a414411302455021320307400400688105c3c040e030042c60081402604803920401041e000001e032850540d084801c1e2802c5c4114010300d481d150658014240c1c000b0082d1030545219138a0340d40c2c010707109514981042d10f0702c400002040c5144101c8004030700410240090303103026020400d5905040e0403000e5240a6584050098a000000c0c1d8581c2241e80c0c4c4110ba0740c6107461200b514078001d0b140010302e80400c980c10404032030351052034100c0c0715405a5201907107840321003068064420482c3c0e100c40144060258411ba03501c10900329801140c10b00540c0d4082c0c102140c00c030890714a4400380703024142d000344071 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 345177634 1250 345176384 345176393
    0x1305090c070305070210140d020309010c050a0f030207170703020c15190e0303040308040f08010f1103060105031905070c05060609060f06030c09090103030c1b0b04182007 75
    0x2040d5005000480c80d516206030307581d001d00980a90039019005001d0395060424a50107403c46285510040da110391301c2c0c1c40052080c4010754400c4075004003950030011400e51641c010029100c81c0b201c940c40b03500c2038400d144030850081d04403120030303a851010054018222046074006003d254020f03409004040c0d8484c09110085d01404008205024100003c0c0c1075561341c42440001c844207840c00f21111140e21000034598016a04083c14180d00020000f4280288001100c221200d4800a02050040c0030140c2c0454090420100c07484200700005561980304d80000c5074070820451400c10010446c04c010740855508442d00b602050740c3c0d000c4001800307001c00c0201e5214508031074035a224905a00410600c03030880101d5030003054080f0105402848000607039041d424050400d0b481ca43e541d0a004048120a210075940c08204003607500c0c059140d1080310f4161690104007518140c0b07004018006030101543d038041480d1f840310040b40034056524019650505160800e4030341742142003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 345178884 1250 345177634 345177649
    0x603030f080f0c0f09040e01060909020a06020706020309010f0c0b0703291c0203101b090608060904081803010207140f030a020d0f0306051003092a0b03070c02061305 73
    0x118030703560b0680c1002c200c0016910002c40e4041c2c0054140551203880e048081000703000094038a02e00d5508214005c10380c81066407085820320700890383c41f4101c5682d000183c0c2c41f5030541c000c420042e041000059400e500400552070000e0017480c14418040d20b60300d42080300c00d401d503108400a920360005a400d00944106016007150740355190000c5918240000d040c1034400c000024443c41c40d40c445010741d5410f01c544403000d82645d0061105d40314000c02e1a00540010015101144401001040c80d034461468284620406420031885403500c0d100c014031900301e030054228480d4020403e00f01c5480c280090f098082c4079140124a200e0903c00701420b16a49070305001f544c0d403040c0b000f11030040d40015001c26602039810051515080034500300e003d01500d070081c5401c1340640c401406142e03407691010280d28089c46135441441e1040b03c0342c1400f407603103010b0741200382500f803018000d040b41070001b0741d00300c1214100703100740380c815a02140064002c461f00c50105105018104180d00708100c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 345180134 1250 345178884 345178891
    0x150307020d1d032805070801020a08181b13060807141813060209040603120305090f0c060d0f09030c1103070303170a0f02301e07030603060603030f08 66
    0x740b05040c009034040110390b0702d407030748190701c031031003014003101c0b4452406103801a00c036540202c151406a40c070f45a046d4043d6002ca980e00780000c4003c400100e41072400340080002d0054000900651411240039420064505080341d901152204210840303428034031640c001801c075140500101413500b515941400d40c008074141c01190240c0310b08425081015045511407a0144010250303955420140000d01843d820160072928115011003880030704812280e103040e042e07901703000395501c1050312a101c006410340c40c04640c0c080d100900340c510b400c2000d480c225403c6140015040c6110b0040e90035145c416606501103511400954103000b403042c480b29450b24107900a18140341b0316500240703200d031441038080c144020003012610010403600310107050b001e00d120643d1580f5503910b040e45a21f1041240852103194130306491840c03403201071614410a1403d0342140d440090010907081488024000700c1015aa02c2010000801c0c901c54000614000d03030b522104e600d03011002518580014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 345181384 1250 345180134 345180167
    0xe09090105070212030717010b0318010b0f0621010e070207060908060105100e090403081e31080703020303040c0b130611030904050a0c140c1b150307020d 68
    0x4200030b034141e000030f6041c0400d4940100030f6500d580d0003400b15800c1d8550034515800c401c0c100000204032541e04c01460081c0c440450044000c110081d0f05801c0b00c10060515410540d0103840c1d4445e40380c00d001416400c440f80c0c2404c030140701c1c0d0003040b80011100360070096018400f141031060140c0e0402506000d081c580c108003843c0f0341882482c1e550364205104040c03140c0302480080c03220700d1241c21000d02203040584241c3c400c0c2054500904003030412110044030000078049480c2c684064018140075170303840d215500340b29044661a20103050300c001c800350b050301039454450000307140e9030003051100d002e94061500d900f05441d0240d003410f0264016407041d03209110b468800e482c1e4101c40340c110307401401d00c2030355207903110055821402a04500c079445807420f01084000309180d00300d2400005140d40f1120810700403040400c0c81c0c045d080c2e0880d100d03403183c5441e0396001c00c11580480d4000e0000d280c10a5012510407541c4c06500841d0350030b005812007911010a10f402c44044008080352 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 345182634 1250 345181384 345181391
    0xf060e03070f261519020901080a0f060e091f0507210605100306090b09010f031101020c130902010305070219030e06040308070302032706030a0c1e0e090901 69
    0x910b8604508034685014003541407102d651625110200c08485003084003d100c00d0f562071240c1c1c01e0300ca85a044003150b103c055880c0d5183c2c0740c0e00f154018421982805c105844010f482e841d80d400810003840d8201920340442c1d522500444e0100c003d62034035110340c0c001c02c02850a50300d0084440580f0382c07034580804040e030030181404881e5400c000118100050b072000b0400b40c1c1d8800000d0301c003401d100e80c802504141015085580d05074590080e1064585804c424044001503205202d00001c1c24455001203c040070310900000e1006084031201c080e0510454080030226030004d108c40ca031a51741c16191580d1004c079a0110750f058068940d101000b4000340c44460340c828020800e000120900508000480300002403650f200302c10f507005107402c0107107a0b44554884c50065943e5205e40c1e803940795002c82180e03000868450086012072038402070611415a00c52000702e9001d0803980600b0414801040426281403140c0c43c01780100605640d680c00041c040300b01070054040340074100d40f000741d05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 345183884 1250 345182634 345182639
    0x30311030103020901140a170d08150d02101206120203061b09010e0411030405010509070b0c07051302070218070f0509060a230304030f141e0a180f060e0307 69
    0x6400301402d04498806c42450410200c0c100000c03602c08281d0000000180090510500c03081c0024007044654810344900c85580c4400c1f00c00101982c3c540712071030340304142040680060038102d11551a9208c0342c189071513050500c01a00b000e0750310540222891480c002035400c15403078100403194100c3d120250119505c00c000894000d0343c0f0031440028148000c60040249945031076002d00c181c80c0f6056007040c0c0328101480c200c3e010300420b40b06540300d44030f070803404100014803c04440300c802504004020082c9000c040c030812946c00300c074410301c81da400d03c00600540c880000340000001b03000e0b400c10b41c61801000207400e00c100c00740701104101081c401d920480e159101210060302d500d0800200044500020408403550002d500381e0400c13000c010700041582140b000404030b045510742010b1840001301c03007130050103110010140f1040c5803000070004c825031002002e40d44014902010000640c0c00384407805c2c0c90550010300c860100307503420030019501942c902400c40d4207d0240403841d1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 345185134 1250 345183884 345183889
    0x60102150603030f040e0405060108123a1506090612020304020303090d0c0e06060307020604061a120a1b030b0f0903090a030b0610140d0213051c03031103010302 71
    0x15080ca080060450148046041036a0400c203403510281040b80380b0b030b501c940340c1c01d00403401042507038126030910031000040361045000c9412106588540300f05410714a4091507210f040f038107480702d04002002c40b0b50f01c14510a18031400148111050301c08030302d07030768001200320608615500c0f00b01007202020041c0046030b0b001410380e000e00c0541502503181d0700ca6000103800c1d841007403203069004420388112400c00032405407400840b050361b00001c0f04d070790701d039810310060380300440b0110f0058005074002400034000f07500c10f29403e180c0c0f1003240751115408000c10f103c2e02c01e1030180c10700c0754820303e40b00e401c01886070720500000000040c11082079107542d81d1030345440380c09041582002100000604802e004105035402d200005040040c41d640c0c07828101d0400c3c400341c43c01d034020700e0002800c0c00440d00401440e5110f03540390003014035001107144950001e400c411180448003844403070005207581d5804032240760048003581c54006882ca443c0103403c84030030402c0c0700340b101018001000507a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 345186384 1250 345185134 345185143
    0x2160b040504090204020d06060c2609061305220501141c1b0905040b090105070f0c030507080a0f020f28020609040c020c0102010c021c0c02060f0f071703060102 71
    0x7034100b69070228105455200060103401400f1044107083e00c0c004c40028500d40c091411b000b2180148075109000142481c2140100404801c5146800041000102c01d05040740200f0100680c803c41030403194a801c00111404114038141e40c1d4801e240c00c1130160224544100350043c4850560007008403049800301e42002e002070405685203921a0112050241001030f000c54048150b40b440d82d0141c440c0c41010042c0402e8400344c40e461412800a81606070500c59113000350415100c00b0122a2443c4084400c1c548500040381006004d0000c0000074442e04043c14030080c19454039442c0500124000340780030b000d40119003040d84410b50703174030030707004c810100c90309414105040a02541e428008501e0354866030700b4594010b8600034002000e646e01141905420304260b00070701c210a82040200d0340d404500030841941d115241d4400d07440360280e8401d4802520190800781400208420900e0940141c041c00031070300e800140c09003c00c01c90000e81c0a6650b01000c2441c10b6013410320000f0740c4e5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 345187634 1250 345186384 345186389
    0x70e090a030c03120903200115050f0409020405040503090f0619031104080d1706120309120f0a03090806061203030f09010e07030809130b10050a03090209070c0302160b04 75
    0xd102c1034004480a06110f0343d890219a41900c206208040c85450000c010307181c040c8508020f01070079100301110380c006008101908100c20791425945080c1030400c00c41c4041d405139642d106640d400d004005803200d00941d8400d600443c0a5500c8190440038000a06908083d507072081c1c804101c0601a552214148881d00045280000e01c0d9240da030142c0c081752096802c5485e8511800c801c0304404c80e80310145044103110304500302c0842c6c1341c0406010000d4403419800c102500140301605003810460308a03030800f60078504235a00f50551640341d604146401c1d108be40020030700d0105006c8003604201703080d00440256111300c09000c15500068036800b0152070b00d2665800341d40071401e80c90b002d4100368007507841c00c419181e81039642c1c0340500955016040c118004c2c4d18020300084c8510140c800d94003a80381c00781c240b0740804032844040310190f1010b000002413664030700410b005a00c5080056200301104e4a991540200b00c1c20083d00e4410010ba440c5070510300500705100448018058408 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 345188884 1250 345187634 345187637
    0x6050103111c150b0a1103030c0409020906041707170a030503180a060606030c0908070503070e041e0605061206270322031b050616050313080f070e090a03 68
    0x11a490a00c003400140600d000b40c415000e0140702c004c01c1541c500d40c000e000c030340d40c25200ea035165900c22403906e4490004039846c24049105010800c42c8843d207400400c0e43c150002c18240c81c00392100041400e090720410550400c5e80401c4c0103005c049134104414030304204010007442410385941d0020803030f200040402000850300d010b00000320707004001e01841d9651042c000d102c4a034a03454010001c00b041e95594000078011840060402004521402981d5001d400381c20302a09111020884850260084131444500410003851001600984d140d041c42a0004103070360411508005107050171104c800400c0e08803405124504901c2917003905041e84049000c0200b505150a00d815805412404910140150249115141441810f4065a1068050b500c0036254880c0384035030100725000352038000c1000c111600e000440c80911a04852041080b240740580e050003c0b80014401e520001599011212501c00c221061040704060801c1c5004d1051a1406500b59641c41021000240 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 345190134 1250 345188884 345188917
    0x1a040f080105060906060901020f150a1a090a05100305070f030c0512072304050108210403080d020708210402041b0801091d060108030d14070e040c020c03100e010605010311 76
    0x42c04d034001d0002000d034ac440403042d10741001600d44e40c5d08880c1001c55903000d8141c0380030200f00081c0c10f140c0107010340d404003808030f007a942d440260f640006c041c0603088801c10880e105c07000000070010400038000d4400020349a0003145145005100c00c2c82940150b84108041e40254008040014040085a00100c680b12080581120107415048071902040c0c01c1805d080021a0b40d5078001070240c4e42c0d81c040680105203801409024103103000d24000100f04c15010008241220010740203400c60034000c4180c545040c0d0a4034240c800c2003084103105154100110070401545018440c80c0d075000346109110700103035203403040107000000502904020a5031303510400600301d40080c0c01206801c42004640b46540c41e806403580d00e0b08402c01c1e1200c41800c000d04040b20351894031049014110360b84079440d80d01000c40401028140f1381e5505011841a071180300c402e82d40c1002060045166054006021000800102e00b036416a8210300d040c141000c2c80e6000e00c00054040381c240302001c41316172 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 345191384 1250 345190134 345190147
    0x6090302070b2503030f06080c0f010302030717100504290616020103180f03050304050d1d09060d12270b0a08040f1514060a0b0319061a040f08010506090606 69
    0x350b00034407045a800c4481868100c0100d58000002042d2880c8270003102e01481f01d43c001c0c00110160302c42211240002007520304c0c00081c0d40c15824940350051581c00b51110951b448001060484403404c2000c0f421140705800010401c2c00ba00203506080b000740e0b4103e1a017466194900160600b5502c000e04050303484001e8240e501e40b0480359800030f60f21061080f0b03482a0307401c00415a8005035420384660081015207000310380190b02940100410703c51a0070720070440d10800184250040241e50422002001100060b50000c08202c0204541e00d418048814903c4002401105042400000005450144407254000003903c40e01e038003501d8030717030002d0b07803a40b8004441e103110b07000003030040103690313a192101481070b002524103038000000708066940342d20422546840c14480d605c00c9003030800200b2081540e01131250054083c8003008114030740c1d1018040c00c88040040090796801010070148101900401d0410003407004038000e0100c0d0810000003180d101c000f415544c400c110004a5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 345192634 1250 345191384 345191387
    0xc06071707020c01230c01020c0a02100503100506030a0f05010f0f1706160513060c02090a05070903020411040816030308010f0b040605072d0209010501021906020c0111040306090302070b2503 84
    0x403218051b06100081d0b440340c2458840694440d03908070200d114540c3c1040b42c1c100315200d00b09032849900800c20003d406460308060240940c0301030301c4107010b07a40300c01144501c01d01c5405024001c2c840e00681c80c1c6118a421101c0e508440c880d00690400348181200b84108000007c0c803d8214403c000c18144024011505840c04d104041c912110304076080000169103400048c46c5804600a42d00301e902681c03041d21440449200711074050108446101c04d2016080c9035001009400e030010031a46460380760035203545481a0000e03004000c009240040c01059480a8114010b218032880d00c1d00b0302e414131450310f0540c01036000e5402003210216103502448145000d100c1040390003030012030b40302030840817070a12001008059001d2400000001980e510004815070755110030000d0310a029066519103020f5032111415400300c1d92500c42000150144100a200031032140400003000d186502c3c020703007004d503164015481d16405000d604c05c000d8028050311010480c0c0d011142c00811140b50 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 345193884 1250 345192634 345192637
    0x70506040b0919030e1003060806040f150e0105040515040309140a09050f0412180b0d06090e060901060906032a090f0b01030609090809060f0c06071707020c0123 71
    0x24914200c036402c1c079800506030040c40145d0701c001c1c25215480804550b01043d019510340c0d2050070300e20307404407001901250041d019100c50500c101045015180030700d40603811b43c0c1520b02c0041840e55110248401c11000700940042d5807440c20a18160b89000e0302d01500c40c240c540710f02901c00070100d1350342e40c89960b8000348002401110f00100500d003826401d5000c0100c0807034007140c02255000007000046d0260300940e920400304000c4100c0d290409643c8034154003da01d40c8000e45031202c0b00800c00c403125001c0e40b44543c0060700181000e1401d469013509659042d400300e4100d900c1d040741800415226028411000c0f1201c1034071915020300020042003d03510b0b4001d4041074900962149101d40c00d420440d03031504240d82c1481480c2c1c81c0d081700e000b00c44510700c0081500d80204001d44c0c40b401d20b80091708251000b5a4040d04002c02c10200c541088030489400c1d0001d402580c7c000020700c09607540384d401c450340d44018864141043d00207007040c4448a4843c411503450040d04000400100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 345195134 1250 345193884 345193903
    0x2030a0803150405070309030e1f03020a02070302030f0102210103030207050609010c05010501080c011701120f051c120606110a0201111219090515042102061b060606070506040b09 79
    0x20010451417411010090042c0183c01040700042d1641a5010759031500c200513440300080244910341d60480315000340d00951203072601034294010224000003694081c4914140290308800160350341c49d0902d601c000c0341c0034800d6100c04580f90710340188042a400509541550b20940b14555103050203130050701c2100310901c0083c200d44c00d20001082c1100017055142480701c080e00c6003004c0d08454011070402d103800740104281ea924000500300481c1072410740c980e02601610aa5a4024605d82c5d001c09610b841d5144001044161101e00c481007110711076400207280918010244c048403041c0340e500e80d02100c0000e41001300d885c0340c0c032408407400e001122000200451517561000c6050072a4140c00704090110301007412020300040c0307402c01c203546030b0425010b030807420703e000d0034450810521000100512500103c1e06401401615800c0007000c2c14010f00044519441c90120b4a0b445d10500400c910301840c01406040300261002035070070b8019a200450641680e80d40d0b030307024039214044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 345196384 1250 345195134 345195139
    0xa08030403051e0d06080115051c0212060a23191508030d0b12162c091623120a0206120f060114121803131e0302030a080315 55
    0xc4c90703400b40060341c0c0f102c421a0710100c02030100110302103c0c500742c07104a1140e40d4000c3d41013040307489001401c0e0f9000101620040545031751140080708a89000341c2110744901c1580e5072820541913044034011180f0801c0d010545415074549640307104994000c180000607065240e10440c07802d207403d401084041c2120700201c0e0340f80c2a0f640303424000340080314162401341d8030300f0944089160010403095209030002c100908942d1034041c55503000d10003c0094015000c52000d18071a030100c444079030b80100407840013032100610b6040c2c2c0c0164542e041c2c2c085000303084d00b501d000c1d0154109100141b440300701100c10404035122026400d08002c1002e030b0095001c84000f40040313551a0f141842030041642500d24502e541c1c8840054909050b05002c400c011003061000d0030959150454580c1d200360311080c84641c000d0341c2404a46542c0104458034090b4420780300c1840071619014210700d0880e00301020200300d41c590f801207a03d031190550054005040040040c1e01646c002d407002d0b5502c80003 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 345197634 1250 345196384 345196387
    0x5030622140313090b0901120f05010b030a0309150806031207030e03060103031107060807021f1401150201111903020310030c0b030411090402011d0f03010e0c01110a08030403051e 79
    0x46141c410b02d995004c1c11820900e4554551501e00305451020f0584000d0050b45404010940300d900d04200d2601c4100ca05640303413014111703251000e000011025100c0c2d21007070013490601540d2200c880d4030b0314220081001040030042c0c10347d0005000382d0313102031058215544d080c1c14182180d161300740500464240c400c880001080541c0300000c1519a541403050f24881e0b03489440490310040f0540d0040d006a00410041640010031210081007000d41b02000030f01c000081c44000000000f42d0000710044221140480c05540a01820360f280080965162070500c4800f050141c078002d41e946602090307030102c00141d00b0b80643d680308000d181c11042c103d580d1a902c030440b42d66a4800c03542190000704002c0e452a85090040c0803a000c1c03036050315900c00e040000750400030200c04e030403400380c0d20464070084004651002c0c0b003240760400c4d000d070241c0354001802001600d806000080c0d0186644508410070200741210183c0b90001d502d4505641c0e144030601483c415091f4021864006100 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 345198884 1250 345197634 345197647
    0x212070806010b041d0f010603020d020706090b070e1c060e0705120f0d0305070c0605071e0203031803040e040611040320010206010626090102161b050306221403 71
    0xf0070018004940100301d0340440e07007004902200c00307401c007507442100e40130501005100860003a005032400000c034040050270080603440d4a42502c0070110145d60030696001407060040d4003420384140030301c00340c5080c603028070a02c400307100a0040c2e101c094078050341c580c0c070b2042d291403d0101800402008150074416201e19001d03a4491090b46100404c62040f2004800d420340a405a14414121522610801314298076444041c007801800c0d002007000f02c1c101c840c600840c0000701c5948842e15070040d6202d1030402c2030399000c2c1d0288903c050706c0340d000b407008105030719034941c80b5036010307a1000b00840d603000e800300c0303140b281d0140c0d801c02018003030f0518640d62903204039841c01000704026400c466181c0d99424040c0c4a440e20500581001e040041c0650f150f050810030264005682100062410320728845070054181d400707004942d00f420261861140c40716001d01c1c0720180c1000c501404460030500210792448112224000107684201000e10921000040c0a03000b0440c42082d2617480e203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 345200134 1250 345198884 345198899
    0x10b04051f09060f0b0a0e0a09060e0915041401061d09010c09080309060901051b0c0109092a02150109060801110f070605100b0703031a030303090a021207080601 71
    0x15070020780001141021140000c5649050060200b02d8a5441e00c07540094280503564100f9805010300005200300403040c103071035840c3c5a0081005100d0003100098240c140307481d00700350360409803c0c800b41d94080d95040340e0034080000016003040c0e20001c1c215030a0302c00d40750f1038050260b40c0d00002a942184407020282c0d00c20040d0340d07118540b410020440c5841c081d000340d803911001c0c02038076070642c024082300c401030404c1c100401d83c403c81410700c5410000d00c8841c108503150f15900000a0750070006c180500c9581005c015009800d90f9001404000c68258a4107a50800b0703009003903a6605d800d20900c08a4002e10240a2a91440c0c0030114a503840e5014480036240c94030851581d9840c010722880c1c00715944050701c2c2c1200010070b090b45440c07582e844a030068a4040c00d1111684080c80f80012440900e400401440741b180d200410410144d80500b003405018030082c40c000c0d0010002c10456903004225021469070460b12001000ca0101c0c1c100c2c9080204d4102e400c1c2031107400c1c00440e0300e8 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 345201384 1250 345200134 345200161
    0x15031509050a05180637050408040801061d0f06010e0d0b0106020d0f05030115030e070e06010201050f011d0406020d09061506141b10020a2d0c0212010b0405 69
    0x4044c5101d005031051820060313555134500c101c4064000b01001810000c0b031304e1001d0302c060030400c4000c00020b9124808208001128030940d001c54403818001002c0081184c01c0c003170308004140403030031500000707120142c1256900c8010318104410f0084400200b441c0c1c01401001c041c0721024284a8554840c0d00e01400c21450a0190401622a00d080030340243c0c81100d00302406200c41c2d94103400c603440c2090b0700446290650700740d000d0589808650440050070040c000040c240700c40c05100c42c0c10448006405c441d3701400c00b500c41e0510b000144018800c0c607103058081001c6034041281c0b07654a0802c0c200a0184c00300540b0072030b041001c0001406842d800100c030300c51440060f9140d996580005481501c201c1c001c00304c1c602414000203000d85505501100e5021a0000b43c81080c10340c140c40c1c0049900c9032462a010031603181c2a59400d00c24201c03e0803800d5a040700204017915241409018440f407428028031070b040016081e41100c90a401c01c680d070b480050014055400c1481542d12403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 345202634 1250 345201384 345201391
    0xa0e03040e181b0618040608151608130f0303141f05030a0b04140304030204060905090d0c03270305070b0304120206070f1b0b07020102180a15031509050a05 69
    0xb031180b264100c2c160030840000c000c0030383d0010000b6241500928400e680361451030030040d845556802c0000d9500014030801c00280c3c481d140314541031400b0140428240c10400c195030420a40c0c2d003c2100c21110844025400d0b43c204100090380000c074941100908410116400780c2050038080c4420134510300521102082c1c0c10398121283c5456000381540d600301c100c4040c1458061b0004600410f10143c3c210a01c017401d40150780c41d00d901c940114041c0c90300340d4480c1c16039a03612020081e0308081480480c090041d103140c0440844e850703403030007402d240386c500c05801c3c0851000f0725039907148501005600196030103415038080039a10058582c0c1900304a400f41c88101d001030144401d5031000c24418401c5e04141c03200b001c0c3c440f0041c01210050b441d52400601c50f40303141c002801007100e42002501c200c10039400542c0e80c0c071902160140120030920356500500d4140c50034030200c10390b1100d82403062400d00d000140d40708401244603109000741d00aa654a203404184184554203401184c070 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 345203884 1250 345202634 345202681
    0x70809030723060915071502030c090915010804120e1903050c0108090604110105090616050c011d13180525050102030a0f05040f18110906030a0e03040e 67
    0x35040112010302ca0760344202c1304803aa0003c04840380442c0049400e010307040440c042c0030b40546480c0c0c407003045003c907402551b03800700d000c6020400342c603a03240a0304031781d0388452880d50010f106a150000071f000c1c1f6102601c010203035680c07000c8140c1064440c948141014500400b2582100b28804140035421964002601d40307029411446009500442e80c880c000c1c03503040020a1a503171140c07200501112001c40e41410014100310030840c5d41d4601c4007505e5003d02c00c02d11096081c08600d00103143c01628500709052007410f1441c89480903d10003800610034050381d02102a00c00f40c0c186a0041a00000c001d55042e8512591420b1001c00104140c3e503110a045111040d050188041d91100301c038464140141c0c410440010b180d0701c220003592003100c0c20300b0064140364840c0c05251040300c0030780011a201308130303d40851718118240030340022030080c1a442807602c000580452810322005211549854568411180301c0e8000c0003210000e06400c8491705181c100008030003003a100c0c507940e0340c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 345205134 1250 345203884 345203939
    0x130903020607350a05090d050d0c02030403060504050318030d05091c0507060203030919020d03120615170f0609040b0912030109020d0b01141e07080d0c09060c0804050103020708090307 81
    0x824182d8006101c9940007012345a2078245003443c0b0383c0324080c002c181c0020301140005e200000000d401401141c0c0181e02c00d0000d0361b2034001c50501980c4c0c0c41807100581d1b22981c4101c82d00782c001d6401c002129041441942e032900b404d0481c1c1e00e03140340b28400720001003142c4612a00007800550210145000d13080e00b0049d141c601c08100c40c026840000b07290060341c49501d510101c000070b4010390814100c43d807060404140c11303554269400210b0b1072640c1c10808107407501074908503002c00307402c1d181d4070106800d0810564100383c0d001c10007050f0003e000500245122000c64410703c0104115200030b10142c8100b5540d607120310200c0d020b50007001c00c000d10746041c140d10400a60003070800c1c00c0003001e16550181070aa40094040d0303050400c510084600760104800c01c0800d80400062140001e452004122500c0c0c1e040e00030070740311140d44260200401c00e1000000035940384103c07030031a1000d00e000740e2103103514282101144180c1c5d960903414800c4041c00100e4150580301011008400c0c0d903200f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 345206384 1250 345205134 345205141
    0x10915090e0f04030f1e03020c0a0f20041514060d150609270507140d0204030309150f0503040305190c02030f01060e060d140a060b130903020607350a05 67
    0x1c0c0e03050300070841c6c21008051a18100216039100340d01400003414540122207100070329440c3c5009051100d41c1c15200141075400d4450400080c10440d03c0c00388050b1810043c845108039450303000c64880c02264203940b007002c820390b16642c900040e0f0342011402d0358100580b000081809454200500c80d0350045081141c0000746000c0d071080d034003140364149010850001d01100c14074002c00d0011f0401c41444154080c0201c40703107880015080958404000583d11415420041d010380f4041d40700219440c55080b11000b05135102000420800c0c01e818040d032603031600d1406454900590708507800d0700003044001020340354000149108a8000d070107445013811035139101800d8445500804201200d601c0c00f06640d8100405640e40d800d00944000311007030a0500442d0500440d21010742d181e5845500c55406840c106c0b09092503541d01c22800c00854a1030340c0c0c080c0d02c0c0d100c01420383d01030000301c2d0102000000c0300520f0340c0343d140117400942c14100d140c820b02440c01c40150b400c140c81c9450003000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 345207634 1250 345206384 345206387
    0xc0301090c030903020c01080403021e15010506041505090105071707021509012003040f0e250801060c0c17030a020606030a0c032303030c1c0b010915090e0f04030f 72
    0x1440f401c2e0390594041e0109144500c0107598001c000790044045100b0701480000e450315481c0000c00c0102d05034050701d14404d04003040600341006803c203500c90f040410040000403091145008108190300301070f921140c801006917454014035401074650035117030700710b804c0c4100c242d0018000303a882125503990340c1c681408100c00901414011501191400c2c041e440c180c8202c000381d4182d1040ca10803a458580c44441c11442c0320119442140710040c42c4d410b11401d800340010002c40344d100c2c1d138403032120642c42c4400104028018811030040c40745c42e60b000c01c01d01000c2440310001d042500000c80410030306d0400641d69501a02000006003d9800461703800c1c039001c22040c00071500846181102c0c1e00359203c0380c640000c44100d09450610010750f040b81058244003840c0700380d000030b0303695454403d400103002c0091902d030391002c81c0c0c0c3d01d040d44906460b078000c00039106890500c001e0000c41c054100c01a0740c8070009812411111311072108102100722800d030064070480c420740d1001c4480d00070180 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 345208884 1250 345207634 345207641
    0xa0e0603061b0901032c0d09060f0801060806121506180c0d0b1f050d061e060e030a0813170604111014071b05010207120f020f090c0301090c03 63
    0x169030894880c00c02103421198070940015155040c03004c920440800501186c00c10004144c640260390b4124000800c0030a410540803001020f1a081040340d95640110040150005000b803109002209010800c107845070012500c5861500c011680d6400c4002007885192201300c0d02e40b0b1248a52445200740264184405809207084284160500098900c15405019040b40716900001d9400b0700010041c40e040b800000c2190700d46a6950b0b4490010050080d9100d640054a413100312444800305000c00c800318008852152420750384440c08400000c0c2424107003140506001c0300814400c80c0045892810b00494449100c4c0c9541440403d1082d0348401041f01c004c0c0c0705140e11005d403099800c0900400620241c145000442440a030000d54080d030400c140544400d00c0c00c400f030f001d126a1500c0741501500003400105065450a44011628003083c0f4000302540c0000f43d0b10421901c840741c001d003003124000c041c4140b51500007126000c40c0c10134030070401c140e41066542480303280a8072 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 345210134 1250 345208884 345208921
    0x90915110f0d050403030207020310050601030c0503091b03031909051f12050402030709090b042003100908121303030f0207080d05151c03080903030115110703020a0e060306 76
    0x41e54103044034141040c0090400810076800d15408120220040c0c0d0306200c1414030103d044000070320b50030b04074001411250001c10810621000b0401d0240000c800a4625405c0b8503107a00b03141c54440c0c520101341140900403d0210390100e4908003c2e0742c07504510300200740c0d10280d6070240242d4103e10b445401c0b811100841e00401c031250021210a07055822056020307002a0441d080d89665001400495030280310660f06040130310203010801c266030125803110041c0389450030184e500c1c00b000075100d078890a4170f0b07080295240c4003401082001c1040d15202d5882c50005c4407140b07880c60f8440c0d9800c0c040d620440029203006542040c10311188240e410190b007015081b400c01e075041080c070005040241c6005140d001c24120080c05503100442d00035000003884ca00c10851040b403902810302d545c05404880982c00a0006000784464200004071004c103500c0c0801150000384403860510701c944d00083e4002d44203140100d84084003084c640d00071507040d400c03107269a070307110f032070b01141c071480c3e0b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 345211384 1250 345210134 345210157
    0x20f030102040b1e0c030304150e060105130e1501060903120206070509062101030c1707080d0309020117070305041101020d020a031206050607050604110904050a021909091511 77
    0x611480e44c18034404104840340300001d04001d4580b048a1440c149107410448040f148180310350034a41d103040c4503004a10000c19500018900365040400042c040381c1046450b00c4200d0fa07400d01851003400400c144060061019005041540c50724402407420201d40401e4844640900c0c6c1c43d1802880014014802e03a1607036521401d00c0340300020002d060b07002c0203c19800d00360079007401c1c0700508210201802184110b03641c02c003142c50028140141c0c01ea20b0340070000d64120000402204802240c0700d141c9400e145400140342c222840143c1c0c485400c2c0300c4460f00c00c4030390b1040108554041e40058020350280814507255541d210049a5840b503007071030900182c0110980900107405818842000348402101207030441e100c0b00070426a401c00c07541610f05501000612091080303035800000c850509444c4138020740307801d80b41c0b180d82e48803680c0000c0c02110b03000b032010640800103c165003e016446010310210704bd45c1440c0480601d04907110b0012494420b100c5030aa03003060890707001842d032 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 345212634 1250 345211384 345211387
    0xf13150b0f091005061c0e0a031d0a0b07020402040b0a0f0e04230a021b01020712030b15070f0f0303091a060d081602061c1505060702090402010201090803090a020f030102040b 77
    0x203100178040740c0e40024140701c00c20903569810304054003042c080c0503110381001c0c00800c40807400e0b08004041c40740541c01b035050303011203016410241d11600c0720310b000ea414003842a80e9580c058408180241f15a5002101107040890070b0000142e10058000c0d01c5421075a0b074001c072094580800013101d90800c8240e00c813920000c86e0020700e90501e90516171100d0b40c0e6200606081c1132000c0c05107603c1c1124400c0001c0c0e5400030f0040100280781c415082a400d440c60104100c0c0181c80104555507040500c0c003401c1e4101080380403c01c21424086131050f5441890710182055034600600a844031180031181d41000d040c1091181c00c01c5020329201b1200201003101c450450b4884100e940e0080f80f20161442200c0c5c810030250f240c5400a00c03214110b101c0850703080740c06405580440d000b000302440708560380c0c102003060b81d81d11030903643e00302c2d011680740d10075481d50710040c2c0c01080481d0740180020b9020080000e44200800c0c085612802541c1c801c01080c0444c00309401c038401c602414603104030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 345213884 1250 345212634 345212639
    0x219080f1003060e100c180e0c160507030c0905090c030105070e0f0f090112140f0709020901200102090307060203070c060f050d050a050613140f13150b0f0910 70
    0x1900704941c1042c41009660420340403c4005c0300382e4034401d821401141c402e40041c24026075424660f0001c0c140314040f10400d04118202241c548103c0c182d103800110100701c2c3c6401d004040c0a100d004542c041040100580e0b68800000549011a1444003c3c020201c039a2424281030013010700c40c0d5500e03615006081d6a01c01004003000024400756041003094000c4901a03c81d0182c0038060900c0c43e00034251080d6030700d84005451503400120ba115000f9050851039000c00040000c00e070341c048100540c642c100400101c80f00d60304040c0e22940900080722010380b114043d8010181e01c88240d05880c0002e4540f401a41e4074856180c2c010700a030300d40c0300304100701440746c061003590f083c651900a1a20f03510403410000e4032001e03645240980c3d502c1090100605c0c004c0540d42c2e05e0315144505006980b80f00c10b0b0702d11180c900402c10f01c0c1c6034180f60005140e00c80b0110500384010740c4440c12503a0482d52010001c001c2044404084c040c010200f0040118500611518441c0c00a080800c0c0c6031030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 345215134 1250 345213884 345213893
    0xd0e100c0f031b021c1e03080402041d01021b0c03030f03010909050c060c033f100504110306041503240225050c040c02100504150219080f1003 63
    0x986916054540d25100f41d65000160340e10340c00c0102590a150b554120301c0c14504000000e000120342000d22030003810962070000741c1149909610640440380040c441d41010f180c00c1c8010030001c60711445520025400041c140506d18420740401ba40040b101544146014503a4920400d030b18011803403004d10042002d0200c0383c001d010401d02c54025260b5100781c01c4089400c035000030340200002c1e00041440c841d240807440c4014218a001c42c401c8504048200e5a40c44807c0030f400300c080030f81090030000c1d901900c00e260740c10040c00040c001308084159400001c281d5003060b12414402c42c2808000c2c8000e9a50141900503690003100d80c2c022421200b120014413500c02c002143e0b00c607003d12010a6003080d081c04190a046034041140e00b04070249011410140c01885c0740d449149009034002001d0390000e805103034031042090001d803544940c10321804050070f900c881207020b4000282400c0c20180e50002190000c0a41c48404030742d00d031082c3c040070019088a10211444110380d00300b000c41c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 345216384 1250 345215134 345215147
    0x11b0503040b0403030c11040203011404052701020d05091b12010b18060102010509010e1b030709150609090b030a0b07181712030405120c0f0d0e100c0f03 68
    0x6218404403440d00303a440034000815049544180c0c0860385042c80c4106000c0c041307070710302141c8104076000c51556062900e2009102c0380001c500f4040d541c0ea01c009429428034080a03c0080500a00c041e08004c0d01c0c04018041d61160250007001ca08010100d11042d90010b0850451811004c088103103000307040a2022a115219203521103648036100101152500070740302c85128003140c030340011440c0030000a0f00b9610050200e0381c0b6a071510000104031000801d00c2c1a0000710380c03080302c907801942000a80b9004854000320b945a10700002d100c103203090300e01540200c1c0e2080e1110442a99120b51010480301031141d400d0709600141440b44c000b0300604407013a03000d070305818414544460f0380903d580001050f04411070aa0840c541c0c08a60902089022165401e10504034070b5850103640d8191241d2442015084050f40400c21441c1c140042c80b1400b6078840640456441c07410190004182d001d85280c61030041034a09510f2510505c141405030390303140c0099486072030482d42d54007101c40 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 345217634 1250 345216384 345216437
    0x3091006030812070203120403020109030311090a030809030c030313061413210f060b012a020f0402090d1212020712080606090d0602031008061e040302011d0a0308010e010501 77
    0x118082003208107e038060080b14180214007a5000042150451401a00b01c0300b1940ba000700074102030100400d1940c848040c581601e50020840e9103030a003440105c0d203083c440b010b04533410301000c00c0b0001d5038410380c00c40703100701c0324103036500051031050b010340e070446100304600c0c0039500301401403c0c030819560082a0440d148840c109042104c550b0311500c00e040f036903090455403a62039a50f040120340e8030544540001741c4d4403040117013012201c0c4078081c03250300b40e12000303028160306014172030300b6522981a10340c0200050103200d00080180b6040c0c00900325880c030350700444e4650141ca0751003d0280b081d01c4086901ca10b08a207100c0008105648082008011a0f4016410031010055480300c854600b016440342c10090f03124141400c0c2c0404003401c3e0f400c06d0346142e20072400c01c100c04100c40403c3c034040c00f2080700d851240d01c0300c0c01c5c12805003500b80031003103d000301e05103200300000b00050042e911038001d130340b0b15505176291642400c0816080c403440f80020b1681100c030241c064807000d560712 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 345218884 1250 345217634 345217637
    0x20a110a030b071101050115020a020f04062103090e060604030221030a031a0f0102030901120f02040b0c060a0e0c10090f0b03010612020301060219050c0301050a020309100603081207 80
    0x903540d81e0740c1d1001610b03902102c0d0000001c038008041c16804209014040c050070296510000d10007084d2402903540c40c6140019200fa00400b01074622343d15039500003000b0b8054250a00320000798110094821500200c0490001c2c51440c000074126691292503801134400070100c501d41441c41e002c1103681510704200c100840406240c0c0041d4010800003042044074039100400d218002c02c1c1c400e0400b6a4224100d405042400c41041c06070ba4080100d0321100000d0a06c1c035028a04403a800300100034100011404600c00a00820343c108004090440705032040304840d003a50343c111051007511580000e520059203cac0304110600e103440380400c001c014452800316941507a1320103251005103168401c03c0c201100100501907660300c004c040c482c02e0714401d405e51441d4034200340256190690610380f45011020050034082140c01c0c0700c103500d09800100240464100076120f90000d43c0b0641e00301c0400e120b9446144c2c1c0000d02c2d07004410880340c01202060030b1003006802181c800400804210 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 345220134 1250 345218884 345218899
    0xf1b320f150a0522050c01091e0e0709080a0302060406060b070c051002150f160206010e0f04021c060f06120507030206030606040f0b04080615100e01050904230c0703020a11 76
    0x1a1340c65001e203078110b105003d40024078007110000000b609850880c0c102282c21408414510420003400d800381c0c00301c3d50101c3c06d031061503136460001c0740c501034140c0022005001d00855142450b50000301540030b00e0090278104407266072a1031020051144080c01400c0b04040b0200f084030b4581052164000e000174016944500051041140c1d5550201e501e081c550140d50180001c2c2303d1447d645840b4401d0300d0000308115410081c14550400d40207100c404840c08541c0024115121001d400c081da11028403242179041940c0f604078007400740a459129060304c1c003103001540901c000d5a4552007034000001e020214119028098035134402440f054214070b04004c0017649121550551004100d4183c80780d0320355050011450521102400104803064107009641c995607462048800c5002d450400c82070300c1200a00581e268060b00d10180e5000386800148075100004082c2481a04c2546051040d250f40d11004e00c20a0302a40c000600140d02800b80f010000d0f00d43c8007140c4010708c0040c4280c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 345221384 1250 345220134 345220171
    0x80312010b2a01320109050421051c0c021002090d1e171b010c1d2b021305040308060909010e010c0c050c010f1b320f150a05 55
    0x6004010400b4031100311315000d0410f80060b0011410a140509134014060182d41020348403401944003903038694420300740c0783d504400303a24083c2c2c040b0f8a182c120107502100d05100604030304000c1c00d0440417600540140a1408080302d564400c98140d102e00510201040416444078542d01000200100d4080941c01168000c501041c40c10f03410342502000c1d5903608d4181b140d40c4540d4000a0403080b030285c3c102024008600e410000000c6130300506213141c1a00d94081000401031031010384076001714600d103480c521210781c0503400d07030150034004c1c0c45410f00040d00c0081d14045990481d4003600007501030020500c10315144c2e0b2183d40003106000081510440e02c0c4400c0d00f1070740464603030404180c02007008820802c050000204c1c2d5182424958002c01c00e03048082e00084070414991541207510f00c070103040100302d4402d4401900700c0076002c03401c802c07080070400e2807400354500380c0d6440c81490203289d032917100083d801d0f194280504005e06107490340c418074409400040c1c55940005030b0401d91 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 345222634 1250 345221384 345221411
    0x3110c03070c051005090d03050d0b040e01150611030f030402030715050a0e030105130204020901030905070b0318030a0e041503060903080610090b03040809030a0c080312010b2a01 79
    0x140c003009002d025040ca00b40d00c0c090030400b44400380801c0d1400d10409004075100780e0703105040022001e401d418031036942d0b001c1c080320380002d012010006070300c81c0c502015a80c00c08070540c000c504c0f440c44459000960b075201c04041d070b41c44840740c7d03800440b41d10400c425515180341902550700b051001c2d040300c5035142c9404009404007100d040d040b0010740b020540811aa40c0441050300c13048040c0d00070841820101080c031220840310030041d000300c3c2c0008520340542d100e6481000803d030018151070289880740250300c040e52060310707240d480002003429039100c40c6c404011034a840f103803900c600c2c0301c51120406100161540c4804111032101044001003c11054052044014426982c1030f803649400d504214000f2031581004007004a011800d003c050f07500002c40383c11640090300c90707407240321060002c0c1c0303880c6004100910303041030000d000404080000160040400b45041041a0307030321204401001c0c021130040c1103c41e244c15100b0b5a04921855500c55810182000815040460000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 345223884 1250 345222634 345222637
    0x280e030412051204090b0405010f080613080c030a030b0301050934090f090219080a08070c0f03080c0f1b06211005031002040311060a030608060a060e060d0302060703110c03 76
    0x600000e1b0301d803608100c0900d000e01c9041d0140c6204826414540c0c10240b50550311b140040c0350590080d00720843e10b0520101c00b098800d030403180800c699659a00e010010064004168410300035801d01c0e01040d80c41c4008110004103160900000c075101d81180300000e900342032004c0d010801e464040c000304e03458586d406a1916950f5111020924801500c10b0100c244001d071003104180e05032030024040c6c1380c00868200b59080e080390415480708420708290305410050f0b131240701c0c064580c940002c1045070a10281407102540d4090340c0440d880b07004080d0710359070b001c600c1450102a288108100d850304002800000702404440c000d26440d882d4210340c00502a1000445180000303010030a62a041004c421551307100388007036042c40d16595404503071258862034280320f054040303081000d4034407943c800e100900d1008100c800a040c181c003010014041fa005148409110b200000c0309420504d46060f54641d0590092481d9a11040100c0c0100680701080e103480b4810012070112400400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 345225134 1250 345223884 345223889
    0x7050d02030a1d0a12050706020d0e1f0209060405100e030a23012901050c0102030406060f080c010215060d0f2d0c030314070b280e030412051204 64
    0x500500f007201d03d1020800ca030401c10205500c911011400940380c408180802c1120b07061443c1c441c0711615184000e80165400060402d1170907010320b101c0c00d400512195524040e456428035038072404401d0040e44503964030365130811000c000422050a12032922001030000f0b14011504000000000f4281140d0b40b00582d60f0040c051111000401141c0b560703080104500020450030240c5035500600c0980540c040710081000c071103078180399000c1c3d0211804000d280000710743c0c80c5014980ac50042401d8040c01640c2951000d000c9240c03c0002840556844141c0043c51841d4800e041440120401000c40381c010341d240400100042c840b118400740e0621803145551802a000407040f08080091506a030000303203810344801240303444645605a03030b0181382c00701e004012400501000d200d8031000905022840042065481d810014000c0103041e1243c018011f0703c0c0007062038107882c241c0c0f41e80e9456400800c001c02446484040707141e01c0b584110152421900ca4010901c1070741c029a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 345226384 1250 345225134 345225151
    0x10309050d020a02030d0306030201020601120c03051f0c0c05100906153b0f101809020108060a0605040b1803010c0903141507050c1c0c03020712080702010807050d0203 74
    0x140f020110300c0e003400300200018452030b04200380380ca907400007581e030281807240c1700104840b60700c2d1500340410b06000310040c60300041102d01625402c81030028641c035170000c5207800c1d4a40f03080005410300c076800000703081c1d80000c0208540307500250120000c120b80c0c00129034582e600d1005489200c10004000c0c001d144103062001d82000b90000800a10012641c0980c00c6105524641500890402d041e07046a0354a00000482d80ea4100810741002a03030030003d9011540c10700d40000d01c05a0300100c91f046d10031382c1c1e03803ca0343d03d9004c24490449021700480012901c240001e001c440c2012019090b04560301d5180e01801d0090f402003421203c003c01610b0002709000c00c00c0c014403c10402c2001039500c00c00051121040b0521480301c1c020010345020708100e000508140f402c14200001c80c613850313080031800d41040250302d005d0303c46c401011003200540104030000800c98403100c1c2c094203a50b080101d491038040070303078011a050b01c8003d01a406116041c003046c880c000d081d201861050400 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 345227634 1250 345226384 345226393
    0x70504030605060904081e0d061203020f0601061d01180b040812090607030807021e0715080c0708070f06050c0d050f040201020c0108100e0c031f0e01030809010309050d02 75
    0x541c00d0203000d40d07900811850090a0060a102c0043e04083c12540107040316204d440d80150484114089481040b03e981248e50601a011604100c000001d056003403094003180c002c04043e500d000d40703a080074401e001c023050501004aa010b8980c010740035004105141a500e8a003031810342c2d588001d226080f02900c18004681441680c80c10880882480d4050070f0003030078541900c00144003882808402000c2291203400708203640d008010001010111920009441061a102c1a80c4042ca4400e602ca050400010300070342034041c41c402405008000340191034a031a903100d10823180c2c86680c0c1124054042c502e41d8001c10030038402c103800b481040051079520700c2c66400703d400341c0710080d1524001481d004240030050703800261220503101c003030a000a01d580c030300d19a0107a180702e0798002c108104061041206100c04c210045201c0c616208100b84100d004506a90307802000c0e0103042105203114005001082c050300103005104030500d004104420b841d6280c0d41086c0e8110408070240e1302 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 345228884 1250 345227634 345227639
    0xd05010e040204060602071a0706061d040b151302070c08060a0911180a112208010606080405030304110609040e0a03030c050910140f0c06090705090f01060e040f05070504 75
    0x20305001e0706009017841d2009080b1141028580c603009082a000141071b00400210301c0c08104554102030000c1c03400d50b50001084e20078504452282c2412201100d60341d007074400040b49000b450200e04401700c40502241c00040340c0b403a48100070741c0800b4040c2c0b00a000900c001078a5541003100c180300c0c040c03801021a00d41810f02d465041200030004480c4506a0440c2c644011203503040c010303500500c00c04000c2103007401d52032103040500ca101000902c1c088510001482c12403502d540c1401c403500d9500801203030327a482008954410b02504c004040760001c00125020450170856605c6844004100340d242c101050006401c485102c01201c03095041000000c1c02d043d0140300e0980e0840041c20007514040f0b007080000c00441000e003100090246135041036020540d4481540d03440280c01c406599a910403180280d40e80b0400c40307802d41648210540460340d41030079515a4040c11001c80800d00590a107542034a0480810030035a13002035460001c61203d5005000f00e5008211548a4070740d10350 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 345230134 1250 345228884 345228889
    0x905010f0305060109060e2e061d0406030b070c050115170d030b0a150c020618090a090209041101112a0609030604110d0b0411011d0102070b030c0d05010e0402 70
    0x164407508200b0f103011170800c000c1c003050b491030340d002150810241411002c00220400034043c5003058210303510342800441c40a2b00a40142404958004103c040c40c80f2013080000ba0b40c0940001001910a580883c07161130040c502d2181151107900040340002d6510340c0ca411a45103548890710002c00c1e10940743e20501c00f48042000f60301c03585828003142501c40041002c0300207601c910301d41d451180c80d4001c0603a1080c00c0c00696564014181c9507980c401d512224644e040b01c0203c1403154003280b002c1020001e29109401010f40d0140c07a26869686a0711480d000d40e100045d02414070101c0c1019880161041c03100c0340f00e2108043c8003c80410b050050380100a1944590703501401040010181c03d07500000c4550307019501064460141810a0114150620510b0010121306450f018042044410b281c6160348070b00c280e039140c05071003d01e000c000c1140e00101120f80941c001c1d0406001b40c10890300116070104450441914207405150703a00d0840c1c5090340301c00e01c100300d264144811403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 345231384 1250 345230134 345230143
    0x616110f0301140105010807050c0a0c03110607200f0306040b070f090f150c1203050912070f03200f0f0f030a0503011707090509060712021306030f02040905010f0305 73
    0x40c015002040480d04459100b8980750045c0240350600c01404002107019120740110348040490300c2c1036903011a0545002144600705000444076401c01e05244400c90512005950342103400440e616654400c04001e081c3e12001d03043e5545d041100003140c846691801c11143c1e00480c030400700400e440c50640802131a48a00f00003103406c03c00458070410620103911144e90a5844010641d58004900c40040e00d5042011038014403c01803891518120b941661003948201245030035692a00d00040b000c001d188079605000b00368005541c41500405d00c00c6400e01c404000c250081d02501198904091404200341c420f010541e00064010402d0320003030100d0200385c41c81c2c034011418000d1000004c0c0c054001405604002c0345010071408100d202004240010304411800704a82c1c102148400d03110401221040081000070140540f514030780e10848200904840000c0c42c0307542072074801c6002e0501c181c40da560036074007800040b51101042c42918005e16000007215190b0b4603601e441400c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 345232634 1250 345231384 345231409
    0x191d010201020f0a08090c1203070c05041107060b0301060314030a0e0906090105100e060a0503150a0807050d06090506100e0703050405190f061a032118061611 70
    0x1164010f0069419000114068400c00405410501e01540e50001c2452500030b038200502c0d4030a1003c0301540c0d801c0c174040000d004041c02204030700310080d1a13000f800242e864030702c5920030451040054501042c0203501828500c8401000420b106580b500c82c0b1041c40d5441000c2c962a8100191110000b90400c21030000590107943d0700341c00d443e1100000c0e01c00300c4c05101c1e042c040c1d20400802600c4034804c2d5941403210000502403a00e4484d0030034018000e4100315043d21011503480c034414010318110b4140c600f2100c1c2c040042c20442d00300018403002403800042114000d49881d1400002001404950b1249902c0f0000080162601140511580d005040310003858075240c01d100c0440c40c00300301d10700707914100100b01c1407050051601e2201c140740c005020300120300d01004400344c801c803ca0503240140c03048084a504014a40c5c80040c5140e810070000c001200c100040d0686100103040c074440b81718010011410708000282c80748881e90046421104960311001c0c0700d000e4502180207100c0d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 345233884 1250 345232634 345232637
    0xb1f0311010f080f010314150f01090b0d0b040602091203040305030c0606181521010608060a02180f0a03080403050303100e0c03130c0801140603060c09090a090206191d01 75
    0x10b03d4241402d884181040600003e8620340c03005151403c00041000a0b01c1203d144440f0550245005a0b248615090a00070b0001840c141450340301c05107860303a44480c1070742c0c00c907800e079410307403901c0c4e48200c025030080040ea41c00c0b01c03201081104000c014000780c070080d4002d001464ae02d850104c1d038141030140060a1900c1110403203500e000405100840590201a00244604d040c6406001503c3c0d83c06c58020300c42c070015050091450220706400a40444007080701310b90742ca03124024840240e00602c0e101caa40c41014010000c01842d1410b142031000002401541d0700341c1c1c582d11880b2581c1d03c16001a43c0b030764400802e0080300d00306c500d000c07001400182c4103600e84d0308140b000302906d03120207080b0344440e640e654500f805002641c501e0350003c0580000801156240c650301e14030900c1d04403801e5103e409202d00180d000d501c2c2000b00c5645d034800622160702c5035603201e509ea0060450034010f076041001441050246000d06007040c000100d03c0e15080300201e445609002d80640c00b05000c1d0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 345235134 1250 345233884 345233897
    0x3120606040b120a090f1505071b0209060609030a0b0106091203050708072102010b01110d020601120f081201081b0604210c03080a080709030f0b1f0311010f 69
    0xb01005403841a5108000c1040f290102a1100c201c0c04000c1e04401ca0054045030407400907008110072803401200c1c88005945c180965980e4000c1900c140324103500c440c0b01d840c000401c1200601e0000720703030f5501c0440103041a0a0003488070100349000703204207045584908150052144680044502d0010711040141d41d80282441c0c0d001001030203100402420030202080407820065000c0706010341c8501d10991002e8030002600007406807003a0905540801c3d42c59940100c9030303602040300d2401494940052450f640381c06e2503004241c0140c001550301501d51050100081e0f5182d0040c1142001007203151030307650610210908160103c5400441070848603000300c9941c482c00b064034201c910240c070309065903114040d101582441d9a0004100f40003540020081090349000307040300324101d580301c046968601c0c00a8440b864180000303400568581c0c006400100031440b01a488515208605c2a0107101400c01c059400241c00c101c1e80c2024130400070085d540d10124400c911140e518024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 345236384 1250 345235134 345235139
    0xc0c0201230d050a090f03020309010306050f030303070c1b0e0412030903172a0d051311041119090305010e150a0e031c1b1106060904020f10020312060604 68
    0x740e69482440107541d0000d0b100d00000b40c50b015594400d4030041d80155825003500781624000b5241e034080c80c0403c0c04a841c0080c089268241030300700c554134907400f400079480c54807900300c2924140d031405821914000402040d04800706100c0caa5001030422400745234182c1024074102110340e0aa84c48407081600d00400000400d40c41040304030845500b07258a24180c6400b405940100091243c9135041030518410314142d00240d0010070b0a01c01c901c00030007064580707143d40d40c15441040c0c0f0150a500d1447c101c04550300e020b038445400c80c4100c3d07100c1c0b481c0a030500c0c050340901c2000c040820218001e840c041050040a02070ba132108051000a03100c116105060350b010110041c2800e85900d80d9a100c090f08654200708890008516103640340042c4121480da00140112041410b1502c04c05009c0000060064003012440064803018000540e03aa0042c00344011000b030050307130711141c1e82c0081030b55a05c0d0760324200304c240c030740b0750203565a071014120074241402c01034082d078041d01082104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 345237634 1250 345236384 345236447
    0xc0d0c0f030311040906080303010512010e0307062304030201020702041a0a03110a080304080609100b0a0302090618150f0a150f02010f05011502010c02010501050604051306090c0c0201 81
    0x2009581681402c0003e000b660f0b0040d16440c5018035080044002d107021400704d17104200102440c100e903412115a00701403007840000342600d00084080c1d521342d005000d950002280340e0040740040c11010498040d200d040480030000f03000550301079015035400100c0b402941041d01030701e3b00c1c030000702c05404410000d0002140310198113110141c02481d0403803009507a90f440d0388200c4001c020041c2103130380311500d07504003a40380c0205407502891b911811385844104003283c0102c01105c0740c01014040c51038619002d00006100090906a000040e403c0030024021001c7e003243c0110381480c0804070300903400003440040c1c4ca030110f80074818020100304100745820b850078640b41c03011038640b840151000300002d034054154200d46489140c2840c00100e00c00b070045246c900c0408180e40244004102a01d06030b00701c0701d00b030080706d80011040000384070310309080c104c0a0000040c01c40001d4032566491228084460003011680040d40f5114880e00b90341e400241d502c01090041c111180140d02d0105 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 345238884 1250 345237634 345237653
    0x150702061e0106030207080f0d0e061602070b0d1e0b0f04020309030702010c020111061e010b0306130c02071a1315021c1e1101050121080702150f0c0d0c 67
    0x3440f04040c1c0020341c003030400c4020b5042d50a26a0040032607a218000e942407140070b01600c4101d4541c030b20aa0000800a46202c8003052000c0d2042d00600400e03400d203140c0c640103078480e52003048443d481c3c10120340b90040c10222281c645032401800034400011608110440280301130700d41c0f00d9030060040c400038040102c102c50169a09003080c1d00c540c0c5a82c80161108034803c150395160740549820444c1e54141e4110410f03001d52040c40c100203a030788442e00200d15020035110360740c01060014001c03480e808280d1000c250900903004a9030401d035210040800c1c2504200007084001010034501400b020714040d02c400380000e952006120b003a00c5000a56038000c100b031307485d04000b041000c0d02159014031003441c2102064046401107034100003000e401011104509507056207400300000782c6481c02140642c20411400241100a280751580c54241d000301c101a6032080f505040140344410440040075410142c1c101c4584400c0050041424044070803400014000b0b05182500040c92914 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 345240134 1250 345238884 345238889
    0x302030a211d09060d0c06020a021504080c100327060b03030403051f0f050c0304050c0a0b0a050304060f02131403030406210b04050a021b030a0519050903150702061e01 74
    0x150f24140326030782c02c1c0024100140c06840580603c2c2c4011011460b2030b400b0403419900d90003540e101610340c00000f207401c0988950b01c1100d9954110074000c98062400c20660740303004100303140100c0d1180700325800c51400007038207407000c01001441740c090381041031074007910030000701c02c0303001d0350509146440d10f50320b410204d010350000484440e000031040c03483c4e81c000300d05d56545a8041000380780040680c10103900640313059946103d04800d03100103103011550002079502c0e004046041682e03144042d01c0036040a0002c07207104c1d485000da010845010310103081030541c0d241a41a03150b21b00903000d612114000003441c001e030800c0105202c41500500d050a003002089a080003041d107045120004058024002d0b601078200003d1042c1c5082036000b410b028a008075488142201e4003503855030700d224603440b03034001c110180318021404144001e81c105d0f104032400c20318580440c00c40001d0402110304501e8403100c1c004001c1c00500c95040065940c0300498a0042210901c1050b61101307184051 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 345241384 1250 345240134 345240139
    0x21302041e0b2a19030801030b0f07120b010507050d0e090a0e1906151e050109080d030b032b0e1e060f040b04121221090206040302030a211d 62
    0x1910340c1c1c901060100250003540d061402c402100040900d0006c0c4600001c0c4000d40c1d0b40501080800e06102403141d040340544003549400e50403000c5901b582d0042c3c5032200020b81440024080301011401c140701c0780442c00034640e20100d00440000405c00e10080180110390035603e41961541204400030760210745011005d41c5421460080c9405070142c0a4a01c2d10101d1110441000503848883c5401c40982c030030040c02800800d803650011175044100b482440380c548d01004000b00c41c90300a40c0450019200a003c1d03528500f0343c00d60880c1000007548040d80880d507554015031241d40c2c00026440505d0044501e86013200c02c45903a8082140c0300300c21284102400104e4046800d1010100c03401040802c0700d40d5200c96450083c883c00c1c495041c416689211703000211704c11203200d00f02420041c5043c1c050001e88242031014040101a01c0904a82113541040040007680e42003011441051040e80c0303070f840d45007140000144255510b81074105001c1d454100504d0712590f40c0c151654803109 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 345242634 1250 345241384 345241447
    0x801030f0b0a021b0c0103061710020c010b030a050a03030506090105091b0415120e010903170901061a03150f0307090203060f0a060c03020c0603041e021302041e0b 72
    0x1040d0842c1c0082c40b0741c625001036032949244020900e0300c08a45190010b03030903241044007554442030305002440960100c0c180390040c01014540c1525076010307007040300b51540001649904400420f18045007224240c91542c44034140004050707060141b1640000141e60845480d4500030100e4906840902481103242e2400034070410300c02420152802801410b65081c01d540c198080600328010306502019158200450074050100500450482c55070584d00c2d01141d081d130812010741100b001d00030615654031100c00080310700c00b050941c0b81c8425072030740d00c1d95641000e407100384014010344061800b68140d848042c9042c0d03800b1410317201f2111100009696690358000042c1c160320a9108183e001840303070804502c00c3d520021b03108140e032194003100d50b5618003804021041c041120002c104201444c441a00740c1c9040c0100704144d4405420480015001c4540409a070000d410051140300425180b2a901c0004c4c8074100c001c000301402117280180700b80164054a04403030351003150005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 345243884 1250 345242634 345242641
    0xb061e07060b0910060909140105120109062d0501032a0308030106020105010f080f07150215041113020316030b01050c1605011e080604110d0203010815070801030f0b 73
    0xc50300042416140201810901d2411503034001082460780200000a00c1450020521f003606100d24069a4102c10300310324607038688006c000c00c002d00c880c0c3c4030016540304c001032000500c3c280124a4006102221108102d03201041e00c1114004400034141d46801e16004002254003c01b0120143c1d030b0744504989642e00e1b003481001884403541c4010003045c2c000000148095040d0300c00c1e4180c480640840c101240c1c0d40040c075075250790701d02254603e034001c01e108001e018818890f003290f06180740142e0b20b5000c04010f43d04d01c078210071602521841a85250308201d0304c4c2080c003030604100c0300300e800c50450401c404911030301481c000611060550b20305581c1d0300740e0b0246047e42c50a50989084902d89194620800b10707403806485202d01041e40c5620b0f2030914420380141401e50700681d507407100d417940d0307680800000e4610862502514841009010b01c3c070200c5000841c06010b0f420002c0640001103646400950f000408001c10070109200502c0041c0002c0008800240c201c0030032403042d04d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 345245134 1250 345243884 345243893
    0x2a011e0e0f041d030304260f1305060705010905010501050d0305180f0d05010e060f01181e0e010b0307050a05060307032403110a1a040e0a0b060307080a0b061e07 71
    0x758107072040800c62841c1400c3c0100d508000300942c4038178842d509006102400030401c45261104202443c8904414400e407880703455084007174807130406452501c0c7c070015550000b1a54507440310710195a1a5100d00d2604c0c240b013024080c0c140100020b49043c04103101a4400602c80e0044141e20341550302c0d0300005014641d141c025860200c14000c0148001d1350032890b00c01c4c002e0000760301c00e02c00ca014031000501d1003907481410314101ca0000100e070841201c4608400020045599080500f00041c202000e00b04028800c2c83c0141010000000b5007210400c20546480b010358041c1c0e1059003655000d1001d81c4454023941c1d0403070762909011420f04500e05060120f190b402150001e0184250740010901407540b200e0f910b981c10594101c0101078803003840080003940c03071071010703500b0804000070810101e00710304066004005010019901d0307094800641940d000360390302000a4400f1040c0024145207218850b60b0303000c1101d400d40742088880c01c945110b01c80c41050621404041602020301 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 345246384 1250 345245134 345245141
    0x30b0406031703041e1203050703090803070c0309050f030a0210090909080a26011707080307030f02120a080a02090f030a0b090c0604081902032a011e0e0f04 69
    0x4640c449821048045103060840070ba4000711025504800000301424907441480811111103070061841031085540702000c0d00502005400c00e001c055886c803144002c107503504041c41c002e81c42641c911fa01104c0a0400030103001d15500003522459408003000016a800203207040c103594159046100110f022005645031402c582c8038103602d5040488400c10003034240300900a044c0f01d43c480c0168615113603501d811031001036400a00c850410401403080520300c0320040303c2e1a01034811501c40030340700c1060740d055402940d001c50200d402c07038190000113501884407903414034096034040d05144540340c0041c00c24034040d11803c04a0307800510882d054840a00c2c0c0304000b440a0101c6038500f00340e2900c149400790441d00c0075801d006410500d4081d06d4003900721000c942c0c6010041c01c00c1c00c20303a49038040c100c0800d00e0881c0c0c148036000c10280038010300310540040c0744041000110b03400a410000d0601d240e01084090103400440d01c6504407900082d00002004050b909450342030a0b600205005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 345247634 1250 345246384 345246389
    0x306011511030408010b090f0609061c061506030c2309040e0a0308060406140d17071401051e01062c031501091505010206070f050904060308090a0b030c0406030b0406 73
    0xc0b80000070380451a1041500700c003058940981d185407040d9600e80100119210698210b0f5000343d800c2d0200f40755160000041041c018003070031501d602c002c1c59540c0070480748000300d4070840c464400d0040001d1a094440d802d0175a40604208001806914440a03c44014461691581408a1020032944030755101e2410741888008a440c01200c0d82400340c8808000c4a28070700c1342d0f050103008506c920900e40c03400e1004c8030140503261560f00c195244032850715603c541c845c54040c180104030200e154800310004c92081e080000030141040c0078480701c24041304500d060003000303480041162a81c412100002016094030280c0b0040311207001c4018101000502d0b54980300300c0b040b40500440e1440460304842d4401005c00214140c3c60001c1c075000c402e0f01c03695016030480c000180525010710140520710a480c07506500d800e0b8079a0000d03040b64441e4200362810704000c51040058109003880001800c0303400300d0a8154500701c0c0d0240418031490182508251300d03694040c0980d00c4503044a400b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 345248884 1250 345247634 345247667
    0x3020304061508010f0606021606110c0406030b04030212070b0106030e0705060d02130503150f0c12180c030c030712060f0c03150f620c03060115 64
    0x2c6103a58401c00ca001e4403584911411a628007940000c24500000f044041d05189020703080002c1e14110007a18041c00289034080f890042c20101e170400e50710f51041402442c403401e0b80f19414205420000d18081c511a40d04a11440822100021a07864209141181c00c1c5140100700c540856400b6800d000b410b03840b0582241d00070400807070040094000d000c24407208040c15921300daa803000c040d5604042402c0d48945c8880c3c00100301c0300a00104550f81c03020740084050303c2e20040c6030503402204401c6842c4001d6001c0c035649007125050a0050030b00ea004100e004250140300d4400298480f1003912401c9517100c1041c0b07200c400c0000315004041c030000034520410462046400290152a00d012880d030f2680a8440100d00700510345200400d68103c030540715180d004107101607100808071507801746400c804402c0c400c0e01c880801311a0080407104070034840720303141200c000d4220b01e000b12100c502b02d80143d40440c486440004181d41100d001c80300180750101003210030f0303d000b0b140c1010240c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 345250134 1250 345248884 345248921
    0x10308030c030604020c01050c03060415030b16021e0102190309120807020a020d0c0e0c040b0409020703050c0a050c040b03070602061504020903060f06030d05120a0906020c0307061b0905100302030406 88
    0x1649c801c4034009140315031025a03061203640404c0540c0d903040300e42c9000041a06400001040a00c1a21201c020a5401600443d0f80300517002e00c0d000c030304603072401c01100940c0d0001155080c4c01254450b50206650070300f010705c40300046d0342d100c1016040700486a410015000005032160b8420403c0d17440d495001b43c440c0f1480c072120304240541142c28000d4021001da00360100d400d54080004850850754403120007804d01e814181898003035445081c09404010040c0402c3c070000d8010711480902521400080c0003245044081c4030645415254075031207a000b80000300706c05500480c110f03503c00d0b07549039410f00591b40800058000c2c06195032064041c803405081011002c82d412401e17020b90b500701c04a5090541084c0c04980900c941c80303400b08001c07950008911454815008001d50303e104000241c102030401c0104c41c5140c220030001e6410343d489032090400718042984004000700180f52031203034241000301140070307001900008010180d00000140600140e030f03004007220f254290765031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 345251384 1250 345250134 345250141
    0xb15070c0807080624030c09010b090406060906121d0304060206180105011a09010c060c1d150313060905010203070c0201020c01090f0b1b0f0304150305010308030c030604020c0105 79
    0xc0c124a089401606920321600344041004180040d1080c03040d00f0400c0c4003178160888410b800e1451050b0b40b8410f400d4070504516003665070350040101d0180c6000d03418903403540c22440400041d81c0441c0e00403400e0001d400c009000450380901e10900c0d50702108004540c07401c0250350052010b215029181940c0008140812b410303601240003801810141e00fa99140142100c0c1c0500b00c5000780301c0d48001030b540c284e0881c40095000003030300c2048014100502c3c01401a103031202070b91140700d007903000181444006203d000e00002c010350120010303150004607620540ac4030b82c080c800501200f075100b106408410420031241c00618a065200f4025526420f145e540605104101070342203000d4010b07000c0d00b68030380d40300d45032002c1200c0c8003c400e03015040c502550115075520590261040306040301000302c281208200781c400444981c40156511450003004407200c02d9076000c803030100341c1400010008a8101815260854208651282e490701e0b4440050001e203d1103006032840e50804041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 345252634 1250 345251384 345251393
    0x406030c09050a092310090b04140403021e0a0b0703020c03161a0105091501030e0102090316030b1b09011b020d0309030209060103060e0f0405070b222102040b1507 72
    0x1101d00c1c038240440128601c000030300c1068840d04541d61b10090031820800c00400c16580c21800990001810004058058501d5100701072030132202a4050b90000121001c00212510b82e40c40b140c0d1a18044d01c40c0304200c1d6a40302450340007030000001c040e008250310710303071120500880f0b411108003400380203840c50619282c3c4c04180044041221400100000585400d041c2c2130144034400d030282101065043e000150000c2200800c00952903500340300313841083e20f040214501c031140c203034044501c640c61807800d40c0c0700300402400550011600c0f0043c20782100810306580840e142402c04178014042842020003010380328501035448100d11481a050603000b403402c20640f4000e40e0062060754a160054040d10094420015040c2241d0005a4030150000c2025085481030083d6000300703541320400c0e40c040c2c000013041045400c0b800349031202e0056441003140100408000b00004465850011840c401a032101a024a1300c5030040305c5a55200d94600100d4080c000707059442e090203080 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 345253884 1250 345252634 345252641
    0x4030e180a0c0c0302061f1a070b060102032503050d0f020a0e030601080307150e01050702031b060402060a0c03110709150803030622060b031806060f01050406030c09050a09 76
    0x101c22030703440d10700344101c0b0102e40318407008554560160010300c095101c000021001000c40c3c421110555082e076008203c1101c06806401810090001c144e141c002e1400d003503c04c000003503c03c6055500400a03d00012101c034040910380700c0c10030011546440c03906080e01c02c2d2003490445110b803071400b0040c40b01c004c0c60381c2c05840f201340c540d9034070a130241e0313107505042d0307118028001c031105030740180b0032540041c4000313542041e0200b01c2c18011900901603210b8a083d2001580d4410260b040403440702c104841d0030103903100324680c060081c921070600d40c0100c0e05500c1a0f02d490801c1002e1700300c5001c24103026281410705805c400003121503003a62204400001c0041d1072100045454403100014841000016640a803800502c202d0359030650000c514110908900392030070311915008005040c401c04405180316030b07440c4c0821980c07520461031050401d0b20040040344514984044920726903800000c1c0c4080d43c0b03841c1000168050403240903945023903142d001c1640722641e054007040281c40f0340c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 345255134 1250 345253884 345253891
    0x3090d0c03150c0e0f0a09050a060501110a081b0120030a060605120105010507031e0305161115070e090405010e01110c1b0414130c080f0c040504030e18 67
    0x842c00054400081000d0b0303200c0f100761000003100c0c11340007000c03440d00517103258001c40010650700c01c00e070b512040d4009031081124040040b954500b0100402d50300076640215041840c400350900382c015681b2000c450103240c04c00e05207004001c0007195941d00075031040e003500b201040c82403140100140c0340c078801d520464030148028144100080ca0b14003900075242d00f08840d29040d2180c1c5c0c2044011941e54211002c142e003008080303120101c0702501a054079442da8110f60300810517103007000c4004031548010031040100400010f41001b8050007055095515000c8098620652140c800071030b113240c601c00380294002e4401d4240810400305500c202c0745040818001c0c48485090140c4110f64050411002c5003034000300e8802450101004203050070100003880015002d0312480003680803007084520525001000e0044028401c440140600400400000b410f007140a034072426150125400c039940901e031140041030801d402207040000850740942034607060a0758590900e941d1200740d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 345256384 1250 345255134 345255143
    0x210405010b150a0207120807080406090305010624030509031c14060a03150905150412030b0a0b070b0a021b060f0105030607051909030c0603140a0e0a1403090d0c03 72
    0x8010000d00d1540300b800c0e580800b086802a100080c5001088140c09800a60840d010103040260100003110740000d403020345802d50b1000d00700d5040d880c02900316070f00e68000d015200c0c0c10b04400034945502c11803202030601c8514001c11580c8a51000d03d00e14010000c10389004049100308007108000e40d8001d032401182e503190007004d80c503031005104800c151b84c000a882d01500c0001403800c06c865402020310781c7d02c10004c454002920320003149591809a40c22a84000c030301e042c100c801c4d5414000c80c105460701b1103482c11943d00c0c100382308419205140d4001c010f081c080c1c002641298169054812a88070240e407080f0f0800d8440c11380342c944004035000180700308c0790800400e450030000b036010b101301c44648425185c4942400d2504d8080404104541081b500840c044001801d243d080d400915541c1c5001c5081045046824503895009004030601d5107840e2801481c40400074255640d00d0f00f0800f0740c0c0304403800244443c11842a0001ca9400540c800c03099020010190014411640103 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 345257634 1250 345256384 345256399
    0x10204060f0801060c21170c09150702060301060c0309080d211a010c1406041b090209010f0c060b0a060801090c031503030e031014040309050f030c0108060d0b01031104050903041a210405010b 84
    0x25a2b503040981d000744800690051401d00060107030714020702003580001d0103800c29a001e1581d03081114584215694200001200040700c115691340a4450440c1461500818426002881c0203800c0c82003100b011a41004584e003c0041400302c400200c400b0ba50003a01580c4191400382490580307010f04450303801024000e00000200d008543c401d889844105a44041c503070b00d010304040b01e160f000c105003602c5495841243d440240d48454101004060a844000700c030342c541003004045892000b0706201385824016100d031181000f83c80313903045d40c3d454240140c440f03401c0000700703144c0b918580d626040e603450551090102c503440b008044c841c40c030070f5994402154440090102250a000c3c2d516010b0380f04004941d000e41c01790741100d038402d801078240c44010095480345602d02c08280c1c81074074a03230f25003000710b005030405004407540096080002c1d458545002c03008420080155040c4450322004203892404400b00008440d801e403644055007031a04045c1802c0307008140c12022140300c0c020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 345258884 1250 345257634 345257659
    0x5090604021903080d020d020d05040b070801080c0307290403030306140429030f011113050904210504030c080f010c030e120d0b03010204060f0801060c21170c09 71
    0x903030b98452043d240d110a4090618175140c1780b00c0007170340081da241104141c092000c060340042510401e80320301d00641c41d008030b50034060070207020000180c0108005030007000c03440c1c9203610001a184e080361030901c4503080c010b1071007141315401c4560700b2440445e084000703000014507505410400903230300c0b240e4206e03156014070000c0200700c0d01c4201d800da00240c1c0001540c04000321a1090701a103040103000d0f10199913035000c42c103007107414845008001c40408542c1807e00b00554103100003400040d00d05801ca4102511540c28060b941d092028081c2589101c40349a244114240d0300215808804044659107640c11580c444076519282c1c0e555610345140c192086200340103100c02003010780e01908451000030ac10460640c094441c030a00e071500c17401c58035290f1320309100401c0113201541d1f82c452c1004001030f00400f21481070744100100b0990020312808101c030b803081c030035003c0d444040036450380580e0f820035170740700c404c4000c01c4240c0c2c4402070820458000313400040551820490350540300e001c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 345260134 1250 345258884 345258919
    0x3a0608070603050121060b18011806290c121b010c090b09060a180b0702100e10111c020606011215030b04170a1707050a171003060509060402 62
    0x1002e14038042c5e52201401058001b1900950003143c548901030444041e11a0705517101d20025030a0340028020b150080c010101c9a010748200006068011030510203000340c500342a004c0004a200f01d0310002d000106900c15440400185c1d14890034155595190749a000c50b0008600080000f5110383d401c2c0041c5100c941c8c403514400050705c0700072920700d08048000302885440c3c0c208914500c24007241d110040603107a50b070300801d0002d120700c000c62542e5514038030503ca246001a600041070003000101b00400d075030341107010036844041d0302d840c0d411030298030032982c500000304d140c011592140c03046040c880341d4003203940d40c4952801e8a640003004680c8108104856092104125102c28140d081c03000034074032155150007500901c1a117007001c0440a0300501c17030307108a56a4002c10804650400c09180d001100da078404a903050031418140070900140c03144000c000000c0c03000c2030540008421403501c0700c2140155421141c03c10441c034001401d16602e880540d02a031140507020700380715412 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 345261384 1250 345260134 345260159
    0x2e1d01051008011e05060304080a090b07080301090f0b190609060c05060408030a1e062909121606110f01020a050409051b0d09030908033a06080706030501 68
    0x9079402d58410b46103070700e051100c4550405510810688020008000400750b450401a41c06075014422003656052420009081d001083c5e0010822080c2885501d02098070031007070b87d045a00f0418086a2280c010942000901940d0b0480380d0111002e1450010086101e0103041a42d0298894043e0162150f02c20703540980031201c01481c90f8007100004000440c80b00281d40c00c03c51140b0041914007004110300300c14444100120707800e80e0340e44410440001d0500c1c00b0407050b40c1d8050130740300c0964402e4504009110300000745004030700301c44c00b02c10901c070100003142103800050705c50b030000c2d03440320301c02070450107a041c82030f44902c5010032a11080d041842183c500c400750b0348803989010b19140c105401342c14002c2c88103440244603009140c0304461000100b104200e8034500080541061a01604115094019107840d80c000c0c02040811190182d04401849901e5900f5035200c0c40c1d01c2100d0204910030000c5503015003022000194008002440c100391000c3c1e0321709009036a21a12501c405 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 345262634 1250 345261384 345261409
    0x100606110c120d0507020f030717100c0c0f02210106080601090209010816110a0c0e0a0605090a0b12070f0e0a020c0a0f0303020d0c0e040609020903062e1d0105 70
    0x143c00c03086040300d846010b00024102184050940aa4000c0d41740020741402c105910010a480304455003611a07942442503100800c4a21800c00c002c043c1d0300d0006002d504420801041c1840b501e40400c03d42d50b82541407240502022401c3c0c10400c40802401d010700098482c03060300b84104400881c0c503100c0c2c0d009581c0c0b00350060b5521462955243d1407104221200480001402000c13014181074200a210b42c2000754010413884c0d07112803900781c0c03070142081c0c0280a00b5555291540a02c0640ea40c42d9201da0040b035011070126200b05854002240c00c0b2010705031b50110720a218000400b2464114043d04640c10265a48200d9496500a40a91041d01041c410980241100200082c2c0d07200c00f240600e8040c0c54010306140c58112003030125060010024049010224049400c0c03070300e40100341c007402c0d1401c0158108050800800d40d241c00161906070019024007282a403074505950500c0d100000b40402c228a654640c1552440380014001e800403140c001c00100d858102005000030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 345263884 1250 345262634 345262669
    0xe0a140c0d18111917070f0501051306030c0207081606020606150d020304060b18040b09010e070512030f041e0b04140907030b10080105090f06090c0903100606110c 72
    0x2855441c0d00030044401001813032400f4208422101291880c405650b401d04013205a00901225082040d40240317180280e200301d04110f010003c0907886180503144404652440c1000316014080e184140e00700354050b0000e14084c82481c4070380c200c496540031030a04a60454090715141c1e22403c0a10031500d005052400441808000300307108403800e0b6000790350043c021040050030004140005000345810b000b040b82500d4103030305101c14000b81541458100309400000c002c000e0f0810000d40c0c6480082c07150a21070300040b40c40400008091048404514245005c03540d25074840403100300991518600540000741c400000c18201000c0e0201d07010744040341034003000341c21100100803c3d00070061540b0200354a4100c03009098441d040e120b44014420b440d400350541c14102844001000208200400340c8800d0510400361241c19065030801520001195100c81400c0403901c0c000c9161b5803840c41c680340905c002505da600401041e00603014005803411015120100520705410850504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 345265134 1250 345263884 345263903
    0x30405030a0e0406050909030702150a0207050f060702061308010b010e0603010510110106060c02090c030103020108060607081210051018050105091201021b0f060903040e0a140c0d18 80
    0x107249a00507020303802a920010000314074291141c01040300000156500300b2507500200f1440118507084000700b6a0003801150142400c104600007941c40c0030610450b4020550304814064a45420045030b1450343c01502a030740d252140e801c2080242c00c5449500055440e110782100c540d0300c40c24994080110042c0105e0a590826040242d141200d10910f02841814440780502d46c4003806100000c01c4152108180008240148801c4041c0100307854074440f0308200500050b0303003024140e50415416605a52102514500a0705c20312840711101c1442004200700803c450400d02c0d0b2405452047e6495004e01c40300c4101503070000c03040a00741091690904040c0002d520440144c6800300005101c0026030000341c4003242240d03c8a003030f201d80c0481011030207008800401c06443e5000030f000080445151000d41c46407240660301420400f0417458001c956070f90840c0d0401d001b14664988074000e141014095200c06a00503115001c0350303030820b080520030301d003e0700340e103201c41ea080700819 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 345266384 1250 345265134 345265147
    0x1c080106050a2003031518150102160311010e030105070e13091502040611190b0c210423190203070305031201030501060e0c071b05030d05031b03040503 67
    0x207807041d40000d405881004205aa07a103801c900500018191a200b80003440d620700380084e08003241d070000032005001e48842032501c0044012821707030340e90010017412204151010305004034140281d03140030124001c8203103c003106200703480140e5001d6002c00d0303c90650003c101001d00d400d9400c21240000070400b580740754070290526901811851807810800508140700e680c41484003e250030b00d004180380e0104092245a410030115084982408020300c080440d600b44244000038600d4014582c41401002c00c0150b8003001c2030b6452800e00b144100c046074540b50380c43e8070f01201101c080d0360032008070108c100100b0104507029290040c20700580149408103001c051040b0138050100d0301449403074000001303d107052029040c0c00481c82c441030255495400c0449c2903072420b4004112203090001804040203055046403520b41d8499003c0940c00d503002c0107480710034820b60196425000305039441b0380a561010056110f200311a4103002c41c07280071100034005001c1214000c080341e0003000701 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 345267634 1250 345266384 345266387
    0x50615070f080c1203010f06090b0d090f0204090302031806030121020a21050f0c0105070b0a0b0a090f050a0908041a0c0a03171315020903150405030c1c080106 70
    0x2000d82c020001a072400070300003046840c142902010310700150340400140411554001c07124020806498842606400c1507000200ca2050031420350280c1d52310b0704007801b005504034021940c103130001d108120088140c00d0194032584412005a00e040f522190381d0101c0c50302e00160703410b031190200e0b1102500340034400c003803c081141d0800d90703200840010000d21a0b034500c59038840c036810581c844842d0030f61444c02c1881d0401407040d030308903500074540841850360b00005440b400e90300042d000459482d004c0701180248038032544a0703009100c110000c1000c8400b82c01c1301c0440341c0d140c1403c114035502c0c00110320031a6107040d0003d000301010031003048581d0f0903c8458881e061009a51407500c0000305a907031411444000072004516a0309030008000c1d20b01440c1684040105114400d228890b6256541c00f2001584042c041e0360200d00e2541c251001c000c9010610400005e942c2d842c08c2134280f003542e0b42c0169050784c5440c0715058200040c0b8440c00032034110914036460b61507059090600 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 345268884 1250 345267634 345267653
    0xb06210714030c12160803040b030708042316050a0e06040221070806010f02010209030c210a0f0b1303050306040b04090203100c140f0904090309030804090c020105061507 75
    0x1200342d1510070082e00fa0036903503440d18940030f000c1e0228002d0440c900340d03404100703403100280e01040d040d81080c4010004a0214011a90310149507d0809160b42c1c0c1c525000c1c1c120003400a1400c90a16213070600d03060403d0000d0004009800c002c4c00c000320f145c1c1e40c020448450300c180680890224401e0200f01c481c00d15401401c100440141000100c29041580d4282060700700ea450b000102130000f0700840c1d581081034606101003520003945081180320201e40c3c3d4050b1500454041d140e02082d4800f26800401406441514802940d283c1000f80c20700b03500700c040000f01540c8202c44e402c0869480f4800b04c11203120f0700d600d501c030241155501020080180301c03442c1c0b425003007625100f150780160703002d00034051009410000000c07108100f10004204d0030105200c8480103104100c0840b440702c100e03040d02d40346081210301243ca45039500d421a500c46a03070340004c0807001c000ca008200c0780ca40740c21040c0201040d600800159035014200070400d0603814104c16801010003000b40450380014 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 345270134 1250 345268884 345268919
    0x519150e1f0521030711130203011202280b1801030603050601030b0c09090c03090d0311070f111207060311040b09102a02031507050301060813050304030b062107 71
    0xc000002802d21040c3d1181150b101680490300701105101710713181841c000300300a41c007a4500c00704600790f40c1080b0f400540b01c80c0008010703100c0d241402240c181a0300000301c4094031901c40600e811410b5a0780281c0b2402e800911502c0d01081030004100c80c2540709119510449070088000e104992941d19084074240d0064044860301008100d20780054685c4001d0354003503824074030255a240340442010307081041c41030b4201c2c101070030420841503040e4004281c41d010794001034131a41740540361520021044206104640055034428410018240403175040e003240c40b45c1c0c83c180000100410150198480c900644141e2074040c8100100d90514464074104110981088040110014181b038080e490309060024007004015039130046003001d211409051460047c1c4101504280c00040c10034081405a00c0402c4102000188a4024280a01c04490300541070382da50350b8403410045030204080741d002d4001c0d003081c0a002c900c410003d2030340b0341d402100c6024156243c00e00b080903800200c040c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 345271384 1250 345270134 345270169
    0x6070b151f081e18152805040302030301140616081b0105280209090103060b12010506091f03080d051006050703090501080c070b0f0402030c011b060519150e1f05 71
    0x8910703451482190005c07141c0114000e070100c2c1103a40307403450311140b840030741030b90300070014200028080001e40020659054540440452500ba2000700105a090048940c81c8170031b03490340d201d484140f00300710703006000703581c4009209115408160042c2d8261402903c4110300b00c0d800c1100e609014404e034051045000343c103180540744c4410140040e049075003e0300165015540c03011809c00e0380c981009201d00d1180000002e0000349090400621082001080e0b9030f03a82c1c1210690f9840091039203240400f4582c801500380e101d40310100c245004040071200301c84443c07020100861058014810380341080d50540d80e04022a0030702004403800c0c4405042c4ca07000702c01c1402440006200d45284900c10114007030f034500359140c6801010304d030107001e402250501010100300c00141c1e901608441000b90070440100705a00d4200c0d20080c032010364040501440d24103030f2908064416441c1150480301f00c000301282940310900d01d0540e080e0507401410820103812002c00940c181084035040350401b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 345272634 1250 345271384 345271393
    0x40e2203021c110d0e0f010e0616060212010324091e26070507060c020117070c0b040501020306040c02060601020304090e030f07030503010e1506070b151f081e18 71
    0x91410289801d8101d210706010445d8162400d0482c100700d01c9244024100746032640d200d00c2618046000b6119000c4559481160328a804060040e6901101c810004079015204150307564203111101030f50480e0301980d80785c510b00701410304a280e8000c800906800a0100d407108520302d031070005511860008403206010a02d0342890144603280e00d460300032202c21510341c0c0782c0f00d83c41c0650500d921900b181e400d20203101082c6015036441440000e241c00080c1007051a038903400411b0f14a02112f5400520a140c0c41080000300b01c0d064028500440003580e05010314104ad56040e40c80b0102100c80c0c0e8016441800200080a01500110000c000302803d803442d1040e0f403500780c41580d00c041d0080e4041103000004010120400d1303241d03580852880e1005030408101e8000030303160700c80d941300540744504100205d0581d2407214400e441c1c1090091042e01125040c80e038106012043d600d84001260702080000c4ca01c0442c04841500703005d030310f986256140d41e034860f0382140ba0005602800c080c0709 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 345273884 1250 345272634 345272657
    0x1b030a0f06060e0108091606231c050a0b09150a080f070305071505160318080105070f0302070b01030f1505150928021b03040e2203021c 60
    0x14940700d50800b40c410395503050040e6210000140030380743c01801142c9940c4c0800100e41c91301500580c00002c1d282d4030b02d00600f4003c030400b11082c101901503402c500d8040300158040004002c024042c054405003e8107014681d40d5603c04000c54000c0c48450f6000820000014024205102c01a0340403900a19540a140d110100309140580c0c42260001c113910100040c41844410410400140342c658000c0710030322a0f80c1c000a01764090000c1c050003605000302000300b0580520204500c002c10703c0340c800300c2e09550303640aa019110944440002c21014002d4268042c86402218055074000a02450316441d507514901412640d55094a072041907904d04030010f2132601540d80a81c1100303e5102e00e0301a45020400c4000740070300340701c0c0c644076a101c0c5140d0321418008a40e010074040d2800684484e605120009100b940341c80400d07244c0000100422031580754940c903802204108844c03e01501ea8498a94440703108010140c00b5030f100c80070702d140500d42c4c444161640052490b01c0400d070304 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 345275134 1250 345273884 345273911
    0xa0603060f230405030d020a030e060a2405240f0c03041a0412030f0909060f03051005061509041404060c2d2604030503010e010e1b030a 60
    0xd55a0718428001030301c40b10210601142c40b5100071002052031940e500904266484030f68a1055507080c180b1140c020411049150103070780100c407180c0e004016101e242c6481e8192500400c41c40404c1d0f0303145101c00c0366003545182051446015510003401030f01c840e000804001c85d501600741c140c9080003004100484132100f0800162a41c191190011500c079030604a0303440100352003000c4000d03e204180b008106224041c5040481d590301400c7c040141e8561840480e01040d0075005003001600341a80024203101742c1889504882c024000c1e00c00250002140c04142d07101560895072054000c441e800421550900414110b40e004000090f8005032401c4007400078411038043e14010340d00d02d41c4c3c0356565000482c1003914100c095044889040b5100002c42c0090790341e29000412122500d113101c16501d00596511500514543d034080786050316000b08503034000d000d10419000003a00019142e040f840c80d56006107a8160402c81249403c034164543d60801080304154a4840b1303002d245c0c01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 345276384 1250 345275134 345275141
    0x91516031b050706051201090b0907030b0a0515041a0414101b08091809071502160806070f090e060d0201051b010c170f0708090709020309281a0a060306 67
    0x3d125030788030186c46205520b014686008160f004803040750400340c80e0203007581c51201980c0d021100341000070744d44c0d65003c040740014907190801904502d40c0682c8048090055015004544100001060140c11180302104a00540c8112180c003100d140c0860040d103448150040b440c10249403181c1c103a80f13451010300c1c01c150749007400e0300d510900107440681d40c00c1c45141d4a52403040c103007200300c0909052131003e613150344034400d000142c2181d0300768075403080c802c0c40542142103500c6600031045440b5401c2544030b03c0700751001008100f0303a0040400141c010b41482e0300700c8809100d0f10171969107050a00c541001e400c4012410094108441021501c07000c0000b03c9502c1000d00000328191034a401511000e4003802c8809030011003c100082800401026648051103107050039490b01c8009210380f8000c0715030030400030300740040100700301c40c04002070700841c60101c5076001c2c00d4500d18008490800100c2d1402401c40d00e0582c1d100881071100746200d40c2c02c4015400c0000311590369840e410200c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 345277634 1250 345276384 345276389
    0x1e1e0e0c090405100f09150b13051012060605211b1201022113020a120f1a040b1308030604090309050d0b01180605010f030b030703060e03091516031b0507 68
    0x140756541d00f5106c14030000c0e0441004901020708200b150b60b550310b00058030303081d071884803240f015100d00000d414821140c440c2001803d40038100c0106400a19180c40500018028140a44181c141403200248aa56103a01c00c502c40c5c1d001e815200780c0034180e91030b02158000d17095044031180a400c1c0070498240700a143e2034003003a400c21110000d040003a1031038500a4024400450603640315809692210415170450790b01c504822110744603071070680d50364103c1c0c1c03002410a01c03144144804194a5150181c07045202d0340200006a403880600c0d071445c08110bc019081d05014000140709041c2980104c22140c00b030305004001650741c0f00041c086e030f85c1044046030031515601c010010a011801030043c0c0c101901001c1c00f202e4101000209900c101895000802d074031400b80c0404c41c2c8003480150007854202c4d02c00d000c50300749411030640c3c0e94005ca5a00b406900c8003140a400366401c0300030f5400c02030884109844c00e5a030790710100c1e0000c0b40f60500c0004205040d84a000054080065800 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 345278884 1250 345277634 345277661
    0x3140705101b0209160806030c2b02040612030e010f0905010c0f0b0108010f0b0a05030c010f0c020619081f1703040b0406020703020a08060702030d020d1e1e0e0c09040510 75
    0x100581c080710003000100040d007407602130f274040810b88000796103403030104861001d60700300013407045c101c10102020005004c50180d04246000004600740242c0100b10810500907260406a0441c0c1c100465159008800e00b00010705940000d102c00d601c103005181d490f0b0702865024855000e0754032000703518402a4480005607541c0c5c407035840080c8450142c18420f540413901307400c20f90f15043c040798550b0a1860003504009400404411041c054400d003480d8540242c103450700e80c04203a0000d10b500c50300800b44400310305584001601c0d030b04507004422954075007140100c0e0107031030314018401c8014080e00704412070009100c08519501008043d000070810b0b42c0c020842c80380785005002400407250444000c5411080400c10099000011224015135520006a403103011400325001011040b035029610141601000c502200b0350b0005c02158450784000305699207848001c10031a052410140c0058101071030300da0a0f440c10180d11030b8014041d000f910b080010502c1b6040481e20305402c200c2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 345280134 1250 345278884 345278911
    0x702030a050304150f240b040e010e0c0c010f020405131e020a05091305060a0506040e010501051303150506120a020904080706060509040302100c05040819020402130f03140705101b0209 81
    0x1010910388140e80002402116400c80c901270401c41c0480c5459014029088070036502800300d6900450300b8101c40544d4031141c020030804080541c00340180d4403d00ca100d205d1074186480801c0d91055100e4a240c0c001141004091420040f040801a410480564080c031005210111654507410700002024034100d0b80000d1364a409010440d000e816900007a009a01c1448240329604103545501d054030824249a600d0791454030115130b0000b01a00000d142d0107081c02c085d00600440d0304914050001100d240c0011461312450b070784d44115070000654080b0300880460042280c17800200802c50258401080e406d4a64022440302c0d441030700e048005070300c00e05070b4031000c2c19984a05074424078640b904a2a181c9490039481d42d40114008400c2000c01d0782c6202000c56640b40d045444c03100784075081c106040d681d2640c0d2048450385100039200c4074221070080c2282c00021400800360782d40209201d44070100190121480c1da940035080380503040e28980360000d0783c2e1707400d500ca100348903520350031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 345281384 1250 345280134 345280181
    0x1021212010f0b07020d060b03030904020f090102010c030c0e010305061906020a120f0807051b010608071721030c04050a0905040203010e160603020c150c120702030a050304150f 78
    0x31007008509038084520f0b24024046140142c0d5018050390003150000004503044120000080c11803140c0c1109560140c40000e41000244000000d8400070800760001c00c20b000c410b01041d4243c8141c50700d80d00004691400c02e2500b580680d2110350000d1014050002440405001c281c0104441e088a409039102c0c22025003081807004049072512013614104540004500010f0140000900303440f0600802041c4040441205038068440b00b00b014000e100301e030b503a9002d0b40e48801c034501481c80c00d1200750100d0410b101d00010741481101d156414140420703030f002008001c07500003500d404001c0b44104000074059444800c8480541107411000800f4181441014211003c0d11000c1c011074211f80410200014041200001c45009003005a0307115a04041d250414030501482602c0e42c0b050400e014024012001829846403548150016902c4941c0c00780d075a806a09003800014008000150026040c081b4a00089000f800301140700c4810fa015a81a141c1b80140d0113a4100e038032080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 345282634 1250 345281384 345281399
    0xe0114041b050603060907020307020a0e370513050102270405040308150a1e03062306041d01092f0f040e0f0a061506090b16020102121201 61
    0x4a1100d0307003101d145a0780c103407416001c2125400001d150b581709180900c00103596500a00c04c039112654010440014262139065140006c102a26412880a0350b02d031402c00c08840c40440780c042288200c400604c0300503034038016029080c000d140130080074500e0241c90004809001604d1400c0404240540410801000c0b01c0c00c40141e900b2684680d0408080c0b00200e0f0700312091030f4222403107141d840d0fa07044d0180702281810001c0d40c0001048520015040f10b890800d1040d40c080d2445608c080c05652a10007035100c10012441c030240e041e60000000c620a803800d6800a8901080b50619140c040d60403840d075400c4602c010400d071031155480e20481c40d401d444030f00c0c41c0b44d280303490000d0329107040703041c2c0104091010b18030416001c1e80c0c0d44c113107820569004122800c1d210308084129861460140b40460290134081d03005040c0000890b8040b4011707004584444c152076040e1001e9003003016002c21481d00d00f464141c02d030706601810303036401c0c240c9606800605403480e00004040071945000f05 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 345283884 1250 345282634 345282653
    0x63522060b100c1a1f060e030c181f0e01120c080601080d0c0f060504290f060907120507090e010803130510120911121f0f0e011404 58
    0x41c42c0d07080028501e070400c00109a00c3c940c1880040368080b140c0c441d9501e0140780c0703001c40d420307144070b00c0482a00400102d06d5031003543c841c00d5034802d800382c400c0c1d00c0356202802003000720008a40340150070500020b030710b8015030394044140310b014004410042c0d0f9900c08881c01030f1080e00407031070403010304034420140541e08500b480240002401002c940d85000003241c3c5641d0160410f40c10410150603034814011884500641c55030880c0080000d0705052070035840304092105c0903c0c0c0a1000040c051002158800d01c40c81582d02c003071403901654500b4100410042c00078a00c40c28441c2d031900c1d00b400c03089584590b520610064941c50394031400c191104d0030b0358105a101c0c03e0960300c02c000c07000c071301206444a401229030035540c1c0ca200c406401e205a6001c654200b508489a1a01e645c002c203208074296400c4080c1425a00500310903074404503903440750100383c4e601e20b00e007007041c006000341056680411380b8841040400031b08444c00c00602270079104500c0c0c0e040320140c1c0310401c0c8424482c0391803 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 345285134 1250 345283884 345283909
    0xf070c060e0315130c0b0a0f090b0c06010501030e0a05060c0903010608070503031603090801050c0315060a14210a0e070b0406140304020a030f0c063522060b 69
    0x40040005044009100301d00b01c0000b0b00f5950080c400c6001801017000c02014540a42084c160780b1303446035a0045c3c0203119820001e00b607000903050710000108410900200d81c03d0aa060024003081da007468015405801c5110034490303035200740c850040200302c0c240411401101c4420741e05981e000d800d01051f0965a240e044490a50003060741000150303000800c4514941b00a86c40c4402440c6a040c00e86003a8010340c0581095400e000402101c4441100214403581e4003101c0081ea0944180070701c019401174480c03030004984802c04500807003190130003a0841c080241c2c440c0d4000d03140703800c182d0311710403055034020015910b810032188545801d04c0080b020713160000207a4102032500340c0080039414400305200c0d20f0070002021805546070456164003642d0000c01c00c0990307020320319042d440c54880d441607100065540c4100d010307040ca20381010007241e580500c5061120148601c003440a2005031030403040d403c20602d1090003c4040d1000b0300414000c8030005011401c0030b05102e42e0b440c030403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 345286384 1250 345285134 345285139
    0x717031311010f020a0f03090e0a02040503070603020711041e0e0604020a17100e12070503090114031b0c0703120807020f060609160228050c0a05060702060d020f070c060e 75
    0x395410f5042a60015009914030b4008080c410000705908058405040c503800c80b203000310b00710741005424201e079001042140c0c0d064044a00f0a540e40701d049081f4040c0c428002e010301c0110091207514641908502c220040b1900414012420980f801e8222490030310694030300e81040042200f54038011550340000c20840c684401100d1040b5500d649410203400f060354015610785a41100b1801000b0300a052400004810b40d150040d0a0081c0e5030b4011401142c0010700c0340390b5402e54066040e0a6a001d08103000a0040d41100d07000f07600d07620381000c0610100c03803203075034800004156202480c090444981d00e03904001c1c200300c0802802c0405c0d4050b0480598090814040d0684840011651156070014139007611018080304905004d40e481c150f6207030710f076540c03905045004842c41c114041e5210301c0441314012202d5050046100580c4525540040280800b40150820700010312595201000c01494200c9a1513240300c0358006075400d4550b0b1849240c20b1007a03540010340c00020b0b4004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 345287634 1250 345286384 345286397
    0xe071d0108070e0c0307050c070b040306150501051b0102090a06110d022407020a0b0109020408150105030a021002031b1005130f0219081e0601060c1205071703131101 73
    0x30030f01c1d1402c038414040c2010b60040e00010020341013034813400945025400010030b0700c1e80940d40d41e0100c21b079508035010943d0f950f458446103491551001c8030303801c200c51040e1100750400d1141c40d003004030b00140d808429140d5400700104030f2507954030681c410140c040e03074807002d0b0b540700004012880c0c41c03481c804da181594030100341200c3c040190f480d0a00e034510f104285240641e00c0040483c09c0440b0750134014250b0902c400081344003911034015006a41401003111042001d5024600b4420400e1040700d4058000744140409030030001640d22165029004480c90240c2000e040e504000b48124000f143e500912036612444486000700c0341c1042520b841651121040e842e40c17040d020408500900c611001c0d982e41504210b8141c2600042c50703c03c0545529001441901d4100c0c01006c4240410b80918000444c0c5140915240010903400070550300b04d07045020001d813181d90100e03400740e44402900500b000140c0415004ad48203043e070503c0308001902620780003d214418448450500c80c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 345288884 1250 345287634 345287639
    0x80303010e0604050c0408030315012709050a021315030c030b28050d0b09060105120a06050a0f0e03070203060c1c0b1f090e01090501030b06040c030e071d010807 71
    0x8400c0810b80020b0122000102d40d202ca00b40d0f001035103d207074000011400044100309a9020010302892034030400e80324682c000740e1004209001c140500c08886200030024018014607100b5030005a1080c80248010302d80283c1c950072001808150b0b1100b0703540e40800142e000c14647c9801280c000b0096070900703008a140c3c40000903c0f0110151100d43d8001e81148402c580251500c808401040c000d414800c202407a400c003292041002c98144903548500b100000d8582054038582c41200b0920001d080150850b55a40000d00030207450741d142d042d00c4041c1c0c3d410002c50b5110f0600c25200d4040151f80d561600d1043c1410700c04014090b1030701140c1840a2140058011820710711048201c2c0300050940e8424001883c0341000d1540c40c010580b04005003000035044090001555186c0b40081101d80ea030f08065400e036102400001c0000c1180000728825007065084a89800c0850030003060b800300e1220361a1034000345a0028032140010020302e040700c0040c503540ba01402a260280191b0750 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 345290134 1250 345288884 345288899
    0x905010605030412030f051302191208160203030a0801060f030603030f03090305070c14091b07060e0309090c090a050303040b0405060a120501180f0b091b250c08030301 74
    0x1000a04510721019900c844c0a00c40e5100c241440c1c6400410001703820030354003051784844050012401801d03160b400d405c1a03c10200c3d4501100da000344519500038031996891030390b4104290b0000442c8018028000580c0c0500146ca04101c4a035914809503260000c01482003400d201083c0515140c00300a2003c241d0041014a004085080200b1840850303d001c5070f452203081300250030700c003100502261038104c020544040d0321040703a50000c551074401c00c846100701950341070b0002290400010700040d240c0c0c1c0119440614a6060301d080c02c3c2d140700881c94400742140d02d10741d00c4c1c000140306100c9241501c88030015010540055003403d0403d02100da0340d10031806058440d071000300d0b500d030310300c0d1080701c444d0f4500c0c43c485020b11095a480103204818861001e144280c0c40c00c095244003511210b00c0b43e070001a00c02456480d0300d0b262014074003120640c00c04420946801041020036641940a44958846443d0000304000e041414410030300c5165400549064108000400240 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 345291384 1250 345290134 345290137
    0x30d090b0609064207030f0912020d0c1502100c02031e030621010504030e04110714100e06040b060a030302100b0d06050103060b04061406040e040620130905010605 72
    0x1002d40c1d0403002d00044010000364040c00207a074507204e003d4440c0907210005038952018080c510300c02c0c2c407040070a11010340c060390514503d010311b89403a0f90b21140132000d0b217002e451101101c0d019664500c0380c00c2d02d03003104070705483d6000e9201000d80d120064000406900344200c04520386584040c500f80806500292a28251030849a03140304020020848603130b0b03107044801d0402604001404d8203805c0c050300134043c0108440175004240c20724004911403d01d801840075040c0d41d0701409250035915503c480006100401600e02c03841802902d00d0020b000348100e01001c80203e000300290f24040c0790180d156903004111038010385522608100194002178040051104600b001c112158441c000c00c2d0a08250300b80a80340302c3c14240000103002440d0300803c208402a1028066907881d8101a80300c10006000c441e001041000f08106c4809440c400c03980191081e007000c0f03900740c070424190060340a0840324201d00c0000140c511031810200714a00300810320544188065854250b018006c0e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 345292634 1250 345291384 345291409
    0x506070e100c11121c020a020a1502100509070512191e020a03060c0e1912030e10090e090703050c13140a02031b03060d0204020912030d090b060906 65
    0x74400da4030780038800c10003851803400c080300003d400340a00c9004c02083c560b43c1c07102014103130710035024142110540c0384040750b4000201d03005002c50703c2c4503240c9144183d0240b4104800380841c090101c075144141e040b8040e0358007407000400180000c0b410715041040d13107482c00c00448100c3e800314001000c4a140da0f07404102c0c0e15003058103800401914000c0ea043c200f68090000d51120180c80b0100030400560320000400c180d80d0b880c0d801102000c01401045030f0b000a0308a05200294420440314044000746000c0c50301c249841da44106003800131a81e5161843c81280101c5c190300014001d8041840d44070381c0c00035880008001e07070307450760325a1502c421984131207902413003000c0d1501c443c2403119002990340481a05010b4030614000304650000d41007a40c0b01c0c1c0c4241214020365014180400070f403409264018103210000c40c0c01d5003008000d50185200c1d030f4000e46060301649104409102514601c40c0c4103101140c00801031400d41c00010f0000c5c019481090359000303000c0161205801e0220 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 345293884 1250 345292634 345292637
    0x10306050a0519030615060f05130e10050307030b09060606030c0f03061c050f070909170d1506050703030b100804030e010e0a120605070203040806040f0c050411070506070e10 77
    0x2214203004402c0e14400001e40c0014040c5c40c284a40e031100300c02c100c442c00084800325a110905d8680c0300200f181c4c43d2142e801d4002d040f50105009001d058210268280c00150703903604074112a0351100841d0410015600a550800800d402c1105841050150716440001214160310f5841e14060004c202d0240c80000c2050480200015000361148910a01401048041e051002d101440d000c3d6561740c140d41c02c1d01c200c0c001d600d80010f00d9020344c0907002031294800003850901414014442c0c15402120310851102d89441800000b10120b04200002c2c01455848542e2030503281404cc4c213945001010340d0165a550401d05a559404003445070410b03414584016800e80600c0100c8081011400c10f40d84031080350000504084901c80251000384241d9052020303641d44c82080e61640030301d00c01c2422542290f00004c000603198415441641d1281c440191443e85690208044803903540341270007000030015120f010320008225440c4d00007001d1400d04e88010a0b100411005e4110105138070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 345295134 1250 345293884 345293899
    0x121d060a0c2c1306090b0f03031c1a1f020105100b0a0309230307050c0f010e090907180207022d1c0b09060402010801060e09042904030e030c010306050a05 68
    0x842d50354615030003000c0c0b89000b106004d01604c542d004070040100c0109103103d03501031007410005003000300980b034050b52142c0400e40600307a500d010030040c2c503810503514421500b03800b054006544a10141c0400c1c0040540e003035000c20704c43c0700070b401c42e413001e4141046d204045000300070101e032803c22111641918a0003041030f650b64a4039140d15501004050301c01c0c002e028151220400000142c00318078007800c100d81c0090349090500520425062245001411000e2141c41a0622160341074212208904079043c280c1d0b2260492410b4090a02d4072028540008011013035143c0154806420050181680105580003501100c0070303101c16407160040700000040000b01c1400d80745204040d40180b14005603241c800080d40e00e40c003003241c080740803408010001c00c0407131255921600c81000580028003d4803562900a681c0c00035100b030740f00c94a144a1005100c0b014002c1303190103140302c0d40707074080d40550f00c20405041480c110103440c1014501034042040e40c2d60384c03404008540b810344400303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 345296384 1250 345295134 345295217
    0xb07060b01050c1515060c0a030e06120703140718050f03010b120c0a1d010603050c07120804030807030b03060606090a1e1509060f121d060a0c 63
    0x180d07094014a0452030603030281071030255080041c00c190500c00ca0414901420305c014a5040040303d010310902103000383e000c003142500080c0a000e507402c5100380100514103154825a400c0140301046036039900007038840c0c0900c0c641002041407250881c259041c0440c0e10045408248000c10321403288a12031040000f200e489500c007948501c80340b902c05403010741c0030b1000b08129580c03181482e04090062150101c000798040304172a40711101042c210700111640d1826100302e000e003030003900030303c002e240c10484c400000d0903c1c180507030103885584901d05589400d06000e04100c00061050044c0360801c201d0304442c3e600407529690151003280c030a9100c4000308046120640c1c10303040264030a819002140b145161241d0110072240c80354000684051400300c103c40c0c0c1892442a907011030021801000c2050140c4003496016000074000900d2030100c810340310180c0d0700d44030040195046030050000030040e9004411a02109041541c007075068a0811a03058200030294040340343c0c01c0c00c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 345297634 1250 345296384 345296387
    0xb010905060406031401060f020a0f0c180b04050a0203060a06050d0e0d050c0706180905060d0b150a080a020315040302010b0a0f080d090320060c060c03040c0b040b07060b01 76
    0x80402a010103000961a9502c0701806001080314400c003080d102e00d0b000001481c1d502c0340c440c40f80015000d5019001503100c640c2d032200c290381e030010102c6a0340d03c604004650904100b0700d0501000c03a180300481c2d03050552090004468020300101c0c800c0c2e00410070401192a0843c894084591a01d45199600ca804030072030300402c0402c0e04070310a805001f011494090344000030b00400c1c00304006440645544010030b481c4c400100d03003104560011420304025140107544115884035018000b8240801542da420482c224215402240020f071704e02200d4043c104600000c2c0a8250a0014400803000f0b40000340da0340344500c1252001700d21000050308143c0700790408100a2006044940c481d0780710300f02c00442070414020450244114020110201e00c24a840000c5903005034122100c000c0d400840000c001e9025040c540041082080c11401001000101c2c031905520301c070f5035242c1c103103031504800040f034607171080c10900010303c018400c11840c0c0c0d04940388031b54020700c0000c00c23000c0d00f0300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 345298884 1250 345297634 345297647
    0x9080915090405010609050102160806190b12070603150e010e0711010606050d0e011404030f170a051506120a0203131a0702010501060c03050f0c01110711030706030b010804060b01 79
    0x10010740043c145000010326035049840007066071400d0702515242482d1030181c10340c00c0014850202c0760350103240814001403520458010030b40700e5000c04220083c148001c20782c020b400324102111940018001c200ca664035214000c5906851480b03851180d20380180d80f0380183c0306010b00000d0025070702c044ac101c94080c445528070560480c000388007840d0340d11005040c507001011809603050600c221080c042c8018440e02c1890691042680c80325251910200c584d29003240e810001d115208041c2e1140303442d0469200e124204a55001c1818074004541001000942c1d50303442c0141b10074031122111103810740109034001401000142c07203a0350111145114541014041c3c0440c403140b0701c48000316141003e083c8601040d400a00076a66145003c58840b1aa4080900010418007440f101900e40c80003e081c40e1010100125404880410001e25540114400c56420441c04510b10090409011200040c9410708003041404100300021f049400010802410180d48900e02d24007603010f0709 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 345300134 1250 345298884 345298897
    0xd08100308070b2a090f0a060c030c0203011d100614101412040318081c0302030c0904020c151b0f0c071e0602010605030a23031c05040605060409080915 67
    0x1135601c00c10314185101c11310391002c0e000038040d44d00004204081e003000d40c10b000840e00d40c1e50343c50f40019055102102e02c140c040350226419502d07560025400b00300d4070582c904090072040545945141d00d501d180c110f800c240c0c0141410101c41f040c2411690350300481c1782c4190329034108405c2140c1c680318046840d04c52400c80e41140780c23203d0180410705601080041c0140c0c1078403c3c6000c1e0645517144a55901c02c41c00034a00c0e050740d4028080d060500c00c0c0c010719000461500c0103801e000c030041c0018141d13041a03400050f964452450304030f40c0715401c40e50070740090b43c408034810b00e000c0044201c00075110708204198a0a800211642c85181c10003e800082224003079a21880780001c4032590308059900c2003900540c00c01c80c2c04070b01440c010400d419200d9002d410382c5180724041c402540310300284890081c082c0401d01500350300003488454103100080b60b410008082c41c0c5803420310112180a031115010350f00d03182c002800604807400700c2e202ca00041319890b2616440c0318030051a4070896 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 345301384 1250 345300134 345300181
    0x317100b0307091d0405070b0d020d0e0303040b010e1504020a0509090403050408070e0609060d020111030304051006060c051f06030609060b0a06020d0f0c030504170d08100308070b 79
    0x300280e6a43c06000d00080c0c0389400380880840140d030480c407280705010303103024090740c1060754108031311070100740100103401140202604155611070500e04031140c00c0d141e2619504004104403c003c2d03001c401c0741c050310710341c000800035081400c42107901c40c10604c622405950300150f0160840d00910964918140041c00001c1a01c1c052800400940207882404a148107199003c54030f0328a94138154864000901094800e81c0e8820030801080e0755150168180310010091001c41e00040c4000c6200d2406600180181015040348504540890b4040020011812842c07400902d0124150040b141d4003ca20091205a002c006000380041d510007015030340b5007100300d0100511508030000303560342201d0b00c00c2900e0b5154400c0c2d0312803070366018030b6001a219004080c902c0d80121000328101f40a4608241841c0d100c0700d071514407042c001c1aa00c543d038807060f84024070642c050905640000356042940b034403403843c2c0d40d20703120f805100343c01031002500720300090402c04804006031200c0c0c0398 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 345302634 1250 345301384 345301387
    0x1080402120d1e23030a15030302031801170f07110f0f010f11120903070822061b080c0a1a07031a0904020402090f0604300317100b 58
    0x11580b000d07082000055210800300341c210380b0529a10700030303038200381c2c4604105a0b0000d043c00340d440d1002950b000501260340306541e00040080c10050b801c81201652003078004580e51140c05001d891244000188141000b91225441003840155885160800070b548403182981e00c2c2c00800b95120448603400c5050f5208001c00324804480000e04440200300140082000074a20803455040c0d9100140700c3c03144020400c02500160300d01102258881c40510607a424425a6030f03c90741c0a9200e88807030811100a24145110941054200c6000341030a0814215808003820440e02d0841c807900e0240104601042c2482ca0307180a0041e1018198094484011401c2400054515004c2a00e4800020b4076150103203000a000245150701c024000b41f1402043d43c89500b040069442040c0241e00603100a282c0c0001c2e0712200b010b0301c06030400c004d00c0c0c07600100070100d42022124042c0c82d44404176005030340501007078020340c202011007440c0c4000a015962110409041042c65010080c2042d0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 345303884 1250 345302634 345302653
    0x10090608041a2d01080619060819020f01020c090627070203070b0108121c0f11041a0315120703120e2806180e010e01030215070507050108040212 64
    0x10907032440d45003540050002211a00303007640c600040f1000740074100032503018201040301d801004000300700300d03d0300307a10125195886801403803c019800e403140007962507406401c81180f410030010380d0482d000303100a040806c1c07007800240136401c0c06005540110124880b240ca00c10355074061401c43c6560108802c140d00b02090300039682ea01800040c0e030442803032070010a00308400301d00320444110700341125041404030740080a001ea6540480c01e4907070782d00da03d020003044441c006c0308a40f0383d0203109180c0321442c1800d8003400505400010030204070030400c05c80404040e0000100c03000c8140c0e846d2a0f000c80240207285009041c2c1c00251100c10a0035206554950290402500e00425500e01c2002d218405030710010540e40184000716807a404400d01c5410700c192002020400350b20311540e2581d5481e104542551800c0c0c000c2414400444010b10039414011201075010000f00d518518094042c1c55142c0c59a0440c0a42e904014040c0045029076540455071050310076480c090701d0ba80e10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 345305134 1250 345303884 345303901
    0x915060423030606031902130e0f071809020d06020901210e070b0703022a040c0e03010507181809080c0c03070504231e012310090608041a 61
    0x14040799591080c40740c3c1c0001103041c00c0102e0310030348164032041e0542808140340e0030003e0400b0103040700d10f0069610103201d4022001046040c45400d00c070000340203214184041d003452840c1604421140c00c0c00c1c6402040141c1b00c0c01240c15840742c100c0380050310b903862100100d07003807821600b294880048544103582c04c4000369000b02c0c101c81702142150760b2603560b9010340380c244c00740c80c0018025800c0114840400464070661408102c02c1d0309460622080d0440024100c4815650120000310301200380c011904091046a420243c6424441d408070103076885406144440d004900004c4a4840002490720701c45c0c00140d0180d40c07201c0c3c0d031515846580c0171540e4402d1000c100340c1c8030b807040100008540c1030900c070b0101483d800761801c07044050005188541c2e1400a08500104e504010b5000b01c981b482007900c1c4e02a080300c841901515056000d900011200843ea03544540310045200c7c03882a0404078110449155050150040d521400e1656180d61002108403c10b40e6503010002e698 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 345306384 1250 345305134 345305189
    0x807030c23010f030c02070506191403130f03030f061202040c0c02031b0102100207030216240807051c05071101090c03140a0c122009150604 62
    0x50342100c62081c081c8481400d19031504410803070702070106241c90401e4072000d200741c01c0b000b000c10080c0100c03130079159154049601c0b0342c40034519441040c040c80041ea1140d6020340c0c03210264660820300c0781542000076015100740b40c0180008e003460700342d2400504140c02500110090000620108030203555009410100002105d00701e00c1140381c0210210090b005944a906182d0044c0041102d0121100c205a00d0807560b5402030642c03051244182c802c0304240020146280719074080e180d1100074003d1800a5007030b64105503402c46d856841240190200da22022200310203180044464440f817038159014032a040c00d00c0348031500c0165008443e200d6412060003005250348142807201d0360402103003220b0321100010300c070206100b82000451007000c21500044626420348880210076030302d41e05144907642c80102020314146c0250240300c0354000c0c0b90145154507055030340012550b00060520f940041200d05240b0b000c1210445c02d03100d000603600541030000340f01041040d104801c1014 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 345307634 1250 345306384 345306389
    0x10905100f081f02070c05211b010801080d020d211a15040f03021003020f040602150c04061205091c021f0603150f14070f0f021c03150807030c 63
    0x2400750f40e8881c2544500d95100b1078a95a4100003048040c03814041040754540c000d54808010b0301180034070100b4003074144a0a02c6e03400060180d02e034400300c0c20002421100d0140c0c044001500904441441c076074010600f06100707017151400102d11401da011000c205607800790200c0d01706107004030010070224200381d69440c02c0002c442041d448590141600c6c4a44500d004000e0305203400d040400c010b0510402c03900440425003405424104d1461800c60380f90060b07406580180c1c00361400700b50000c1310215050f044010b101a80d803915060280282c144120354130103803c10b907503410000b103080340144141d02201c900c2e00e502002030104120f000b55154081414902d00342100300802060b0740340c0f03200c1d1008032640f00744481e82a0503a83d004000030b00c200f54101740d800f511890064201e88180c80c459100d0b602d02e8648814242d0b400400610316020b035409201550302448445040700b224008054034241280b07404140d00103080b040103091005c90340003884a102e4000701104003d4201e014105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 345308884 1250 345307634 345307663
    0x2011709030c01150f0303050903030d020f030109060605281709010231150509042904060501200a060e010b03150f06091e0106031a0306010e010905100f08 68
    0x104058481c030303a541314543c4201c4102007880481000000e000b28050300c10013030004c05990078021a03290760b0302a0b070b2040120728000c500c00001800800e61610034031004d0860707490103900f01152001c070b150180701c600c1140075440d6018206c04c202c4912420300503440304001e260780c00c146c1c1001110345000c1d410214001020070401e40c030360704480f81c117030190008080724080f00c40c03234030b924186c040c0340c0d55840d2441540800c001000104e806440714003030202607c4400c10005c2c2d45005d20003901c02c0d40d000044107507100714140003040000f1780c1d1012449000d110380c1f41245020120791400140392880c0c2002c020b00d068104019400925419440409489030580680d0001c0380030385c1e5003d84000003141c2e581c14040740000814154203002c1000ca0344000d202200d040014040da1011003c0b001c00d902140020752a503880e001840c2840b4051000b0800c1074005094039410400c0c000c56003841402804881c541d6680021440c040d440d0500c0b00501034400d201d5902c50302ca045141c4c40d00384421740004c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 345310134 1250 345308884 345308891
    0x3020d0f0509030307080a090b0703020d0e01030e060604020a050706060e0f010509040c14270402150c06040609081b060a050c0f1b01060504020d0209041d0a0f02011709030c01 77
    0x45980d0141c011901d4105008010f1403402080350744a0465800a4165608100c89501d000c2032084a082c010030030240a5002814000c0200030000c08070042520a6410513091900200e9648800201c0c240c1005040b0340c056144d20404108403982c1c014030601070450750a2810000c0d50804240b1614051100240c0780e80f034503a01c40341400342d01181540c0c0241102041842000703000201d07e440109044020000044443e04030b03000746548160b1010109100340350390600c801c61a040f8004400084041d030103900f81015400d81c3c1d5103039a001040501071903100d0714981d04101042080704c002d001075800c030b4440d03c0841c0d4010341e41c414003110700080d40e52400c1e0104074a00c1800342515842e0b4600c04a00303151031420242180e440c1694040303825250b40f66130012429956600107000452015a00182c030340c0810010802030750103440800110a54581e4204018400420608400b07a0085e201070f41501030340c80129241e485100011072030482d441c00340400140080001e188100d5118001d1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 345311384 1250 345310134 345310157
    0x30319180b131a2209050109051906060e0105030a09060501080f0d0201020403020f010e0d241a03070506070507091b0e01022e18050102070c0b0f040b03150d03020d 72
    0x8030010b450007801c2189042051004c18034003000b0307011426107040c1c0c80500d40403031030361140320105030354084e0000c58a40e52108104501103100d842101012590003405101c440d1410002424070810408414104080000060850905a0449845183c1c0144104015a905c590300c42d00d60400c81c1d40b0344c41e24040c4621604101e4414002d46084e2a0028041c17666443c40300c0041d540b030b0013444560794100d005070280c0004031310941000080015a080d12540026002e00080101c580c0c140c0d4a440d031030603410116506403000110390341035076410b503400e0b9511202800e14038039014075540a0051241003680003104d801007a100c1c80301403c22611244428031664006a8a919004136014244d008c0c5840c2000724504803900c01010f005086130010701341151400051844138440401da17a641e400040031010418516980c5004000742c1003241e0800454009440c0e0a04c01c0d03100c0e841c928080407000c01c1d04501d5030b02c1c00d003108280041540030300c0c1140b8070b0041d440c2c090864424011a189480c40c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 345312634 1250 345311384 345311399
    0x503121f0b09040b0d051c17010e010603150308040807140d030806010813050601140102071a0405011202160b0a0606050a0509060d06080706080a050a0b030319180b13 73
    0x84810748004444040c01e0016000500000b06850649203500103101c4e04444d001c26402e000107640400f5800501e01628907050000d0003180101d900ca11100d20010010400404400190381c1560101e25022802d440b2004081752041c0c210b800203883e030080064002040f00c1c1c0043c4131000c82c1c24521081001d144807808200806c48401000f4004c106c1590010300d95600c29042070703900c141c1c10071510786036440c00e0300ca030380c1b43c000e0981012401c4050000d426646680420051000b840c00039000c00e003080d10710320704241c28010391045506102510801600a0626805550289416000c0e605a42909040c9900088410313590804503500d0450041581c1d8800c5c0c0031101108038030345a03145041da80c8030500801d640703c01040c81100e652618086041c0c1e205001d4000144850f9841c070905007000a42041150f0300680b00d07840c0945404400c0f0415280841036038909485050f0106c4410100101a0b4881404012900740d040d40e00d0070219821319413001410b92490b03441c54050340b00e5210400c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 345313884 1250 345312634 345312691
    0x8030f0a09143a03020f0111040617040602040e1f1401050a110c04050c0c060f100618080717070b0304020a0b07030c0203060403050c21190309050312 66
    0x40e10703000520440c1c0380c076140b0000300c03c8100c007201e003c0701e18407041500103400c594082e09401c210010381007452412600c00e001d01174404044444072949140601d4242d020303000740d8418420b001110308401c005400c0c4030055050714000c1042d1a15508140340c0b84d40d507410144801d48000b90400e540c8400840c043d50820310f400074842042c1c6405160034030443d019503008100030071240782c40c4a80d56052001d40c4980c01194040c00c03540e0112a12000803180540c2049001481c410095405404002da04c0e40c00e9540201100d1040c06c1003200c1e0020414060320750102600080810b01c00c0704030004425044518044c0f03080c2001082d00d00d000c2d1a500c002caa00d11040c3d0b000303944442c0c1c00354148860720914004003501442401c0c11140c1500c9503011a00b0004c04179001c2e0042040818440368811051000e035401041c408164030f51140c062400004500501100d159030402520b1407544041c083d601022111f900401282d4170340d425034040c0c5040000455409004030800d15111905290703820 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 345315134 1250 345313884 345313919
    0x31c210b1f021e10020406021509010b030307390801110301080303010512030c150115020c090f07030605030f0d11030f090607030309150f180201090302091008030f0a09 74
    0xa0183c00d808104540010242c55244902c403541e00038803035442e40110643c80103100504064015140a28980b06100413040008280071031507414400d18000c0e50b035004c0301710303103620ba440040e213034200204a42c1030514840c1d041c942a01c2608000d80c0b454080301c0d403040c4074121040e49009104090105140031403a01003881000c540d0750040c070052045103005a4200740c80030382c110441c2c1c180480340020520f041482205040510070990062101c0001185842c05515050004000a9a45501192122900030000d2410401880100c0c0c8880d119410190081100404403114034044500542e15500e200300f04c0c01c041240d0000c094400c3c031010040d00c0184441401c1a402c000035007060081903449a142241010355841c425400150890301782d0083c219605000942d80c40410100021150110b201440e1080010280c20060f0384c40000182626070580701d113440d035203030001e8055900085400251043c04040f0b15107032422480720140102c0030f03041e510a0503003035946295800f03889098 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 345316384 1250 345315134 345315137
    0xf050613020d08070215121005040e0a020103050c04092a080402030604060f0b09090d0305061c0215120f220804060f020f0f030c011406031c210b1f 65
    0x4840c1d00b0080340d03825020f0051240040c00280b07543d8001010054a03034014a0700c0000601c1041c1808040d081e0780641a01405090700c003001800032401030325a445020103802410552280d00180400c00800c01b501c00031b00c03007103006100d1500c0c0c6000130013042c03051505103100003c80703884128038a4030980c0d039a4081c3d500078002c1c01441e101d40c0c503054040d20f02842e512203019100d20fa03002c81d9840e517401c402c0c80784240c1c00251040108165009050365009080d261160b03c120020394003004400ba0801d078200c1d0f0455411400c400040a0781c0013a010364500d80c41e00c0c1c1c096208110250f409501c09920130804500b00c021a42000070000b420307082010406040010203000502c0364a018106150701e80c0824011a40d00c444202d00c101e24041600c44081c400c0d030804903d82858000074001d02d10741c0c1203003a03040061440d04902182e43c4058210001c0346c3e0381e0ac1c6d08415440c06005501888960650714070700030107200400c0700c41c4054050304035211f0040702c00c400107040f0300c00558031401054100303 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 345317634 1250 345316384 345316399
    0x2070c05010c1a0c040302031509030f07030e03010207080405190b0304330617010e030a210f02130608071706010203090301050108070f050619080c0904090f05061302 73
    0x4000044403003640001084071401860343d001103104040051152154580c010074507a502d0541c814181080c15041d01c91100080390000c0c403900920110030354410340d070741d0495183c944009040c11100402001605a09540300091242c00d12614400400c261041a02c5244045110030400210112144500c5020400900204001070700e84903c0555485940481000019100490620300b211602c024041c80342d1b03d90080000c1e60351000381103c4002c0e81c40003000070304c07902983c2c0b64880c85452540703002c00c1400020068a180c880c41e0304158410016010420a5002c034070b410000d50000c141e5048803140c4074030018280c0d00c40c80d075807031240555994071501c20701c1118008032001c073702401440c15130206003c0303441d007510244130740d80c000e141d008010042d00c2d18142803581e20300c189801c01c0d8042c020030022800d5440c0b007181c0c082c06894103441c00032840c3e035a070320f407040d0103006500200740c0c094208108001800b00c1c1804070060240150140c80582e22007442048842612010080d000700c2c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 345318884 1250 345317634 345317639
    0x1090b090903070813052119030c08030907241b1e020111250806070f050d0b04020c0c090106110c04021b0114010e01050303030c03010b0a021608071802070c 69
    0x8003102802d481c490b02c00040001e651980001021001c01c0c0c91a50349048280c0030034500b0820230041c40c604078605607000300801c001d5860050035170f11300340005060803400001103070000504005900042c080d02d04110340400c1d01c00f402d00c45079802c44080ca0002410701c2e0040072405071103406001b10691003810120005220815800301d00141c14060b418818582a2121a004e0170311800b1142501900003c1d0503072006010803c801c7c0040d08510030943c000b8042003402c0c3d4103c4990b0365007400701d00b81b15803a0702e18280c2180c094015403151941081c0041100c3c070000c400020f2009444800b01d500c0003d076070300d42d401195041a24004178820b940aa00c2c0558182843d41c0200350541074004102540b83d03120002c58259041c0e2065025421440401000700e0503240c070006014000c120091417540c10b0403140c10000b8081070103240407200b00014100c008600810111060246010840b0342c2d4960781c4226949485036031154000312141c81c03440540682c40c6200b19031000c0d50000428607940d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 345320134 1250 345318884 345318893
    0xd050a0b1f0306180506130209090a1e0f020a0605030f0f150103020c240105030f0f060103060b0d0c08030a0914131e0e0604022d0906031f020301090b09090307 70
    0x43d10042c03440c0a11341c00b010010643c14000188102d1200301c1d142070342c0701c103172051005c0c1250060250307a154014080d2000018901015000d01c06c4808103506501d60030360800405403808032030029032010107041c0008059400001a610508894042d0143c0340d0700c01e44900410729040380d609401407110702d410030300741d8000c0d0702030820241035404581c420700184075040c1e0b40303200e03803c4c0120380c40700090f0041246240800100008540c005c0207881e014400ca450141d0318081804000d10550302c43c0300c4407010b03403901c4581200343c541040c0c03542442d5690b021143c5e01e030b603c0b0000401c001011920042519000740f0703211311801001078400d002030302c3c03801c90441c001c160200000c84201115140360790207a100340034000000c0d910b0400307041681020310420010090311003100602e64030040303018031180002d003088810032105036071102d016a5002c0010b0b040500040b0208070104414400c00e1030a400d9502560580703510314802c200000882c1c08000c4035a00468100041d980301b0000c160014 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 345321384 1250 345320134 345320141
    0x60b10121a06030108160f03240b060706050405010b12100209011b1103010606111e0f190507060302190309020316030803041704050f060f090d050a0b1f0306 69
    0x703041812500660090480080c0d481d80c820381c4003000360791050300c0001000741540300c880002d1100078840c1a840d4555a03895540000c402e0b007801183d1074801c02d40349801042d800c400c251950050010703545d180d142c0b0f0080024035090324251f40e02d40c41e0442d102c0850504501c40b40701003900c00001c10b01101c440c1e60000195100000640c108401030580300c101340e071001038017002c0911400b5078014085044060508582e00d591100c8100031080d000e001120001007000d15451400d10180145022480e0010349051969000b107070b140e01c2001d071503080845000554414086c2324000392114156030b8601241a03004898010b81c881e40c1c03401700c14110754003a5024032015071003d13041d10550f0301c5810301703000e01003d0b82d402074a101900104000422030b2040c100214040e004080d5400e046c00c00011549008101d00b01c68043c0c000090030308048250300e416118803080080c2071122040795032800c0707903c9000184045940075000030200c4c0c28a00703442ea001b046101c0034038058860528507152140503 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 345322634 1250 345321384 345321401
    0x50705070803040215040608010311090103150f11131d06091303090b0304240c1e03020705060124020f06061003020d3213081e16060b1012 61
    0x1292013441045172088400c0a04010016a00c0d03410140d89117040090f41c001d802659144200800c0d801403000400c03081c100b080c503003441480010300c0c80f1100f111030028145801214200140491550380c08141101290150362070402110a0001e0680300041e0240060300c1e00e40e030000105002407803440d0340c542e891000714000e00d0b05140c05546c491248840343e109a0342030360141030389440c000c200320740081d000ea4000b51701d1004010f1260301000003410303658a444104c80b10088540c500780c880f0b109130150b171b444613002016290346503582d1890104015460b0200c0ca00301030003401074442203002040804e811076802000c3d003459942c940c1001041450b110100301455400d020982010001307224070f500350004441c0c0c01b5111080c0c00e445c6000303060303080b0070090614085020024035401d90422030010503401540c2e00d407101880601c00c02020702039104503650034800301e03135001e80115490114003400d0241404200074198082444140880290040f01089910001c0d1030811765980c4111075 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 345323741 1107 345322634 345322639
    0x10e04020d030f210501030201030605060301030b06091b0a0e090a090302031206010225050f120a020f0f0d03020703020328030e0a0e010314100507050708030402 71
    0xe0011241d080040401210b0140c1c00d20881c0900420710382a071018003d409140382d421507181c020710092005a0000b410f2103c000389904104017124140c2e070300600e1511013076450006200c02e840300902044944090310000c911801e0000025000c1444156500d440340c0e1102c0d020807210a03c06060859814a45a442400030785c0010460300e004512801030314840d511580142d0401c071100c164031010003101c1204040f803a40740da00103400c0d20380c00ca4210110f400e6040c10f10034043c555448001c02d6a101c00556400341c0362528000c00b80140060000d5014800c02002c195070100f54401140903a104110910441c0b40c00d000c0000c83c106a0b100ca11050904101003000b4035602c43c10150610010222401840d01c0c0c1c030202b60080c0801e014003800c156540e103000110701c8074600191015000c0c80c10506001d64450080302c0c000c440d5a81e509040c1000d64440c4072140c0e0001e44100e9 = true := by decide +kernel

theorem cover : BRFrame.Cov 345143884 345323741 := by
  have h0 := BRFrame.cov_init 345143884
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 345143884 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 345143884 ≤ n) (h2 : n < 345323741) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
