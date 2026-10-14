-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1631
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:57:36.163007+00:00
-- url     : https://prove2.me/submissions/9ad885b2-069a-4d82-b1a0-b3d46d95aea5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 293165467 ≤ n < 293345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 293166717 1250 293165467 293165471
    0x30c0b0705010f0f150b0a05031909050d1d030c030604060908070b040f0309080c0a030311160b093105060d08031008010b0301060f050d0302070323100207050c010e03030d14010801 79
    0x501d86c1d9424050784506042c00001c520148000f03040078030304655848600c030303000102050181c4141e54203807400c0885100040812101c00c107400481c40c289116413100e1350110001c1c507440003031001085d2203440140002d404da944070351100081c0920241101c500350f900c50101640c80c901410f0032014904080404c4002907190f84c0002241100040c0064140705d0040001c101c051944d6025a10000d1000d280308040c098608090300b81f40e014031202d00149100c8500c00d80c1d03541100200500300260780c003580c2e421340164000308041c041d6008500d1259070030b01c1c40003c407030301c0d0140003030307040504010010482c00c1c0010402c1b50701e4075000c1c1a0821504084001c0c064006000304250a03100c681c05860b48014051208000c00d01d4811001042c481c083c0c0155100c49444c1e03261001161201e00145001411021841602c150304010300c0c00302e400e0b400c1c804c60502c0010340d284e41e102c40c0602881c6041080c4180c0c1c0380032580e02030045960154160f242003107403109480d6550350982003403040800c0740d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 293167967 1250 293166717 293166719
    0xb070e0604270e070e010302030c091608040c030602030c0c3304080c030c0a12021227032a09040221030706090308011806030c0b0705010f0f15 63
    0x81000340a840c141e922158190020038050400d0b440901500d06403604500c0c0c550a0303001d020381c424016100038100b0210511499815401814648805104840d02840d801c9040045584038400c0108a4500d50b00d0442d41c41e071540c2c24140000c640c0d0340c01c050807081c4000180540c0819100061010f2a903403c1650480b41d245030400c2e50401c044500f40c60a003100601c102001392154000da0391052088403442d003002000a20540756070040d00c0320f1002644a07001d00700602030a03e100d410a50801d1008204140c0f011780e1307100860007000c9008403d840503026a18002508100351020a44050229008001800442c0c602c0c0592a80c1c000d40ca900f01c0c809aa440e81814408a0310594020b4810700c1c030002128034000549656000e460000e000a00c05007000070254001c20f145036009503503009803941040485038124006030b1000ca030b0589020b904000142c0100015001c4910680303002d52184403178241350b8098001094012052840c208401d6400a102c0c0c1c8807100031000f02000c4203541d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 293169217 1250 293167967 293167969
    0x1c121404051306210803010909050a050f0d023009271501090302030c010f23040f080d091403071d0108070e040b010905040201050702130e0613020a0e071b0b070e 71
    0x400480306001d40524006c00041c071858000e9040200d01c0c40c1302c4d8080f41d0f007202d007a8980906004001044184035004603913a2403e1079410054000d9003d03510403642c0300d900b2490325000740d00c1c0a4150402254002041c401220743d95151031589041d40c02500c1850843c140c00d481403034650440302d6404640034448078921551007201c0c400300f80c130b0380a0004c00e2600c6078280151000041d803602141000616150130701000804441d00312400d0040c1101e0792100d041c4210345008400c99003012009521041c0b2010360160301c403500c9822a8007000301c050000e00c814011a082c00c81c01e40004003090010314080e4600016800924102c0b507c98040e5404584c50329031180c500c41081c1c6002d8000e01356031006001c0c0d265542e0243e80c000c0e10504005242c66100e5000c80c409280c061601d02005a8510340705101c54001d020a0764401441e148480d0030744a2a03000410400c114011030681d503242c04002031741c1c58094640c000001e6214050300c0ca0000040c5800c54400350200c4400c0001031810f0481452 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 293170467 1250 293169217 293169269
    0x80309060613110d02030405030702150703020606090f0403080705041e051305060108150d02090f040201030c0503010b0a0e030c06042903040f0303020d0f021303021c121404051306 79
    0x114412074950344d10b80041c20000c0c0019400141c0142d42c207000800c1110016500c4105040907820044002c5440c0c040742d09010781840030090501c1d00030106501003200c1610f1500c502940b2540c9402c19036201e86076008100c9003401250000046d111680d18013104001c482c86803501107030300c2200e070500700c006940c845800740c44090390f445000c61054808113001040c0c0b554a0b03130311258007401c2a440d9640b00cad000200100701c140e821090500d041d00500040d9607060103006200056424940c0c030307551400400040501c28132484100f0480221000b04040d0b0702807100b81415040182401e40312078aa036881c2005070b0011a901c0403100703240c00a1802405d1540507248281d0704114104e001441c0c03514190080d6000090f0411520341c0c03203400f626031900c1807001d81070f1705104c002d03070801041c2184140010078500e032429031540448022100d00040c2c140702c0701c882004440c90030f800c011091007034001c0c03079010300e40000d51f01961061a5610000441d030084040700c18592403500004405032600d06 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 293171717 1250 293170467 293170481
    0x50a0b0408120f07150f02030a09061b0e060a17042111030f0c0307020405090607090801020f19140309160504020c070302061803030c071e1202010f0309080309060613 73
    0x546503e05000b10404101c3d50103145840700c2150b6000b04405c8240203e10003280c0c821140410955910041d03d014080c0303d200c0c08140b0803a00342e0007800e00708440005020492190702d024403a03240000c030700c41c01c98801e00403810188241c420303401d042c0c1080e00d0030641e00303040000c00c030401c20451200070f000c580c4074400012807842c49602440c5010301c1d800e1000100e1781300000036040c41c4820824000141c559101e01441007102c10003070612070824503030041803484160b10482e020f070700510159485225000031601c510f07411168800b1082c501d91000e84040e9a5920b100c000315001108200d00c101011440d00d40c414407a0002549058854080000301d0141030b030b4016040c5c0c0401410720040c00c1c03903402002c103401d42d41d0900305030985400020740f071a4450441c64100790030015080290044102e0140f9010008055842e6598200003044070384200f5441c01904202200590801c000d0207070340401030781c030381040a80740d80349030444059980d20300c1603412902400b080c0c9041003000c0c0052080356 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 293172967 1250 293171717 293171737
    0x40306022110030807060e0316030306050d08040b0901090e04030e0906010906020a1b0f030302100506010309211e03150501020d0207121a010e0f0f010e040318050a0b040812 76
    0x10b0700d4941503896506007500b00000860300d01d540c1d1061008841c5081010700444440e8a0000801c007030989001802e03107506030b002c0340c000c49185202000140441040e141513981c00c030243c940328204c50004035640344040d805459600451800e01c030905910140a0907180020750340c80000f41c907000e004449050326032040c00c0040c1c101c0d00c20640011402006541e503898071621441d0019141d044c8001c9003001a40200c0259009003c0c602503501c2c0d9014269100c1824242004080032580b2584800c000816a02c10403020011030517181c1409030f90004c01051485501e0702844e4595000a03008140c0903e1104260385819030004031b961000907400a86402d99001c0e000f094605038014070543c0c00d070311044030031384054504803001800711100a4000e0070300400c00c5425040001c25141800d00c06405542c4e460b4403c0700510950450711030482c0c20070b41c545005041c80800c03c3d19121140c51540290b68030181070003000845520440c041d205482e02c5505480d800d0315031410500d03240c402e41d041d038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 293174217 1250 293172967 293172991
    0x17030402180a0e1c0306210f032703031205070504140111030c011506020115060f0c0b0a06080c03010605030a110111060f04060b010c11091b0403060221 67
    0x401d5a038501d07540040c0c10240040012031051020103040307050251040062911413402c208076007290744c0c18000e00c402011069015034041a201e00c054140329400f5201518450588140c002090312400c000182e0000300307000301000710f07580c1da440d8881c4402480141c3c00180c04840701021000c040c41503e026160303a8035000e240601c5c240b19007481884092425044c40340c00b40711448101c00500c0206a040803000000890700d0102d055013108034240e8008a045a1400d404010b1842500300d15a05603200c83c1440851420f50314401c0b6800504240004e00c1120a1000c0c054608416041081651140415110100242c4043c1400c0b60400d00c10180e159120307207500300101c1c14046007100d5040043c5442099520582465440e040083e42c0100010440c001004103104141c41108880070003460540201c000390b440b404a140c070440065440381c00c01001080c8007251545034400180b0354a0003150300c2c6d6a503410010300941000c0d070003039965020000c40802071011800070078882d034100401 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 293175467 1250 293174217 293174239
    0x5010b0a0804020f1203030a050105031e0601061805040e0606091b030406020a1b03080601020c0a0e062107030507090509010204210602070b0f07031407020307020d060213060c17030402 81
    0x304444664945001600f04422140f500c14000007480290b08c03a406010010495515140030305243c140001c0300c0352251850742c0642d0000500108140c3d044400620b8112999034401c03000002e0500e9a9102c0c0d588507240400d03009007000301107407140c8103c0d0100c42c918410b40e15010889914010201c01e1860b00c6003c000090006000b030f40a0400c8214614203840403410309034070310078041140a070035008030f5003c0741001655070b810021040c0f40b150540d20801003914200e050f951019001e0001c510900c14044d45610b01c01402c44008180c0700d0700001c403441c1c00c3c2eaa0500c1c40d1503110368000c0280311400d000020307140c09414002c480840b90103698035054000d030320003200079000015100702d403026001c00c14100800c90202d440c5000340c110010450702e03130800100c0681200e5040d24135441c40c1c08801d00300b0501d1600803050300c45140e01905d041007810003074a0b12030003d01c5007900700250016030400104541354003034550b05280d80b044000560444580b8030881c054041141c000f98030031440b0310703 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 293176717 1250 293175467 293175469
    0x270201051606060b030901061d0a0b120d09090f09120807050c011e141b0c0a170702130603080403030e060c070b090a05010c0807081e07051005010b0a080402 69
    0x14007809511041d89940d03651039507501c10684200b030b03000030034070b4401205000007182c080c80f03890010f0900010440401c0c0b515000002d683c80300811214420780c2e2044240965120302c0707849284002810140d48a05843d00009041c0c0304442c01040c101a00d001e60b25249414a4820000c015404c68058a00c10300169003c481c55680144803000300402841100c050b80c000340290050389504d4900650884083d100034400c07074280300544180320407410148407503280c00d01ba000c040203440e00e034043c2c0e40c0d54031085030510300244080000c0060300c0c41018030b11298400c00160203418030880c0c17112101000c808091090303030014040076045050801c410000240900a42e041120700508440c1c113214a1101c614141109540900300f00d041c0010f20603001d191401c0e414014001c02d0030302c540d602d011622450340d02d000c0d14900400d0142c0000c5d03403004c15440010454040740500400c81c3c1e6580746450f001da247c0031062521001c5609010000c2100100981500c02e00c40300d65a905003170341d489030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 293177967 1250 293176717 293176727
    0x1218030f0307080f13080304061b0f030e030a02030303090708250b1317011d010c08040f02040b0904053307031a0406060903021005031b091f0f0201270201 68
    0x83c82120502010411000013039171044140008001410185898a1402801416081010584042c00001c0c071600e82d0010320020180071142d03403d49411040b2090640c0400e18208903054081d601d13202c08010860306072800a4803400380c406040948211030b151914036000c9107141c2160585442c2d081c070050000101d074070090080e039081c510074100308994030144a01070f020105481d6181c1e075150040084070b046030750803400c07000580c00000c014583c108040249101000b91005107260006840c1c0015551150011981910001c207500006c0c1001d15195944510300c0212411070113455590400010000b02001008201010b200b00240c0d1480350490041c00e8a2448240700c8102030402c07035158550340303d04405000d054a488650030f09500411000c400c12040f5042000020000c000c1c0d8101d0a14106c40b000c256a540b81d5250660f00000425203107121000401215065252110076503105290303c481640e80d030002c00c20202e04282c200001e1400000103554000780b10b8107400154450 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 293179217 1250 293177967 293177977
    0x1b0a050c1f21050c12011a0708070c0503070b0415020703200406080303070e01030b1207050d170f1b06040c05150921060a020403110f030f1218030f030708 68
    0xa54500c10710142c0141c42c0708222001611075200c41d103804244064a118012100ba01400054109420751000070b10581024030230030394003c00050010450404100c0f80300107850107060000e0a071103105855440a0011b90000d101e03149213060101e03510b03451140040743c0c4909690700044808021844d200c04a00000e210392012500030303644a900040403a02440514024040342c1d868440c154004000102500d5030794903a24480c20340696041400c841c001052411030340d00b502d0040381801e481c20301c0c44a40034140d0401043c8a000191040e072402c1c003130300401d550020404100c04035030031015a19a0382c44119001071890848400504c030f2450200b190f00c1da03000d12050580d107000440400304282ca034110001c1110f09140702018109900244210790f840b0201080450505180d41c55145101078920303056400741300c142600041e140c03424026281240c10540481d162400010701e1034810703601c102020340d00e950005655142520300030a01e9000c400c40ca1740150709004464076440c09070340c03003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 293180467 1250 293179217 293179247
    0x1202031501230609040606090812040e010e0c0c01050a06030201030e060709090203060d020406030507081c020a080f0409050f0a0c03020901080c030a140403020102040807091107030e01051b0a050c1f 87
    0x240946944ea80c2c0c1d50080c10b015002c166900c007032291030500c010386403900b00c48280c4a100c2041c0004e00081c040300c0b6000c0e0466500003440006a03d0f01b0011909910030f0700091481542000c0c10490000c07070301e810440440c1d100380d03010000702c201040c0b01038482d00e007694024009004140104a0000c40d500515009070b8020b00300c03550071405500003001c80c1c2d619401100d040c0c02c5603508104142085c080710030185101800b004040c51a080c0c025110030032090014800440440c01d0156141c01d00180c602a03c00c1000810407401d100300e00380c400807000c840107000d40341000025030300b8034424020b49400d1035060f100c0200030b459100c10305c18180c00082244484540d102d407116042c0f601400d0882c0140e000744c00060362181440c0d002410320701c1c1c6800220781503080c9505440e04480220031140d4180c4c0501c1c0c0304154a210745c00407100c070702c02c0748402d0307c00846005001200500124010b5640c170b1240007190402080c0384103100070004d04003620b040d141181c0c200d84c80030310701070302505041c3c1403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 293181717 1250 293180467 293180479
    0x103020c0a0b0a1803021e1606021b010e1809030706110a09080703170d0e010606090501180b030c03040606120605010312080c03011806030507120203150123 69
    0x1400c4495186028404003054034441404024803c10403c83d200b01002c00b990302150310400701301c0b83ca000e5510410304800c1185100015100e9000410501803680e088040303503440015690741d2140250740e664504d000d1603130428200b65503c415030240031640160800600b41c1000c0b04100003d4500c00c40e0010041912400100080c90005000d403241113611142e1a0321291105a00c600c01004030219411120f015800b0034000e101083d0000b00e00140341000c081002e03680c003000b003c80f201030000110062043e600b07003203001c118160030130311403020b41d0030a0fa95928424211404000840f160380314071059103030100080f98035220303031a0046500c075028140108800b584c44170284410794a240d400d03240b4503a01e100600c100f09003000300410040051403c00d9803400c000c001eaa510348010720440c4542d2101004c4144c2582c6142c10a01c002c40d08007080d629041d944003c1d00c450b004c17a800c4100c1c8640111000d90054800071701885050f0b48030122500c446a81e410414035595251b5010603501007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 293182967 1250 293181717 293181727
    0xc02010e030301030302060f0f0405070902030a02070501060602100f060b0403020d02120a150c0305070e1c050303090105071733040f060303090501170a1104051806030601061e0e010302 81
    0x120342000190300a6100e540106114503115a0780d42c80700030003134940c4034500400d0044c00045880010030101342c0340f01100c01a603a40f200301c1c00074028800d103003005040d5401c248001a101d60041060a05090304200a015800c01c03a200f0310121030590150104e140000d100078400b6081c01c51f0400c0205102406178881e20038000c071040e10b420f014260032268074101c600c0e20f030384070343c4280281900746d880317401c5c240101d0500103009031900c0b072050310b031500511601c3c0c40c0c030440c86102d4565000701508642540d6880c1842031440340600800c0b070380d06d0301180e1059004008500c90701202c500c150010758590179007032100380714514088401611010061000c0b150904a81c0c0c5074030641059041c074203c005005442c51601405104103036108034103108108500904a00d0302501ca6640300100f440001030071034400400ca0080e0180f6040560402469131004919940a10410f40220400c5007101c01581e038400088403000c604011111115080300b255010843c0251035030a81c8400504002d07040c8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 293184217 1250 293182967 293182991
    0x1180c031101111605030c0402040506070f02031207080705010e0a1502070602091507030908120405190b070f031b0804090b0d0204110a1d0a0501080c12070e01020616120c0201 77
    0x45100d000c451512a041042044170b45420048812140f00650b810750900345070000059040c022560301403e00944100c82d8001c640d418800c600210030700014841e242d810a05061105803c054030032036440d80383c4a50308001c90340c000380c0c56101c82e91000d4a00248140820440f0280d00000c02c0fc4911b16000c0c04203c0696442c0c201101582c248034829640b07490700c605008108101e26400080f42d40c00007007201182c81c0201c004c0300d0680e0000e4407200c43d28406046000c2407082c40d5030240380d181002040000810107000300c118000b0340281e90b54400c00748088140b58803003d903c0802402000e00304420821402c8582050a03201c0000b0030313880b0410708075000710303040d281400351191451714000b90000110341c0220080c540400440c0c894555910404007150090310f06024441c10b100203800080c00010080048615518000c0246085814003000c05400c41c918440504c0c05801100b0004419034004171104003043d009581d0440d02c0c0c55020a002c00400a103000c800455481368825100 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 293185467 1250 293184217 293184223
    0x60f120c090f040317010b1b0304030206030f180303010b03060d1b0f06030c141210170d030b04020921030c0109050d020106060f02101d160801180c03110111 69
    0x10850142002e00c1030b5140c00d14008143c484a00b28141140c0304890040c04214490016504048441d106081941030f00030340305840d40c021640020340c0464008200030a50b0034a03180d441c01400e01d0b03035800310750010091015440f80404d024800030440140001340c41841c00e100c1114115000c0e10516090308482c0201d50701700c0d80c05410841c10340301d000008011055061058843d09030303003460a80b5003900240804d106500c10000070444480241c00407854030319009510b50000c000030030302c0c10420703641c0c28040340c2c646090150040200b40382c00d6407400641800d000b103500c00c4030000e0112502e02c0e2050844007450255145410341480140442901081c09101c0e4102c0c00303019000800045108201c0242550215003014003004032520041402d0703034002440608004143c1c1001c00c000d544c20101c00310707001c035004030580d80d23200d100c10344803420751640103544c151100b0030000e020201c070620300c0003400b840610000f0a0404151800c1001ca038408400c3c641860301490b05045c5040c40100b00c600e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 293186717 1250 293185467 293185471
    0x80c1207110705010315030b07020f060106020c100f0816091206020403020a05010507080712050702040f020a1205060616050a0f050f060105040507140304031e09030212010203060f120c09 82
    0x4042003a5110804039401c040100c2d60080c442460140180781441c2814990034695100041141001d1000f04180500903c071010182d4103140445296680d600d00c000c1d6940c0c08554568007482c1c01400b247c51b0140308903110420201503444001c200e494040710108901c1c0200444020840d0314000403d8515030302504410441c0034040240c3c031181540100000340c01c0640c407c5060140400800000618540c26030302815006810044c0340302401100395503510494100075401890603a44004065141d0301810050015695802c24100000b9000b01126000d4558581c81081800700300210303504030182d03807450740c0700d030080e605003104070340d2198403122030004201c6460300103003141e0030710360801c01c18140188006c4a00781320389d040c4480040c00c5a000f296803d100190300100140906024054840d000001001c0103080c405524400405122107400300302c0c403c40c103400b0440c55403c014000d8030702640000784640310a41a02c4200980000c43e8189180d080c0103100181d40281d4400b04928 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 293187967 1250 293186717 293186731
    0x1406070309050c060a140c0c06120901050a050420060d020414011b0213050606090a090e07080c0f040c09080d0507170316050c030403151b080702030703080c12 70
    0xc00c903074040b032400d90300b003a68031040b4a029074003d00c0410a40c0380e00001c00f4981010120368142d907038001504050800c0c1d2180c1106801020000f0180c090b01d69030285113126280c1c04000300020340707170358400741c080d1182594058801c040340c2400d43c01d90a5502d860a0041c5801000c85103000b0180036207000f41c0e04150b02180c01154200140391a5503000488040107040301101001402d52035130000d40f042c007140c0341403424150742e8000900252030b100b0403124410700041216240654400300c07600a000d4003000c00120f1b002d51a800501d07000001303641165007000038804802c2d6001c460a010003060b00c1c038406000c0004e200303c0001c282605000310f806180c80e40d628555100142c0c2819807010030040032011041d07804108002d03003103603c61400721401c5885d103070660395800741c0540c6510310301032904007503c0700242e05030103461400140d011409a1901c03c2203151824800402a28a0303e0110390320009070b0010008031000038883d480d4260b201100f010000c1c20f03c4000f00316801510340460b001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 293189217 1250 293187967 293187971
    0x110106080a05010606050708030c0a0509120a1106041a090a1205060105040606050304021309170c0615010302030c1804021b060f2404020309010605031f05010f0e1314060703 76
    0x4207062000a000b0390010700310504040e0310f007000a5031805907501c001448406103220200e6031200d9107100c1c2044421440c801800c000d8902604c016035a00e8240d03089007156110801c450003d49420b064095408564024902c5c0005140c41c108040883d0f1101041c3c41d4801c031485004202a004110840266400755004009660400c41440121a19a000602484000d00410006a40301c5c1207020142d00303220310110303240e400341c6042d200b4418072588007400e0010108400c0000d40c070000d501031183e40c4410410210480050041d0120700c41591504806901006800f54002901c00756908001d4003402c018503104a8031500e4541a01e2800c541c1300c0f5030012028045000c07003015075580c001c2500c14814070a031114803080c560104502c116140116000300004100c1d50081d80004010107001d010380390b00b81b410616a001c0b0240c03444000b61498900000403500200c1d0740515420340300c6206075980c0a4980207600808400b1081c0c003110030008103031a060300c0b21800d0040a0040401e070b180 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 293190467 1250 293189217 293189233
    0xb0d0513051911192903090a0c05191502150c09010807020d020316030c02090c0702181302010806040e0f0601090c14370e13051e0711010608 62
    0x180f90a05070b98103c91003103081d4004840c00701c06070740842044448604924541220024444058a92000e6001c41444010040000079a004a81c0e2040707184103018400000781c0b22420824070001c0d072001d800b2840034100007030010b540c4078003100031a0441e90040319040118000310316200344048034085510b4502240c1400d2079600300e040e458000754a400600b405031031414000b9502e014400400d2840d1104240c0201414000d002d041282a000780c2403a031303146410400c2c0e00c0030340e0009804900408101582e52090043c3c0c40c070380e6019210440150001c048240c0046130302171400703003480d03234032603607030b100c500142c0808200d0416102c2105018005643c98410b8900031200e130710302800d042c001d1a1049120009a01080b98001515080c0c0d0511440400c000c1070200554030400e510006109545003c1d1b05070000e00000b81c1150440d0f0034460690500c5002050b1074003941c8644030881c43c20381c81e0010522414203103501c03a040e03203462200034003a151500d003500c1035940520200d41111131 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 293191717 1250 293190467 293190473
    0x7081213110f0108040303110c0307060e0d1d01050d022701080a15180b030d0810050a05100809011b0e0a08010219030905030d110904150b0d05130519 66
    0x11003803001c24021141c8003081005580080d0240318004d00040402d6503403a41484c00400c034006844c20040d02d4021aa1103601c01e1410030010402c0781c0c0003031040e2203144881e00e84a07210341003414200007110346102c442c00c00740c07005498940010280e1280690281300d07482285008101c154490144408546241e9840e88005402d070040540340800b201d0a0001c5283d4810481c401101201c004000c415549460101c0c02c500170800c4070a9113625000b15402c50b4180c42d803110005000780c10308442a901d0380c0c1c0c4ca908101c0300507403138803503d41c10106240490190318042c91070243d2245013100041813900c0807000c19564013507004000710101d41090264406800c1c4000c03490040c0a15500842ca401c440750030f42c0900c00207960b01442003540700c104880030000b0500070f075841144200000d0051001c079a486801580141071424015490300047e00c801402100101c800c8035011080c5600d0304c5842c2502c04003420300207003000c0e100c0d24100f01d00d01c005241040301179404044800308111400040c9 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 293192967 1250 293191717 293191733
    0xc1006060201050c070b13050607050a0e0d0201080606030a110417100b010c0f151401090e06160c02060702060a03020714060106020d0815030a050717011107060207081213 75
    0x3800c104110780c036050030042c00c1481c000403103e0701500300d0525004d5664103255440412504500141740d8000c0c10140009550090085c0956112940341c1002160644084c0f20040181c0030000e40050810008101c0700d08052004540102d40301c0000302e07203c41c100703016650701d030f200d9845180c00003410402078500c0c000c1484200c5903102030303200030700a04040e40c00081c5801044100038044a651a4040042004020710083c042c81441070500000d03000680a6080d04001d100707514a46007411102d41c2160f4001c00d80318412502010102140c00301d084040f584002421306c22a000401001001d02617030b500300203400d9000c640d41e0050780d075106624000c03605000d1040c0003030b5140d00100051000c240c0116000d05c601400349030501250340c1e400c034a1175802c1010010b13147c05016025100050140203d501415158801600260141120880c50803200c40791000510800180510b40c009a526001010400d016180050500e52090300c240e45034201521640004418442d40204001d204 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 293194217 1250 293192967 293192969
    0x3030206150a0305103314090f0a0e071e1a0705030403021915171506071103010b0a0612050a0204050117070201110c070e010803040b0403260c1006 65
    0x280c0d0b0a0124500d169152a6036080016509003c540c44034030f962012501054680741c02c19042c0b40c8542d00401090112540038030b1401030300c034410f110190304c02c0603003801c1603618040d46001c04903019542d140c0462900500b41480c84000318000c1003000690f01103260f01d000400c2041c105150107403864181c5100c9208241c0c190300c01c17880d00c10705c5610082480841540d0072650140d80f28250946402c0d0307462890281604642c03000010000c1d0a101d0036071040300507030f514442c100d042032543c56036487c106c090240c1c0c1c50060313032168040010100040c1070180f00d9490744406800400c07040440c0000402140e000d41100300021105101100d00b10342c1801740c03540000340c21108514060034000000c00012000d62209451100403021800052003580b05101c161030070b4507010307219444080710380e4a94030740e403160b1100441c1000004c00d080c5004412102140c603e086054603040ca15502da181940481640c001040c099058800700081e82d0f000a0152446940140000c54601d8492400711411 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 293195467 1250 293194217 293194219
    0x40c020a020a0909150f0b0f030c031905241b090f0603042127060903150b040203010308072108061e0d111806010f08090c0a0303020615 60
    0x459000440540c903600c1226003610440f8030089968865403c140800641c503904000c5100d1070131181158030b46441e4800099250b00310303401c685142d9030303500b0142c0d503442061000d40c2c15040203087d01e050001034070210603403910030002d032409452102c111010140043c610140e031541e80d24100f0010080154484812051043c40d85003054000d40200d8050440800f80e18051003002001c2004d0102401c140d00d440f96107986014015210044020134031400d2181e00d400801c0b1540c503407607103d0705150381c10302964056075a4006152840c1c955208205038030100e800d00f50756074581660152194001540a18010340009039991a00d2900e00c4501891402285280e44da5101e16a540c0358005010368000304200c40c0740c00d5810a2546d26604400820940c40e40300800f281c9082c10018040002c00e4107150865104c50600c000310546020303044103d518070f000440f00c050186030305000d0900c807500a400c0c401141c01c1c60108801283c44100755400a40159014004100542031044112401954 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 293196717 1250 293195467 293195473
    0x50301060f0f020f1c09080309030c0d081b03130b03090606150f03010315051614071e1a010801090201020307060209030c13091106030c0d1104051e040c02 68
    0x200d4000010503400d00d20401c00100072900c0301051216100b01310404104040c1c000340d8192100480000c001855030710841c0010481158000405030404400e40705070220240244c5008d00c281410000c00ca0720030b213800c45442d9010301c0503003e80c8070781000c181103d0841c40700075640e402083c2610780410b034655001403100f40040041005203d0301055154006005507089540c100122810880b68018521007000c411030110002050081c04404403051480c201e4003003019172600701490035200ca6a81000000c20003040022600c0d80703c05008214107070003089202020030440ca42880031070710641082d00e241681c1a5814540e02d00140c18074010301ca43c01c001c0040000960010b900d901034044c0141c51180e02040c00f401584050220307640015004004002c042c007994040001003001600a0743e160440500054082c06c20342c080382d0082400780413142c1031484110400003d8215200325000c1c6038400e000c0010b03203840d0740515080004499003250101500c0c20280412a20204060310440d4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 293197967 1250 293196717 293196719
    0x6020309030c0d2013020d0515060c1b190e04050607030b0a0612020f070c03050606180c0a090911040819080304030503072109021908030d02090f0303130e07050301 72
    0x1c44c440d065200525250302034840ca00311400c0010032000542880e91181400082c00703004156880e80894826004000c4d454003000c000da0074852140140c6000305800c1e0f0180c80104110520b4500081038001700600d400010f09000e0900e00c040c1d451a0300c401c0720341c80c9010a1100300724042c044140e201c8a546001c00182c0300300400240d400410b4030070502440340c2ca07846030000069940446108000b0000c0b82c0c0d0741e8220314500030003005918401034a203402617202141c002d19007044d031050704440350101c080980d01d507031040790780b41c0c0c0c4250f180c50180810682e002541e160b49004542c602103050220540320740c43d01804a00305500c004030603651903d0f2801e100002030a007025a500a03406141080c2c503a80c0f4040b040c2c4075600c00804a40804101c400c0201c04440c8030b820600419100761242c0c0d28a4200b00c40c03640803040103000700820307600184680c5c0040002c035806042070710b800405a59103081709a02003411540001c1c60694418180503050004030400b604c0f080c2c00c8074036468524559 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 293199217 1250 293197967 293197973
    0xc0e0f030c0d061409030c0d03060b0403080d0f0609020c07080319030e0a0b101401110a0b150a1203090e07020c100e06031512070e0c031b030106020309030c0d 70
    0x1070100140028440c0c1c4040c0c401105010480c1e000c001c600502e4048501d160410b90341030f9540c0d4010403c0c00c1c0c5c55216408061130154801d001b454112510700461034109130641d030710341c1c8840c1c0107000c40342000790351041544010400341c000c410042c06c002e8030060351000c544c080705090082d140c016400703540c401c02110050103210010801c842000c3d24000502101100f42107040c00c444100182619208406100d404480c182840c002c84d0708401500032400401c030015280714180c000224841c2c0c00c07008808011900f4400e845a03c1000020480321840c000000640900101c2e004091000d507c0c0e240f103002c254000d2884005030948100c0000b040c501180c0080d642d001000e0464010500c2011980009000340588120124000c0c25180c032031610461407440f03010114481841503405280c00100040082008029100803180c0e00c6d903590750384c500300c2c1c84076070000e445400403103034182d10a80c29084074405113002c0c211541c0903540e121101c20405107041004a000c40c403031021a0020400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 293200467 1250 293199217 293199223
    0xd0e040b060405010e0d050a150203090721120905030d0c0203060a141b04090f050703200d0e0c04090308010f05090606070b0402011809150e01150507060b04020d0c0e0f03 75
    0x1000000b120101040011417501d981001c00344840184080d2200703c4889c2c000d840741e0090344c8102c26000c04c441040d540c0b8000301c528595420000d291075280310b12864081106000403030002142800e101607913580d14400700e450007001901c0f5000045900a49000714a0140002508035225100510a0a03034601b5040c0e5850000f504103c039005520a60201114610041c0e40003085180002c201341c10031000d103c0c0207040101d41400000c1e1400c14401c4c43d603200b03242c540071044208541c0d03d0410900c2292a0000c0c11500039100c002e110380c2105d900b0640e207502031520f00314803e81da0b005055240103403104582d07039942c100ca07105095900c10089903440785010b807140c56070002d1710340351161503500050792120f1921010801c4a00d00b002c001c1040660354118207480266030f2100450075036540303804801c004081c06500003000c0c5c01c0b0702002180d4850b5019141d01c500401c03000074000e41d13110001d4120307400005040242629150b800e220150441c40d010528041a10300200360440f80700000d403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 293201717 1250 293200467 293200487
    0x3030906190902060423040920030f0706020120031b1812010c020d1704110316030b01050109090c080705030717090105151206041707050d0e040b06040501 68
    0x41c041d040d45500080d00c1c098000c1c01030140c02609455035a42c95800368501c0083e581030b003048810005940d0f0384c90b0704180c4244000d0903004002c2c06804c126005c4a20000c4143c8034140303a02d445905201032600100b44003030790041a00c2e4000042e0303006510020070354411080e8a00503118070500403c040840716121403109100501d506996507100340318101518500d413803006410415103010741141d01d1341548145403140d2250200c450758608450100e0300c118401024018003000540442c0c001545440042c00d907140c010103a480c102450348860503e00c68230750003518130110290042080d03503045000036001d01004001400042140350000d040d140c1e001d090301c0308001001000500041c42000c0c00b5201c1c0c000c1311060b011a080000489011348003d4540b43c003446100d00c601c0c2c0c6035180640191000c503503548058a92680ea544035401c40601e411000f600003407041000c800041c07c03e00c4400180030700394a0b211500442c1809000490721520001383c0500010801405160781211400d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 293202967 1250 293201717 293201731
    0x3111605040914030d090b06060406120b06091302040905010e04420f0b0f090a0c030b06030103050d0f0503090c0f0307080706080703051005180702070e07020c1203030906 75
    0x21610121038944502100542c10100c0070030300010603002400642c6406c84240213002d2440a455501c07070301c00b004914440d903c915408a20583c400c818900072580010400700030061895062152850102c5c1e03503103e004143c0c0c03104076800241404a0321b21441198054585004650701a2400e5030310703a000d004100010840340c10240e02400200300d501e0524409600403284640c81410f00200e11402074048601c4201000e820000368142e1030400741040d40040c10010541e41c40e0b0f884a214880041919035602001c0540b6011f070742809440d1000114000d501c110010b00d20344502200007070200400d03072102d07801c000040044c441440340000c2d20b01c140e034808940d514280b65010000910381000c2d41e01c40030032801390440015101e500024868410700041d2003d110b00e03074407034140e00410b440501449502c9074000000d24098a480221154086000e00407a41042d448090144015034202c40007c0140d0103403100202c0c030b0a101020a54900300d5000039421400d08481c05502d46170010140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 293204217 1250 293202967 293202971
    0x5130f03230c03070906081002070503040b0f040308030c0c010f0b0915180109150602010b0a031707170306040e070e01050d080d050115140c060a0f061703070311160504 74
    0x280305501c6042c4034000c0703010700007011a03180564500c00b0801820b8a84940b8000c1d00030191010710942960088030191907200c000785280900303042c16894035400c056030b11228448240804000112403800a500444c560079185407180041c4032201e0954a120080702052810310814080c9a214003801c10780041440d4004403110710040045140c054001e88803102c1074121000018014003641d101c2400f003108600c202d1040c3e82c03148010b0f070a840d80c041003550040703d4282d017000454054613224808021811050b85030880c5501d030058411403008150b42450030000512001d8501482404108450400980941841e10780c4445110805110740c90040001c0030000007002410412900c140b0301c0c20104200d01d586900042a07820050308035100440c0b0300c01c844c081000410f40c16101050820300c000d00c05540c500106401901400c1da1704020039464480114135150120300c5141d810075480015500c0750102e040040040c50100c0b0301083c142c00007010200c0150501480c00c069a03800d40700 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 293205467 1250 293204217 293204273
    0xd0b03030a0903060f0f1803080c120118020708070605150a0e0c1605030417101b030b01021011120a050903030711070f060507171321060c05130f03 65
    0x162409440c07491b0451503468900004080f0402c0b190a01c0c0c1040c0340a0395900c0b0150342d4411000029105206d501c1100018000041107405440d0100c8400391114502c0035040c48040d90742c000198100703981c111003007a12001042188424074600040d825401c9800d203c0304c030302e0640612038026020b042c22107928030008030000030001d07590010b80010ba10a0441c1c0d51540d82d291746001410b18400002d041d40282598604100036070300526401000c800d20388150b00100d03440a070003e0020004890550255105c4d09000912a100e03950411164104c0c9960750502d52002c000c3e078042c010841d01d061840c0ca8244a078043d000030640760b01c203015040003080810000c5000e458890150b119a40c5010041404034000d68030030080c0c8885403041c41000000c103640c0c1518811400350b00021500d000c5a108100070b402e036050281c40d002a905240e140c0382940310f0302c0360400d848080302c2840c08620000b03103507099191503904140003005000c401500050940e0b6500068001260212400001c0800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 293206717 1250 293205467 293205491
    0x3030c0b0a290a0512100b04110306041d0304081b0301020c0a030c11030a031d01030b09070c0201090b160201090611030708090f09150a05180403050a0203040f06050d0b03030a090306 80
    0x140c410180c50014001c0b40b00e501007540315540e9001b14100702c8812070420f915961389061078095003030107506900c1d01e181140e40e84000c0c03100030f00641100c00e04d840740070f601c941320302041800100302400307000c4040e00008803001101001444601d690310301982c4100586940d00070003156405406900d803400c0e4407041001e04002e0403280035241d05131360502844214a08041d001091042c8013000b03054055a50b050250055040314002400190003110b00c10014042e01d100d5a5541111171050400d00704441e100d0540c1d20141d0000b20034030000604400c018005d640e000420350008004600c0c15484250805165584900a5103002000050301150b030100c0d42c1d81e03000c10b4dc14513134805003c3e4042031a03c146100948540103001c036001c1d0028000c041503504041410401040c100d4002c3c43d41074660b6034044a003640255032a40440c0800d200220312615600d000e1801400280e8070251a019003400d444100d40e03846840b40d101e0b91040002d0007402d0b0308142e440c8202e0740c00010000300d4400c140 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 293207967 1250 293206717 293206729
    0x6190203070c0e040308360124031e0305040501050306040209040903020601090e03180d0507030b0108030304060c05181513030f060c080403140c070f03030c0b0a29 72
    0x1000602021005030040b40c50b048140a091180e8065500c81d1b40d282c5a140c110b1703200600c801d2a0300c10307243c074110642244038903801c00000c051403060000140c260114135101c140460440703044400c48009041081448614491001c007902074140411a101069602400d6407145104c5d05d41400000300020341c1c1781e40c465042d81d103c0c0384041c0060102c01e01602e0002c2d00c800d0240588801c05280c03011022000c0c50001c1900d203d00e11904050061010100420400d2003804904440038860b1180200000c0d40380750181d40240000781c002c64030ba0070185440c005503090410b0200801c00140311001005012035043e5484020a5074008840c0401c5042e2240500c10080300c0e45500ea4032080020401010180b182e0312140107220400036500c1d021002c0720701c610700b80c074090b0025040741044400c018114000300400c00d04138049031025030f42e820b902c0e910414290b00542c0441d0710001180c0c14040c3c20403002d548510240420005007a86110039120803002c40d5000801200a4460000c0d5441d15 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 293209217 1250 293207967 293207977
    0x10c12050912040b0a02010510080705040504020f0a080d1e0e0105030601020f060709030204060f05010c080c101118090108030409020c07090f0c11031c02300117070506190203 77
    0x200e40d0ba59a544500c0445220762003c0c0a43e0300661804001820380f580f2401d040b41034400340e2018000d50b911f00001c00c005048058800e80e400040003405141583d92076000310028203e040241030030510b00603016100203101c0164200c03405a55000407400361f80a1170300c0100c0102424160703102d48941c00101e140081c218102c0d006c611543c0c00b4440707030030b030404031900440c0c0c0b00300d906008a41e15507403201000e0115221f5070380843c24004803d40001c070014060035001c0c20040840f48100e1506140c8002e44000240691040c40300080103286182d0b0884800e81401c401e940f2046070b54902071a040d9a44242d110b422401c50703000c500c00c0c00e110000c1c072100d402401e400380b00b84019074030541c1400007000c490340c4141c0410150b80040442d0103011041d03549120715010840400540d0f4150300e006948810340d1020b8004580c0c100c12210b941c1c0310309460602ea0000f40d21a100c2d0b050038020516914000040c400560024a0070001c40c1d80b0b8070119410402d8581d0300006801e07095034260702d10300035 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 293210467 1250 293209217 293209243
    0x1080c12071d03150a091406040b0601090803030609160c0515090d020f030702130b040504030e041112150307030807050a0c05040e03190e12100509010c120509 70
    0xa0814450440c0d440104564001c0007240a0720020010204240e90f5070004488003a203101c00380300003a00e16585ea40071011080c002c0032003145202c81d802d58a4246007080710b003198840d1600092009559004d031042018000c40300007145541010030000324031200c01800e04c415203205413001000c0758416039040140076804405c452407c4c01e5013184503803403203040710b1344800380c4034105415050610019036400519440000f441ca031402603001e010015840b8581000b0480d00e941c108400e940381c1d03100e05445075019558082142140c1030400c0207461109404902c4130740280680d00d1000c42014401e6086407094290700c01116414011030305000d22640040c3c00725038040350400c24030002041c020341c090b22801c548c01100362100b0410046403810141007526520a11014040c040383d100c01d5801000c0380d05116814400840009507480b0b0940580d0407950454083e14190000c0d41c01019004401c1070001e001c0041814001004452041c649840254544010a039041c205100140c1482e603 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 293211717 1250 293210467 293210497
    0x20d090501091502090114031f15020706020d0203041202040605060c0303160306140919050a020a080a0504030e060715020a1d0d2004060f0602010c02120c070501080c 73
    0x52820414000d01880744161266403000400ca421403e50388203c500d403000584138030340b403a2010261007580303030001803841e01040e42c003010601a0807070b0403013810024454a140742903070b01a45d9400a00b02402503105c0c4d41558415a184400c02d40c0100985082c0c5408a450360361014a80c000174005e002290720040d0044d000050321600b00b8000300041d44128844030008100b031020403801c40c01c54209106407221a001f07040c000d5028544040c1030b0b6005070321031141c07562051809003020202ea100792450641c05500003a64100b2a8009242741c1d403000c590300b4104460328040c3c034043d1500c4803a24035640300d828006564810000c100d1300400095858030310464882c0900304028200403140710703a148030b10403180751031011740c0b074038202680c40658084018000b004c1d03045581e003580c0c1201e8180c1a8026102c5101150174114221104014803032540041115103c811004e03007041e56425501c200681c0400400c40303440400650f5208540782031801031039507500c01710207200e03d00849185008050b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 293212967 1250 293211717 293211731
    0xa0207051c020129030304060f02010905010c0f17130206071e08090a0e130b2206022206170a06030f0605010302010f0228030e0d1a180c13020d 63
    0x142c0c154486103100e50000c0340d20749407501048a00c82061601440302d1303850b5104010501c03030288a603035051140c0e00e56000201d41007900b941c03841c0c2501d94909002000502031800040c0f42a4007010f1a200b0846010781603040e410f100c0513800003525465070190050340c001682a0421442c2d180022070308106100c0e2031000b400518219005601c04603920b8820b621400f4049600900310710101e000303100e1400741c0340a00c4500d5550300e00722680103141d01d1003d24194100701c003140d5103e400d41300b800d04c541001a511035581071003000b00c4401c1d5101e10242041751100f8041c40750425803004042100000d45031103a680d803001c1030050402c17a08010140c102c4146010100203860b003005040e04d00c00d0700c500c030828440c08000c90303840040100d500b00f1a0344d00f41e140c4d182d68112441c800301090080c900818000300f0781020030800341c0f80041c100d03001c0e0120040c00c4800c004c03041d03106421947d031001404d03c0756000d0400035a5281404a441e1095440210841c000b2215504444078081007140038031031f003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 293214217 1250 293212967 293213023
    0xb0118031a0c0c07121514240604080c04060824040c0b070501150b131703090414041205131e080d090302040b04021201030803070e0a240809060a020705 67
    0x240180d0f800312104820968030904401040c06402040154010115401e541d200030480c07207424503080d1a2040148c0c1340085009031100c01c0180040c044a2008041680141041c4401c603107940e030050444d6008400c0d0451084518218040700060b0071050481a45590404420650659010f10070030f110005501c8100441900108030903e6031100841606035180c540d00100d00c10500ca900590700728040600c800840303111200d110316100e0f000c4070b00b04040329005c00c04441ca4064041c008990a00401c410404070850658050031180781c0039040c504e480b0200a108281400b51158030404000b440d00c001808003025802828014100c03440300000d440301030500c4040e400140e00440c1003080f08106410700d4000c0310084441801030f0507032a0302e56110b250064001812850030004500107d140c2d40d03031941d10b45000350034042001d25504060716106035800b4048a941000e210030281040150380010469a505c2451028050b0f52500646811400c041400b00405902c08811a0500030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 293215467 1250 293214217 293214239
    0xe0307120213050705030106140f040306051b040b09090601210e0c0301150302010804020303211501030c0c1b1710150e04030c1e0302010b0118031a0c0c07 68
    0x9500e009030b96020b00816004601410781da07007111504082032040004000e164032401d1050700700300f1004c91030340c1020b1425015074000d0380701d0391064442036220010701c0040700704d0801a0500c0d0301c1140d0b010b450a4503068041a80340282054113200f00303641d5000450a900030050103082e0902d90841c00c40c2d07440c10304a003600500582075090454800d400b03c400b042d060500c1100c9000320800c5206814900d10380c0112001d8500420882c1c06000503c4900c1c4840825480001c4002c0030100d8487c8510301140710010034001ca50303100781014100103d6074801c581014400380c4164100c0240309041c2e2020b2860410f4510035403240440c4980c248146110b0000030407003480c42c030528a010303c0043d0441c50400100c0e0140d000d641c210300020404200000d0043c1c02270315142c3c3c410146400c0121036400c4402c1e04091340601540076175150140003000e13603031103c1d4800d50026036654034a071860071350311440d122615112441c0300800401010451114600098524800550b8115140b19458450b0061 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 293216717 1250 293215467 293215499
    0x60f040e0d020d0e0604032307060e04050c09061204060219050d060b0712030f0b06070605041b15051b0316050c040c3204092003040506060904030e0307 67
    0x401801280c0c0041d0403144130304560780c64000c00070b056908050654540c845034211203500c56504104210b4000c40c00d0b07500384040d100803e03141e12181c501c1010801884190340004180d481d0b03703038040042c004540c1d11403059810705613121544141c2c641d2070b0f03d44900244a200b040d4130155207034800c05041c1c43c0e805402040e000c01094400e0003001c4d44c0d10020300b000c1c028414000c02140c200701c81004054031990205050072010b80000c20011031540124480b54040081543e080d1740300c2c0200002e115622069014800044a00500031071a110302400c85c3c03589542588101702c00000c6100c401c5140036480c40d20070035079006490392000d4541c200d90300c05484400c00c8890780500c88000141c2c1c901403250081d001402d0305c5220400b50351580b410445440c001020b5921301d584402404603c11a10103031000d007142440018a84244039001504e4190a07060100795080030020040043c0c0082045a0490808d80700d06155403100e240039244683c0c010292605845601d4002594949400c40c040d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 293217967 1250 293216717 293216743
    0xb090c07020307210f03030605100305010602010c0807020c12070b0c030408071a09270406200c0d050703050403061103040b060108070e010e01020a0602160204060e09070e060f040e 79
    0x2030105036031684c2d00a00c0314209180c5505800601302c030540441c201070b00a41c0464800e140020302141c0b0b40000508100d8000c0501c00000e0780c900060020507024031410131150707074506010341341d894141e100039680c0d0300d4140001d02402890005400d4040d042000d400600801c2d140c00c0c3e2685c80a800480e0f582e0010b02c00d402c1103100b002c2c0005420051070f034804074220350361008546001942c806002048030861080c420307441654402905a400003c00325000c1c501c600340200307584071604e040c2c0c04101126110401451070400845003842d800140359202c0201c1e50501684503c41c5040503207250045600141c81281056071004080c0300500041d80304911a1182c03070704a032a654011a208101101c8590109401c4501c8048039802452201c8040034144112504150260340d0365082c0d0300070024035041c8202a1210008501e02806110080c0c1040c8030744000514111010550358021407250908a04040010914a4650010100e000440603106010700d00011030b04c40d6541314800108 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 293219217 1250 293217967 293217973
    0x18061602010324120c03060c110606030730020a0b0c070906360c0905030f062205011112040c0b130504050a02070b0f100602030f04060e040b090c070203 67
    0x11040f106460558214140d02e14050741415400c01d040191003005501d000d46030340b151284008002007090180b880541080c3c0d4407044160381d4100907a2030240302400702032007900070a030b05204550803880c0c4c04032541038405a10361501907060050300845540c6001070740102c41c0c04400310323142480b07000501e801c0e108541101e20040d40e8012640880e010b500a944041c118807003251885000c085200300003240316200000148040d940d40c008440c0803103499000310780080400c2145140c14000041c461a4200c040d0241e40340c0380060500c42445020003c0008103030000107010300000358010b141690560b00e400740e80e071217003d10f030820b04c40044804a03000c500800e0081005002a0141c8007603c1d00340c102540041d052004000150000410703802e580f60f400c0c0700e074401166492000c540610506840d100c0c41d030801c410b140701d800030035810071810b541c0300300311030340380086900c08030340440e101450b2000741c0010803800078025000404c82d242c0d10541d800140800390407200004c05001e4422021 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 293220467 1250 293219217 293219231
    0xf080318030702131526010e010e19080715060e070e060f0702120106090b090a0b011e020f010c050a020c0f0a03020d1406070302030402040f05061005180616020103 72
    0x1825070380e100d1000c0080d0041e80407280c800d00c4610542010038844500303d0f080c40d4064a400941045802907284c2808000405c5042d10ba12a020b1180c40c03a060b02c000024000e402000700c3d0990b03103101c0031424801103140710301d5442c14850300c9401c0d2a40340c2d81c01170500b42058800005840540224019070184e40382c000b020400c40c0d409022441c3c48038a001c0c01c6d660400760150481e60762500915001d81e08030111074101d2a03002004c2c490303500070f010403980c00201d5651441c14003801e000001c00700302009141c11801c000907a04104010001c441d0812804040620960100d050076400b00e008075842d0300301407840300d00d15046409417081907080d608480310f02c159441004818050094125041440030764144054100700c40c0050388075010b0001d910260051159041c981a811101c0d900060390200c1804114075003402a003403040701050080c40309040c10030004030385402c0389100005000c0c002401c07000301c07404401d14092076140103241503107420b00303001c40a00e005150305013240001d2920341c0b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 293221717 1250 293220467 293220511
    0xa12030206061002031e0d0908040e0901050708010b0d0513050d1e0f08010e0a11070f170708030601030c180f03060c030501080a080702030a080d020d0b0a0b0706180f0803 75
    0xc2a652407400c440381d10541c9106d5403281c00303400d600070001e1b002c01c1e5440b0191a800b161600703000300020b0006000c440302601d0102a05421120090515010010382e80c004100c5010b8143c196007410f00a500001143d0b100d00440e51801c00341c0c04001451405685590108550444441d00c010302c5030440f0003a2030811000102c03004c503006d0b030ac1400410381c6d04005029030b00709095400e600c121145400603040d0341460398039189070003191007207070148a8100c0303800805c40041e041c9407030840c031020068284012907468103690f00005141c503041680e0b4081c00000a8820141d510071581ca5aa00014030340d150a00395040c440140415510320741040007001c102840b030720500d8100c130320322030150402c24a075698401041d8403501c0300381d078544191030b91708010a0042000309905204c004e401a40c030790701100f1800584626100321442405030390410000c8096003011144040e511080002d21480700380b44040c1311100b1104060f02c000345034840c034000c200c22000254092034102003d002c1c5010482 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 293222967 1250 293221717 293221723
    0x10209091513090f02120318030304060503010e13060f020a180501020a2a0603050a1a010807110304080d050702011205040510050405030d0e1b1503040f020a12030206061002 76
    0x812030350040d44400d840810b0611650248803018855071141100011940000d031404080c41d8a42c10190000100f41c59110010b200710740c011441a4040d50509250100207031071404144680d41f0804207050000e00700d2480000311140054fc40402040303c0c0001000a4000b500140c0401001c0361020b00400a290303072441102080b140164010605040959215074401300c0c4050b0410b0139840c0e0400f000704081d0103408800182549540c0007801c1c0c6451442d440c16a16441811600400c045881440c07170b034be009644c03950144403408d00f02040d1004032841407440c4903690002400d4021100c48c1000c00707034090002c02030b0038000d07a642e08803a00501c2c1c81c04200e842c241c40042059018220380e007000c0045402259002e401a0152414908a4107045e0b042c3e9044011060385904502500f0030340b0305514038100284c4109072048100138080300c6045000d80b002400141000e4082107915086503109040c86024180e5001080c860000c1850040d58038807040e54080e106141c26841d0158480c800 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 293224217 1250 293222967 293223001
    0x80a051c0615050301080a030f02031c0c080f1b09061b0705010e060f18040b1c0501112b0615110616020a060b010315080304030618120f030f090501020909 68
    0x350090440c54006039009e03560f1151200d1800150300050001d1100460b00e503103400180c1c00c1c40034001c5a0400a00d02c018074000005040210812054041c42500031740c6051546000f2202d450741d6544c3e800b160b001131418042c0560310180101541407054000e03001054020031241c0a80b104060603485008001d1f45000710341d1030301c81c0c4000a10840e0208558480a07d07960300015000040880003a00420765403400762031844104580c030f10842c008c0080034401c0c8a801c0050100071070814910307490398500382e0500c07030714031103406801ca001116400c0c0541c804801441c003a00025841110802c01600e00001071306140094081c000014141d20301e140c07801010341203a507000d000105c8032580c4030001411100551810107940f1800f940ca040a0b2410050180014200840d115072640c905142038810a681116561519000c002c0c0062140d419140d000c074210300b40303080c040503544012001410304a400d040d020742061145010f00906500070182d418041c1c0d0b445a1b1a500c08007007000140407 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 293225467 1250 293224217 293224229
    0x6060903050a060f09020402121f0515090a0801020c06042a0306150504060b07050c040b061c1116050c0a0302010e04090302010906092108070c080a051c0615050301 72
    0x451425100003450650084d05444d000000015455070b0030303008034040340c005100c096401c1c410001841a881c4003005501800502040341050840c00c0c40c0208440300031580340e030001e07282e01140b10055a9910b9501e078000e410240c0085448030002002039541d00419603068800000c6c400800103411841240a0b048a80c811441c021551850307460200400c6080120600c0d51010800410a6030740c9019110080001c04200c0e502c0ba44c2c0d5041c40e034184411250528480c0d403a01828008507260201a01c050404040c2d900865100750300d6994003802000c5030b803601c010310020b003180503440d0514a002c4814043c0d0f044980100c400c8041c40a030303010368040680840c80d0040041c1081c038058100d1050f00c2c8c460720011641a6036a41c80009499400c002102c0741c400301c01035880409880c3d15040c120340840c9c646041785080529001d09003404200c0060407010000401540f120300030401c0320294010030760b5032500c9800060030000107050a00400030300a81045800b150300307204009681c10790721 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 293226717 1250 293225467 293225473
    0x60303081e06010e04020702030105040c060e1f2d02030301180c020c1c020a0902120603030403150b1503090d08011403100e07030b0108060105010831050304180b03010606090305 78
    0x40c2d0750015180030000d840754a600903005c02034a401a1004e0081c20301551160b21001e01480c181079020341b0b410001d0f00034034002c10410901f100c5904070400060449480c6040c164801c440c3c034010b00014038601180f0070900364458030707007020480d40000114101d07003100041040d4064081c0d08030013554401c408600040e448001d55001c07a2030030b11641c40c50031410b040e161180520300e81c00300d4100c04250307004c3c0e4415a40807035001912414080f1450f44070324224003651407d41541e64101c88250ba8040d800502e9595100c603800035100c0e8000e02d490400c40510b2a82c491410500c0d459461a89089200000340180000039100000044c2041c2100008011b0880421842c04200040c055802c1030445482800030000101e5042251180a8032448018120130341c10310002414120000c1d107600c600301003a0096021115003146503807a4442e510f40303416040700840c10068554003030354001d41c040a8144d80c03600411a00b65200b0910390360180c0084c00f4055458105032111006c030301c000344c400e030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 293227967 1250 293226717 293226721
    0x3020304120e060d060e09012d090501020f030f04021002010e030406032f07050f210a020705090901060e0606070201050307140408071206150f050d1a070201060303081e 74
    0xa400380c5440842c289014181c1c50800e00584602c4050741c1e5030360b000c001c2d00401c1c102840f48004003030051010030308a42101880e40004000c640c8409a03440d410a030103196640380c1201001020340444500480507044541ca03408c022101524000040d60b08a10a0b0280184821400c1c018019035001003e010040d50905190607000e601420200307407241c1c0200110141059401c018004055062607100c50147c3c441c1003510b811898012180442001a402480803040802640340c1c1500c00c6010f4000306e40d02c2c1c00403582c042c0e14250803038000c50ba00c0300ea44010480441015401041126180c3c1900301040d11500281306161080e810041d00007042040001c43c194002c0c680e0030404241e0349152460555105406030529150740c1014000c180741c080101e06110b050301560740c0c014400f50381c605005142409101c00b9050710b215481c01541589440010b02c000145034406c10082c0909520503481d00c032400038000d16281c0030440100307602202017913100f01901b1070600e0320301507840180310903 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 293229217 1250 293227967 293228003
    0x807260601140d02041d0f120306030d0e0303120403030e160b030411010915050706061502070905060d0b040503091005251e030f020111070308060904030c0c030c030209060103020304 80
    0x360840001660010b849030031b0140020310101c00a400781c040300b0045c1c000b04c90038040450034820080c0c0542c0740900300f4418480b0607600420742c0402a641c508103081d10244290109007036001e60340000c814810210104024903030190002000040e10a00341c0388846910151403108500e40e02841c07010440a000140000705042440c2d0841c48050500480365940c8006005400e516491000000391002c600b00003000030710b0007214003400c00a84800428088000300a50302c3c1803034072039145602c0e1141c0201d00541c85001e080301030541c200c5000316591610b410015500c1e8840714005c7d00071251081c0d104a0907100340c0039100c80802c682002c4108100900c102e50f04454500029901c240010394401c88600315011011811072080d2a42d20100303d00c0f840107401c582d648402c0c1458410100110000241e010b07604c1d6038002000c0b15510701e10b0700d0301d040071180c9188810340200011690721010090200003021f150440348219865400341d550b50004405901041da0002c2c661481c12020100c2c0c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 293230467 1250 293229217 293229229
    0x7060504050c0303030c13060e010c030c03030b0a0303030e100b090c070302010f0f1b2610090e070821042c131407150810080726060114 60
    0x3041c010421a41c0740c461840c0024159481680d50b030940010024101c030f031103499080c2c400020101810108005221140044c084000e01400101004035114402c01054007ea00030041800f01034014010152a480e02400a007886034980700240315101462030742005501860703130482009401080151070b03c420880f00b5811102080b03042d075480703039001c123042400d41c81229940c07001860b011444000702c043e1070340c6e181500400c440070014512094001c8407403004980641f078a40c070030300b4551940c50501c0004039010a030880c5101d141000020004828001040c40503142d811041e5695010a40c102101404800c1350000a48000b40410400f24000310091401aa80c1c0c1844c4d00c10740005082e0003920ba48121a52000000c0c1d46021006020501c4c42c06243d000c8084001e2000608005c0c41c5490f08041084150401c00728000140e25100d800203900300520742c40d003c03602400e480e24403d407985201c111251400d0746108228440b0301e00700103000750481340e4000345c100c0c03403c01c04414044 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 293231717 1250 293230467 293230471
    0xe030f0a05130815151e0607020103230403141617071725080405040e0a05010c0f030509010b01080403030b01090e0906010512030a0219140610050a0807030305070605 73
    0x102d10b0300c220400245640305020130b4401c0040c511007000d251034009012210b14410513034403130081e14a803903607000c00c1e025410070703440104007101d50f00e444001030320040300030b80b103010f828800160600c0d240c036440c42210700106001d17501c00e484007d6244100c42804401e40107000150010305510f50341f03000810008640040d0941521502503c6c00e03419845a0420301c5c04210000302151000808100e5072520a84442903119604107040400440c1e40715240a07000702e01615109139502e41414501c1d2004001543c5601d50080082c08254607040c0041c00341640941c10340c0120381030030001650418184612054000140c4070310a1640707458504500900e16081d4039414490500004280d40d50102c1d402c034450418000200110760400080c0b00d000601551941980d5105006a052241e00891030302c1c2460551440d042da111110f041c40f6072141c1022116002600900c01070102030100402c4110580e030003500d14a802d55078070064155038014512003d000120188891b80c00100d29800483d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 293232967 1250 293231717 293231737
    0x605070314040507030507140108010902130e0702011b0e01050a03050c040906171504020d08030423011b211509050112030905040b100c0f060c0509040e030f0a05 71
    0x984030701c0101a0300e41010150340507a980e9209000070010800b040080030040c140e401c40b40309030f2140b13120001c0c1c4443c0041c09080001500410510508851500e1001c002e2801e07a040140900b0301680282c0201180f14695103000d16034030707505140a0144008892410042c1e40e80e81c0340204a02044008140c00713411041a50800c100001e520002c500030700c8090010421484002d00d85501d404e03103003070b0415560503000207845040101580d07070040e1003151a070f00811250303601c0d079462900c100345420320b02e2485401d0134000a1095004015480900504119500c9407241940c180e800c9d603000c4807401c0302c3c4860582d5018951070074400c1da040103420548071101e0124258840003094150b8030242c20030500015030266510a05130b2014044004200990b000c005080522021407500d06082c20072009020000041c481000301c0110034190954008100304103a100140c8020295480b0b1052640300b2818000301017960740d4040100c0d0602020481030350300e089402c0ea42602d030781c0c004034a01c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 293234217 1250 293232967 293232971
    0x110a080c0309071806090e0a050715030b0a0b0301030203060f060319030c060e15011d04030c080d0f020c0d1d090c12090a0314090f19050607080c1e060406050703 71
    0x50310f4091104d404480f5044a402040d05030070003d4100c12100351044522260380140201d002003a0041039600c10b8074001c03d241049912004429805001040d48007034001c2e00a890002d070408903400a141601e200702e050340c103561100d41a82c0f07c8410251051541504101d920031144910740382594030140c42820803200e10f003001c2c2c46200c00c503101400b03803018039040104909120035858042c00c0c09050085612900c1d280001d10482000344002d000070144017900383c02e8030500541c1815140480d071400002c3c0a81c01c100340d01c0b8000b94106501da102c403841440c000c243c0050240441a00070305444452400210300301081041807840641031403142c00040211050b4011540c82c003601c9442080018040c01189107401046c103030241010740646001030140810603a00c0d0fa81c0c9403455202100c0d84d60040300030308950100a251a800300d90301c0400043d04908201000000d855110181d905450701da14062401561404070082c6100702ca401c1100003030002265980003c0c0c2200c614500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 293235467 1250 293234217 293234219
    0x909020a0e0603160801060504080d03050601051b10050a09020f0607020607020a08010507091a19051c0527060f09010204030609050f2b1b080307080a110a080c030907 73
    0x2c601141e20070740700c1416404140d10408119174114040c5070050006185c820324180c944045036403178015180620742010346810114109030701c80d5003543c083c040c541d4018500d54010143c4150380d1883c00c4400c19003241880f00107134002d0744502c1420022034000e0020007068124000b0010607070301010701283c0c0b00405015607009611590194400307801c41e280001010304100340d0140040b003665210384440c0103440c106041e0301e42c1900654541c042c6508281542c0d01c8100307000d03a01c0d40210f03c4003200004010070f0b02c0344012626001103024202298081d01903d0130030758050405940d80600c83e40c1c03544000c012030001403049007001d600568000c00142065100c0d52004241c6548040a0719180e120803a460210741c0140100c0354025819003000140300490502540420758098148040c81054100b440c5d030000d0600e500c0f04031640c84a07007143c2e80e02d8030603000303011311078299080b100341c0345420003245c2d8403504a42140d00851144c1c90f100d500b6612111141e82036440101013214900840718 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 293236717 1250 293235467 293235469
    0x2090a060e0f011406090d022709030909090a0308130809040204030303060518040b0c070201050d020a030227031914010504140c0f0d1b080a05030409060501030504030909020a0e 78
    0xc407034081d0036520440841e40d4503011031021014107680c0c00034841c0004000c9503032182c0d204e004030041c203941501c19010a81c003081407900025420349000304c0d5411400100b000c1d114002c801005581c038220b55460b030380e4030b410032140e507a038000c580c00501061424011542141d04c040d002c20849108941c0700346000d2400300418140c1c1c000d0f910890100745c07104802d00081c9400810400c410b111101c0c1d00a40d850607441d1004040700c054141c50b20858006440819079100d0801c80e00d07901c00072041507680e0300c0b1051000700254041101d04001c008550a0004041c10510350701101c400001c0007090f056401e203403044924441070808a964030720b01c0d41d25545801d420700407148640e00480078891080120005030b030400c004031001c640300703044503280e980e003954414031303060000c64001854200c801c14201c054048078200b03401ca0f401c58800c810000c07042001c00401402958480305003403041e05d42c3d500056042d076000361402000308407048410302c40302050ba805460054070926003c145515410 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 293237967 1250 293236717 293236739
    0x305070602070302010801120b0711010b0d0b0610082806080105090601050405060f03120904020c0f0607121e15050d0803040b01060c120804110a180b04050108070302090a06 76
    0x3510240140c1c00010701001990703080035606004040110b10100c645405039038200c00c18600600300400e01c02940d00c041550002581701082e5200c014102d0b42d442e24042c02c04c1c25244008032005032040c00d03181d04103054188035540b07141c050a40720110740380b801000100d10030100f4030030010281c43c9544020000d20900240121405401200c002e090310f941407405200079a00c0003040580501200307a0418880e4500003031040040208001045e168a2840c0000300079215140c4030603624454030700c99511610000c80d20300e0045400c1d0702e80c8190f4081003420041501c1c100c641b41c2251032103094600429a076603402c1804c1031810143c0346010580c981001031022040480182e8032400080304010401c04512003d030301400c07160912079581c2c00503035964018420b00700544820044c005001c9810000c0704600c100103600001c0c04605010b03110085041d0620800d89104078507420140381140d030742001d200d224140d0b81039002500041d400c40d0288038510001500b424610740da51607000614a0001c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 293239217 1250 293237967 293237969
    0x60609020a0908010218090a140106080f220b04020a080105100617010b09011b1205070605161b05030903030f070c060215181f0204090c02030408070b090a030507 71
    0x440010389030552641c0c014400c2a00d900f00000d20fa1041248884d03440925503003260411040b50038801a81c1c5111004001d00781c017449004203401703140c00100e1080d4101500511070004482c41c01744680e02e42c1c2c08900407203500e10f0310302030050b01001220f0103e02280d0082e540640050001e0f290141d44070116800c486c4201ca03038144e41c16140e05c080c0700313190340950082922052001810750550400d1909021817180c100801d05001040701d0000c0a0f0346103202c480d1019401c49a10422604820805489948100c6040f18421725005c0010b07118560007003142118100c0fa80d0342c4440c201040719800f450715081c0030984e030601c024070010340c541c1d0b01080107041e0701c0030640c1d003e0348a10079458641841011508070304150340000c58124408000c81c030402d0360000182d0b0981111448071031400341040a140558020400212151201141c031034005008850410304200084140140201e03200d000f80d00424800d07421440e0704100c80060138010740000c1100034250500a5500e41c0e42d50710700241 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 293240467 1250 293239217 293239229
    0x1908011d0408120f011a030907090b0a0b0a08010e01050d240f1a18010b0316090e0a06032913030201110301030b07030c05090607020d11120309040e010207081806070606 74
    0x41d0390018031046c030340c81c5000600c0a0120710001d0441c11308951054540655005a82c1c880e5a02d103081c08459851030000c0005182d9926504d940c3c8202c032000802040090250b844101452000040c4609140642c251070070780204034500008040d00305007044c400e615210007000c42d1034040d15411610288901641d4100000c440e05030340140009000044455024000c0c3c3d100d9803400400c03640c0240c0003100d0f444442c2d44d0088a806011160980b12124a40c000122181c60034042003082c0034550b200c0c0c81628001c0314900710341c1550401c003440c0d806000348a010309003206404503544140d0220310a01e031a105c1c2c00045030760142240c1c03a0080340c000740c4c015910401c6000900c0b06440c4c15214803c81101c01e842d0141c90b103d0403101107102e620504400a0143c10013004403c2440312401e484481c43c44000d10000e007032079a08601c0340d0b413600900401c0707110b03902d0180d10303008400c414404c442d10345030712038840c41c188540000780c02c1d2020728101d032540d0014030400c80103001030001e110300340103810 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 293241717 1250 293240467 293240491
    0x1030f110406021c0201050124020304030b09010902040f0c02070b0c030705061303110a030e0d05071503091406060a030b070e030303041217010f09020a0306030510021908011d040812 80
    0xf80004e030703080201c0600381d4001d5900d004014480c480914041d92102c1c0d140a0f940600710190307010892039849150310250402c490102801408001900110035080c02220140581103840803270404541800b5020700151f48400c50030001005c03404007500380d0131400000c1d40c0c01d140c11030f2981410a00c04075100c6100f1891840340508140e0462403081c11090f0801c010b01d4900d007266000380c4a15983c141e1030b031113481a504050b0401000b000301101801145030801c0c226840d040014001e8070030b4000031200d14140300303241c5100d5440013500700d00c50300c801048a00050f1454a800080c3c0d80083c0580d001c210700c01c43d0180440d1400c00045000e544580c03244a0018070001d0700920107841e030030719a49030b0260140100b1049280b40045019543c90305001640c9403103da0041d40140880c3c0c0c4006d14a015490f010f0b084e10a0342e60240841c5103400c1070100da001c00755001250340d00001d0140d0810b0701d24203c40b24204562040ca0036611620900ca141e18016101e03c240c001810300304e42c0e003d100300f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 293242967 1250 293241717 293241733
    0xe1b04090c060e12030a170a0b030109030503090d080606030604110705240702010207121d03120310151b03090b0c0708010b04180b15060a0306081603080901030f11040602 75
    0x404e04024514481003100301960400d58186001400489090740d00000300e4180000325541090300d5020888451004000b04003128581c07401600381e8008480d0480c940c00b40346100d002850143c3c141901c6004000d0050b8a141d440c40c0420001386041c5100118046040c0b20315400104104503018402078500c68072241071850a50a60301074000a210308110390040c4040000185040201c11150300c407800c0401220340500d0500c80101c1041006030380c18410b00d80000d1084100303000840c0906000c2c000f050b00b0300d4131880341c0e01d50508031010f0040003030550010030410240e80405000003600c00d1400760080c41e614018000550030540c918219500110420880150240301d502c5c000c2d00180e03006d0100300051404070303540a90004015110030035480020f4100303c4c600c1c00079005103200501d21a1215441c4200074003c001b207004900c1715100ea541c41c8645280081c603240c044a5000c248e040c680080301c1c3c0110007602c0202036541c031440d01c885554102c0d95481c1d02a00281415900900c062 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 293244217 1250 293242967 293242969
    0x1061d010f05010507030f030504050c1804210503040f08090409060b030c0f0a1406190f08132004060b0417100207080301030b070c0204050412020f010e1b04090c060e 73
    0x7181482d4401814424108101400a50010364002202c0161b0900060a6407941426405c0c4040408a0707540a2501c0040c0c42c0d1000034594202d0003a0302480c5000007640c100e03030700001003008034440c07036004c1001400010000307024140f056031070354881d110040c102050000070805817400164200e540f562141040211400c0c00c1001c096450821100c010b0030b05200349c007040320100640035a1100040c1e8410340301f05600c0310411030317444000c0320903007010641195000501c8102c8015400d8002404e41d40403a0700e0500c0c202100e4413407604a00b250107401d0030120b241a060503000c40c2150026120400000d00b40307120300242004000118081000fa4030f0318660303508000501a550001501c14003100f80850a40d20549064035800b031010781c2151144002a0342551110b48001c0d44103050008000401150300c041070a22050b940031200d4403e80c3c600150300343c40e18621204d9041c3c0c0940240c0201c401d01c2224403030f0420015000040d012103d4032584400503080d0004070118101c2c5a4980c0c0d2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 293245467 1250 293244217 293244239
    0x1401050f011d010b04060e0303091905031519020a0c1a07090501020f0a02100903060614040e0c030a1b0512072607050103091a070206010501110a0c120501061d01 71
    0x59000100842c0c8541c103042e00202280118003443d400c04c00d40d40042c03c0c158070b040044404c21000107181401640c803034005d07403441c24154051301e800f0f40500a1200e90070410410a94026072011705010f4601c25013480f41c8000b90803403401314080101180304000441c603e29244109641c0c8003099090520f00b105d40601b6580b919444207045501c80c0c02c0c100000b82010039400711681d03045407801303c400c0c3c103903408540c54902508081d010300e1400c1400218240501c00d2030150034407e0741c040c031203214201c3c40580c585003418080c98140e00408101d100103030018000c0090f612240400d42c80e1142c60300d02085441c0c1d034101000c1c1c001d034842c1034188402034002d14580890701c40d10600e512828000031100c0e807920010701c102418941c482e4030031320412a020141d1464003e1503a01d68560b40380c690b000a54940b828030801c0d0102c1c0f40088507001840d070110781c1444450b00a000b541d80280b41215020080b515100e09846035540c3d8403001c100c3d0f4440443c08100c0d03814840e100070305075042c030003403240c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 293246717 1250 293245467 293245499
    0xb0702060709050a0519080d0509030d08071e03020c010207030c1e12230a05120609060f01050705030909091b010f1209030309020402030115110313121401050f01 71
    0xc2c4840804100a6a66140d107590256003055070311072048000120848295070040c1c11581c40c43c081d0b01c0c0103400295110b800b41424000031000c4503103082d212481952444419501900060280c0b10500000d40c0032202c074141560451030700520b4a00c954004908a0700039420840c0002c00d980000014001c0103400080303221311100500c0f050031419034032211801480804030080c40f481611007401c191006c03508141c9180d10350055603450242503002011a4002c1c1d101e401c000c42e0a0f80801c0d007505060041c944504405403420f13005d82c9a00e0b0040d00c6036084010102d401c0d00c010045410300717403100c0d20010300070060780b4001e214905880440c4a141c0318103009080c1000b5a490240b20416888008024188071403800060400f80e14181100501040d0001a420500000000030702041e0890b01d03c54000306590b60740c514480384a503e64aa101d007800b1141c0041242c4402e000200c6a5043c10503070324401c48043c4818018102c2860941c0c00480307032103046681c1040100588109889411 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 293247967 1250 293246717 293246731
    0x160204050f010b22050303070321060b0901050f0913091514061e040603030e030115030206030c13030606080601030b0610170a060e0a270c0b031e040b070206 69
    0x80c198108801044079005881c184104e01001e8981612540d0350b81c9100c0019200c0642500d5446419050207000d9001c820018a406180306400100844091260009603901480844c1c90003462400454658110480c00410108100010709042d5140c40d4080c6050f0902d100c0401c1c2d001e1a41042e0300000581000c140ca00c90404121076948005000f500741d1242e41200c1c580d5000310b51180318100c0b4031030401902e801034a02800881455000542114820001c900a10510f6030505408003e50310910000f50060010301c0402c2c2c0c1d8854000180c8258086010704101041e036a894a01c103541301d66100348801c0d0003440040c418002c010b44540d0740203500307403908a2240140107005140d01c421522080701540d100b03022075485001c1e904140b0090062410b100746ca8100780101c80c004144041404440d285070440840b00b01802d00e484100c46134101c24140c0c4168584400d0080b1944000d02d941070710004ca81014500f1440d0001d000d0040f070040e4218401c91900020207442c00402030304807 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 293249217 1250 293247967 293247991
    0x50402030a1a0303030c0d0c0903050307050a060605030f06010306051503030f0a0212160f032f07090507050d020c031215121914100e34050d140316020405 68
    0x5a110b0706c00044403040c4001c200c1c005000301e841c1c0030440f203074041a000202103010002d00034061000008403503c046000308010061980d569041554400d50b480c6000e2690300400010008a102a404668840e58003201203003e4680140004d04580c0480340c844152280865880f503a00d43c104040042c8103c084103451504501c82038a100743c2d51140001000c0c6001e001c881402c2601c90064001540007028040744440000110b000304010000c011103081c0c4280a000241d03d20316014a42c040c1c500c1d512841c1c0360502c40c2c0e012134040d500c180001d900900c006c0014207040605080024803d2804502280c500d0a4507010007943c2640203030142d48513800040c0014050300c0c4889446000765000d62514020046100854141406070b84d00401e9240b42035241029680085581005030314003080300000c119a802d100000724040900314902c1444941c070910850034101401101c160051042e842c12018009405185901000000c901043c100e0300b844118101805403a401c8a920025 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 293250467 1250 293249217 293249221
    0x4030b1005220b090c0406140a0e120c060f0c010509011e090c0509010e0105100801060f08190e10141b0304020612130b0601030903020c100504050402030a1a030303 72
    0x92070100e000b0701000302400311485920301c02c1115030300c55502e002d005805104207280000702120381380c0081c4a8403020411854107a400c00b4488821201000240d85610a07004540002d0000001111500780114441e80000f0b8440b6601c2c0c00282c0340040e0302c40c41984e961503801512509451024180110680c1020050301030306c144035030080801c81d6000e0380003480450504080b10480f4459002e190422140800070442c041c00d0700701c041c16034038107503441c003054402d06c0c5044440c0ca40034440c0c0c40020b882e80c012150318911405080e5040f0003400d81e40d00c0c2c2007041e8407229040303994103803080d00503512140480e00000c6281c0520750b0a420380c040118514038114040c4905649819807600c40c00e000000004c08541c0c41d001070f200480c03441c040c043d005240c032003005045036900e0071040da81c103070718040026400e61003030045001d210ba1603805822907800313020a2041c00c800c00e603044401d005050001095030b8407188050351041000d100c02050700e26400000c222040e600a040c4ca000b40c0040003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 293251717 1250 293250467 293250469
    0x9090e1f02070c090e0303101d01090b060d020d05010501090509040f02010c0201050d0f090c0602121204051905150a1a040902033309011b050d0f02040603050f0a061202010507050a120504030b1005 86
    0x85050440b04001000704511490000042c107510401c01f1100c1c02c2407010602d00c80081c400c0e840754b41030b42c1007a2649075403141c42d00100b000020f0101c60042c440009101c07100c0043d48580b20088200388181019418542d1141e2a28240c0d050800074845907595150701000b0b12103503200e81030091920b40050300303452005100908080c0300b80740040201030034030340102e810030608100000c5e00d00555035042c0d6564006140c5140c036035a00140752644160703501c0100d000f9000c588075496898147d2111030400e040703210f00788000f42480110580c1e0600440c80400380c43c51200c00490502e0b854030ba0400b2200d0003085000c141ca102c06009110326130300d0040b07040300c20845801500100001800c106480c1e9002d00d0b41d00d009441020080c0c8281800440c0024a4903010b822260040c40450580c000b503a6518100808541c868415030300002d000c4210308025502500041520070b0180040d03500301c0800340c941e1710102c00d02d413a112001920000341002400350640c0d490340c008485004250044d49090 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 293252967 1250 293251717 293251769
    0x207061406010917030c1203011a0421020a0503060a09061d0703031803320f1f020f040e0601080106020c21160609090e1f02070c090e030310 62
    0x20144054951500607104d082041c00c1041e40d0030065071104654528024000300e10041d08207204540c44a0705900f401d4500101450036a4251000d0320b480c000402c00d42681c0c000600c154000030f03a00f00003503140100f00c1da2818030006203d50140c00000c03c1009180c54800300b150411140d07880d00701d4040684400140313001ca851402c5a4141ca4501d1610340e000c08600c0c0d51240301d034001000d10300440c4c0039048907641d90580764038026462500e081401c00011140b0f0f00e5240d454284641034000780e6100440351410301900d0780c100000d210050402003002c48040f2903910940003111349808035400c12101d503038451885400f51049201a04241e07a04501141c0700c1540d0b4244a16040342e010807100d43d90604201000c144e00c020900c2c040b9065991902414504030b6000f003404190070040c406220340000140040c5400c07500c4c01680710b504d5246c3c0c1480003908448811520f01c0b031151400520848075004d80a07044802d50061992400e01c0e60b0060012001c0364001200090306502c000320200ea05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 293254217 1250 293252967 293252969
    0x5060f09040c03030f110d0221130603020c0a0203010509030405190311010c3002060c0c07150507051b0a06031b030c0201060f0807080606010e1e060403080c0102070614060109 77
    0x50b08040c428640c6405c0103840c000300c1c0140851407072189040035180281d0005040d01c003400322501782c03a02e06108030b010080c1c41c400d0700c418454400700100c003000100d1090740200710064184003036808090b0f60340c1c0007900350f55090301e40350385e10750000c2003c1c4050b181c40036074002c8002c4842c49286850f451b50f5294030095036800052814000001005814440b54000700e0b09010080a041902c001c085000b462004c07014400d64001403140c10002112192000100c69003902c1e401c00400c042c5180c260a03500100103140c44c101001014844d110005004105180060303074401c000808800103407050003c82251680110b0800d0308001c500b80e0540c11314690310f1000d1909281c0032682544855003640074207241c1c5e0000011050b0a000020b8001000c1401c00030f82c0d01d04c0f8141d840c50b849620044964000c000c950a43c0301c1803c41d08000441082c00a800d44508081c03c081e04065513602c2c1d03082e180e080b00502c0c8220b42d40002d40e0408108461245e01c07442c1d01149a210850f041000c0001e01140742c03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 293255467 1250 293254217 293254223
    0x16030e0d03020f0f030f040b070207060e0906151b0f0d09050409050a0507060f11070b03061e0301050c0406020f070b0f0706110706020a0810060c061e06060305060f09040c03 76
    0x1c002001c2c040344881508543c1c4840c0304c40c00050f42d90800c1404041810411070381a0b40402050021818051001c100340302103a009549098007101014200301c074542d800350626911400040003c40c0000451003c0d12003004468920101e442c0c2404007a81882000028031040ea0803d04444140a4022090109894094034001445400c9141852401d554820050410300c154800060415440242415001202da032290a0319440b2101d90b42c0c0c404660240108003281131000607600d062070140c40c6201c0b844502e903c0c15000349100440d0842e074080d00d144200860010303080c44184c2e01041400c880542103401401141d150103190340d06401160500c078407603d0006000401d00015402080b0000141e01c1070a0b41d4407400c0c94090f00a500806140f400b10b44500e000814095814006000b00d588903101c1c0030040310b00b60b480500800481c02d140d0138451049044515003a524450f1740060101e548001505040c0b2108102c0340c100c0302380a0030f2041c0404004c00c400188007180302800c03a54 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 293256717 1250 293255467 293255471
    0xd09140d0809150a180503041805040b01050d020a0906060203041d0603061801020409020d060f0501020a0f1b0312030c0e030f12030403050912101802060901111207030816030e0d03 79
    0x56001c00e44000e002c0132420708109410145102d02400030120060045403010f027451080303401500340711011741d00129000342400040d40300401003400d1400205068a01c0102000e401a403070794600c4003101e645030000001680003240620181040600340743c11600c41160700c1403145003000000342e0701d01005012a41100502c02e0708034880c04250103550140040810564440380c403825040300510341445024614928020300041a50010481c2002c4e00d8201820040868a0f070b1527850344480d059442004003214541c2c00004541000941c2da8125003550300481d40c3e41c03402e1001450300d4a52a5441d100303410440715030081460000303c2d0990301c034511160503102d5a81c3e00f0300741c600f0f0054042090300054101c4491504d440045101c07076540c5240c880400000b441e40b84644400c1109001c002d401040401074200302c0e40c001d11044540c81030f200229003040110302618020f03078100000c00c40c0411360700000c0c440320039507400810a50140074541001820324401c0303031035030b2000312420382c4007456 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 293257967 1250 293256717 293256721
    0x80d110f011107020f01110a06090c030c030f230c01180506070c090e030307050702131d010b010806060306010915141c0b0a03080d020c01020d09140d080915 69
    0x11005012019a8510240003002031542007480c2c030b10b00360b10402e0b00b2032142e240b810b04500c403580601e07070f041c3d41510010000c1050a03107a0781e412004000c428002c0e04e40c1c00c240c0d40000300203036003906444065403003048503410003002441c04581c00143d8041721364841c42140280300c0042c000040303018215200b480e00484c2071304a485180c2c44014030360802900060005000001d0041500c10b580c100c2d010300307a04200d44204440c4080e10f900042ea0841c0c0000c07410400702d005441d00c2e4001340c4022000e10000035903903408180c032460f10700b03003881c1140d0541d458103020300541d0b0b00300d40c80c11380c445001e6442034030714605040000c100f1500c0b40106c40802040d00a452032482c0300d040c005d10700c941c2c000c266a540b80d03008000052090180340c5844c513070130309084171704020381050b0071940101c9070b2001207581050680101d60000c1d420203006240070359424001c2040c0261280200d5003c280a40710f0200036076071080415007441d18005290051056090034021440c100207141e01124507415200a199 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 293259217 1250 293257967 293257997
    0x70602070609120809160b2104140106050d0213051312200a0c0501271409060306100303080402060d050f06101b0206070809060f0301030501050709080d 67
    0xd02031240040d10107403600003607600f004100b031000b402001013034644080b95074581c0e0710380faa43d84a003507503011800c1d54860b040004181801c040c14024240c000302514600380060603041c410707011101651141090070700000c10410a102d03070000b9201c203030780e5882c6481c0c0c55004908001000290303600219aaa400202d80300310032044101e44a070b1041068210300040d42d80284050010000114400358103007484e12b41240c0005c04185880d03024000c1d0320700e00c4c54840152140e441c140300701441011143e654000c501684c01c900405002c40c1d1b61078060f04c1c04c03080103015980344020b01d000d00a038000b50900c02130700109001c0e1000ca0340d0504d071505032542d5a101154243c0180456000500d0800060220605071060200e00c14401a107642d5103800410a003214405c40f0b8601ca0013501459900204c0981016001800d0b16409505154038141842c1c0c00324480d54002500391880001c00320040c01089401c6c040e580e00922140790400486007454007041d100c500c00da1096041c021510141c4002c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 293260467 1250 293259217 293259221
    0x1e050c130e03040605120604050103020306040f03090b07080d05010803070b010312140307170c1603030b0619020312130c05040c030b1201060611030a0503070503040606050a0909061a03060c0706 85
    0x681d2054041c0c0c0c2d00ca5036690b0014040d5080410349058246110001600341e080c08e00c2824103c036001801032480740c480351510358070319000f04410b5080004c400c4011035000304210040c40b6251040e0206980c070b00100d01c2d00000c48070b042e0003d6050b03400400120300841c2c41d840c03540781900d8200a04460522442c541a207181d0608880544118408410003900300d42040480e00c9412845074400869503c80d59901c0f11032189018006540301c5056049011a2085e40050741d608030140000349086440440d88080000700f11200005901c002010b42100c846080307699045030396000301040f400d0031039856890704c1502c0d00580307007d6031352916038040c542d10a030807034814144050641720070b201c0030b2140907005e864140603850100e0600c06004152000020498020140d65615941182c90f0703038400303c81c107a0002e03205843c0d81c0c2e01c84201103615990180302c2c0c0001d0088110008070611245062005c6e1000e0998a031117150f507013264203541d900e000c100320f903100c910007030115610511440c1c5100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 293261717 1250 293260467 293260481
    0x306061e040501030b04050c0406230102011d0102040f090504051f02090d050105060414100e071205090102030f090c09060118170f0115140d0303271e050c13 69
    0x40e100d400c02e4000020b1014000200d400340d4040d505540000302c440c01404281c032100d11410b502c50005504046010510001506401e40d0520020a000089800c035502861814154000302e0350700280400c0070b0507101e20124010110008140140d00e0031341c984a86030f207081c40418141d104d15080b225a800703155411190320083c0140144541100380c10018020401141d03100d01aa25010049180e80301598410b44100c0070180e81c61481030070540250404007014221400b48622a14126000002d500032a4030540c000300005840c1c0c98101060440d002010300640c00ca5085188000c2c09a100d42142591010f000c0c00c03c01059244009400c80c1d84030598004220321220001c11031071102c01280700c183c2544400d0007406101410340d01440d02440c94030507070140e60341d80103606c03010307003401d440c24446580039040004100c00041d11031110149498070310003680744602015000c111001020f01e17840303690001d40105110069071445e586100403000144a445151140301030381c0300d540c000b21 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 293262967 1250 293261717 293261719
    0x90b0d0b12010b240415020304050319030f090b220b0f09030d18090f090c06030902130c3e1b04090b060f0d060e2401050306061e 57
    0xe0318242401ca64001c0801d401002c1c41070b50400280740c0c0c4090702400c0413480d040943d007507a151504e4800d4900020407403032020303002d5000070b10002a0b140d0702070028610729070071007000d14042002403800828184041151409200d410001441190101400c0c1c94035401c03188144001c040c05a1220000c0c40c00303580c8000340e005000a019a14015410702401040409400300c0c0d41304801d000c026204050035004032856a03176004420080502990000b0403000f507003032130025142050303807074800c10381260b03401410200341c0300c172428000c504140800b00034131051000200480680c03500c00070240120484990384640200849170910942d84224182d8a034451444040c80b1444c1d03102640c9400d084000800b0501d1101d030264110b007841e00078110202e034418503001841da1514100300008002c0031200341c1000542d0f1004002801d1449511440c2c23041c2c80043c440022131424001607482200c081b1401c04d4010741c01005543c0f40040c807580c11803070031213440c10800480b048001000512070741103 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 293264217 1250 293262967 293262979
    0x6090206040602071a0301060e010c03090302060304080a120c051b03040e04111504050105090d11220e01020721140a030c1d0906060904020d091406070906090b0d0b 72
    0x40e9143d0000303401000c48001207003400c14000900b0081c00113020900c07907500070800514403040550701c101140e00c48144642403410056840e50081a200c0e001100d0407181107400013410616150002501c43d000905141e00b484041c001d6a001045801000c0c400a000041d01203580413850f418401d840c06059280380c081003500d05418000e1001030681da159004030110400000845102012070301501c1060f180c207450f000040c0140441280480700c00d0380d03503400342c9803c010183e88501ca040742c0d0a410f400e000c201d080800c421441265508040320707589a204008030000507101c4c150050380c8154803004078215040c00364041c0d55082c1015800c4014000c0042c0ac1107000e038042c3d01c172081145003a590880081c0361451503a11114008050b1070b4041c0d54400022804e1506500600d0980070180015041c0741000507003005803800e16200301c906000021403170044600c02c210044d84080c191070000c0140e4035244001d0200c245034010305064280c00610410099000c1d008284c1040000c0c00d4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 293265467 1250 293264217 293264219
    0x17060604170705090708130305030c040b0c0a02040510030c090506010c080d1a0a0e0a09031b0302010b0f04020f04171e0606010f090b0f0705120a050c0c0913020d0609020604 76
    0x580d5220402c038080c0301c1c441d00b50303940032a503160700c41c9403d5841880752003008400d03042a40c90541381794000038440f24036400d0401010a5510a0740c0260442c1c440e040c008009a5045104002c01d46000829108000228450070804501c07402074108c00c9030b04440c0f00050503143c0200407101811007040281034540c1c0029558040d15490b4031007008244880c0d821801442c0e07a0040046052052040d450030b04030318004100880e001e44e0210380128420305110324540c084c80100036a81c01e00090030fa000d42d6464500280504082624402c81041140d00b14a000b851030b0803503005008038040d83e50b0200a01c80350454440082088170400103890007040d40d0a010008400c1d03485102310391450009141981c12101c2c1401038001d030041d02c3c84180320f581409182a008071140d086a101501c1c0b07481044003070324100036914020601e1400381d944042e42c2c0d40d54001c58514140c0c519030405e028198180400c421400d501440340d44556040340c10607107107400c90034440090000d01a02075404000090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 293266717 1250 293265467 293265509
    0x912040312020606060a08070305090c21060a091a07030b15030402010f020c03070501141b0303010312080108060a050a0209030d0201020310140d170d0606030b010e060a17060604 78
    0x8441d0600c82a01c0c1c0c01c55505960358070034050107014805070800440d20040120752081c0c0650416503110305074400320b41500041c0d40000340c01513070308002d0141e02c416500482d17a48041c01d000c003680c000340041c014090320300c05075074200d4005004840415840f503a600402e150620980221046080081c541c4100d0070f0030580042655000b503030100d001c5241c900c014041240003003542d5520b0303480200903010503464000151420140880d0740404541e00f003200606000c0c02d00e1440075408180001180c5a40c15072600c040004190140c407003d001c503440c01003164030000524958420700d168030200d420380364510500c0c0a4001c83d10070980c9070281103225590700c0d0381503015610503400035072114001d031303940c080c0792941e02d003840069034108449820304404a031500c429040b0888040710181d1078503400815030400c6420640181c40000d499040f44000e83d0387c0300c1a03840311000e0488100b4078018503254041d182c0030703010f00b401150854820020710701e503864800343c1e001058188070541081080030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 293267967 1250 293266717 293266733
    0x160903050d0e0d060614040506010c170a11030c060108121305041d0105040308071b02010804021c0c030b010e010e0f0402040e10060909051c05030a050622020a090605160201030509120403 82
    0x3500c107d000c2da203080d0002d81958031400c000302080d40c1200c0150701c0c1e41095901c203803081d84803030b406500b8440d082c4169624100200002d10701080402c01511142d41842d008034142801034809020000e170501c888141480700e02a918200c44084800145001c003100540c41a60303001c98101c0e0040d442c0004020034150052841072285100c1c1c0e488480c0ca40749545480a240c206100183c0060102000140141009100342045191603541a0a00e4105555800810039240c00c21111003010314010040c191780d07621180e000d4892521081c03071518100d024405000700c02007010b4810754a50165903040601440000b00b0b081d40d0b4031041c0509522100010058101d1443c1110750b403140300c546c0808085074014000400c02c46a8489107180c4034803807010080c11000e40840e6001e07002422013020b50741d0503004165a00c541c0200580c64001c8070002a01d1450558440418400c04100581e4481c00036040e14520a9090070001070b10b460b0b188107146089001034241005040000300402402085 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 293269217 1250 293267967 293267999
    0x60303030c0e0604060507110f10020d26130c03080307020102090a090209010c0209100b1209060604152601020304050a02091509040f0609060f05160903050d0e0d0606 73
    0x15181d003941860b4181c00d0100354412440340800084060080c500055211841c010008000500c2542900364400020b080505203840040159015048500a16403c9080d81ea0b41c80f0368080c0030f04900b40040080c05500c0c8000380110341c0c44455034400c00c00c11a415074208085d507008102a612450303c1c48001e4000c0d07120000f000c1c4100044080010150068022580444e0040c0e51b0400c0741e480682c00d106c040b50003e03011000c8400855000b0400300402c101524600006524460950506143d0740b42040c03000b41c5a81c0c060740c00d0007000e01c100d0500004040446501c0324010a0701480e900700301841c403640c950804800d5000005010600c20b0020701503414a001f1562584503856510025501a416140a0703030803498403000200410b03d029a901c01e02401004007050f1100596601803c441041484103165130350740080c041c040e1241c206840040303885080118100e411a00c07a66640c1110054a1080000c005d91401c03d6445411040300c8117940541300380b211540b20100307410001030b1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 293270467 1250 293269217 293269241
    0x1005040c06110105010821070605100501110c010c0b0a0e060115020d050c10020a05040503011415010201060506090405060114030705030103031b1e05120408010209041407090e130606030303 83
    0x1003510041d031801041c41013904854084004040300002600188140036044482c10b2481c0c100740540c10100d00b29008071441080400750050740ca41c01c0500141903200d201c000e10090380d10024414225903000761a1821711500310a01020f20342d1450800320180c00f40c224401103030301880b00001080720315209004400d8905400b82d0701c40c1044828111076034010b0034511200c95000f89103500d80740005074001c0101c03034058034129103000c0d100c2d4042402e55404030910000c0d9100e003801c01c83c00f0402090f440a1480091000b4007240707142a000480c14027920f07807524804c4d075955020a225a000c1c006900c1c220880a907401d0b26454038950142194209110540125084001071101c0314072030100e00b055194041c2070105000a03001c00140803000802c0c007140c0c144601380d00c0d0350041d803a1101030002003942c2c03000036035101c8985090005442041c40013802001030b01040c0240305420103a00ca068030078902c110142c90b40c0d202402c516180503c880a08007500e00000403042c0b42d03140d00040d0503424 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 293271717 1250 293270467 293270477
    0x30504081e1b0303060a150210050106080403030f020a051e0403050f0a03030609060302100f02151612060e0f090304051e010e090105100e190609060f170402121005040c06 75
    0x6240d80360b640c03240b00031030342c681d44919401024001250400800d0784c00911910403980014100d01003201121000e800800116080078100410140c1c14082c0710801e1090348429800d1541c032001c080c000e405680807081c03045000111414800404100f503900840d04001218400304400d0078058540c40ca003401600017a04003100810f141005004030b0084035800341200750f2068a5020071180200111080000c5005d804a0710708612084032200d80a013020290413045010b48403000f40c40d42e00c00b4400300c603526090030020402203d1b500761041c1c1c40041e2660708407440d07a40a107103e04600c151381201d58018195010030140c1e0701c2944240d01e181fa400c2c4c0312900aa0a6401040b513810000d100d240d912807140d082c01c68850380301c0c038008202c10101816a070010f050300c0d24141c1035070390160001000505016401c10409910400c0d052a05526050210444000c03a020b4110b59000400c040d008996141d01540344010030400c0345140e0210307031010450750400c0c1c548040d00714010322072080020 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 293272967 1250 293271717 293271757
    0x310140114090705030402041503030905010f03060b1b0703120e090f040b0a0b03070b0c06100b040b0904050709180b0906030d0219030207051302040f0f05090403030504081e 76
    0x8149100d8040301401c000b0506081076486800c00c807100e510080049030407507140d20b0780c02c00144040d607100d4084c41c4262942c0d507906052038001845a560203502d00201070810204000c1101100e04481d0644810190070000848524006103400c00c039500081c1240c02000340c0c2e8800359403044c84540036980890b5030b40310940f9207494a1820000c19500642400070003804070b640002682d1100e801c1241c0507082d62411544c8200071080790300010500b48040d0484010007030040811860280171b00401c51600f400c16040283c0d10030140914010140950303a2171003c9800103014600000040503944440c41c203849132100c4135005008100400c0b8040e07000034000c1104c6180201c1e12554100f1207030300600ba01c82c0d20182c503a4980030b0038075054065008a10340401c03141c03180588400c1074240820302598561508400c00302e08540707035200e98040041c281c1c00340940c5c0d44038803002c1c1d04103800d4607000c10340e6200c030700f00035900b807190701811129856448a01c1e1000b51010019082c06039400c00644018 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 293274217 1250 293272967 293272979
    0xc030207020f0d050f0a03050d06090629090a060210050f1e0a060b0a020604030f0203070803070e0a05041d1504080714010e0109230706080705070201020c03101401 72
    0x2a004240c4001d520030b20115000e00c03542030091000035050b01600c102c4031802148592035040460b00c071019400100d00080701c3d00c401e1b807140681c600030300582100f00481460500e0089043d11908402782c140c1c290715400503c030390070500540710000401083e0001d07081e920f48020750f80c1c40c0c80440d60741d8801d00381000035009030b1081038074900c10749a070f144000c500c41c1c031802002c0c421003005219900240d41d80d03c010807070000c0301c80030f06181c40c0650000c1955090070b04014102a01e41001e210441d0300c100041d0001603c0b040a990304030b2098100b90494203107410004203d14002d801990304985080b00304078907a2500002c032980006800103a615558202e5240f0400c4403080f20064a501c60810200001680d4480316400c0d41041c03000001d010103c0b0480b15096039000c3c1c409507204549a15018501800c02400906181c0c644000701100340c50898081c240b5103006282d10700703122000c1801c1055900030f000340000035400030190f44421813114111001404207540a06500c80008004501 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 293275467 1250 293274217 293274221
    0x81b060c0c1005060109090b4b010c0305070201020109050a06021b0a081207231305093102060304050318012c04090605040f0303180209041203140c0703030c03 70
    0x58130069407203e80050400d100d00011380b100c101c4c1560043d800c800501c902c80281c0682030008903048258950350b034031a4061a404510b640c0741100741103c070fa4098643e60780c21001205110b94542005501c5d260b1900040c0c0c010016881c0141c00390141611203400c101c5140d00030048104402503520a0b14800b482d2140e40fa501c0040040a505040100e900c1c140190048a580145240350000010200080b010a05450542000b0b00301c03038003080c1000000e010084e208040c0c0801d60302505140b80011010801c1c9030300d050040d1910440042c003410390140304c802031403400c0c3c002c1c1110b41c0e079003803a20f403a03981c07a13200301c16107051210305140401d900d40c4200c00c40400310143c0041e04130350866680e409080381c101c580f2116030140d80c9030030100004101340100d51046010f062026401206400c000d0190750740c449424007403101002d48003005035540f440d50790b04550444140002505c0101098000f020a03040b04801078080e0343c00c01c803410b552103000300080c81c0710340d600380410380c0180c0c01501 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 293276717 1250 293275467 293275471
    0x402030f0d021f110d0207110612060d080408011103011505070b010b0307020c040c0203030604050a1506080c07080304140705010504031208060312160c0e060a03081b060c0c1005 78
    0x41e0080d09881d003c0c007070400440200c0c04011440040c10803890359040f21180e019900364841d080d00401d8440901c40904c00340d03031030454150385480c904004d040380113010303c80041c640d902c0750004000038400d110706082518080d007200c8000300003081403420000d0158109129020316a0300205c14407400c0c503c540140c903869944020200b0507a428240c8842a907040100748804500c10194403600036500c42c060803807240e01030f80140d5520305221003440b00707880c0000c4c003180c0040d0402104494101d12540c0710011980c3c185030036003154840b8003d900c50b41c80341680142c000034001c0280320030f014141720610703495440401210340c00b170380d81e400547d014015032102401c503140c1170303d208140c0c4e80540251236019a0007400e44407104072108003d20319400c0710b0724482505c0c10f070b4107000c02005000c00303064000e41181821500d03136107040740004203400e5050000901688001c0b510940800d0b1078840c24014480d0310b0705850031850035541510715a003158490000038450304dc0c0840724050790b84103080c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 293277967 1250 293276717 293276743
    0x3130c0f230427030c020303040b0705010533010e0d08091201150317070b0108010605030708030c030d020901050f07060f05241c060f020a2307060b0f06030702060402030f 75
    0x140f60300321410100c072003092081025024420001c58110041c5d8090004001810300e0750311031030300c5030500d007080c03400c4801c0108880c034842044070030103803a0000d4110104441ca42419001188404030380100c034000020181940c0080490480070204504000509034040301a5182c91948041540b21800d844c007482e440e101c1e100e4400428008100603250680843c0b401c0981e0380d181c0308051361040900071090b4071034010340e55600006e00451909000c014000c100103070023142000b40c0345006603120301c101410b2031116540007400c04074590280c01551019405058040c0e03c8107140c0c10540e02410503801000581c514103000039100c807201501c07540c01200c580c16211104183c442c284004812480c01c0b001444003041e8087c1d00003170007130050128240300440d01581301d600032540603001026040c2c22009071b00507101e120b0364907000c900c1514803058002c140880e02080c9500403400c812398004030f05030000c0000040081c0140c001411070302aa1094040340e03d20480040c0725911040c03400c0f001 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 293279217 1250 293277967 293278001
    0x1e040606031e03210e030d060e1e0f0a06080d02030c010501090603080a0e030c040204031a090d02030d0b0415080d1403011401143901060b03130c0f2304 67
    0x4201d070b200704121440780321510802c002860100081c175440c030395048510f612007496141d4805002c0c0c3c5102c800c500d50800321004203804042da0810001012140050200c0e13a01500c050000300d0b441d42c250080300c01003a500b026541040500c6400a4a9510008400301e140d030070070000181440d082d204030011030f90001a042d051408600d0200e40c112000b101c0309a140c420703850309440030ba40741e10062004610941d02180c4421014100c14190040101900410b403c00010032843c41c1d004002c5694001e45442d0020b00d10012400050007049000d0a00d036080c800204040b801c03a000249040f6401200d48510040440002104100f84824001d82004074520300c8440c10b00d500074030b40c01039849400114030b030038803031035a81c403030456209100e44144002035001c41901d00b010003044c103a000e0310100004d216240c2005090304c45840090308003031078100c01d8045002480b4000c07100402610b0394600a103207907955022809058810410000070244910850f01c8503450207100e9480e00100800748 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 293280467 1250 293279217 293279237
    0xa0e04030909241206060b031005090f0601020703241109030c0406050a09090c05030a0602041d0708180a0510050105010201150e070c050715020312070f0c06051e040606031e03 77
    0x1400c0d100d003913900700726911030701c445001c5018600d10001e54032030710b829004d41d41501d2800007007102018010340707110800046035060001d40d9a021403080107503500700300c2c10030451400000303541c14440b83d0302013aa00603103000d10310390b849120a03006283c0504c3c120115010340c0000f204100c125115440b4840c2d2101030740030200102c03990b40e000704c40c1c20b50150146c42c0c88117940300c010904048191800311100744c0e00141c14005603944222414005c000800140c4142c60321030030180c100c3d2005071080f117501c1200f040780c4d80640400c00c0f40007103080e801025203251110001c0701d08098070080c05102e0155084c07002c0078180d4481036001d10220746142c04203000c180c51350402900e035594100b209641c1d5010340740021541c0103441036602103159040d03000713550325580105400514400940145c0400045129440400354081c0041000d0781d04880c00050f652510f000a05004c1003591259900350b0102040009105841d80008100c030700609c3d03070680e40c2c0c81d184118646228030910080c089003890305 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 293281717 1250 293280467 293280479
    0x18011515170f0702120705100c0813021c05010c020715030c1d0d1e032003090f0f030a0c030b0c040510030225061b02010209060909060a0e0403090924 66
    0x200d6900f156503070042c0c80361590000900b00f9103500c520000d940961241d40708101c0301300c0310700c591400700d4030742d240030001c03801c2000d00b141d130202031100043d1040c86188146403c903804503c41da1680c56002008200004c0d03c06800f945896142c89601c4840c4026076106003001e01900400e440c4041598480002d8649001c00c1800880c0414400b904400707400741d0310f00011000c141c41504038119400c10942c0c7c00701403400402c8007042482c0c001e022000c801d42c900701280c0c000203440020a0840b20b44800302507441c045100d42c001081c0e00d66240c4103030113040d010311040d07250103000d4074010400702040340c0d00d903051101d1910440c814143c000049605101c2800d100394081c10004400c0c01903c080c841030030141c52010340f5003c8098807940e9540e0306202c400c81e2051001c0503040902c0c0004d5040c01125800a1098069800101c0c080e510586c00640c0c55550310b5545d030301500b0341a9900485003458280101074114500419682e42e1410f0801030303000303500e002c80c60882c8084004640c400740c1044 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 293282967 1250 293281717 293281741
    0xc02120901031116031121040605090f041107050c040207230102041a0a2c2106010306240503030904020a0e0a080c0a0501030209181801151517 63
    0x280c088140100140103420031141010101c20816000c0c0c2c1d100c0c41d8907088a086d15080202c500151034010004000c0c01000201003019242102c1e01e84c00c0046d12072404001050140d41780d405019032240c90619121040855000500610390181c400c0703034550186007042c84200e10403004c5c05042c0450802c00c078802840250326600041110740300250525580d0854007487c85441e46a07000e480348040340c650700040e8002c0315600303108124042900c15040d84400790020032407844a89010740d002101d050401284404007003400c00a550480b4031944e0f507402c050780181a200ba5178100c14003115050a5040c200f18448010743e9030040c0a51b14290301c202c2000025413000c00d150083c42138280e014101607072420080300c014400b02e406011410002c0c404c00c070200324540c008505240c41030050240340d48074402211881920120303208034980310b02c1d26140c10340c058103180103100d40c206881c40003c40a10100321007101c00c0116010800c0c120210240e800030b01c0c400403040401e20b404e0000d200400b070b407 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 293284217 1250 293282967 293282981
    0x203070f0c0f0e0c090f01180e150301051506092b020a08060123011205040b100b1c0f0222050306010905090d0c0318030303021b060c161509050a03030c0212090103 72
    0x5041800004019202080c4248d00da82d012200e06800041001690302c50095070003030300a0228000c2182e8501405900104980450250701840b0045044280ea80304d4000740c0b2114035041c1d403001046c1190307405100b00050960341c100d0080100c8240040e10318000264503042c1c1e6005820300c040c00003400c4028048031803c4050f2410405000c100410f44520b61059a0040e800380840a00925041a200300740340c5544e40181c4044404000d00500d50070040c501d00107083c103038074000c03a00119507406000a0b018070f900500b0308944541718402d41c0242041550100c82e416401e84205a903034005907801c85008580c210190340010700102801d92007010305a0f002c91003800c108801c01d0360360390001400402c1d600100c01190340082c1a40c840f00402c1a1600b01507450002000c075881c080140f507403680200120f03244811f10030303002c1c902080840341003c0300548000d1810044443b00c1d0400139500c2c0d508210650100c2d20780420058914804281d21002013480d202c0d1501d4031b014100110024022 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 293285467 1250 293284217 293284219
    0x20f0d0f020403260906030123010905180a02070804121a07090b2b0e06060906010e090405030c1903120b0a12050106050916021c020703120203070f0c0f0e0c090f 71
    0xc01c2001c00065900e1b00041d50190180192400031400c190044946000c6640c030020305000034200e04000595822590300f6442c054100ba10419464801845010380120300c4000c03d2010042000714814080400b0064424040c1c07490f2120801a40300380c0c44440c01c2558528005890044180401c850302d00c000c2c4244070610b18a00740c2060406c00f5045a111800800f020503521a58811401c100400c07079030303030441ca04803981440c9080c1240040c1103500b55110180c003c0010704000f505108090043c0e42500c0000e8059500910101c202824022003281003100401e04906142c034600c007152050b81c3d15130001914500aa03030610b102418441484102100c0c82d40d01c450012413151078a0003018010350424034a0030f00481e01000190400445124480c80d132400004003101050340010540101ca03040350070301c0200440c54204a0542c41101c10150400311070801040400503443d4494044441031120f02d00d000380c03207505240d100401a02d034003060107000e0001d00d945140c5144803000d400c1c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 293286717 1250 293285467 293285543
    0xb0d0207020f0a08060105011d030a170d05161205070e1c02030a0f0c1d0a0510030813180e1c0905090123041e0519020f0d0f020403 58
    0x298000000c8151030341380c200040a81000b0b00410007940c020320034058910411442d5401d10710200c3c04070340d5402c117400002d0a501c4000c00344541c004859000c5030140140e01e107007480140f408000005072034020034165800155405000c100030340f03041c440e440c06130640303540358198840c0c0c5ea0100940c110380c0746001c00c1510416044140141d44c100010280a44550f42140210300c2c0341c1030050040d00c59038003485009183c00c1c0350855401340340e102103034443c0358800001843d488421450a0824264000420103c0c0c002040c00603c1d1018507140119070883c07507050800402074001e02e0546190a04115140d480000150b040c0c07800210b800d000a9464500380018581c1c0398001200074070281e00214002d48040d0039503482194074181d00944160a071000c0c400d041c0d506031040340724090010292011951100401d00c802601d50080c0c103071b8092501c0c15502c8d800c4190104019900103603402c3c1c061861314189810340320a6009584c116034010003107260322400c00d101020340000b80515081440c2d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 293287967 1250 293286717 293286739
    0x904030e060f1201030c09021617070602071109150d08071b15021b01170a2a0206011d0103120216030606090c030618020705030c0f0d17010b0d020702 66
    0x81040301c00303800091a04000803050b0b52660620f074011a03899005080e80500400c4074040081c401a00904029802b0745044403210720050081440c0c003400c070000303200d81d00018241060203c0d0318010341034504c086499800030386039411214480d0100c81c3d480341c0c02c071002260b110301003000c09000c0d08000d030140c880e540f210328401001006c0d40c913003a0041d404041e258603045000c180c0c100000c5800d05c0034a0288201c112844001900000882c8405c440b9014001d00140c1c1c100c107a60011180d0700944450007172140010800012400f41c81c91101006204040c000904022485800300c40c04c144c14081402903403d40c2c45212401c1c2c4504030000c2548a0030341066800d400c40500c110003140220400100c19040c050248144c0d5102c110040416045c1102804285440d40c14042140071101c80141d4485051416500754021456500a580580080704100780d6011541d81038441c11580d4200c41118203e250407c440420300840c00b00142c184600c1000b4902540105001400101190036038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 293289217 1250 293287967 293287987
    0x5100306080a0506090d0201060b160501090210111218060c0a08160c05060309100c02210c011407050703031107051e06060f030312040204061a0c1204050904030e06 72
    0x502450b002c44144e8000c0c01007040001c024460148a5505807000b404024034260f00d0038228083d40352040ba001101ea08241d0030080309601000120b80d02511022806504000241c640301c566107013422940101c0d844101c400c61460700701c0382c402580340342400c1501441e1050242d560402c01c980c4410340f0960700e214021400c100050b06800c05410003100c503482ea40c0ca0910210302d050342c82103018180c1030050200e00300020841003c080f441da07000003206c01c14504120714140360b10120242541c40c294204c2d114440d203170002c004520502c4000c1c0404201e0707060192021100311090300004506003d5140002c2c826044180d01c480043c590604010043d2111400c1c944098800950485260855000440d0901080b64080e030100c5011401410345800b2a481740b062040300352003601040002000c666a540c031083c060f2002c4c07a41c20240440f540d00d02d400729030008108043c03e00c180a011602648041c01301e0b4103544018080b02a142c545680503038110b0071420343c20b540308400744003001c04 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 293290467 1250 293289217 293289223
    0xe03150c092202090f011706040e280b0603150f270d080105150706050a060f06050c150c0a030906110a02010b01081b030705071a07080604050609060a0510030608 71
    0xb440c2c044450042c1e80d010388004100080460901c59418420f0301a030f841e03402c42c180c05020380d0200080c0d4000c9100c03200c100c9201e00380700214000801c0028410803080e6010741040341601c0301c40c410007043d070054540c40d0405580760344e07152000729290302da4000100480f00145405401450f18000507480c03804410794400c40b800513100e1020340383d0024401d40580c0364804450b0b801003000b43e440d0808011002005203462007002ca014007041c0d1100c003c80c80080c90340d0b105000034a004803c5101d4591191070003040b036401890070b5800c0340303d04004001000c1d281c00f072113405000301c81c0502c1c0c80c1c11030a190582c080c09481c44146c1d4490f40c0c800d0b040308018400401070823164140d03400081d81710000c01c005840c40001400c4c0e01c1640c20305419136840d060010080700d801260904245458919078138084d500c6903010046604003000c140e050118050b0001c01c1c041c0500c80071101030006079a00018041140011034545a102034541410440703800d01010351041201a443c0118a4031345868800e40313 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 293291717 1250 293290467 293290519
    0x12904030b0103200a0e07030b0a080f0a0b071b020d02010c0b0a020903071707050f030304080f0d0f02031309020901050d06080609120304030f0503250201050402010e03150c09 77
    0x7412041407520318a900c4600011300080c1008940004185081040802100318010411070500d51b83d02c40012840c0d0300d5908100090429004440c0302d4042c95441ca500e0b4072581e1000c03201c410ba2000490741040c00b644074050908a125a003088120780d6400b085502a104641a41030001e000c081d0b1b00420b010500c640c0c8640b0300c010025984800c0781c410315250822661000c03000b11a104140c1d2529200400e22501302c8004484aa0218001c01c00090852043c0c1c1d100035814440c00070710507503107540412000b1905001e61a016050306200405907128451001502d8595002101c14403481035a94060001c0542c185005070038140a00ca0410864134075810400d4140d100100300007641408000391182000200300c0e10303086082507600500203400c800012000d1003000305c0000c0701c0ea50b1000c4a6800d0003000b070140d0481b04011031010303000f040140c0d0264005201e80180122509001940780d4460000703420303031540e543e25601e1761100c80c0c00c1000b0362544010502c2c1071440c041d40c1c0c800848 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 293292967 1250 293291717 293291723
    0x51605070b0a2a080709051302070812180c090c0316140c0303010f2709300f0302131403030c3301050f040b010e03010c0c0515012904030b0103 63
    0x7600390380d520030013501c0e1131001458041007105400c020702440e20b0320310600d0f100604810002d82c48040314a800501809201c000ca00303516041010001410314010f45950075903510420768414600d60b10a00035070a81c102e8079010804810000315414940294140f410340d540341c500800036004d80e03007100e020b50b440004420b80652021005018141c01504c14a000344000c0341000a140c81344030300071011580107041003000503a294011010701095000c1c054202c58a80d90f100382c0d05080c801c1d5001c000303404c0b00401c07002424040030741c2e0016000b4400c880300124140070010348913140c0500000c96980180c1501e815010610121280c2181000000d2918603040c00d9168401e00c82001510720303000c42e004c111172040032200100400c2d2241e8509020011050310b01203007540003140161400008084460342540c0790000d24102c070b035444244140154800c9081e24074072503940714100c001c0c02c028040c1134400c4414600c000e004500e26082d0b10059440c481019042c550340f903c4804031313080e00360310039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 293294217 1250 293292967 293293031
    0xf0d120306090b0303190c0321050a05060d020a1e030b0c27091b1201030303050114010c0c0b03070c12080118051006120603200103051605070b0a 64
    0x510840b0203500802002c079109400841c14a403002c000c8080c0c515012a078801441829030b400f1060512400c900d0400d1452004134503000102c3c0041d0398010301c42121210305440c981000704000f0b01d0300152240540350001d0803041005e0500410b185a00c2201e10021401128001e0000000c1d0f16040c41c28400c0103007800303060300c03400e4001e901e078948030b00d20b0800e402c480d2889480414654400008942003a00c0c03c100d518241490624500e00e8031880e0580c0c480341e990380b8000001c01d0b500d50043c0e4140d4051104c03940d94407038500c0040d11204003503000240380814904d03040c02503400050207158814002d1030500b001d0b680c0f903111050011641d02c2d403180080c0a41c0010702c40e18185e400c0c00b1a12407417250b010041440c1c1000340c1c0b0f1401c00d05000303907806c101890300e100b0204400c40e0000c001554101e004007600c054600a02005c8210903581d0f180440e043c24001080401207440404a20509840d480e1030b0580703607034071603511040040500341400d50320460040818003040c4000b8406100701c9178 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 293295467 1250 293294217 293294219
    0xd0e0c0a050111031206040914100c090b040306050912041401020715051602060d060b1b0610090203091c080603070f050109062001020f0d050a0216020f0d120306 71
    0x184624109030780c201c00d05119801c850b483ca0040c0000403650b000fa0803110801907915008009405000c000001604140d10906500700071100031800c0e04905421500400640c04800000d030341d80600c6114034403407400180403c2000c554030713401c801e900c0203004098456103d40c81451300d41030f4000b6041345424085494001c451540c04000c1c10f0050b10380b0300c210070603400d18404000e203280310318410030b81c0446015900c10215111801a03e800410960060084036194440788005400036617400d11103001950342d40c160781d6404600503006440d00381014200e941011003103800380d400a84107003017038441c084c8001d481c0c0c40e0019030040d000889a403861420f08214041600e00380d00c640040d0305103203038103004110b00d80c1c116012508031100b03424040321604240400b003240c0c64074180c01706115400001c8482e000031426000700885050708008010304d403904650701007280618081944081d03c0082da12016280146402d07082e45001490002088841d0b03031603002181d100080702c004a40c039018 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 293296717 1250 293295467 293295469
    0xf0c0206090f0a1e0602031201030210020a0203010c021510060c171e03180114191b0906090f0317090609040f0506010f0c020a03030c0c0b1c060e0f19020d0e0c 70
    0x4260040c4034130300c007c500340301800c25019800c04043c44002e2041200c807a03001c90748d03802444030481064005008008a20491070040d45840507000001e810510060014801004207952402520b0b0650b684442035561a6181d400620003403048000510050102c0d03060300302c000c4428071181e00c0c6071101e143c03203003401454064500c143c850f1071005079052482e403001c0c1c22021841c041d840f020f602ca03034185002050501400a00380c2d00d910381034400d42510795085003600305035143c0454440e40d50b07060034143d0350030070b566420240340001485040441c41254200419102510765408004c010b2440d00e0310241c0058221410180e031140308645400803c034056800840821840d0142d040c52030340000d0b10382c00603542c01310070701009040c4480c1401403c184000c03408a480500744000c1c003145c4c0c42185d40080d00700f020085420f50070040c200701c0c01107005c04541025a008000340600b0342d4054882e03480303d031010159000e14100b450303800d210341072a2030528000c0104d2545030341d004c0c0011451081c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 293297967 1250 293296717 293296769
    0x90307051b090a0b090712091509030915081b09040c09060810030b180a0b01080a150b0d0201140c1006030b0604050103030507060207020a050a03060f0c0f0c0206090f0a 74
    0x180403500b100d00d45101d980c44e03030304e94290036030307010050f03140003150440c846c080c3c0300c01006440b5000d05045031110403501052001d42c0014501400f03501d40c0e18007165100b201d25091026614100c00080d082d80108040c4005400c0e00390000c0c1c0384106940c00c040d07000000c07070101c9210072402000100d1440d0700701300450b0841d1116800000e0040d06240080c116243d50a6490010704202c680e0f410300c1e504440c03548010b01c80c4e45920b03a80000c00b085207503940d201071f660341c0803d181d09a550391030700074203801211594800d000a0714806020407011403c5034005540352040041c6803c40814204000010140b00b8410140090920030002503140d00b181402e200d030b00b030014402402280b44c00010b101203038208056980d00f980c08480580c0d100f0441c400310780c096000e58403039600210700c6000441001180d421080600d0040381c0b040145020a020407503047c11090038900100350321240d03603030250070080b00810540401400c0c60003001c02c410301040c0003891503400110301d084116150b4843c02101c1c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 293299217 1250 293297967 293297971
    0x522050901110a080a0605120703050105090a0c05010807031b0c060e28080702180405060702010902090105120c0d03051e030402060d0b011b0c062604060203090307051b09 75
    0x91002045080c400d0350b0000c919101d0f89000f14140019003000440300038103500100701501001d0038901203400c018101c60742d281d080d0b00045406509010015852440024110004581040744010114548401900c4005010b0100001c154481c045c5698013100c1d440301014090250761458100f03911400c040080380d50742d071080480d41d0410742d519071485045400034a26154a030224150085c80e5291035445841002c4000750086419510154200c2214007020312443c040c0c1d05940890760740e140100c4c200c2d480f00303000a60140204005025606080c01000d041c00b0f211001c0b104200c2c0b01400040c440c10081d10120001000010b811189100124100300321302038410400c0e04500b05980092403034007406074000302c596512101c0d400b01c2d0b0f01c01c8414690b0085000741515001d5100d06064400d680c2500945c2d001c01c81c44046040481403c104a800e0a001070000c854207884540c0c0d843c01a520103054022140302c18002003010942c28040f8a41610440c80d00c050491f0008051003224940 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 293300467 1250 293299217 293299231
    0x411100507150506120a0305090108160212030601230a111501030602070f0b0f0a0b010509060313050c1005030a0f0207080d09030315080303010f08010b010c0f0309052205 75
    0x80c00400000380d0302d901c1d820720000c89010302181c0707a5500700100b2401582c40c0748125441c810300044109140d0003000500041e0710a0380c03107411a40d0b82420a21038600321281d6000168019a070520701c0c6446600a59004403051415203883c000d500c45e01030b107841d900c0004286840300020f04004c0382d600410039140c00c0e01500040c00100701107001c40b0861038814440540b85940005030181080803008002d0780066000e864040c0e1401c1000140600d440121841c481d00c3d40b60404903001e40d07001c4d03000d44003a10740080c200b80c039507941c000c441010b011030382d0320031913991054520800d025960082c079540300c001d10b039503105d460380303402c0314003000340d600f0408a0050540704001e080c0104003200e0403280e0b40c8a900034017082480031443c08800a111440164012204294012070805801b000940c100c0e00c1078590b040040d40c50358403e9089030254100075011805107100300d0300245200000c02803240c064100400c69564074070100d042c1c0b00740e0110841606208001c0c02d00311903003e04c83e2a801200b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 293301717 1250 293300467 293300477
    0x51206030706080f0c0d2405091302060706020d090813061b060510080609071d01060503040b0a2004060f1404060318050102040b0309070608100e1806041110 69
    0x4902040a442034802802e1022914204400100d411000c2422201e500ba16520208038003401007e0b520346039800b629001200510001000074070b864100e144600440d03a440c09810b0481c413990821100742c1c051103003210116000d00112031148168852a01c07130f0f901a84196a503250103070b060500001c1a50442414011032040c5400c00c104500544600f10380d1040c00020903440c3d2010140c401142c0d54001d41162083d07000b0050700c1e0202003407010072106005445004042072881007540c1e003109000310000200103200041c0850700d0012500c1c0c0000000c4000220800890001100340140c5c04205030399140c001000c1151a9000d03006440c02c00c801c3c5414454011000c08640c8103106500c0394500b01a01d42d068480084080111411850b80c0480210340e40c960341c121035480c40d0401c0701c00410900802000154450103061000d110304500231601078407905221030f852071103001820698001e007401c0903032020040100300d0766000d40c1c040c0e040c11004048030030420455140c0e00c54841d04002d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 293302967 1250 293301717 293301719
    0x9090204060906030b010c02150c070806130609170d140702011a060d0608030d140105060c1507031113050916020303010302120f070603060501080a0216020d03030b04020a0512060307 80
    0x2da00c1040c0005a81061401180d0545c20000480d1201c6d2080c0c4e004c1d43c0101c02c03100c07091820b0790081c010491106100c05550003181d41d820450744500f012240307050940752880f040400909181d108518540c070070307a4968050749400542402c650801c210201807945c0c2c60f1100107601000c9040c0310391000c010b02c000c1c0550114605058118004111030368001e04003c668042014081d4010201901d545001c0720349540c4103c0007003010b8000140b10720000c4000c070001150728108030046070702c3d40313550348001e01c0445000e1010304400000146507604155a800c59422a4100c600c0201440100c01609400c0c1500b08002c01000010141040c00c0010440e0003006865401205481c11241c0403603295035001c0c64003440c9410402030007000800c030300038504045800780c1c041d48502c2c103890080c1d960511581e16500340f0012480780215407404007411344a101c0042c0340121012503818824038002c21144c11441c041000e80e0009001031780468004034501030790354100b4205035404101103008002507 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 293304217 1250 293302967 293302979
    0x15020705060c033304051008010c0e0406050f090c0c010204050618011701121b12030c140706050f0d06080304090b0102100207080a1202120403080105030d0f0f0e0d0c09020a09090204 80
    0x20704e0f9120128000c503111800501552650a4004010106840288482008031000a10300c0032140e2246200354600940414603050003206440284409046801e058603001d10644180d000004005555902040003007010748510003d0205140c003007112500e40c10851002500c14a0351040c842c082c12462401040858081955102126080f0420300342c007460013404000c0c0498a50055180c09986001403403c055000011b0000f16000d80c0f03211032401c00145007a074560b1342e01d1242d200011014040f84044510340e00060410352090580040c0c06a41c504001382103030000e07404584015a12446800c0c0355805000701103564030310310021172401c1c41725a40c0300348501030a04442e0070020031005075044152660f041700c1089840100042c0d04d841c10b840c0c010174a00c02401601c0c00380c0100340d40e4082c0c9600031500c90750340242c0c0e0b45500500c3c5264580441d0200041c08000d6840b125104c074560100d040c100608000e0000d00601581d140c140040181400316a54400c1200a204020801030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 293305467 1250 293304217 293304301
    0xa0e0103210917030c0a0b0f010609060f0305180f0f010b040204050604140607150203101707150203132603040f050904020a1d060f04020403050a15020705060c03 71
    0x39182c01e1100f207a1005503100110f403842c0034520b40c030400e600c02e01482c45d09010742c3d40c492521400940310f999035240e803140300460300302c00744d44540800b003519031026a11850098000e1640000c003001c100c203426266246847c07504079481c496a505810800200c0e4581c442801403c03070b844070a40d829072a00b0303c0d00c00402c2c503070711a070310481d6296502c414214902d03545030b41c00c440b846a044454200f4941114414400942c0281d440030b0b1307040c01e441d00000c1c161780403001001010020401500d80a8501401d2520104d0301400d20340440c0420070901500301000901c0340042c0c42c40e4544034520101c1000034613003440c40410790b1049544140300402150111030b4030b14013035400a03a440d642c240c0b00e52010602d41030643d004010900e4040300c0318923041c94201c1e03c5034807610f000c0300c104420038106020301c800ca200b540405007903a003041c3c132001d01091454500c0f111079200d8001c01031038105545c89860803c1400c0e2003500d0400400800d0018040801e10310312000543c45045655a8a5070340c89111 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 293306717 1250 293305467 293305469
    0x51501050f071b0305010b13090803061908190b10050a090b011b03050d050c03090a0b041b171002030f0a090302070816180e030901110c0a0e01032109 66
    0x1800c400050b501d030800c100d4010540301c540f1040c00280185840c1c0c40c1c030034040d0008070700c6507020b4940c054040820200c00e001d400c020395001610b1a1a6031240781c203100b01c0d40c202e8030604490b1000d80308000307040e0904001d64500101401008141800d0900d800180020054000340340f01d00311a90900ca10b0343c4004040c0226615590000380c441e40e00340050fa80d107503841d543d05001c500360b054204103141d0004000c2c080610300702c40400256540004c841018082520b081c900c070792001c06040c0002c3e4140c940150001e00030508103080007142000710241840341d400c15200300c43c0100c04055107141c00c0020040f080c0681a080d41036140505840002c188014511050251560301c8041818002c0c0b01800142402006480b104800c5441c1c80300d0311405846400d01e03455201c4a801d18280640c400e0242c5070441101461a1000740c1c801111003503054401400980640c012500051352910301741001072004000441c0380d0340c918104143e506a912061400d43c44910040100352584000c02c80 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 293307967 1250 293306717 293306737
    0xf1121011b0e190e010f140306090d030213090501081612050318010e1206061e0604121506030b0a1109030705060a140c01020d2f0d090506130605150105 67
    0x640300d00100103c1583c40d1144d40302042440c0b86000116071003c0c003c8100c03003980c03581c0c03841c008460384400c00d05940e0041201c0e1540c007500300d44514181c880c0700350024814901341e25200d40c0da154681c92154110b45080c2e000104580c4100c0c045000038004401440040202c82040401415141c949a88038030640c01003900c1c01c05040c0c1c540900380e01424404540c0b40d0003600080f000d10701c08014903034610003600c6c1e41e1321405030b003503200c0e20704a001e0811895100c1e024080c28145490320a1321044800942d80896131030070300600001400da024880c0c840107501940c4010101e0808070807a008a941c146c410600028041041500544000031160103c40f4165112587c40744c2c2d1880c200c078050103051901c95404000a40c4442d03070030054001d044144e1010400700b1101c00892008165000100080042e070074a003481813105850190140440408401001c500854a5070b0395500b4108112a0490840d10a0000005200051240940c4240002c1e00d109a11600d41d00181042c007401e1215 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 293309217 1250 293307967 293307979
    0x90a0305090402250309080c0a06050f0a2607032910050c0d1d090f0a0b03070308120a0f0509030702121005090a05010f02040f030f1121011b0e 63
    0x15440348004da138403091080a0b003400c040a00340503880c008005903181d10803802640f0404034a800c0314a000c2d80c2210468441da240c4519004040b00c00381c1441d0484010f40f13090001c400e40b0032001d507481d070410f520360301008841d0108901d400003000e002c403a0030140c0c0c0e2000050f440300f0f03e1184540304e0462000200100c805014401500b501160302d4466204d440c80e031409107040040d1955044500b60b030104000041e54603240102d0005d000310284100d400710401202d403400714820030b9099011295928010b400d0700c034016101d407240c20580d80700b080b0071100c5066900812841c040e4610486180701d15042090042d414081d440340c0e501e01a84001912620b0301c05040038021008100440c0c16410031102403005240c0b003450b181d2600c200110645165003089800030540c0b0252003101c094400122140d08114115120b682032108005811181d403103801c28049503135074070114545008601c540000340210220010b650035190107004c001142c40010b50703440e02507604030092540e03109040e904 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 293310467 1250 293309217 293309227
    0x100209010f030915110a110a080702091b0711010e0307060210020d0617010203041a270109060f05010501020f010b060304020616080d0902010816090e0702070b03010906030209090a0305090402 84
    0x130124416582c80d60700e02e541e25180b41495501c0c03000300a803040245940340c1080f01c400742801d040d1681071a42c402880c401c020804c0c00010310302400c600703400c0044803840c5c000140c0d184040b01d585900c401c4041e41e559050080781641c1d0760784840003c000c402c042d0042c01c121441c0160295440c048504a504c850b5004a1890500e03009603018200604d03141072a000304e00d8560402d203000b588103450070350780c915a4000740d0f078019403164130503030084421090403108100b07000080c4c0144d000710f040f0040c8a54271240c00001052403409040145864203100049552402c3c001a1070400c1a825015180c2d05080f40c0e9100b07a510306044d2548103406032091036032058880300f0308011450152005002c11000314043c0362480c0c09501048201d40700703880c0d590303035504c5800b103511808844095610004619103818070510303d42c0b001d040e41184450040f64201604e4440d0040a90000d802101009039142c80401c1546002c603801a00890a080600100e484a0320020010303c240319400340190340001d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 293311717 1250 293310467 293310473
    0x30703080c0a08040e01140a0b0405010f050c0a030305070801050301110d11130b040e13080313030201020405040e03030901050a020909070c1a040809030c220f060503190302100209010f0309 83
    0x201481582c401c0d000c1340d03100e0f2103400041c41e202c820b000f2500075040300b181050603814105016070540f030100d403042c2e0400e468040112007105a128116040000c140b0110059080030001980d02c1e074404d49020400e03107003c900003015078005a106c588260304012032054041c1006003142d8881511010201e141612107414a101c7c0c0b046807801c1031205020071000605147d07180c0a07205442c200310201c0b08da42c492011405c0c10304042000070301083c0b0208045401c880c0c98115030403941d4400d00000d418640d40f4000034088841d010155460382e00004104103c0000a1007600c0d480b0a9842d801c500b0030503420046180140f00030901c0d002d1080c2c100100007803052a40303500003010505110343d069458240380044c2e00c0d410410740a4000d01c90401e80742c14600d0441c0324011180a0302410400c46441d41c40b10401a00403029a01202591480b0208440c1c500307001c3c1401c40f86007680140c1550f1804e240080c5040f40009140400c6441803007509003503a400721041404100d5407a01240c1a07005003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 293312967 1250 293311717 293311723
    0x30f220302100801090b01020a0201141b010c030e010f0e0a0201050d1e0f0c0908121b1e0f01050106080a0906021b0d0306080615120304081203041709030703080c 71
    0x508040d600030394010070381c414558483d407154103903401c50074144000c18688005a03a1010003180c0240420000300c061300038540c0703601c094841014801002c0502d804510f964900f12030b04030502c90006030712544059604002400f444504d104080300400220f82c680040c2c649070000e01c0f10082c104940010318140102007034001142e0645190494800900b00c0d80c00c04004040c0154030050090400f40c40b0050940108101c408482c408405032005c80741884500d28540c0c882c1c503031220600d200b1020a280f1900c200304040c01c0d803140840c0d1a82d03881036404202d141402020307590702e0030b030305040052065590103d035058010710340b40008150028146842c1010b8010745410000d20300303100702310510728400000c0c540460340c40354404010050720780c01c1c01511001c2c02c0355404400f08444101d2406d42c00c100007210310700019041968141a1101515810b040079280d080562500c040240f006002c212500105120140f02b1010324103409840030a403103c1951001500c1a00082150030241c4401c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 293314217 1250 293312967 293312969
    0x30405090c0d06060305060a09020a0207050118030503030103080711120a0f110414010f080d0c08090409020910030c2312070510180e04051b06040308040311090603030f22 75
    0x6001c20303c0070a4603003030014000d110072a05180300d60700035a1b001415600354800c44242603034a070f01412071241080c00560300846113114842c0c04850318440000820010300103140654403800c46a40c0d59041800c19442104816182130b10405011601c034240714400102c1c460545da0000044005ca0098144408414900031030f0680180c1000900e44e00a6200034100341600c0001c3c0c40c96084039150103519035640740700088031000c41c07000d042c1c09021602c0382c406421003190040c00810b204145c1e502180782c003581510481c06801c0703280c1c003c0c4208070140b880100a054401c1c0ca0407075601032068407401481c00041224095a140f802c85a0b150b0000e01441001d00f4000c0d00241d608868058000c2a4400c1d2a00b000a002c251850200b00e00140319000c6020710740103002840e00e00c0c5180d10030070f08000303201e01e150f60103141044000009054240500300850080ca0503031407504500042c060844401440d40f4401d800400819403502c401405a40d065400b4074030181d520101c64405c40310758221 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 293315467 1250 293314217 293314237
    0x120504050405070c0b0903090109030308060604090606050a031116021c0803010b070b1f05011d03060103030c02040507080c041206060b030a2009060a0813150c030b060309030405090c 80
    0x2c010030800c05641100c80307000c0c0548100d920100696686170b5543d160b019168081f400290405410000300303204628041c0c101234002c2c461460b141c1c0d5234cc1290100c03004d85d4442c0010a2002c10035141c81c030f406200f0f031104105040100361500d0400403030216200c403803440003441900590b00a0001e8000c100075081580d07031044090750b80c1c0d6100d0985818680041204544032020300f000208174840050000060110203d04203800c03d003070100542d41c0c1c1078600288100b80100e80107003802c66030100000d074000c0d0702036260103a0310340260040c4400d0f0f520060007032042c040c605090021070030b0641c040714112611407828016842340c82c5002030180c0030300d03031084058a00c08814072020b4205907206260030100f880d031060b44c04409054010042c0622041c00c0c2c0d00c690140044207a250090501550000c0c06140340b082c40d030007075a207a045c0300120070b0800314840e80d00c810810550f6010700c9180c0a07a034003262404d09610382440c08654911650055601810101000c203410300220415600d9540c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 293316717 1250 293315467 293315471
    0x19091a010324110304030309020127150305150613030b010b1201080d02032703030a020d0206150a1827030e04020a0c06050402030705030307060506130c09031205040504 74
    0x1941e400d128094400c0c0c4000d8420050303001c2c001d402d0440441c42180c000700c202d445440d08550b1030b510150000d01a00c0310590600540c4a002c810040d400030180c40c5101030000300407a02d5040ca8011054804180e1840d020300d40751100f40440c403010a11b40d440c400700c0031903106964140446d005941c00b001948010301a910700000414240180d070040c10717008512a01c1200a0faa07100b40169485104440790b6005d41c2081100704489c824440303124101d41c1d1130502861548a01c2e0012a00e154030400103500140c01c0350b600b40702c030306606021541c0c002034880160011481d0301000284081e06a1044620024038000354610784446500300c0c0c44c41a4045003468049507440404104204000b0b00850004081d14010031262825200f603848159641c0c1d036140d200c954039903c0c41d00400001d0000c1c2e03803501c01c200c0300160703a5408000500e0481e02c0f403000801e140c00d040342032248500311080b64554103801c040c102c0310402e034170522000c1201c1d001007201045110001058903e0b104036004240c01034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 293317967 1250 293316717 293316719
    0xf0414030c0a11031603150204051509010e0a050609010c11100c06050105060406050f0c010f05090a06060503030f0a050d0b030d08010e0618150414040b010609060819091a01 76
    0x2010105404000c01c0c0940092040c20f0026400c0640b50740400c5100c080085c070641e4280301141240074036520001842c02d005242a8881c0c000541400c80401814027800b40003a86030300d070f5603003c62107128400042e180742a40e20308140000e025802003034801410000100d26060070b0050a2006e21030110300a020107403900141c1000510084010b4001d6500030300340300002410b81401812142103401e1655450300340010b00c030a44c5126400030441060f199201d08100f80c4400181c49054040c0c00c000d40144070125403480e25030181c8216030721640c0310790000e119010000075014100c445c414103d2410360368881d040503480d801400d440b403205404ac818465100354454004100784d06890f1422100d41c41d81d9900000c120703101002c0c032501244400201c012900c452045000a4001c0e00020400b04e0201c01341410f05900c50012107003520145608401000070a8120b4100381c054142071900244900c3c1c0340580d180041c1070160707100b2115903940810814000b00540d45916022900002c541c19 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 293319217 1250 293317967 293317987
    0x306150504050909030f0a052b061505040312082d040303050603010207020d020907171609050909070501200105150a0f060c0b0408130305071a120f041403 68
    0x3982003800b44074003c0707841c10041030042000000795501d4685c1c90340810b00e0407008607000c903816041480d16440d00004130306400541c00c0c1500001c0406160f40310005a061f26010518040d1800c0d113a009050041c01c00c01400401c0ca102c0c54103c000031141402a019200c524461410300c20b40b407648000307070b41d0903150244440742a01195014a000c0e690511460b19041d0805080f44514000250b0001401807030000500382450010b601004600f0241d1024240300f14411030500304695440c1d1001c0e002c0f42086142d07420506010142030151540c0d07503186009000540d98103501d00035141070000d4804c0d0541c0f0840407880c0881407170200b50007480141000015240b2650108ad1142c4c882d803482500407681c0c0000c1c0c4240c0e4101c07101d69840407035425141e06e4018035010003600969800c4410407017000d60591300391501c2d004501c100700410301d052501c80b070b0002d2066655514000034000b0041109000554500550000c1d0486034a50b00c0340c446145c00050780e0107540c0854080d010128a0003c4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 293320467 1250 293319217 293319227
    0xd0807030509030d080f070311250b090d051602300715020d050306060915031605040f030b06011709070314061b0f0f040f050f030615060a030615 64
    0x42220a40c12500000d118500c00d680c05d603001c5850f1182c04841000082d8804c0c0b10b07800041550300d02210f072514250030f8600141d008030040c4004283c80c0a9003c090007085006144a640041c140d4042d04240c0300800000b0001d01c40c0d540070181c50f07500b80b0310010071355642d408891071321005031103400540799101414001482003030400d4001c44c050507400040e411001c1d21031042c16105540503025074800b014041c0d031150806800c507a000101401128036a8680100e403480c08180f1111054480c640766401c6d407601030f241038002c4200701003408108002408644100c0c00c2d40d51054030408203544043c0100d9400f51a04958024803200a0511610b040c01084010940f40601c04881c20342d26000b82c0c00d0364a400590f0000107541001d0421302d803c15000001c0e10340711200c6804146400c1c03112103000d8454002c1d0700148600d442d915030411052411006601e901e44003900a00424584040e01014445020b8503850140700001441c0720881e01c46c1e0f025901a1040b200382c2c1900503145940100 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 293321717 1250 293320467 293320477
    0x60f010503010e0d0203090621040305070b07180e060409060906150501021b0418320a02030c040b0402160501091704080706050f0c010c020105090106051e0d020d08070305 75
    0x302075440c0c01404044900049420362040e1003175001985048030b858103111480c2e1190803005000e50302904080000160761139007034000d9000f9030f01d40b52940c2040c00e02c01100b02025050307000748411a802d03107006181c2c4e004080100c58034075007603803802d03628040410b010786118200180b040340341c900d1500800040741d000c0100c1421140003100710a41310801a40d0354107404103284011551481000c040346070a4210000f1100d01400d0031400140960b106440c4c00e0800541000c844160078054003a032651034008051209114003d190114590300400c4d200d02c0005030030b138040d41d21400050b855494940441d00748065560b003401d0301c480c1d20f0030264004c099400c02100c0c1a44404940c004800d2a0000d8400755031801c005410101d00c1c15034207844560102d94055411242400f4050288100703100314107070012103400219091174004800d41c2100d0340c5400052244e0300000320140c1c040010f81c0c40480c801c0e81580c082d40044070340c0c00060144041d1721001040494001410070400d603001c00505 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 293322967 1250 293321717 293321719
    0x3122d0207050a03110d03200a020102010b0901060503040b0601050c07171605130203090a060203070c0b070f320a0906170112062c0c090a02030c030103031808060f0105 74
    0x1014107403a00c081081484841c030020b00024003d0f8440e0f400d80c80c04002c06c4004a10a003088680880410117200c0065038107501000b2607040340310f0300c0c1c0955030207014502000808a900211940c141030000c0e1150101600c0a0b22041d8480009080d50340604100c0f00d08928000c210303a11b1642c1c66543d01c115504403054041103000b107500c0b2828409000054006850000f05049943c2002211140c0250401400101241700304d055500c0491560702c015800340c1c3c4c0c1940e0311848407030340341441c0003c2c0780301400c80010000c64681810919074000406810307219464150601900450481d2112414540d0b5591264074001008240031b03400408031422129030b40c41e00c1c2140a500070311100102424410700b94900c92040d901d000140d03c6500013410341e41d802e2030425a0040d641c4004061103140c2c00d40d200191301401200310a440c0034414560310840000066145240001c4400120b01061000806009580054210000b4004410806019907000b02d5400b441c0c100e04441c0c000e0003e110345 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 293324217 1250 293322967 293322973
    0x30b0112141b1507020d08030f0f10051011060c0c060a1104060309022205071403091b12030a0e0a060302072a080102120708090a0c03122d02 62
    0x3100029011a02045215031281e08800b03148000040c000100b00000407800281820450480180d0750300458002c81030255100c183c803480c00c0384060607400000b40101c0060656401000802d003010390b42c440a4490076501000c804049080540b806c07020500d44071810f0084008001c001007100000d072000c20350241c111205615054541003c640c0303039964105a03090208002d0043c50300030307040b15a41501c0941441107000c02d2401c1282c58440504c0c5021140351120140903105611040395456001100070842c80c40c140b035035201c0d94a5041500346041c2100e900182d000702d982d12540e924503042204c0541e641c820305032000134011181d10100034440d80c002600494003920030310030740b12640c5d88454141c03a118011941242144010544440400c0d0402c00102d030700d00003030016110303107450000305a0040c02c0442e00a40125070042184d12168820f00e80c04003c5102011003100326900820340c04400030702d040703080342c1c0c515000155000300b20048545291082e50407403061221034096090b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 293325467 1250 293324217 293324243
    0x105060d0305040e0c040b12060406061103070b15060a02011b030c02100504170703021e0d051902010902041109010306080c36130b010e0628030b0112 66
    0x1040609103000c2030140000701c0a00c4107100400380000b4007504640c0c0d0b90b5a441c02c096072a6414079099200000ca07a402c0031030070003400301c10b007040d0080701e02410207420300480110034001190b5880c003030a02c0207810341c0c1e4070303401042c81c448031200c0d500b0310020081c060a5442d205254080d0180069002c0c00301480701441002e14154403c1c8540801120303e0740c091310b88910107a90036400740801400c2500c0e96000c0e00003498108141900505045101e500586007202c000605c1c41c2c003030540420182001c0e0040ca800703a0030b442d4000210303400340d0320032022030420f0600f034801240107100303404000390400d244c070092058545504002c1c0c61141003d9a0034400143c0b90107456031580c00040c401034014000c1d490b5030007042042c42c502c0301c2c49109800030024082340c06208584804090303420b140e01c0c0746040c1445007440103504805014103200c82a07864642000404110500e0406600000d81c01c140403480f01c2c81400622000d00540c0c010f0312499083d61100b1345090010406542200c1903074045203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 293326717 1250 293325467 293325469
    0x2b0213050c0c19020d0b19060915050d11090a090501110903100e06060d0807170403031d06030406020f16031e021b01140d1532040c02010f021b010506 66
    0x1c1400c80f8190b010304403034515601e40d41ea030221420041c052a00c00c102403225000700c40381300c3c42000e000f0702d80e2000105150700110b0450703243c4c14a6401c0b0600804042c441100030900c0d82c1311034a41000191151603180d56a0030a40006210030715004001d1b5013070501c000c1401409c1400b40511440c01c03800c1d200420407000601040381d01c0d004860071190861000900d091420400c1071485502411803186030030440d0b41d0705116030300c070042c00c0d1b41e616401150030f206140d4049007500d40d118884481c1041c022014001a0450100901c0140842d0300051400d134088000c0c0180c400e0041380300c030f80300700c0300c0020715001c0c01c0f031514000f11a450400420403e18103a100250b20003044002d0744c030a41c80d08010781d00449251011205070040c484003086070049008091150a5403591552446000e0300d0900011100e081e0a0a84184070360314030b0401400110b46010360300d1502c1c0c40071100000c9a1200e600164003400c0d04501141605102260760440031018030036600072400300c50003c00c0300b540d58030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 293327967 1250 293326717 293326753
    0x1103101a0108150d2303031f0608040b132103060303030e0a0b04060e0705030f0c091e070f090b12041202030a0f050306040603081c0b2b0213050c0c 65
    0x502843d0b03000195500c1e100c041100301d8503101c070301140c0a82010010514030449403955101707648919401c01d25000300e2300b42000c01400d0101030080ca04c2c0c05010340c1081c1d1039410245501030885180520f6000119042021590065002c01d07480d100020b58440200703406001010940300560129081290034146080c0c0071418100356035101c0f03482d1981d0789440c1c4403000240300c4c9510060341845070bc0e07000300300766408005100d1038200c500000c10001c0107400610040c488060301c2840e600682414143c3c220b0702084546034441e00d00d10341403001300918801207501e059213601076414500009000090041c031800c50502c61405004608008840c0307070801c81e600d1013030807103060000c5e0381001c03100c00441c1b1850007160060002080800c58036141c0d241d036101e03035011070b8803c4019405180d02c110407084601440701c140404032001102404040f00c5403508a5a20314000305110601514104540c2c3c0c03001000d0742e40f5007200e41003242e8984141c00312910340c44444140c90742c2c402d201218060140c07117 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 293329217 1250 293327967 293328001
    0xf07020313090b0a06020f1b060d090c1809020a210b07090f1401021e0c06030f070f08011a130803030a0c2c090a0e06150a06080f041103101a0108 64
    0x7c400601c001c0100c00881d0703039100010250598009410490082c02001c0e074002d40070080d025590041c80301e0302e000146607078000407140f0700a42a0422038881c0c0540d4a4628201c01c4440200d44820803180740c80d52860100c42c41d000040c210001300e800e0241c59035014641100341e500e00a202c0c4100780d110440400e900100f00740a03801a4001c5400c40c041d0a51400c010000491140c22500e88050310701c0011580c0d08101ca421800c9140e417003c00500070707844424441c80000d00d040c40310140d4105410404812500c100d18458035070f0014041b443c1e5507120080000900303810007031b42d8030f9050070410701000d0102c081115001407100181c450031142414400d11903034a2842141e6480c4801e50180111500000c0030b9001090b03540f03c0481c001e50f0207114052140c0144441e03104401ca610f020880d03c80300c0d0750054000c0040080c1041161280a01a2600701d0340042c542d4090141c00d400180c07501c456450900005400c0035445485402c03010014142000d01362030707582203540e0303506541104400c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 293330467 1250 293329217 293329243
    0x5060c120913020301030f020a0506030601020615010c17030f10180c260105090702011125050d0201021206040903020c0405040615030b1506070b0f07020313090b0a0602 74
    0x1105200305080d40300e02008200d4071001820601003200195241c0e400c98000f40c4c02951403c8650305080214036080708034601424088414605500f040350000f5918140100740d4140040c48030941c1d010f0381c1c09162100c02c9294031000141c030a104103011031070031760400c2d01c1d01618070f0301a0011460340c140c00140b40d4107423046000040030745514060854041e00f020102d80c02131292119060405012141440c90725252005452a45502d013000380540342034005c08000031645042945407013186007000700c07031558030f00300c60001451000c044891110143c0600052446c412000e44016040e01900034101c064000d131404481592404140019100350b81002401a0400010108241303460303480681c04c140244030000c4c4002050f2064001c1c0c0c00350390015603061010004003c0019042075041180c1802031391341c2030030310800d41c0d00c0f84102200503000414012014002850b0b00703200b002940c40034001507581000727150740d51644900a1040b405420302911a004c0301240081c00000c00c0f011400d0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 293331717 1250 293330467 293330473
    0x3060e06010e0f04170d1d010b1e19083009010309030e030d020a06050a23090a020319030305071806030b060910030e19080f0306010509030a1101020705060c 69
    0x10720308036221540f040082c401c4a030b40c81030382464a1001d20480c042c192001c0ca400c0b0015140125451040c1c00c601b040f000c13100b880c0e0500036000d25a4851868402c80d0302004da00e1a0711136448180045e0403d0000c0100043e961828480000c08c040002003202e592240004404403400d5441c4d1204102c1c05d00c40700f0b0b0f1101030b00030004d01c0404d52080d400341201c0743c004e14060b190b40240e400007a040c5262580341d071005034401500d803401e01215114917500a824003008106011b07c250341c0d180c03085407020001040c081c03500005159143d041c480c01c4036203030b401401d490f415121109101012080801d007900064a000c00068106d401410101d41c181503c26001c400c04e494002e0403406040200070b0950801000e01c1100c00306d403a1840006103c501540707007c0344020800c036540d850090030814111034250081d680c03601081030324085079040698900e060703651742e40c0e20005842a10418082e41d405100f00d6928070144942c0c00c00c40040c41000340c0c2a100310302da42c2c20400595000d0078a415480350 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 293332967 1250 293331717 293331721
    0x806090c040806070e010c0b0106050a09060809060c07051011041505120402060a0201090b101a0703090311011407050a200a0918021002060a1508060a0c12020f0403060e06010e 77
    0x50300410360790b45d007441c2c14074040b51000300650b04c000c00740c2c401381c3c458004164040b0b41889100c0d04400d070034015018600c3d181c845894200700056544101070700c2c0c1d010a04002a001c010301c00c090208191aa00c0b004082c00b42d18020112200e50380d016219000242e038100301086400d6110310300b03c660707103a4103c900c4503031078890350204034250384107455070b2047d1b640e2400d4940009600c4600305100e6921110980200c0e85814142e46400e41501032034a0451130801030140060b03082032010080d65000b20084940e011540c0040c1c40822900103650149070b0f0100b03d201c1040f500145400006204450100075008c0c000d40c80c1c9078134070300c9924643e8800c0c2034613000e12414030540c0c84020360110700080307401c6501140d004146800128222400160880010000c1c020110700407640c0344410183c20041c560324008000307450700000b4008403c00382d190307902200300610a5005421070202120301315a2900c140d0030945043d0701602c0206c80302c4c1d0170071510000d1910b0104070b1a0480d015805103100035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 293334217 1250 293332967 293332981
    0xe1e0111100606170702010504030c0f0501110d0912180302060c120a0504030b13080304111914030c09090c220f09020f030a050d1b02100806090c040806 67
    0x10500301140e0090301c111101d03680d80050358016200180038540310315500445a403040340390990010300c00029681420b080c480000e6012102112154025140c8039501210345070040c05031140003601801c50700041180c1c840d07220ba46d800074191a00c21b00f030501a10307405213001c3d030303134484001c00c0d401c01d02149440c1040035040807801000400100400d59800110081d80400d850708003c0381d400004602280c00e100f013040c03030a1140d0700b001842142000300540c1399583c01d514800104020800c0d03544d18200b047d00c3d03d492503481e8402094180c4851443d8a41c100500d900d13021901c13407840392080c0e101c8000c4a080548200d4000c000e90000341050028003802e01c131061904480754507403050f5290400428158070321a80501c040342c44408641880f00c0e004000c0e001e01c120041a10940005001c000003a034001186012071009041442e0141903ca5641031003881200002e50812400e400004089a00c000721510800c012100702015032580e402500c8903001d540a0200d0a50080f404106c407 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 293335467 1250 293334217 293334227
    0x105071413050d08070b0f13060207140601030503190e030d1412090a0605011d060103051005030f0607030e071203030f09021f08070f0c1b0807080d0e1e01 68
    0x100241d2841406555503650011444184500400f501d1640d000714040d4100b1045e01c22032030f040107407030300c092a075414111800309486130705900040013207500061072800c2120202d0f00c2c00100143c0e0081c2e03134042da92030620035100e600102503294455180345110340900d0040d90707154001d03440513001340030840c0450f205640c07581c946021a850144144084410740f51200b02103849007420601510500116241040a445043c2c202c82c0c0448034a40120090003a5070035015803107502483c02091548030340314080114603441d046035415004050081c46021800211f80e4000d500c1a9804c00c0712100007160503880e080c2501408643d070b1885000000842d100c0e4006205011206100081c805465400240c075494514004410045400424a9215000800d03d03a0040340707800c1401c030944010200803d407911164000340300d19003c1c0c5001040708010b0702108054042c1008444955480710072450381c58101c070054000155100d0503400540c10442400801500c140c4041d000800c040801518 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 293336717 1250 293335467 293335477
    0xe0703050c04090809540a06091404020307051005030f071806020f010b01110307080304050a0c1e12170901021501090207060b03030405010c08070f02090c04051201050714 75
    0x1800860620401c3c45959509030745514065243c4099850b04034001c00511040c6c1e54060b105540c1c1404d1624506255001481122529410f548444083e50760300b080310020081c0741c0280084601d003000802a0307010202034940254002c50031035080355525810000303909030205d1040e000400c1400402d8032a00703a007070340a030401010700303204501c0e8000c1c9451441c44401940224010707480b50000a50260082c0b0810140c05800e01c2d0038071041020b480355580c1c9103e00407000f018100c0000004003401002e105101c0d030907501c000000d0602c3c0d078030320756001138940c0010b42540940301071750000f6007070313807080240c0c0051640704450303942605600f160250950001c040b001e056010f500c46100100030240d1495029003100301c00142c0310324040c1810701c12100703581d05060096004000511803a0b030002d4030a034070b0f5036104000f240e0350940c078900070038281aa003c00a4108607150f040c010b20300d613000054010b941040e00e0380340400c3c80c400400760a81d03c041c0d0358080402c4401540161017072015000b06 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 293337967 1250 293336717 293336723
    0x102030919030212032809200103020706050112050706020606030d141909080d1b020d1505010b070b0c0307090302010503090106030c14010f0c03050307030207020a0509040311010e0703050c0409 85
    0xd40e1543c008507030303041558001c440ca002160116800c07214a0200305040090b4001001b4041102c070b00340750768088400766a40300121101d522002006010ba200c2e4040711001075000f9820f01040d655240307031340c07401c56412004990502614201080c1c8600c001482480ba84005006144000d0080b50594814001e0b440304201980f04121024200406c1c005110394a5900d035240f06c809842c18030b0460a0103c10742084c3c00304a611120340000c00d1190640083c1250102e0b07030720107540c07031500d003850140a034050112a500e01f418000038004022801602d407650165007481d004c0c1d920b80c040c950781031104032608400b08900c10400c0c030240d4400d20207150300110040c00054000d41340d031902e050085095021194000d042891000e055038040c0326452a28010b082110344481c2507940074010f030100404080030190f010401205543d80c030724840c0c005180150200d9000d0400341402400b40d807030305600350103075801d01040c84566032000034018200c9800601a1811000e0b00081001410b1200015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 293339217 1250 293337967 293337973
    0xb040b060103020c0307110406080708150a060815040209010f0803030a0c031508011a01050f0a110a0218100e091f0b031c120209220e060a0b04060801020309190302 72
    0x40c13180380100304014042240904e0740382002e0422002080f0507500f0326000f03218280c20003c020444020f00144008009151155000c090350b60012400010030f01d03a40143c41700e22503494401d401c0d4074a400b105001d9130080d202a1000c1c2c2c3c03104104008c1d50f0044c410480d0941c820000030700110301c1c07680041040c4626140c00700310001d103181501c0100380d46800045440c2d640300403000100c16801c1e800441c1080c00c0c00e04c9400c0c002c011403032401138060303140841d05000d2002c81c06c0c004c01c1403d02000d4a0294000c00540c4101d0306003003442c0c00c030701e42110183d210700442640030600000d00c498091103060103c0c001d01c1e03030103000c00442d0710107a01981003c4007103444103134030243c55509110f5140c0001d68150141da0f5600b00321070040aa40d030020b800d004131071040005102c5603c031801c1922100303074190641c40f50b04c42070a110000904d00444400c403140034440603c0100b0b10550032014180301c1c103d4051082545031046070b4200c1c4000e80e0600030350341c040d4103c00b0205c2c100c2c00c80107001030301034019 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 293340467 1250 293339217 293339227
    0x20a0c1202150a060e0f0c0a210203040b011e0308041e03060e0c010f03090c1203110607030b210d0e0d1a07260103140c060f070606120b040b06010302 66
    0x40d06180c600300360f41544556031900000d001203a14110382d01e6100405401008403410240440380c40d07442105d10b9102001108200325140310343c03090400a1040700100110342d02d1503d8180910001420b000c0c00c4140121944590070500560f03615100380e98105030603502c0d0926154104940b901d003c40702d180d403050080390000c04507419108006002009401130900184100c000604403800300c4032a2007818a002c4120700801c10006501d4191112280c0601d140c0070141002d0340e40240c101070183d014421030040100c00355140e01304d01030307500060700d15841c2c8001012100002c1c110307454082149520008005165520075034100100c514040d04014201400c1d490328441d992100217040c04045031a401e0289055000501d9018654502e5003221500c2041501050303441c41840041c1440030403009201c5540782c00e02840c86030b91001003105070b803010407101c0744e070440d085020709951040c50188001840c580b1101c80c04030140d445000c240b115a1695030ba1a0189030151820b07041540c04c1c49 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 293341717 1250 293340467 293340493
    0xa120e0a030804080f0601050108091b06090618100201020703020303160e03030708120a0501122003070e040b0c2b02090d031106060604060509010305150a0f0f050103020a0c1202 78
    0x30040c405003c0c404d01a0a203032600e11015458407506a101904001ca40c0b01044203a5001003411404035000712003800c100c082c0000083c070740f070190002a551250000840740500103100c2e00d00a458141910704040c03004604000ba4203c2c095428040c002d604100000b40c021043d000d5001841e80441c202806194500b1000c03d2450b00b01e86011222100c002402603c0354164802195004601a40910040d81424407008000106510042100079104010340081501c41030381d062200c400344c102d81c0c500d90f8420a8900d640029282030398046080c2011a0003519204111001d440101c01c0100e180452541d100c8140e440e201300c03200100d40e00b8070102da40317941c40d803d400c81a140aa526221404040707110fa50400001403e8a44500c4040008025090300202600c400e0082400c00160980c0d940910140034000f00b84141e501162400b008141203405403144426140c1032007400b010b4039210340040d0300b2481295961408101c00d090340c20001008956102c0000150b4816944440400c030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 293342967 1250 293341717 293341733
    0x3010c030b014b0207090b061602010903051209041401030317090709050f0106021e0d0e03031b1c030b0a0306091104060f140a0308040e09070b0c03040e01080a120e0a03 74
    0x843d541d40d440c1d021020500345035810486440030341055401044900c0680c800500e85200d9901c0841081d400f40b080d59055a000750076010085803c10143c03101c400d60b0f003094006642c02824811311692402000210500d0080700c2c0d14140c0c3c2c0c3c95200c40b066a50b0a03085003c843c50000d004142901c9180d90100d0109058040d84c0d00030703c0941d0b4004450350400b03a020303041841412820154071140e00e80200d911000041000078004507050803c0d400f40050701190031842100301c809625040c1c8030130b4121101c030028603500108240c400a000603006c0300822425240b1000c003841e800b185140b0309202040c003d500090342244603214807070508441001007010f8510035480004262030f1620b081205280390f0f0200d0440d10f1080728208841401c55540352141d00450140300c0c20319118200007a010b01082000a000c0e1111550342038490786007011855890384180140700b4a034840c0700c00091140f800060322400742e80c1c09000140c02a818135400c4900300c0c2440e81443d0301c500d11610000c0402d03602 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 293344217 1250 293342967 293343077
    0x120c0c0a0f051e0f0606060903030705151503210904060909030e010201060b09031b0a0f0b0c10090f02121f05100e090703030324090b03010c030b01 65
    0x180050a003512003180c2010f841c1c500c0a0000381d06030080814a80b06a2002c070386a03038080800c403499604c50000d400842c6c45c600691400400e9440750051a501506011800d0351140fa002280f8500700940c581c24076488400c0500c02107d040680001035580b103004d1006411119405480003039840c1c2d580009005480c0e01d054240c0210307219088152695030b081c080c01c400307800c00c150194500b2030081c001c299a4020b4505080304441d848980d40e40f00c0d0303034100c1c03000c0080c2409078a0924880d128803c40c00542d01c49444001c0b140704001604116a02501454181d0760f0081e0790240070300215001e02030445048a0704800c0c2c2c1c01004001e8504184600040e034021192002c0054549400c40080360045c80f95080081c100d00080304112402500103009000e0329898500450003018940400d0441d00001020880304003010002042d072807589e600070907056804800922540c01c0c102010390856031880804c078000303003d02d00300c050070241c4c04a165416011020001342d0000c40c2186500a4141c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 293345323 1106 293344217 293344223
    0x40f0513110a23210328050a050c0f030a020c030c31200a0e10050405151605070f060e031c030f09030210060b120c0c0a0f 54
    0x40c240703074120a01040c402260190b03420301005442c1c0c0c009203900e0203004d0381d6002a1b0903411824410007080c0040340c440500d040c08801c0112400d901c011500c1c0d03194484c90810710380341c410401c01401822116406000c6401045040500700500342210a10912001914600064048442d8921000e6010807050304040390741480015141d0b1704201400a00000c0d0010003002d20b0000414020707c9554402c0d8582426808002d0600b9600400d100000c4081c0400d00241c00c00310050442e8506542e0240e00348000d0002d0a40c904000036412240d5412070f610070882e04500c41d80728000350041381002c2024140e0782010a40c0d039200842007184070035201d800350b070f04140260b20582d940002d41c0001e00403006039003400b80d560202d1141184170240f4040e80002d6040f044000e03509101850b400c180829102e01c40da0300c050342c019401119190043c2c41a00000a003200c0e0144c1150748 = true := by decide +kernel

theorem cover : BRFrame.Cov 293165467 293345323 := by
  have h0 := BRFrame.cov_init 293165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 293165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 293165467 ≤ n) (h2 : n < 293345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
