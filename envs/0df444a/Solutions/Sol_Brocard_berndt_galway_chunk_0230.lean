-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0230
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:37:16.079585+00:00
-- url     : https://prove2.me/submissions/8dc4ce30-9e7a-4a55-9ff8-612ce6ec7f2c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 41187055 ≤ n < 41366911 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 41188305 1250 41187055 41187059
    0x90b06010503010e13020103140c03090705090606070b0a110a02030a080a06030f03050901020c030d031e05040506011a040504110403021903030914130903170702060609010308090103020d090b01090f0501 89
    0x1841315550b00900c2d62550080e000703141400c590180d045840394a58640d200d041c00e2801c0c1000013569041102d869480788a900070000b03450520040ca503004000c094051841c10202d030315102488100580482a01540c0b84480b01030003c00802a0844a0103907000d190b40d40c045e072100030701c1a0005040c0c00351080c5800c200b040000d522000c46100300c0d40c1401e000e503c0d2141c000040c0c0c1400c0c200e0b42c0154240c05242440842c0d10350640c440854400312a10350600900f41d40030080c112038003107900801740d0740700340e0041c0704c0469080d402d46642012011003e140c0f5031101c0100701500c80ac01184185600c0102d810b0046243c8104000c5a20351110f50030000145180c07001044000144640b844000b080d501a6a01e0b071207000090348003400321401400074551902d401844001c040e64002461007031100444c152510100e2030500801300104031140990a58807901525800384101c01c0c14140d00f005019500c14060042d04d040a014108403049076140821040c10340d040d0900991482d4a85001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 41189555 1250 41188305 41188319
    0x6010203090f03010b1305011502060c070b04020a03050a06050a0501050402090a05010806010c0c17060f010e07080703020408060709090b01050a0c06090c18020c0d0e180403140d090b0601050301 85
    0x950707088020031100c0d165804050300c0442e0050040c00f41c3c2a801021000507010458140d030009412211700384004e10384400000e100301d0302d410702500d4100240d4002c0004902107607030701c96226082400246840720240d960340d901460200c04500460314251685c2c200b0040c0703100703480780f5401444140c1c0e00750300e0136400d030300044c14010080c02003d040c4044480401c07001c0c0d21520214220710384c0070100a01594480000790044050030301c12340241d11404000401c0502603003581d90403a0b03130150905c0321a840f88401941c4142c0000c084004043c0d0034000000e200c00104616805112103884070100203003401410f4090707584e04101103051000170405d8002207507105045c02100c1d5004100047d02e00700d10b1410070014161640318500d03107400d100203105610b61640c01032140c44000340895040c003160000a0700c8101c071140d52268006e000090070b1842403100c0c07a445500c58413a103420720000044044071207868200c0700c2d0954045079510182c03803c108609121310381041c0e090070482d05541c0740c004 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 41190805 1250 41189555 41189557
    0x8060a05031c0908071217040308030a0203040204022802070b040b090f0301060803030c0a0e030105010e13030c020907021e1b0d03020c030a080c06060f06030601110a0803090105040c0e06010203 85
    0x2101c05485180000c0b140a89442120140b02400641041e41e594541d650b20035086101501400c3d10008240c40d038550007400004101c404403507004502d2810b5a80d000800002508000c2041e0f0300305400300200790841c40c01025250000c01c040c3c400c031198000c000c0000f4541075050704800c002ca001000706100c0540b180003901c051010450b08442e0440302d0741c0c040380c050885648440c2e070610010050280d0701080070040e0081d00c1c40c954070050004299000c06080e54409c0c03207041315400d03032180400c241108264880000c580242061b00030140c103940440e030050000c6a0340e00050f0001c0000e101c82d400c016441001d2480c07110028a0723082d07080101c012084034000740c400d21407c0c05401007000c040c02804000030411000b01928400e080782d0404c40a50fa00098105030540100b030b00103000c614016640f0791442030094005400c654032500151041020701c03140c543c0b9441800e00200025160000861181d103d44001003840c1c28a45042e1142460301d401c4400345001e00360800015980c008 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 41192055 1250 41190805 41190823
    0x131b0608180c040b120d09150c020a150c020a030803070e040501050901120c03150903110102132706080309030d080c0d021c15030b010b1602040c02030412050703020108060a0503 78
    0x7140004c20844400c001088103084440d100340c50701031100031a071000d03088004001111885d103410782800324055801c0781c2280c206200294842c18020092122145620040800c045141480307803400f405c0b600090743c2c0e00410381c421540c8101c000100180c290380310006140c40b40c01505c083c001541050001903921005006003104900186c074083c050090101100700119004a0340081c0300c800e890010020741424203065010451426189141003814421100c80c01c0e085d0101009132410503d800081d2a18442e8109a11a40341011075000c3d99620420000b403da4000039980c170781840c000d00d81807110410818041c04a80c1040040800c0700000305d07151514103400050f40d848501e1180e00758031108071b11101c201c2e440c2521120482001d42071403c00c0c2c901480310361241c9c3c0c0e0b80304202c040e944640d810380030f900480440e0000050400d43c115000d59011401034a04040e100c400301150030090b80c0341a1103c0c0e002ca0810020765800c400210340008042c1d85141000d810036010030355943c101 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 41193305 1250 41192055 41192059
    0x10309170304050a021206220809100201060801020408070905060a0303020601030b06010c12110721080c07080102070305190203040e04030509150d0c080a020c0c09131b0608180c 78
    0x600f08441405000062a401005441d420060388481a51405d0484000d241529440e4400001042c1607005107175080d0721900091425600c0e03003d0010461181c041c0c48103644d25082d0108260764203001500c007519000c1c00401400c0d10303006070801910b2025060902845e1100801c3c0302107a8007081b014117480c0c011002d0300c3c9585600d070048038080ba4240740904000f1715450f4481e051344e848907a5140041d000c03000ca45007a91079400d0441c101c289043c44d115801d40e80075080e0001200c18000e066001100c8040e5140f50b83c0d544841c80c02d80e407040004500144000424158090003540d054611243c0c3d8030041d0305190404440703019100c8090b0014050200c00b0a07008041e540f1007a01d00080501190301c543c8034104000e214003e0101c10b518500803ca0840010380360142c14402d60b0f086008280023040b0300c11081c41480031483d00540b80311034a408218541c400b113280c00c817035441c0d900c0c03083c41442001e51510030001d00ca414040d2610781003070001e64520b000e43c01e0014040903000e1003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 41194555 1250 41193305 41193307
    0x301050a110304121e090806090c0a050f0612010609050a090207030203030109050c070f0302060a14040c2603220501020102090d060506010c020301050f01140a0b03160507061805010b01030917 84
    0x50b501c06407805004d001c178801d103a03101080014181c0c0c0d0b000040d10225411281180c0c1c458031a406190f856402c081b800c80d40269048108100501e40302c060f440801c000601001d140440d00316000d0182d0303070709822a00209550043c20044c5040150705500184100e600031814102c50382d80081d12031106104020034582c80700e010424122100c0100c802e00c036404400c640c5003444d01d10300a074441004462001c5070030710300411031280d0848803940e00e100319400310b042401141807100c2900f0300071813921240303003101c81030742040b0340d180f8100300130449921000f54000c1c600760042c1203c0803400c02500620304590040c4080d80043d2110003900a00c2035001001042d90703542c00c3c00480c0d8202400d000694198204000e000e00c2458102c040783c10b03075100240c0003c00a4000c424050401034500c103140d603008040000410003515009507440103019403030020714203200c07a21078105031881c0b00002803014104450080070090240320301001c94400f828140700350011501c403981d004112154014541c0303c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 41195805 1250 41194555 41194583
    0x6100608070e0d02060d0504060603020a120206070807050f0a050604021e100e04020c0d090e090a031d0f0a090c110615010c020303070606180507031e15030215090301050a110304 78
    0x2451006a0b604046c0482c0100014601030401e18080c08040c88140c0c064182150049500380000b900c42c060316801800e000d181590660360f0485c640d01900c2c0959403401035110848141c2814020103288034010380041499041c1401000325400e454005820f0b000704a010440045d101c040540103000310740d00301800c0c0b01c081c42000c200030344580300c58035001b03000710756000c09550b8220304000b0a0711000742c9510501c0c0d4691268903030300d42030660b000d00032a44d03074801c2078602c4c819580c040c40922005041c0300034400c10036010400344195500b00c14a102e44560101c00001d03400041000b040b00018010310381c07820601f0f0303003070f80c2c05502c400410b041041090030442951820821036519603030060003082040d55071008582c4041c540c0c7c40c1680400e0504010503c80c3e880707809200c030030042003080b90029080703020400004001440303481c180003504100000c05a55a22f88402d09242c0550b1900e6441c900c11003050300711980148400c0416141800c1407041c14159010307280c1c46a03004100710714000c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 41197055 1250 41195805 41195809
    0x80f1b100306031e0501110301060206061207030204020304080a0305060901030c1203270807060302040e0114011e030501060314190b011b110a0e0603100f0b06040806100608070e0d02 80
    0xb1201c0d82001e800380381842d0442d4204102e00583c280014000d40c000c020340440c0780b020684ea40710a01c11400141d024002080d1a450051035103456014841d0848203416500d81c0410700307980045400359803003000880c1c43c4046c1d40d00342c025158010001c480c5e034802e542c10359961100c8a0000e005401e40440050030303040425014802054a088025000c041c101640c5883c1900c60b01c46405540c00394000e680c0000784c1d1900074002c1e502a03610080103200a80e00780958002c21650b0303031104504004103848070b4243c4080f00c007018018698a9039010542c0d42c1040f401400b0368918000c241c2004800504000f001605000400350141c040600402c10a0011004984072440141d00091301046400750301c00308400100c002144510a8410f0a860ba40e102c1c08402031600850f02c007900b580280e080c29016000c03a030300c45010000e540b400015403d0400020800c507412a03081070200d80d1204043c40009280003501c0001045545070080701480c240ca0b00804078558894194021401c40031400115 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 41198305 1250 41197055 41197061
    0xb03060a0e150406170304090c1209060524060706020d09050607030608010f0506060706090203160e06040e06040317040c0302040203040b1504110423040c020304080f1b1003 76
    0x1c0160612078074181c2846480d1a49440c4400300142c4500e00d098000034010420f0075101c00e01290301000345060600e40b0035524080c0c1101810401041141005101e44a80a125070003106000761000189854516142e83c0c60002030a000880380d000c00c5521b08465441c81c0440e100250310140143e11010400790b40c102400c1d04034001013032405042c08020000e0f074554090011580400020b02400b25429a05c008851007507030555003100040203850080340c881d40140c2e80301c51000d01140d8860500c480488054107060f00107141340703850f4500740511031405c0d010f80d5a02400b988044c1103281003c0da40a0200c0502001e441aa04145d1000509101043c100d8100858020348203550f07a14061600601c4c0340000c44808041484c030441100080c280b910401040807800e1900c20300c0d06040c41c0c1341c29030f1200708004143ca0b50154526100186c0c44030700550703500b0b0200780c00550b241c0381031110031402d001d0302e4600803829a002280d800b003610040301d014210b4150a542c120103d5510000032005 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 41199555 1250 41198305 41198309
    0x80403020306040b1e07050a051305060417060903131e0803030c03070305090706090603020d0b03010612020a1e05090604150806070e06030411010e011b030504030b0c03100b03060a 79
    0x4103025442c104000e1010140205210ba40909824a80704403110016030010380d0548000000a4051050b4000c1c540100000c010051814004009041c6d03500002411540950000600300182c1069011034040030400c05400c40d0903075001c1c1d030900d501c21030509100007072842940701d0015104240d61003020081488030240482d0015250b0780d1808840030b100582c0152680d400080c5070000240c0503041c0440d4a40c15181e05584900c42503182c40021000f82d0040305030541c50030f41d900700384240c0c0e41d002d10920303005194007500114250035a004100c0e000c0c545900c00c105c2d07500002c02c4044402c0c101c40420090f11411900b4640540f0741c40c0100d8000c03c100c2281080586600b4400714072007000140c29845101039a0b2402000111641440340a0200340c8005102d900611040398180d07000e242d00c2000910185880c225a0b8120108001d1a601c4001c06401044001500b48140504081c03026401070f505041c0d50f107181070198030440140d41d0307441800c0b04980c0120110350031b41c1c4e4440c81c10300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 41200805 1250 41199555 41199559
    0xf04141815011206090f0c060810080d020d080a0e19030f02030f070f0c05040f0f11070206030103020f181e0a020a05032403030a05190903052806020307050c010c0305010b0f0708040302 81
    0x7520036154900505200001d0b118210500c0c6242e00007c1d43d0bc0c00080d440e09081c02075400340084158581083c3e0301d08902501c400c0c2e401361034210000d0700400422a00700380010080503110380f580e039410080c088101070860502150020040440012100230032101010742c403500c001100900c604100319600540e80220340c0c014201408148200103503001010846100b8a082102e800e1140e02000d11f44a0020002e400c0702003400100050325141c05c01c8982c404002d012560b010100e4920003009c070908640e0201001038013096a03e500d5042404941c1c480c45581007145400038915003d80140030041c4000e903420b0016020300301140c0102049002800007808481d04c4d588011000341094015500c440343d0001904500003e4511030b1100c3c0b03003103030b410202405c0c0d040c10212041c0ea0008a404a0740c182c404400a0140000e50902c000c5205030383c1a503900e03444242600e880d909440b007210208007094100790040c00907419548c11a104c0f03114445030582c0c1c80059203041c44540c0036551002c0c0d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 41202055 1250 41200805 41200823
    0x307080702031306020d0f05041202040203040c1a04080106060203070803010e060a090c030b0315060906060304051212090c010804030206010b1c05010e06120a050c0f04141815011206090f 82
    0x20b0384c941c00007541c0c1480842e9071128400ca01a0f45011036590041d4800d511050f1610b100b56000360819500030f40d0414000c1c0000249a80c54418080d50751400704445203001c1c0d0b0004040000000030700c0341c4000f40a281c805949800220384031040b1340e02060003414038400e070380c0021423026503900d00300200514254a050100d550200ca028000f8084150014013a0150b940d02004045205d00d840c1d214100003030041100303482e44400d1268680008004071a0703480380348501c8216580f51005040c02c0f240c3c0b0b8034014a80e140811401e82465490f40c45e09060100702d5080c0b10020341c02041145c1550000d40d0171a8890356580170250000c04002c50f010350361407400c4008190700d2420403a45100305400d5407405030074419984141d90301c0789900f601805a8004200c860082c0c5480c0301000708901e80103001140d003400d00080040d004d64143d035086540c12100c42d0001c0341040501401c40039004102114006602d0400759828500a10344004e00065480400d0b404101aa850620400760444440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 41203305 1250 41202055 41202059
    0x20c03060703020a02070504051b1303080706051902090a090b0118030b01060206100311010c0204020c0f1b0f0d02060a050c0303010b09130203071b020411070812070306060503070807020313 83
    0xb60003503004410480c014024468017041d40e080902640d4015000801170500e500b034000c0c04108103401041c469200003901c00d2000000c58540000303082ca80d40140d0700062075040629801543e68644501c0300710103030043c82540703640d541714442134048608107000818217000748401207074841242c002d41081c0da4800d400200900c1021610203050720f2164080b1426078030307840884944e0705050300c030040940424002202e0306512440da00c61030144040c002605022944601c6400c0420b03011021626a008503050440e070f0741103c001c544095010b80708403114903541008909440030581c4007174040e0100140c41c20480388610211030f44050080d0650381c0745c0d6162503400c030845d4061012548111442031a0702c0125400748200d90041c81180c0340c24901c007035101c05030061340d0403002045c2e90107a071321800711a41d0446440180101c2d442924256629080d0352010641c004001c1c0c0700c2000c15203401c009201c080e030080c04488e0810750a08120040350388a500880c0385200b00c0c084c20322818014840 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 41204555 1250 41203305 41203307
    0x20f0a030302071118011e09020a0309020415050a0605070512040305060403020c041a0d030c050102130e0a0b150c070f0b0a11010507050d0b0a030203010507181d16020c030607 77
    0x1400110b0b04c03401c040e49139420300c02c0c20054801500b4032410266400d50300100200d21242d00e107810180005540f159019544060400032a0800400c01c0082034454035030500f14641480f40c0f400c0041c800c4046000f40341010003041c1001c440340290000d0044c0000c0c0d030b00900004014480000420050300c655807500d134900561150810b41c3d00301d01522645c0440318a80ca01030140b641000b120405254044a540041006004400c5003d60601c1100c83c04000400c41c03e0004081000e5035101044405103005560000c0c001c00608030b1418515281c4995901e13990007038005a400d510445040e142c501410005042c401c1c203038400344003c414040001820104c8001500000042e601c0c0d480800d201e8aa86900742ca1088446400280301007000b81d8443c0c0059110240902014000b006040d032030798003180c21100c05842c558040386064070303164450032070601d4002c0039200d1080c81c8542804c401282c600c0c0341c28060007140d911000403282d0302c000d41c82000003100141d001012940300b4202400 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 41205805 1250 41204555 41204557
    0x14070804120f031407050a0b180106060e01020f010b100c1b09050106121a191805041b0f0e06060d050403080f0615070b04080405030a05031210050108040f0201020f0a030302 76
    0x2022008a80200315161482c0415000e17184403540103809050800b80983c0d94085219008000350302c01c0a4403d01d43c000c82000b4815800030702404d07203a594440e50608d002a1034002d011a01a20f00e82c140f07098050307283c80b894441503c140032410504641d0649140092000c0000c0300307022103514003c00c0004003505680c0013a812110709844510840d1140c925200a46103000c82e003450210145240310800c0c06c2c400c1d00c2000320702c0700c2d00462183c1610741a14041e4001c0f0600c4140000b600c8002748401d0048000403988085000100d069030207241c40003851240c2110721401c0e01c0783c0d82c404000389280c2c403100704407020305642c26800c214a240c546001750801c83d055079502d04000400e4009000c0b402c100c0e0b0b68252071040400c002c0e05105032030b6a2544e0641c4000d1085802400520000070103480411445101500c90300146031030710080b1501c916984001003007040d1034140140b04220f984d030040a5a03400c684c1100002c003c3c4001800180c1c6042e00b90a860961740c032520388a41c00b4154198 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 41207055 1250 41205805 41205833
    0xd0b06250c06030212060f21010b090105010923010507021309060f05060a050f0a15050408100b0a03020d020a0e071709030a08070c05210406080a0501061407080412 72
    0x20444070410341ca4a0302281280582106050003006000201d80140350210380c602115000a102034519004103511b2154003008040c00b0750607079183c000001162a0200340540500000c1c6040194a45030180322039071290002e00c49409030350401604022648950121402c00350041c0105440d034000c805a040182100c84054600c0e40c503142c40882d0301100c40c0103081c050b400081c0825507030781c28039040003001192400307455803081d0180c0e40000c014808802581e0f15540329103d040d00c861415000d10b003040301d0160584070b074910f001ca540400c0e81c2c03056030060a4a80503a01c05901098a02c0070840c503d210760040503c40d81ca0070b080103e10790380400e2443c52550002118481da8070340b00989507503805191000c001254449000402d85481038074207a20081c015812201040080e0700c184480d4550704002d01c0f0f18440019091003e5504603014a030401d9058004002c2985441001050218003a03180100d001d000102101402003181c140d50141000501e004010403030352410202075003100c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 41208305 1250 41207055 41207063
    0x7050a030c0e03030306010e04091e0512070b010b0d0f060f08150603060c031009021207080106080f16050904110409050c1e0714011401030605060f01050d0b0625 71
    0x101008007121445108a1012010040d0045007503446140040d6801a00809100d03041030b62410310201069003a18980103006101c00b5000c020304107414058107014000003500c081c0d1008226400006010f5540181100c05141c5256220603450121a010740700b98900f0800e02c2d82400000710714040143c2081d0704588009040b110181020104050b0358103085488541c5138200f4000100c4420014005543c8003030407400c0a81d14907150031003181280c2211a500307805421210811854540000c413607405040141400ca03d80d140000791051481001045800207100700d0310350481140c011019a07128041c002c006005c500c504a4184440e600540b080104035800e02c0003083e461400c1004607884260800c0e0300c2c1100d0b005440c641420b0344d01104040340c00c01e0982413542c01640c400e10400c1c101d801400003030311442d403550030003506a41c0060030261007800c2b040e8402c28a6038010701120b8851600c0c81c404140e03044101e0001d4503a0242103088030185524145d504024007140f00d2025034184a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 41209555 1250 41208305 41208311
    0x11b0b0906011403070b030c0a0309020a06020d03200318070909030e03010c030615110316110301110a050702040b040e1203071b0f03050310170c0a0b090105070201210507050a03 78
    0x312800300341d5600c00031b2052110216040002ca025815124000d101c8600e090501003480001d41c5e01041968a940c0d1146005130000302c0c46004160317042c012102031005501c02c0d02c00007170740016010410310000d0000b540341c150304a401c1810345c009006402c005c00440d40201700b1507100341005040d00340704180c8184607502e03040d54104464040c0c0300302c000381d40c20440c001e82401c59030036040d2500365002c1c14103241840b00384040001040d48900070160107126800c900b4040044101785804e50701010f0070403417031000038017100e07422503480b2060724840e9804071400314000740d00300d0110b0300070801c008100e41da0b07000341403040c0c03001c4624000544c0921034a958242540300390a85031080311504140c01042d030045c0a03003201c00307e48035401464106161641000e4200c2d980c01440d001c20a2031445103549400081c0034036910302e4030340030410040028296075481c102c41040001e106220304600241400149540c01c94240d000c0020000302c998022410080341c204160041c1c000d070002c0d49078500080c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 41210805 1250 41209555 41209589
    0xa09110a060f0c0503070b0703021902011103060616050d0203120714040608180601140414130f0812070302070210021f0c030e070e10170c011b0b090601 67
    0x1401500001280d50701d039181403408030808412940c42480001c01d440e0f500c41030000c3d07804104002402c901600d11a200142e82d00a0180501081003402105000b0341e458419145081065102160340c450000c030382c010380e59003c149141c241c281d2800c0c4080e19038450401c0e88412036800000a01c0380400601c200680399890b5441240c02c005040002001c4800c28041000b4441c0210300c000d40010a02c2e45490780300c0700d240f0001d4035140e4240e05c4a61b00c1d62008059040d981428820b42546151b140c032550340e24940703810380510b00174594800403c11200a0180c80a00c2090030549100f1030740016100c0e52410031030740040203504910343c260310413a0710341c0d0706482d000e000090b4420099512000e0300703850360030360071001c00500c0444e07084020305403554844d54408205010f45070103003d0b103104040b020700f0888134010032030040e43c011201782280420540100b400000703407581004000d117484464883c001209109104545000804801c0650207018407603402141c1c0c40d042e0740f898004004080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 41212055 1250 41210805 41210809
    0x31b050a06090909020d050a030e10020705030613020d020a03150605060301080a0f1113090615030816050309090114010210020a120b1c05030d0608010908030601051b0102030a0911 79
    0x14041c42000c0c0440c0c1c0400040007055080c0d00454101070005212146046941d12034070304241501130100d002818003100741c075062400380c5160411071041d100420300c9034107010202e541e0b00d00280007607049404960207441190345100d00344880740da0203030000340203903541d191a0003070014100d400c503902401c020001c5aa8103020046d41d041b00d40322401418003403070a46819006180245040e600319003c00c1c0314124648542805913443c1c1c10700c03003001484002c1400c3c103004840b600150503071107901d01002000411003560035602c46a06154600d50046100d20b8820705e1741c0318070003080b5048003a03200009201c7c0c10b01400c404c80c0200a800b41e0740804007041c1030100328403c158114020614014088081c1d4041d54054205400b02402500300440006100000d068103600c04a0f980c1c0c0c00082c4c078072000400c40c042c18000f060800024031169403203503202d039124000200603504202d00490f1614500ea060150060f410428900843d034234204900840080c040d40a4141c58200d0b03036207800050b81c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 41213305 1250 41212055 41212069
    0x70c060503040b0105010507050a02030601060e0f0306130206031f090905250b070201020a0b04140d0c15180f0501020c07050f03071418090105010608011203080a050702010f0204031b05 81
    0x141c1c3c0d00429014243c0c2c24440190340903001080c099640384a220044401a1000c0001d54040c220980b9600b0f00b8030510030400080710183d032401e5009401ca041403040001da0240d2400c22f2039412139116480e03989071810404104031090f0441031085a041c400200c2241075841200d0031402003007950085c0c59800014208800c0c80040342e400e003c814202006a00740040c0a070504c41d01c1403041d1518094242c0712510175000554054481c1c00ca140712800b40003104122500031000320303003045280c00300d20781c407245c035851b04145881070005d4452520000400c200c81440c3c044582c42070682d4080c3c030107030400b40c1c000e4110b401000b52903c6030b940701107000c3c070340904581114400100103211080c10090104105402d014100350400e00c09688290241d1081c000d051241124a00000c0d1540c54500010281c0c481a070096000295400c802d002295200f264290702c40c0242c400459291181c0d107089004200c13035008540c20500c00705000c81000510310080702100070494401c808203884104100c1320b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 41214555 1250 41213305 41213311
    0x7020d0e01050904020d062c01030b19270506060303040b0403020d020102010213030807120509010219050c030a0b09010e010e030703030c050706060b0d05090d020a0f051011070c060503 81
    0x100394104036403490341d84940024245050007800c090300301710b20070401e03034140c0e00190031080d41c1a45040c00c6500d009401402040f02e948202610300240d491501ca4000c1c1100250450600d00e684e0407035505c1c0500c864220103c0b000c00c8903840780c81c10b013810f5103c6ca080518460112424040c50022505034076001090b6000e50302000c42040c9044e01c0c5a08101444169040c01c905654080c040c0203041c005003818100210b0207078800659601192600e040b180e403030424190284038013448400030f80e0340c0c00560303002441801286004070340307090b0815519149041c2005a81407141c0c0030f07010100085001c5940c003803421080207200d182061280e140c00d8944c1c02c20142610b6000f4805500428402c5d00103448090b05801c08130301d4581301e5140c079420743d82c0d150410307080007900194110300340f13400d84076441e403060050b40500000d04072240d000791119191480980f1000d11b03580d6917814048140b1400000e842c1c038120400081840703c1142c0502d0308204000c2d9010101e240000407001e0040301140c0c4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 41215805 1250 41214555 41214557
    0x11503060b010e1207090e070909031d0105030705040e061201050c0417030712050d0609110703020606041a060d0f050f0405070f060e0105030403020307020a0b1c020708090103020903150f0601030507020d 89
    0xf05c2581000c0203d00100042c6003134102c1403160700d50001d003146d0390f40724606046009a42e01040c280104c0213242c10301c1040000c80741004020410130800303030352003029101030b11035580120b40981c0754540045d0380c81a000078003556a528000a00150fa02d00400400442d00103e05040081c40c0400155071640102240903001c2103140c3c1c03074004014450ba00400043c000300d0000604c4d82e8541e039640302150f1110208001c445400580036060503010400700782d00c2075040354103201005890b0440048150709005990160501042025109415400255641140f0f20040001d40340080c1c020080350001e980c1903a5900610002007041c1c1000c90140050b1110307500e440d20f0b00e0a01c08011209944020410b60441c0401d01c0248016502c1d02e035900d005105ca0307200c440d11403030085210314807000c204008003045403040007a040090181000d030b841100c0e090a0040e2034898040100e4248001040b00c04c0c0c0490b4600d08001c0240c040a10050040c20281e908000692381e03202e0030b980c0c1d0640501d60320 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 41217055 1250 41215805 41215813
    0x9020d0b0d1205030709120c0e2202090705070b0c0406030b09250917010e0c010201020a0212031302030a0f1a0402030a02091f141f090b030603011503060b010e12 71
    0x209110703010f50000c54101da145e2074400500303981c5a030045512046104119420200300004221091007003442130340254483c0422080d1004544050079220540800280645981400184a980280140c03540f003904006050f24514014440c401ca03980980964804285044c003003010741c1c1031501400340700d400348a0f170104048815000700101e54510009850400c1000b940110700c000c41d04240b100c250850000100d0071062072003100c0e0900350690b452074116031050018080495000808003001c4492120f1a079680e00c03031105005003201c12072400794062060400c00c50802103688642001c0314001d08201070545108038940c0034a480c00c1d10301946c103500080700e0002510f0f046c4001a0800d07103c02110841110b4504d92090b20002d560001044014510100d1683d003040014440c0c01c0b4a12140c1c0445c01c2100003010304220094000c03090200c00c007200241240e18250710031202800c01002c0981016560302d0501c01a00c82c44070041e000030090035509900d420212940b00e01c002030880a0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 41218305 1250 41217055 41217083
    0x2090a02070602071401020a0314060a03031409030316110a0b030a0c0e1c0c0506070b010e09070e01121b0503030d02130e070f02060c03090706050d0e0709020d0b0d 72
    0x20040d4100c1042500e030240d080000c100000e000c202448140d07141480056100d4985500260407240c40683c07031058191040200300442d60f80b094400e051b00c0c0d06050101180d20319000d1b54403e405040d40858143c880052610412300a84091a50031481941e05085644850013848050041032265410511040c004030311850403d80048090078035900d40720601d8209880090540041900500c01c0c90090031451004e0040940340301e4080c0805136162845d041c0d10380c3d91829652814860107441c0360b1480c000c121400710a100d10b400802e00201c031034140e96142c01c0d10102030180e0f0f000494032180124030b64000d02d0054a1400c0480380d008001e941130000700b8500c0700195010b48101300483c2e41c07800300401c036040c5072010140034107856611212503695220f070181c03500300068154a13243d4820300400601e2000002c1c11816140307185400c42d00c800304000010301500601c481540d040c022402c02080c0290a40d0241031203480551042c0300300f28694091000a003c0400044c10b668005a11 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 41219555 1250 41218305 41218321
    0x6030209010903060c0c1a06010e1c030309080d020403030504050a05010f02060f070c0602130503010c0c050a0809010c051902130b0f0402030c070210020a030207050f06090411040801020c0f070806040209 89
    0x101c00c05c011400d0920a0a10085a44429038070984801541501d4540001d01000f540e002410b020240c00548200f05000d6541d44030180e0240c8115000b4101074607924610100182c1c801550324800007200159150742c1c0300c3c034000c0c0c0380c7c0d0807900031180507441100d800502580f103940c1083c5001c00e140c0140c0f60307a403101d80038041884001442e03601881810621880000c14510040041c100a0515000e500b400e040c101030030340d0130b4209040300b0880d2a03008040840c00100b86010032540c410300d900d903100e040390f0050303034104a4904081c00030f0203044040c200e41d03c105420031003035501c00c6070900c402886510703d881c00c5645c060880d6030041c2c2945180c11450409500864108140d10000390800416500080c2210124661400180c002030f840ca810145c042103441e01820301242c041140101e0300003c01d40c40c5c0950250544200c5d2946000d17001c00c06003800301c0300074081d800300a5559000d14040180d80d0364003008400b64070700c12034400240d10729002c0360300d602481d401020003103203803a0400d0f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 41220805 1250 41219555 41219561
    0xc01050702060315040b0607030503041106070503190e060c010504050c030601061205131202030a0806090103030e0906120f030c070b0c030f0c07080a0303050a0507020c030c0d0c0b04030f0506010603020901090306 93
    0x1801c2c5e400542c0c0300c00d00310065940c00d015000e031501c0307650307141ea80c1c0c6030510b080c2c0605002c184425014000038480040043c03008070a0700e81d04043d006c1454a03034005818100d0790007000c19001c9400141c0043c44014604040d000316104a0041003150100700105050680e10b41d002d1080c0000240c801c039148414090a070005500a240c00c510700384101d0a60b100c400b8250101c14894003d07900c006050700c07501d9000000c180d4005012180110950315686010340882c1003e00854815901500060382c182e64192112040c45a41c40c22902a02d040c2080c00d980c0350301048044e034561003002000038100d15000100c620035024039001d541001c2d14010400103d8201d8890036865015566000c582d02c2070401c41c0c0030303c1034000c0e07902103100d0402d207038035000b01c0d24050448011034110b4107014800e900c00143c4620100e07070640e5529404022403c0c041440c0b1880e03009170180c00000075000007031014000c3e01e400b00b14081c0c020358005c0d0341e03650025002c0384540001a804604902c8003000850102e0b4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 41222055 1250 41220805 41220841
    0x60402090115050c0607050a090605040305030904050a090b09010b150304050c011107031505070306060206070c1704030206030a0213050d050705010c080c160810060f03080903190c080c010507020603 87
    0x70500c2c5091a8001344940d0600398200c1e07544000510221301500c00325440300d80e110046c44a42422881c25045441e0580c90b031091942c102d02441e00c400c0402e4035045198000310086400a0101801d414403c10741030280200405542c85006410200301c280f403060340c1120700403039002c1c00138031258499400542d44c010503805604500d01401034000042105940881c00c1c491115000150501d084ca0313001d4122041504503000310340c0300200304504240c201155622a68001c071481c03201c1080045081400d10880d04025003041001c01880383c941c40c0f6130040d0840c1e1801c0c280c0c0341d038001c0d15030042c804a10f81c0040701900075841807200300119402096200300e4180540304007890854040045e601e003060506140e03d200d4170100d4100441001400901161000c0e41d1f010b1000070b00d014500442c08401e4040503041c1078000a401c001584c4c20806514080004103140e58108400d041c54800b5985c10b02c00c0c2506802000c02d0b84100e90b101d10110781255500518041c199112108031000203030380c01c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 41223305 1250 41222055 41222057
    0x702040e1504030c021f0f03050a0e03070302060f0f0c03041209030f08030a0515010504140d171914030f0a0603020a2904141e06030a02040305010c02060402090115 72
    0x8908240103101c032038840c040c03080b4081e444400440365148188100300d801103a01d4811200101a40110780d9484075000d5042101c0d480d0101d19600c622507035030002c00390150139158500c0005030700c004160700400d40320701c01c403076040d010045070342c4448181c094801c1c11503082c20942c0042001800007200c00d0004003180c9050b01d8544d50745e41d1203954144404a000d982943c007400c000c800c020440040d070281c654007808070010521000d0182c8006881401540503420b0703150a140315507083c0340c4851358641180d5422007041358810700c502e28022016882120b56840c04d0b5030403100034a825001e18040304603000034440c40d43c44e41e034a2104810350f8800282001a815450700800000f580e1520705c04005492500054049124140709034040704541c50022909540180000c010101185100405050080e54544071054410b0260285000400840340e8000d00c08018024a61480ea0181003030ba803041000b007164444049050360345d2001150020360208042c0014000c205400f21400041c0e141 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 41224555 1250 41223305 41223313
    0x12120408040b0315030c031612032309030d03090f03030b040f05090606040b03060103170c030c01021c06050603040b19020405060d02090411040308070618050d02010e0105100b0702040e 81
    0x503416521000c3d4004d4481c0e05055109052800c000d10b400d10086208032000c40c02040704c0c144850080e05190240e101384000507d02c41900801e260044041c211444009000800300400813040310035244c0001800c540a440b95041c86c1000c980070b88103500d03445801036084100c4918a80d0704070003802d40454659005500d80c1201d0100754403a020f8140a0301100c00079159034030346881800704552140e48054803d03400a001080421481649482c00c0d2120002141d510382ca00004c0900d036104000000b00310f50310000ea004070102d20150400011085035038284185580d41003000038601095901410302000840420480d030503038540461100350404e40035050650301da00003001034100d0008400d109400103100e0440d031800748156082142d01c5280304e4145800c64803102d0140c080ca07030008058603a19090900c50394511810910880d901000b01d80e91807040500082c013911021084a0040d0b0a0070302040204903444900010754040140c1039041940302d8003084003500010041a051b401 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 41225805 1250 41224555 41224559
    0x21609090b1b040b070c050d05010501090e01020403150f0603170306010f0801050f0f010201061806050a06020703051b010309020901060215070203191b060203090a030e0f0a060c14010c020f010605031212040804 92
    0x2c1d6823031903010b80c4e0302500000034150715214207002600d1034900d03141c4041e40304000c1840001da2614403d0350f14440e000c40010f2036038400480030000c10580d00090b1510101003d4041c1c4190b1100066105603000e90f29881c40a000c50401e40703030340030f081c003906038408142c200000280c1010301a1500000c0144000708010b56192f480b00003640c84400ca00c82e255444040a0007035080c14580d4000174042d9100600e0a68695280c02d51240c030306200c004064401d403440000203038030a800c10000c4640050a11409507980e00c070196840c07031944a6943d903280038000140b00c1380c0c004419520030b03413a0149010131080418008a84807440c0304d2520741e60072004c110f20008200d052004d10b1013444600014100488d986c04d0107452200b80d0060184201c80d1206003103201e44a50303219904a891506003440d00d9251841c0181050080c0c00819080350b10b0000034403100c0c1c0d03000508007107210f041d4000b002031a4590302419224140b5101200c88a07108001e664034062b81e40c02d0f00d550080c0100442400d180d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 41227055 1250 41225805 41225809
    0x40e03180915010f1206092007020f06030c070606090203040210020d0e061b0703060b01020712020a1502010b0301090302010203011508060a0b030603030f1c0f02070b04030f021609090b1b040b070c05 87
    0x51160b4014143c8207644a041d194200001c140294030a82c414108e43d040c10040d40c00034892643e02c0c50702d940900400b1001c503000c00d403010203070b880540d44108144400717034803100341c50003c0d08111810707841558012070440029002060f4445801140d554658060704a0310500640d6408102c401103480904002111180e40c1070144401461080e03e000c81e500d804280020b240c10410707003001c92100044900100181d54039030211040322400b290030072010305205002d90041805030303074154140d42850307000c2c0201a0306500440c1a90000020032888800c240b038120341c0180121011900b01c1c03000d400500001d0301c04006558066801412a881d02403400d030700312059001014455104a5881040c0340311032054000c0c41242c1c4115901107082c100642c4803600c2c00d0703034040e01c0a4140f09030000c100d030f441803003807001c24500d0b513858459001c000d030384109143c0144000da00030744041200c030010444d01c1c1d2403080c84105070310b001c0740c0350ba04250816007441d07500d502491080340d0014418000189035 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 41228305 1250 41227055 41227061
    0x60a030609080403030305070801060206160306081b090a0c020c060903010b03070902040f05041a0103050714180301110c061501170406020306130c090306020d0209040e03180915010f12 81
    0x24441c200032a15a440c515001c1c007901c8008d01104d06006050b00103000b01d0342c2c00911103a00075545201604c10102485041e00140b0031600915041d0056075038686914035184014810280240e46028071556152035400450700854285e00060308104400f50441c13400c50040d0001180081c00041c100d08014002032a0020590103002200d80200303003040a00c10803407901004210940e42801080ba482e4099200c1002c084102410b250790350380071454151044a90b46045501182d090f6a82c0780c00420f000041c1c4580303150540720358207100314010641c2e900d2041d01c403a05100f00c020800f58481044201548404040c81c0741040180120304011a5490750014007840c05580010307901c0c01d050781804100050b4024004078a0f040090200c44c070390740824010100c0303401050058680c80c805025402030f100d40140c0e980c0c4641440e041542e50100400100385641c00c440d00c09034040403000c240310f540300080303440c41d40301d07503009044140a500840120310020b003680390034000c03007450104035012 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 41229555 1250 41228305 41228321
    0x6130e010e0702010f0605060702041a1c11040228021203040b04050d0e0102120a090803040e0f0a0501080307081b1e160b03070315120f171303030503060a0306 70
    0x1014101900303218a442d0280f0600601c1a1400c005100290809002c00c100344a1109d000340219951000d0b07500d031100b104542000c1c0e130002003234219030400154561540001d50013098170900458a051401407601c0d2003203d510f02911a50720203001240c6403c02c401100d4044203400303600421810f008604c480c40b0085100b5032241000300c01741d0405013821842c000344c036070a0200b40304002c81054040d03a0000382400340900b111800d56610588076074111403042d0b041d80418030318032000c42c001c6481e140e010507842c4184802c8080d00c070030380d03601c19100381a11401e10550840f908104552000300300400000c041402031040c01d04848040820074a1400c210451125080c800602c40003990f8a4107200b01080345074981c81a0f40030a080c1026000544400b41000d018181c5e02d90309000e023702d401006800601d01401008214011400c042100050b5171100b00c44507098060004000803a01040d41d03000b20b0b113140f518190710305654056502e40c2c4041c110650000d4103a8000001426a00540b05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 41230805 1250 41229555 41229569
    0x801090b0a0501060302070308061c02030f010e0c060316080604140a0506011209030207090e0a080a2703120c030e0d0c0e2d0a150b0a110106120206130e01 68
    0x9000d01d44640030004880042c0c01c1a420980104040c03c042540b01e9800350300414111000640307405040000c0d1511200100000d4244c0134819086000d0081035003e8500301240c407040e50000700c80d0708100a0030b07102c1102d002211180011800b800e481c480d0360010703400940548005003c006080c403a00c40d0180c12185955560303152010807100d035904c280410200d5241c9a02844900303040da03006516800c05004d048041d0780c0e81c0d085e1490a5404000040c0065000100e00f5554038100000810301030980d18448102d0440d61900c004106c040b43c2c100c2c007200c0d00710f048100a04000c240450f0100f60700d00007030b000c010304220040c03400e996146103d403aa600c070740c41415144d4a804200c0302c203848000e01c0351400000c0c500e40060020014210000340300001071441c80140d6270754031083c00405140c000300800590464010500d03c0c40c2c500200b8524400e61103410000504068150903030b121070140c0d404001210b02600d00509001001e0842070b2504180c08603030702d0f161410381c4521003007640101 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 41232055 1250 41230805 41230823
    0x312021b0309010f020102040506070212011d0f0c1804030e030f100902090c090607030f020a06180b0a0509030f0f09040507180e0615070303020c0105042613140604080109 75
    0x1015030704200c4e40500072500380000c2d8201840c120004050f4018014003a004098080803c4074080c1c083d0322000c050000d0300c10400000c2c8902c41c01980c0c40480f041c40c00707440d10480558110740e1a1908403007103440d8451018942603921a90b084a41c001b0150036680c0522686541c40300180d01404091580c00311450b000540000c1c5004018017a00003a000c2c0100d0181000a24050b499160460344519050f003041d02c40500001c00480c5820025a005841d580c5040ea5480c1c03c1c00300312080d04c1442c2d008010303401040c1c4400b0180c80841e00265a5903103941e00130000203d414600070054000e07101a6248582410f02e40000301e41642c0c4111104030004130b4030142e8480c03c444031260300c400307000404400d092320314049020072901450429812500c9401242d10020903110350129240c1c03903101c50080c0701900300f502d002c180f038511a0282c038a680250b040c88111140501d420b07078801000842e0317400d050078500020420003080c45d03000c0c550000005c101c0894406000d0080101880c4210464 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 41233305 1250 41232055 41232067
    0xb1c050d090b0304050705091003060609090605010b130302090601050904020c060a0e0d080c0d0608010e0f1209031b04150b07120806010507030e1311030f0a0b0d0312021b03 76
    0x301107191540050075108028014440894000035002054074025140e007a415160f8841d541244000f41d4802003150f4140500414650f202d0340003003410790311501040c0302c60b0340c850f1400001e5000d074003542c02e91549141c504001524001c4c1085801420604005181107401c00106060b0381c0510f00745070507070740007c050000342076052007000c0c0d1036134522018201050031a80000c4c40c00700090320100101c40003156a9134603031030310b600000003805000020484008151004c6450303962419500c0711034015400070070b0020b0b21440484803042001009000412100c210040d58601030403071079500f013951000e4040440d001c081c0c545c0050b143c8200c10540302d2145141c007902c80300c101482c4c4001c00c4a10000e0000d1a41c1240540e02e0451345418150740001e02e48003c16900c4804091005070b031030a100d0b41e0400c4044090040d8080c02c1101c6000e1641da441e665800240c1d48894002608015040d441c1d20119109a44110414034001c00c0580340034600d0b60700d100400c225900741100c1c7d030400594 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 41234555 1250 41233305 41233307
    0x3040b090303040317070e04020a020a020901050103230c070b1e0903040b030601260a0b0a0b090a0b0a03090b01260c0a051c02030102030106030204180e0d030b1c050d 73
    0x211603804019400150315615181e0b81c010300c1a80a55082010b01000c0c2000c242c600740280303180d45040700050000c5444400d4154000d654031601c070381c1a070003010700500102c0d06510078007401c420030140b03140002c007824000e2403582e002c620040000b508203806114144c0042c0c180d8039150700400414411041c09031400c03030000840c00d800341541d012540100010080310684500707a0381d0055003420254000b40e442000d01502c69023594600010b050301d6410401c040100d40c0c03182c0400c141c1500d207070407040d460b010031550601c20300c90101d0b844401c2100810146031741d080100040400c6140224511100c0d54401402034401e8002803404d180a9492690380559014442c04d50610b000041481780d00400100e2800516405024020000340741c900c00d17071500d405059404c069010b0000c650302d60b50b52200030002d402501640c16408048511410081c40b40c3c01840a540e22540281a042c0620344050b0018110352703082a4000c03039846e510402c07040c0804035004e411802500509802070717031603070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 41235805 1250 41234555 41234573
    0x11508010507110a050c010804030203070204050c1815030c0306210d030e0c10050a02070803030907030303180c050405060a05060307031b020714040509070b04090605030c0105040e1303050903120304 87
    0x410b03000c2c00c0c4c0c07200060740040b520004031110414001c2c07e0a0843d602c45060480c01e51180c6070021350010708000a0105410f0210b0040c94604026119280b04403002410045c40c1c540307042510701880c005001080102058100458121100401c25102c440c4101a0130300d445802ca4005030f000d4000c1442941e1841e01806565404009800600382c80d200c55070000740c128040401e00030800c47d010400c40001c500811510018290315800c03680c803440c00188032a40d8101c20300088000904041c0804403440c2d041011000d83c80e40054180b00180c00d050a004c0140001001c56a129642040000e502e07100c90000b0b50203022565004140c05d500c0c0741140d82084014010711046521242080002440e40c040386c04070f802e1304441c00309450300c0703c0c80c1341450641642c0003242c04610010700000e10756525880602111010350958800c50800c03801503c140c0214420b030690a0180d100007100c0c4a12424005502446030810b01e0814140501081ca0071036286c41003078a0700c00000501c401d01031904 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 41237055 1250 41235805 41235827
    0x50105010e030307030e03010e07090501080d0206010303080c07030c0b070804030305010509190513060e060a1b0504050402130e070507050c0a05060f070501141311010e0a05060903011508010507 85
    0x820810784810003600440d950b481484009400c203d120741d130100960303600f074000c0c8400786100e000711040c0070344440741440100802c1c416800e1a214103400c1c038040c0d500101c0c0a034100c03601b548038000c0b03e139107141360394550b90b21107001142081440d42414002a804500f00da02402c520b81c1c40103d10301e010302c0c01400710380040c0c1119100d032685108028581a400c198910bd0b038440400103d0f0725140d00d0100183c42500c080014501800e00d9054006c00383c000503604c0c8941e0a0400a010080941c4001c2442000515100d80000d408000074401801c0c0b82d0000c0c00382019101c1c0d40700c40180d6403580609042c0c01920b00d1000100001094024440108120143e180089918003002da1030640010213911550351011508000440c400c400d0020039030007642200d058540114441c5056012110a4a8243d07001c462901c2d1100c280e1040d948182c002c030b5414000a000581c24030704210821541c4d404c0040d100b0351664030381c9410310041920481c00b100138040394001060b24248558050003058443c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 41238305 1250 41237055 41237057
    0x3030406020406081f050f04140106020307021504060905010c021311040501110708030301092a030212130b0118020f0d0b0a2913030b0f01030c0f0609030803090307150b030105010501 80
    0x108078064400e5902d0104602140c0e807c8800d89030401d00000401e010301020400c0504591000c400002c65603001310082601a2080311100b01e0702e151a07015900702d001c2e134029180081c072007003410310055024047c00319a480c00240040003109910f03e0742c901b41c0e62414019002d498000c1030400480d6040014411404c80344805008080e082c100302a54a0005120302c0b601c41c1e03100c2088850070300a0000200e031340202c89203207101c0b00c0b1090324090065800307044e600e440c400762000043c0c0344250400301d030300c44640e00c1889500c01380d10700711100000c242881400019079508120078111090480c004045002c004a0041642400d55042004003105603002c0c0f4090041024024014010a520b14040c04006c13500b81e17481d082203010000c8010142d8100400c0300c14880c1c180990b04500425a80c102c1744501602c030092512900b212200d00c00c1e901c2140080340142034140001517898020719401400c8500300ca09100031a182c00300b0b0072140240001c0040e981c2c0e4040d0303100f1f013002c0c043c1e81d02420003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 41239555 1250 41238305 41238331
    0x2061908010f06080c0a1403010b040303080a020f0d090303021b070924091e06031a090c01020a1401090209010f0e0a020a05090d0620270f210303040602040608 70
    0x1a128002d8a185130040401001c10000507600e0305403802107440c0000d2440460b005600c130b60316004054420340c0540021f4010030503010006807064400c0c002c542044c65200c1005040c241841c2c0c001000d00700040040b01499003d02400351030200000c81512806095002002c0b503904c0d01c00190101c3d4882c0c5106205214104203440c0802581d0b04c1030002c07640c913144005a003401d0015120b440c00000010440c8003424440c0002c1800001c0c08007114943d020f4400c44443c2d01c403507648030340c6c410b43c84454502503004003075600041110b03103aa049054032030b80c00210300b01c200d59000510300c000980152901482010f0f05108500c41c0c03d0000c1d0b80103c00000452900c044540c0240031030040e4050f5900c00c500d550a0f6004211003a002040501d888000900c02c03911480c50fa186a50051050310000d02a410303158450301c00b09440035051a18050f284e010320f840740c4010f00c054028140400040b012002e003281001000400040d0b01c03490065130300586460512600808000303002d8100340c01000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 41240805 1250 41239555 41239559
    0x3061a090f071b050703050d05030405010c0807090b0708070602040806190b010c0b041a0c09100804020d0b04080705030a0c0201110309150c010f060f05030105060d05060411040902061908010f 84
    0x504080c0d042c3c900c540040e20a440c407803440c80c000b890582c4603000207049009915400c1c0c1010380000c041d50103280702e24000e01402c0c030200e000710380300c100440f504400244540800c000c846844001001802d0040d0b00302d17454442e03140c45030700a9074880d17881244241e101c042044080000f5510a050440c6000e005010340d004640000b02a10441c01c40074000d103800c00042007c0140d00c0881202030000c07600d44204510300510750341c500d9040008114007908004951420943c4140e0b0300d180f1580c0d004151040d0340e00399450300019608000c004450400c0100540c0012407402c10150000c141c081c5c1c0c821100d00c00a100040036401038818410b10355009000640c0c03950f4900400f000c9544010407496168503800d001c8501420052900038111442e0044c08a1851aa0036004054607010360090007035450b51028000c104900c010040c0c000c1d0056808a00025440b503d0300d1410b120040000c18041041c2d00001e40d140e2000c041c43c48280f04205904815581184030140140495404000070034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 41242055 1250 41240805 41240807
    0x209060907020a11040b09090705040c052503020c060d060503150103080304260408030304050d0f1d1908010c030b040e150603030f0a12050a020405010c1b03061a090f07 74
    0x801e801e0044c003032403002c050442640c80d103070b002101e484002802845039081c2002050f0710b400c903500641e400b0703a091998900c0894000d8048031039410400807401c0e244000312600401001030308400b1011402208103c80c25644d0320405410b40d600c0c1624002149444e00d4200741c038200f4040c1020407118400d50042011a681e0380c00d43e81d2241d001455224040c5000d880c90580300c4009040400070000030802081d441800009540700340d22a07402c45080d01003a4800303840403021002e1142c009560401c0b107480d040c8002081d00800f20b400b0784080e545840c440719100c080d9400d50840403050303564041c0f4544069250181010010082c1d07810048040704407040741d22026151007801a03404400d021502a450404c101c6040840384030243d1345655040740002c16060840004040103400d0002050b2001418406c54040350b6058603400240317400380c0d5a4800365101101c0c40c1282400440c40040425100e000301d070010210480d48402400200c801c01503a070078085e048180c15550746040107085 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 41243305 1250 41242055 41242063
    0xe0714030619020c0f03030a0c080901050f0106050a09080601170d090b041a0c0a08130f051f0c02030d050c0706050306090103111c0c051201020a08010504050c040918020906090702 79
    0x1038150702e601583e601041040c80d89065007200e1051130503c4000f0404c500200d042d484225000e045076204480c0c1d80301c0d008604e003604c00503a01c0d50002031010b001000440e0007003000304040c103102d08202e9190350341c0b0808641408801d07440403050b41c0b541610790044103018041d1005411003810106003940c10609151240d00460059103110008079028a0307103001071f40281d901181c800c800f00d444884452402e414207402c43c44607410051060040803c2104607a10036206a4501030803000c40034502400700d0380d090800d15003a1042c002c6003403500d40540c60501250100101644401e0b40d5080604102c0786040001da0060301044001e00602420303070380f58003603076044940040b00d00c40e00001c544002070000400380d100248000b10707068400108440464244100c40303088644425100340c0988543c01d0f0b04c22003072070100007a1500c00500c89440c1544c40784e81c00030b01e140101c90610352a4512102100c00b240707407000c0e00024000c0c1c588214913110b40380d103a2000c400d4400d0800340c2801c2034040e5403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 41244555 1250 41243305 41243341
    0x7050a090302120f0a081902060702060a05070908060403030e06060d0507170102040b040e060306010b0f16050709060305060919170306060d060909060f05010f060809100e07140306 79
    0x41001c8144084540280800c141100d20302c40c4405e4501c05641c0b840e002010b40d01c5040c41040b40800e100c52007005c14000310f03846124800740d401501050b990100389070010080100302d1000d00050950100310b419040003010310075071013a1000540101d08820452501d10001c00840c4611240c0c1c000d180054004580501120122801c440090515030782a601a008540100c100d0002c003103000103006402c20986030240d44244d0a8812a988410b040d0700c2c10700c50741604404a100c01c003e4101a48901d01ca404403460240c02940c01054682c810442a0340c201d500640d00c40e4080010f1140c0c0000c24450308041040504820485000c50755032008802400c4911440c50100800000c3d800c2c1c950000300d401050100b9810002c25481b05040c0000380a4240107a038924641b003044854480a031140ca030588251303182140c80d943c605141103c103c00000d1000542e07004100460310200341c10301404000d075a00001411804ac02c2014061b1980100c48800344264000001d224516010707a4003100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 41245805 1250 41244555 41244559
    0x10b01091206060e130c0e1003080309011b020309010e1c1401110409020d050a05010b0301170309130b03060702070b0912031c0b01030b040b030c0409020a030f0c0e07050a090302 78
    0x705200c600d05098000700311a40c03200b94660108000c01401003079000c60008645e00c2804004200e503114150442103440c112003c15003071030601380600c080f40c264405140c4c050300313040021440c4101d5400c2c81e207031090350f22504800760303001180c2c0d41942d6170468030a1648031002e44510404203c0000c0c5030340c0c43d02030b41d90042c08480c0b82030713400e280224003900000c13140ca0300c00e001700344c1d25956068440029401840320b000c0350392070070700811440d8160307021b0359040701d41c00c0c0c0859080d64241418076640a114a40c04001d0340300800240e8110345030f020141f40d85041000000030454050401d050424000078260011500151000d01c6242c8120080c7c40c909a029218403400689035480b4619612488545110b20b141c1c15040800341a52074008a200e03540c281c0e4140401e003019400d110aa590a120305032741038100c0e48803d602801c241c0d00c00020b590000703008580003a52503d401d6203044660720141c0c3d5042c40c00d1407d00508030030702010303500051646081498024401d90007803644400b03000080c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 41247055 1250 41245805 41245829
    0x507081909120503040306050108030c0d0509040603020415030308060d150b06090315100909022d060a0201050411010c050c09060604080d020f011d030d050402040908030f040209010503010b0109 85
    0x400c284521940340151040210420140031a4201155250000d101c00c50752036040000103e42c4003004826504508a0301d0001c00f030820350448161000c1c5c114442041d009540d4050010243c0c2c0c403402407003000811030100061507411070500808044004201600501100300c40c01d0010322260600c81c0411401280007600c0fa44100004a0500c07500a07850752501c64017044140040031030400301d0045e046010034420702e0390380c0d42d5500182c460704200654041000c91800010503d04a0582156443c5072101c05542d203c0000060058108601210050f90354604100c104044d00c01c1c20b0080140900317107444e84410303030340d07800360346003070f141c1c0024094202c2c400401e1701034440074240d07805402008240c2d41c402482c080000d503986403840300c05000d503080164000c80401e40c50b82c03018507a455500a1480c00402400c1e44001d800c0c081c0040340c109640d520b804001c901040c010318043c3c01d8440f01c000780c0c2d06060040140b480c1040e04818802e900d855190b8140d603802c19401821104654240 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 41248305 1250 41247055 41247097
    0x50108040602070c231e0631061106060109030b06040e010e101a0406030302060f040c050310020a030509010c0219030c0b01030f140c060403111306030b0a0c050708 72
    0x40e1008540c0c0e480f0b03031000c118082e000c00744200360401005c464542503d1410b0356500fa12808a084031000241503000340b0204061a00388880100b9803002240714003000c481d1040403400000080e0303032a403201001a00006c0c0b080c80c030510600c074443d007000c2d09203400d89030a403c54851812a071400341880d8844c03507a80d030894840c01020741058100285801c151040d0004070340c0c0080103010300d4030600500d1740400070000007600d4144581c00541b80c250303006001507a15800310305100c80c00a801551140101d140000d0199000c004040400504400160320b40d1525140602955030151962050341d0400c4480e003000356001887d50341c29030b880110b40c0e501580f10304043c0c80c0540c002d200900280304000000c0140159548000d411074030440c00444110000b000b107039102d84024081c3c40d0300c030a04100800c00b044542040454010009018402c0384800307180240440c1c10b140c1c1304861030550001009200002072244100860311818154030b003058590701c0e100e0714410440c0443c6580140b0303500d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 41249555 1250 41248305 41248313
    0x5030c041403160f0501030b010206130204050919151107050c011206050301060f03050607050415051b0f070302040b0303070c1206110408010510170d030504111504050301140105010804060207 84
    0x3d003040340b01c0744441d0311400c984400301034184020134021540070904000c0d41000079440003500510829022910a2840325540c1c20000a07050145c101440d80c0704050082c110816800d454a8a1921032405910b0015101ca02c00d8151030710880c0c0b10f0345c0c2c818180100d80104401080c0c3c40c100d0035003441c0088201c5182104c1d80c0040c4002d0b00401d4240d0b180000118440c1e200f024404156801082290559078a0240484040c80b550041606813800030044001850049018000320410702c81815502503001d52442c0c0f600201007c440c8095000120800542c1014418841c1210040e4082c1d131034400b03181c4031009034940f14811004401400001e01c418013010782d010303044408102d02c101e6500c90b560150540642029908660002240e071030000d10003080110000d0720004620140c2030401d2418420780c020000280140c4072030231500c02260301c40d44c840448401d41055081c1c1291101c0c2020b0501d07007100c000c281e1050b100c0c2407607001172080323030b070480046035004c1c0d03200c10056540d400c2860 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 41250805 1250 41249555 41249563
    0x9060f0709090908040812130902161a160518010c02040204120f150204140402090307030c06050c070806060108180a0204180b09070509070f0c0503040b0c06010605030c041403 77
    0x80880380b028900750b0302804002200000f0800c0303400c50421515242d0721040c0c825600c0c4a100300150700f004044200300842001da8000d050000024040381012409503210502402c444910281c0b0240200c810000d03500c0340c8801085821980d850814102801c0000c540c0c9191402d4804906100e41c07912607034115034031138040320080e100c1e81c8824a400000c52402003985c001c0100c0c01c403448010024880b281c4a00c510999080303070301e82c001241a295000d02403000079030042c842103030117005000000c800320390114403040007401180d80d0142d5842100110314180542d94000710180c1d005030007480600d82c0c0c0304140d1500300044440c078100c041003a289082c50310a80d000000c0d001400d14500030000e5501d400c8543c0c1150060031056269616003061541f1105640507843c0d01124074004a5005031140d109492080914100003910301240d0701c031103146403c584e012901c15800000d080c3d070114014410039004080c0340c01c01c1815401c1002c035195141c000da0089882d024070003e40e070802513400300 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 41252055 1250 41250805 41250809
    0x90b0307080114090609010c1b1b170f0f06040305030c0d05010b090f010309020a030308060f0a0305030c010b090906071d12010c09120f020f040e0f0a021809060f0709 73
    0x407000700007924900755200752aa070211200c07510b41c01580000303010464107000314018142e02d55207108028100100e0343d010080d921106944052074007407140c3c0101c400d2240b03030002d400a00c4140010b0418030050b9440e02d4244d10100201da000120120862400010450b410030b07414241680c60390348000b03602703443d0b01800140503040c504140000920000c1c0b02c000345400b0070140c450070302e8400424019402e503580004002c0d00521001000c0000ca4813941c3c81c2904480001c0c0000007040e8140c1c0040d42d040896007043d542a0000a0b00e1444030009100c1d6030704050b426500981c46140100d0f8454640500401e02c07018050702e5118991000190401c6003071740003000b060a4680b40c50b00540e1402048411910700114107600e0001c0380d40c0450300c65800729a94010350050107a5a01d50a010001c01c0780a010780c0c106841e0092410100010b204240642c1c00040040c403100200b80108804209402524018441c105082c402c981d00d02141442d404030003c0311903001c585816000302c072854142c0d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 41253305 1250 41252055 41252069
    0xd05040f020d140c2d04020415030f050f060102070308031f0e04060c0207140f0402160b0a14010302010c0f02210109110303090d02090a06090906060302040f0c0801090b0307 76
    0x403640340c10401a26155040001c0700c0901140c4081020300103100c400c520908031403643e805c88642c030241207008417400321031565001d00702504141c0c1d0307035641340b8240e1008445a80825295030110701da40d1340511515a01080006150243d402c1100001c0e40714841400042c0c009a000000101ca141c2c400c00300c041c001c0003105800c2012a6500e121a58482c01902c08131039103820814071081007840000d6440c00d4800079811100031040741300811010804450469410940901200100d98004a0071000c40c03401501c04035103c1c984850400b08403034a45031040551410600180050b0741d010140c81c01d100c0c0d200105611030703041e034000201c00c0e6170baa0302c81488009245a012540880642111401a200d03a8480424040040405403280500d40015401526a052442c05480c00d82359507a0000101000080c890307840787c100030207442006809492980e112401082181000d225005500200010410140160b900700502d00c0406105000905450713440e030595641d0b0500c43c0d04018a50 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 41254555 1250 41253305 41253319
    0x1009080d030207110409032a08030907080706050a08060909010f0504120e040603050c01081b030103080711010e0f060f1b0a0507050102030c070603150312030603050d03110d05040f02 80
    0x2440c4000703029620000d0201c840c0b500c407441903c0346040a002e26071510780e1507150f6002040a00700300c01441056001414440c1030440b06078070200f140c02c1e000314010050f038005003d00504180d800d601d440390780d610510800008002140f079032a408461541c000b501201c1038015a110510b40c2409428150100c0740300900c1e0209200800100f0b001442c01e40503d6241d030b2060781d011008200403101d192001414941101c02010f03401d40c422050f2541c0714426420a2aa00c00f198168201c1600300341c1003103d010500007211818007038582c0c0055141c03042441d003403c0c211491408200c0254031442032038010340009c9140e12020101d00180c9000005001c0502d11484040c10071b245e46820940060340c080c045c00e9404140c0354800b0084421082d20400185075451916008038002c060380001718001c0700300e102010000809039411320401a210380d0740400c0c210304600b0310b641000d020740000e00c2410b18007d50210b04041c0300081d0351801c9009800010290b480e401c042c00c080154940c02544024 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 41255805 1250 41254555 41254573
    0x6060a0e1501090801020c16170a02090402060c0d2f0d0c020f0d061a03070302010f3005040c05011b020409060902040203100305190c0312090e0a060504051b0405100908 74
    0x640091501031901c111a618002d055990001e801481c8070140c44035070541061122b1405420841c80050b0454400781c441d5280441c01c008a605111110351060001194032490b450091010702669400368028503106040340e002034120396540f00094008414070074102582030641d41c072004c443d40c13205009003403050b86040300e1500f20003c01c0c500780f01c02c4840c1c060035115005800c0c006001c6003500e0303040c1c46540c2d65516050080d00c05861522000d04546072f031481010b000c01c4520500720081c01282e0000c100744c281403600c8240614690016070422101000140302e62403000d030035450036a01501c0c0081c03003407040d0901d04003401c1e11040c0650000e0000081c0000c002d0704200c0c0344220380c011000d40b4610000c0035002140542d61980c00f804802c06040d082c40491503402c1c1d962000301c0305041804009a0381c0d120400d054004880a0001e40e540e088200400c1c04c0c90b0081b5503000941c114124003580341640c18603002e02480c06158025a003040280301040e00544414000d8603503103045412100d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 41257055 1250 41255805 41255827
    0xc080a03090c0b0705031e0c0a060b12120d0903051204050a0b0705130302101e030e01110301080715090902070f020a0b1602010e0d0804080f06060a0e150109080102 72
    0x2180e100021a0001d100c02c80008507034100b0000d480c03100b0b41c004081c0d80b80c100000107101d411100a501140500001c01100c00300710000c01005c0e80c040d00c41e18010030f2085003a010804200100d054108803500040200c009002994080b900c1c00c0d140390700700141c03032180b6040c21144c501500b18221704844d050814481801f1000034080c401da0b216248404140e900c03400c00b190305000c0c0e81c2d40c0400b083e410b80c03c240f00626241d285080c03691054a09064203480d403d5903c005441c500b031311380000c259190200b21101c00280610080d030000008014070f5945484841540c030030040c415018207105280803803088510900540e40240300c144402d5456000030b04102502c5050348000328072031500080300081030b002503030688e010218000e200c600040035a80054070303892038541c1116400610900300d04009400d010142c8003401c0c0352002004903e2030191a5454404040d08162150083e401e0800c25000203001607079108450000c803801c03118500740140c0c0c00100320703041008076500218041540c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 41258305 1250 41257055 41257061
    0x723100e03040e0702033604090f0203010b0d0803060d02010c210318030f03090501020f04030507080c0d020d110a03080301150e0a06020c1c02060309060a0b0604120b06010c080a03 79
    0x50f0f262055511a19211001c4c142c0e56440303004900d07100c0ca20280035000d10303200204141914003606080c42c1c8152011400050121600780c40e040b500841020001004d5003024400c0c9401c981d8140c8029429014584440205002c0180898031600c42440c00313204592103050103189640d801680e0b641c5c01d001d81c40c52605c2110040c071128002901c1c0c9a581103903240c0400860b00925010386654115401c0b50000710042c05d00320406685035034003000f0144c9082c0784680108021070145001d0441a410501050709060040c1c08140c0b044042e41126005aa110560380c42420b034008107080c40d04106030049010b80150307030307c0500b6150001c0000124040301c071280e41c06071502a911107158008450810400306854000d01c00180d01448103032855041a41c0700700c582d19200e00040b401c911b1180c0c0087e1141c2d10442da035241513009682804409601c034040e0a4001030300700c81d8a0b0406007000307449030340c01c603480001a01d06550500421026401001e81c03139031641d000a14541d64140e584405409 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 41259555 1250 41258305 41258309
    0x40b1c030806030c010c06020309120a09081005010b041502070816050918030d0f0609020406090510030e10020307110f010507020706020f070e040212071211060723100e0304 76
    0xc1801c0c01c0c0001e005207400f00c0d181c4480d180503110309003105200e484590094000907e100e1161103510752045109900002500e000b81c10340d038030141c910703040203021410034240700301941c0c0701414000140464104002500c0588402d0f1a5003000d240162900300d240a045d1f03440f480942c00344074400d240c00700840400c0800e4490a541d080580d45070280b0303c40c05801c000d0007000311500103016003140b61a80342c01c50101210030820105019840360030440880c0c2c010b521950100b441040100180d0814685080d8001000c1c10100005040304c1101519084021048030034980c0c00400900081d000b00d681ca0790044103513080303502180d46001d195000f03150030344100026100b815800074200d88001602030700f001060003d41f49881c03500e004100401e501801c1207038081d44251145007a507108100c1c0c02c00400c419644c0081c50201410b28000030000541d41d20f01440c01081040045240b264440682e00d01164070460344075a0160034906007070504074250a8942890795440d0010b50000240c42 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 41260805 1250 41259555 41259557
    0x140f031014010507020904120e090a02040305070e010b090103020a0504090504050c011116120201090302061c060603020c0309090711070e010302040c02060108150402210609010c05090a090b040b1c03 87
    0x141d90035140015075103070040e804000d5002c0c250000082c0003030400c00641505c0025402c10f010104003050000da002c0d2407c4424866450340480d0030400c1c820100060300040045002003005541046110146c62098016480c107058000503100384c050b1140081b10010281c00c0010070070b500702450170380d07220035140c04054005079000b006109042ca011440300c050100d650301c00c18170320385003410b504500310304003100340e0520085603c00000f680380e0380300801a620b42c101b04103210708920300d10403049490542006082501c144547c0c00040b031f0000480b003000c2000c6452007145e0381c0b9154126101c0d8078a620a070301a000d0070000180050031014403d043c0e078422581400460324080342240e80d03c400b4400c0a4582e40a96100840e500e05041e2194000e0300190160040090f04007a84640c2c10088400075078503030040041010b415400c0c401c54121482d5442c0c00d629204040700054010310007070080050700796a034103440e25641c0d115800501500c10140c1010100759820003001310b80d05d003000c0250 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 41262055 1250 41260805 41260829
    0x20c0c0a0815100506160204020702060c0303010914040b0408030a06150e031b06070b04030c0501060609140102070602030307110102090409050a0209011205030328060806061207080a03140f0310 85
    0x20700f0a1025154402600d038050b0621741806807000401c8114140600e00342d800c160708005d07601c0582c58850080240e0f4a01000456603945495481c600304c0700d60411109040d58401c080c08001a003240106030429000241907881e6203e12040000134162036000c0741d00900780008400c015a04012019070000b011001d452600410719200c811131100300c05401d9200400b04034810009412a0310a50004d01030301d07294920300d50b160340305070850705107802c1140030603121681000b0307a5000c0c80484411150a1006d00300084c0342c060065542c0c00060000b0741805075040f0200c040300b401758143c40c0c18020042c02803002d12803908003243c9074511240164041d04010f800400c40780b05941506009a50010055143d80d0340d480c00d0314204d81c034034440038054641d4000500460102030246402900340c950150585050400c200120b049140f0808034140d04000c108114106002c02ca003010903405080034010601c1c03107041400d0620424890403440c060220602902030841c1c0d28500550b66841009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 41263305 1250 41262055 41262061
    0x1200709060807050f060a1205040503090f06090901060e131b021207080307050f0d090b06010f260606121305010605010c1223040b07050c0111060a020c0c0a0815 71
    0x140c0d12076a0600555400105c0c10350210700ca0b0034038100812445200e0b02d00007a000c800e2004510640e41d0a40f0181e0b4541d101040d1034045280101000705003220895600c0d1818210b50702103014500305100b9081172000300d10401a003074072a01c5081211b550341c26820004a0f0070f000300c0c541001c4603100e24a00501c2031843c0c0300e0210031680104c5644640020b825810341ea80d03030204846507405020300c900394841c2440544100c000d940070b41030280d44a106010034601d4118001401050003002c0c00c420420512908000188000e2040d090414800c05524240d515100865068403d00c02e004c01c11082d140f04005000b204d10795000802d078880c00091140c940d44a004407421a40100c028100c4680d01890f000d9603400b903040000d14140f0910594030003091100003100581065003e0000e4010006540007001410f02c402e024030242401d101d11015502c407100f640c2c0b04030040c0710100c0140d000075401c0000500300b0040e60440c000400040b58980c0b18840c03e0b48a4012000d030030003081e044404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 41264555 1250 41263305 41263319
    0x30d1506080609010b0c0a1703070e06090a05040902180f0103050d05070809010f0c05070b07031101020408070e0703060305071d0f1501030207030e0904030305041a070507030302090120070906 84
    0x20050042c0710091400225900f010100700c5144d1000343e409140340702d541c3d8108002080c0e482c0800c09200303404200b64491410b07040c0034000c941440752141c4520340401034020f1a698090b8118103581c0306640000711003550f840450403180000114000660070340040041020788010640d0599201d0415a501c10544070029980c6000742d00e03008261403000e01c007204c0e40b9441088441165025864050003001d050745a05040c844542c0080d501c2d0000091002c1c145900801143d00c44600700000314a418035160460f038441c0d4242c01401503010000b8007143c03406200e60003a20103103030441e050b1454540d07152086041e41c00c00c0320000840160310340015000c042180e00091141c143d443c042d191161a00d001180254814203017102405110600d00d035854480d190b5061042d031003030303c00142c035051a0910034944810890422100f980319410850280c1e4090299407600d5414240980c0b80d8004000584081030128481c0d0440c0300c180c88108106000080c0a80480f450700c80b0800282ea16051 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 41265805 1250 41264555 41264567
    0x10203190b030a1e0c03082502030c040c140406030c08090607020604020f010c06060821040609030b060a09020706050619050105120a020f0403030e040b0a03030c0609060e030d1506 79
    0x541c1ca506801280c1c126000c01c6501200500d43d04074a91003104030035569517480020742c42d982080e03851050114840300100d078000c40d03d0000c074600c00605400e4a0b656070000b0743ea68540305401c0c0c0079503141d6000c010f8050058681000c83c079010002c0c1c588841e212840100207080d4501c1c0b90f0005550600454841c3d4404a103040c01001580c2c040c240d40d6071130390240700c000b00e80c0c50791840c10409854003d5000c901c0c0342c443d46004d001101e0181481c1110b0a00148d001500b9120744d83d010102040700b0045160011410300c1200d80c0700230284d07140d42c0d517000044d205403041ea04c002c5071140001400fa042187c26404144107002c22130f50070043d0100c0707400c211501401400750501160080200c0c440410100c001c142d4003920021000d89825a0440c0841c0550002e40c4204c02080710f9110454a03881c03d400354100703015042c0c840e00401031468070014050010580060150b130343e0381c0080030030701c942c0713030084030b03482d00a582240e0307075003440d010a00b004210181807040c00214a20010032000e200304 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 41267055 1250 41265805 41265821
    0xb0a06080411093d030302010e12030906130222020a0908160506030a0204080a0506040b010801020a090302061303020405010b040819021012060513020a030513050d0f051b01020319 79
    0x12203518900111302503000d5540103625401136440c5044040402c1c40c01185250001d1031081d0b00201d0800100c00d00c040c0303810307103021181401280610401a044000003006984106d10320301c00e2210ba161340c000b0600d1203160840312140742180c0c1c845000b10092540040c90050320580d00c068840d0b640c0c14510b82c50704030130000c007188510b44140c100010701c1d040c8043c6070041400480103181c0355803141040e01d4004801800c84564000c80708020900c20003100403070041c58039038000d610304140316800804103100d40c00020301c02c82002c10405070387c82c030703124124010359400303841001296141d01c0c030282a0f41091140d60760300d210750100c41e100e4410040c2c08904040c0d008d0a161752007820441c1c180c0d154012015012a0507540d0140040c0b159912413142440604620b070040e83d400c4101c60080c1030b204000c00030300044203109420000500002100034103034000b894102d01c24050300c101100c1a00c00c1c0c4c06040c414081c010520440c0301d030194000c41c091103100608200c4480b00660200c01d8034084 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 41268305 1250 41267055 41267071
    0x60803030a020d060b030a0605010f0807021222080f010e1203012105011a01030b011e0f02011103011701061508010b0f04030506070903030e0d0c1401030b0a0608041109 74
    0x61001c944210090380281c40d209103280740200c0d99a4865a4050303072904125000d1280c3da4643c002004556080040b80701302d6049440c20405c180340c00350002c1d641e55052500703c5901140040c82d8001c44454240c0f2028030030b4441c2c00d100c0365641e91411185d940c05020488042c3d540707010850508500c000500002c0c810380071400c582940e1811060012070400b1400303a410500f08640c5a00010b0400e10071000403841a01d032100440314a13030001022220340d145c4080c10320440303c0350954130300010080307004c4a41c800c2c604401c2e02060a80102c0c007400a01102e83c260301c2010002290416403151140e48a00740703080200210b95442c0540390000010a00c0d5038082910040140803206081d8020814690803411aa01d0a544c1c0d030b0307505150080485800d40003a403061028001c1682c0640c0c1d0707040c080012210780000d02450303250300584850a05c035080e00c0c44d4800e10550400e0f4025088455042001084800826035640020300b00300d0302220300703e43d01d0a0011a100c01c81c0703070400c070480c09108a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 41269555 1250 41268305 41268307
    0x50417180609030102040b1201030c090915050a0f060b0301030506070f050304110a1203050913061511010605030601080609011404171c020c0d03140601050a0c03051303030905010e0301060803 84
    0x2040c0500550368000e40b40c0e0794140d50200030101d600c49421004004054500704c1803121076246080c8045600103030380100000e03505000481020a1021850106482c210071000505444025800c002046090160200c140c02d0030030004d41c40443c5000b0b181203c1c0650260ba41a9030f0b80001203440e0114901c01202255083c00410080764141c0c02c8240500300262420504540392200100b1840d0482c038100e00140000650110305e0a0155440e00d200110a600b4030285060032200900030b22102074074420410f24200a417501c0307030250044802000c01400380d0f401940c590000c152244d000b282d1000300ca60824001010001301c003a0600d03c581d41000945072040034a02000416921510b41640030351641d030401c081d00310480c8001c2c01d91440d958014419031610300350241c1501c4c3e911030404507580c00075007048013907604a011281c0f00e04070303443c0100d003903d12842c0641d2175009842c85250403d1a142000c81095005607030780c2c2c16103400343c8401883c8040c0d23004140c02d0360014065480c070380e08 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 41270805 1250 41269555 41269597
    0x614040b010b0304050102070b0a0506040b01090b160203030904050f0405061303080105040903120608031b030f0904110c100207060b0d0507060e0303090d0804031101110606090a0b090a050417 84
    0x42d1407026580091160340090b02e4221207454902030381d98180e80d0314030310964820a020140c0b402e07102d010040036003828400303000ca14201050200303016680c0c0001e01d40303003940d002d20304654060003202c440c410014030802507414a005004042c841c00c4404803014810000458540c12110010840283e07055594a41503800c000a01000d03141c0314004505102c003203000b51825031414000c0342c0290088400450300d0300b0f000c0070b14240c01c5090320010600c1e500304011011a03911190b0031541e0915007606e0204143e210fa01141100c0e01c10048074000d50b0040c0000840c0003035950b0020540c00c0c0c0900c805221500c1e04e5010440810030b030001c000d1076540040400c0140da402002c00b08103c16004040c1c034100b113002d0303012615200c0114000c81c0c2820740010107004200915100603c080e00a207801a4a12131104c462503880304042c2141c0c5c4901401e8000922a40032070300200964140544266418100305d00d0312005030000781c40c115000d000da05081e2020030000d000740c80102c101c500d0f407004111 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 41272055 1250 41270805 41270819
    0x10060e040b0a0906090b15040507030228020708161d07020c010e010e030d080406050708010302011209170c01021803010e0705010c08040801050412080901110a0305071809090614040b01 81
    0x80e4507042150742c01c0d25200a50080b80e54606d150f4030039a564110480c44455220401c001c50700010712203018584107200e1010304540c8044248490b25940a800120403512038099180c10116444a0464031136042d0328001a0304107074142c0c007100c00c1000d440130b4107000d0400502c100d541c100c400200690100345c2c0202258424020140300c07540604010480344501400319003000200b05410012038000d0043c4410020144121a8000d0440c030344980d403035046600092945204c0b05143d0039841d1103101c0b000502c11a906008044030800d000507564465020845000c0d400401b84011451301c1803e80392480e080601442414440072405005050305007401560301d500c4840d402c0e20300000034030001c95223101c24460a801355002d0442c441e119413845400034a48040100400c0040c2d0503c401507040c05000002e03201c25034101e040c08203042c0c0c0c0c1e1030401c44500100b002000054008400002801c0c20f0075441249014000c0600b480030003c201110411014195401490202d81d000104050 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 41273305 1250 41272055 41272061
    0x20402070204060504020a03020a020705030106060f0f090906030c1805190c050f0a0c170f030103030e0607020d0b090714151c0e0606010e090f01090c0c021210060e040b0a 75
    0x26071009100107030076911140860102e070088045500420ba0005044420f2901000f24a0050400320001d00c01642400001406291190b000d44180401c0c00c865108181c0180b105002500150364100202ca40e40d043c0402070250504c41c0e42104003201e001a41c1c0b0701058010148904854011881d40303c10307402d4058010715608914504020003030001c95148401c10b40100103050883e0303111191b50040e401c000588540050461114600800801c100640c4901c1036904490701814000110502680803405500c50b00c140290f02c1001c460b0341030208064507810a0203680180c00302c0751002d44070003021034404c61030404154009000d45d020040291072000a1089005803012043e611000d803031118152280c0d07a0082c261904807008104444d41c0c081d81090200c1c40c11910703026a402e00480c0f41e4906c91040c000c66080d180c40d0244060303602e000c1c2a80b13440302c95024218424110004100d251502820b01d901c1c5001400c04e20006080610303000664042c81d04401e0400140d112403c00e5001 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 41274555 1250 41273305 41273317
    0x1b0f0c0507030f0b07050a0f0c0201090b070b090618030702040504020a0f030f1716200307300803071209080403030c050c09090c090405031e0c0114060904020402 71
    0x10064000aa100010800e001800003103104060412000c050351503d8008064001c0001c01000300a2004041c13455008002c0c1800454504080c48403000e6400101c400b0b101c00d0b000301d1550400013407070204014118440f07a11443c921015180709444070342c05401b1f444d081140c0c0d140c15030310a001d085c000d442c0613442a034000e44001e05204c03a0943d1111180c50081e090352042d100401030243c0070f4180500c2c542c1c0041e4000d038240e43c0b1454040d18500001c80c03105102c0c009001c180070382c071210540354010700e108419000014100d84001e542c840000c0b400c40392501c078002040c01300341528402c0c0f8031455401520320790300034401ea045544a1401702c800b001061141d0844c5502d82e0919000b041206000b400518040d035100b0850070040d00303000b8680038064100d00d014044030410814009400303d00c80007480002c460301200e646850804a1a60091808a00303c130007841e0381380c140c5c0072002c2000b4102060f00710000e01c01c8440250014901c00c80440e1302903042084140001c005140990003011 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 41275805 1250 41274555 41274557
    0x10c03150b0d060f0b0a02010606050301050109090203130203031305010e090402030d0813061103061e10141b010903020d020d08060411070b09010b130501030c090504052802090a1b0f 80
    0xf0b00e0507500c4010079000d908560200e02940740c0000c02c07060440d42801048007801990070002d03e50352609000800039001e500c9903008880c2c0c0030010039003042915440c159220b400900b01d9071515801d0014410749101c80c401d040c04070350105001840f6080800149115075001805880c1031005024280c400c1c40009007080d12207444800c201c00050083d2240640c076680e101710380394a910704441404201030040c4080489944400c015616543d00d0b550107801000545c41e0000058100c0c0b204415503004400a001907444160345040c1c94080c15800026001c1c042d90803644c841d1a044803e903160031010b24880c0024489800140140c00c05070450102000d202400c1c0345000800c0d00c54440007d019a0140e410f030f5103903141400b540c03400c0c400468420281250030801c552640d80e80c241c0c091958421582101e88a030000340a0000c203005104039007030b070040400d001f40d00c031766900c0c5800c0b082243c00720b10404845000c12001d503214810100c10031b1701c40c088001c401414139400d581e9244c40d8034504c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 41277055 1250 41275805 41275811
    0x708030402031501060201020304060b01020c0307052709150c07080d051902030f0709060207080c09060a051c061b0c0318150819050402090106080910051503010c03150b0d 75
    0x3030f001030b4058101d0b81c000c0445900068490401d0f203400820b4654445006045510000441041da030b404114001210f8003200c050b0000e1010300402122141011003104042a0300c6040010104011442c803100400101c805511943c50310b45e6040c42e40921240500004e000340089000001c290b400684c02c41840c44a0a10780c162012140050b44d104407003501d1183e41000500240640060700d410142031f403400a01142c07410100d04be82c0c0d44e41100c03482ca2150030b01e540820b0054494145040c00b40201505051504460101880b05c4c40c6400a0484459243c0600b060b580f15681503440081a180e54401c8014400317038030101d61044410b19059041203041200046464580011040131811503d4102c1249055070b05085085150f01c004055282031104100042c1d4a62580906481c81418090301c43d44981c90080e2a20304240944122503141c1420302c411010b074240b000d070718044201d000b40a0441c0c0c0300021820349201c00039007558589040001e0207480302070b03c00b900701d4410360390b800 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 41278305 1250 41277055 41277073
    0x5010e0c03010e0a140a0b030c03030c0d120209030307030f0212071109060f040221090a05070506070809031204031e0c140402131409010801050132040606050319060b070803040203 79
    0x20310210f000a0300c044285a0307403240c250005040600c035002717440301d040f4055420442078041c0a6115603541041e141006142c03203007186500745541c10b0b034480000c0074040342d8454a0500d005070085400c1100b100243c4141d41c0c40c0d8034100165400c60b000103501400e003100051428007802003805003c0c1c20181d20200c80e24103506140c44078400b8104904c41400c0c21265442c404a80000303580005d0046076054001c2d21411b004258001402400c9030780a0321400d82e11001c1e42048075050242e280308070352602440034926080b29080c4040c00c1560700540529522140300c1001070103094020a00402d286441c0c50100611803813007134100080d03d0050400752a00c541036040031510542c0d9046040d04c01e460201401441c05e003800b00c5405019400c5c02004554102201d101c8800403445522011a0300c4894203074070b101200d08140d43d080406401409101d845031409801c581040310140c0b150020117894900bd840e141c0500303811070700c00080c5189803082d140c4402e84a9070004005a07010b204004031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 41279555 1250 41278305 41278331
    0x102120904090b15040c0c0203151f060f11150a0c03140c040e07020d0e10030207050102130504112d070b0108060a0501060309111002010605100309020405010e0c03010e0a 75
    0x3244e106a080148026203041c0900c00c1008544040000c042008583c4048400513100011610705030142165a18407a41c1c9540c84803602103a074910500c04003100d82e000040e030540203410f0032440071302c6031620755030303010a0401c42d6695a6401982c08220310b081c4003040c17505080b5405005580010714002c20200c2d03d00c01c40d00c01c000d6007610003804488000504000359550503c5e9141c00004038400340c4814107034000000c0c40391501d5038066201b182000c8044007140d0007981226400360f4488001c3d500e504c95040b0031615074900c1c0c4104c1d80201d003008411290070b1810b00460346155012050880420151144411401e4061421203c55280ac00034840800d0354201c859000b84003400003480185000009002a100103a10040a060400d2444400103131b05e440c00e00c0700881c1c1034a00c15040c40507184224054040ca502c516000303180004e01010f0207600d500080b0301b90b1300a42c0c051015903071359502c401c4036a0ac21030741c0031850442400144100805044404d8000400c5400802c8030791400407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 41280805 1250 41279555 41279573
    0x6010507230a11091018020307200607020c100f08060d0605010305030d061401051b0109170909010e010602030301060f03020705070f140f060d090212030a0917010605010212090409 79
    0xc810360350b20f03400e07000c0740c9030500c3d02d000107a070700c074480074021400c09261054018580013103440740c406180e0048001070000d8440c04040002d8a81c0c07800361a0019846207403240c80300d00a403002c0340140a00b18020361320342080c81d00443c40b10200d60703403118540042d1f40115200c0801400701d0b5413000082c0c00c40c00201e0681d01640307010314012800340d55503a2424003060101c6059500c0070481ca256501c40c222103070380290540e031603461030400e03200b0780c215041c40302d900500414400070f1019182d00110180c441c4082d01401400c001515031600c40c0c0d07240c103203a01d1030000910408005074003c02c014084180b2a1060a02011446c1005401e060196a9250074070980d034001e0000040d00702c200304415480c54407c2480602c0903039212040340414404140ca40c0710303400601d428141c07910464402c54580c0c001c501c03080034414046c0d941720f4081190003060201148550400c00c5100725101e02c502c58107200d45021940160014501510f440003581e007180c0181e650385a01c15500d40c090004921005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 41282055 1250 41280805 41280823
    0xf0a08010207031107140d06050601030b03060405031b010b090c0a020f0f010506010909050f04060e0709050c030a0e0d1e030b190e01150804020d0f020607050105040204140601050723 80
    0x1848100030035142d20761451030141e15170f00c4807401b1400440341c20b18a480759600c811040c1d4201c900400c82e40c3d20800141c1c06000e120b4041c03900761003110100400e000c0c010002c0c20401d420901020030001010f40c40c0d90980321000c00311a401a1a08003007040a1645030040110300041d0055440d28161076160b20704180902c40c0c800542c1e5154020800250b80c401015000781a425404021034104000038040d40741d40103200402483c0d850f003150300e01600030440b04009042e03003d8148201d19042c81881002d4005854803a081810807036095a079690124101044d00655540c0e0480b000d445150f00100011400070b01040c96501c1185403032989528104c52100d501500000c550b003450708240e0000a00141c1c094074840510402d8021082c0e0b1190441e42c200d50102c5441d40c81c200e032414002d403103045e07040000303501000002d5240c04102064001a1050b0300890341000b188048207101c1e40100001c81e00680007882c20444078000032185007140300c6021250003000c01c0c0413190105581b40070019 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 41283305 1250 41282055 41282057
    0x20a06080118050108030919080307030509040b0f01120504020d0b0403230405060d020c1005010e0412050405090c0c0a170d050a11040303230d0204061704020a050f0a0801020703 78
    0x18005100250259040b5596152002020046589080100c0707071a805135940592140074100c288ca5600da00e0841104064030024054070358644041c500508103500000307850b401a410148680c08900d406000c4003650001a15050f58500702501688001c0200400480c0d00c841040468404500c004060342d22492190f00c03240a80c400c400e5081071601c02a03021020060003c100511658881c1c10540d00960320010300507841301c08040c443c40c2044c0540200c3d850072032a081c00042c4481403080598022401040384120b001c40030081100e10340320b1401843d4200180c00c020070040000d0703d0080804503064015a6000400c03982d509020034081e407440140e4810115410600e82c05910030141c101040000c00c200d0054081c00071480350091b4400a424000111980c0700d95000e00e907868014495002d91407076a881100601c840250860f010388000a40c04062504034124502e202c0360040744c00412032041140343c8030412072122500d5400316000110707050005840b207000d002511049100e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 41284555 1250 41283305 41283317
    0x708040b070515100b07060e0d0206060a080708070e181203090c011b0602030903040b0f040e0601020d080c030702072c090a030c170f0d0e06060411040e04030c020a06 73
    0x754103180b0710300450f103107019024070880703001d00c94000300b000d1207403003243d088421858a035103003030501c2c600501e010707090031701075003d8100d01540349580828107600c20345040300d08040c01e0ba05c40040c1940d403280780c00340031a03030f40c0019401e00c026001040d2013544021190001142c102c0e0041c441030420101c0c10f2400702e20320300841400380317551041c84590403e001c20728101510303d2440f2100d4059500801d0080d040c50781c0000818581d04d414400c45000d44011402036580381307c2d001c01d45900340d20510031a2102220000070488541c40400d0080f800442ea9413950611744996142107010b40c40549003000358842d80c000054015100501ca130031312110504c002d00018890755000500300d00040420307440341c1010125800084c5c109582a41483e040200d001c641101080121210b104800c204070318410045031074540d04000350040c0780c1c0b115690080d5101d40c3c842c1c0041c4003c2d00e545c8000000004000d11007808400c0504000945c424081c1c600400030501e81d40126a10816030f800c00000501 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 41285805 1250 41284555 41284567
    0x906070801060c0f050f10050108030705060a050901021b030a08010f05060901031a04060605070203060a0605090703050702012c070801050c120a0f090b010927060e1606021005060a0806010506030a020708040b 91
    0x1903202351401401044044c42c5060315580d200d50311800002c150506030b558601c049004040c0950584440cac101c038445211102c0c5802640c02d81c0c0e80c0040000c6000200340c05c00100d6040100e40500088520180c50142455221001034000d440c00000e040f401c040c12010003403559495000c1c44c001040e198403800c1e5995114018141407000003040050814140041017190752201d00e06980e010480d0328000900ea100d0900803400f6125202c2101902d00a9030024152803103d84490590300c80c1001c22030b403840b40d940c0042400c1e144112489004c00e0010b010041620044010b480e6000000c554005a10715503440034070122081da50042d01c1d40d1401030011b1007078240724071400410504210240450f603130b403141c400d80d48400c50140180065100c01003034007440410080c01c0c40000400010001242d00e03480c00a65a00c400340095140b41c0c1003002194440c18a4201d02d001c2d0b42c00d07917000c1c042503800c010a001c0668806001c40c0b03c241c3e800c100d14004543d01c1400380014096100340385603150 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 41287055 1250 41285805 41285833
    0x14010b1e0310050105070804050604030b06100c0206030105060a02070906090902010f02010603080d020d0906050405010c09050f0907030c050c0a080403020a0b1c0e01020708030109060e0906070801060c0f050f 91
    0x22a105840c5958030104140a8000503014072542203c10134607107241d681e0b60514100505015590140303801000100d030200811404690003841100c0a86410340381c2000d111084415141015000e504814200010f00041c1070100042040ea6101c2c0102c0307000d0317580d1310000011514940d01402d003040c0d41300102011981d0040300100c0b46001407000344070031811901c400381c10307101d054241403a01c1c0e40002d80300c814210a41140d109590090000c108a140c941811800f801d0f09aaa04001680035040810a440c10740050000b2440103450144542c0e6480303002d074000c1c01106007100900000380203c1002e240100107140c915803042107242d03180c51441c818003040740440d400040c83da460134842a0440302441d103200e11440d02ca014041050040209000d0091207400c2c070107405900c0000000c180c2d0070340c9401a5003201e0200084100da070f95550f101d00c0d101c440540d40c035030001e0110b03401004003e105140c1e078101580103103011203116210b5902c40b450050f2002c0b43e4005504a0030100e0703034070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 41288305 1250 41287055 41287087
    0x6031112130212031206010e0103090602070c050411040b0d05090a080c0d0207090905030706052206020c1504050a030e0f040501180b0f060403230105040507030b060d0b041514010b 79
    0x440f500d10011030400107290088440d801c0014485410440b07640b200b804070341e101c0e4001c0a40b03260000300855a865440c18200c00d00c000c1405030764011801c5c81c9070980ca030105042140c0440303c9040c4074034144203180390a02e0107001c001d04074044c02e01c1050408800b0031041c90060141d031420300020308104000c0140641050320079408400c3c000d1411002034040b51020044680c1260302c8803001849a4ac1e4072030040036000795174114001c441103010f002d800c000065004103803c030050380071500103030465039107044050ba0840300103040390000798440c1c2c00a03001300d07409089c40b07038000d242c01c404000c0500403034200c9009a20409a42e200d00011081c055181e108030518040103a449040602c40500401c180c0e100b10310000304880d0400e141444404028115130080d202044024411420075050050340d400050000340c41c410805804500706e4607100140706030300da42c007a42d03144440e941c40e1150800040e0203000103001584070320410030017105c007880e491b02804803181c02c1c03034072807001e00c0c90f4440b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 41289555 1250 41288305 41288329
    0x501060305060c070c1d13030201060905070c03031a01270902031501030b03161505131e0b041a0c0307020d050106080d02240603030705030a03050a18020a060311121302 74
    0x30541c03161000804904074042a1f800301c14588200c0c444a650b00d81240145066445558000e04d04401e011049910414003010780b4000d03502441010840d404c04144420440b0580d804684602c0c08101c400c80c44440c40702450500c00d84200810703076200d001c03e0681e80215846008400540402c150560300351180800110b0194020101e00104103000c280480a41c080c11545440344000000d03030754403900856000c038141042280c2d48039035600d20703105140c03031a20386602022160b100100314058107005540440e184800301183c0b400c00031038030010305d40c84198064000d020400c080400b41c0ca484820900c818407903000000e14a103403026a03401d2001d201000780c11034100d10448a450412a4460040c501c00c03c44250341648404c00042e1540c4210040107009000100c0d98800c0c0d139405a000c0c03446001c0c48202030020300d69607000340110946201c0c0c020352207100d054091000c14420781c40300c1d18912049031140e20708506a000c14142110881b5105414030005c5400401c6050031818800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 41290805 1250 41289555 41289569
    0x40303060510030c170a09020a03060504050d051c05040c030b0f070206070e0a1401110f030a021204050306150a0807090209040c020102070201080115181203030605030f030d05040501060305060c070c 87
    0x80000261301c0010400343c80c0380d642e00718804041e000319000360010740c031402406a004000c8038910750703203142c140b000d8502250240d9050040c4007200c1e001500801c1103505540004100c04018074201030380d50000c00c805041030b24a9005540b01000081003008464050342d0400300005140c544a40d000f441c02e00014041801c0100465110702c1a80314490304038144e440c9000540012402030700100c0d902e0b104100340c1401c5204442c102d08000c80f0100003080703040e8480e07003038a00c88100400d84201c10f100d284981609580000700180c0048155404130b4000c50300184109040b0740c0c0c1d072443c20315107007040e08800c11941d400a03e40342140b80030701c22400b600440340001c0d0300340041900040d0401c00144140c01c680b0441414841d1541d209020050107000c543c1c6002102589070010f19010104409088012a1a00e0004505441c000403101d4582c4012001035290050f41324200c4042c200c040c00450b50b540d01c400c000310014505000e00d074890314a19a100391240424240301b85240c0d11070340215 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 41292055 1250 41290805 41290811
    0x507051207030c0903060905030d0221100501120b01200c0127031707050a121205010e0a02090105040e0a051b0307020d0c050c040c08160512060f0a09020304030306051003 75
    0x5050f66401ca070b4000d003169004500012101010f041c490308500c2000307004044c4a05c0058603c0640600c12040c15090b0318000105800d40d40b0784440c07540c3d04c4d1050064030702240d4090103082d43c0c1b0070146c2040c03074064410f00d001c2280c088103480d110300c60b406000d0510200e8100c0101c000882d64400f00d00104811031080c1251058a0b030360100000c0c1c2d1950001406c256080441c1505604051089404255024045425514071401c140c440301800042010005009080e025484280760003083e0681d000b00032040b580e03031201200000258450000a0305000b01400700280081c035145583e0300c42d0740d4044011030a49428030400f440410100000309d1074100138018840340f40c0d80000c03c292400c146003400e010720b402a0070300c2460b1040d518401da42c45400c00b05140b00035a07003e99014010b00c82a480b01b022000400825500c5010f030340c07508601a2000030001d001441c20030801340b401d9038094952400c03aa200c02600050380d20459003640400d4549400308517a050620010008203000d150030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 41293305 1250 41292055 41292071
    0x206090d0804080a050906040308040308070b070203030907050118080105311110030608031b010506040204030203060c03040218070201090c0b0406020303041104020c07120204060618120510050705120703 89
    0x103c0194054081c4080404c4408a040c82503903d90200301c8004c2c42d04071941c103440765628545000d4582c00084104e138014208d50114401c40d00001c196070040e40348030040e01d0504e080c1001111264144845001d40040907800014403030700c2840351a01400344045040d0365103010030112a420080f0342c0140400f9250b000034a408246000007040120504940540d042c0040500840103070800760000b0100b40070000d5202038801c3c94074590403980a41d40300a0003079035240303400c00080703016a00c00a5095041000051103607000c40c00150b07409480203003491209040d05d44004c101c0201200d1120260f903541c1411010301180070f05600003400050003591a0604109000b5283e01000d00014603184200c10b00c03660300e5032282c050300c810442c42002c842c00c82e607444045080c8080c0c0030400f0b07401986810000b1554a100e01c00407418144154000200799107414070820000684880c1a20700b4003076402c4020f036405c0c03035005050082001d5614991555407003503411092550103080d44080c58504042 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 41294555 1250 41293305 41293313
    0x90f0b0a060e03061902040312030c09050a1208070219060801080c04110a0513090e01020a03110406090303110c040504030e040507020105070e0d060b030a0311240f13020306070206090d0804 83
    0x49070f034005200310302c5d880170300305485450780a030199801c010300c241c1c0040fa240183c541d25900001824031541e4a00c80040d0362181807113441d24907800b03200a0081d00c61100780104020600906045102529107505544604c200c290001c0c941c0d000b203000510450010440341d242000341c400071150441c0c00b0440c000301c039038908a1074810b0190030380070700c18003107100104002d8807151b4200604a0440030302400f45101a594000e621a940c0980401e00d800c1001003261500c4d030076a0700341c80c1d00d500c1c2ca00b070660850320140c5040741918890b1045214a29a81c060b50303d47d0300134980901e1081e11a003000d003404608204c00d880c03004007004d08584c50700040140c0c0542c0070002000303081007034580e040212111304116001e0040942c0042c0c051060030a40400c06a0000044000c1006002075800149260001ea150740e080086105416886030010444a008412200c0e4110081c600341d604d48070244d60220f810905c00b228510090b0b0040c0f020001d5120090004108001c21803030110302919195a03 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 41295805 1250 41294555 41294563
    0x6020d0507060c02031e0307020d0302130902091306060f0e101706150c030301030302151302010302090a120b0601080604090b0c030411030709020901140f22090f0b0a060e03 76
    0x3000b404150b00c862040c506030b802401194819400e500d44940c445606010346540c3ea40141d41c1000140308099100001c64802d1013941d07131441d00b0394100ea1031149455000006074000400c401d07071040000020755928a040d208420003010f2584600b0940701442c40090403e451110600d40a45170499800400e954494907403d200f1040b00114a11915030401090400c2034010850502c1e1000243c1000c0c5208000083d50480380b19500b00c0c0d002c0d0306800c9030045a00001d6403101030a07040d101c0204010b602a801405a00c00d01416201800d5035031080043c00111042c41076545e001580d06200c040d50b84025625844a016682449403a046688802c030702c44005000c0d10000d00044003080410415508040281d00e000741103c1074039455011880007544010001ca0100d240c5521ba18400640c94042d47c19415140d1240b6007010800082481030154824441400020070303600030900b0744140c031413200c0e00000070314001040e07200c9500f40b059500d09900400c040c068192100d1023180d900103 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 41297055 1250 41295805 41295817
    0x605101e18020c19060b06130f0506041d0a020d0501030614150d02040f0902100801060915050405040b0103060801110c0f010e06130f020d0602070303050f010f150203160c0e0106020d05 81
    0x130907040c03904641c01c069001700260840035078003d400080c05401180109502c03002c1c2c0d003418140e40e5045a88908004281c81644a40700c0750040000e004c8650440c4c2c04141c0f075100300903110240c03904a40c01c8400048881c26001280c81036941c0c0082005582e1101e201607003d210100c108820b1074050001a2030641c5180e0024415034881e402303480c404826410500c101903000e48010700c40303400c1000c041d090302424003030b400c005075009400044580e0b041c20032489440b0b054680d0740c03800c4e05010911018002c452141d50500d91505000541c96200344a03003000c94904800b115150902e0201c811b08010703010912103580c0e810134215080859010401035045010000c51488000386442c1100304420740c03c202940c4640341208c0202881140e800a00e0a03c1c4655010003069403020b46801c80c0400a008164a80715188801e100118003202c81c450060800e004880c01c000d1150100110b615081504845c004907660f000c1100041d00da0125000d400c4074005070039115011480140907000318 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 41298305 1250 41297055 41297083
    0x30309091505040f1b0201021602090c0c101a04050405030301090e10050703051e07020a02041a0a03060605180c030408210703050907060207080a0605101e18020c 71
    0x1c044001c40010480c54a000801c0064000d1080c00858485035004182d0081c1c0700c0b095030f601c944018007140c418800c07a080300e4460004054414656003d102c0c10002c020120700107040108107116841100300b100002d030030310414012440d000c40080c55682049504d00703940c000e50810003400005240803055905481d0400c0f4009250102c08204030328041c0c4001450013014542400c0c42200b41c0c0c9600114400c810000d03880c20040101d030b404880b040012039022005030032220f0084014036164000441e0406a0301c1480224880100000d084e810741c0d038030855050383c2da08820030880c140312242c0c081084a1003080c4150345054020f800542c03000400007481000300040b1410780032100c5951289110011380d0a090501d08514040c008181c281c50480d12071060110015101d4030001c1d016080d240280081c1000c4416a070b101703005440041c04140d0201440c1c480411411002c0c2c102c81c04e540280003203010300d0340c50481c0c6440c110b9002502e40000718010003060302c0d0301000068056a9685c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 41299555 1250 41298305 41298311
    0x20313091a060409140610050a03090206041d0609090f070303030f06090203130507050906031f090f030504030c12080702090910060f0603051303170712141602010603030909 76
    0x1015601c91000203074111401d40c814008940440c070804a40d00c80c000c450100701c2c4066154581700200004034401030741440004a0401c10b10324a81d219030812040c0900c050f240d04d044c00d4072101d1413180ea501e0100705802d0500c0349010410549002c44500d03400140450152070f66406070380000f921030f483d500010b810f2686032388510407420b40070f034420401070400c814115101d040540300400c000b403551005441d00d10560a02040390301c1c0840c0c60f00e005a04c01002005c03404814034090390468020705520800075903d50f00c03900030842401014101c01d21031703901c055035036042d8a090038103504917801ca0b00411045124090018030210102c9403001d804851040704e640d5400600d40c03505503000848001c56013040303c001846800c0c400f614090b00c102c0e4030b06118550321401c0f880b4400328041c80140010740c0500c2240028201f241742182c01c640d091034070310725000ca08841c20301902c0c040c014400c2b901b28a10200701030203105000702c041c20045c41c4001d1148910f140c03402000e82c4c59600621881039a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 41300805 1250 41299555 41299571
    0x13060e120607050c16050117070504030c0603060311010f0807110a020604030f1e12111e030a091a2d0f03010303080106080403021e010905010e0303150105040e1302060f07051b0102031309 82
    0x400303072b410764000715400004807400603140d244c024098070b824403044614000100186030f0a6006500b03c23445c0c03804c5641c039510150740d0024115026940107480000f280115110076000da10b03807100500c091405240d800a42528a00d0100038660010700d0045040800300c216100080707070381c403824080e8441483c001154100d038003891800c01448180108690f0240c801c01c2c100781d0390102c040c0c0800c040340d80313410b000d00b581c6089400c00d40c00c5410100c0b0440c070003003220303a9542d110030410030517085010650103803802c000e1112504550104800500c4264084010010140d11121050240255141403249414a40e4000e552046005100c401c42c081e0b2892001583d00254050340d207080e00b0800174403507c3d901c03038415904d030307442524522401e540001c2030100a500130402c50342200e10f0007801d40720b241d40d0441e1111444803540700480e4800000c01160b0400c040381c1c400307070032502e029001810030b1801c00184000e80c2105804034505540040c0058403850740385000d10742c11101c0394400070500903 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 41302055 1250 41300805 41300807
    0x80a03020303040201033305090903040509010909061104090501050901061704030f021606090e06040b0307060309020303090a08030903010b0103050c1e120106090906060513060e120607050c1605011707 88
    0x1c016888503080d00329451040c47c3c020031080b80792004540069a27068015150300d02c100b500c0f4030850140381d400c1841c04004000303071041c6a20030000d20f0300034000020700d400c00d1903000138640d003d03a0001c051a91100c005200501d804600140107007114140008001c0e2400c4a02c405450020070190a0086081010b502d0324000e00c411100b03081c01c0d0302d003904040d45507030700540a95a030b405030060090000700041c5c1c8609051203041c0c1c40f110700a000b800c3c890710300402200a0800c07104100d800d03001c01d024020180e2109110328010300788401c007940d1100a2203040c1821603200615450416051000340603401e0b40f85030441d1544034203110707901e509038140d050740c002d10300c03034408600b400a805000010702c10f40c1c01084041035849030340003400415518a011603043c00744e820151121030011408000480c040d503c040e10717054001e400c24800310440305446e41400c0007260004049000050000c01d0190180f1035003e00c60903103080440c200b0b0030400002c02c192082c400c051904a404000b0500d40c0f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 41303305 1250 41302055 41302091
    0x4031220030f0a02070f050d0f0303020f04170606030105040314090123040f06020303011802360312070b0f04050312070e090108010924060306060e060109080a0302030304020103 78
    0x80c84500c0c040726a581003408101d542640100f02120060140380c0c00445c10582820a2200b261001004a070204196454200d29900e40941c00c906066007005080034480600d0084c000800183e9031780391a2014460070242020002010684603900d0807007003200003504120485121a440c2c0440c41cdc031110507a006880307030b0b4182c1d0401d0081c41c14a0303030041c4030314004000510548480c00e0700364440a0f560724059076070307000138001c0b00d445407a41c000c2b00c0b40040d0942e001e029a004000107030342000024a40941c02110803040c2c94114003a80c2106103201d0034104407261140d298000650710b411850f403104074522001030418280d5003600d9010505000080054510201d03a1200311245801c2010000c0d022400c942e0109001b5245030f4000a02084184503c0101d06c5e003020614040000d01c201101001002511031000d0030303910324000c80071560511071070001c1c00d021040c0f0202c40c20a0000900114000e41c4903140c40d520410a060001e80d0100580350030a134203080116958000511207110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 41304555 1250 41303305 41303357
    0x1a01111504080c0109020d0b0a060b0408060c0a031e0606201203090c060c070501080610050307030504030504120b011406070c031e15050a0b030d0207030b0901060305030f0c070605040312 82
    0x1f012816102800600600780c9a2500401c0071540c01c0000702e9a428140c4100e000380c1c4560f5440c0d0300008005802e1400450003059101ea16181c00100116181c030700c14047d1105494850040d80d8801c030601250750440441300d401c454506006480711907210201c1da81d4454110058000c82010022804003207081200f50100b1000030001500e41580510307542e610041c1d84692800185c0d0000070411509140e13410000b04100c9680300c62a65841e070005070043c060140c070803410051b0400c0005401419000741414692044842e4500d41d454902100c10007181101610f1103800300700000c1c1c0c000744c90202c001088075401814480480140030314103039555144d07203000e401c600982100d0451503040b9441984079007a44c1504002903400041816030783c10007900baa1025a2101c541400414000195581d01144020010604a03140e0741ca590941d003011f00240e0320b0304400701d010100d9100a100f07a402803c1e01d442d00c24241861510b4480020f00d95904400c24070070f0688108442d03580386015209 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 41305805 1250 41304555 41304559
    0xb061608130602160b031504090515131103060606033d030b0a060e060111030f0c0f060106021605060306040209100203030604060e0c070305090d061a01111504080c010902 75
    0x1031450756038001030b403114810760401d01500d0b40d641c0c02081c2240340070141c03400750014547c100c0906103080140801031030f540000766040e101703100540d003001c05d12200503813141030740b0610740501649610b0406000d07940c84140902c070750050020440c41d41c07500800c0c0d9520074142c0c000e85184516055180c0b0140000e041006480d641c8410304c0314500c2101045082220300c142a0140140d80d4260320308102d94260285060a209100124070306601c5841c661294041400a80e803410071041040d1800340d010090740c58543d0400301040e8111002030100d140108030b01e0000d000103d840d4500d155000e035485c01450b1041a0101c007080c071640700c540c10340301102406000307880113110350348020790b403500304a841900c02d030b00700344020500304800c011082c080c0a03500c0312a4280002c556003035440d40c1108003401c0d00840004000000302e0140c0c01104c0070041500040e000c4c0d500c0110004002845400c10140309a000302d0032a40190444000c55a1180d00104501d071601c0e140d444107405041494001b075 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 41307055 1250 41305805 41305837
    0x30d0c0212030720120c04020a0302090913120513060f090b030a05060f010f080a02090d0c03030503060415061d010203041716050d0309031106070b0112060509010b061608 75
    0x8100304000140b40030444410b00e13210564904040069040009480c1038281c0c01130f46141007141130039005090b00481c107003400340c00c145141001c145000c0303085609922044000b9035010600403850444a81c0c0c403228a010303440c1c000c026091010510183c1b0840301004032807030003030880f1889400b245024040c502c201030b9881c14040c07410005000c041c1c076018400c0c1c4090030319188560040c0100e4842e0501034580c03110580c0c450381c03070034001d400211b080c90300840000b14078000107030740c800200041c52180d100d840c0ca0341012000c0c80100c0320404440a03040160000c28402e098106100800002007410254505008540100d0950285901ca83c1c0044140c0e810f10301614804034070091403402442c83c1110090365002001341c1d40079050300140129035006c80c00e20115400c02c0085075180000344c003c52902d0b0381c075961452800e00036404002598a048003081c108115800755940003590300d402800481d824134006a8503101c1c80c000f1501c030780d03402e9074030f42d04121a0105031991000308032015 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 41308305 1250 41307055 41307067
    0x80f0d020a02010c03110a2a06020f03090106050103110f03130b01060e15040e060915030a0b0708060306090c011d0406140108100b0307030908120c040f050a0302030d0c021203 77
    0x19003e0149000c541005c01d0801c1c4400b20001c0c0c41c2c80588400030019650301d00194062143e2071003c00c582160400b040011a06000204050740018580c001c2c1010300b143e900d00d4820581d900b11815178216034101410f041c20b43c0d986d42a03c4c0d090711014114407180701d40d00d4455a007120900254004001c01190f0000000164140c02c07070f5159031007403005d4611120250b070b02c07040041d05108174003031005a40d40c3c4038040748041c18001d000550040144030101e00341208500000d29109034140e04403084401d00c2c007080075aa501c80703062a0000c10035002410103080c4402095214429481c3e01e40c10040401e4001c0040b8118000c140000200544200000c80e100c840502c4c07100c0c010420740340030601c1c2c0008201e00c450807080c600c0890b80200400c500b036880752401240179042c0400140c1c4c2c0510b06012260a0000a6000c10b00400034448903c0c0e80d2441d00c03683d021559170070b0340840d114094800701003006da10003140888068417a881c2010844045100040707900300e08012140b060322001c504 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 41309555 1250 41308305 41308307
    0xa0f0b0a0e060402060a080c07150501090b18060121060f140a030c03020910090e010e010b0109050a0504020d0204030503041202030c0d081902030d0e010212070e060403080f0d020a 79
    0x1456005034000203081c040380d0300d40d540c4160b48200c10385000f504010700300020715075944907080b0301d034018901d812030b14645030040d04c440342c0f0640c1d4035510b0040160355400400c6250030074801d04061543c2130301c500300c1d90f10a415040b21000390003840a410700c01e2a01901503520400b46010400c201c250008001c0c1c19114200341019a801e40900c1ca590403080041e02501c2c039103c1c11380344c2107a43c000c61001c0704030304503803d0103071030900940b14a003912850080440c07204003900591504241c400700004a80c5104802e00d401e440340c01e04c105040c452041014481a100c440c1c601017503a0040e10f0150382c0d0121a007180d0000c1c402c551020b4801e010202c0c2c0130881012080c0410078682c000c504640117945880d04100032004403607402051410308004c044c05114400c10a56075181c00760050302e007000c0404132901c040c1c0b50b45a00b400c4459500043d07248c001452080d91a0b0400214903040303400c14080c07000300e007241c840d0380001341c03203c1400700700b001d140b8143d40b080b500c604084000c155143d90300068 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 41310805 1250 41309555 41309573
    0x100207030c0b0304080a031e020c0a0b060402180d020a0510120509010203070503040308090a0c170709050603030a050d0204030c0902070203010506040912030b190807031b03020a06030203090a0f 85
    0x208480011100c00e00042c440d0700302007603a01a0790000d407580c0c90020300103000d9001b041035600f03902400084401c0400d0840303031840507004041401c800340500851a1409404096005000502c034500c140a00b01e0861048100541c004030140c5520960007000e000117007041c4895030015600009928000c0303411035006a00210301200b800042c0240c5d183d4514090907800211862000607005200280100344106642600003101a00307803401c0400c140c640810041058101100144130760030308000e281001c01c115001801411010407c50401e8400241c403449003101c081c04014000c00c0e447d08520307603941280d00859000020301c0e070160f900e02c44100a03410449050340300c3d5203068000303411800c10340100c28a9942c06140002012007c88055009100c01001d154003d50b020440c00060050b401e030490150030000c000b071440f98910310b80100310f14650612030705800c610400030001070300e0300950001903580314140941c407a526042c0c1949000c81146010340f030801040b85000034082c0e079034 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 41312055 1250 41310805 41310809
    0x501090503090a060c030203190507050a051f06030b0126030a0206060f01020d0c080313020301050a0213120302070e07050c0115030b0901020403021c020303090d06020d0501062c0f100207 82
    0x1540c3c0800d0b55950340011380d18130b40030000260141e00300300900c0075011324108285461a09a003001c50030021a900c0d079178075011002c2e00456032503004000803083c80234600b013a44083c9140c182c0901c405800c40d034421800060600ca50613014400040c0c0242001e5103140140194064404682e203403804c40d24002c2d03940000366800342c01450041d070302c4a210b502c040b0f585c0441605a8540815000321030750364450341d07400181307650000364400e601d140041c2e900f030103018040e002c842d03000b50b180c7e4028503500740c030840c999000d00000212080082c0001c0d030013240c5c91044801c50269544240d0b69032109590301d205855800e00594a420404c892024420012009483c01010744c5581552030002c0d00f400c0b032103107000c003035401503050030a10030140f1043d2907a204144041d050341c3c209050302001c10200d01001d542100c0090b0089201429010b6a1190304e005008a18051340001c2403140001c04000444481c2c240e40001486070101e50340383ca00301c40d51441f001600040c0350f498414802503c1d02424 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 41313305 1250 41312055 41312059
    0xc0d08040c17060f09010209120105010f0503070e070e0f10020609060703020a05040b0c070302030106061d01020105010302100806030705060307090603060b0702031e012c0d031415010c050109050309 87
    0x358012500b044015140b6110b1000c0c1c40040000d903c60315a1807030041c00040c001d41d0559020803400d00561505921080145003103000480c8550401a0100030f001c0d80d600601c2c02980001e01c2040750070351345400c05401110b9424002e002d540000042611240c550f4407070380c0c00c103200b04696a40c0590004a0311320174102c5d5810b80d072154440354000c50a920519400000042c000d10060000f45511030050035005c20020465594a41c2c80e40460b081d11107036813004e0702080d80000341140203e50020844107050b024030013040b296055130300046000d080060210100030302d900c0090100e4804100c07000140400a09036516881c00980040101c05a8003441000034101800060181000000d0b141307100d500170080c12044040d102e1100b011030480b14030a81942d00c4020810034615100340c42c0d0a03540c120385025500b65822000c1034071302104140e04204142c604442c004081c000b01c90880e030482c1c1c100420840d21008000102c07035220303094038090701e55480c1c100102c0800c0750010081c00000d1003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 41314555 1250 41313305 41313323
    0x30a0806010c03142118060105060d0219031d0307020d1e0b0406020a0e0108010b09060c030d0e01020a110607200a080c07030b060d05030d05101e050a0f050d02060703050c0d0804 78
    0xc41b910f1000050707407501075024075402000103000c1440e0120103051545d41c080401810051140c02c1011083d100ca04a44003103a03413000d50710100c0d043c400124240240240040d442d003000355001c00c0c4242c003800006441022502d11403040b8414490000e035426401101c00d074000e0915042020003980402000c0011a02c0c0100d0381d07040c0d5000f101ca66040302e050300c03085810021804107000040d40142c582000500040110b01404107070b43c45500c4520319108001a107450003200050040c080f02c490110459101404014031540e2140c1003440f02c880c021501d103d050482c0038040c0c41d200c0b111600514918001c1004252440002114011079001e0408a12180c503210140811400d4081000e0f0154000300704030f00e00403105401c0250041c281d482005030381580c80c580f021700320340b2a05900c030320340c1f0100104021624041d9041000341c1084070a600102d0302d4000062680443c2ca40c0c02030007400c0220380761050500070015500080400d2081da5820381488500038410340c01120101e0385050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 41315805 1250 41314555 41314561
    0x9050102190e04140f0405030702180108060106090e0a0c02101109041401060c0b070e100206070201050604110702190b03010b0307030606030506100305040f1205040e09030a0806010c031421 83
    0x9070600070305401c43c402d00446004c80d150080c203c0d201030303070090064829200401c940c0f4016120460350512102c02030b6105841035040407001d50819006034054800c10803041c4c810b0008440e020880c5402040014001494501c4508142d081c002c028140c107040038500401c004651543d10300030007a40404031810404141090020503e484084c0990800598401801800100b6492001d40c10041d01d0a01e2003070030300004001303200c0301302000c15580160851024015005d8090049030340082d000c442c1440002d007488135441e458014030b41f010b0b201d46003050340c22121020b4205031a025003180010b45591f90303121284281160300541d40c0c0e00002e4586400011014824422180a00001080b0f0064006417000c2203010300406003040d00e4400502c40d0550000c0d120071241e00b101025501c0c0c03142c036586842c1d8000b0a04034001c07c070b8a1590010440400002c0d40400350030340c010024248003400e1f06543c1000c41c0e620701030021404d08200c00203010760709080200d141c0e001e54901c141200e0b055503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 41317055 1250 41315805 41315809
    0x1061d2704030c150b130e070308071115210415020a050f03130510020301030305040b0703020f1005090d0207080d0324080109060b010509030a080c0a02040f060e0c0c1203060409050102190e 83
    0x415584000c07da50704801014000201010018000c0394047e020102210904900103001c402112210496614000520105c10103a04442102040e10016584900d00d41501c07842c48500c4007010000f0016400106060081d0107001681d43d059490000c1d551a454201219040d01d030001000344c40071b100e80782200c2c9529040b4001c4a050740c0d0315607141d80c1004d18000418030709801c203890841c1503003d044c0c20b00c544200e0400041002d08003440d404a0b003410902c51040c14200840d80e03107800c54100c17a40500a00200244c0098080043e00d00013a15980c032298110380f80120304205c0710301c980140c02c00035008205420042c42140035000801490b9911401902d02d44100740515030190044089503022440e940f001c1c018895901d425283c641900d81e00080888811414240000b035442c101030080c14202c0001c103078803008031000e55141a03079810990750346109680c04460b51810003c0016441d4541741c114000c0a64410001e640b00c03110000400109202d610400d0000f604145070ba840da8 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 41318305 1250 41317055 41317061
    0x3070302061012030e0d2a0b07030509211608010506010503060d0b06062101031505040b040b04110909030901080a02040f0e0604110301061d2704030c150b13 69
    0x3c81d01c0210f603109008042d641078541d60905480b0702e50200302501a080441ca45412908052402003100c044416030500345100f0300185401c0000356840c00e015080c0000d8002c02140c0c85113a0448411150000540c000c00e04d100c40c80c4000c0440b8040c50a22207914841c0b40001c83c152100c1d10028065a5070382001111240000c654250384083c01001d02c1c00815158081141c000c440074045502c2c3c0b00b51414030060b5200c2d094001c1905000352001003003845983c00e4800c0000c811100148100c3c1017684944080c000050700c041c203a0031000c1d020800f08101c8000b60840c8440c0a0078110403850306c01c05d810345981020040070b000c00c2c0c0070400900246402d00c216400d032511079800d00c112900304000c41483c5a80180503a03001380d602e000031501082d590020f54001d10896403078074044a180c1c01c1041d03510542c1e2400b68080c1c459800c468075510304800c2c5d0f00a4101d0010101d00b0030750742c1c074101214078408107000030f841109000800e140c040110b800110114405541221069000040e401d080b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 41319555 1250 41318305 41318309
    0x206010501031b1808030f07020a050d0309170f12030402031c0518010302090a090b011205040209010621060311150408060604110c011103040c09090201020601090f021b030703020610 80
    0x1403d480028501082e4003814003202c01020700c086000f50503842d00700c5070786154880070390f1441c2240301050b00742c00c5103010001100500016500c40c0040f42d03c0380d030050070040d580d009034070000d06031070258100d06108001c940b0040c0300001c00c131620b21125a880010741d0303006031340036406802000c500140c1c40340040d00900600d40540c3d1080c1c948551210a507a64100e032000d0b8034105602040384480c25510b00081c00080d03c5441c07030000d40c4400d450300242c000740740c274070490b22000e003400e041002580e580440d80d411214581040500c4038107080d07a680414005600c800021860850084140104078120f030300326070000e442d000e018000401d402000c40c044d62240103080d030320403000100c4508094120051102100f00c1d012300f040d02d07107a0101c0c04d54400760302d04440001c000c01000188501c1c490000000c100011003048107503441e80001b07440b010140904500301c1d0b251000e6280c47e130000d0381103038104030fa62040d4960b0410720400103900c0382c0c04500240d0040c850040421101003140a031003003 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 41320805 1250 41319555 41319581
    0x3041202190c0f0902180103020d0e06040b150a0807091104050603040c060e030307020906151306050a1d01080f04150c0909051e160915021c02070b0714030d0603050d020601050103 79
    0x5500b0360070b41c0112301950102081960f0241c8603090342d42c01030010031100b40103610034801c2e9800d41c900900ba0b03103042040f41492500c10181e81d10108600c00002c5030300e605980c01803001007070032101c00b403a255a07403085030700494201c00004101300a00c00a1403450301619282d6581c22602c866a1007015901d00a4150180d071203180c45010510602d09240140d045c159003210b80ca090824440320081803441d00c0d480a40494000990070082e02c2d4800c0410350500a0f071f030302c81c84031001801c0008007055001131420703a030140d06e1000704043c03044100c003081d40180030324010302c141185440020003000e801d20956191900740380210f44031160000000004500c80f010b41441a51030070380342030750380c800e040c40e050620282000210382c0c41d4804582542d180c4094004040109a4103030f100e07a0080c1c000200009c54100754400d00c494440003045840850300142c0500391074000c1d0354a9800d5102d0804d10755010351905400000b040404075030252000280e400b900c4540e0303601e00054040d00c0840b2031400c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 41322055 1250 41320805 41320837
    0x30601050612040f0203010903090801060b07080703030c0e0303041e0909020f01050a0314070306140103060807090902030f010c09061b080702060703020309040c0908010606110303041202190c0f0902 87
    0x20342118040b0642e010340070b0310300031540a455802081c211b806ca1401900044c2a0b000c0902100b4405d0003141c1c02800d00221a528224280d01c03003503607a0085400007010561200b0180c2c4035180300b5540103c074420010152940d4a541d001c03004c0070403001855442c4078038214880002c03200042d110712000c40ba000b8105d0011000c0003c0110b544d684208100024541d0b6001d503058041c010080c014458422520300142807810301211540010a0040090405080000500021502080101c11925142d42c00b007240ac005100090900c06800407203045980703850030480720a40e1204020003250090748031861002ca0901d81c14108a02c11140030304130407000c010302001403d00c2c1009100c103601a206032420211500e00081c00c3c0e42c4460100800203107021001d0003101c00a1241400408030760500c60310090484415a03240d00004202405411803103080010383c90080c01000040d50ba40184d110200c18649040a07040f2090b0207074110340d07030a40c10701040343c4925100315034480725031500301 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 41323305 1250 41322055 41322067
    0x8040308070f0804030f1104020c0703060e120c010605010e1806010c0c05100905030d03020a0206040b040501140a050a0f0207021e040b030106080f061005090a05040812040807110306010506 83
    0x110300980c084003040741d580c031030003100c00d01045061001d0006148140b00c1304515480b02d00b07100c0385010442000e02d10845c810401da107202800054500c0c11240d1000004c1000d034680c040c1e0303508115048402542c142c1000410309403600381075205009460090f02c51803000c0c0381103000e1000e2103a0304003a4500741410400401e210758014010541190310504043c20b0050b2504003285560380b201c54441e01186c180142800141303402d00071001d501205107030071420074800c2c4600030f50b10b15018001070b1000034110045401c1c88001c1d013146001c8120a10000218200320320103500822080701c85d20300b070a240000000000416000f05c030361b455002411111100c0820900c0c9810170401111107620a0b40c9007180071990301c003801004005d02d8550f014000c07940003d680c0a080040080c451880441007510900455035410200307500001c580c58000750f6542e440c54451403511410700070541c14604d4404010810465900034a0018420042c1c10950f03182c4030181a90740d1000c1c003c1d140d1202c400d00c16 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 41324555 1250 41323305 41323313
    0x3080c01090c030515071103090f030a02030304030f030f02030f19020f0607020d03050f0402010207061412040c180501050105041401020a060908091c05190212120406030b0904080403 80
    0x18006145580000003074441255075208628540c50340102c441c0d81000303445041d0b0201c2c021055901004d03900f440350350800c1d50540c0d2600da11490720120b22440e104141100d2940f0104440c02c0354139800f50850756659103c0c14540c10031804510103c0c0013a0031410040032492001c07040d20304403145100b019051071020000c4144171000c0e2184007045110b80c00711680921800c1100d07038042e50540e0003a05441c1e06000c00201901d0006142882c00d240d20420702c00141d0780001c0f03082c2101c407e4907044000780d60580b0301c1c04e214810f6200bd04500707c0540240014403a400000008440810107903039520348502d20602c084d03d00074802c240c0451810700040050800100081e41c25a40501c10b54240280c0b603074881e03040300d103c10815150705101258880480c1883c0c03548010b040c80c5c00320345c105a54141d995942c0d4130348807d1000400404851003d004540f2904210b11400500b00309441c0c0044403034035480d050360403d205080000b81810000341650800d000c20b01e01868100710840d29250031a00c07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 41325805 1250 41324555 41324557
    0x70807110117010b040f050103061d040f0c060203040905060103090b07210e0a02010905010801030b0703020906040b0d09050c100e150910170a0216020f030c0d11180603070308 77
    0x1a000741440102a2408001c585101800d4043c05955044c0c60311103041c04032401c280200c0fa00010305052402d1000e0205905c011100c40c01c0d84036002e20a19291703101c0c84e001d400c040b01410b0040580c03015902c0030581b40c1d0044081c000703490704d0000405c125500e86c401102507468541002d04070807514404640c5c524890b9492214414240c08481c6841c1121003038030044850701e407100390068114028000031580c1c0101400d005001c01d103040c101d82d50664452404040024141600717041d400079031403e041d2200c00c269030003410800069502c84080094400140c03410304002c07035aa00440300d03029010302e0000c00000203008240e50780d9025050b02d6003489030701c0c550380009510040041c0b00c0908190788540c0b115a142c402075450341d01c011034400203000c4030301000d010445d8041c014407081200c8241030005c94001c640490b0b901c0c0b000032104001ca410500e86889450304000e200c01200c06001e01c40d05900c40342c0009640b07403da03031913000c13003000f442d000142d6003103606800c00300040001c141904 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 41327055 1250 41325805 41325833
    0x6030c0306300105061f090b070f0b010603021b01060810020c010609060b0703020d020706050901030902010e040c03021809070813050106122301060f05010c06090b0108010207021005070807 83
    0x5a44078041c25441e804410030040402e081c10143e444108018003803c18044441404403003e0440b041e080110314054040c0e000740c0110320040c00702103012003d21810b40c100c80034070f03038000c440c1e4245961100301c014080d51003442c019030144c440800c2d07083c10100511a8408070307000c400150164103020741c0070030082d51020491449a640300d00012400540038030840008010060400341e6403c83c0d4034000e428210824044810354100704000c10035160080122050083e003440d00042d00045440140d640c00a01801250428030b00070100891340e4041c2c0c01841510841211900d00441c0d0104000140c0011aa1180090265004500c1c00d007040355903008102d204c0c3c0c00100342d0544030350404c4041c00c2c82070703005c0c1d809141c502001150f549031605400c0351281483e009002c2a0704018034440304c0c502601c1210304000003001480d050107802d0b030118008962100580c101942d40d041e00c94041c1d04800c1d0140d10130001400d540f2031003400b85048460003540480e1141c00c0000e1038640500c404010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 41328305 1250 41327055 41327089
    0x80711060a020d060e0901091704272c070b07050304031b03060c050306010f0804030e060315030a05010b0102010c17010b0901030b0402031f1401140c07150207050f06030c0306 77
    0x2035070007140004170555510300c2007807284000130b0800d5a50401c1203107020105803103203002c80100001d0010b1703820500c0051510340030300703150048507614020100045c01c01c2c8071001008a456401c040071030041c403142c0d11916030910101d8a41c20b4980340584542d1080241c02410703070307108100801c0003401d0030381d42d0b000050b030752000c8400182d503075100c050070f4810303401030b000000d13070000100311166801c202207030300c2e0820507c0d115800c2d1515560180031203038511402849501d000c000a10003034156000c02da628070b4080c0c02e031280003900f460080c0c0a080c50b400254095424182400c060302c0c460424949000b0029403c545140d01e0001040c140341d0054035524100b6489001d41e44d1f40d9103a41c0000c500a600305041180ca0a84001413100070004036004004080e031007940c1d0305503580e4001c4031009004000209256950b074850686071a00c0c04c1c50f03201c00030080c206400e540e40c094000c40c140c011a6010347e10340c184d00c43e80e0810060b051004035011100b000302400400c1560418240320501d421300e0b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 41329555 1250 41328305 41328311
    0x10050c0715020c03070306021c09050c09040602040f0f03140d1407110604060e0405010510020c0915030a0f110301050c0d020a0c020a091a090601020a02090c1e0406080711060a020d 79
    0x1c59003c2410285c481d00103807061900095104080b0075401c0e400e00d065110681c0410030406c00740e55898454203089a80b61041003810081030074880203070704450003003034005200710b0910fa48200d90103080c100c601c41950b52003c000864011520302003502803a00203543e07241c10b074078072000241001c00d40040f5010b0391a09420080208a030300d800300180054201c9855189010195000f00000d60b47c0581010b0b0048105410a107440c640005192250000c1121144800d5641340c2c20b0340701e590391001c0c1041e410300c1031a000070140051003241036a110301585014905006900905098071340564a25100d40402c02a032503075501c0035409028405043e1420400da1261900004c0307040026130050039503035656214040003400d504d09070440700103090712286003038988000040d44848558401078007600c40f21000420444822084820f4201c1c1c070400d0350450903250004007401e410900464000c281c1c003001003043d4500400350b081001c180003004010321b0341d441c412000a50000e00c01d070a40706803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 41330805 1250 41329555 41329573
    0x2061303080708070908011406030d1110020f090d0602070b16020601061d0d12091202060304080901090306020f09090f04120311070f1a0f040b010302010305041106070b0610050c071502 81
    0x10080c011500e1403803234550015414103182c0304150810750204900c3c018400400c030240240c1c4004a00e0750324512121800507140c3c00c1044010401e4454151070b1544050314140c0d2104000d070070360140810500035503400000381e82d00c03000c801032445200104005640107030b0040100910913020028040c0741c04004210f00c3c020700c400304c0c40011030031804032a0000402c180c1e225440c1d03c030301d0480062109038640044805140c01017482ea11010340301910008000400404c5640101c1e00790700203542c41201150f40d80e484d41c611500719040048620720038030a80d0b004c60089020550b0003805150088400070801c0c0c0b80d22029001000300c0040c23680360010034000040400d1907004c072520214020f8049100c1041240310401c003074a001000c3c00002c00d001424000818048072140381500e9081c00c000803551503a00f4901214140342c50303e2544031500140040400208440f0300e40035040070359600e8146441d10200751103a02406d12140e5640c0e00020b01005081d800c100c510b041c040d01030041e204112 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 41332055 1250 41330805 41330819
    0xb0d05070908010504050f10110d0c0c0b010308090306070801050315071806020114060405040c03030503192a030b01050a0305040809060a02030301060806030a0c05010c02010e03070906030201020613030807080709 93
    0x114102c1781924250400c80da050000c00c402e200b10003a41504e80340400125520300150820341c011520403410147c0c0d15000e01c03414034010380c440f80826810030425005503039289041c540d980d01c8045078034002d0007160042181d07540034030700795030507200001c01800e030803001c84405d403003c4140144603204006080c000b5801c90f15881c84041e0107412194004079001c0051003620396001c0c0c0107400103002d54a0682000040341d00c0d802d0100030b4035031624050b5035948034130400004a502103000c00d21040d1406401da1709161704890713000009040c50141e040030b4480c031b2a060781200e0407050401d010820400c044ca075014400e80c081603103c2d1017100e6881c00c11440001050285d04189103440142e40300100602a45800880665001d9012802011600780981d20300080e0103081c89050305025814618404681c001d58841034080360150481c1d41c2141d443d000c00001c1c00303542c4016030249c0141d201250301d010305182d803a04400d030181c84886040c1c94440c411500f01000078000010042c0014011070300ca = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 41333305 1250 41332055 41332061
    0x1103042402040611150108030a1d090c090906040504031b0206120403020a0c080a021809030918070e010302070f02010507020312031609230f01020307060204080303010609050306010b0d0507090801 86
    0x1d808142d445028040413030540c1031800f60030800300c6841c60405001049000c4002086818054152404030181644110102e520043e03401c100303039001e0500d0040103c01146200508480b07407088680000540319030301070104942c0242c4000c0c0001d004403681030004440051034034181032025041a01d00810380e070310341240480944080b00140c100c03990401c144003007403820340090030b60b0b0303009020706030a01d03030004802c011050b40b039007149000500001c42004040c030a890706844054030001c841c14512801c00f00e0710200312210707008110102c0c5008140c0d4030078401e442d02944c2c481542c07124000540c00540c0c25401a03141264540b203020070b803407035984071034025500444603801d0450350302e108203401400700310071500652054402101400e000301d400c20b40d1034100d00c4041d11140040d01d110360040f07041d07118100e800b40169000040c0090200340000086040f614a5590a10305607100c00405840d81c00c00c0c0700e08000070340d091210300258001a44101d401c10818100070784940da071a0100e90039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 41334555 1250 41333305 41333309
    0x60705100204030203010e1f0b041806090303110412110609150a0e0d020108070e031009050c03011503020117070c06090303051501030c020706080c0c0303010f08010f110304240204 79
    0xc50340e00490100300318202401207200d203c00c80b0011307190b81000c10800d010700307442c125041600c40c0d445d81004441511181c0c41800021090203c0740000606400c0050103001046011400649400407201220525105031021764a20308040d8038000f801f603c54006584006003019484001003041c03121603510b4902051000c12401c1c80c1588039401c20070050a024442095540134010039448600140c0e07100d4019544035950342003844004161401107854948240013481006150090010a019000924001c8950101c00910201c0c0304d01145402c9001684402404911410320301d800603851608960341c8030300c092070030140d038404544400056801346241500071030394490134855048a00503091603404e03070070700f020301800d114201c000b551011a0300c00e40303003002820380110b250301803840b00700d4412240800803aa10b07075845001c4103003014500e11400031250b1a1829842c040d50311400368001c54000b0b144440d0843e55151140a40e618404a8414003840c040c4811a40c510a510240c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 41335805 1250 41334555 41334583
    0x91611250303030e0102070b01090f06091d07080309090c030702010b03030a030204080607030b03030d021809010e07020601080a0b1b1201030803013f021201050903070605011e05040b060705 83
    0x80c0620710b06010701100c2d010005408280d0042142031b021511000c200380c1111500b002c0040c90b4282500c50f18014401504002215420510100c80c02802c500e49140220544420340f0107036075884841c0c40c0c2d00e03c104000150003800050000d00a07800c114003842c2d10414a0002103600400000003e055a00070048000802c0e8041410320810340100440c1d58070540c01e0400700042140a80002d58a018030001510305503000500c00c525a40600c1080303540c40070250802e4070325610b400b105000203d0444000e0b00500c140301c0001115207000070310150542c2c1014000720903490f5107c90041142183e101c4410024007001020003010080d030006000718050072505489506244003c103801e4590881c00820b000c03080c22011015401320ba40308031004215001c07210300344803440820040c04180c0b140181310752800c0100107001e0000300007040454400c6074100110380e222840c280807000c5520208806090001c1c0511088c24181e204c484d8441d00100b016040c00c00d15600c052400c000d24035541 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 41337055 1250 41335805 41335873
    0x90b030405070e0a0e070506090a03062f0304110f0d020607150c0201020406050405060d140f150a06020c1207091109120c10030b150706020306010806091611 69
    0x3c00102491010b40210b142d00c41401351117a240100c65807a0618010a8030903072000075482c00c540e0b0380c013141030300450744003401740f0284002c48207181c00d054100b010301400c24a40340700d2030801d81418048174803956100c18100c848520b03020a1100741c420820044e904510440d40b1007001d6502c03507000d024060f200d028001110000124054103a880c8103a00c0b07070540e8010300c02442103d4000d1b050ba02a07a0303065030020340303a40c9902c103488054002c00b000d410f48185144148501030122100c01c0d88682c0400000d04440d903080818803810000d98416140180c00102040403146440c4440850f03154181040340c05040d205c00745001141c03560808030242c090002800461810729090340420b81303455401030900100c00e40c02280340380c25050818130030503954a545400d140d545410f1006030080c0c000285485e20594074021000750b20036955103021400c400b000600c82c0c5050f4042900c40c0045c0850340700107c0000c14240c400c9000209003462a010384e641542c002031f83c103640b4001103210031000e4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 41338305 1250 41337055 41337059
    0x412080703020d08070f05030a0f02070b010317070f02040902040902190806010503010509030a14130b04030605060d050304061b020d0c05090903040e06060d0e01050c0306030721080a090b03040507 86
    0x2e0f03e410034690b845020f0144a40812192035040440400b9181d094205150750b03550b14070541001304500f070980600c0781d1001c20100300340220b1018080c180d0f0300c1000d0300707202040c889410000c28002c00c40700902c00c50380c2d0b040020050401381c0280010500c042c20109185149500180241c4400240c1e8440c00740c40e04c50400140c1410811180100426002000715042c46550140c891040c14003c00611095081400c2c0c412546401c41306903241542c0061030194840e46214500c2d0310a102c144d07100e60604010401c1460314400c10320a00ba4404d000354a894541403041da5140c0903c5407101e2000000307541d40000d0703152a40300c4004184074078102c2c50700c0c3e41000d041102c0250041c1c2220819402404144030101e00d007900240c0041080300d812b40c031241c0080340e29003e0034204800b4a01da500303210500450341c2156028501845085041e6100d9540701d02c61306003052400480400601520036113000031650510050008111600c0c0080320300f0303162071541c170440c0d10a8074208c070307035030300510342 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 41339555 1250 41338305 41338307
    0x5150f191401120216021203040b0d050109050601030e071505040e0405010608011d07060c061b02010c030f0c020601031104020f04060c020102010507030504020f0108070e0d0c05040501080c130207080412080703 92
    0x1881d001807800c50011030074841700c1d031907a030340c90000c0c9200280a0110840d80018504003001650700800b5510f18080e038841ca00414880601003e00c81c0781100c0742840c01003022503010340035456442c1c07807241c01071a00724074008103202c8600c00500c81e0024060100001f00e55004c4158559101d0303801980080f505600d400c0d5544e0842d0384c03c070030900103180ca40d040540c001c2c1001c01e107001100c0961504000d8101c26040000007829140500b074440d800b81400482c02d940c064222104820054808001c40e143c3c0550890948504024150060308070381d0040c000905140d00e00441510040c00050400410b0303101510700da0b20641003080071074803e00000c001c56030309028665001640e4076003803029042584c0420380b807007640031469050003004000900124070684c82e003e44118000c0c42002c81e003a8600f0500c6800c1046d0180c240140c0c1000f00220b900e0200082014801d0000b03040010808004030100c4004d41000380101e941e040c0c1000000703140710302115403e00711401000c0290361a070b02e901d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 41340805 1250 41339555 41339567
    0xb040e070305040f06110906030901090b0f090c04090804030204060605031b0703080f19181b080613030e030a0303052403060a0c0201091e0507060305150f191401 71
    0xe12080508010402001400c0c41078601d01e4280c2c400c030003186a01c0c0141340040d0a0040c00c101e01d030060400b104001c141c00381504040c580f01d01480c0c4100c416205c600d01c2e0104180308541c01a955070104a480d03602d4141580070045641c003929605040c141c41e540082d061b9851940030310300203040441031002c10120004e1510307007000b8091800380350149540d009172807500c00521024521056000045d1040041140c480c800c0e09e9040e01004810350a000a1f61101c54040c002d4070751048003880b00c07078038009942400b42a80c0440e001800389540385480c40040e00e0300c485040f020000ca0401c03508454030100101130b10503200b0740380451a880d0600290079044d00424042440d160b950301d100070541c0740401e0302c5030425a42d02d00843d900b03100590036030140460b444010035000007107071200030b0441c8902c07501c80d00900c16026124081d9459804806551043c1c841e1112206890750103030741460f081c140031107141c00c050800c50090801c180d1f107001e1014554050707810b50640d04641c458a40c0c3c410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 41342055 1250 41340805 41340811
    0x703020307080c04030c091a0406080129030a020904140114010311030309010903030503130507090504020301060609080c0607030e12010b09071706040209150c0102070209060a06020303070f1101060b040e 89
    0x2010144c10989035885403c1c0111440c418400381580d202e0301c4000000048a044c440518068000d01207141c4c0d94511070f0081c0a00740d104900d499264072401000200030766100340a1000500030050080c094082144001e400380c400c4031080d10401080c095000c080c02441e8242d001404090031640c51802d10882e81c804290965100390401c124806441ea00549000d042d241c242c50171301c0d229985c030011211141a02d00000c1d00d584107035003000540c010b00340c020b40e103da403080d002400303a980d031190251445200c0d801100e030a50000b05060405c1e0801c4006001e13401c0c040c2c9842c0b4859040c05000c29682c1441c40120100369448030054182d45c1408509240c00030705524180310b1400d075060140c560b01502a054512640c0c000400e9241c95803580300c2c00c4800c004441d94243e9800c2c1142d0618000d40c802c0c0c004030300483c001800a0442cac645102164201e030603c0d009180396990b880c80032507955191000720390502c6801c20300300c0c0807008248140b40c0540361654869554a0130066000240c0d4002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 41343305 1250 41342055 41342071
    0x22050a0603110307110709090b0402040e01050106021b01020705210105070e0102030702011404030501050f09060c03010b09090a1d0a210215070c150c030b040b100f0c050303070302030708 82
    0x45901c402d03064a444048a502800c03a00d0f001e51240707050000f003400d156440d40070702241c0e811b100c2d1140500480b41d10941c000c520854080045040c02c240b103d098500034030034030b405600074806403210082c426661203241c0c2014815a41926210350015481d111a1800b117a40610f0480b80082c21081c24400c45400080500300b90202403075910000f0f43d45c0c8036107040281003101191070010982502c07802d0360084d5611100910039071a04000015030320400302c0c2c130361406c3c3c0b181802041c4403041c079030101c90607a000d41c4007041c40e00d04074030709009622201030400c100c0d050740c42c40710640180221202546040c13510b401342c000c0241c43d04018800710721111030308180d8403020a10003c182e0300040d01b0030081301c000500c0384650343d420341e06407010352034808050400203044003c019005403ea05c82c2c807599402e134030704218000d001c0c0c080c40200d603181503246801c100c40d0444c52880038002e40924981840d03a02e4103100c244c0c3c0799910281503810540b80300000c00d40210510000c16000300d40755500040b8 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 41344555 1250 41343305 41343311
    0x30c110a0509150103020f0f0c07060f0807080414010501170d0305060d02120f0a060605181017010e0a0f03110619021b1524090a0e0322050a0603 64
    0xe101c001107400e1006400048500e01004514225034042d8050b6000542d00b01821030702c50a943c00304605075403080751640041e0044d8080400c0f01030007070301c1000c00094150340d6064075030b807102c805441c0c900010744240c0321034040c081180c0d0800000d00a40d030180544400c0741c0c449991202d182c1d4644450038a00405240c00c1c002007150a031911003440c55080e80454028102c0540406100c0c01e10600c0c20054015019070550719050100c1c0340c1200044880907503210010f980d400400d03100e0444141d40d2040310800e0520204906900709e0344003002424043c000141003c100101d035850708402140845074032031904651401d040d04840341403410b4040c040901900d1401403c0c1c4440d403030301c8940c206000b540c0455516135244c105561100003c1e1000100c0d40c0503c40486160302e03080007295035001c441030b401150541801c0780e080c240301046002e058a20a40c403190900405441f40c050f0210743d9100911500014044004250f00c410200b01c042d07004150800d001e100380c10310b05800200034181 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 41345805 1250 41344555 41344559
    0x2d0607020706091401020303040213021201140a0905010b0a12021606090209060105070f03050309010b09011d0a060605070807060209150703090503030f07020f130606030e011a181909030c110a 84
    0x10700882143d40c0540c1c101c40300d00d103500070401060024010315071800790402507134dc00030980d0b106080300b00d035201200b02c98402c880d554400f142400e40c0d000f4001c40041d14010b1107030b0f01485015454011003007490603005414407140c0900c07200800c1d0316140a503000c60b20b13048840c00f98200050941d82000c02803900c46d1926070540c43d001c001e00c442c684000c0030014000002100c24000303611044030078900401c41c0b0003a507034410300911420240e4880d120580310000c0030030b11a003c04d10401c001c031682511001d08115040d03c50003e241c00106054a030b039070702040040340980e41e20741d825501c850821030880c0c94000d2801c0c0240700090b41d070040740c0a40e004021100d180d042180c01c0c1c4900701e5045581c03041c12110080880d00310450000200d4140e4105000452060380640224001500d504001c2201c5c0c01444040040034103210507042d00302c0c4130340314900251b164412501da400b104032540c1d03800e65440c061310001290002c40040d00054104200310b82000143d8402c00c3c5840401c90710000141c0c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 41347055 1250 41345805 41345807
    0x71403040218070309020a09090b19061505070203010b0301090203060c07060e03030903040303080f01060804060b060c16060e0a03020a06030525020604020108060910150c0203030301080d0206060102030c2d0607020706091401 98
    0x2520181c1011161045900f229002f8200ba4110742c025062480d000090f0158017400500b06411001c0224425401d224040d14541814403c0030b9160750010010481c5454880c0c0441c2c1990000c5420313a002e03a12800315012801c41040118056405a00290358880c40c504004000900180404942803040b078010461541d000c2c112136042a00110300103074540c41240019140d10030700088400720b0207108001d0a40303808103000d42c41102c41e540c43e80001030281c0000c1216000240c04020341c815040070b0309002440c032a07400603a00551000746003005800c1245180030300c2c504c160a020050f440350381040110359100031a01d412540540e001c2116082041c0f140c010b00d10b00d8000d60200344000c014600e007541c4a46103403400b194000c1e0a50b6070360758444e800e2a860b0740e020281c00d40580b061801180642d40300000b16600307a03a510014144014888c00c00e80b040c40c110b45c0340310b040c05003070003100704402e00144580350041401e9002008124a4030b880946480302981c40000c8007004025001856 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 41348305 1250 41347055 41347073
    0x30f030103020f04060e0718060e13023115030b0d020d0302010213080f010b010e180903091305060114041d130819020114071403040218070309020a0909 67
    0x500d074103d030780001a80301c18010800603e03041e400400d54018450078000c04c070b41c02420661541e194400d0b00301c2c005460345015141c1413012100e064008109d003400c008092903550241c10030408039555082128070020034119801d0300c1d25102d44490b50070510400c0309001070f24a441209500341801c0c441152008002049880980406030142c030f0196114410113200f0360458000c0d80017001c0c0d0542e1141c07034a64150784c0d0a005070089049601c0d06104e000150300811703c00181c00ea00800c0600000b2549020507074810f0701801a03170b0310388010701500702c8568460038000020a10020300180c0780c40d0201c001407820b0b00010900c1581c900802040c00005154040b2050100048080c0101c1e5242d074561406003608001020701041c4000c91303c00101c0402840c03031b08460703295500070b0100124180b00013618810581e0784802180e0740d080d00d1820050320704080c2d039101d800201288010341c1c400104a04402c400c9941000090340c1e81c2a0300c1c21031030b009180c0e201a10140c002000785113500e0b51144a6 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 41349555 1250 41348305 41348309
    0x81c1b050a0503070e100908060105030303150d080904050f071e0f03020903070b0408060609010b040806011503020c16290405060309030403050a030c060b09070e040209060c061017030f0301 83
    0x1000b90020000b40b103240144280c0c0070210000d810a501c2e940105401486440070b4001c0c0c882c24003560f0000200e514002060382d009949900c410000120104100308000a803a9400c40314076034244403103619036072036100d150b00c100c0c2d214402d00a28540f4003801032111654003942885d410400140d48042548081d4550b40c1d03044c60b0400503541c0c0e900c040000d142840b00d521000b0310241c009400b01d1214004076009004103015180780b100d603621454032910364012402001d07020f51280004100c1110303a400004619002814018a06107600c0d14050404008440038100b00391500d00801044131212502c0c180c10381c0403044100015018000d48503d031260344210391203400c0103c0400c0c0c60050a004690046501c441222040000d900d0f0142c440c000070340302651464900704000304d0740d09000c42d100d0300c0b56400760f50341038100c80200204402074016a0340d05801100902460032422000c1044501a0b52740401001d5180e1402c82003015000340d041644459420600401c1c0c901008801900c0c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 41350805 1250 41349555 41349557
    0x2060906040b060a03050709060f08030a0e04020703120905070609080102210c0c06011409070f1e050415050301030b31082503030c02071211030307081c1b050a 70
    0x109883d240001004100d05070400751490144040000d40e1002070380c8640211344c1807000b500b488544d214850354407401044030542c00300d030913450303c48081d15141d801843c40512a00b08580c3e0480406024000c80741015011241540a44400d002d4a030300b0044038402440002c2c003e524003a840b074001f480d40d20014400140d08000b072008107a9101856084d03450070040ca42c1224450f40c0c1d44c0c550311240540f0010054051004403004c100c80038414141c40c04100059207070041071500c03440000000c0310701204105e0170850144004a2002003d11500845060a0f941d0030b0f1a0350443c00d0940740780d107001e0010006a030866640c101c1a2207800d0300c10010445102403003105049604110a1a02c80d1000400c0c80240c02410340e0f252098220085c41194000d9808200c3c036810210242c0e601d035103500814a404100385004000180748940d040f440c4030003e010703a400c1c4225660b17022040d4000300030011580b010218100c140021520420901c10184bd640c40420400c00201030034511075506000cdc = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 41352055 1250 41350805 41350823
    0x91e040c080a0b0a0b010f050708030901090c060f03060b090f2b0c210b160203070609030918020406050d09050f07080c0a090b0609010e011101090b0a06060206090604 73
    0x9024001a2059140103010300000d449030440189401d018004003100c65414491808190140755440340403440c0244459444542c03600c010b0380c80f08044e46d00000c1400d00a592640316210004118072414030080929403a8613044c400c08880140996420b40c00401c04040240040c1c0b82c02c0c2d98600c01c8500301d0b035054401e0422070041d4883c4160101d8a22000c01d91510811000c80821202c011030408841d10000c02e1036a500111035211003100c3d8560000e0140c0610340c0124848421704c001050341140580104c1c2e25041c01541c0e41720070340d24019010340100d80809000c00801d959204020100700c4501070851810b41000c00207040c0e80512540940c03041d03072f11070305e20007040410440303c604018610202c6145a0f91a4070722560b400600c07a07494050302a0020001d10103030f40d4080d04c850130400824050424150800450740c0c4251550514100014441e140e0915032080c030522050500540c00302c1240c0c0303402c010000603107649901c0007085600075805c2208000c3c0219640d90080da01003606 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 41353305 1250 41352055 41352061
    0x9030a050a0903080c0a0b0105010809150702240105090105030a03090b0d020702061b0c010e150a1e020705031204030519020f12161409010308030405030412061a091e 73
    0x221802c00282d08001c04500c40000d9004e103071080018240c02191051300d540303005a07200c40044801d0503058480c40705580c042a001510044003d11a5a02ca142c610460f4005807582003071101082c2c040fa40d040342c0300e0540c401070100e03061240455000d0041078005140b041500c1e07500401c4a80070344a0383c4128000804c480c0b08840e4a038044607281a00200800d4560000000403000d81e01801100340081c0300740c01443c901b0754001c1108070a101e10043c80c0c0702d4100034602c03030050294800602c00e000c010311000300075803040703005104042c104001e60051001c0d078140307810b06180160401003014031581c1417000b080001c82c005592809085002c3d030300e96040c41c0600c08a000140144c0140358007a0040b5040c80d800040015800000345584a55984a0341e4403104c1440e40d218214902750001807210041c00882c1d039010042d50454490b0341120701d41591421038085041c032214084580c66258000e20301c1c1c0741280000600c44100890b00300202d4140078190440c0400c489040c3c403122502c0c1000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 41354555 1250 41353305 41353307
    0x702030406020318040b1e0901050a081005130b070f0210090c23030106080a021503060303121806040c03021003050c0405010c02060705010c050318061302130b03120307030b01020609030a050a 84
    0x6c5100d0b100d000c3c144202640c000701d0565035102040c61500d02540301080001043c0c034111040200311444100907111000c0d11850740301c007604d4000c1034603070307107030828034440700054066004207210392525512040010798590000307080c8003a1150000100d810504c203030303010948225070a812500282c0002240140c0058031003050542011199495407804400250504020a41d030b040b0510840d254501105c0c3c100c08441580001d4039000d400d6070041c840050040d104401103034014000a084240140c0285403c929121080b902201c2d004e1750348408104600308804200e4608002e418180120718241c440301d120b5005c0c0b4803440341000041c0c0001c2c000e540352131040310031540c2c10034000c0c003940309800ca01628650040d160b280310f070402192007044202d0042940350190519016000100301182c0800161900404449952130f03600c146401c41c5503010012101e0203101900764a8991034050405011100c642059a040d50051010410001c00120884401c0c1140d40bc10720340b9607980e000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 41355805 1250 41354555 41354561
    0xb03160c1e0c050102010b040e0c04150f030305041703030601020604020f0d06050a0209031207030914060d1b0206010f03050303011701020408060405010207060c03020708070b1503010c05030f070203040602031804 93
    0x81c4481405580c51a00060040d89100780e030030380701c003030b00280640d8050390103020441e084001000455040958684010f1030590012610225043e10307540c20319840c0c110300d0390007040e60f900460226070b00280820040b4042d003000c00340781d01ca40002d903095291000c0081e482d100c004000230303c40d904030040054650743d525020703031a031030300203804010794501030390741300020f522850f025803081c81050100c1c4451290740048580c500d40c076036a2b480d061440d008546a00c10500f64206034407001c1031119504200f100d2062030045032462510750306081d0601d8002e030070030740d043e00b0620820b40c0c880010300101d0320000c126030445602c0c0a0124501c590810342c58024055034000f843d8030702400060006000054015004090180d44200503440071014150b040340f00e0741e60010f001c8001840305034042250100110b40c032010500c9910141030f003001c00a401c5640d52030f100b0b40882c9010080c800030100c8a00495481b0120780000d43c41e103070520070065524000c4c504035090000c3c4251244510703895a170 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 41357055 1250 41355805 41355833
    0x6050a020d02070303050603070e0103051b1516020a080c060403081612080f090c0f04180203070603091b050d0209090708070608041a07120209012c09010b03160c 71
    0x507030440d1500e84903e40240602000e41d035192207841402030114680c25000035250413280e11000601010145c169021046a030103a405d941c495004061010794000380c40c0105840c94009122a03040700107407040044203035854020700119804400000328584801045505580d00134076201e031034504603c401c000441080400606200600840402164000e01c8080c0a840c2020102e00640c1d690051a55136140300c01d90780f64840c6d480070b506141810250721860681140f00300c3c12031807155a80109140140a9105400095a901882d0240b10b840101c1e03041c0341c4803200302c16122900c1d000010300042d010070b00280c4107241e00e8000c90030760001009140010500c010507241c0135940c0e4038000e848100101c4003903032060f80030800420141c9102501e40d00c40c6172036499501ca030b078401402c4140250883c02d07003c1e06220ba81010701c0741030140c0400680140100030702015000ca0508144100030350103900030501d400c800c2c424001c0e60303140815000240c0e6400d1409041303038091401c101e50000014 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 41358305 1250 41357055 41357077
    0x2010525050d020303070206070c0f080c0f1b010905010203130902030606040e160e040b031f02130810150b030a090305120f060f0607020d1202070302030312040507050d080706050a02 80
    0xc10b0b0720020b001e4020014610900c070540039500e10f666070040c103840700441d08800038061403800030b11000184140b0007030404282d0100858502483c0d1200051603c210200022120280206e42d55130b15a80310b030005c0d02030042840903604002c182280d003003242026001d4520302c0340d0044001001500c070001903900a05021515400b90304249603102900c1582c808030500107410040c2c0c0310b04606060040c507000c0c10000d002010480106403481400160400c448848683c00304058500f0000e2514050081d01c41a80600122562811000c1c103c41410281c003c80303041ca02d00802c80c00c907814066a07440001007101090080c3c9034a01190300340308004d9880d0402d6606810700c54030040c0c0d11f002031b120f040103603101591903c109080041034040c08174001d40c07200400d44c4440c002981c0000c01c000d0311440780101c400c00e64913540040d0450b004064958500c2a940d0100414000104601c00c0103040940d0218060b03151603c820900b40b0555601900c0151914041000c10406604980381c048503 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 41359555 1250 41358305 41358313
    0xf06061c05070c0503071104050c03040b070f020c0a030309050a08060c03040f0302071d0405011a0f060d1d030703080c070c03080921010204030c081605090c0706050103060f050a06030201052505 85
    0x407d142c074104600c09550701500492500002803580e4401e40c0450b070045801005040c041e0380c80d00012070340110400700010850145142e42c1c43c4d1a2a0008a1b001951007604c6092a10b4144001c0c01242c0c80e840c1e00c000415404042031014008180e81201c1d00310740c10200d40040c0244500b0142e11b06031590740042c202800800c00c0d0072190001c080014005c81c402c1000740811800c1880d405500000101c0c21f960051904580c2400b40c034126005000d00d502c013040208030300d0310788010842c51410b402c07284401034200049100425600150b05c95111500c04400340c02e0003010b8403488189025404004c03c10a00003c10015580d501c0b140c5042641c045840f81c81014043c0c0c604a0103500144002c40740000840000f00c2d230b08a002ca12000325403100c060070800d4500d01000c00003029406000000101002c0041c000448c4030b42c082d090295015040115600b41001a00011180c00034032207002d15140203410f1006030780c000304545940c0700801d244450220012001032000046600003840d03445 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 41360805 1250 41359555 41359567
    0x501060e19030803071115070203090f030705040c0309020102100501080304030b07020c0a030302010e0d0203160f080c1005041416090b1203070c0305010c110a0303050a02160b0f06061c05070c0503 86
    0xa4481b090b00402e24032030054036502507610360394034140d00080d107031400946c10031b120610490504805008081c02c00504582c015640d03000070030102c4034020303440b6000030348800140c3e040d5601000b00c1000110120b000300403a40c54814260b07240d014070b0100070300000040010610840c402c0001c122461001800b03030040aa0305d2030042e009000c40881c2c55800e000c0c0740300619450740003100303441d1002c2e110000540880c0d007a54800c40c05d50400401110f042105002074604030724208507240314030100880c0000d0720b0501e8104031580c0e0490b82600c0100343d205031a0740320701d13800440e203020440307801070004102901c0b03110000d4001034210f03280e220710b4031010810905000c2413107101030407240580001c0010320f130703c120116440d00d08111307000200e80c0134940f01c800292290f40a03d5000d100381d8001030800340a00301d88202514042e0099036024110001d002000b0a03145142d44c12042c1126081d191101c480d141c0a4001503425070141d4541c3c0c0d41d4001000503004513841d002c0b0341da2100a030b0303503108 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 41362055 1250 41360805 41360807
    0x7140702032b050a08011404060803030103030306091506020d0f02120a021b030a0201092c0c0c070608102919020d0f050702060706090c0902041403010501060e1903080307 75
    0x440c032100c0341c1542000b0b16000b81d006070051044846030a0f40d5920440b05a003403031040d00c038501d840980345400aa42e008000b450b0700007800590b020390700c00d6034003103181482d00344201c0907900d0140c6401d0b09400c20100401025400040c0542d0300758482c2000301030040042002e03410008817a00c0144d607400005210b0904a6000c00c104480052059500500550720070034183d5500015000902003014440d080c452001d4000705800d824182180d42180c02483c43c0050740203200c2074031519480480030440c2d00d40341d4802e10804010748241d03d022101440e14041c1c0c0394040302c541c8a50340d0002240304a5406580c0b82208200c0349e02da0a000c90766440c00e03001018120341e08228a194014042e25928008081c0700b81e190682030100c55860600785600380d0204442c07940020300840f542c41d43c414042c0b000070754080e80303d4024101e0140060701c50303160036444040c42d02010704191085e403610b0014004c240c1c2200d1044020340301a0349485a100c0301c0c40c100d44940c802c40d08081c002e1003010003008112 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 41363305 1250 41362055 41362093
    0x320030705070308150d080f16030507060f0b130209060c0a03090501021e0a080313051002210f0c030408070602072d0c09230103061406030607080714070203 69
    0xa18401c2e503030010241c2e140c44c034800b29003402d10001a440346d0348290b6078010600e281c01400c035210044d54250b141c0598600700d8610440d800008070f02280000c01e00205024462050081d20300b41c169003480300580c43c000180c1100507120844403110350206007014151201406c0d14120084e210850307003081c25030304000d00000304c0d5100c1c2d00c1c01442000d42c4507005403165408024140d805c40000c00414230180d65014154000625040080680f01c100d24007181d010403011865821351980140d4540310010b0701c0d005c0070740c1031f04804940317018081031240c58503107a51440c0d40100381c480060703225240e0789040401407040381c40180c1440d00100b865018009481005945000c1c02500031044541019091014941040004e80303c225400d070104100c805907048a9005003a00c046202000e08012456920110a0b0000e5480740d9076103456603030080c00180c0e19600308000b04e0040495240c00000284817080c014240c800700040046262201d04201c01580c0c20310390b00405803401050b100c0840074503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 41364555 1250 41363305 41363317
    0x3100905090a03080c0a0c051501080607020304030c0e0702150c0415080c09090601110313050405060609030d0c0204060308030f270703170706021909060203190320030705 75
    0x200e14100104030030305400901c040c00c460b855214854640d582480c82001608000d6640702800070812491000036002d2040d05025040030110a1040d41000840c601d4074400412442c29036000700010310115039070120010446050808207035007651220401c034208100849202101200b002c2403250f8441c0d403d000d00140c824200340725804019a610861300b060040c0c07102a100181004031f0b0740181003880000350b2180b810f041542c075166519205500d1a8407281310a80d500240d82c000707000c03030319050040300e40041e821204142028000e400203519410300860030400c0c080c000403600110344542d0440c0000315082035145490b4a000c2d80c41d42030079071049640c0c4a01d02c0c440300b07500307501c1200d808000b0120301d403441c0100112811950f480c0c048004540d0b44554242c01480184001404c500040034500111700100044c103804520251540815400640170354006100d62141c104c0d06001d1000104114940400c00380049064445001010f4140c1001e001c03000040150040c0c000c001021 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 41365805 1250 41364555 41364569
    0x60c2a060c030215010501120903030905030a020304090b06030702031b0a1506150306030b13060b27070c03050906031905010b18120303010b0714060f060a0803030601020a031b080310 80
    0x602c0004c0a5000001554240980e5020402c20940e2824807400355009408080c0700e8100020140d030715443c1d592940d0050164640180e0000405001c1c0400700e0203010348440c410342d2080d05600b00800c0182d1a80210030400940ca0b03042c5519403405034080015800407a0016010288451800c00c2200500180e025400006d01c0c0b1420050b01a031182c401d03001140e4200c403601ea40c82d01c81d00c5144840e5000441c1c10380312a5101d180c446200c2e0740754034401e100c1010803c80c0d0351a440131040812030b0f00e50700070015001d201c01c1d140c107230011942040c00c584000404480300703543d0b9030b02c0d00044002c03032022010310620b480c5064008907842591000400c074055400d10050001104402042100304d050083d1010b2034000b840104410340c3c016000d81a0540310301000442504040d1402c0d103080000c03620b00c054210342100f804000d042046040000d040313101c0195185143c03080c0040e660380c1c00000028104111601c0c076101c24110141e03a40b40302640080314035900d003030250340c00b88a00682d0140d44 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 41366911 1106 41365805 41365813
    0x110c040e06070e100e0d02060f0a020d08090703020a030204090c0302130501141818030c07120219060c03030203040c0905010602030a09050307060c2a060c0302 70
    0x12040044003008228030324026900a007020400080719000e0500e512011004039440940d110502c0c2043d0381c24000f100340c40c400300d161885416001d4440000118091a0860b0301064004504407a603564281540b104000c5070340f18001444000d50180c5aa0030030401030425400c5154900c3c01a0038240c00c9641c1d0750003003900e090340702c021108a295240010300046081c1c501111034400c003600c403910200b214030400240d503180601001c2092000e01e80407514003004200722801c400b406025a0314103071380ca80a1420351802c4d00022882501c002c90782e12040c00106407080301319491a079803a0000d00a5460640080d480a03100381c44181030b03860080b404400c42c2c0a000c2c024000b40e4000c2d9525203441200030418015600301ca442a0404a410031110783d000120001050304152101c0b100201030404409050050011210084c0c040c400000c0340d541201c1c081c0c8600307020741c0980b = true := by decide +kernel

theorem cover : BRFrame.Cov 41187055 41366911 := by
  have h0 := BRFrame.cov_init 41187055
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 41187055 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 41187055 ≤ n) (h2 : n < 41366911) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
