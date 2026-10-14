-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0193
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:22:39.883113+00:00
-- url     : https://prove2.me/submissions/8e3eeba7-0e18-4860-a658-8a45ccdcc509

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 34532379 ≤ n < 34712235 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 34533629 1250 34532379 34532387
    0x9040f14090a081803030408030a020303090706050a050904050c0904090c08010e010606201507081506090102070303080916080a0c0609060e1909020d0209090c04030b0615040503030f0c0d 82
    0xb0040b5030002d85a0f2600c034500b1450200751814103206581800208000a004001040100340700c1007503801850712490301c04541c50402c102c0764040e0701800002c22a10030700b16405411140c50344011a000120381c0c84000c0c100c1c3c15401800141d80e0001d00d842c01e20028401110100f1085070b04080003030280b00303000c0e0402c6003aa80c15104800118688030b047d03492603100e8940004030403c8201c1107907070440c10112440304c0050151922000305800506103c0c2c07140301d144400c0d21611094030307407a01d40504d80700000d54403425488083d04212100307022514500b0240720b16001c3c3e18041d0a0000b00d10b4480c2d040c40d454400c03a102c100c6400300e0f114000985039028030301c008204c41048d00d43c0070030789604400348514643d00303410000c0034000385c07034000c2881c802070f202520341503035640030040c1c650b42018140000044040d2546c1c9185400b4401000000c900c072104aa03c0b150650300e01440c144c6e84413200c0500d000e242c000350362602004c00e0252291004201401c84a02c1c800c0840301204407001c0e040d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 34534879 1250 34533629 34533643
    0x70506060f060909070311070b010e06010c050c010f020f0307080a08090705030d1103090a1502010c031a040902130c0c060507110c010509010e0d0b0f0903031302040b0609040f1409 79
    0x580080d030603c0b07249802e01d40307a9030030396205016050200b00030014002c41031090340840700c1201e074140500010300071080309004880c1d0001d000e0034088524240f40c0c4510b81e81c0c24403010030604000310203080c5000e07a4402e0101c074560b0f0070048105da4407401a803070f040e01a07400100050380041c480340002212100c000030a481142d00c007030302502d4410034800301101c410034114070602c240e1004110403d001c2c0c581d001c0c01401030011090000b03500c44001d00081c20340e607484105208142c2451a101c41200c190441202e00d024100c4c7c0001e031940312032010481d684549080720401d81d180104916041d0380200a1010680c03003507100300800d94a01c00305407450555241e10414651240c0c001e0f035450b5000d48010468250b050500010b500d1086001920300c900b0788808403940440c2e441480a02d01035040c1031900b20030b00074040c60642c9018510401010360000002c3d11890300d403480c0250390780b189412103074912000b030818802c00703d007480a41c0c050287c24080540600c00034001414000c4081040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 34536129 1250 34534879 34534909
    0x100b0a060503010320030607080f070f09180608070e0601020106060503070507060b0406090905030c0c010c020319082503020c010f0c02060d0e0303040c030c0b07171b010204080307050606 82
    0xd6801c0d41d013152a42c010045848800c0c80e03e05405100c012150380e01004000d102d60003544c4c8000c104c3c540f0a6030305a82e030070040c08450070310208540c80c868050b00b01030800150392640c0d0800120f10f454100c1b14014241b42ea2103036000e40030303980e0080f543c0c0500ba0042407080c10207800a202581e40c40e03104503100d01c012190340c400a50280440d42c0011000c1d0440185008010030100346140c8402d55401150381070b010031203480d4000102004640410b20081c4e5030300809003040c3c48040082e8012984403101c0704280c16110403c040450100301150b801c1e83c46503503005100b0b94510b81302c0d204003031030b070312201800b03070050b00c50980103401c00d41c0308030300e00d048a01056403034150030034096007031019640214400110142d29031084514855081010314402e50240403c100c0082c40c41c03c2520350010550465600c0b800f04000040210b030181c65040141044000455036407600c0d80c103281d1010203201e2203081e181d4000100013501c0e64000010705411402817060f13580c503032168802c00c013001044c0226 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 34537379 1250 34536129 34536137
    0xc0d092108010e180a0203030a0201020406090f0e06060c1c0905040f06140607081603080105120303090303060603041b080f07081f110f030c07030f0e03060f071709100b0a06 76
    0x10318002c05007130301169102c40c00002c88492110650010f41141c00c07013120040140e5004c1403c104040d400007003400144458206059541c1c1070000016100100400c00c0c0d0162000081e8032025403420001c484540c0361842a1050b100d08400c00208150340700d00c10184950b0070002d20300b08c0741c081c42c85400225544407010360201305058060040070b4004400544800c1c00c240301400b4030811b100c01d450345d8103109546450056042c501000750003500100404215417003030040200c00c64001003202e401000c100c680d15207076030310f41c540b400d20745444100c0d131000c3c0d510b1040c0c009104240010307c198484005001c1d221819150241e542c3d950646080814601c030440e10000b001c24900d80c8003079140101982403510f00703607001c1203600f680e510544040e21810b038001b41a400b411350001c6c6051460301c040c50007004001c0d98000180d6255800341030341414266545c04201014007481c812123500300440449106403074540c184a860744108610f0038441410584054810300c3c10007808000e0780c0c1c20b61070f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 34538629 1250 34537379 34537381
    0xb0414070c140114090601031202060c030112020a0b0a0807020d1704060203040302010b10050c011104060815011b0c030b0708060a140d2003010b1c0b0c0d092108010e 73
    0x85001030b200829056100c25580c3e9025603080f180354829540c4034030106802440386525510f45403012080124082d000c64204d4410b21002078141c00450341118050800c4401c000594000120104a1980100c1c081040010510103183e003082105101351559000d50b00c050644080585030840f6505100e000c003102e201c00140082d16540c09590414000d200000c2c0a817511008120b481b401a8070103004640d010641140007982401546001d000c114a0b01e800e0501e0610060034190016001c0502c0d4040455803940503445840344180703020710560400b07100003a07070130500f030742c80c441c0c1c08140c514118250025000c940149142030040d00007501c4040460320b0095102184402c0d0389545a115001090310004a4808440c2010080c8250070070400c02d0003d10030542190111410207001d442840111112820304240400a0340d4104886e4a040d5071000d1800d030007441224840a81c0529110040d4184000c03149115040c0d02c0c03850744c1030780705002c04c181518409000d22510340e080582e08 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 34539879 1250 34538629 34538633
    0x120f0c01080a0b0301090b01090507050906070f0327080708010b1807020f060f07120b0f060901050f07060501030c0905090601050d080903010e030a020c1e01080402011803060b0414070c 81
    0xa40c001d90302240b4000c000414202903000030f03003956540a400d58440b0a40401402a05414030690380c20144d14205245406458004200d0034000c081015001c40c0d4000d030154203060103040b0000b041a19005584100c105d594094104003107a80244600c078403402034081022541442020741040d40100541461114103a0050000d1001413520b42180242c6502c00348070750b000c1050780d010349650211800b141c45c1c0858001c0c505c0d5070980300490600d0403c1506200c0361510b00800204890a9481950318140307900140c0d864456181e01003072070035000454900384055a44441c1c140d921606600c1d8580d41d0780c050000590f0302c183c0760b0004c984c00c120300421580c500038014401980c4034091030360070160140002421602e003036405031080d80000500d030034041d1707051203c50000081126004123003080785c4855880f00590100441c1406008804201560300600d401c2000c03804000c40000750b07503101d00c1c00e400034188031101e80340201e04110400d00c4104a600003e0311a046507614125011125 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 34541129 1250 34539879 34539887
    0x307030605040b130504150207060203040b1303090b030702030c03040f0819111306030503180922061503120e01020c06070209070e130204060908060c040312050904020f0d0b120f0c01 80
    0x544100d0b240301c0f98040d51f4080d04514006000c0c054010040182c1b00e15003400c100000920050200041000c1c140c00c400010340c000b03070002c080d40e080c0f01d401900d81d52030754010384c610b00c20b41c408124184000b01d80003564070340400003041070300d0041040d961500c038602a0700003050b070f051800600000f203151a2419508050f00c14050380400032202040881d81d036143c1d1f9042d82c0c894908440c40710b01160440c1410300300341c05102e4120411100310850301c10010101c4407000a1030000030705003500e48410440d0303ea644151031000c0e60b040030b10501d03118005400500300000990846000d070240088e444c0c801d1400d00e0690b4201600a000c0c90202c0c4d41d03040e000c860315040500c00c2540b224203030507600448502440500040c01182e2502c860150030b200a251030450010038039800c42c4030401003030001800c41d89900d4540d203500d040442d01c81c03000340009400fa00900d2100a2410b0010502a260362500e4005050881e1b040d62124001e09210b20b07060303210740c1c3c0300d489000982c1c4007140109040d403103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 34542379 1250 34541129 34541131
    0xc03020408061306090c09050f0601020601050d0813030c0b07050d050f040302090601090e090c030c0303031e07090902070c05040516091202010905120703050d170711010912050307030605040b1305 86
    0x4c40c13180055410111364424541e80820340158070415510381c01c220340003041c1e041e4143c00c080c0c240000d240941c50312002030420603942c50b005014850220b4004040c441135a04c2401441d807000041018640301c60074503c1d0358020040a540602c550490117140074010b1003119021141600210b00d01800c54003030014815003d448581089021b200000c0c42d6a070520603540150646406030251154030802c140c03a0240d14801d83c2e01c00d0f00108180046c40104440c100200101c003015400e072951084400d891600e410f40c41380040a00001750306080280016000b426206c4c100c80412a42d150040880c420003810f404034008114802c1003401600385607140318148030f10514280c0919a22400450007a1320b40c034002d8101503101100610400c602400003454a00316894111241c98816840541c1e842d4050301ea0300610840c0c1c107280c241680203400c08120326422003101c0740c50040e00360006189500c00c4480e00c0019162010100d860310305405214011740f8018800004030410b44621402010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 34543629 1250 34542379 34542383
    0x90a060501020706032d02090109080705060d0c0903140622030f080a091b0f0b0c0c010507022d0a090e0303012d03050a0606050a060f0309080417060603010c030204080613 75
    0x41024801b10170740240c04d4007000c02c14051180582c80e04034543c00544030040d107400206094000c510140300941300d2205490405080c400045080300d41c2410507201c02c455600040c1c68800314018054031440300083c0c5174000c0e0118503a00e0100355000d01094040044d0760350050000344a02d0440030600e2090851a410000c80340340000ca00310b441e0340c3c00c15602c0d4204c405140c10003042400300030f1460000075103c0281840250185000c054200c865210308482c400c1d42d0500401080003029511200b091180b07848080620954841960030f0124407254415500c030310490b00345101103039040b45801034440b4800a40d000350308590900408c2c194041c4000b03940c17411101082100c8400d07854034881d203001140206c001d012550707110b040580a40700d254200030f004002004040141d640c0c0060340c080c00400602d8001032241c2d00c2c0c5031666030391095a0000900318039000e010b2550743c4e400300c0c4980c00340740103d0080180314100700c025002e0303004a205040351034128200042c03a0302491140802058 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 34544879 1250 34543629 34543661
    0xf03050402121e0106050303030106051204060b06040e0603060c0a091418010e01080c0a06050a0807200d0e0a03110d05030409060e04060b01020a020603060103020904090c14090a06050102070603 85
    0x1650500741c43c02600c2158003039504410744000f040c040f020700c1044e0107403070158051480c0d981031942c00391151040300344480001180100040074041194420710f00c0c01d10080c01c1c190784540c0d42254421000341505d9040c801d010302c90103c0c1028074048101d13000403000340c481c4540c05150072220420603648102960b000b401540d4001414080080154083d00304070002520950620f0807035407600003c2c0d90054010fa4107030100340700c0e0761b40000076140d8030109481d02c210f86035204142180e0800d14007102c5000401140e0400411a4003c82d40c4981038546039112072600c0741c4441000354241d2103100142000041404c82d030b8990501c000707020a424080c4045034941513450040c0001c8900951041500c02070070014081082100e01500e04203440902c0281403070368141e00041c0300381c4000f51096050550008040403961125000200d02c2508080c1440e600c5685103011601e050740c00c4846e40c8a02b54580c005021070005104200a0300c1043c1d00600344070f4117022041d8020300101e40f03909005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 34546129 1250 34544879 34544899
    0x30e0409020f122508060705040303021b040b044203060e0a0b130b0c030403120b03010f0207050106030b01080f060103060f020c0115030201020106060203040605030c0703090819020f0f010f03050402 87
    0x400e01d02c81801c40004c5080501c8200710340703070048182c00d182000e03001c00c0401100b048100046580051030116030040115002000354482001800500f01480540e8002d401c03e14007070f0740aa141090044ca0010000e41d5040c91116104450030000c2c100c01004805908182c041c070118946500009501003c60100d481d8210f00780c07a2580796127021200340f010040c000440c5000c20420112003504184403103569411410956405000d000034110b81c43c0005983c0c04014241c0e960035042484a42c8440030219654000780c1445400703020507002c161a40e00b060000090b12510000344603e0140700c0b40054040d81e400e540c0c07880d01400850040d484901e800b0300000501d140d082c03061302c42c0c1010701c00c0703284030152540c40007900f90303401c0d58401425904184010083c2582160440340c0c8280803504180e501c1c080c601c1c0984410446811205451244000c0c1d0300c401400001c0c1d0703207961390080302d600356100100c00c108142d0140c10001c0714000349180c10407041e030ba40240c10a507040307440148041c0c0300c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 34547379 1250 34546129 34546153
    0xf090c0b0903070e1f090b060702220f0203010e0601020c01020727051302040c030507020d11010921030f0501050d0f0501090803070f080f040203070b0304031103030c07030e0409020f12 81
    0x910340b0300b80c0b80e41d007500c0c0f200341e5180e0005c00c120145a00130b018074401400402d00c00301c0026640d0041540c060300500d003c6e240031780c45500e681c00d0440b02d01c248000c00c1201803030683c21000250001d0181f030306c2c924500d10108059600000300c0c20344119050f4001c020342d070300340249911141e01c83c10038a481c4440340d807040c5031449a9401440c0c45620303070b1501d45100499900400c0190341d11314281c075061511340300c01e0114159021900361020042403c160500359a0400720070300400c2d42c1a0080c0002d4142600001821340001c50682c980d002e5030303014407401c0708000c19041150003e08c503299108041c0d0084900141c240e003110344e0158020000020000326507158001150b004940007000282c0b00c11391505201e8020b80d04d01d0300206c207441e0a4045103425808296036461034003c0d40ca0882000c00042d040501c15090401c1010740401600c4c0c4a04203002e000b04980c002000c2140810019118621a41007034490401c40a80090421144084450500071190f080d018420058002c803416145 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 34548629 1250 34547379 34547399
    0x90b03121b16032004090b13030507020303070303050118050106091202120604080301171b150d090b070816091a090303130e101508060f1201050a0f090c0b090307 71
    0x710301071001c1248450303214100d401d405104c0da00c2244203515103241440403e22540d1100da00282a20103070b0780912007030a080e038590040c608000d6042c8400250300c0100750389904010b0403100c01040c104015081200103800b076032802d018890005809110800c140d80302d511700200710700d0000d0101c0901c065008005803c2c00030845041e0341403100000104022610320800d0b54070025508060103291084c50b00383c500c40c901c501100c500c64160500100820900041101c1107800c203c402000003103c2c80c0f500300245007007100d82d500030946590000718600710800809020503800d43e194044c141c100110840310702c40700c03e4996011401846a41c1081d24100020031031240760258601d0903515101d1a2131201100800c035000d14801600100402d40d44500c0100c40c42407103050182e090758a071004115030066214182e44d100600101444074000d0640c003403402828420003d010410521784410103585411000502211a9000812212030030002400d000713078005080d100c0e02583c540c1030710 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 34549879 1250 34548629 34548673
    0x302040e0705030c040c17070e0a06120b0a03050c10090b0f04030c05060f1b100c0f020106051507020d05010605150c0c090f06060a02010608011104090b03121b 70
    0x10166209070014802c510b400c1014016100003258184000400340c2030040421540f025500f480d1901c0c1b502094006010300400c405881005d02064800da545d40e800030710740540011902403a5180070000241c80c10001401010740b5003240041811103002c1050000d07940e05508103400700310300e10902003000306400c4014500000c5040c0d03020b4aa40c1503081a0000004c0e07503101500c50801004414914102d107016580c5204502c48184642e1007025649030510f540090a600c1180c94110305003a01ca822449007480000c069000704003040d180e90500c610281c001840c07003800e090600541005180800781c2802144c8608000300308141c0d90804030b40405080c19809042c118081196401228100f110300c0d809031007120012454200001d40c01807449000e41172500441c00000c3c3e0028640c003d400560080c451030001700a04c2080d00d5440080d43c0040c081c0b11005410114100054a0300003517100c13030352180562003450702044d4622051079074040c440301c0e0030314011540940a0f40c5c1d0208118 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 34551129 1250 34549879 34549901
    0x60d060e0a03140309060708090109020901060f03051005010e210d0203040e09060f010b18090703020306180118020a020f0d020123090c1318050f01050108030a02061f030204 76
    0x6000072806490701a10f6454404040c2911a01c00c0c410010402070016059410401a0820800980f50702140c107015042030f000280d003050b0880000160540c4c08142d203411086580d6080181e5129101d0010b21003500f482090b0000c3c400383c81795041454504448a4200301e074502c49020039030100000341c100f40031002c1c0c6001503040454100529a408001d05900c1401c040142482c0d180900412801010600a60788460804603a815038449034450b003412540008200d14240d14040400501035401110858005c0c40c0e000c8100d8204454041202d058602179a101c9140c865110f861400a4004581c031408500c501c6100011080c4280308403c01c000e0035600100e11900306080071480c0f9143c4001404808886000300094140007244c0c1e42e0f00340f070b82210144001f000103404040900b24104c00c604100d001200280100300300002c4c1c1000c03115101c002880103030703030300d02d000f9407280500030799440560003a500043d02c00120400364414040c0a80d0003203295902c83c2c001c50300302c130740b84400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 34552379 1250 34551129 34551133
    0x6060901031e020a0f110a0809010c050f1609090503030a0e0115030f03030c0804111005040b04060c020a0f05130203040201020114040501020a02070b090a230301090b0f010504140f060d060e 83
    0x4d40340343c00c0da02c840501414170160500e1544444513080040d0350341d91071480901103807400b240e0070115a1192500080c1e0035040001c032040c40c5081104151103201c401580f601000c5003003400030382075810303003d894240c1d038100000d1411640c900e86190701414008010a12035540c603100304071440c40b43d12180d40698001d90b8000c0c02d288061901400b203c5010b0b0190090003140800c000004518a0903201a5401690302c1c110a031015003040d11503000d1600016080032000c0383c04181c169101040709603540c02103501d0030710f1075a101d07465140c081e844d018041c0c2084040700135211180701d0f0707001541c1080c030610001480818030528050303015000e450443d51a5000954600394a0341081036501410407111958078050442d400510042071314803d036540d591a44a1044c6413113402442e1020a4001900900c02c3d19030303900d40718080344030803a03105440c109404004105420144a80a0001040f41c5017202c00e840da1441e138802c15000520310359000c0b0561004a0002c1d1490043c4100e80941d000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 34553629 1250 34552379 34552387
    0x70203040b0d060803042706050f040f060305060118060e060306010519030203011404120305071d01020a02060d0c080a020f04050607080706060807061101020c060f060109120c090f09050606060901031e02 89
    0x4503001fa150441000201c00e07814000103002665440485034a120b40031074000906299401059010b0b040c0c5610190250080c0c00c0005111021914400c280d501820820018240c48030b0000340254415a18076415a000c100140f042e4209000d40308040641d05901c112456501d90000342900c084c112410207a0042d0f4003400200701c4004103030b168120b16401e00748003e00c0c19840080100040d118000400c2e0b0702607500680c1d6034000e121034103001d50040d181070340c0c1d500c8a10118000d000600500000207101200082c807070802e44c401d07036102e042141c01032403410707190008005864000c24419219802c0130080080042c641d40319400c0141508009003034164902a4090115050758440e4031850b401000690240b0001041c4540c1c000c004d020403140544a41c030040344c1003400b68020304a003c0d00c200d50001840701e01002401284c044030f0040c032a403202e14078828150740c91004001e2650b800306010920900d810002b9217103510303040c540000c0d07110072948840d9810405418140c0501e500007 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 34554879 1250 34553629 34553669
    0x307080d0207021c0b07031d07030f0b1006020a0314041e050111070f0905130503031f050d05030711060f04060801030209010902160305030702010b06040602011b0305070203040b0d06080304 83
    0x40150300c0d0349a00d5843d543d240051138885e002100c02c010078000c200342d0746011200b008a0f018100c40c0d1176450301412202400d44a10703100000030300d8100d00380c07000c141040014080b418680300c0403050b0b0f2a164050541003402c0c0d942564405034440649281d40c0d020710003c1030409992188140c0d801140d0000001e07149000c0c0090500c0000302c1d481e610075002100c051049c5000144001d041714110a400070347c0e0780d01c940340031010342c054a00003001404008180040c0e1000480344d040c21401141c01c11005ca607950301000310803403000c0d00084c00d5030010300003840071408241d00101c0d08100502550f1400400e10310a40c195445038010f00d010550034401482542003d0000074003415040e0301c214540220054980e01d19000d00340001d003007113000400242224030030340211030200806401075407920f84500b8081d010700b00a4080f400442e400c107441c4850705100c2c0c000c3c14065031290f0050352600d41440340d86009540a02030803461952110300000d440c01c0c04100520007803030144c6031000810080 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 34556129 1250 34554879 34554889
    0xd020d030e01081b07030c020f0306040804080705040b1008180319110a030512090a08030411011d010905010c0302070503061e0c09100806040912051b031206060c0307080d020702 78
    0x1901300b120074060801c0e96056880d4070011a484a501804d04c0c03814581c00c3e10004101c007020014444d014055441884104454a0050825549003000b5190303070300d84800621080391030095440d540180300161075915140203030070720703904003400100c074160040205a00c0742c07640e80a0640c20410b00c1d0740304400303013046502c86600d0440380d1440c0f020f070014001d1520300801f50300512180d40030446c016408990075540800481307080701e40c8104030586a180600704160303000c40c03030600766010a01c00400c02c007410746040b10140c40480161180f26546051000445004284480880c15413080e407501181c5582c080214030f00c205000c042c0196088000030358800d80903005050321040c50b03014002e241403680c404480b8001c0f031080c0e103441c0c4116565100060041c000541000c0c0203864900c4000d801103030b000001300f42c02201c040d409040740e900d0710382c0955030344034034109022000b1201021034464944100200003046c402e404581c14045144c69440481d0f2000c0d106100722640003030040c045041c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 34557379 1250 34556129 34556131
    0x3020f010608070f03080c0f0a03051305030c0a0b160506040501060501020d091a03070302190c05070b041206050402060f0c07051f020c040902040f15030b0f01050a0e04020d020d030e0108 82
    0x300740250500c0b84c90503d02210a081c6030200500e0020046150646074004010b46180340c55400d040721900322107030901801691014015000c1500344150114041c02c00260034007001d00050000d54015140203440a101e030829116500714405a806090200c1c134200302c400d0041c0e0041c8000102680391600291a1440540f50300c0c0c14044031040c1004540480a4101582c0300c3d0361318415640d54680500b00d00038800d654040640c48480004400040e40c02954810704506c02c0c01103c55081e2200c240901a01440c0f00d40b18810810316003040020b4225044580c0040c4040c154604021190284e821660052102c07440d1075408010100800c0c40c1890003c801d06001c216000000110000c000391140240d90034240102d403074044850441d2039070b9001141120b0b249404103d0f03000b03696503a4072520b42c0b900c019030300345806038007145c07600700c60544d10b5040391002401401c40034908940745e42c6861004006a0b84182c61070b15100150316441c0644001600ca582e5041034080c0300000076100c2c0750 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 34558629 1250 34557379 34557389
    0x60b040e010e0601080c030403091505120108061003061a0a0b0d0506010e060306010c0f15020408010509070803040302010f03021309020304051b0f13020d1a030d03020909070509060c06010303020f0106 88
    0x4042c40500c4001e98002d458940c00c0080f110003107513242e4607400e042d5210846076005801c030b01d01c1d40080ba03000c994004c005d051704105901c03880c450782c4d903030b080e000380e0b01c0400b03a079501c007517030045441000040c0099005412900880802c480c5c01d00c1581c00198a040b043c3d44080004c070800100c5800b0040f040c440c0310ba11030307000d0a05500c00103218000c11040c2c0801043e030784c10300c6007035112034013402a082031300320010341c1c0700b1640d4a60414076180d03540690449e1051760240d40c20140841c440c0071000c100351060700c0604004508052468004544051010243e5800e040d800c1101d12070040b614042c04c000340000c4040561707203040615007946407151a10500d40484580211540791341d588041c2015212002c60303080c035a22801c0c1485400034070a411802c091580341090003145141c181c0c009401c11103080307040d0340741c4552100056090b44101d541c4c0c40d5101e00c5d50400942c82d90f00800c0940711407200941001d00701010204042c1c5801002c0e0010780250344080c00c4078905100901901c40500 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 34559879 1250 34558629 34558649
    0x405010909050d08100e06040b03010905010b01020f07080307031808030408070e070e1003020f12150a06080c0a0302070303110310030b0604090c1202040b030706050403030f0906120902060d060b040e01 88
    0x8a8181d1002c0700c070a80034000d00650000b510f012401c0f50740c0f190000d27105420002c00030000c4080360f2518900800700c608495000d4016000c503103001030340209000c406c0302c1c0908055032419005503411200307104102c20701c45025100350004240110100090400307080180014070160341090b0301c92840e0030000306880c0030414001d0a9501c0782d220780d86141c02154079800d0158079084003910075201e9000b940c03282481c4042d2441001842d84484002d5850301400342c0d0480207207500c0c0d4008131021a0100e8465a0f500700800440810038441c2e402407462074080d1038005000c0c0c07920074203079085030f200341c3e80c4003800e9030021401d000b44503440b80b6094010714111000c10090b40141e03149030340c1102c00e00ca80e144140030301c03030050b0075915190410101c401000f419525441d894030005050381e0000d00050380040c028920b100c207401c0c00b030ba40700c13800c0d00c00c0c13516060320080d610340e801c0001d028103000c1280c003e5000d1101040b810041e004550140400d02c80d05a102c60a04640c8020100160b1041c1419 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 34561129 1250 34559879 34559881
    0xb0103060608010627150519050a06030506030714012606010f020106060909050406090f05031908010e0610090308160227040807050f12070201120c020601061107050405010909050d08 80
    0x710181995440014a8100c0460b4605a010791b02d00c3c07101c02a40a1034004030046c943c035042e45044001e850a0310001c89800c100746468100880442e84c0440308182c040d0b005405c00e000d84514444112010741e03051501100904101c01521000c1508800f211100a101d10500a25680000c9041c400c014284000c0002c3c40c40c04400804166551048240700c41d41c400c049014001d0a4200f803c0300f03501700d05181e104014510b007803503403503100360300809107200000c04055825103d0303a940390407075080300000d000c0c0d0307100d90041000f504080d0800344d05200382181d0001c0004d41c100c002d000b0100390042005c1c040169030060241c81c0340482c0c540c5a41d1003501c404122400c0c000381544c2c1c1c02581142440340c503103c81d072420380d20380590401a1486481445207540d0074000d80c400a00180d4802e90358111460540340310001034411441c041009a0031000050280720310600b091060101c203482150855540d42c00841c00700c07002130704003079031558594484100b03106040209a848001a03c0c102150b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 34562379 1250 34561129 34561169
    0x130c080f10150e100c05070e0411130b18011404060e0f060a0f03050303180c0a030b060604030b16030e16030201030b0105040305030a08180a0807110301090b01030606080106 76
    0x2400703450180529805841d400c088540f442a040c02500000c0603021003112000c4070b0b0040c00c03c8103450801c460134403c40f4408540d115840c03103554011940108203481e03c0004200700821852860201c035841c0b82e840f03105800c25611803d010b458034600d00074580c590b504104118241214281c8007034042c4c0e0a0400801c56950098810382e0710028001d10300e5010f466200010701c1062055024001c0c08012a030701005029000c4021405400102da0710703550025421a023903112610340c03101c00e5001002d03ca08001080c50074045560000d0b00074542071400e40c0365074848418400585511558820b83c22003101001c1d018800e2004810b0620001c0021440c0c225aa004000301c90100a0405882d44860141c3c0e9004406480c095036010341500c1d04d0b2a603090000313019440441d00c0110440d00b040140c1070100d004104006c03a543c00c042d02c2c0f440d01511391503180284c040d10700b143c2d4240d1f603285001c1002c180881c00160103140700e10b0000c5545440d03c40b0440c2558055003100c1c1c0300411b03640d00030300 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 34563629 1250 34562379 34562401
    0x90506060f0a05030304080303010807050109060509130b030d0203030411010305101701140a021e031b0c0304030f03020a0b0603011103010e09100f020703030e01020403020f060711130c080f 83
    0xa40305004550000382110031402180320a00305501c410741520000c41d01041586020010b14181c4082404846030a6690b900440c0c020f4110b1196801240007044071141c14107280d15140180c0014580103d114000003000ca41760244003441403006810200500c020000c549507034110180c0c00746000c0c841d40c00e0100c03162004840502c604071b000c00449c802894207210a420100080031920f807070f4002403a0510100c0007a6005c08044103150b6680d4050b00307110700e59042581e01402a81044181c0c0c08001c1d250341032294440f9440414900c818403000001070300c8040309220103031180d40a403180180502e0514403840001d002c00303210f80d04040c041091652280140d90448401003050b40d45500c076111007a081c002d0441482d0000ca045c45c00c00039406020340c0080c42c0e01d9129981c20046001c141d01e001d4200d01841c00f00070751110789d840042c0000d04d080b0000e007a480d801104050a0811080c0c0002c0b0103800485036003001585440c18044071541100d556680f0010b50f1202002500c0c10780c400d00c2e = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 34564879 1250 34563629 34563631
    0x40b0a06050304140102030103110306071805040f0219031d030403051513020306010611070f0b31090911030c01020d26040b040c0b0a0c020904020114030f0f0109090506 74
    0xc0c100200400064280060300303500f1250302010a001715640e5031203042c948546c110081c06540079125010106038220311589020340c40886102070301c84c0042c200020803015008a080c400d20703651f0203200d01c01c14804501310a03100d400440d100001c5101100c80030504a68401c21035a00311b800901c41000401d401081c1d404a010704142c02407215907401c0070502c0032070b818440c0030b50144144000864a560001c04500614a461048841d40d5070380e4220303054014818042c040301c50700203124054aa03400c01740107045160210300304580d8103135100c2183d011429907503c02518a600c2e441c3d01d4051205200414804a0041c2c000d000102d19850010b541d400c03d0020400802c02903600700d4004a00400d80250b17018aa51100f200508060070454000e040c15142540d91145003400061202c1c40e60007103443d41034847c0c43d88451246c00740c007045001203005206a05000704000e46803219800100118810200004541690305084480f64450741c4160401e583c01c501d001c6030040814000128a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 34566129 1250 34564879 34564889
    0x50403170a02160612021c02030a0506030606030304120213020f1309060e010b070b06060c030c01050412080f01120c0f1706060109140d06090209070804060b010f0f030c020703052406040b0a 83
    0x1580c7c079041c01304054000001455541d4242d480030080c040700c06e0094100c3c03800307100210b01310b03040364850500b09a10391080d031080b00102d924a116401c01414405014424001340110050611501c11000d50050b4041c4400780c1410405c0442808814000e00c202d070064066010006465814031402150070303c28000003078581c1c1084800100c25a4900c0119a410500402902e480c0c030b58102c1d40501070b160a840c11600088803c11104500f4440d00c3c0036071144070081c01c080ca050b40780c800180100e5001c00c0007aa50001c40701c0c07010520040c500c100000400070203540d0405070601101c21418030b040941810304008258008102c0002d21074040c9100d01d10813110350940480c03520707042000309805140203400c621001c041003225504038507550701ca01d0158805109000564004480710281031068001048410794403c0310b65120364044181e18000703004031000d1a8603134840030301e0a000d00030700500103000101c3d0030101050716191141c0100058030140504000329002580d80c00f80381c021 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 34567379 1250 34566129 34566131
    0x6020d05070305030708060d151a0f0f060a020109020301050c0703080a0b2209020301050411030d0309051b010e03062401020f07090e03040308030a0c09050603040203070510050403170a02160612 85
    0x118819580d51494500e106500407014461250500000405007500c20303018000c07082d882cac0c4020414281a010115107800050640e40500800c0007004190b03085a500c1108640d030315819400161000d109040c040c403164190303075407900c400c0d140c01000c0701c3e0014031040740b40d414910300741c0c42a110545003081ca00f154044580100b419504024020500004046e5240d803d040511050102c2c070034044000070415400c0d20b292420044050341980c0c40070000030081c3c0d01500b0600c0d8000c2d0880104250124140741111a80c100400081c2c13030301c40103944485001000c004030703400d02081d140c01403002840a001030710311480348001040e00c41c45544150070105440e202103003000c1009000300c4000c4c580c441d20762601ea042500c2107400818a080740100402c003003400c00302c0c0303500e800c0d4207032480307564020001c1410b24101803d0081580380c1100050070300200b48408000603660451091040b22100c004588440d01c46030f00070300d0304000b004003400100b032a50041c8400f0798420300c001c440c221103602c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 34568629 1250 34567379 34567381
    0x1d18010311031011090f0d0308010b090607060c030b0406090b03150c090909010605010318021e040b21011808073216061404051e0307030c06020d05070305030708 71
    0x10119041c202604003030300015241c84c0e031340191581c11001500d0110300a85401d80000740140078400c4c50340c071550b409400310f82c0316401000010000001414000b0000d82268285441603403001d081e110700020a40120341c03940c01c114024200351044900501086a081c0400c640010110b81c40d0300440e0494540400810700090744c110300c00003140c04070790f400b034628038051030800c1602e0300900c06030040c9030000b410a4803d00c075251680010710070032034000708000203010305100307049030f8022014425a040750300e44900a015030b480b181d002800304c1c410100c0b0509002c014403201d00f100c0510740c0003044038200d2102500400d00d40d80642d452254007842000403001038011003602c80800400d1a100d040c1191140191444003140e9443da8008241e2080f00742e98980f4400d441c0003e080c0440d981411081c00200071601d00001d900c107107600306030040c1e2048103501000c80e0508540d900b099038402c481c40c01c20070600f64104019100f00f103207458610300740b46840d60024110320000d0444010884014 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 34569879 1250 34568629 34568663
    0x303080601111c11070f0b0c0106061805011d04020406090302090f04050a0b0703090c0603090b09060c0f090d020a0807031419020f130c110c01050705060417040b04061d180103 77
    0x4070344000341501c804c031b200041d60740e4083c50710141c0c401d890541043d424644001551030080707607185200c6044c502e090300e040e800e10004580c0122803401d6011030349010300c0c0820043d01c0754401003028141c0740e5a04d98a06040d070040c00744103200680b00e0946004414208000300f1804505045840d6100d00400030710f4840741c0f01180070704041c01d4054541c100034140010440e80551000482c00d1084201c00100e998040010351145011036141d411101d041000f0112180d85d80002d0104c078100500990035944980c001ca140a0036980003010b40d40c0c028001402401241000c0a180d130350300c1c0c0002c00c601007020750011036a05940c40002d004d40c4200981140c50340d6100b4403882041a81182004100d402080051a52001000040c0c0e240503034030030843c10707505c5041210400c41e00607005040c0b503107561352840102c9858800c02e410082c001e00c004120708004200910081540340e59000400400b640f0541141c040d280d4114801c0041010641070b4007484428a81160b802c2500780d040300a030705d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 34571129 1250 34569879 34569883
    0x1060302030a0e060c0a050c0a050f0a02010905010c0b04031101020c0105130201170144010603060606021204031b0302060c030c060c040302100c03050904020c0106031101020d0203030f130c0303080601111c11 91
    0x3594002b05a40100420400f5409001440088441c001d03030390031081d01c0e0340702c00540758041c0d0040302901d0102d140c00000c020a024042e05203004080000040c60058a107101900310751052311880c0d440c1c0c4001810200b5989c0c001800c0070070042100b01415907500d0007101c0e0800c1138050600525400c8500d01054440401d802301c034607500f1130440c40c1300c100c4403d083c00c18024811400200c13034a900e010030201c0d05510000c0c1c100350310100ca54003586041e0450300d80102c10203118000f8405103800080100042e10740802a000789400c80d0011074035040c064003802d041a200a10f51440b84406100800140e9540308146029099078101084181c0a0741022125803085121013a0014000a0b5415101005601c0881220b0003144e002c8191540d034001240c03103c20038001540141d006101050245d00a80d010a0b0810881e4060900c0c402c20360b59001000c00256109801044501c4204000c5580064210100c80c0f0020043c140039150410400301c000c0c1c143d2040703c100000c0d200403c80c3c000301 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 34572379 1250 34571129 34571143
    0x9050a06090f05010c03020a02030a0809070b0f07050615010906050705070f0803091c050606100e0904080307030c0c0201021221010305030712170c030a021201060302030a0e060c0a050c 81
    0x480501c00c180c03450070800c0441c0302c041d10480d420340c03030443c80042152207442603c405040d0f80c0c0c080c502c0c01040100403121200098081080703070195000018549010302e000b003d100c062500c040340c5034005428041c1c10200001c1c55128400403010301c0d801c090303038807821502c10345a071400d2a40d01c0305c042e800c2c42890014607400044040201d603c0210703a44400002410340c1520407154500000c86850040f0f401008400c80103286500a1003c6041e5181080d0001e41c40c0300380d4606031000108000000c0c854480030380b030030788844400209100d586075142c043c0c00d4007a5850f082c44000420103500003551902544030800400c90702090280082c02c9414071030090b10028401816196102d0401039201c2d4800301e4125a60980c90b501c22504a02078203050a068003800c60488141e0351340c024540481e403008142d41003981d402c00c00c4c01d2110840801203030284c0300702c0c1c0d00161203203461400001120b1504003d448903a102c0000c202019020300d01b00d0b04010068030340703641c94545481d40365141c411 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 34573629 1250 34572379 34572383
    0x90f0e06070e030c0d0804050f06070807060203100b0313060e01060503010603060209012601090203180f060f01050d0c05060a02010e070605030613020f03040b0405031303080d1103010e040609050a 86
    0x1a60140301c1c605074088000200c8007000c4003983c0c1101c005034104000083d013045d004094175070a110401440c47e0940b6413041c15000a800d1f1494400140d6171044a0360100c0412030380303d54080140111086e000000e00058012660014a103003441c54044c0b2112044240041c481511500040c2d00e840081d0031080003001c02800901000381c40785000f8002e5000070382c0c0b00f400180800040c10041502c039400061040d401c007484880c43c9d080c030320080041d40c8028041506041c0c80764418034030340703410007090300400300300c8014150f1810724000d00800b540069000501c80c0d11000f00e07580201c0d5690021a0860b1412642e955a43c1c1700204241d0242407000707925400d43c002d1450003c0d100760044005c41c071905044695484007250f10401904a0140c10880d40c0b0649007400001e000403003038144030750030602500840741407183e6000180307100911074000300c2d1081c03070103c0c0c811800c03021070241611740c5003402c00039404d56041140130b40c0111402400a080d440d1107815020038401c0030310641078616 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 34574879 1250 34573629 34573633
    0xb1806010e22140d2303010f090c020a02060403050a0308010e07051b0a290a0212010501030b010c0501020f0c01150e071b080a08011712031b040b03151018090f0e 71
    0x184c90b288007400d41000d480f08508038003541801d040018814100b220f044e0b840e0404071003051030070000f1480c02022030003041c00562050300b0a140c0940d40302e4018100541c82400101114200c0b46001801000180d20000840002805108000750800140c81202000803011844c039606001e106240180070200a019049107542a245002c130a200076050303030f081032580c80415140c1801c8502203204005441d14140307000c400611486d84240c0082c0c0c085401450f01c3e01860039182c0b039441c01c82e4401000058103010000b40c00b440d085d028099680200400401c0070203051806403014a900001420402000b6510792a090500c0136460802c0340190000140e9448866800e03014009241c00c3c042c82440c8041101d520790200000268070f100041c500e907400d42540c80d000314071800850b103240d0b0313850520010f00010644010010203184901c1d551040c000c81d0b500c040b4280091304c901e44599038200996041c40c42d11141140746040c084841070031000840c1c4554000d28070044c40c18030300210841c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 34576129 1250 34574879 34574893
    0xc010206071215050d0309030224030403030b0f1302030105030706110601051012020301080109020108090d0210021602120109020a0f0608010e070e1f02060c0a0c020613030b1806010e2214 82
    0x85540035141f0001c1e030380309446080304001c0b100c6810440c0602850390140604081002a00282c441d81013854a40e40c040d1140301078100010000307051000b41025440c2055004c001000740b8a41000100000c02035410101804840402c6e100e4841505000f640d000e404a615210078080c805c6800070070131282c0000c210b4503941c40b501814060050f141c2c007a0f0008201c032003c40c00302100821156508010f070b070014480b800003004003402030f40101200d201085400c84c5440e0158039083d24901b4940c281d10b000145d629028810020300d8a0b00d504811000c0e180c604084c0501e941020109046d45c01050748400701d40d032001e01c1150646028402c4542005010b142404e40740000200980c01c0c80300794090b210103a0301d1105280480c0255030304500040c04140810004d405c0030002040980c01d00400d1400d010307220340320180000701c02c5e0380c0841901942d42040d01d5010042c400c0d44d000d00200d0880d0300160601301e580c4940341c00d09882c100301d410302e0b0b8803030745003081914200c4007400622481a40c401c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 34577379 1250 34576129 34576133
    0x20c060d020a081b0307030b03120406020f010e011e0902040b061207030b04021e0304080c0303090304030c060206011a0306030a0507080c01090f051f020f030d09050c010206071215050d 81
    0x1035044100b828000c9080207012030f141c20441c01030b4921640c292030003035003541c2c1c0381001100600313240c94405406010f000008281c100300c007401403010702441d0f00184407000d4941c0c883d5003100d200c1946654564505040d00c1d00302012114a1400f445108074040344142c0c4a000090044c031140f515242c1c0400b00250b08a0b40c0308080b00364500c200b000d41c1301040250300c518140400d80c400e240c0c0c00c40107404500c11880c00880700350099500540a20700d4181004210404d0602c0c5500c00d484000b4254070100d410000c00c059410400701420040c0301400d5154541040b244144400800034104d5103004000580e2580f4100107400035150031104075000d40360381d202d107642c0302c14100702c1d0280018085403000c940e9980f207000c40c02c21250082c00498200d407139294500c0d0310320340000207041140903035407070600c41603002c1014020070903c4582c0041c140d031551619501d40811142140e0540d00700c40c041041c91504410f070010685210500460942002c0b01f000c40c10407601d40015500481075240c06017 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 34578629 1250 34577379 34577381
    0x30403030c0201080601090305060606070819020a050d0908030405010f020a05011104051c02060a0e010c17040603050f131202070503030f0315060711040b040b0d05010e0c0103020408120901020c060d 87
    0x8590b8001c1e2941d251607160a0011180b00301c0742c0c000076010b503019201007005400c01340024020386004080c002e00349045001040034082c2c0301c02d5610016807100c1c3d505010b00c402408503503070b80700090a00d041c5052405481a485c2c3c001c40c4138032818048041e403d0062240207112200809500800800154503661103180360307a007180c058680560034150720742d020b40004102504a054005001078202514041c0440e004650700380300300c0c1001100381c1c1d0140014110050000d00c5111204400d80355424041e0083c21100010300d002e034280c150500b403000540030664800c00c695000300e484008811022401c0e4076005181d0b11064244c032000540c15029030284020754022070f0003802c04c4d00850903000c1086454051198068045a0301e2100c0003082e01c0d20340d11107030300240050300106035111180000744d5003030f02e241020f60f8181d44610038910f401505000b010021042405c086003424202078150340e94001525a20f01e031441300040512186e03000700301c070508041e4014501c560382c20050484c98 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 34579879 1250 34578629 34578647
    0x190e13090c080706020a08040504021317100c0804120c020402040f080109020f0103020c03030712060f08060601320309010605040905150a020f0d05150301050c0405091302030a2303040303 82
    0x144280520f08003c103e280c4007140c1440e07420b400600341c0d030401d0705142c104002075001030310082094912150018824151039141004580190050a560160024850b080c2e8110300c0380e110030130330303030310708101c0018202420110b607041d0303501d80790140341524030108009100d607410802d42c0294843c030004d04010f054028000c05482900c88111600000d0b00650581c06150348072441c5800901c0082c00c01840380501c0c1719145210000802c015a840d03c04082900d03c42d080700f0707180d030000360070004556008800e8014140d0142c08031505203800040c0324203003a2040002c0440c40360000301107540000250003c01c05070100070010040400b1610701195640030600e44070000c90b4070740000403d0841d00384280c48050b00380786c0401e4030b0300b01c200d40c85070000c1c90010141c080d5208038003a1440e10f51002d203c0c083c414000a440569110300b40307400c00c1030314280142241c1402c050041c4c00c00058801050190a01d98003070350464503c201055102100a00c0d200c1c44204c034400814000705243c1c2c4101305c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 34581129 1250 34579879 34579889
    0x90201030e0618070504110415030b04050c0a0e09010e180a0506090a02031209010203091507060c050c011103090c0103150b030a09110303030402150307180305010501080c06190e13090c 81
    0x2030f0240342e6610180011f0b14400c030020042200b003030100b0004c0700501091109002c0c01c500d800906034042400040c102e076020b4401003442d110110301c050106403c000c40c2100c0307020450324524a5803520351000b600c0d003401044061a407101c001c80401a003020441030028650080a0b202d41d49010f88a460780c43d040201e09038441e01c5a0445101d0003407404088500016060340a186080103d0003482031000c2070158224009a00300113074008a61603220b603c1c10401c85a48850f03075035450940c0a82581c465036011001c043c0104148144044002204400303410282004034000c90843d11280b5100340a51050701c4910001081041c07140141c0d01c0b04562510a20710089100d1410047c180c0d01d000c00c80d4001d400a01c00c010700a403500714403002d55404456031600c200c41d241c0c1c44001035038100c9142d1040b221070b911400117120044040c01107090075102034500c035040c01d19212800c0d010480d003181e4401800342d006500700b00c1e92280006260303040c0800e1404d2101c4000c40c03034140b81c260650310030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 34582379 1250 34581129 34581133
    0xa03032d0c0810120318030b090c01090501020106060e0409081b010203060a1a0909180106060203090307080105041a0a0b0d050a030305070509100e030703120507050c06070b010306090201030e0618 86
    0x20007031200c407400142910410913140342c03000e41a9900303840c07041d00034181070801c0701d180310000300198403441c200d8400c416100c0940711a203160130016188441c1a0019070569040c00c00c148a400d500c00c1342e064843c0d00841e00410640058240a02e0364852000240c2d0034034000b0031691045901500194000c2c0310a480827410b05a0b14072000106440511161104180c20007141c562417801c01007268000c02c4c1001504040031303501409508613a0154010b8000d6000401e54040c00d140c01e120003801401120000e01c25403925560f0018080000102150300c400c140300850300507074140e44403101c0020041c0c542000ea54950609541e110f0a038001100040d05001c0050312071403041c1c007903407070854019102100b10388003e142566a117407100300607501485034000000c081284204000c030700700c0346500e40e0755039100d03103042c0355080203141c0d02084e0045404200c50400030302952040d5045079001980016000c2c00c6200413405007102080e034603c1c5104480c240804424591181120304c2c08002c2 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 34583629 1250 34582379 34582381
    0x12041a060108010b03040c080118140318010c080903010906020c0c01020a0b0711160e01180b060703030e031b0f0c0411040303080c1306030f0f020c0a03032d0c08 71
    0x8426914003240c14500065070103004101d003480e00030103550064803a0175003032289511003400e1401c40c0c2c051241c8802c80400015590203100700e020004000205000103185070103031344080031104204244106041003041400d410500c0310b8a0160303001004000c00900c02402181860030180d045805c28940038000c482d11030150b980002070f800d020135841100007409648403401541c40c1031003440d40301e030240201050241c03a0307420000890043c00c100d4800e110554100840b554074a0b03010822208c0440c500102105d09a65020558002940c50f00d4040b44064110440b5802d40c0240ba4601ca491a4030f01003810600c030307000c142100e480b042a81102c1d82c90076030030b0130041903c400000c0559030100801050001ca44160901c550069030340d040070f481c0c00f404400d14075002140b03610403000240d03146041c101c10782c00c031300a420502c1c2c8510030960a050303400c1e0310241c40d101201001400c0c5551000740f021004040804050111658000d41c180340e00041e614001505a00c20b82e032001508440c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 34584879 1250 34583629 34583663
    0x50717030a09061811040513061404030215010305070905040c0b070c080d0e18060303040503030304030905010815061918090b03010501090905030f090312070302010c09050102030315010305040807081204 89
    0x132402a1041c1c100f04821504000724040c4001000041c00513000401066020404078090380241c1803407030a48140e0000078174060174000d06102c0440200984440ad0303d0040000c600005a090140d50200000142ea40c49501d0300007000039060340124018075010807074406020700312a407501150709800940e004580700701001c0ba6940815001c0941c888110300c000017045151001c1c583c0d000d031001d81100d1401f034607100000d00d50340003183d0440015404020920840d41c2c040b86071904840300c0010110881d681d10001881c9000782d0440303188400c0420300c0c1200c6584140036503c21100c2400036070600c0d0b41c82e903080c00042c02c103070602d10303010b50f00f030100024000d0070300d02c01c0c013100b650044091801d0591800c00585140d12178058680c1c148a0340441c0c2d99200c1e190401416024441e0300000b0b4140100c2d4000703807a820b025031156066400510410051595200044107064401d28000440307581c0d40c5400c0340740d07024640001d0111140071038504e480400e0101c4280c01540903105800c0070030024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 34586129 1250 34584879 34584911
    0xa140903031e010602030706020c07030b0f01090e0303040f0f030c1509050f07060212181f121104170703050105010806010e0c0a02030a0e0402090d0506180309030706050717030a0906 80
    0x30311131080168020405400802c42d15405084540da44409941032559aa196802d103c0b07408c1e220082d4860240004100512030ba2007000c1100642001650861a060310399212003d0001005003821030100000b004061082a800380043e0380094180010310180c010f14005003007000044400348184501c0020582c03000810000f00c616030341c0240850700c42d07684c03145d4040e04080c40050b1480c00c3d140b0408540c1e030301c019102210340c50020050355000b4006000901444080212030025403911031051200c0016030f00300d13400d4640c400380c50000441a099054609511540054555407920001203264407000c90424101c9419054860498039002da0252162080402c0e00d070141e8400c1260b004c50314001c0000146401c0001c000509104030000410160307544518101c82e42c0c0c04c6502040308406045011000301000b040042d41400103182c0840e9907070465000b00814081c01040c500204241c03040f00400300c500c141082c1d42c0b40d00309034810201030a80300360201c03403060070b0111007200c8502d8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 34587379 1250 34586129 34586131
    0xe030c07080f06310602070b0604090308040206030705040302040e06010302010e1c17160309050411040f0504090503091c230c010f090f031a091204030b0a140903031e 73
    0x207110098a03a9483d04c1c80c040000b008107090700300d04420283d90380300803080104400b008041c02148050303038807142480c0408a180008240310b110703618180b138800c0400d502c010800d5000c0c0d8192444c9503a030f00c4034501a078450050fa07000035441810140101d10710b00000c143d15049034405e80f1078404000042040250141811886452104581e8182d101140144000c007005074548980c0c10310b402410080b0500302e00d40d0b50825000308003000c130200b0040c00c0612030f0406801e5110a170504103410100f09015100d003d12a040c07040741c5034003080092210500840761041b000520701103511447c03141d03001010020301d109640c2548401084454820b07100d103100d1000110350058a0881c003030400656030402520100800c004a80c10045241490b003070a0710301640c0960880303200011181c0742034101540050031805150018000d0800c5201c0c4a402d483c141d0390301600104041d641c202180c03004124804102001c0307440b603070a00890b6640400218082e62464000b008120650300d4070030101c404c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 34588629 1250 34587379 34587403
    0x10030203060105220b0a0809060601020601050102370b10050102030304230705060c01150f2715030c14030105070e130905070b0405011706010203040b09040b040e030c0708 75
    0x2c0100b101e900c52881d96003c0c00701210038a0079403601d15490f103503a4081c0e41c000c0c85d15000447c1c047e0060080c9900100036003030f8000400d10090125604283c0000d4070385104982e5102c100d03600c0c10040741c0e160004407003d10017080040b4400d0070809141410066250155100300c04100d07450800b040652021080747d120b16041a130101c03e58541803403482c0d00c510061a64112405032060110392035070303100d00802003915404000300fa6403400c1c0600041120072035104014401d140e503401c00c4000d425a035188200c4084000d464690007010700d604000c0c0500711070420203110080008400c1000300c0780ca0034161303544d0b030503815405c070340c4441858225201542d160002c03c424601102880c50f16042000c3d02c424041c0f4081040c41c000c0d59950315241994010205c1070f04003017130500c01941d00094038501c555002c5401c01850401700b0010352280714501400d081d5000018800c1e50b0b58403150804070b0012000380042003401c05d0b003c06c00b500c940104498800c240542400010098000554003048003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 34589879 1250 34588629 34588637
    0x3061505070201172202030307050d05090a0501080610050306060d091518050c100c02040f090506060303120609040c0509040b0105040609110d0203090703120f0f050c0307061d010908040302100302030601 89
    0xd03018a02c40c8600da85c00340402c81c0c0c144000c108a40010b041403080480c0d140603a00c425407100d0348601000302881c0c043d0000ca04024061041000b42c1d60742c1c01c007805100d80d06080155803500d450300403400b070307210792040c11b01298181942c4008000b15502c01544048440d0300411600b007528034030b110302c1100b8601c0070300581c0c0503090401c01460043e40e00d0707484550780e08010700400d120b980401c050b81c54880610500994480c0e0581c00d012040c812594040c0b421006140b41c982810014541c01c2000b510342c502580005d000a8100120001e0510203031000a1076182c00c0d14003441d0a01040c0c40c01d0148900075800d0590004840e8064083d0000751b182c9404110f0400d44581d02030310013500000c000321a1881850400400700f42c0c0b000c040b40c0c0200c0c240d43c80c0786510660b0200600079070111100c4c0000c20004104880303030890040280e403860307a0302c031601289051004491040701e400410103a00194039240030082003144040040c8200c9200780e070444040307040e05c14140c0c00c038002122160f000c5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 34591129 1250 34589879 34589911
    0x705072006120601020709090b0f01080a0f030e030c060304080c07080705010c0f0f0c0806070809030a0915020a050613030e040603050304030b09070b0a03020706050a060b0a0f0306150507020117 85
    0x4070482c0c8030481d0300903018412209a95901c82c860401c2e181080020768502c0317420000d108080d5240390b2101d015005140051080c49416940c040c1d40d4511450050100642c02a5009032550305100240e008140105190344a04282c00d1541069201e110250801e20600300f00140f555000b144c45411690140c452141c83e90b501e07160301421019010049418041d14024200049e02056a00f00601215001000185003141015103008005000401950f0090062a6000b54460900d50a4600d18848001105030400f0213a18040c0384032401816030042c00d0400c540002c608440000c038601954500300c0c54071401c2c0510041320254000504545c10401051021988002d142c0d90401c0d00142240c25040d62007800100039000038000c0c41c0044c0d0006691400c1c0021401038680200c442c40d400c1101e00d261601e40c007807500c6880344940610132090580741c3c61500951102c402440e01c1c0c0101090742102001c000c107590300540d003c80c08110000316000d8055111466540300f694006025455 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 34592379 1250 34591129 34591147
    0x30c150c0a0602040f050114090d060c120c210203010f090e0f10050a05150d15090b09030403030810121b18060305010b010f140304020301060503060705072006 70
    0x603620018000480703110740445000064441e10003400149044051110014181030004208246041c4080040f910620400789a5a03075002000b50042d807140000540a481d428181d81c100418603003001c03e54500107101000e16001007805101900d10414050700d040c4104540301240000c4c0031f24403007800c084600b846120392660164010504660881308403075048603840b031030001c1c105682c4c0c19460321a410300c280081c05010760741d04814645001c9465207060702c0800c1280345001805803414001c841c008030420000c0e03106c096101d42100c0d10081900d040071f001d595a5000340f0040700021410300c00611200c40002d00e01040d542e80b00b5143e900b04115440d0f040180313103104d1822100e104910f50003c0c8401c8004e2010500001070400829054950b0420310700310b9480c140c000f814802015138961280f548842e0384d4052101c904222900c90304c0b0307030010074018000c50b00941c0e014800e89050141481e000005044200e01c140d21701100d58040944551081c10280500c42d0400014066845 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 34593629 1250 34592379 34592419
    0x1020c0304150c0506010f08061302090403030c140c0604111c030c0302011103070806010314060f01050c010e010903020a120309020d0807061b05040501030b0607031403040807050d090602010506030c 87
    0xb000985103001c2c3c0640e495519518180780007070740001c0c81413081c21010800c1c090180032140d840740c50743c0417040c0b0008980d004030300400e40007403000b42050790742c1441c01d02c0c081c00344a80a05410210003140d4a5413566100c065540006071425100c3e2480342034030306524a40440c900c41e10383e030200c1c03400421a41c2682d040c0c0f40344800e0b003011070075075481c1e003031003040701080700041d40c4600c11341c0d80c41080d241014000034040f030340f40e05803801c0e41c0c2c01d00c442000869140c580031036070b1030402841c040b5600c0241c00007060052401c00300c050055401c0c0442c1105041e80010b50f058564003480da040c0010503425010760840d500000300079001800020710102289802000e41001401900c1c0410b000034000f41a114400410261101040003c141440305507414800c08160500c180c0d03406240a403252005080785185200d210450b580010000f81000f114100380c034070459106048440b410123600c0003401c80480d07170048100541c6001d0018079117107800500310714044d0018080305035004066a543e0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 34594879 1250 34593629 34593659
    0x7060912050a032001150e100303020309011103090a08010204030b01120b01120302010902030601080706020f0105060a050402090102071e030b070f080403050310050a0b0703080603030f0a05090a120c0e0901020c0304 94
    0x1362076031074101d000c290052420f028292201c0ea1000001390b90704c2c10304c01c007600c014101610201040310700181c1030000230b4000040b200c1d2010242088566a120a00c100c0d1a42c072444078000d030000f140d02000204408150007400c1a20701c5030580c01c030700c0e03a296220074040558002024240c40d8007500108035024482d24a400c0d00c50081c070002c6200d41803500400c0c540002a03100300003035406508100102c1e54140306c085100d105100007449242000d07000034039094400e001d03003031113180c1c0001c3c4100c19071b0082040b90000e25980071041c04202441d0b468800031f0340c10f4881600c0c104204c50010305a01d20600000030300007001e0310303a45102e440341d44044030b96400003840503000c44990706000c075199031014a21001095841c02080d95466544ac2c0217051840c0541000d0003a4014020b100841070460180c812221152421503207488001c00003e072300e036601d6403195103d280400b11590502411b49000d10648400860b070060a8407014499401c0b8801c01241140c0394206101c14085001103803004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 34596129 1250 34594879 34594907
    0x160608130503030709170114063109020a171b0402040911030405010e0c010203071203020f0304060207020a060e0a09020711100c0605100b030411010207080f07060912050a03 76
    0x1241400c01650341e031914603481070b601e100100303400100403c1030300307001c42181c58030030304c131a0003480f12585d00c0c214031002400c047c020a106155200005900900045030010060714641400d110820502c02d0407009200140042c6d006912554000c164241081d200d6841e200300c980092071412080414421482c400404440d0702503020040010042d8a03805080040c0446003070960780c1c2d003000e00c1d020f403c541c806030015545800004000b0140c3e80c010080d40c2c01240c001c001c00c5d8600d10910307002c81c000d2040100b608440380011042c0001d0142c9039019003002e51080d221300e01e80300d0301e52000358dd2070080320041951101c020f1034103202842d4283c003d8541e0611a83c5030910000c4000c000610388450301400e8000a83c190007480b0911051b401020303001401c0c00c00c50500380c1d081c2090400c640c800207002404080404002e11702a074420041003000f03090440540d2080420f1b803804545a003118407136400020003a04000c101d11103040d9411014507400001062808120382d4240d036581d40d01444 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 34597379 1250 34596129 34596151
    0xa0510050603011805060d05070509100e0c031905010b0405010f0c02090723041202040203060102150c03100803040b040e040f0c0e0a0c020105072708030d0617160608 73
    0x40040c4503200c0740040c5000c1d00c0c0549070070f903a8411541d901c10403100000d00803481000004e0a440c0030910100d010400c0c1c0b0340c19110b030890742e61000d040072558075441c2c0c00644203803070040400000300e940300081d5010700e86141e51550328403020088601501c00038001d99440220030441000950300910180c000c0c0382450070803c2d0800305c947c0010310501422a40b200100f4500c0c4603603451400d844682c010080010740303e060a040c2407080c0c491a410484600074021a800400f04038507030700070405502801e0006441e41618030300115200d905070030680d01e102d40c449940c84003250341d01d008030984066444041076542801c7ca407005503a00c0342c0740031700141c5650003580180f10218000401541c0034010802d20000340c0c2c1003140c030b084203e501d100052021a4540010710840d41e50100031300104441d60b00d0141c01003220215010074840440e880491940300c0001d40c0c0300419603540014084821544c0c5807960719003144200c0c0d403035240d00440c10091030b920a4080c04254015283c0b039070008d0040c41 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 34598629 1250 34597379 34597411
    0x6031a0f0a2607090515090c040603051008060a0e06090106180903030e0f010c020c1e04090501110a0201050f0903040b03010605030a02090a080c03071e0905090a0c0e01030b0c120a05 80
    0x6116007803c91a0f0000310340039484000300280454100580702241d04240c49100403440d204c42900c445001300c0c06040105511076012401e480170b14030760080907003003040595581c1d003880c1c0c80c01c0e0010500c801021241d8050413002450080e018400e0404544801411260f07898500d10030748000d15412904805050b0b5801000160480c2048220a5900c1940000402140c045806881c0511840b1028403e0b010050420000100c48a050b0800721b01905c01003125009842c250340500800c642100c41c0d0240420420261030741500324500440789101600625150079070181d84a100b14001c05003001d20800040100c1441840156805070614030014100500100016050045170b444554554003070400025a0315051020700010b1841b860b804a140758200d21880314103102d4810180529500d030000380780020103101e0311224039406490a0704180d01d80e09e003100010002e000580e601100314000504440c03030401180d035080c072460032003402640c030042d002014210092100c01da1404001d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 34599879 1250 34598629 34598699
    0x20d020406090612051203060114070311120d050c0a020c060a02070b070803160903031b05030702041b090b0304030509040506030a060515011b0209040201180f06031a0f0a 75
    0x103c0b4880160860115070100d6107100c3c28200e10745074044503020144402001844840e81c0c01c503c048034485521002907890b00c030b45003400c1ea03013010000ca05610502036900303040030301548280188101e990800c41003060b80c4651108502c1030080e16202e10250b40881448161450240b010300741c8040c0a104a42c00140c071000c4580a541000d40101e58008021061088180c11500207500c039507010728003054807078a140c4001380303410800310720498142115011038050140a0045919442d0050800d002c24401901c490042c1c8800c4016400060444100824205a82c504907406150503a03625800c0c080c210b41000000c04000d485e060381481082e02000004460b03001d018070400d5008032020249003004005080d0070a040441c0d18280c41c160000070059441c8202160015020301c1c01c6041071152154080c500d4003d80c0229008200035207001030104e6060308070709266420321390842c1883c800f00c41400400d0030180080c1d6448142400c00344524100b220040f500e80c074030000c0117281c1640760 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 34601129 1250 34599879 34599881
    0xc0e04081905190e010e090a0f051008010506060406120507090905090a0b0610080f0601090330030204050906010c0204023009060408040605130b0309060a0b100c020d02040609 77
    0x1041001c011032030106804401d5120000c10500742c03070041c00c24054111594000074207000c3d03810151841035100c0f0004c100608039641c00160314080500e400c1126003400106050390710510300c503031002507080000007001801d040701500e04503070345515800e607000c41034036100c0042c04004006201b004100000002c0807821401028000d1b40c440010f040b00100508003141c81c030b0f00041001c2d0190141000c25040240d00503440e6604c4001340400b480d03a9245c90004841d5800c0b607900240007444a50019104003441812100c0090300300703100c405072130030300041c2a000c0c0d02892013680d03800f0310f48000090441d4010303000c4202e000d100a00c01407900b98202c041550b101d116003844804030131800750900310a03694004445c1c10038005070041c21280340660354a0f4407440359000e21400c01c10013044c0c42104400041010303010f801210314941d01c81c17038050f86403580c49130101c03001003410741810001c12180c1009146102040c078160b440c1c10301c7c05070a030240401c880d05060102d812075a0350000081074049 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 34602379 1250 34601129 34601167
    0x27020f04030609020301050709080a0303021b030a08070e100c02010503040c0f1202090a0203090304050d0311060406020306040b0f01020c0f061603080103030206090105060a050d06020d0e0d02010c08040c0e0408 92
    0xc2004002004400c2d40141807c44078014001828403626520522245500080072164a90305280141c3c0e540441149140414079440302c080d041c3c480031482e108500e0b00079030001c0c440d18095998002da2a0710f481084242c4c901400b0702804601c041443c040503500c150001c40d4050b000d4042d410071680d440901100b880004d83c06a031130018000241821494031315603550f0050354902c419400d6086c0803000e00c3d124440c510421f1b1260100c0d00c80b4808250281c03c803150000f074814143c070914949824804060740c000c6860502c505d10b041500320241c03801c2c0c1c0e03e907101c400041e8014103050012800340320b2206034180c622903014505000300d00000d100759804401041c402d86e51079001d5451854041c0c900000a40344d82c0550341050108411174580e40c076100708540c01211529080146400d02400a2203003c0442d2007550800841c0141e5000014050000c5040e0754004c012004a80e0b10840e1840c6066800070710500942e10200101003984000d80c0c1c0040c040c141c0c241c44c0200940180d010420 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 34603629 1250 34602379 34602383
    0x91209012703080d06060203030c0d021309110d0605100801090518071206060605031e060f030a0b0103020109060207030c14060f040906060801140f0904060f090b010504110427020f0403 81
    0x2000101c164000c81c13640501d20013004180021030031414100c072482d151340192890700441646c0030424581d04000703101c550009204014082190150000809495034002000801c080d03040031000500d60a1041a80c80a91200d945013511a400c210404000c0c0202802c59800702d410070580c11440007050059900402c400100b03070078800303400c1c0b0f441c4096136490f6000b80c0a00c41300340100b045185a030300c5d8604100d41604c00328140c6035120301c001000d462106603001c3d090700c90002900300f04090b440046050305d0007600c0e20840141d60b030108986d140b4507400020482440c40c03104000c41a0032000303002d40d08000074000c0d070a1641d4603501c1862504143c2c003000155454050400581da00499142c0c09403200d202400700da40e185002003800d55451100d018050302e522400141802141d50115401c0c10518105100000890038800c41b42c14083c019075201d5444c1545050340255001c00b120120740300000c01041c410300c0400c0d00090403401c15661020240c0070003030070480e00c00690041010754 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 34604879 1250 34603629 34603643
    0x4060605120f06010501050415050a20030d27110d0f1a1003030e37050f0301051b030910020a090305010b0d02030606060d060b0304030305060306091209012703 70
    0x10300c442d035070326201040e48264103112080006200300c000368410110386486030304020390795802c8040211407445501c410f00c0b116500c1032545c2c0e40100c10220080c440c04969800c148000100c0a50300305410070003021311003005159400702c0b400106025404900404002c02005c00d0f21079544400d0002014401d04a0381074061402840d00800354805d4540c10880d01c5010610190841e13801410528000440718890360f0004910b80c0c1c0078142406013500303081360b480c11851040e034502c401d15111126000c0c3ca4452505151126902d00741449020f120301c3e61f034210b103000c4280c0d20040c0c80241d0b0001c0e00012300e034000c505d42c004619945000400305190079036140002945181022821039100601c1184190040a180000741c0e40026070349412080464000f65190400c0391240b00500040e0710081c5403010101c20481415011380c00240305144c02c1e020748600fa82c0d01617410351115054240904109000d03c00301d00c1075481540d523a40f11300d01581410626152100b400900d102e031951048801c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 34606129 1250 34604879 34604893
    0xf01050601090e010302090a0e010207120306061211040e06010c08040303080f181203070903020301060905010905090307080403030806010306170a03021b010c1401020708031801060b041d0406060512 87
    0x1550740454400c0c003c00781030804000c2541113500080f00108050129500d003170b1110744042ca08482941183c410603800b21224010861442000d0050a000e2040b0000309090940000c2204103502400d21400300340d541c2e15182c2401d0000c14240031402901c1030f4104202c45034440e0010307000c2030052000d5400313604c0d0240e1901d0a5090010500700060080e02c1d20790300000e4801c80c1200004541c0400001100080d49030f50300c54030101d4020304a903002a600d5030030400d00141440141d030009060350001a8240865610310504503a04c1c850003000400880c410402000800d20480e40c0c16004207052501050031aa510050f440900c6030401288a40d000684081c0800d0340400050911400c00300000254285c40d00018020320b1200802600104600c1c144110070754084d030403110100d500c071a28584a00385500724400c00503607042a4105980b8080d80444c0d9043e206050744c0444680c944a5a0300f00782402d04040000c402034000c8601a4842e08045515034528500c40c1000e1600b400502075 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 34607379 1250 34606129 34606141
    0xf03010e1303081302030f0709020d0e0102070b0a020307030b040203010603020c0c0109140d080c010203010b0408070602120304030c111e01081501050304030f0203040f09060314062203110f0105 85
    0x122001d4052540a2444403520001940029001d640185419a00a00714410b8008a810181401800180ca000700800030983c10181d50180504c40d2015404001c0300c064a80030324201d2145440c060840704060000810f4a0b0303403038004542c0460245004540b0710a40c001140c1aa0401e0b0002c00102e5008121130002040c00c0141c10741a40c0246001180c4600d40350310b12903942c0b00d58004070701810122481c81d09004840003101c0b000300800e0003c55580d07035282c01224498009005d0342c03c40d030140303002c000317484e07440020807207805840c6000361440c1d62180da806032020000510b045400c034205005146003540c6d861503a41394210040c0034490702501c0303a000100001402894081049100b0781e25a0803640c0c03000c2130300d6100c0d40c98240055581d05c0c40354282d10f580503640c051003107003e4a84001c901e140158020380210f0f0320034600d1180a01c90040c2d4203807201401c962811f5080b0b0100001c000080a00c08400142402801c00b4002c0c1c089180380c0d42e04050740c11000c481127a44a07400e02034 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 34608629 1250 34607379 34607399
    0xd11070b010e0a050606040b0a0302070206130f060f0e04020306010216060906030b04060e0106051c0c090302090115270f030b060901050916200609101b0207050d0302120f0301 77
    0x380c0700d100c085042100d031404070005015401f481c000c080000a020601c8881180680e04640003260018807640d11002c80350b98504a049080c0610224403002c1074002960502902c01e07810480b09944030f65a0405054041c07000941005220904600c00d080710324100100c1c94544802a0040b42d03107000035603042c540702609445c071501c101806103150000c01c02c058850010303d14195241480e240c0d9980a0380180c0281d00f01d0307604103940c002450201c2d8200e0f00f60f0866807400c112031080d1800e0002e60381c0c0340003040c7c8050465031508003103849482e10f03041041d0103400740c184100c888203200c8a400d0300c419600303c0000540e0400ca0b880d403404414041540360100509006103001c55a00d09a0b14021010001c080c80074069141800b44200032880c0c1d03a10300038821142e800603081201c00b1803528018256403000b81141803142e036072621a0004605a0321048118600450303001042ca4500e44028014403903a0180d09400318002e2902480703c4050904c01040e00419540c0340a031a0f50424640b84 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 34609879 1250 34608629 34608631
    0x1107050105040e1b0f0a020f0c010309120809030f0d0f0f060501090303140f0309060f090c150c19080403050f030414040e070902030702030a090e0105030604080d11070b010e 76
    0x2418040140700030003c2c0c03005800c0c0103074882c0e0025202d032910ba210080700d2629002d12040552100c00205841c1d80042d40000d05146100d00b0604984103680014019011565207420160080c0c592406120406004400d500d4020700d0076000c5074074200040c03070020b440d90080c0d44840039680d140c00f00d0101142960162a06004030780f28108107080c070b090000f9209040c0e61000a09010802d0001014a00958169500111912101c41d924a2b00d40b1500b0b4462301d0889400900d5107034107001c0703956488002000700080001500c203003a0784a0486510f54150016440c5504134880c00d8810200d036070803440d900381154401e00031280c40f60f0842c6015820072043c41d00c0901c41d03510907c020083c01011072a80c031000481524001030781c0081c03514660402d41d29070070141c40103000200740b0000310360000041080741c00c5035580e85022a01e40e010009840d000b84102581580541c0210700800d0304000100700342c0108080014031710804001c040055002140181c40e4440f0490041001650030240a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 34611129 1250 34609879 34609889
    0x12052827060905010c0c030c15180803090f190305030a11031213030e09040305041805040206030610020a1208041403160b091005010e1503060c030402150d05071107 72
    0x14110345818048001d04215441c80303928104094042ca4005125851a1101c06035421045a200c51612400398030000c09820201000080e001c54501d000140d0385035508003580c00c0d400c0510302e44000380d0b08112036801c074102003071ba0000700440b001d489068540010001140b18802031621450000310103404076130418000c09454000300411074440300030f82a0264040d076416404481544281002c80c0c2c00340c10b44003210780080b001d40c02d1005050f00711020700211001e00f507020440340324070100300d41600c0c000e5600035040309050004c2070340c070b1800380d40010b9014120b104940b0b001d9210344030f00301e0a060045442e0042004002400240020f14441043c0e2070841c0c0020351030401c01001e200e112005810000c0c01b0b00207400085050864140208204160054014421961150081e5255000c1070354030340b030300c0303c0025196405404c0c082a007512600e07101044074155603480d020b10003000d07510461145100e00030448001000070500ca82030041005550b51682c00c1c41d240269807814140381c202d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 34612379 1250 34611129 34611197
    0x30f1d0f0304081518010507080a0e030406120203060d0c1d060406030b0a0903020705040608010b030c0f22090227010b0c071a0408190506060409120528 67
    0x140300f8400c0000c4c00c0986014a107035079198594502101c88a0105100c641c110030394207090500c5403455000114500032540200100140f248043c403940c2c0c0e0744158400c01000c203020014007110303a401940035541c40040617200000d0400745664640681c1d042c1e8120310f80509803824070104104109810b0380c1e0000c41580c0801140d421a06c4050000c4001449406003549483c88502003510038003000c00100703005041440742d2a101c4010b40e01030084548007500912600c0000e12040c542040404e5111f18081c01d42c140c0b454032149480d0f10410040300c5a0300f03968540150b1030043e16401d100e01291085201040050804400e4210032002c06a000b0340601109200d9041000400b043c0001100c0d0f45400b0f030302503549840c2e1380c2e00340f5028aa12000d9030f4001d030b40200c00e421601050401030f5901c114142c5500d0350b1000100004c440c1301950103000c007075007203901705100c0340a5401800454401413104101401d50182684240700300740c0c0400016007a4030240600c0340c0201826110b030052050 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 34613629 1250 34612379 34612387
    0x1b0d110a0f090501050618040b01020106030b0106020a031202031612110708040e0907080607120902030304060504060f03050c07030c0618050d020c0d02030d03050615041509050f130507030f1d0f03 86
    0x142d110075056980f1f440070b1140d99969404451070b8000d5118000455011010103900e694420002e91984403404040e400708064000e0034001c1c803924400c4a03c02e10f902031840c1d09419101d001155007109414010b29425a5404e010b0b030225000070207405002c0c0f19080741c0796a0f038240b07501c3e041c40d4031019001c08040d9010100622030780e40c021481759030103112407410035000c6c40ea02e40a40094000000084d400d800000350102c0d4a40d803000040c003d450300d82c0c07150012001d120300124202c1d0f0f82201c80501805040c04404000b070b20070f45100703c52034040c1d0004541d00840041c0540000b03d00700c0300f1102903210fa8103038a04c40d07405120b1007040010443c0c3d0168240c0d40368001c20f072241040d1101c182095500c03030003c0c00a0f03490603810f041e02520280d0054030340c0c0e113810824000d840c0819248003c205091400101c61604007000408411f0207030126109014034803e203409400080c01800a054a6210b091800d60b154868030315000c90200104000d04c861990035814458107505121103500100 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 34614879 1250 34613629 34613647
    0x1501031803030b0a090501080f0c1009030210110313090606020106060804080a0314070806040501051c0b193303020913050c0a03030809070501021b0d110a0f0905010506 74
    0x195032581800d405040201d02c42c4400d10010300109820f400610302c0384d01c2d0200106105400040c0c5100c1a42c0403400c6550340000c003010044144200c0210301c0002d5034041c0c040c001410040191a0340e044507003400d010a0500030b8985045400c6450603400601c0940010040c1d80d980e40280c000501c0540000c20000d03061141c01001032400a101070140c02000850342c20343d52195001281c07001c40c440c2240704c281400600241690003c0d030b40d042c8030703034141000866a0300d1302c80c94040c3ea0b00051202030a0800165851841c090001082c0c0103076052070074640000080c083c040d260340b118080805d400f144c59542500c442450b41050207c0244050348030600c01a101e80070010b401104001d02e240300da034240d01d401c03403511010400b00d81e001480c50900000b011b0b007040d82e05000d078045c1829110119111001203035a20103490f0040c1403a5800d000074021070424114071242c0c240282c19180d050203201c008549072413080e03403041e005107410190400207000d29204d264098541110098a00501c01d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 34616129 1250 34614879 34614911
    0xa0204050d0305070809090f04050606030c09070f20010606020105010806060604060804080d091112010e0c0f06070203010614010f0201020c060601080c09041e1104031709030304030605090303150103 87
    0x2100500307000c0001a000e0a05c48040d040e214001d0000f4040b044900d010b540080551005070f500300c031284180c6006c00c0640c9800314519045020240480741c40d562281001c44841010000050600c2156880c0e0368103401103039002000d144d16900046101c910f003e00090850304140c1c00b905064003c007007030150564403001221704440361460b0502554540c0d0400e90194802c40000040d00761a003491070382040000c4040701c841040495502d0414410002c41078281d40120070081215000401e10000314a84020003140c2c44030040c00300d80c113003022a0301003400c5030100e810108051803404030b403112a41c0d003c8803105076000d40b031000b03500b00b2507010707901545e464015200b24184940400003604113900e00c01500c4c01d0b4440140284542100c03c0008039550b524440f2900005003040462100920031504450440364060419040551410b0075900a9008a1622503060004100010108120b0300800e0b0080745c052001e180e50f13090514001c82950700da04041c906040c18840d42c1040d414503 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 34617379 1250 34616129 34616149
    0xf120706020c030c030309100507021b060a03061d1005010512011503090204020711090c07020603040602030901090f050c0a1703030a0b040b0d05100b03030306031002131508040201080a020405 84
    0x1028201503124102e409449045004105000c07642e40300200c00c0080f6030400107540303100348042c50301c10020758403420812a1644151960040302d100981e150a465003402402004480558500065001e80300d194140c60342144030500d819181a400a100c00194003500f0440104803d007881d514001518040e019640d00500c01c0f1003e03041900000483c280c003903040000e9682e8010b000319a100d501c1e00d04020388040c075180b894003039481c01002582000c1c2810480d10a5600140030500b590307620340d10b2401a50009144c100c241d52036407003210025038110f043c000028030032006400d500c0101800d119030000b19510504590508a281c0394040e00003000f225008000010045180c0071075030082809021901e12040c1c000350390621900611602044210207010744840601003906c2da2000c06a5900054a40d25419001034900b565101d1540d4001c2107454440600d200101e5600e01c06071703087c90007034140100031503550000c2001319030323004070481e0b81701c2c0c85131000b18242414803002c075122660f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 34618629 1250 34617379 34617383
    0x604060309120504240c0b0906040308010e101e0512030705011404020603011401020f030a0201020903010501090905030f070609060f020c060702070303021c090314030c0d030515060d020c1e0f1207 86
    0xa600c40d60096617900c607018034030299030000d4288016082c0300145d03958460007140c0a40c00250070100104040d0078030341120380220507580c0381850300360400d074050203c20109004074440c2c8001540000b80c6840c0d04c1d80c1e160a0000711005103031503004a082083c20342b10170301031440c1c420802c0310402005a4800042d81d0640b49106042990b1640e0400181d262180c918103114180c44003168014141c1d505400904500f40140c00910603a640e81823608261200d01c6001070582d01b0500c403200c9088c0b0300e400940740f0305000d06c7d1b012521150b40e44031031003240d11282c88200200c2c1c0001d12054104003c000b81030f0409902c1c4000c0491501d0360720025243c039420300d1080316405d500144a40348c184644050070195400c0016010520140009265a64040d104c00d00941c007526200f100c5d4607000c1d00c1598817980080c4040002c02000b0307c10094281e02c884c024161720f580c244981b01c007102041203c40321365042050495403c50004005515114594071102010b912103042c0110840400040d514295 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 34619879 1250 34618629 34618679
    0x2030c070f1a0a06150c02031b061303030801030218060d110316120506060d030504090c031d10151409070c140303010e0a0203070507021306050604060309120504 71
    0x8646180c1118103031056280c103a6540502c10500040d6161035001d02d00300c465034413850106040c580801c2c6c4190483c0c98003c1e505421042151894510028600250081c014085440c000080e807002c8004105500140e00180c4460018021800c00d0841011030710a807100d40342c11071600c040050070203504900b0041150040b0008400d07907480420095a051501010558059881e1102c0528911011805650728404d0070049440b6040041c2c6071083e10b40c055803132510b03003800c00d46514050304100d1800420507a480729400c07500e0765095150624440202c0c0501040711344251803809a44103611400655200b11804102a031146c41d0801c0e5440400d079001840d5039154602528104495400070300b000d00300c0d111f042c2c5420008001503042e1405800784042031b880f800258000c07808102d5107040803c070200b050b04094944010702c860141d01000c00031800a40381c4001c0b80064100358000404640c8800c904c108022803841c52407900e90041c41d00b01d04007450303c6038060240103a1200c0c0c020701 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 34621129 1250 34619879 34619903
    0xf0e010509130c0302040b1b0706030b0d0303050411090f060f01030c020307032102030106020304081504031d040603080a0302090a090510051c0204110c010b03010c020d270303020a03020f0102030c07 87
    0x20f540039070103441c000d2895a0391a038903041192290030395146c01e1300303401c0368500400101013000d42c0203203d4040120000b600e410980e40e4107a40641c014036000c0c100b0b075030b003c0304140f205155a542002c40d42c0309900d1801029a54100b40e010f11001d0401544c0c3e0074103141c1012020228158000180d03060150589098900c80f2a110b24800c0c0e441d4002c90b001a44500010010440c940c002005004035001201150741c007640b5801d0031b0b000c8510917240100040d00b010504034500041d0310100303240060041c0700250141e5a5a5074a201c0d91040b084080403c0d0045025201c5e8902038100704020007038404140014a02081100b41040043c0203080c41b411079201e0880614094220052405902034000c004003c83c40d00c1a8500d5000400c1b58005503081c058105a00e0030107015031001d580d907a800400c03020349148800d035207000b41d40c2d4000d2a104d421104142000c00b56202d441d0045000b80c01800307008000b401d000303017049460705020855a0040042c0714144014000300d51141d50080015510 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 34622379 1250 34621129 34621151
    0x5071709040906270201050d021e0c0705010207090b100e0103150e01080705010809032b02070507181b080c0c060c1201080715051602040f0515010306060203090405060a0302030307030f0e01050913 86
    0x4840f41c80342144440040100b205804003000061533000c4d07810036000c642e542e0780d030ba100c20415127440e4142a40c002d1107079007042d105280a120340c2907501c1d50506000ca014141039844140da80025442040700103e030030010811201c3c01d000800c00b92000386011891442c2442005a591007007110003120301e0942d886001d0340520300c2581e4a0754038030000f0305540c2c40e030643c00c00c00d41d118840d00480c000100030b01413030b0120030814804c008510180c101c3c0a10307507885001d0141d4140360003e1090f040b0100c10014000548002e101c55449840d041401030703211808034005111001d0160400d8145512540741400f0f00c50340b40320095940140d03443c186543e0210404030040d09545044003d42240c01e00c0c0100c00c0502c41600a0740c0b040d10300c1c0d4a40004010300c0401102034541500c80d200140e0020002c090003824150080e95000b08064a03400c5142c0e034a6001ca0f1540c1e015040540004544d14054644103a2004005000050918000341050001e4001891100d008811468180d0303640d00e410007 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 34623629 1250 34622379 34622407
    0xe03041a190801180b030a030e060d021308060705070203120705070f080c01020c01090f050904060b06070f11040504080a030207050106090606021005100605071709040906270201050d02 81
    0x6101d50181807507000d0103040d08000b801c1c0480078064039079450312085100d45520024810820460001001000310750b2140e20140c80c030a02442109410200800038003840100a0000707210901040446503e590714046500341850405000c40c8100306c1e0410100c40540d4000841e4840411003041041e950010751030080e2400c840c80d409400580000d88000070117890115200c2a00c00003078081da071720440c008004407001b0300540920004c9542d01141400740d42411203c585c2c1c010710400c000620fa8100f5000611290402c000c00c8601510300201a41040758683c11455800c106035810720081c00d00b036441555034051410158101030b404100d0a0502800350850801454000800c021041d00e503d0001e4846804121403001c040c28031001c180d050400e8100002291401c1d902c00d4140406503503541000c90708084040000841407045161540d5070f40315087e01c4034400c400001c0c25017081100540d00340c86142058041e2001c20003d000580d03000303011a6500300a8420069641180c050001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 34624879 1250 34623629 34623637
    0xa12060e01080a02130f1802011704080f0c0f010203040503031e0f3d050a0e060a06030902121219020105040308220b04050114060a030c050d030909021804050603010e03041a 76
    0x103806d2400d00c0d10a01c616400c0840390034105000703070703119030303040742a1815581c15840607a0000c1085204215102203800d2a4000d424116150340c203855840601c030700e00300e003a42c1043c2c1d4181c800d41c100000744140c4890341c0051095030706860788108540d140c20000c041402c20001c001e50403001c9240011410306541c002d060705420b081601d07180c240170301460011181c3c84035002c2ca5014400a46011038040e82c40129140300301401020782c00d0141c00c180044001e03010000c4101d1304800c070441c03942c1288400b03012290b840d1100040d070644510291540d4415983d20882400540e4541010310000c03036408440c0d154003560b100300301d01220498a0728203103a1002980f010b080301d1030340e4003480200310040d00141560410210b07008580d07110314041000e40182c5220003003541c50041e00401480c1840c14103075540034084c1c20494050341d0b540400030245d901100d040a4803d512508042c030501c0d107481980d8125109800800c61468445a0710741e4910403409002c420700c520181200684030000111 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 34626129 1250 34624879 34624901
    0x30c060507020607030c1706120109080c16210b060616050303090606010807050a030c0e0604060c061b1d0406080a1505010602210c0c03030a12060e01080a0213 70
    0x2009949090507000f5143c10058400c2c60000c1d041c4808942914400c5d8552007424400400d411065104e5200b00101d141d036649003070f039540d525000000e001c10708800c050000f1101e0600544035450000da0541c180782d0311a006110f4070058036425000d4455905940d400380744e40f15140c16215114400003803114001c04c8418601c080010b0104010050301101441c06061204110744c070307603182c4800640c2c0154007203c2080000c1c0003800500035261094100c11443c603114188100000144170104843e94442e801040210f8010a2100300704503d070700c45c08009256450403030340c43e680c0c01072005001d46c00d002506904026000440c00e0b42e42e0301d0354044030007000d0502c2240d03044520f604d0035504295541d0240c0b0140d600c0c04000060050012030001017001040c20703084400c01d01c1c854091081d820190b510a041d12841140c4055501d08200910700d100c1c4580b14450800d00b03941c84441600c0e1542c21580e41101c6120040100d000000384001c103640d4100c950101c40c00c010a4040e0040c80c0b58400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 34627379 1250 34626129 34626131
    0x2030c15070320120d0e060411090703050601050f18030706170a050103021c060e10060f051c1214030408030402040f020909010509090708100501050a060903080313030c06 75
    0x900503414600c000100305142c800d46a5200700403045010311451561001c031403016030403014071050a540300d24020f02c85651140350001d280003808644a241500899048a005250700c1000c440c1e4a0a070364400e80c45812854284241d14001000902c18007031842c0540545078007042890f00e031000c034002114a40310160881305002d5130354800800411220b0781c00b485000b08400468050340d041e0250714107a17500903201602512000b4030b40803020018107402e0303602c160f070340e1007210b1102d0050254140d002651034000c90003600740800b9540c160440d900040c071a46c000030480809034000706e5080c4155400c42d60708030f11035900406c01c0d180c506050b0003440d1400000400c000411213081e0185002d07500a507403c1143c8440c001c1107004038840c5881485c1d0054298004020790b00d0025420359022200406459500381c0c0d8100440c07400011000c0360f2101d80d00d074801400300e400c081d91000000c022600d40740003810314580f1051240d12001d0100100d01803d030070030317506143c041d12001c88003a43c0b10134 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 34628629 1250 34627379 34627399
    0x403170603070b1801090503060108030313020609030a050606040c0e010206130318120b0c09061207090b070c030215040302060415090f090e100b0a050f130c02061f0f05010c02030c 79
    0x822a010b00c42c4d911030b15030100c0d8403000040382e2424001174680c1038480620082d450354840c0c0c00710a40c96a40c1c881c00700c1c3e000000b04001001900c060291211880c4502c00a05035428030308100320607544440303001d90802c4803054040e886aa400280c25400c00144149003104001c94101118101e1001190890742e80d10100e0016448540e482032403112070040500d94a25100c0004006041c41640c1070f0642c00301003844070300b040c10444c0d11526009051800c101c14010f94400d8001c0a03504140d5041c0c0d00d9001a840820550a0480c0362950b41d043d8800601d19280c00c550010b006c2c3c1c099409050103071140380c041c5210040c000c3d06100040d001e2091740c00f502365901e05080014100d2001403c801b806403d940040304c402501031031884640040c186004a810f140501410348210300c0380d42c0d48588603410b1003441c0010b41c0302c0e96000101543c068206468030740c184e165030301c1c08182040d03c1034003601001c00c040c07048441c0745c3c815100240303800c8452003218000649000c1c00201c1c50341c0d102d00c51a0f = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 34629879 1250 34628629 34628647
    0x3010b0a0f0305010c02160303050a0c06050a06050906060403020d0803130c1212090f06030c02010f06080f15040309030308040311010609020309121908060109080d0206010501170403170603070b 85
    0x41d403074001c03a8450070080c0301011291100300e803190a4000c070080e016060b0f05003031000900030005054609058a0192804041500c0d610117075841907401240c29035560b0b42c01d10040c181454a50713401507040d1a424601481c0d940495400c2080c01d0001c1d11070314001c400700f800c00d500b4a0801c40e400781c00044900c2c2940e203441842081035010074041b1030340802e40c55000c101c5c03809047d41030100e80c6000d205d00a400e14020081c0e010344025880c4074115541d41d400d01886413418440c91015158640081600b4645440c0041c60322100c41500010400d80c43c0030000041e0303005d201207013501e0741840d0900442c2c03614a8280c500307882e15050b080f883e500703252002c00e204150b9405944603600c40b00403180ba14014185034803041c819030361003621203107032070b5052880341e40180050307034000f441032600810302591002000e00700184e200c01a00181c00c464010841503a0200b00311684031011002c542280c14640d502410168070a0101c0400c00e50030070004805545c1800a0001480e4407484682e0b600011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 34631129 1250 34629879 34629899
    0x6130507150509040b03010902220204090906060329010306110c19030f0c0c1712040e06040501050f03030706050417070302010516170a020309010b0411070606080606060f0903010b0a 80
    0xf07000c80d60080b40341c08150805440d05000311a45941c001d031142460101c07502d100c805621402c0b424034500360f000c02002851459911901600f140100c038001811811b621f484405031400500c2c10312a5010602140c0c81815501201411240e02880016024a1404c68500c0a000d64502c20b2014001c0d454080200b41c02c049034003900920030745d2140e20040c0410010742d43d1600f034602c0580861392000041c0700d020b21501c543c04d40c920503030b400c9402c105c810401529465100760071500c0403044500a222990a06010351405010304031200d400c048440801b090b560700404030041c00d0142c5541c040b800380409841525001140700302001d030303a103030f041c10068040c20083c2c0340c5428032641d0700c40c8814075500c50003c000e451004000051026203c1e141781c680650000b50516841e5580e661b2070410700d540b82d10070b08072800c6d81d1103941600c074090740c180b910441c0c1641c0c1c028005a0022410402e245e59200122003006011240c0d5644a02205010900500c00c0c0162030360000000380c0f010499000c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 34632379 1250 34631129 34631137
    0xe070f090209100201020c0d0507060e03040b0705060a0b010c0809010c14032107021c050c030307090e070c020907030207030504120c0320030a03050a031e0e010e03040503061305071505 81
    0xea5a245443c0d155103000ca00f00d214030030680035240c00120000350b00ba84944010b200c1140140720100d03403040b8410000341581d0056005002040000544a08001c82448099070096034002d04010340140380c4000303000c90601c204001d143e0400001c0134002c503030060020340e01c030a40000001c0c0343c03000c240820380d940ba13200d0144020a19001441c1154112038800524071030b0b921940a403010003004403940480c182c0300480c3c0030507c60700303104e0039881c10410000f444c4100080c0d40d40703410311450031400c048140c0e1b01400d1002001408500e40002d40c84008840c0d03001511454010399541c40e80c2001c5a09000326000b140b111034001100c03909220741c406c0140282d0b40601405281450721040c0c180281d922402417523019041400100086400b86c3e0107024181028100840c41030010405a180556060140c041581d40da40610005041c00d110b106047c0301e07210020351034a401e00c800680d0700c8200500c0c134045440380b1020501006000e00a0800030720305584001101170120381d0103441608 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 34633629 1250 34632379 34632397
    0x30a0e010f0b0310020405060f0c070b0d0b01170f01030b060118080703030201230106080a020d021204030210021305040e0f030304060204030b0a0b060703030906020c0f03040e0a020301050a090e070f0902 89
    0x802c0310751301851103c1e1403080b9001c5560061004d031902241403000700c1d03190088142c0300c0860003522000500704044078010604811035207000980700d043d01002408900010780600c600c1c3c480641001905c426044040d81929001204a036945c0c2d41c1400403030f405541c50b402d445621900035800603411000281481c180e91003500203202e040007201c0c85480764540300002c8007003451780344010440140200e0b16260031007240c0328090300d4940d40142e15010b0340c2c882c0ca02d412482e4601020002031581c14408104103690f40407042d80350070031582d2582d140c001140a038a1145681c1e11030207035880d40400c8010106c030383c1c13181503e0300c0b031909040c000c00a4020b40f000b40c840c20001c600245840c2124800c243c2e4480d00208054200515a20114000c00e81440215a12a8200500b0003181001c002e0301000ba046ca400440d0307140e040480c3d0b015a0f48001d065050101c0c01400103100d00c0d900c0c55031090a4900c1d520000500040340228103240c4005603000f001d00920f8500b0200c0c88a02540040008213 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 34634879 1250 34633629 34633633
    0x60f0914060102010507050a031a091303020106080f0d030b031e0d0f05092d060c010903020f010b030606060a020703060203070c03030b10020d05070204022106030706091505030a0e010f0b03 83
    0x541d40c0d1005a00ba61801c6410f940041e41c100150541c1501a0b40940d03000c1c1c0c1b40500c0c0c0d4600038001e8002c01e40701e80041d10380c0328014100e90000c02c109982400340f40c003c1c20300c04020b450f54403800d801465407020607542c001d05045c0c480d00c0019003510700f00724860501120044070001403600c1c0c00b420f51521028460000054001000802034501440031036002d49400b400d19044180f1100307a0502010218095400c6100145103019a81da1080040c10f04420b4003400003d074400319241c06031818402d00704404841e4108005d68807156000304217142d2044007518260794071134078030008034102803a5801c01040d10344003100b0301c416150301c0040380030101e2003520200145900002040703190a15090b80800507809000b036584500e00c260080d00300544060405420300701c44600a072203445d52503800c41564014901040030320315081240700010083c509081c88614200488040300c4040c1001e440281b1a0002c007040c1310406580c07140b00100346680c001c009007070491906074040d0411201c0c0324424 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 34636129 1250 34634879 34634881
    0xc05040806010b0901090303030203070c052e05010305070b070312020307020115080120090d08030a021e0301060f030203070905040e060712060608130f1502031b032404060f0914 78
    0xd50410340499480450503107501b551545199011000307540000c0c00c41e0301b084070700340038003001507002c018800e8040480c1e030005864000700d411501000c840d42c0c00d401500b5081000400c041403000c220f60064a4018081c03d9172040141030035103290101e000c60829031840001003045083d81035104012000e4091a84a4020383d5000c8c142e003a1101d1300c212401c3c00c50440758943c00131155000500c81e100c000303031020810303071001e403612040e54200b1208040e07501d40004141c01c14851401000440c404031010681c210750521400a0103080d03000044011305600001285003580241610001018003d00034009001a00340194442c0d80c1134400c0b001140030f99520714080003490241c0016560a070381d810f9466030f1003910b10940303100005402d48201503c03440400108042e040002e9181d50000344c0075a40341044444c0f664446544203c20702128800c1c814800b41c0b58a184030480790b03178940078113001205881c40011f00203142c0e5a10007a4008284000081c00c0d07a1aa0004044004044800802 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 34637379 1250 34636129 34636139
    0x2010c0509030c01030c020f0f060a0b0307060c0308060d080706021b011802060304020a080616021203010501141c020a0f020105060f09061302040803130e0702070608150d05010c0504080601 83
    0x185024060307580754140c00c03404a00c4110b510030f03400b000094031705104481d007402402c2201810149100800f00301504418100810481c49008003402c185055006045591922070010021440604010104403429020034030595a03c294210fa15411116a0b40d0b141d8140c80c05100a602144d207451502c1040804007203070050600c1a5003518000d543e81c0200c0e21100e40c2085459031004000702c0c3d121100d8500801c10076810000244220181021104541015103000e03140540c00001e064000300d003080184807030707640060105244c1c001d8004040d1a4400d1000e241c120700400070441d01410310201c1c0710b102082d0300490108506d810354000b00b1064a40a00384500410480d54141c0c11002c0a0041565401c1000d120a06000c145000500b0300c0e40703c8180d03905690003103400107040360380040305200c032960a0036075941044180c0010b21406141080141403110000d00020340242c403821030140c40c4c0c640014a0749050342c854004c00865000c1503028000307030494041d6a099118070000891 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 34638629 1250 34637379 34637387
    0x20117010e070e030102120901150806090c0409110d030801060908010203060303070f0f060c02070303120507020a060b03190b1b030405060c0d110307030f050703111b011805070602010c 81
    0x305031200c0020550855440c08810f440b100700c2d4020082d0199420072401c404c80c9844d801c26401031444100104a905c00c104640c0c0058106410a40c0300d03070408800c0c4150080b0015518a00c60030940f00400e15444609020b02c104101009040c0c02c041184501c10030113902002980c1a90300300e80301c032060943caa6404a0803400116851501a8420407040b804100244140401b00e03108204120720940c860362503006460000b0881d10159001400a008240d088884e90034030002910080106142541c0020368030075031668050251a5107144004003910b05124000d10908108803100429010349050409500304840d85c00261115240c01007009072032008a85c01583c0100c010700c060b44a01d410484076600024020001d00d58440881c01240c44000242d4410556a140054a81c0200710715005940b0000e14000405150696840390000b4180c203845694901c1d000401d030403500305507000d0042207207541d480010400d0207010740800c40001241790681e041340d4002e00500b07504d0f84040e6 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 34639879 1250 34638629 34638631
    0x90112110f0f030703060b100c0506070e01052101080d110703141006030602031512100906020405031903110304030804052403090d0206090c0607080c0102071e020117 73
    0x140514202586044280751a5564441507000280480404030460340042c2c42c2c458103074411503c054480d03422104c94030f06050b00b030701d0420450411004000701903a50b0b0741c075200c00901d013505005420b0000412a4418415103503880c030240d0036078086854486103111007100074030498403d4400c61032068815440b0320421950014880014030f2150b0079a9a18441a4108481120644102c603003100403e2101d000d400300441c042ea0006940c3d061034220046a04410104c2c2c03401805040c41c1c400103000001041c01060b120200c001070b040080340b5180020f8800c1d50310840c0e261080494030b20010901c9040110407130b1098036400b001c01c550200403a202c2c0664400644804d0081c00104490705001c1c0e00b054048901c10840610070320270100310b1485d6003041d1f69031038655104d901031340e009a4042201c203801c50300c4107000301103400c00c00000400510039050024800800803402e141e079031100750156240c0360b80c0044d00300003203072064440d000480f10101c0c0607400500c185800b0b00d40e03d81a08546 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 34641129 1250 34639879 34639883
    0x60603200a02070e0c09040f020912071a0901120504030206061806010504090c0c0f0b0a0b01020a0f02060a20010c140705070611030d0203010306020403030f050a02030a0f0c061a090112 81
    0x103000158a00711408104d100700809440c102001042082042ea40da4420207484d0b60403140c00503101c80c00c2509100141d14150503000540c0d002c11024400c0f442c640b40320302d0000880006041c2d91b11380040c0101c0e0811644101c0c440c070642042e0610040640104000341b08442c03e8602000312034140c04801c0c4801c0c4151505070109000308030921201e045500180b8240c12541010000f119803030b5101e82c0910060b00b4240c40c103020640a01000106500407201c1d80740c1300348014101c0035550344500c0342644440318020f21400e800102e42c0e50440c0681161a10702c48101c0c002400746081c001070380c0c00780070400312000000781c02590926140d8488410365110a4205004250a5007805026220364034102d640c1d02d1144828481d00e12050005d00042d07010318814000561034030300d1880d020300001020b096001c00e001003445004802980001641d11000d03051030404400c4a411380143d07034a88043e50f001e44400c0c1001044403c8440c50b210501002c00240c64020302a1707650b0440000c031040b80c47c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 34642379 1250 34641129 34641133
    0x2090609011a070c1d01060906090305030d150b0d090b0a0504030e0103150b0a03020d060509010e130215030a0213050105040602150c0c1606030f2003150301060603200a02 75
    0x40100b0030002d09010b0320610388142d8919900c1911040c103120131502100743d03c0e80c501424070060105a501c207007014010708450400c50340362411030f80c0f4641c890113510b41d80814036985540310050840c2d110403d000800e82c144203144d4074104080d800300a0417012405480784d50341800130425034041880740a00ca9034040e5951611040c0303503001100640a0048030050388482c0f030350045060381c840e0008110310951510010380d6640e04440c0302c001d95101d03610a6100744042001084510014010340794040b0202e01c0358031001d44d552002419050408640940600c000300401c19035040b2503004000b0a4081d080c40388009954000454a030712545c0a0800160490b45811280b200301807081500043c104198500700f0705100e080514120b00d40c40120510050824201f00d103035018481d040000003944070034410f49010344000c1080300d5900c0341c01044908000006400c103d10300140c03850050b002002840503035680d4200070301911801c05e0b6150301102e005000160055484101d030705040f10750700 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 34643629 1250 34642379 34642409
    0x70b0105060307031d1e010b010806010507050109050102030406060503100605030c0f01031407020102120a02040302060405060903010b04060312090b0715110d09080a0f020c030c0907030209030a0f0209060901 91
    0x828032503142c001a1464090507102d103a402c440d03620304184c2d44d4082100c8401007031820031040058040c1c1c0c0707a02c0301c0c82c040c0b640b41000d20303507441c0d0f4001c2ca0f860740803900f806d0065030354400b803421034010000d42c840500194804401d0000708031854000d00200d442c12002c403242c05200540340b1040ba80e051107226032540c00544102e5642c20718907040a82494141800900035a160a000e0313286002200c0d48130050358005a01e425243c01d84d0341c1caa421440c210b8086007801c0c115800300390b65124501406101c0c060106600480741d509401c54101420080c05c203110303655403464140c2040316840c03035850214a0241c00070a409441c1c000380e81d0341a40000100007540c4080134504d00a21011040a1450100f00500641c1320b5090042c24000b40c400d081c140da54200544000301605c079030100c40d10854110501149080e6000039480442d003e049840302c400d6103403020250024131543c05281d0709030003094084000e000401048a08071402500c000c00c00365940002c100308448240600040c40110344 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 34644879 1250 34643629 34643639
    0x3140610030b090f030d0207060507081603050a0204170f010b0d0308130204110a02030c01110a0c060c0e13150b040e0408030c070b0123060c0d12140103050a17070b01 73
    0x602d806420405000070b9459401c505080750707085a000e01c2c800105203800203003000421843d44030307140d8003a03118506040b140c02c110302120a400300c0d05c9405401c00d0b8448020030f8149030164101d80051242c4c00c50b503a66010141840d5845460001c00302066510b8214047e049007010490000c142c2c0c4d0550303508186560b41028120b44a0000c80f081ea041952669a1b40c80c899002c401880050566001503071118800c4041509640b03152501006202042c04170f00796040e0000000c107412980f02c8408aa07101401500716076800202c0421580004038840c0410303c609950b00848600b00400019101591924407103500352003184604c00c8406507000014000ca0050f070302030f42d004a0060b21441c50024191107407512a42c007a04406807100015640c1d518045000c1d402c01c144144c1a5422800e180d00007a12030380705c0e014890a0802e006a030700c0b44011000007544520302c0e4031600007074810296108d09189540d0241203900321006108113501d100c284080c5030a07180016802005281c19a00308 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 34646129 1250 34644879 34644893
    0x302090a09090609060507080a0c02010b1011160f03060b09130807110a17010c030902010518060708070327180c050903010f0222050d0b060109030803010905010314061003 75
    0x1103801075a565548131900310015460340140c0c3e001d112159140b0400c0c1c202032980e42c0031124030a0385007040d60b140001405540e2104c2150040c0d0480c0340c20031400301c6000000c04c1d41441200e00d0754221039204d00c0f0002c00c0a882079001e550589004010801c468085c01047c001205000d4079a03d00f0101d48001440020745607070020000d0742e1042207065095802d101c04295502e00681001010304641c2100e2204018240301d610008465880c05110040c06074001810030f00c28101981001e03641c90000366240d444250031030300d11076484058141c0c0e038107003820020f09008601580c00f04180c0d0f4464142c60408250f421002603035860200c41c407400f040042d11500401c40107c15409201c014855815155400c0c49030b01540b8004840c05641d83c44151140340c640c2111500103010741d24022001d0009807210709580c1c940300e6000390070300c10540300c0c0c1006a40e21031203907000a04030302c0b0000c00801c80c0c88407078005d02e04884c8200341c0702c028140045800343e101c0ca01223520022080d40100204045a0781c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 34647379 1250 34646129 34646141
    0xc0d02011e02031e0a0b0f0d03120f021b031909060f08060f030a030905190311060d1401030c0501020d03020301081f2306090c040503071509050d030c020307060302090a09 75
    0x421040e20722400030b82c00101c10320144c02c9800000d0780355034090302e000c01d05004454017035546080f10052800e40b22075401820007166900e148403150b50b91a5108288040d580c105d5210004190041d0414000c3c1e401d030035035a038491950214882c00076170400c1d2889008007441e1080c2e6002d0340b540d00221900c0c88080302c02c84001001d10b940020007464084040c0c800380600c031034250280e40c80c0b03c2424245001d20009010f140700580030083c1e0903100300003003400d1800c0c84640000403180d09036100d410400b501c0c007501141d840b9000b4100000300000c100043c80090b1021a2000e03000d86050400c0702c3c90179800c83c04248a004a0380c0c01110800c1004200406e40c00c0281c001c00380002000304451145520103016112034580c0e000f070080038030255241410306603038006100c2d0744082c6480e0030f14010075210710080c07017032806a08000041548007401012048003820700501804480c40003414020a080600c110a0b4080e000f502c0c404640300303200c3d008039401d10b8005805041d119191540000003003034 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 34648629 1250 34647379 34647391
    0x9030a080304062c0c030c0604030204050921030106032702040519050c0c1612081804050a05040b16090611010e010204060302040f09050f0103020d110a0801020c0d02011e0203 77
    0x154426000e040b009800d240c000001091008030111021504c801c545480d80001c5400d02c40e0b03001c55101c20180e07440300d04880559605039404106030b01c480300c58070f24009408104259400c0c80a010a05c10078480020350704071583c96500340b1040c1040d1320303c1400e101d04030030750403564115078400c0350250419401c00c0d50480d128082c42c00b400220400004115403007a254084420030020341184400401c01c030000f90f024040725450348251030f0018441c54038403489002040e4400108202d20720a48448000401050240c400d02452500e13924100040c0b508071404c5485182843c0880d0140d0040f5a030710307500070100c0d2250f46035241480426217018440300d0110403036649030b042d02880d603c0c003070020300003c0ca440c0e100907840d903080000c443e0340e004254204e80070980c034010811a110340c01c55045030440e44c0684041402c0c40403810321002c0d550b01c00d208141c20030000302c000140e001c1c0541c004d20108040506807110400049030880c26601c80e180c00c0d06003c100d08c0840d4503c078425900442d0800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 34649879 1250 34648629 34648631
    0xa1e080f2205030a0f090b03161808030d111614010b0402120f0c1201180207021903031103040e1b0c0a0f030306060908030a11071a040504060b09030a08030406 70
    0x416401c0d881d14159500d00300880d80354001280f80c108183d009035410182104904144c44201d0600805c03814901005105400d007030840d0300845111401425441c030b40041d6180c0d40052079444105881d680e0f0b001c3c1e44030800c028a0303d650034075000c480340b01380c2d108002c94800212088285803501c258100c1c440700c2c0403c09550794175a8011541c2c0e07e100800d0482a0751038811481e01e4411350a00170b0b1800200300c0800070740204040c0880200e144a81070645580340c00c5054520114441480207010300c0170001c0d0402070303020014071801d1614524000702c034880d5454481100312034900b03030340302c2c007443c400e214110b250f84011650340c920000c44640c4100541214030305180c2d1070744400c4d00e800020b500c00d0301c860b583c8070136610a060f41406128040d0603181440030000b85050241613507031250f00c40725020840c82c10a40c1c0200101401032034000c0041c0110120074100c020b07010b10b4198000c0c401c0d68401d9181c8100080c3d02c101d40c000b030301c211400048c080c001a44464071220344551005004071026 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 34651129 1250 34649879 34649911
    0x40b0a11070909060e0f01050402101107050a0617071103041a0d092009010302010813060905010203010f0504180804062303040602090102010509070305060118060b0a050a1e080f 78
    0xb000c020321440c40900e010384004141c1c030000700d5545050412841340100036074103220800016840e507048410b00e0300803d00c1c0041c100c82a82140314100021a0460b076880142d0740c0340043d02c15072041e1000030a5201890042e030700e8a54080a0341c001da0582589501900280b200b00455241049420b407584580c0036441d10704414003000400f1940c0c000340880b06244a500c0008081c00ba9030350680500c00300782e6003000c2a5040d50000b03007001400914880e01e407080815280100301d000e030441c421169111000395101d50f15651052006040d5000d81401285801001c2120100d042c518060f900d40118445140034204101204c10414101d1511404414003070310100d001100030080d446a40105e800580b115600000242910000381034080380342e0040405201052001c1480d80c1100c8580701320320b121800007070480300509480d600141c94003402050f41c0c0d58036600030300209811760855a03000640390300c82c0019204506540c3c8451b00150786c0d600019103210103080141c1e040f1001c00b04002203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 34652379 1250 34651129 34651139
    0x130213090903020120040807030807060b09010303080627070309030903051f06050301090c0603020c0c0406170d050307020c0f0409050a030c02030105010902040506070204020a11070f0317040b0a1107 87
    0x103860341d0388000c40043c0c2d550703416400003840d07014010025800408100780740501d0080002d5640c401400041c00040000690904018142e8003c081d03800010382914030640e901e040c00b030200e000841d10310f4003d400c15803520400c003401c81c694190040c120020100d80d602d5402c4124001d00e100002141072000e020f90210101c0c0040009000c003c8101540c840e12050720280c110903030b400c552286010781c5c1406003100004039030440d03107001e81d5000e00c0c005881e403030310001ea540303003070400030b610798002d4a8010041440c644036650360288895940c12500b803007802000860b00c600c8200d80c0795005170044070207145140b07001d6414881900c3e00401c00f28500b801c130340381c1c941000151002140800c04101d404009c50031301b030084c10300500810300218200fa28100100d5130903c1001c07402440346070700251010429016075003a21080b06408111000d054035242d0300c44a50255020580300c05211010390854180020126410344500303000842c1003002045059a0710810624031206501800001042d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 34653629 1250 34652379 34652381
    0x6150503040f11121b01050703050904050613020d0b18070818010906060e0703140903120612030c06041104050705070303020703022506080606030f180109060903080a1a13021309 78
    0x484c5091038400b5003403100442d43c0e500c0c600c00c580d07207034907040c008280032800c0400c0c0c005003544c1d40300d0015a0081070594400c00000c1c09510401030030000c05d0300c0820412003581d8180d00000200d0404d40b1030a08018010a12584050341113541c400090550000a14440078505d1007048041d0010000f10740d407001a51110143c80321a0040d103101c0001c00100701c01d42d0381c540110441120703442d19103030460415000c855102d220f000561a15010220045841034642c0c0700a0030b9082c4071a419a600e07800c04401c6651540d5050764141e0709840000e1102c240d81c6894420300d80a02000e4a40600d00000380d0b4059010350040e49050301917015500c0d4a08003800e00d81000c0c0140c0d541d0a45001907d0704001010300414006044113000f50000c2c02042094407500358140c1d0812601c1624a10464a00d004140035005100c0001c0000d418520104209a041041c083c0500c000742020701014042d030b208000e04040c0d9000e06130b0f011000501440511301c081d03008200040e044029010f080e9203481d0450 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 34654879 1250 34653629 34653649
    0x601050f0d02070f030e0d0302030412150906091a010602030a030506030a0204060b0a11150a0e030c03070b0f06090f04020103020306010221031e01030503070b070e04090606050406150503040f11 85
    0x240e44c01c20070343c81140c02c0550098007802620b4044030040c04841d043e490003540c900842c002e4041505c500e800d54014440101d003007030001c10411b03500b40b048078420301d003601c06050480400c5a100b0304051201da045c0c2c2e403801c2800d0682c3d4090703000b1810448804400c5020301405000030750076000305044c075005030b2102e0040c00d029101d1706a1586e61540352100c001d00d42d40710b0b00341c0c4410035009040440c030800641b1040d03680145c180c94011520401c200350580c11846100c452210328400007a03520100400d10900f1032007118104800d80456650030184003181808a51540190786628009030056019901039a0062418030485010030b0400214810000000c074541013a040c0110800c0b80d010320140c00341101c4600509664615459640c5042e0369004040c001401c030b519042c00200c0315071107a104034040f0b4100030001e01280200b41801801020342e4092140111300b04000855412200b02114484800d5542d0f941c0c599551611200c010700d0100408a6070b0003038030410502c2a542d804d5001d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 34656129 1250 34654879 34654883
    0x6080307030f0e0402071a0402180703240528170114011a0313060f050109140a06050a05120c0306100f120c061b060e0c150906030601050f0d0207 64
    0x240303000c1c0d448003e055080c101103050302c2580100407a00000742e01d9031202800e00f4200b00092825200d52001510b10040c0341180f00000100008000b40f40ba41034208500740100056161001600440ca215014001340642030300071070052300203011490104c1c01c1c0401c51002d00e25492020341c8135040c01c200d100900700d802046039101c0004031842000c090105006014404043c4134400c03c0d00c0282419010043c042d031481c00144111f00d040c411241c211560110b41503c003000250303168038221b4000e103044180461008040d0300000c1b150145071103084141e90000b0501c0c2d505c1d0f440e04040150311950303028050030768043d80310080d01d192820841e05003c2c902803050844070a040c050348001e144880d502c550000d25406501d840884d805441900c2a0b400720714080004200c01014088003103004080240340d280f4020040b9000b040110f401c00c407120084501d0440203ca8940b8050356002c4c2c036819170707804030007080030603010360103800280380c10110507d4890601a00c410a18100d0b0000401 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 34657379 1250 34656129 34656137
    0x60a020c120123060102070605071a250801080705040903030608030d0605270a090f0203060907060e060304170a0912050309010e0409032007080106230a030b06040902040608030703 79
    0x450b403c0c0085072212080d181c01e0020300c0000c01e1511400003550340701c9520500040c0a8006442c0e8180a50881d242610040070319003d0312608000c42e40d04004002107002c2060004c01c401c20030700c102e00c05d4211604aa411a0042c00c90310308081c100401044110401c0f0141551190001000101403004c1d0a026244030400100c1600d400140464120095101d501c01c007804d24207400c80a41d807071a50740d00300315804d400040708901403030b0003000c0b2000c20001035818815182008a1800b00154004c151003140d540c07218800c041e0010300450307010640c4c1c0100000c0000061801080d190400380000b1202d80c070b046010b4a5403030208101d2844840825115030304005002070003940c1080410701c04120030359007003240e00c185480040600f000b8800c04243e140b0841030f2204886410003505014002c3c210081200030f03a42d2039003400c00c90030300c104204900f4074030000c06142d1601d06581c0044030b0300240703010074569400040000414030154104e0348141d0b01c4001041d086400c1025005191194075 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 34658629 1250 34657379 34657391
    0x25080606092d01020f060c03070c110429030d050403060e0c1f080c180906040204051201060509010f050904080c120703030c0806090108120304050307050d080f1f05060a020c1201 78
    0x90601d03825000340d1780d00341d200c40300f0320002554817000c03241c0c4072070940f4016980b2011858604201310301c3c891910b60040c00c0040360842074864000b01009101e801040c101038810640525444134002038124010810611040011170071582010422080b504c2c02c0d10807104040c0005020803000f4100c221882c1082079a203c03082e07400c0620240c010003400441818107541d41d1140c0380403a803c2448030f0088440c10045105501c03560191405400024548070301c003c07041d818180213154511450703200701c00c10800040c1300c80e00700f200b04c02030302d00240c0000c1c0c1c65a02c1d0703200c6103003d034480111800d1301d00c44e403286488800c0140c00680101340c40703a5404203481224090050031408054402d62013424140c0c0100a4840001580440340d8803050a403030322aa5503003000380c2140070347c500c080e00601401959a64146c0d0054101e0300c40c00c102d000080d4251a8561203410512010303032891030001800300f060180c1d1800b10301070720b04850284125140d101504000c034800300e80e030038040360690791548 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 34659879 1250 34658629 34658719
    0x50c031210090f1404110f1309060b0d0209040b0403140f0406032a030b0d020a080c0a09020a050909150301090b16050f040b0a090803122508060609 65
    0xc052040041140b070804d10126684080303d44d04a0800380008111040c0d0381c200c4040c60b02c0d4000480118040141185080c101a0150f80060020040210b40403450b00123484c809142541c00361710840e4018210134607030380e5507540d55880400080e0040c0d042c02032101c280c426802440c2c0041205085003191291124030304070000e41500e15900c081030002903800b06c06591410aa8008403400145142c00715214a800300450050079078030300040d4000e245003102107128000002c8904403184183c03102c2c0e00682d82e07804140207d00840c801000003c1d01008840c00130301d000740d0075981001c1030716607828142e1003540029084400314101212030f060140c04010f1140301d9085010003040d06400d10926041121400e0802403180703024001d65030101040403034036035109200c01c001810300c510840790390301448000259900d0301100e03204680240307001c5d268000b5080700d02010544c41c25880e0302500c0c0d1220010000315402100307907160481e403003c42c01c3d1100d0718250f41240401400c541801c404000c2c00b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 34661129 1250 34659879 34659881
    0x90203130606120506060405100b0301080c181302061e0a030c081308032e08060402030c0105040b030f09010e01090b011e03051e030418020a031409030703050c03121009 74
    0x994030a83c2e40c603500c80d1040700811400720b00c85900c5030f81200c0002d0755655040340e400c1e5079104c9070045112904040000300e02d20a0001d51f10591030401c646c011880c1c2455170441c141d60008032040000983c0b01403400d001424160301805c21580c00d00d1402d02110203100089000c1c1d0881b900c2000000c1e110b840094031150480003007504290341c40d0000c00c0a081c1901d884083c1d00c00949100d8040240c1d40c0644110104000c400d4040301c524558101401d6992101d0340c0c1e1802c065809034428040e0030955000c641c0604100c40031113000360f40303880c1903a0711841c880c0381880c00144050155500c03149043c0e440e10080c07084c0c00b01c01d4400d609102003035051001103422a45100003c0700882048641030011070310000fa1040710503140c102000070700c0c010351038060460081e6808080c4000c108011108040700e01d40180400c40451b0342c007004501010308030380c5403050060ba03400030150820001078020900c01d5000340710850070101128901012042d1480d00c45000b245d038035100c03000b0343c803083c0465801 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 34662379 1250 34661129 34661141
    0x310050303091c050c030708030d11030126010f0f140f070503040b0702030405040c050301060f020d1d04060b0c060412030218012601060906110106030c030206070203070902031306 79
    0x40c0c00030340c1410045030101d42c80c00c24503000100c0745210900c000041140801c00d08001401c040c0c2580c1075960b541a15590b217030402d2001c11030090034503207030744580103044040e00c1c100c45003030500c0400c0ca2541905814001d644134407034600b41d5250013a41c175907429507000c0c070f03000440040000600001010300c03842c000700d40503100c025150110001e00c04500da109050f41c1e080340d00725511111a884480c800e80c80e600c103030742c020341d0810300b0080c03002061500080514101c030700c075440360b8000038039510702281c0350822a003548001c80c50b20080000c00560344a081221110701800010b001c42d00c1701c000c14515001540c07030b09400d511080402c42004211803142c3c034881d1007400d0660410a0b410307564501903252512090401c52210368500c200a48c000c0100400c480700300b0b4010710b558482748014214480c6004540c04030ba500785032040794050522814007100d800211104002e425039080100700ea11031881a40c0c14030074140c01144d1400a4802180581c0380d400c85c0c0014802189020310503209 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 34663629 1250 34662379 34662389
    0xd15050103060b16020418060f02071202062701060b07050708071707060c0609150b010e0303040b040911070203031603120b0f0108040519032102030907090c1e050310 73
    0x902480b040440c080c95031340c005049a812a40812491003040c04200b40c0b20401901805aa04020384248800542d50041c0301c0c103405080100d12892954000360381d80d410580e283e01600250000b11425120514891420071031400004682d035550380e4034000050b00700200c190f6054014580c10407004008105420041170131014110b03008180c40342460b114441ea204400c24040032903018810442039034015082107610010203040003000c080c0304402040c4410201e070101d181c0c021030581528001040d00d048580c0040118607050600d624680500342c0007200e0401c1440a00a800050390300780040e00351052a02d40c440c4003043c05080007004030b050000d0803c800c52070000a0a03003038036810b4841c41503003400e0074820440c0c1c541d403602c2480d2800030708000c1d409074940c40390001015030024108070201c0c0c80b80c0462000340b00e0042d16000701c5c807094601d8802903105480070810203807950842c6001d2000303400c0208104650240f0b1940103110f41c010080000c900104220309681c401c500c0e42c7c00f40c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 34664879 1250 34663629 34663649
    0x10090506030a0f030c0209090f0c011d0103110c07080f10020403110f0d12020d0809010e1c0302040801060e0105030f070509071b08070807150e190303020d1505010306 73
    0x2003414800320742c0360040e851010f4110720031030540c03074189405050382e210607950103042c1c0b00315454822900c94030b41001032001d003080c0c051002c0c020710940c85090030704c0101522030f010242214000d0015001010394040f001c6c2d0112040c0021881d88c2014400e80c03000b40411006054200c0c4803140003803e101c04c3d01c0344008558810311042c004100e041112150f1443c1c143c1e0034a121000340000151968001c5000800d00d80d041c0344c107207c0c801d80c0070529038540170058433864903944891880ca401e071000c40204446607403080d00c51a10502400c511102e180145080062426840b44942401e50702a508580020745c01d00c0010051070400f08011f0074811f010501520700355091000180c041c1d10080c0195080111201105022081c80007144080d280d208099690b10012854540340c15048242c4c00e590040c4c2003420303280e80800c90700a084044411502800480c0c81d00300f100e0501c0d01c090030080d41015404e0240460941c02485003003858681d00590425035403501c0001001c4d00c41d10340041d00c01e0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 34666129 1250 34664879 34664881
    0x100203160503010f0b0a020102190509040b010e09060405061903030c0c0504021e030c09060706050411090403050406050310270f0209010206011406160309031101050c0a151e05100905 80
    0x550000f213151042e1791205403125a2000700e20380403406030003276000a2110300c003080e1401d125660044018400c80005480900035007418200642d00d4425001409130442c040b440064002d20305070b84420b0380000014001403142101800d40d6180b02d442d034204030041890240124103129282c115a00100011281980f92510100760b03910b602c20391600511118002101244913840e5010544030204c5014100329101d0f400f40c2402000392100342e8084ea4000c12072001e8419034280110154411601a00c819141038070f001d80071a080e900081c03502894000c1483e01140f0660348076841400003501b012001411090b45070120304442101c07a042020394070421130194180d07000f08540c1d0465170f000c1e601d03555228460020608500c141c04042c0601c0c60700559810806412070014000c2c0e074011192030b50a00d440d003006441502c80d16140040f603500c40200280015a42c1c1c0c4000344c44100e080d03002c150300c028503103514001540d9248802000b0b850380200550000150103140041c40113072020b03c21 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 34667379 1250 34666129 34666139
    0x90203060609040e070803072402070203030a0509130e01020315010305070c0b040c0b0a0206190915090c1502010207050c03060105010903030c0602120703060e06010f082710020316050301 82
    0x6101d41030b54a40a151543c5905402d028140150781c002d010b2070707040d00c0d561242454101e071000c2c481343c0082c01b041403044202c05909001d100790b841c89a80035004601d041241202592190031080307116a00c44080c801d0043d0801050103094050040c0e50700144e1241001050441400140400103040601c0c00d03080003c626072003001c42c035065030040006c610b10f4590341450500380e90b99800440d141000010b140c5815031f40001d00611907404a007564000d10190210308003a90340710900a00525007004881200b08000d40c00f60b0003440c032615545030101d998100100e164482c2c283d072180540d5004c942c1b50103021061100031035051085015012030760502c8006404100c9500014040100c81c2034000d0030001e0315411030300c2030204c0b504000c6c410301c0c1081e0024003611241c041c04821182507008580254052a86030401c408543c9860780306540e40b010380d41280e07028640410583c040304008200e50300e020b1081116088414101607070f28030f0a0b10503070750030300d421210201c2044010401004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 34668629 1250 34667379 34667389
    0x16030e0706050d1b0206070807110601050906030f0d0806130b1804030203070c030c0f08010c0c110315010b03040c0503070b030c0702040b100207061202070201050913060b16050709020306 82
    0x5454050500a444103e0500e01030000d1005099222450080c141030840300e50300007804900c01d0721565922010340d614440115914160011800d1312030f440000144800e18200c1c01c0d1544c403400150031152103a4402c07000ca807912215400c1d801c041001c68060040a04201e900c00c00403c03001d0b24203129500e48480454034890b0310600303600c00e00002e0b1000c182010308c01c0c81154111904860a010300d9034803400c010f140c0380014800e0480c030b1041402c00003420901805980b41d00441600d03201c0c0201482c2c1c5034044200035610820368580a2144451280041804401e02038010a4540340e01e0385400c0c58105900402c68020f50310a038003401e020040040600216503112040601c0240c8500c42071003c200544a60544981d0041340001c0400c0c0e40e81d8009204001c4031020356030346034855000d1840000b2845885c0001e40010000c10003402c40c1e0801110051310341c007482000040e201d540d030002c03003440c2d04400411803800c0028410f86040c000c007000050003a245910003140f42d420907000040b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 34669879 1250 34668629 34668643
    0x10804060f060b0301030303061806080a020907050d060602061b07020d03030e0114090a0b0f060f01050f190207030c050102120909090c09070f030e060108150a060306110316030e 78
    0x40c032094942120151600d000d4025070001c00010812988070b584900c0c02074040d040c0760044a01e042c954040d100021003182c043c00e412a110003024020003000e40d000d20521110003881c2c6018400104140880260640701e114000d14107940134004a003800d02200070b202d0140d51598210341e034140848000359566032400d8a40f1a4035040c006000180011444e0240080004001d80354020b039040201c45440400c8418007280b00700301182e146d0352010741030482440b0980300d0030b401c005145407243c115401103005002d44501c0c8010f490625190b000c4161042040e40f5900c001600907070410002c000c2460311500241c1024006024180d1001c101c1e440c1d280103e40f90706115039a5480441c0b0200014401d1203041d1401134884a13030f85c504040c0c06080d0b90540b00003500000c3c606100c3d0b5511901c04210141a00c407030700d0140440e44024007060840c6000a0300008441d50303121000000100d640c400c0c140484003c28407162240b401e0103040c0c0204c0c9007503504074245810081c0c9034445000103c1c5070 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 34671129 1250 34669879 34669883
    0xb0a0e101103010608150307120312050103170d06052e0509060d0f0902030d1e030506061902120a02100b010309050a0204020d0207020a080106080705120a031d090a0f050114010804 79
    0x404056a0740203400740c010000000c2e1b560701802160780c0401e00d00e8801d10205600c5000c3c2d102e0312003000110b4540401c0305d909101c060715141c2280e2400192900220082955034596040881d0054662000408004110301502508a4044403603c4914451039580c00030801c1828003900b4910700310301045003445040401a0340070b980f41d170512100426130740724603a102d40280c11242d00500405010f441c401c00c81103000c078081c0082c90304002803882401807521618021b071845007050b01c40d5070310417219a0700000507000d42c0110145174200c1c85540d00a00f07030712a501d0303005088003001c03580000111020803408a0405051540020100da00010060b010075410b6500580d640440c040745d000030b018800c2e00a501101c00440010b80200542003001075400144c1503980d140ea03075070700b00207020007000304a0718203400186084011a00803108001400c4d400e032102000200480001400514102d5682c00745030b41d0745405410401007485030501501c2d203502d60401590031907002030000c00d4011300c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 34672379 1250 34671129 34671137
    0x1606020c090a020403080c010605010905030a05070306230a0c08011403060708041b080304050f0406050a090b06040506070803071d0622030f030f03050a020306060f0d090b0a0e1011030106 82
    0x20600704280b0742d04803001982c02c40800c6032281079689115002e00014811540007a854a8003c6850f203404641c1c00c178004e40c40030040c035070280b46655007400740696281c0d80708800e48400c2a44202140c4890807449400d490310001a4880c1c1000b014050f41030603006680c0d00486415500741e01d0300d0000303003180c004806040c03400c256540c5140c4044d0901030710038401e100c5105028001500030000014205480b0b00311030740711005880c0c4080c481180c809101d4682d0000902504111000c170b650701418050310060840e40c6040c0e1034202152003640f019404641d07800c000070801101d1544403015001c4206085a9030904003810070008100d401450204200740072041e180c0c2c411140e1510b0301500a5034450014207000c2180d0502070101d01c0740008210100c2e0a2030009090b00f0124821240301c0c0000428040c140341042c940c511f13064200c1280a46182e41d01c0c942c00c80489c1008091a1007036a02100103d1800c003402030041c04e140404000c15900c80c24003000308146444a02540c2c159240c500e4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 34673629 1250 34672379 34672381
    0x703091520012702090c03060a03030f0905031608060a0605061b0708160305061006211d030901030e03030f0103031107030f030201020307091d041b08070807081606020c09 75
    0x281050050200700d400300d00f0802210207414a6141e01e8003549a854000c40d1040e60030b0303980c0132851383c40d44001c03100e444e0301c1125420203000090144a008002ca41c2a14040d0b90207a00ca0002c83c1c43c144251100c0d10383d401401c070301000703100010041c6c261b204440b21700030720149242c200410030706d01030102d08414091801074141003810041200704004c000242c00c45a44124458102e0504040c50000707171003502500300081c98030303100e80d814082181c0155032807801f00b0840301041610300d000b03c03403801c44040e113890103c5a84082c0000000403100300030051580d81d90341d4000502200ca00030540025500709004010544400f02c240c00e044a41500b0200e03185101800f071603080039240c0d04001c05c0d0441000c1910705240c2d05501070351007400d0f9601c0300f0007010b403030b0b9080506201000711081d185819200004001880b03000803a80700b083d002e60411503250b11132020781d09090280e003001e2169440b02408018001003000b250344106a4490454403290901000039105d90802079258000d03511030b0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 34674879 1250 34673629 34673687
    0x6080d0e1e040f02070201020c0306040309091a0603040309050405010503010605090a09030203450619030e100906060e0c070b060609040e060708071d0904050c0603010b07030915 78
    0x841d610810303500600400c24202000b000000940207240146c1c0107210f0000204041e0400080c424000c2c4e4141e2100d001d9030b442c10b042440508171880d44031442080c1d9409602850310b400003d5402140b09440d410034045c10901400102e0b20140c1c800c0e40709a05140c4100941e071a989101ca81089255801107110151303414164610b102c2c4a1750700b040c03409080b2610f01c10080c41d00103c102c0740d80c88000642000d581040c030398043c201040090741e10040400106020078480d4111016031b0340ca82c2008928040c407071103101c2c00e00c090400800c0c00640c0300c005c118108502881000301501c00e241114006041030402d00d042e901070074000404c0580014003049065945105030f42c078094004009010208502c00160749800342920028041455000450a80382c020600480e4200e2043d08070b85140040904004808030068010788480c01094038040590b22820002d501920608046640d01c660a18000301a440c05600c0124004240c108610b400c0d68401d41d00080c0e900442540721a039003400c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 34676129 1250 34674879 34674919
    0x130f021206010b1206101b2d06060503030a05040b0c01020f270102060910150905010605040e1302011b0204020c1005220c050111210304020406080d0e 66
    0x40d000500452048600000f10a0b14141c01092800500c44805940d601c980d000c6c0000080002441c6000c02c5401d030f1007944200d40121001c2e550b5000718003c0c8070036129411000e40d040c0c554004901c01c0d900b44008001801a0381c01100d0007000c2c10b030300842c502404030a00070500d0183d03005840c3c0140300010b80b003240702d0094060700d042c001c410f07007d40e43e03c1c0406491865080b4021140c0e81c0402501185141250300110b609403007a06840e01401b54032100e006c100c4010511039040c00d1500400c80c2011030f84011500c1200e02038102a219640c1d03850800c0000101010010701c4902214482c00c00d00c00140da00040084412000c001041044800340c4005000f0f4021541c4d000340034800c540d10180c00c901580c10980c010700c441c400d120148003006242400b80001318601030001d84207480d00300312035445446d089940c00c03214000d039003280ca140707060043c2c0320308070f0700420400355804018041985441d2184000800d2000c00070321701e00b40034a01c040d000030400740340e0b284520a12072000300554a4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 34677379 1250 34676129 34676149
    0x91008010c0207140405240109081005010608010b0703020d0807050910030501031101090b0912010e030a0f08010e1509040501020f070b150411070b060102011506080702010c020303130f02 82
    0x52000240066003a0120080d0303104000d00c61501d006540030040241c3c1e00706840349038000c00c110b48121491045000444400b002c44c0510181008000c5c07030005400b00041c1301308508a00c119402080d20351401400415003281a0001c0801c410204090000030745c001903500507011407420864029a50940c0c01e0b0f5880c020300c040b0a0b0440121440d00300743c203034198401c9051b24403031015064021108001107900410303d004500000904010101c26840c091120f00c4150392654004219205040302503411034101c941c901c0089078035056070b010500d800c58000e03405072007003004034011841c0034403180c10640c00c1c41c42d6041c003070480300000c207007071040c20f404445000320306805090b03480155141400224804607800310b11520b078034048420901d40ba006200e401c00712410228208038094803400a074a5025007810305641d80e446003450b100a840c1e1440c00213001e203031a8403449240400d000b9003914041803202003150030402c2046511304030070030841c4e010307600044080259000c0c1d20114a02000d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 34678629 1250 34677379 34677389
    0x8070e030703020d050f01060609080709050c0d14190b01050909070c0b07050c060603030702030d0f0302071a060103050906041e03052505150405030703080603190312060e060d020910 80
    0x100c0350079038100384a00007940c0d802e1b01c0d404d40000c000c465a54001106d00e80c0c1d4078000c0b10006d4200b808204501d04c417a81019400828801c0d40300d1400c090031000c9000c0f90007041090f00c414950310100000400f202c1c0000c46523442622007400800348040c0001c1081c814441c1851141c590b03000400c60091042c400384038083c3e804902265582070405010744150410000240c40d4070031900007410909001c000e880155501400404525540000c160349150300381c449103007095820700901c0301090080c1d043d0201162130700c0b5081010f04100340014240c40c80105040c425501540512001075107003500f50700c11507030741d07841d5410801da189406ca86a206160f00030841c141e1012207201c0c0c12013451040a0520b21a504443c3c0c1e100320314450010108007128040c20a070424044ca40209010704803031a07000c03100805445080d404900c204008062940341a00000d04c9280d03414840c103064858400a0141c2196803400b80c50321f40001819500c000304000d01411100010507618000c150851000e09 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 34679879 1250 34678629 34678639
    0x80307110a0b010503070f03150e03250b073b130c110d050405040f0e06100302010801050a0b030c07020103020405180901050c030106080a090507090903090509070e0108070e03070302 80
    0x15142d00340040141800c2c02018401c1c0540c00f0009844d40c4078030a0358040f00d52100c08086007285240c0d20301c00605400038099640d0004100009010702c040080501c1c0001080b090007101d42c071401e06100395000100002c0070702140c41c1c0c81d0711000015503043d00c0c11580203a00c40301160416144501c0e03501041c21565044085132401c880c0000094218100592050b92241018031081c1800740c0d4030030340c0341d4068010030000c001c14000ca09040e0080000f09025501c0442c510005503011454100d00701c686421718220128240115a8005c956a00404c000c0790b100d040c1c80c2c2012a08041c0380b1024040001c03c06c00000d084e411079001c2d8055074001d1600900c0604d101006400d1002c40d44003c0b00e901c0101d51809000404002210003070301e0681b640361f81c0d8110680e9032000098000d181420342030b641441902000500800d0030300483d08100c0c46682c994071031500d80030a01c40080c01c080d0580050007000401c56007640d80c00514903078022a0381c58407011000491011030700301b8880c3c0c1c1000e0b402c9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 34681129 1250 34679879 34679893
    0x3100506150f03040b0601020a0c14010e06030103060c030f0e030a050904110307120b0103050f070806010201060305060c090301060504021e180d06020c060603070510050f09040216020a080106030b0408030711 91
    0x2c1c50084001d0341c4613a0080113034540940d60074004985643d04500001d200703e101d55018060354458070105115280103041404a00020a000030096003003640100c41c059162032040044c02d505004201c1102106c070010301411428948075a01d0780a81e00c110001c2000c003140349010b542e10358112a4261800c220b40030f42d43d0410ba28000e21004c14a41d882e0340e100d003800d102004a500c640f080d00c3c4a41c2485001c2c4000e03446081d42214800c4002d0603c504540d200e42010000c600144211405544403407590b41d0b55032000003d042c2074881561109103d184184040080900300c40c0c580b40c100303000c001e80070380d940403001c00003990300144170016074229108034a010704201c801c1d03004040c0b1350030140c1120041e68540003099540e9403580201d6400060001c0501d1038680500043c11404181c41d602c3c900340400080804c0898100c02040d0071002c418040da002542031810b004006040900000d0000f03500710f494051400d54003030001040500e001000800d5948a401c45a4030640c1a03402d442c42 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 34682379 1250 34681129 34681147
    0x10b010c15180215030105181e0403020a0c060305100801050405030d051305010606050702010e0306060112020d020d0905030a1e2102090301051f1202030a060209030c06130303080a0203060310050615 87
    0x12542003406240e000f80b102303035924610b000e4004d441030710541d02c000079640b20b846030340000548810003030001c400758810700c110400007c00704101c88014004075075001480d271810a28409420200d6404140360f649007205010225002000f241c4503e014248041010b131140b007a003580418280d1000340855181c03c1d4041070300c0e5032103401000380c203000740e031200030054503141050348505003945c010b404640c0320790030745030f0a030341d10380280c0129000e0090040c00c100160b01d4401c15160303803050880701e030b8100140c0860328640040300072111000101490300c00500500c400b50444020040520441c8a040d80700200541c090301140d00d252400760003840103081c643d101c1c0140e02c4a40d0008805001484008a030080a650307100a465800500030074040c0401c1d1103050003503000421007a0140100200c16509480700310040a820203c00300c80c4e0140d074914200100802c0000d0440300407070380104180b02250380c0009042d0b44040f0318240001c0c090f2607030310015240c0c400e250269001050f022502d81d40f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 34683629 1250 34682379 34682419
    0x10b0a08040638010206061c020103090309080a1103100c0903030513030606090b030c0301020a210603140a06050604060308030c130e09031b01050106080f13060518010b010c151802 79
    0x78001100780c08446c40d54898008000c8403561510200904e000003200c1034015611a802500c002d5000f41001840c8646403600c4504002904e0741c150390450304491414210b08041004d460750f0b0007030180400000642d560000e00c00f074841d200240400901181030903012003483e40c400019540402c2c104800c1d0350b1010309401030840f050381c0e40e11901851589158500701802200d10040d00c40d038849256514464665001c0e98240e44400311041c1c0d14600440000c9041010102c1e140440d0010010f90045280090030b81e400286494040d40c00c0503410030003c0c0362401030b280c2102c04000c0a50302d070b0001d0b01200030004c4032a4090b0032a00c4505043c400b80d036102100500110500035103246502c5600c0001500340e0f2020302c5000d0001d0203400028086c0075071110500d420108203848182900b0b49030b00d81178281c0b002030f182c1e628811461581c0d909040002d20401038496001e0a06002ca011151501401410f000c880284aa5150401102c0145400030030b80185a4010413a074010700c54580e10701 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 34684879 1250 34683629 34683731
    0x5070903120801240c080a020303011e1202040c0309050601140301060906080703080703140a0905040501080105060306040209100302030709020403060501080708070b0f04180f05010b0a080406 84
    0x341d404144000c003050007900c14550541a10803c1072a94500d600751004030000b04a0300000e0002c201000103900c0001c1c5101e030041c48003000981c001d50b04ca50511203042d444040300f01500081c0c01d001300080100030310390384c1c4900e107954040b60009035411141c00d0a8002e03116101008100d0b0040100110751003241580b9202d50290540080001d9515071000b001140c60714001c8a010740d2000c3e9042002a0301c80005000c001e2092408a80010008000d055603411190024012030b800a409000608040c803409004100f01002401075080c60750203c2d03100d54001d40041d004e0449000050a01014140c14030021a4060f08440d07006940ea11180025002404100c84803400d1000014040c00c1c006102130550340100c0c0507010845c6003550581030355010400e84d034114030042c0400142c0b1100b004045420300dd1003000400d0348109142001708440c4141c006001d114000d00190710f540d640800c04c1a4440d500440005540c40c0d500210000800c2000140c0c1190450304501d011410442c6502c1c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 34686129 1250 34684879 34684883
    0xd0501030b0c160b0601090f140118030809010c0c050d080913060e010e0a060b07050102091201050705091203040e100e0c032503110d090b01050d080a050703021005070903 75
    0x807004544900b001c2003440d02c40d41181200c1e02c1d1002041e4004a8952011280c02c4501410301100d01075440c0c600c02120769155002c5020b088003e4000106545c11088161000e50f152135601401411941c4d08940b80c020358554504010218004204221010700d00c280605801007079100b5030003203441c3c00d82d02584174184060140840000c4078800030f000d401070f04182c4d551000c0b007007003503800c129030840444401081404915100d410006207502040010b010041c002e80025940d610890f05000200380d032800004076680c90541041a0598132206030341d1900c6044502030f04030910074080718603500880d0441d00c2d00c1c0034030314180301404405520800895568002080050b42e071303c050103130709000881e151b442138a4118000c209a003160714600e03203880520704001030340c440780d54103024444d000400c00c0c40070300d540d489a0009102402e88140d0040000312000002e0502c0c42d03807420742d240212041401401400b181c1001014004d22a2040a600c1d15504111601d07181e400108645007034401 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 34687379 1250 34686129 34686143
    0x90b01180b131d061c0b010e010305012009060a02010603060c0810060807050f071a0a051e01030c0302010305040c030b0907060e010e03072105030c25120201180b0d050103 75
    0x1050740102080103844000d00c8081546969020b00388900e011751700c2c40e03180418030446000e40000d480000101d010784440c40c1041c07a01c4d81103160140c00c54030f90540c1962001035144820098907041c40c03c4a020344010344407213480e00c11880042c0c0c050901c5410040c8240d00703204980702c9182e0700c00700c1e4920524403010700081e02980c9903410f0b204504151861030005070308005c0d1454a80688004041c1700784100458682012200d004c1640c200c0259000320419840780107101d0890003008500c4062800442c45c0b501c0341d407459a80300c1c81d21440307100080c14076449400040520010940740e0009541101d111203491810109007529120036004141c040303241c81e00811f109504c902141c07003a806000e001801c3d81c1d81007081c070158202c0451204a410300780503001e500000e4051019001c4100008001c0400c0c15150305640300704002e1949a07200000081c4c800c01c121803071203680000c0f02d502070030a1922a0070207001c85140380c1e056080301402c803a0000e85000d42d050305509c03041c1243d001d035070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 34688629 1250 34687379 34687417
    0x20d0507090b040b03010504020702060c19120f020601030f03020309130615030203060d020d050709180210020d08040311032503020606040203130303020d0b0a15020c0103090c090b01180b 82
    0x300003001070180d13000d1501845005d1005100504040d80245015400200700b142494080d07010a45400c5400020758070342800c00c1d61400130082d25400e00c40441046003070007078400c143e01d90001e544600512016000c0c0c1c160301499001d150081c4121211088041c20707040b01d600b90582c00a0142001d4422404990650015041300b540310344207890060340700400f1404e05c40d006400b000300e001c0318071000707403041d002d6080c0000e4502000c5c4113210f52124020ae00444402045c01008005411704080c001035410500c5411a1143d12a110640c00b552600b0583c50b100054440c803440c40c000c8000500e0102c4000461401340701003a8406d00c1118429800c4880c6992441c05020903404241d94400c84d4860740c001034800030303000b070b0050218a0480c034000035100c42d540e40000c080203425808001d101110952008015a0510080c88061001c0c01d0502014659076154400090030b40b00d1501c0c40d03a9140d441d0b104c10b0384191241d8005640000c0700c0c150007511414903d220380c0c02040000400070700c40c5 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 34689879 1250 34688629 34688639
    0x20717010501050907030906060905010611010609050403020307030f02070b0f030115090506091c0c03060b01020609030c070302091317130609030203030301050405040c03060606021e1506060c0a06020d050709 91
    0x101899060720b8025020b003540d17440e8244140d01809081d24125641030b00e580d4081481e0085102d554024036580d62a42030303600942e2842402c40c0c075160424030350346003002c0c100408241c0000c12640c0b80f039450324000b410111042c0b412410541241c001055011002420294820304c44000c1c50503200030345043c15070300c42c2140342901c0741811031023415008078060215031031515101129007031000900c142e052141506941c0c030143c50100d034208898aa6031030560701815681004442d40c0407203258021850700003160303002c46e07403040a840024030814803400000e817401691172151300300c25402258040d40401c3c02c030340c05056410128402d1040c0043c82c40c0000c1407403085042d5011071703401401961841c2d0820003400003515006006403170042c00e801000000420030b01c00c4900601c140da0281c1090310300381c410001c981030002000700565000042c5d40088680790504980c200e2002c13101c0d00d50b121005564103003031012206010f015144081901d101c400c6440d08120b00c030364956680e82c04603a84071 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 34691129 1250 34689879 34689881
    0x70209010501210507110f0a03020607020303010315050402010c080a0809190308010e100302030f0d03050a020309030d05040311010906091505402303090d02060f130602071701 77
    0x71401c00c1c038040e1140503143e1140c1107582d100b250001110f1404900500000100624046100318202c1c0f49500402c055000c2c90790500c8400d07044241c0b88043d5145500d5500d41c1e54a051014140c4203a80c2e60b43c6000c9011603000e80d5540041560203041e16032140071160010f01484021942c40c2d13404e004403c0e42030641e98513400c0c04081550b04d03864942459003001507041100c84d00400c1c0009400c0c5000002c405aa01000000c0c580512140105a071544d03415000b02074030000303401d69030450f00510070704c0401c0402000b561080040032000280ca65264201200c18074900e1180c0352130740d460300081c9010302000d5003002540354098522040c1d1800b02d0140107040b074804035440c031403200c0700d001000c20403000b401c10301c4007100e405020344c0e4216900748482d0b8030488080f401100d07144005034228050b056140740ca00d400c0500c07400514204004c10002c1440700800c0d140c0203116210002d2803003940da1001050341c034920b00d2510b04090b0a621560080e660f01c169002d8000c0380030303603851803032045481 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 34692379 1250 34691129 34691147
    0x20303070c0b06031204080d030c0801060f0c0312050a0f050105030a08122511190b06040b060c06090706110d09030b040311151008030304050a02010804080d0908070209010501 77
    0x110750344141d810507458a03030210010340604015854051490340c1101c4a0021001d131010f004050040d1140b00101c500c090100c803c8480804103001c402c074010480c240e000749180c001c0d0202070074440b01d001070341e03d000c46108282c03c1a1440c3d013442c18061082c0fa2410380e012481349200d4120401540e6215010160740f54400800100904420003554083e015240212604160040e560004d15001d4580303400c6c0415202e08400c5c0024a40140e14100c0c034402c001c40407042e040745c0714a21100689440300340303010400400e40c030b014079103854052105417140802c03200c04c07081d400c098501c90305080503840e07180ca0703c511405d40001e19282001202c0d40b07010030720740b444003d980c80b104d43c3c152440d928081d06040091055084c40003450001c0c0c46440c0034400c012880b11a28811015498205800c40810308980c102c641c03280e2080c010480000e40c0011540c040e1f50302401d00200590762031400d85c4052007140c1005d05994204195002001130000103040c0c401c2c42100c40d41c04036078845c1d00445d07000d00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 34693629 1250 34692379 34692391
    0x20c03070308030c16050d0c111f0809070f030614180d0804020103092108090d08010b090f0d03030c0e1c0f0309150c060f0e03030705130906030819020303 68
    0x800201d4448134500f0000d051004000c4850409000162551401c10111155007070228000003602d4080004640080065040c11607902007038280d040c0480d500320000940810500502c8070205a1043d42080080d0040070321061100d00d0341e0700c1e4900b03030010380f0540c14402006028800403c088820300c051105a907494040201610300314481d08882002c8050001d07410315039900c0d06140424a2002c0c8882d02d12100c12046909201e0380d0300003018081d00503d0042903822038681340325001c0e4080700150442d070300500f5458075840248000b41c000e200d01050198040080b0001c0c008168150304030740c0c007140b1580c98050302141c00d14180702d4001800080cc03070a1203000118200090314408920241a010b8580341070310940700c0e02000303c200d410341c561002042c01c001421082000701d006120303801a0b1007905200d500395801c11240c0e04d000140c141c03021b00c0800f260a204d8072510403103180007801c2c040028880c195407400c20340c41c03030341c4050800d220454130790740b03240740181c000411070303014039 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 34694879 1250 34693629 34693643
    0x60804020607171c0203040b0703020901020c0114090604031412070309060318020a0605040302040509030406210e030a050408010b150306010309050c090f091c020d0c1110020706020c030703 83
    0x189a075402000c0348005402001441041c00b04089060b1926042290b0130f50b240d800503034031f0134142818003481c1001028042010300411002501c0d0740c0c0800d1443c10340750b00b0b00b015a0350b50f03982c4103014542d0190070f0006400c000c0c042030000034080700c440c07056180c139030120a5844c405030340a90344240b13108038a00036012590802d401c2107550302c0303a4000c0d00012014804c0c0042c10507581d0016001060a9012000040300406e0600643c40c0c5403040c65044894600158038280ca01100503050b52550205039000310044914a81e200000d500300941d0207258100f540c0c0c1d0303003004900161054115018405496190050b00b403058107006400c881343c3c244c000c0001c0d007965280001140604040340c0700715a0ba01032096651a19191514802d01503042110000c0007458000002450407c0072000b001d6101c000c11414130b942034010502c1d04a0780d0461508120f007881c030b4200f1a010740105a40140c00c05601c02002100e268089014002e5581b41c1e400e83c0e101229005c105580c500d114003001e40b0311 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 34696129 1250 34694879 34694887
    0x705070e0a0902030106030b060307050a0503100207030c0503030109051506120c090609090903030417130306090201031d0c0109080f0606060c1603060603050c181f080d0c0c0608040206 81
    0x10825040d0000ea200500901c0414015015070110b400d454840d401104e03d000c240051002d00c3ca418040350018010079184441c4042c54000003903500d030340441e58401c03e581d0018016040c1031003103004541c0c5581140807a5620350703680c9814001004120b443d241c501200401030300d080c0ca0035104842d101e0f080985e00301000e80310180d017040c5a03807005040075030241007009031043c01c1d112041264071610002c0007942d01c0b40760504010b07d80c0300720200716003079800007000000c0c43d420100c442c0c5000d407900110000b400f03e05034401039009141c20440300b5045020402900d100040001d540e8540d404283e8400303800c5640c645a89903100d9440c001100b80c0d8200f01d0001c1c0b11410480040c0941031031034402c0f100b8000c201c3c20060204000c41d003046d5525521006c040c414020100190018220309562100310f480e010a000300c0029009008154003c001d0302042e00b060031000c2d40c030400382c000d040c169400000c0c1007a0142c07000c05807401c02c407100c0c00d07203500001c2d42c9401820301521468014241c24a8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 34697379 1250 34696129 34696139
    0xf01050a1d0a080705030115030c090507030908030112030f11070506090d0605090304031101180506070c03050d0f0215010501050405101b0305120a0501060905130207020d08041a070507 81
    0x781c12810044000ca01c400c50003071031603580d03032180c5000b440075501602005007044140b5080d10182c803001c040c0e086044c0380810024075400d030304500701c0d00095400681a01e40b0300c5e049014140146004d014620084004070300721201054900b0300c4c034407a40700c0c40c080c220074841c00c0d5440100700089980b6900805400c000c241030002c000c00385480c0003060001c4442480c1d4400040f40d1051701d0142d6260700101e0309200b005070081c8483c8040b80242840000c4400ca00305800c11001c090088074007a510104a850030400c083e05100301860f40041035a28105d0720a02c02000040c0e04a440001485100301c0c00c613410350a10343c0203042c0d0360184d40d0b80e890181401c043c00b06120300036410300c08002071042021141400303030301c0c41c42c2c0c4203100365035080d0b80380110031100780311600143c40c09400c646030200400a594006080400700c030f00640e14038195400000b0303114001d000e983e00107504013010320500400c005803c001401511a1030400300c0400d80d9000022201d801030f440c00401c0c07688000b1003404 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 34698629 1250 34697379 34697387
    0x81c060e15040b030d03090b07020328020a0501060315111905030c1207020a0227010303030e01020d0f020304020a0815040632010303030507021212071b0c030b060f01050a 75
    0x40180d0150001c103e00e032200d80800d1030718000700c0103440003d07682c28001e010050402c4103540c02080340d100650030280c0716002c11003c00091801040001c0b070303820450b00c00c980240301200000b500b110003001080c2d40d9060000741943c1c0d4050b2241850302d080702e0030000c8101c01050f202100c02011010b0302d40c5070030320000d03136031548060715003103e0f034006201d10303120041407681c910f119041c1640130300b41850b600e1060100703410910304c4000100902c9500e080540e8841010581101c1e00341c038000ca54166004a002d00911a880f41540c4460512403042081995031b001140900c2c8241c4001007510b40d21034915442e01da070410300b001c48000e401c01003404204150003800c40125189003800419006441621681d5028110181c107415071034010424184c1501c10b285d40041140040c14a0850000c00c0c0c040034841d4140c58800c640b1101d000c210810f01c5400051480c0c924540340910314101e0707082c010502102d40c40119030300d038120400905541400382403242c5503001030711800e0902e80340f100300ba5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 34699879 1250 34698629 34698661
    0x90218120f070308031305030309010204060314010e06150f040b0306130507050f25060516090b090402180405091507020a030e0d03030e010c0f02070509010f06050c01020408010207081c060e 83
    0x41c644444286d0100c0101d48180010b5001e100d01800041c0d56501d00400603080da038500c10852644007444004001584031201d40a5000360221060400128900000703070260254503941c011390000401c2c00b2443c040f0300c900540c0103580c1180c6d82850846a5415a8140c540c12610a40015018803074401c140d40c80038041d0014071004a20200c3c901d102c2210f4407030034203961209480542c2c403401403043c1095000e041c124035080514001070380e14101000b80304140700d02c3c0082d500132640005c0c40020401c0e481c60320510b0031401081844607083c500354903542d459008002280494007000170a42c0140000b86a861003913164a6500080104d003040284c440312828003642072603205c0881150346079080c8035a500c1d0600719204c103107906101c004028a440380e19040107002c0c00c1401c0050025002c0d5040e03400427500d9074940304c1c0e91100001a00ba0180c000c592240d5101c0d8000725140d8200f001c03e0020b880d04640c7c2161030304210b50600041000e42d03800d4860078040031400d0010480c9140d0143e000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 34701129 1250 34699879 34699891
    0x408030f0304030c0605040305120603070b180607060501080a03141c0e0a06090c0f140f0f1c0f0b0a0504030c080f04030c08010501050a060206091b0109090218120f07030803 76
    0x70020700fa0058407030001b903170320447c0d0440001c0c80c00181c0100700d005920050f500007030158000c0c2080c0342403540a064a04c5420100542140e0810041d403d5a031414101c3c3c141c42d602c07001c2803025503528000c2c0343c1c4c1c8030340041c4101d0214140c1c0c07901041e001c0d00c20083d90700000031560102622043d10825000038000c1c5401540c0901aa08000000c01c805000709461548108444100b1528014820582e80701503000314111010002c440703051955590000b0000d40e02c00ca566134081e03000440024881c80d44880c54911822070300d0071640601030b0a4164544441c081c0044001a03911400034074100c2d0411940200454105850640807590100143c114802105d042c186095102c1e19209124655548403106a80d1a01d006024608140700041d0041060f40010066030400403511901d03803d508004507003c08031121251820783c4a5002c84c8000c00c86450115a10140b0307244010049850b640c03950302940c200b031038810002c40d000414414145010014141d02421a641c5004a40c805010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 34702379 1250 34701129 34701137
    0x304120f0302071b14030102040e040b10031410051305060f070908010f0f0c030c1407060204050607030f0e0102071521021215060702061902011b030b0906060408030f030403 76
    0x40c0d40005084c110711805091a400d8942e20a03600c1d00c2d500400c0b0101c0507085074040c0c1d00500c400c0007095500e15219401a5020003400c0990751920084050690103a0010302002c024842c028602d0001048c072003550b00307051209102642e1118082c0d40c0e05514132030024403d60245000501c40040c80d8512a00808240340c6980000d0780e4020007825034501442076581c0aa55415107400c020a03840f0304a06805681424001131015260140180106460300d20590740c000509030100589941150054a0f0041030280c60340c5680c04d00906807020072035030a0106407070b10300000d450b40c00090018121003000d81e8156004006040071590030b20144000c0e0180f4008801c5100044528000b4020f00b070b410a4000e00b140c582a03010f101112403000116010300c0b010000c00700580c5500d0106c0f50640c0040c01c08101e080c4040d40100e005208501920340c0c03101050a4a00115171306400200301d1500840b204080c80e140c10b000c011280c8102d00c9500030a0380100b01c031a94440f21840916070060007820 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 34703629 1250 34702379 34702387
    0x40b0a021005070e0301051509010b1305060f09041805120c011103040516060e010f030b030309040608030306040c0302030c0301060309080708130f080a0c0303030518011a01020d02030304120f0302 86
    0x110070059402c00e0354002d02044060006510394182407055991100c08222000184040c150104811150600460a02c610002200040d112008100c03100611020303201c40e079180700220240d8080c1c0c01c031a009a109a091120f0081c1010b0305040e031081c2190400090010f568010220700107503070100c4c1740b00aa0f07540f250004c2c120030040102441c440c80c094006405800c0161645443d01b100d01c0d0052014031841d40010030069070301032040c1c00c5001150400242c01100040000c1ca90300945100344e07801424100702080042d03000c4040c600a000c01c0e0340a2111819021080d400d030300045514421103502031004002043c460f07000f4a90650150f451301e45010004e854200e1294082150400030010081c002c106600341701e00410010300b1804081d1030001c400303a503412422141803002600700350311080070485445001d0700c400809038035a40200803043c1c64400c13401e0b9022910010f24090b000761650856114004001c5a00c51a402a540c0a00d5540018151194058180410304050b0300380 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 34704879 1250 34703629 34703653
    0xe0409050106121a070206040204090c05040e0a0302010b04021824070b0405061308070b06040e03040303020c18010806010905070e04090f0c090204060f0c02030c03060c030717010308040b0a02 84
    0x2c8500400b5100740030062064252a0601100402000b450502442041d4080011050380820f0260300941d0466020601c0340450030a5001300c01c00b80c000a5100303140c5685a010a80002111036085201c0d4009101c10890707001000200d00072100f060101b5048250650303418506100c0ca002c0580710661000210011605140b0094004400071240130600005100a21100300075880d400a070803488804041180c0d551a81c041c01244402072280c0c4c02100400c005544603001009111051400c40f903d55a6a08009542c0c2008010340380c0281c0403091a1000403001c486840e060b200804020442a40b81c141b4dc04000e10b001000e442c01c0086203480020140c0d11070042d020f286000c4d140c41e000d0060141081d060b92445a030040c40c03500d104010402031303190803034bc026101e03114070304000700031900300e0020030f052510491419030305010f0301042040003007540b009180911026039804070b408140500c0d1410b440c5081c000030b0040c0740f00b0303c4100301024418005201c90740c502c1c410703549907042c68 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 34706129 1250 34704879 34704881
    0x50705090d0f1b03050606030613020105090d14030a03050a060803070807060b09130204050f040c050d020a0b0301060306150c0c05041a0a0608010503010b06070c050d24061a13060e04090501 83
    0xc115120800303c4903a03810814480104030311a0440d90440207000302c0c3c28845950580360b541c0700c2c4020b05002c4040307404005569a201100c610b2900841001323208154101180d407207900940441005c64a407101141c51541580f0402d0180d440d148015072401d802030704c0b90961900010001c49455481d03880c4421142c03140380301e4500a0102598103140e100c00361040100307962008010761110b820200411000c55000000c80c1c04807203003030f00c1641c50380103c2d002090b0300c0d07030340d54101d19811280040000b0b1620b606921a0b800c0b582a0b0b60000301600b000724045885000071a0050150f5401c00e505124074501365005401c000c8040f00b50890143ca400c011a1240751568010000700700c0701c0c0010042802c003800303502004a000c83c0d81520f402c0c46691a4203c0c014a8000d4902404c03d24403414100510103140c46550300a007991503907d40c0803c11010040c20300c0740100740320403000c07003c0c0850300340081c410b0318071900d22050340c20606401e0800880301180503803960742c0e0058a8101c140045202 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 34707379 1250 34706129 34706153
    0x1902040801020405010909051b210c030a050106050f030a020906090d03021b0d150207030e0901030f11040203010305061513110d0518060a0c020114090a0b0109050705090d0f 76
    0x34990000d40c60340e203420000341c119006a07201c0007206043c0800c11100e0215400038866108298543c251280c45468000c85810381002d00380016194900c02c5c88200c81186019600c2419800c200f84582d0707032220811159801003014840c881d0005001003254124203401038030240a0142c000b6003084020320029031066962442a00940c0041e01007a4001c00041c4644003402e10075101c0c1e8042d02e03010380d00d40d80c1c100e4060101100d10f96001c036905007051301c184000c0d2008180103041e02e070556184e080c02c82e41c1e0101380d07c040700e06284101d6451010300302402903c1c1225000f8010b480c40b540c0380c44114150101c0b00e903a42d40c0c40122103540b07650040981c1300303a002451006043c940c075a025400d40000300c078030141881802c5408904000b280b0040010707400e511030746801000c2903c8070b03500404d038003400c0150f0005000355880f5042103010140010200d002130b0003501c1c0b1051034cd83c2c6941000484405495050008904000c121601e0402c0c00b94107011510558400e0889146900e6440749110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 34708629 1250 34707379 34707389
    0xd0e0f09041412040f0303030b030304030f05030307081b0d150305010c090e090a0203120d0605040507030c03150501090b090a1a07050f010b090613021903050a0f0506090708190204 79
    0xc2d0010210704044100001198000300003001442d140c02d1040c0455150144e110050401d911090300d00540e4805205a1f001960b00000e01d00c41c159461a0850b200d800440b60300002443d4040026040e80400304550312440c5500c45040c940500c21030303075102610b00d402c001c1010b40c92b0701d200040000c0c8248601804183c203550b07860000390400703401869800700076000b258558040c05820025950204d9400729541c0e415219903a02e070300315440345002d000315901c02c991180c85e000411090320307015081390b0801079043c0e0381004140ca0000400c126440107010b03140c005205008203010001c2c84500070640c000c1c005051130b40091f0380e460038101c1030002d50800340b810788001c2100c5082103000c1010441110802000380070540e403800204107081c9000303004030300c01c00304d28480c141c0c00d9401d64100d5030000d05040301e059004d550030002030064401a1001c04101d40740156813030070224103100c0d60707000307503402050901947c403002c4d021039a2100207446102c100c0d00d03000c1034204104440c8000c00040c5 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 34709879 1250 34708629 34708643
    0x1b07021203030a180203030316140c070906120b0411010201020c010e070519061202030a1b02010515100504030f0602041e0f0b0c19030e03070f03060b01050c0d0e0f0904 74
    0x4680042400141c4404d40c01c00d14664a4035032109006a40c04426240e00c20101c078080b42c1980c0e07069004803030000310000b0300c6150681c0011080885d03400800d950040e14aa00790911810781c0c1c40c072110049070120358001e00309504c0d1601013000188803003070300028041e0507c000750510304071b2414642110350a00c1d8281c0036a02c10700701001035092a4109039074a414641401010510380031700500700010800c5250406036000000030340d07840e05a44210340e60042d031020700005d07999002010f030082005482080c031114440c1c01c940a01d03d804000d40709440659a031b418205407969417800217010b4554030840d0120f03001d0001060742030140c82071548080301e242400030402e15000d8940200492a00320b108090b0081005500d5000000b03010104220380018100d4040c040303080c1142c48000910003207505006008001800110500d10441500c0c0105820408400303a00b00550f01da100f403101310001500320346950029a4002d0405494100e40074000e54000261180050f04c00b03541110211000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 34711129 1250 34709879 34709881
    0x40b04090501080601060309030906030b06190206100f1202010503042102032104020901210b090705040e01050403020d1101270b180606100512130b07020106030b1b0702120303 77
    0x4402e08010b01ca00408250404100032341e040e07240100000b000740522410300d034846401c0070031900c2e02c03000c907842d05d140501426085c00c02001e00035259803080da031090105e5030b40070010842d41208034000c8222502010340004040113680151095000100141c4a00100d039849041107800070710f00c1c12180c1080d0380074550340c05000c0100d0784801c4d030404042c180102c01104210050312441012415591000d40c041e0005c8004140c2c1c103070405400c80000c01ca1502c800500010741c000007403d20030303a10304960030b00c41544809065401c840c4111005001a800740c00d41100d82c0d401002211003581c000c90010070103c8014403034032051400200741c40c076501403102014042c48013001c4015000114580c0e21310000200102251395090090102445101c403104a00c01080c001c104840140c050421458001d281401d003002c01d208c849802901c038084e1400010b0149841171050320282c0b0351040300e02d403041d1110140002081902b1007071031045d40041100c80056138030700b0320320201d8400e08402190750f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 34712235 1106 34711129 34711139
    0x20c01021603030608101505010804020a08030a0e0a08060403020d0e03030702090903030604110307080c0d0612061a010e06090f0a0e040305040f0614070201110102040b04090501 78
    0x1072000300c002008064154000c6800c40f41d2420036a09528400d01c0c5e160306035640d01c1c43c1461540d1310701c04c0034042d0350300402c0384640042c0003030080c00c035007510382030228616400003480c40e001c5003174000c400d1242d00c2e080c6060009040351303c0c041e02280c2407664002e0340e030b64607071180b03042803042005c2d05030565281001590700c1e2503001403518843e0f08200a15a80360341c4159140303401541007003882c04080c1c15040031240100740a594418096a81c00c56900442c1c100b84005800c1944460b800a90a001c0d010f0359183c00d4042c10001402c10950319002040314090282c46060180c0218202840c5daa048240e07801080240c8005000420040001398501d03516001a10012a820140014154000058003e80d040541810703189070301c40100355000214400f66a80c1400b0820007800154498000c6181c1100540005400c0076101c1e400c149654015820903201180e682c5c00400c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 34532379 34712235 := by
  have h0 := BRFrame.cov_init 34532379
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 34532379 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 34532379 ≤ n) (h2 : n < 34712235) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
