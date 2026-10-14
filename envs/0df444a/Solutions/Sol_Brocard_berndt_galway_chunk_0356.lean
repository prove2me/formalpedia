-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0356
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:23:15.229444+00:00
-- url     : https://prove2.me/submissions/9e267ec1-04e3-4c92-aeec-d89c3ddb8707

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 63848923 ≤ n < 64028779 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 63850173 1250 63848923 63848927
    0x204020a0905040f02090f030d09120204090b090a1205040e0c0c07030507030602181203030624041706070503010308041203020a02061c06090608030a050c010e0a0503030405070e0c0403080901 84
    0x1d5103620283c0c0150030201c00300000740c501d034028813081c80c00700c2e00549002c003c0003e0564812200c40201c000c5014054180482050340c0c140034500c0740b00400214002c040760740c170540c00d202c0a64019555900c450f140c5810400b8110040302030049500e0481d0a0500c1c02c81d00c1464500d000d0403400500304001000804800d0500c50500590b40001c00c5455940d41c038503040c0c000f544442c481200520340100e041c211b030314050000d5100b181caa1001103043d5260802084070324401d4001c001342e107400c04a400342001640a0240004206580040e84501c03075450a0381d00300341000b8080c40400508100600006001c0302c2030700d01b552403005030140e880340075160030307450600c0285000e9408000030808040008031b100c003081307940314454410b0140a5940c5026410b5030000c1c01450840d400911800c2000345c440d00180c507529503084000b18130014480301c41c0d400d20300c140005442c2500000100018004200312503030040c07016450300113880c5808003c403400d80c015808000d000d22000900f51419038 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 63851423 1250 63850173 63850187
    0x110703081f06050c060a050615031302130b0102010f0e190c1206050115090b18061e03040b0c03040f02122a01030f0504080304230106060e011e0c0204020a 68
    0x490103100e41c030400703900c660002d4026084140c00c2c41c41d901c107080c00039040400c140651030282101030038000014a24900354001508000e00e400468900341c1040000350303840000c44200c07441081000602c03200010002403c0d1880340c1042c4209030b003441400244010b0001c0c83c9034000480b045030050300119171a10500b08003141c1c0c07020120a030403044000c18440c0c25803050b0304071690809103070205002c044090317803103101a209094070080309208440d110484601c080613030000c010034042c40d2002c0f5400307442581d82216840c01d10f88002004000406c1034601d140754102410102c100d04500d0b16654442c0e540200342c000a01500d0000070900710980308029450010384184a61918108605036200d680c0d001850000d00003030808254608038a900e03c5190301850700101f1070703031440c0d4079610b5903084240d1405016041c1031180c518202c42d1002071040d0f50180c200d9030340f80c084401342d4000040500486240c0110300d0642a0064001d080e00428802c900c0c0c0d0b81583d015803204180d40c41603403a8 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 63852673 1250 63851423 63851461
    0x302150a170a140106020a03021222090b0a24051605010203091c030e0c060702030703020604030c09060e13110a05150408011401060804060b1f0507050c0411070308 72
    0x101c400d403003032081014842e0006042c04404500d0815541c0e61a1801c82e541e110991004d0096000103490302010385090000b07000862584902000e2440010100c0e8020001544400119580d98810514528240032940000d000040581103001d404081d481d4502a03500d040d0002d0040001d410b100010004070400d15290704140215180d1074008082a11901c030041840c02e9072a08403905c0c210b15011388210f04082240d40b005010500d10740f0103000c00c079400503000341d905120310b050010040e0f6a040c000e0015610403022442128581041c0c034007510007907042086480000020030814118081c483c2200e82e030403945581c1b490042c030740800c0d03145213250000c40d008a00a080d02c07500507442c3c03004008403685013008003c40003408140d900c1114080c02035100050002000c43c02242c40d0f600720940724840104850400b42c00c0400780440300000c9003907440814804102a024041d0901c00d0802d150000e850510101c90b01200622203481130705001028400b00e41d02203251400c03210010341d00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 63853923 1250 63852673 63852707
    0x50f1002040f0603020307210506030606030102190e0d0204060303021b03010b011b0c0e0a060315140414030c010f06061d0f060706021603030905100e030406120b09070f1205010302150a 81
    0x142c1007008480802741001720f0b0110700922500b004107046003014401c41b403071864156420103103a05e4002040f6403c010340581e9035841805110000d01503aa039100e01e40c002c5201c0d40041c161a5601c80800b403071080788200c80c40c440e9141c04821010359800214080c0d4201c500040500441414580b001c00c03061030740c2100c41c0140e1124108103850360142e110b8004d5030f00030002d244400200b802c01c041600c412a0b04c03900f80e1610131000c1000a414401c180d1440043d0030b040e40d040c032000c03007461401c4401c0324060000c0c43d615100c08100740758104441c020007401480c06100132680784004160075181c81400300f4060000040e001b0180952581a90501040c2c03041035800c6246604004010304091034040d5440d0040042c0d81d40303500003030721450190340d400c0c1c00a181400e18044054440441444420034001e484001502e015030310b0b80c4546101d034106880300409115034580c000c2000c450903a80b015203624240040c0017513901c0c085446480d4030f5000c000b5540328680320080b04c5203149a00350307100b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 63855173 1250 63853923 63853967
    0xe0a05010f02041d04050703020d0201140720040c0f050c030403080408061503030c06070c081603080108011a03070902070305130f1e0521011107050f1002040f0603020307 75
    0x1960000341c2c00070001c94100c2c4000d4422140e4404c801403606034143d03030013000c076441604108018100084117130610760050405044124802c02c12910a0b800104219006607800c403980c031f4030007042d040c09009032000780d40400000c4c15034880a0800300b0a0308582090020101d10034084007010411a00519405030700c1e1901d42e0359561425584074015600600c04168a1042d1f01c0a400c001042d07640c3d075035030b0300700400300b07503c80300c00c02d441300140c150060710040001c0040000c1c52940e0345401e0f40e141d01c00d82d10b43d1038070340c540100346003150703621241400001c0794000440020b0b68001a040c0a81d8559500140e85030864a0140c44601c0b074039a54030b22100301e80c640002c4141004c40a0f4003100e80c42e04002e100300c08a0078070f20003460001e025031030344a000c5000f045003560300c2e480c0d6400101004800001c462584181755000d60708148012a06a031001c204082d0030f640901c500080360365010030543c01c2034280350940358050501d0141d001016808000901d150344901c03c110381f49450401501 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 63856423 1250 63855173 63855191
    0x7020118051e0a08031303080915070b1e0603070b0d0609050702030315090105010522030203061807081b0907022e1803080115050c030c03130807030c090e0a0501 71
    0x110b03086141011901c9040c2c024030011302a18040b0031114042c00b14009451403604680e5002407542004c0340c0d440d0040021440f03843c10060940003441c0345d500a550305400c2c2d11f84004005842d100141c1405071240c05002401030a40300098a5015074844001158685a103800030000070038540d4000c05203503040100380840360341c0110085004403e4542c3c1c0b8000c41200d0b005102c1780c20341c00c1c400c19001070010080f03801d80c2c0020080c40c61403000500101481d55a80e0340001c0c0c600a41514104010340d441806564200410024440103201c0380d006081c0c4204044100300701c0d0720307003018030038050fa900e0800103040ca0710034010364000002c0742802d00100c0d829040610400d01c0c500030184c2c02a440e14001040c6000104c8100d240f8560580c0d401c4140e80c20101d882ca0720104020106062043c103002a04442405101401c402401ea000135030312000b00346e40301c070410010b550250005410414003440450380c4194201c0a503001c1c02e07404500d0100100e80b452416941c030301c01408a5180c21344013 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 63857673 1250 63856423 63856459
    0x21c05011b09050109090218010e030c0d030210061d040b1e070203070201110303090d031503020a0909020306010506040b03070e010903050607170601091412030f03010b07020307060309080702011805 87
    0x304041c0d0f5803e0383c0700344950743c03101c0499049104410f803c0c000c41021500707000e0258418440360342c0c40725018045c1e40784c01021401241141421203011030158100148510084021348079110003440c18104030310240c4026800d1200700000604060801c2c0100000a41340c00c800c034002010b6620304000b907c46629140d0030081d100cad00720b00303070480c000746100a0601d82d041000003500d014031f500d8005410f044403691000c2d40104520184000c52a002101c000b000d40e44904a03040107113920040801d030740800744100f40c01c00f00160001441a03100380404d02918000340190b0707a2280136800c00c00c002300d9503600103039400710941e40024428400c0ea020019683d521400c40300402109a420011303907114000103503412a030703c1c007443e0171114085810020a103030458002810030000c00640c0e16000d1120701c0c2c0b03c1c4da03034803d80202e4404000040d560046080c104001001401c081c9000c00900b44540c4e1003a00d1440780c044081d041101d002d14000380328801d11701b500020074000b0211541d4011009a03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 63858923 1250 63857673 63857687
    0x5090a020304030e06070201170403120c1d04060b0d0906140114040b030f030d2301060f1202090a0b07060e01051806011e1707050a0b07050c0d021c05011b 68
    0x2c00c4002540408501c94030b07060100c15604425416190b115070b145154042540b4000020801d80400400302001d40e000303013007882048090b007000c0d0b070b035101c0485a0785540940d44603102d5165016601e00301c020409400179000351012003801190100d48507401d81400e0015102d01d400f511440c041200000030b140c981c2046a01f5050000d031018080303451150105078450a00b0782402400750002c02040507507005961007404c5502d64440608000c800304032500e403403810243c0244000c01c40000596010756003110707034154241d8256500350b10300846007000c5000b42030f8511070102c0d5610041034800c10031200d80c0010103100c120300002c00c51032811444468088444030382242013400388000100703198904025464681c0400c40502c007895103050175418048400000724406030242c003201043d9542c4074000140140f074400001c1d521207009050060414201082103841101c0c1e400072040144c030b400c1c0d40d03e41c000040001103081038141d0b0030700c18050003105404050849000c02984001900521 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 63860173 1250 63858923 63858931
    0x5150712141f03020a06050c010f0905030408070b031521100b040606170c0a0c0f08070c0605030603071e030602030c0a03050105010807050909060d081305090a06050d061505090a0203 80
    0x8440320755004220300c2e00780310041a000103900181240403e000d0030340528024202049030070f00016056804a240600b00c80c21158215107541000504220581d400c2140c480a1b1642e0024240b03541444c0c0104200f07840c181141ca4043c80c105141b09413980c2d0444040c04000c82c12009440540c1c040ca000f1000030240340c0000d9101354075124003c9506441411850350440b040010302c240380e00c906000c001c1c5900242b04a1080040c0c0106800000e468206083c1c59940f140510070785403030140c9040c03c180215900a07108100040c401c00c0010b540006e55002101e415108038202d14250003542a1907008580014040e18000014020b0107a06c0000405009501ba6002c0000c1d90f01d0300011149600161060400100180603155241c03401d03841d042d410213001041c808000036140e0703c0007250b801042d00355003587c40c001420004c0c3c3c2001d464090380714101d0030003040101d080200040031480015005840c040e5540d810203c0c1c4014800000c0203010002c0c100c00349440e10108070406584121 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 63861423 1250 63860173 63860191
    0xa020103060f050901030f02040e0d020604061802010e1003020405030a11040609060e1602032709070807021b030703080f030406062103050307030f1d06130515071214 73
    0x100c0000c0d41d15280c00b014040c1c44004000081c140d2071515100189848104181d80c8190b03200542610488104200d110f6855140c0103024989018102001261900c91070405180000010780c070050303034000d00302c80d2558011650200014545c4c0000c0300280140d4000c55050311640d1240814001142d1840001c1c0c40b00320b07403e00050f9103809001050758028413500145034170203c08074881e800c00080240c1d20360100d00c12241802c4201030348421812a52001c490180b140300322128840c205003011a9101865040c10901410003500007940c0340319642161540341c071001d203010b4482d941072145000440d082888075072114083c2c0d503040600c3d4400d550459406203800000140700000750801030b680209040382e14894a240e85064801e0b510081c400020580e9941501031000840c1c4110500b41c1c0b5500440d5125180018543d480e18102508942c020250052082c00040300041c00641e0070504000b015000d4440000c15070343d0030800c40c170348a01d4506000041402e50354104030b1500c14410f10b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 63862673 1250 63861423 63861431
    0x504050109020405030c13020d110301030b06030d0203090103091106070303050702060906040203030f0306130905010b040e0f07090c18080c090106030c08160e06030109140f070c0326090a020103 85
    0x1901c1c03400201e03c594131800b50036800103000c8081c81e10380017842d5204050b200c04050300e08401481d00c0f0040340c00b0202010684100840140140700704400010703803001c0c1c19002400400440030b006981d0340104485e980c1016103800741c2d0420004d00c08407611900038080c202d00c2e02e0340784600c0c0141c060700085070003000506c0b500002901040c1c000404500039500540914a07000b0100c1101c2c001d548001d100c182c2014210b194406900b081e440b916640d00d000750000601450410b0400c015a540c046038001558000b103c00701c0240008100d21040310308034200000e40765038000050350911150400b8120000c4908400900035a0206951005c3c075803c8440b81e103560f0700c4540c20317001c03610007040c150300048410000400311000000c4450310080542408420081c03a42d0000f2501d82c002d80084010700e445000b9650880640d901450700708590340c000d10b00a140c603980c000c2c1400c0480d0743c05030401280c0204410364141640302603940c210040c0c0008420301d0300000c030301d544040089040740000d20f4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 63863923 1250 63862673 63862679
    0x30a050711060103030c02060304080c061003050d2c030c030a03080702011503030206040308091e10060b07150c050702040207060b0a0608090c2b0c06080912070602070c0f0f05040501 80
    0x110b03030b050589500d03484440c01da203407039024068103400041c811200480104224071180c07404000b0f840c03060114203454400d940c2580f8140b810f00503c00001000d102e40a004c0324001e048010b10b20300003c001c031124160107042130000a1a042283c0842c5030103000c0c0010550034141c0c4040c040c4c1c07184600f41c0092001c03140390003400300100701a20020b801038000c00003150000f48141981a00030004c0c000320389651240c0c44800c078000002e050300c40d00c01d030321000c0025210034480c01008010178543d101c4a003022510703140c03869403025090300c0005240d691440d400005010f4801d940c0c40d59005481103466101518195000f0524958014440c00510000041d018815882e580c0300e0782600700a064039030040024000141b041c01e004a040408042601215015224409501900801c100c0300c030245003050217028034038040c08400c510342210030000e072070110312402c030354045034007840050742c5004c142071014503140b5540100c11011004e003800907221142c4107200c0d06450301100e040140766a = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 63865173 1250 63863923 63863957
    0xc060c020d050d05090c0a06022415060309010f110301050102010e0622030903021201150b04290706060b0417033412030504111207050420030a0507 65
    0x1d041e80000042c00400540780d0400113038010541040d00b85080b1980700e460322001500e9140980c0116005030301000a00b000b103500e02905507003c45200b004244981044641c01181680040c6160301441c0300101051090600350700044036811104020803420a030b100f902800d40e8021b00c1164010743c00e0404100c400b00740425018000c0303014030303100700700311044015044002c440d500003582440502d581c000007688401c441542041d400c400001031940703464103129201ca056400c000c03c0c55030244024011119a000c40b509240d030b409142d13144170381010180302a11b2003030b1040100307a039050120011f1401c0021000e44140d0b010b107560544281d088401855490040c041d048a200142000b4100c0341400141408402d10701c960110381c11002036120303000780880b40d024407000030b99150108424071840306594400700c1c400b147d215a072258032604580d541ca010f4010f040c0300c0d6a441c1c4000c4213041e440d0f0418502905161280c03038aa241420245005042c1214070b44040fa45a62188038001 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 63866423 1250 63865173 63865183
    0x130b0c100507020c18060402041211150304052503060f0504110d110d060b0d0308040308010609240504081002040f05030c060a08040c030209011e0801020310030f050a120c060c02 78
    0x4c0141a04942e00d00e0865944980b410190551b90016400c110105e200351030754180c0342e003850013017030721610104402c02071010b056842001880110310500c2804006075012485450300343c0d04d5200a80c40d5107014031358414841c11680010400c81c50007411021000c0c07140c00c040c4c404d80c080c503078100700c00c01c4103424440540b002c440003c05900c54200100124686100e66501d0780b80038502c0001c1007188140850001e001400003a40820300013400c11040551060806005d001c0510b000d01009140002422000c0c40300440380c00120042e065400c0050310035070590b001010301108460718884d8200100000f036008bc02107200405542c04042402e0500140009540300082e099915003481c441c0100d54094016000b281d01e403440f42c0000016a4944803c503019140860301080d042989003000b08609100343e00c181c0807030b4014001c10580c0b544016a00d004c50b908a90040010082403620341d0601d4001da40c01800c024850085c0001558800408103200d807242c8420001e00d541c501050780c4c2e034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 63867673 1250 63866423 63866443
    0x130e0d030b030c0402030a090803040c080d0c080a200115050f06070309031b08160806091606050703020f01020a050903160b030a0b0607050109030203090f0a030206040506130b0c10050702 82
    0x56403100030743c21010b0525a00441d481101c01d0b100050306c900c1651240c619038011307502510305800405041c4844d040034800d01c200102d40f4144200483d48640d41c61582d030041074905818000d4900000304188400c3c00300304a00d200e0351000300a10740e98004a84e030040b425000741d5014840c42101c4520718280401204c050301d4260300d88200c0d0b2495a914040f80481c10041d085446001040c00108070a00300146c070001e21406100c14500b604204005192070f01c001e182e0000c507072004011120200e8400449000c2d03034070510740b00390345410b1030a0680c43e00c0100c900c031101540c0f001074078040c1d0780e60000150400002c00c03400c0d2024020103450280030240c070b40c06400010b117030820100d502c0d0201030b40040150350340a00543d04000290b210142150007002040c1c025800000b039188080c90a503100c1c8080200c1198509100b908540126a00c0d004900809015060008003140882e50050201004250724407940340d075182247d40d160380383d1404c0b1450101c1e841c02c100110b0326443c0040740b0f04050f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 63868923 1250 63867673 63867679
    0xe0105030f04060e030706060b030a0c03050435040e060a12030206010b0a030b040c02060f01090c0e040c03151811030702030304020103090804050307060903170301061b050c130e0d030b 81
    0x140c0303a986801c40201001d1031003040303520080001b00002461801110003d042c1014120f03181d160981000c030540350400e04605c205840c0030100400a000b01c0f208410300703141f0b080104075040c0c03248208071104801c601c80c0003401101260004e0400c025032420740c0304400a40d4044a9150340d601d0054004510040060141c1c00c4140107000a40080d405481c0b50000b82c500811192211400b15046402e01c841c10001a0405010000c0409040c080e460051070300c4a010000c13000e0248000741000c0c1d4071180e5600c90f645903202000c05603c82e07001519a1a09410788440495444002000d040c01c001915542c2d81c0c1040304c0703658020618029a482540760303030051480e642e40c85d401140240703404082104e542c007040c0000315240d00c00300000805006981c0f5070307102060450510310011000048043c1c800345040005001090384503d20005d950341e40201030803c20114134140341440c480001c3d164100c00c0d050a140380a203890b0700034280869070001524008405424202d09450007607120300d030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 63870173 1250 63868923 63868951
    0x402030f01090b13080d02041503050601110c06070f1e060b090103020108040f05070f060f090801020f0405150702030a060c030b09010b03131e030306030b0703052a090306040b070e010503 82
    0x4c088000e001d20b6111441520601d242081c0d031900c0501f01d81051b0403420440c4010200000c4c0300703415100700c0d60488400d00b49205404016200117030b45083c0342d6601c40c061351020807400100035154100710302c4c2c036a02006d030f44c480c41140c500c0c40c8680421190107507185030505072464540d0511020150503a030b01030f51600d000c2d0347c881d140e184082192440441d4035104200b80002c80000b401c0d51100940b5031592500403c40e894000109000016007100809034410404c1c0b0f54900840b134105c0d0219a800e8908440d0030305c008416410302d00460401035050301031070b0280420400290702055900171142c604100400d103001c1070002101d000d008013003001c10104007043e45040712448114010348124903a500e440c0005484403042d610b1031004601103a102c1d401481000291006164800c1c0e051508020600c1d000f9050021814094007820803a4101402640c3c0002e84404070344107810043c04484c002c2c2007502d002c40101904131507980c0019007103401c811082d841101224005d41004c8040300d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 63871423 1250 63870173 63870181
    0x30402060909090a0c030c050f0402040e01052b030906110615060d0b0d0b0f070f020304032003030a08011e06020307020618121006050402030c0d0b1302120402030f01090b 75
    0xb11002001c0c290035203502c501891080090422101e96000d54483c0b201c141c2d88528010a215441d45052540742c45580180010300484c22440350580c119001107a0419400d122105901a101c040403400301940c049029003006064100a4040443c1d8032030b580c0c0d8180312040388000d521204191030b80d5400d90a82c815031129850030b04c02400c0c0b03180704244c0001d4410101d8000079281d60060004465002100301008403144000c2819540300609082c40e00002140103402500c9100300e0000800703581301e5604003590f51490324202c41c26140c0103000c40707549101d201c9001e03020080034072a8002003042c40000141c1c09004544243c100c4046400840c1040080d50070007006401c582140001201003303a16041c80e40c3d100342c00810304c0d034400058481050240c6002083d500e00d600f004e40a640100280480c071200c1e0b07130485a01001c00103000600440090000300518a8803486002050001c14181030b01008042071500aa00c02c41c1200d40034041010704d142070390302001010301603003030041c001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 63872673 1250 63871423 63871429
    0x19020d0908060a0b04060f0602060402030c0102060405150703020f0406120f020c03070314090603010617090a03140319020a110606100504031e08070c0816080709020a020f0a0303050403020d050304020609 89
    0x14013084801080072401548a55100040390056488000141e2207501407000303504040c001c00c80e000100b8405000c25203401c0e2101ca40d210480010715401030650307030000e00011b100f641601c60003503007403e949581c3c44d41d503500101026003000b00d503403032070b0b191808210103605d00e81b0032500d005803018080c0d82040310544094076513000d02d9810140e184001c01c0041019510303980294083c0c0041d44031050021301c1c2c0f00c2201da591200518009060748100344410200341c1002d01c407042040000c007410f81da640c84610800e14680c000e00003e06590000c100e00d02502d4208418848825100d011548142c0c1c4400030800745080d24020f080200d1810002440807921507a01e000b401c2203617a00070210382e190740c1e452455a0780700e000143d45012080006015090341408400c1a42c044445041c038a281030444035901c515880c454001c04030350024610b0500b900031b101407011042040f040c1c030481c0846007800b074003820044034101d00500681c240321520314055400d903070140750041e00290524407042c0034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 63873923 1250 63872673 63872681
    0x6010b0708040801060e18070f0905090a0f050304150207051315030506040f1101030902010e0f0d020910060306050307030816030306030b04061a0402090d0b07110319020d0908060a 79
    0x80c1e03000c600c104808103801d18240a180d00806418904c0203051410510188420700469031a42250f08010010440102e9260749201626881e80f400a655190304101c6403800c3c0c40d85600404460302d00c400c0d0000c6c0328010019004032402d03c090700c1c1003407003c1c080c01c90700d508041c01500d0307204110341f0f80c0303564000703c540c400188004587e81795682c642e00ea885481c0761030341c2110100c84076030502100720108185d184140a0030f007400c4c20144180661070740041e180505280100780502d05642d0780a40c2541c58a41450782d19030040c10442c02410015511109643e5502a0401007420045e0000c1c4a0400044803000c683d04664640c0c10048007510650151a1008042c0c04250302e9110101c04039101e2004076004501c1074200090840304d00300001c1c174104088070080d02c130300e205000d80e500c19100e0f0442c0504c04c0e580020815510ba0300c0c0c803070945508001c64100c0e8042c2c40042000700c07840f181c1d42c01c00e120b01040340e001c58521610300d103011178444d031043c0502c4140790004808134070409c4003500 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 63875173 1250 63873923 63873937
    0x6070e0301091a070c1704140406050919020d18051608150910050c070309080c0a09150b0c0a0501051f0303030b01030b030d030f050c04030503070807030201181416030506010b 77
    0x70b170a9010003416115540346042c0b00c1031303180b1018400501004000003044032001114030035034060140c1442c120024104072802006010700d8620000f050844410315070486000c0310000504206110044240e1146449814030480c1c80303204510700c40e10240d81021084040b1500c0e00014542c04c8201c801c0d10828038005024080207100c0e841e544594001207000301c62090a6100a00340c0300c82e42802c0091140e403442d40030100e00d400045980c0d00c10b4a40002203825110409404205510411414000c0708059441940802004145140c81d0f601c0401c24801c424004e00090040d612605903542c840b0740b05080b28210740b22129030400020b40250404400040141030001e4120b03158000729040c01d42248c13940d40003a07034904058880c80b05d988141d54010501c2d6221030b00301420f5944060740c0b403068440150030340c100415041c0c1013510075000364080d04010280012104410318150f8011101c01c2c4001c4800d002d844402c2602d61030f420740c02e40460780c01c000244016440c040c2c100764180d221780 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 63876423 1250 63875173 63875177
    0x220902011209080306120304080a0807061b020706050903030c0714030609060f150f0a03080a170103050a03140f0c03040911090a05091314030301050102070f0b0702090c0d0c0206070e0301091a07 85
    0x4000054242014805072b000e250041c1c0c46140d4820491a1600c2111154200580401722150020004030b90000e800002d580c801d060030b5030b8032325017203000a155000f10143c0170300d1072180301c0c1c003c138020084400f10940c1d420243c0c1240c0203521450045501c500007150305100003240c4a0000780c06820030f030b00350a0040d601400400e00781c0d0440001c5182952160403c0c2d580050000b10380010680c480c01c0c40804a01c1900a6145035056640d0760f0f8652038159005010003200d440d840b511410503038215040c1c01805902946c1d078403400740601d91280c0040c0b1a1641740303840d080b00d0b926a40c003240219244400e004020099850a00003000740c000030140000700030b85004080d8000040103a0440c41010000c2d9005580725072608000918011041c1c110a05800c21501c0800c14040c2180c241c801c0300b0750495145d41f840c1d50380c0b1828403540c041d100c4440851802c0c5010140559008114180150b40076038031540c50b000c40000f40341c26510f402030003d0100f5051b102e00300004d103550a056402c040b241c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 63877673 1250 63876423 63876427
    0x2061605090f21061b030406050a02040e010303030b01120c050313060b1c02120c0112020d09080706020a0806010e030705060c030910080f07090605182209020112090803061203 77
    0x80800e007000e2585003c0640800d0040c0f400d444800200245070380320424505c1c04101049000c02034505010144c03009250036115000703e4401d44254041d500a0801007000c4031442d0b03580e0400074080c15200803003e01190300241c4a15500429009002c20a165a16610300c0c1d40c81c0c0185031840c100040c90300750340c6142d84040d0606640e86186040c20710b1044800641c0511007913004000803030b422107020000c19480b4007241390003641c101503120300900c84030200503101c00c0f0b07022004016001c800d000500781c410001d2001e04001250740507218003101075031018841d41d2400010340b0785d4840000c1c00c590681c0042410802480d10000914588031514107490a00d0143c80203d41e81d4034403c85020701040440d420008202c00c80c00c0203d5007d0400d2030000541e034a000c2d000742c041d00c200c0078150024420010701c401c0588801c1801c840c0310340761469102004290f044810b0080840407001c90020b26000c94400c461446401f410404681041d02e4520316199141004201c8140d049002818001 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 63878923 1250 63877673 63877699
    0xd02030a05010216110402030106020a03110c0307090905061515130504020408010501030201020d020a0b16110601030602040f0603090803060103020310030503030103081801050c0607080a020d050c0c0d0206160509 93
    0xc3c005000c00482d03480080b51040c4091800d1407402540144043c016841030004000031035002900056141c0c02d8148004288802d4204a0405072107600340d94252091001c00035a291050f03020b0030509010300c09a4000340c489154219552500000d083d90008801e01c0c11600d941e08000140101000d940c4242d2049940c4c001140076030304a0383c48516182d41d110010819540c0512800c1c0c3c0c49881c40c03000d0001e000c04c80e0794079840280050702072001c00031201500c038030b0240135500300c071480b95084085440a603524502200a0350080c0116010590040400645140607000e0b401e0002d41c040c1c0d900342542d4620380110300a400040862036a4a8500380010103c7d40601c0294041c5006040c101d5440d040d041e2140103400d25058401e0400c1010010a00c03160004078209400c040e442ca4903518a4450714065030190007030307031440201d8074034003028010400b03c9a8002d00807003100708151401c803c000c00e13050b81c45080032140028036601143c00081c00d948103c0c003c1c42c1c0c05074014040845010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 63880173 1250 63878923 63878933
    0xc170c19180603020f060313060c140c1c090503060c0903010b100e0102120c060a050702011b03050415020c070e061c1b050f0102120304020d05120307260103020d02030a 74
    0x30484a40c1c0100daa038a900034415400c04a610a0601c641903401602d1802c1c04046140a0740749035001603c1907503503da2100b100c2e4440ca0b0b200e80005c410500580d00e030b114101905072251703441c41d46800d65600d103010b55400e1901a0a03081e0840342e0081c09068a0382c0c8581c103070f8040380d00c822151a415503803022400038a070358090384900d264400342e0b04c0c0701c01c1c407170400006480c0c103d8a81c860013107282c040c40256201c060005109610034200e03103020440d51141101680940b417540d5081102c8010704100d421101e0b0706a2003540b045004a640c03028251400003248100c0c80b5001110340503800c1842c3c14000050040049070300080d01804880c03c40040450442e00c46d1035800d001c40f1810340601100c03421901740481080a498100d900080c01c400c40c0700040e68920040741603803e0030308048001070540d035440601c4446140c0080544e43d5031880f403100b40c01142c1c011501d040104108c038003029008000d00c5030043d884070300607400038401d0342180c0800860100180c1e007268588100781c0f81b080061 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 63881423 1250 63880173 63880199
    0x906030f0303040c0e010602070311100311030a020703080606160209040c0f1502010c110309041d030a050c0d02010b01020c010c020d0c09050105040b010203070804050d0c030b0f040c170c19 83
    0x44c016429a5412030800303519601450040e40180c2c215400141c0a01c045203822340b075094241c0c0120f032040041343c5030b8041640604900486229000400b10400190680301d80090000a10942d41c1c07140c940daa01d8200700c1c0074022854020002800a14507000500345400f4840e0000c1c00382c100b50590317580d5903140c00c4007091b0f0707504140b006844802d0010242c0f030b02402006111040c5080c180c080607801c6011a0703481c00f880040c01c0c800d980352584609111f10480718409112210300507a951500c0c10140508160300c48140c586481c4510b07060314081d030344103101e01080000b0580c0545018121403004496551070300b00c060b603210385000c4002000980c0c1d0300c1180006d0250348070214103036150000300021101d0124901e41550801c01000c40040c1000080710207551084030614040501414880c0000d100b507003004101c100500144190203840c020320360703c038070320400d0402202c0e6124003190606654a107030301b510327551004801c0003192400380c00505140c40c00c544101440b940c2d41560031162 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 63882673 1250 63881423 63881431
    0x90f0909050307080f0703030b03032b020f160c1a0405040b12060403020606120307030806090a020405090f0a0f0e030a0e010201200c0d080c07060b04021201091a0406050d020906030f0303 82
    0x50b0705c2c0040c2c680704058160142c0040d030380045000d14100002030a01c59a480d20a14075004604103040b881400002c2c41ea0540d40a032010382c1e0300c1c07900e072000f1007420b03100c460b0b00381c4055031034494800340051300c1840d00b001e213043c144600f404c4904061a050030320014100010b009035215407504911500e01500700070842c4524003d50007003996040ca0700600c01009803a05100c00c058004005403000b0941064405410036130580b0702d401c50b56100356000c4003e000e190407080d070200301d00003406503108403050410f0244410100c104641c80755040703080308407014080714074a0350b0000d0003050f04140c02a901544a071406000114175040880302280040b00340c407101010401010643e241101170400c90a0624151070800020f1070902000c138149900810394000c019680b44c01d100c50701a165601540c42d4211030461070483c41d40c441d08450b010b080540141450405c04007801945480d160044d02d044801c083c001c884c0060054090001d54500100620740610590340131013040c0c84208000c40c86 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 63883923 1250 63882673 63882697
    0x1e050307150b1c030905030c100e030f0307121101020405090c1303050d0203070308060402030121030215010e0402010f020604110d08090a0902091903020a060c050114040c06030c090f090905030708 86
    0x65500f4626001d003408003280c00c001d0095025891840994131540796060704030100b42032008600380e1450000745440d00c8020003420701c0c040414003074100110001c4201c1c081120307446464209004031a014200d00403480741917400003440b000708150040c12801043c0c1071412445203caa55182e1b1185031401c0d0402c4902030050340002166024142d00042c2c0f242c0010003214190314551400c20b0103482084140c0f4480030f942c40c0d0240da0004c240c02000217044101421100000a43e5180c490100400e011681640842c1540d01150a0b43c0d10100d421031041d640a0200741a0426441c01c0c42a40c4045000465458400300100c80301d40d82c5007224100188a1030b2000342c3d841402c001400102e86400c0901c000c4070f18500f0080c001a981d41a049040d9400d62404000c2e1100380d041040c09040714441040d03030409032500707000034400004062025140c885d282401145180074003210407901a11442e114955041d00600100342903400844519010308100ca0038101c494075103004592200100c520 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 63885173 1250 63883923 63883969
    0x20c01060b031501090302060403030807110d02210324030703020a080c010306050a1a0304111f030e280503070210080105040f0203011d060102011503050a1e050307150b 74
    0x40d0022002c010250005002c5c80c0008000c1d00e19400710700c09000c1c5005c0101804000380020b5111441152075850311120f00080340c000390300d81031019407191403107218400c02d0b11000441c200d50030313401c02c02c5900908c07440e2200403e541c0440c8500c00540e100034401035240c01440e10020150f9140d0400c20050550140605201c00490300050211030890f40880d01030710b94054100140141802091130b04d9554506942c1d6954440c0342502c0e0225281c0603881c0d100001d944180c1e024800b2080d034400300900d648017009020303000314a071641d400342819030a003405210070000100e605180000701071f082c841c8003180d082400c00d60001d803541000d036440000048031140104040d182034040c000e04e00c0820f44c41149994117103c84040710150440c040031030450110003095403070b4400d6102000001d00c844810300d64903204d2a2085e182d5039848001c0d141032080e01c0c440d9000400e1211030030f49007607012005500e0102c083e960074240300003030707649907007560790300d1015604945520656808505180652031 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 63886423 1250 63885173 63885181
    0x5010209040507180909030e060c06040209090115060c0f05010608060703200904090222020703080609060a0e09010b0a09020c0d02010605061e0403050f0307020a0806040210080a020c01060b03 84
    0x11040300c200611440403c2050040c128140d0031307050030f01c02a5281d44a02041e0f940c054141076620a081e1a02560024000075a2000c541307404a86907021358070031074049000b52541744190703099514281a07001542010780003004420b00070f44121080920444180ca5007181d01d459007801c42d1070a03400071002d5004201001a400e51610550280548079410080b0780c01c0135548074070240c000c40141902030b035502c80c14681950346007501500c60f84d02d00001e0214201c1c1c89900e01d806900b00310030460100b921034010074031520300401c00503c10711020300403629441c504142204c4207200900501c7c4107550b00c3e592114103403151200c210140010345d902603541c0807510380c0c05180100c4c070a500000c5900d0058107003d9943d0381c0c1d080f00c1300c0314548440ea0000e003000703038141c107146e2040da80010401c0c4120404911413040201c0a0030106008403628581150b4034001a500c0d52001c450085d40507010310030b4003000600030b9201c03d81040301400c0041c01c00c000e00d4503d900719030182e0002050700708040100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 63887673 1250 63886423 63886429
    0xc020301060e16020706080c070203101518091208180111070201080705090d020618041a040608150a05070e090f0f010602030a0915050f0d090501050105120c0409050709060305010209 80
    0x11034030f980e480e01c0100303100d42c50610014201040600200a40b01000a00c00250b66040040029510340c0c1d4000700b240303151003c000b07001d01c05548500c4401403180e2504400002062203000f180d960401d40f450312000130200101d0303402c800103100b10907146c041131415170114400d00c90050701140e200392680d6195503078000585244002041070342041010841d0500d035480c0c0394008401031350f0540b43d294994084180c001d08029058000c542c00030714010008a0030400111008174200050360104407240d1180c0c11651210307150750181c000400324501203002044260306c101d900071302da850051925510140011020b0304203a032521300c0a411001031041d070f18030002d01d0500526440c00190329140140e030000e84072462500c94402d20110500090003003a004070200e400060300301040ca80d49083c440707040402003242d800c007a41c06602c1c0000114190074455141c05c622845500100000341066003008013525400b40203c45901503044001038001030360280c80003640c452400580c4654400c014 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 63888923 1250 63887673 63887701
    0x60b0a051206040902210708190c06110d080406110f0a080109151211091306050108010203010311040b01031b120b1005030c1b0d08010303020d110615010c020301060e 73
    0x80e0034859407800140a0042e1b0301c00c4800710074520f8400041c60902901d0b0f0109050540e82c0c0e00012450007888210400d0162240a26184921440104000781d1702e422080b21301300303144095007400d41c4c004195001c0e15409a402d0f0fa134003610400c000b007040c000c0c1c0b404018060304605490045000003140c50600c132500016203e0261420351030800c14005681da55220601043c03044484524115040758184031000484100006002d065810700d400c02028004505124140c155000b030714100c00070a0811040c000c59040302d030410f035041e1540c1c02c49000c0100400003400c04a050507900d0400d07840c4540300544134861080c4030b8480350490040c03a040802590400311850f449088044643da4001d50807200352900007948100c85071310b07140364880d0304810400c0404149500d1064680c922021a404201141601d1007a030942e0781060318103c3c00e80da526400000726505800c11000100c040b8034103480d580401c0350515052191404a8020900716015074018550095201d0100034103240500b00c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 63890173 1250 63888923 63888931
    0x1c180b0a0b03070b071103060f0405060c0a09090c051306030e010b0603011a03100803040f0f05040507020a141e0d020105060108070203070f080d020307030b0901060c030801090f060b0a0512 83
    0x1400e2201c100c039000000e883d00041c2c0104580c0420200d480390600040403041805100042d084440a081c00038440390350410840b03046030f0f180f0074440080d010f20300032401d0321a20324480d10307505003081c01c01c0c0e0b0b40e501904442c0443ca040201c00e0150040403450761607030b500240250f880024034a80380e0503105003991030000702c03203000e00070400c0100840d8494003860300305101400c08003038494580c1030780c9a082c030b91070b513101007041e100100d0040354070340c0c0489205084940300790074020351566810500094410403903c86016070401c528180114031031019800c0e0700010340c17090b90303501d1901000003040c040c503400002c240303540003441c01c01c10941c0920409820040900308019140340400000f9541c0c0725101d00100f0340904100030070b0030004810300355880d028036000d0554030381c03810360b2004000b4069880b810b07108101c0c0740c000280c002d0160f480351000da07030155140c454680c02c0400400103083c01403007880380c0c1c540c4d400d80020800c20b100d01a001019040d52405d03039402102c1405442d0400c0a0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 63891423 1250 63890173 63890191
    0x13030e0402041a0c15041101120c05070f06020c010e030c0705011b061a04020703120525111e0d02070e160c061103070905011707090b1c180b 62
    0x140411480c241944040f0074090350802d0780c035420750003407600700388a80d17440f0004c0d1440c00c030074807080014074040510746040a0340d50b00b24821a1120660a6070001100d207404554204001d03808a000c8007284081c250241d0b0000d407420303654144503401c64410005100c1c90350002700d4454007940003804038100030802481d000188400025050568100c40040100110b45e9000b50340080c485d1aa40c1c5200004000d0003103440d036880f4240605103014248451150038600f400242003c4000c1402d401c0b20540d200680100c2c001c80e100c192a05511405104068800e00c44a2109400081e480b0918000c660b009400e400381500e002900e031410316000103074041040d0701003082d035038081c050460102c00e05103400d84502809090001c02050030001a40d1808400000c2240885c1c04c000c02904803002a0303924101a0a00d0100c0300b04e202c0d0a49000c0d001030303d440e0042003490400c9014200060600d1a507408107040c40c402002117521b81700c81400c0145110f010841030041c400c122951081d040c13 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 63892673 1250 63891423 63891427
    0x10609060503032512050301030b0603060412050a0e09040305070b0c0a120216020a080c100c0209040b1e0403020d030606020a02090118090209010801020403050c030d0228060513030e0402 82
    0x71000903103034014018886290a4140b5003840700000e001d80308010180c0000c9001c107440f0051100520581c003d010640e210f03181c2c81c0120310281000101c46121b59044090084811000c12044440b42d2003000c0f12410030501c0c0d07002c2034190751054030350740c0124440c0d02d036540d55600a181090001c41c0c000d200507801c2a0038440032841c1a0042d40d110340181c410000165140402041d5103140c43c21001d0103504140e6401d004103034440002207001c0040000c481003040c10300a00811a44240881070094000d020040468005804090784607040459510454843c10300512003061000c400c80d02075006900202240c06623940504c40e40380681420b10182102d4070064002c2200c2031010301c6040d07000110046100c2c0c1e400b034103900c1092425801071441c54a940c1d03a0b80390368040c2d0031901040c0d405010703c61410071507150008054100314000e8014001b40480700060350561151400f003011866582c5414000181c950b01c11103100b40e00308007803c0f4003001c0e2410f004046165140a09016030f00c1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 63893923 1250 63892673 63892679
    0x12050f0a03090501210f0c030b0f060909090f0d0201050f16081b0f0d06031a0103120e010c0f0f0b0c0a120504110307030302061902040b0403020108040f120e010201060906 75
    0x40042e070581034400030308020031005100c056101c0d168000701c0c1405402841e00559110b40180794200000d0020140c0d0180a46540701c42000801c100c003036400c5030320490410411456040c400842e6a000c0a42c00585208105a0709034508103802d9994403001030755100200103440f5090410f0b2600b108a4446440700b0b03000c0c0e844081c282c200080c1c41980100c05030400c00d0183d5968608641c4c2c0001a488040e071603c50404041003e021207000840c0c00e4004030b03101000c0c001c0d03000c1d01c45041341c6d0480c400c0340c0c00b81840202601c541110301c03001030400126009030808540c08500400015215030400030b881c98044c1800c21910101070440512454104480f1800c1648003421000003ca01c0c1030005090321186804890845040429909402402c80000615030041075451040c0c05d2021040c40c041c1c58049400103d206030702402e0207a9070140710a00265114640555015101e1440b0f502c180840c4e8480c507549111964000740019045040f00c40e003960b0a0140c20020001c03a0320900c11303241 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 63895173 1250 63893923 63893927
    0x60c020a03121505060c030d0506040b0315090102040e0115030b01020d050a0e0315010e101401020715050912030a02150433020309070f06051201090e0c030712050f0a03 74
    0xa503040c0110002d0b0310380220140f07003043e0318010001400000c3c107055907030f007220700701540301c0c0c004080b503001851400001440a00305401898179204000b000384ca182024002e00c00342141d406003035201903650910000c14400749010650703010305401a9102c44203003201e0001010303a44801200c90442d0480c040e280a942d4104041d10140c410a0030804205440070b03000c00d00d416070400b1144011203000300001241c0c840201d1450003000e403a12681c0607681c40f02c8010104000101c0001c0c0164000c2e202001600c18420801c4d14018040c80c2240c500110000010304000c01a800e0350700c16000010702007081034041110341c001040444030035030f40d0305d090713101c000012000f540c27684840c0105004040402d5000210303400c00c1492504111f450b82040811035540d8900c9018441d620004658081030160285003034898140d0403040c4505c0517800e003a1070001034460520304926078032505580c0041c0d0b170b07024800030f0060003808542034203142c110704105191850740b01300c441c407940041c400c04000caa = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 63896423 1250 63895173 63895187
    0x2010912021b090a1107060509060105030712030302031009090b0702060601030603020a0b090d020a06030e162301140406021f0203130b07020a0b0c091005040503100b150703050403060c020a03 84
    0xb99003103500400ca0303503400100308054400520811010350f4002410300800607198041c038054050b4070229011aa201e0702072603501c940e1402800104034241c80c823900001d100707400440c2e10290700d4202d1061242d6410f40802691038200b0115000c5135040c04100703283c0c0d410004d0340e03413211003441c0c24000d00780786401003058201c050040c542d100e01c1c002450802070300e0310b00950003031700d42c050081d600050341c9240040081041c56101101801507a0341c2c200c50308140803001c1d05846113100800206440408114038003410814000c0c103005402e81010f1440b058100540010b002640280180101c49060b00030309010f4020100c1c900c03031040c018450380f10150a840031090380e2010380201a0344816106130320301900d01c540180704a40d610200300e110301c0b0403806003052280070b903500d24501c2e0369540c05607210f0150340034050b010703400f454040c40280542d40013211b00d420090625142c0110030010240568001001034012560000c1c04004201c10b034403401115074401d201a00a0803901d0740c4c010042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 63897673 1250 63896423 63896473
    0x30207150b0a090213030209040b01030c08010902091f080615150a0c021e04050705071a0601080705070812150a0806010b040e042906010f020f0a08130e070201091202 73
    0x24136404503450740003c00d80b429000c00f0310340090210680345064500000300010901003200c20400c03800703000568000500a9030391050f4010303d8007901c0d079140301c0c0240c48101544081c81e69107070100c40007d61900288800d17030094044000c00094441080103004481503000c18200a81d40e04200b40d50b0f005601000304180203504440706440801c00f061340b101c01d0828140c0d038580c410719100612100c0390300a8000d00740e5921030034000798005ca00b04803806420104403112400300d8a000c00245065204c0c000800d401803040c40640d092000d42803007850704560407103140400b4034001410440c1483e03c1e0364981d00a202c1c42c1c2c0181a90340c186000040c1c6400b5500c00c2901150000021508015060030120b450821204001d64003082416060f03c803040152341c400c1c04113008104040308144042805141c002100c0000c004003c040d94440c1c81a9026400118840042450200d00b03000e038808101c1c042d00707a6500120348141103081c03542c1c1000c01030343c1c01070941d0b118040407110944036018031803a0f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 63898923 1250 63897673 63897689
    0x20c0d0e13021b100207111207170f0114040b010b0304031b02040617010f05010801090803060f0402041a03070201060603060e04030f020c04150f060203040b19090e07030207150b0a 79
    0x141e01440504000d402080c028420190051040c1c80c0c12900085e40500308042c02032091241e8010311009225410b40100c007211070b0342d000b948007400071a41003091580a0700c1c002e82124005040c0b41e03160750031035051245a102c1c011103002440140085001c080b03001d000e42d10281446c6080c20760b4040c0c500f42c140400580c2c40d011407141401035569036440301c0010a007803a12051850740c00e0711100c1c02001c1d58100c00d010703039260000104044405114000c8000da00072a003503c4d5031a0902088a40e440d08205543c0c0a5020840401c070590607039002c103200d0107203d49260b2213007000100a420350724903400240c01c040c9031190030051000102003003a00242c02d41082c04003100b4000080b42050300703424080750410708080302500c80420000d42081112609d151055050341c5405040b6140d218620920031300344010b00c0306208401c3c0d2260710100c0040c15040c01030380070703036103003201440b5a00c102c55641c0440d07404034006c0b0a00120346003d424458000d01c0403c41e010944000440141140c008e0181b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 63900173 1250 63898923 63898927
    0x30c0403030e011704060516030e030a140d110a0e060a0c08030a06030b090a02010207171e07050d08190903020901060f0302120c0405010f030c050405092701020c0d0e1302 75
    0x145034040d014405504160321104821340c80e186c1814805000242d50704e07440d0b030341c0481036403448500c40c0c8900c0e505409a5806180341c25401c07235045461603107058060703a10900c01c210120412009126a40080d100600039585504140380060320051044500768041d0508200101a059206015510590b4800341d01610394a80402c4d640040ca482d802c001d03c482d0b020300a2080400000422507200381c402d80c2214801c546400c41000140000d40c4040240d03070192104080e514000b202400c01103821340200c460703d65079000058103e030300480d01552441d01c00950400c0140b007207000e25040f11040d092502c5c090349968041000d111051181d8000c000c00710040300a080d2003601240d1058101d02079601e8a81007c0e503640d1000da00a11899001c40c40c202107901c00d00c3d00a00039180b005070140c44150030146040184210108010000b030300c44507020310344020681c12030321000d400c010f140000580300c42c3c02d004650300d095001c04e140410b0080300c080501039a030351300701084a02d201e8a80050307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 63901423 1250 63900173 63900197
    0x90111030702130b0f04060807120516030f030314040b040201050f0408150702010630060608061906050d0b06060c01110309010911040c3006030b090111030c040303 72
    0x240c158051480002d500400005443c00011515003080f142d03413204407500b440800035501000b04807031451060301d0b0700c2c0d00070301c40800c0300f041c0700600080c100780070324155201044200c400c1800f00016800032192140700b008040700341945403081c0d101118048d50074203101c0c18a0786604003610f400a0000307040107400251184808104411740c1c005020003c102c4844c00d00c1c07850305020f0303158101c0b29140190310f800400a6443c030040d00720003d840a003061403000341c000f540c44c040300c00e4140700f00780c0e80c0f1911341c1e000040001003009602d114030048082074a40440054811007070750070b00e501c003500c101c030a00c2c40300001c60816102c841d0000d6003161400d40c0c0f520f00020460243c07090b44140c020025001c010880e1212040d005080194030a1212002c101d15410070802102e090440d0400020741540b4162001605a444420360603428921801c406400c61484c030709868913034100300c803000d002209020101d00c00340140e07810114498200c0b4154a03000055a0f41c50165101c00340800c0074060680c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 63902673 1250 63901423 63901457
    0x306030b24040906020706140112171216120b0609061803030c15010e160c030e0a090603030e0f010806150705060c03090d020c01050301060e010311071a0a0b060901 72
    0x40120715102810a112035102c81c20501c0080d000444299000c908003c10442c50b070064040c503d040c5ca4816202c043c03841c0c1e50b41c9130351440694070103620071911401c00400c803d5155a41c00e03a44202170085c2070700045040f400000341400d00801d090135699081a40c1c41c146a6102d409445604805490441e150000c440c0040040e40d80400b00f1609400001103180884c0c10200300100d21429800040f107541e41e0314048248650001c40e80749c1214519008000c4085100d908442d054900030310b41138880241450025900030303166030103911116921602001096004801203003141c0c0111341915a44a104002070b01a440050030709204101c0031901d16452030542c1d043d03540f03150300001191700c0c500e0700c4420950b007a40242c410301030f40d01c40c017074505100501c00207082c0b250b450183e540506507460108141c890042072007805050580b110111020503407043d01802002e40160049501650114030406140c41c1c00b4242003a80c0b818600c0340c031850b482c1c0000700ea83c144c04c207103011800800180703a0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 63903923 1250 63902673 63902731
    0x402090616030201020a08010b0a0206010501210c0e13020405030604140712030513090903020a021c0506090d0e121906020403080c010f06060c03020a11030c0603010906080d0306030b 80
    0xd07040c0c4040044401c6000e15034154081d203124540c0e5244c241c4c1d166280e04802c00240286849403005a00c0702006100719442001c001c8a10b11404615481d01c3c400c1e0040302c41612442c000c0d010000e07080709006000c81c41e01210030040d0701c0140d20210716043c10003020a4031020010070190011a844034001181c1400b00310020082c90440b4456020f2041450000d1099024417a41c2410720f01c3d03d4000300307244007584102d03491a541038004041d0000c0c00e40c20f0040d40c9107014288010755110201c608045482448003500c1070300c0c150094031604e00c4501000d8084900001c0c0d0034040c561001412410201c00910310840c0d0940405c02c050306940fa16098002e44a1030304014681500031074540c200900540101e10700080e41d010600155480e10001c403101036600c031015006030300481c0e1410104402158660341400040c0503540d50150b0040410020350003a404002c88541c1c4e60303001c0084a10510804903981042e00d01808028510b8543e0100b1a40c081c00240c64031424266141c440c82c0031640d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 63905173 1250 63903923 63903937
    0x906060c0607050301050f0103020306060702040f020c070305030d06060201060e0703020c07150c0b0108061b070602070210110606032418070602011401050a05031c02010902040501030f110307060e04020906 90
    0x8450042c5071602000340140c2080c4100360280320010500d0410f503001e402642d1007100301400b85401c0508940800c00a05661950701c001c0c264200503070000c0040903c2403070003450080d8000d5946001c00c441900c02c81e001548540c0869242580511800c05501f4440d03800918a1502507181d2070160710041c10300c00351343d21041e181040c8202c88101140c102860410050284607520380c2e980e40c07010901c2d151401221802d845040301101005482c2c840c1c0301410001c1c1c0240c80040c24603081e0b0b8085109665181d0424001c81c0821000d5880c22a0400c9516441202603002d08019002d40112450f00307031410311101204090f000004000080f03a00224054000400c1210b150590303039040a4028145841003080324030200c80007240300e060102a5000711040607009080c40c802070070702c5002000c16419041d08554840780904003680e81c5010b494080e5000303680d40e6030008080e103080d6603146004214207019802005040080c00d410030f0a40d074601c44161030140ea0f40795014001111885905 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 63906423 1250 63905173 63905197
    0x140a09020a0b071103070f1514030c0a0903080a0302121509060f0117010b0a02070501020a02100f02101b121b0f0c0f080a0809030711190308031e070504030b0402090606 74
    0x647c89042c1d020720084441c100c9405840c180404c1d4116100030000c0b65003611400d01b0030204034070800034001070800c02d0700740ca07220100c59101c1c1d440b001564004020040025004030355801d03211000b4a00b6600b22040d440c60301c030701c6004d03e80410280e1100030440d920840f12240e4061246e40200300c0200105450820700c00301d5a111502842a0b406c101c0e85c000c014814082c010509500020300c0d902000d80080c060030102140f030300200d911a032002801c1d011800b8080300c014196803103000d110f18158014906040400741040c000300728003940d80b030a914860901d50442c2aa184c1942d00c1c003280f81c507601c0d0040c080504520181c035080400100200341c54440d00440041c030034031001404030007039950385148154442540d142d0340d178010f201020b00914848201e4042c03030303d800c9000000c500b0110040c08500396a80d100c00c0f00382c2d08111940c07088000b483c40f40c4401a04502013090b84a1079074201141400d0039600d5642c88100000c00007400340c40b8480101c2c00540c1d1b00307020390341200405 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 63907673 1250 63906423 63906433
    0x203010c020d0210180b2e09140403081503030c0f03030103020907020d02030d1e0f05090105010501050c0d0302160602160323030a09020f040e01140a09020a0b071103 73
    0x940360007503489450829960041c010b4040644d400c4440e40600e0343c0701001543d9076094820951203404110801030b04031300400c543c10307001c10002039407109581c00740b91088107040c184920b020105015100d181162040b00000c0e0000c1000003500f00c008182c100b4048208003010301110004a440c61041c09800c81d03841c0700d00c3e0310740341381c04500100450507288241e807880c51645690030242e075102c12117030612015070824821007035220f80d1588004e2003014400d50b00b00550f50b25041c00c0c42210010020002655107550400c0840b0009024850040c5800e2070068a48454540410b4480e0900e00c00e04003015000649001040010302d1483d40058001004668518801d002041001010002200031540001038441000b454505100174100b40c6004e0340d02d144d807070000340c0f00140b000b07090480c1e00810186100c03261380c1b40c034803c5040703044a0300000110b8a50200c1d810407000d000800010586060040100050b01c40b03034120012540d400381800c0d1180c8a501d0003c196040c03d6401c0d03a014451 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 63908923 1250 63907673 63907691
    0x6050a0b0403050c0303030103111e1306030501050f1b090102010207020901080c0901080114010e0601051308100b0f06040e06010504080307110108060d02031518010e07030c080601061205060409020301 88
    0x6094001e100322840b034800c485129803003200f49a01d0340400d01c0007401c184410400148581001c2002c04440100c1a1036152100280c00000d6000241400003e4940d0399804090040040911074242c100040c0004d1100c1da1502c44000b0b0004038040d10180300c0c6d20004103946d5040e074005d40580303862550042540100d5030b160014540d031001d0800405201d141400c0c000143d80038188941d201003002251880f103140c0c00c269160690f00c2010b008241000410480528841d0400a001c1c0103016144040c1440d0b00300d506440054800082c8910310803201050008050366035141158101c4004025040c0e2503a62000161420300407a40080e0f154000000d0002c208080c802000228240c2600c4250b12501c80c0020310024020f1440c0c000d4059000381942422680400c02031580300c00c00812409003031501c08040350960b40c810140565a501112090003000505580040a00304400c0104a03039850100003e04014030900d00c00c03065543c030000300d80075407100d8100c030030f005802400038810010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 63910173 1250 63908923 63908939
    0x20906160204060e010b090904030e0d11030f03090105223602072f0301020a02011d0a0b0705030405010b04020c10140106051b01024006140a020106050a 67
    0xa00c000c0c04034821490311001284002e0701c0d51070103041e140d5180c0a0784c1420041c1e0103001c214500508294148000700c200814695512030b100814584203203841c0c5408410101450702e050004c0c003800e241c81c0c0090081c0e09960764041d054800d1790078801136050403840801090b254603207080d00315a029207592080d24521040300c1c0e48814801c4030141e0024001000145d040080b40912600100182070540b282c03081302101d90365084540300800303048411040031a00183c2283c0c0150b43c13080240c0d44424084c490700c08d4055174591194608005440100c034a07641c0c05107200300007071211040c0040800802e0a010b02544850f81ca40d0001c0d0046560b004412049070340d0f5004c2a17881c0da0041d04010114030001c100c2c030400307412200a0303281c0d10300b0451070210792180074424011b00650b9640c02c1c04410046041001840341200440d4030101c1d1580669404200c18007040445c5500e40c06241000c00203d0391161800c040d0601c49502070342c480d003e03e00700328003600d07859020a07444941c114010030710751 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 63911423 1250 63910173 63910207
    0x60304050a1b05010e0607170412020f040504082704020a0306050f0102011a010516020d030c03020d11070311030a0b070203040906090923070e01060503180105060904021003020906 79
    0x290140034207a030300c0784103120403002c1c68a1030b0040038002844942440d200d070801502030040b0718443c401060042d0001840d075031490304168410074110442042c0e034001d6043c55400c0358030703016081e542442a490039888003449486200d400c1c484030540400300c14030194074000008415800100159070302c0450344401130140c8110300405220341e102d05201c4640c0d600500c40c10b9000038040c001820680150f100642d4140c20090102e1498a180041240180d990321480459140300c0c7e25820500d81c0342e410020b2502c03880c0038850040c80503843c400c3c2e4070040d00042642c01c4907030011200d540980004042420b0a0710010001c04611a60003444011030f004009001503600a1004126499880c06076000380c82c2030842c090501c2401e4001c08060101a40821001d068500202c641c00d039910480e01ca10341c482680950300143d004814020085a40c2550080107542d407002400b0a04200c00022403900000e48002d10441b06001188401402501500c862040045c00b840c1c903201c0f2a44901000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 63912673 1250 63911423 63911443
    0x20607050f1f05060f030a03030e01020d0608070303230414040e0307030c05190c18020705070807060e1203030a0506030118030c06050117030a0c0c0e010308090a0509060f091506030405 81
    0xb504110010b100b9091403820711011000060040c00e0500340f0b03490540041041012449940d5003c12016010103c0b90064800814808004049461540c24002c007548000401d10443c44002000320b051600c0740c4081d40c2c140c950249a095048844c040014001c105549045600340004a4528285600b04180810490085081d2402e8200841103a140d01d000d80000034034101c0000300511148020884900140c400660010702e414015110b0710f280140590010a00da401400c05005542d44407805001c0d000c42542c44040c2d40c090010700540701e01001f010840c01030382c4e031350011741d803980c00350040f0043e40f20680d0a03000c0e07195070342401800101c403190140c2c4d1640c104800003403110341c610100c4e21040540ba020350306007a043e5000b21903140d1078860544202030700c1780011604000088107240218850210542e0314514481030050140040d40b08500c034030004000c00c101d07070b250008111041c01d41100d0b1450707103949030a040c03403281c14240051500800040104400c1020001e000415 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 63913923 1250 63912673 63912733
    0x40506061f09121b0b031906050105070308040c0f0f0503190f0b10081009021306030201080a0f09120203090a08070501090e0703020c06040c0906060516020607050f 72
    0x102000a80c000404a00c807905140300003a280001081241d54060414000c244103030b41244410b01ea1a64070110305281c0c1c0c01804d24110000180040c1c80170004000b102041034402c2400f80e1490400007800b11700a000000d814006008000b9081024411441000d4960a44800182d98072508000f19001c89400740d5400b07440754480d000c24a40000303103403401140d030005224050051a0740c5e1074040d1070b80030300750004080002c0c401040d003890a100003051a00c4102000170814039500400140c4034100f04007072143c903e01030003400941d0380300b211a80c1c0700050440110350300505030451001000d503c100604040749200425a84a9020008000188003180c400c4211a100e50401d5140d181e14483c60703001c940902d2040140c01c1071002c0141c0d001c0460b00700103052a0441d03403918100341c0c04890460742d8141e0040d00307005800c894403a02c0044d2240780ba1a80c2090031349403445000568401e4007030b1207440041034980c100002000041e00c85603106042d18245a0b0720400843c0001d010140c0c014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 63915173 1250 63913923 63913939
    0x7030216030f0906030506030c12030f0a02011517060f180105010b030604050603070b0a08060607020d0308040201080c13050409240212070503060d0b0411060f0301081e03040e0c040e04050606 84
    0x2480c50300c01c1c01b0303041c05070400a026100d801e2003c002c11074000590014000180420310103501400c100070090f000700c00c92038001060760304c00481e442c442004c990704520324064255000040100e0009000c5070300040003001240591150050031100010205007060303a582040000320340d480c80b20b0040e600a0b0b8041c0d0b414803050321414201a10b580c00d038051054005070502c440d1188912490600390041d10180241d858140d05401260b08403c03d07030420b4000c500d40388184411540d100703042503400b02500e0800c0d801c00a18400c0c04120403018461248120f4a480c0400c5c20300c5030410f2000801070007112031254841451081c003010350051000401e20800e2a0005907800d801b4800b100c1c41031000400b4008107440a0b03403045c0300c641d0041e0041d28004040d020605c013944800b0002c1070100c0c003204466490b98544446c41317180040703d880e100c50100321941010759004001060328160b80c0d601c2c403800d001c0da4400350580d5041c05254000803d904a03241072105000003c20f4a030f010f21425030f240c607 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 63916423 1250 63915173 63915179
    0x42a0e0108190b1302040608010b100302040f0512010608011404061103010b040501031e0e031b070312320d0b09060105180102010603020603040b010f060c0f0b07030216030f09 77
    0xd41c40300d00190425201410035902400001c0410311144c0c0d21204020041c0c49000d220380105044414541100780560b55410340c1e60323100d25000d1208980454586401d40c94241807655404001c0140e02c0707100d000d10401c80307500140c0c0744c080d0000d502a21084008004500080705c000c1480719003a00c00ba1040d0346001c125050b041800c208070b0b4141d400c0885440c0c40c04c0d2030100110020100342041481018190040700d210038140d00422180c010444011900c070020400524010061a0499045540035210400010300075050b0791071585400e0800300000c18480912100c681c1001c852140c07010040440801c882000d0740c081e24018030a18400c21128120341c0034402803500590740d40303010403400c1c405401901340550058400100600c00840d0441d969800b080c4560810f9504440100035180140800000d66000034000c00c21440d0030f0020410544074801150304015000e040100c6050001e503055002c1d4044031400400072451b03114a03249800c00602800c030b900c1010300001c04980e000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 63917673 1250 63916423 63916439
    0xe0a0b0c040e0117030c010501030b01061701030c030204110d05010f030c0e06030c10020123061c08030403050a090806090f0f12040506070204150e1905040812042a0e01 74
    0x18900b03503200e07a4a24255a4201400c42c0d89a80350618040d0803031008000110101c1d00070702425001f180321b007e88413250350405502401c070384044a5000d41c86070308800101301144c0c245800030201c4ea010794000404030381243c00310703074903100700c4251411180c18000000380c024140c0039602c007181e01071600300c15119120034a0006100d4180c5d0041c0e410360040c0d0003800d440c600380304c11007005003041c000040c07200741c2d00f22105940d200f80c0d00f102d1401440202000398500b04a103429002c40c412a4038000800010b68840703440d400090f01c06820004081a03042c0c031a409a0100005480000100e495a140c500015940c840e01800601c0340c0d0b014900a01c01203c10004509080007900f03450a82883c1c03d060a200032a040340b041649c1c0280c43c1c0b8445170340700c0c100a114201402c010110280b1500d4050740b201002c403100d8a56900243c681001c00c404142c0c41d000352a10505180484085921181130030940016850b0350400c0c001110044e206031580e00705182801c585990603005a260b0782d540c24 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 63918923 1250 63917673 63917677
    0x7030b060a020a140102190305041110020d0305060a0f0e09010b240d020f0a0504030512180f0f030f030c0601080a030f050c03070515091b030c040e100e0a0b0c 70
    0x6100050b0f441600c01000080e828881401c41d0000f001c001030801a14030140341501d485001100c001c20381d036106101c14000c11640005420310b059481205942000340000c0d600c0d41c0f203801c41c4c004c05507150040b45030340d40c4a407208001488150651441d00e5161900c001032001d055529180e00d44c030341010140349084ca41030461021440342d174550034030300c80c100700c0c3da00c0c60b44840495050903500b00240c003900c228040141210350400c2d076407141c0b10f43c03c5261251501c101c42a002d000e511090040104085001084040002099402c03101c007503011804501a000341d010180d615006101100b03c5004002010b0301d00001b4410441d819641d071140d0450300d034881904c005c0c000515138420b00d07c141740221300401030f207100031003105e103040c01c5a202d650030300d038804d00010f80e01c0e200b50302880310807071081140005c00b0b0036204200e0342c0e140320000026510b104084c0124015521901d01e40f01000701409000c0701000e07000c1d81440a1f140c403160281d107070549000708076520410580460710350300324102 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 63920173 1250 63918923 63918937
    0x9120a020609060a02010f0c090302090a0e0d030b030a05120d110304020f010c0f050f030301140415030318030206030a090605070c0503030109110424020607020102130b030403050702120607030b06 86
    0x1194a407110081c140030044c3e20400b4031809540d2640c0c03010400742154410b00c5a81c0f82141e0303800c51081e080d03104201c25810041c0004465509101c28032007c0c840c00b03d1900551041d604000031842c0d07221021909041000320013904a00503200c00802603086100100340495840e401003004120070600035081e404140d8019400c80d485000841095018000b198445401021203e14a20040e52001e2401c05a007134070b2a030b10341010004100b20b420078894101c0c0040115014402281c12200205811a082c8000780410420318a20172481d514100000302454000e41081c1e500d140849400700948501c0b1000c850141c98800096020751040c07440d0315410703500c6409945564649224031000e0a4078075035941082d1810480054804100e01100f4010161086004494620b0f0007000c1c1c01c2c01c8006104105690040084a100b00311514545082d0380d089074a940e05c0743ca0750306007203565000303505000703400c0000d03900c3c60591040c001580030b1040106540601403541e04c0030a0000e1350140c50 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 63921423 1250 63920173 63920179
    0x806010f020a0503070212070f12021906020c280803071b0509190b090712060b030130050106061101050106090e070e0409120309020306010f060207050603070e0301050403030209120a02 81
    0xc044032005140002010011400703c800311229141c03500c801096001e465071000ac0e012403040b19410031418804001031100039981c91280d002d919004005c3d4555076003a4810380b24103074000c2040d0110102c4003d8081d24100341c9454142c59844204e01c0f0340e41d600c203000c240c0b91440146c000400b2142160600310603908040c1849016440b40c00e6071040320041c480e01160003944800343c224190f103849146501c100d41c81d03566602000d0b2212030f01d01c11500301750845220f0180800c010300050703500740300c0d09201a445410200e501c400700200d0b41a60707802c0100060041d4240a0009036650b80b100e400700c10a202c2d80000c00540c4d07a904801c0c0c0300302c0141e03c1020182c0300000c00040c00300780030310f1060211000182021400007483c2c0d0398510740410202c40f40003c699100c0403407040d410b003003101b140907101c020242d4028508000000e5506c0c0101d10035180b050300000005030700e00b0b10407421f680d0724003006002030140c2c1c1040e10b00a4045d42250a4250003485442c90780c1034041c1c0c0000e0b64261180e009 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 63922673 1250 63921423 63921427
    0x4060e070909051b0712020309030607200d0203030c0717040b04030c060305070903020103020d0f0603061b0c0c050d08070606090203011403010b0907031109130c080601020303040b0105010e0a150806010f020a0503 93
    0x35070f241e10300b82c086e8001800640c003040c854424207803400d01c00280b1401503650f406611841d0480c56112400c800c0c66030f407007103600c5241c8001c0040e80000c201c0f0741160042a0340e81c0c0b2004a460221001d106244500c444400c000c41d0000780d41107020050700c16a449a981c0004454444004074200d81c0f08032100030001c0d403600ca04001550083e0b00800840000c542c0c0840d06003a6645548242c034200e40c003c82e105030f5104400c1918080c00a1040440380313051404007025070254580040c00a00303130060510401444000c81c08000e0000304444c0e070300354032031001d10000e80c1d00c501c1c420094100340b2440480a6020301444140e18043c440d802c07185400a000c41c0503034490281c00c070004c1050006840c0300100400582a60341c1d174801c060721070482725820100d007046964a0081c40341c08007070035050555009000b4080003507546800c0905641c400c0c40c10311098000500060b0a01c85c0c07641c410085c9420085481e0301715030380b28403540c1c80381c2800c1e00c80c800e080b500d20208a0740d400149030098291303042 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 63923923 1250 63922673 63922687
    0x90302150705030406050414031b0c0315010b0a0c1406040201021209010503041101030e0102070803040204060b030609070e01031512140706020705191505130b0301150c0204060e070909051b 83
    0xe03d1b403010ba00700c0c7c042c2c60420203000b041b041241c40c40d070200303080100c9401c0c40130049006500070461128030600c2a0701610003429850100b2071059010b0154543c0c410700441c1c140741003803144407042d490700d0f003100720606400c205048a40d250782040da800d030b00501070350054062002d80d500850709000010795806142d0381e96902e03201410200c801525040540f6070b0303d04400d541e024006800003d0260b018140d80b820030b1b104002c115005540001120407081c030800c44180c1e03807041c00702d40c4030406081c010300c80c8000000407001420f4000254941006078000442c0789800e8031404108103210b030031806060808c0d610b00c103603a00003900c41c030001640000014496410000d403c6280160140d00302d010007511380b5140e200f1080c40919180004101040d6541f11051358010b9000808540403402d203176504040c400d00c4030a50003001101400001400601107440b940c1c003600042980030401d40c4a41014140109a8a014481c0702052810080801c0d80b00c001044003076911b0103000b04a030f1030100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 63925173 1250 63923923 63923933
    0x90609020f03161e050414030109051f09020a0308030114030c0f0f010207090c0f080115020a030c0f0b04210801080d08180106090b0414070c0305180307090903021507050304 76
    0x43c0d5841e820400280310f404210b8124181c12014440a40b0f4483c543c440f03080003241d0740704503c02e51881d803090381070015807400700c4c0021415109400d600180050700701d41d03040804024002d0014000d4215111f041c00100b8400300c10085c6040e1000c081c0311041808a103000c1540d101d0094400c0b0f580900d070300c4800c03c01131400d4003004000340070600540304030980d2072610710112151420141d0204e501c1e02c0d26806040d900c5013403140540821000050500c0c0e281000030355800c0e0103080201403001c40c020000031b0010031002d0900c1da0354400d424610525181c40d10301024108903003c81ca601701041c9104000700c3c09162800d0607595444c0003000800a104000c5441c94009402404690501c0001d603460340307020301682000c0c00302d034600410b80d400e5403024442101c049000380000b80600c0800c0c40112a405500301c038040750985015502c501c1482410400660300310305165141c40707549800130f081c40032500710001c0705029800b0b40e441c02c14407581c4c0c021130344011554100012004c00000700042c07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 63926423 1250 63925173 63925201
    0x1e0302090109020921070801020f18090912030601050f0c0106060305010902090d0210030e0304030f231005060604080d0201050a060e0402010c0308040f02090702060415020a050f0702040222090609020f03 89
    0x191707800120b5060030b981c3c020507800c81e4000034070f2030140040001d80d54201e00c40b52100540340c03401a06c44216610300410b0f11500c031070701900c150344e03500c100001154541c5c0c4100103903100c80c088041d05c01c1e0f42e000426a154020070103071240b00c001c28102000040e401c0954401e44403902005004040b100485c0e50030001c05141081d064024580e40f11742d600a585002c10151000d5407103000318203005109414000b1010328600c98014100c4140c15041a0010010800c0c0304440c403010004155a110040012484d005030b4009007180e100700085040407582c1500308900404080408000564480b0305203054824100c4020b03001ca0404544a000280b02d803106d203070f0081c00303400c1c45030040c00c440c3d0014100006c240e4540c00182d00ca8000d01051100740741560200c50402e807001c624194490b9805000e42c01003d080340c00e580c3d00840d0748804d5455540480c6c4404103c1032258110710560480b8035200c0b046c0f809220000c51034144007142c500540c2c0b00f2581044141010b440c11551402c412034802 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 63927673 1250 63926423 63926479
    0x90f04020d03232a280f0b042301020f09040c090902030a151401050405010c080f07120e01030603211809050115030b030c060c030904050f160309020d0f0c1e03020901090209 76
    0x7800000c4146e0216100140e5130f40101c0c0305914045154252180743c00380880c0c1102c080344603034810042d007440038003410116900c03031b5025200801e4040c1c00303241c00c1d01d4000895005404e140c1c0001304102d9507860952040880030010703004600e809445555070950310250403840760102e80104002e000759030080400803c5607105070141803825000d80c194621a4000300001c071800d0080100081030b0f540c00007100c84681801b841c04000107031540d1100344011782100401c442890410b5a0041e0a601c103038404180c001075a5540c1d46100d030f82d0789140700104824420072001c4d103207070000d255550340704e4062084400c038000c00a21070140c10808000c2c5990004035802c81a03c010011103440d42c03140c0c01622b104901034040303ca81d0380742501c0d001060a682c4020041014a8429000300594078150070b11000b581150541d20750700c2d241e10700718002e240d0711b030084405403071600d0314401c1d44040850408140e91003038900350116665400200c0036800341d80d01e201d07802600510761440d07103140c0d000d582c055 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 63928923 1250 63927673 63927683
    0x90109020f130603021306110607051b060108060402090f071403190c02250308040e06030a0b130203100b0d03031a0a03060605090f04020d03232a28 65
    0x250007500610b0309469929035001d000460740118010307104a4100d4401030090a00e42004507040041d809040e03181c5a004141105000022901c2c60461012041074042c0c14941c2d42140c2855844480d9240d5031442181c0480c4107800390340000e007100f0480c0c1c0d0014000d0401c6e8865a03000711418090201d1038000801c0402015035011104242d602103000301ca400300e0881c0c028040022000304450000d910014403540e061503402020000034160104640488103500005251a11080c001038200004d401e000703411001c44000340038002503032078071040d1000e10071021501c1407a135140d0306205a070326444140c1da200101a504002007030090700407180d4850b1502410394000c011000080f4400801e41081d0b80c0282d03580424803e500344034507610b4000700c0e0407410600350318040e40010381c441203000e03000b410004400e12040300103000030802c02c101040340a81c95100d81e1500581d5080f4154880d588451089441401900d0742c000b1655400070480700c0b04080b0104142e0440d58818050030804841d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 63930173 1250 63928923 63928927
    0x50f010902130930110c06070308060f03060108070602101b05090a0320120a0f030c060204050612060117100522060803041703040e130302010b10020c01030e0606090109020f 76
    0x600003410014042e1020404c140c8401012a500034034036201070380c3c8540c941d44881c00da403003199103001c2590500355043c503140380142ea415001c03030542c034548a400382c0c05215190020508400c0819008107581c25035084854041e81c001030310081e05c0d031000b00c0040d00480c2c085c800e2030705c80c0708a0080103604000f070020a4482d81e030b0303512010001618907140541800c180c09072940da00e003480c288084c203d0300070010302003a180c2d07031520f2100245042006041c407400c0e0b01884c00b04015034058500030040100626158407800030034120400007101c03d180010821500b43d60b1030300321032030614054070b91410b503594601d09000c103000816913007440154006000d11035111500700240540d0003e0441d4001a545031450000007018804a580ca080450b070803d201c1440900706e2030707280c01e078048000503900869404905083e0b0041440641d4580c00403510b02031140542d4000614035a01c800070380c3c0030017501c401c0c0f1007001c0d1522410354015601c03040c220700400c1949203940141c28150f500250030f41c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 63931423 1250 63930173 63930203
    0x103050a090f060b0102070f0b04060c0c120506040201111b100e03010e0c0406060503090c060d02070209100503060703020c0a140c1906090909080a180f08060103050f0109021309 78
    0x1040d07041828000c5800907280c61380038000796410b20090005000c0e01c0305104025080c00c0e4140d80b035000d07901429080007060b070560b0003880320441d2020014442418400c0c07a039003280c2803c98440c0c00c00c86060b4045032403511140c101440006a1030751801445108411482600042146502d43e4441c0c440c00c022078080802000d560a100d110700115800c0010301c203548040e0140001d8411982c4800144103003802002602000441c01e104c083c0d8040761015603071248110000001e000d45000a50004041020810079040000048003075540440440d1a15aa44c0c2d10442c10b91045424000098201600d0b51000400885900c04610240e0f030a4030345007542c92003c103400b00398005c01021450990a8204a26030704540c602d070280c610b10006205c62101c0f51124035282c0f01c0d0300c09050800c1500d1044214079050800160042d10301c132890a042a9590b02010ba41c80d1802e01060f18070340180e1940703200804051040c504055406003400c220fa00182c0c64000080c100d060090322043c605803818 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 63932673 1250 63931423 63931433
    0xc0201030e12030906100e04030804150218010207050402040b04050607080415050d0515010906050c07050406061d030109030905190b0a0503040308060d020310150302100206160801050603060103050a09 88
    0xd05040000039030b12649900d0610561840d100010703001d1b00ca501d2070b400c4140300d03e40941c0000c0358400d400d070a092045845900d82400c0c44030b0602140d1244900c0400c800900395404140c0301c55200d426401c40d28003030349540400040b8440e034402c00d045c0100c01c110401c190b04000b40545000d6020f40700c07160030319641c0d024100307610f25440781490005500290190101100b803081c242c0115000e00398aa040b1000340000e0325102d800d003e030f40207004011130f690784104d4040051001914029109001060356004042c12000d01c00711102c03161800c03075044005a086c140304500100e5003607170360450150314000900c00c4161b0b15241d136810030107400c000840d44480c20301c0100340c010a1907691580e6484c00741030041c400c1c44040c04091140d10b00004d214090380e07001511000c00d07100841c3c00a00c0c070a1215003114085680c1c1c1c8000c0d00712540210601c2c2c4640c0202e0325903c9040503114400c107030004054102e409000901031140d00000a00204000d03500c29401168080c05004000401c0340c41d689607 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 63933923 1250 63932673 63932683
    0x302010e0f0706081003020f01030b030c0409050c13051501050a14040303180e071d2107060e191203140304060914010b03030d0c090f06030c1b050a030c0201030e 71
    0xc20704080d806441d0410071903502a241c603038000b5140d043c40d0159829a40011503880c640310003203040684824000a50f50340c10b1249c03160011000b0001c219074240d80c0b0303159403104500802184924411085aa0146503d0050314070841041c101d15240c20003107001560719810112210f070410070b641a5941d48400e01e2002080994000e4940d0221000c0172080128003400716002440020764440070f00150301d400c0740c0000581101301038628aa00031610200d20798805400038401c00c1a0005020302002c08085800300940b071481d80c03400140e500180c18070200024440040c0900000b1000401549000500f0f43c0c0002e0f12a15000b02028280c4040404640080c1e43c2902c81c2a611000d4004110080171040211000d80000340520900a80001c1d2070340140e150002809440c0e101e8140d410348501c1c5258082d0150040d640115522000d004005040c052074240210320080a2030400381d8101d10b41c07146095000c801080e182c0c00343c0d90300b11030715154043d040b81070580358081c000d40e216003400 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 63935173 1250 63933923 63933943
    0xa0b010608010801150e060d02040b040603110909010c0906050315130b010e03010c051615020f04060905180106050a030615020c0306010b07050c011d0a1401080f090303010603090302010e 82
    0x1e11180c141d41040700341400c45540c410984088130b1000420084e01d042d0145182c0e220380c049401c0d604107403950004c0b801a00c40002c0c3c0b02d40c0240360801c0401041068414201100700039205d17000d190b50740002c0c1c5401c98502c00c0b6180042007040301c04126840c03189000350341c4408909580c206001c01400480d072241c11100714510043c0c1c43d1100d041c15542d000e00142c0030154200c00a108501000d40c01602e60b114844055808510181c07610041c84038800c10310041641d010030031541c070b5501000c0210b1940040c0111800034420a00008140c5808640020f5096100c00305000c16480c1100946a66120542403411300d61100d0000070405001d103003203c070348060b41e00503000c02c0d20b44401701828924141c00c0304468000a00030707003010130030004860320321840a0802581402030480c55141001c408600741ea4404205100440c480d000241c0803c06e000003030301c5804880c3c4402100072000403041782c4540c00c2d0780c42840104000c9100340c10040a03580280000190700c0807210801d420291144 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 63936423 1250 63935173 63935177
    0x12140309100804120215060d0503070b0411090f04111c0c08010507020c04020313140703060f06060305160c26030c04060906020d0503010501030507140c0d080601090f0302060c0a0b0106 81
    0x2c0d00f084180300904400ca400104203202604501c02e540e07000c9600100302034103da001d603042400b40d9007080010400c4505541d0000b0100c40f0515080c9000c0710140b014151060050390101c0108407030b04941020b0300c3c022a44062a00d102c40700582c1444513800c0b64280c8078070a03e80710204900400d0101c04040081d080d100000300381440e04040183c80c001c900b60040780500c2c4100300300060403008003000b01c0e5680d800014000710115098100e1702e451300311f80020b407440d41380c4a01c40f440d01c49281c4c040400c4035000d88007880b640d50f0340a010ba040f0108a0318640104800b10740c4140000c2c01c0400045111140c085841c4da4800604454003264100700c1e0302d0005001c00007800d21007250010044801848184000d0091600103c00201390740810310031a4145a19540490602cbe0b025080010550186541041e10790020031a500c0d40c0e0501e0031600804980180e000c1a07440d4800c440c0f03041540c40c40d00d60280782e00d14550a101165000401001c401d000f028501d000046039140310034003c00c225 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 63937673 1250 63936423 63936437
    0x60d090f050622030504030204020705031b0a0c06030504030503190621050c0904050d0f030209150703080c040f060815060a02060f0703050f010504051f0603021c061214030910 77
    0x101c80302690088005580c2ca0340703a442600603000664008100c400f1f507507042c0c038056100e4031280751040c075601503501a04404800201042c1c00f50a00003000c0040600401c042441d0540c0c4800c1038044070825200070b000680c08100003040c0b5510801d580748401c0c02e881000810701d58a100c0d000a48680501c8005c0c00e01282c03070a042132010030032039185c00c1b44040300e0040203070500c1c0c0d0b02c42d650351108041c41c2040c4036240d06404c4a0601130f07419100850340103080c00c451868115412a0103511801c41100412140e4010800075079070941a6001c1e66521100749550a05102060300c204a0051a40111040043c00c4030007581700c0740c01030140500284c0081c011800c1040c0703900941c440c02002041010b00c1c20b01000803040c94160f504e4111442550002142e80320310000c2c50280034071800d510105031171382d1070029107140d0560003020303c69200059002009a42c4030180140d44081c8101295035640e00c03400e0010441a140603419038107c032080b04d1404042e00003113105a19400c0703840d0041000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 63938923 1250 63937673 63937681
    0x908100b0a1d042006030106030219030603051905210306011d310e030a120e03040e19050703051602010b0a0b0a020f010213030201030b0a060e060d090f0506 69
    0x428140440a004404502d0000507452000c800c40c900c4010005041d03510700041601880303080002160419078042e0001c0e50325038547d4002703806540040b04581a05a1041c0c008032a9886403140d80141c4e984080034242072014501c00e40071240f00d205084da8139005030f88010000c2c42c441d04c2101802c03c484022036403a840e040c400505078255080100290f00b4110151740c2981c1d4032440c11520340060b00b10680c800c00044e104c000580c0140400030035095161094035850b0b8000003015250b203010a5648a01584200d0f02c0e180a4030000080c0010030742c400e05c0309101c640305422103594020100d050300312203044440200c00035204199021800b081c1c2c2c4005000c9980700441c01901c01d600180005d00012502c41c020915030a600e104000c50340c0740106800e44518403d206500018a00d10005c0d5222942c1402c03001d49280707240b000300d000c01e10341f5120003407034100130318010304948054a40d50454000384040c001c10760300003c80b541d5019910030300c2d500007510400702d41d41180d000f640200001e1030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 63940173 1250 63938923 63938929
    0x4060911030607050d0507030612030905040507092301020a02030313090605090103020d02090402030f031b0f0d050301060f1b150f050907050103020d060e0103081e0a08010b0a0908100b 81
    0x5416118000d8102e4020001c189402000321a401660801c000802d81c1d0f50540440c01090b440e048404425481e12020080c140d122418a0036144121030070091915500d0060f02c5d0b28084d440789520359111043d4102d1003402150888a00b5001030041e607588940d0343d80000d0855028680480c070001c00f4030030078040a03401e8840c02c4040d1409031611101941981c0000700f0201c0b03e50b40c000c0c422510400020110748080c420041c001a144003160b454881c0d0b1149200442015442c0c0d02d032510034082c01d19a50240002d2110b4140d1098a86504e103901340395044948040e04480c071414030040020f0311041d07699488844100a001d00040e0701100c3c69420350f181900c1c203c050311038015042c1010b0100d4590082000b600325202401c0041c1c2d80e65004072034001910103a480038444029045c00001813050010090211658036079025004040440c400c1c40d0a008d41d007400c00016620500600104050f20020b102c6040075003040c040c003a0341c8a0700c075417030889041c0c0d41011803510340700500b070309003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 63941423 1250 63940173 63940193
    0xf0809012a02060c0412060203060f0a140f0f0d1202121c0b0111100f0905060a050609180a020607030c05010c20010506030a030810030c06030c09170d12020c06040609 73
    0x105042032058070b17240c5040c130319440c101c80404020305860390000104455a4030b001c40d06240c040098002024180c0c1c4020412645c400c0b40345d03690203400d40080100451400c52103540f20484011f00c80a01d4010549940721210f803a146950103510035410601d030411044c00c00b615400140308a00c0d00c801c08120b600c1c40030380d02d6044206062114904451b031045d0004070300840204000c580004150085035050720140115001c090814001ca0061186035a0a40c004600c0341ca402c0d100c40046403140c04c0d0b03101841102848910054001942000052608030700a0084900030700d091015071100d074441c24212042d0005250100b12400c60289181840c020f000000050b440020000c41c640400800d40b9603100e40401001c000c200400100c0d2445401500000756421842c2071421644541001c0c00402d481440d2201103076103807500094a80e10700d00c84050104000e0b028045c0134402400581700d8084042c2041250f54007405502e602e0002001034900c158015640801c0c104000e04118581c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 63942673 1250 63941423 63941431
    0x21303170901090e07090b0c0c0a050a0b161106030901050627060f060403050a0606050108010f050d0b0402030f30270402040e01030308060f0405070f0809012a0206 72
    0xc9003400708045503038012280303404540709241a0000c4c1d54a94404880480d402c0e041652000c1003c250b2103c4014005201184a4000c0e01c40e903100d0b98585007007282221007032041c04c81110341001a460010400c1030100706d4144100c8011080003141400540d46d0381003180c1109890b0340d1102001102e10348241c203031400141c080300d02c60b4194400819514800c0004050a0003104050340d801010f85404080b10300440c0c00c02e0585103050307030320701d0400050075091141c0c60028002800215105401102c410b045030002060034a414070655180340707030303210028020b0b41e240c080c40300306254003242401404081038017007207101090501c1319140c1d10401031002c1080c40540042c041d40000d2008c1054680301e54010f581c188824510f83c0b0005000b07441140c01402c001004100000105074205117004d01920040b1400d00c000c0c00c03088184001c58100f00c414000050200341c0c940c0d07070745006500f02030700010b0711800441d1400211501d0f281301441100e5489412121002d581810341d030501c401a00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 63943923 1250 63942673 63942713
    0x90f010516020705010309080c1507031a060406180503030d0e0f0303060108060105280906170c0306010302070203010f06030f0201021005040b0a020a0e03070308041a090a030b06060d021303 83
    0x1000d490440000e41e180c0f610f02a40341410b913160140414884417200707030381203091440200c2e80142440718800138451429290360010034144038400c0c81d80a0b01009028451601904190402e4a0f240085403140740112095406115442e00882c254034280003d101c0c0c0700411101080320303407104586910b042208100c2458540080c000c0c045142e1b8081c1c241e94200d08240b0301103840d04600e4490a96014508540b070100a41030340d2012040c0341c2007821365040750520b480d0f0040700c0984512006451034201c43c131001caa01c00300005003440d03000c0d078042d103034481c00900001011900c0014220171905142c0003039810b1403a600343c0b0310440d0783c10404a0b2a682c1354034400e100c18105595110800000074140d01000754021407401802845900c100c0d4003039800038120b5007041c1c1d42e403c10401a0b40305d4000c001c40c59000f904d03100c0807030544500712400d04401802e082c0006145484843d81c04401500b0140d2001c030400480f9000c41d9980058418961800d4a48203a14550302d015240d0504c400d4020384 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 63945173 1250 63943923 63943951
    0x7090b03060a050702030c01020301080a031209110405090a08032a180409080d1503051e0a12170f0603060105120a0f05011b02010e01050718090c090e090f0105 70
    0x11649020454a4000840b9280415107031644a0144d045006035802401e00350301c04800000c15003000685105054080c0d10b6034059101c059505009031200400090a402c85800e175800d11030504c6d5000c60b500130000c0e003d41e0031300211650781341c2240d4000d0b1011410415174110000642c440b0316406451455401002c52400018041142626400840251084da950152034050100c00030440b48804070007007042010b0070b100968280540161b0009075030074459034100c643c6581c100d021288140074088000e229180e61540c40621606a0502400801c548401e81c0146c4200f84200c25000f040701030030001c254504101850311740340d01688079500c582040c0f09114000c00021486440c00d907000322400040c0380241c100700c0d0140100b0240c2120080746080780c0c050b481c2d03040d4000d00e88082c094009010300d4440c903101b1100c01801da5100d42d02c6080100c0c1c208809a215446a031070b200c45801d00d00071044e50390407140303050f09040301c402445801083d441d0111180038407549502144c1454404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 63946423 1250 63945173 63945191
    0x112060b040512010c021002070206091302070b090102090a2d060822021305060a08030d09050c0a060906050c16060e1003060f0b07150216030215040203030d050a0b130e0709 76
    0xb1f43d0f604006a200c0c2c6066030004000041d929400100c0d0410030029000d4425180c0b403282c1280250302c1090242d40480506c80895000030044c000c54108000c004c2c64803002030304080380e03480c01c04000c5451030f46007400603565003e44c0100d14070030001441c064580b80d1035403074080c004141014070380042240d00002c034291000140d40381088002d82c4a55500c001680c0d589003030108500e05065049101c55200108880b040c2407043c1c0c0001d64400d201c4d2083d02d1200c5031160038411682c18600801d00491001981481024840c4011300f058503501c0c0c044548030b00e00030408050300c2149801603000079030a503440a80c40c3c20241e006d07980710703c0c075442c040200c6850304074050101c0a042c0a010700884d03000480400b4042c0d9145014582c8584e00001c540d111140f5403009002400c2d00310480150260390801215500300b005e50300c0c0b1641d000b501031450101d092036160000c107001441c2c00a600d950b07807240c203069242c01500c07000903000d00c0e00000c1d8004440e0031071032801006500c40c110b0710742812020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 63947673 1250 63946423 63946427
    0x90901060303140310120503070f061d030f0702040903090905041109070503090a02040c09090510090c0503091b1f020d030b03010207030c020d061e020a080105040203040305030f060112060b040512010c 88
    0x408221810500d18449190aa1521238103500c40c0e0003001c2c140244600c00b0300d050113a40d0707104800c2c11070680c0500c24409020800c2c681c07039000d8902e082d00003040a10a5501500302038108200d024401e140c2161030586072150034007103134801c2d60706581c080c001300b40840d080d003095041703d03070403d502e4201141145407110f0031607660248230300700900454440280c0d1641c140180000c9001d480c000105010b5458540c2010f00010628418940800e051140110b142c0d40100c0860380078811243c050241030001c02c105402d208002101a0340140c00c2e0202981074048220361a10412403940c09442d00c03204100c0300406440c040e102503403090b44100074000019401040c4561400d60588500b61805220700707010000709241c100400c1381e01890240c0e006828400d0b801090322400380e840e103111760b903224018081240811580100856000c0010030119489403a80a502150501d0071000c05d520482002083d10000d0b41304d0300050701c01080610451401400030040404c02c44002c000c084002900 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 63948923 1250 63947673 63947701
    0xf0f0607050a170421142b0801050a1a2503020c0301050c16050115030f06060b0f0414030f0f07081203041218051c020102060f040c050103020c010b0909010603031403 73
    0x40079004c07030201743d02c0100304500040030322281e00c28142619500100407001c9000000320000c2c0e0100c9059420b5055001e5006025040c182c42c40030f000c913400c0508003d0f00c0c44200352854140b0b00201e0b010300016076442c2c030010f182d04d203890140480c18602007007460083e10f40440c4406452190741450100f0074800700b0300c0c0958000180c60075141982d050181003032030042465511480d11715041030004801d12414480d030900d5107100352001c101e11541c8280000a5001c2e00c1b0840c111008104020072001c28104031881c03181e81c00506941480300850304161504141f0350107000a900019010813410704140000c5e001003982c040410302e145070540c1c03001c51180038483c01a0034055186013001900310a4a1660058030f40503122266152800c1e2180054a2041d04100e006104101c0013035454008005a00d014a90029040c15520300b8a001980070390401146200d0540d0785e440c2404482e039640d08024000c00551000083d0141113040c000c000a33942004401d40020800c288640c84280100d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 63950173 1250 63948923 63948959
    0xd0e13200f04030501050106020c010f080f011a120406050a0c02071d1305060702010515010309030f1209021815180105041a030f0709050901060e01050f0f0607050a1704 74
    0x1a156901c200003080a4107000319080909550711b420000300d002900000e1203102e0107400d0300c68551008020340101e0f00310008a4122403a890084010003a11680c4070001a10014516489080070f0410340203100382c18040f64113680c0d050f00c400a01242c011184500c03800588240301400040b03081180d0303014030840e43c0c60301e07031880c0b5000d50000c3c00c0000300032414003210b50302c0720503500a0700302200f00034060300b010750f21400024094000c400c035540c042c1c411201d00b25410303101d400340452a21810b983d0b040c800c0b94902021a02d850701d400c0169a594081e084c012a40c0240d00070904168000903d201c03004200a1b0191801c3c03407982000e44540000141128000c1760b021640b82c40038651102d4130341104900c01d80520de00020b00c15149800b203907203400d54200d050208190f07986d844072135003170f00c0844c03207a031648400480040c0101d04046220404440d0040c0041d180e141201011441507807180e80181e405030011582401004070050300c208180801049050403d41898070f02021006842 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 63951423 1250 63950173 63950231
    0x50702100c050915070c0803180102010c2a0318060c1203180b060307030204020a030f2d050903040f0609060f0c0c09050601020a06020307031401050303030c04051509030d0e13 77
    0x20504908102c61b07183c2950292240e4020b403603d41c540c9001c15042d140039100586d01550a00080b00c1055200351460900b81149180b103112804685c441d42550003406d10080d0100200d9041c481040a0fa00242e00011b0030a5601c0d040c6032009403c00e48401107005030504209414036540c0b0384446040d8050242203500240c8241c200d40320100064030300f00341ca41c0029089800860850170765505503214540082081c64280404105030141d00f491854140031240808640e41c1ca0413400000ca511081d80300701c0c280c00704c900d4552a1070b0044a441600d9001d600010901181803207003d601040e925103a1605041072915242c2c150f60b26403480900d406501c40c880d0782d6900044440c0c4c4208220207019402c10811562800d007480020701610f030104c84803902e1f4180400020752420300008032845032140480982c280360402041011500003460400c0c5111014041a5480d950900980e54010155100c1954103010582448044150000c000c1e40d450702e0046400603482050b03444400c40c418003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 63952673 1250 63951423 63951427
    0x50109020f0301051c0605071116060203180d0c08030c19080a0c060b0a0305061005010e0d02041104030b0a0506150c061b0708030910050c070507140a09050702100c050915 75
    0x28003410315451000b203034040c086074204030500c494640c01c0149e8081031411401690b4201c440c0c0c85803120760040610502d80164020070800322000404140711001c024001d007004d9080c0c22a44074031480030685c0d00208240d410005a00050720340820510200e103001031070304d1140914035180d41419010b604000c0c010300126901100400c41d16900805280364010118080c298403400d1044d0b81d50402c0b03800c0d203076003114184085003541c0900e4419004810040c403608102e100351f42030001420404810501502d020f000101c0010410181d880c4545403002d40040c1c1c5160850400103480d1f0803001060324814104446403003000040b84203035000044e01c401c1c100314014840c4002c414400c50708003610340c0c0030102c10303c19060408103414031421b01d000401d220988400a2990552048450080503903210250410143d0055002003411210007401426015038405103501655000c8807880c0041e00082d44600c4240c801e4400c808024100d07207041d5090180643c0450158199045e00a014000c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 63953923 1250 63952673 63952699
    0xa0804030b0c160501060e0a06030c0b0901050717030603061509040308061c0b090606010e06040e0a0f050106030b090702070f05010e13020f12010905060a0909030e0306090709050109020f030105 85
    0x600000c40f40d078040580c0d04041e0540e084e00701035000b072866000b40c120b00c02003140850350002141c0a001c05580e0000c0300300340d0107450505801c200d5801081140d050140c14000d0201082802548000041e1014170195a0f03150103410141040c5d0700070304516040390700e0400d05849803600083d03581d02c140c0c035091041aa4032500001100440c006030102085421455050200144800c0d014081e6002c5000c03101d00745c0702e034070044d140d40d40100d00d0745410a2081c8810801d0401c40e110300d6401a2000c000091000514041e65003910000d030001380201c0c2c0c843c070207050b1508000f450542d000b0958805007000c01e082c40540d0342c0748296486000e040049400d00459241da400c0d24006844118020842d078450404000d003401c0d8001d000c071902e96682e10000060000814006c0b6031007030304010f1020744013908150303044d802440201c1041d0204922112030502d9a00e003000000c0c00f500d041401401040d01d000c503a0360035148140c000c0c044d014010311228844041070340c00c5d00d040d96002c80b19800d003003007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 63955173 1250 63953923 63953941
    0x9040308060d020d0b090a0302120705030913060b07060617011401091512060605010206070509010203030705070311060103110f1e0111120d06060e090f010b0306040f02030103080903010e0a0804030b 87
    0x180004080d000001c2070040c484415000144101e11f14429000e40c1c400042d007515030100b03401041400f03040c0340c0042000386050716054001080a491100c800100d8a807078000d1284182c1041400b154a656240000d1046141d01c180c1e941c0c0000c401d07802400110105500b00145035018402e5800300c03900c0c0e140b6840c84c40340030f0528001034454400c0302e5191880b2070424001a204a10955016010f54008244402e204800b20341c003908041c0c000b540345031904241103a042c0c0c40400b043e401c001a02200c501241410b00c8094001c40c011030119140c910381100b00a002030f400e6113041c1c81011600281100c483c140c43c0388104401090034000d100d1801500c806003840d40300c0c6d1083c801d04000042d1010300c64807541c080001d840340e65a565211400c1c100a1259210083d510b8808044003840100982c0b42910025503110341e000d0300c04035054451525000c00e80c1c2080c0c0041b207240c2c10120b800c0683e07090034400da120b8501203000404645406840d080302903c50780c000545510314903400103152903 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 63956423 1250 63955173 63955189
    0x22020a0903080309010c08070212040e1017010b130b030a0809010c0803010801061406040b090405090708010923060105060d05060109030b01150f021606030207111c1109040308060d02 80
    0x10b40108440b81e407031070000d1141d4020162010880301056070140400c024070300c006000c155092085a4540c0b031b050a24464940d0420004c20500c1103861135200030805590740080c071000e4010245c00031031030180240170040c0f103441d40380018806920303211368900b040d07a00041c42a122904058003940d1803509000488000040b240081c2c580c0c90000000264004d055121108503030f0380108250312400b01c50300b0070004c2e10540c407440c084090207121400c4180780c507a20150700451050700b103401c00d44d03031514070b6400e641408a040e12140c041820309841a403540800c0300d130644c152030281095605003000129a805603900302c620b103550f10000100c01c0d90042d851400919000031102010b9a5507001d6010005c0d070300700c410340018080400b07c0494500029030082400b52900c46035040c58104581240250040c120a4640c07489000b80d030a04ca031111502e000c000d61081c800a048891075041032985420b0f503070700302c50203000c0b410f003003001096005203a0f07a00940304417a030486414403400015200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 63957673 1250 63956423 63956429
    0xa02150a09020a0b030405060603030f070308100f0b130b040303020a0b040f1e03020f01060305071404020d02030a1b090b0304062f0a0207050f13020304240f05010522020a09 76
    0x901180004280b130003400f005541326622030000c132510f81d0b446805140c0c03240250708602e14195014014100003d010f40c1c26994400310791070710300131000d40d0764406034400401e90f4824401888002140c0302030b44e2503042142c000d440040c0c0d56a141c00c1c0741d50f500a5444104650240c041d4255202080810a60403401c40307403950410080841e0200e040d00120340c0251544040300588501307191582c20104c18003900b01100e03002000361039894604141031028680c04031115034840c1c0d00300601280c01c180c1c0e202850060303602d1400082c1100c1c0010f655035050803402e0440062002c1030404024001c1c07442c0c11643c1c855842100070540b18a2403188145c4ca115181e030390300d1301d080f0400f245000000c0c2c910207000783c4080c4c2d40c21a1041d0b540e450138402c038100e98103010758200d001c107038140803400101d40003181c0007440b074551246030b2440c181c411105c4074045a5200441a102e0403d45031017140e42c01918054102250340e01c10020302107141c640c0114141c1584d841e442d4010a84e00c0103107000e6440f03c402 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 63958923 1250 63957673 63957679
    0x90103210c1203020418050405060a050901020c0616020f06040506011e08010219080a060803030103061a1009050a0b03071e0e061201030501060f08031c0b0a080616050a02150a0902 79
    0x1080c0c402c00a0060340240c0503000d1070444d8400101004252800344d14001c5402170060005a103441c0104c501807c030007084080c5a41d001c020f0702112000410607940300e07000b00307501c0c042e9802c81c400e0000d0a19040c100440c0c059480601130102146010841504442c004040400140c103010301e5403088a85903404000c0551012503c03490206110220666006465840c000d03a6662660010100c50302070080d00001d07071041c030060000410a501c11160402c0c02d98203c0c9425800301d000950103044940213500003030f015507040205040c80021761000e0440e0103403403415450120b0001340306074104400043c2c501d1104420509650040e007032188080c0c8054a46c95841d941d10300018658030082c40100d40319071809000060b210017005181050b80c028001a500c0c0000c0c20100640e5803800b026569136596035802840e0050352050405c0303009180c90409010503103400c0b07861a0074040890210003d0210403c1541c9200740e010901c952032501c04008610070351511050035000709081c2c2d2000750 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 63960173 1250 63958923 63958943
    0x10c020a0308130b041d06040b0303210a0501050d02060304140111180603040506010b130b0d050402030d0e03060612071a190504120209040201020307061415090103210c 74
    0x9018601d402045112082820207030300302e80d281a0300e46a071041340729101c203815070360008030406c08065030202d0304144014008540040c4440000c0c0c215030026a08800d07a102e03d03501b103074002e0310511556501168044081090351702d041d0100b00c8621240c603000348039020000001d002c100c40f0240d2001554040c40c0204a13100b031503940c1380f03619809002d07074030071440d14501c2d041001d00c0d107202240c0c803659002014103070f2a4131740541040241c00409180802d8524400c012482040c01c1c1e000c0e088182c1111130204150130103005140c20540b00415040070011070010980c22905c00007003050304903109a4800c0350000c0340404590401c1c80d150403041da00068210317640c0640703400d14003401d640c050503e800007007000702039000c0c2d4440c451449185010034010484001600d00390301d09a902074011b005580c60312880b076a91781c00b05d40b0381000402c0d102480805000e4812840781851000c03031405d43c1d20b0240c55065807601c50700700f00145500704110440d0003450008605c01c00d500f40c006c95100705c0040e = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 63961423 1250 63960173 63960179
    0x5100509100b062a0a050106081203100605030612010507050d05010902030f04150b0a0308030a05010e0702070302100915030e01050c1c02070218090304150306060e0420040f0f0603050f070c02010c020a 88
    0x280601124401c0d0582c9d440f990703a0160301141c0303650803280120040d0034404c81c49803030010282c0307007030704001c040c194860b8000500480340903003801080e03c41e072800d43d140c50b6903480e00348045080f030b2410b8101c900d0700f920500030070030401d10b215100c80c3c00540201c0c02401da42032202e0b5003005030613403551003604603810100000401448070003840c010001e040060015070f8980304403404900c42291301000607400b9110800c09410b02c120104200340aa140c09010030f40c807000c10500700b444c4640d0b4080081e940f6400315980c1c800a118080d00482049455460031100c94140c0107030340d00d0103e00003030311540001e0f205c003196a01d48001000081c0740001e200107143c120202c40d00ea4100b0b103d4240000010444000300398481d20401d401c1d02c0081e1070f80d5003c030300c103482408000d0400c0075000c070f180310060450783d81800d020400360008042035000082602d051115001c404040ea900540c10b040c00c1c04180401440500041d552001403860400702c031061600040fa42c0350f10303821000e034021035036040c04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 63962673 1250 63961423 63961433
    0x20a0f0c0b040f03060f051b0c15090d02100c0903020112020405041803030e01090206030705031e010f0302120114010e0a090f0c060305070e03030406050a050705100509100b062a0a 79
    0x305003103d001713103010021008030441a80940b4004c56a1300c1d0640500b0400450b400d0804028003500c0458004803115002208040200da600a80e0001c1682c0d200d001001d100d81d5042094000303108907150180b24800745d070b0301c002d4014419400024107000c002c0f2080c12422a0680c1581c1c01014020014442c01d5040c800840703076040890020b0740040d052903120f90200805004001405502038255469a5a40101100c441d040600b200e4500803c41d00300020b4001001c003000e02900ca820440c5000b50301d148100442c480448090b40b5480c2d041c50a20710700b074600c904a50341140c02100e5a0390407560b0b80e4040b88001c02c40c181005042007800d0008000380483c0c0c60400054074050f031000c001d0760715071500a4541842580d441c45d49030b40108028807400744030b84003404402d034483c14031600b030070650307a90503040848001d0380d80d0483d0355480070800c56500c03c0008001c15089004200841c2c40103e000c40e042d40f0540807042c241140181c000e11500896800f030000456a000a48541030498901 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 63963923 1250 63962673 63962699
    0x70b0a0c0813030f05030406180305132102060a02120301090510091803050d0902060f0304061b02031210091a01030e010b06040915081609051303020a0f0c0b04 70
    0x640000a0925800181ca050701580b0b40c400e160b800d625081c00e00051034008a0b0140e20007842160b4003604c4001d40b40041d2528403104000c0352113501c6141c3c9400c0c1c168134407840020568055560300038501ca800d03880500c4d400d402803050343c069480702d03990741c4d030382c403059260004d1000c94440702c040000c000101010103500c52809840f0034a04e4801c140e94441040b03003900c030302010104060310003040240c0001e014000604a11095010104581c07159400145072a0010003030314a04000001c2000200000c1d442010342107401d85010700d400c800d0043c0c00954030b015540d40c4001c15a030820114843c1006041404010114a007061102d030000c01e10288208032280340441c0402c1c102003c5102505041c002d0402c011005099541401c0c601042580030b090710f6140007c00c0000a2800b18036090300b4090000501e1004658001c5a45070140710340484400610940180d1f1450201000007a070108061200750341002c41148041280d0503d0040c2102c6544041200440014009410311a181d5 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 63965173 1250 63963923 63963941
    0x2090615030c04150518010c060e0a11100c030c03050c03090907030911041a0d06020405060c060403020c030706080a0e0705040e0d030f0501080607050c0a0b0a061401021606110102070b0a 82
    0x800714040c0403d058269441d00076178882681c8001c24046d4140c2d00d51041d00d003204200e000e48000716035080c2042d152401c00d00794100c144c1b400342c0031840c01c8486040414810001021501d003011038520720740c900400c55a00c4650042c100400010aa000705404000b42c1c3c00f50a401005010681002d5001071700034040c109089504500a0520035030030f15062141c00601c42c103e803192100b08400700d040246d074000b10142210381176803d01003c14035844550240805861000c021b240710b04281c00c010707107010324500c58a8420360003c2014401668031a500540003443c03040041141c11880029900340f80d0150400b0745c000c4e19098503505441400130300001c00010640781008080a00b40c0c01e94140c0f8004d0090000d29448070b0049484648160000c1c00410700a0050702c00b107000690f20004282c60030b65040c1003058880e4001d000030041600c00c0c44102e0301c24002001c1841e0381d02140c901e0100341d4401c031024880c2d0000f00b644281020340465984551040c400d160303d20f40b5441990007800007030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 63966423 1250 63965173 63965189
    0x80d050405031011090622031b0e0c0a031a030609030a09090e03040e0405070306020f0405010908160e06030a020310150501050a09030b04020a080a030801080c010201021602090615030c04 82
    0x19510b0b03c0002c0c8603140244068851035460022803109100c4294401c0080440c0b28288024a80440302030000040240d4445c252940d0303480071a0035880b01a41c202c0c0c2140108170a080306011040f0300c034400f00e034101015800c01003541c4602d42401a040170419400340c4e0140034003c1045030120000c4020b08000300c3c15114031611075254032241c8111500c0050134040b43d4020403040c000e6500781500168414030030001c4401c99030720707941d4032816070308040910100001c0209080c4015a0080e656101500a40d0028015a00f001c00700c24003215281c40341021134030341900840e0b01901e081c81040180ba170050201e400344120107019500800212a5064603c00c181102240b00c0d8840c404440c00185582c0da8884040c0c11501c030001c1008010300300301c0e8000c191500c0010606810300042d00858000d0301c1e0300c6480d40c500040c460401040100d2941164810000000048140c040343c0d10259015214001e032070ba15a80030410070b146211100000718000720400c600d041c00740c002002134507180 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 63967673 1250 63966423 63966433
    0x417010f06140904080f0f0f04030c05010314060d02011e0203180f0306040602090a0f031202060109060b070803180106081608070311090604240302010311070302061f080d05040503 79
    0x1d4418039402000c010030b4560081028012602185640000d00121070b001000607180c411080702d8104607511203141c07840c40541c00303d010014405403151240c02800f0a0038241700051202815004440e002400148143d0700d005001c010b5900c20040942c04000d1001c005881282c1e00300041d6907074001c10030307600c4014403041c500b005600300403101420044025006180700c1c2c882d5039034500607402c08101582c0107218003200088460340010014025800342c40c850348514250b000c02410844140c001c01603075801c3c64810003061415104440303500350022416900e0780c48179240c10145014080c03d180041d0700f8204c000c40d600e0004120342243c03015046188074026592844152140300e144001b40c4003110403294031400c0d04092004543c4079400400c001004440d0041200c0380039000059405041d400c0701c814011943c240c1310b58004014003000c07007410180d0036500256507400061001c0441c290911401100c0c00ca40c070b240001416a05066540e54441d030413000706550051320602d0b20a11038 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 63968923 1250 63967673 63967679
    0xc02091302120316080304030311030403050a081008030f07020f1302040501080708090a03080403020a0b010b03011701060308031b0f0c15070c0c030201110f0f0c0f150405010309080417010f06 84
    0x12140d101a02c40010304030102d050300c07031790760a42000f0025024180c44604841d1451104802944210721035290381d9155948840c0046c40207a004011070300c00300348444103200074800001034030188900165516604c0311248045441e0ba00c80081103608441014016049030100f60060004e440003a40c0d8595540d81d03900c012506a10b040d22154400d400440500000c28172030030101c0c2d0302c07070f00900454010b14010fa17290004c146090348148100310000c001441103500c11190269070203a500c0080c0705290558440c034210b488040c0510311311001d941141e201d44e4601c801a40c680e14201100307286ca0704644960951501d90051400000020080006962a00404010300e00c65000101c5c401c1145c00d40d401907070b1100e10509006180d00c01c1080044014604011250380c10b4400780c00740c00901844401d0141510079000032900c5110201c1c842c64606416105540c101c80d024640490b22641504001c2060300c1103070400e010041c00c090307004650790015048401003200ca503004008482d9 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 63970173 1250 63968923 63968959
    0xe01110a050405060a0507021f08010f05011d0a0b0c031804020c031605010230131a07120c020109020a05030c03070302011d0405070c060c0905130c0c02091302 70
    0xc00e420142010440c240000d100d54100280a8110440907080c4039103001c1e8940c000074010310760120b03614a1942c81c0c400c2d52041c40d0340f0600081c010194001c040d1812030400c40042c0c100c0d0411013030541c100d03441a00549050b034031b19000b903000f0144c0c4d0b460541d0714000403a800c1e8403984980204030003c940200014524141031003203496038101e90020f036003007649080d4140b00b6111820404e903103940d001e00000c01c0c40d01d20008140c1143c042101d000403090003c074a62105100c0082c0017081c2d500106030b500002c1880155640084800c0d0070741e0f80c0e000c0c1c4e1010780654180c038140114a0300140341040007585160154012100a4000c0702c0d40c0044030380c0c542c101580c4800c808841609600b11482c2000194060140e0440d0348290300203040c00f2516044c085000c4500c1120300c80f0001f007a10145005100e080d1281b801c214503a4907000c03d00d58288004203081c015019070040c060b070380d10f2000240c03062161a42d00ca8035540103144c0580c0c0d0500300314010001802d84000c0c0c1c4140507031010151420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 63971423 1250 63970173 63970177
    0x90c0603070507030309050a021c02010806120705101b1112010603050c10110d0302031e040b07080403031407080702010e01090b070810090219090509070905040f140a0e0111 76
    0x10701c10ba51a10318110300781d90201c0142481c0d01c1c0c1102c0c035219903505080140d030f961100015607071030f40e00a030700c0031201070000420300c0c01301a000070f02400880702613400e00c1c803002c00c00c0c03c01c2d9002916030031000c40844a0854500480c40c8180340c0c0c2c0081040c52608009806000652910080b01d5281c9400880d0a14900f00c84546c800180141d001444102d41410661014440c0840ca402c0c115480b00342a145c590900e628000d207040029800000c010703003440b1000050300c0d2203103218924800c074980390f540c8007041c1c40c0141446d014401c00b4000a4109440790b004900940840420401582000600541001c105544c140095403c1400c6000c2c0340354140b1910400d01d4100d0307030025141d1a624019148050050111f4484d114222000704003007020b40024a04401e6804001c1400860480010900f2070960031482c410300d0084e045c40b41c01680003049000380d80c0220fa00060003c01c800400c0700410b0002c001766800c1c00084104a04030070a64010b0502c0d0524030024080c01104098400081c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 63972673 1250 63971423 63971431
    0x30a02030706051e0411060408070801060302100813021e06131703071a09010209060c150609070e040c05090a0e09010509010513030507060609090b0a0c051c05090a1a090c0603 77
    0xe6120700080201d02c091b1045da8500501501c02460151109401c50500d1082e41250040c0da4484000300f0031410805945c400200041c6000401d0b418000280344003080d00e00c001030312482180c03a00032a00000d040c14503032444d5009007901c4e5603825401118902005c203104055128111100c510180f4a0103c00c945000b13503c000c80800d0b0700c0f100084001040300c05080c2c2c0710300e99030038419051251203000003413641a112800814450070b5185403040c03a04c500424450140c40c41300203018046402940700c10308040c080303c0c0441d062000c0601103450340244940c41d83e00864a40c00054419841c1c1101d9006502c1d503002031001e81c0d41d500b05142641e100750751003e04402c2c2c480300308003c28420f901030006144900c1c0e02241260781d0301300002c00d84101c1c880644650b5258000c1c000c54941c036104000c0305504030300b09030303040c80700c0302c40f1082486400c030b28050100358803200001c0058006008000d200c5034451040081004040c0e580c44500b0000c075031440e903a104407500040700d45030070f0081d684a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 63973923 1250 63972673 63972721
    0x5060a0606050906041a07060608030c0f0a0b0105010c0f0606060e01020606040612030c06020d020f03161e030f020403020a30081e09030f010f0b060f09060f0c030a0203070605 77
    0xc1e0a21b04000408003040d00040030070070790014040d43d800510b090040c0070040062500030342e02c3d0040111603d050411103a507140c8540d010611940005210390301c0d1303a04450003401c00c20204070719030401443c1614401801800b132441c1c41800310f40150000d03c11811080c007a400c0300d40380c2e9110307401e02003114514081c003e010080645c000c40000d104060f103515280c415a00503052200701c842d168243d80204003800180032000c410050220001d000300101d05c0010f20300340e03095903850b9080c452005403140d202000c06882d540d0500c01c12000d81c040f81d00441c0d0290083e0412a625000c03116104150000076154091101080f1080a030350b003600781741141c10240e2186424080b0917400e51400c404800d0820f445010300c000001c698081c8109692070141e4000032131882990f001b21011101d8403411a17104a10500103810350340e80203429942d4800b011345e01240c3c2e0711a018500d10342c81c09050300001c0c03144400a10070001c1c2c0e0303002c4040c011152262806101c0303a250402a030300003910340241d51031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 63975173 1250 63973923 63973927
    0xc0909060b04120204021c05070914041509050a09170325020d03020d09060504120f020708030412020a0e0406060302030601120b06010c060e030406091a030610080406060b0705060a0606050906 84
    0x1d032030554010f1603624410b100c01f55110440c000d00d00706440045035458080781c4219020080001d848100d804080811681001a540c0c01441c0003210803040c09001461652400016881403040d0f00070b0741c900784c00400013551100c2c0d20801d010690320803500d03020304290159004622408040e10100008541d40103000c0300000c3e0002100250040e0b110302013190b0f00c40350080003140c0c181c41582e0049000c0e02582c0e00e041008035001e021000051400e60440d80984c030100600c200c0442a60242ca90040c181c00311034209000081c05030596410407090420414140410032a4591142c8100da10a0b002d030355550380d03504011156402c0c03100d009040c003800880012610b62240e50040181803044d0000200e1803098030302c40749150442d03005a0040b900c80c0354248038400c00e03484499a4000c140725076a146140820100e100380480341c07101014000f13440003040401c07245400450103803400c012040e84515550401665441060381c401711030070700d03003030022030f46902c00c100704c5e0216039003d00814 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 63976423 1250 63975173 63975209
    0x6080a0303050a1e0209012007180908040e01080f03090604030209090a0b07030b090a0615120e0303040c140904110d02010507050303040302061803090d03050a030905010c0909060b04 80
    0x6406402d009040408050f601d24502e0018070754031180c06400c071180c100040c2c44000c0f0308005031100310192074030090409044800d038440c103000105007041d103042281440d00e0700013010b180307005401d10313960003083c400300030401181c074103a0700510504966100088805030140310400a441e841580c5049810080820080c005400c0c40100f194000b05008211510904c0b2901c039171466000544110300000c0e22040741017850703e0402e2060303810058a07142040300c0c62501c0c03200249005403919101c02e10030b140c0da468600d15001d5000f031b0718000720705003aaaa02d20b0a07142003a401c0205018105004100301c10104190805040d0544a560721501c00d4004100c203004010715000b011070101d0401808000f4800003d0003800a5400340f132103a00100b40d0f42c00c0070802c15107407620700d007a81c00403603100b840005207507070f62400c00010f00c54040c00c09543e550342c2003004030003800000d4400340a03513084c03000720880c9551220001e81181c00507030041202e1601c0d0b40d028055032040c0e12130b1805040744601c45e0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 63977673 1250 63976423 63976427
    0x80301090b2106061e0a2315030411060d050f010312030507090501110109051e01051305060708131e060501050303090d060c09030b090303091b180403050915090307060306080a03 78
    0xb60a90703213448401640c010001b8050500642000d41111101c0007400c50003a602c11071041d007841d040700e040803285066100224035000c0140054410f12045a84508948984007100c13580c01d243c201c01c0c06185404010810310320000e120440d940075280358403021142c42841824044c8810f965051492450300b401110b100d030092074404525540e40c1010000a5010844600168110345030041c1240f14842c2060031500000d200c0001494140c00c0c510000750042401e641c00186420046156220982c05601c7d605603038030020449004449480b0489618075504044544501c40c2400180e80b66001d150720381c001d002c85560003080c00910b4800150481d0006001c000152034500d620f665651a8403614080a44048403c0c0e0400000c1c800031890510031070741d0030203030692070a0011a01c68045400d25102101900c4440c004501250070544180c0032220020340c02010125040f18403103038190113501c02c480b07040c400d00c07480d0b0001400c02c0c080d015003403c842400f005412501d00311346003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 63978923 1250 63977673 63977689
    0x10518131104061502060105040e150a0510030609030804202d0604030c09180c0308090a0e0a150e0903030c031b160614060a120609080301090b210606 66
    0x220300da00c41c0d180d08004c03e100001c101c1c551002003240e8014040c0d549080244012103000080ca580e03540c005040140d004445422010707003100140304001a261303207504040340740220704e070070050400d0b04020850040c50307800188580201d001e005c80401e120f0f294150300002c0b0242488207900130500d601c2042450802c1da244402c415101c0708440c0e243d0a6090014507207034401c2e0422140d6900943c070600407441c45201c0c00080500645810911459548455103a807a881c13000403c00c2c10700255502d172548502c06410014048203110411506010041002a061100039600c10318001d1070001684e0f0007058440c0d000b00141d8024501c5c68581101981643d400207240c44503c0310420301602e1005028001880d65004101085000398001d103400e02c142d41000b01c0c1ea1102070660424062143c3c0d692005c60122108103840840610003403510401900d10010702905d00b82011000003a0030050b46c000e54001441140c10800d000201000d14000c4481d00c114505264004400900340c1c0c14007182c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 63980173 1250 63978923 63978953
    0x31106070801050f1f08010305070e0105031e10050403110c0105310b0313060e030703020705100c08040f050f15070308061c052107021e0103020c03030403020601051813 74
    0x1c580c1801c200d801c0c5044180e5040c00c5185d00025096200405c18442c00b40f0850303001e8218030321503002c44e514100c0002e6480c0007500b81c0c50901000310143d0711502100300003000d40c1c09000e41d006c0c01645044d0a01624001442030f0203000d500600a0300c404d130350311a400701c0e2580e0708011807110700000c1103514090480075012481103456a082c0c0c020501c0410310000e58850303404050b4030b06c0c080c003261820a041e10005914003400364000c0c0a900c0000340c02150b4030040c2d4906440700c00300c01000d1801210480c1a19070b01a0900341d0004000c104105010382150607110305540110a00c1b043c40e041c41110301c0c2d0249802c0c0704c02d1091140f070b00021b201e0200c03d03421180040940d90131380941660701c17100b01e012001c202d40c07643c004c181d0043d100301204121050903011140c491308080031900841c0869030b40a184880d44610b400905009a0199056460803100c201c110382d142d00d05071401070758629007030041c644500d0303800101c4020320214010491090780d2140340c0e181d00c4401c5a0740c06250070a855 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 63981423 1250 63980173 63980179
    0x604060b0c030901021c050304020d11041802030d080402010504090b060d0216030e030706050409020c160806010303170c1c09020301150e0a09030e0d05150a0603031106070801050f 79
    0x4480060011140d8015059040d08500030799543c4100c000007a00d016045050b074000141040754610b1078070340080c10740f41e100d601610342071071044a5252004102241680142e4070500e007540c030309050102075001c008110b2081c0d08a0754007010040007511641c004580003800564100000e00243c0c02c40d410a090041c0050314481c100301b010300d00d010503600301d0401c254522100800e05014076030301010217196024280d001d010300741c2c10580700034040d100f0b0b8081c40180c0e82e000110032080003c10410400d901e030709a030740c1041080c2c5a17010107448250038807007500082c0c04111a03024003041012842e01500819040320302d4200301002640070015100241b041250303590700e0550240e03e0a0084038001e00c0c1d805010500705007031a00011907860301600c048040e5241421413800690400e19400c22407100f19015680c0020902d40345103422403203403e40800743c41c00c0052060380c0c00d8039004001628425196054600c541410190359680101c2300038001038916001001903003003600d64241c4d821000703 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 63982673 1250 63981423 63981431
    0x17010b03070303120b04050105090a021b0f0109050717030d0c02151015020606030d08190207030201061502031801140c060405070e130302060f06060d05071d0402070b010e0604 77
    0x100000307041a00e507510036000b140c412000009074402510400060f00030444d0108419410400495100c0200a08101e10350b94006120045040e441c44058070b04071003142110000301840f4100c82c043e00048104a0f41403040150100b1800000da4954109050180082d400c0170011456000503045d003005903015401541c400b00c141d0b00002d0344491061031004003a00109140203150310001c03600c0f104080454000c8400d2081d142d030082414269882c2034501a403107a1a50301c0d0441006943d288400c50b4103200180342010190107420420442d0004440050205042107081e07841c4d124145454181c0351905108030282c0d80a166025001a0071b0355030281014081511145002c0081d64103a07059402a5005c01141250030a103a0f40510540c884402c2c01110b030350040e59802c80a480c160f0007100c81000580c0d40c0c0c0302c083c1640d01f8104419001d201500b041034016207002c041581211011203017440c40c01c0141002c4c0200c038400356020b8920407441e072030301141b4440b21001400d2903030b1198503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 63983923 1250 63982673 63982691
    0xd03051c0e010e0d020c01021219030b09100806060901032a05030118120e0604030602030406090f110306010501030c0e09060a030b0c0d0609181101110d170f060a1701 73
    0xc24843c5026038180a00105028075180001914003600ba20403541150b216104c2009200f250038207948140c3c1d040c1d055003844146112041c0c029041d030312801e039080140301b01040345901c0080104c10031541010261140c544800d400e00440c11824080035046940d0400080c40f211000f10021078052040d50038981c2240d2207c00281c2918186548d10341410001586e44060003003003010107042d09124100451800444c4c00443e005001d140300142002e42d0110024040c00055004011095405652480520060b24020456400e001c074503500038461b9074000f0880394041d01c1405401000d41e158003070301107588001c102081c10f000300042d40140000000000050451005501900d080805648c81c0c1c42403120351002c40351503501c203c200c1c5043c95041a2861043c8076554003458000c248a04178094410050b030f090805006e00d43d4140c030403040d000130b442d80d000387c00343c0c10b40920305001e40d50303034840000c00d85600344160344981e0b115001c2c2200f00540b1609001018001d01058004908161 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 63985173 1250 63983923 63983951
    0x70518011d060309071e0f0905010302030c1e04060306020a2304150c02060414090702030403020603010b03040807050f03030a0c020a0b070f02120f07020f0102030307230c010f02090f0d03051c 84
    0x1410395640c1c031ba086202c1050006c0404150b03210b02900000030100020740c5940c002a07501c54101e13064501606540c1c495107007030400005944842c8401400034440300b0359a02e808402948840e802c840052140c4141003001503012681342d001c0501d000e243c500309410124040c0d0038202c00700300401440b140084160058607030502900007002e441d0400e4528080440a03c10130074ac00808000031500200802d00050b070f030380425203041da510303426080c0e20b80e0340d540340400e00c92040100182041c400d1040c0042003800000096100e01c00000042c00201001032069a990f4194400145419035813000113a0107841048020380744060f0744100c0c0d5103032554950450303165100c0340c070f14141007400085c901c00350700f099003d14007500002c0c0700451175450085402050384440781e5860303003d811841c0801407134040080a40c2c10500c16035000b0064800c040114400940c0b001c002140070720100650b000040ca01050241c41164064503a00c0c500340300c0c18400003c101ca1504401035603a940d070700d200b143c2d02d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 63986423 1250 63985173 63985199
    0x30602030c1b07030b01080f0d031a03010e070906090b090f071e02071508091e030d0e100b0301090213020d020409090b0a2711040f0203070518011d06030907 69
    0x40900c01500c0800d0445c14000d0742a04142c00a0285034401d000341154a17000007881107401007140717800203c1509400007100c060441e490380c260702d50300f445d81c64000c52402113000021a0b005010401ca110b0351641f210050f80d1080200d598070011070320004000b000c07105d03142ca07400f41d02e9203007004041c0040f45044003c0011054841e00581c021003081c018007102074082c0070302a0035414035926600e03002494641d1402820100c4c0303c00321840607041000031040003070350468032540005110b2903440c8034405555503502800440550b0505172240d0f81c90606101d8a40d039960007800d48031540ca03101c02c600c030207944181801100543d081200203104000c900c180105140300390004501810856107807000d9511800e400001070300d0b00110b00103581401c1064100c1558000c105034910501000050005c1154000e007810060000040110003907000000f8041c903281e03031940b05490344641c03004652003020100074415036400c4031250348940c40e00c940519400059081103415090319071003010041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 63987673 1250 63986423 63986467
    0x40906020c0607091a0304030c03020709020f0c01061a04051e030109080301090b0108271002030702030a020f0606010c0605090102090a15020d1e0305070210020715050601020115030602030c 83
    0x2e03081030b810720a40d154030450010051060071884c8030043c0f62040c00c0c080310b00c4050001020f10039601100c0c01010b000388420720052420210031074840d0410003d0401507800070440d000554608a404203088111140c400741a1250b00b5540b42030508100c1030011030610080c18000501d50325140c04001c1d42c0900600f00100d01c0781950a032a540b508807403206070f46081490701c0c10f01c0069001c0203000b150f07514005800c0d0740740810070312601c2400d22a080c20000c1035070740c0d19400c9000000708441359400000810103081551708982c180744000c144136803101000d940140c00640c55a0481000c540300c1e030082d540220300780e00018500300603140003070b0001f00584c0c0319007014221034032101d8010386c042c450041e441000e030424590003031242100401414224440302c09042e030b11400300d000607200b002000d0425200200031980c510b440c0c206007543d90310140c28129a5420500000c403507510600481c3d90440c02d2070a204600360550b07032004c0103504000e00c6004924411312111032011351800d040d90f10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 63988923 1250 63987673 63987697
    0xb04121b03050405010e04140a0c0c02030a0c2c15060d0e0c0a0f06080402101803050c0405160e10050d0c08040c050420030703090c181401060c1104090602 68
    0x243c1d40c0780c000054190304554040c544250324250000d00264440d60009900c500703000741c009503186c5e50304000d49090401c500040d4240c0f03c0e0340c111400b0010101412400d40d0381c00110b009100d194001010507282c98011211900101d1402042260502142140c07684500070191801e0503585840c200484070030354003100f41a0f00461684520703042048911703014286400340e10080d1810164040c00c16000607000a028900001041400c40c1c40343d031003a105142c80d52040c00900342d403420541d030780311801c0d20010b10491030400446c402c83c01041d200340102d8929115440c070b0480003030411054035000c00000040c03040c10003d034201d40030544101140305240361039403010b0f414076041040d003e614a40100303000303a01d414110300c05000d04040c1d252102c40080c4006a681d52042e42c00c0b0060072102c14002c0c654007064102142c1c0150903202c03a44000602d00c010072203240e40c1800c18405900078402e150108540c40e00c2c2d540031520040d4a210b1100024001080c10107407640c3c1c1c1c034120391000e0040b04d0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 63990173 1250 63988923 63988927
    0x203180616082a0a080d0b0301020301030c09050c0306090103020603071101050108030c190c0b030c0903011d06090604030509040c1e02010b0909030310141804060614030a0b04121b0305 81
    0x3d261907046200b5140f070780981e04004141c4104400699031359a5039402a0140001003500c0f1500d8030a60018480b0740d4010f0001d6449503501d10380411203032001e0040c200300b03500700b02c0052a00f295070703802e50b44070304d400a00065060f4610703020b001c2c1941c0007070141010460901039807800b034282402110700030700d2001c000315a100401e094040c00e0502407407003a0b20a008641441c40492031025140003a5642c1c103075002c0d521348074038602603990700c43e40940c140c06500702135900c0356402f01c440603602c50200c8103050f40c09699840c900030381c4552003207c006020800a100e5580341c2e0404da07000c403290503024203052000315182801d682d241d04540c599000143e460300201140b9041c0f03208410340141c0300ca0000c5096003080c50181c42d1401d198003840210010004000c0d0040e0740c0c0c8030010b0102e4800002d0a00d03181080d040040c0a489503000740c52852007100c0c200c8240c2d00f0000f44c01500345401404420385030b12240e42d01f041c603031400c0184808220b0200c0e0607103020f034100141d810003107200ea00e601b6 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 63991423 1250 63990173 63990187
    0x80412140708061e160806011b0c09060b03040506040303150806090d0207060203133003030b120312040605060111100204091a031903260603150601020318061608 71
    0x40b81ca00e0304248144842e4040c01400321405c5002e007040810070312414940c642d5981d44004891041d04c400d5103ea08624a071403480034080b04949110a80b03002800138000d00b526076400407607600c0141e600074050b40c8007070b00082c0031a00c00e51000d071742c00000e03001c40d860259681a1440ca4118142e07048100790b0070800c038840b00160100f05e00c800510f00e0b40007a50905c030b052070340c010000000e4403411500020b105030380c0790243c9220311036880701821511402c4c0c61200509005000f44200d4550600074900c8a90700100d5100000c20f540e05c1c1d07118005103101e00d0b61696110303c041d010240c01607042c490f440c080c00030801010b10504034080c4910f1001a1664a402c204800795203100814068000980000007031549011443c142c0303034203c903004c000c0c0c0d0000314502142e03c1501c0182843c4000149401c00061311080d0102c0c034061001101140c0e01020440c00c003d44039a02620381c175025a00400c004161500d50345140f070342c2d400c0000c181d107040c2201007000052506c4410000c8502841c0007038a0f0b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 63992673 1250 63991423 63991441
    0xc1603080a18030512071106070806011e02010203060a080f0309040207050c180a060f0f05120f030c01020408070b09010c02100c080a08040b280f0209040204030b010317030408041214070806 83
    0xa00c6c1e22070b0f480e2918540002e003101c202515504007615402c200b22002c7e00003045030740140301400504248140c40240300b030a00e01c0090003900150f40c41c9102e0f2940740070008107540d0005c0d86200c0110140095441c0000b00c0302004001e6118410844260042009200584e0b546044c8619082c005450030a0685815940d22084031015008a2144040c0b5542070207110301e4650b10406442e81a80c0c50300810764110070061828800401c00c0c0b00c544030001351940c0c2010190007600031683c0400440f0040754032502e843c0c14034014440000d001941280c903510140c5400b11a1890064590034000002003280d155030169034410142d030b01c0459850000c0c00704120181e42c0c4680c2c04000320003d141060b11040f0001c40002e441803907030304855121004158a0a010390450394042e0000b40110344e00ea41ea403030a806124401d10040e9040c2107003c08004001c000801160702c0b0f5a4070104592a0505180401d4800c0302250020303140b038038070002e00c0d0b10030300000c004801c0901519802020700385420742070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 63993923 1250 63992673 63992707
    0x601030309170304030308060d0b01031104060f0b160305040f120212030a0c030305060117040c030b010b030c07060f24030c060302120103020411120703050a050c1603080a180305 78
    0x7a100b01a1240225400002c0203c00c1d182a29030524003500b581c3c4030203001445d000b07070500c40030303101c2c1e00050300000421607409503035070000c0c0040d5400c1c49840c1c0e84000201190b4400d204507034800e40d04002d81e0b0380744064652102096131007820300a05060702c1d49140034200906800c000524080340543c041076103400e52203803660311880f000440c501585900000c0c034840041100400741512040801c221381e02400c850b00503c0e480e001c107600b103450141000c5031040c441c0e2005507415002c441c0080b94000414040704d11846407000c007a40303807401607030f900e00044c0400c8101c055281da0740c00c010220402d50341c90507168403501d1441d8018060840c102054609800d5100d20706141c81000180c0c1d038046404003150449804488c00141d0191603446861140300c3d818a1032002d01e024020064140c2e0503500050081195004c10040795950500b40c19943c842c2e5280028407c0c5020001000240f04110640d40305815110100b010100031003000c40a0100d0300007200400c1010500c6c58020f002d03142 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 63995173 1250 63993923 63993929
    0xf0307110609010e04110f0a02061914130510060902090910050d0206090609040c050304050c03060402012a060c02010c120b06190203160606030b06040e0607030903031107050601030309 81
    0x20358145080c02c10400030b081c0203c0f5410603405a034550301a480c06114030000e448011a89543c2d081d41d8501c1917100a40340c035030444a805d050800c101140319031800c140318440038114100c10820058070f41c0382c949001030780001421036441c880c40f034040000c1c6e0160f00801005107100f406c056110341c100420000c0a08009100c8414180d0b0030070100015074503603494007400e40d01a10825615030741e00021414034410b4044050b049410018082d9007107610400451255006501f80c94405030401c1c1050344552003950040d0024101490040365181c8000303103a90312600c1e1104507a281c80711550f410f020341301c0c0d105222025075514003461030415046007000710b0030000c03e54100044800700c0c0c000b40050159030351a64569444040070700b8058020421100c0000450740420200d001502c1c00c00080d0025003c11207102c1c101c0c0010920702d083c5030140e9901610124050030701c80c0d0702e000d0102d0042c02d019100380e003055100e10503103511018040c01007402c0303070185010b450150f0450501401c0c5500e20f074 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 63996423 1250 63995173 63995179
    0x12050105071e0309020a05040c081603020406020d05030604090b0711070e101e0e011202130507020601060e1503190c090f060f0c02030d020109050d0e0a050f010903050f030711 77
    0x504031542c400d40c204042e568640d00c6081c00200d4403c1d41c004244804099048160854540104894031743c0d000703074445201e817004190140b030080d00844120241d000d144140c00c0580c0c0104180d407400e50050000e10340c081d1006e800024800345684030903c0a00c4291030680201e40d42410803000d0100512610014000703110901019042841034001100c02030310451050310240113002c02e0486200b00c06400400200a81d61941d503115450812045100201284240940317011002c60b00742c54001c1c7d030711568280c0c0142c24660300e40742040d42d08043c00c01101d64000703c81c5144c0790b81304d10b8241c00313180070b40c2c1030b6036940040d5004480c1c0c0004481124043e44240810366004100c1c8105481241d0140c0b555442c0c0392900014000c0305441480100000a626015622000021542c154007440305070307000b5821511034020152040e20310040c50140690046802c000c18001414084c0d424050b02e007041c900a80c065980c2c0e2101418620030215000c035a400c001070040901400180c0040049011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 63997673 1250 63996423 63996437
    0xe0f0108010e07020c0a08010c020601050414160302161b06050403050d050c010b15090118050a05040e0a0b010f030b2d0a060305030d09060609060e06060f040f1205010507 75
    0x100001a1503140144104128140b2101c000b4410718070a000031204404043c00c0710303030b0700394070b5603820f60280c481d81da0410010b204a400008062600380a2844c200c600560b90f01440d403103c060a003013064403102140140b507001c0101e010f403091840c1d41541032a00500031340c1951900d000c0307071031080042d07503010008001d81480140081880454005a80c0e40d5904103a03a0743c4041c1784400340500000c18040b0751018242040840704c0c0c503101c00900c040c5100740c2c4c1d410504402d5030081405440302d402182e41156881d2014480d03428298071952a100034801250100392083d5070700440c0840c240c1102c0c0001b102c0a10070010800e1080340113400c10b000100c4984002c1500b5482c06c00d0003042d017803684410078008046142c41000d80e01c00c5014640040c1070700c3c0d842103007440f100054543e160049130114a07001c8006a00c82d803a200b1a000e6894890050071240c45003004c02100d41c2000a541203100402c200c001241300c0c070382031030308000c18a00c2c034120454601030504a00b10b9400400c41d5041c4294 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 63998923 1250 63997673 63997699
    0x9010305120703030912030c031803020c13060b070c051201111e07060603050303061207050303030106030b0604080607020703110102010c080115090305010f052706060f040207060911010e 82
    0x454141404501c0685a54a90881c0d09084000d002449005814034505955920555916400680c034400850300c050110a510000360159131240060240041e0030003008500149440c01c9540c21140990001041141d1603d002035101e5010b81c04c21540310a2031003040069060620740e550050301468000c10042c914618040e2803441b44c1300c400e07803282c0c00d41603204541c2c04000e42543d40c9550003003000c00c00c1903128500256258019200544240c1400105034240b8100040080c1074850240c051803c40c0d01e40329082d00038081d4407204540c018424031010400c2d0000f01b0405109586541c000c0946d645981485607281d000d9a1400d41164106444031600a400914550444190b070b055107040c0e820104040b2816a02c0c0d40008041c1c2d400c0105512100d40c140d0420390081c0c00d0001c154006d612030031071415140003694001807da07040340d0300152183c90b002421300280c200c050000341ca84181a96584110b40f5144400c0b00d001d42c0c0d4000c1420325503441071803034684140960f02800c251030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 64000173 1250 63998923 63998933
    0x1030b010c0b06060a0504090c020604061a060f03090325020f0607051b040f0207050115080a0b07030203040201020307080708130902030601050d05040c0314060a0c14031302041407120506090103 85
    0x10001c040b1401084d000070390000851154040718014842d00904200040300349800946a403400d981c1981c446041008600d07500c040182240c42c0f1040003011a4a0303c1c004601d24855600000e0413040b080c0030501c41c00317181c042c861400c81885040504011083d0103984100040c60500d28400d0b4041d000500103000004c03400699a0b4104144001c1020f08070040400034010b00f0b460181140b6640c00844e5000401005400c141608102c103130303660846a455a688994038144880702410700e6652502040034a40698010754201c0c1c01031042e03a140c038006450f00451031340842003c4a0903038001502156005502850700064000c900c0158914141a40001c1060050120f01c4050f5603956021500700140f440180c0300030741c2d01c00c0d540304242e422041c1060722140c2c00c4801c507a001d428080078807101403040e2219031561a50303140080c110784400109548503800604102e810a42d121504141680207a40d510705c00c0a0030780d1151078090340f0030100010340d00060801e5000b000c2c64001800010 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 64001423 1250 64000173 64000193
    0x20d030b0a0902031f0909210203040e100b13050f120607120b0307062309011e0225050406060c050a0303050916090c030509060f04080310090e0c01030b010c 69
    0x140d00c0450141e105c0d100e00c5d5560550f0060410709984050b0701c0d40d0001841172898000038079080c003c110700300300740c0741e1002c0142848020510b42d80040c4c008000a21511f00013200c1280c000b050010241030305901c03101e00078010340c800c07200862041c4036400104801d2820105104c08280c040c2d900c03844407200c01c070324642d40d0000a0020814020362581d41d18808481d60f0125621140040032103e6850359030f00b0107802d00e1072103041501416024110401c19440343c1044803a084010395940c02000d061911000020b10004031140860060042061008880c5072444404940082004071024178190801044582c268400c200780013104d8084004903201150f0065004e070503041c0400c2d15940d030030b00e10703051405e925500b101c01c540004022070101304035808050031114079107007009182c03211030909030f48400840305c2160300c0d000100014002803842000d1a00500003505200e003d50300d50701c0d0701060b902d42c507201c003450303603c000031054084d82d040c054182142001c1c24800c04030451611040249 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 64002673 1250 64001423 64001429
    0x509010b0703080c0306030f0307060218190902031306020c0c03070503070612090611040e0f0f0408033c0f01090c0206011406120a0905011b12050402030c0904030f020d030b0a 77
    0x2668000c8001200e1347ca0500202a07070f40c00356000d503a41d4a415291134802504065a400700d54000e0510040ca1420700d038508000522261500d919103030304d45120b20b4040c4d80010614104442200c800400241140c005403a07982d00382405044400002c906051a00455602607803107588801010006940c01560212000c6c42c46140440ca888031410a1000742174546c1e05444500000100003410780540440d90380141244020000c00d40c41d00031010300101004d54004c1d050f000c0c1000030807040282c601354003001d402d0b0b420020309448030468540483e007404c03c1010b0080d140500c01c01c1506401e400295015206440b4108100c0304003c1c002565484140500720706402030303060080755696080d0640b0071134644201c9600040c905180c0e127401915415208440d40c1d0b0070310314186070404050207000050800c943c1e45008900d01e591804029040241c0180d800d401b9150f00c4080355100c07a00e000e803183e802519800c1c0e0000408070028680140b5054035010145002d05091035a030300c4514070411 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 64003923 1250 64002673 64002691
    0xc01111305011107050a030b07021c080105040504030905030708010617030a0206071b20040b0307050303030c09041b050310170303070c080d1a0f0604120605040f0614010509010b070308 81
    0xa800481c110a910f000c945400c0903031b2158002100108000b051a15644516025401d0700c240401158404170380d00e41c2018582c0110b4030f2100103202601b46039204650160103072500f45052580c1d00d020073300300b1040d81c0120740b80344d440d06000d102441490080340c3d09880e01000440c608465003c00079252680030780120700300680b4036048402c1e42c5400d90504181030304000501180d010034503094000b0306035550f4450181d420410140b20380d1401103100c800f158000380255196a81c0c8410b44c42480e030003000d20750350065803460100d00202c100340000003800000e464441e0749060002640b603511800394000b02038581520031640d004407020040e2604841181841442511140b6000c44c29010301c0100040302071605040c0032201c0321601c81d14014007401e5606c0d1002200e09014098507100b503004180520200c8040384000902c1948130303c0c0d0146c0210716003030111f042980d0318403d541031008004034407202c2c00e006224518000c040c030360060091034012440c2158903500648107171001000c400f0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 64005173 1250 64003923 64003937
    0x40807050a1508090a061b1205150f010c0f0609060e06090d0c0c030506070806040c02010b030601030f05030c070902030411010905011b0302071d16110a0f0f080c030c0111130501 78
    0x1681800c008078441170350312034002c2c4903030303265088003803808150b22803c0000140c0592540c070700c2e03490721301c00c2c140202c01c010b80700c000d5a050b217801e014048100b142082d040001e00640d18000ca8043d40381c0c0c0403054850f003004640d04181e42460340546d0540000a00d29410900610000d8040000c08040c0c818550802c00140c0e4a9400d010070100360950001e0701d1402080c0c200301c0c0240d48842c0d014401c1c0d03021981044400c5c1624801c038221103142940c560945d010f9801400400c00709403000000d0b520400490b85402c660040c128140b00320381d481880c0894002c4240401c1010061141a00400a02c1d29295962810700002c01102c0d840000344890301d01010640e00717041c070a002440c094000d20080a0342400790381c05003880d00e64111024005115076188440f40b142c41030031000c01d1100b5510040c440d840300f0340c8550044c02c01d220806c65842860300490000280030790080c04809028202841d2070391107828005d429151000d018440c401420800707102020007440c0440140c0c2c07070070302e8200 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 64006423 1250 64005173 64005181
    0x131403061008152a0d050f060a03080d060807080307030906050901080606070f1202030c010f0c02070b131a090108070906351510020a0c14011211040807050a1508 71
    0x2a00c0080014071030b040704089046104964200107000381914001c801c010005503640c841c070000e06247c01d8420a500080381075040012800c01409440e000c5004100001c40d1981c8070456403a20866a2101e90700b50004982c104c185900308240320010b00480c24140e24107a410380000702180401480903103d000041152802e0140c0e064200300c103154011043d04640740384200280d601c0e0441000d0b1640c81d0708050220f0420103050159284405980d002049031900b03100030742220381c00001c6140c102001d41d9400242071084043c00a00780711441042e02d41c0c40b190400010030100b001000c030b50501c483c000c420003515901070000d030000b42c1c1114466481c41707440107881a420741c615545007030003021502170101c42c0554011383c0a0105080f5041c80422140b50000ea0f1170f64914000903105244200080021051450001c1c0c040403052620765500c40480450808071030941c0319a1103040c0c0b01160078071022f00108845005004102e5503001c9451406510302c0442080300c229030100700c04d04000c6 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 64007673 1250 64006423 64006441
    0x6091c08070e10230906070204050601020a0515011d07020a06180510060e06090412030f06241103070c0302060c0102070f0803100918120513140306100815 68
    0xc0c1203040700800700c07880743d98084801443d03a070781041500c40001c01c0328039a0010b04141421140c011a01406503410500190200002014010119410340c0564074824001500520403103c444243d1000004e25504009203207450702074040080380c80107200c2d02800b013075540000340c501c642a8090004246100c074101a0a125800100010000e20400b402c5000303003001600184141c84458802c0000d59070703682d0412030701c42002e66019000115010660f41c2d080e2081c4c02ca1010724000310404038409031782e03c0c42465418074409074274560340c0002c8050410f059108203010100c0d90070078000d50415581e03403650500c001c65403000a100340000036555400103002e40641d21031b030b6041040c0c00300c2c802c001d0600c140b155004407031803580c0510640002c162041540f01d086540d800130004103189070700075542c5c098601054048001840014002e13901d050051451050150411996501410320b016042c945444006000c404041021002c280010100041d861b002000c6071110031016480b10048 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 64008923 1250 64007673 64007687
    0x30c1b060f02040e0118020708070308090102040b03090d030c02010618020c070f15020f07060507120314100503010b100c03080703090602071406060111100e150a090506091c0807 78
    0x3070a0105001142c0001c0c20500ca032100d50407641031482c52003455442c0d000301c008a109501006111030f20910075580420302c2488915403000600b0001880c10343c0743c110820540c3c00844145505030300c045504550700d507150041e011411014002031010f6410034021040c004280c006405031540e0206040c2002401000040000d02c07803041c084030120b8944101d10254000d40e4441000752040381c14940c5c1d00c68002992070101c560a03611607007802d09541d03501d1042803524030032004058035548803007540c501c041c03010b600507410003580c144000d14040034107003910f03040d0b241740e0f00c2038101040c40d01e0242d81100a1000c8580e0624106d210b03651103e03c2a002041d103450302170b15140c408180c0c5002c20014a20009020308110119481d560790800116811031018008441640240c501100c1d040e100d600711298111740582035488100d0f5038a82030705140c0007192101441d43d2240c543d0000d00c0414081e1542240404000c3c00f545007104da0400840182d0b00d03007030820000001d000400303062141d45 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 64010173 1250 64008923 64008941
    0x90501030209041b080105100f0206040201050a0e04060b0301050301152114121803010e0c1504050409060207020a05150910090302100207050a08030a08130606030203030c1c030c1b06 80
    0x2a08a2244c9001c580144581e509000e1030303002d0349005a1440034580150107100710f00c0115030017401c86944580c011901074005040220a200410455040b160385600804014107444400c0d9600c070743c0b4003c02c043c29100c50b0b203120341c56100e045030284590741280550025801c3d0b407468084409480340341c1103040c0400d00014018a0080c3d81409284070980f2009190141482c03c1071042007120340304060803601440d4200115512400c0105501c5c14102410341d41c0750440c03600c003801d1550741d2010600707541603a20700315101c560000350780f03045180c000035400203010107454100b9003000c810565820ba1103203d400c01c2c403928854603807102541c4600f02d0300c005941c4c042c02c1c500740d2001140002e9900c41190003214031a04240f04085071280000041d0307600118541d0f1900c1140e190001c00d41c2d0108982002510b030a61501c03004405070700c0410044c40d02c2c1802d14020403010301e40423001084500d802003607004060401e00f10302a2280d10040000d000351154150016111182c600080141607150f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 64011423 1250 64010173 64010201
    0x303090307020415080606091b1c051003021302070501090f0302030d0c08070909020903191203140114120a1e030e0a06171f0306051801050709050103020904 69
    0x410400012404009400e4940c42a42c0a200100700742d01e0802141819000b128000e500540025845203045200d050b003100b00ba5203560f1100712158911855070388040000003410300030190314222a0b81c0c61240591040c00c8031402d511060540d400a4482044418094500ca4001c00c10f0818001d081d80844003042d80b000e04680d421003240340107512a0480c0500d100305920780786401c4080c901400c241841040d45544a100c141d060071040c0000307400101d603403a0540f06a42c128000c0007104030212443c2405000a02c0f4824001031005064410800407a09980760840c01046044508010140403043c1107942e04845100e070800385250405000b006000c402c03e4409400700c0007422401c00148a0203035817452940800c1034144401800c441c412070b00010b004801200031401648086500000585c9410181c1c010600c8a0315009407180c105450039607980341800300c010308036510b85951603190300087c031032450306490240c00501c640c0701c1c19041c16000241102c81d540d440d4443e0105030405 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 64012673 1250 64011423 64011427
    0x30c030d050f0a05090325080301060201050412030624030216080301060f05070503072405010303020c0a1e0311150408060603061e0720010c0c0314090f040905030c03 73
    0x284003000c02a0000752000180e8242420105000700d0031405450302c290b0181c0021890a40c00440325181212030703a42042804421f505040c0c0010028402903000744820750001c1154285400d084010030220a01c4500341490442d04110004541000348510441e030b18410109050b20308040e000383c407851710314105503017414a4800030400d0600256042e0744155850303d04a05250409075424420800d0107401603000b48076060003e02403404241000614800c1c941c443c88618003580103607182178004502503002080c070b1401030b08118a045004011280010051000710110046410654003010340008401501242c03c1d4484c0c8184d00c01d083c030868141c5546a540e608150b44502c81070b81c2c960301c41c0c007401001c103214010340030014250718100d0b28030917410b44401c001074035003040020014075901100103000341048000c0c4200c241080c1d0a803130b4115041e6035490002d10102c1218044003c001c0f09100c07020030394580c40f1401c11648000d0703c002802c0600c500b8420310b5402034180c1c03000c2c1c45c0300c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 64013923 1250 64012673 64012687
    0xa0f020c070806130201090b07030c021c02030c06040b03070e01053705031e04060b0402030a140f240604050901061206080102030f0f1302040e0304060909020a050304080c030c03 78
    0x900340701241e0740c14068a00680f074070200d0016903020070101a00003460f02c142072101d8440f0900a0200f90b00c2030410b06075014041e404101e03045030b0503002e24140341c4a95a0340b000d40c18140443c40380c41034101c03503d031b2410741004540c050602000d48184108115044030808907402542240e02134011940c0c03942d64241c90b416003600d4500401e40300001100b0511816a010f40180240c80c060900c80800304010744c04040c5804900380000e0050b54200e4480310306141d0754a03244000c44c0610220000400c01c0c0e29030300c0240c440410041c010010350f204200803c11a00150116200c9845268200000400072900000c541d80250f802407035000340034500000700c144d0031500309900c84a03250340c20f00540f42d41d4041d407401c03070004440c4c108021400b42c0000d807000e0040d20307560303038403080040c0022450103113900481c2c21914100444221544001400d001d1550131004003001032581c500294900b0500da10300520501001c2d000400e2020701288145d82400c0a00035180d1700980003046a4944003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 64015173 1250 64013923 64013947
    0x18060f0b060d0903090504050103021008070210050408030726011214010c030b12010207021302030403111606030e0106120b060a030605090307060b0d0201080c1809010801020702090702150c030a0f02 87
    0x10032500100c004c5012401c00046c20304003401101d04a0790001c00c1482e41800d00442602c03420002007000c002c5001d2142803240315005846414081d0340980d40441d264030b032101020700035040c40019101c65488401c03d00030030a084c12011415101d81000c1d109400c0c13000e1901000c0d241403260420025420000d01042d03042c3c2c580c1c085c4401d80d0007101d250400b504060703000d600701d00c0303803001c00ba41220031a8101140448a42c0055401c50300c00e240800040c0e0070030314032600300880210541c03681c115809080000660600401200d00d0400c0c00070400c05162503c001c00301c40405400034400c45034180080c1c0147d03540b20140c1c2c01160452014004c0e8604916040d88903842084116003082c64502d8442c042d0a10114010116034180c403850b000b904c41c142d90328069001240c00703d0f0100040c048100540e11000004c0d80200140400581c803805540b04015240200400180441d800070a072a6500704401030030582201180201c1a0f03261102903071320028001c00035100350010700000302c10310004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 64016423 1250 64015173 64015181
    0x130c020c04021b1509120f07020d05010501090510080c100e0a0e09070e091b0406050d0606090506150307050306010c060504050307030305010602070b0a030b060c06240418060f0b060d 80
    0x30960f4090316142c00b030314400b5080c1507805444858003503104000c914103181c0124004d0030b0150360011340d01c0c10300c0306641c0080c0003002a80c00882d0300d80d441c0e034010006070a20b4003900b0380000d5480740c0c1d0001c3c035041c8950680d03588600d908051080305403840d002c003000d0003050428110940138092081c12502e50b0542400c690301616855818400c1c8040003804414051341c0310301588028005e41289440906001c5680d20304180c034550055a80c800010143c0c3e498070141021440380b00003290300d601d4501e210b401c07290004c201c240a55040c3c0f9082041a8600c001c076984103890b0f041c5039071a6211000122403811b10a01c3c0108054a028103110a001d4000060000e0a03ca6541400940e0705ca060490700c841c3c00388135110900c0c00c03e20005440038001c0c0c101440154002c0c1003d0309005480c0506868940181e0b10451500300c65149000d20355800748805081c0300f426074003400300030142d40c2d140f40081d01c0920040c003044c1e640c2c0798901c6555150b41101d0f00c00d0300300a041d42e03151410060110700034 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 64017673 1250 64016423 64016467
    0xe0106020c031203060f0a0f151e080103020105130b071109060d030e0607080c010516110613030c060e0f060a06080105010e040b0c040803180a06030902130c020c0402 73
    0x544204400d5040c1890000f030b01001d185144030f100e505540721001400441d01e1040001c99008006034800300c0c45030b280c03920742002400791000304120300b45d41c0000030380b076404d401403c04020601e03520800031258010340b80f541100e81c28a49a0b50b181c220103425103169a8680001d00034034030000700c02043c0f10201c8040e424401c01100d100215031280b0007008030034014024001c011659080c1049c0c1189002d06c060800c06001d087c04903d400d41c81c0c0201404c541007154030300800310040c1800003660794440b410b0032485031010000d0200e424902c80e0342d521094000030080030420042c00000070042180c108161601c070140444074030820100820751101d1040718442c00765803401900181c045014010325040750109800603129441c0c1d51201040b12400412401d20108100000500500e04100421100c6001100260403040910030800b04c90350b9070748031608040c1071400300000760b42c0b00381d4001e4100006a20000f01da8003075440036410301c20140304003580303d840850220302c4041e8100d4107a0301 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 64018923 1250 64017673 64017677
    0x50c0a0f030c0c0504181101030908071a07050703020705100e04143c07020313060206060a140105030a0b0109090603060e01050901020a17101203030912050a1710030c0e0106 76
    0x1070340d81350b200384001c8070460681984203002da9081000810741812030850350510600d404200c4c240c0daa00e9020065005071422078803051003111a142e54285901d440c1d4000e0080d1410f01e140081507100250b072114180202403052840c00e92070104107004104000c4e0012021b0424004441e10b5203601d85042c0044860515016402d40300944000100c0714007594040c0040252400e9448542807591800b001032400c1c0c2548030800c61440040c194840d150700529903a070003414170f840c088060215040c1181d1007071400e0041c50000a601741c1e0024140ca40c86142c00d10000341a00c08180100c40c0051a544000a002e1400c1004402d109550b084030380d8140c0d40c1070003401503407102c41516080344114402c95000500c0791404802c2410b00503c001c6d04840c180d20001000340c0c540400d001c102c1c4001d10100d02280c0d940303030354608002c500d024030b150042c1d1500340241032105882e0098550700c46c10001d62914030300440003e080b1802d01c99110091900b110b80301007516200c00301c2c0700c907514081c011400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 64020173 1250 64018923 64018943
    0x4060209030d030c050412060212091c05040320030a080d06140a050306010b2805031602060702031614030309010207030225030b0910110901090b0405030706050c0a0f030c 75
    0x10300b180c000d0162007640300e82a0f844520741480d0060850340c02d0046c01d0100d0743d0a80030005071a0150344540d28901449880001d094903800c258980c0722031a05004440051060a00c001c20100d218140e4180c1585e4103143c09440001c0d002c00005d05055100d4802070615002081c501c0c1601da031580004141c1d50510003052000a200c420400c210311544101c60b41980020014494007100c400544010f04c600d6042c0d620181c40d400c0111504002075048000241006c4200300000448100e201800791060003d400c0c24182010025100c0c4604850b207050041c001d5066820000020400740c0070300008800d0301e450703040c48041b01e8040d6005443c250018400c00200203041d641941100504080148071345041b1455a91803800d6038400404440b024010103000323403c080d0860140c040b50843e804241c1e035070b5400542c00034042c100c903070f00003800072142030009006981780098060180d80250030229160703030108460520309405910300500caa09243c6552080503000a0840703852031090000751 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 64021423 1250 64020173 64020193
    0x15070206071101110904090812010306021314011d030a051207120807020d0c020103020c01050709030605010b040e06060d09080d05100e060f0d060f020f07050601060212190509090406020903 83
    0x10f03082e01c80ca81583c0301d02100400c40d00605142941c440400c0e030b44074554160806e4865071a41e45058026481507c45a800003021209000804a1003000c0d0800030300c5180d40c2000c200000b4284840b0310380340c020405482400b6804c2c0e035410003500d01082c0c1e100046503c40340c58013160340142c0d00811400c8a03a1280e03058100b00090080801a1040800d540142142401c003401203401030640c440581c1890790821200c03110820130300030301e0b10502d695214001e900d491843c0800480340164001078600100303000030302541d0500d40d402d5400c07600484516468802d501881d20080c00460802090100300007400f0342b1594198200d548a907501568041005a8804200200200031604145e000b0034001305e9004900c1c0c0070000c0220305002c2d00700001c50f4011149090202d81c0140c481d8010200e01041400400000301b100a0140196101800c00c1d00c450566130405070049124000300f106880c544880054801d0b410713207829100c0208426074034182410131000a50000342c8260107070046001c81 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 64022673 1250 64021423 64021457
    0x2190201020405031c0c080a030e12090d06020f040e13060e0109030f030c09080d05090a1401080415140a14100f09020c03070804080303061c11040504051507020607 72
    0x154007103c10280c0581200144c90341412025031104020380140710b9400c1c0c00c1e40201e00418050500190241c40001c0d10b04403442d1807900d89180f0310360480520400700080c00c8291110b551090001350320190141c0c0391508100210035902542d04001848201101004011149141012078481c000d16080000202c3d80109600343c655010300130303001c258aa5640307500750f40710b07074001034810135a4508041c0c2c050302c840c4103c5c289141c402c16040010000b0541c05442d10305401410002c11010b00c1801c011a0201c0000e08505801480034051550118810742d0f440c00c00e070000e40e05100e03a0306c800055450300450100040680e0710450418010f4880000c2803510151140700642e4455100d0b4441189400581c10180d44102c502c0d40070350005103e030f03400090291015002414143c000303517032685040000d02800041411441070001c001e140d0110204a03000d2090003001000d0b98003080300d40c0d403418400d01e041d07060550410400c150030708000c3e415901054042c01200140e44040c2020520044 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 64023923 1250 64022673 64022677
    0xc0503060909030f0909070c0609240e100c0c0503030c030114011704080c07080304030605070f0206011a090d021c06050711031623070608010911180f0d060219020102 73
    0x1030441d0140100117411262405480c00d580c03049031131500d1600382c0366655449098030404c210859101421003030602c010282078160f07aa406136400340822903003ea4000765a66480424030440710580d42c0c81d50910308520486154040503001f204030381d5a420103c060b01c6942d4000d1141929481e40425003540302e600c15596500412080e0368201e44c1d545030307070f04c4101171544a0111800584216800005d860009101402c01140500c10000303652030300b410301803c04909400c895045410a000512100703400042184000100410498449106401040b018100c504010703520040d0204480040050032040110813032140909200a8481d401d00b510340341500122100c258005011a201c24408400f15440c4071380160100703140020081100e4006c00582e02e04a00140c004002c1403202e42e070004101d5005207400d800070030100c0c1031214034a01030701800c003034a55083c3e00c0148000e410358681415072071890000b4520f400a501c540b07000c2000790301c9241c1180403248212407400f40c050040c42 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 64025173 1250 64023923 64023937
    0x6011805010b0a0e0a080111070614040201020a06110904060816060302041202090903070f0f05060108060f0a0509120a0c060605040506031c0c0c060806011b050c100e040c050306090903 81
    0x100c41e0500102400c1680c0c81c200013803226030020001d10001404a50174040c95809088007425180d840a02d400c0a1301031710460005881a41c07444000c1c000140d9000514903111508040005801604105040d80c1c1d031042131360b01d6a01c00d00300500450660340214901d628141e490139014101d65880fa025002d901a51044840440003c010302016007009180c00c0e60110f400e0095900d03114031580e814283c100ca04100703072480c2c409091130320104003042060314054a0004004c100c14604449030a032032200c010024509a40c0b1907011925148003004203c0c080302000503400d8940031004002090302d112140c003521100e003040070001b4182403038170a0a004040180c00307002c002c1046140c0e4003c400c0018090020081500310640115005a10240c054031055940a034503003007200006000b42184000450950300703450908000450019003080e4601c410f07140341e0310810320038105440c241c20307690803150401e0404003100e040d654071200440c0715a80403240030a860300c0365191181d076409002 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 64026423 1250 64025173 64025189
    0x80a0818060703150302060d0605130203010b0f21070807021b06040302040b011b0c060306090203070f140c0105040b07110d0f0c080d29030a0c030803060a030507080601180501 77
    0x700c04202000d200340c0040c802e40b0008641600c4c442c2e500c0c1c0c045001a440324601103003040d602e2030184001e1602d032101c00c0301041d00301d80a50941d4100642503000348510001040721003030016004100504082c500704004418680b501030034a41040082c0183c40105d42c0c140c0140202c1d86070610040035050301c80401800500328a040505603801d0000410700420000e051040510f80c0000303441c07014099030360030741c803030415290014500742c0d000d000e89003650044500300c1d0051081003480b07584075107040d89802062509040f161480d1240d5486442440e44000c159401d06042109001804005601640300c03a0b496040714501c0e00e22158581422035000c60024070100292030b42203201b5031180c110280a82d812500c2c0c01ea85040d0182262941e0034480c080da04444000381402e914000e003c1d69006080d80034060a08169441c41050303140d034040105540d4003c80466071301e40305e05049402450b402821107004d540c88500181c0e40340c809200300102d00881a00181d0080c04900515040728050303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 64027673 1250 64026423 64026433
    0xd0c03020303040b0a0e06070309030206010b040b070f06020d11040f0506040b030a050726041b05030c0607060e06100e01080a0b01090f0e120d050901060f06110c0d080a0818 76
    0x10754138034000100c0a80011541521541d0b4101641c00030300c030881c0510326036200054002414079000e401c201d416400314040040c1400100a0024041c08580100703a000310030750188185880e08070002d004d0780c2404d07032202d860010904200f8071000014420b441242c40703480403003a070ba0740070005180b2a5001c0d01140c044107102180400003541c02290f000703108c43c05d0410048030344100c03184440c3c002c08905d641c958581e10611080c0540300305000032002c1c030461440c5065080c64042559000b4801d480303400341e200000c40c201408000d42c01408400c014205076500c5003001c103100241d42e00d0714020000c0405104c00002080c840001d10140000d5002c601d07a000c0340c5ca40341c141c10003070258210f0544820b80300c07101480010002e001c0e80c0c40d208900d503282c45e25512540f0604044840007490f445960b8035080b0140040c6805e91042c204480c442e150940e90301d800000098101504101403a402c40076400c0310b40d007000b08000140c5841052959091465070381d00c00320100340c1c10f8604011486801c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 64028779 1106 64027673 64027681
    0x603060b0108041110090302090a09030f02010506030a02042a0203030702010e010e060c030709090504050606010e04090c0510111e0115060f1b060504050c030d0c03020303 75
    0xc2071804600340c0c642659020340028001854600c14140071030880d000344e00c201100340295034054180007050502404110103000c10700c0088010414617044074803100e205206103071040c240200100110040c4d030302840f00505241c0d0004005403480034031002c80c00b01d4904942d14244482d4001c60303891504030002403c44a250380c02c0340d4107905019040100c03240c0002d00c560050120b82205070359444001c0c068502c14040e9100e215120300f017000300000d1080201700c0910512007a25200300c41d02d90442041b046820382d501c003e01c11201517409220f28180a901030300054402e0a2a01c410020320f00920b29054410b00480d141062510328125616030078024502e1034440080505442d030708001024041e2031255511404000d6003400155288210311081038101d070300201c0800c490308041c100700c0e4440180680d224004d10850b802030650900c585500090150140d000d1030039519 = true := by decide +kernel

theorem cover : BRFrame.Cov 63848923 64028779 := by
  have h0 := BRFrame.cov_init 63848923
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 63848923 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 63848923 ≤ n) (h2 : n < 64028779) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
