-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0897
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:34:00.840843+00:00
-- url     : https://prove2.me/submissions/dac3c68c-978c-4047-8bba-382a6267839f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 161151079 ≤ n < 161330935 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 161152329 1250 161151079 161151083
    0x609030a051b010504080d030905120c0a03080708280204050301020c01050103111e1306081c021209010815030109050d08010306050f0702031602040b0a17070503010c20070b040b07 79
    0xd6207014000151130501a074040e54445e94007059200a1080c0700c1d4001110b8903016205451030781c00900c01024481d03101c0d4290020560150000d8810164402d400c1c5034000c2c0940b0344840c85051800f11409100d003030312006082c0410001e05114074a03502d43c1100c0052200034000c641d2062901c00b044d0103007400348419a5509180c285201c054105841d020507845001c48981e00303002c400e0400c002c10800310307100c4082d4550340c2d00d83c00305d550340c010040e1007800074008280404c00101c05100031314129544040b0080b051003444a0117060b608103840f250001507104010000f0300041021034014011910090864440e00d039040034985d800402d0103061328000c17039007400340781e60700c00c55191444010b45003603005a000b000302540b11009020068040340c4000c0c03012a00f039148100188509440da00440b80c1032092500b80903016004120030402403205800a0120031104c442c0a011091100040c1c5071820801d0220500100c041c007070f003c05401500030203911280c84030018005034000b4501 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 161153579 1250 161152329 161152363
    0x11d0609180f15180304180f050421030213050105070f1704090c0302070c0b03060301110319050604050705030f040615090c0e09010308040512030912060405060117100b0609030a05 79
    0x4c22070a5542c0c84070b0010200440d40110700d018034165200001050000c5501030341036032200e0480d01d05c01280121130050b40203003800b60980c0d60304911400400002a001d00501d4070400056000040e004150f004a035002d0804d5901e940d90b60401007072a45103034034000c10b66109101461811709141010380b0a0792107220041080490810742a0103d00c01d1039009840605280e00400c490307042d41000310b0340842d001c2e0000c58200074100d0021a1a0400e41e40300e200410991801c2c03410614510500d075002808527024009400c1088000d37205100c054100c4201d58120070000d42401010f4000d103c03201c483c020b404d42265610b0b040c10006207900512240021082c4600c1d500514001451034180c2c0c0d00038a40341d280610f01710070400f054000d0340211503580410b204015080c1d5840d4800b020700d10400c000703004186001d10703084d410160140c00c43c0500c0900e1000780c95514500144075100d888181e00c000440818410000e8030328040d042c5802d616215622095040082c082007801030b903a00854 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 161154829 1250 161153579 161153581
    0x6121008060403051813060b0417060f0411180408090112150510181707050d1208071b03030f05070504031a1308070c060206011d0609180f15 62
    0x1003425140ca034107540240c0014001d0100d1681417440e0604854424401014144a80c52041801042e218194804070046d400810100549180300030208500c801c0705000c2d049502c1c0c40010320703c0206002c0e00151010b0400c10f40c1c0249074640140000c40c1200001c0d011840c0d00d231925082c01c259010b0000d6500060019642c505241c02078056180c8848400b5402840a81480203200c3c60080071132400d0200709060f10242d131484c0b004100c41000d0000c0341405500301083c0e40c2030a10302851540000d00500145c55950041910340011855084162904035210744032840110750301151031641c1040c0041114015041642652090f42c0c0c00104220902099688900981c3d86d80681e01c409050118041c0c42c9020300e0010256481d442101140010034080c42901e601100f600302420403074000f42c0c007030418004241c040084a005022a4045d281a05840e0b002402c800002424450203102110081403040c1c00051707114410174581e00c200c07010f6003240c042c400c0e0b030340d00c4000e1920222910b00e4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 161156079 1250 161154829 161154839
    0x905060417010b0d030c0f02031f0510050a05010f030f0f0e0115210303050a110a020a0303050109051005090601020a05011b08090d080c03070203090d030e010f031e02090609061210 79
    0x34000c03805440d00350300c62506c40003840e00d07281d0314519000310803a0f06004120404580b812904c410700f261621010b030019262400460410b400b030240d4004622491840408014503a884440d01d00301e440c440c43d02154902031604180007400d50201d003030482504060303031171106032015071004006011810f50145034541e141c403e02d4490300e809100c1d070b182c92000d02055010030300941107150420307040c41001800401d1010300040f560011100301c0016040030f1180000d240e8103001c0e0340c0c05060f02c40da0400c880c0c100b42e0651078021045110b164000c00c00b00c400100e450f070090000e5021190860300910070750919251200400030b507061210003154100780071901d6164000b501024009440d20790041e541c49000c0035442d2900300400719411031000f00480e02690b214107109484181c443d4541c1d940104942c000900200d000982182c200f507e800503c50b03120b01008102e8208410100c00166130300b008001080c0603101340020300350085000148122884a0050f12074494034495041100e815110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 161157329 1250 161156079 161156089
    0x406031208062e0c050d0917060105030a02040902040f0507050408010c0305040203060a05090a0807211e0f03110708070204060e070c17040e090c030c2407030905060417010b 76
    0x41036010800714038043e01c4803143c21072081c140108049424000d051801d59a1414a00500c01d1400000030341054001c10844543d40881d808105240b009040c142d818540401d55540000030003901c590b88440340d00c020364590380e0015807540c1c0340103000d00861400c0f52018001d50702034850981e8030b40c40d05283e8801c82c0e10074171510b80030740e40c018013074480f980311318545001400c80a0200d01a50142c07252040010351b143d002042c40e284100091103d0b84003101c0079614000301c40d2031a4040c810b207003050a0088403041402144410325083c60b000c0410642c60403802080300350086000d4104c001760400602c00c1620247c10614403c0b83e090103210388441a06094200955410000c60000516103000401e100c2d0344070032000e100c1304568205540c0d012002400101540c41007455000f9800f5841c0f2810184280303040e00c40c00395440421540102c250900c483d55441d00390601d004003081c621f0400d44221503c00c01420020f0855440e16141c0c91505a00100e9242c404a107602e4070745ea80803d8280 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 161158579 1250 161157329 161157349
    0xd1e061401020c03100b180703090c0909020d02010810090614040b06130e04020102011808031032030f0f061006180608150a060e030c12190809040603120806 69
    0x4060080e017000140d640c01c6030003915408881541c4140180c20f1803e8043d051032006109201f182c0e0b01259440080c10300316000e4025030402c10a4500b010f00c0a809070712454644200c140d82843d00d03010369500da400741601c0700c80b16003000c00700760306040e4005400d500381c0758110041e00c2c084400f00494500d0714100f04040c0320b101c0840201c00e45050382080114030404595901074011300004c0b4401280d02e17610854039451413001ca942550100c18070111842107130010300940382c0380b008500c00d43c54404400f40e07000c2c0d60034003140800c0000060250b0640f01407001d1041524404100d4a034942c2d4044515181d0004494000040f03f500d84d00003100740c0b04029920b0440f001c0010743c00758905080341102e00c80401081c0700005440c2c0316a1081c0c42d2524003148000b40102e0b82d504032480c25500401d42011030f0340141c10720600b00a03003026080b00c2e0114030b80c240904030b4078418424001d149810b403024000c500b40c1c50b5020345004000002d118001c2c50741c0c1c007601480d641c0d1559a90328002000301c5099 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 161159829 1250 161158579 161158603
    0x6020a02040e010b0a17010b100804050c0d020f06130305160608100302061b032109010b0111100e15150406050102010e0607050f0904020c010212090d02120d1e06140102 74
    0x14010006c0100b5003901070400c41e080c00200c00890800d2800c1d010039020301303014200c0800203001034200802e00c00140b0481403190300840e6503140340002078001506007152903602d80c0c8140d50005070280c8400f8002c80640c010b40c0c1c03110540c0d400a44210450700008040d1240c040850001030004241c1380010f140501070702c2e4000d22440c1841e80000c00c1c0c1c41c24603640540307664148410050035601001c9240021080041400e158505145c220000d500b5035a640010740e0500401a64080003941301042020b409050104001076810a4a1015161110102c14890340c250701d4410b016040103004590ac680d850309880c10302509984000481c201c42142506500c90741010300419450380c8940c0c010070780711040a420504149883c0e00080c12a0b0051070785441580d40055010360742c0c01883d500c9907000c800c08003d0b01803c64042c001945800c03000c02c040c0e20581c800280d174440b0280f01e900401d8010210100d03902141c155607030741c3c001041140241030310184686054019584002510000c2d62 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 161161079 1250 161159829 161159839
    0x1020a0b070309170c0c030f010605011d010201110304060606020d08090307030e03010b13051906030206071202030d0f1409070b180310020a0f03050c030c070f06060e0106020a02040e010b 82
    0x250780d080c07085009240550003101d00800c24842115842c081c4070203030926260307142c00350035213a000c078040600d01210740046031003690508004120903a0082c00300320340a0f5110b040c9401d44941100100d0041c0a091311004215102000b1b00c4180165a072122040d01c03e1a001c68400501d44503080d030304840202d072510302580c0100f140351700191180d440303203104c000701070008940d042449001510076040003104c1d240c00c513601e408010700003c1141c074140502c64070800c10009242140c02288003403161500c040c003222424968411181c0c0700308210303945000201d00070001c005194540c0c5024000c0b859803044840c5815000c14078010300851140c04545c600d00615140840f4441180c418010500003d07900d07000d0101002a080a02d00090030940e05a607035100130b2100402c4085c04585014241d503600d20010300c10801d2096a070400c4640c05500020065210705c00380c9091009081d0030b0308a901144420000010241e07000110341c01c5a9208071824802010440343d00341c203d80c1001300c031135488 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 161162329 1250 161161079 161161081
    0x6081504060207050f0f01090506130317040510050411030c1f230309151015050904020705010606050901120b0d020913080f07060c0c050d03110403050a0b1501020a0b 73
    0x32100c1d402000d01c141314201313403108003804d0452541054a88000c4048a0351500000000c014040c00000d9020110703429008641489440c024000309603008450341c2e001034040800c003409000c11001c00c101018007401d200920b858903109142450810005000e4410035201c50490314242d690030012004612980d03910800b0002c003260301c0d40380c000400c3c2d468851451041140036440300110701c640010001080d600e024003480010140d4002c000b21024000100184a0055403200b4011142c0d00c2d4909103840b0408000005c000f40725202c0001c01c0c940c81e01038005142d80e01b020240c0b42000c0243c90f8a440808070040355400e580b086180d49500c003405068101c011719160400682080d5100c0c50203106102c29075602c0704560002500c41002c040200d41c590400c50b80b030040032a140d15614140b00c0064042c0c0d14141e48100c03c01c02c00702856240c00400030b4440e00c800584000315040001c55801c0100760900381c3c085502955150071602201401003059400044c500ba941d582c003011036422 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 161163579 1250 161162329 161162333
    0x70c02040203071209120e010203030103150c110f0d020d030e060f2d01030b161209030e1005180f01050d090c0909050d020706020f0a0204150506031906081504 70
    0xa610003840f80c424400240080c80c1202d4141c031907450040d2242200071020f001d46100940700781440710070f142c1190300403c01800003500342c540750000d03071b03a400070301041960b8032007015945143d0145070080c0700e1080b0b250b580025503000400c0e02e6905a6502918050030b44c4c85012425601541e00b00c514a6000c140898040c1c848011041e502200030310071000000d0b10700384071a080da190030600101e4001c0d01d41c014400e00c441c00c40000e410801115510645408120001d00f5007001c1030302e02202c1d40c0d0758400c0c0006040c092801c1c904c184e0001401c801c000c4000500251040d04403100c2c40485400c036801700020b5041c0105c184000e040305841c2d4a0803c80421441c2001c0c01807000c00300e40d140b0a1801c0050802280c0c010420380074800d4001e0241c6030340211009107462001d0340270208560140c5003645100801140c040e80194040d07401140820441c042d400c0e9484103a030106801c101c00008204403111044140800383c52400400d02c2310541d03800302c0e070380e440000c1c0b10348250043c1c4a80120300 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 161164829 1250 161163579 161163581
    0xc01050f0601032003151c11030d0c0f02030a15060f08030f04051c0f06090203060a060303090506090301090803070216060e011d0f040c030c02010c02060f010b0c0f010c050a17070c0204 81
    0x81d2080394800c019806d103614502080c000303524403150181807090203002004211541c0030800ca0340783c094000304000702118500510f540d01805000d801003180c07540f81d10170340d10f0900112000641042342d941703400c4940c42d0b41200400d120b00c241d448080c5900f40120f01342a000c03003100d2117204001c0c00f20303040605107030030018510718041d5040c0b020b2100c00d0030714001035042d03000306a640303000341000150001e850043c1030034680001c045407070755440d006041c40001c0e00b03d0711001c10b503901540c01c55210030040022074014000c50402402d0014040100049644e002500104072108401c010425559460301a50749010f0305262a0109085900440407103154440b01828580c00500441519034000301044c101d4403164a400d0000c2c0d02c80304003006132a0240590585d10480b4030040000d42303000c42281b52412410b001e80645c41c0400202055006c10030040910103014060080005448079500a030465000c0001342010695159400041e05400e40b1940d10981c0031380c840c100c602c07004d070b400c000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 161166079 1250 161164829 161164831
    0x192001140d050903070c03050d03050c030621030f04080a140f15040204240e060307030c050d0201052502150405090610030e030403060b0405010503120a0c050a080c01050f0601032003 80
    0xf800c103110034420880480c984200500003107000d03001030401f403907400c0320003004e0701c6000307101981d4101d0400501c40103440307180741d82a01c641500d1540120000000380541180f18050408050180101b404102d1060100d10102c4661040b400808020302305107509850f9112402209450b421070f04c0d03a440c0714109580d585a100348014000103424034004240f201582d0501030101e0780c0e0316481c2c8240300f40d00700000d40b560062000c9000700400c0c1e2030746d610080d40c000300780183d5000b5076014482001310390042042d1003c241031601210b416540000100b078011031202c1d800c0c0c0c0700d10000080da0b80c018200c80221015a900503050a03030a070b0300c1d501032041240d5103031074074400c0594880d541180a0406d00c0940069442000d002c65080c01d4036081109888042c1c00c12032280d0420003051040d81300e1601143c084050074204050409550308025041c4524140302078511500090038208038801944445d100f803403400385541440d101d030001103080b42c14582102441500208400940d80718050141d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 161167329 1250 161166079 161166091
    0x3060a141503160e060301150f0902090d0209070c030e040c20070e0117010608010203010803030414070b0d051e0606030106120f020a020f1b1809192001140d05 70
    0x280c2000f090402c40340964861a07014030b101c610041c2c280301503841c0078007504600e100c4080070001403034200703102e0f10311300040d62140c0340340143d000800300d0355500e0b000f295808860f0010100c2c0c81c0c80c0b410b04805059104480030840c0000c0c1d5400c0804080d01d858070500d00310381110759500401c2d50b010110b10030200b03409000904d061007401030011780758003050412406044408050070320a40344d046203c0c00d4801e25044030038140d0052005101c0342d100013054a07805030300216940c0203100d0b000107090520f102900081d0080900003440c00031160340e5040789000300c40c001c40d406840201840505071030700c4269131240d84440b04100410420780720341e494000440800c0740c0010050f03c0054820304030382c040b540308005078102c0c0b00300d640d09010a008150a510031001d0301c0030803014001c00240c10a000f02401031000d11003c01203800c0d6203040044060100070804601301c800d01a04140f41d01d080a180244560307483c215501d072040d480780c032041c2c134850b51842c8031500b4418034841540107005c00800c2 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 161168579 1250 161167329 161167333
    0xc0412060f0c0306080705060f0906031906060f080609060108010e1f08070306200703121103071d01090602031c09051f0b04050402010f0c03141803060a141503 70
    0xa00c42240c11640b1900014600c9900c000901d180344c0410903090400d00c1c1e202c5441004103010002510003810101c4043c5501280c0c026540c2d83c0b001180300070510180c9260040b20700e02080030032348036088941d498500c01d464542c3c40244d59010104100a0000c1f2503150000e01d03c00d004220290780310045c3da400038020082030301c60203840504004904034a41c007600d40d5074008001081404034900c2000040d08000e45c0c0e0b45a0844107100841c0b0600c030f10300006041240221544003039000d035901030818286000000ca5aa04240f03200030001d504800078802013842c00420341c0c4003580103903415011505117402650500420381c80f03810b4807801844696020700d03250b500050004105000030030340c07050340c5041b80000070304510b1088110b40305c4015840c0610700d00801d0101503a080480c10302c400a503840c6c01042c0010350714044030701d143d006030f500000481c003107060103007000000f0310311400305c1041d0122034075941c0b00701c1c0120603100d4020100b15400e0074840401c89007100d0b015180000000501 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 161169829 1250 161168579 161168591
    0x117060a080a050730080c0307060507030e070e07090e0c0712180914040f03090503030d0603050c09101203050f0a030615080402010f0e010e0a09050103020a0e0c041206 74
    0x1692810810307100411240341d005000240a0b840c10b2180041840d140b100142c004250420a4420b007170b100300340c01501d02c620218000241c08410000c45540075071101b4140083d04003198041c02801c00c3d5141c010241c0a05040452444021070b01e86100d82c00c2940d44131440ea01d02003c04411500103031003c0d441c0041000701074045001003088201d0550255911100c0300758041d8007200a004035000b8941c0d07681040142d10000050820716074100f90080341427400d012040c17405446812499100c150540004189415000740640c04402201c0c05001903c0c2046121020030101d60b5088558603400d054400051080e404040174801245100c0c3c00d010380b90000442c0001d4044d00f0942e80000000d032034280500401114000d1900209074a0420b48080e003004d0b0b0018010000051302d060800043c0950310f6400c4e071103802c0400030503001500d08021a9144d540202c041c3c142404140d0007442203000c0000e000800c4100c003481009403010807800c081c02c0c03042d40c107803200d2202d0041d186c103a100c0c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 161171079 1250 161169829 161169839
    0x30f0204030b1e0a02071208090c0901060e0a1e0b07020a1d25350c0307021c050d050402010e180a0608010c08060d02240c0c0f0117060a 60
    0x148a50040711410100c02007250610000302c04080018113841c0110300610800000a0481510524184460034500c007159035801241d071400d050750842581c00580701c000064610781240039400f0485c1c0c207440440346c00d500e0b4541c105845501e00d0086031218940041000f504001501500300c0c1440100001d86496540d00e2080444e80091400c00c1030462840510000d0b0340c10013503d48480c0071154605051810901015050b400b507002e64101c000d10484032400102c10b50320320325184e285900d2000555003806110700d60a900101c4044c00507104401f10009081c9180c080c90101c1060b40e5112407520b40c90001002c003800c0060710403030600800640c2180c0715910908010141c000080180303880c1e1030400e24500c180c4095074031040950349040003038802654486030280e4489000d40e0b4400c01e8030b9491005c110100300c080c007802c1c1040c441641d19010041e8100040c0704000100e82155200c00c003a4003000761040a01000c6804100f01080452440241d802c4017588200005c04142000d50381e5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 161172329 1250 161171079 161171093
    0xb060a0c021002241e04080901030f060f0b071e150c0203040e040f05102304020a030605090303090d05040501050406080711030406050715060305032a070f0503061602060106030f020403 81
    0x42c03229800c1d8440700030030081070500c80d54040b0b0900d440c50f20320085c141465140c80c070307007485001f61190400d6110054040d11404a40062005080d40d45840c1e00003541c80030041c9454001100c01c0703590b100b8402071441240c4072030b18580b0080d50017043c94140625280e107a88002e140f00801e44046d030109000008001d0140d81503644542d002d00c042400242d05487e0090920660340340d064251413800c60210503c4200051041d400b000300302401a4039281c0e4000104505401ea00041102c0d040c84100401c0c0107000c0301441c0107140ca4421100301d03100e00380e001c0c1c5d00380c0114021107001075810312042025510555485400c9011340c140404029200c014560840d0701035006140800c00025005007000601841943c0020b84a61308102107800c1d0740d605500e0b81310b60f80ca0b0413450320703141281040511040c1400000f9178820340c1102d41165507818401903420382403151380e2180c06040300240850b005040090b00c0100558081d1641303a00742801503008044001a056809030f0034000400050340f4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 161173579 1250 161172329 161172373
    0x10b16111011100c080105010e03010b09070903020907050c1002071a0106180b030907030f03050f030a060f081c111009060f0b100e0d080d020706050a0b060a0c021002 73
    0x495a035001ca0107025994252801c101c140c3d00c9843c09103804884094181d100504605440d401d07e000c1688400e2030001074090319421108a0f8480e92940c14020301e1a000101c0d071007124401c4e40c0d03100041e6595207090b200d0380107495480450f504040d0310030007100f41750b41c000c15280b0f103d2161004032840340c0c03102501446c2e00360004000300e204600ca58100c00d40c0544004000d01d1076001d082d00d50f24100c030070b403500e03009039200090420482564090030103000e1003e0742d0703842c409540410f451745041110a406019030307115544003048504000b1130411310103e004084210318901c0b07884041c203446400c07280c0c600c51036070403d03d5006103006143e0150250180c022658001d81c3c000c01c4103240708083e40200c076050b9003000d1203000c03290343d01c4100f40d410600c07841030040100d0725030385c034030303c6a003031418907072180c541110305c1648001095410072113107034000e5028001081080104030b0100050142c18031a2140f9070000c122003c207074500610380508811a484c040e48196401164446501040c07480 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 161174829 1250 161173579 161173609
    0x13080c01050f0f01091109040c020c060f090a120f0209070306090905030706060602030705060c0313080c0102180a0f0e0a090b0112050d080408090906030109020603090705010e030303010b1611 84
    0x822241844811a070030040b1901400c05e1003400c105c0700c500c9014080c07182c490385030034a0045846d040084c08843c0248090a07202a000c0c0079165500c4400c040d4292a41c49950f02a100d100700c42c00110302c40c41c070380400c1c69500c2c0d88215801640182b9800300420860300502c50f03010107403199004104007440740913480758030744524000c1d80c0740ea03c02d1901800b640d1594112400b1580180103110215038001411504401a0907000e5601c1d110390320084e840200c0300c10090201900080e64802807007055004000340e0350082c4441d20400c01d8202000042d101e44c3c400d03c4540c1c54001000c2c0940c00320104a690040c000325400200e8201d0380c1c1d1032424a8a00740e00c459200c0c00c2540d280001c1c400c00340031b002001d01e11403804079900d16113590307043c9003030060f483c1c49800356a85000180240d142580403400342074008007800c2d240e262840c039a0390b82d907180380165400100c80130f0f5400c0240c1000070a49059405440026080c0041c00000d08111914600151021140c204400045840e01700c403d40b207c1c8 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 161176079 1250 161174829 161174851
    0xc0c09060b1312020306040305070302160605070510150501030f090609050102120a020703050301060f02031b06150604080c040203041e050606121501140d05060c09030c010807050313080c0105 84
    0x107000000754000080950f80045100071055040710f00681e00410042e60282e81414080c0d1500458141245007001480c0140a1400141d00201c1c03d40e40200141c10f04a10900840303040b41200809402920348050422001142c1c1810520a40d806030f0000995201182c2000400c0651610741d44181c41c282030b015280740c0d600083c0440158103005e11035900056a080070b529019496500030031511051050004005800042406d218424030440340755581a0b4803103941640c80c60b051030b44403941903036040000ba00d801d855a42c00e0419070260340403582070102a00c0308240303890502020f58001001201d000e6103448110f10300400400d038454840e0300401c0209000c3c50500140020305210000c00d1704aa4010300d05c20b4070400205401d1410343e100d40580401e044c80020100748440d0304400000d1180c00303200f04000881000d172000e1b20b4800801c03002c4598070b00c81c0d0f00040d10b00e642e0544580d0000754003040010707240038402c220300b00c60a1040c114140b41c0f614a0800908540082d00c1d08030002c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 161177329 1250 161176079 161176087
    0x60f18170d0204121a07050304081806030a06150c0804090507020a0203030a02030d0506090c030601030e031308012406021e03070807030c15110909060301060806040f05011406100c0c09060b 83
    0x8048044000c8000d001c0301003101c5d03028140714901400300e000040c4000c0c0030410020306000d8004d86505085480b49021340302c551a81041b03040031020301690300407141c01b55401c401c00d035181e512130400721280c0c0ea00900c0351031800e070a040680000d0040246114198803543d004140141c0f4100000e1000100c1680036645a41d041e03400302050f00c9016000c244221190400d0102110300c1c0c100300c81c3c00040900700003031100390305006141140076840c210031100c40604400140c6100c10341044d003213100e4a200d0300394401c084a04092158095021711801a4021501221040111010741c038824100e502201e04000f01c55407440150b901003c0c5c12800107030345c00c240d00200072540c03900e41c840a5141800380898005115480c03028081c0f442c0c001c0c130070307041d03900402c00540782980710343d0140420405407003080c542420034040490351010102d03004e6190007410210301c4072400f03405010303480041c2504110505001c0884003c1803031031080d030f08005064400580005d86226450040c6104000a80c80d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 161178579 1250 161177329 161177333
    0xf0901181e080c03010b220f06080304080105012c150409080a030c1d06090415090203090f030427021201090b0102070e0609060603100306090f060f18170d020412 71
    0x1c00c0e00d401043e42c0aa030410514544035030326580c40c0003504180313461030b011f078416522148010701104441c11180510303052000c01d072800040010801e13108079000038411031340d9800010151100c05040040201c4410752088038441c1a200e10b0fa801c1103031402c2058643c4050000241200c20202040b140e0041c009080c0f8421038060140588469041c00d11900c180100c00c1000440c940b90840244980c1d00001ca40d1040d076140d42c0a0070b4070311504001e02070001e032191b52040c0254030541e411030903403242d08601d0320241800421103003038030f07484840450048202c040c2000721500c060380c504003050302401010203011803c08c1680c0205280100400e40d8103070030b400681440003a400010381c2200e64002c000460702c51048254000301c2c29111076540f5030350f081d4040c00c04400c50304000c001604000429013405094000082d641c0d02030002004989401580d04040b1203060b159800468035519200d0086642201d2240c2050b08142a040c90a0b40d03514210781268040d03041500740d25045422101 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 161179829 1250 161178579 161178583
    0x603071d04060c0e0a17190f0c17070e0712090c030b09070b1213020d03050405011b031b0c050d1514010602030f1804090b04060b03030f0901181e08 65
    0xc07003041213040900c0360380c980300c000c50b01840300350044194030440c0218844005000f008203840801e0341030341000380008a450460b0000e02010400d032444655042d022941884138440a404401004010070401d0b1400c8080301c0307a804000d00300c40602c81c403450115490640d900450710080e200c3d020851400e0704628103003041545c00703032094889a0041c9001d1000c14843c80031901034001445004469540e455054440c800c28510300030b41000c0e10500c40c90801d600700e0050020360303509881d0443d107103450241c08000c1c400c080c0c7d400750009081d290074200c44442081c4080342d80e4000c2d0048a145912880440c29041c01c5210885a5010302c403606500e040d200d02c9007a0900710340c14600c200e294905500251389010300c82003031a007141c0008081c400001e00030003c20400a01620a110900c428240074041810031101a40c4060400b00c00781e440385008001c540ca02181000010301f0031228200440315802c06000203404140c03a0040807034000d401140c481c2e843c580751521601c100f0b041c070b18864 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 161181079 1250 161179829 161179841
    0x90103121d0d02010309080c03221415130b0309070311040e06060913051605100201060b270303030a0c020f0c2214091c1706090603071d0406 62
    0x486024070805a0201a698450b070b00c2000341c1c0928000c11345030075505000c85a841603083c040707110b100024041e802c2c000590105018501c141c2c0380318201d9503994080541d90300c02e5403411980408500381c60041d00d03e0540250000c40c1c0d118011000c415100c62605202e940182d4040032594006202001003020645085c2c81d110000c2d42c040c0702da890103d9005070360300c2000e06901e224140c03800008800322042490010002c0c0c108080f5a07185141d0418040c50410500400e406030415004451856005016020071a41d070820064640b1303140c5c1080e1a04810031040c41c0850b50035100c945640c994080001e540254204100003030b07003030071010010342b8004442044040580150882202076540c4169900c0344211061002d440e6205824903280103290480321014400710200030300c41c00541c00980310707a07080021218010000a0000300341c031481c1c0200c0712004001d0402000441c24108004c21076000a0080c0c110307001c0d151580c101d5005440d034a2481000740c221030040009000705070041c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 161182329 1250 161181079 161181107
    0x1c12021c0f150b0f041502100f05070f0f020706050c0708061f1d060f06040504090c0e01061409130623040507050c03090d17040303020105041502090604061103070209010312 76
    0x1860074aa2500c00366a171700541c85041d13810a201c40b14448198000d00c07071030901c010320003420410380381c9014806004280079522400025601c45400600c1806440030000f50030f02500240740192070314204980980c011034406c207960040301c00004e842078040004030700990f050140d43c4491402190001c0d400c414651000421503410340302d81c01058800400c42d40c100c3e03011b40d410981d0505e00c00110b8833500c600d5008607041440c1040007024804403070502c0c81a07400981440b4060399072004121241406d81c1010f00c87d00008203c507003098644a0008034591040007000715203140e80d900e115036040307603100d801c18000c0a01c00d80d018031403405103c0c00340d01510504086040901d820903e542d00e0040c11201402800c9550b04102440356541d0540c0403d115a0f8469540e142c887c54002e018201c192030459003260362800140c8000c11a0080c1d940407074001e4200c50409150090803690021210b031010072500042100c14050f81740c00202d580614040c900d10b221442941d40001c0c1260002425 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 161183579 1250 161182329 161182349
    0xe09070c020a09020904020f040b031503010c0e0904051c120b0a0f0605030402040b030d0c02011b030807080414030703030b120d120e0c090a050106021c12021c0f15 72
    0x1040300590710b40d4082d400341c5920020043e21a408880170a00034070801c400c1102000c4041000140c582c060001103100741c8000d850004514480010315003a5030051490f00003154880d02a407245040061525038014003450488a021804504585100c000d15150700c0001d901e42071186c840082600440b40610019a05a0320041c036000da801080002070240c28100400000070800355134580d00a100020b000405a5080c401c4922018007034500c4081c007240402c50008110300e400c041c3c094001c0b111501616203401036681c440c411a03002200034001c03960040581080000f0207400c001800d02244079440002d042d010400402c00c8071412125546090f600104103551015031044210340b544481c0c80c0c0106101141c281362504050441c3d86054101e00324608000500400d900450b040740c0b0507400780c44d070340281e600d4401c8090840c17042c854003150300d0060115040d940340d40101211030003000c0c0300080d041140608001e0750400c0b0f5641102544036030f11400048006ca03840c400030a00004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 161184829 1250 161183579 161183597
    0x706020f0d050c0a020901080c0a050301061a0c19050313090506150a0309020316030b0f040503031501030603020d06090b060a0f030206030a1103040503130504050c030a0902030705100e0907 83
    0x404560703030341e111441003040000c007042060b101c500420140207400e42c0140141881c0d030711811496980c0202c3c82005105074081c104c000303250704040c41600161003440358140d030710f4102d04000382015885031981124512420f05655815900004908150340c4a003010f5130381c40d06424240e040400840d002010380a10341400e002599680800c0301040202d003290082e202e221140c01a0000c020a0305d000e505070050514502c009800d0070f0201080d04e220304a002032903140d0307450081e400b6200b158000c0840d802000810500200d00c0b4420b44026014034000c01d00c2074499003c114141d00700c81d407c880ca80c4c3c5599410082088806103e030f40200e0544146810600c2d120000040c0380e2f140c8000380c01920000080781c0034480715005441c5420f1a642a10390341d003803601d0000e030b507540302ca5070750304031004031020220341c61505000720b5010312008500d26040d40c0340c500c1c031400106060130080340e152040f030320300240b50f44408010040502c000c1d282c0303030280c140c0c010030311520850040400b020054850 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 161186079 1250 161184829 161184853
    0xc080703170a08073b040e01151703070606080f060906060f090a060909030513050103050c07023003120c030106051c11040312021509070911070b0a0e070602 69
    0x103052180d00103824501002140054801c1c5d4280344840d4001880010302c0100300c04a01e01c040d0a810b010403c02d5a08200b69581c00580340e089a80c0300d118203d01441c0054104641e0440006181e080d600f40300507a890440e0a903180341c00c50703080740e0050300170360043d649080d1045030a000f1107900c45d60b0180600361a180c82000904940040c41d403d070b100e03407412030105070000120380c840710150003064400c01960401c1e00707000e00b69800607000c0d00d01d0044010b00110b07042d44280902d070b000c5c2d401581c20900745101a420880745002c90f80600017001c0042188100701440405040c180b0b41d42c900141d075031005401400d018032200100002170940c4200f0040081c4c5610104542c10a880c05040806a690346118580580a4145180c901d1140170402105010700f86403000040c00168003210100702c0c01c2014449454421110204a0b400202d001c00c00341c00f60b40c04c418000d00360504003e1804e44240d4810540c1000ad0b604650000d588080510032650304219102c040e1503140000d2016127445 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 161187329 1250 161186079 161186087
    0x301050c04090903021c020c0901150801060f050702030a0c05100503040f06090c0f03050313150f0e0303130803040e090604080702040b0f030f010c020d0f0804020d0206070c080703170a 81
    0x60320071900c950303940b01c3ca4101810b2007801180d0800c840030302e40c40000902040004d60719880f00003154803810f030600c000150309088098560b080b09050b2100c80c01a0728054003a514068944100000d10404102c0e1100503030342031001c54003107441501c04c0000d031400c1c0420300140302032103081042440010010b1102080e0b2140d0b0f840b02c0c1661002000c80d20790002d24000c1d1003002e0650082940c9100300801104102003c4040e01010700d084000f58070140c0c0d25032910307140c1390708400c01313101050b10b14444202092280700d22519490014003200e141003241c403540c060405955010340d01a4001107414800d14031035220341c03a0040581d8005248509250300c48150354072600c08024031565481881c0c40c11615404c0789281600340003016210324407000d01103e40a0700c44801060300600424a41103062401410307040788290459948000554855092000d44007203448241e0f404481404920300041e032045402c0007511840d00039021580c51450015503c1d42c124910595854090000042c41580 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 161188579 1250 161187329 161187337
    0x9010e070e1b0c0a05011a09041110050c0d0c02100c03120504020a030611180108070203040314120c0706090e15090601031b020106050f120606011112040311010e0301050c 75
    0x2154a5101c411511030611550f1050400c80d00140c01660140410710106600c0908480c8540780500b08032006a0b04008201c03404035401840304569520000c000d04100c41c1c90a0b0303803085c0e410b00c1071509a07001142c0c2d1528034052560000241e00b64040021402c0c0b0f0603180042d183c00b8100303404401d1403554082c2c403116400c0440c00394213565500003002e641c1c44049a000071908004200540640da0912000320b9000d10655400207044d00850451940b0804005101d007555074040c0d070515085075542d1241516100400c90740e4420900c61008d490701ba00020040302c0c07408401401040d00d48007020f440b0240315803200310441e44400c01c00124048510a103076001004403010f152940e43c100c0142e0052125007409125003c000403005010f42d015445001036550840305001100494400c10100b9140742034105007942201c0b001c00c40c0f41d402042c502c031004a07000250b0702d1400c00c100c030070b01442d00b15500039607800c0c01c5000780c1d03a82c558101071050041c1000b90000d00c4540703010320843c480361103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 161189829 1250 161188579 161188591
    0x9061e0f02030c0324091014030c0114070218010909031d0102030901031e0504050d0e03011802090702120c0303061c02091609030b010f17060702120d090b070809010e070e 75
    0x10f440b54040e2003800031800110900d85c8010102070017424860040c1d502e00480d802608013124004540c0e050a2800258410440c2c40507074038080c00075114241403480b0341140104130381188003040740421095510381c60a028190f2810005401d400341d003001068160031040ca0401c00031110424009640c6c0481201d00c031000070300340460b03000c0301080c2d84c10500340c401c15404051440c000c03e220410101040240c1c1c075140966440100c0c1c021103040500321220003c1c01515148101503002c01230414840c0d15900c480280140d40c4261143d041d1600c40303a0028418403202c2e00000200000c2d440c1c05081d107480841f5000003042c1a181c1a408940129400f0b44045070760701d0a800e4003041c461041c0407030005903901505000165079600f12503c0443c8007801469050301c0c0204155032000300004d8141d20418881c0d0082068941c42d01c0d400101e42e01403181030404540310102c24010a14008246d402481c00342c1c1c03481c8080c500b85000e5402c48a100c4041129504203641c2002080031041c00d03550084 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 161191079 1250 161189829 161189851
    0x10908071a0f0d0c020705010201060e2410030501090501123c030504030b07030209030d03020d020f070b060307060207080709020c030c01060b0315060403031b030309061e0f02030c03 80
    0x481c0318090090082000001d1600e800040405000355660481c20b0440d0140d002c8030301194481006900307039681d500a421907540301c4030019050b030303c8000c070310050360030100c40084564100300003080c0058100000500440e440384010080006184240e500600802001c660040ca443d80c6030405446113041d41f140c2d91441c1441892a5818210014500e205401e14501c4140070380c0b0300030301981c0007444140c5051881c01c0008203010301034001c841d80e00c0401400780007000781d249001e074000e40003035140c144050307420302035001d81601501c01407140c0c03030045240c000f1070300d444001c0601c1c0c141d468002c05d04541121a0401000c4400601d240c10b80c0c807001000b5846070102202c484c0355011b10402c1c0003047d820400b0024610344010003d6002d038150203110f0811601400900c14248250b100040004806042c1d0000c40610700304001d040c94031901d0042102d01458403141c0a4802e041106030241d080c0400515514106210706d19a612801d00290304500c0c1c91003442c500c5000c02050800701d4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 161192329 1250 161191079 161191109
    0x41a0f011203080a06080d1709010c020705060708130f082b140c060412110f03090d020103090b09010c0e040e0604032001110301030c090902210c060f03070201060501090807 76
    0x1440744c1c0c0c0000b400b5014520450b0b0116100501c0105503a03d440c03420414201404041280040103000c0c2c1e249440964000307185080c641420701a10741c1c4650000e60302d51350f00744240b852150a04110794010100001102c01d0715082541080c2082d000700340000c000e08010550359860203003005080b000d8425418007040b4403401c410144145e00c158040d03613100c0d005d00410001000441251001c2001c402c1c0d56800c075110103041400e0340c40b1085041540168010302920f0301c5403401c45da1502c40b0170b00c117240210b002c0aa540d11441021410303035050013540d45440c200b0401c103520455541c0144000c81d81888068042444542c4491000d4005410884080e00e50044041114680034502d80b40f00000c0000305c21004501140da0000c0c001100e41c4101424000b42100c824082c1065480d001001125810490f0104201c004050100b010740f40c0910050700708195240c10281007500c0341ca21002e9982c1c039003400b0081c02c46d0b0a540100341071092004043c0100c00b0001000c80c10384105070510180 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 161193579 1250 161192329 161192341
    0x3180105071d06070b0f06040f2301050303040608010905062d1e0a03020402070501090c080c0a0b04081527010212011203020a0f03024b0d120603050105041a0f01120308 74
    0x503010001d1100649c508203043c54805440701108003200d6004000e0210169881f04105a101e109601c50721000886410050121010b150300c002d800280080110042c500b00300d0480e1200ba9a00310015140f4030942c041c0705013405c0100074034401030740e0b98030a00032585119000501d080c00382c0c0001b074003890b408610ba03c20814254010030b50305800000c662500c80c2d5402c42d0940d10343d00b4003280d50141051120020f100d910740800e4806403480040500200240b918040048010040200d1014045290f226801d45404081c038140207042c6400560754404c0490f0018041c0010f9005103909941e080c228000700360701040743d901e407550020f12160308003c0c5080c103e1406000b02c085515113141541410b0016200403080171128140644030107030000103203940d00721030401c1071401d200c2e60000040300c0d980600c81c401c041d04031001c54900044003500e03a1181030031039404450440d01d450746140304842c030f01d41e141c100550002e07007a0031140066041c1141d100c00301040b117000500b840071240102e89 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 161194829 1250 161193579 161193581
    0x6120509190b1503161721040806010b09060301060f030207050709050a0e01141305070905010f320409020303090d030f180f030803180105071d06070b0f0604 69
    0xa03900c40c0e03440c1c01c001118090812221801094510816090804014829600f400728822500324400d50400410030304d08900035801945044040c2014010a811040f80d60007061000c140c60700d09040c80ca84450601c00702c00d03d0a03406030030443d0301402c1030000c10195507802045034107440161034038208010f00000154041c0c0038284004010303000c0c0383c03c041441c202d250301180c03107032032420024020705007000c911a0807542e8002c03000e200d802d030000005480004c06041100c8052103001142e16090740c90846c0030071120281c2000c07140c0041110700300203081562030b038048007058001404580d056210408103400c406244503502980d11103801c4000c5d0764090003500c03000301c4085c02c10030454107549001440700c0600c02c1070b14007042c1014051040c0c00c00c580c603108143e8160a00c10030300c25040d80c8450610350001004168405042011950304131000e016075401a03100c0c0c0c44d9040300d14410364a1040035030682d40000e00501040c403202d00410011b111040c0c000030601c4594805844a0b00460 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 161196079 1250 161194829 161194843
    0x20a1206180c0c020d0b070c0206030a0b010e0603250c050a03020a060f0e0c06030c0412030e090a0b03031801020c06120115030c020d030209010905090f04030e01020706120509 77
    0x10200920301800000c00c24540c10700080d45000c004810020018800d81c140d0b03030380084060194000a5000b01100012803072034800e5080001c078108611041c1e550390004086601c101d86000ca41c07510384003403404d656088440c0342d0200d0b0084480c2802d614140000c0034441c450710968800c580310f0402038401d841d0081e0810b1042c150440300f078418010f00d41c01c02940d50082c2d540100c0d5900e20b0031000c40d6000b16184078032030010070300c00054042c4454407000c010a0740c1018004d407907000303070400c0005902c14030008911046442a120540c0c02d94502e0204540590003c08080485040c504025100d60340401294101c44540c1c0682500000340740c0100e02d4601c2c40d40c5103079000100022900a44005400024100d52503809034241411981c4002c8042d03601d82c080d101c0150384140d2094041c2800794001d0600c6440624000e04102e1780d900000390021400d0300d500c289610171400348400d050744003504c114402001c1c0001c080b000c3c0342c04401401c0c1000101001e580340d41e10310200305040800c1c0518 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 161197329 1250 161196079 161196107
    0x60803191b1203050601090b0406050a120204170708010f0510050910030606080f010b03011a0d0807080d020702040c0201061a0c011821020d0c0209090f01050403030516110601030303020a 82
    0xa032203a03106628014000b491300751250b60218400300d00014110f030b4070100303c2e01541c034580d0b115030924000c01d00541d60080608440541140c0901000c607500344240317000c4000d00f21341c900810b03d0502e0101601d0841d941c425002e140f082c00c0504010054941c5c84c0a01c080b900b040d42c85050942c1c3c0c001042c202450603810003040e107820700d0400500d1207000940d884681400000030041c100986082500f03c81c010301000310f034108840e00c1c000c080d140011f0501940f074000d18041386400825568032940b07038425004040116404164441542428414080600b109000800200b0300f4185c1d0b0200c800710721074400700490300009425103109002e40080050301c11141c80782050100c1c2d480d1010a030307640e03036000300c0c0d840c0c0c03109816a0350188001247d540803805070b158604c034103060b0b03002d00c030004000030120f125502c00e60450940700e031024818203201d01c2c040d64001406050050110000c030138800f02120820000c9030584291b01c030042034283c112a4141001070340c41c09000c0040c0c840078509418 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 161198579 1250 161197329 161197343
    0x15061b0f121205070816051c0504080f030405010501030b0108030705070302040b210304090e1516032d06060201111b070806010905090709111206040b0a08030d060803191b 75
    0x90119158000c41246d00a200200d030180d10107010900481c0c06000b0f124201c900c540c41481004e0001c0d54070360080741c100e80510f0950340381c500700c150814500d50080e10f080754169034600040040c400c003c004070740544909005180740000d5070321420350358081800080e10a66480803001c0c0310303650700000060119400302084522004240c1865141c0e0070521030205601c2c106220382054180c0410060b0841d26004651101500c4040c521315250050f11304000c03d06a4618031000c0303138000340200c151400c02502c140c02c0030089211b04072081d140d19500403000d5a040c00b0240c581c1c80c51f0101655610540e0f480100107045102c1491450300689174403400017400303004000f0414181e0354105070b00c07800146044030100e03a9240301100031603107204041811620700307026041c0c04801e40110f29822400040c00855103103203070000a050700000d44d01c040015480058001c40d81341c50750013410000c20b0000080c508022002c21386c0f03000c1481e03d180340d130200041c00d9208240100001c451520150300511 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 161199829 1250 161198579 161198581
    0xc0109060603020f06091e040f141f0807030213090611030403022802040f0605130621020f0603040c09021207030e0604120f0203070615061b0f121205 66
    0x14540000d001c180030030780c0944810316400b10903003042d400b1100b492601520b245200568141248040c21040e20600c2d8801c0d04c41801c0403008410307014022001c005c031030082825050021205149030451421b103141102e40e90030812030000c001c01c110040340d0b0192040d405000c0340850703002c020031030700d00002e00340c62130000d07908100b180250240d442588641c007159142e406214617540c0c00d103800c031410513440070030070004001810b00350410440003605440114546455600140b8100a0b40d08001a003070780c1c2c1d80040092101300402440c030013071010f5601c0344884103900450041c81880901c03901500c00000400c0c00c20500700380c4030b0b0080104010841d1210070765041c0390615181601c441d0f00107400d00d1f0150424441c00300d4900d00490384200b154000c4640c00e03509881e104016200c0c0ca00350b020911440b00030a203113001b140f440f070302c4942039441901c3c20541c2c0a00840c1000c51008110a400401030b00000c145615a8141e1742d00108615241c2050a40885090704c48603100c103441410710f8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 161201079 1250 161199829 161199833
    0x21216060e0a03080103020915030d11031207020d0909050609060409021c0309090c050a021e070e01030605010e09030304050c01142502130e1005060d0507030b2202010e090c0c0109 79
    0x803401320b060728800c4078024400d483d10034103000000045000b80380d054104505142500d03018048004450000c00d0607130341010309102440040c2c0300e08444035409a0010745160301201e50112145d07002d821080c0c402c00c02c0c0d080040100c4c41b600d2000302094011544ca809120a5580d0340303d9268100400c0c0404d003a000c030885c42e005081c0b840f03e201d5400454100001c054550b0300660a03155180065402050030180c241940c914940540d800e03080103028504000c90b07444103002a6034082c600035400412254540030302821240e5006080c540340741c10510a110004401060314420341b8024a8031240c2c806000542c0303001480790707075424410103080882603141072400b1942004814000c607042440c40c00c801e82d40d0800c0d181d1350308180c1c0c1c2c1c0d44c10100040c00380d018142c1c07006402103009880c0f03006241182e03441070302c1d01049400c2541e02c0140b0380200440150f1140086203500041481461b40400560002e48400f03040c92645216010500c0000e054802107010740e0010b80d8104c3c001e1007030503e0b074 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 161202329 1250 161201079 161201087
    0x9060c030d0b01090609050102100f02091201050906060a050102100507050d18030212040f170109050607050403141204031e080a03090203010f05090309090a02190e0907021216060e0a03 81
    0x7440d800b07404101d1203080043c1060003140890202c2d441030300601085143e144551001700115441400301942c203000d0401c0c0c940700d038418603821005200000806040400030300d840c0450017880c1e6442260000000d01c10703070340d010501d01d058107019980429961114102950940246500310599502e030115850707040f80c0030f9110a142070300a800381e0b03404500d000e42c0c1ea00300303215600440c0d114400c0d0510030040d94040c513040c000205020000003912a119545007800c00805513000c000140d808142070050001c09581000e15500550040990b51064440203140e80110f00c00078041d41c0e02d4000c08130070356510008840f01c060f8402c0481c8d59a80321000c014005100642c0103030300940ca8003884003541c6150303100c0c0c41d000d228043c00460034610807004103e03546800500c1c0780482c1c1e40a0110222544000c00003405000441d115208050f4032441403000d8070000805600840d8405c0070300c480513049c51022110320004146410140305014206080948410b60340c0ba4000d00c5401c0c00d40040c0f50380 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 161203579 1250 161202329 161202341
    0x7030e01140105180609010b090102070801020406050c060f0106120903030b12070914010503070312090f03061b03091a0c0f03010308130816060309140a0f170a0e0609060c030d 77
    0x20466030705004c9031003400070039504501294926001403031400140800760042c000b40c0b400f06d10510445003ca03865680345400c8ea0400d13131255000c148081203d140c243d80034052140d00180582c01d6000b25850244014112150183c8000a55640d6950b41090501c01d030800084030300080c040000301580801e045583e540c5030300c1803c01e111729000143c01009500e400070350403520700038000d2141c03500315110419071040c408110010300101d80000100c1c0014503074040d000f18018800010000383c07104071480038860384003250040600d40003186000030750b40212042c0d4401040a0000e440d5194035525056119001000c0e1400704044000000c01c0b82d550020100c6007a100c1e400040d01c1c0d41d44c02005d0766403410303000c1c0c11141d0f140728800307000c4240300707030b0000d00814040c60580810009009405040260004040c1c407425900744038130040c040e0030b50585541544294440303107000c4841300002c050f02e082c49011841010b00040d550442d1f90b80c1c10964030b0103442001031703c5c0d80341050b41416000f401 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 161204829 1250 161203579 161203589
    0x3070b0a0f14061906050706020d062408010e0f0f07110a050a0204060f0f0e10050406060309020f0a0b180f03060717060a0f0b03131203020d1a03031207030e011401 72
    0x40841d84c2009101540300d040000c9070401d882d21030500d0f0096039580b01a42084000d504c0076543c1c0d010005080c501c482c017014910300d20b259690585160070b003000701000816009034005800c4601408141405440600c3c0e014002d20800480354803070b103000322561800100c02c11410700c60320701c00000f03005010500108440c8212410803105580e071001c62000c0c0b131940304102000f45103100c20040c0f090301e80700d0942d105600c0c003904a8100c1e02e4038000740840c0c100350425000a503441410608604100120140511013111031100031460148808514450003002803201003002407a96015110404520241c070b100400b41c0e00d00713282c40b00e801041000d003880d08080c0140310a000c81c0d001d0800007000c405640c01c107a134001c65035041c04890f15090344050020003004440b85c1410012440070990501e400945079000f50351390510104005c141c030800500c03518040613080340004c1a5500008690100c540c01b920580541d484403000c0c2c004280d007511851031542000c030303000408014480304d42d050f00c0d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 161206079 1250 161204829 161204839
    0x5060d18240b0301090503490e0604021309020a17030a080708060a1a09040c031a01140327010207060b010807030203060306010620070f080705011103070b0a0f1406 72
    0x9000b0b01094261840010043d20f40c0c0c000300045507a5640d4034505d0400180409441c2d80440c0c1110244503200c010142540114aa1859a04904c0031117000340244102c80d0002131a186c281500041c00034560041d08032446030b0354103160383c119241e1f01d079410010030300c0c48610708074000c1c20202c058070303640010680d4000449000004199030700580070036001d9840584910710007420301640e80405840541e02081190040c00403005541c0d45005080210390b150750049103030803c81d800c0e075070481000340b1504e040c0076071045004030001411080e82e41c00055a034144000c2d0440d20910544d0000003010180103500005500b42484103d0b04150803d030400c1c4e030303060055528120b00310200d0009845da240c0c140c00080041054611545800c80995419850134056a01802e101d901e03100031035102d02919940f0000c01c008940040c41443c005001c00e0a004032211146201c1c0da86a10900000078442d800354408506084083c1e0b00030360505145003003c0201c0003240c11041107903101101c142c0c1c415 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 161207329 1250 161206079 161206091
    0x20103060501090e041b0b07200d0f08091215090c0103060302130e120d0501050a090504120f0e0402040308091e130b12010510080d0905060d1824 64
    0x1d5481411020121a2410019a059200c690b04d0b04001d400c40c140c80300e0414903200021800d021200f00601e54940f0581c0d4810000c0c0c60801c10013102c81352140d0081c0b1400556610a000c160500c60f510180c56000c80d0305a42c0f07449050000c1c0c2d8600c40791020004034420610404c190900da02d4030903001d003013541e0849070b240511500440540c2c202d404001d4100c00d115003480308880207034000103620600c86040c2e410711406c10300c00f100190080c8401590480c4c0311001006942011104800038014541041c0844d18282d15040202410301d150780c020001240c041d020030707922035000041c042e24000d1003550750766900e051080c12500b200724451b00c1001d0104886569144c0f00c42403040e40130001d4455491104510300d00002400e040c1240c54000340d81d199113100c003400a12841e442820920703070190095041031a00c44c070f032100c038280a4090000a0b01d0501c030581d130f4182501c016198082d030110b05100c0c1ca02c00c40d418010304660003001002d100210180e0b0440741131a084080405c2c40c0700700303ca = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 161208579 1250 161207329 161207339
    0x60103140115030206070303060e15090606070201050403020108180105100e160f0e2803053003070203130f090f02040b071103070806070206041e030f0503100f03050a02010306 77
    0x2c031200b1180e40d01c55041c0034041000141004409851000e01a0034002840e40e590b02d07018400e044101e0701358031303514100860400c00d443d1450340960840030694005041218907400a0401d100c0d81c04064140b2200c0c000190151003904564141e00004800078809410404200705a0342180d015106c980d000c201e0000d08005160720001400c0c41c4c881e600d000c06801048030a8444001910301203030050121103803007107a44100c8a12240d0300100d540084121451410310b103052000b10b02d8400e20801d102c0c0e013000c10140c00340050b1000050a4003030641d4a0b21034003002d914601c11507036184402d011b0800009986400b8111001c101d41100400340400b61035911030004030301c2280a81111840306006240201c0e40c0001021502c40001d41107520704c507260a0600d2502604a9010700184e1180c4200000c014280d042c0d828540d02c01c1c4110780c85501d1a0f50b000e0325420f1315540400030440e02000056009a02007180d10080404408400049890b802c10307984800c401d1009038003083c1080c0340051 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 161209829 1250 161208579 161208581
    0x1050a0e0c130f06030501020c03090906060304080f0d0e061f091116330b040b060712020316030c1b08060c07080f160605010609051804050703140601031401 69
    0x16980004150b481d00c8121000040020301404410101c4140e0f11103010000070000d00c01402c51124103401142c079a5202810030807440c4004201c203010300c43c10f100740400901c461098a40c5400c00840083c0c079090442210801004140408010b0b03208003400c0c401c0c440801400c07801034105044000703c641c0e40b900e49081c241c0d041c8086442c0c101000f04161a40c01002c807154104c2a4031071800010f040c02d1314141a465040501d42c02003d022140d211807100d480c06100b6415098800c1e1418044104e022001540310700400300081d10220850311a040082c9c828001c60307005841e118401e0075120341609004165044020044540004400300d116411107080301580480e201030300145500d81d1500c80321111500b000c03408444900c0140002c80d4120484c0d03020380300d60301c0000049c403180d03070040c1000307420740304180e005c076003441000c0d0b40a000030344070406002011111410030314065207880c64010324000341a440a00b540a29003c810840c18000c1845412280903003c1401600c3d4044c518034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 161211079 1250 161209829 161209843
    0x509010506010c030e061e0309010b0d0305030103030305130803130b1806180708030d0207060c17150d020a060f090f1d04050f0f0c0102010c030b060315060c0d0201050a0e 75
    0x1400310743d80c0701c10900001d1003002000390003103000d0052404d080119188255054241c01842e140820220401001030340034071406990380c0049803560340c00380300c64030003801740e110600014040685650002d02010504113481b404598003071480d0781d40e8604010384220361003800c2c4088502e0768089000c640105040341c0310076403a0001001504040d1500711070031008001c06140d8546070300450a0000d00392001b440540f002c3d1020700303805a0b44807440e181c103204461540e00000148010105c8041403035402e500d680c0e90000c02d504545044c1c0c0226400140c41d9021500c0095100c100f80c1d03404103200c0d5110010790703008100c1d078035220609611001d00d203103000700341e0007400c0310411800c070b003404110071940c42c10380c015020300265660501c890107903509040c6420100b091310341c400c0045603520f50b4240f003089802041890100032000c1c000b400600d10b84009007031003400800340307602d40d101a640d080407181403403401c0003164960314861002034082e0804072010550646001310880010101246807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 161212329 1250 161211079 161211091
    0x20f1002040b0d05070c05030304060c080a0c0e040e0a0219090e03030c07030c061b02060106110d020a0f11190f0e0105060714070b12010312090605070b1515030a05090105 75
    0xc1410210078082d030f40000c01c002030030a004c00c80c00580e42404900306000442c019400742c03270b0218a45100850141450502800341103c00d8604945454183c0d8032203030310050a01c0451f0040741075140b08002c980303402c103515000ba41c0481301804031040c600050030f480c0c003160b182c40020702c0301c0100380d101e403a1240011107803410460700030001500081d21506d42c49400c030344202c00000380240c0e8145244802001c0e0713111000582c0c0081d0051110613000416254102c220400a14039085a60002906c64054030b00c02445c0c2414100002c2c1003001a990f82d524450b400380001070348416040c400302c1d80705882e1003111074410100002103a03030b0348000c049606840014005920784070140e03490030354141c12452503142e140030f0108046900c0f080c900040034040381d2040e100b501541541025040d4204060b072060034005030803c10400f19410005540310160070803402c40d00c41d038949112964000c8543e1486600c14030500a0004a00c0c50308090350040c0d800302e03000c01907943c50750740c01c500b03ca00a80705 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 161213579 1250 161212329 161212349
    0xc062811030d0209060706050a0902040f0506240f030702030316032d06051203090f030f0c19050301150608060d0305090d020d120504061701150806030c030d020f100204 74
    0x401042e4820360020586810060401c602e084172588444040307400c02d485103603030161200e0f0682d0541c9014003e00c0021103c40d00104510304002c0c00080c2e0f60301c10322b1503400c3d44084003c4c0c10309500103001c05681c1c11300c0211300119500d1400c0c0c4402902d0360f0045a12100c018a0000f68480d000d100c0c0c4110043c0c141400c0381710003400d00180c800502da418a80c540c101003900d41030040b440d91103544214560301e07a600300441c2ca5400e407074200540040054600340c000c2d48002c1c14100100c000003810f158140741540c03100c1045515003000e2044a0b8103420894040d805c0c04078109500880d0102a411a1130554409a50382c03600b01c20060400850000503000420034410074003140703041a441411036200405424401ca2030340c1c0c8004142c8001d00c01c0d03c012a0000c03508016064004405000a910034201380d8800e60604440b0036040404100c0403041103010310009010b1344080100e070015400c021b0490b09a03000031302c0000d603603d04084000c203c5004031903074181441c0190007620280e52031201 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 161214829 1250 161213579 161213587
    0x7050304060804140a03030c030f02090d081c0e0a03080109020c0607031113090207020a08070806070302092209060c11071202061309020904290108040201020c06281103 74
    0x10111081400034100342c442a6804003654024802088606003052080d11f000c6100c12903030074050120380001240d02c0031075004000030a1030b507462110b0b0311400c0c0c1c0e1000da426256140b00d840c42c1d842c0070510052004941c54082c4c480d00e0b014002a26505891103951400b406a0b290a21070041e80110500ca11090740100040f40300c082c0aa0000c40c02c4070564900e803400d1018241395200300385182c0d841141c0a40e8001442400d50401402d1840900b280710014540036141518035a51020f0040101d400c02d0750100d4000700680d48c400c5d200000d08032500b0a00c403050075400c4403030003d00001c0c070100c0c2d00928141516030641d018018410760380d0103810140c886c941c6070031614130790384032100d000b240c2c020030804c9170002041ca400c0c18080640012480183c0b100d40309801e0208a610340b0ba1400d60b07000160080b132029602040d54649242001e2078610151740b580c1c0b0041c0d1070841c0318202c0592200000c1120800f0844a88000b0b100e00d0f9401c1101402522008065800c8214031003805a00d0304204 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 161216079 1250 161214829 161214839
    0x1905030c0f0d0b090f07060309060608150109051f0611010f0506030706030228180605030c2b020a0c0c050a0f0b0f0702040212010e06040b1f02030715060e0a0207050304 74
    0x10f040c0307640a030060080d00e90b40343c0b442d030742c40f400d00d0790a41243c03000c240d07100300001c24823180d40f26a05c05400f40c4401048240c0c940008180d6203030051040c3c44003d074807500081c50545080e101441801000304400a210751114000762a0150454a8500d41e6103030983d1b0080804590249600411005c0c0281114508102003107010b5400310700000f02103000808102a10441110b600815000c603640368244018041000000c0c10419442181002018002e0081034885041120341011001e00329207003442d51035100d01030160681c900c3c000b0b02840460b0085409400c07034881c00c0c50718441c0600365100c54490003005843e20f0345000d8141c0d5680f01030801e0200700c4034840100012600307400e0040c02c10085500240607607214201d2209001c450f00010010390104880c00b982200b0111018042c600d032520100754800001c2d0000c0302620684016203c00038001c1c4221180d10303800c40e8200d00d0760380340345020b4809400300f48500c103032900d03aa10000c0c002c24410710070b49031503650000186203054036103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 161217329 1250 161216079 161216093
    0x32b060b0a2006090307030f020c01020c2b080c070b070809010507030c08040b0414030d02120310030b0a060e0c190c0213050f09010605030f0a1e021905030c0f0d 71
    0x301d80e8031468040904030680b074590308204043c4580d128a005580d680154500100103441b4071400406640c0170902e074000d00e80c0c0200e40c40350300c1c13401514402c0321080c1c0c1c0010300c040d03c2e099035503101e100410802801c0602c0391a500400c40d650001c1c0c202c520060b40c910381c1b0410340c824007002400b4034405104c0d01980d50302c980000c10680d400380c6054801d000958a9202485c0d0007940311003514200090200101980a0381030b0a08010031405403009546020002c2d440e9904040314a481e0400080060030740b200b024010b5015542040c06581585001c000c1c0b100209841d000f50b022000388000092000701d012822501c0da0f1000f07000069450704a1601034986002c4050101d0f80710b2044103015110355464496a03103c0c90340030044406906101104500f1140307560805406500200800034060400043c3c03400c802c3e0f445001240324001c1c2244c2d1980d10038801c90020740c803210031042c2d0505481c04540307600070b80301c0480a4a00d050b100324104681107170004102900407448100f80008a40b038 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 161218579 1250 161217329 161217347
    0x1e0618020a21023c0109090e0c0d030908010c0302040e0a0501060c11030c120303060a14012703062a03050112060506030a020303031008060c04060918020705032b060b0a 74
    0x15514180c1180903110f0320883d00c0d1355445101915002064006a40703603404888600100580b000801800c4170f03940c00c40d902d580110362014010510366a1a10402d0305ca0b550020080800c000200b0800041e01c0d0010040e6000744548102050b166012405051702803040c039040340c800341c560f01180c65071551442402e01c40300d1030182d81030040b0040c080c04e6898142c8511401e02d40400a075550345004d104100c10080345401c0150130f0070b0601d00301600e1366040303070140c4103030a52402603003141c80714000600f0401420b40c0005100c1811f010003035811008051100046001d9041c6144d0701c090f00d2081142110400d100300720f1401d001d4840b1130b0100c1c1d055800305030405000790503980c1101c0c003500031034615407040d621514580010541084156410310116401c1101004030310300e05490071000520031540c90040403448400c49400b4542a00d06504444199510600f600d1b1103110b000c0740c078200d130351080c0789504c0b007800308024004100040d407041c8400c0d82d000480e00760134118280f6084079410f107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 161219829 1250 161218579 161218609
    0x510051f0512040c03050d0305150d0c03050a0c0e070e01090e0c12010312090501030911040b060717030a0f0209150f090d060c0f050310031e0618020a2102 68
    0x1003004060340480342d12481910550003000301c260002d2442c0b0702a8034200e403181d0480704051030181489088110001040c03042e0400316200040c0400c1410900a500b0881d40028440e1140720680e004015418a43d8000c90328031a41300400340c0e84074070055811850605240d40080c01e00381301841000040c145554100c8103211030b07142043d4100c07840c0715890740c003a08150798441c0c0000014001a40c01040300c80944800c2c078050240c280c0c10354405c10351884050340301b032080307440303491038001512040c013960001038002942048594825881c441c0306d60050b01e0f211050b604014148a6428442c00bc440b4a50070240400a10703c040c1004c000c40c03078100303286402218804000a500f1030740c45450b040d0760680101400101c07801c0a4101a1881549241e902d080c0303c414410401c90200483d002000c80760000401e00003103900c2c2d082c01c241800b0302c01c4000c102a14044001041821800b18210405e2007541c400b0800d079101c085001291400d40f080c00031601d516498400103003001901c03008651 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 161221079 1250 161219829 161219837
    0x70816050711210706020102070804030b04051f020c01051e3c09100608030313080702090114090601050c03270406180f15170f06010602070602010510051f 68
    0x5182c0300000381002600714885501103a03034805401c007140c0103010b4031000b484140000c51800c41d0a17501c8544074050b510004d090754081c01c1c00075040c08414404c0d03141503078540c90008198400c2044420094025640e0b15079a5880c10002400600d01134920f0240744080b2051107005550300104120001c0f1100c92104080207030b0810205441800704200c0140105c03804a01c1c201e180a68185182c901c0110480c001c103414a1800c00c813081020040701e03040002140000b003d030840c0e04101205e071060520094000c4242d900003e80c801030200c1c80050030700d04850108140e00c443c40119041d00540c0381523082c0c0d401c02c10041b20f0320306864040000039a00680c21a400201c084001821980c55520402e295020514900c0b21003020b481011441c420000d0104140d842404102c460004503005640c0c5403003010503c4040914108600b0070b101c2c0100044841c19a10307640000d407100100d1140f03030055800c0c5000f1804c507580803c02d05e02690301c05000f06185031400001d1440c81e54000d50190140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 161222329 1250 161221079 161221103
    0xa030e0607140d050705010513080a0c080715020901020c0d03020c041d0709020903240106030b180106200a02090c03061302220501020c0f040b180a0b090708160507 72
    0x198401e1003e091400700310388440f070301c5400710706103142919401005030000302c1d96070266000089240c0c003a1100390500345841818240c00380f405400c03d1045441c0601714030091101c644804003203400610780400203a09581c4401c040b00140540d1204460000340541c1001448040d14101a070145460349501c2150709121000c08040e1810121b44e500000200e6400003501c0c1c580d0308041289001d40041341d031100c1c41c030b0450362a411064000c103008150401d5141c90300140d8942e28014003003201c0103039001004003941c0d1424040c1804865442040c030030084100e5158050720301003003000110b41c0140928101c1d0707030b035040c4850b0540e00040c03080d9802622a5080c00c5e44207490b1014140c407004940c0c0c40b008100305c004503105400d81b5075101504551003c1000401512090043d4201d070f1025500840c503100c104c00020002d507446403007a60380c01e11140411103d00e00c15041700d803511070f0540e000c1c40c0ca80c4401c42c0c101c690010485140541d80c8a4180d9030f20100e1003100140004da010300721204034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 161223579 1250 161222329 161222363
    0x21215040906050a02040305060f010e04060f06210501060506040302060d020f0c102004150809010b0d0b220b010608191821120f02090a0b030f07020a030e0607 70
    0x443d44281d0705102695408038050080000801420360403c1a09000040540c9488440b460000000300010031854954098041c000c005400100160101e41800d010440c0c1d0180c8400a200c1d6000701680c2c03d40c00d01c1800145414403c04aa0540c2d03000780030549010b042842c0c2002031351051480300600b5904126454502d40e05000101d144185840081003928040740ba0b0b4510200c01d461a520340c440800c801c204200490108406000403410506041ea8801030000e00400c43c07007404580003102c1c1d1655070200064240c80c1c0348110031880914a00540c0c0b50032024510032180742c014185000c040040c4825402074a260b42d0000c1c04a588009840040d40d10406607501d041103405041d0700300303041c0ba0400041182c1003c240c1d0f1449090000c0c000c1c94540200340008000355034410035903603003030b841308082a41c04071005200090500f0300c08a6594005e18050b034421905104000b51400101c0c02040c800b03c0d100b803032690035aa41e05400e401c41400c2182e00d40c0030b072408075521007444841402d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 161224829 1250 161223579 161223581
    0xe060d06080a050615010c06051b040f0f090608070302011b1514070e010e062a06011511060a02030c0c010905100c020a050a03080c0d0204090911010201021215040906 73
    0x7a0000c54040c00c22401c0d6490924600440904988032140560010780c2c0e090340d104005244a80d0480c8011840c2d4913444c3c043c2591030924058160b00c0701000402042c5d00c032410345d540301290464418800c0442c0e41d2808641161190301641805810105080016600c91742007210942200b00440070440300741da45960996110308000710903141c440180214644118000c0c0d43c0c0020141000900802c5040000384140c2c0c80d03500c2c0600c40d14001c540c140302021a0110030503642c1104404050709120600071550301d220901c540c110118001e2004020b15100d07440000e01e243c2d0120080030152a01d103004000b941000b4680f142c500c406210307040e03400d1001d00480d12040d00401c00381c201039550702100c4094584003110748040d50700c0120300d000002da00080444000742c01d46480200b98440102c1d2091920481400b00c0c1d0b914004940815901101da1000380e42ea0f11880c4452401c0d4050001a8242e015101941c000d480340c01c40016013800911705062840d240007400010352980590340c0030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 161226079 1250 161224829 161224841
    0x170a050f0c06010e071d040f1503140c0a03031b08070f030c031808060a05060d050708030d0f2705010209040f0203041b030215222c0603070302010e060d 67
    0x86140c2c0c00305004000160050000c2508242a4600500400c070202030481002c0907115009010350323035480c0903132400f124680c002900441c0100c03801429079500e081819a0000404051009000720302c000e88852501030980d07421a41d0548804031441190b004e4803145200b03501050354040f00400461000441941000600034400d481d040100c21007420024498804c19000c5220242c0c2c6e24005d01c552040001e043ea40200001d201044540d1418041800350109030402030080c45824008618844080090000c01e14054410030203140749001017000e9070035210740c0000401040142030210b800c800311915000d806140003528008030100403c1c05c507031081095105e816408000e1008002003010f1011000080002c883c090b2810741d00014810011a542c101030583c0004003480540308440004580c1038088091f00040c40d6215111a08410070301b1150700c9428003a1080807a244d1800c2c00c880c095130010f40140305c00350840d40151031051145a007190b0194081c0011009100c3d240140d03 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 161227329 1250 161226079 161226097
    0x16030f3509030a02030708090a030804290304020f0d2109031103030906030c1602030102070807020102010f1103130c0e010306140a1a06030c0c01110322170a050f 71
    0x459459924000c5180d84000090041c00c0036030003c110080c0c01a50001c160798409400a81c416500e564001c00110340d18a03690008040f50800315001034a42e072044001c070b81c0f240354503d1220080c1c00d02568810503100c1200c00070352101c64100030070110700b0181c400c0072401d4480c0543e4070300c4004803502441c210f02d2009090300000d00c1d101c3c0a000300071032140340351004d2406500850520740020002003690100030300782140e401000c42d000d829801c44141d220603081e00a0001c41d03a40c4200c0c03c240040b039002040a82c01b560a08560069612491003100109894008010304584842403010f400341c0b03804005a03005200924080340b40d015100788140218031681c00080c0400d01c406181e102c5910040040040b640380400b00c101c00b801d540003402e5102012558143c3e01d5855065040079030040844600042d0301c0c141217407021380c4140d0000e41c000e03e0402d02d96406484425000c01e0740e01170040004160714201141440c10300b4121003e0680403140741005414a4081d403507600c400c7e0042408 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 161228579 1250 161227329 161227397
    0x70c060501080606010e01030e0c01080705070605040f0b15030a060c12150911030702030405010c02040906090b090c0d1a0403030902060d0218041109120118050f070501030216030f 79
    0x41c8004d070768110380021202142807c051248016400900c0e0b2594040d40980e41844a05400507004078801c10440302e4851b8000d03000c2001d801d0906100118105030802180c90040000100d40d066103810250001030308001d00030500046181e8400c8040c0c0b17041d80d44042403110145e0402d21010650244603501d0341c0301c00c104c98206d0319289440c0d0a07515502c1001441c03440800510080c15030202c2100e0944000307003000030f810042c610200700181181030006d4034507860400c0c950100f001304484580a624414100c2d40b01da128007040000001242500a0a00c16901c00080c8942001d41c01e00d80d206009050016040760f194020400c9a8440c84102c07511550016004038040d8042c0c2e000035026105440070070510290304190700703643c401c840380b031072040c15180c1c5080424102500801984030424010030b0b42000c5519000380d442040307400001090084650105495200344240c1e0f10030b403003401201218881584059071200600340c6045c081014800c4186041144000514010704c83c0e140 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 161229829 1250 161228579 161228581
    0xa0b06030c09011a0a0203043302030306010909090204020f0304030210050112030507021e040f020405011103030f2403060c0702030c03161a0919030b070903080f03070c0605010806 79
    0x4101420010301c0e4915600c210800b00c0140080000c21101d00005010352645540e90440c00006078038600880d0300840009200240345000b900240c02000306a500c00112041220020907007030344c0701c0c0011940f4600180202508008120300b6401c02c6020340d002038001840e0942c2c070004200c05501c00c580030780140c0d204101002c120300c2103100c3c042c010854412040d00c0e208003603800030014410000040d1040c29024049124001a403070420315100009004108038121888000040d41281c420b15000c1140408000e040e070030003004a911070f100740312452103281d980b1b0140c0c0400304026010010030410617195212542c90400400d4080c0303e14071882a01d0381600e1040500e001214503c4c24042d4200c0d00027000001c00e480b50090549811641c1d42051030142c00c00500e190184168042c1c0c0041113040002d84101303444001000d8038011200d2142550311000207503200000351100522032641080603500c0c205d440009150000d1007440e00d070b109144c640d20350100f0b070b400c01e07040b42100d900b10754 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 161231079 1250 161229829 161229841
    0x30b180712200703050c07030c050a0801020408060c1b06070c06060506070b040213110706060602010605060f0403081303080712030606031e05060a0308041e05010311031311030a0b 79
    0x3010240079070080c10703400d010448150041889100045001c44246080450000201400fa201781c0700707401c3c1c0c1c0f00d088551040e680d08082406005510480d8000d190303e4202240010041c000c4905030391841c2c0007000d00e600c0d940c1c0ba0700803da002d1003c190b0f00389075003402042002c406210f980d000c1c3c58180d980080485050030540121441a8800c901ca20f00402075000040d080d00c106c1c503886034040f110040148000f04034074000c6e01104500341e02000307000850ba002c00c007450b4024001d0311a0ac0d40200500b0340c0310410b02040d4450843ea0b40c4d040e441c00d110820000340e400c0024456a00c0d101c030304500065407030303485094641050b6400c860f0a0060300f5001840c0d689885500002c0040380b5040c80800d802c88014000312661a2200300c1c01515440024001d48035507595078015130303101310501d030340300c1e070302c91318600b45644210a0000d0840d50320360004456110b40034050f40e1400344000a491601c484a00c4807604803007030802c8480780711080184074655414444010018000c020f100030b036240c80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 161232329 1250 161231079 161231087
    0x150a050a06050111100b1207030302150a05100e0709090903030920010c0204050402060702060f0301170c1807020c130b09010911030103081c02040f14010809100903030b1807 76
    0xe504503074100000101c4c104025500054507500850b140c050000b184044080403981a10994804008612500000004055001668900182c141101d41034540c40c0c844883c820749a066581003100c09510a0600c0004051a0f150b0342040e00c1c0c0c03c20030000c5a503a45c40380151550303c1019000b00341d0710000002407100c03080d007910040e040303229000e04038802c2d0800a040b41c052007030041d0045681d00001800c5480d1101200c0c511600200000c6c1c41d80c480114107000380d40b09014241500140d2140103c2e003040c0014482c0e07414200034680f070580040d4035152030011200030104c6086100d00c412307007210b0741c0322108050717040c00d002c0c03401242d0281d00100b4007155010680c00482044e207000400c00074000620103403819250b00580c001d60301c4013150042d030306a1328404241d80346c0701d2001030001103640180c9008411512107409862001c2201001502c002038201d40b03241c0650030184041080301682c0e4807154001c0d00c00d00340002c3c0c00700405c1c00320703136501034112000c4810000001480015608 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 161233579 1250 161232329 161232341
    0x80c151302030d03050903040b070501060b041412030a171510030f06050108041a041b09050609010b03190e0a140c0f0307080c010806011b050d0e03030c060f0603150a050a 75
    0xfa00741070110381010b2a460b940c0340b01e1442620510f1802141c0f80c01040b40a40040d40100212500a9290383c1c8505034030342c002c5290071840340300704c200b0b8060103030044021081c2d41604003140c43c0c10003441d828442c00950403000074960302c00d2402e00407805a50f0b07991784540c041c1c4070b0740541d000030f1200c0d440b100c81000c8038480c6c0c01c49818081d900301004002205800c004c50070308604900880700703032103516003004c0200010a031044d000c81e140b000402c1c804203d5010620480c400c444584541e40e03a038030381d040d00b44015aa41c3c410040d41c40c0410f003840125401c0312102d8112801140d02240e115200c08043c91410740800b6450342191107586094600481c004629400450281455070302c0d084625582d0a003100816040c00415000034007240e00590310744134608480c4018501d46055407900c02c3d00d51041214080100c0c05126040455007400001d80b4100344613600205000d032900184003030b41240c000c00c540e51600c90042181800d5140410207801031707492810109003414010395400a40d01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 161234829 1250 161233579 161233603
    0x61508070b030c0a020c0303041215050601050702040c051b010615020d02100b0a03150c0f031107060b060d0e07030c120803010b03060f040c121b0c080c15130203 71
    0x10000e00140001101c290031a81c1000c0e00802d841d40c0c0c2c508405090f800c081c1354520242e898000410005000c1c40c807000c40d070504d9445190300c0e100c082d0012554074119081030b6403140c0040c00600050005003401e522107aa00c04482c20400d08021481581f039011a60380000d103060341e51542c41c01c0010f80011000c40744141c02034000b0380010811087c000b1743c0c0749a0501d40010081d111812007455032100f91740301d0051600098005601103a0303a08000180c100020b002002034103002740d100444c0d00c02d10840b011041d2403400a8604152074842e203020341b01a401d51075001c24101b088042c92803039440f400004088080241c0300301c40c0766041c01303030b00c0c1003a0360701c0b0f2010a0420105c040000d002101124107480c03845220341e490b9101c0e0804244101011140d468100b80341c041030030441d41c2c000d5170b110307000b114a0009121860405580030440c4480700e03040c002144024081100003413100001d00070101c03a00382118031003d5000c500c00100720060301c4594a110030300c1c881d601541403d2007000c40c40c007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 161236079 1250 161234829 161234833
    0x30b0f040204030b040b0406091502030f07090506090f0a2d08010c0207150e10081506040f05040b1c151b0903080a180b03090d091a0702060403020d061508 68
    0x540fa50322500d022040c0180014101c4003a28001410000144e00110815400141400e801000b0384828802940180c50b10400e100002001a070454441e00b401c1d002d803103000d4000740c1000c0c2d82d41c05007d042e294914003194003c10a40c0c2c041442c090348400000b444c008120121600c40070007030312000101d01500007183ca43d040040300000380c0d0300002d0030402c880180a1000307242640d800c044440e01c1041e40c0c0c859121041140d0141225844010680210044561241e940c0d0394081004030501ca148070305140c0c0e1684d50810410f510342a032114210200103010b00109500300c020000d601d4480307000403111046400d02d4501c13880e026100e24074400c5120100311020b0805094041e204c1049480010500e6031300103042c0c8441e80c420300898814044140f55107a0154a99031240c0b40c2d50812203860195105402d10070301d1040c840d2f921003048800758100c050911100450040803548211001ea81051007004000010f85440800c0c18561b4001c1e2000601c0e070100240360980b418199000b10b01e95 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 161237329 1250 161236079 161236087
    0x70807030807141e070510060905010512071e030f0b040c0b04031e02030c030f0601030b06010f080c0d1103010b030f091b13061a0c0706050a2c03010606030b0f0402 72
    0x1c14003102141d206040d4207841600c0c4605a5078070422174403440c440100303113009011a6124200706038224100f5a0b400510178083d680e00e880c1405102c9030b52941c02d1a95038808041009070148801400300000315403411805039a40380d46500381c01c01c2840034101c0f2540d000300104001e01818811601c0644180d0084c90320300791031a220115005400c1d400150401d00d461000f00856808101c404115600501650507804100201c140c46500c00d110650b540c4070f001e00014036562040394110705080b041c0d10703200c0490300c80c040c2d1403006e03802c4049107150700d59440d5050300c10410214040c40c02031842c40c0c103c50b40e0b460550f0b0304808112024105042c280d01c807001d5881304c5c003104584440350000566580030050350101c1500003425030303079011a04041a0050601440003010014841e11844008403a540c0d03681d0b280c104c905200b180401c200103072150070041c50043c900c1c48141c0051485239a9200581c1c07120000070700b103c02c0d41d40618046070780c0b002d03072084500740035101c0704540c02c0845e421070030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 161238579 1250 161237329 161237357
    0x619030608033105091302010306080c1f050403080304110112060608060f040f09050c0910030c060e03030c01060620010501030c12080408060405010209010806120a1502040902070807030807 83
    0xd1681c0740c2d406000c002000c02c5000c42886210b0f1420002c2030001c100380700d0750030021045240c82d0141001a4000790900402041c0070400252000050101404c900e111a1828800c4e260020440c000e10003041f80422000000c038000c00e0107180100d00a01c1c0c200c1d00c01e06508005407504890390207142c816424820104010750b082032429a01030350030b41740c42008062580004008108013480400258903140b042002c0c408001020402c1e00ba083c1c403440000c0c0c441d50071150100e400c03880b0051880d14603100038090305115115a8400d614041d007264208892070880c5801c1d0351264010b100041c0d01c054091084207400311380f00c4510744c0200020001541035480703580054202e806400401d84001c418602013045031000c440082c0380c1c1078207490103070034207180c8035020390310060301c030741c00900504042421403412841201140341e0740b40041c8030f402c0140d514254044c00e14580d010f11a1b60034032001802000b2400100365580c41860340c29510007080c54045c000c924050080c8003000340030000100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 161239829 1250 161238579 161238607
    0x6020f0706050c0f160303270303050d0b0402070506060f06040305060f0c04120b01051e030619020412080918090601090e0a060903050c010501171b030c061903060803 73
    0xc1660050300e0800d54890b0320381d66981c0b8101d1440c00742115031281140d2440220a40c180600683c2d100b580c1d4417083d0a0015249903400c0110004034107107060402d400c00010303008400802614000ea100410b4101c9a100010b04030303002048103480340d4000008101003443d2000420201c2d0780201d80e19402c040c04c2d620b43c1070b542d4200510700c01980401c0c81c0482c15980100083e20000e0628002c0d482600340540b031700f000484020f204582c0106134000d072150030680d9107007a840c050300001e4002c0941d643c8180348500020800003114035815801c1201141e01c500d080c12038840706005200e41c0750398004441c184071b12035100c02490800c0280302c0060043c40f0f6800301c0d0203411589542e60101d030080ba81d1096074180081100010a05460311141000309604440a80011a401c40c0200142d80c0d079400075042803141102c441101d0b80005a0150000344200a0406c070780380c011b011190261072800100e80b1070351100d030b2141040300b499034481607940d41c5800b40c40068184013000d903091180380e0f10300780 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 161241079 1250 161239829 161239843
    0x3041a090d0c050c06070503040806010911030a23010906030308090105060d080a0324030516080c060f040503060702060f01060207150302180306070923060f0a0507050307120906020f 80
    0x40400842c18560030a0040810030992103801c020682941c1c1c0e0f42030b10b00f50b641da5116114009590140d0000011000e01074400c0140d03603809405898a5030740c0d00f15000e03009260030078240301c000c001d1002010038009440c03c098040d0039900400600107055003406019104000c0c26509941c2c182801c11555407690840c503480246d0040c00580c03a2a1003030803d4001e048000c2c2c14620016202d207945600c203d80b1080d0400b100d000b80280c0d151600065105808500e8a0040c07410b40d920980d40e485442c10440020a001307038103200310314203143d00e400000e420000280d50b6000146c0c008030a01c20101c06080b540c0f4011700442c002031862620f40220300c3c005c584808443c0c01456800718400c02c040e4581921400c102c000142550f1107442c04010181c0780c41c9650148100c1c0c91401e981c40300161890040c080a81c00b001810035040c024010112032595001c0c2442c00b040150512000f4000303241040a03014480c0704480c04c0300495004000241084840d500070003c42d488000c044001302c1c0040341032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 161242329 1250 161241079 161241103
    0x71101031d01020a0207210f0201110607030b09010b031e0a02040503070e181506061312050a05010e01200a0e0d0606032607020d02040e030a030e0f01050610031a060f03041a09 77
    0x410461080c9000589a2f6402c810800d55540203c80c10440400d526502c00b41454104689000280e41c07140380580d440d00049501000d001904c0d030b03008581c41c809000c00b81d1300960b600340141ca469120b0b0086414200f043d840b9415a000c20380901841903129413022701e01d01c440c000142003180340c06e2184140d40c003016004c1e5010701400a014402810b401550801500d00300240c810b8840701d07450540d96640002d00c017500d00e940313004070b50100070f5810f0180500680c1c007100c0316980c494841744200075a5000b105048d040c024888054299610b8288850072058054000050100e00c0d608064441040c0c500b841d50f144c1c00c0200288804a25080603180096010f6824140211052011600070310000805207610702c004101e0f8488168546c200782d11000c0518103880f50040040081d900b039400c1516140d80c80040c08007250301c0309219031b1040c9a840c15440c0c504038170400c42c602050655000007120a40720038000100018000c2c42c5c803600203120703140c90742031000d41f900c0e170069a140c003500c001c9 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 161243579 1250 161242329 161242343
    0x90d03080406060b1207201506210304090e0105040201120e071716140306010308033c100e150315070306030b0c030903071101031d01020a020721 64
    0x204082c00200d5000c207001c1e1104500f460b90780d001036442a50380e07144c1191074100103510a280480300c020882000840c00b60100c0c02000b905140c6030204600440052500e60490311900b5500044810343c40300403100001030000d541c2d101c0c10054128103581480081d122241e041c0010301c00140d074000301484806243e10702c0042c9030b8104a40b0130f418100240e200d24446070000059941d07141000c220600c00c2301a00c031b071800410b503603404d5207181c02d030b2038240543e03068200c8001000880c04880c01594030014142c440c1c00100f44400002e40414829440c6d8442011003542da154505c040c201134603004458ce50258407468501040d0240042c4020318945101050401c038010b151020082c024040000506002080c0f4040340001c000f0100e500c400d03036910810340c001c0b5103000070b000110390080c564800503614042d000d84034600003000e43c01082e810150b03241d00d0480000000000014442c80c003200142ea505e4900c40000c0c60018030741c0002424100d8255940401141ca202880303140b540b2101e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 161244829 1250 161243579 161243581
    0x1401050f04090203060a0203071101110901030903090e04120311131701090f060504020301140705070618050d080f070302090102030412111309031b03020d081f08100e0102090d0308 79
    0x1c5000750114602c000d4141c41188203100407404185c01441c400d24569a030743c0c04103e036922820f03080c2d40e4a01400c1040400402c41e10300c15510036042094210b0203801d00641441c0c1d0740c0c0109660f00006c90301542c10240b40181d0b00d04035945402800c000c0b035901406030307040282c0c960311650101040e104025640c40540d026910300c8138290003455956410103000c60b500d40c1c441c03e00c2c002419044500328480c0d4a05140413030341a41032074429002e00411360f565414000103558507030003800305030f80302c1e549004200d1200c0c00003030082242c180d0308001603540064a00b000c80e03c0c0100f64270090107260606005000504259a0010544089440481c0d0318102c20b43c6038200308030704a4119421640081c112411105001042d8000c0700000340310765600541d4582c01d280010149082e55030040040e000041140d0040d403151051035042208442508100c0010f540d10b0820301c600c540c171001040c0c0003034030b00c81c101410300c0c4107060580d01030600a40c03070910700000042c0001c0703004100405202204c4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 161246079 1250 161244829 161244859
    0x9010807080405010f020408010509010c0f211b0e03011a0105270306010f030309050108101e0b0a090905060604050d240f0209040f0b0307061d09130b070201140105 72
    0x500846405d0246101c210b58440c1c41c0d40d5414060081120b0446156080a500c0200a48907500222020b1150303a10301003440d2901e140e480c01070011452a01c81c40f519120402c07110103000d26030740c807410041e403242d004001002e4281801c2d11042010701e203145264013810445660801d00b00c56240420403412003000305807a003042d9081200810041c0c151241400100300d180e03a034219101074a000c0e071210140c89a540004507600c2c5001c171244000b1541220301082040ca094400031070440c10072a034030791100d80742d0401c1d81c2c00c0d80000ba0140300080c0583c2d401c02c00c00f040f52081c42e410200c15100d561400c0d0400010130b224509132000141080b000305540004240a102948130a01c003843c03040c4500c06c9510038280c069001014414030440c50030030510031060a0340300e10b0010a038003070040d0000902d07054007030300c141c14411507182c2d80d0250780340d14010307950750b5030740d02441951a611482c4100e100c80c00d020340d01e80c100600000c1507a150a071903000041446103214110f900440f800d80076112a2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 161247329 1250 161246079 161246081
    0x80615030a060c0203090a0e010b040b07060b040f0b0a1d1f0e01060504092409021c02040906030302010b15040323010905010c020d02010b0a0504050703060803030a0603170901080708040501 83
    0x1801d070203040c0c180340c5082004015030101c01451500303001c071180b4142945400401c1c041c0e035001e105840c2001030400c42007040350600300142150074014140000d0502d040b00100701a51030214019502c195994a40e00c1a4a4100c0c04240500404090140340c0d4100701308a960700c070b402501c07800ca1040014190b0880040c00c400880190005451014107942d542002a115820900400131000d04041c2c1910280043c40601d000809010b004003000c00c0c6010344640c000c0d848a0707003900314010192003040200125000502c01040a20000107020b45181002400c40b8524142244208607458412030300003078107001d42d419070781c00c00d00c6008481a10f00707034181951544070303680302030b0b5003440b01c100140001913110480b03003043d94003a5444034806842c00c034226404504000e6000000840600c1a070820350701443d4400034030b0800203a01c90300d41c22400d1035a00200c030894141511000309004010800d403036404902031a05c2560705001e81c01c0d0000e45000c800409140400c26003070002002e015007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 161248579 1250 161247329 161247343
    0x1c030e011107110301110c010e060a110304020108070e03010914010b040501030c03110105090907020a11030303010b0a080a093e060904020309100204060e031c090506072d1b08061503 80
    0x200c10030359981f80e130308000150103000f000301d03100c3c1503004040000300c1d40112401802102c480107082a851560385500540c1d0980001e480d00c001c2002030b0040070081e403000d00c14002d0140c05800991391031031400c1e20f01c40c00d4a441d030358024047e500300790041000a40301241c00081d40d5103c2e40b070080c124828001256103010703e54166500540032810300c4541500460520600c0b0702074802400e908143e00240b42c1d0703a100030b105140e501c0b5002c1043c040664402c00c000c84d0090107031080441d82c0269034079442070000540060346014601e000021401640e003542580044601e01542d02d0320001410004280d030280c0300710b0901a079000000210750641c24000102c1d03c3c5031941c011034950362117001c018007000c90200b00038081c4c85101e0f901e2050328013803400c00341c4070781d244c0c3d4400d064117050605000049d00043d2049511031280440a6804021400f40d0441d400700313020700c00300c0a21141441d19a07119005c0000c510459580c00521650704e02284566000c58000003c0703c01c0b4042001092030201 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 161249829 1250 161248579 161248601
    0xd0c0305090904030c1a04080d0f0e070b040e0f0c040b071a0a0c020f190618060e0319030b032505030604080306010e01320c1c030e011107110301 64
    0x42c1c0d4001c001c2055004000c0704901800390210350509901c10407000070000080e240175000341428407003194445a00c0d04040786881d240a40400d040e200d81007058508041500203061352880800d00317010889510380d0f80c990060007901c4040c0c0c0c60804910310034491189000e4110005000500d200a00407401c410f400740a642085400540c070301807031024002c0189105003030060249001030022010b0001e0b044502c003060b4190380481004682c4c49200800c2e004012070925022103c9410104207148248074284036aa0091941c92914918408070360303010422000c149841d042c55003605450010b10300e450104e00c2807806d0b4892507802000d0b0050000c40d0311140d0303d440b415081004000800d030255000310020780b140d400e01443d050040d2043c9404d2482102d401d401c4980201541d400c400100e2442d0000c512a01c0c50092401d0429040c04422078405024215040c1c03004c1c091070b498440c01200c506400000c2100c2d407200408140c5511803003c010308070352a401c1d01c4d07079404d81d003c0d8010703d280c0f5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 161251079 1250 161249829 161249839
    0x70305042c060f090610030b030a0c03060b0604060c03081f03030e040b0d0f330b10030203071b11090106120e010c0c06020a020106030c140901090b030d0c030509 71
    0x1840402401900030800c10140c8984120710003080183c18081402c0d440714000030600b5005540c0c9900740f00d81603508018030000c150b01c41c0c5d412402ca86050085001090242110025070780c00d5090400940784008400e07805150b080000300710150b840300d29040c4c02d50340b519096006846104e00703000314011440b03008a0b800501c00c2d00004264100a110b2251042034030103001e000040707070400912052845019203d40c114290500c0000c0f01c100d0740c1580414003640b030b2401a080c0a10000000f400c891134140381d180d82d03a0b00742d81c2510307010340c19010403400791906528514016500622001d00c0d9440803642c1e0201000030b908008a4000341c070428400540301006541c0e40e2280100740440d04c0b8062100d00f840c0a00c40c020011040c00b0b9a1011541a1103401d941c01c0e82d84d071264000d50000b04070204555a42d007010000640350700d91503000b4050b00e070100e848050300104210740c00c00180d120401c82845c00f003590b21640c902180140e400c418500700003000307800e5818191940d01c68992040d0b401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 161252329 1250 161251079 161251109
    0x30507030309240f060501050703050a0324060305090109021318020d0303150b04080a030f051204060606020c0405010f0605090a1d04030f030e0604060f0e030f07020424050607030504 80
    0x103c5101550041080320703480c1801007820f25107950040700d4203805070500143d000c000381004070340144010b25100c206403400241040c2683c8010808001d403d01280c0f07480e0709211708001940d8180292a040b01040e0700810040311142d00261007002044000e201d03440c0c80e0300716892341c2c801c00e040d04c1d01d0181c5c020749201c400d20303e10700e40180140a00f91076120030560034200072a00c50f50b84001d503025561250000c000581c5243c4060310038001c40003030842001410000986014203112440b40601d214803000318a040c02c0600107400c11119403c0c89001e24a0080104810411010204100d0b011410499038070081c14022509030a0190000842100b4131441d0b00c03aa8151810b17120b00c10703402a80d0305117409640400481c10b8601a0542c560103520800c04100880d1040d03200000d82c104407100014014182d81415065401118000c6c03c0c600e07000c6114030660515004e40041004150809418134500141c0c4007103000260250310300611000c5a031204160064040364013500680c0e92050007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 161253579 1250 161252329 161252363
    0x10612060b010206070c03050a1d0d0606050306060d0c03020d0204020f03010608100906141002160803130504020418050a02090a3312020d0204091103010f0509040807030507030309 79
    0x1801d0750781070090042c82a2000590b840344900030354400582e05545807464014420412601501204d4243d103c04401c040013400d00e5a0f80c9182c120480d120f00d1003c9051450300c81094100800208654095080c900d090000681400000e9040c0e9a0445005c00080030710f00101380240102c22560104040010000c90b07030940111800c2e00c1410000d05515503241c443c803030320080c0c03035480c460060a0070f40e12042d11f243d4078003601c003001502c2c5688102c8460858842d10007030349101d40d0b03020241380d80000544e582c84644428800b0064003060360b06502d454074048862856503003000030540400ea50f20041a51302003940c04a40c00c215009041ea0311180d21a0142c24400280100c0700043d00184094950248020502452418159200d2104502150140b40041c3d8404414560f8840d401c2101181484485c440c0e0b801c804030000a85441c0c1d81080c0c0100150705040e00201d2040040000b0400000c081c1e0003124812941890102e482c0c007400c0c0342c107a0240a00740340081544441901c4082 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 161254829 1250 161253579 161253581
    0x170f070903290f0405010605150703110c030106090c09050a030f02060a0e0307060302030a0506040531080d0519110301050607050a1505090d0c080f032203020d090603020a1e0201061206 81
    0x1c003845c0034030000c0124945c0d4a04001200c104200c4007410f0303510901011307020a02a880940307a0800d072030f00340c401c01c41141d0006402c5a8041d001a484166210f01340c2011546c45120300e40a0f05054820b10822803d54607410f60112061000900c22000042e03080c034031606c141440d80c202c4002408461105469035000360280d042124004800703480c00000464038501030040074040c008101c22500304121441082d08140040030320f4070300c0c00d01c51100100000e005400200f00c9162600c400060700e0400701c030744a00600001c01e448100350305005c55121f040704400c013120304540048403015541c020a141035030508400e904040c1020b00c04038a1b050b45c5800c2900000d00c6200b500c0f007a20020300180d40e09a801084000000e0030204e0f0502c4070b1000c2d00015001540c21100c04141c030301d14803051a8642c1c03c07030342902e502140160401e182e41a150f542020000020b81800e04055040c5400e9550007000b05800d28810321094510914650000f4004e40c040c50181249005941e04140070341001f01c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 161256079 1250 161254829 161254831
    0xb031801060f14010804110907030e1507080108060103080f2802100f0608330403020a030f0806060904110c0d09030203070e0f040609020f06040303170f070903290f 72
    0xf40d07150004a8051150300c00d044c040d10569001c03662201c403d0a82051040b00c0d4801401c3c2030a05564030104414a40200601d0711a002ea0688103015450000c0004121400603840b0048562144005200040f00c1c40141c98100510012440d00c3d41c080050f803010b945400c8034407040f440030ba023030b07502e00e100d9021415007541800b050781805400c003405002011242c0354821100c40b0f410070441e01c50b889403481034005108105030080e603003445040b000c85900c000b060b503045001da40420030032420103030082010300f001c04041c146017100b860840041743d101d1080d041e81078400c0f5543c00e80e0440000307001041d0345015103890b084540030002c1c64005405502c8500041e0712901c00c460000600a488003c406d20500e148004808152155a9a040541000703602243d01440b440d241e841e0540b26600908001c0d4009da0301e0b21090701e0582c44400381c8400141040761041030364410059402d0b0040c11100480354884140040003a03205840300d144841d02006891100c006070034000310740d048282071 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 161257329 1250 161256079 161256089
    0x70204060312021c0c03200706050a1e080408070615080705031204140105070c03080f0306120d080c070c09020a0201090b09011503020f011709100b0102030c070b031801060f 76
    0x1240010b0307801132213402c10140161040001406491042e000074032409071a0900c5013110456074541607160704203410a491900588006103001c9044910540c1c4810340415043c04401d00458066a00e2030080581c2c400810103045c04000013910010094281e05c40f80485960480007440aa00e400c46591215501d20402e03120b4424880200004c010395070072039041300d4280d281881c2440c0b4107001590a500410b030305440191800c0400800320b501013008000540d0390426040e40d80c45e00380c1c200b101052008104803261780c00111801c04464014507190340203030000c11a203840d12041d2500106044286e004460f955002003038034103819805400450000b881501c1c042041c0c1c0d00c641c4550700301c03401c4640450405903000c008202504059242201482041c90301003448039200f0341004064106071b807008801d61000250300c81120017842061408842440954900403800180950714540ca0013007005244002003c202c80d410a0b00b00801100741120082c0039041d40c1d41c1c40304810508134425 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 161258579 1250 161257329 161257333
    0x60a09021215090c1e01030b120a0305040512010507020d030203150301140115050309060705090609030303040b1b0f030a05070207050d060903080a020708070f030e0406090605121507031107020406031202 89
    0x12411440c90000010344003d03201c050b8008017170b004080114040c04040113401c1d00300460510303183c1c42030401d010852015000c0d4071a40d50702c1c1d2030002032044072100c5003403c0700664908024403081a6000c00c43d02e03082c110b1840c0c056140e85980c42295425160080b010303905628011132651026110000a412900c4051401000801d1030000790f56610046440c01c0c0301742c001900244070346015401500c180b1f14040c2099050041c0c860100785103500564054900d115440100094060b0401c00711505010715103030a0700b08240042c400742c10b4000940b030400c41c61f480d0000680302078404c00940d401050000c0541da090000d5042500c01407071a02c0059000a00030750004a00d18018021151810f50084005180c88050f440d824107612200b28214100007803000c913040e01c3d40d52800340310060802032000140c040c3c40d100400000c814082c01204094200d01100c0201e000e062805550089403820007141258400300010214492260000c0d4400e20340f51000c0103110569802a40402c4180c003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 161259829 1250 161258579 161258593
    0xa020615060a08010608040f121107060f020a0305030a0b0603340905042318010e060709030f05010902101d0a081209041b03020705120c060a0902121509 67
    0x2080c08040d102d0040700302c2c0810424001000481d200e910140c0e80240140c43c42444480345a031940006400c480c3d15100003442c01b442c424a03d1418400e02c401002e0908041422a00300384020b522010703602009024002c02100260000c049074001d0040060300520790341d541c0c90300d9001031286c0941b1805618111601443c0c442c52131104400e02c1d08141e0036500d0703415805181c1402c0002600c5007111a0306c1004a012491030010140245580a000b05650b200001440e04c0e81c0103003107c0300b604034160280e02001c10b01003002d80100500040d6500000f0365903030300d50310b41805405072800240017900406003450702c07001e0301e6100144c0c2400c20b1480d4171520860780f2400801110025a015075032450700803c0e01000b840e0460341c014428030101900102e091452507092010240908955001280d00012103404124080c4080e04202c80c90b812000d05007403030b20b91410341e00c140050405a00b00ea8031802d00d41503550b070f090172420f00f03020582290500c1c2d448040c020001b0342e0540e014921803041c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 161261079 1250 161259829 161259871
    0x30a0b0a0b0609030a05071e0311060309010219021e0313090c091a070c09050402031510030b0c0301030b010510170703060308073005071e050307060c0f0e0d02040c0e060a0206 77
    0x2001e800122134214110100102b610000c0113016407001c0c0002c1070a40d400c2018089441460031452503006a82e0042c1031071880c41c0722400f4481040d180d21030320a0704100022030b4003076240482e0f0810741c0c5a462001810025021090b1503446681c0c03c0200c080c03220b4001000078048034401001c000b0700c034100c048041039941c0306803030a5800c103440080d0305800880c62070003095001351490b82e2000711607403a040000c0d600d4135141c4d1400c00903a40520810320010040c401d109a42e0382c124010b010a450422070328040c800d00400c190381070b911161000002c44085080b8038420340100c005141c00c00b0050340d40f0b00f00d518050b00000e80148085130a9445054501d003030741104902d560b0011700310303114203242001360b03540e10b403070800c4d40746160952240b0700941c0d5012034410400380040ca44205400900122410400b518003011171140c24200442c00e140750b112a1100c04806502079030694011480302c0b40d10f030090b07c10000c0c41741c2c0c50340c2045001c10f200502c15070001e000c4e40039881b001d0100704004d00c08 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 161262329 1250 161261079 161261129
    0x10b0703021203130b101205012901050417150a090201030501050f060d05090312090a110609011d03010e01020f0702130212060607300806030a0b0a0b0609030a0507 72
    0x403114030110807041411130001c911040c2030300b68045200e401592070f1544a01c1004140030707500d1401d8403140e40d40d60881440c403140701d01140c0c401c140840b0b90401400c42c280000c0c014440d038060824915101c0c9005d070303038204080150b01c03884041c00240b80328919060719400010601c6900c142d0000f0b0819000003624185001e02d401905409400f05103810310100100b8040e28003d01640010b12080088481c0c8a000340100b074080d911000c0a40308401090918120710540100c406118040802400b0800ea801406440854402007016082c000c1d540b07000a00401c2081000c035025400051400039029410b8010140e162007110414416502d40320150220301901c01036100c0200b480022803214900740b0040c0100d14030a81d1258603176100b410441c035442040b955a02c0055404585060b243c2d0342003107449621407410380040468800395180c601a25901415034602030f5651824180316460700d800b10b414a035000b604503107245140345888c40e6203c085201da400324140100c802d00c021880 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 161263579 1250 161262329 161262331
    0x8101a1c05073f0c09081e0d050306060901030903031b0203190504030f1e06090602090108060402130501031e0203010b0c120a05030a050601050706050a052d040f0c0806010b0703021203 81
    0xc008021043c05204608000100801c1540909110003105c000450708801c1001e240d074440c51a100d11011148a5140c6191510031a0042c050103410b1041100d0780d11448140d4210090900e80824407801c1410150000c061075508001d0004610f0f161007455500000184091030702040302180080d04894100c03074134002d0b40002070109140e80d241c100421135180344120400c0d0122140d00d0850460b80d00c0b0412620100422180d454002c1848001076030080c40d6160711000c107036425487c008041032207903c2140b0b180549030500d43d80b190324081e03c0f1401501418640c2000e10215030b00d50f1200c1d000c80a40e0003014100c02180311b0580c14102482e540001d661804a04da1102800d64459444a03005440c000301924100401400200013080c820b001c0c0c1070154940c1d0300e0024243c107100c0009801003007180b0303403119440b1008504001200c00c040050b548243c1000610250781c04520300000c0560240d80b0400032441654004640702010b08024000c0611075000c458420462410b0324800d404 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 161264829 1250 161263579 161263667
    0x102010908040302040e2505011d010e090a180302070e01080703030801030b09030715050f0105040b0a09052e1509060806010503041401021908101a1c0507 68
    0x340c00c0c0b104000604041e00420704d62291076040c2c500b41d0b68141011802d09804410700d848016003d00c00700940e58102171100011565050703c50200020600060b15501d10b102080c0e024002032400100400c2d03041d401002125050107241ca010b407940d040003543c0344130303134000c80c14039940c40d8000082c00140050564101c03581901d07001c10503880d5850745000c10384020100700c0e4500040040d8000620b54540b0020380c2c50148000040c00d09080d020601c41c00c0c3c0c140c0040c3c0c003c903e440e649045d81e030354500c1c206003110b05240e40452a80d80e0b0400020821544400342c0300d86030151818803030a0b804485071102a02d20100781009080c002400842d0002454400c03607000c03c0c00940405c001d544208000c42e4014020804008018001082c40d0300b26403100300c400c00e8800341c5032080801d144d03110aa0300c1c2c0015415108004040c1082a104070b0700306400c0094485000010f4078074200090000d80085008050004112030b15080384d014184003900084194000c90032400301c00541380d9140d090240361 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 161266079 1250 161264829 161264843
    0x31b1b08161a042a05090109060905090106053a11011b030801030210021908090a06020a02030309061b030406091502060403020715120e1b0a0e270f1b01020109 70
    0x150b44400c8035200c01c01388081225429134000001c540ca4550404060003001c0c851000a5003d10340240c141c1202e8004e00424042d074180030041006580f044491000001921076802441900e4241008650f0710b000302e00c030b94050008404020310000c14040c610110080e2600f8008502e007115040c2100d4007c0c100a010800800040c800740c10306041e0004104a54012103241e404074002214a00c207130500125040e041c00240d1020505240b90751100501090005210809180d0700180c2c41c0c1c040c07001510700828010a105001c07003861164134001210030010b8a5846403101300c000d003004a18040d915945501c0ea030a0b030320203132001034920701c1150103a0141a1460401d015008a01e002c3c0c52940108803220181c1c031880d01942c403404072903001c0600140001c1080d643e200c501071824414241c850510844200500c5200703400c0107501122011000020700d4000c0c02e2880c04040005001c40d1030300c1602c00344901d001d40040d40180f103e05c2c030911400c50000c1600124269030300101d00174500 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 161267329 1250 161266079 161266103
    0x20408070f0f1e0305010513030914030a08130b0a020f24061003150f08070801050103080322080d090201140901020316060b030f0a0b0106031b1b08161a04 68
    0x30802101c183c83c1040004041480300c0344d56038030740c2821340344140d4007030100c0051303030030b1030302c101500b052640300284080030b0358003103c100c00720010380c84011904001c1c100307540000364404074166425090001c0c00c1c0340340405071203241843e0000e5480545007403425861080c00e54240800a1300481da0000601104d0f401203295202c0080c4172000d12040e00203024182c90302840403040c46a4500000940a500f004101482c030380010a0f203400c03203950080440c0d034074000c0103001143e10724044035071001d001440980d014040101e60181441c43d484060540d0030301046006180c0c0e0030b41c2090700b895000342d80d4025140c82e20300c52040c03144500700c442c50240c1d00800000702a0b804041e0590742080c09040005005009840440e0828803842039150103508001905820070190b074078101c4c0503100342d280420407011900070503c21081d00c1003441c41480440b82c1480030000ea9144c0e20071403d58080d00003500e624400e40704440c6a00b2a03401110340700c1d443c404a02d02c200b40841641d00c00d80c1c10402030032507 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 161268579 1250 161267329 161267339
    0xa0c120c090626010b040204120203190c0302010c0c0509070509040c030b01050a1407020603040303050415060f0323011416020604050c1504030b070c02100e0904081813020408070f0f 80
    0x1101a040542c10541d500e591840d1000c6c6c0e01d52014100410009020310706508092042604100160109400f0710002c682101d001c9402c3d0000780003034903420300307102d80004d50718101001440750b00e40c800e5900100c281c0400c0440b9034460042d200c0104d0658003484101d54002043d41035403402c9200d00e0002c0d900303008220344648034800310100000c2840119180000a8000c03170280d500c229401e0707001c40c0e02c0700c0c24401003102000d000b4000305e40f00b601c01c008660801d00a07100003421884058110310820701c01c009445003050b55a4400400712008218400c082c0c0f090b8020740404480007900345003c0035122072075900204651348156880400352045410b100c041100d166002052009003a005200110014540041c10703400b80c2643d4540c801f01c1c00c4240f0410021361001c102110802411543d10b41c9507442c0c1e0300e031080c0c11540c00b184868460042d040603c0c501d142c81c0c02540e83c0990612040b10a26105600510507265500182c0b0002a212104000240c01ca4440d04040c0b401c40c86040013 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 161269829 1250 161268579 161268629
    0x206070f030b0d0b07080609100501050d0b060316080703020c030418090b01030615091103061e040c05030f1506041e0f090e07060801080a080c0a0c120c0906 69
    0x1040d80900700091024010004200d5a03110b40307100703c500034031480038040c01c5e94016048aa004804480030800ca00c4c18a2020300440240c7c41040c0c14810085012040300b0155088064082000340407984c90b0301d80804808200504408140f0100d003445002c00c0c03c0c0b510a008491a01400c0d40003985040e19069901483c20300c0c000c9601a03859403603241c2000143c80c50a21402940240342c08201d42c81000c1000405440951103154450328281c0c4004c0428500b030152a4440700858500071481600810078951080c89200d99503c6031500e0060700440390014003442c054040b40c0c54018044d5900c620700c460b0000e10401640d071142051000b0014500202c050141d2441009800c10940d0750300e038520800140f00703400c440540e54864840750301c003130300400c0260028440d62a0840362035140a603440c4c0c84221909024000c80000104020102c108000301100260f0218141208541d03851049403090783d4210125034a032909400010311005500400c0140c07001201001504a03900003242 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 161271079 1250 161269829 161269847
    0x7060c0311092b120207061b0f0c0801050a2004032d06020d1a150d2406080910050403080726040c0906090603081b0304030501180c1203020607 63
    0x210840f424803d1400c80c1c500309000f018881d01c1e40020118901c44041c0c01d04400e0340000013040401102414602d540401d2255466000324180c10034a503141802c03818090160800f240a6090905010b81b184407a1b0042601030403104420341d0751210041e200038103101c3d034400a401c0c8078080d80200000345200100701202c0d0540c400f400d8070403085940c2c581c2640c10001d2042100c03a56450000b0344082c50b05a070a4440c0c00440307040108401c0714600c00040d0241240c440c8003140c2d101c144106443d9030603803844045c603504074082d9011b5034500c001170224104681c1c0290314003e07407200c00200c020501030740d401583c0c161105c55440d600e12004a03031145100c060b020271140242481000300c044200d1090095005d40341c0d90920500b4044604151120359110788007042c94040c0401c0491514016540d07a01e00103120590901d0080d64900d02e0360140d500003800175440c21801020051820f481001201e11400d059051325a0354100c4155030000c00c8130140158100c00001400756109880711 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 161272329 1250 161271079 161271109
    0x203130e1e060105070501050109091403031e0a02090d0f061103070903030e0105210406110405090c13030c0e060a060f08042d030327030914210307060c031109 70
    0xc45c00c3c52501d17110a07094400a0380051642c43e5034030311800034400c8244600303041e00c02d05001941395040c0426400203103509182c0304214072902c0400710b28074003411f130115414503070000e0a21110f81200d0424002d01220244104d4081d80b400a01d10000d40030b0320240e0744a000c894443d0741c1003178a10b0f1015215003e0142d01141001030400900b070511001d1035800745258100314100c50146000e2078600c0458203c40c1d60403c40d454244000c2103540e0b1030304401a480030008051941707920250400c64440041c6410040c0a401c5900c4042958495154201d00c03ca004540c41c952080d501c0704142c5244c802d5241e02c0c00010300020002d004502c0013810b420b41216080300703c1c0178a80303000880410707103e0920300480000c2e84442115009800628010081100d403158410342c60050b6500a81030368401c0c0f141503184000c000240485503280485209c0d489001c04103090718000345445140c41c3d03400b030501155590318000044107100c0c03181c441c1407600702c50080024a086003407410401c0032115200c3c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 161273579 1250 161272329 161272337
    0xd0f0c02010c060c030c0f1b0f02240c210405040b0f030f031206040506030307170421030f0c0b0a020c0c10050406020d0e0612090c0406060203130e1e0601 68
    0x702c00004840d4824080e82030700980c0d001810f8261400020440c01440c000e007800c0005101010070000c0c0a4a400d11401c0e0b800100c1003018595840402c94107031401c2002060390098030030404000d44044011714000d4020f10075103001c2241c41085013541800751484660110f0107000900007410994400640c41800174451445955107500007490700790881079605040d040803c1c0c1640d1021a068415002401214148083e19185001c40d40d0390182c07400281150101a18100d1404041c038125000b03000102030790090b00559500000d00f0158040d0224005262800401110751182090301c01c91907011303400100907107616026102a400c0020440c6141c01103414a01c203d90350100400705100d007035192603131154a00074010b03040c1a1400300d0002442104844c0307403074603600e010864913228400c070000c0e469501c1740150035141c44420f140f038940080c9400d001044450300080030702842d01241104541c902e80300d10303500108801c1584c110010040041811030030701000340d0b059034000300602d0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 161274829 1250 161273579 161273597
    0x70f060606031e0506030303040308040807050715120513021908030d0906051e0609070c0b190f06180e03090612040507051008070f020f0106090b040506030d0f0c0201 73
    0x122802252035940c000004a56a510915003503101c90504602c0c00c800b0700d01c100600d161020100351207100040c80103081040c1003000078108401c480545030855004411200b05070749810510301889585e14074440400c024400c40708100c1c3c07080c058140324155a039001c0160443c40c1d801e024070045a80019907009000305004120218104050040e08500e094081107062075810000204d681c0035003801084481d5000041c0c205d16802b440341d070409420b90300c10394544d0b9500c1040b41e035821440401048400140284040c600ca00032100540080b409810003240c40020605021030740c0901c036610003c0441c20343c5058200c51036021032720b007140071400d4915064110000030b0f000e6000c0d80c1c072072550480000510003441810004d400c0030b46420344692620203e0aa8041c1c0380071801801c010401c80034151040d412031090098040d00144400203001c29500e4205403005015070180041c029450071000400b540b4000500a180d0352681d154400005801807085441c0005c1d01400e0b81440100e031 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 161276079 1250 161274829 161274833
    0x3050a020f031c09140102030a0c080702060d02071208150a05040905030405060f04090b0402030f04080304051f0911060405010903031116030c060f0c080409020c0a080a0f17040302060c070f 83
    0xc00d501c946120550f136001212801c055190162044034440b0034115442400010b0381c940d04404400607151704a00c055885074031520000300769204d50b0320054451400401d0100c10014451840d04041000d03486040b25541d500c03003020070894101503102c2d4000305001d01005241070940c00603050500031819a485d040d101c402107041d5a000c8044021008400541000000100d10038024091001c0380c0070341c030314109004001220b103809007014054060000201d81007000800503804036014194052141160020090005020714541550381020243c05c08907149804000c80301640c03c161100882c40742140c80403585000d01b20102c0290b03100303001c1c1f51a40b400815182e000194404d074201042c081c18100d0040034060f4400d000da0030b00450820080002e64580c0c00d40f0180c0b0400c0d280161240200b00003203103044010325028004a800142c0d100801754040c001c241920065101c8400704440b0f0039060101241c1140d000d001a007001011501d2421000020701c031250003a0b1151940032265 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 161277329 1250 161276079 161276113
    0x1c150b030a0203060c12010b130303120f050127020403020d061d0f01020d0e010902030c01050306060d15080705030f0303040f0804031a090f0a0c030803041410050405100603050a020f03 81
    0x155094217029801050071813606031601d0425005d086002d6495003844c00901500000c045a8000102401629080340304001c200d5881100d03055140c501c103110650355520341940310640e110a8550403e641025852040c086008a03001c40c1d9000c0c0c000d10003019980c840a0007400740440c04408901071000005810604000e003240e503200034000180d86808095403182251414121000c043e4104882e0300056a00440ca03110408000c0c00d04030f0381c965440700056150301c00c03092850406860070802d1402c40c115100030f5002e4501440071500030b03c0d100c208055589941d00315003121940b0400c000b500140d181445075480c036124000302d034100380e141d6449414480b81e0408000d80f1070795800801c50318180800404050240d80d10141c1a010410b031108044407643e40005000400c1c004041020480304000411100782c5000584064030b154160b1744006c1c1605030341c00d4556102d040403203a065a40d40c8a494200d0354400020310b84030360b1940c00d2020380b107808003810f0350501682041c94840232107 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 161278579 1250 161277329 161277331
    0x605090a0507030b06090a090201270b07050106030605071403010915120b0603060f10170c040204031406060618100c02030118050708030703090b0f0c0312061c150b030a020306 77
    0x481c00004400b40390180c288095207000400c8000d102e800c5c00105005030342c009070400034800d000348000041400c0030000420782d03803060b40031331300c42074001070b11070144541907010b40d050324406d410a0000342c942003070031200c0700850030030214100010401040540150f611655803c0040d9655110712940c40800c1498060141700c140c4040f01c001d81000818502804600d40c4842e84a00601540c200f000400003c210344e80205042840083c9081d026028100130f003801c40c1d00003d20541d56143c40f441c01e00d41040f815024030016204050104100d40b6000f81039415002107140e520000048030fa0811400300281d40700725081c4940540d00c480540c50038040e208c6d02c0d810001604488590b940303000f03072402d0f1481d80400c07960b820a00104002a0348000d00c8811504940403035034607400d154088480710300c1920315046282c4400281030241440c1d4001c1c4602c210421905014281c1c800c244482800e11103082c020801910f000014601026030b500c425803007030000c1c04882c200102c0d5804285030100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 161279829 1250 161278579 161278583
    0x601060c0326090d0f1b0501200c160819110414071407082a0d020d030c030e0a021e041401080f030705060606031b1602040c020a0c030605090a050703 66
    0x4055010094030403420000d12113825858a02032101d84d01c1d040b0000c0100318202a11540701401c003a00e4000e01100350032070b81da03000c10038400e113403140c01c1d034502d00301245d003c1c40300c00383d4601811341d0541881c01d00041803002c2f116410060041c0c3d1300407204102000c00008000c407403480d00070700460181d131218402c000c2c46031b2144003000c1c8541080500274219045448211462090030404080028204005d880a80b0910b030301d140c0c110368070081e8411a078034407548407020f181700f80d40400c1e4002d540010745004000050301d01300030001c0b961400300d050705d03505d03000c8080c50b91150340014014102507a005250000e40744080f9240c46030b10300010141c41842400421103200000107200e518000c0c011210a000424020b6141c65000d41e0340ca41c640740700802d141d10821021000440c1c0186a201c243c2c01110f10102d0340c0c0d910f064540307074540500203000e0700b41c1c01503103000b6403040c07203500006165440035008140c0d1244540b65603030300000f070700000308800d080d80039402c90701002032f50800c210801b940c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 161281079 1250 161279829 161279897
    0xf070c0e01090605011b08040b07060219140714010f0f021908011d0705090907020a0308010503120f0903010b03070b070b10050a1707050907020a03021c020601060c03 73
    0x1450034201400910068100152903841e048041000d81e8001103200c400407002288006904200e080902642c001c80c3d004500310640024080d04004841e4010402180b201c59100900e4044034411510303140b03d28200c4246844c2004800089207200107014516041480041545000c4004c40e1040d03506a99900c0d06041d004a81c044101c401214140801a407914204240d507262120003403840518008002d840540c802c0410b016a100340d08032501c480f03000d40210b5050405000003507a442500707070190000751105002040e540390102d0121007013130f0700e0070f65207061001c0c9034071019695000031403903a0b2540da2000c0c0c2c810a910180980c02c010410124119100c4030241011001c04600078444051500c2d01d85086c8401d650308800d01090b40c00001c188840c1d09000b0030600d00d007007600e4200306d601c4192001080b8441e43d001541100c414800e030300f9a44250444000540c4020391700d162200560131041c0180b20091040b42441c424034060324002c01c0907007080c00708122030050b801300007441c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 161282329 1250 161281079 161281103
    0xc010b060d020d1805150a06090203010e090f0f0c120705041508120f0d0c030b1f1202030103020a030308040c030b07020615060909040602030a021209010c0f020a03020715050f07 78
    0xe0f800d202e40b40c0400403a02d041c1104107410740e101501c840c18428074260a0b44101c000c07130301085003544150080c203900380045603030b96181c40400300c60039030803940d8101e40c0c451620781c0e003800140840c2111889070200014001000e0181c100b100c03190320030442d14074600c2100300c0090313742e0744c82c0a0010780381c6010b402c422400303050010705418200d4032141d81c04107020070020007840c1020780c42103030000360044000064550280608a01515100310915403040862130303040c0b0b8500d40c4819a4034202a01d84900c015078176a2032440342a4002440069400280c40d4010400300380a0101194440c3c410300c0441422030300c944d10000c101e00b0648501006921503010032031910744079042071f40704480031107806090401e110006803030a400200020030054010000c5070764009960141c0346400610080c221040c6803682d8024001c00d005600f02c1c3c0060b9081408420746400461004e80032030b0184d0203082100d040c0254021030b01d010160381d02c20070404120414280105a000d0014130740320310914240 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 161283579 1250 161282329 161282347
    0x40b01030c06080f150a0305031305010206061e040c02161409011d061e0301111201050603040b0403050304031e050901080a020408210403240e03070b04080c010b060d02 74
    0x2280741c0e070000c800b4401484140107086042101480c0c0c4405078215001d03208004c1c0380804e00c0c0707800684c40204184030105600c031400c21301e169a00301740e81c400e9007110013548c0c450041043c8031001e82001c01d410b103140602180c082c10a50080415040ca07801224610020040d8030082c0444642c8005511080341400314080d1400c24410382c01030030105030300b1000c641c901109030461307000a030001c1c1c45406006910401040c01d50394402c2035107001802009030001c4c90091107529440000015440c0f0300362000403c2c9481c0c00c4094034080d0b5044500d103031030ad540715903042d5141da0014200b40c00f84256081404102c5000440c10101c59401e681c2e40c94442018100141003954092f0840294500601c0140400c03000012045400d940c413440300c50b808003a6a0000c1801d02c580d03040a440c20100701c007110000c031140118111751400d503035000c04c441e656401d0707015142d0080d410010030010000010501144050010303140d05583d807000092000c0d240b82c00104503a10126a1030601c58012400c194 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 161284829 1250 161283579 161283593
    0x140f07230d08060a21060e03120a1b08150d0c03021207060f0c08120a150f0302030c120c122503020f04020a09080d0c0b070e010c06021b0303040b0103 66
    0x701c508820704114129041010001d081d8500d0303402400c500d14000c04100c2e40415404c00c016002c950825810014a042c4040d510746a5000600c10424481030301c01040c0c0b200f046102e19407010007040081d107134040483d20b00f01c0d00f6060207170900d00c2c1040d912000d4596655048825031000744038400a900207859881031100320400d40c44080556081540104512f5822000704403260710140b5240c11104000d20b01840729009190402e05d00c1c052250030800d85548030380c004180c403107040300440c00d070690741c02c00020510740c6400000e405801c400e41c002207500f440d801c0d00f403140c10400c042c0c0e010303008007901042e503180c1c131001c40c0c540c02c0d813002c48002e2880b5645040b000b5141c4458944038000c0703046401141c0300d180e40148650240d6400100049024405d0300314102400143d400e40d41483d0300200020134194a05000752a070440d0340c1c01240d6503600842c5920380248040e190341142400c00d440e004000d4100341065000c0d981500801050704600307000461040d8401c030b079101c102e94158106a9 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 161286079 1250 161284829 161284843
    0x30f13091a01270506210f070e030f12160609050a1b030b04020f01021c02060912040e0406150510050c0d05091e030c12060f0603030a140f0723 63
    0xd1020900542e1450798100004000342130f40e030180c0d20107507981070800c0158111565141240001d2001e102880902d140f1401c5080c040d00807565130960281400b410151203540310220200340b0760280f003600c01d40d074220710068070443c1c111040d0400c6030050303600c406c819120082001c66075a00705280010400103c82c14401015106448212581e415603036204050000504061721500c0b01074507040c0b9583c0308016540798880c503001008884030030100003135a108400e4440d81c40c240240980206520300d030b64240d4044640c88035201e0788a40f83c58845000074500901ca01d030005502800101329921104040d494140c0e180e950310380d84802c142042801c0000c500400d008112041114084584d604c8200c9103070300c2902245810303240700c3d00f000a450700200e11105500721040c0300c0981c80c034200101e20144922108880300c0314581e00c000c101030303c07403044500035808a1008090106107489800140154418000d051172402d42c140d03c2e200788805d8407028240d58107241c4002070858040500000d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 161287329 1250 161286079 161286107
    0xd0501060906020d030504170a080411030a020d0809010915050a0306090501060207050910080d1214040c060f0513080a020307080d0c0602090102210414060705030f13091a01 76
    0x24407505420060003d49a8001c040d960b000c141c0c49801013006c1c0001d9042c00c5802d695440001552071a540708090031141084505964403030b10b00500d0001410089840b00b500c0394000c10140014550303540709074468200c581014108100a00c0102d200041040c2e2507c010303026855440e190918840028140c40081e003040070032604001c0100240c80d00050800b050b030b44202c880880d940d42c0c0c0328002d00c0392507450f8404183c600c640e010701c400042c1c0208200d080c03840c2c1c10a044c00180c81c0d02e00e030101160804c0da0000c080b290068001c1102034803803803003402c10078242d01e4403902d014a540710829220410707410480e42d5801681108003149000c110309001000307560040c080380b1124030ba01030190702d81504094140d0b600000d0140007a031003440305200c0281c52850814090f10186602001078005014000c050004100512890700e48001039481107640310000b9482e0000341d000035190780d000313240c40c160000c12003800841c0f10701c094003450350007103c0390700c034180c1800c1000001450a4030300c0e516 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 161288579 1250 161287329 161287337
    0x11a0409050606040b1302030703060306320702030409050f0a1b300504150c020703111c08040b0307020c0609060a0c0302031605010e100b0603070c02010c060c02030d050106 76
    0x49803000800c0480c200750b00c510101c0b000100a401c04000c2055001640d003030704c040d5032000081000450b00340d8000002e5a01801c801c026906c03851070b102d03017004541c1004448886918008240050404441d0350f230000041c0b05132810705a488e030110065500986981e01602c2100f010080030365564410a04d0440b0004522aa2601400c501408e46050701c1d40741c204994104020910040e205210403202441d071150820003480c080c108230110b03102c2ca0107440f16107403c2400b41c02e1102d20008071a020b4135008681c10070705001500404c083c400840071038602c118507100c032103004500d41802500051030341030100c1d83d0740d280c8008001d007004143d452581c820a018000b9015541b5038009030307407801500b42072005078040d442c1003c1e0710790701580c595450080c000500c50010444103420801031070f4891412a0342400900000c24103460010a00e1a00100240b001451042c03080c54046071650060528003401140c3d0340720581540c0180c0b01c1c032000742e80b00149502e042c14441c4070b40c2d80100000c0c68 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 161289829 1250 161288579 161288591
    0x605030616080c03040507150806040c140409022d18010c03360b040303081501080f040303020702190302190b040b0a03020c030c0619020306090720010608011a04 71
    0x101030a440c8000e8407400f105280480000c040220400076040546049881c2842d08485640014a80b070003c03110580141c1c00d04252000030b45c01969521034401019500500b480d0030070450700000e402c481800348000012007540f244100c1250401c000450f0074850b40c1d950740b01d12165034550701c8194081c40d0704001002c501c64000c02c3d03101511040c0411076101a0800b0381540c010f0703455405e120800090916070040c000106909441e00420032207109450307048042c0d45907602c0ca440305007488031441c041010800090f1400c4400c5c09480c0c2d0040c0300c3e0800500302900c540100700f481c8044200d900e1a0b006c42c00d000e00a6151055103c03c440c0400c4005290403428a1400c01441c000d512550303211240c08104144804d000740c040d90b0b110514141180e841d241040c56a994580c8180d99420105250010384107010503140212031049134098001c502030f0300c03400d10803240d66600082c24a1900580404178441000a002d060024184540040b44074140c280d00512101401440c1c0da204900c2c00d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 161291079 1250 161289829 161289871
    0x15030903030412020109170405040606080610200d080f01080d12020903070302060304260408071206020405120703030311070b15060c070305010e060c070f021009170106050306 77
    0x100c1c2c2d0700c2580a41d403852100c080b000b043c1c2c0540407400e401404442c41480b80d0205055070400340c421234808035024400b01e65200401d440910080c2c1c1c11a81203014118000d400ca40601a8071034014041e50300c1c4081c01500400c414140b03a0114400f500040b0080140010010981800b03805802d4072009407580c5451441702034200d040c040f00301c211103030300401c0c200b6083e0b0f002d11500e070040d600900321560300e01d8149481c4d103090003041185900500300c030518150002d1100e041e10140e4120f20010105241001c00d49851748840003401c82c0e840740c00300008900d81d12000f00c0001a404035000030310340380307007076141c050146c070986a603400e14294203219440205800081598110740d05400000200d061080444c4692250351482100f6120b011400000c1080541c02094400c4248098032156140c035543d00741b0314418420003404107100841352a001d442c4c41407040c03050000d00c2c00c01041c0307150366400c0f49203a05400c1e20000c1c0e141c3d41d1004100000e050900c802907010501134007a1082d0700fa07407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 161292329 1250 161291079 161291083
    0x215070302031f06080f04020310020409020918010825090218030c01033b010903170c0715050718120c0b09090103080a0323011419050f04021b0a02150309 68
    0x2001c2c50101e51b04000800c01f552418410503081010b0540190740e5544c50340040710103035112480c3e043c000e40c116608242c2c4180d00c0071441e03042e990002c01601c07001c0c1c0c0d000c032041c0c400d0f10b082c0c00340710850204e0080010040f1442c4018075141c50003408242804401908041c10b04100045e494181400d103000502003005c46000311807900302d0500740741d0b0380e9074080d000c086821100d040301c5400b5610341121030050640040c1a4800c1410760070f80c1408a43d55200310040c580203003c0c006100752200c3c20000d01d482029002507a001c406450f0a140700450b01046d2020b00000780d00c08824075052102400c2840b52005101c40604400c20700c15180051a5001c10210441440003074100603011401c203800a1290700901c2e0300c01106140d01c01c0e03440b4810a101c120707840c280302c1c00c1c2c4404032040000744142802c60000c1c0d600c04602d07100700c0b9001d28000905c0711108502d503078a6401503007000405107e1a164000c0c08d000c45104004003410074242c414890b1000c822015144124024020003034a0400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 161293579 1250 161292329 161292331
    0x140d05030c0a09030602070602070b0a021801030b181602011409190f0614060a1403100e1e0c01020d0c20040603060e0604060c0906020a0b04030215070302031f0608 72
    0x28020703410756141c81515045410f14541e420042c08903000003001802c0c800b1540160400314004c0d2444042c58841c04911022807040603d4250120741294440b01258000e600c90b00900313402500d0b044d10020300a0080c4d100c3c990840740c6695810607640d0a03d550f943c244214a028074900e1a0f0030350b03034240007955603134a1400c0b0404a0151031016407400030403099154408030319034040828001031200364240c4208410031100240161078440c80000d5940c2c0c010080c0307600a4018014005900e2080c40c00400f6040b01d1403c0c00070351050000c5403880d094409650404030b1450406045174602140009042800400303082d000c2110506032007003c1040d01c0c044aa007200d000912429124805010802600255002070420b9140142a07491000081801441548950000c000303045480c02c0590300c10503103029000050f070107262820000380b0102000740c2c02c98002d004541000c08224a00c46a81d0002c07500d08000075004020700032a91101c00381c05159900e40b9114410150500800a000a41c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 161294829 1250 161293579 161293591
    0x106050f09270604080c060f010302091b090303070f05010605031606050a022a030c09090307080706140112030f1e08042402040311030f0c0d1b030f140d0503 69
    0x1891402c21003140800489142c034904903802510140d107001e04110366242c010020411036030040d100001d80f4803140d40c5a00781a286d0051007905940c03504035050610014075402d010340c20740100001c0c13203075a908002600150b031140d01c140c80c2c0340c01646441e03405c5d58681c3d803085000f58050140a588000e00c034a00d603080e29150310301107131640654902240f41642181e200084d030040f0085119505c02c82032280142c07400181c0855503c540c803031003441100401144c080ea8903400501a860008013a0401000418000c001c041082e806081c16100302038001e83c444a03c3c0c00f1403941010070142c200c5500c881c0d4028505206503214001c0a1324a00701040324a41003c002135400020204000c410158440d2490b40c0b0003b0f003941001b250520081d0702500041c1d0705046120081e4510303280024150301c1c60303824400504080c40e07034202800010b00002c081214861601c1103480c1d288500080e0b900c000314083c8001d049508841c0c205101c0010104503218400d0300071416803024542c00070200c3e80c00030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 161296079 1250 161294829 161294851
    0xb040b0903010e10060503073c0e01180e0601150e030109080d0212010b030907090902060c01050907080106090b060a0f0c06020316030c08240102011413030306050901030b151201021b0106050f09 85
    0x260b000000302681c3c49c407030b0841e030f2003d15500b001003149484088441c6543c1c0d101c98003040000d10703014280b55281d500b442003840540342c581c4200d8041e84200011324031884040c0004c0741c1b1000598409034140c00800c107a1003034681c040340e840c06801100e403901d0b004111144240b81340d42803581005449011a00401c1318443d2191425411501c1d00b000300c0f4900d00290b40204070300d0600c800e13066140d000610a629256007000c00101350303040d4078402c5c1e00c400c4400400943c44e11a0340b400998044240b06013032030600074020b200c003000c43c04a00007903114800f0040c28010036000810007808a9260130785481c100054001000340900102071070f5480074440c3c52500101c0086000100d0240024603102d101003600766091000c000d51200a02c808544a91420f102068403081072040d030107030900c00541074186510204000e000300c40700c64410040b02410072685002646019826030380b00846510140001002c1000000020310039480074290480340a50100c5e8041d00017a510304e8042d150703036100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 161297329 1250 161296079 161296169
    0xf030806091317160309030501050c160b09030702030a0b040201080c040b2a0703030e0f0402130b07050a140d120b0f2e050408060f010b040b0903010e1006050307 71
    0x500850240c070413030300543c00b0f00b0003503102c00e160040203038205210032641c96081201003504034580c1400e4644448481c0740e00c5000712090384401141c200c002d0b0042d12140010401000580c81c28040e100c0818000c061120040c202031000602d80d51000340040c481d08410321041c400c0d6032004040755101178424064100e1642c00c00c203001450741e07000e1a82c50881c81141c00c00030415400058441002508803680d00400300c0c01070501c82a4130503d8a981c11a904100c0140f0041c41404003600006006030100c41d6000c00302d9035000030f491080807849042d80d1090b022811510707403100c9030a1a943c10190244196103403500865407a0400d210380c5131040aa10719001d0040300d202350b21110075004c07910000b90784400c00402503c41d0b807250298940724003032000000c140303407440c40800d8109d804130b0081301d15103454000c0c40a01d68000c04415035240d501c40c0e00e140d003500c004020750380911801140004a16241c0b2080510f0311505030701404a0f6218a010100d4101058043c0e007200200075401080c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 161298579 1250 161297329 161297363
    0x4050c160c050a081005090d0e0d0c080a08180301090206090103090204020d020d02040509070203090a060e04020714010e0106170706051605070b03040b01211202010f0501030f0308060913 82
    0x4a50482c0c0100b0380050041070300003071204e00020980c0100f20030070001c01c0b040e100c1c24041c40c1c9445a102181c004034204290f400494201a0544010035000d03500520195840708403050504c3c401c04019078241801243c20a160304021005216600084008102524a5602090050040e01e000d07034107050b9941c051a0035901d4540403207104240c80b210031540d6080149481000303412034000c850142200c4000100868000001c40f1013007040100807105103450280304a07121440301d41e5441e0095001c3c0305050011b80011042c458001017800040b40085142d003200e802c6500c0755005004000503540001e4603100c01041541c1510700340c2c90300541d03502900e002c4294060265800400a200e003550001d030b140802c6018600562041c04412031690b681c11001043c6414034034488aa280c0300d5210b9800150310f00322202500c2180c0c0004110304039400080011181c003684203541c1c501c0740c40d101d402010360000e6840d40c0408c00312002c07030850404064040340c0d250100310080c03a0414079100802 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 161299829 1250 161298579 161298593
    0x601090b0102010b1216050a0e01090903120f0506030d02030414060c070305030304030c06110c06060d02041b080108070801050f0109020732010c08070c0303180b010b0703080604050c16 81
    0x1400760409005075401c4800f01c0f080c90b5035171000045209480c60b0406e4080354520300354042204460400d11050310a90a2241000040003001021020722400f05a08007070600340f80211424007400200000f82460100d06060038402c040c500b403000c6400400040c80300924500c0b0082c1920404d4441da52100b481d01d1c2110326200d80c540005e04141300c00b00400080590090306a050144503403400d0204074480340000c1424090b04511078660b03007101000920b1070078820091740c0010b00081c00400e036071403014917841c00e4544043c40b240000300e9840c01404000c000300600c200074a0a80c00030070191030702042e902600d000c1130162607103031500007031100148158601d15518843c1103000818544c038141d5480c221a11203200c5400e80c0f035081c60700d1240c406000b0000c0c0c601c0703002161240e1000c419603950403001401c040e80b5090f50348411030064130110b0040342c034050103021580502076890b003c40c00e010301808030050215219509050030046104100030540b0783c03040d1100038062214210b460640 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 161301079 1250 161299829 161299841
    0x90304090917030906100803070f06020706200405010e0a030c06210c050406170c09010c0510060602010902090a0606020a03080a020d05070504050f0f0d02210610060e030f0601090b010201 82
    0x74000c05010007401030030070021640074090400e442c03103004055603694a045d00ca00074100050440ac00c0809568042806a00101a164460703140007501c0c01007245800200d0003141c80c0100d83d01000b20b03081c8020350700012014440402152401d101c01e06e5640c03002610398160007400100914000d00911010103440000c0001c600035600b4000419a084024101d42151150303200080642c1c840030050090074a00500540c0001c3c0b502d4070b010070070001900e00800981c4121454411074044210041c0c2501c47c03600a000c0c954004034011065004120382c101d0302419241d0000d20b001000c100503500003d10500030303075250a00c0310031540d40c02e040000070f010340d81c9540200c600302000c11240c958000014800d56800f140e061070b081148a040c046126000d902060b0024030b00c07469600581343c8240313440001180c0582c01c40c0c0e01c040401d5950308008042d00d0101c10880740c80380900c00c0c01c1c0c1001c041a0200b0050f401001030340928812256500d9040c407440160301d07520385540c41d05034800c0d0448 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 161302329 1250 161301079 161301113
    0xa0204111b012a0206010b130f08070e160516030e041401030c081605060f09100c06230a0c02010b1903120804020d0314070204061403070504050903040909 68
    0x10700c64a030a0324540c0e000c0c1c607150700003100342d200e01c070303074990000710441d40c549800e890035402044182c1c20b00c401030113a5030250440591140c1600310005000d0000c003074600141c012200900146840c0074024ad1914501030b2052101c84c2c10300920017021036009041d81c0d804001f401c514021002141401e59003030b241070405940050030408624103c1091466450403284140c010740c60881d039519085448254101002c4803082c2c01e00002c00580ca44103002e09014550448450b16211543d4002401b40c0e95880300c0d8004101c00000810912400d44101c504488034004001c100c0170441809807403103680106403441d40c99840a008441d5403007540181c2402c000504084030600007588070464003002848221001e0344402e6505948910844245001d01da014006020a54060350195180c41109860405800301440088090784d141c0c014200141515542800003007409001d01d03041100b90f4110f0b9009900701024030003150f500004841c1101d159007130000e0704503450f00d000c0007601e00c8078040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 161303579 1250 161302329 161302357
    0x12a1b06020406030219090515030901230114090c072a060e0405150102060f19020d1a0108040b060409030c02090c190e031005070e0406080303060a0b0c0a020411 71
    0xf0681c543c06078010301c034132038048242c0c0b000c5481d0014111000d003960b005060304950020184052942140082e40c1c10142400020480480e10000c600707483d840060101d07050408600100a00b26007901c072014058016595804285401e12010032184198800101849880e505641c0d11040208080d9041d503020031901501e15540e4a0041000d141c09000500c5149800c0125041c162400d45640c101356041e0045d184594901040b0a0388071070081c2010410400d20300c920341c0c0d058407440141040c034440381002400001d00c48200b4601d400100322903041c00160028840800e280d580344d02c2e4000c5080b50046004050f40c43c1c21104070a0111009420992040a2141070420b040240441c840a0141034010548075803080360f845100c0ca40958164000c800c8980c0b01d03d485800072503100126042c00a201c10b90f00d4045000caa10652082840341c1011050050a142902c8a0b40003002e02480d01c0e41401e4421040a0b165240744030000d00c1950381d621041c03a45100c1e402541c05042050070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 161304829 1250 161303579 161303587
    0x610031202160b0d1e0c0306050904050c01050304083f07081815011202040e060708070c020d120c0c320d1505070806010503040f060e0c0a17012a1b0602 67
    0x81c45c0024044280d01140481c0c00d001c008116030030020780d00c034801e580100003028550004801541c43d0707400036105483e6204100600404071140d141007440015208140d807038148010550003034001103002e0035803d500d03880014810f40c0e552143c02d82d40c1050611502c0d850100020900500e0188075101da00d04609012000082d00013940c41c91064840c004d850910103200525100307501da0f0012038404002c07950320000704200501c503040006440d88090b12000d40c2d20740f1a254803005144204c1c0d9800040e148040b038070308020040c1151001011051030980394a1000304007000340602c600304030301a00c0080700040e602035440e6510b10520716008880420a460401e0812001d01821500a000320700c0150200da1254403e8048070b21031604000c4112a0340d490350755400140c84d510360798080c0ca200c0e1803030305035681d40e0703030a4104010f041c810801051010b0040802c0d00b5130f4024a00348012401407000008040510201c0b134100d4200c500d0044100113180c020100042c942d21400340905201007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 161306079 1250 161304829 161304881
    0x525030f0c090312020f030307030203150a03080a030b1e01110304051521011421011d0f160b0309121603031d1902030109050610031202160b0d 63
    0x80c1010030f9a00600c01d014040050ba141a42d8900036584c21000c00c4d8010000545a507100390701840c1c1040d1268a01031a1002120000d0251036840d002030350380c41400a80510b1051305486400300314141900c07400c1c4101c24614004c41010101400301c3d040c480389601e0b5030b9002509004403405400000c000030202c0f4030211100b0354a0b08a50440041e03148550b50480000c1b1216516504941c0c0030205010070300160340a1207000c0a05c00803d6449180340641d1071a18002801200401041c40c1c900d001003c8800204c549001e865481001c038a41201d0700e0500103107020032903201902d130550b403156920f4659040151600c0d082c00f1640c418070070b02090181440c00b00c040d00416560095400380140800e0440c4d204494003c00303070111603580190781e10b0011108075111040410300003000002d0280582c0c50741d90601504442040180740c1c4d440041c002c101d50182012840301541c0300070b000c2d00405000300000400503000c0d885001e034010400312402145500700034804201d0400e08401801c4e40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 161307329 1250 161306079 161306087
    0x270f01120626070906051e01030207053717070507150206152d0103140a050601021c0503130f14010c020c030309060405060d0b0a06020705130525030f0c 67
    0x310030b0308002801803510001d4500c103c2d02034001a41d10060101558803078040b6000c0c0e00940d440a824103254092041d140070550034401180c09215480462070b45c041c0514a040385d5512000001803441d00a010f8680429071803503061804000ca4000340340d40340d15904000349409995804010035120428099040e41e9010801c81d019005002c0315113910080c00040003e405070246039001c42100c464028544201c07105641103041c00181000034420740c0b1500300800c5401c00300e98000c42a03031158284001940d04008001c050010083e00d9a42c0402e003100052091002601601e92040b91740101ca080c0031040408003005a445954031460741c1c41000828040d090740c2c69140058002d40e840b01483e400c010048807517a182c000e00281c5403a041004128464210030b08050744159661001139013519148440c0024000c1c80c0c000305202413901040009950128010035810b5040c80c0510070084250710308824000c2054915461084060a0803001843c81c0e4000c86282c0d410500f03541c880c1c2d070300 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 161308579 1250 161307329 161307389
    0x1b050907030c080a11030604050c040b0f1308030703050f0703090b030414010b0105040f030305031801090309141e121023060303040b030727030305270f011206 70
    0x403d0711100c002c1d6136901a41022100f101c103260201000030000102c09140ca5071100360b00c40d20001a071414292100403c640d96000301081c03803084000054a0b2000c0c0ca010140c25000700b42c5800258501581964020081c4c007500500c014500d80114900d402c01d801442d07408082c2000001a580320314081c200141070b2103082042c076402c0e500e0051401d010303510500071034040d1007103002851030300e0f07196690448166200030442034900c00f480f203180120400078040c0c614054040c1d83d410307d100c0e08008110000305619140d04e8403074440303100c5000050700c0c2000903c0328008112006285141102e02c01d80c1046506402e070404540b622010981120522020340030000d100c09100b0f00b10703900c81c001d15540344074a01880e04004000d00004003c24400c8045440641038100c813020103442a0383e00c0c29a1461a800071004601e01041e5903492942840000b4a003040503880b00070080760b440d02041040100301c5020341000300040207007040c0c605c540c0044000b0410018045881c411000b8000e42c1f00070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 161309829 1250 161308579 161308601
    0x60306050f190603030509010c0f141c0306060f080604090c030521090d020d020604030606062102070209060112090b0c0703080705030411013e100e0a1b05090703 71
    0x30b900d182009000b1402d10501041e00e83c103446d0240b42041880c015220741d086251708841d80001d460759070000540c180c03054103003440c1c0b0304010951110364100407004427110782005010580303800000c01400d075000301100706404a50034041c03150b49449000c140640000b02014040c0740c100c1c42c00204102000502040f29411690700190f40b9403500458403051003a0065540d100351010318080152070f0020354000a0b9200030000d514042e40c9644110945201d54040d4001c01c8415210308040d24508010789441c5900c0e04c0114904902c60740007540d1040040d00c05410017280c0c407145000035200364002d0102540105880c581858804080f0b50250b01501c0c04600245c50200400c450600580540340070f1070340024901295400d0b040111010050400c507450403280844901e2505403004c0e4551000c1c202440c8038031401845041c2003450050002d50301d011071841c1455000b10058049007581100350b122640440714150900c201a0664190304540d600980c403c003480711240e0140d01c02011a0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 161311079 1250 161309829 161309851
    0x2070305043201050403030504030b061f02030d0501050d020d030f0311040f0f060c050601030b09100905060f0c0a050405040f32090105060607110111060106020309030f010203010501020a1203060306050f 89
    0x1542d00d801160740307004901c001070101c0e00a204c1480042d03080c04110341d00100c06049803041c030207540c24a02c00310311a141441c000d40c10005400d146840c1d140181400f500c010380741313103e540c4480e5000c00c105041d50040981044440001200c3d0300344039400203410007a07012480ca07111920380e2015000082d85200e032030b0585070b41407400600740d4040c240048400f07030004040c001b00c0c1c0ca9619404000800104682c0940c0100300003403411103070358030440c00c103240904000c0401d0701c0c008983c1c1480c80c1c409400f0420129081c0b141e03c2101e41e03c01d08403070544800b0369011403110324110310200a0038942031340708103420001c0d401209a00c9154111204900d022100081640342c0841c0c8608841c0281d54113034020504019000c0400e00030844400c2445040c54210184100c004c607603400d051083e0090733001608000b406c10810b181c104505090030210000843c955450040080c2d80c401102e50700030302c0352810700540204503020741d000380e0003150132000c20b00051602c20548800104c04aa0041c085 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 161312329 1250 161311079 161311169
    0x203040602070905010b07080f0f0d0b030d08041101030c0908010603030e03250323070902040626040b04050a05010609020a120209090402131d0c03010b150a030207030504 75
    0x40c411500545040310030b030f183d0480c0f0382851f0342c40300c880300d50101800c526030346400c2214414252480b80107020892640fa000514149040101343c100801a140007003003080703840030311000c64140031035807000c10000d007000188208881c6050380c1418907603201100c0e65103010b1000007810b4124104100004e801c0b400c0d03410584400042c0c180f5040101d203402100c15610700709200144401012031000305107140c5c58804405030713038203161802a4a400118070315402060404c440c07504100d0020180c0d0220312407243c4045009070380100701d44000c1014001c8281300000c00d085c45403d00000c034505410000a002c1162900c1802001c0e41c82444c401300003501080b1040500405803081e01c0080d500105101e1660f180d0b40c00b0040201c50000c0150000c03039542605140e45100c501820106407050000350003e040f02004140c2143c012181880c00f50302500d080d00e601032000801c5030300b16244d6090050f250340d0079003400c03203a43c000d6420086c060070700007429911020311115440490102c003c411845 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 161313579 1250 161312329 161312339
    0x4060c081f03110f040c030b032116230a051005040803070305150301060f0f050405010b03071101140c03090f0c030a031d090708011403060402360106020304060207 72
    0x46030212140307040071031022400c1800080c002ca040854600e10003484140e140740601e000400300ea041c11340901c08203079184400390803401c1c180300c01820445194500c895500f901042c0500c24031440780881d000000101c00d10f800c01072600561104c13002c18503007000c408041c0b00d1059a680d038803400c0070340e0b142c0724428840e140920076005152080354088046c90960301c070b580054015110150001002a000303104a03400c0c0c0d00d092046a0040074004000b00190f881d280b400c822400307860700964013541c01d01005016610a50742100c7d0030175420301d00851001d520090b0180100003c00e6022070000900050003034070b1110308003070b5005804080548411030045e2120a5684200c102c0b55a0142c000e515204042806522440c070f002000040810b4030714881c8000580d01c0e50304540e079901041075403006101e2020310b4010201c0b144000e500074406410a034000811000442d01d4010310801016083d01c454801040302062a040c4090321110550311840301035102c2d0060b0107000010703c242000001d07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 161314829 1250 161313579 161313601
    0xf1a01151205060a050405070306090506041b0c08040b0f1b150115030f05010e0709060c05030f03040f120206061314010303050c0f0304090c0f0c170903010f0504060c08 74
    0x1a00048a03111580e1418600305503034040c00c001080f240d4446040384c0001110f8480e400b600344217030266900060b000e810010498104d0700d015060300d00580c68107083c182d1800052400d440c0001c4c190a007000d0003103692400743c181d44141c2c0c001c00200800402c0e9006040b001c0c00248c410f0110342d850800700f60340c640c80303004d580c0d4210b0901c030705a031514400108600d05a290b9060811941490003040400b01c030110441542c1d07080c2c1c4440103010152041000181d40b000d0448054240c07440c00452103405622501e56138000c8d085134401e00c40e000804035040200c5241d111000756030042c0e6000320391031001006512600100d40f002d00802c03143d00707800b2000100c2c0c030409820101600f0209500d17401c3d900e048600e40c0080741d500450f44a4611500d078400001c1000d0710040408070380116002c04040d400800e03032002101f0b48000d105c0d800c00706400280010440b010030208a40186484e031040400007030140094042406140f4940b20600c014071040c1c0d0088280c00c2110740b038085407502c5010300b1603 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 161316079 1250 161314829 161314859
    0x105070c0b030c0d021b0c0108010b0301090b01030b1210051803040314010204120f0203120339070609110901030209070f02120a020303070216120b060604030f1a01 72
    0xc0000881900a000311500100a9500019084002804d2080d122501800ca0380126401c8007940b0107003480500740b04041002205224080c0f8103c07542e54500720354a1f895000601404650986841401c107060f4881e0f03124180c16040240310030551844582407948544040e03034400c01039828440000c0b64501c40703401d42145d01e9101c4006501e0189182c0b2210100c1e004200c0e0940309540820000803140c01030940007440900034403040c281d245262040500c0c01c010820402c054100500c20000c1e07038000b001c400c100c003075850082c504110314034600c440021401010780b0300ca170003000704c0c0103014071040b40d100c2d030314007841042007104000720030040040742403003440001c1d48100c50301e000401e0a40310700c2916010388000d00444294220410b100c8401d40c10003410180160f0000c01007040156042010701c09000d5401006460181800490203841c034141c1c902a10b551000c0d00401c0741074440f01c044034021a0400d01c040481d002c03038581a054940150061031b05011810000300d04403105400c94 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 161317329 1250 161316079 161316083
    0xb070c060f0b03070f050303090607020406050303031e10050d0b040201120513030e03010504050316050a0206030103200a03080a05130801050109150e07050306040b0f1003021b0303091b150a0309020a05010507 91
    0x110f027007151030001c2000d2540480b0b07007260460340f1444009565181000a14006d107804100c002c0c0e10f508800122a1a40004080c59440c4400810410003500ca03001c4410555030099400c0842d6a5103000691b4a5a0200c030345d07518130380c40d01e800c10640102c03032600da440061013940d03070f80034442c00c031410103003600e1307080c0c402402e40e4100300120703e005070380029409000703446030040d901143c0660300010b01f0364100368800d1340c1c900f500350396420f50a00e2540c401010310f41c1c21141c41600c0e50460711145d1550160048000502c0380000e699940d50341640c0100005084070744c02070089684810b040e2010f0000a404220301e5007280f000800c410561b45032040c0300d0006541c1e91819030740d6800130440903203c0031100c50b42203a02e4010300071103a06c0fa01540d100b451400c2d14056502c64240c032907140f0204859104401c145c0040c402e00000070004a00101c1c10034604080c1507001c1d040100090710300348928681c42a8400006042000c140c041c2c011003135150007103c2800c406685c503001564144074450700 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 161318579 1250 161317329 161317333
    0x6050f030115120309090623121e030c06011202031e060c0711090703050603100903020a11040e03072010230d06090207060606030209010504030b070c060f0b03070f0503 74
    0x1800030450084412000e40e0107845e00ca108140e86002d8001210032031703088060b420b100c00ca240140360130a141d40340f012070025039051181042080d101621018010002080707a10712003074103030900740b080080e0340241c40d40509444031b5583d80c420502c000688910124085d00030103807000c40d049900c1e10041d2a5501c20f00c042c045658401c0302086107a03105646c1121854000d90f0307440116151002114451100c58174001b642e42410400c052030030125078003080501b0f062111020000303501045030807411b54840c411102c081001f8000a002e072460504044d0188030116404c1d06018801d40c10440e01c02c4031381d282400d00c42d50541404590094803140300d0200d00d0214111490320f9041c0070800411140452207800c04007884c0e41c21044d51115440f1205841e0046002014481544a9000181003608086140000180c0040c01c203000f6403001a0040d52003078000303800f00340a200703900b0002da130140c010001d04022003401c5004003007500c40b8a029104c1d4220108010000018401c143c60000340 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 161319829 1250 161318579 161318621
    0xe0604050609070e040b040201030207241d03070204020306040f0908220b070305071109130302060a020304020943020d020d020714010306120b01082503030e030102090306040606050f0301 82
    0x542d80341a01007d40224101903082000d8008503403492140802c400f4003802251101c12442c50728010340c0d083c40d594800d280308050129541c004004201d44200d40d0584015031690303a000c001034000e05803802c043c0c010604104816003001090001005000082c01d80098045506000c010591500d400740c10050882040917402090242014000b258411484000348002a0001c03800104054a125031011007a408403c00c16405005507a07001c03925000443c25454183c0002c1c0040d01c02900a280880240d4200030344c518803c89154030003501d110a00078680d10490030f076281c140c100c1c150b10005010f04040400e82d14404180c5104407080c0ba0f00400b94141407400320540350100c0d240303441c10b0656401c80000c41c500300c2046400d1182c050140c0a03099031414125030309010441a144104051039101a80f8260700b016441003543d41516000d4040145040030074024810b15420720391612800040000b0450550080d500382d44003520108003058100301414242d42410403160000d80c0c0c0c0803 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 161321079 1250 161319829 161319833
    0x90f06120905070f0e0f04020d03080a091b230f10020f07030b0a0c02150411040603170307030605010c030f030504030e09340203070b04030c0212031e1c0c050405040e0604050609070e04 81
    0x750820342c20141c150760000e905281381e900e04411051703840000410300d4001901b0441024001528001c0042c071401021010b0588fc0000d8800035502140300d1192108034110b10500d842004000d1039a81c0203002c40d8055926400e001c1c00010381181c00d041a41c0c14520100941d500c003040d40c20102d010610160855211940c80120700d5440e00b950681181c0e4600b0000081843c2104662035203441c25840760392030400740401001e5444a40016051128544a00e400240c0c0450b4081102c60a841e000a590301c0785d140480c0c42c0031440d401a03500842d074100380600f84900b24100312843e55001940c40404003910034a0b98180390400e41320000d0380081c01041d0110b12042046503106100c2c0c82c4c82d20159515900045140039104204201c9034000728041c1c103228910298000e90800c040d002c1c50034481c5044000c506086a203010744400e5458030b04400c4818002c405403000b9110091040c000301544020309556400c01712425503140c426003021a05410006c62000300b621901e201c04041941c9507 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 161322329 1250 161321079 161321087
    0xd05060703091b031505060405041e08090618031501060c1e0f080307020607021c050c07030c1401080a02160305030712140601020d090f06120905070f0e0f04020d03 72
    0x44010354520400d00680c000022800c060034028500c2100600c0401400a80b940c5c12580d004051900403890320052102207001314030407102d0f8503503009104400c14858602100c80e03001d00c10341c460300400080b5541d001941c501410030303044401078007101e12250004988050300d820030300c18400401e2035014450003050030b569032040d03000c000e00c0926803084016600c411070035805143c20380301d41c0703004020b0003001da0381800314503000003040c4010301e00d2100d42154060000e03441c0c24000c050050000b0802180717a01485011b0007140c0007847c030760390700d50341c0c6c0444502a500300c13200ac3d0000ea40000045c603c078a0f81d200343c0d094280d08180f8950303800c2c9503075400c2d40d5507030000e00744505021010402e4a14400740d4041d034480c500e00b44c0424240c030b0034004000391034a51114048000e10046140c1802030202e281a1034040310220310b40100c0044010b180c80303008090304280507026024280001c2072071240861410122050044400030039a03c0300c038114965142941c000394403072150309081e0301092003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 161323579 1250 161322329 161322341
    0x7170a0903050408120304050706020705011b140a0302030a030c031a0103020a0210061203090603050906150a0b12060a05010c0c05130e060412021204030201140a02030c120309010b0d05060703 84
    0x10900b0700300c3ca020344800b1128540701040c4414040380900104000800000b8890800140305500040c4055824580064118801030b071000c070380542c13807001e00c40500207418007029035103800c1025030b501d80c4110b0030300039140d600094010300441d08081440003039500c47d03c00d078016448072901c07042d820070500380110081c0d03011211003421846260000c00c1d11764858840c6500070300c0c24020100041d0944d00d009028802c651380725a0078186400100a121040400c140358000f0516850392030810b5420b0003e209a445900f10a40c4e402c404200061242d14064000e80143d20440d0032540d01c6a0724401158040454031009208003000c640c00c000909007440307015004071840f9000701c0e000c000c2d100000c0c5070040840c5c0035561481c44001060355941c043c4042815012940001c619050964001811616004502c800e0400001518803050381c424010780e24440303c00400d82d142d501030035940e0100c540045d335090390b99518042e1140c480c1d103402c00081120355400703000303040c8595030740b2810390003444 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 161324829 1250 161323579 161323583
    0x6040906020c1009050106090b0d0209190f06300305160f030c0b0f09070302130905030a02060415150611010603050303010f032315100306051e07170a09 67
    0x2070284070320152500c0034000110b2900d0040070002c1c2d07042085c2080c03425603140d0340c000b102e000d260490700032440e00c450b50005c02030742d0151040201d54607000d50180b01b2001e0741c1c4150a0b01858102c17013000034102500315104a810300c140900001111070428140003540000302141c0b0400c04c5404000680030740080c0250f00441600004c07900301d90b03110020030840406040700055140030701c4030200b2840ea030360303a070f0003402c1d00604803541d2408400203541c542080c0406031082c02c41600d607080d01d0380c150304801e1080e5402425a5200c0c0e004800103540d6943401c0d9000c44001c81d42c0524003100303030402e00c60303861014480200741e2003007481d01c0000d40b034180c0102040180355480d85008804514100001c5000780107000c10483e40c43d1450500c807c3c0d0010360390480d403e050107014404010f40c8000b51410b40507030394010300030850319828402c2aa1504030350000307112078100300820941c681404941c40300100100805001c968410307100b11808004107c0800000425402040340b0b036410f070380001c054138 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 161326079 1250 161324829 161324831
    0x1805131e020a1e090509100305060702070f120f060e030c070b0711040903020a020a03050610060c08030106030b0a030609030503010311060702030717030d110901090b16061e020307032406020606040906 88
    0x4d52180049400e0303440032a0040b020304049181041040000c122003640901d151003d00940790801d0100181101148145600b0011000117842403001040c207640706964000d1303080118040031101726403290000700701c280650044550010f050710309002240d11280c0d1200b034800400e2004000c03c8001c02003010194114070446c21080c0051701d0b00320544003e5402000286224900842c4040f6071440d83d4000608014a0f0000040020000800d590540300c003130034003081030340301d98000c103080e031006500c0600800c1c10201480107050b0443c0c01141a00c0c0109104402e1510302c00c00e01ca81845100c00c02501948881d1003048600c20184410075031945943c2568030300080d43c02d4030003e035080315442c3c001d00100060300501d5907800c4400403005086015100d42042d00300e2080030100810284041c6c051a281d424540c404000d6160030600c08000200131501c904142e01d0007401030407804940ea04034914140189407884404400c60101c5d0165070041c89162b0300c1030180006016242001c403821 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 161327329 1250 161326079 161326097
    0x3010c3b1801031101090308032a1902010c030b0d0b15040f1a011e050702031011130504150605070f050604030c1a070e011805131e020a1e 61
    0xe0340d181c80e580745400c4501d034054103655045040403000344114000150602030306800c100001803102d010790741c0c0108960605180c4181d580902000b02401c1404807040074000221700e091894442c04204001180340e008100c0306071070f004290222040585515448401200b0b2103001900400405500c07240c1c11007122061840c05011900307840b1a40840c4e0039041c1c17600c070f041e03440a480c04404003c0c40720920700612000e900c4e10381151410500302c110401c0140018141d030554408100901880300800001c110b1607805e04008442c3d508100d040c2420301c40341700000900c51030140070300c1250a01454440c0343c041d1074a05c041c4c1d12030f0305c04802110341c44003102109000c24014011148038a00076102c1441e20807042ca8606c0325012854141f14402513080144159a0f0b0b010311884550b200c28249600c0071000310180581c440d015a22044e4400ad801088110321340c407070307000080028007941c05014802085030040080e4064209408005040c1218584251044585d40c0d412000c5c141002420 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 161328579 1250 161327329 161327447
    0x1050a0b0904180803100612111b03090612010503010506100914180106020304150507032a060c031a04060e0a022109010c1b11090c090301180203010c 66
    0x165401c100c07886d910380e4400c00750400c60580c1000501d02c0700c03411b0303400412070820302178862129402075145071404005a6100c5081d0350704200201d84031003070024100c1d91034052811202180b100709020f91800795080401003806801d24402c40c01000a8a07143c050701315080200b0380c070384c1d580e03202900d90348000c0e42c820b41c00098114050090207171002d50b003d144e8850904800140716803000a500003002020040c080129038083c424462104000c2902240c614904203944868495070402a0880e4600201050310f103815a0090b408580701b00d1146150041041c2040100c560500c16009510002000504001740d5607004014032120040c0801060143c441c2005e0111000c0314000d103142e544540c030140441d04444940318024a0f000b0410f4041c005603504110859005440d0b40078050000210300481a06030540d182c2c0360015000700061003506800d41868140640c080e8000e500c6d0284441c080f40c49010710228110032034056461070400014a00344280d078006046020410020308804 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 161329829 1250 161328579 161328593
    0x330080702210405030d050711040507030e010c0807080907180203060301021903020405130c17270705040f14130302031c140604020901022a0901030503040e01050a0b090418 76
    0x100c0c080040c2c40d2242c41d28103103828140b4121480c1c880e03800b44001030114200140841c40c599240c00003c0e500860552a400c10540c0640a0401c42d5180d41d400c0000e0160629030146540744070322810703540d0321010340f10740c1c02050729034006018528405c1441d0260b606261009d4004503042040540018030b07040c4030480c0100c8680107082c1e00c0b13000940010b4108110f1a0091800301c0611a450080090354050034000d130000c42419150040e140684000405c2c0b0114201e00f10550f03000c900910341d6411a104442e42c03206164081d45110307514010484c00b92844512a0084281001c811504941c680400381b02c503a8040040480843c441003203c15003040440c65504d518000e004004500b541030f450180b001c422000303101500480c4144500c8510b60b900180480d000d00040001d220104644002200502146040590001c4c4001d00010070804000010022075660303400e001c4460341c070f030700400c0401d02c664402c500104c8418030544103940341c9544400099145a8803501d03240a5542d80c100c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 161330935 1106 161329829 161329873
    0x2120604090201030e0708070e0a0902090408070c09021b10110322050f0a0b0a06080304150e03010e1006080c0a03060b0a0e0a060330080702 62
    0x1d056900943c8408121600d841c10742c1c0c0c6803a01d0740b22140e601c41c003d00c6070308826003202002454001052042c90011a8000c00414454685860704561500700004c160340f00f01290034000760340e801c2440107003044d4481604110754504070040140c1004491800c56009500700840b90901e9401d2200300c9510600741c012001e00c100c001c824030741700c140808100410034899041c0c0a818a01c0001d031002100c0d11440c150011592529481825101584140d00d0f040e4800e000c00c0c010024082000003490100380740c100446005400001c0c02c0d1000321402d114190000240c0825051060052001604000b0001c000180700c00c070100e00d20118a1001030a076070b42d45c1d03080074045d5030b4039220a80180003001c000101410141071003002001d00b48801c070759200c460100040c1e01541070b8035101d50710390b034810b4032455822822016246088014800011802440c88008114800800c14 = true := by decide +kernel

theorem cover : BRFrame.Cov 161151079 161330935 := by
  have h0 := BRFrame.cov_init 161151079
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 161151079 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 161151079 ≤ n) (h2 : n < 161330935) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
