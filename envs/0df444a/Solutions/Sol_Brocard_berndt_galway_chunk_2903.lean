-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2903
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:05:41.912851+00:00
-- url     : https://prove2.me/submissions/965ce915-a0ec-4056-9adc-681745563a07

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 521942446 ≤ n < 522122302 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 521943696 1250 521942446 521942459
    0x8180a0606090c031139060f010b0408030d0f020f0f0409061d010e06030703020a03030f080903091509180106170703050c16050a0b2404050907030327 66
    0x60080e4030840e10035500f0034804080b494060700501951aa064224130704084042e0900442d1410710031040700ca20b6015004810300868104c1500d1241020500500071410800e0011280310b005901c04400c0c1c103002d0005010425011085401030f000c2d5642c0400e15940345c4041d54001e02c5400e04640240400041004108900070090000c40f52026010007140e42e407000c13000c0500d801d514880070305060707035001440500880e40e2050f40026016007210505500ca501040d44c1054907002600415001400b10807819880102242c0c00805c00f405182885403c0d00130030103448007818204445a004240086691524032580662200014451500e56580c3d030010f0140b0b10400030400390740600500042c00307035000b8005c09001c0c101d040186882d06117000d0683d14142c0c071380360342142e0380d000341c1c80d0810101340d80305041030140c86543c20b80100d541c0005c1c02180d460054201850045040c00c080016808021070714800326034150400e2209242c8213091070100902d19994181d1960503010041101d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 521944946 1250 521943696 521943701
    0x91207150f0e120309130b030607050705160602062a040b03070207080106030302070e0402030a060e0610050d0c03080a1205040c14040911120a080f07032006040308180a06 75
    0x107040e40d11465100708101052011580010310001da80c0d9004000e00031881c00c0110341e80e80e0380203034041d00007035942d20600040d0030410192103410010f800803c40001f8840c2c144042800e000b003200316804998a001400303502e4900040c40910107200e0300c01c0031500c5808190880c81d170942140c80281d52151541c41c8401160010ba941c02d0052080e20b4012440400510511060340c0e0590004c140d140c1c0341092003d414200144201c1c2c050045900200c009038442c001d0b04d10708803048002d803455142c59a10300c2005141070380054820190003428001040c1c03907130282c0044e01c2c1c005a90640c0c4149a0206036101035912410300d05140c504070800085c03144221940040c1c4101100500c132210310082004107940c0400b0001d810100e0314409242d481c54401550300080c00c9a00036601c1089541d101c030205a0030030350480e4602d250005644c001c2691004036407107001c0d1481c01e00c02d800c181000c5200d0361810018002024445040c021802000301c0c116030703000b054103200846912061038a4280003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 521946196 1250 521944946 521944967
    0x40f231912090303021b010909090c1403030a09120f0b0903070506250c0c0506040306060e0f0403080c03040203070f080102071202030901050901031e02030c0403120e0609120715 78
    0x3145055031020390001403080000c0801c480d0158000d180c6d856240003048407402c04480303403e050004800d0700003102ca065001d0004503e014107507010103145400c0c020342c020010b00c510544650020030083c800360350450a50803d450040810b00001c605500c1e01504000c4030200161182101400700050204000014441c89100c1e43c203a60541d04d400c400d08075110859042a03020f140888455408984102d402d6102e40340604002034006903108045102540300350400d84016031038841c10301c0348400c2040c090b030300188038660f002503a1900f40c400814649000e44004461140000801c081d940c040000d80c010b4080305005043c083d558014090003035210708012180c000700c3c1405400e04a0000c015104214010384a144c9002001d00044008000101c0851210b5500092a082e05011031003c2d52007091a200e003680d41d18107600304203031042550300c8000b04004020b22100f4150326a1003c0c0d035007403074007075882d0700c10002c40d41d08060038046e182c0c110620340e401d00c102000c0084e0380f140c1d8484 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 521947446 1250 521946196 521946203
    0x110a1212020106080355260c030a090c080709110901020a021915031d010e06070c140102031005090c03010b0d091509200f10050a09170d09060503040f2319 68
    0x9a1f07142024410b02d04d079840c100d6112080c10344a000502c504a04200559124408400003c1c1f0b824841d40c0300f20121441da0400c0050b580200300510030703000305104040d0244018400a802c154011700000d69407205110000c8c0180448803503100340d1503140c0200c5018015070462008030045840c40140213040306203410075030075002043c08507551010b01c5261102005036028004503554258240d0780f080311a081140d58440140100002010038400785001780b4100b224211014a0001041866880035180548610041004110f14503a4504485500d2008000070031000f98504003000c40c0c458809a10303010500301503080c0b08006182c40c4062100380e4000c4d00e0b40007600c0d600240200c40c8030480803517400074180d900c118021805400230746811140c03890b01c40242c644941032750180c503800e283c68518591101c44a41c41d603603040340b003550181c079003440d12909500d041d84420303817200c4840d28054440480b1031500c0c500400403202d241c40e80b40704a021614443e04400b01c803095445910000d4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 521948696 1250 521947446 521947457
    0x303071406040b251103040f08030306190605160f081201030209070504180506121501080d2a020a0b120907080a0f110a1212020106080355 61
    0x41c12580d818500c00881d2a07002141307640750001a4090390460603c040742d090510080c000040c909a201d2207620150040d10041c645a0401c08144954001c002000000d5080c0c0482d00b032118a074003030203441e81d0341001034103160b0f4070b04c1d14182149440c6030800702034815034001071851011001c00302058101d0348262082d840a64590401302d510780200d00442482c00484610004c3c1d540c0a500f0040c0c11010040080c8403c1980300780b503902d0651030740c404d140c10304108001040b0303d00f000d01015a040c46a420710740303030705200c00c0d82000584980000c1c0d45950580d500081c025500c80004032030180044042e904d683d81031410040882c8982162102c4c1c03644a01000803440b00800b10340e0354071041e884110000e61a00c4d0340e1b40c040414140511160704456409000943c03a509100001c8000b401108807400e40c6c0c00246009003510030350342004040c0e5104100041c00400b0001c0f046c0c54002a55843d111062854504441103c440d00702c02000c184500c8510942619040203100b0390a1f45a200c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 521949946 1250 521948696 521948701
    0x6030d051e03041b1d060f010e10030605120114011d0415090203030703032306060a0f0509030114010617010305060c0c1c0f0f080903030105040b0303071406040b 71
    0x4a44500c00d0129041c0c0d0320085100001d01c44903400080c6400c103228031000c07000078000b8481c48210180c80e50003e2440480c0c2c090b18020003603030700c5100350410781c01c1c1c400d8009a0224070010f001c4000250b0303180c0c01017001e00c142544262280d80403001130440140000b14044d5580c507460301800400c102c0c4032203046050300000340c03c03030701e10302c10107281c05400c10220307490b075480d00e42800010403510030405580e00c40c07521400680d02840140519442a02e0004440502800c40c888000004180034461014001400050703941d80c4155550700b0030742c0c41c20400e40f0100400480b51402603a55441d015801c0003030152400b00c20480042c141c416954507428035058403c0c640c4180035003032001800b03640182d0042a01ca0055100410021040b0821110501c3c0c1007805c45085902001e01100058840c0303818400740c940c440a49201745009251600700c9003005120740e0b4030791206105141c8515611141000710391000e1041c0c1d00d82e10f0308203a510719a14000d00605498a1301110100e602030202c000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 521951196 1250 521949946 521949973
    0x33040f0f05150a020709060308030a050a02031b0a0c0f1a0c07081e07021801080f010908031812070b1b0c0a020d020402090406170f0102211b0408060603 67
    0x1035081110001494403030107024101000d8420350080341c0c600c0450040e0740e4003143c6c0080c00e009030001035100e00700680d0f0382e00d4110780407402c0311805080c26211500400900c4004127500c02c901c0b441281c1703000220703510014410f080d22807106010303008100b1111080c2c10418800440b0b07601c070328107200c543d180700b990351902c03440302d600d12803c03500030711901c014044084011881001e140001c940000014079145d4207400050b01801c1d100f451240d01d180d50070040c070810406000f03e14040200b00002d00c81118a59140d0701c05001c02090101d5803250443d005260550400500b40b9003181240c041d542c81065080c000521001100c106030b01c18212040562940482d07000c481d031001c186005048216585c0d030801c4401c01e03518005036407254080c4000c031000c0d50356100e9000100f80c0c43e84903c2080340900c1245041c40e00c2c085410790241d10601c007520740d14000c25000c1a1031211202d14004030350b10034020440300e149482c2c20081e88600403030003141007000003603040d000c5c09046045400d00880c104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 521952446 1250 521951196 521951219
    0x91302030a0c0315030b09070504050c18150403141207030c1b03020a0b0a090812041a0f0a0f03020c07030c051f0e010c020a0e0705030402090a05130233040f 69
    0xc008a4544010b4420004a06c0c0c09910b190020000000d44421a0b0b0301c3c0001020f4a0f02a500044502d50014114400c9801d181d0586010042640c4c6400706945e40601000784d0b01031403101a0103501080c01d0249030750030901070401e220f41c0d0140980d03103801c1070b41070042901c40c8000c8100c2e002144190856801038000c044201107a44c014010710040d4200400f00c1900c1d040440540140048914081002c1e2400e010090200811400c2d8035112460421880d81e82072120403850300042081120000c40c501c204116214620300d41030a649102000104900a126812040002e405501e0001c01041904040c074011038204441d00c2c0007080d1401401e0b4107400340308841c0340200f01d11b00140703902c0354015000900f2180c002484440c10590b0343c17070340040030101100c20800043c3c00000300801c43c5041c5c0c40071900710000d000108400d01e0712100e1405018ad01c2c05001c0d1040802c0d04c032100140c880350f010100501d0b244940c4601303a01034045400d1841e00140500c0200796143d50300450b85c456460b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 521953696 1250 521952446 521952461
    0x61101060509070302072d0609061d16050402090a030f0c030615060e030d30020d05061c032c03030c0106080123040f05030f0c0309010e0406030b1803091302030a0c03 73
    0x5550321040d07c4055949500801e041841100d401d9150850b000003004e20740c0c844100302a03003501a0100035104904228071500390b81115114034414400e481d50340e2681c204e1202680d0b0f000c43c1d010250b07081c2e41018180c031026544000c1607541040645a0317002d0b00d04d21102c0456030507848900050252108054480b002841503100048400d10300301214600b1050031061a87c40060a05e5818108440002039901072001183c1e03140c0c80c1c0b81840981c1c02d116601a0142c911513199030302d030610301d507002890403441400004c0328060a03022803040c1c082050901e040080010201c907a00d00c84600c15074041d01c0c917071181d4211540f8140030781d0360440c1c000c0c10749064800103517480030040d55643d465441102549a0685036844188040050001d202c0c0052600c0c140c04001140c031501007400041198000c40c00450180f400c0410030000038200e032139055008075086410070182402001c04a1450040c041c0c0c0607030259202040b514880c405500540c050130005006101c0410801c40035416900b14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 521954946 1250 521953696 521953763
    0x1207120515240d14010f0221060310020a1e02060906010509151512040c031e03121d0706050403060f11030610030b150a02240106110106050907030207 66
    0x102d0b042c101e40d4900315000e61480b5100d0140c8003400e08001003854215a4854440008960700207180458010320204d513070010344446070304002074500040071a4540e036031480b4800c40c0e2500840e040d000180034184100d04140d8411002c9105000820000d607544401d840c6805180030b00000822a81001c04503030303100b0205028200d45407803001003480661070010403003004c03042e03007072000c413016003030354903607540a64000c480c0340013102c0c2942030111102668107440300c0c00307030510300300701c0006600203203503000a01c1c6081c03000800415440e03030601c4900d8044020700d49030107a1080803442ea40c010000d001039901900c1c2c2000350306420890740d02107170f6000305c289648160034000240780e4900f0800a9240c0e421900d000300303080b08007102203421a00030320f481100c1080c1c0429103858031a0b0420240e10405001101380000c81d407100400c420600c010700174101084487c0c6804811410709404ca100144409024200cac54076000e900200290403c2504603130741c94030000c1c3c0807660000c3c00e0b00360b54600324 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 521956196 1250 521954946 521955001
    0xf0b0109080d051303021e1c0b0601030e0c040509010204061b02060906031e0406020a0f021507390203010605060f0a0e0a350d0e1207120515 62
    0x110b44141e4a54100396481c20364000420004030050315412800b409051301c042d101e4042c900050308011060f0b01400c4580d00070f14002038020f0106036610340c1950003800c01c1c01c0000b034150300c80001500341880c82d01305c50f400504110521000c00d0055000f0300840721607039901014000000e00e071004410b070a201c0a54092000d01c01807641c0e18003c0c0007140c00141560000c09412074907400804042401c0b03c040d00c080d507010418a80d0f03241c115044641e800e206101900712903045000901480002414081c2003084039088c1841d44809048c0d400101103001c0003c43c440200120444071000b10f4060407400303542061400203140c2021001d83d19421401c24071941003050f1100e0072100785140c13014443e4040d522500008540381462000001c1c2c0410801c0f12460303000c65403d4094031401d01915044691064141c041402d07030042441d4120720382150400b5407460007040c01407500c21260400c546501d02d5000c090304101001800302c003100070076888030321250351b016002c040c1c140c076124400e0403444 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 521957446 1250 521956196 521956213
    0x3120504080a060509030702030a030e240a0807031509050412021513080f18190803040306050c04090615080f0105090705161502040f050301050c0909070c020d03030f0b010908 77
    0x150290013541d409410041160304000f0650000792070305082920a50204040c142c4070141d9003042007994502004280c0301081c5000310490021103440b604820340c04028200c40442c5d422031094001c880780c041c4a00e400701c150303522035420320000d01c800e9034211400840a042148902d00200b00013803810440440040650384521039078507000003182049588020411808401440d640083d09220901c0100341455405c51020b001120040603004525000811010440e50100000701c5056039403141000c035007510b540d440c034440345c091070b00400500e5003846c41c08a40b002441030702080000c42aa0340301c1180d01c85582c0004012828040c09400000b1b403800501b603d40254014200704ca0804d09603019070301580c9911351200441c1c00e09000385500010b00708000c8408000c040054034044008005034203000f80510500e01c502103051340200c0c101c50014032414000c1640005994010313000d20580c10151800400402210300010340ca1880c2031020002c03944034440c82d1066a0781c0342e00030a07400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 521958696 1250 521957446 521957453
    0x4050a0e1b09010312020a050a0b0702061e0105130f0c08090d05090f0105070f1407090f05060d020f13090b040b16020705150d06090e0706020d0905040b0a0302060309060103120504080a 81
    0x1711000e829982540700d51031594002840c100585c0f803103a8081c0b4054200b600300b1000090414038060004c0c14200c10300350140d82c100c0c00d80004241100e600b19800b181410284403540042e00038820400720382c82c41e0550840031150000350103480b60040c039043c0c400030750003010152858082d460345c0a410081c0301c07807800d07440e50048004084040c001d9103111a010071035a26001c00c1d0051680c0e125072904941c03800c00c90118580070300d640e081c500c031a0602007860180c2c0450f444040007540a4800c550390315105c031a9448a819040010418000600c806e00701800c140951250039103084891031404c10018500082016654412181d16409002114130f0042008554602a400a20207040070416540811902d02c1000001c00c2a12404900202c904011500707140e0b490780200b080d900071a801204003a404040e070020f0b500120340000380b228904001c5050304c10181c00003504082c0000c24442944000605241201d2040707400e0100003074030560032201c81c012841420420342c84004d121000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 521959946 1250 521958696 521958713
    0x90f0b013f0f02040221070f020c0d030e0d030509010e09091905190b01090f020c0706030e01110a0c0209010501090501020c0d0203160b030108100912080a0b04050a0e1b090103 77
    0x29503010b901140d6415109070002012130b07110410050848460355049204c0d800102c03200c5600008505008442d00c0c00c244029444c1c50180d402d01d4231411104a900c0d007014014181010b0704640504a407031000d0141c6005021940181d01c01404280544e65500320743c645480100d10804020300541640da110321051009250303203000c2250706000300d03480c0d00d01164107420020b525500035034401015526050403542140c07150340c0c0828040f8010403803001a046d00040e604119000d601d4001003542d680711815004207001c88001c13071503400c00551280e4031513001680101d600e000322000312141c2d0f0780d8401035800415900ca01805038022030007080360b501d440030f880c1000d2030015003502c9202d60048504c0d040c0c011a500b101441900c00700060190307000422600454841d00101040403560940360790b8140c10b6004650810060b1680c0000d00703402064100c2c0c2440310002d00144420b0a0042c00340b030160060758190007070b502c15039014052042c1c0314500d0034030045001e407030520b00740d0a41c1c0f9041031f03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 521961196 1250 521959946 521960069
    0x6180506040e03030c120c031005091b0a030204090b01020c0a0b0f09060d05041202060906040b070e0a030804060e0402132c040812090307022101090f0b01 68
    0x1d00030b6591403000c80c0c1d4a02800194070489415408a0361403a056001c0a00004094400504120140104001c0c014000a118143d40c4101c4803142031780c1d665024164054580e031501014542c021a0402c18650907801601c295018081b05200c0e8400d44030049984203030482031268400ca2540042000d540290010903c46480510300b91070710004002013030407544205524400203a8034000c00050000031401c01032030500c03902c00751001e400d050452a0340d8450241c800341004850f02e01245c04d40c0e0264000c0103607920041c0040201e6981c900780340800360041c0c421000401c0d02da1180124a00e030510880e500080d0b071242d4a2006402c0107048060305014a6035200c0c8015482c0001e04250341409509100354407807940a5550003d8042ca4600c4400190000843c1d50040c4115001603a620a04040c061260940024400e0307012407440d015103442640600030070440117500c0b003030007500503505050b5402c0e8040c0c0c0070311410b07440f07250000b480300c00c802d604210003074000e00e082c42e01c0106d140e40 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 521962446 1250 521961196 521961199
    0x9021527040b0904230312011503090b040b0a06080c090a0c09030b041b05180f0421020f0601081f09020a050406120308070806031b030307120909060906180506 70
    0x64001d003200228022400a60342990302181250b81c5131848100c240403001c0c5c031503002c400f5608102624400d540c068034107008a4000030400c3c02d01122640c1b01341e105032502504030151180a041900f00b01990341000d85980c2c04181c1001c10200e508500024013841c1d0050140641d412582c42901e210002d100080d0400304002000c4000008698601c0041f0f000d0390142000303402000138000221013112480d400305d1b008028003401c046901c0c045052207540032450591080c4d1655861906e01224070809542d402007014880c0041c4000d5800a2044503111071341381255016600c9021003a507a404000d40c50b000b450520183d683c0c18481e039004180c0c4144040d00828001c0c5d01c07200028203452858104001e510040c011001c14964014034842d00814a4281042c42d4180107000c0ba880310001c0c0c0300900c031800c0d40013413202c460720100201e643c100d421018002100b00070300c40c001c140ac13005100e64000f190502001003010b10092040504564103081c8030800e0500f2000c003007010749001808103 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 521963696 1250 521962446 521962451
    0x30b0402060c0106270b0d0809030a1202030705010f050408160309091b0201140c1623010c111c030c050c15060a270b120a03030902152704 61
    0x1141910000d0044030f000d460140c00c40010551841650200817241454444c5090f050510b5065540c9610580120882d0040e44d1541e070740c0301c0f0783c0101f07160211180b070090001e03111880c170f110220390202c080c0159920500081c071031501140314010540d071080d03e0103802da200c1002401c4801804c01101038880307100b810610707011681c60980b2400c46030a0401214101181d48080c0040c0b82c0c288034072560409428051101414181310700d1449009514030443c0441c06020f501c414020105840040f103250002d10300c5203e840c0002c2580600b2000703500c03801090300100903103040070010508a40c20444a041c0901c02c20006c2e50450240500b045000c00b44542000015185541408a02070032030328100d81c0003132070504600b800905601d50341f000c950203030301c000c141d402c01426961010aa076651600881d40326203440000d80508807100c7d0f9400e081c4a05070800040503050703000840d0860013150703020418504c002c0c104203240f140c403100e01c1824818201e21040a61303280075071a09000041d100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 521964946 1250 521963696 521963707
    0x1060f090819170313110409051615020712020405060f060c010903080a060b18030322051305061008251e140d0203060612010e1509010f030b040206 65
    0x180d05085801c1c2c10035410106140045090005490010041d0b20000482d280307503161410103100042c4403214002c12602590b00412003642e5113410401c0055048002d5554141145140b01043c2c96188a1401d000381d40030448d0801c18004a2040219403490f810050040b000e81e007000028040100315940c03140c0001c400036074a441d82800350007103103401800080c40b01400d09020f0005000240603c09440c00d0017000c3c00220410070558002c0c004003081c0f03000d900d41c5500046d041d80180300346408400884d0402c1c0e5220b070f440303015400c101c9030182c4003000d11241c2c02080c0c0d41a100308a640c0d07500130583d07645120445105204841c0d2100c0199400c0400400701c02c66030f003440c006041508009034403000c080c14014079030f0829100520480c02d008070040214a00b007200750080c1010080065808400141c55440341d804544004070340e09440691907850320011401c109080e2007184100261107034946917418001d05403070580702e4500e040104a0710310b03540d0845082d0020001c0303800c110103118 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 521966196 1250 521964946 521964959
    0x3080304050c03060a0b0109050409081216111b0904050c2206050a06080c0307090305100905100e060a020f1605070321050a03270c0f0504060b0301060f09 68
    0x5540101c0c440c0000c1c15441c81070408051400f04040e10601c20146458519040f60fa00b0510f00d00c1100d2003a02c02254601c00740c01c20445900035100841d40e07040901c4100004c8200410100003080610f4032100080d03c11416503668a0030f044000d0030302e00503402c031507210525100902a920900c80e00c102c81c0010000000b01d00c0c14083e010010000556032040703110b481d4010302420000c1c1806a5420380001d00d440780041c44200701030800103c0d4071000002c246010322900449000d107801c14102c86404150804850040610103403d54140c011844050903c0c02d6901034211000c10200c010700e51511154600c2000798008000280612001c20600d030400b225140101d88060250700600300b1246513042c41d2140c1045149079654a02d44225a400100d4129080d0f6219045a140020b203a114100c0b40d21203203020f40b0403174150340c1c1000781060100700011818000790340800f181d94442e10b82d18401c2c8002da881a0044500166043c401800300c940b180d110028a5001881e00f00a403070750780c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 521967446 1250 521966196 521966213
    0x3030902031c031b0c020d06021e03130317061f0201061707050108161b02270a0f060506031b090a060206010303140a02060402012001020a0216050d021507020a03 71
    0x81c2c80740b01090b1500450010310b4900303081000c0c0c940381414011906a0190b0005080002151000302a11b40c0420741214040002c1c1744242540c0d8848038030b954a0400e079031304400c00c5620100450001c0c0d03c144461030406441d16a00780100d001030907405520341c1030b0044552181441c42510210b40da5a00d00140080318040c814000150180c09440c585080100040c0340d04002003816680904008074041503d9125040324902300700d126460244030402d01c0040c440c03502000d0f2a45940d002000b04050024549501900486070303410308014411100c00f0f500107550140c8202a807100c4107100042c3d481511504e80660308801d030b14031900d010050030000300e0304102904400010703405240103004243d0044c1a014100d85140b60950409040400c020364a141c0148001d040060803442c0111a42ca12403100303000c030000b94025500d4082d0590300a588443d842d841c883c500032042000a124280b09181d1900b440e00981070003546404007044820381e0740107240898000030540400004903001c82c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 521968696 1250 521967446 521967493
    0x13051503162918040b28060f02030403150f14090111030613020a1103191e050f0c0f061306200d090606080a0807050709060609030303090203 62
    0xa000c94886603081c00703900d00e40c803909082c51078600c0d00d0303031040080c0c80c14554082d241c0b40902280840b002140410210b40900340000e203060b00104800344e4820075101c801421101d00318000c1d1801c54540c0c1d1170600301e903411000003800c00960020001400070446214650988152400001c540460040c0c1610204d640b40030b400311030810a41d06100c00045d00303010b100c5802c1110401035056040400c0001e401542403041c50035030542c00510501e065004200c01010351003080d0680f0f40b01c0c4207481900c45e140303032555000c800003980070600000000c1055000400da502072790300c00d41000e4520314030b0186a4003200203502940715801001410640c100300c0284910982040107092880915180060700c4540c3c003858040b10401c660207441454000c04d46110a40d11301c00421070141c24244940108665000039a081c0516100102030028180042000b58465411203cbd015558205641120018001c000c0000c2c0041c40410210344644c120b10609070005054608c0e82e2140c4401a8044400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 521969946 1250 521968696 521968723
    0x20a0c0902031609140d03120501080c0a0617070305090a0b04110a06020a020306060105160b0c0a171311011101020a2106050627030601031a07090513051503 69
    0x1001200e42c2c184988880c1860182003c3e070602d030402c0c103000c5c0201860302006000d6052500000305051150105a11281682808016558550b0307900c0d44c5402c2c1040c1000c0c0901e02b020000100c0038816a0410741c000700b41d030755101d032545038810210050a00640000b441c0d01c00c0500001c0454034841c07070036010307d110304484e60ba211000c00030302a44024a500a40c15504503004102c00750720041519039000000f481d040d0b64695021109907907130035074404003030044103001c0100b02103401c880000709035681c1c00d62564898030040d280d010300d81c800304032100c0b91000910f80d0320308001440c100400f00602d005050281c00494803a0031076007260000b00d039240001d920700304aa0340c4142200d61840c0354900d0080f050140a00b400003040642c800c0c0340004050f4181d07820480070422950002c181a1200202030b10f0003544d40341040100c4842c450191072010403094040b6541601400c548003c8503800350100c08075400d8016440b004260052904800364648203d1000a41c0d05001180c5506403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 521971196 1250 521969946 521969951
    0x70812100602010606080402011707021609020c19020a06030b0112051509100b0417030903030406080a060b030f01051e0a080a03081602070b070c0b030106270b0d020901020a0c09 78
    0xa07040c070003820754005034403010030b00c40302d00c0510000d80d07840621071100400041c1011503030784585104a10b0405501200c0a0390020044d020459030996001020502807400880f1145400c8991004503e14480710003035011a5451041001c40c1c000c0c0c00104007140141030071040c1444030f03002c3c1000d981d8101d07816010042c00050701d40c5a80351980042c0c1d0490f09460035480c900d03062198074850391180740502c10110702182d25000c80b8407410400c80318580c00280c241e0b0340355a80c91102810f02441a10141c05550a14a000ca041d00f10142500d1266180b15007404031a480c180a1010f0381c02a403090841c1e8080041c80001e6548410400da002450340d40c0023061991900e0400620154020304800c2d051b50748103488202040d800030701901a03d0010520907501d21191034030743d4501c161079002078241d100210000070b03413541009001d020400c44805c0d24140c018002444240030203d8007510000d01d10034010283c507500203038050311045406004907100d804003074a40c1034011000d40d1142140e185c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 521972446 1250 521971196 521971199
    0x708070201032009120c03121207030b0f10030902090708090f01050f011421070f1215020f070203010204170d091d071b0302010e0111180607081210 65
    0x141d052040410207661885032541e09544440c6040c01413090401151040c007402001c1c0380c41c800107015601e00508000c08aa01d1005515402803441e0019640c07040d95135a0400000c0c43e4901a01440c680304000800d00100c04020070f0800a48405192a01040594501511005840d82c1103164020341c12500d850364a86011994180350991898003034007140d04103403c0c03284028104041c603054403234503a5044c01400610000c15000c044152081c0345100c10140d108080300c4010585c881030340e24004982910589450681428582a000050a0a14495015084070380c5a406085a810030705842c40c50000160002401d9801c50340043e016034502000386074002100b00044520b005803130400114482c074000c6402034440e01003004240c810000c400054442c1d1081481001070040550040100e403a43d0030028001c000c084180c108a610b4110302440c0c84080c074040d1b440c0c5d4840c0c46600001c48100340244103140e00030407000c4400203004c2c09003010841c1d0492040f4865512440c0031091503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 521973696 1250 521972446 521972449
    0x150c032d0a0b0105160b130503040f0f0f0605030f2205010209040518070e061305041101120506060405120f150a05060a0506182b0c08010608190507050607080702 71
    0x44403480300b41410700c001044000c88858030045880c07910307a0000e0304400c0555901212480441e280a0010114080000c01062201c0c0307801c0905c0a80d40c00d1a03c0340101601c1d0049039607994424081d0201080c01170000403100d0f44068600f03580124000848a0907000d04441050b4120301d5040885c0d890b500801c690040d800e2610440f9400720812140c030b40b4000b5000d40080d04e9002d54040e03281c000c1030b0f68001440680340e15003c0d40018111200c1081300c0d00c3c09092140c07110b1200499071740003880408203071418070418001d2501070f81c0007e02080c44c0ca458481000510302114811003c64041c04020a002038018000e444454640701100d10f900c0c0792811040d03003112401865240f140303107443c0c070034000e50700e6032001c1e196501c2c0c030a031540c608840e031b070bc000078021622144415030034a0f14000d90051070301c6503c00d145e2103610906403007440039120710a40e82603507403070b0080e80600d5011001c0b00c40303030001400c3d0842c0200d01a2040e19001500c0d580800e505d42e20120301925221000a00182107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 521974946 1250 521973696 521973701
    0x130e010e0a0210050304030e09070504060f09080d05070c170a0c0b030403081b0d05011707080c090406020a110102180a0b0a09050f0a0e040501090212150c032d0a 71
    0x6140801601000d01c86500040c5440c18508500c003c024011001904160140d0b02d40c41d14000010100c04030f9160801b0700030300c107920501035180041c00c110f5441441c14050544031040e501201c000d48484158000c00316107940200c0b40c00d5946510190000030b8805144110500c9200d503140641510481410800031071903c907400440104410010400820341c0050184e4100e5100500c41920490215401444e4000e086a59503c5450b080c0001385081004126200e041582c0301034031400c654030820f554030340000c42a040d4000c2c0069000030000703070040d8003e105808183c2810b140307580e28a0606c60890300406c0c8106450300c005c40450390580b03131403403000005100b6101000e10302411204001c182c08034911809018025017041141c043d40c9074a01c51300544840c0c1035070f440030303c0c1c0380c28070078080c2030044416409504e1b80c280d0700501e030501140c5043c04d403031200c486107000d44071141800c41c25030004240007515595842c01a8004100b802c03401350000b0008216501c0f41080a0744004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 521976196 1250 521974946 521974961
    0x140a05060a0506041401080a060504230a0c050306040b1206011203090f2105010f02130f05120a0f020409020d0311010609060f0902030408041a1b0c0603040b15130e01 73
    0x800c190621003040714417840c1c003410a11800a20b000241c9861300301011001e00091f82081d64003c0c140f600b469201e0f09482030b00c48144001403014061901c0310100081146c500d0b120420000300304000007030490030160062640003d0140c00d40e0389503100c1e40c56060402c902178200030070580600e00c0d44001d06901c8200751010b0002d4041ca4400c0c1c030b1400644ca11060500b03001030001781c1c0030b1041d60317007480000e40c4988403c0040b680150354035050090240070544040c029204640380d00c034404107141c2400825503101001c518010003410645840e0001c94a6600408a9206890300f8100d801621550642040e840c440c0e21804001040c4006140c00d646440e04038903050740c1740036403c101e8841c05080c0401141c00205006070380c1c0e1180d0800c64203a1180340c1045000b0185a440d014002c201d110041042e11004140c04038109041c4a5460b01c80300f014981c01d910080a20200d07000c280a01c22541d001405601c0390394250544801041c0341c800e4481e0b030700c6c03010b9643e0030701a031404400b8007901a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 521977446 1250 521976196 521976199
    0x190c02030301060f051822020f090a080a12110307060c030504021804020105091207050607051f061d09031b0105010f0e0c03071119081804140609060103140a05060a05 73
    0x43c01c045c5c0b0405000415140007401d00e2241c1106402802d4030450181d1004e44050400302c00c2d51394456400890902e035210b01c5085005000c9032f0300000b405000840c468441c2540803428800035046903030120b4200c1d131480d444a411740820800c1400080ba540b146030b84490094a01240364501401042090185042415000407a2104100040c2e9101c011100402c0c0e0440c1d42000444003240c00c0c40c0307000d0341604550b0300030070009449401c4c01f10004100426008a601c850007240c030180000c026110700c0c0c03150781e10542400090b0910081c1c480c420303d50101c5840c00300c074184441d0355540e8400c01c4080c02c402080382d54640050252171240c5000310064000c1c1c042d0003000703003031089214280d40b100804000c100710580842082c00344062000882c7c24081812a0294071014204240c155014000100360f000440a480305541400c1c01804000f40d0808000384007039540d04144030744004010b1070181096951f061151382c030500c0d450708a014541d028000182c0380351210500445409980085 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 521978696 1250 521977446 521977457
    0xd0606030b0405070807080924010905160905010c080f1c051302010e0607020a0b0705031908130312021b06040204060515041406040306060312090506040f0608190c02030301060f 78
    0xc04e19070000e0030150001151f240c20381a55480c60002401d110002c050f07210341d00d603684100000101004041810707036503200790400c500d49030810700381c0402c210081c880c8041600341400f0001c40d8004c0e180c003620680034031001071a101004030401710f01c2c1c1c0040c500410500104142c54000c4825104043d8445901107800400301442d40000c1c0011084007000342c482c00d8005024411502e0754100d100091800d500544e0702c0300d16515195440f03420528030090011310483c00b4000b054172803440340f030185558010802c248456a2403c48100403100c80160169800300500d20b440880d082c2c01172446c031070660241c02241040e10401050711095400248140306040039480c648408c0c50403142151807031180940b101d0503a03c041380b00381c0981d41c0084d240910b08007001081c041c9103c1245d0990b40550f4500030156111410070485014074043e000340080c0984040c001c06000e071140907005075151412200500c494a20002a9001e65094500507000400100451904110079a01c50002410b08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 521979946 1250 521978696 521978701
    0x71e02070501020a06020f0c030406021b030a0c090507091509080f0105010506030f1b030a020301060305070f09141201020a05120f01120f021f021b030105040b07030b150d0606030b0405 81
    0x3590b541c130500018001c02c0e80011390061032a010000c49071220102801d50f030f01d60796034001c00303520b500c1d41c8182009240d00303005084659250208014001c0c1e54003c41d0700c00001d0a140002c40240310050034001072041003c004103131100303045a034064000266540140380c500307081003141004100c0b4500304290b130400006200c50364030841565400712403030fa0020b039035036901d102c040c0c54415207218006040d900081840030f0200b80e17400450503525181c42c244501e4440510440b141e40d0820201000102015428440c03042d030866241c00700140144110060b189030f511041c03ca0b48841c840c60042840015800c204030341c1c801b54250b0108034004545550740c5807020081c030200075500000c0c40c135040030404a00310f5545211696a41c45d0300000d4004525001001940d2691310103030450749001d941c8800c030301a01c0d05002da00d100b5648050201034584845034141d02030074001d0071940d4451111254409407040b910081d118100e15110085841450074802604450703403200c5540c0034600702000c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 521981196 1250 521979946 521979949
    0x9131a03070803040e0117150406050615030f040201260a05010f21030f200a140d051b0705120705040f0e03030f0a110409050a110405011d041103071e020705 69
    0x105c41c0d04403907600c4001d900c12002c00000b41d0804098219400d00c00c49014140414000140d000780d100b05002d4800754009c046c05c41009035030b80012144800d4401c0c1013000603005520514450800e00c02c01200085c1c2150a000400300701c1c02d045581520884c1c0e542c0040000400c955035960080c1403091039035200080e25007840700203207400c4402805026111441516043c070440c07024080005042d40b00c8540403403404019213401120105071120040c014120641ea200401c0c80c000e840c009464003840c00c07100c0d0348034031101280c0c048940c03080c1c002c0d280001440d880d452040d40c0511920f170b0143c05018209401c11040312207800d028400306280192180624000104498010600440304600c594656a030b91000c0c6c41a089415600c1001040020304841a07800071030162503004001c5c4000004515000b400303005e14480c40c0d0018016481a0aa00882400c0c01c40ca0b01e070064070100e0810018403003400c0ca940107030b50328400a00020b410002a07404040409100481c034809400031928100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 521982446 1250 521981196 521981219
    0x218010b030c070302071710050106051c1a2e021903030e010f06090b09390c0106030f1407031101030209010318030e011b080406030209131a0307080304 67
    0x80c60301100c01c00015804013454001c00400d8001c00d40500c01e00c0c01c1503982500382d07841c0c0c441d4800701c4070075030f0500001007156030041090316100300881401c00e444482071103032203001d0b21a61002c8031000301001130307210b050303140c0c2100f1115400841d14060110066124546003070f4040880303d500315000100321540c80b0311f0000d00b02c840da540620300804c0c007032180800c1500405810301540c0400345000310000315202c40d41c11030284a9402c0301d41326100e541d400e81074040c080300310000d001c0c80c0b400d00c1015666400c282035501d80f11134544003414200b04070f2082c4242105d40a80090301e40096800c07402d0200b081c6103240c41d001500d043d01a0440a146540d00c541e0780000c42d040314140358003c903403148964401c0c0c2c09440f40a4113200340040e035840ca800c000c3c00c2d5200c804101c9001070f00410207034014032201c503480d070200355000c4d152501d054036025088000307410200034513510140c0004040003200281c05080c3c1d480910b21311151141c4101c00800d440c0034501d5120f512182c0003440200f2500c00b011 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 521983696 1250 521982446 521982451
    0x8210f04080c010b090a1d0102090312070c0902030405010504020a05040903020d030c0c0f1101080903042403020903012d0b03191703010b030106170c07170d0e0a0218010b03 76
    0x4558242c07500c00c0101124090440c2c1803805410a04080410440c11020b40120504646641c244041120804c450701e09038480d14010681681c003001d91036201007400030092007154042c104500c0c403076403100f10380c40680c3c1c0b09440c01d8a0342c0c0e442d40144415890400c0d14080200b800300c074100031081041d80c001c1d44441d0004113400a05580310600c0303103120b01800c43c0a0245521007104511400b052030048614007400c40028000b407101c80008001d504004100d6090340c2d564440c0308503825243c2400c076084605560b030401010303024462426103480900544954070b0b03180c1d220171400c03602000705440d0403021244c200031007410101d1225854402040c44466140007000c1d0290000c801d051000c0300c42d50416070380442a000000009201003401c02031070603501c140c0d80b04a0b151240c0c0c2038440240031306840100c0c0c0303028100840e00001d44040540e4800240280d40c950034071b0080075aa104882036400762070801e030814500e60085140001030140000700a0018456075410800300c80c001c6e0100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 521984946 1250 521983696 521983703
    0xc1c02010e0907030618150501140f0c1606050d0b010306050f01052101030302062a030105060a09031e1407060f0f020f1e01050a0b100c02010c02040908210f04 70
    0x302c01180540d8880d400502c041d1104d030642c1806100c1c2c2d00110305c000d00404890480c40802900c001c28103600c03c40d40380c5018000889194200002c0151441860740800088040c074402c461141034500c030040350300802420070303031141a1119880124001074424400401d4109494a482803040783d13117040c840201c075002840c0c800d4442c00e14003201c0d10304241940c0808040348a8600000415900082c090301c82c1540d40880807840201e1000c1040513480c0d110b0708000040d091005008508000700540031406035440c210001a541c1e41303e8203c0c4602507009044c4107400d2145840c1400052000c40a0120003140141032003841c00030010002040070303034850100103900160b020a28400c128003a10150040255003c2015400c01021100c48080500d6041c0d42446c000400e03a605e940300d40c004901002e00310000c225200d900071110310100e40d501701e050000c0c801c4c6840260301d03188195080c007441440e5103a070f0f8081c10110702d9003540c41c0c442080f201d1440c00041150001c1d41e009142c2d0000ea1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 521986196 1250 521984946 521984959
    0xf07020706141204050a0312020c0304050d032016082113080d030b0906011826010f0c0e03030c07030201030504062d18050717011803020c1c02010e 65
    0x42c41c060381010344500c0070035140e049020700910041c02000300e421883d1911076100c0c4000b46290009400c143d0044e001d411740c203500b003400100304a05050b150f403008141300307242100342c80d0602e5800140782c06600c0c1c21001c0541c090300e604c83c000c801c10400d240141002c2401011400d010001d11104040200e060943c0d402e8080f0748401c54102c140b09050262407040181c03030030403007041c000400802a90b61130301e1103043c4440c0071070469401010400c0700564030408807a00c1c0c0b4104002da201143c604c011352542034035480c850785180002803140c5900102c06080118103000104401001c45400b10310b043e203e070b0000c0244c04194100007884900712035080c00c000c030301ea582d14100403004004140c0ea0318801040398004802e48a160b007d0301c071003055403007420440e01c40f2070006a00c482c5001800104158011402404031140d4224009080c03c142d400115181c09400108407016002810132000360b8000b01000000c0c1c80c20f5140c2c42a02403002c030140c0d681d000c9079000280301d041018002406000e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 521987446 1250 521986196 521986217
    0x40b0a0503030d021b0f030307020106090e0303040b061306080f10152102060a020d031d070b162a060206130f02131104030b060a0506030412170712050f07020706 71
    0x9955000e00c1710b0102100040e54042c0c420003404a03203950044030040015440c041d40415009150700c100001e846882c0010760859445540e52840c00e0701c0500b55651102c08000c2d05c13841c3c142207003e07030000307484100042c05c0307420034102c00149464010380e44114a80e003440740340c06032841d03403070003c0c0d04076110044044602d40f540e807a004030400010001075004040083e2585405030001000d0001c02103079542005400c69034004810910480c01501a0b15004804100522200100900001100341c400024983c0c69603881c400300c0c500c0c1645050307419a40ea41e80000103d400401c0c20001d019a00162641e8507080c0103d209103116a0002040001c050b4283d40c15529258200c1c3d03d500c0c4094001c008001f00c40c006140560850f00c01140c600b000e00000031540d04108440304c0440d0300150126046443d02c0d56092445105001c0842c104003070183e01d402d0004003c003040e401071105803616035000c0074408100083e540f00401110b02c0a07861000d0100b0031303500043e00003c0f2200d5280298884 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 521988696 1250 521987446 521987467
    0xc070302121c2007060806130c1d01140406020606030d020714010f0507120801090b010c0f06050912030a1a0f030a0212010e10060e090601030308011202040204050d060b040b0a0503030d02 82
    0xf81001c050455215142c0041445500001741601621041307501c1440b01e60184480341c1650300c61070000c40001c90300d40003440c00c12041d030041d41144005040600319881d81c29980860f540165000d031005a01507024000203007001d101c640800030103840602a01c904080e0345031f40e0004000c24a504205a8400c49142c80b803158089c0c5001561110701d088911741c403151300801310982801646001071401c00b0402e00d960080b8400790707403207034010140c03414201c1549070400100001000c100c038601030200e06e030800819200040d48a01900800015a80382c4185400403100c070841205015010b0702e0490f079100e590000f01c001826504803441c5404070f0400341c081d409403001c030208610521504070841480c1c2500d8000c0c000f0b81e100c2420104d590390794071310300300d80e5110280702c0900481c5481005100744c1000399281e00b0b5242c0040c0001d45400d5540d0301103112801d9030082507940a81c4c4404031003140c41d20740a600d640990840710702d55114140ba00081c0c482c0720361103501e541240d00040000340c0c2c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 521989946 1250 521988696 521988737
    0x12050a020607031709150109020403031e031d010510140d0b0a06090c0903051506060307121503030e100203091c113a0f020402130b0c070302121c 64
    0x8042c500101310a07400c102c100980e40d00c484515040303400b04254000300c0e80c40f813a4402d4a04481c0c150f17940c4100c4540d44e11083c0f030409005450030b81050348682c0810501e00820100070f6040c500180002114074285901d1600c6c8140c030b070007202c0c0c0c0003508044401c43d40c0e9000544d0403440c2e0001c0e10003006885070341c0840c0080070950300c10b01410703081c180381e040d0300c0d508521410f003201c4c00340d81901e5403180c0010701d00500400440716654048001d1010030b0300c640c8641ca80b00f445007208a000100d00c090400b284c15504143d6004800080403c04460390601300b0b21014840e200080c0025400d002c08600042c0b003d0710519032035078030b00329030700030b224140450449400d22500015084440480d911000c05441000d0803101da4428808503804407040307401c902c550680b0542090742e04543c00c0c100e908010296114582c20780c00034030120400304659100100504030010454010544c9030316501c1403011001e24012071074220342240f04800909000100140540c1a0502d001124400b40002c0c4400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 521991196 1250 521989946 521989967
    0xd090501051e06270408070510020316020105060108010b09040b06070f1b0b1218070803130803030c2a030a020c010813120f050c0109050a060612050a02060703 70
    0x14a60900040c060a030b488100b040c034108055402896195407090180090681405025412010800d00c40102c1e10102460550454441c0d8031041c900903058860301d20f462170443c0300c1e010055000082c04480002407290309080700703281c0001d005074500400082c02499052161114540001070301c0030b800d98075540850503074100105000d45401e50b070700b000d03580c001780410100c840e10340409900440f020150300c210221510ba50099103400000e0000004405000c0c01d1020345950071a000b801d00b440c140203400c040d02c402e40046868007000025580314400e60b500c445081e420030030511a9440e0039000f02c800144010140c800100c4407001a0700c4101529001c0703000a010108200038030960100c1c148000c505c00340d1346c545071900c400311101410200380700000c00020a0103641102c090160300d801b86207120504001c4e0504801b20211800c0d0307400c9441c119400e4001c3c44060702003002d5442110040c01040c082989140b0719a1b640564840d03c40c10040c2c8989000f0402d5000c16214000313041 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 521992446 1250 521991196 521991203
    0x5130504110406110703050d050a0e040507080405071401120b1512042303090405040c121a1003080f07081308010c020705040b0a050913050f0304230a0b0d09 69
    0x1c1100c0781d850a807103094102e8040c1800080d44840c11100d001000940e10041e41d4205001c4c0480e007444c1c130340a030b0f51035000c0703161113060050300b00481115581c0ca2088a00c500d107140c0f15040c0900d00707881c100e810980039412030801c13140307624100701942e640004000c146100c8803e0005103c1c01c807000103911825850201c00c2c171300e000010000c0d0341551140c09540218461507a94110703820000c800c10481c00d1a82030840302e68024403500c0e0750307481c2980129800a0203800600b008549a201d44003010300f00344400d840503840300c040c420a1200d410324841c0c0c0051018107219405040d83d582240354811076609100d51540840c0c0302060000200c100c1c3c8804914079070001c4070544d515001c2c0c3c064800410000c0250166050000302e5081c075014018031403000400c0414850f09002c01c0000032a4003a002e0080d1380001501240010410898404c400500c14011a02c2c1d521340280c3c3c040ba00714061440ba92074001444210554450940354010f80c0c06107800181c8480b102420341008014403540134 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 521993696 1250 521992446 521992451
    0x18061704060f06150e010302031303180305011112010f0605160c080d0905040b0d02060318150718240f031b0906030b150405060903120a170703091205130504 69
    0x45035507030104e0b00c4140302c013142c686400c400c07103500040d01240022600551035403007407140c440019204148040c40003401143e00c3e03600580740d4468608450143c0c1c1a40d8613910000340b5941000c0f06840024010718111041c41c02c7c450411740001c21500961080070120b840c0060f07602e04004500480c00081e201e140d0840f80380b0305140400801c885032078819540680e1500c044003c0b6403c15600d1188a0340e00030702120720b951204d40c4801d0350301284d90f102c0411400b03207841103100c1c0c9d81d58400c0140a007050340d580c0303084a20005014510359405602c2103402004c80c070740104501c03030f841c81103691041c41401c090f601c1914001003a009417180218013000d00c20700700100490560003840d01021b03251a03a83c00c001400c0c0d00400c0c44003801702c2500b00d150750170003480200481c5c80d000e4020003206030702400340c0e8042c050301005402035421003a6120003040c0b200342141c4403501005c204541c00010791805000020b0710f80c5400145040c1c031111a403c229001480030082c0b0354092130b690040802a004 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 521994946 1250 521993696 521993699
    0x2701060810022a03210f0c1c0f02070c05010801152307120801080c0d08070501140f04051c270b0c21040605040b21010b0a18061704060f06 61
    0x31183c41e076200d800c080c510344d8212803410441c0031181791003501c91101c4000011940d00c0e40d403410103258001003060303220358038460041002103019002d601244d40d50a40c01580f0b40c0c84601c0d0400d03030385045800060401c12120010811036590103140c0c0000213079400c0445a4a030f1212040e4112940c15810303910b0301e03600184010810260300400071100ca8240c0d03030b110403640c80d6180151144010300019621070001070071400410f000c2001080c0152003100005600d1050107910100700d001102c6000c4450324076001c00060000c240f201e0040d00c0f6142c650b06500c8415018050300c1500000c0c1506d17580c3c403c05000043c2d601621200c000035000d024959511007822009003955104004000f0543c0b80d1101d0042c08a00c50740b00a480950f4071986981341403e0600e105865990000c400c902c019440d101058005821014401030107002d00f42c141a60320b940f901c0b405445200740108110040c26204400c20201341e125601c030450405001018030381e82c6460401401808010000841013458482c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 521996196 1250 521994946 521995027
    0x1050c070e041104021b0606090c090103020310050a030f030e09011206020c0a170a02010b09010506030f0903070c1212170112030e12060103021903150b0315270106081002 75
    0x8448000c4079052017211f0f0541c0ea0801804075509050303620242e105800c2c04070750400d40c000d40103554080d5610310460b4000b0307950400145a21415401030f554030b220140000103040e03105501c803100b0a41501c0141407545010301c0d000a5020903000034110550208403404004014421300b01025005800c80040840304021005584d000f00000780140d071900440350050700300011094100c4030000c0505003550750700c0a85400b10b040c01030108031280002c2144000082c0c010800c01c011f80061400d618001d4040c0c43e0889047c2514281c60091000d02443c459560002151150641e122120151001c14051034140d58142548030707101c4e8890322a501e20790070401c0004060b03040740d0003111900c0c0c0082495841ca80c01e1000c81c0005081c220f0741015030460042c0d00e030840b02c949200901107482d41034140110350307a07108050300e40ca400d80c045030050101808001d001074600681c03000c020004c040c40c1a02095840303035000040c0030f84540105180416101c960190f800d0b00407101c00c010b030845c0c230064 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 521997446 1250 521996196 521996227
    0x70609121415061c020d03031d070b07032a030e0103022104060513120c29060f04021201140406080706030c0f03180f060221060a0501050c070e04110402 67
    0x20f805070f01415100702c1d072030000c103101000420100d07000b03844d0003c10761060301e08030094a650080000c45109101c00858060410001c2030020151700c40c00a448072000d00d4001d1005030441001890300d01c0050344441481c841700700b00c4500a80c14106405652200c01c01600a8051030308864600207007020f10b180300c2c00c040740c4d0003441144940010021950382804008280e00c01d400050f008020800141c840f540c02805950041d50181c51010500003203094000d04070421402035814508a4a091003018140301c03440200b084400c48056041c0b2484034501050f084052050841c0c40a8454000d0955221170740a00d002d031202809480c112030712610050041d00a040641001601003c00130300498420301c2102500d0301100039141c082c50060701e071071926460054065407460340c20400300c10f0344101207051225100c10140380c0b49003850305008100a43c400c1394041e40c103000d010080043c82c141d000c41da41e02520b19404091400792900e003000601640f44041c0e55421500c0080c0000c1a9034910 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 521998696 1250 521997446 521997451
    0xf0c040c08071d19050a091401090c02030412030509010206010806070203340305070c050103140708040204110c0f15090712150204090902040b04090305030c070f1a040c0602070609121415 82
    0x1e40c6c440d01c240e40d503006050103c590501000e0210000900140008409600101d2100000b441200e043c84c0e101e0b001c019840505800450108500040341030341c558044c8401e50050043c10043e00003807419a801a40301c1c030561403804ca2524180b100300301400100c43c03442a41c02404000c031103985805107406000e9a009007001d403485070003407100041c00d40c480e001e0400074030414085801181c0701e00038103685011024004980c81600d03038206109100440018069042d03444004044844c981b1440c6410f1030614040c507440d1901a200300540101d00041290440f02c525030203200e80762050910510b100c044082040d292170001400150000c1903030040c800190007181c08014140280c01080102c0d41003c2d0000d000c81c00174400a100300c10040c1c003404200d405443d050b40220300795521502100300401164031803078285c00c01d000a011803144104003402c481d000401d42d00e410041c010304415440c2c403da40686085029910405c01c03090071100c0104054421160780381a000400911003004 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 521999946 1250 521998696 521998699
    0x100e030f07170f0105130204092a1d0405030a0804022710080d020601060e13110c12030403080402060304084b0301170c030d020f0c040c08071d1905 65
    0x400a10f81550441031149038080c45020424160032403469007440082c092204051f6002c05558101c8640781c0c1c02130380d0402d10f070020043d449040c90304041210400d0440c8400140b03444200700108000514004100e400d00e10050801195550f154400602085400304c00703c41741030f03240342d19042003c0982118a0086c141045c0d1500b03072a440ba461a1b58800100c915000160710080c01080b1050041f0340b804441c09000d40000004030344e810b1540184c4e681002461003ca0740015200c164030400e1000d034080360300c0e0032005407071814070b07403002402c0c08806440603100f640000003007010048100102c1c2c0e54031080b034403030104010400d000e0108000c82022008500c13000c058009c80b11003507946808444059034000242945d007021000c0c074811900c2d403603540241c850191040c60380d903010010030f081070040e1740c020f24244040704400c03030030400c0d015041d500590610502c0b82c1600d4005c10284d82c00020752504840440e90070b10a403945070703100c04c0602c0e00304081c0300c4801a5640f2100881094600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 522001196 1250 521999946 521999953
    0x3051e01140405031902010e0102040f0e0106050405030d030c0e0d060506010e061c0b0d0204050108160f0311010e0f1e0301051807170106051504090e0c100e030f0717 73
    0x2041c070520180482120020019041048100d50050303120200d181c4910300b920000601340c03990000e441c2281d001c0d400c44c030f801c0c03401d90a04000c62a040000785015000522f002801c1c140b804020950b9000182c00070414583c5908441c00c10754032610741c035100b4140040c100c420001060410b4002070000360f030854002054080f4140301410b2040c00c80d071203543c01000c0c003940300ca080c5034110000c049c030140955004440600d4500941d8aa00481d4060110680581000040e2082010a2400700d43c42107003070104040b010404190103040301040b0200078200803d014100d0800201004810000aa44614481c0f0156001664050038141240064000b0880f0b520b0703640ca002001d446603015400c0c43c0d40180340c1809141d030b12000010421894a0010a101e03881c0c40c002040c0340340c407040400c50010301140400076581d80c1e004005400324040302a00c880d400c46e1020410f000101c42e00b00050010f48070703998500d51001c02052902e03904020580340c80313039207803100c4460000c1d070303081400314521 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 522002446 1250 522001196 522001211
    0x1e05191523030711060402100e060405060304030509010206070f02030706180507150210090c170a200a12111e0a0e07090f0609150306080d02010b12010c081b0403051e01 74
    0x10000590321b004503001859a080c01c03001801c1202e00200782c00301250000414000040d558a404016501541c400d0701d900303807505010300009140c1100185282d0402c00c84540128445401104860485401c2500032842c0c0e48a032404610b4030308070000080c043d22036641e0000d0100c007041b2054a500810b03038251581c40f80d8030740b400700035a40105006001301e104800100400d01e58480300e032006036a984144c44030380520391140900741c0d603a035034029510942c20340601c07440d00d0a00304203400b400810150440b401129258240d90317180c07201e801c60190003080c0c180c07072072130101d4070211a440000602c540301040d12032119000000c0103844101c08100c90031320100c3c001c480140c0540580310241e40d1a04010b00c0c0c80041c2000c40c000211107001c0c566144004180f070941880b484c84000c40c0c5800106101e401078060000c4c9401c1c0404080c95039141c036840c4415280d120543c01c1d00b11105403c0881a5032034096065200d1080b58002400d078403c00a441d81d030486141c1480d209040000020000c24 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 522003696 1250 522002446 522002477
    0x80a05070f0f051804020f0a0303020f0d0521060102100906061805060310051021020910052d060a08010f240315050a1e051915230307 59
    0x6014002e8a0740403944000c500051301e9031150142d4440c0c00244010080e40c038803004511118002c1c1c10680c0142c00a0702450340044040101c81c032082d40d50b1804515003070395041c41410000700b40b845030801c40c240b00045141c0e41e200304040c90101440c45404c004240451414a00800041c4259032101003504c080b81344010582c890a07100340c0014001c2c201c90344a221040c0c008040003002c50300c1d03e4040c00008a03180d01c0403422070806014030340902c401031030076004102801000520002032802032107000d00c00c0d071b2104400b071841c84040128511100c00c10441c0141c94170100b041d583d80088020034122480c23503003e80558101d8410303920b50307800c164a440700602254506034036060550018000411491710a901400a1081072590402010f232038000180058419501030305a00d0701c001034123140f4441084410b80200000c49402c1d2042d45040c52520390302c007440c0f00d80d80c500c003010009900024000c0300c500707607181404206030b44401041d580010300c1e60026501640081c2047d0b20b2800c64 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 522004946 1250 522003696 522003719
    0x10c091203020a0b040c030b100302010318050d1b140d0909110306010c1a19060519050d0503040b03010816080d090905090703050105041a0603030f0403080a0504080a05070f 76
    0x240da4042d4040c000c0218140c48a114602d00a40b049440301005c0c0c0c0d0000202d1088080701e40a52441d0001c0c50f90705103140001429102c441030002c0e42486e80418443c005400020000301080c03490801081c520251b21160400302e00d04140581003506d5200310082d11500402d001c038544809840c0d40d845552070f01840d008072281c0b100d00e19070b0443c3c00c20114210758010300070032010380e22450b004e0090b05207081c0c05c42c0358a0070594a80d40d4800c400031808401403090b0185001038070081e28265588000c299211584441904c145805400703840051800d0050a104a8020f801c84184c80d80e0b803544e603408844d9070b0302900c40c0c55502900030350102158516020543e480c45101550700d48200742e08201c01c41c401044050320b0030485208065000000880030b005941c03269008078954000400c60075074080c80120020700545c13181d0001c200603d0120030b0745050754140c2e81c0062105403900a0841d050380d030b51185070002c0b40d66224031055401080000a000d4054500c4000c5140075580d49020403400c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 522006196 1250 522004946 522004979
    0x10e030c0616020109062c310e010b0d1704030b130302060c0903100b01032c10061503020307020c06030906090c010801080a020d06060b0f1b0c0105040302010e0120010c09 75
    0x140103a01441080c15a0290041e070b481c1007000340704540b00d40350031041c048c0300d2214012407000d415491703c1c1d080840c01644111010100d107a40280106018400002c40e6101c44042c01000c21005c0745c1409640f803816419140603541c000400c3d44d00f82401649000032040c40203045005124400000c1e4002d003800e415141c04550241c024010410b1038622400a06103002000d41050f0b583c1c01d00260703600e26122090030101179000b035045106081c48003e402c160300c6500c0300c0d03540fa04101c1e040000d0240fa02c864420300019250058403600c13460b00884c100700c44400c0403580706e0008002c2c8001048041030041c014200b001c2282c032284200e01c01924241001d1040c06026003180c01801c000d401c0803001c3c904981e129007000201c85480c0c01c202d002e1500480b400403000a00800c1c031038808c0081841483d24017800800506641200c0800241280b20358000203040250075442c2c0318059002d90f03905500070500f000926883c60941d10383da4000c2c0079505440c1c001800d005000035528400d20100c5a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 522007446 1250 522006196 522006227
    0x901120f02070c32060706090506100303031109010807080924060405060103150504020a0e06130614070c09021b011b0207060512180a12120b041505010e030c061602010906 75
    0x219042108007001001e400c002001e90751f070b50b00e0f41801c2001880030b0016512418a50409840c85821030500808031100e0641100d1410010403601c07586a81046031142c0c04446440c0c0300c5c8440e590040707054107040e41201140517031a8206200c00401c41030060141c4250303005d903020000c41e42c488004505031900b404600c0c840e03c001b0703030302441181080e80007808070203a1030401100300c41c1a03030089102a48503002c580d0300885140f000707025956100f41c110000640015825040c102c480d12441c4400b42c15126040300b090b80015030180812480e03190148401544000300302c0000c1e030701221942002c04e01c400c1c1c0d0050045ca600458680e00580a0b99080540c4907180c0d00c0c02e5640b0800c910454011003840655480b41e6510400009d40d00c0388172540c0a44240d860940c0380070320b550002d054611075100b0600c03d030304000400c2041d551580805086a07000d19203107010300980c001290504029000003900440006032034140d810703106015404030f80c401c0e66403260996071407034110340c440e00c1c040000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 522008696 1250 522007446 522007529
    0x180203060d03050c0a05060c030406061706060409030c020d031829030702010e061305070b0c1c092102120105061c0809040e06070206070e060901120f02070c 69
    0x6000b10384100050300c0b16201400413181c00070a661100b038942617085464100900000040004102e56405014001e010541c51103903d00742d541d1050303884040042030f46014607612803050741403510940c0381d40c001c01c0c2c002d000340f0000d12840c00c0052035501c00d0319098540c0c001d1450002184c0101040f081001910308404040380c440c261004113480c2d0001c3c00340c03411592134480d0744401e81d5040c04802c0c040d115001c20741c2c0d00c5807042d203403160074079416070b00c1b84602c0c4105004440648001244500c28150840e50708444c0040d40d00040d40c40c100707503030032404102022014020950a0320003030402040d0089591034005e10322520000d00ba0b80b0f04a800303d42006485000c03001c2039900c0e080031500070748a5400e5500306001c50b80458200e580d00034084031181d10000a1084030f42d014842d03141c021100c0e02e0840341c1c0919074070101c0e0381c601c522a941410450800a12a00050b26030b000d203d075040c00450565542c11941804200d0100c540901401141c0c401c40d42440c0400a000c4a485e201d07081014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 522009946 1250 522008696 522008719
    0xc07150c080d020c030f0c060a0c090509070908061303080906061c0602071b0501110703050d12181a012c04050313061d0402070804051504080607080118020306 70
    0x7058550381081c0c411454041d004d0060303440d1001c003032010300021250104601d40307a00300d4003000780c90300328054545145986440c044c0d044e000e0b8407542d80401c0e51740030386201781c540d10768200c1210540c00580c4031f420a409240d00f8070965401032607101802c140280d0716207405403204080aa1a20000d0321500d500c14908241b003200c200c02c0f464807c2040d80120801401c080310b513102d200c1b4285490004524000300c041c02405030b5a00180e00e40f036110714040c010041281150b5440f40d503542c0030800c40b010710280410300310042c002604824800403254130a82c0740ca407d07515201c00608e003481c580c403c07001b01501c00400d00001d2403020070034403854020000d20f0358000103915440300c0341c0540161000c3c0800c000450220403003020242c010a92961856a2650400e211012218200741894880c0e801040681d009c80e075034906a900790380c001c991000401143c9103110700107219940c000005401100b003007104242d04981704074100c45a40e01040c042a2401110a0881c031040300c442e580080400070 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 522011196 1250 522009946 522009953
    0x10c0915082401050d09030e13090515060d0f080a0801080f070306020a03181a0105030a03090e221b05101b080d36050a1101170a020c07150c 62
    0x401040b10364042c1041c625100600c2d0302c64080d40e030285025030200b05413031120034180c20902034540824856407000c002545d455900d042d02d41d0144408031184141300d0380440c050341c1c0d41e41e401c804125071041341c51010740a00e25012171281c009030303180004038450b04000583e904020560240d030030030407805032103554195500d1000a40180d4460410550348403880c070340126005d4100c410142c041d4108000d86034400f07001c140b018070140c200c68060340014441c070001030303080fa203660141d55001c0050f40c80b5036500c0e4800e1010b0104403649a21540c4400e040400340a200c84104807140403401c40b42007030680303443c01e001c00d1000c0000540c00180c00002501c0704d07403042c00d1144404e02d00c07400070581380400070752088082c1c070700258100100300c000e86c004404170080c0702065010b1132030800c0794110440982e21819100c0348803403030107000f05946003514080303a0f2250808c41070040d0003185411b26400e222028000a412001c0017030540d22440070007144402107090f1440c0f00e80100d59825031044440e45c1c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 522012446 1250 522011196 522011251
    0xf05070501060902180909030f180f0d03170c030402061c09061a03010b0f03031c0b040213060e0901080d030c022a190e0402060912010c091508 63
    0x40d036140d580d941010a040fa074a000400c407043c501c060014104074100100319248170050700c8a02c407640101f00201e450f90301c2d035003910b80b101c920b41c18105024895001044200c12070080d100d81c0200c51301002c1081581101003038101d240603800e860f1aa50b1034000310511480141c502a6000a043c0007091315504c5001c441603203180304a00c0821441855610101644d035005515592584020130765601814244100c0c020401e003110b0381c1c0d160440482c08130341c482c460306450a01610007809500200380c041e80100c0301101000e401150303184901c2c22800c0c4008628051540000c003500ea1300c10103807920b0b00107281643c0c800d001400748103104502c00e0b0001c0010044070401e45c00354650f91418910000512044507094004141d00d01001e0003c204009800c400302c101c4207a10000113020000d200b003099980164142c5419a0b600b012030002140142268140b0b2043d60078000707159981c1e0341c00440c031400c890040c1240040306110350801d03256000110783c0008503410440d0f16a81c00003455 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 522013696 1250 522012446 522012457
    0x301030c141e01030902100203031801060f210c08060103020111060405101d01110d0510030f030305060d062d0902010c080d06030c060309020a0609030f03030b0609120c1f0f05 77
    0x14140042d40e40c4643c6d003c0342c440b1542010800150b0030110400c5161141c0d01c10705619425501c0003007000906000355050b8141240c05a00c3c409081114641d0281c004240202c0850785c101c900c507064140c1d01c0040355a0748209000490002d03441e01c0032501404800200c85001c1c5500001900c583c91050000c10000c01104589031000b80ca90132800003417860a2140091410018605582d01c00300382c401401510800341c824007082118103c104003250f9070083e143e405075410302c4c020030580c0300ca800103800141c0103003001d0907062a00141c20b54030780d40c0e4a40000043c0819030411101e5070590604811118205800b90101e4140006500003802c800003c1400403007241001440313a8803920342005244182c0c0080000c2550b9404036425032901c41183d07401000070745884600c10782143d0b9091548100300200a040c10344800181c100f513602c0d03c00340c61071014003905885041083c0304500740d8038003008014034082c0e1440e12259040d808500320309116061140c403a680c00408a47c41102d259021 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 522014946 1250 522013696 522013699
    0x30c05040b03060d020a05130614090702070315060b0f0306030606060c0d200a1b09051006030f06080d020a0308060315040308070e09070903123605090109020301030c141e 75
    0x40f07800100d41590b238500c50704120501c00a00044072400c049005c4082848840158443c90040040000f2142d000503041c040d00d601c42000024030204085001c05809690001c0e810f40380c020407804070506c1750760f0195100c1d00e01182120301c544c0701e40050204038440c92501401c1ca40044c00200400c5000d0000d0301e841c0b030703119200440a054100840f50400c8241e400841e400c20102540740d12080010000d140500050718040049041940740000b000c58a84210002e054541405014940e11a84401c0051a030202a41c09903d6114002911605000d400714041010140800c00e42d0800041100d141300300b00300e0070100b0f602c0e5902c0680d82e10100a10180030030810907815110b03500d039880442c1c083c4165458200e99203095113041c5034071014903c418010070100c0020b00b82c8004a14010030440076092000c8a840c06030301212003003400302c0d41c0155030030080b035000003c1c040c202a0300a5040349c0c01540411440c0740c81c1c050001c002c07003e400345a41d10045400344520a6000100c01e039404000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 522016196 1250 522014946 522014959
    0x10092303070f08190f1205070513030c2c1f170a11030628060801020c0703140601060e061b151603090515091203010b0703030c05040b03060d02 63
    0x5469a070011808a40311007210b41a4001c50b5000350400000f484c0a0070301c44038285480d6003122500010030402c0421940204140c0b102c012400c0e1030f01410444000a0052641018141e00c9040c188029003441c800c00001224158925403030041000303001101c1610300143c106c3c80d80320701503155140e0303400c0da00f0780c0445012460700041c0c04180410441e44a94000d000e0032074000c03d030904001e080501c030030346070180c0c0183c41044a0320780c0b030101d5017921951103000d156080c02c5411150004240c2d070380010000b51b10025903c04011070015074030f800c8911030140351018900e03c0585584071003081c424000405d00c100d140030300350b10340180030b0403004c0c0369402e0180b0a005c5100f0028078103090401c8052804039140184050b4034040071641400035080d00b014001000789689242e9aa00701803002c00900e005103001c144645014400c240395504000c0c01d03d030300ca585034442c0c080103903c07401e0120b0100b454411701050036800b500139241100e55403103a00b82969610811700402070f01c2900c08a03070045 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 522017446 1250 522016196 522016207
    0xb090d260a110a02010c17041a090c04150f0b210703020d06030809130e070306021602090c030a0e070b25170d05060a0b0a0f0c0f030804030210092303 66
    0x5444000c0c3c01d00f01030b00e5001041e5141d42d100058000da2209421080220914003040041214240c3d401411b402e6003034022400d50354003881a003003240c0440c00da54410f0a040f1112802015412024155a52203500740401ca9480c48803050902c41c2c00500b4899001000d0f0002c00e03180b1010420364081d0f5a170270050302d8030503a02c840400b103031041d4104032041c52020500310020704120464000d10b0b60085410080341e20402a0305a40b00c00501c801001c041d000038548441454000c1c800f12007990140c1941590309102e4400c4905c1c0c0c0044071001542440c0c030303203068000800013541034119501005054030b06015031076645541a0003000381d41982c40c05141c414001901010000850078601d00619102c00da941d600400f40c1d10b014014030b119442d200010700101d1039000c02c41c0e0580340c06007000368030344584800130384480b003da560113080d07030020311980424190488690743c4107a02c650301740d40c0c0c0e1a2a5925510071034289500203024a04215030300020700c000904624000100c0740c04480c20721 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 522018696 1250 522017446 522017471
    0x219050a0602031e06010c0c0915030b070201050108122718070e0102070e0c0d1e0c1808010e100f0b0a090e0601151b0606050306040b090d260a 63
    0x243e1042c0c83c2c2c04526419408000d03822410081c443c3d4001d1024030303040c0d0703403c0c0c0360340c0b100e20503200e003030003a18060755403269400f40c8805041000c0c0029a800f1100e2515031511100280c020302d400d11510106002e1917901c40c0001d580041107480c424680e00400103044200102040c201c0b59403d480ca800851840c3c1c0100c6810140807154403803405540d891030a030151200082c00c1c0030582d44000d215442c1942840383c6410800207507100966200e9001400b801268050940b04000c0940405614a40041c802903a6031240419043c221500840d1124503942c2d0075942c202ca410029840f100d40101c10501030805560b00044400000680003142a8001d41c2c001100c09803d584141089551900c5030200c901060092600500107149482100381d0503100150003481d803480d024000c10000c05940302000829845500a040c0180031a041e500c0e1510b04445141d074203030343c0f0818903c10b03000c82c0ca01e40d83c422001c610b14003100681111112442d42c03500c510200009c0d200f080c0e141d0700e801410700d64 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 522019946 1250 522018696 522018701
    0x30f080a0309050f30120901090c0303091d0c0a0c050f01060b0405040f0b0619020111030705031b0405010e0d022e120605061b01240608090d0219050a06 67
    0x29003d85501400c81c01200404828002c40d1050070050008070814910104000c12401d44082d89102506c03400c0b03d58410354054010900d842000700303001e031103007004401e1652140340c1500345c8048020450500c06100111510010f040b100d000e00d1000400011680a1007001103108040c807900c100d8180c10910100c1c903080d26002c0d040050200c0020504008034541401446600e10540c00c0c10030001c00c0c0305010840c148140c8541d141004280502c60362507138400d502c0304030414035503074000d0b843e03003450200100a6482a10390715045a00b480e44828098480000c880c01c588050311960b000018082c240b212160081f041641d12162122411850172403c914180d51568144c0c50424541c8507290082c0880000b500d203480480c2c0303001c00600940d21400115170a108603894540500da0785a44e40030701420400d24900700f00c0041000c21003a61a2600018068408580b1604400d0791980c0c0442c0d543c41d00a6084c0005a1003e00465070403903451381c124840c58010400c2e03441e240240e480e018203 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 522021196 1250 522019946 522019963
    0x904060308030114031204051f1106070503060f090f191d011e140103020904050309100f170c0d2a02030a0305070512041103010b280f030f080a030905 66
    0x10810603043c100e9594175013881041d00306c50440d0a441d00705410f0001280c800204982200490202801e00303110315400381089000d05000c0400719941441c083d04001e202d40c0040d90b2050150999090700d443c903190614004d803144011b03075803800c969074880c1301410031413000e0030491718140d580c3c240b21070003800e440e14068010f402d208000704140025500200f03815441c080591602032400214000c000585141c05044030340485142e80c0c1d60f2140e04000c1e05500c140c1c00010b40c840000075100c041c0503000b0114455844081e1100d00c00c0c1c01580f40c0d107800c0818102e03003240381d05004105814000d002e41d4010701c41060008020403080072030100c00d008001148804e140568804112606481e6150180a0340500e1924005090601d18142440801001740000b004c5640b503001185003900d0951041d00006401000c003003162003603041c90a28038428013048018031080710030210741401a070420b0700840c2d50001103000691460348a404603038124805c00350406031101941c10101d1800c008025 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 522022446 1250 522021196 522021209
    0x150507140c0a020f101b14011e0c02010c02100914031b010f2a0e0324070c020a09050405070f170606041509050c0403082101050402130b09040603080301 67
    0x4103241a401001383e004114402e0703030f21800885441400c455407001d480800410480c0c82181a43c2d001e1500c01406040080140003c1d860b10022410110100801402c12042d1000400c501072402c0b40407400d03508502c0c1c001015a0003062801e02c00c1559a12008020b406040e0402c030303004d07007444407600f168050903080820b05804400e549540d01c0c00e204000c510070101b641040490400001000001640c420060013103850200b559030440c0611b200703240008006098400d5204c400300c200b007202c42094100d0341464a00d100044a0790300030155612070640060080001518000b00d480150400a208603514024000c0c0050b646410020309070207018454061440c104001e640350f445e282c0010800761260b8107025281c1107007468481c0c0c160503945003410108150f0344240e0304002d140b0595000034010180050341c466100f141040802c60a11141d880d102d15903a10f5041100740d00403503902e01480000400d08000b20381d1408004d00040401901c00b0802c1c659075120492036030400da0250 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 522023696 1250 522022446 522022453
    0x1101091b06020f0c0907181502030c150f0f0a0b03031308150709210b0f0123031f0905010603050102031506030112020609011404060e011b150507140c 66
    0x140300558060241d0366840c10044004c280000074440090000c0402500100501080c0c8000e054080000366000d800740c079039264031300c08407801100001c1d5684e000b240c3c82001805090240059a40121902d501030525455082e0307481c1c4403060940c0005001a100c402000c0d56080307003a03880d44040c005030041002e1100341c00550303440d2061690414a00c140d4034183c81c9a084c041008650308041580251004403070400240461400c138141c02c0501e016002d032007914454200125074140810799230581d070b10650041c1d00142c0c3c1d034441490003d0440c20466140d080404074058020b1303101c031101205100884040344081e0b1a0703d6041c21185550010346490750000308001105507032203803030501414161540c51840d85040f00601c0c50803900c0a0080c462480020245080d078440d400d2841107007111036000d81d54a695010140024501264030f5020800d41200100500c14441c07604241e41e4000d00d8a04241e0552060074000f071000814140905c64254283c801700c204400241c6100300002c2c004 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 522024946 1250 522023696 522023699
    0x111250c080d14030910020a090e2d01080c0d0204140a050109060503070602153c0a090807030c03050d0603050c1207030c0306020a090e07020a0209060906010f1101091b 74
    0x41c000c254403020f4002c3c003042001801510361002800440c5080e05a1005031202d41e00b0702c0c200c038070300c1d540c0d40a50a2806c9810a02c04001e00c002914403005400440b03030710100707150948440420b18240f190503215040088034009900303080315508040b80c4000d100043d8080c0448144c0d5503004280c43c1400382c542d90382c0040c0b080542030f120300d8001c4d140490042851074508107000f56201c9142030b001c40305015102c003043d507104014041c2852032210250038103200c1c0112101c1c48402c440040c443c0c05107200c650124802180c2031145181c05a044840e1900e48501600c00341d4981d5900b401c101d082200810a1580a9120b4400c460246200e000070380010740500d0100310108415800140171a08030100c00c000196007640f00c074080b01e50000000d86c40f00c040c51010785803140154400c201d082034117000c0106195001ca0300080040c401c4508150548a0740284a10020100c48550124408500402c2800d008090424015007068004075244004c2e03620070a410110846030340200c2c00f403100 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 522026196 1250 522024946 522024973
    0x902130e0103080f0904150303213806310608060f1201020d0b0114190f03020706060e07080a050105240d020c010605010206010b0c030a2d09170111250c08 68
    0x40d8200e4ac0900c10070500542100011400b01d03001c1d0b03920320018480003020300309840a01c0c0407005080400003851241c90312944940401103880c543c01e0941c0c41d04c0102c1e031060900d110001e10009450031035907406855500d0704141300c5488018003200303130b000e010b5002301c040700071003400144120001303c2c5000c100450792000150060408140a1114603401d00c8028011049050200108039051070424065103045000b80e0081c410b07038070b01510f42814400e001c200c11110540c4a40500d815a1b40e1402581e140950380046442c20300072030b80d01c252a80c050104207800c2c000d0001026503510701041c90030000004c808200c0e40501d843c480380b6510791108110a68040c040d0034018070080e0255890040e020380126101d07c0341c0e4484000780052136007158803c01e4a084801c9011146d000d007220030316012000a440d0000d03034071502080e89a1b84038094050708060040056540b420f440c1c0d03074100072403555560001c0340c400c030320404d102c01e41c80c8d030140c0070070741942d5250018001034000c3c000b240d45025 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 522027446 1250 522026196 522026237
    0x61809042301060e072f16050f03070e0613050f1608040819050918011401090501020601180b030601060e040c052802070f0902130e0103080f0904150303 67
    0x12031207541d2500504100d0750035842007441e030180c0180f512120f21291800003c480f00c003400c0803000580b0b520382d50000804170003c0c800b98140c0c2074111240b09940c2e64000c100101c40d07400b0481340c050b049580c1c1000440060891140c104c0e000800b400390799881085080300700d0340301303d404510034180d41d000d0110080e160642003041003220310f0502064580f41d10f5100d0148144240c0d80c02405110000c05161391041c0192000002c00512852150a442d41d20b02c0d82035800f80210b151020a0601c84401580a095007400b140c00c180c000c0c0102e40c2c03070300419001c00080c000b0541800d540b900c0480c50140c1e802d00041c3d002c0c141d5511442c419101403801e11080320481d003031140a0100803c00c04409221400d858400755080c1c4158101c1940903d03402c9041c04c5ca80e5000f42540a800b600c041100c00d116000f503e10080c8143e8600c540c15035078000d045d8840400e102c05400d040040007002044a4110000c02c8010b070003900201e0950b2160940141404556105400244014040124044000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 522028696 1250 522027446 522027503
    0xa03200c06030114040b061207020615010c0303150312050307020c04060f03081e0c0106031a1501080c0c03210907031106130807120c0602070608040206180904 70
    0x800405090000002082061006002e404c000182e01010141540d840e03402401403940b0140c40035448101c2403ca401070420103503900c0d805401220f0018080c50041401002e07020416524001084400c1d1000c1e40200b80c4400d0040c81c0e0100c038440400414040c107401c00c01c0f02025981d80b6902d142a010080c10840c032075407124821414030780104540d4400d401614140c94000e070320150303100b10600740420150384040c100c003c410f80100d451221a0300650103a01120b01944001e816074440e00300340700c2980411039541013030401083c048500da500c80d43c41c07243d105181b903401925080d00040c58a103540c000b001d49c60401840e40c150070400d09421164190040316180081100c3c50941e42c420080c944006c0b81c2c00d005640100300400401c807100f095400629030b48080e9110b40b034540701c02d00c8110080c0315050b6100e01d50305a00040b0a440021140f04a42e030580d01c80c0300d02e484a600b08071056111450442406580d5112000c059943c054094011403040800380140d5200015514080402 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 522029946 1250 522028696 522028757
    0x71e2303040f030b1509040503030702120c2d121b011803050a050f0d0605090f0906010501052107020d020d0203090a03060f420b0a0810080a03 63
    0x180000c01440d0b8001c504502903070781c4480440025540c441900246402010100d9031121805051001f0300c200400114002c20f15642550403181941c00703450200d01c2800d0340ca149580c051401d0b200d600d5091002c2019124803200c0c00c107008840007000d103260030005081c1220078500000d10942404007992603014007070b8803200900500721448000800307054940006801d00c41d001600403c8a4450360488015440041e0300070707120109078070040028131141c01068010710488010600c803030000c044d00b62040a5010041000307a00700801151190003c0702598107880d101601d078a60355000d220002e218105560040c2640349031070000915015219102801355007040103160080d49030301c0b21010680780c00001c00728050f04002c0080e001041840c04c0c1034502d00045d900e0040d0609101d10360700c140720301083c100100c183d00004400404036584501014082c0802100340d2140c0100c003003d41c4103035440b03200e84d5103e543d90000e44c1003550030f80f400c80008002c0303028200484031031040380b07210005 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 522031196 1250 522029946 522029953
    0x70201020a080703021518030304030315080f070312080c07140a0c080c0f01090f0b0f0c01050708190501050d030813120c0606090b090103080c0c040914101a06071e23 73
    0x3106d4450702e848e03110150014040684400740007035103c4208803010010500c00c011601d00ca00c59420094407a011800200c0d031992a8048942d45180300e482c0e0180038815182c091494503105030798400c80042100c00d80a1a402056564004180300d203820b10001d04407038001c0d103035009095041145002c800d94031941404040041031245000f0310802d402030b503200060f00c0b550f541500b0799003040f40c02200b1400c074242d8201010001001da2100d5290f0003a04000404400304480d10070074000d5490034010306802080408482010074032605100b0340040c08155400c4845600c1c0d00d500f0303207100e801d420220200c2c0704141100c00b04150b500c9100e004040f00c40c005c2010082500c0010040801884044e05045000c1005030f4410020721000b07240343c2008100f0481d5494601d002400c10b03600701610081d90080c11340c0c6035014039071400360100e0f59100804441803015190100102c0d50010704040e1011042c80c0c0000c03001c0000d80d946810b0441c0100202e14142e406002046d000070000c000d111107940 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 522032446 1250 522031196 522031231
    0x20c01020a151a300f03030c07080c0706031b030e0a1103030409060f0303141305090915180618060103240c0f020c030114010308070201020a0807030215 67
    0xa09045140c0c0b1005507103800451209441d907060351040000c42982c50b402503640c0c40800e40e00d020304413003002c0269411040f1541d40e45008501ea03c1d00d91140b009000c940041000803484c43c00740d4010250a0300c01c00489017401408920280340c501581c001c040820742e1400031100c210b0124142000840c001d260520017080724a0220351103a80710040100641d50300c400d0610300d03a909000756000b60460305c900300540c0341d13188003840145800e0711068010803c44001d1120901030001140e086113601015010303103520f000c0074441100c40046c000c0d0b400c1d0142c445000c0000c0c1080c68074600803d9201080c00002d08207010300d5003041c1010b09496040001003158204190300070076414112a0424606120000990052500480c0842c4012101da01c2e02f24504101e0350080c078620198001c9074201c8824106441c24142200e2800c0c50754100bc2340c22500420000d8265001440047d2040c0705841e102195580e0703105071a080581e0840140e0050560a40c400d0b03440d049041e8095606001604441c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 522033696 1250 522032446 522032453
    0xf070819110907020c030607031b080106050909220c050a09020c1e010219020f010c02030903031c0e070b03010911071713030b010f060e060304020f0d0f0b16020c01020a 74
    0x4600000055002d60102c03000604003600a104200507450043c05070341052074018030080c0144030007030044007485001c0c0fa0200c0c0c440c0c8244071060580301217460315841c0850000400c456000c0c010130100c0941601c080c50318141c0b40100401b524544201c842204071030621080141d000205d40040308518030600c50007410790ba0000e130303180d00c1561403140e0080c569005111940a442807219100c0034080718036030b050100c0d5000441e1105289420000c000d00c002c00b4030b0807a264840d1031400c0d5415032051142d01a01006103d0718650440e455000060401031904458202000b0707901200c2c04400110040121208600411022010b60b1181915020050356040005a103803030481c018010301250100000c0640000c42011315084090741c1100e69440e0381c0f51002000c140541400102c14070080641410600b003507034080d41d4010b1003000001f1450342444054039144005945015456080c03001103040c03100e000d80114842480b0005442414002038900500200400d04541c044050300011 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 522034946 1250 522033696 522033713
    0xe030f070807060b03030a0f030e0a030e0105211003021302030702060f091501030602091c0b0c0f0d0609060302011d01080a051008010509060a14011d060d050f070819 73
    0x1403541c05642180c452506082c4400107260b00f04c00b4a81502c000140ca0626a81100200742a0708466a0074000d80070802120382d101c003c01180140482c070403803088900b6600601c05020507100c0341100c501c618100c029150407812081d908880c451440304070910a40c10096003480150038915029071460800040c000c0d0ba82c900140340d1501241e004020410941c814007a400d440d16080081c0d034107558403410114025481680c903688241950028215201c001c80420003030150081058a40c0c1e544854801c034442c1e1000f000808038000800c03a0050700c5d0f890340700d070b000a00214100001c00c0790a41c40050b29400e540c001c580301c0030f203094000350751507a40802919800001620003043c551100310020210070f0b0190440d01c0d0f07a508000c2001042000020084e2140340d0a00051003506c0d0345012020140800307014121511065071100d94048013186c140f2600203a029000c01c0d000c00c61500c41e81c0c10400c0f60821a807240e000107504011448040068074505001c40014540c8864541e444406 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 522036196 1250 522034946 522034957
    0x1e06060a02030a080a0f090c180902130b0402070209090c090a0b030604030e0f06070605040501110705190f0b0f04030e0307140d060f020309070f06410408100e030f 72
    0x108184d4500061a4a0458001c14401e10369003c0c184190034007445c05c41c140078064001c2c4550300c50300900c03040c442c4041e4041c518074150041c10382419201030072508000390084120454002d5000c02c250001a01d44024682c030480349403002d040700c81103100400c44446405085058110306280200c0d180c1d42e40400c000d80c101350326003068100d049450300070a0190003070007609a88254040b0351b4000784039013500980d114510502c020003c0c080c1040c2803018500402202038140c3d8044103840890020a84071103000074058054981c8148171543c1d040c1035040c0460784011810b1482043c0020503401c0154100901c800301c1c041d25615041041815010315054091485410403030034141c140000c0340c0c030a001141c8410019035880c030b030030510543e072342c241132003550001c1403007107000115640308d11088800030000310700300f2074042c4d0100310180031041c403805002180c00c00c8541c3c5419650011009000404612010f002000301c512400b40c2100e400c0006451070760000c02c203800720110a0307803c030380703 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 522037446 1250 522036196 522036217
    0x21908040b0601091401200d0e1305090705090915010902090108060d030e150d0507050702151c020d020903060f10050f100f0c08040f0e180c040f141e06060a0203 71
    0x25040782c1011f000301c80014881d0400b2140e40102400d1002c556489030b01c1c003a4504040d0b403200e050646442d9030394112502214a80035a800c031720014400341c50a0b41815401100d010100d8880c0b608a4502c0c2c1d4a07540e0a9101c417038015800901401a541c000e00303415881001110062807034110b07510080c0c100101f007004a8810a410081c4400d010540300944038000d807121010492881d0030440540a035208140a074415a00c142c03a40441c04081021940d004e43ca580440044107404005100a03410407000c0703200c5917400b4800d03010141c0307003009842c0c0320b14402c0c3d260161364103006245003100043c94001502414500144c61115111001c1c8888051103078070300000f0958520b041245c20b0307200c2400080202c030700042d000511020159000c001d407000312140d0b002e130780c1b0342d5402010149928480032006400010701c00604e032420f40d0003c0d01c5c0b006418800300e80d54850f84580b42807101c080b507220507408600c00b681d0a0a102041c607043d0301c1074003541c1d00307860840c0841001e9680c3c001c5040c1c10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 522038696 1250 522037446 522037457
    0x70e090c070605130606080616030b060405030a0b0f06040903200c0a03060c1b150b041808040305071505031b070614090d030c050d020904021908040b0601091401 71
    0x142145640d60440e844690080c1c0c0420003414040c503001e9440f50f00318026929541040340100350340f407020400701c2c003401010441c1c0303000703040c0d0900c01d03406409504010740e4084020300000840e51810b00111014504c14654a01a45000103070184d0406014104034015483e000e49040042c0d0400600107240c648039214800001005031070714600380c00340034600e410041254000003000400d80260014002649900c0e500380b812120741005c58101a2000e0280949072800e40d00e9201c45900c02e4469101c050404120520240c91079081401c10060071682624005001c00030702c00300f0b10100380545201c812100c80b0486001000b800c0703010180007080301180d910040c1c4840604407080f00c80c0241c2c000c10a1210b6400450704c42c14140c0c00301c0741820306000fa0081000054803900c074000707004616843e101e040c40e81c0b03816010003e4028a091b0350300541c1c00c0080d88a41404114100d00304040d580e120b0010b40707041c3c0307003040b0300140280140e4140020b00030305200005800040500c002c50130700c2c14 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 522039946 1250 522038696 522038701
    0x161713140307091d011802010503010905100806091506151209071503060311150f0901030b031006030201140906040b220611070e010f0911041706011a03070e09 70
    0xa0706048183c1d0101c0e04251a0020300032003035002141c80454419080000c0000708890102c80c810060365000080c0020001c10042c0000c0141d80e2080d0303008000c1e100340c50025902c6007005460b240342941e101500354483d034040100a95400076950740148280d4455507140e1103034050303500500070020300a0180050780700180d9035603010450600201100d40320000c030814085405001055103000a80350000464840c44403410b24054280c214102403915929080700c030300006203142c000c125194101512015000310a9804010102000c2c01309000003c040b0729510002d041400c0916840c0c00d41031b014821008150345030300940d0200c4814200155546000308030200c0c035040702142d50705e00c0007020700f404103089034060946010f107550041100c80381c4d42c90381082d1941810901c45d888844190680a022840e541d41007c0b05428031420440d09003a141c41e081c82030790603600b0b551006903204900400905400510340e9090007002c0f40041d1550515160041c42000d410050740e0103503805401 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 522041196 1250 522039946 522039949
    0x30405190b090105071a0a021c05040302100f0e070305010507030606110d0f0309201002030702090a090c030b16090f0501080604092d05010507020f0a030806060d0216171314 76
    0x8440d9040c0c0704ea404600d06c50328003000800003c0d0400400d500620081c800700784039100350b43c42501d0090703806400174400d1080720460b1202170002c850000309900e448915400000204000420280d44039030f0000c00c1d01d150041e4010219942d0358014800c10868006e408407044022620101d40c1d025071034000000c2401450640c0070f01118000140401c03000c160500007001151002c0d190400210707100340141c6e00000040382c1e24041d446010398800031400219010030b52580c80911954460034204440a540381c607200001c0808031040c2a48184240d404014298051446c7c005407c0d000c1048800030b05010000342007202c000d060a01480c0c2d03c00d09141407046926103505084955825900420408205260183e00c0d902c4102c61035070900021404032070021540d00b2207480290000d1030354401300c0d1000c0318240340141401d0f0300f214017008001e034000340f280010b040882e4540d1282516440034030f443c00b543c66801000400c1d800c13082c00449c02d5002d00305011411111000c40c20000003e4000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 522042446 1250 522041196 522041213
    0x5071a010312052b090201110318041a1503100b03131203090501060602010b04050a18021005090306040c03020310060803041e090e0c011b0b0c0a0302130305030405190b09010507 78
    0xf00142105441c14004600001da80108181500c01e907551008e000398003115640c1c90203081400c050603542107480c0d200d5410302d07a00c9901c401e04510316004041d140b80313000c078103d850860a0b13892820070010410620300a1034000000412060000e545540b400c0c0400b480300d41c144040081032803038044248440144203421a010700740d00034000300b00c201d6a60764064001c00c581c44e020390186052200040580301a0b1040407031854003207101c0c084041c0305608106640321001d0381c62091010503c0400d0942d10200500341c851441039040340c1445085004241c9842d40c95001c0412082c1044000d0103014404000e0303408454040c03440b140c00091000b54424101c8050b007000a64601d041c904020285000800300c3c000c013801c0e00c0310140810100000c8419005001c0042d080e00f07689404515000d46090003051804528613005040c581c1e41c00e0111160410b5500c1501e096001007020301003842c0003006500b0403010f40c480c5454052a00c5800071840c01002501070510501042410600c030740c01 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 522043696 1250 522042446 522042487
    0xa0f02180108101107020d060b0118090f0621112d01032306090606040306051302030f01140f04020d1a10060503040f0609050102090a0605071a01031205 67
    0x100d019000d503840c2d06082ea07592030990f2640b0081c1d42015412405060038204a50b0344a40240c0b0882c540041d43d20340d0b002420360001d0303103030402641c1c144142c02c6500c80310031a07001e408003041c0451790030b1401c15031009a62207908066040c0700040d4141004c10729108246040384d80c070904030070000d1000d0700010101091240d5504d00040d400060452031008452260340c402c109813010400058414002c0c00f00c070940410500829440c80c0c040f0ba1145044071150781d11410060000d4a419101d94030041036650566000915400f1526901c0c00c500d800d100349400c0b000d540e4001c1050081442c42c0308003040e005040f5000006241d400f203401e54890114547e1504d0b005204070800440d006240d000b920390032070310700e10601990f00c070101d1480e10940859000b01d4000c022000a0120358445800410620030100c40a6500700406a101d8840d45480c4000b000191203040d10380340d460801c10024013902103c0c4211080034801400010306800d40240c00004906c1c100c2e0301c6a100703241014014482 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 522044946 1250 522043696 522043729
    0x16060c03021e130f03030801030311030915030915060312180301051008100912182304140c16060e0a0b061002160504020c15040f120503090a0f02 64
    0x240031041e82e040903a000404189403101500e1840a54541c0309842c0124680001000202c140c00100080f038030540b501034000c20401c2c00e03240781c5404003000410f050700201481120030300100c100064903e0034005134422914070302e5a0ac10742d16001000a4942240c1d0600300585000451fa038081d041b0b1044c1000e40c1010050000c10190502418a4260200510800e0031900c503c00d0040104400e9003c0c4080c2560f00ca58140820a1240002d4840e100d8000c0001020981007800041d5412480507020702074200035544800300c3d8130503041c007040d41d0365500303007030502c0c403201c0c007444240001c8604449802e01c00a0903004001d800d841d003c000340460712510422031282c0c0141c0c00074015030480c0e903400750034122007001240d542504242e80340d82c000800d20400f1030020700b0411890030150010710581030664250f0302e440c03100d4182c00707250700b00c181c405451005490300c0d04010040300000c406501041410918190314090310b82543e141c000600c0204400f000c0304031202151a03214042010350103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 522046196 1250 522044946 522044977
    0x1507080610140c070902121b07020a0608040311010f0c032a03090201110a050705011d011706120f0609010e060f07140c0a03020a1e0f080f1e0a02010b010516060c0302 73
    0x45e620301131f44000b10141c981400440d07111004840880401c02107501d080d50180100381100e140240c182c9480070010070607001c0c0b001c8508075151518083c401c92a916440c8940010319482080000301210800b501e9030602565601c08040034400c4003207841401d00c1c0a00c1d0104526807a480120340e1680300c0301004486100320107000c010020003041c0041541c500307aa8503004820065001e480c01090180502e0102e4071001c2c1100800341d0303032502aa0f11600107400342503d058810121031400e2074414400350240c02030f105021011600307002d140800141c00c0010211401e02c1000d540480d00064a004144441c0840c12460031030010207450303c290032001070720480a0f50382030217915015940422a070850708150b80700411a041e1421450903508148034444500c0c9076580d004256001303084000e08408140510b4600e540a81402805030150340b041d5034686040d4a40a0300b9035004040c4281404010b03c000c6801c0b0120707511b011442d94010001042c000c2101009070002c4c860711070400c0d06110b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 522047446 1250 522046196 522046207
    0xc03030801030203010c030615030905010e030c06150a030c15032a0305090f0c0f060d15060801090212160e0405011d010b04060512181507080610140c070902 69
    0x160403030000c9048900950080c840354140800440c103d6045002e07165030b1000300c40d0010141440303507004403469807003040000f48004020759001d185410101e81e01030203034000317001c104e101410812911100340c002c0c1e8040c2c442c3d90450303850740c50310850781c0500a02598441000002c8500c81d0f000311702e8041000300e000d901c4603038109102850007454091000482d00702004296120744c001070101003401c41d8000b6000c581c1d410300411205204030401a84c1c00303001030050341c4000e40030b44034807e6110fa99500b1206054501031000c0d2202d94140e01880741c8620503c680e14154a6030020564080209104454000074002046d0741c1880200c80f0a6045490007001103090170740c41c03c0c41d00040c0c846108503803140c0ea03211101e40781c52040d030103280c0004000380300303010703400c89034000f15504a2150382560307200c4d42041c0c8000340b41550040044c00c11041d114144442c0c1e6801040c8a50011000c2d96212802ca4146034090040e04c40c454461b07a01450000c4c0e0805d01480600494015004420b010755450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 522048696 1250 522047446 522047453
    0xb04032303030417120103060623060904111c05010303080f070206070e01031407091a0309120912030c03091825210f0c05070c0b1c050901050405070b120c13030c03 72
    0x3040c09002d01c95540100c07882b8083e40c1702004811040220780103107003905d004240c7c401e20000d00400c000d0000019014424074110f000707a010f07216006030682e0400103a543c51030400410102000e01080211402d003020721680c1613002c00c13195441001420150300d0800c0e000c0040303005080b0900300140c9c901d50003080c00089039201c0318040446114009000400c20800038050f414031040e9901d0516070700c030030310340e920140c0c03140080c02c0e0010004018598400d000c08800e42182e211040c590302580000410040926102001032080f4205800388000703850a0211042d02c0050010f1480c03081c600c410800c600d15108e0746a00030034218012609a4000181c0c0d543c07c0a000a001a10301540c100580030400510640595001582142c04064094a030400941c101d43c014a01d00b124945010324010050003079004481c000c0741640000903083c58a82000e6007001016044614980020045440500502c5000581002d0f2104e01181c0c0d41c0b8100d80b00304545003056100521908810f034000061 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 522049946 1250 522048696 522048701
    0x3061d0625021617010e030d0609050a0e0c010e0406090c17160f0f120603031106010803030112060b1c050709060b070c060e01020a0209010b0403230303041712010306 73
    0x1e5520041c481000707290099081c0d03190400941ea00328102420042000301030320201000d00324112060000440411015103181594405c6900880550300c0d04000c10100c0700506c14a94000d141690404c000740c2c0b01c244660301e0315020007006040110244010a042c0d440d94001d00c028003584804020b2075a01a2000c1c10f0325202d0030103075055090303090006114105400c0b8001e4507000655946020b244603000907a8a4075141c1000c41c20410810700e0941c682420f4820394010f18000d0325040316540e180340c001032414105030000c1003d504140010481c50b080c80c458103e0240c0e0004000c00c0200b551004101d521811507046000c0c24184d0b1030480900902003028001c4d45c03040c03035040c0121603c880d004000391090640c01041546613a00c00c0044500c60780b01005040c50502c1070340c58150039500098a154002e80216a0b880c90000e0200704000c1c0c080485030401c0c04c6007100d0740350702c541e200155403207000c010006014a8948500081c0d0300842c04102c440800440c00021400d50b100e003400e200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 522051196 1250 522049946 522049981
    0x115090209150c1b040605100f0903060c09081e120705010902031c17191a09070f030606170f0603030403050d0f03060e06030604110609040e030a230403061d06 70
    0x40d1130806070701030070311420540500310a139640500b482d48541c0c01030b042122200c071401448401c00c2076038100880010640c2c09158491050b40d0346000c00242459529414900b04c0800445800d003020702c0e01d0b000075804a4441c007150314003402240c0f24545410083c0c00350611802c02036250080e4182c0c003061038003c180082620070682c3c0c0c2d0154040708040031076110502690040100c03071410030052204a0035402840d482403280d1240b03080d803c2444045440d03000c00f1348250004c104041e4044c502c9903814420000100031900c0c001e071030030560030031200c002080681603c0c3c901c4200390000e24151820811500115030000c201c032074004003260000d03c4003104042e80d00020f4145500010520105c8004d9405038000402420140c0c0700c1c1c2d5181001006000c50285e0400418442c010480e9101d01c01c500c00c514040300915515a00020014100c1c0352000400005003040035456282ca0001015941a2a0b21000000d000c0c802c41d00c0d00e2240304d0b0800390003400d910030441080300c00d110100e46041c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 522052446 1250 522051196 522051223
    0x3060509010203040b1e0c0d0f050f06030d03060b1b0304080a0605040c0e06101101150e19110d200d150602030306011b0c0302040504140f0115090209150c 68
    0x100c2500c0740380f011003480700b54440c02c4400005041c04140d92a804134000c00c1e0326231410700e0001c3ca010301002e080066450488140711500002010041981401c2c40240f4144449140401c00c0509110002c1e501b400b401840000003404551003400b24001001107070040c02035502110012103042c03602401500048a080310106110400010149a05840203000d540001c0c601c1300381c540706920440d24400705500f20328040d900c51001e2480e80700b942d21860301405443d070300c0c6145498080041c10340ae10850708400c040798079008400d03000c490403e084d40c0c10829000701c00b007030042c10100c0141c079540c40140c0380d6048aa0020b0304c0720500100340e1022101240c081491a404c0341c0c1d0720010703601d902049600f14041140c043c2001c5941540301c0c0c200b00d400784038131401e0702d04580303e8000c80c1c00c450007210210303014081040038000b4100100603071449240c2d580022300c0b440d1888402d1940307400303c0384101c4001c00e4000c50300030a90b070750f172140e410300300f1405020654403854103603c4d0603543d02c004924403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 522053696 1250 522052446 522052463
    0x515101404140c07020301060f060c03030e1203180102090301051612060f14130c0e030f0304030302100b010318082d030403080705070812040c0e0912130306050901020304 75
    0x60312181814062029221440000307200140e80380348001d08035510001c400c90749175603203481c0851841c81108425020b044603655810206280d4a0040e040351070320f4240344115400224203803c1030044a0481c0d030f01080b0707008916512240e40302002e019000d144001c69040d403d044c10040d0010f0350035030121000f026551072540300c0740032a00080445242c0d0081a0380c250f10301109002e80d1080c52000618400c010b444034010010702181c1500301d9507500c803014005017018500c4810307031404105010706050410040d614152440e50065550b00c080810750003441c0c0c9840e2a00826806640f2081e00300e01c80148808801c81940362903000c035072004009603020700703810600d10300c81c1c28518101d09800c250106894a1074986032021ba4000100a00100801804000c81d800103680700000c0c1c07030110072100003d00d1030304040c03401401810290700001a5105c40341c0c200720b40c880e0300260341d01c3c00036842c54132a40c2c3c0f600c0c0100440c0170806036030805008142403030140460500c05600952040707018010a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 522054946 1250 522053696 522053729
    0xe1302100e01020a0210050906220518160306050d1a090f100b1903120306090b130908041e14030c090f060d1a160302031e04051510 58
    0x35104807103600402070050740480f030b044c030040c2019000c40c911a43c086c10910b0a00b25404009400c40d80b16110003c0c03c0c1c01c0d031b00c0444210300344030948040038100c00c03102446580e00c89502d580308010002c20301c15523083c181503d0050705009500c000007408000d801d14a007201c46080c11040411540704048000224000240240380003090050014441c000980b01111213401014094180c00c0764261740b01030b080240007080c42c000d6801a00442c03044c200802d00300580740c0090102e5a1603031103640c0060070011110515074030020074210000c01090b001a403c141801e0609640c0101e40107503046a880c0d202280e0001205080d0504a8180d2004001201d00b007400b0725031244081c03402d5642003031503400851506908298121390011001c0c0ca00f61150f0380300d490303044020011007a8a00d01403a02f1003030112140d501c0c03a5001f804200d078203095117942018070118208140120032800c0b155402c1c4086001c200302484070754046014400301e00a00c0c140a08403c001400e80d125a81d555401c200c039 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 522056196 1250 522054946 522054979
    0x20a0902032e030206070c17070305060708060a0308031b0a0c06051305071502010906090305180a03020f040e10020301030c0f0f0b0a0e01030e010f050604150305030708070c0e1302 79
    0xd030b9910010400d001e0780c0d40c58070715070078030a00c0d41040c0012a9001d51040e00403902a48044514620010500043c501e55245d810b20909000e03000d000d103c1004070308070422400340c0303070001c90f0300449500481465a984e620303490f02c078500c5d008860f480f807801c0340020f80ba415035510080100246024000c02c01894035201d130100c0c910b10a90500a0464200d05e0003004042408040001c103494280004100c60072a99100011a000030004401041000ca0908407446401003402c0203440d0903189104102d045800140045c5100c08000c2e200d240c0740d65680025450902807041c0760f000c102400c0d5207035612464080c440b101140900c01e41282c1200c80080c0a0000b40d8003802140d840c50816880c060607990115080409403a065040c140c03111003440001000740310b20061030340003a0303000406040040030030043d10b1440c1c0030b00651a00c400c1003400030940120488210301e03170060f07050750380310401e16202d00f2000d61a4410700700320f028841003010740700040705895000c0e4421160300c980c402034001c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 522057446 1250 522056196 522056251
    0x5090f01090b040305091206040302070e070f090b0306180907080d050a0903030c0f020d03080a1a011e11030f040311011b12020f190501180201080a18020a090203 71
    0x158082c0040302c1d844085400301e4091001041100d5028088189048590b54002e141810a45044005a1141c10100215651a65019040480ca180c109140000d4501c01001c8810340c3c0154440507100201080c0c2aa441620a5120000c1072400f00c81514044001c280c45081030b1040701024000d1110162245200708111498183d068407004111415a1402c60b03012050381c00844841c0c2a054845d000b40c0d40b002c180144051196907440311918100e80381d07109440084203100302d10425010500016a004808602490000200c280002c1050342c03044503e407404028407000d60000040d04190304041100402c25a4001e002c03085400458200440c0c064004001d0355440d200784640480005041030400109207241d0f00c115240b081c04c8000043c10500180584c1c6061044000c0fa20100710081c014200a0142c011070402c2607030041d0000703002408000e100c00d0b800360361011070f5820304a454201142d15600601524a480e0b250200c07000207501c150790030220884000b0703c000b6045181c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 522058696 1250 522057446 522057461
    0x50912010204030b0f130b0f04050d02060105150f040312020601230609120f010c020705090f150607081608030a0f0908090d05030d0e03130b09010207051c02030d0305090f01 76
    0x1c690141350759110108880c4001c40a80000340d0b0008445600010401814549004510b0707802d014007582014601645085c8201d9031031000d5402140c0100301035941c0b4520001070202407601955254a81180000c484c03185030401400c10b40c01c003400d00141c50703001030610305071a500c80b1869406c00c200061a001a42c28403000c5a0002c0200901041820580000c1d0240865803040310712010000b00c0450070b4845005000c0d005074000d00c2e00700568905804038a4028002c7c2181551905202c0c030101c6c41100ca18001d2401208006182810444c0100884540d05100403400c01004540e182040e100c1e072080d03130045a12424414010324001c00c9114910307680d40e002031414a04071411041c042130b40888101070340c60740000c0c80b003160811014003401c02c100000c3d2020316562540c00c01072100300c1d0f5441c1c0111888030703000e02444401e81d0300018104140c0303a0481d0b992040c440018503948480402000007505801405411141c2a40642146015000310009c0d60000548402110708a4081 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 522059946 1250 522058696 522058703
    0x90a06082506030c021e0d020120030f0403120504060f1a0d020103050c0702180103021005041203051309181214090609030319080609010e010501050d050705091005091201020403 78
    0x1d9042042000e02a9009018400ca94010340f403068100900841030140c414140c0c0c02d594103e007100c04e990b5030342803103075510201c3d20301e03600e06c4078011461412103140402000d040800c444280410149401030010301005440b2540070702540c5014507284020b8041e03803201300c02190801003500820f540c150324200310164003a0116281d6001e5800460152001404200540c1020041000035881c0c600c6404100e40f0180e04041d250351541c81801880012051100c04200c810f00c02403060134070075642141d0542d01490003a898004008840110240035804180c915180842021140310818078030304015024009900c2c2c0041101020b544004107044003900b81801080542e50341d16007000500002130010341200e08018508030050f8150700085203600200d030400b400c0201ca85171074000c0d9030142203580da00600652420700040c1180c010282196002d589420001d03070010b22030819038103100c3c4000e0603040c540501c034030050041c0e407041c40590b00960320101c1058080c1014002c032002c4950 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 522061196 1250 522059946 522060013
    0x411040e1f150804331a1801030308060f040501080c0f0103020418020d0216200409020604030b041b06050901020708010513030c0602040902030a14160e011d090a0608 73
    0x251943c955104103c0d1020a4000c1c98400a1030201719400d40c42c100010200d81000080700350101c000100268441e00c0301604c07410300740d990302c0f40d05000805000e0450350700d4141084292140ca00007042c003102c0c811103680061500000054245001504038080d82060b900320303554000510044083c0e101d103009407a00c0403184244441491003d0b80105000034070140d0050414280b60102050f034480b903203040c0d884c0b110007031117800030100f140b290354103400046030100b201d00709035408038205010b035100103858000c1020006041c4101c10703803070445502514402448460b03c4881c06000c0b5000800c1d228014884c140c00850180030511820b4018542c80b4100c84004030541c0e4211040043d8400071078545400f804002054841400594080c0809910100b405025a4058505e40900400b84d228913195001003090030b03500040c03030703516201e401e01c0c000015036500e5050a0b4410348040c90b60f038004400c2d40400200b84000d0340800250384108041e0741c5c2d240c60040c01b1401201030b103850300c81d0724007 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 522062446 1250 522061196 522061201
    0x3081c0f0b1c14010608150a1505210105010905090f0c030c0f01140c07090f050f0703390201290d140a20010f0503060411040e1f1508 59
    0x110112903414007144503200b10f002500780070190a0030f4941030b030700c00d420036408407141c0c500c044020f01c1c4544c0d0000317442c00104610403031000c02d0301c6403070342030301c105802000c802d526219050001c14030070529482c80b8001b40000e503500c202d40802032800302d4070021140507201c0680044c0102003280b021404000700140780040c80d250802c901c043e400840c40e814020000c03c4603140740c05034005802d902c0182c0b40036141181c500509101580c0d00d10710250310003464170342000703244000600499000803451600046410303d1411b14031000d02400c0130803050700c17901c19114000300034803a00c4101c00b451682c006d0282d030310800007086040e1625442da035801825030700c840302e130703070420440300b100b00e40c01220306503c114103c0180a00380b540c649020b0320a01c1d417641c4a40e00c00d441000f500349000000303180400f4030800c54071005085000c0a484548526150450300c2103c4034000140c0300070340041143d03140d00d414085611045031a134181c09405c9800e0b0840001903d5880140c1d80810228a0312140100da = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 522063696 1250 522062446 522062479
    0x60b1308010b190509072f150f180f070305060109060e07090e190921080114060906120c04080601060509010c150615090f0e16140403081c0f0b 63
    0x5d0009104008011082120390101c1041d041607131000e01a824249240154100700301f810000d10001c0d80320b0554050043c407003900d0350040c115030b10004c14280085510b03400c0800c1c904004000030252103912400d94040b0500001207030f15070484890220401c295681d6843d48020b602d1f0071641c21000c200880020400490038126442c2c3c80b20032030310140903109200920f14221100702005840e200c040c0d080c19510b5401f000c0d0740071680d40460401c941c0300d41c5400f864080c400c0d07000380c01c540940340108a004aa450300016129114858084511145414014086a03802a1250308107a104100000400c1ca014108a95002506a40303e0051040c00d45843c0c0e00c7c15180070341050190341c1c0b20000111039800c40d9120600034915510840030750301e000203140303201e5015008450021451011300044400c00c1d8212a102019030514110180c40030b8854415401140d00281c03139000002078011072000900708c1211254a041c60801681009042e03d0701154000c015554006002c4410850709 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 522064946 1250 522063696 522063709
    0xf03010e1027031d03072c0103021c050a0812040314040b04170a06050a1a1c030309051203090a0309120f02240d060302040e121c060b1308010b1905 65
    0x504a083c0c5040a11441640480d00c0e10100340c2c030900701300e816000c108a803187c50900356005c510020042a699505640005000040da0280d02020b03c1580c0d0005007082401e00c0009103080d003000100761611003503001100040e004450440c0000c1039242010104916041a1401d84801c4003419041c5400d00d10303052604c0c01b160301041101d101c1c4a611a000a100e80101d40c401c01e4200c50100303c40d640c444061403400410203006220703281841d409001c00d5a91403803003589541525001c24406071605016041c9071240003441290800002040a07a40300080e00d0002c11b8441c1c0da402562560b03030000f403400c072606180024889007208000c84054504412422a214080b5141e4080900180c070510059031107011014807d42c0c4900d0204103524242c8143e001440508015005801007d84510b8443c403540c1041a49002d00314540340050010760f0202e0042e006007085c0c07541d40d05160318403018524817442080b805601b0455041c1c680c1c1800d400c10403401c03900309160003040c0d00385800c1151 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 522066196 1250 522064946 522064967
    0x6050706020408030d06092708070303151e0603060b07110102010b0a090e0c0301060518040c05120307060f061809060929060418060b0f03010e102703 66
    0x102140c09010108901c3e60a10081a040907488400030b00c841c5400801015100324042250349030503040c0002074060411040508501c1e40180050796481c03503403405a006200d200320100b003a12103500301080051001e8900c40720f04d10ba103514813448a030f661a0480c2920802d01400b509013800342300300400584aa8200508804140004141280300e80c01041014903035900c4101c101d81c5400083c01007000030300402c084417100ba4000d02c581030528011a030751801f9510040300140d0000000307001c2c001d481d512000501001071146450500d801c10b629a2034221400503030321149000310100520300c240c0b1801d0115040c440c0118080e4440d09414170040c01540740583e54a502d40e0380c100000b603200120350342ca484011500f5440544581d4a0f04003000d00101414001c3d441c01e20215886e14180000410a175441440031400702c0c01480422b10007840151b2180e050f60911080d80360040001c120441d580442d00c1d81082454803259002030700c1c004d0141c0c0d10481b00c90b2803e030340300481d00c10841d211 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 522067446 1250 522066196 522066203
    0x3110d02150c010608010c0203040f05031506061b030316021501050a050103020a0302130609030524040602090f150c0f0c28030f060504030e180106051b010f060806100807060507 78
    0x3013290b9903419075030955106180c02c00050300700107424800d80c03031028038180180005800030300f440c50343c0d07c146a00c08076010b003072107204d82c00200d0182c0504410041220480c007151003a40e4a9080011079211503120000088001d03000d4000f07091681c0c074904603118100d6400030802c20349035140c18010340c025441203010b401015000c000c0c0c0784400c20130010040003805143c4d641074125195080003400c0c031554400b00e00e04641d12551700c8506103125020320380c01541080c00140c0e14000e030f10000d035103c402540c1da01e40250b448030f690b00070024140064080d1303905040a81c4d00300190441f81985035082414041c0d4020031180c64518007805481d1800721461b107000301c034111551030707865249402c600440c0c211100c0e9100c3c0e080208060b4421152110707000150780312091451800b0824103115014003130348041101c04183c00c800c0046c50340141040e4031450000b0440a101c80202402910081c018140c807031007104085140a90f10350041030448083c01c0107400d5241c1003581c211000c2c2c2c007107407054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 522068696 1250 522067446 522067451
    0x30f02070c08060601080c040f090c11150f0109060506190c020d0f0c062c040209040906060306111303061a060d0b03060a020901020703061805030703080103110d02150c01 75
    0x340080c00c0c154a1001410040c80100140d2400c18001000309130700410355000c41c1000e0200b0000311080161003025200407113070124503c8482c02d021a1079200910602c1e440780304000c3c0844079920741286113801000c5844041803d42c0c1c239110360406640291240d280c0201003048030f2204200300b0710a00240c0e52080c034000d50301c004e803030300000c61540301d03120b05540d0802c4e1484040d00300400c0d07120a000400e1241040742540300d01a032010350341c01009610100081c000d02c40300000c0e0396070f68101c9131102d0008208110000f0642400e400030880360004444091030014a02c142c0c0f80030b8003d80c0c01c1d01910340610240e042c00c50303a40501030402d41501c1c1c1408001c1c0e2501c2c100c1a41c03250040c040700f40b82002d000914103003050826141000103060788102c90301c1000600d40590b030104140040d2030300a240403429034200f800c110f0702d200c1c502c00003a009000218600c801c26a0003012241224042c802c40380d200440700c400c100090801100080d40a0001c2010891024a4402030702113001043d000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 522069946 1250 522068696 522068707
    0x31c060e090312070c030f0c050c031f050a020f090d05030702040c1e0c020a140d080a0c03081e040605181e0d030615081f0305060601091d07030f02 65
    0x1415039850301070356244625000031450300000c5002c204100d6100c48240303090b650b401d6450b00c0260030200c00031880c004004001c0306401c11320208000100064a01400300d8400b4034002c000c29568100719140c007000b250620000ca039010075140282e5001c010764880b5140b82c41c103403400300408095661022129400240b04050141e61948034609098030310b41c4500d1100507038805030914800015180310107100070321b9030080250f15584508029509002c1d42041280d03d21030001d100c00381100b9005010000018204c0740b003a600509400ba00c0f84283c455002a0701e41d000140b01103040c110b00c4400c500420000a008101907801850300109003001d503003a443c400004681c20850640c54000e2a402ca0010803441808100076030700041d451403030104600d90030300c80700401030300e4059405020000720301c0104104a00848040000264030410740c9a0340b9a02e1078915250001210703c40d010174050ba40001d0001440700140705801c2d11042050a95510b148094004001c0e100841c035800e54284107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 522071196 1250 522069946 522069959
    0x1e1b030304110a05041b05130e010f0303080903041404050a23190c09030f1e0b060f0604081c05040503120405040b030a030f0e03160b0714010e031c06 66
    0x39406507016a031210000d0101209100540a042e40310340e00071460316018503038140065210803914400361801039a100140002e2182e219040c0c6c0004000d081c40c01c000141801c03a85034580116031294071115081d0b0f032188d26294407400746100e010501c02034000701c0007161030180e21055012086120019000e50034059281c0f40118040080110710100814054809014401720300e40d0740c0422028030071032a5840b00288500c00c2440300070040301287d4002010400445071031515a10080030100c1b4941060400c07080c1887d05840080c0190000030010200c0d04000007114280c0b41d5400042c260038021001a03654a00800f650b042000780a02001c0f9840d98144000c0b810094035040007604e850405040008640c0c0c071106e60b40c4254000e01301c80000035000580f201c0450100d0401640040f1383e100800d080500900803203904c030541000c0481c0320004040501030030b80c0102d954500f625a90b0040070700702e5150300500001e42e8400e0100814680c0e508204500c080f040c040c0100c0c82c0e554500 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 522072446 1250 522071196 522071203
    0xa1503140702030c0601050307050d020d0828030b06031b0a090801060f0e0c070f0b0a020d0c0906080601180512030c071d0906130803130b04050607090b1e1b 69
    0x101c0c20801078000148403480c040b01086954050b041c110080c1082510b88000031300d00e4840304000901503122007002a00788103460040d210102d000c190200c0701140994071b0a80c0010a0050031008a0b161154141c400d0500340d0660f8411b1040b0700404003d00c5210b1800c0009410401910703081100000c8046000b0a0a001d01401840c50b141c50840e91785c01d161001c00220001845154402d81c14481d40d800700301004205654207400103550402c503100e584020000e0300c910b6000c21829418008125202c65100030b11a0840d0250740d2490801d4031900d004440305002040c0319a00c850051000340700e249032041d0f1054111080004880c40c10402007400c40c10800c042d444a892900300c1500341408450548013164041d484070041c107107d103404076507101a008180710103002940701000003600881e805e0030b03c1c3d10b0207070440f16001441c582480d0481c0e5480080351100000381c1c1074140011150300340c1060b2101034041810b0b201b140303c030b040703800c44a60300070f10307400000030405500344e182104051 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 522073696 1250 522072446 522072451
    0xa0209060904260307090b0702060f030903160b040c0501021501090506061c0b09070c0503030103030e0d05030d0c030c090815130b070f030b01050705060a110c030d0902040e0c0a150314 81
    0x4800b41d07071322843c16440141c5103080c1c0781e001045800c4100220401a03440c0c204844a050124240c1c0c3d48079101c0c41420b40c03940c019078030420b0307402a0503003450303040c00700080960b48a80e114040c1d203200715440e03400490300d070030391451040160446500140403204058000c0e0343e01240c00b4010500700304400103000b1051284030b044602d200d40d254080110ba0400c44015a4070140300d00782213400d0320301079440035564801440040c082000700400d000240d5a900c03000024250840f0840741c031840c1503000c0760004c010404501000c01d10f841851410640103508034400c50f400c006c0a424112840030400d044440d0003007a0410800740d807142c80000814240045004040b01c0d51070742c501800045c400340403909141c04042c140711041c8241400940c0c0040e0642d03100d1044600800c00c0300d408000d4123000c3c001d0f8007180b031540c000441d4001c400d5810b544400d100d913002711005c0c022107828071400c1d44c441c056548403513041040c0750414041007040d00214a480041d914000070305150450b004521045c06 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 522074946 1250 522073696 522073763
    0x6040b122e03020a1205100203060105090a03060209090a0b0a12080c070617010806240d0222051f06180f0312020d140904091b0e0115020a0209060904 66
    0x1401c10030b00a506207290180040c003d440320325041d0383c0e13482d01c3d69a0703100039109009044940000004d50f20f030740301d841960a80c8402500015250f41c69107000c0001e50040c03003403035004002400000359520f201b401500b03010880503245080107030401ea84c3e80703554001500700b60382a400400c0b45019800c01007200500074a80d40d51402d801c0102c032100805005c0c81a80640780a50040c414401076400b0703011490000c900c44403807004485514004581c1c02640750f0340c060761241640d4240c51141050f1103c0304280600040200000e9540284c00800b0507038607910002c624078100800d21085004051241030010090310114206a441050720035034600c503081120041d80c5000d207202c440b0740400c0440ca103503185080045450854500b00c5255000f00f234800742c80340d600c49401d5030500c9613840100c2d8003200b81074111001980c0740c440c0494008002e2190780d0145a40809071101a803000c11012050350340200000035a444620801040b508040c00583e165144114062a61600030740a4000c01e0039 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 522076196 1250 522074946 522075031
    0x40b07060603020a0909080306120a050a0c080c060f09011b140c0f010804050d12090501020c060907060c031b0618050c101d1201060b0c160506040b12 66
    0x10751041c0013940806a10070503a50b81029001800100c809080c1c81d800706080d0382010401c4050340b4020314100300504090260b0140c1c5800c101407055084c4541c0503100c040b81102d1403e03810340f003444117a03c5130706090013810b401800b0608aa622450702c80300d600c1211a1030000c640400c4e00c401d031115804100010300c0da402031141140c075003450b07904522229800d00701591a8601600d405888039040741540c001c11000900105058155900001d078868004000f1506d6106850955030780e8030702510001003921a051002032032912502425904541c0350791a80703101800000c030817400d8074480b0f10880d0b800d0745440a96681300c0c0b241d0492544030f802500101140e41c10b1206004940340c00002d20010000202554011031013103401e9104402c0381914081c16034445040010b00400d8103070440c914500e4001046642c50500090828641218a481c1111603a5840401c80c0c103110314442d0800b400403c0c001d240702118000c0da4154401070101081185101c03001c038130340c400760000407125817400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 522077446 1250 522076196 522076199
    0x10b0a0e1f08060a05100806060f07061d030c12130e0c0702090105040524120a030c120f08040213060e0720030c0a020910030506010b0a0216061407020402040b070606 73
    0xb40d00020840d0042c2c1c068034204941414400400c4200e500140182c0a000561010500948a2408540d1400f018408007502c8180d02d00d0081d0203454150854540665a0b40d580702c142000031003200e22403d85240100082ca01a608000d0190042150403401c12107401c00043c401121a20140c861808541c01a56540240c41000b12039501070f0849800327546400204508001025500c0f945114405180d11401c6880340018818000c40c041082c04e502402c94100e00b0143c00c8004104451320500103e424150203178002c4641807450302c01080000e01041c040707405403c115035504c00004100c903004c01d00540781d183c015140f180c1925140c0010354113805400685c1400c03012290007640d02405503181542940d004c07640e4100710203019220310301020100d81ea503115260b040c0300841d800003d40c1c0b40b669403041c80e004a074008020712009801030710900e821091b1500001c0c0191006c0b515811103003030562290341501d40000100320f030800d50070040401c10301007100182c40414407036440400c065 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 522078696 1250 522077446 522077509
    0x6060e040f0b0307060e06040312030501060206070206060904120c1b081207020d080c030d06030303050f07020c01020a17090603040c030501060e040b16091205060108070f0608010b0a0e 81
    0x10780440d004052000e00d01079003190155408030302d1a0480d0fa072442d00609641a0714002a142d2045a00007041b44e54000c4410110a0b0150001412250315409860341c03070351006c03004c1c0d8072600d08564580c4d20101000002e800151083d24004000c0d5691501e400c0010055545150403107031201d415181213010742e000c21401c0350402c4000d04005141d4107241c240045070340030410242c800c00000784107440c04522401040c50810030365600031361542060214595074240074000b0300066400210008104000a00c828000100d1614014041e03000f0a0350080c43d4a0784502030203650029140400204000b0039140c5d40c600c05980290302450b01a4200c41c83c0d80752503421a9803da0045400a00c0b490401011825006601e54401e01422000e541c5107100401191055207030381185e204000f03100d51503002d000c1c00180d0581070f21443c4044a511540380d86585a02041c64802c140016440d0742c018002410f040c40035002c2040740f4244900303400120800601b01c012a4400c850391200e0078040c00c1001c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 522079946 1250 522078696 522078701
    0x302060f0c0705100f0b090106031a06070302030a030e1c05040e01080616030c020102092806020105060d080702121903080f0105100305040302070306180203070b090f0d1506060e04 79
    0x41d00001d10039103808195a80c50740c4940c1c8800c00c00120a9072451091032460f125040711307902050061034080301c1c2d03850b40c6003c1c0c001c00040185030010007403111501c80e0f074245131003200d0016030140c00035810b10329818000c4019003a81c3c3c8030303020342d8000d900c0203440c81c0381c0888894040d8082912420745a03418510340c2041900168068162548411705021200b0201c0c0310400490000d40360108140d003401c08103a000e4031687c047c640d00b10140c001d0104910310b01c4903d91110144e0344032592902c60b580c0d40d0403800e8030003c0e61140e9000d155603c028000840c002d0042c40703a648041c06003856000040c1c1c80604100c007024a00c268108081000c400f0580d01120b001c0d40318030104c80d40e100c1c2e541400040307001d0b075a001c4034101c28181c1d1240814103160080105070019640905c0612243c0c03084640080f9000c5134082c200e0281c1718140000c580030840b0002d84041003406800440c00b01c3c0290100070450030b002e1700940f185c40c42c455154550010f1801500007070034860b1580c0b081d00c4030f03040a1004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 522081196 1250 522079946 522079951
    0x1060909051212010e131203091406061c05011e0902100219151b020c0f040504080306090613050c09101b060f020d1a0102120301030c0b1b0a0302060f 66
    0x408802c00c0042d01c0c120800a00414103540c6001011103480e030b07444a080c0e10200c022400a40340c016008030343c2d4002d651641141894500c038150000e0005c5103041035940d20070341030303645503888985c0628800716110401c142000301d40c010400403803210940c10045c09000e088044c10b03011240c40d04440015800d102418403400300c580e100520440301c2d90040c0c002c0d400407210b0b00071301300b0416103555401c05030980c101e404160245da000140458007a540a5958250707800c40602540700b020344120a45482c0c86010700c41c6030030103d4285166134040c00c0043c84500105660303882490740c105449560180d20406100300201c0c41d800d80c2d01d00c1400c1c03c0100f0001c00f0b50020041000c1d520f000c0c2100855061035800843c0d01000101d068003880c1642d034040e004681c640c0100a02c1c0c00b0003481c0010030003140c10300328902038003a501d08520110385540144024000540f500351b408204101c1d001040009180a082a0200d42190b00e150201281045441c003401e40041c1c2c0444e00b0720185a20081541c0d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 522082446 1250 522081196 522081223
    0xf0203120a060326040306020906091207031b050112090206190c1703090c010e01141c050a0b0102071703090a030605040308010b09100e0607060e031305040c0e0f010c050106090905 79
    0x42130307004400c688076225500000340000c0d0042900280c41e2610000d40d049168002d02144580466070700701c40e5030f0705180c8010b503940302b82402c89030a900c00103584141501e00c1a5160000c0d10707006045034014203144001260018800c011502c0d04150035640400840c15030782e261800d660013401e00095260205030b980e8020754041042c048040320000308520b0203132080c2012240c01a0741401600d003091000300c07090907010700248540300e203211804142911411040f081103140c8540c042c41d000c68601e03062550141e40049414000ea56009900d01030311040907088a1a214400003c242e540f04581e00440b5610340310014441059089503129001d03000c0050740d1400c0004240000d8560b130752611041090041443c40504070341c85007400c032a001504940c051041080e5202c01983c0d99100c05c0c5519100c0074410300104051800b4001c1e054280450b41d282d10180000070708100d1006d5010803d00e052028424160b000101c00b8010403000f428402c000080080e100d0030600e040c0b0648180c41e0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 522083696 1250 522082446 522082493
    0xb131505120601080603070503011b0201180201080606070c08102a05090613050411040509010e0712050a090512030109140906011205030705030c071701020a0f0f0203120a0603 77
    0x11000250000040ca6002c01c0900c1c080c1c403070741c8903000481d0401130103801c43c68040d420514043d0740240c240e00c09801002d003d6008010030f80e441441004520803c0313100900041c0c0704000710300c052919401400b907150040c1c110000840d0b40302103007458002c4c240f1040c0d41d0291107250320022a40c001d80191004a0160078025003540c0141d80281248a182500c500c10301000c120040d104821030b0240b4040c0a019004000d0b2401803050890706400900c11180320b0042d000000c26420752004845005941e540c40700c0341030f00103641d400700203000e00610154a803982c0303036240000303e0000c11040002e204500c000c03699035410804c603003043d9820700d03038150040c50100c41805400f4000140c42c034115640e00000810a10961070302c01e08600c5084c1c0098154440480c03100f40c0f4440108070b40c01100c400c54214903068011100460a07030113501c000c0c001046040c0d41e100c0e0200e005400c2c240e903046440c4150b03880c0c4034500500d80341c800d0050b40c219483c0e91380c8103000c2c000c015500110428884070903254 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 522084946 1250 522083696 522083707
    0x30c06011e0b030f011a090604030c052b030f1106070f02060a091707240501080d030c0507020906031006060e030601170a08130f0e063609070b131505 66
    0x100c03401d0103c11b2065602d005a61861a00e141c142c11007514082d610051006507920341c3ca0509550041785401081d101d407070a1a0106070440d841d01d041c3d22200301100138266900c880782c0382039441c031440141c0002800200d1a031b04010400902c081c610030415915008021601624002d00e0328000404182e03c0d40d1400c6441c0c804030340c203105a500945030110186a880045280c01041d07040001080c80482c41104001d003464040c43c0c11041c1030f0f0b100e030403c40f200b5081029086058035500061341000c51020030140015003004910b10390700c107101800704c50196113903803209001c232249a0f10080015001c1f144032002480d045c40518014000a45c21040203800c90304e40c01d4407500030781401031a44000180e018202c43c01c50403d00010042006800e030b0751640c65080d142081c504403200c620544100d280c0d103030504000d4103407242c03a100080c4000c0c4032b41c3c00e50010020f140c00c081d210758401e1156840004e10f40d20524000d0041040584554170381038a84581048a19007285581c424090117026 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 522086196 1250 522084946 522084961
    0x110d061e03060e010e0f030a0f02150a0b0103140a0e0601080f070639050d14090105070303140109090308010b1851030f070e03030c06011e0b03 63
    0x310200740c90704088000340c2c40c07842c200302c103004109841034009240141038085e10f0602010000d00b8168a154481e50080802d003070080361103035040c00e0454a401840408500e000086030702c01d621100701810001000b60000440d598011000c4805090040c0c4501c107003041d42809001241c010408100100104509060021f4449000340150400c0100c140051111407150308104117203501216824808405a260007160710307407012a054580d4030914880c0240c1c01d1107144221042d140380c0c29080d00b0895907900458503a40118030543c100b603140d0200c5424440e4980350b850003070001c02000545880e003803401801c1300c0c4050344040c502c48070910807480300000002c1140003c0c00222050495107035081410034495080c16445c0f6500c000fa501903044500c040800d80303610400d0719900209501e1502020400c62008454810302a80c1c00004510f4250040b90000390685000341503d04014901c100f41b86001400d0b444001c03c1c640c94195640c0141004000001814035170002c503240d403a105c0d0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 522087446 1250 522086196 522086249
    0x12020303030a090c0b031f0b13050f0328170c0a060c090b07140c151c0603020607300806010c0201050c032b060f09020c10110d06 57
    0x10030041c0d82ca615049403008001010305080702400c200d880301900c03814500b000049541400c100d01e05a013443c4100800c90b09005009d40310601c1141e02400620f03810041800645c440090300590103200d034031500b00b003840840c1c001d49500554410b8240b040b09050402e1203042d40c6000c140d03107680404003c10041000082010a881f9401010206042500d884201c1d0702c06002d034003081301044089420020000b41c984055114110141152002c400c0d1200701b0400801c102d010881e1101c080003401c408942c2d034050100f1696890400040d60b82e525004101e0a5108403011180001160b03011142101c002d02c242401d01d0003d11102c181e400b1080c00500052800b80c002c5050010700c2c4420703811603102e1411103121100f010103032a102c40300304c112461038401d8914803036600403400100640d84041441100110360301c035084000783e03902d003c4c00d000095100044400b00380c001c01e000100c17044104e02840040c0380c014004556111000107000c821104581c1045000080c8610410030300b50108 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 522088696 1250 522087446 522087451
    0x20d05131a041a09030705010624081003020a060903030f14090108042d0201080603010203160516080a0e040e0a0213020f1b070303080f190902040e150a061202030303 73
    0x9041c0c1c00c035242c8480c20a0008580e05010340f48551102d00c0810034658404000792079514400c3c0000d0108a48507443c005c0ea160440307402040058408000d00b41151140c20104e4100031030401000360303503031250040f500c0098640c000c00081a5100810400c165001c1c0c17040c1c0440b1490b24000043e034904004070107551080b1030740e0300c1c10880447c000c58240079116203141401c0255812420625120551005080348444001d902160703264000620030b04060086a22030501110902c1c01202c440c036098810342c000003d00e204803100d45040c01c0000300c103a1300074031a0110a032203802100115801f00015104420003442071768004000003001030311084c02d040c0c00b400141d030b00036071903c0382114420b440e80035810461a602031304c0ca2085c4107458011507881c3c184e0b030195640b02129910010a003005035801e6550f04622029003034503400c0c00780d10380c1c0054009403004101252119201c3d44080c6454207140c0c0348562207d101c01070122199482c8280802804c0d07070b11071240c0c06e400b2500001d4490200 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 522089946 1250 522088696 522088733
    0x90209030a060f1409070906120203070905040302030c0a06050a060b13360e06061c0b0402012606100e0d0204020904020403120309150506031e1f020d0513 68
    0xc07041401040801604902981c609220413000302d8500451002e603600002d203d0030b1001868288041031203030f0307108100450b0b0341d0040e000340640361500031840300818008105a0850200f4441100102030501c210401c150103030001045070b040c0541c940742214482c0d40a40100c40007009200c00e0034100145e00e00413100d102c900c4012818245020305c00c50080300e032214951000c14100b07007006034079030742c0507101c802d0580c000ca0b5415503d06041c404200c2501411250400d4003042c0c003000074070040810340e402803061400d1780f51040080100d403500107100900b64180e4002000f006820700302440403401301d522398946105011101d5000c6880c0301d40d481030190003075400007050a85500e80d81c044400450344035102d0a080b02c0c107064010020300c00080c0444844191045113040d1441d180140d90191100801428100c1c0d4034040302002402d10040696140c06103003403005070b0308842d91910305060f80358040941d035241c20648242c00c540006101d040d031001300020071008644104140b9064607103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 522091196 1250 522089946 522089951
    0x30702010e010e281805040b070c0203060c07030c0c0e1801051b0310050604030b07090902030f0f0a1410330c0c05060711030c0d170d18060213090209030a06 69
    0x802c0303400080782902a003000102c0d1404c0e1016109810046e88600e22035801035960181585a880d01103640d25102c01c0082c1d03250388804017140311640070100400403030f4864102a6480400e940e82d0751041d28803a0301c460210301e00711f41040500312170b00300032001e40d0781c00100810030707032410700f464100302e03403001040b4810681c01200180320920414500f03000f51000509080d01c0307603070720710700f5615841080350814001611070000203201101802503a01510310706a5003005603480c145211031454004240c0b01d082a10f41c02d04030504107051040d607010300700302c5160000980c1406424200605954001c4040740071000c0181283c40c1c11210b0b403a10b11195240020490099041908100101d5046254460000203003035040024840100303c03166002d40c103950841416204000743e0012280c000350103500f440b651800302c1111a002405c822000940004843e94084000c2130802d812003c100c415907400203400f100c900c540741c081070041580f034205500e008500c0b004a51140c600080c001e19168 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 522092446 1250 522091196 522091249
    0x702060f19150b0409023c03042105211e040507080d020304170a05150606040f03111f0509090c1c1406030304050a290309030702010e010e 61
    0xb612180040c00400c101c405140d02c81303460303280d0701000f5440481010660084d0740c0c81240083c1d100b04640408500e000741002c034540d030203594182c10313500041c4100c906140f46008020200c40500c0b500309089003941e50340e41c4a21f102d644403c840f80e040c01003003141a043d0820401034041c00890070408003074204000308036864502d00300c1e01d050202c1e08054118010801016000c03903000001d4800c440f05140ca840c200754200455035211640e0040203009130b00300242e0465041103100e59640c1040014103551710302030b52264044a00949034000b201e04282c009440082071601810b0600310b241201c0700c00320352202444018101d44168001c09020702014000121480320306020b546101d0f0903811954a0130303900503246c0008201840100004042d44000f09443c0e08002090f24103481000d885803002600300100001940392038510042242268a6480000c0a80101a42c0030f070b24100c005648521440c0b00240c0032000c41801c1a042010140c0c1c20b05841d501d10500030018100c02014180300c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 522093696 1250 522092446 522092471
    0x5030606041a06190f0302071203090203100e011a09010e01170102071e03020706030e0d050c010b06041214060601170702120408070f0b0711061305180702060f19 71
    0x411001c040381e000f02c1c0400d050b022442c81200072110b000b99680c0d004852030801206800301d01503103601410300c3c4859070280b03105071b02030341c0420b4946000030100c0e0b9101c1e0240c2c1c51107003a00d8842c1030030b140f0b0b46d444140240c0840c5030840000d04d40001185c08901700c0d0304290003450802014072034002e05480b884009652814290304540c100e58000d50f940205040300c001c0201e001000850071401880b0340000010082d1292062220150340a00a040d00300d070308480464031508001b0341c00e1400c1d5a9480260341c6960b62b54000d1006141c246007840005034503003049822161204032550440d005103003006011f0b0b0340003101502840c10861a00c005031680c0c02c081f894043c00c010b03a5440c0c50b03000900450b8041e0000b606d50100c0301c40040710094191100420302c03103401070392401054051040144805441e240c40038005030407000d06d21a01c00c0eaa5503001a10b00c0303000f4140a140b080c5034806110100350705204040e402010544846003600303006460f030b081c840c0c600300031140c12559007005000741d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 522094946 1250 522093696 522093731
    0x10507021011070f06110c0a051009090e1c1b0209130c0b1911030f1c02040b0703090803030f06041a03011a04060608040503031f050415080d090503060604 68
    0x5505101080722907150301c41d01a011134061600072140410742c2c91001c00c4c0d0b1280000b42c416640c81c1d015001082071b620b4401800300031082100d5440c28480f81300800314a42025200e00900c11390788000a1a5410400300903202c2c481024150f441000404140d0059070006080000140b1368156244000740d55900220101e84000c241d0040640b411402c00080c1400c407a00903258000e060b4001c1154010100c2040d41c9840040d20030050381d80040c040d480c80381c010728014201c02c0c400104c140c102c42c1d41045003a002c82e8803a8110050207440454023406040e800b40e006c0015112041c001e600c2c506218450f070104a1005020350300c40e40e12520302680210140840412048001d030007801240049200210380c200299020b82c02940780080008585100351082d134020754108028516542381c0c0c1d08040404a140d1105030180ba42d004d03000500e9407124401d00b0b000340c100218280c2d00134100750f131a508100c0400b0340c0100704540b07144148600d60703003c44cac1303903400400c212400685441c03140c0001c101e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 522096196 1250 522094946 522094967
    0xe04051f061508040201030e0102040f03020d0503090d0327060c02150d0606030e160515030702011d010f141b21040c06030b0102060c030a050915151e0105070210 71
    0x3552940b4031203081e0b03180e000100c2902561007603c0604c0805803008a96080b03000d14810008043e4802c4003c10140c10081c02807141f00c0c1c010030680f4508945240482c0c2c0c40001d50a04070001a0b410304402c40d80c4100a031003c402004c98804c0707013041840c103c0c0041c500031038400007a1103400d1140171420454000d40c112144281c20600074002140da442010300182001e020808441c001c094108281c00b418880b540c095440c01051340d01c00504031032250320160130003050034066650351680f402076480d1b040c0002101c40b1760b80380080b40d03a80504083d0410380d4002c0014203010611a0280103003c0e40340304c02c407441910000905a15450001c1302d1488014070b0342c000007015543e10092100b070114004c003841c251400b948041c04042c00400049030348000c2140d0f00c540b503031004d2000c94540d4086400c4950005500021545000e0054540d403401600075601b2110783c10303180c89004500d0800c44640c0400003c04c881c0034110021480010b030043c4070345c0c0c0000307105440741e2840086030350040d064540c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 522097446 1250 522096196 522096209
    0x3310e0c16060501080c010314010b1e0702031504140705030d030911090915161b062a1106090604231204260a080a030209060c070608010e04051f06 65
    0x2540e4505c50035444007602400a80000c0c103202c503060030601c962802030b0403108400030f03141c034046502810034403e003d02040b84c943c0502c10031248002d030f035080180c000740c101c881003401d507581818984030071080c146e42d02c20071042d00644010801c95501080018403052141004105040b143c50440760031165070421940c08003803041070010f07003507001518802a221041103d140390320ba20601d40e010b484c80d8030b20840024843c0a04074400340c060000c00011900c00c0802207080303100502000c0407070500c0e6000b4107443e1300d100346100700f443e4010a2620042c110710040c0c81241001401d2a8540c00d0051000d0b100120b4180242c03090304d0f2141ca44144603503480305484c01006500180e180651091040041d9001d50400e031031180e103414070012400020b840c009120700c010365502c03400c036a0442a071082c141036003070007406404d0715500010b01841c00098042c0c40e1945c20554054640300060f004611001100400c00c00000c4c000900d503074406c8a00641003d8403c024084207006d0042600b001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 522098696 1250 522097446 522097451
    0x307020a0b0316170601051b0a06050603060709030f0605041103150906010504180213060506040e06032415151804110a09050402070807020303310e0c1606 68
    0x108038180c01c0c007850064101ca41c0f0011030b50400300c4210741c1940c0081c0c012a0b20340e042800701c0c00a42c0614010146210b0004060343c5070085426080d051080c001810b484d0b5580b100c04124117071800303002650307104040d070420146680c00c41d00d42281103e403040000384482e60704c0c80030906000e900101c00c1c503040707001411610796241c80c112061025405a50901c80d07441100008034491500c0e000301c10702c04041d00d411aa0743d180940030030084130244074900080d690f60300c1e030118284c2c881070001c001800700349519150908100d001e0600d040c082e2041d01c03600d82c071000040904402680b001d1500803541e091205501e000c2640083c51440b0481c0c41c3d640422000506401c2d1001042400d09081d002202d041202442d081c112004030320030b0a08000c0051101d11080c01a883c16a001d044558007a005684c10b00d500c90b40424078543c00340382841403500d02448c20b420034885802c14900085404042078003a185841404c2440500c080e01c441041c082c0070a40d1140c092400704007400046d04070340207 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 522099946 1250 522098696 522098699
    0x2070b010303110105071e030203150603101e050a0308030711060403030501090b0906150a02160806040510180b070c0f031d0108010308030115020a050f0607081e06040e0307020a 78
    0x14044440f01c82c402c240650a002c0041e140500601031f0050620100040307225000c2c200000710020343c00100405900d4401e250071040707a44813003002e140b042e08404e02c940042c5040510113084a441d42005100c45107148405000d19240c2840807c1101da0140f03078079031a500e80303100c01c0e588080c01c50902400c91140c28104010301d54182c00c013604944400b582000441e0300d41050012501c02103855a8004140c00d00d01c01c1c075050500d0081c41a100d192059a81410382080846100b40c03085e07000030343c0f0303a001030b05000a02c0003c1c031041440c6601b4010800141410a46000b02d512010001400c640094000101300600074007080203070070741c49a00c0b0f600c86840381c60f000d04829070841d120294424100404074032540280313410303410b8036040005a411a0b06e06101d100884000751040c0c0214055110600b0005804100b0645c801c40340c00068481450500c0d40200001e5004000503041c00b04c0c914280c840d1841c0d00031082e044102580c000c0350003110314810f1072a5104060000f9000010380d01e0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 522101196 1250 522099946 522099953
    0x100c06050a060f050105340c2c0412080a0f02030a1b0c02060d09031103030a0c1d0f090a1113140901050918010912120f020f07140102070b0103 63
    0x2102c015655810342d55069203446000454040c01441419503641c1c1103900030320300302d510070141041c0c24200020001c240180996810403290200e5004840e50b80c02507009003544001e40d0030741c80001c2441b4424248a00d001d1301c40042c880c888001d000c0a00200c84041003101e0580c1e0014103c186030458199528103002032030b01300401c11440809451001c10200c0400b15100e80341d00491240c0042c151410400890b2202000740069001101804204a400c18200707400313101440c40364029400000d825040401e01074a948140c035046009050604900d032043d584a280c145081c3d101030b030300c0c03c107203990395000c2c1d200901c000e01d00310900c10030200308500780c0010217040000b510826030300251180c120b10700f400341e00340c401c0c00740310740c0847e005000030303101408201030503034110120001040c0d50720f4540718900040007034004003000a00040040a01c00410b026818031481e061808624000c2c541d0700410b07260080321001070102603280c004a2050501350103a070142500310100c0b4009507580e24 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 522102446 1250 522101196 522101201
    0x31d040513031d0d0803060f09090708061b0a050a020709020d09020a0e0c040506030a0f050411100c0c0504090309030b010e010e100501020c0607021903150f021602100c06050a 77
    0x11400c400050441a103c0e0990074001c0c160000070a018100400801a81e035a8070041d0304010021908a03242c40100b581360b5407459900ca0241850b00003030031045040200c02401c1c014002c043c0803a22601121221101ca5803170708543c10007500b40780c002d403544000b032004ca0901c8520f80c06800c00d00c0c00803a5000c0b00e54200e1f44034480c0584202c0343c101100795100340c55003500300d04883c8ca12403a10180020441403c00100070355004031012030024031140f1040064040f14810b403020380303452030070710f2810303101307041c516047d1010f80356604041c50720807510350314906003c140f4002c80d40116128008041018001c8060f140519404160158150385466403800a28400d1081c901c106800e0300c0868150008004841b05548042c1e01609144e042ca0062008a502843c8207d03000201220f60500f050354164100c40954820b10240204220003080350088d03401200d408000180f04201005824a50010341d0b80d500c4d90503110110b51107400c480640744404c64010150407142088108000001c055 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 522103696 1250 522102446 522102481
    0x3040f0308060f2d03010b0a031101021203010909330e070f03120905060a14030424060501180e15030109051606090b0304030503040209060f10050316030c0c031d0405 73
    0x403c0b1001076403034513034201401c1c0d0b806540c4568010741000010300100303013010340e168038121060045a11625105040100a500992010842d2940d464152301042044201004441c10502d01c000504a0202a00030800c011003c0c180c4515610084440740c0300d0140b00d49002440c046034a03a1416640b8105641c1d0943c100c83d14800060320071001184d0b5181803000d4400c00209940c46a2030411030000c8402e4942c40a84151883e403aa01d01102200e0b07045d1182c6803190301c1c1d10348042007040c1f83c0710000d03002e02651000400414402d04081c010320440e4030b80075034040e0310303001c80031800d10070400400e00605a108000c0d129010768000c8540a00514422000700d4141d641c600300c0c0107076101d0b0001514002901c0003400600c007000801c000d80742c0340c0314154000d9030044c82e6031200100701d000640b0040704a013182d0081440881000081c1061440c00300b040c0f20a0b080601401c105442c0007800366801c0c140080500c41091040702499603402c000341c0711008040e00c104041e0500202c49070301300080 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 522104946 1250 522103696 522103759
    0x30a03030e070806010605120c070638180c0c0d1d090103170a1101020d09020405090c060f0703021c05041e08061b070605040305040807080303040f0308060f 69
    0x95100c00584410b0004800d0b041b0f4410b580c0c1c1508040035181501841d82d07014202c1c0c002c950090100758003081951183c0841e500c1c0006a09a42102c1083d42c0440a4031303482c0200e981191204012542d9211030701c50803503160300324142c0140d40d41c3e40c140c15840e0b80140400503002d0f106441d030303032a050f07908806c034030b00c0d145040441c110b0040c42500c01c000d0460313001d001c010036146100202503101c01d2207030054050320006046c11884108202d201508a0300012001d5544946407048507065003051720030030303401c80d00c5ca10191101d15401000f0542902c2803486154a54000050f044c0a0520a03c020500015079503040c15034410340141c0244a600540520001d40505814a44440d070f140082c090464410320041c0c0300d40e94451030758181500e01403640070500b030313030800401000440a12a07140325071b109803602d030f40300c50820050500d045020b0700600c02c658003c00078800812403014140c200142e241c1b820341200d603107620115401c203140a10050700701560300350503d03001106864401e0311254 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 522106196 1250 522104946 522104953
    0x50c070b070503040e090d1d030c03060c0a0f0201090c030b0615040308030601031b0206010b090105040305010212010311031b06030c0705010903021506151603030b0a031103071508150f030a03030e 86
    0x16a0120103481720b07c44482080460700400c06000344840c240030b04010b00a0003030a03100700e10413410121f0700b400c00071a40842481c100041d00c52410390800e07000503807100031388000c022071070050b680c03408107400364007014050409460004515660f1103100c070f850107200d1070141e51250b59919141416400a07200c1c1ca01103801e10200c00e42e08601d45d070222039906c40c00d9008082b5a46094624141a0301071035025040000810020010075024001003000d55844e81d00582590300d541052500e5140104400f8880c1d0021008210b80c02c400030006010b42c60308444150740e0f61074036000e541091044003c020015420701d0704103810f150700420480d41950700314251101075500c0c4c008010844051003134548017084103108a204640701401031244443c82410001402d2180000094000d140c80e40100c40c0380000c2000214641428840c1000070507086071981081c911855014040d014004e10f142c14a003451540d40b0403a82c0d60606c1d02c20b031681c3c00317000c0e81c204407003906005021300142040b201e02d610 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 522107446 1250 522106196 522106201
    0x3120b060304050a02040e0f010207111008090601090b010228110609031504060221010609140105091201061806090b1c0b0a090c06050a2d050c070b070503040e 70
    0x40c00811240300350303403100c09809165003650801c40246008008440d071031240380364000302c1060074401014032a010ba0030300e00c47d00d03061504001a506500486000b000601003e1010740100054101c2c191440040082005000100102d161011221020302002e0162903850051841c8960101501740601f401c506d01f01c00c03803000d000e103e11801100c00d40507880030342c41125034004091a5904144030300c0001d40f40001d800c0551032040b194a40e40d80360207566030700400c14240c0024020004004001c40342c69050001800070305540194501e150180595100b403c0b501ea500394050006001155000c001507000e80550000800403802070001c900d00e4221028924600000881c044c400c40103c4200075284680c1c5a00400c14060000c410264603100c41d5000a040e82e40f0020190042d81d48442c0c56514001c40103203600300c910035400300f00780314072240c0d90820303070550400c3c1e049055030500a590381c460440326807800002e50300c4007400d4400464030341c08120000c0024000c07600200d41480481c0c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 522108696 1250 522107446 522107449
    0x30504060f030902011e0c020a1517060307050d061b02010509011409121612080f06120a03080c0c060903070b071b02150d1803030c090303090e090a050a03120b 70
    0x111043c41c0013a02203440050805078601d01801001d0040c2118030701003440501580c0400c1d00b80343c55400c031003e21888000c1445040ea40720052080345a40301d0000e21190506a0100e40c8685071030162500895040c4110418071407160070001c280c0d940c030304000e02280c09035040280289420340320794600d5400e2003c9101401000300035640500d0b100406002d03040701c1100e1249003603100300b0300e81d01e20b80601c1d4990320110f28002458a0800d145031120101460109d6400d1003220000309860321400c0c01007001405e0b000000fa031803007131a078103040204203a00c80a00000881c010007503048424801c0800300b040445000c4043c1003503d10511071458151a9590151018150b106803289001d0313036580103201524144810941e0340a500302403601e000791031045002134480d2003214080c08020141c042080543c1031040ca500140689421881942141e80041c8046501e1195122b0400d0b4580800c520800034000b241c012680041100c1005c1d680380b8001d460300c51042c880c442d20030720f0041c1ca030502d03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 522109946 1250 522108696 522108701
    0x501030c11031317011103060d020d15060e0c04080303070e0f031204090c03020c0d030908040e04060911063c0417060f0408120405010902090a0b0906190608040f05010207030504060f03 81
    0x50890106d0203419582d48100784044214502c42c1607900038810000c450205d01104580084c00c47c111030041201410404141440400508440507410007008108411000801943c1e04060246459201e00c81284001264100c00c2250560b15016800000c0700056500000740200c0c0e4018130f080c01440080c03c020390417030141584509040e00000040c0390790500c65403046c10950710901c03072141083e840d40d48030f0003001c00468080380e5003a918501f490a004084034003078070466080f5500c82c0b80800f1000c0e505c400c0030000d0001255414000c0020991909420038030b0264280f1841c0162074a9660012760032100b00c04c60603c200b030007640c0c08101c030070440c94809840b85030030258031841c1021490f051011000000d0040e5215580d503d10030006a8581210030f01403125507030b01045280030a8200080b148003d04514494141d403c0110b400c4620191180e08980c3c00e4182050143c0c0e481c10640c48140381a0030040c290351000451004054006000c4d1095481315a1501c81d414503a036002e408 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 522111196 1250 522109946 522109961
    0x10207050c040218011214130302100b0a0603020c0f1209090703060605040e071e020c01020c01030519090201090317071226060f0a0803090103150f0501030c1103131701 74
    0xb1240071280301340c11030350040030043d000e51b0142c14001004003440c003607944071180036101892a010a1003a250070725a04110908001e5205081041101c001c4000180104a03d2250805258010610440346201408950041180181900c0803910b9450010581c1e078080c002044c400c0000788080b0725418070902c51017042d640b00b030b1034483c5814100140130100180080100c000c200c002181c1403914000e1440c00f09052401d40c0081641c0e108050001e8103100402c041d05042514020800c0030410045c1341c5e100c0d82014003800041c030301480740012501d0300c0507600080d040300300c1c0b21035074074003403803007030000c10b500c07070140c1c3c24003032821140c500403108041e59407581700e9a00510001030f17002194242000c0e4206100401c84001400b80c8800308100b960075a1004450b90400700e151504c95801d0700030b110b43d03000c01d4509201c0c0d89040100740021840640903050402d5541c0710340c50710490040b401d0004107d50a000c4a803658034070b4588262100311406025000e841c400010103003090305009500303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 522112446 1250 522111196 522111217
    0x1090c0e0411010c140f1c020f060624031504060e04200406050d050a05011515032016030e090606070308060a0f15081006050901030b1201020408010207050c0402 71
    0xb00d85503104004440c6481143c40075280c0c45152068004d24240c00c1042001204010004c0e01c940450b00e1500c4003d0b48954030903d0070b5410400c058083c1400100361240d0140d0110340401c1e10181d0880d4040e03201c541510500170351175000041c8004403801d2122440c1008041314140046922520a034030b103100d041c1c030020101e03088800c128070305601403102c0100007000504000b40f401d55070b40c00115100e001c40810b03503d80d04480c601d03c1c01c4c0002030003038180b00402545014440da03d02881c40d00154040c0d2070000030181d0354040e800e80c8400b880c90350030007010b801c42529110440c804400e10f900040310002c82c04140c01003850282da0034003400346442003400400d000d042061a81381075821940040141790f0010350344078046071200039400440c001e800303104200a001003805034040d00404001e4103a500c0c603131f4128002c000c02d65124048403050842840c01080c92074900300401d200303124030721340901154000704000c500301c14154003424100c7d005404448044c0a0602403200720b206070031140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 522113696 1250 522112446 522112463
    0xe011a070f060504021504090207030e030c01081b04090615030e0d0e061c090501060e10030f1e0221010c140301030204050c071b0e1608010501180b0301030501090c0e04 74
    0x55000c10450fa018603030040c00a001100c0075032040c04904d4055001d130f000b43c0042075001c140e040074503500030035101c0d045900350000c2c000c0f102c4402c000b800d400d0000b0040101c0544424000154164880a850050070440024421075407112142c001ea410040149030000b40303130083c0c0d0031111200080004e80705103103444144c5c004c0300c0d4105200d5075038003020380780e0780c070303125401d150300c64540b040c0301c0c512095001e0b1300000b03545030502c20518490f000c05000089080603000e0180040351148120350b035450327440190044000710740f1454101c0c1944440c40a54000024035803203500a405043d1f2004000b140d200800695100c44429100f24903220707045070700d0410501c0180010305240e8131054012400202260404069030f9481c9600d00843c82d803080c250100705410003050810840b00c3d90441d0b03e00b8804242500c1d400c9005100c1030051282504001c441620000303480661900f0700058401010003550342d41c0c490814602a09020350111a030b80d250000004044d880c51201e240160f0b03201049 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 522114946 1250 522113696 522113723
    0x11010510052d060d06030813080d0f05030f0709180501180207110f06040308040308070303050105060f031605040b07060b0f12192405090c271e010e011a07 68
    0x900541d03400264403c4d034110f41d40c803004000b26a640c000b0341100f00e40300782d8240319242482900d50a060000d0520024000a81314565103250004181c0e640901010300940141c0d54000c801c5a44400c240e002c001c611b000c041d0b001c2c88040280d000b0a050311054200c0520030601e0b03c400a003240f05042c405840000705e010080901c0c504001e50405580340180b60504254480d200c2d07520340d03030041c0c2c01255615400503180e13041541500a0a004101c116600b6041c540294002c060b079110040c90800c0b41032003d2410803c0a0203001980e001d406203c0c0000d03280e030b501b450400c00500d11030074094410000e2301c41013503051034942e401003081c00914014190380a5540c01c002526041c0e54411034004215940319031070724200d10310610a00074540000325550401c1d00d401c0b800c0182008800e80181050019458170100a144407010500c00c0000c4040594030303e03000783d454006603e00348038010142c0b0000201d16800340d40d411b05036801c2111141150070b002c1d1007202280300e50340d002000813156622 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 522116196 1250 522114946 522114949
    0x1081c110d1206050a1205060f0708060613090f0e06010b13031511310b1c180b090d0f020705091e040308070e0906090c090111010510052d 61
    0x50440203500b20400c04500162200d00084803250503410540030410703845411070504c0010040b0035000710020030b80c5d4586003050b1900070003414000700443c1c000c0e10001104071541c103208000c40d00400f01080c08001240141c4550b4015014030254175079140705090008c101005a0700840700003021200c040c0843e1751071039981050b003149510500c7e24455483c0c84090400c203189004041040f24020040180313942c1344a191520b50a03c0407188801610b90303404e005204d0840116007115140080036850317030303501c0500f06000c0c0c2080f64250003c0c2088081440800c401d450816019114480c00d9400640b10a8030885549588501da030340141d00c50350040200f400d11480c125041301e40752410810f428034810190011103400e8404900142c100010040c403180d00c90f101c22008841119042d80390308103040040c0d4840e8001e003085001920000701407001da0300450400e00c040c808a402840540381c040300202e0380b40303124032515014410560020340040d40041020050740384440401041511460 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 522117446 1250 522116196 522116207
    0x31122080f1f23040303290d241505090105030d05040306110403240f0212162a020f06251b0b18030f030f0d1401081c110d 54
    0x5014110201200084150180e1000f07180c03071159005e0780f00030a280b0140281141f4880f01c0c109003090300303070181c110702d2000c0c0d485981c2040401e400a50003072611010104002840c0409074940c0101841c01c1801c03444040f005601500300e540403a100c0c420341e80d98200745512051841c0040000510420040c40000c1c082c0d030044a42da80c0c0140f4240c203040d203d80d50400c6180c80010b4601e4012540d031501c4651b41c420340158046c61445e02025070801e208000c0c0b0b00208500a80100710f120010240c108180e03102c3d82c190041c82c140b0710180c000018072030f003021307031164402e840c2070740110a1a681e903c03190400304100c603030300031202e03a4082c88203c04160b640403204042008546407102e00b1680010100d100068401811400b03074040d03030721206c15451241216003500c07807034001d0300030b0001c600729460300bc000e40c1c10544803607040c1907a61000000150007400542c000c000380d07042800002c034803490b0014060030060451020f2801d8060011025520a601c03800c2d0b05449034080011000344a1150 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 522118696 1250 522117446 522117461
    0x902070206070b0a06030204021c1109030d032418050106170a0b030c04021b0f070f0b070c0f120b0f060303040603090f0c03030206090714010807031122080f1f 70
    0xc4c200285242d2a40c1c0002c4c183e030f001012070880040703100803a58400b075451140e00745070b240d200c5070985446006004a074603003086403040300a0540d02c401801001c11600f40c07540450680440d8003e4050b2240004080c445110246081031880c107000450f5040c0102c4a9504003000030400740f00d550b41d003a410034003512a14800f1605802810f51800c0640c69500151840818112960b40413504011a00d854410f0000d05440550b114140801c0800560003c1c0411b941320301a58071754481d0141042c3c94080c0d03180d40002070400002d02c00041d009103502d01c04500c01d21a1001841e151a818400710380c24100345c07005945074008000400c04c0600a50000300d459214024010300d2103500d803510140032469034000e03030168010100f007143d4520203001540190000880c3d0110480c20f01c00001d04030b400003030050041c10780d1601d207401c0424030341c410758a0305004442c1c034081d05025610400c0c18540d031840344c00c0781c9104800382c5290500c004250003a900c44c1c080ca201180e03401440081c0c0c0079020700c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 522119946 1250 522118696 522118711
    0x1200306060706090501061502010b0d021002030c0a150f090201020615040e010e0f0d020d0206060603040309090e1b01020c010c02090a090506130309050103091a090316050a0b010902070206070b 85
    0x2c1082a00041d400c0c092901c00d20702580c00040d1540c80c0800c1148a5070303a119800c001c5914100c840b44180c0d407010602d5003102d8058035021000303605488164994810080c6284079840350b038069108004000f2819440150000c0c01440007503440e0b0340007000d0781d40c0380c1402409600b0540008100d4440c020400c01205001080445d001401d03554044c2101e0040310f5120903900003114020140200f002030500b14041c9200900c0c0700806510004c2d15000058045c5109120001c0801c05041c03007076100c80f01500354200100500540300d41c0d00303543c403e0020600046c51740341c001d401065600104180c182e901c010b071030341c0254100c240e080107849100100070150380c55451031000b011980800c0218032032030055a040c6211003017810042c0c46070781580d210b0303410141040308207800100101c0b00142c0c1d03e03451041d0b100c03e40e00c8003809142103000d46100d025203503600d811481c040c4080000d40480c22802001803c07904d03621030400c8000c0e44141c01c03029401000c10405600007032242d0b08800d6010a8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 522121196 1250 522119946 522119959
    0xf011709031905030114150403300f0e0108101712030f0703111305010c051e0c120102031303050a05040503010c0503040b18061f050603040303020a1101200306 70
    0x4190010388441c80b0081d04540000e03804001440070b5106040310242c01001112070340c0c944001d21021400c80d2103140001805040d0f00200c100e0314a45582065240710101c4030301020003a0070b00340003800c80b080e6020010005416032419182c40d4040e1358034501402010164900c202d04005044c95610043d030b22a04841c0b0600e000032654806010165000d4403008101c070302c1350b0906120043c25124100c1e2802d801d44c20801182ea034009440b90144101c400a00740300848040d9030404905040321080c00d0040300364194244001f240c00030410907011700c0106c4d50000d0740f140210300c0c0740c200d0108a030312251440c0a0401c09010a005001500d45501070717262482c60203454901003801e481001d4110000314001106010800580b11026588446107030200003134440c14261040c0c1d100e1000d4801b52035108031101d100024182c4420060140c03c0181c0400e50fa0f00340391030010001d512400c4082c0004418078110200f80742c060250444100c1141d070030b444001c500c6580504203a2000e460180c0c40741 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 522122302 1106 522121196 522121207
    0x301060818100b01051201080c04180b07140c010f02071106090306010e06040b031b101106010902030c1b01060f05030d120203070306030b09010e0c0f01170903 70
    0x10210100810710f0320380c041c016140b511803020b4280d0309030042d200100d03509100007800c202c5604c041c0c0d0200546c8019081510711031213560001091240080c0c0070032031040c840d40004000348031a100c07030752030300504088d0309007159110102c000c60303942c0118400051000c00d9082b001104000d403005032601c4003020007e52561014010f1012840104010901c0e1381c549a2009460302009411a4104030085010740154031500300e50f98400e980d02100204810f00c43c0009911420202009040d00c2e401c00d61a00c01035040180545001c19043c80440321000e2000c40007030780c0320b0303a0b2000080e10504100d01c60510030810740200d402540200303215060704d40d00c903110140d03d2403201c80042e00c236101c0200c1200070b054642d0010b13020a501c10309112000c034040d84215203c035040001c0b1500b101c0400c0900146d501d481184901080c0358510f40340d8210f03041d1080b035501c1486081582d1810 = true := by decide +kernel

theorem cover : BRFrame.Cov 521942446 522122302 := by
  have h0 := BRFrame.cov_init 521942446
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 521942446 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 521942446 ≤ n) (h2 : n < 522122302) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
