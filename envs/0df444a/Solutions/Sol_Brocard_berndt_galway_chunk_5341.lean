-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5341
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:33:09.077478+00:00
-- url     : https://prove2.me/submissions/55adc808-e5b6-4746-a497-a8b2ddf6aaef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 960431654 ≤ n < 960611510 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 960432904 1250 960431654 960431669
    0x15040806040b01150e030c102a02030d02070b0909070314091501140109050f2707031b02030d0507050d020d0e0106090e15042123040812070228 63
    0x413401c1d142c4141c0703d0078082041282c01401040c0451800007002004440c8014260a00801c1300c401e80000100103401e0188a0150760300301c00b0000c1e2401454181042c0300300750800c64000131018400720708040290340601100395019512680d80700d07820307402854180b080d21100d00e080c00c20460100030010341c07050801c0400c8002004c80c0d07640c100710b80c400b44640700c07100e01148504406001c40d051506401c100e40354000d001c041c0c038440036860a00d0028002d0103003a1007640d6030081040b41da030180108621000c0c101c1c9003100c01d14440c0030003500d034040c0c0c2580c22480ea0b20382000c44c1c25544154207880070000300c1c2c44110340d95002002c4e1103000740541256280039500700000050760500c184150300d20252183c001c0c2404000d85211600950720080c4125118103007000110840150800c003507049900544445c4141d210b4420000406012010300c4020703400200414400352801040c0c5c2007801d2020ba9446403921218400a810b1a500c42c030b40403110501000d1001003490204084021280390 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 960434154 1250 960432904 960432929
    0xf070314060303040b130f06020a0506011d04022e18141f030615050301090b0a08031e0903060702011517030a2007080c130506090615040806040b01 65
    0x528a0300304011904980c00c0398141c00034407007000f840522400800322140c80404415046803151060540ca400c1d981040006900c03080b420000c002c807c00c0002c0c05080300d16001070004070760701110384021400800c024025407100520668a0410309105403111740c50180450501c1038080000380380c010a190b2056a40c800d040f00010216200283c92075a00c20290a502c180034000200b02d41d142540803610080560303619000a110591000b040120031442c0d860603501d5140030350003415a0202c0203050712071a4280001c01101c0000400c5652040e01c8084000d506180c224040c0b0302d50258450098040c00741d070302009280e6034194420100c0e03611003180d5051598448044860f00e03040c03151541040e81c010400040302c94000d0003814450800e80391034000c4000506402c5080002c194000900ca51001e220301c0224070f041ca159890b08080d0080801072442c0020001d86001c0c0064001070090228686018440120200725000f41032074000701d60b4642094a0092600308091095100322002e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 960435404 1250 960434154 960434171
    0x70509040b09061c020d0c06210b130b190e01050a0b1c0504020a180c111b04050703150305030403020112053d080307060c08010803041a120f0703 64
    0x1814101d150040c0301c0079056134000398150a00c1444801940740c01e81c1e02c125201c030900300094800704080041c0100b641c40310b01d50031180090407130010390501c110b07118900700b070b0f032000b8030351582c0004400d402c184003004620804048003040c48001c1c10040d171207600360048404601c1e5054036aa450490307505584144040d51380e180d0440203802410381c00403080b00300c02040d942c2075090760441078116000403c044100c0e941d5540d1400b9950848410b050441c0d00e90000d00c0c0103603000200c498841e02d00b08080c00f001c068012000c0703040c0d0314100c00c4da44075668490115030007034800d5000404a521900680e040203440b820a280e6903001071000300e00061072164910a08a40c902403e070085808014000e11310782d98040d42e180ba8030310781d05100701030120180030000c074400c0c000080c001407000c41c1c050b655030141030407d81c0070f50798a51514410312215100400a01d1800022141261500344a1150448150859404a1180c40705c2520250352510a01a0005001d0001800b0742c0720364800304050207 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 960436654 1250 960435404 960435409
    0x60b0c1605180c0306010306050904030806040c050307021f0f09030909150e13030c350711011209080d0606080906070206150d0b040b180102040f06050f090306070509040b 75
    0x10810615482c0b441060049000d083c2002d001d03581099050601084072903c88020500c0c1250858040c0c2c002004001401818205482122884507040c58024a54585040060350f03e030b036102c00c140c04c05908920703000110360042d03000c0214540d03c0c8600b403010348103604000700f00750140e000d14540c403864103c1020000304104080b508540c80d94408180720740c0d42c1e029408ac0b11a10031829428440d10210040000d5061002c61061f855800b51005401400800d0000c0c140792503144100714400400120011806511000044900034600380c04e00041c0b03403090b035000e041000c00042c12041d000c91030300154003c0e40c0090040d42d005540e0031500e552002c80c070320344d10034050341c003203015070854004200c121070100048402048081c0c8801c00081c03196807599400d60f4116820f8421410034001c2c0404580102e0008103000e007000b0081d42000d0424071800360100d41403040300300f8003400081070741c0b00321005020b40f001e60070001c09859281c5000742004d44030b54002d05c08036100d940b80c000c5024207032 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 960437904 1250 960436654 960436669
    0x304080d0503130303050c0d050a0e1504080d0e0a0611041701091212090b0a020705060f040c1e0312020a120c0807061505121612050619060b0c1605 65
    0x7a01c0388440c030803d0340541d40b02540101800340c000107024404020150031561540182400380d42515400108072601001c21800c043c140c101c2c212130306100c2418070021074551b130306a810003030000c10009540109400d001d8034107078445030000d20481c144103460318814860700242c001c6907100211540c0d41204680c1d0700c0c0c225011010010014a48040786400c00380c070959900350072140f500000281070744180c58501320031700c0869110350415000120001000000d0004a41148509207030f403025007419610300c13001402c0360040c0d0088080c6c000300c40500301c012403443c100440d0401d100c07003101ca00b907140003500c03500341c3d100503501150600f400380001c0707101e00440000a030700443c00d903080a0345a91418094080c541155081e00740c52400411030b540d401541c28a103180c45002440e80d100070710382c80b01c0201348a5015802c12048101000041440811a00d074040e8880c603181000c1032010841c1c000410080d0080980620b000c01d8040302c000e00041e40c01855110892100b011558030300811028 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 960439154 1250 960437904 960437911
    0xa05030c0d0e06031603020409060f0f050402040f0e0403021e010e060f1006050c0705150a090806011a13230108010e070c030c05010f140117060402060a0c030e0604080304080d0503 79
    0x2104000141111703520600c1310309440035030302d40580303441d503110f0b803c10584002d500150000000c4c01020002840c03207004030350061800342c90550805140c0b2240e4442a003840c80ba00c15a8986c410004041510070722940050b030000d0300f02102a20002581d0600910358140c0800d030600c1030b8400304102c18856002240b050320303020710f00d1035841c1c1001001c60701d5421040c90112280304010000c40c045c0c0e2280340c18201c10b0320120556803266040c51004080c1281c0d540300035116044040103001c0461701c8620807184040140d00f00e0f1b503031003500c85898562009944840e100c03403090044d0042c19110b090a40b125103000340d80304d40040e62950321224030917001752084004181d54600b00c50000380501801300c2040e004100000b01c229101185000780c50040284550b0340880c00c0c0140303c4108000c8250080d960002c3c01001d491905c2d9002c152284280f4a001042c440708101c51810140f10f55003c03074109002900050311241d45020084c1d0302c0e000b80c014000c0034043c0c15034064900340706205a070320 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 960440404 1250 960439154 960439159
    0x1050108070c0804060c0f0501060b0c0d09080c150712091505030f0718090203010f0302100c0f14071706060a050915190b1b07080a0b01050405070c050a05030c0d0e 72
    0x502494400c040d5105408a46c04503101c55040b900d8001103002071158400400c6201c126030b584d4142191400d0902d1208401b003000e0000c414002d102c00c0c1c5002405508001c0d003680d40b90300c900008000d451040c066440300915018020a41038a036039400080c190840c0c1c910041042d050207150313810340c1c1c5808103e401c000000038200006e0030707a52140700004c51103000c60243e0220541c590f41a10160307030098001c0c04c2e008200c0c03501002141041d4a00c000e4103103803440c00d84507a48a40e91051806442080041c043e40e805030014040c06c9400c0c4520001003030484101c1000d544084000c5441c0c0d207049a99522405220354005840c0c01d000e01042d1142092007a100c0c0c4200745502002610184080d821008161034080402c0d8800c0000061490441ca4008094031300707024141030345010500d07008200c81717030002d101c0c21002030000010f80303042d9182120041340c950340390201112648118400036046111b03886080c1c060010120003071903c0560340707040d01c908804c0c02c203050b00d150786815505078 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 960441654 1250 960440404 960440407
    0x9060b070224070605150103020307081302030c0301141503010903020a061107060c0e1e13180501020f041707060e010f020708101a090c040b0703090e040b01050108070c08 75
    0x4014904006511642042d9203142144015810445541504098000c07154140d6030400d100280c00507291a03c007652003440c040d131840c685210018400700019200c80d60380140d480550b4119a4184000170308071001034001c010f50729010050250180c01500c009000f10002d48a003c8031341818040c200354aa01500200b10b1807000399540701c020703e075405603500c0c081403e0001e02c0014a05021701e640003203195581070003850020040201c07447e400d03000381d440b00f01c5c0480c42130205d86680c030a50403194610080003400c54100181181900106c1ca00100194800039070100e01c0420640948141c03040300c0740000030298001700d60760751080d10340103c0c03020800e40049410710398130949240717400c410382c0d10503190000d03565000b861a10164440513204035455070310b2980100c0e14084140e2200380216094401401e2500740301c0301e903102e0b5004038420b02c0b0000a510301414050b10208004000e211100e0303480c0d2900c2c0c180300d09248402c1c0621303070000311060045076a45100b20041074103507400414a5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 960442904 1250 960441654 960441667
    0x302062d0903061b04151d01032c010603300908060a02090d020307090e010b041503030f02030f0307030f0c020a0c05090711030c0601031406010e0106120b1c02030709060b 75
    0x408100c000c40c1c04d40e6084400070040031480007520768615940c480180c50340001c4461404400710100c1c40c00758a9070405260030100300c5400e900306140390248aa40b00000c984400d10010b4a01420321500040c15407203101424186407910081802500000135420b0082c00b4103d41c01100c80c85c2c0302d417050040c03a034005000b2964203151907004160740d980090000c4c0300b061240d8003107030804181c1ea202c040d55075643c80704e60303074082c0080c040d44441c44800c82c0e04106646103400c1e55000240503020180820a20302c0240c10140c1c002c104175901c607440b40b501d02d80c0320300c1c0980c00140a414407010740a242424003400c00940c0b40001410046684d111400ca620a42001f060200d07803800100720b0410031801d0000b080790401c06000510800034010064001581142048815003c178104149226441280100001c819603401030341034952030703d44801c492890a0303890300944158980b045e444520110007602c1803109441c4101814402d41c180d480d40760351248804216481403041041c0d408042007179 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 960444154 1250 960442904 960442921
    0x6040e0717061f0b1b150123150d18081c020408101a0411040503010b06040b0a030903170903070b0610050d0f06031a041e02100e01090302062d090306 66
    0x1e0210f441c01039602e2015822a00003d524001524540c1d40d02c0d006d440d0b00500c000350803000d40c8130003113954039404036541c2252808107400f002440c105840d402c0300408c01a07541392203500724681d443d02d9200d500d919502a41082c510907402802e0782c408414125408400e42c5c00c1a001761401c440c1c101d009000d0350b030098141301d0702800081803d01c080d420440105000369941d44a0800c0e40e403c42d50445444500746400c0c1421240e072600307100d220f098280010451409070030111201203e0314a000700b619540c0e4501034074002d8441c02c13010041c0d40380008002e4800c04c008080c11302c480c02a071240c55603440d050240024503148002c0d010004904010040d4001000d411101c000c01c1442c80c000f40481d900d0b207a0010500c400c184c000c8036101d110081c8018050030790b90030842c84d00c41003683d18510005034001808a548140c2c510107208103c40c0a00c210780c01610b141c5c1c002c5130040c10003652003103841441500201e902c40c250490302d00710a828a4000920030544903c15030142c001c10b07042e2107a106 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 960445404 1250 960444154 960444157
    0x91c0c021003150b07020a0803030622020408010c0305060102060f0708011203110106030c1d0106081b1c0b030d090e0a05220506041101110c040506040e0717061f0b 72
    0x450806243e1505200d01c90300c604080004003c1c50f104402503216804e42c810003610f19001e6100401c0ea60080c0144422680d803600c03419071481841e283c04400700500d02c5054081d020b40c0e800903020303501c0c140050396120f4140d0005840345200741d0039a0500c0d590105000384c0c01c0700540d1814000707111030006110001014640060450007424002c241c0320049808600750b4405070030485010802c084104190380780b146182d1066080b262880d1025810104010142c0000506100700403840d044007101c500c4905007200c122012006014001c05040340d010b50150043c1030085000c4d100e01025901c00500c1040d51005495100c2590011500e4400503400170b064003910103c03442c0305010442d54401980021440303070901c54000350419160500300a003103442d0070514179040c02800324515982c10303004140500940c20841e0002001e4940c500450f0050050100c500c080d4820b4440105680c10700e01c0e00c401da400001c90807039105640b0f0307684000001c40c00191062400c052410309000d412072134030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 960446654 1250 960445404 960445429
    0x1f09031e0201060806010b0417030307021b040e1b0306010506090612060f120109030806060c0a1425030b0a090b0a050714031510030b0d061a04090b091c0c02 69
    0x4008030f0f03041d490301c21a0f030400e0320030303170000740d1034100021f00300100c640e442129001c640312030001e1030847c90906000307900c441c001020843e0341a8041241d2915544640c4040b100541d04c030200c034030907400012504e101c2c0340c1004046104e0300c10007000103014507040d0101d95080e440070707040030f0400780810701c000d1841e14058201c80d846542000409215246c1800c82c0800048400000c42e42802d10f050152404201900f0280204001c2000e105480400114000e00d41c2e44011002109902c0ba17024a0410507401085000074040d2202000e841c22a030f2098800d403401040807140d0354880c0312030f03201280c1800d40014190510132000800d501070035400b05503c10107606001030082c501d02403d8149610840d881c0c1e45461001c12081542e0501c0d00e000310422500b03003000c100051545000882c403003101000102259150008006044880f0260ba4500c040162003409881c0040c50804510201120040320703910a51860340000d842e1003901c10210a251f032102d80d5500340f2a02849044251207 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 960447904 1250 960446654 960446657
    0x2031005090702070b07050c060a0c0c0504060b0301060f02070e010b09011704030806120c03010203270d080a022a030c0d080f0105040504060e15090d1e051c050103051f09031e 77
    0x6e2000b04250709d840000744141e030b03a159600402c864181c0382070301611005401041c080c038a040000d00052210380e003120b05440e09428007844845e10341400705c0c80c0003d150000d1400340c1700c541c00054a00400400350022203026202d80040541510b1030200b41c5e1812100600000d4415000c64907a04000001001e00780c0c203942070300d19078000703540820309903841a20a0b00c0142c0189004045100c5105018520300c0303071a4000c2c14980040c100300600c046000380c01c07008480d03400100c5520102e03e246070024824800303107450011005100e1843e44a801240100701103000b030403a1000078a110308a224070030112a01c0045280e400c04090000800001300100c5c1e40030b90b1105009000c0c80100b00c022902d07001450f40c80e48914101c04400d0900c41030700c6010302072001038441c82d8900c002000400f50400c030b25141030754a40c46416134000c1966a100000c1c04090318000001c000c0c8500400d030704198450300205e4240c0d18141880c0d4004544580304094000b41c103200307100307404512405908600950a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 960449154 1250 960447904 960447913
    0x20c0d050a11030304150b030604030c0b07030e06010e010603051018020703050913050106110d050d0c020a200405060a060c030e0a0b0a090302040f090f120c12020102031005090702070b0705 83
    0xc0b180003031079030b40195801d55850103003040c0361500c000c59014850754604298090110303404c1a0780d01400300032900340001d0803402d050000801d00c82c42903020410386114942200c81d43d51b03480c58160f080d05000e000d440d000900340b000003940e2400840c40182142d01500c1e01e0810800b01138840b0000790000c50003101008400c0041c440720365500c82c1502492113480c2000504d95150090192555204462064580d04444000c1c40841d401c0001c3d20901d02c00e030036022605000c900b00490a1500300480106003141d400c1503801001d41c00403010160b031205450401c56916141c04100301a91948640c0c030008400f110f0020010f0f2044100e61442d10015101400003511003150782500e402c41c018030800103c03119804c00551a090003820154420003a0030400703000c00f512400900d00400d040581000107442c9031007a01403203401000640c5401054925250b224000002d000c0d500c266404a400d1100710302c0880c55140004035140a4805038004200192034120511899008002c0680f490f014 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 960450404 1250 960449154 960449177
    0xf120d1104140f0108060d060f27110f06030a1802030d0c020301060e16050319021911070b18030c0a060e091f0b220b1c020c0d050a 58
    0x80c00c80c0640301420460245080a601c010203100c82c0c580d02c0d0f00c0c0e19041040303400070322442c0e480704e49009410f0358000d04045000c0303450702c0d00c1c10050141040f540b60fa001503501e0603081349000317440b41c0c0d403414860310602041000d1002044141c0201c2c04185510440400c049540050a58001190303103140e44c0d00c0c1c00e50818103400080c108071402c1e8450001c80d07802840101180790030311654010b45440344d0310080074145812040009000b64200300c1c00c0c04000800f20340e60a403040c01002c0950f201041c2950346040107a200098250300404210210304108184110395001040c608250340c590306089040c1001c08000b001003810303208801d80c050180520351010394031041c44910151441346c0f500c40584d803100d82071151410340240700b115514000400381c00c100451608040440f83c440c02251b480700102480aa903071600c4910703184141c1400c0700000350b40081403014050801c03045403403240400700c14285005030700c0780344100d480c60780003e0203880700c580c080c501038075241c0001c0c5818800800d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 960451654 1250 960450404 960450431
    0x1203090a0b0f071701080c04110d05040507050411031302010e06130e06011b0309030b04060609020c21130b070c180b130212060108041704170d020f120d 67
    0x41c01074072805504001d0104018815030400d45103840b0100211070b5003030940c03612060f03036103580a5008051242d903c6500c10700395080d005060741c07141d0195a508201608003071808985c0c641a510440b4007481c101038030b501c2d0031203404050f00e1056010040d00e44e40009140d00444581c403801c9203240e80a070007800075070031848081071450081d000080440b506403d0240014002c42c1440340c10102c114010703520100000d0780490b000c8c045a85c031840f411403d803913503c0d00601400c0585c100551041c401325064111100010b0207006000804c0e0110100844d000d601c2e000074462980040b45400d07403108100210000303c0c0060000900074249080c4003502c0307103804c041c003000c00140080d08544a200d400c0e210303d001524641c2c2c058544030214075100d118002d503070b08448018803150502060200041c244550074003610190b0701020040f42d42c40303846114031198030300c0b0030107200e0f8107110303818241341c41c1c0d07000250070080304002000400081808000100d155800036014542007a00e440000c260389 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 960452904 1250 960451654 960451673
    0x2010b013006180e150408071419120f05160807020d0803040b0f0c04030c06030906060f0f030b01150e0d030203070c060509030609010605010e1509061201030209070e031203090a 78
    0xb0800c402c04142201042c3c50107280a00000f480811a510b02d414000020101c8044030f54440d41b0a40c1c0720025243c04007201c0c1407110602d1005241e4042039000010002f240b890411540503e0300c40140040d4240f100f115207000c0c501311486101001003411020a03e082c0190198038402003c503108540d20f0764078541190000da400b10b9240503139a05000c00407000301600e41d80030b08102009410540741da00d8003560a017081c410035060561741c040030000c1c440c1c2a04144007a011990100e1501c5682e880e84166104842c0b0003500c00e440c2120000c0be0300a90311403450754920540d501c4a0f007401303421040000303440d000141201548410400e8a0008100385c1d031420007007009840d000e49035411076061504001005081007080c1c1d161074420700c8282e0b01702d40140c1030650269000002c5014203e01c42449100d8007411a80c09840403450040302d2081c415824183d030701c281d03500e0440343c4842105503a8066102c84099150300031410343e165a844280c061030b4003080020031290845070a07180e04244 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 960454154 1250 960452904 960452939
    0xc110a030507050a08120a08090f0a05061f051311300a050402011e09180c02210f0706110d0e0c0f060f030a1d0d02010b013006 56
    0x41c0e401c0844204400e2802d40032240040c400080a000d80b802810510105072041800500903c41c1e0350011501c24141001b0208180d854402200d102c10340c54180b80307031340390001c031140003d021480f280c1c200e411040c112068119040a0700001c020081440c901024000c0060040d41c2840c00b0701854604590804103a03061200d046245651100c08840c181c0d10024010000295203081005000060346e01082d8103903143c0c040d1091000405000760b088888058541c0716044c400290b403994082c1403280d0b4451605000c503502110310403c00503010707400f42d00d003011060ba00028180205056503958900034111144a03600000e070340b141081030031003660002d0a8144486903100b1500001c1da030100428000c1301e008445924608001c1c10005d050351040e0001c004421300044049007038289a44c000c0d80c0b40c209a030250740c250800341c0036041ea482c50341445600041d802c00343d1200c025405400c405141c1d140030900d0b040140c8842c00071140311045100f150540550383c00c8006000307440503402050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 960455404 1250 960454154 960454163
    0xf0f0c250f1d0415020f12190908030a0c090306111201090615030225080a2604030e0307080102030a0e0606040e03030f040c0f03032001090809010c110a03 68
    0x51203820003409001c4035006421500301c2544400844021521002d41c642c0c0c055413000491800d02201045a8040e0141c3d11210180c20408201c08561010b1a080c43e486420f0001a40032004681040714080e0b4412040c0a810f60904002241c103141c02c0d60072815132440d180c148440c4265503036417650115890407409800c92031000c160b85034040c021500803401000b0180f400e0240394200b01b808102c22203024003c405159000035007000031441e90b0f403041d0b556030307840907610014505410314071a1540301220310b000003481d40c003002c04803844008900c10b141984000580740b691f22030360140c0e40c80200d909450b0f414480c1130740004109000740001d5103c2c7c00d0480c00407600e840000181c605c1c0090280c120392250703040012005002c240081960390040010000c1e03040d6480c0e03410f080c0220245908074035009072403640c010050681181c00702c00b10401c0006e8480d04484c155400508031245840000d006590070486070310a50710484510410300d01035a91500d50041c84800109c4061580c2d00454 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 960456654 1250 960455404 960455473
    0x25110904060c11160521010c080915091203061305070518030712061806062309070e060a020f07140f0109061e0c061a030c03030f0f0c 59
    0x745265000903103c50141203c4000d0807a054042441031022400c0d00601c2d0003401642601440c0e03200389078402c048000d924008000800c0020001040076400702c5200383e461096001070150403954112152080550001526604003030001d0540258805840a43c0c4000801021441c01e2214850b4900400094507050768405c0006100742814413103040c4d041c8250000071082002c01c4030000240703843d540c4800002140c05446101c0b07004080702c244098141880d04402164a8162040c01b400011903901401c004050b82000c000f034040044032480001f072000c1901d13210505040014000824442c0199054815481010b41c9005195800401510072401c04d101240c101f140320801000000e181c00e0780c0150510300d01514a803c11100c070851459009105141241b00701107000b0031941c8403505224032154107881d54804140030781c204d0310030f004031691142246400011034040400e5082e0540c2001040702100076280c10000d03441ca41c0d4000c082c04c5120001c4190429a008000f1030b2003403 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 960457904 1250 960456654 960456671
    0x200c090c220620031204061409060f06040b0f010305070302041d04060e03160314070b0f0a0608010506010c020108090f1c0807020307170304060b060c0a0501112511090406 75
    0xd10128140341c001d250343d0036a030400c500f0894040125044280002d4601c1e110351241d25041d40203000c403410500010a0080a0020605002c01c00c2805040002d240c0031180e1940e004000c02c0311503200c20103a001252429042065001c2e8101d1503000069040040c1840d54039151a4101080031500d0502e900000007040200030040c8558007500c40210001e40c200716040c0c0120f84841c0e10900064144511507400c1c5208000181c00c0720030a0354015190386803410091000380040c00103480075000359060007808101c546052141d01c1c407441050351811321000480c3c0040d03441c03600c0a001c081e503038003c0e034071038001c144420080012203810500e414045805d4036640105100c1000d8002030454000308001000b10328040319140c20186541070303d49c1c1d280c9a0749025402010f141840703580100d0702045242203004042444214640510000d01c00e260f0031403050000c0303104009044c0304500308181b40c56504004980e0101c8158852403a040142900781c0c0002c00b0304400302c130121404c98031098403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 960459154 1250 960457904 960457907
    0xa0302040f0f0e0307030c171e1801021203071209050a030e090901091101031d0a0507050a060e15030c0c1c0f020309012a02060f0703200c090c2206 65
    0x384401207030b080011394202540c1c0d039802020070302c00140c0035011f040041c2d06a000c101075030341164169002040360842c1c00c42201c819500b40d80010410400504848605441550001c03651001c070f40f45071043e103491580c49070b4003511141d404508031030203181d80d040510009501000b4041c0940d0013600d0b5810079960120400041520003800180540d0500c103001000410207a005030f03100f042420080f40c1c004a10b103464104661101c50300c0664800c1d66042030074030134003068410681e60203458a03c00c8a896602c2a6000c1610203246604005c20b4880e8400d09004900075680040da19541f4502d48018101158907060b80410701100003840e906503007410607000090781d10210030b5800518180140e110018103404120b820001208690700101c628025604c112202e005a00405943d01c400509405408d5500141d1044012802c1114685100c01300522002801c890940050643c005801c007803041c54040030708a8044810f05216000103440215101d030064805032a8500d0002e10340b207070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 960460404 1250 960459154 960459161
    0x605100905450d090e0903130315060503030f031006030c020a0308100f09020d050f010f1202150715050c0a270b0408030c060109020f030103110a0302040f0f 69
    0x3410740c0741020080190100400c41c120002d50a01841c00e14031511201104980c90110445414a01400058102454201003000203440440703081d8034070360ba6020f0500396284559134040805a09411013000001c0d215080b520f0380d9005a080883c1165950010034a5a00894031035680140c000c0200000c90080c030111000400b078603e024400000300f4600a0740300d0120410160410008400107246098400134140044c01c1d03450b0304810413035440c0d1040000790400320080b680e49040c80701203103001031940d40941c107895010301c1111743c0321b207420100d409008240d1404c030707041180030040d0003511543d400601103a5019070801c0c014000312945400031101300a044012290081c409020019031005207460101c81ca90000028000f01c030458070140d059a0344032840b200300004000c21a03060100191002854041c120f5001340d072215082c0042c0e0080b5080e100000000307200400101d00e00c3c00252500b00c80152401010303c1c1c03650041020b8a08800c0204009500e40c0400404a1a50320 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 960461654 1250 960460404 960460411
    0x8280c15031a0114092d120607050f0307030605100e04140c0f0d02040308030406060608090309030607030c11120307090509160c1a0403090302010e03010e06061c0605100905 76
    0x396080e030480090004c0e00060040400020201c008104142241c0b0f580740d40490000e002caa101c1c0c51442031901140d4440d80807202d4034016107100c8401c80c144880081c1050103031810b41c440324105a21400007075559000200054209906c565000500c0c1e1114000c0b0300c0500c80c0e541d40e84130002d02400c00e001c02da9041204200300c40c11013108000c00710041100340e42c01c2c42041102155035000d00361000001e80910b4201500070b1a0000c00d01c000c000090f849403045801c00e03128902d59a8503030305001c0d00c07801022446905134112000060802e482607011340c02c00c4009003040074904507580318840c5082402192031584010010910103100e4220754400020001260001c03102d2400d403c00051105046600d2428455400d20550402140341c010038072020742e08020805900d000e0600400c4418035103c01c0e07020034918803181c1124141030044244000c0a100108815120303181031112102403400407000d5000c000c035091001404602525014000d0f1404507540d090400841008407030001d0b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 960462904 1250 960461654 960461681
    0x30c0b040f0611060a110c070b0d0507051903090c15030c09150e0603090106210c050114090d050f07140a090903020d0c0305040302131d01050108280c1503 68
    0x20f4030a418908000400740d500010342d04010a1005030800103004a0260f6a55070a003806020b0000c104601444080d00001901a4003400760f03442e0f1070ba081d1018801c141080c90a035851040840b8100d0080e0000c594641c410900d0000c0580d9420751840401c000031100c0c00065101c500d024506035000710030501508154148200440758100040d0284480b0411036014010100000d4810403080d803150008240c20114201c0050490080703445540548000b100c107890140303008102944070340003230030014200081d4103142441e07003410044038800b0301404a038584078606406903285c106003c5c440c000e000c4c0c1e02e101440516008104180700c20950001d44080d4903150301107010039070003e024407600324281803008210900e41402c40e1944640d40010350050081c4040001000d81350b4400b03011303d041680084040480707540d4184c20f9400078401c81e542c0c1c3d40509030401d2081d12014030184148000810f0144c004a941c1d200130780c600f000e9201d0070071401030480148429406010301000100e94 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 960464154 1250 960462904 960462917
    0x1050a061206050a0e010905030a0807090f0b090a032114070b070f050d020708090f090115030b060c0607020a02010f0824010c02040923010605060306100207030c0b040f06 75
    0x30661050600c60800300081c0c8400c3d141c00100c0c9030840f4541c0182184d030703074280090101e0324103801c0c4141d41e0b5004030411000101c2440003d90110701c6055400140c03510300102d4820103142c1844001150490102c0b15807180d5044400000a400c450080301c810301807614070410340d080e0000207000b680c5111040d0482d40e400b000404002410300c036200384d200859040200010081110445450242240f40300d540e6100040301c00034012401e000c0c2452100864150888041c907105006010b1401e12894852140c0c0010b24031509000c2e07048032001c0c60740a41301c5401c02071094141481c2000c2514544096000358542c0342c10346d42d02031040810b5100b5428954000e00781103c03a40c149039440902c511800d02c0e11056403c040c0c0c481c11b02c0118141e001841400546058248803c401408440b286809d41d22050107200c2c034031040c000c000860340020086030443d55048180701d0410a02d070011000c5000e1680c0110010785818408030260580104c25074440b414150313040e44001e150f40041050060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 960465404 1250 960464154 960464159
    0x411120f060f040f0c060815030f0705090a09020a1203030b03120405010c08161505010f0b030609150303070f1502250302100f1b05030903040303030e030403080c0c0301050a06 77
    0x1400244250046504507207641d00c0d584034142154072100b8010005c003407420568000840d250701070f52050040748031307500040e01d0503000410903681c3c00c0d60010b00345054010321401c10485c6019640c1d5940706000c44004031704140305500091101c80507410100d50800c0180b4010245036251003203518000c4190020201207960000140d000d00451103103604002d10380500d041040120416a4440074040711152a2003040c1c0c6007050074510a40c00040c0241d1801000143c03881c00303001c81c64122020b00c01210300d55100e18003441003032240141101d03d0014020204103080c0c40400c010580c242c018400e00c440040c49107841000b000501d110f060710a03005000d401d522a8841d04d801d007800322241d034010700401807440c09a05251058012001440c940b24102081d44c1580c2c11100b0098009410341110743d01103001511140001d4402c0700184c0e20071b1000b400024080d50060701180d070048200c13402d00313590344c2e58504260310180840881d904072020f220031600302400b406030440204c10301804003d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 960466654 1250 960465404 960465433
    0x30103020a1203031107050a0201111c181707150815090a090803270a05030f220603060521120f0d0c05031014030307060b03030d05041112 61
    0x20140c0a402d115640030781c468020180282e1158003c0303025020591341311046030a20365210301081c141a404124a5070441405000c003042a01078000440c41d429510413058504039101d0001043c018955503c6603401b064003680c044200500c03804100040113070606014400c070328a412091000240302d00d80701440305141c2d1311a1203d0054206840700003859a5803a002000b400017500082c04082e000428000c210103034005850340c0c24110409600078402185149545000311700d0058600e40061120b66841c4810350010710f05030391600b1552603180c51482e0307081d5805031194002008680e45032000c2046082410341c00ca5680e40e00c1010305c21407903014a1942d01c40200103446038102c4400a000301c00c40c07149900351840d001d04d2100401420b5440c820140081e030042e10b9120281300807020000304000d027007031800c40c2028041c2c003071814091207555880c068003204003001e43c940401e1005516143c007a203e001d11403401001c9901c0c083d41580107100644030021850521604034290340c50300b48 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 960467904 1250 960466654 960466669
    0x305100504050a0f1419230313090c080903120403030c090e0108010506090c0a02070b03040f15150f030515060312030c2226030903190c080303010302 66
    0x10281440851159141c0c0381160030030100060050450890030000320500c20141d201902016110085445010000a00c2000001c21420003006003410101d02074403101d20581a01418038000100e0b805d1428820081c1007406487d0880c0d490141d075500302c001e21592041300b031500880c601c000382d0710340048440440100d0b10000d002030180350300c40c8030395840140300b0100000106060034030f01a003540c4030f03500039000c0e1800f9611207101e0031124001c214801aa5000c444003000b071500104866881d02150708204d03000200240c40101c4000f46510119542e080395020303902442c080003034180a1050760b80703500f0b0307410307082241582c401d01c500f0700005600280e01818100e540c0d6010005649400002e40b8103620700310281010800401400804948a000740c4043d60003191041034504520007a00a40c040c1c9208869411010080124003103040d000a0241404a1000d4902d407681c4400424034104121ba80003d0103044410075a00b0712603208000000b41c080305014600e10351541c1c0002d03950 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 960469154 1250 960467904 960467923
    0x321909050613170f0753030c070308091c020d0f02030a02030909060609040207030203130b12070f091a090102012f0c0a0f0f1a0423160807060908070305 67
    0x244400c441140c0c000c200003c107101d1189040030349401c3d129074030708106031810200c2c00500c14030481b015100d4000d500002c140c81c41030f451580c004e41440031039142105d0340000942070401e18000c80201c41e442106425545140c14020f4000f84100000c1450080c042c05c3e07903802100443d007041c88201941513000c800c944421000311100070068980d42d0000c0c4007880341c4604144e00c18400191102015008009442800e040898200e0502e0741e0f032480706103501c188007508800001000014a00078010481c42c0c60117450b514000f040702c3d466501991401c2580c24070104200c80114001c1e4056030309019031146000c11024880c0310b4180e100381e14080d840d040421884002000c1074200124200704904084142c004502c5681240541030070302d0055404002961001a81d0b0fa2259516052030406400756600000301d04408610b051491005a0892031942e014007400c000f078a807041d02981918041c0ca000e80c040c08c141031901c9005810381045a20078041a00710703a100f003000c1100851041c11 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 960470404 1250 960469154 960469163
    0x90c170c030c041109041a01120614010309081b0c190f05010f1e0302041701020315040f1d0609010b030703030e0907050d050a321909050613170f07 65
    0x841c18a0041104c0b01c502030841d580c1d41042c5012000c080d050508040100a24030a884110b40344502da000321068400a0043c1e07000b285441c540c6045551080e0310905d5001c1c09586d0890518100314007804c2848010744c40c11003184e011002c010417030718022411807031114031304106440c800e14104d0f81440001892060314140300c020203501003000d020322480b5a0704d014020100503040c1e61090b0140017900b080c00364050b50718240f0030b080342500c0305108980c0500c511690804181000000f00805000c18800f9518115118400701464800b1603d0000e00d040310310000c0c240619051242d942100d2007160b02a1107075000c4001040800d13004110340c10318003402d980c40041545c402c0c409541070b04c11840e01d00411440e203030802c0542c4c1190380c480c078801a606807414071b403641c00140c400e2071699800c015016104041c00400c55003400c07141240704031003070080e01203070300c5d045030f00d826003841d03411101c601900790004102e0302000146009803001c603282c00d070355030304000529a000b240c90046800051 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 960471654 1250 960470404 960470411
    0x605010618150c14010c08010e01350d083408060604050907020c0102010c0315090905070b070f15020a0503190e1905072322090c170c030c04 62
    0x30080c3c801c0c0300710f2000b140c100c0d00b0100300c0a5841030302e6009009007010302d000a12104004104503100040e5641280d012284292075007222010441c0c189103501e407000500d0002050f8030403041d0081c00741850340162600c4440f1a4980b82c0301e00c240e09400c890410500c400c00c1c0c4070208105804110120742c1059514090315103582e140007245051041d500410341c403860010400c4041c90340002c544a105200380c0c000d026581c48164240c054800100c800b4020080343c15040c40243d01551200f12841d02074000c6070240c641d5400030101e02d5200d4602941c0304544030031081c003402035010680e01d0720f1100c58070840c0f41c0f062880004049000c040c00c1d100f4a403440703c0c0303c0b40d86014240c00c00185221204203841980100ac0c11004407a81c10b4841150f260040b00c20002d145610003411070316886044a4040f031141144e001c01003030a10403400280441a41640c00000050341e2180454a41c0300d21004a800e5081400319800c84184406604042d40645441c003c0c40d00c0115225500d25819100030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 960472904 1250 960471654 960471689
    0x30f03040c03050604140c0a14010c050102070606060519020303090a081b0d180e040c03080318070303050a030e0a02150a0207091103060f1c03080c090301090f0605010618 75
    0x15901c41c442d440605284a048140000e01403c1950200345140246c202d8400400078001d109103e5400d00c90140b2881e10003415486650052580e4840c0ca80314000042c5041c1c1c16580710000c4483c16001400060310103d9010300c0490702000f003802141640c00114194036100728826910385005100412030b00e40400c000c0310b840700c3d070034200622604120940b1400091114020081c07200b942011003107030b40600740003c46c9401000007500803900314000c03034542c2d1f09545030700d2080d600207010309130100b3b0301704100341e00244240010006140301781d6455944510510009083d10400c001c446169000b5408980060380d40fa9281e650b060320b20716034251101180c820030303424030f2074680c0113091050404541c0c0b003900700908010342c400c00c800c98440c005440c405040c41850b008040c00b038081039501d0340080021a0003202c10035400b80030500003d00d00b80009010074251005418100d44010440309100108505401030a0141150380341084200b28212050403440d0210303c1103507031160100706003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 960474154 1250 960472904 960472913
    0x40311010c1401051e0606091302071a010308071a060609010f210608060a05040f06021602180405060c0a1b0c090e0f0c03010902060405010f02100c0e011808030f0304 73
    0x1150a00e20600008201174540908842900804201d489040c002801d000403514507110080c1d800c1d49402400344480b05a018410000035440a00107441c8030440022541c00d04008200b254042c40c410072401e13455110a1a0502a09015800024040c60700c0010400b00351912010707035814000c01d2901c0c0d050070a40c400260355030311905010010904403040080c0481c40f4a070040021104102c01701c401a956030359510003115015900101299110a03c02c1d006ca1402d0f0040c100380301345407018688005095000407a6555485000c444804845081200344081480007a6203c0000030480c0d04d00102510000d0070180e01c079640340048842c0019010500418100010150685c00400c2040e0031052000039940c4a045d508c000c144d1050032512506420180909001c1583c080c16070380c1000d007060015500c41c070b140d40c1c20740d085205110b0310000d801114090300b010b01c0d800d915171400e0740045000050101401c0e141e2000c20603c400c4082005501c000216801401003120b0182c503600c0c1c9190 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 960475404 1250 960474154 960474173
    0xc0711010e012a171206010c170d1407030506060d09050102040b0d060302030d02010605060318010917090a050604050904080a020f071409070c11060c0a15060807050303040311010c 79
    0x800c406020b00904442c0001550900c4035038156000e00c4110603003081407040c07114284100f0031841c2c0001c1740c10002c40d200354003410342211a148200512545c01d06a407101c945076400a91040060380d881c1c03088000c1e0310380c41c00d10303550304044a131034240414501500400c0c060b2103070000c07c841386503a0320704210900c0021350550380a0700320140c0c0faa94034080000b00102400c0c07640802d80c4030303003e2018440e00080c0144500c40448501400c2c0a0565895a000d1951aa000c00e45a01e56540703078042c02e40000c0940400b8512041e00d21941c645078101201400760040700c1ea0803150080303404000c1405281d0710724400d01d0788203a1000d1096906c0761001403c07424600010260f040d1031083d180082011003a150080c51443c800b0746000016640d90324044501e0510b9034000f034003a6038402080d030160b09215000b8945100d00a01b10b0f40c0724044c90b5165500c0e95140e001c01c4050725940c0e682445005401d120300801008124001c45c2028150744a5612087c0100f00c170328148292001c0e18010000c8051 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 960476654 1250 960475404 960475427
    0x1905100203040306060b03040507081906150312170c07030e100309080403052b051902071827020a090b0a090504030302180a18090f0b041202060c0711010e01 69
    0x19402d0105c10782c5c074200361070550802e071822900c5000301e14001c40da107000041e10b01006044045103405040c1e40780c48010043c0749041e0440514602c051000c000325a1039a03100382c148039207a9506150325260a1100710040000d410301d40308010400910000c2903101c0100c045081080324181c9541031001001d40c014007005030028219400410700109001010807400034010084000651424588e184c00100090029225000c103405100d2820791b490440007030242c5a2403401200e40190710b400c00f01d815440e400c090100516101d10385001c4001c189110b00122a003020701140307819680c3e500081c412410340c01044001c5940c1c1c8408040765551007a607000800c40044108410705003410020080c3d4822841e03401e60b03104966580903281844408070007124551281d41c10001c5207007038100b0181001042c103840300070244940381c0104017a44d544500580c4210b0150400c8550050080e05094000309201040c15050010001040300400084a055024601840c030a180c0303c0050302c2a10199 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 960477904 1250 960476654 960476663
    0x319050f07020a03200102010603080403060c030f0f0204050102151b0c03070605040b0117120415022401050a1a04090e1f051b18060c0307061b080619051002030403 72
    0x40b83d0000902020812101301c1000c01000e0381c0c0d07813010000041e4261a460f10004200200400080002c20300c1c40e40007003012400c602d00440c980131030b51081002d03603100500e40d0141e240d00003820400c41da0100503032042c5962901d40c00f0710600d803e19400c4070507003030401c01d80c0c40344000103407644450b03006000701ca00b00c1e688203d040000b42084e0801011a040901540415850725105c60103810030000700c1c00b040e040c80c2c03000140361904181d81031080b51400e003c41001c0d441980003030107090600003098108000341c203c41c3c81c0203600d080104000026030390301140000b01900c6460450601e90011207080e50304c118000718801c001681c2c99490f08041d40c2e160003080356801d5642c14130b08203d4000900580195254460001540841050b5441442045109058800031000c11428010b0180003500c01c0c007001d407424080306484400036140d040e540075042004c120404c481d00780d00041100d4202e02d080c0d542030342c01d0155044529281069001b2684500a0b2810030200203208000320340c00786500 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 960479154 1250 960477904 960477919
    0x61f0c080f0304060f0b0d151404050a0303060b0a0207060509061c1d0c0d061808030f010f061704030806120a0f02090c0a0f260f04030905030319050f0702 68
    0x40e0700081910340042d10101c500710b00384a4403803440d03409401643e041c48402401e5850002142d078070210790543da2842d032043d5645500030b0401e026140c40d1807a2166000320094a220101460300501304c41c0d00d60040c0402da48144106034a4580c002102c0301941d082d41030499a0300c003480000b94281c013400003441000480c0c1c4c0740e406000e90103500400320000c42620031159007c4036100d495126601a819944c000326070325030600110344990800301d0b80c6000e6504514000400d13071560080c9a1040300c641c8400c0c901c401c010007444601c1c1101d00b00a101c240740420300d42001141a01d00d00f2400740026007005404070128080740d54003a90031850030080320480b110600d85d803801c40e551a18800b0140d129082000020310300310080c034115100702c1101e41d502c0c056003060000c16280e42c05800c40c2180c604844020f000103d41c1c0450450340985561060035016282515004200402030342000703000350801c4c020080307403400e848080c006000c82410001c0e2501d44040c42c1e94202c0c056018041d600001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 960480404 1250 960479154 960479167
    0x30a060905240a06270e090325030801030b18030c10110412120c051b09070306060518011107060507020913050624030a0b010617061f0c08 61
    0x80c0c648000c03803000081e0400603040b9039440802c00c0c00c070144d108940c0442c003204102c603640e084126188010202d1001444050f0361910300c1d06019002c1280c09002d141d0000942c1d0251808100780191104401ba10395100b000c4c0c980e6000303119981c1072000504040400300810411a01d03150004000d50700c0e101142e8807013a61003080d41d81c582c00d00c1804aa11031810580c001c944a40b01c045505032855011009400100340d80c400c0d0420029107040d07020461059003c10010750140b1003000c0c1c0034490b4020740321041c941030410807142c601600e0103040c503140010402030903030044140c981e0311078224001d0751202c00f40380c016107d140e18180024810300078408007103074554101002c0c2070076600a507001034103992608241e141000c809140684543d02410010720709451208141c081042000200c8200c15506d070007183c502041d10034104c40c0301044900600c0210303800125111541102520703004103040000c00b19503100c0341d519944005001100e0b64030241c0303000d260a0030115038000300c1030f42e4411 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 960481654 1250 960480404 960480421
    0x10b13020702041b0f0f020c03151905010f03020f1903030e0310060e0919170a0e10030501050102061e06090a060807090c02070509070f08061c1103011410030305030a060905 76
    0x1c802402c44042983d06c1201e078041880003841e050995000b60041400641c3d00c4080036100100804081880da540300584180c2d1004d8080c09000700454055140a2800c5104000760481401c8000d801070200c0400407403928440340b100340890340c00d41402065a1407140220303083c19083e1164100c075605220001411460120001d0300c01c41102003a00d22100c8070050302c060070444090701030210050b0780c03041d400030340d20100100b00e22010ba041041e5010a4140859054000c1003090300209075200700401041d601809107a0340701410f80c000300e20303420a40c0d420500c500d00c060b0210b401000702c1d03400903c90f0305295000502903d0407030103c0340031541e1404114060417903010a400140940040003c8605140400d58003805082c0c0310450740da10000e100b1918040001c050580c8901d4003a16402c148110a48640c1074500800005840c503099000385402d5802c0b510780c542000e03003401e040207009404614075400350383d4980b500541d26119843e6000140055070002da501c18a05402e20030140c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 960482904 1250 960481654 960481667
    0xc030f040302120a170f1b030c0c150a0c020409020603101d01030b070c05150108070914040209061002010b090f0f150307090c0306081b030609010b13020702041b 71
    0x780e208a840780b103150741c0081c4a90300d8180c8900c005000c41605842d0800640e0365402505600c2c600c0d450b070604207000b44512a41d030b40070130200c0072555040000d041440420601c0f8691116000ba902e04040c00495080c13a48207101d030609250400c500e202c184021991650044100b164008050640380d00f000c20082c1618a05880781c52040480014210400460200c1c0c440c100c030b4221207158420760f0381c20341c1601c0301c800c048001c17a00d41c001e031281e500c0100103000e50346000c4c01300324000300310260800c400b002c21180058510f0f05000340f507504020050351004c4a41e940010152800650058031280613809046000c0f9503075801a0103000300440401a4075006100700181c00529004d521075080c01503803140d0711040300c1d400d50004035062107000c0813034102c00401611850001841c5560300402401d10001c80c1581c11998041c509103400b81c50308001a075000a0f101000300700c3d01980800007540c13180510841015550041441e0056540c1c560050500e0346280c807007007003840090200103118 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 960484154 1250 960482904 960482909
    0x3020c01050c1005010b04150e1e1309030917030403050a021012060909030e010e31150504110f07060b062b050a090c12110a031a0a0b130504080c030f04 67
    0x12301d03c2c54043e007031288110313036040030420f000d00001504021400a00c0d0041c204c26021908040ca034071001c105a44584184030b646400b0782d4034485080e0510390301002e00c50b9921800d92165000b0720007071021450100e10504101d604a5001007180c03486a81034412840b1031411403c0d0780c0c81c100001903544c68603000400018803954171401c900b11030304015a0741c200003010b075540110302003400c00e44007480a0001001640da8010340081070101000d19804e030b0340317a000d403035142100f01a82040b1a09003406801c40681042e0720042c24440748850b0804140283d4801608035612840c40406980b02d070803c940c1d415aa182034620317400308003003a16100120800500200510307010008045001c14400c020107a50720600729614240382841e504200c100c554019101002d0020100103030340d81d80b15044004500c0f8600e9003100390091000c4a0301820001e14949038642000541307a40d6a5880041c80310f041411240025a40c440742080001405802d40261040c80009000c01a80420f01d000e0000c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 960485404 1250 960484154 960484169
    0x30a0c09060f0b03090318040b1018060302190315210b15030c090c0d06150807021b010f030915090c231002010b0607080d150303020c01050c1005010b04 67
    0x220b056940c08182d50502c41241c1c0d082064100340048844241c0701c0d2001000840010004500c400c003000001e006565990310460201c6c2ca0325400c40c500c210b0300340c00c120041c5001e0504605010105c1554008140c6000a07a41010b40d18881d000070098003101e401b02400300c5103401c0110540b505070358120715071080780590300000020000392a14600c45c4200b4450800036000c1c0445114a4007401036001c000340032085205424042003010070040d118080040101007280e03142e110609a01608002000e803894017103400c25000318180c40c007806500004c0d10001c0c41c3c11002102d18100840082101d59001040c00c0c4ca01100c185060710650080001d80c1d00460a5006090744c91400c0003c00900c4103501c8480c802040c0704c0c414500c0c010016182500382d500001c102a446400007070001e43c0b1920080314141000709031691140698490503400125a0100f0b10340241140c0f4081c2d83d491310702000034104000064420107803807060000c6031244405080c28445540c4a42c100104c54019004000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 960486654 1250 960485404 960485429
    0x2150f06030f210a0e0414061503040506060d0f0b0702030c070b03040b040201030e030f040b19020109030e04020d060f08030a030c1416030c0506090f010b0d0203060c0306030a0c0906 80
    0x1000d140114040e81220311210755403203100d41e2486540b00b143c005801311010b200d8038502c0703081d66403111302403d01e100d0070030f485105041c0341400401c54580100704110100000520801001910002d4030703e40064007128541441c041c4c6141000d15140324240050000c548801400100382e0000060140b240c80d001c162100c0b940ca0f142c0300c54035400110f6018041c914500041070155000b03510200348289114240e915280030b51842e025580d001d548401601703540000c51845841c08000c07540d034002600e10081c00080f5440d10001e1802191016503072280e035001403441d09000082cad020740028011310a420325115500c0419075181d8010b00c001c1408030303040125500340148039540c01d070014500120b105050808080c4401c0c010300030010214207101e00c003051407020400030032980e803040380e07101d0042403204140155103080d41d40741c0c00b0303a6000e540380806e482c006aa010070b41c0d03580401c4030904a0b484e41d03550f03800030303240c900090000740071071b6104080401d1445941d00a4415980b07042c5024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 960487904 1250 960486654 960486673
    0x6040e011d100c02100203060604030210080105090a050f1b041502060105030f0c0d030f03140408070c14010512061801030537031d060c010b03120c070501080702150f0603 75
    0x102c2074404044428006810001110f03004a9155003c0c5400540180c541801c058407039000c610304070200c400301c5020906e9000100b116191902043e9845040c80106000314180040c0344101820b001d4620000d17410b815003841c3c5041c445000b618010500c0020901814100080c0a501c40f002802014081e000351030391243e440d90009050600c0720809030610b48010103a480885940810429101c00c00d915030f004200e0071907503000c1e10f45c0114014004036607500c0c558506001c0d0030f07002e5803022405050071074030104941c0e041016280c0311108010316400303c1c0d84440005503a10714070f528011302128114008070503c480024541c1400c61521400030302c81d00901c1110f80903401c0061141d01a078415180c0d00e00080c440e210588070807400d610111a1801c0c21400a24642c00502c3e240c071a682d5074540813412413601b0000c2048109102c04030600d481320000c03055407101c0346402440c2c1400000f47c003140c030240c42048034502096046001031031508140c1c0392404091026a2154482e00c1665000b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 960489154 1250 960487904 960487933
    0xd0b0c120603190314040b2a070e011406090901120507080c0904030f030f05071e1d0d02031005090a0b0105011107090c1107120303060b0f1206040e011d 67
    0x48051200c018508000000c4043e50111752200280d0b0fa6000300150034000010b1120081010305140c00344c0241c00b0490488116030030301200d408e01c805c00c0341c41d030020b00100925110905103a040d00c102034072842c480314440700481d8240c82220211608015074400014007400307036240c03689a40e4400e80680755465036806246903646481072845910040c2840402e0009000309004036111026040c00304d10845a40124000c90380200e460501007488400e40812524815840c0600f5100e00d050100c240484840405910996042c00501805003c2828020755404108000c100100398030180b0407403034211035186d00d81c1c00705041110340c0c800361000404c00d0342c041d10103010141510001841214900359004001e00440f001c04001e0041d100041451b44400f8400300000d8440c540203200107144600d001012100c1030341c00392050450603c01140066041c40864816804540c80d204403512118005801401c1072803143d40d90b586420341300c0b444801c20310281d1036003d510205451001140218 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 960490404 1250 960489154 960489163
    0x2108010509071110151d01060810090c0c0201031506080402040b061c021c02070503030f1008030f1b0309060a030203071701230108090a0303090f0b010b1201061713020d0b0c120603 79
    0x6c036490004000401441070314426199070307a00128074502c03481065aa454103408a80e00b1240c04000035007558101c10035941c05004a0f45402c02c500710304043d15141c040000c00e0100060000bd1049890340311201c0e25a8441c0300380d07240100c0382e4254100030420008050001c1d8405201c10411a216003408200f0050500c2902e802c5500000a1072655560324601940003400800030b00e51008240c1011441d07900c1003015029044000b04003030350b680c07161441c2e00042c484d100c040006943c401c000342e1046032100401e42c0c119840a050243e01ca0301c6003030040d2441445420348286412020000003a823841032905468040f0b1602c040716084e41003000112201c2800325110382f072950000d019080002d22a502141e2580e029001c0e03071861442d142c0d130360002400c00b03030300401c0303c10380104943d11500c000c0b10090f40109014140074006500d01c9500c0500c0c0300c0010710340c8000700d0f800742000c000d43d00c405030106521513003c4031340761082c9448800550300b034002e500c181010030b8101000031a24200020b = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 960491654 1250 960490404 960490439
    0x130f0c12110f04060c0c0305010c031416090506070c050306040c090e0d0e0d0f080a03090201080c130b0d0f1104080c1e04051918210801050907111015 66
    0x20b9003034074082c20900255201c41c10384808942130303000d40300e0010209401784500002640c080d41c01184224000400c826080301c00b81407242000c503c44480d110307041d0008070200403900181c0c0c0351501c07a00035080240010219030b10494150045108000801649006440580d400c44104020081001000380d80d6440f05000541c0407600c40c0200d10058501640e8410b0b9041c07181d107404800c4005940d0341c4a01c7c5d0803101a07000070039201c0c50070318119a002003145074041511644a41458040d084032103c42c1d10300e1040c000c2c0c0c1c0e04009088041c030700741a0004000c00702d410a0a010140704c034040c176041b43e0302070320410905005103460180149003a803050603580d1b540d100c0704007550760717120104001060050461039075400354008805820800307020742c50071541c1a54000c141c0c81024180803107407404541c10740305045d5500002000c61034018a1607415914107451030070140e669040c09442481840e100440a031051441000315000560080801c04106000f00203440ba5900c010201c42415203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 960492904 1250 960491654 960491677
    0x1a041202011b1803020612010906170c1009122010020304090506031f0e0c0405060607030e030f03040f080f03070213020a090f14010e060307020705130f0c1211 70
    0x10085010b299114042c5a601e079080076210b40301480e0b617980002c85c07990000d15280c1a0500c00da0042140c84802c0c4600c1c0000d00701c040d082a000a02000250389600000c0c815030311031402080350101e00362051524034040c00003488900764036001c80c10980c64100d000e4440072034000e28641e2500c410b05152a140311607003070303940045007010300340501c1001410005040c217030035100700000510340d043e50214001c3e83c4d00d20804001040c0003244045820b1041c44103031725000321300704000c0c0320b03c40c1c0b6100c0c11113190320f825242280d250f585180019041480300c0d04010414070020602050b883c0c0016102c0c0200e44424085400081c100c43c696038507405140c402075408410700040115480d415001482484007900c1c00c144150f44510403d00440310b47d0b0032501490349811200314255030403086424155008440141c21450110002075440029010301c1d40111030310101e018804030303590080e003039485c0800c005000040780544d00501100d9403000c410401814260908040403224044440c1041c01 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 960494154 1250 960492904 960492941
    0xc060412050636151609090b091303030b03120a020106050d0803160c06062309060f011202160b04021306031109220503210903070615031a04120201 65
    0x42c454030f00c1814107a02c01c2010340c0e0148008580700702c07450342d21062280d20801ca1501c050b03412414010500203041e0008a609803400c481040581d851188155120380381c040c0a038540b00907442c049000d010001d61054040c0300e07a2900c00c0890617068040d0481074a181d000300001c40d0707a4020000c140d100010007070600601000400c1c0102d0310500c0b024001c1c3c025062000e511882990b45100b1110319904c084101440c106a500389141d4101d510305001c0411500c10b0500c3c01c1c40070009000780c40c034060315414080318401800d0450240d0701551045540315001e01c2521840e8202485084012103049115441400d4941e44c103852910a0005613600540296001900d03c0309100c04c031400030300f1100d0700050a440201400ca0b035031b0051540300f4030600c051601e41c41050203140f400401101000c8e421140d41d03041280c0c44600000351307004550421004508800c1140c3c81c102050381941020302a01d50900d01450350032540401070740034a11541c150724004250341c104030b08031540902446102441d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 960495404 1250 960494154 960494221
    0xc0d0305091914042d0515040506181504091101020706261003060905010b03010513081e1207020607080a02041211040e0115051306030503030a0e0c0604120506 70
    0x141039000020880e05c15401c0d6680309034006400a4400d0303d003c61070921a140e001704503840d100b0f21100c1c800c1000c1900c040c82641495000203450b450904a283c195001a030002485800703c0d42c10001400b01c090030030031890f412402d142c50441056605680076101d0614005001841384250094078600d9000c203410589021042d200181009440c500070307003040001c04408030707034588103141140b07100d140000b50b542d42410500d802d4980c02010b20a1100d0003a003601c01148403034040310244140d04111220700c58000325643c080d80960580304c040303000480108402c10380c001484500a90b49919812001d80c0c820021a090784030b103026081000001d40740c000001405e80c5008074601100500209002cad95501c00d1030708480b912030585501c1541c2d0301c020010703030619840c2107100805c08103080c400c543c11901d0f5250f07244006414500030360380c7c0f4250303072090000c28000280681001001300303565030360f642100078802c1c20040041d64180144404900070b1458821508074034000410003101501 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 960496654 1250 960495404 960495409
    0x31009090609080c0a05010c05040501020304210501020c07080705060315060c0a0b160909020307090e0703020415090611061b070c05030d0503071e1e020c0d0305091914 74
    0x448103204680050b00d580020000800c950041c1054510520050021038110700f0700301d0a580c40c81c00b005080c800704102c14002664040104c43c240c1d1b088130718040110007603044440d442110203602034090351002ca00801c8070140860418100c03144841243e0016440740204502440251102181f11147c1000c2c00e0707240c1840d8003d840513030746640a840303800c0103d0711411140801195a041450251403010208640021034100039200ba40021030451629010161540c0d41e81c1c060a516013086000040301a44642c04460280804400c0e50715041451034000e49001c480f805600c001c11104090300550010014905200e2580000c2000c1502c4000507581c25661080000f65941515000003007810389007040820f1b40210710b5503c0d1541c92400240040c01303d00c44409100403150410610b8000c1980f2050602500c0c041c0d1041c8a401c6550031016071a20b1000301c1613903007008401e00d51a05150300280600038010095600c1d999100c4000c4000503100100c0c0508074294002041203003050 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 960497904 1250 960496654 960496661
    0x7050703030f0917040504060b1918170c1c051506040b09090c03011404170a090305010e06061002120f0c070e010e06011704110d080f0409150b031009 66
    0xc04404001612101070340362480c6401c1c4d8201e40c6049200000f4081040f07007040c0c45610004c1020480c2141040070305c511201a13110b0f4960640e082008101c085808000b1208000b001850038000048a20308101c45154581c0d9011094521458046020740702440c0121040700106901102502403940315402005d031084c0040c0200345c100e03664440d03010302c641350b84281c203000d20f044000820030f250002d0101401e403001c1013052000080c0a006010001340c06200c0b801030704008241c503d031241c030444000c44584c2c487c5e502c00340c138941c00e2022401d614180401e900b800741c0800d6400c004001e4455200703990300c0b560f40c8048042d412080007003040c8400500050b19420f001001920440d5540e008500302402c02a08190152180701050110030340c0c21a20500000390b15040144c1e9503d002e440301340310100303d154843d000e1222207201c01c04101040b0100c40c402c410a41425454980300c2032864020300440524140d041c0c40c4803008140d02c1d80304010340f4481e00c1d6003110b041200382000c1005029 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 960499154 1250 960497904 960497921
    0x5070c030f23040909050111072f0405041214040b0a080a0e07030516080601150503090709050c2a1f02090a06111905330906040b07080705070303 64
    0xe44264055840307000390020b0040000b0200c14030082030500c414100b40f4210358200c0211042d0210400c0340700c5c00a96114010b1204800003417180750000c0c0800c150100c150301903038a5039400761400c001c02080000d0b046115141012a0f903d00800c2e00740350017103034407500c100d018680ea50340d4217100685025100300b009a0f030064090101250403410061118503b02c415007040351650021141c05030307400045c1c155036004029444c02010b455240100c1d154004050031000020082c0020005520540420040c0c009000010080000303252010182800d81c001e02c40d0610307011503000704060000e55202c086e01c5c006c0030007005001c0c09104030724000c82c00040701d0200041c603902841040c0d810360702d0302040001070406890b600d18038590320381504e0420450b1b41c05510400300305419400070400001d07001804d148285c028055680c031080c2d80384510343e0100e020014011204e801c00140e06008643c860040340309843d05082903d81d00d00641b4042c508076058400036106103c41008a4401d4020510 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 960500404 1250 960499154 960499187
    0xc12030313020f030102070b160c08030402040b18091b04020405300d030203010f092c03090409110108010501090b03161403090708070911180102030906190305070c030f 74
    0x641c0c8020700013103403e80e004804140d600c404604100300c059001e80c0100341c1594003614003503110f82020b542d01d035654040600302a0046540301c00e400c40700c0d10b503900d41c4c5003440e040c00d07903002d15032400e26440b0396103981d104015152000d003154070290705c2c2018001e44044d034030010003040240e400c028290800c4000507a501940700c60740f186ca954481014003c52007921039594015a50350f041420510308400d0303a500c16a007040c07900d00800000724029480d00f5955030444983ca541641d140d504c03620b54003801c0016135109244c10b64240c2040b08104684900c4882070301d0b0f0a18580e40c4100546102d03105125074000240c080000071a8440d17442d04000c103036502e41c240b42c4030424440200c50381d83d400840300300480c0c0d8444501441100d1041000b04000c0c002c005050040050705000e40615000350300c0c05051101c05903519003100ea00a0050365041f0f040900056160700200350401c4c1940b80c803600719404030703140a0214041901c16070300f60f4002c58140d00c900c0c0da1201d41c10300c201d81c0c50080d0b80f42c510 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 960501654 1250 960500404 960500419
    0x30d02030c1215010f0906020c01032a18050d0302030403031107090504050f1006060504140307080d080f06030604021c02120f16050306060109050d030c020a170c1203031302 76
    0x14070b030b0803010740c04502550712a40d0040c2a100b0035400074001442c00c51310481805a011401c00180c0e03400a0304018040c001c1c07070085001d02d50f210485031584510b4035000b01c0c03000940c04400c5201e50000044000202c402c80c98030760070ba80d0760b00740034030b00c424042c01600503041000305102080c000c0d800140d02058003011a40001c1c0c2d213100c0c610454900340e0b001c460b680c1003a10034007141c842c208110900d08556a03420080d0302d16100d8050224030447c42140b4050410292441e0b03903a41c144102c00003882600203540b54015150700c02400c030fa50032149201181e41603408120355040c0010003c2c400c5602134510101c1c00f01b1214a1140150310795403c9a0203d0803039007000c08040180030301c1d11380780b1000000704a410802814185406003a800042c003a60020042280f070741e0b071101c003010807101c003500e18000303200d5107040864103496264406900105841c1000580300d62008500c05403916400603510081c2c02202000605602d4036070796502070f401440400c804005a50844000d584000d1605 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 960502904 1250 960501654 960501667
    0x50319110a2307050a050120060a0b1504050108012105120a021b0d061d0a030e090601020102070c030b18120909070801060522211e0203030d02030c 65
    0x101c1c58000d075060300b00e44010050040c100b00e00801c0030700314841c115007006000280d00b0700c4086002030300725115150401445c0365000c501010000320404003480782009640b01f5241811248001c1e1600c22000d234022003118a80c0d10513488620160b43c140d41c816900d054299113040e800c010000e035000e00e030f0034403030205c41c08410025508021500034203c074070503083e460700c80c03401c0003034280750200451b034090440c0f00a0b0040240c2d02c00f08450900b070f5220364005250780c0e407210340410100140200f180140724120f101d80c18981c00a0441c1030104080f1544c040720390b41c0800490a0303020340c40d03004000320b108160a00001c0c13060311a182c3c3c400400e9508156103043c0350b860074503003450401c4410500c03030001000a00e0342040e01f071181e40421581064001c40d494003000400a100b030000c0811721018000d00e4115544102291000510310b6608204008000540e0a0307001d02c1d007079071304544980710780200150400c100d800104819800502850500901e458000c020350700080c50041e1380541000701c07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 960504154 1250 960502904 960502937
    0x9080408061009050903090d020d1b0815011d07030c02032209060b0723120a180806060d02040908090405100807060806060403033b1c050319 62
    0x50601c6a03010145101c40b80d440d0400f100211000a030003111a904200a04400350b2a00b0125840041d810344020716100d0440c10440c042c05114180102c4404240100203055800060042000007045003400700d02d999452102e1901820625105544006035000420b40e500980c003801d80700702d03540141d0b4a802c5030f03e8414000405000c80000d0600442031090010040e82e200d804041c03c884040c06103400c5540e01d40a110482d1118134880300340c1400c51300440f20710705100341c0a40c510b0741001c1d030b9100c017400030010303180d90804025207904e81c040510010720303c280001d58500441028094040d203860035024040034080385c0d807050b90107807010000000952618404caa20650388405010400307400c101d6002e042140c036034030450401002c9000e10806030f031804d00702c40880754142401130321720405403100100d0080c00d113100310442c641444c0401c400c54680e890b6840c11401251848000700380120041200400324501070300b01e038010310040741c0088660b52090395651042c2400c00e42560040d14 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 960505404 1250 960504154 960504163
    0x503101503020d0b0409030507151b030e0c0a030c180e030a0309170304080409270852050706032c10051b161703010e06010309080408 59
    0x100e440001c0c0c2e00041111160003503100c0c03564400421a03061080d6111510014642c3c0034134000036001c036181070b250000341d0025511404044011400b4401103604200001e40100001d0700d070b50f1414021f03038816240914000b100e41083d25804100c28032038508210321840785202082d030180130b0b60358807040891880400c2001e05100d114540d80810603032000c0c07030302d10380006c0145491241d120040c0240000180b004c801d860541d06400c5c4006400450032561001d01034181111500c05684c00910405100c5282c0003001039014001c550b240c2c030b4448012104010894520692003412a0002000c4c1100d80c840c05448001000c2150a82036043d0340381e05003070082903071010740400d5880c4800c039030004038020840440211a110140c3d500c05942d00c03141c0b101048000311007102d94520000315994110070079140c00c580c03203107105500ca0552420354403000311003040c00e0b29412400d00051148a0940049034140e038035410144c011a1a0080154040e103c8810203c0d0140001d000201c0c090f02c0800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 960506654 1250 960505404 960505439
    0x503060d0c080f120a050306011b061424010e0402031b040602010603050610120308061c05010b0406091803030903020a021509010f02161214070b1207080103030f050310 74
    0x4000c1c18409100f240300c00c0c500f8200c604058060141030285110280d000000d4a40c08402820201c6c0f41c6c2e600030321100c0443c10300d25030061010f850b2464001d0f10088202140e0f100319a028000d0a8001c14840ca008444000142e582d00096507910000c0c480c2c14a03130055070b044402155201070050616a400e004c035081032304820010f0b9586c0c1c004000780b00003000107907000b03240030000d425468140340d61602010b08024018050002010100e80d00341c88605a1040c1c4d04070003a1200c52038059441d20700d010b400600c80741d074402ca00b091000b0420030650701c6580c42540c4546055620075609030380c02d401070081c20b0019003e50080e45103a4015880b4032011a0511f5080e9a1669448a00700c00240610006024100455000c414603290027608008580c0541d04407a070081c0040c8000c1c0f0b4081c0103145540812041c81c015640c0001c4c0b4104200094901040311036070a0200d503a540700d04981a660920000d40060b828803c9180c29a0191000b19004810728039000340013911030424a0107241c940 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 960507904 1250 960506654 960506669
    0x506090d0210110c2b03020f0601060c0b0919140321011d0705030109020904020906040803041a07120813060903021609200924042606070503060d0c 65
    0x680343c03040004180400810050225200030078007903122910001000d00d90400c05400c1c185929110a1600822800761140f10490444100c1d6031103a000610451440c3c804031610410100801c1c480701c8040740d454960a41034080c2c040075002034450803200e40c0181c00a02c8140002c212540c0304940b2044898248404090342815551402003a00400e58070480b00410040d40c020510108c42c1d802022070b0b0445083c55400340e1a400f003100005c00a10900307910baa4051000a030008060700044060011103600340000c00c03440000c25040d031000c0c03040d0107000300555004030003207006501800c445500060391181d00c80f43c0b4a125543c1408841107a0380c00d40c0960f0050b403415650658808452029040b0003805101d800002e447c018070001c0c011589003035200300411500d0303c507280ea03d5800008258800c03000d449082550031070000b68854041c48550342c070090401c41000080c50f0340540e80c044498014851595006003c81b1150000390005601c00c01c00d0062401148003911000082d2201 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 960509154 1250 960507904 960507917
    0xc08040e0a0b1206150111011d150903130b0d0204030812180d02070e07050910030e010b10050a0f140703031b1b080304030207030818041a0a0506090d0210 68
    0x3005101c40802210003c030341d10540404c8062084036664060b801800e003814101b400310005818003400e8080702c068075268070180c1c0741201c603000081107010003005400c1204030f900d03150700181d228030030341544020480d480241002890f60181c000c200c4005603003001800d0903100c0d91800c1441d4400202002d9084240061204004543c0246c0c2c03a002422002030030240240c042c00380d11002d00c0d21804c031040c041d031000620342d2801042281c1440200410040c1395801c540c1020b401405240501400d80d0318101009805040450328040246115107441e0b04104480b10111030f0f900004261204125911b102190f20038440c20180c80168802e40b40031400348a030450042c40401c2e0f880c0e0001c20044003c00c0342c0c90039006142d0600105801c07000c40c0f075807a03a440c01e0036854883c0c0d903400280307500800680c000c004940320201d03182e500411541801410034502054081016069006900a0300b224081016281210040040e2000a032401c085031400f50005a02d0004201001004ca2071 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 960510404 1250 960509154 960509171
    0xc04050c09090a0b2d0d141b0a3c470c100b0f031501090905100e070501230304080d18050c12060c0306010c08040e0a 52
    0x8051006682c0024620000c0103444c40a2002485d1800802c0565011600c182d110790b4020b2403402e45032940b410054a0140c06036500d14103c00403183d64121040b50b4020051060704202801c0b500c942c07500340c02001502c020b42407180c250301e022040441c615a4031082c1940400c1d4001a0b07a41400028030482c50000300f0b8a040300b096100d2104a0381d90b001041c00846031002c02611414041d07600000f41600c20310030b81403000c0703400300f882007406404049c8100d400e451720b5a445a0803001c2c4408081e107440b4a040c95005c00c0c580d851080590403035004144100500c90340405500c0000c44a00440454a002030540f03020001c40c0d010545851594101520030300c01540c218950111020f010500c1d0751410b04041c400204900025000511200c4000b400b40d05032111908080001ca04400c000282e40030b00b80b412654480d890a20a801100a104150a00540811901d1080028101c01450f5580308001115400741e610421151204140300116040f10703500340181c810b0156510004203400c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 960511654 1250 960510404 960510409
    0x9010e090412090f030f0609020114040801090c120525090603050c120a051207140313052b020f0109030506130c0510051209010608010e0102120907030c0e0403020c04050c09 76
    0x21100d0300000284d00060700b0420005003246c01c00100c0d16000040062401094401254200080104c0b140038200125010035070b00d0042d488500403c0c405c9406101603941c81442d0308500c5a45400902217400518065040c486d0b800224031710703040415102000e0b42c5d207900c07400040b151b8942058400d91701c49a106101e605150b000e40c2040c02d0030200a14910596a8600c4e558910101c1030005520020545000301300005400881c015000019a80c803a4a4406141071180852040328400d40b501c3c000070080d1100e00700030404000769030240604a2000d502408134944000c0c841d1410481e82d0138002000c501d041c0041ca0080c601209401d41c0901503043c090083d01264112134806c60782109810243c607081000c41d64200700600d00341d405540e41d80950750044c00c095103d28015400c1074003603000c0d50410b42c014180003a0490039100e564481022a6590351458000107180e1aa009824080080c949001681c898842d204551003001007031b0115040d0750b001d0b504044401d10100e0900b050f031 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 960512904 1250 960511654 960511667
    0x30d05010e10030b01140105070c1502060f062116060206150604150f020a120e0913020108040b0c041a0c060f0c04050d05030d09140601060305060d020609010e090412 73
    0x119101402ca502c60858454004c80007042c4603e88000e09203600d5410203900070002c0c1c921458004401070115035540080d1201c0758624118000140100f10004440d0094002000e000e44030181c11605000b000400d41c100191035400042901d01ca645684140c00343c10b44800c07009080594050180c07400c00c07503103d504404a07010054030501e0248418400c0111141c0d0001c2d88040901c2c10500b00c12031810164140072030030354064003051544202205540c7c00c03000091201c481a5032150450381ea0a07545a0361030b030807810007400180c0d450f02103400300380940440b40c0c019542452036850690b442d900c2400e503120b14490601c08020114401404a01c18819030b903104055404054442c6010700201400348600d00800c2e106900b10f0450b00d050000030020340f500315050103030400c4081440d003400d244045070300070b65128038851a0008604640b007402884e00414000d03092520000482d401c0050701e41204901a0403c210355025101566035441c065014034000c0b81c01c04030b46848100f004009 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 960514154 1250 960512904 960512911
    0x304053c031b091311030105071e1b031808060a05070e0f0a17070803160c27020715052e06080c0f0c06070203131401052703030d05010e 60
    0x6510024800c24030907221031400d44c0d8002058203825040c03d0307a9203001d500e0340f4404205a901580b91408000d0942c0c0c0006c2c2141100c40e001d0340c0c55896000d028000c8940011680c00c1d03560b105c00e0b0018070b0b0000307070051840c00850f200481e078250481c1d0320f03048043d107020401c03103119004c55220410f03c50b202d0340092806030f200c6829601518102800004101e1544492103075070806100a030b000102c040b01444000054107002c0f041d29502c0b4580d00c603a4545400399101035550903480c1800040301540603200741e126460010f00610ae11080421080003034108050a6501c03501c410746a800c201d007980f0484c2d1280c85008000004403030744002c0c92615004a14a04c418902144028086144c1001d0b16507400711060740c150303aa03101c0c14a402e090034045c0100d1200302c2c0c400ca00910031400c0d00030010300341104541041504a41d41c41c00c007075581c4461a002310740458020880141d04080c2c2c20311000d0f00560100c400000c400c1c580000c04e1456102d032090080c0e070f0703a550006002c503245007020942c2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 960515404 1250 960514154 960514183
    0x90203042411040e090d030e1c03060e070c0c09050c120903070611190302090906010f0e27090307020f010c1406010f0e16020304053c03 60
    0x11850203aa404161603040d1400700701141d030424122071070022a8000c1c079007691040001e1519265540315001c00c241060307807030804900038072402c490620b200303103c1e44524284050042c00603004454000803001c2d4160307425810551100b80101d00c5600201442d0301401c4c0c80e03510078884403454241103410945580120309068100780074486201584019142c0f24140704040d4800d40d151000308910358410000001c05041c18041c42912903115500500003059003144d0704c490b900300b039002c11012481070075600b6600c580b01c01e021a4081d40f08062041040d4282d0600c9500d0600580000e90020380110340126000c1e0042a0b403d11164207400342d0350003605140096060000c1d55000601c000d07810001c50741000001540c00060141c28400741e4032081c0f908040e00c420b5612200d017041440214011081e028003540c0200d5a041151404074807180360341da001d0b605007410070042040202494404c4e00c14600c000340d10581144c811071001c42d008241d400070007041c40140b400d140c100b00303d85090720b4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 960516654 1250 960515404 960515407
    0x1e041707060617011a01090b0f1e1b011514030f010e060601030b040b0603040b0c04170a33020d060b210718030f2a03020316050604090e030403050307051005010902 72
    0x305641c00a0014040e22044001e0301d031240e05100507409d0314000c4581030010680b120300c0810300089440000c1007070f80c0ca42056502c03000e00340050382d42a2000360004617650704090100b001440104480c503001c088005040c0c80e5100101d0304403c0c2941c103900a8080c1c1500981c0c03d0280c2582c01d846400342c14002946c091180b4a00f00000400754000103201030a5a10060b0003d041600500111b034050b003001e01c4007500040060840342c1c0c2e00c11241c6000c41707004034060315a018598450400f108580c1750400707500c100c040e0003207900b0086d421481d050314907a62241d00104030600c014000d0005800700105444621580c0c0901c00d0174420050010410710415040d4605a09295920007003525001400c030641d42c00c061030040030b948000c8031000820030380d68032100007400034041c00e44c080324001ca08560000400d10880c0c84074031541e00c07880754403580030082040000d01903007140c000d009942042c0c1c0c0c105552030b113581e03013140d0140000301e8040c0c204102c2c1d485030307240c5440381501500c02c840045 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 960517904 1250 960516654 960516701
    0x10c1e0309030905040e03090306040b270d0c02040219050d0c09211b180c03181407030c0f0801051302011d2b06051e04170706061701 59
    0x500401c100d80696170003142c03500304c840100380f0300b0000c41e091410042c0850b02c1515060a001d099560b0940d54410003181e24403015210950500c01c1c0314400341c24101400324007060791001d480039840484101d801640134001324481c0508030096001072174446d103c40da84c0d0030704510b646007100d15142c000024010145001d000c000300742c0c1001c404091035000c03590440344090425401d2030268004031003080d0350111012822140300705800f422032100030310600c41c000000c1c0e17090341950401907440c491408003810200c00709114071020300301d400180098441403038603511022183c01040e045956012558101009a40002d1041e190700015035103d142485c081a0300092644001c10700900602da084c0d0304081d056507c50b00311000920312844d03080d90f03d0644203a1540c1011005105840462030f20000a9580000e08031044600c4203034020444a66a00d42e500340e001c2c00c038a100020070000c00d1040e0030000d052031055801403c140001c09c01e6814086071002d080d101040c081e21004075011010307 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 960519154 1250 960517904 960517907
    0x71d0d030c080d090c180e070602060c07020d0501020f0a090f0b0904110d0e100c030501030c05060c10050f220210080c0903030f430201030e010c1e030903 68
    0x940000780e9016000759070701d52059000c0d0014151080016161010307200e00010961a42c8500350070315101014140f145141c5c58500c0e0380c0b95042d920440000d80c000c803002482c980741ea1f100a240c028802400074058007a161165822a081a10080181c08001440aa005030400b40c0c5100400a02220585841c1400203a00d041d008180205004030344402d004283c2e040e6404c1944da01000100d0100401903201c040940e60305d4240c072060000a00d0441c452808500c00c0c010366060b690014802c001c00d525180a0041d6a880500076080c980545080034441013058008d103409800000003e400b581413080d0a0308a0200d000c40c804542d6400441c60001600c031f10140080b1003400b4240500d240e0384202c1d000c1640c0c1304010a06504d404000b949080d0308411601074007009906018541408194170f04400748420300040b100d031509036100640e05804003180c101011144189800b14544019000460960f0311120840d00800c04181010078117240107100000440d1880c0750070710a007000c5440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 960520404 1250 960519154 960519167
    0x1a03010303090f180c031811090c040f03111c0305030609130f0b04020109080f10140613020702150d0c0807022d0307140601170d08070e18071d0d03 65
    0x100c80341d011380310b0585c080303070134001c0d4045000c410407210070b03685035000c03450300041612a12114074401c3d003403403021444244909007130307405031010300b28000f4601f41540c503405852a0075180785640103806004252168a0725203545055a100340c980c152681466800c200281174010000e1102c0c00201919602040d60407900500c510780024100036280c8490004072900405a002455035100d540c5c21901481c400040e01000c40401c898200000454010050380743c0009482250b440842c00511000c1c0042940c01804c06902c001d002400303e44448045880b150410301c400c032810f03540e42141650554005890703d81c07140d074910140003411607a0b100d4030b694003010614075100428040c80350300d82603c1001100c8c080d80d008841d04480940051540303540341030900600b02028107403410f0311441c0e00005200c40d031494840c0c44640043c1c3e1420411140c0300d01300c0c0758041e400302210080404038801c80c00701600404c0c03103a0f100c0c00e0300c4400807c00031281d0019200240070756034881080f004a41d1000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 960521654 1250 960520404 960520439
    0x30c0c0c140d23100b01050910030605041803031823100504060603051e1e24070f05090315190c0807080c0309120c071a03010303090f 59
    0x3440c41440251000c51038039410324030000e01859907038041d840c00c00682c90101c00f103040e034081281c480d000b58140240985e1a81c20b042030104030140700306120761a0180b01c0740305900302494000b40b11940c0c0e000040680d00394500d00700b1640c04951858060581c18000c80c1d101a03440e5102855109082c1c0d03490255010310300400715041c05801c5116842c070004e0181c44401c01744254180030f582424180135000307019600c42100c0c20321490361151484130804017000e10754100344010700b81e01c11030070400f0b6607130111140001d24035000d0034120188022424445403540907450025020a03d0004401381003e07000d04c08110501000340502c258a0764001030041d8039112042800c0c800b03446005040c0c1c159042100c100420b141441c0d40c3b0014650300a11075481000341c0d50742d0f00c48036141e0b844020124130080e100c010903030f0040d0700c0c0c1003080b0000b84002c0640c0e010b52011078842d60340da0801c1540c40c5141810805a0510020040040c180c1c01041c00014091410b4440049403234104240340b40c43c650f4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 960522904 1250 960521654 960521669
    0x3040c0e16050a020f07170106060903050c0d020f030d0f0201050c090a12060b12010b0a12020102030d05180a060605030705041b12022107080906070c14210703030c0c0c 74
    0xb83c00d42c0552003400800301404c000d001b19910103484004440a806092107401e80940c40c218000803140d10420b8104101ea811601804030000c590302403140340241c01a0507030308005078100c40e0560703440400801c003a0101c90b90b200491101615030090950b030014016076550346050028241c1559581d80ca0300407030301c11081d0014000382500c1d001c0042d06644000359030040c40d50a07a0550030406400000c5000421a64040c440e42c5400008a601c01251000b0340140c0c018004618903480f2540210340003010314884103c14010101c540d490145044400c80e103143c2c440208011741e0034100070ba8800762404980078800881d042d02404e800071640351220080094114110356940400c0e8103c480d00c5490701901d8002c1c8118031488104803400340e99100010701c0000008024140200300b59004040503a2104054a0144ca603a0203103003260400307000038080e00d4000300f80368a484038032401302c1c501c10343c3c6140c82d80700394107000e81258001c0e40c0e030720b0500044501100c00503028404080c25584c01 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 960524154 1250 960522904 960522907
    0x50a0305090f010e0307170315060901030b030318090c07020d1212060303030203040210030e030a030c0e030a05010e1212061e12070f120c030b06060c070b03040c0e1605 74
    0x14a090240b41860b160421161035203081c89854418074040010506180240d02901c07030503440c1801c4d00f507188000c0355080651040c0382002e0031946020710091504200c149004038120340040000782c115809000c40b0200985007406260090500c811201c0e8001c00209400313050440a80116200303211828004002c40300340442280a81c0c010035060008800c129010050350380c40349405802540f003030750203a2046100d041c582500700c0c4030303000304442d002c3c215011358105206c140d0158040c1400e0100c42061042104202050741c50030007442403130a0242002091822841422501704031480d02d003c41035480c1005180038590f04c1c507120316045030302030310f5013400d4210104800b010b074207903a204035510a2420758100c1441000040d901c090724000e084084c0a9a41c1e141c00000c558400d0354000c0286054001c104081440b0740d00301d0b580400c028044900d0130141c4546070b130810358103800084480c071010003400180101009040007501d00000380742c240d810951480b03031a09642607012003c0260 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 960525404 1250 960524154 960524161
    0x6090607030e19051501090e0a140102040519090506060a0e150405030114090c01030b09011206020f0a030c020c010503091b01020708030c010b040b01030b18060a0e04030f0207060807050a0305 84
    0x500300b001d43c0c040c0303045068003002ca40c6540b8150351110101c400b11200780035041d0020507802c5040c81000c0740c0e415000020410205c1903500e003159040c443d0609001c5550038400028107444a507040c010000d1104042c114031802e1020900403520060400c7d03004440501c000d0456030303040900d503250704408849030b4101c60085108484188500c4d04160303099428656546c0c45030040320115801480203c05989402082600440885062400c0e0a92000030100100200c1d5000c250750300c8400d0098102529150102d00309401d144d2101e41d0100029a94110040070b0079414810900007081c2441c06501c3e60411046140c0d64066541822182160000e18180240c0c000c101c0e2000520f4013500303890300c865440721240d008041c885103450040d0302301080010a50300c03074850303101c03c24401003015040c40222030482d15044001005190082c007031740700c0800c0c40412502c05621452080d6500c1194260702c990090415003185d00060a0121500170708c5041c40e000003d030b90307500c8028038000072183c1c1c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 960526654 1250 960525404 960525431
    0x7080106050105030c0c1f0c021b06180a031704080d030b1e030a0c06020c03060c03091c0e06030f04060b18060d0f0b040521090a09020c01090209100f080609060703 72
    0x103c0ca03080302c6003207c1c445003420a803d40300360851946507405409840e521094607000c82402800d04400d250b0004081148800382d01c07149e030b0f100c40703214000340c0034104090312035440603030100791400e0214508801080030026048100030400c051a030300d14082c8005041c540110b0440041c0d8108800400d0f043d084c0482162030800c00109013030f80006400086959418010351035200c603c001501038000c2500040f000c081c510200d034001c0d1141c2d00200b105140c8009203402e880c1300d804103541041a0702a8240540c0e5407500518041c901c03260010b03006052030b01d0440115644a6481405440e2268009500840203040184e02c041c0c02c1d1100c040110340d61401e54003035400340c80e00034444c0340b45500303100a0000001d07c80d00800c0a40e1805111410803126800103409144456a40085800130a000710b60341500942125601b400000c941c50840b076002580320141102c000074041c0d5a50b10401c141c035a103490440040861a01070100b030b0030041c40d101e4888100600503414945c44902c1e40e100c95 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 960527904 1250 960526654 960526663
    0xd0302030706090804180506031b0109090f0b040605010e01020d0503060f0904050a02010e09010e06010507080d0c0f0e10021203060d0b0906190b03030a080a1805070807080106050105030c0c 83
    0x1a40610100300c40583c074640408160490b0180007022072800284129107050342c4241070040310300400510000701485140c0040440001c841c6040040040c00002d03608070601030a0342e9160741e10004243e0a9141e070501045031031a500544c1003146808501032242d0300482c004d61011310514000d9601e546200c04901d8604000d403215800410706801c020174800b000c6020312543d4800d03130340c114485214804000d141c1b00b084c011809020078013004142c0b0780d80541c0042002d240301d20442410002a00300d00300840e02d0060308800880d182c4003445070b40561140c2d80c1e6040810403550100b0300f00700c500300250f44441081ca000d403000e00001c01300f00c080d0354a80b4112680c50344224024800e2a000c14515142c000c142c60082c1d0600c14082421002c1009020748107094001034000c6051000c0b000c401c1f070b040e00014101c0518150703213160007045040310610a102d0940500001c201c49451f10090900c0c04030146c1c8288296450308505000c0350782e0140840e034101900c58032854440801d01211400d0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 960529154 1250 960527904 960527917
    0x804031e09120f06050612100b01020c060408061e01061b17033412050406140709051201020c1f0e0a0c03020f150a030e0114070206090d0e01020c0d030203 68
    0x401e6400c107141d020000d440c00702c00707243d504c1000c040c0416107030030302481007110040b0082c00140c1c10447e5034001c5c00b04998410b00000c10148112000e100c0720720089442540140c0020300e80f504090100a0814450422000c0c8220210030703100166150600080040d240c480000e02c10031042001d960610070f0300760710180c00c03851440e0001d541c0d00b8040c0c2c550751b10010b03100310b201a07550510110601ea0348135041d002107403465602d6940100f03024094542c0100f0004104885141d0f403030600030f01103500d4044052107100c00b500e1380a4440d040108000300e20078421029000c9070b004010080000a010400004561164400c40040042011400301400b14020600a103100c0c3ca146d90701805030030720030201113070f000380d50181a9424520610601403480180c85059075001c0000400c2d2030f05c80d0b0711000c940d0908400003d00080311001d07902140400307a400303000681c05001406510780c41448100c070840c2c080d00b0710b02c0400281c000045d4a555a080681e0300c07604500409406040c001e1045405 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 960530404 1250 960529154 960529169
    0x51e06010206062d1807140f030403031107050616020f0a0c060813050f03071a0f060111031303050d0314010806041b320409030c02040203040f0803091c0804031e09 72
    0x11510030a132520303030741c020701b11100c9001403d034490380c441c6003000d40102c58028040c0200d55203103640d1500c0c02da019248840707408810341d004020f02d40229901b80700303260051462814003c2c00e2680400c0003850078084d442c0e954115084421142d000901c01a5034108840351402d08040035503031288540f5002d12010000703003540c010f180c0803142c00413010009240151240494103001a010201d80c0b40c4960f040300c0e0181e8600ca0400811120340c041d0100903800c2509604032441d000c00c041e1300201c030321490340c130403111075002c5035540503481d4060003280a100c420705621000c1d5032405204075500c040c0908042c001c0b10404e568120740906441c2c0e088082c080110125000c04043c00d0820501d4032040101440e070500390b0104400c40c82c16020700680c4d5505540c0d19010141d017602000003e50003c0d00c111031200c0c6144460300080c198102840c40340104c0005010740d03a01d508415004484c14074007030b02c100030039402007000282c0c200c080341d03840b5503082510807418416464251440405900000f5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 960531654 1250 960530404 960530419
    0x16060e01020c063402060f04020a0b070803010e0610050406050702040209040504030e0a06020f0a03030b0d0221070e04030503070318050f0a03030b0a060f05130306051e06010206062d 80
    0x1381e00da20b020004d10f54a418100580920140031000c40e00c1d1600d01d45413000180c00542c045000792014181503a04280014011100156101440429640300c2001119070210201c0100211a00412101d5101405480e45c0301d40003400c49000301f0310b100702c0c0034641c24448003042c2501552110346c160f450340704001c0c2040110341400e09000c0d10501d41c2607115407040d4070b40b070004600a031010400c02024402c40c0020494034402c1c0da4150090080e0b4074005030800d694060440c003513501c160807144103992040170411005028841c030f07424000c440d0403c81c1402c4500341032000281d030004c03c1740d1340074601d85000a082c5035400800b100e43c200341c21002c3d25901c00c158000c25038a4000c501c81c0e44003480783d1001c0124441c00c40070302242c207050744140c0e0003090703640e078404501c0e42c001d02c000e080752184c09160082c616280d41e10001180c40907030b600100080520b41500041149480d5950407403000d000612031031401d04009030191a51400f03c40010110070618001c80070072200d0040d074400000c0c2441c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 960532904 1250 960531654 960531661
    0x1504080706080105031009050d05071406010e0907060203090105030a0902060c01050103230c03102d20031524030c09010314090303041106091e01031116060e01020c06 73
    0x1840d180d400e0013102d100e80541071100c0141241d40c498480801c3d4003c0140038000c0c3d041c0f200390b4540d040714006940f00c50300041c480301c070300a0500c2250f02030030010551510500302424114500092034001070155401001009607c0e84c112090341d03484013080300003003001c60040c80441c10900403801c00d0300d91503080400102c00c001e1401010389540482d03580040000e21032010250307035400449801038040d04400419804e804903500142c1c600042e034a5201003000c1700325003c07078a084a0007986030104e65242400b240d272898044109a01c12000c0210324118201109036903a44280800028800d0a04c0c00103075414010703032041000c804032a01c0d402d40d00c0349001d006056443c1c3c410701425002034130b0500407148403c0051203940c043c0d200480107509559035580d644031100c0e1404080c80c1e00210038040000c1a5447c041c00018001c070050440f6040d08511001400b51030140303050f14590381d010310058180300d8280000c40003481d000b06001c0b41700103480256900911403a0f928001600511041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 960534154 1250 960532904 960532907
    0x6040510090915030c0504050a0917071214090103200d0e061003080a0e0d02090109090b070306080307064a06160f0207230406080a0c051504080706 65
    0x4103040310b14a050074044010f55070340c000d08404103800028590b200940090000f420729034001940200c4007800007070203a0f000c0e11801c0d0b0718101d051340c8102c0b0f41c90000c1d04804000c4403481c0d200e0084c11608200e00181c00d0380c90481c403680152006a41010755032016000386130a40b00210420300c04841020703036210400c001c1e070006000500762800c0c0c0c0348131b4080841c0d2074859000f10482200e0b008180d007030610700c814404a848580007199039901004412601c40541d40c0e40710800d0080681440005030300f10b140c9060000c08000402040a05182040411040d10007008032840d041e44468005205040401c500511144020540602207c134a17848243c010b51101074010b13a6082c083d0b50714404d10300082050b5a068111071650095080c00304603180203016034501e089034141c81c0141c4043e03940f1800001c850002c0c141030300f0b484004007003461b151400c007072250788003902e4424040d241c081c2d20b6071688026841a03210343c6004103a1001058040703a03104e001d0b2005094520183d41841c0d5582d40c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 960535404 1250 960534154 960534167
    0x30108010609150e04030507080c0619051807090f15140316050a03110111010e07090c0207151b0611030403030f0902090a020a0c080d0509071703031506040510 70
    0x100e29560f440c24900030001c41d5001d4030b83d4219851280e5411403940c403650b0489241e0049041159407803024041c101352940103220562245031180da19002c00149040d83d08251400601000300360740d5802004510402d02103084010b03a0742c413403408124480c125144000918601d50f00c009542c0700c0c1100800c0c5800c107050806007442e01201240e4580790590f03048094a10310744912544505034542c20800201940780591000c001410000713a940d50104803907083d5101640c40108a170400c00007808050400d1207000a0010503100900070f46040c603032003170071240050300a43d0078014500394400c40a100c03c81c48a20040c5c0c440030034040d1b245074680c040c031f2039003058074124003090800200c5418100d030741c41661000350f002811040c081c0c4406880b100203511803a104020000f809444101040041004141c05800e890001560b840c048520398184000c64008804409100051408490001080c1e81c3c00c42108188407144c018010300090341031040c3d80c06030340c0010b0703c47c219118098011301d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 960536654 1250 960535404 960535409
    0x70c031103191a0c03090c13110d0e0106060215061e100504060801060302030705163f030b011d031c030e0c040213060804020d080f0a0210060e01030f03140301080106 73
    0x107036001d0075100c03130350342c01c1c5680400c4900c8030440c2d101d14500d81151801140500d0301c0c0280b48030026216850303001a5070345030b215000441015441d000f482d01040001d1082c5001000e16101404a0101030040d600050030040e2096200e0746412413158900100c181c2d0824500c10000c06544513000044030240a0b504144983d50116900c54000111617000340202ca200301c80c0c651310149041045044003150f94241c02040e17441e10b0f03202000440b051001502e400e0385102040700103555580030580569800c2c803e4003541c041605000359100d0340d98102e84121003000c11220081009050352020a1800211031a0b0120030220713300751881c4031b5003551040c440d450f8a102590342d811005c20a02c0203a116170034903080c1094034902c04012840c400c1c032040d074220344010700490250840d51140d01c40b540044191641039400000c042400701d4040040c038070300207a01074051021518140305990f24a038141b00190010080f80400d9003054442daa100c50641c1da03980d03c060701e9584500c4114000c00050 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 960537904 1250 960536654 960536693
    0x604030305060d0c030209090f0d120e0318090a09080f09031902010206161e0203030609010905040b070507080720130204080d050906040e16080c070c03110319 70
    0x3020842d0707800d140105800781500444400d1985103541d081c045900c2004201640d28040c4140c19840d0000504c4201c0080b0096501c038000660b039440400100c80d03844151148640c030800911303c050f401240404400e5a00b00c410508941d510f10b030a501400e4102c200600f4000c3c0022042c070740190341c5001e0001520142c0454480704400420742216958100000c0d0169000000150104004942d1508074803e5840c00ca0080100030500620505101d800000960004030404c00c0c44d0500040a60041c0a0f5100c184824100b50300d65004600c40540307898100040010650700340880c0404954400e03a000310310060020702d450a446010514404552240507640c0390a90303201c1c064004d8409440968015003016000a9010780d115444110100d400107000c2c80000703100182146107a2207600e61804001e808914018002d00c040002010200703203000600c2148045404504130205681e40214007114549200c000645040c00040451141800ca501c0d10010010914103004205191 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 960539154 1250 960537904 960537911
    0x403030f0b060c0a06050604110304050706110712030305040c1214060601020c010e040507090305060a02090108062b1112150c030105030a170d0e010c02160b0d050c0f0a0206040303 79
    0x800742002200e1003450400d002c00e030b00c50a44640030404a40c86a504400001d00005100070a00054507554204503425650b075000700104112441e000391202c408182218040d2801d80d04114103802c0e0b18403440409820142d4030b8000404009081c20010040e11208428482c0e0810303510f007814401403440e216442500606020400e554000910441006016140d81c2d9801d01010288030007000000c0c0524200001484004007160b014045c44d40034004030170000d42e07540803136400034084c1c0c940600300b10300980d40700040e90614101c0801c503404460004010706051006820b210701c1207107000503025401034460042c10fa0b2108006843c0d03882c0040c0e442d501c04142d8600514a8090109201d8250144c00400d0140000b8840205040c81591901a42c034100302d004c0481c01c0c101ca141100a500c82d80d503c040445906804000b15410750503040c2d1800b18041c1403c1000322039000c4e4101d01807031b15440d0303000315864103c01e1040d150000f07051481103071940d010a100075581c901c151010b4020924 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 960540404 1250 960539154 960539171
    0x329030106150516020a05060a08100b0a050d0c0c060213030203070905010b0313030c060903110606030a031b1515050a08010e061b0d060b0406172a0d050403030f 71
    0x442c0640d07803402d9030700e40c03141d0b03090441d012030900c41d09103030f00f03030403a8422500b0802280d6950740c0c0c070161600410f55034134075a041c81d000b5000001180e071500000080081406060f1005511208071030440080020111310340211001c03c1d924500ca8000c0201074900100383c2d5040072075004284000c4a000310300701d40b04166204d0030041101c07001c1c060840342e003604100080d031030000c401c0301d2021b039840381c13500c1c0e10b042c40151202070848040c08001c40004102c1140e0a40d80b03841002000d0f080f49045011700413074007442c0d4016085856104903030141c2c0d074001c04900284081031a803070018100b5004240300256410391041f42426090103018401c0009041c045203070740051050b41d046041940082003a62140c02c4182c078050744844028610030010804c0108844440c01101d0080c51341440c555100d60400d02c0241600b003514140301041c403c1d410400038a00501054090581c1c40c2000e001d150049841361018544100c074401c1409c07500b440188010503600d9842141d00c000c12240c03c004041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 960541654 1250 960540404 960540419
    0x210c0c090e0c09190203040314040e10082a03100f06081207030207181b0207030b061212090103020c07080d0e090402101101020c01060b0d0c0e10050304030329030106 73
    0xe0b404e88250702c0440903521100004240b40d8001c40c0c010340a82071100050034203030944405907201e0340003d1a03c0c00d0a505008141c0403200000d070150989101030b29010700007060b0101c030314018a403212101400200c110016031020701669101040750801403180c0d09141d50400098030442c0b04181091080f0040c0b1442000792034103450030a40c0c580c0c0684030303051418088540e8109890790780130441395075040d4028101111000d41e0f2408142d0380150805500c0d44c2841703038840704c0c0100414050184408141031407400410400540c0c0410140c130f545031035011004a0085c0510398405900e03214001e80400c06640000340c1c200400d41c84e0341e03011621920354003030040110060350300a403c6006200c4031241c4500075400001c08030855030005080c07038070710701d2002d080d900240c0c8841c025110002c2e401c84035010328040d880d5040b6880c1802e5101030705c8200407071701d94400b2700340b11800c0081c08030100d420107100f40c01010400d11210799415140307080300e00d40320000040050785171081d0700e009000650320 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 960542904 1250 960541654 960541669
    0xb1215270604030e130e0606090711030909040807121d03010204060f0c02030c09010f05120a020f090c07020d0c150311090f04140406020301170604210c0c090e0c 71
    0x3000406440c0079107403603038240c0350040200045640601c10040e0441141800d20030040907507051001840301d41000070610080c5c282c042c04040811001c401c6450f04007400000722503220070180c68500e401e0303a5506103001980039281006240641800d6600105d41e03000c044645200406002c01e4090005141050300300c0c46a88641c002207501050303514500340c050280da00b00d0741e0001c0c040e54028541d070303400681000426008a40c3c0000c1c1c001e4103220701e052590044501c2a542002844804000c2e00011102e913030082102d4850101d4000140748078151000752000164080c102d0070408071180303440d00c100f01c1e840c01000c01c0c600202070600e180c1d03442801001241c1c422085014941091041032080d5415090905500162100128004005181100d5206034041da00060301e03541406402d03001c11580c05040b8000768044001c0c000401d401121607030044090070440d801102d950181550700620b0b1007005001d40b88001c00000b10b5582ca60044502d074203100c016a90900c81040811144 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 960544154 1250 960542904 960542971
    0x19030f0b0618090601030b06180126010905030301030b060a03060903051e07021509220f110c03040909111002060f310302030c1b040b060f09040b1215 66
    0x451340716600400100704600070050b002070000d0181c1034030f84c200030400d850b2190300b80d0010301035201142d5101905514001c5c14500d000f4080b000384102012512010794902041c00003915600c080c01c0420065600c1001c080000c550000c001e20154145050261440d0006540e8410403100340c2000403007085c8000803108007941c002c280013000485041400030a41154540e560005280c1101c81c400c40305455204080010142c8080b4041240c000c040307080c1c8a03001c0b4441401f030300900a07481c100b00e003c400d84041e286048400a00c80c0c205082c2040305082d400c400d6500481d090810001142e80821440c1c4240c040204101d06501c4406c005203107280f04030303680001c22007118802103020031340c2391b0188021402441203d0801e000700300c106041c0140134000c17200f101c00d00c48511800f804c01307001e510100c00c0c040700c0300c0c1e04100402d2010390a92054100c041d02c00c2d5034401d903103046a5501d69070310259009034803c40e03500c0c95440301d001da4a2101910100b04200002400794504901c07503485010 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 960545404 1250 960544154 960544171
    0x509090a061e0f050402030c0a060f05093606061c150816030303050907050a270c05040906150f260a1a010305010b0919030f0b0618 58
    0x90045881d65070040038025514049080305401d00c100c4a0060701480c4540e404001000402e4145841010b280403070382a109802105690800c0043d140c010048014220185c10100d90321465074000a031408405175114034a6490110500e030403200b0b9503906180c84417801610791054a0b0082005814001c00c04d401110080342050988081c0d0aa04220119444c074000b12503901e44441e80c1e6030600304003d40745040d03405032420030402d1552500405070070200c1180545029414240481c00c42201c60051000c200340d51800740d54607401030380f52a07000b202414410040391510384002050ba81c0305100360a04181400400301d03d17410001080380711101543c4604420190401041d10480d240303044c001c0884107407001d40d01040403400c2d40c1500c210703c003030750000c0d608001030f120070054010907900ca0304151a00d0014010f401c1500102c0c3d0b40c440d000c55012914015402404400d52a1500028500c040603500101000034100c1014003034081142c0d202d18880001001c0781e1002d104481592 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 960546654 1250 960545404 960545413
    0xa0c14040e160b070201030e0f010e060f06090f071e0908070501030203010b030f180102030405010b011d2d060d0903030b09070c020907091e050a060e0607080c031b01050402010207050909 82
    0x2c6001003000c01014610b1047c10045a03100300e900c0668200710070024442c3d440c0c1d454030360000c4003000c2132003680c0d070200d803104c2100803500f0b0134004a242e07520000c100c030002d107092202007125075020394402502c0e1a103038101e40800d40c4c1c90810041c2a50b0786481805002e100380c001c0410720390b00078003d0f2070503142110640d170b0030340d81e072a16000c2d010030010b4100d42800d00700b042c038450200028001548520b015400100c0e5515004000501d0040c1c5140a00340f66008510400000d0b6603500240181c43c03005042d07120100c402480003256a6840c01c01c44d07074408030019000010405075044060351602917101041650100c0c41804040c2000700c2d82440040c0800400704010301d06492015000441458241e040307684420303e61f50701d02d409800d2588002e032910004c0000780b030710507801e1028090601d0b01000203ca000c0124225004800c00100820804076141c1d002031001c10640d813003681019504481c03012250b504d24002c2030306071400d0303006024220011600341001e070410360050301000001d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 960547904 1250 960546654 960546659
    0x1090e0a050c09060d14102304180b0a0c050903060c13090c050d05220818060a080103030212030c040504050406090b0c040504060e0717090a0c14040e16 67
    0x8100400c4020007650241c041408003d080380c0f038030005088030003a5044002a090340c10004403008510041c80c0f2a00200401d200784078183d00b00342c00c404101e40c2c88101025004001c0d00182c0600f481c0781c02d110002000384036240030310044e000b10b00d00a04038030300f04001000d440c906c120340384d04c247d100c219095401100800c504064403001840da200c102005c05090070f0f00c455001d07055407100340344503001500128030f441018080e0b200d44d9801001c2c41250341010003084041b8100030b0051140904444000f08298101c011300d680d018800d11170050000b07580740c080003000b4000800a000640040c8150401120900044000c83c1e000f01079000074981018944400c20002e0080140700711503c949880705c1c41e0000b200040c9590041c0c84002031507403181d00b03000600040b00d20316444031030344c03014a42c144000b00e40c000381c1b4031103946007466148041e0b9485400c410b00c1c2c001c101e40014101c2100c00720004032907480000400804c0400c582c10303c441f050a40c42076641d02d046c1d9104080070315124004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 960549154 1250 960547904 960547921
    0x90a020a170711070605030a0c0206091216050d0f080901060b19030b040f240f0504090c081002190203120a05150613030215070b0c03222001090e 64
    0x1041d8040b60625006100601c0c91459a080c03100a80c854400b1400110500401031082d000f0b21001d9801c6d8801015189840c1204030740d03904244540f00780c0c900c2c0004101400b103480e04c9160303980c16001030484460200e02240203010a02c10000000051035134404503010070301c18003601c021503044181d0542051544c40c1c4040702803020080341428559503682c401405d4896010781c40c0c000240c440d001960560940b42c450000418241c80c2e40c1641440005010fa10380d401401010b83d601038800060f540d049242c4201d048580e038000c405580b01d00d4242601c03800301034000340340c11480b00400c1001c0d10504031090b60b40e0301800140e221610801d03030005500280702c2d4001c2c0d50111944142c1c2d000d041700b41010504940c40b0502c6041c00320780c00e0505005504041040041310b029420307405160108980324809241d0010308655448100000030445500c084203030703441101c0580b0a44040c1150350328080004410884500c490121407060036003103580112409000c0765004001d0542c2da6640620 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 960550404 1250 960549154 960549197
    0x31803120a14070f05070609090b01020303130c2d050604030f0b0a20070b0c0408030a030c051c0e010507020c210a0b0709080105130201140a14031005090a020a 70
    0x207815040d40030074442e42002c04c0413031058290b082e000300003402c8802c0c2042d00003803510b01540c00001c511420040c3c1c0700f06907680042102c1e40690174155100d0700b03001d145400d0300d041034160b00c680c06002e100440d0000c01c51800740d0303d0703e210448600003c1c4250b9603d052150f00e018034440079100300004040c041c081103403196190780c0f24805210018030505e500800700121500c02c500c0180c4680081400310400454507034164100d40711801e400d0070585040a00c9940340306d10401d4030b04050703d90511385609800751040ea00560a00b440b81c0b0481d0524003a101c004040c2c0c9008240d01d0342c20103010a1015001180c0c6440440001d8100e0381100d4041080c6861020340c0300c001651807098503040b80204094038403180c003540441d0784048001d441d0440203800d4400140c103c02041200141c03d20041c0c1e00000507480440d09004140c0d1190b01140060b40c4c0340b10469502020814000200009000065003003c259403044849031405d440c0e01140804078003c4000080204560b80c000c0c0d10190141c00c0b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 960551654 1250 960550404 960550427
    0x10603020a0306051009051e0615070f05070e0c09040513081b03040503030a0e09180a0b06131d0d090518040813080a020a152003040e010305031803120a 67
    0x2d642c0039582e1b1038014100c4408480c10042030400302c0341c0d8080c0d401c6000700c0540007a000c0703c00145281444211480500c6004401050742c00961a2542048014482440202002c21038076030b007460115103920b0968081450240305070700d030100143c82c04400c502d60504060308440300e0ba003401c8010300c1402100c8843c150b0f94401d440300740400101c56038208001e203402e0313001d55644c0d128144000180221800007a000b1700c01c0d1583e440c0711000c1b00400080d860030468109200d020300361200e40118585d001c0b00d804450384641003131003840380c142908460a40c4a1030200803140010350000c42240e0a109030300039182d010404124041c21001000b01d219001402076000a1030311240291054980440303074462034080c0c015135122000e502c1e158401385e008000445078800500d004820081425980190381c1024503203160038924001c3c0d0400523100940442d46500c0440c1d61607041c541da503604565451800e00c0c8410204003014100820884040c0392104d660506050003e002514142e803c032 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 960552904 1250 960551654 960551671
    0x607200613290114090f010308070201030c11060f070912031d03031c0605010e040225050f010f061a0a0801090c050d1802040b030118080702041119020f010603020a030605 75
    0x340c10794180d032188110050080040d032a0031002c46031541c0511402d517000030201143c03080c1c0600100080340a030000c40e0500d0740e0918000030300711032404040c0d41c421100c0c40c001c40c061040c2c50402822120000c5554064002c80d21000b00070b03507a0b01860040401118401000134000b17149212251415600350b01c402c1100400707690403c03414140d01300c102240c6045e42804d1a0b25000c0070841940c0000c00e0001621050700c05500d0f1205140b240d10250502d0403080002c543d81c01200810f018080c080100c040509000030b125084081058030301510003030054001108080c6450590700444404461408030991030300703d0aa840d0115450041071400c842e03905020041019440b68461072003109100b0b40f05031040c0489241c1401404229a90303e070385980aa89400880144100151314030884d042c0d01902103980d40b102032012801501c0b240d0702100d0542408982490f002c400d00da01c8408005181e801c40b409020a600c0103801e80d85140310180d0080825081400400c00301e4100070b9000f6503e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 960554154 1250 960552904 960552953
    0x30309040905011805070e06010305010b090907030b030f0a0311030306030a23070b0705011503081c1410030b070207030b0a020d0b131d0f0622050607200613 69
    0x198080130320400103541203a03290040c80c402d10860614070303045a084102841c1c200615130601392840068031805d00000c0c4038001e404001071900d0b20a80016103007040140650741d03241c02051041e07941703080008046000c1070341410440c030555800001e0700d1041e003009000303210315515038607044080030300308041c4045500c034480c0051003d0310030407900004203d00d82d0100d80c0d640403030820500b1602c202524111556014a0800c00710b00c240d002c1c0c400c2c2c04410103964037501c4000358100c0040401c0c11100d40c0c004421800c02c507107034880d800c04000b120b00a60164a02c0c0d900c0c00c208984510650200516007002c420100e90010302c1a80034080700c3c0583c02d03000842c2048a030010728212034000e03120701915240e1041c2030324445a50300e441c502c1d64901d001003001c1050300d90165243c010050070702030001500300c003041c0c034801846031032411990444161a40d5080010008000c204c0140c0c081200315000c0407040842c420006555100301c1140c040000643e00c00e540d10004030a11120b01d041c04000f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 960555404 1250 960554154 960554171
    0x3030b0319030c03140a02070302130204120b07021c0203030420091f06050406050706050c040302130c02061602060601121b02010b0307050a0f18020f0c0102030405160503030904090501 81
    0x3001000c004814002c3d203d5983d0407030701d442c009043c004000701803c40900d0600107014116000100102503a03812a01c0c0d4540741d050411040c0203008136400b0400c900140000402400340d8200c3c00c0b4010b07113560f801c2e5000c2c0d05003e11101203040c424101d07940180d2081002401103144400050382a5511702d5049030040c0329140081c039403050035203ca040c0b02101701d0001d010b2500303042010008202034140142443c3ca07011028141380108440901905e4032400040c1d4134082010413a0061075000703007211081c80001850f080100030300080c18015200707540c0491540110301090b0501e0104940c000e001c07650340d460044a04030f085000110305142c4400201401034244403c4030925255940002100701c501b204062400c1d030035502040c050900600b0500c8500d0880155500303a501341c61408400c40248005070009110304680404040c0000c00d00030709418041d00218092400341080701c0740c44400c1d0a0380052005240300d090f03411b61080068800a04064008105c441e005038000038035280f = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 960556654 1250 960555404 960555433
    0x190209031c1706030c0a0306021b071701060501140a0e01021c0c03090b0403030e0105210709090b0f0108160e032d010236040f290d03030b03 62
    0x20350301d400020900492440b0340a1810041040d44040304400900782c003194200895101c40e046c0c0005020f840d00050124800850b501c0044c000788039100464480981d102c210039001c0b401281c1d0580b8550800c440010207610515030200b00e08184410707a4500100e185042d900c0044005029056000c3d00111000c01540d6400303020000b0440c7c0c0f90075803540311518004050f41c2d03e0b070b0031602a803501800240082540b1161400014100382841c9a44d51402081c4c907940d08032071858852180c80c10420410b4460b031100000b0115440c411040c00301c079007070908014240551500c4030340041c508400046c5142000c000c500104592802c00941240c3d220002c2400c0c48514035005150311a803500c60380d0201c220201750005255201d00071410003000c02004400e0f030001c0010440030b10f2810112610b078141c0c2c10100403e00c603008100300300d4001c1d40340300701e00504514501e0400e19000450b001c0c8030400d01e445800d50000c4010021811500c0e00d65066004082109000340c00d0321a154800c00f406 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 960557904 1250 960556654 960556693
    0x90f010c0f0804050f012d050f04080d0801090e0c01211a100c0f1712270a0506061c0f060b0a12020f091902070614090619020903 57
    0x16014100c055551400c0009110030b603001742c6503042c100f02d18001d03140c1848804a2001f00321454400354041140c03201041150306010b04030070045010303000640001c003890001401040b11645403201c16540e03030786004010807038868500401c0a50005c04c1940700561013210045000701d10001851188024041d441089500003070001150350141e4580f0201464118200301d44100d207407400103d03e0800d603030741d05003044c0c00c031b04000d185003500304c544001c03049884150742481c81c42000d680c805e480c051801c4001200c0350501b5611031304c3c0140b801240d052001ca100100c2ca50090014541c9485140500005c00c1c4194480340000840c1012000004c1480410303a119600856000c10060340b81d808121180041d0361002080406242a000058450325080703441a1001c0712003541da596220455080c03070441010003420240700140d00c0040000e2079100c802d468560b20106201a9141800079699410549a0040d600700304601080c401d003484e00201442940601600c000030004560384041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 960559154 1250 960557904 960557933
    0xd080a141b03041d091009060f09300203090112090c03050307151e09110a081614011b030c0204090b090d08040305030c0904090c1e060311090f010c 65
    0x80d900700283c10490a002d80920030340707404480706005403c0c100884486d580b61002d15201e00d00b580c440381200700340301095100b03100303916030241c05102469081c60401c00b000103c40c030014003220088034240e03d09070881c0044140103510380045140c000142c00540320802d401c50002c1d059500c40c0304240020391001900c60055200e207004648450b1585411a103521500e940c6001651400407480100190820140f0300b21685440001e66055241454034802c005c2d00e600700d030026920b403000034270408001078180c0c1128044420490303040e110900c4180c104141003032b941c0000c107040c03542d8050815100440124038800e00700504110140c2c4c0c082410b65454043c280c44000c00d410811003016001d00c01e002c880b50f007510f4008038510707241e500544107003c09441050f25080106180e0304903201ca81c403101150ba081101c00350800d036140d10280d1400d4064a483c1c07030521101400048003400ba0007100c01102d494048241406031810501c01c0480d1418100d0f4100000180c0e101d01140e15086140361 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 960560404 1250 960559154 960559207
    0x50717040209010909140339151503152211010516051501061706010909053304060503060403090909150c0e040612030c0f020f060a020d0e0d080a14 65
    0x184203420b038007007090364840c16201501a101c4c0e0a000e160410214803440d40e41c000b0b030190515510781104ae00c0003c28800e0030250103220f01600c041d6500184c40d038062003240280c05112600c0d05010a0340003244911000405440900d00742600642c014000303442d100d08000e810a40c0320441e0740b605890080688580494002c0308e10041c80444e80c852070940c01c40300760704c5072583c150503c6000206034860314401c401034240d40b10082010b0b100c1004100070001d01035000f8182281c060340d040306040c4415940c05219900d411070005403800d011030310611940c0c02d03490343c150840c5007040440c0985260f400444003070600000c20b0444018600c00e0085409042d82d542807140580d00c140030445505400049440c00452039602c00031794812001451190301021603840d900540c80810000307042425036540c40727640410400449640000e00030500c1d4000d83d80c058600c2c0d1203205010080034410409804a903013040b4454a0700e01503806403000441c0284d1203840e00b0b0444001c1a0360195a154868 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 960561654 1250 960560404 960560437
    0x10e0a030815010c1a040c051203030a18080d020705010b0a15020706091202150f070f11010c110f01090b03010f1a042111090a0507170402090109091403 67
    0x8502951101d91281141003030130005118202034a40e120514400350b000303030302241c144c8000780400415980c041d0003801e020701080c007180e49486005440303400031521030100f01d01d440c00400040500800f040c200a410000703a9152102c81c03220100039510203001552550b498400280142e102e040c207000091581b420003a080200c42c1000908061080c1e00c50002c20003070400500424120001c5820034541c100c402e01e0035280d406060202c0d900402c06000078006c8045503080c18021030710052a5014492413000b03009d03042040054806001c40c00f000340240316001a9807404d810000c1c2005861041410554001139030703007140c0b881c01d5200343c1262001d00c00b204010082c002e062103e5100c102c0c10080d4140c02c150420111f0f54a60300090b54966034000d0000f16101401282d880c041e16950010b40f0380032840c031301002080080d02044d12030f0000214003044111400c0c01c00411075001c0d503401807909809905c0d1006130009080400001c0d82d10b6041280082d00b141e070100010301050b81040c4154 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 960562904 1250 960561654 960561661
    0x30a020f191a090108073e0f0309120a050d030203040602070c03031d180c03100b0406090e09060f010b090a05040e10050f040309090c030b12010b09070e06041205010e0a0308 76
    0x10215a03028080c20140811f141014400c440011200354800b0720301c18002020703080142c401e09180503088a4074900340152082420181c2000c4007c1c4101141a0340c41c460342408100740302e42c1c51019110107000ca4000c004900040c5101c2c0d00215041402050050b083c82e94a0310f8040d40f005141d4004c6010910760a03a00d49906250b0007148017140e41101d541c68a114a8074514885190080501c4024030001000890300c216002041000c0c01c41900c0d00b9440707076280d0317401a1510556014503884034906600043c00480c00084e01442a4041364035801306900e008131440d900e422510105a02908400c4003040700d40380c910415003404211401080b15044c001c0c03d00d030464001a0030581c0014000e01040701003604400d8a00444071204c5000602c509c043c034049001f011000c803804d6010141440720f550750901500080503800040700c40d001d46858820b0180e03a05101413241641203001400108007910348507940740150740c00341c000030a0100031202c041d400c0001c0c501c5c084010805a4090 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 960564154 1250 960562904 960562907
    0x17070b18131e230402090603030712020705030106091116212303040f0b04170a050703080a1803031e050c040306060b0901081303021f02090906030a020f191a0901 71
    0x10b400081041c01ca102402e18081e43c003110b5503120090019006003055030100303c25071810400c4403820742d00b111034210300c01000389009440700d4040c81054400d6080202c00b00d482401407044940d000b20004d80b00f41740980121900c0d45881d034101c000d46001d41c5c1010604c2418512401d19aa500d0711565640300740c82e000200c0c203d000000500350300c141481441000009004c1030f04040ea5650441c081d180d9664491400092941c00c140004150810104414140541010150852a200b40c640003c6035503565201c1e03084400c140740c071070410071048200b4004640a80d0082c1168015a0704030480c40b41c65401020984c1c0054419420842d4001003c106101c014803c820280c9900074019182001450000b03080440160902041d884824504c000b01402040070303070a441c1c00e54134080c4410b41e081c0f0b904002500302e818554050383c040d000041841c03402280c40d8510350380c01800c251343e02c6000000e002d200226190700075003a11103000d02080051441401032103a80c0c0614642c0e0b91030001400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 960565404 1250 960564154 960564161
    0x40f1211070f08060606070609060609020a02010b12030f0f0405030703031809090804090c05090d030906023003090a150203010906050603040f03030e03210117070b18131e 75
    0x21407840c91510280510852001007500d80d0084c001b1904130340c030340c000c1e030401100070504820020700355454400001010003403034028000013126500200034010f604024040000b03007030b440300080c5400401c007166840b499240641115082085200e041c5a00e400203c0d02d0040035800903000b003602c0580080025144d480740c24081c0030311140500045c01c1c2540c468406000790b0084038051612103903115103840c1b01e801a120002c1c0700901182c040d140c1800d0141c01d6129602604005000314032290320100400c1e081408034140c00b00c3c0751060740b41361911851494201415a080078080d054903100032a001800500c0804d02146005aaa502d05122401210000da01090140710140104004a842d00042125282d010306000ca104010703034400600718891110b40000b030020415170303000f170305035002009810380d100e1a4240c4903029408408968460b10f03403107505409141000005091006486801e55100010b042e0354010340013420783e0025200c5a842c0690302c0d15100006e4000b007140c901 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 960566654 1250 960565404 960565409
    0x604150b041a1f3f1d0703110d140709050f06011b020910090608030d05010801020c070311010215091501140d020108150603040534030b040f121107 65
    0xa504014030f2a00302c8013428050640c251034003880c45099205240b03a20000c2d194000f21000c0c07000340c011480d250050f0000b04445c03021281c0800003250014120350300003600800303890b00070f28a600c0341c4201a0030800b035030281010890380ca1070b480840315420f540411040010305100e020125a610307044003c4450031100030003460402c00e1410310140c480080c0c4030141c100e5501542d1840c1d01740d031282c00d1280c01605942c4446e8540d4681440010440c2b000302c060207001c000740d4428050f9036a00c50f50300b4241d000d010050421608651020000614100c0c50007180d4107060050b10402c1c01e2000c4580808081110003500e00e400844180441d0f070042603007a805000701c8aa83d115400ea801c1c0401c60412607031200a05001c44000440c08410b51300a001784000d40003030082c1c0ea00e2929280054803580d40703d20b00382c0b80c1c06440d51145444e0656240046400340d00c0d00c60211240c0c07071a29444081032000c2c006603810200581c0c0710010034401c03c00115824582d4860440c0e2000300c5010030700d4081c1c513a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 960567904 1250 960566654 960566689
    0x40914191a040f061703040501110307020a05060a031113030b10321936240f06230901081b03040b0406110c0604150b041a 54
    0x7040360708414030036031a0609540002d80d40050000c0c60b0100c0f01004040c5a000b00c15074040301994609031510020003081610400e0782c9038840c3c0300144a2090345d0740140b400007507000603618410300450618201400884003145804100b250060400458a07482120400d01c01100900c040c03060190803501c00390005105031040100503e040341c1c206090401c9061030180211060040c1d0808001807420241c9440040c548003004071006480c1e21055414491404100114900300b0f01aa0101c1c806200303600e0a0000381c2d150103090b0840400400d011911104514200c401488000454014240240c01100b00003103c25040290150502210214a04212083e00c4003896020740800c2624050030085c01c040680b03407a5004240e50140b4210004401b01d9800300c00c000c14040104049130040740204800c004010751401002c5585c0306505110307030940d105002090010b00781580301c2120394424440010310f4811440003a040d01c0c0900c3e1009100c0c1100c08826440b4a402e907000071a0100a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 960569154 1250 960567904 960567911
    0x201260703090c0b210601030e030c0f1c0207050112110714010522022b150b0f0f090703020f04080c12010e1e1f050a0c03110904020c0304091419 64
    0x78400380300340d80c40480100800c0300f0742e005c001c0303100759004e03410640c142d5400b50242e070303103e400c03002080d556a040720782c03104010300c80ca0005140d01d08100e45007480c1c0740b0842c2d02422840381080010358880300c007140c021681c0c07984d0b114100202e900d000c0c042c1c240940f058510b82011110100b00c50700351800548000c42c00110345480190805071001c1d612000399054503d21050320090114154185010441142c0741c080054201e08100015881150408415504003c008400c0062040c102c40b00703240c01c0c0d04091400d0f00e220151402500d00b40e4040b00b0381c6405031419500440400309a08a0b034841c021550018045100600c3d180ca9441110180300c03008004a0781c2c0340c5080c070360f60000e0380c103401102c02d0000f00074a100c1a00b07100304124407584003218241880c00e142808000c16084504200c803c0ca4491a801035912034020001c000040082c1141841c480c40f0800000b5403010202501c00d01c410000080c0a009900a142c402407a4024272181c40c58a0030b50b540031842c8078804032048614 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 960570404 1250 960569154 960569167
    0x306080d050315041b27050d080705010504030801060815101b0204150e0a020c0a02011b02090f070e100509130635030715180c0e01060f030b06070201260703090c0b 72
    0x60301c41c86d5400b15001110020b00d801d44a042141282c49040f20140165090508101c14190094032640c102c50540d07403a54004c0d0744046401c4591602c207403409510011118610404a218140116071101403c42c04800e405040d40041d04550928101da0588943d0340420848804041a210b500035a80c40055140000244c03925071070702480d400081c140b04107020441c0c034041c040007040d09919400b810310718203030a20340301c080380402c4e00b16050340c00280c51603102d881a09180310f05402d140c2d2203860382c605082d400000c01010114414910a5039a1340304c60000c0c072011060b0203005214241032760310000b40700710340090004400044818180350f104105010004041888400400d40c1200c00000e021402102c2c545540401e60000703000522101804100c03c0c0c40d40c80d0481c1215074546030700b55803000142c1c042d41a9a404a0101e0344854180482000355009040c6c0078003a4000007540039942e00701e05e80039215410f0a80b10000000d6946000b20200441f568040001d0714410107040c1c2000c4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 960571654 1250 960570404 960570467
    0xe07080705060c03040317030f0916060e060906032a040b07020103090213090302010e01050603191502071505091504080a030e01020903150f01060306080d050315041b 73
    0x6094801c190040c103000442c8001d004050041c4d40142d54030440c03d040313041001001d070400341c2042e204980d181d516840440c51544000910b000800c01d86882140600d103403900a444200410141e181c10010070000442140d680500035803080c88a1440000c0119490140e000c0d158800c0f060031451071420170084c40003940c07900075640381d641d0920340452295150301c003080d0381000f890b06885040b070030401d0403c20107406400c01031400034410000c11141d501c032005c042d03990f44044040441000140881c0f00440c0911014680103042150050301d00401c80e0b03600d0186031100f0418103a00c5580e40c0500c611310006000300b94400408180300c10860030541c41d03030215031154108480c103240d52003070b0101c01c048080d0180c8032001402019035031100022503840700c09500466101d282d070ba05076000410514000d11504055a8551000f00f601c60f1030303880290340d83c0c1e00c003804400054071417114001d140c1c1d0719070117804201c0c0c1004900c2000e200003014081e1181c4401e0b450500354020f0b4030280822038 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 960572904 1250 960571654 960571663
    0xe160e13032304030c0e0f0606040506070807320d05070804120515150a1a1213020d240c050a03020a0c08070f05122b0e0708100e0708 59
    0x20064403440c00740d0b11400c400d032182d851049500041807198201c000081800f42456514030806040c03c0344001035031075030200b0030540700b18024075610040520106011502540c06000c00c6c0744610240214076103210580060b00720000300d020300304000f82c42810000c030814064007a81518a0500c1414042243d0740c100c520300490049135851010f054001080c0002040f258034048000c000c404820b0900d400e00044400001d0b005a0103071403043c000040b50b0743c140712143d44241e04100b62608106030760003d032842800107070a2440d0600c040d81c030600580c1d68106003a1103c0e1140780c95822520302c650300c580d070646c000e0240c203441e2850240410181c5c0e420004880080c9010b140059942c108044256901c1e464048007510f844c201181203410066402100c105180c09501101c0d220300e0b044440380c410b1301c2600c40c080c0d00700d058204100628013010600041080d00c10720003140560b0001c0c3c42515000d19540417014503842441010b203503004500c203118030000d00e08041d000041c1400f0003203954 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 960574154 1250 960572904 960572927
    0x41202030a09120218041101030b0613050f0105130b09040b10080f130c0f05150408030d0515030d0f030c0201091106030a1401030305070c0b18130e160e1303 69
    0xc10208100700c108641c2d03034004e010342d080d0301114600c0103421b003410b081900b40c48441503103010070f25100000d5880d19285c4151100241ca00540d03151441c101000d128180a2402c50b081c180103007404583d03600e50000c4d0b10034001d080c15469664413500b903801004161403140b20414081d006100da0070400d2a03010303484076440640038000d200e0a80380c42e290b52280004c0028058070303000003a0004200c1542011114044400841c0e4030300d1000b03003c1000300640d10070b07072292080a074000c100e160155829500040d501051208803104051211404282450741100b10310b00018244aa034050541d0035100e40d01103401c40384000c001002c80c81c1e990201c4644e07842200c1d4801c64006c0002100100d5980000f404055818400da549503903d1401034050f400100040301d4000c5902c0000c500040702d00700ba510300c50012941442c0c01d50f42e170010702c208007090f2803d042d03180d03490707810f048640c1004100d10500200740740d01c201c00103072509220010290303002d450301040b4110388000c2c9010036030040c040c450 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 960575404 1250 960574154 960574169
    0x70501050c0412060c0e2709010203010e1906180f0608010b0d02150c010e060103030f020102090d06090203010b0a140f1f050a02070302102a0c0911090a030b041202030a09 75
    0x2520481010f0603640c010140e0051a81f103410003524450010444840b640b0561001c80700303001603101ca010303072400e0340002d001c0c0c4074a51040c007000801140891080c60138050201200050a031f886192110700e04c00304c54050140c4a4a8034007001000280d8480e03800207041e0304000f00304200d0b040c400144000210b260103845004800c1c2c0d43c0f190082d8910454400a070b0f003500800c0583c6451140a0302d4610901c4282c02007136a00d100f070680180107000305c0e01030020041850034803524030b17921003005018240085c0d81640d6282090041501c41c80101005030000501d600310f0031500c0820030080840912455014140342941c06042041400014400d105a03040003a25220306090807032078001c2950000c4d5024a54050110103d60082c4050415681c2850075208000099402072021036a0600040640b00d11103400c100d2074805600c83d4025082e210902031403d0620310001c0d408a00d10b80080d2508096141400704106210380d6210241041d030003c0c41c24181c103450080d1001600d48215074 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 960576654 1250 960575404 960575411
    0xe030301090b15131d090604030c05030c010608010605100905100806131e0f0b0306070f09121101020706020607120c051c050603010c09030c180905030f070501050c041206 75
    0x320955403040709030054804000c3c01511555144030b08540f800c1d1903c2602ca1807004604001c50708074510740c0c0e0b80e1080140300010302c29916183c0d000c0710f03c0c4d810b051041d201e9002c14420440340c40c0f0280036540c0286007110001c1581c82c00e240c1000712005607050043c05003c1c0d80a070400141c6c0b100300c000c000c20107850810100caa582d800105400f4660f08445256040ca081e586041c0f050600d0b00c40c030314950212404005c0c0b104880902400c584141203134035895440301000407445445200300145141e180d19120310301a0352031945003200c6030503c4003114240710f2244c508920396410003000d0010500c51008104a0808183c060542c04051811034001500c3d10b40340340c0518041c100300e0b0074140c2d20b0b013030501112a9902c1e04c40c00409050351024460b508005000710243d12580c10501501d03000441d58441c01d25003501940d24071941074417816480d46581c50b600220760309202030200384002d20b10040c0ea4541c586801403c481c0014200001c8010a01050000c010305c40d018003035040c1d0028000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 960577904 1250 960576654 960576671
    0x315010905041b030305071b030f020d0311070608091b0d080915030c0c06010806071407050106051210060b07030e061c0e071d070203310311030c040e03030109 70
    0x15140c8101a40d0a404840703c24002007016400001450031034007a40301808410100300b0850a4000140720191854980b81c80c0302d0058a072a00d000125207120307081140c12040c0c90666a810100700e6441030010507004020004201824480d94144d803082040080c075080003c0d00140ca995645400a02600d80110b040c20551300c815107612030768078001103941c0e240e00c1c1ca20b10300f009540c4660610800c600550000103600340d000200303d40248031a8941c0170240000244101e060342007910141d502d903403100b0001a5540304c80301040c12100c031a00107010080c0340c205111003074a8507603001c44c13407482c4100110004282e205041a465880488a096941450902c0720900c44416240481e65520340b40c03013803812076000105802201c00d0860002d030f040e00d074441c00e0060030750200c456a001d600200420801c0c4070030f0500300c0c020406081c02003624010343d00c2090080025540040710000c80408a0360090302e0704100424549a040300d041c009600c0031044141c4901061080350b10640e1200c100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 960579154 1250 960577904 960577913
    0x40501210609050c070201110a02061608091225060c021512010f06180e1518090607090e161110090f0308060108010f060503060411070f02030606031501090504 70
    0x1400030b1100020034401c50400c005410b1096015400480c0484e5803844224901c1102003019a01550010a113605080340c072042c00081c0740030f03607000b2128682c0030000510b0560381c0c0c12003500100500401441c09a03241c030f20035440c0324001d40c580c2c0308000e070241d420400142e0000d40fa407040741d8181c03401024440042d040444600030b001c04416040700c004008100d5030003041c1e181040711a030b6550300c44403502460160140c049240900340300e001e01d0000192024114a200301c02c4080302a207205034000c40c500d90103948800507120321183e90001001c4c081b000394019120401340c145900d410061f403c00c80700307807488000c40310f85e4042480078441d641c614104083c440160025540c0c1001d1000c401d0710301d0011603020400f0f8088020800040c0802c1d4954483c000c210b0584201020420324941020010740e101d410052034141e006454214400c2e41c0800f80c0040c120040c8100c080d104403a032180304141c20540010201c601940c0020100000b1215010841c2e045903a2488006400d072903900700f = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 960580404 1250 960579154 960579161
    0xc04150c11090f0601020d0f090918050303070e0907031b12060807080601090c090305070e09072d06110d0c0c031205030f100605030a0b0f090c0a1404050121 69
    0x461540c4602c01c01d04001040350b49403200d80c452003090342580c1d00e0030303014001514200d150014030400034010010600100d4400e501c443c003064001820920f80300d4181d42c42c00d14684c01103420000144070340c1a02c00250906400c1e154201416040602a00717081c50001f01c507041030304084408001c010b5000d080410303940d5110102400c00c00c41640c88884d1140c0042e5954a420b114a226403450000030090851054002c9001d076984407014101c1035142c6007814007144400707003c00f200340c0120500010f08940040300e044012040170451503407000c041d08910750340680340d031202c002c1c03010004010706044404641d9002240e05410010b49000c40c1c3d0920000113038081c1c00040c40f01e04404062858241c10101079845440e1807501c6d511195590003c004292040c0c0c0718030b03804910280003203402d082e120781201d03401c208090005410504110009001d20209132280400d504000031500c4050303a202c69000d034401840002140b44c0313031904000910310340c1d590041000e03008200d980302006881c0c1d0340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 960581654 1250 960580404 960580433
    0x50712230a020d1104060309110d0f1205090303160312050105060f07170d0605101106010e09030c1f0f060f092012180d08060103020a020304030b04050102030403080c04150c 76
    0x8139519201c2d611190003800800b03c2e244151103078440ca1000050b2847c104c5103c01c03603680d005020a01d6a8041d0f07860740d0111100e0300741d03031f41484014421000786460400240c03100e4174105052030100d4103182070185c840074070380341251560780c10400184103c0d00c0360000c80c0c820002c500140c60f9522141d041001c51140c0c901c0802c400044009800d480b005100e4000030f0940d01c0032502c240911800801c2511596065000440782e03400400c010410610041001c507408007401098070f1034425500082800c0c42c0340e900002045590b00799a100c2c220031035205901102680c0d140c1000200c0c00c181909582c020244034900c0c1058582e00d4100c145140d41c0c400030b0552810b480d41544842c909012203040c01d00485242c850fa5500881c00d0510010000f40c0002c80220754a59002a444040044000e03501030416181544400c2200000049035098014821030040300016140d00341481c00410303600b405041c0000804060200b0311001100e072103001c0c61490b060070400b8000e84280781807620480c824 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 960582904 1250 960581654 960581681
    0xc28080102040306021e07110d03030e03071b08010b06090f06040f080a0215072303041505040e010b0430022e110c01110f01050712230a020d 62
    0x400c0c00410040945c004e002000c900c903006007104903041000005d0b034050744201034403000000b04205034030704004458100350782c0a4a00403c01800b4000e805e4a1a4060700c41203800150300d0030000398801c4001c00759005050018000e008540d96803001609900070400c0151180c2d03440300d90081e441e5941011600142040016800850340d580f140c2d80d281c0c851100180c0c0290b64103840c0034001c080321001c440c0c1460b0f200d685d2100c8045200c80b40c0750300103183c0b42c001781d080c842003001240c911540446840e000c0360300d0f50b81e140d4440c213003072168048103410b80c8403119103d41800140a40d0011203c2d01704603456100070003158010001c82c1525890f0010806900449064412a03440450ba8681c60040e000607800c0c003031881c054442280e5070b15514401c520181c01c80940800558443c4c0c0d424648a03400c0e00448601c2005e0561031401c40e4000c1e2074403c08070b0103003507090014288500601c070901d01042da8100c21600a90b810320f0342414000e0000100990029046034041010b60000d040120603 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 960584154 1250 960582904 960582907
    0x5031504090f030e0a180e010f05150a0b0a090b0c070b0a030209030610030b0c0c0c10031b080c18011101090b0604180f032006041209080c28080102 65
    0x40d4180b030100415070010940008104600da404182007090400702103c105000b00350344070075200100c000503e034070401300489541b80d4040303254107425802168094810400070440c078800d980200280c1154990009035001ca0920103054900d0308a5920401c61f011000110b41c0e985100f0b080c14200b840e16003101c0c206910208038a4226030b03050b40507169086041e001c4034580d40783c200b01e00d0070106581c0300083c940c2e80c034540022903000003400980742e00c03d90081180c0340e80c03648000092000b024048180002030342d4040c901b90410b0081104851240e890070312503280c4c14603a84071002407150b5101070801400340650030300d00c0d034420b400e0418448401c0c002000640403034034011205440940b1440d102e00c2c02c1c0440ba110403050707101d580031610307800881505584030b070380e40035600c0c501540340c0d03080c0c0643e0140a44d040715070217101d10780c81648605411180c260603000c010f0121125500100d41c0c03648400e4040105450705003803400c400c02c0400b140d18000d00f1441401280503980e030400e4089500 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 960585404 1250 960584154 960584171
    0x70b0a03020d0605012c01050f1908010e041a100905100f052707050c030d09120503070f0818030a1107080c060304030806030c100f090e100605031504 66
    0x341980504040b015041043c02416500d0004490311405007079020020700c0c09401840040085940c9103034003100605049041102c212401442d80d0050051502caa1640046404000e03901c059028050000c0c0c108509150405450359500c11503508420401c0940c0100400c00030200480c2420040c00c5100701413143c0e141000595a0007082d074880d08240b6403625001190620f8641e86000300c0703442a85c400312411146800c803080c540f4002d40848180502088000380e406000d100030101c818088401090444052030b00504082e00c403960b039002c100090081c00481c550005903110020100d03d4071a403141c8800749503424a910042c003001d032502c0700281103003819403c40c2c1c2019001e8182c1043d518083e5592201d5501c500e185400705911490070000030b0b0009003d01c1900703402c114043e04891b400b401c4400841e5030305100030f4031140071442000910300308540c000000c4000d13041c8001e01e076141c2e0600001d050010300c29405034805114021000a040e5900070344040400710f030080c002d210100d07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 960586654 1250 960585404 960585407
    0xd180807060507020c0112050a021b0a1502070b0f0a0e012c1209011404090f02090405060a0f06030f140112031d0108010603090302210d0e010605060d020309070b0a 72
    0xd01403541240c046007820000b80c8031a00109248404c1141a1140c0442c40590b8003180010f0000030800b01070700b40e09204695104107072600c2012580b48a000030120001e00d820300100362005091204e9800340100400400103d51490f800e400c000f4800c10140203403140110107000c0d101c0d02180352501e6117803030001d140c0e0142041d080c4000e00603810a14540e0b902d44180e10f9254040c1c501c20a448510400842d119035106100807140003074114101402c064507003901400b81c40c64401180580768002c1a0b08070706140520485812010448034805e11030300d00059520501b503c2d100d03075818540c1e00c915540c00140315402c580082400b01550888941c1c45003200c400e03050240c0810b40000e22020103510644003850402030a42c04161500d9105a05e0008120044e22810004078118091854000c809003201c0c0080140f461300d0441c0d860f1039003100046001100c03561024807803d030303041900401c0385490703440880d000c5486030340000d070b565525544a6482e0050b6680102e5550300009040c0c814513 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 960587904 1250 960586654 960586657
    0x201090e06010507330911120712050c0108070c0b010e150904140f2b0c06050907060216060509130e070308090f010807170a06150509040c230d1808 65
    0x44181000040700700d0317031016490484140460041c0b0704800e0514001ca18584178216100f20080003003156626600d9903040a07080c07900d80300c00c90303940d8004540f0268540e0003080080e032040349441c000382c10b072004d40c070b801158500611402c00308910200105050760400c1c007107840c41c0f01e4050b0031171041e42010301d00000b02608500141c5103074092a20100700320b640220701c14100c004518000090100780c500040110000d144450090007070f41c1e42c00500041803402801c0c401d5140a010380321040c6000c0e4061700304210017124411082c6188400c1c09615045002e40b142004190f842c003004c1d0032010b09100041111000c80c0e003052241c03400000c00c002d900c000030314074054181c512485170f8410100550340c848058401c100810100310004012400350200e007a4042c0403e4404a03803160b0396508000e81d00d40740302c03200d00003d4000030f03109141d040500900304150300c145410303004994894880028103003181140440314078009400c01d041ca07042d8000c644085641c601940a0301418544000c46 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 960589154 1250 960587904 960587963
    0x15040f1a04051803030c030c120106020c03070602240a0921030f05190b0415060f0201051b040b0a14121821210a020301061202070201090e06010507 65
    0x2181002d00103922284000c0002003a095108000c60030341c0c0f40c1b00145261500000c082141031903081c00701190803005906218024695034010b03090342c843d1002030604180440d0004402d640c8881e2035140d2400d40c4080030441800a003000440326101c10f500750000e4070b103040010344a501488160f81400211111412401d0681d0701d08100c0c0f40342c0d940b440819104201c41c0202d04518a94186003d000c2035004044c0d0250010000a40c030b0090300c00100c80c0207207940040000030b240ca1481c10402d40c092040307a8200100d080440c1c400e0058640c4981584650302070001083c0d00460780148181c0621540d080890008100c0d0341c86014000e424881c10a0490328040403400d4402e60803420080820b99040d01c0d0f17000683c01e540e424404041710440e5010045c0904541c3e8414880c51600d081c01c44101c1c040c0702075000142e52940340c158001c2c2100c2580801d01039040c4104500e80c010303070f0402030301022502044c481003000c0e036400d80140c0d400e0003041009082c0b20340907140c0340303181011345030400c0c0b0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 960590404 1250 960589154 960589159
    0xc090510030c081501050403020f18070201050603192a031403090f040516140c0f102d05071b05100c1407080c071e060207050d080315040f1a 62
    0x119648004c40041c40d082e21070b001c140824820001400542400720b0804010400500341010070290301806c4003404404490340001030b5592001c2c01000e2506202c0d5110b410310342206540700d49a5a1100000101c0340300c00603c0d00204c48a48102a0040464010085d500701464181e100102c040340c640300e0f444503000b02e100d040c019850041c140f43c54480c10b03000d8046c0e02c10340d001800c4a00410f5820b20003075800d91010340e40c1800340880403e010480001c81d40d030400c01420042c01080b140c201950b003040310300e12500b14a4403122104a071508160080300c840711101150039142c00d442540c02152000c0c80220300d180210b545401e010000a040f1881e01481c4d00c108006011240700301d5480b10006240d07100d09004000f6035004c5091400a080040c020700c0645070b4407951910b071050a00043d560088404031800302c200f00583e01404240020a01a606940b40c05015a25002540b1005000d800d0ba0120300040404a0b281c075403000d01d582254050820484101408036004150458516407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 960591654 1250 960590404 960590417
    0x7140d03140f0f0a050c0408070609170102030c030f061c050a050f120405040b040609090c0e1e040206130b1605060a0b06300c040e071d01030c090510030c 68
    0x4400581030b40c54a8803d4400001c095115282c24200c0006032001510701d185401c0700b400301149078101072082c41c000700800d031a03102101c0d141000c08100484280c1d440700140c1d10600801403408502411681c3c8807031184407680440c1d469000041001c000800c0386c11010021440174800c0240000c1c030400102d00031001c8070720031419090340e070b6610060070700e20541d152401d000800076801c003500089074144000f0404a120768407034601c0811650052419151a2aa09010002d90301400c6800e50081102d140c82d06211441d8041c071210308001410003402403200003489030f2640c1034009250050122020340941d948038002110401c0c0300720000954080c0101c0c40403480002d424800c1c0880810094070715405e012800c154000c0c1000440807440c0d0014007201c4082a19500c03000b1982b00710307511250346440718100708076441c141200030000c000f4001c80e840030104030749555400fa80300e840c01b480e0108004801240403a01d21500780c1c270a54001950619820003140c064000540c1503a4550360306 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 960592904 1250 960591654 960591661
    0x30203191707050304051006081b01090e070c0314070b070c08090325061e14040b0703031a0f0a090213080105100e0606070f06020307031b020f060c040311040207140d0314 75
    0x404236120781c861903500390301100d4403822030220048241c440581c141000108184c1da4044a2410b483c125403410028607844250320405030003101d180c3d000c076548031906042c038801f41e17207544000202510a0003030050b600c58600800c101041242d110752400b40c15240f10002c022003a00c8640b51284110400340322810001c2516886401c2c4206c41060480d00003200b5000803c0641e20420301e00819661a4404c006c045801001d0030010030145100c2d41c1c000907003401c0910480e4149105c107580745c1c0305180c2d0300c96500e003d40e24128144103603040480b005070b0ba0820040a0b214440c0544d10540455003004e08100070415905c1c014001c0b078010054052996842c0f004100113031042d054010078121102c41d184010a0940d0b01a5920120500303000414107660b0007008015042492454016030003032000860201041c011250001000d081050800d0308ad6520050340000282c0601c3c0101d601040c408280994885040318800c0c500d0191500c445d0b41c254020701400742121780c49400407689010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 960594154 1250 960592904 960592933
    0x51b010c020a0b0a09020a030f08040f24030e1e0c13051506030915041e060e101a090901020f031006110c0907030e0c0a090614040903020319170705030405 68
    0x25007101e1744c0c0c0142100362903425170750b80802040705040d0075190180c0500c008a01c0000703100300113024060104006100802104104020b400b001302500b04060400914660012001803500604484400b009003011984e110180c90000d40d040081e0381314100381220010b2105c540c1c40b00c0d00031451466081d600d4284d040c180651403005842107402503009030300740502c07070f403401014a40140c811101484440010041000c070901c0b5040c1c1650200c1d91071070700d50300c01d41c000c10140719a00325440c024890080300b45800c0850b190030164107400707024a4000101541c5080d070444650b24500a00140c036030074041c1d010821441c4500503031002c2501000010000340700011602a407140090803c00d45d60381e10700e001c03006072644041d981c0443c4140442640c4555443c00c0000183c00b0507400001c090b4500030701469031010f801d108500643c0752405240200340e01200b1543c6c40c0e031400000d03000404520b82e007200c4034007090001c1e880d1110800705001100358804015030080c0d000e442101c000c070750740112 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 960595404 1250 960594154 960594161
    0xc080732070e070926150a0f0c0f03090302030c0f030a0906080c0711010c1a1605040e01140a030609052a0307140102011d0606091015051b010c020a0b0a 67
    0x16484049101013400300324004040b48040d08503611500205042e40030001424a800c15102541c0c0319002c00b14200034400800e4400e44211100c003144c02c0c80010b268070720242000401c0b000c0b0350304040d01c96440805040c0200308450341d516120f4101e40d1081044400c0a44030b07080b013140302c000280002c40008409100e074080c9402403014510311464440107540b07984664000c03880580c18452880c80039000706019031403104a620424610704407601d8115040c0c441050440c14150900800f440244003600ca0a420103054503e242d61900400440708005035031010250300041c0036038100540c0104021002c9200206c2c00f074a220002c1614503107140c42141804a18440341d09988140c400f00140450404121219201800000341514081d1030181c215244036100241d95402142030195a00344403032400e500001040056108504140031055880000d00e03019082040115940d085811241c1580b0707100358031440200a00c1d000c40c20040d480700c0e02540d050365018440030006141080070700 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 960596654 1250 960595404 960595411
    0x306150411030709120623160c0b0f28060620030a031505120102040e0105100219020a0f140301062907172109010c0c080732070e 57
    0x100c03451601d0341018105c0d011100d859205440c82034641c800209070385190100f01011400e2500c3c038545900d0700c486d0125803001c4032102c0c4010030000c880f01901140080145903000b41100050021648070360341c502a00049110b01d1003c41c174049d02601c6a111900d030300c440c0c2102c0f640d403108581290074951351254541400c0c95081c05400812001c0c0c92103100754401d150050348040c00350392013500d41c000f054400c00e42031941125a07500040034845840c07224000c07401070a044405607540403445000035104c0d4011a841d81003145400d402c41d04656410f035140e80600207492094980945d20041020956900401d95000307500c0c200022880404144191207542807200c060f1122180d0b0b585407110a81c0a078005a030001d0000103000c00031501c28005095030f20103542c584084407151940c0070b81c841009003c0040b180e02d411a1030710300c0c6800c111401200c50b00003240756242d001c40e041610602c400301d425110740352216110110b1358941d021044a140c40c018044820180c3c582c6481d4111800c180d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 960597904 1250 960596654 960596657
    0x60b13181109010b19031e0603110a1a0d0608060703050f100323010b040e0f16051e0f0901090507022505061605010e06010302040515150306060903061504110307 71
    0x100580350380b0161041d82c03004001211b140000e0301c0c0310074229016080112543c403500c1161218010024000c00e4608500d401d00308032002d00003d450615441100b04102020408503070300807411000400c2d869024131300819020302690020700d04010010001c0100700d6191900c26206004184030b10046d0400500340d03584076079080d00e08038040d0340c0c40001c0381036030503048459900c03801064144d444600500c4081e81c2000300502c02d014203501c1072814802d14241c2d051044502c40b0381040f480d41c44ea1903d4160003000c3d172040c41018508000306010424001816801484410001a40e5001c0e13034007941c1305200e076a00b0f89004034808a0321a1303040611010342c0000b26000181030005162280c0142200e46520118803580f6040380c1e43c0038250380d035008400b4280c0c2c226000400c01e6041a0042701e0344603000e072920030106c40e10100007801c50304458a00415042c00880020140d4a40703070201d07100150014215502032400c40001d0107d802e08140c1c503801503040005482c07040d140c1c4010b4a0054925 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 960599154 1250 960597904 960597907
    0xa0e1e0102120d1d030c0607021f0f0b1c021c02060403060e0307140f10021207080622020c120306090114180916050307080a060b13181109010b 63
    0x110b0903181c10365003103c040301002507910001c0300424442400d14140303803841440038588aa5140001c3d83c1030100c020407980554001000d0203141000c2c9606070081d051424100166091004c841c050062040503842a0010440202e040750210f0094400514a100301d400640d0450442035180164002139402500940140300910000c1c0a0b5000921b840b6428030460303081007025101c00413034420280d0710800d1130b0003044029030004014010410844920242546030102103d2540a004030040181c820080c0c03003008a1040c3d0f449032018051035070306001e0f41015002803200080254058025011603105003520a215100b690f800d4078460040200103e10b240c4c40e0841d43d4034a04a081d0000f6400a40040100494251404100e001d60703030301d0009180720846408000e00019490b004a84280e104c07039401c01c00800c00054002c0f5060303002201240460b081c5000c10940241300c01d0540c951401c0415000440030300f000c00c3d040c024000c19100d102c11039200140300d000c180c2170040d0000c9400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 960600404 1250 960599154 960599173
    0x108120f032a0703030c300b120f060a0b0d020d0510140f0a140c0c070b0403060b0108010f0807120212060f010602010608010b0904030318080a0e1e0102 67
    0x6900507650115030184000044490011240110514071241c5074140d20080b45250925a043c4102115004141412042182e070780c0340d009210700004040e0006501e280c507486005c1e007400e401c4002e4000c80604a410400c103090b4aaa80b2801e080d940ac407640c0c40342d4270000c1c0321800103000f0000c0d10035001d41101c61503405070702805031101c03410303030240d59620404c101c1c0c0728440154480c1c0a817010007407a035800f903070910044016030b4000c00361111000c00d04010000c3c91558039914440d400c12240e001c2e0301d0740d0311500030039a8200011035100b1143d5030030100340002440502c1e00030032903c000990310101d05a80701d9203e40b038024400d00400616078841d04c82070041900020f80c0601032070005018580146804072590310b00101110b00c070341d150054130010003031f09030240100342c06007404d10700038000700c13206101148024800a20180030591100e800d100c00c00c10050050700d5450300038010a64610200a02030b28500408400314000c51031082c40c220b5143d42415180400b040590103040e4901 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 960601654 1250 960600404 960600427
    0x309110904060914010c1d06072a0b04051206091507090504140109051623040314070612090b06240a021c0302040501020a150f0f0b1306081903030b040221010812 71
    0x2b10081c880844d03d25042c61485210030701000b0003d01c048013185681d18286401d11012601c207a8400c031a903400783c424032029440c00301c0c0340101d40d03420741d0448820303a42d518001c80b0b2409150f800316070424a020400482c084031900301074181d4800c0304050045442d1900c615451450f4030320340c0c100099503214825502104050641c1c0000065141a410a40c491300d401d0441510040b020a566220784420800710760802419020108a044c0030000e600007620f030950140d034020007a0b840340031458074510400034280303d03640344841d0108920b07403242241d8101950392080400c030f100980c5001940c03c0c0c09103100e4000c513820365106a001d807a00303460039900e403d0399032207130703110044801d440c0d5a000e2a4041b043c4545489581d01c1c542c00301d007414500c0240032418915102c82284142070a0301801104000200d280e0300074088281c2d022120214202107004160301485107901c40c0c000600c1000c220044000b01240690040c0b0340040c07640d0759480b40b03a0b22081364442d0541c07001d051080b40142c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 960602904 1250 960601654 960601673
    0x509131b051216172e0c03020304020301060b0306030c0f041119020c0618100c02091509060303090f0105030a0221061008090712020d0615150309110904060914010c1d0607 75
    0x1000005c10584510020188040d59001c00399400082c0e03003c002c01056240901401c002050548052840c41c10407401098554240300c00e81c0780180c0406160000c03680701d641c000c082503404500401d40b94007003000310b1461120010204c070b00510070701c442d0000070718140b4100c0d4503038610071100706803204c540c2c8107018640d0110f07003400d003e100c82c3d55088800b40e110306102c2842307010a80085044604400100445058040c1c6031500aa00520411702d40d900c2c4c01e40c1c0b10702800c0c02424080d482e0313a110f8000c0c00191103155209446100c0f90701d140f0843d0100a40780c00d0041404a4101d1a0b194074244d0072100c0107011120307038606501c150010003044031203a080d40800d90024048424209282c1c8a0406403808141c00c00e00132460030008028010700c182440446035401d10b003d004403c001d4a44244100c1e03c000c0c200d21450300c0e5000f140810125a11021084c2e43c070a00454948860401e160f000b4141d0040100104022024481d40b00040e400f401300342000003017402e420172400d40c0b42c80710035 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 960604154 1250 960602904 960602953
    0x30506371d0d050d15030f0201031104030c030c170d0e1210022208491206050307030510050709050a03050c0a0509131b05121617 57
    0x515068020074003900c050007141c03856080c0c0d442d00e0755181c5140420000b250030100700030ba24212000c0040c80019040c240e9045040d809180c04100d1280b08020360840d0b1140da8001007080c01039a01c00001c00a80d4901fa500b22031030014008100490f2038180d644600a07690300360001a01c1000304c142a05d00034010024000c1c0e10030446034403d170103401080c00c030392041c18100d03035a22003aaa00307003205082503424000741c14008050007000070b04403c8003c0302860624142d8540c02d50b51440c49464001091041085007911159000070251541c09811000908403a000039400c0400100300760400044041c200c0fa801002803c201d03441400510081501401002c104026140001101c1d5283e1480364051070045001d4042039010707004200081049030b106a024100388010020404070000c158580c07150014035988440f04120410401d250303a03034014030b5111030410700d5000703451800281200786080e81c403008008c0c26210b60107800300800c0303202059940d50010340611441d20b201904c142a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 960605404 1250 960604154 960604181
    0x3030b0114211504020c01050f0711032b02041e090501060f08060f0904081201061b020f0d08031021110607050109080f0703030b0d050319051303050637 67
    0x4160702c241000130306990001c03580822903074480061140011411800e25081607031130601045d0507881702d84050b181c2c02441007007440402c246a0f5050f040149542c2803030a030008da8021551030f82c54040140d0011504d8011110900880a01086c0310001d0b200352410707107040d82c03104403100030030b00f80440340c4a0700102565000348600000c0b10050300e481c800580103a2007a03900648030303c05541c005080c482c0c141d0010701001408180d40400b02c060414142c4003940543c3c0c600484c100442c00305a9911081100511080c8000104021103000007024070598010b11400c03204140402071080c4902e0b1101405004c5141010788810b0034034052004010152141c000445e01c1019038981c424160042c5c40500c0d041c0d500098028101a0305208a1411041c2283c43d0005d045060300d543e0380c3c070301540c00c441012071440900b0940807401030080c0c40e0304002c1d1400c1c90289648900d0200d4031040251f90441d031021030b920252001048803045074594240594003100340402d02d443d004080d014442040c03c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 960606654 1250 960605404 960605431
    0x2502010605280f080105040308070c0b0c0304081c0e0c06040506040e2205030315030a150e0c0607050f0c1c120c0f0609020f0109080604060e031603030b011421 70
    0x1020000301c80d0010082132a500000740500d860f05020b070641c480140310000304181c0c0601030000651818030550021b8170a110f1030380700d0340c2c3c5242c041c544e4820200e028041d10911000f04411400e035421083c81410b03d01c080e10403200c401030621945008070b0145a0f4051810b10080c0032440084402580c4280d0907500d001f5100021a4080341c0001c4124090740e058100101700031801001e00b1144d00f8180042d401030400f54006c0d110381c0c2d4102e4144d1110340e0341684a0308080410041040b4803400d00d0780c014205075903109503243c0315980c0c40c2e241500c0c000134060001140320a28200d400b00580c950341e50030340a9071000c180e5404000040c42d1840c03c0078171441c1000d240106255600c142d90040c421040068002e585004010480080307035003841c1000f0120200f8407003840003146640d045607101d200824402000ea90260441c051503041d01c405900758059403090550680110440c03c2080e02c40c681d02004ea040003803007070710815040d180c07045603140c0080080030140c40086d83c0984d00c0200507 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 960607904 1250 960606654 960606659
    0x150105070803100306061401020c040e070504140109140106120207020a091a18060d030309020a24080901181b180c020705062d0d05250201060528 64
    0x4a000c2d08180d80034919003c5000091003005840d104043c007410020f000e40c0f044003c03000000399a040e0072601c060003251108100d00202100300400d501400c40140184800346a13060800c103400c009109000801d4241030620781c104601c049054141e6200c1c3c0e503080740d488003010040c000713540601030880c5c20034160040000e2482640c440c02691024441e00040903003900e20401004501003018040a008a00c007448104c0e41c0e03401a40c0050390381802e010911024a00000b00c8140d5580d00c40e580c04030f40381c4844c0c00703183c0e82c40720b450b6010714040e00c80143c0b54440d0146942203e1400d10281000c0411040714404100c02d07074915002d00a0a403d85140c0c00d03151642c98501c51002544044c1c05174592040004064050000e50040c0c40e00340c2d641414410b40007580038040c0e004840d0301034501407a40000c81b202610070200c0f121075046000501450422805250ba0044000803c100c1c40340d001c000600040d1041c05890122132307004110204c3d90060300700c07217031800003038070b0200c1009092101c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 960609154 1250 960607904 960607913
    0x1022a01211b030e0105280b0d030e090a0912210e280803061c1205030406050c070b01090507020106120602090a0b16031b0803091605041415010507 65
    0x4000718251509104540b001030050090142c4011846035004c0e6410241009210340700b840502d070040c1c003500700d200100c10a212407071005000409107150401e914202020900d40c1002806659400948038015140d9070064124100d0b00c620700000e00b030926800e111005184500300d00c22922051400c500d00a41103600c0100c21a4049008410144c00c00f04801c01c4d20b05500003660070000c0403e001138103008040d40c41c504284402481e4030b215170031400410002c40c0e6242c17540c0c034009034040f0f0446c2d001103005501034aa608100c4003203410340c0c2080d001627544066041959840740d880955000d550f420078101d240505030080c40107003159a00c901c00610325070b14610303a0501902903000182e03a10b420b41c090002c10042d6411801200d242040200040200040c1443d107541d010301d0042504c3c3c844100300c01d5064801003014202020200a200035804042a43e500d030011012400c0402c1e44cad01e20522059a03007241502c000700301c104000a0340b1000c002180724000c030052400f075140c440709988 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 960610404 1250 960609154 960609161
    0x624040b13121202071d040609030323060906040902010804020d11060708070b0702010612060f021308100b0108090c091e010611010501120803060d0c03050d020c01022a0121 76
    0x10309488400b51030314030043d040c0c0c05000010103804070380c6021603180e04005800310442c1c0054002000256a03000c5441894465401003100c1820004640403040e80305050400340541a9140c61150040c1c03070101d0450b150501c00d0a10159060711ba803641c0c0d45d03c1c0d80030412506440320703054855502c800100003480e0740d600c004101e0203104038515503d95510f03050011034404001c0c42c0c1c01c15a85040010301109036030181c503190700b560200c004216030f0510b45048011340202c150341042d040c4100c0c40860b490602040500d101700c031301a0100072140a9100444010030300307442d00e0016803c081c42c007001c2c6092020300f496201800800c154282855504d400401c80f20990040e40001d621b02038903065420b081c01207500400c0c10204400100760f40d5151130620740310103400079108007000c05a020402262340907140c02590040262220307034544090283d11a00144001030040c004c041c400d46030b880180e0035801d084a003522506084000c000d00654102114680104042e00100311105041c00f8030300 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 960611510 1106 960610404 960610439
    0x5032a0601061418030607050406030e06270319020703020a14060a03020d29040605090f072003040f17010507080f0709030611030624040b13 62
    0x94421441c000e044d2803050305030003144200642c054200002e4401c80e10ba94a0510280d01005032158580c50121000c801403c1c4200004403039103001003041d00211110002c69141098901c1e00b422101911300008005078044a018405c50801909010051081e010740720b894003c01d00004d0024099800c00104056000c551a10b46022a4001d103800c0081542226600703090070701240c003200b10060800f40942c0c18a040056242420010240b00384100302c000c90443c3c8803000b088030030ba00745007949440304d80c1000381502840e00604c000c100a01850b6002c11040c2c0c5020350f802c030010110076070590164500070401032801e4100c001158061990101020030355603141c1e01359260f01544d000503003003034a05200c180d1941b0007000198040c2c40210b641080c80d80041a0104159040d07200112000c0c4081c0000c200040350003001c2c1c00e003e607944031005030154840c003c0384800b90190 = true := by decide +kernel

theorem cover : BRFrame.Cov 960431654 960611510 := by
  have h0 := BRFrame.cov_init 960431654
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960431654 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 960431654 ≤ n) (h2 : n < 960611510) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
