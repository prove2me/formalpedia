-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0771
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:41:13.441679+00:00
-- url     : https://prove2.me/submissions/ee8247ca-0ba4-4574-be38-4be176672a96

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 138489208 ≤ n < 138669064 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 138490458 1250 138489208 138489223
    0x90c030a0b0303031f0f0b0d110d180213020a0503070c050a0b0c030f01090204050f0409020a050301142409150301060521010f020304080f0a02030f0f0d0f0b010917 72
    0x60201d1341d881c5400000c90f40c05510003500703d4240882e5080010b8000001c2c07a080003526003000020b4a003020080441006205000807800d1281e03090100c101040050b11904559195503404080400100c1c810880852340c50342404140320310600c424502c0310b03400f0742070325032241740e0f410580c103410303a5401c0c42450a8200f140c024a8240300c582045420103041002c0c60082010030021507069880e070f0150410b0340607074018140c00800c03081c0b039816585020b401c1001d01d00e001501c1c45003030b13030384910220f42518685c801183c4107007080e8042c0300754850141000b004040300c5822030302d0001c10403030001c1c0024102401c2043da034901041d803900580d03400e6202a0050034024540050032520b600792102c50b034a5038682004551910030200452411030080340d10569102c00c81c2807038200e580b1940b0700581c12540d42d00003107100500070841c00040c28402007403100d036001390315038a0b045540a00d00548a45200c4000d105017800d07850311090760070482c60707015540109280749092902121503480c0601 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 138491708 1250 138490458 138490481
    0x21130501050a14100e191508010c0f1103030103020427030f1701031509080c07080106030b0a021206060903010e120910020303040309140d02030d08100603060302090c030a 75
    0x19000500c4a001c04680c0f1a01d034580c03800010084940c0d5015006100c40181d00c02d201800c05140c00007800c00401c41c201c2e18010680703030000201c2c500c204070b10000301141034204080a81d0744030040d82100ea00f0503100780d6404027500c0d09800d040d50400c0c02c0360b101c0c0010b21009005548505640300c07a40d40c420481004220010a03602001040741801804140545901c201081c10a666800c1c2c2018414001e4180c80c2c20410001e103510500c6102c10040800341030a45510034103220042c1900c0081c06041d00408039140041106821401e2100c0f92200240000b50440d00c1041446131488a0103e5142e01c8103044450f10740302c07481c6d8400300e80509035051010906019402f440b001c4c0b00f0340c1d40003800c840c9200791a0000000400c841c1640d4900c0251406170119181c10010020000d038090700d44031404001d086494101415400310346000000039200001c2a52035040150101090381100f004000070f01d000d01c0910b285802203002c3e02e0b00030703106280c1303c2e0300000001e0b030044040d0800c000b03040 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 138492958 1250 138491708 138491711
    0x909030e12010603170c0712110a06020c0406140f100207080d11010c09050310020307021606050d050903031506030901180b0106030e060f07030903020a020604060504051521130501 79
    0x103500324000b4001c2a0b40c0c0400c68000c03a41c4c11144090008410549000345200402490441e007414001c1244c1b0b4842c2030110b8543c031017281a1185610354801c0080105a141c0080010002800c100303c1500d51940024980c60b41d003004200c0c442d5140702d0785100d600b00039280386020100d4600b040307003410324a401c194600c0c410300d2041c4072040d5100c135200000c528a1002005001003d0000b26503d196500c41d241d807590006000580460b095401560000e04a0040700c000040c9020415100145603020002244003c20110000ca40500620f5404558000034500d980340c04480881c0e4810705180303903401004040009542440c1c01d6020611803110590245041406484c00d03004100c0b09004040000f82003000004280200190490181d804091282410340e82c01d0300403401003020070004d0701148948482c5ea000750311079000800c05000c280ea2601d41d00ea00b00003d0081d041c1400e400079030b90030070400080c0080340039090030703600f40d4070200d4110180f91204503441485000c804c001610380d5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 138494208 1250 138492958 138492979
    0x30801030311011409030d0b06030903091314150102010f11040603110d060f0f080a17070201020c1201061a03010b030705130b0d05041211070302090703020708030f06010e030a0503040909030e 84
    0x5200000240c07c203181d501100380080d040d40d2060004a020a480c294441d50080c0020100e0349459940c5001c03540440b680042d40c0e003070102c084403510f94250742107600c0c1c9104171812146541e080c0031391010711001c400140126041c4130358141d135610030f0b44103c008140e03840d000c129421500c04200c2d0300940c0303020b90501031203480d0540c1c0baa1400340e40c8034011000914000008180300c01140100d46190071a951041c03104454200030b4440d8003040b01241140550b40b110800c5a5034105484000001140009115420000c08290441a200145541580031b0004110203400c6408886d8488864a8403e0f12a00c0400003500030301e090740c118034600d103004078007000420810780c031661085000340605036016801400035120240c44801d451400d400c0344606101500f000700440303820540902d0014070f000c1160300d90f0a0b043d002a51454001081d42c001d1003030341c0d80d001030b150940d80300450281502019654903581d9a00c914400c0450320fa49480074102807500808106150400140003030f03149 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 138495458 1250 138494208 138494221
    0x70b15030f01140a1d03040519150c150204081b2103030f010f150806300705031501120302071805060a14010903020d020f06040b040608130308010303110114 69
    0x5800b02182c65502491900c94050440c90f58074010345c0f90b205800e8080c51526042c1024083c0b03455044510285c0c06600450000380c50445072001703903c0c5035903a600e142c00a803242c0b4092041602c01c0400c2c04500d401404188507005011030605038001c07401d21002c050344600008940780c50f80190b1035811349401d00004022200b0302000941c0302c1d01b140e800741100c4c0d0323803103140c0c460700c00d40b2178005c0c0d407003042078154484400d90240c1240c54000c80010a046040b01c0180301c81c911440907a107640030303138281d08001460105030030001c0c2d00161000720041c00c01980e111041c041140414400c1100455280d0041c5c0c00b0715000340480d2020305a0910000b413900101e0070001c000e0b08050720601c1c0103540041c0001416540c03030f00c2812000c90165070b659503043c9150200302003015031300d8003070340d202c0e180c2650380106903220401480204860401c1d107407554584ac601403d001d4005004400a1050f000d00c000060740c8001d5040c150313507041c10900c5102d9104a00d070703801400c1840b0392000d10b07601d22007071020 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 138496708 1250 138495458 138495491
    0xc15090109021c05161202040507140d0903030b09060922081305011706130f020c0a12080f04020d020103051909060b0a050a0e01090b150304060f0e03070b15030f01 72
    0x100301c4d0040b011120815210030307400380d81e1003003841499403108a030b400300d5005203815080241c01c043c283c0307020790007030000360401d12040d80141d40110210b07555020300300415406000346100b4010440701c0b01c00902e81400401d800d03210080c1404d43d0560700c51103010080b140c0095944820303400c0b072102902d44000c0010306075940e0080c020a40850866080010480e14440b001d0b4828030300030341640d02143d407890041c4003900220000e2a0019001d11003081030300c4003040004903090181004120011001c00e02602c4000064250410910980204070142c0c03030300101d07000c48650a1030005015958400c0002c1c849203d0096444000c5c24424610180901c6400415400e82c0c01c6556400d441d50350010051200800d1080840240d404801001408083c1d03105d4111a00d003c2c012030700d05d4901c1140b04c5410703841120219041e654607505c20105850900c142c00202c01400c00540c03901150341c44910700300e10300910452062031038003190f00c2191818481c0010101c071202c02800048500740903c003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 138497958 1250 138496708 138496759
    0x40b030c1b0a020d02120a02120d030516211107060903110d0e090405030f030405060114060c031804020d0906090b06060702090106050d150b0703090602030c1509010902 74
    0x94081040808801c0095004558280c1c0c10b9401444540400b40660a002c0310303d6041e11044144d0142414060240c1c41e44e100c6500c01a028002501c885002444e000d400c540010b4420382002d040c41104c01005604401c00344540360301c041c6802015412552024007400e485503c0700710340c90700400e0b0300081110542122984e61b12a480340341c8001d0401d8100e640c0d40c560110144000b5410009160132030604110072a00207000c0d400b43d80c0380c094013942402e4686e000303940848169020390010403403030340200704104415108485c280d1074001444403241e9207010f01d49100c00c1410b074503140d541490342c5076812200071038010101808407101e203052075401080034002c1514071405802c0024000c0c6850301c02c40d0045a030080100c14141d0904104880a40090803401c00d10742e59108404101462040580002e160510445545458624000b00080720a500900a65000344039150b40b8040200d1180c480208c41400080d4a5541d000f0442c0540401c0c10080c1d0041004440c170315030b8012007220701 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 138499208 1250 138497958 138497977
    0xf0703050a020601091509050919081e04030818010216140103050c040b03041712040b01060f0f02070623070303060501081308040e0606070605190f020c0304031403040b030c 76
    0x460f003e03070760b40e500c01c030075203a141054100c00e030f0070038105001001440e8085900039120404446c1070305903948000141c29035030002619544004074143c200305201d148580348003804005030600301413039952082694000d81414111070045154403d5040e4420840c00014404001554410b01d6803405001703d40480e202c150350010b403c0000043d00c00c0407407003c94080318000800703107156079640d40707030035891004550100070708039810480d5540440d074152109010f240a0114001c995240c50340c01380801c0d913140401c4061040038070301810b00d1600410044225010703400c110f512030b080c84a140c803034013020240c030808000c404030b045800e15505a000405986081c2c880c1c007030b1500c07130001c486140c0106160080050074100410303c000c1041140a50b000b540182c0264202002c0303540c1c03001a02da08484810f20001082c071804000100c1d8014100140c00c2d03607030114601603034048015282c0c4182d00003e400030903584e400415069007041110000c1034212841c5441b401c01e03500380301480d031040450 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 138500458 1250 138499208 138499213
    0x30b0103020712030e0a060504050d0e030c030c09060604090204140918060103060207031403041a070309021516170d110a021f02040503010e101a0d080304080f0703050a02 75
    0x50006501034800c444032150050002a0100e8566904801902c4200000051400340505030f02c00500c0314092076009511460141191802e9050000d211701c010540705031199106108540480c0c4010902048008d400d81e8400c02d25526100494214406c82e400440f0b030a00c001800180301d0000c5002c5844070f4003c5402c41195212001da07902480c40681103800140c0100c80100002040c603401801c3e02440b9081140741403440903040c08542c1c100710740c2542c2d050915a02c0841e01c02d50080516031261083c2801c0081180720f4000c640d4010784042a08000da900044014401d00011440c40760703180c0c001181c0144d21800c4192140d90740140c6284100b0300e00707040c98000090b0410b4107803240f654a550081c00d0003403154800149489511003480c01255007008081610b8600b0b002d031680c00c02e0307a9402049000d821140960440380d40300c0601e4903026800c003400c2c0f0107503280010203c0c0c41e030f00444d07625141d0312103081481503131041030161020742030009035410825800c5070190603002d4440d0203 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 138501708 1250 138500458 138500471
    0xe0312090915090a020d060b0714120301080706200d02150709060e100c1b140306010305030f0a050d0501030f060c020f100e03040816230d11010c1b0603 67
    0x6240c02c0c0051410301c90b6484261034000540b208081d90292103001e180400210b409556002030300b009910014080e24842e4a4440d00b01841104000b0703042c00192000b4130515661512804588516407070003940f041011411104502c182d51200713459000c143c0c1b0302500c2616441c400060750b502510107800e01100c02c50000610410f0150f01e5440c101c4183d0345801c031742000440308101040318130708405421b01135074040e6030740403c00c012880d52480340a002126025400c082c190710004940b03100d514460745c00000103100003a0040150340140040f0180b081e140e11410b00242c4443c010800751040741c6280900001c1480360b0103a4500c910342c05048100041d00340c0a000302d80310f4104a8020001e40d1000b621508180000d900028030408045c098908041d140c0e204070342045a079058460b599403c058085c0609000340344200401619049000a148840760216440c4203602002803c040c40c0007401da00390340d00800418010315802181420b07194491055407959010314020200000d25054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 138502958 1250 138501708 138501721
    0x601020f160501110a171804110f0a3c021b09090304091a0301140106080f1509040b07030c02010605030604060c02010608060405010606020c040623010e03120909 71
    0x794000d0316244112914504a092000659061a005103025100d1007844031100102c1c05284504255040b1410465030b00d0406007136601088016400b618421444c00c40c0341149641410212070740c0c020040c000c0c0e91500c0c0390301d0090303460090002303a07841018a0401541c0114483c140210426480c2d01c05510081e100b40c1c3e01240d50340b07038441039109500c00700d40380e0390258542001110f50240848084919054403104070105517850a9050111411550360303c00e03c601d02805042503517104c02c1c2042ca105d61400e10000d041c1032015145c885c0320208130b404120042d0581419a811080190098405081c036242488001104031602c8000070300d0f180306034440b00d106015007805c54000900a24071516151140c00c001d000d1060101d042d50360360b000001d40c04d001400000d10603805032000280480c40c1280c06400c02c600c041c079039449540382420500803064003185043d018184000000241e406240068601002ea0030801354944144603400405541d000003e0101d14800e40702075459031a1003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 138504208 1250 138502958 138502963
    0x3040e01151718010e010c031a01022b0203090405041b0503070503030d0b030312040503040314010203010513091a1008121e0304030c0b040b04050d0f0f030c03060e0109050601020f 79
    0x1101100b00e40e000b91001c01c1180586800d00104406518000550811800d40036400c40304420000d00200e034441082400b91071040080e20f40910080c005000f054500052100b941060419481c46d00c02c0c814061f5a1501d200f002503454040025104000c075050a0406014503200d83c583c100c000200040e001c5100e0402103090011614040c00440c01d22590030106c1c2c0140010b200c2280d018070007489040c01a186c01c801103400303036008030007856980c0d0441c2000b40c203200202c1c07006051a030040004010303039100c2a030405e0351101d2083c00050721803818540070000c1c100601c1146035282407081480461488030310824216084142190074081d00b030a02d8800900850355000252880030072103084001c15200107584c030500c00d01e03100e10001c00c5a642d00500c0701041d14217a03211075141080004100701001000c03055103080c00c04032031070b1411020082c13402480e0320786001090b03241d420142e00180260402c401800d04111811084d40c0c4948100005000494140d401071058494088820401 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 138505458 1250 138504208 138504227
    0x1103161701171c020c0607080d0609051e010f06050c1c08013f02120a050307060c020a02030705100302040e01140a270c09030b0f060a0b0a020a060b060c03040e0115 72
    0xc98003e01714138070180d02003003519003001d42d0940300080104482106501d0520418015103480800080d0701e09146d95224100003461022030043d020300001032000500c1d241140b42107814600d001c40d541e180540c034039400e0030301100ca03041e240340140c8030440c640ea03084202d8905071081c10344800d0040c00c8403100c0071541d504400c04511603440007000080c20000302440350920a002a0a035044800722032078040c5441d1041000b9229500041403200c1003040e10f004100c001035052008220b00070241e00001d8031102c651250620a800604103001400e00a4060301c000301a0030345440c4142d0384d5040e5448010b00c4001307049200c4c5625600c0071800c1c07a4569520800c0480643d0b03210510021440003100070f0055006507410321866100001c0081c1c0980f2a40e80b2400e0841c0d810191420480f0900107c04107640054503020002c0c45031809041e070004030119600d4010724041401d90301000420581e105048003040c15020014010440c44d081c0d0300118101c50220760140314055040c1c40484107800d4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 138506708 1250 138505458 138505513
    0x60721020606030a170f09090702071a030717090f07060207030b0c04060c0f150c12050a2714072706030f02010c11060309070303030e01110316170117 66
    0x1c100c54044c5d0000c0390500036200074880018414038100030390b00000c40001e001c0381d821006900040041c00f0704c0c0500051074502c140d40d81e0449085042c00c0300b000c0c0c900c02c0c580d0300040502c520000015440c1e0001c02405203a403040d0fa0969401c41c0d00c3d164020344038803850105548104a03400842c0c8011240703011038040312803954542011a201d5514840d414030b581000340c3d00b9102d40350000c1990781c2c49100300c2e8184500c644a40340c604c1c0c01c5103030300c4040c0c400c020182c4000e00c0c80c20141a801c0465441c1c2d101604402200a00102c06e4603d000350618100c8418101680314000300481e140803c1500d020110440c0d501e4040700040001104050780c02502008140010410014006500030100c1c480f10920603440121304a100e0340c08100e55420855035250264440c2c8070400034507030544550001440c0450081c484020340c0c40400700684005000d0b85101c2c800b1941c42d0b032400c1e00c0f0b030018803038484141c65019020b580d070b03d9140d0301c00303880d000c202201400f404102c1d5a4034689a030b000e0b0324904 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 138507958 1250 138506708 138506723
    0x213060e0a1d0907081207120e0109171c03050709080d0f0c060e1204050f0301140609060a030f0501090201030515030607050901050405060d15051914060721020606030a 74
    0xb21181030469140c1000c2c245560910039800701254501c428080c01101e2090008519103442281c1054601c511140080b10f051181c0581404a581d901c9441c503402d450b00d00c205c21990501c00903089240517a490002c00103648002c1440ba081640368200501410301e955030b8031210342d00d6003210b944410079100c000e0041444990382c00304007401901611101806894001551452109000e0070003500c2c4400e1002c0031800101802949014602441728010075802044111200c80510100a101030180c51240704c017000010308599524240001540e03214000918885203441e02c80d02038800e8403c101e0200c1d040c000000c0c1c551120f10f500c1882d40000900801c0d254483d903409460f41d50250351040c0c10444100000314098440c00000c0031005103042c000102405410101c107800403141e00410711072026041d0240b4400c135691600e03c1650b1410041100e01240180041c0c114810100700030310101003c0300d0120031440381c0a510591003070640035610305542e80301c10544c5a800001006003c03c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 138509208 1250 138507958 138507989
    0x120406110a0518040603200306090d0c020f030c19150e0d0b0601020106050a030b01090c0509030312060d170c07090209031009020604120b0a0b030109020a09050a0902040213060e0a 79
    0x20302d0441603905006102030000502d40e07840340c40345451081d541404c50a800b200f80551600ca0908028050f400b04140b8060802048860402420ce840342200a8802c0121140018140c2e500344070381001254010210320303040014283e103000890561140300c0c50740140d184030307030038860099000007214040207083d120780ca0100c0d5100314040d0b501504584c110341d0303a40e00c00b2860b0780325519081e01035400350003804061762505043e01c081c0c0d00e94605040070030105000391800c94400205861003400400c5080009650300350215500c214520006070600d145240207040c0d1011110007003481340d0140d015201540d03221a040001c0c1c2c4104001e2030b42592100d00300c42003240440c0c0c01008003510050626241c10f80c0c2d042c00c80300b6904403040503103c1400181c28019442e01c01e1142c81c0301100181c00070701c540e04d51500041c420410904c5038110031500c0c4c000107050305659a0041042a80c018400c5483d6050020003941410316030007000e0200704503c4001649140034480b840443e5104440c91200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 138510458 1250 138509208 138509227
    0x504030204051305010204061805030123040312020706090b090c0a050d030519030c0801120206030c0a02030c0f01020415090b030a180b01080a1101030e0706080c040b120406110a05 79
    0x5102c01031040b01c03850b102540700000201d00b800204018285a52100c0f582c0302003044c10309180140758400c901c21780c9800c842d40801c400d62031204100c89140740d40c2c842c440d0b980b400c3c01d0301e640c066007440c030200e588001031440810210707074002c0300020700552190315a90b440c80c007910b60700c0c407402400030380c0001143c10030020f0b45400340710120800d20900e0301d43d00b0081c0860411b07031008940ca00700d101281e00e4aa03400c00d2581c0c083d500d54018a60714500042e02c141d5500420031030310010300844d0401c2c3c0300043c1c1090143c020000c03500c0403c0c80380c048815181c11070300340c28000d4205001b2050b2030f0342d0900c6002c0140307100744101025180004600351542d200d100700b44004100044019020030b04c02100070011030000301c640d50003040c1c400043e0040c0d15481c80c0031410201031042007414549000c00584020100040c43d00940355139040c8003809859a0400c0c0b6014022a8840c2014a03000600c120f82a440140054025442a04140040c0c0c25215184c0107d0040c0c01c500000610144007441e0f1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 138511708 1250 138510458 138510461
    0x902030907090c0e180a1503110d0314280c08041206140a05070207090504050303040f030504080102180405010f05060a03020315151b0102040f030b09070f0f06020d020d0504030204 79
    0x41c4449075084c1820542000e07008602500111981d6101c20703c241c03c10810031720707400d0181180c0e140401d07043c00110340c150360b01c6411000c0104415405100c5000100040501912076007451025000e0141d0b15042654900305000300341e0314654031120004500d0503540c0d40a846c0707808645500070300712400c0608020400c42c0324002814248c80e40d503150311020401c0c00598040e83c0c020040007001080b2881c142a01030329100466021410441c0f602c802c00c80854000301c15280c0080e03000101c0302e8075860504085496004541050f80203500c002140074100180600c00780341c0b0941610140f1090380d840c040207004203054426035170030950070409134613654429401107502090705015070b0081122800460b41203070322210411408440001d5819802500d50410100341000b01c00035881c15080c407040304031410892200038650b0422001040c6820410700c0000098802071001c41c04007a640c0205809060303a92107104054010001040702e414800326850592904c1c0d91101860146168240030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 138512958 1250 138511708 138511721
    0x60605090d050102040b03070203040305010b0105070b0408090d0b070f021c09150219030507060b0f10030b0d0501020c2107051b040905010c0305071209021507021206130c090203090709 81
    0x2610742d5805c100100b04d45100601840c003d112550055031542c0c11440d20341e0031182d0201c841d81c107005050040200007150183d40740d60043d441041c503a01e6501e0fa45c003040c0c42d1a50703001c00034064500e0408124066900060010b0038000075401c58103000f501190004062514030800c0340051000c2401340000301c0d8a101b20b065044152048501c0044007002c18500003800c188100d000071000103c01041c416070707018070f50302c02e44d048a441d041584a980042e5400311030342e0f10780042c0342e201d4031220320342d07525480016502d5403c180299920ba600d0080242c440880c0413500494148400c0403055901c0c4407400d036039000b54860b00419280d80b000c0f4101d00018412003440768003645620008000603001e0251502000a03600c01041904100d0b1000d000514a00440e01d40e883c90510400b0140c0d503050710703040c8450011104142e44001900208a21140c10903c40c1c0071482020103000200c44d40c0d2000803c414020b600e482c48640c0c5800305001a0312080e2a80c105680c400d441c24440511076a1110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 138514208 1250 138512958 138512963
    0xd030e030a050f0105040b010b211b0d0b03150c0403110604090e010b09070e030c0d08210411040c0e0f130e0705030705060a0207030314071a0910060605090d 69
    0x240c221028580d20b41d450203c124042c01c055075161428001044541c062440c003400b04081403e0500000000d40c541480c81c4c0c81c07402038150441c1001c02c0c01001d000e01c00103000603815000968a95501c41c1400107813112512039070003442600c80003001300f10507103c030751b00034040d82d0402d902d02461612050390f07a40a8000da140d1041040000045a904501c15040c40b40200000458102244810021900c030020211401d0214440794040c0c01e6401141400110340229521028400d8904020b049401100743c40405103404001c460100f0343c01c444220701c900e22440722106510403038801c0c002903c00510b0301c2000300f00e8450350001715241c0118100c2c0b03094400380608a106ca216400b0070309a54460642c0d02182d00860010302c00c9050511052020301070507502d092911480020003581d4080c2c03803202034200016041100381342200b007400c50ba41540c0209203107041090300361580321101c038180c071070f0902c5120300250740800300114040c440444e0600c0d1100d0342000036041c2403041c1740c250340743d04 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 138515458 1250 138514208 138514213
    0x504080d0b010e0402070f1103300705070609030606091406040e12031006080a020a0203031303020c09070503070809062401050712020606100e09070507020d06060605190e0d030e03 79
    0x9091144c07101d102811a1038000d51000300c0d20111424003c07000300365440c48078000d400a10110110600d108a030110342012080d0300300000945044d48019400346010081490242180004020b90710602e50401d03640184020050075540c1c450540448030701c01005040d034801d40000820901d000d40c855880b2070920381c281c0700130aa03412441410360b41f04603220803141044c00400d0108562062505500204046045180c07001c1041c01950303c1c00300030030f101d0b108104c0c2102c180405100340000e5900c2c1c00d0103424140b00707040070400503040c1e41040701c0e098001241080000e412900004095000b1103400c18000611000020740000d03205085040605025040100700e00140b41c2c60100d440305003c80c0e02038041c46c1081d004114141c0c00c00d05480b810080c0c8042e1510041d42d501d280c0075041081c0c0d092240e036400b103920100d01c40e4a41d95501070704a40c54140005a880d4204000303000403481c0030880b00d159044004140c4183c100e106901c1c1c0c00590660000001900520851481250003800c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 138516708 1250 138515458 138515477
    0x203060d020901030c180b0306011205150a020316051306050d24050f030d090e1b0a031a010c0b01140406030c06120c08070c030c17040305031206040504080d0b01 71
    0x7140314010282d200711030061704030004000c0001100c4095425100150040c851107075200c0c000b035a500018003a0000c8000150b8484c0100481044106944482e12900340b1440c0307840045400290401c88076507480040b006000b040323040c441c03400c0781c000d0082c0d403a540340b0b000d04080007210341e504902c4210440f07640e10210074140700c000d554041c2e030700083d00c0b031445070f0b00c0c0c10700040c44100b50100110703600030340c0058942401c442e0407004800c1945d450240050301540d4040120f2a101c0300c00c04482d010f1040000c000c41e9156240d00640007049a50802c010501c0c0a800119507030031080700c01501c1e080000300140302803041083c00b07802c3c41e40000c001007121601c9455088600c520741d0b1000340403500850803c130b4049864060800d0407912800c00034201d10b170030b0300051300d0350300c00c00f10003810040c0c4000c90804001034129101310703a0320610787c0d00380c45644070300d08a540d0794840c0e03010b0340801c6064000241c0300d00d0540545445164003a00032810b00e44143d0101d00503040308080107040c03000500303 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 138517958 1250 138516708 138516713
    0xc07020916020c1201020d0f020301050a090e03090603010608090601050909030a08040c1d0103140601031e030201061a09030f0c01020705130b100815030a03050f1b0d030c020d0504180203060d 84
    0x3000b0744141c3c1e01c80011f9030740103010380d003000b11480030230710b00108c03030052004125982c0c403069a442224030000000c60402a039600f55402c520500010584c0040d000c800800e1075513000b034403507110740e654100b115a45d0340c03030704200321500b10203c47c91a11f5034010030040740c00702c3c40391308a42d80003442008820308036a129070344280b8103a01000740c021002021001041444520310380718121200a90280c40c983d4119103030117485c0d1ba48040e200d02031060f215190000c061003540312038024243d030050b03560b43c03007041c03080d110312a4844480c1c1ba109224441c0740c507104c50008a60f503c0e44141c160000c3c41034501d02000c1c882006204981000c1c0305035100d20514464440920140380d20003103a17241b1501e0311f404649000810680c001d001c1c066030092050800080c5c0180448030a2907401c1d000640303c2c80e0640e6803192410b00160500c1c9a402491000e800240c0c0581118a442e0107076000d444503200b0070308003180e00c1e0049110312084110148a0601075071130a9000350381003040a4002d060201c0e5a4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 138519208 1250 138517958 138517969
    0xf010510090503070e09060106030c080a050c07151d0726030c01060b0a0f0305040209040b1302030a0501020703110d020a0f08090415060305090a0c03110d0506070210050c07020916020c 81
    0x40e17000c40a0350282c0800c1181c00482070007007a01400c0c0a00302008829500c6400602c0110000d0910402c180e8035408070703400748a90001d40d90034036840803030f42120100c1e2017484000341c010100b04400007210144002e034140004903c0c1425162a0440400011260140e040d81484141d0001880d03002c00c0081000c000170170700806002e01281c3c03101e255918200d5030020301c000b00c002450003c061078441030000694400c6103c1390840e4110048445945409000705800342d40000020360500c110800c44013040410740207000283d001c1d4441c0344202000084031034550110128020041e0892505000001c0c80d1140c403181d41402844070500b40020780001c03070101d03445200041484110b210701008045c0d41070080a521464000140c1111003481c0d6990001400307a000040a00910b95150703c42038a420442e10242d982007070885144c0d04025101030b48500b07007062112029810600001d908600300341c200c2d010300342e01034100602075071a44c00400c1041717003101d8403034114000c180d28501e1540d2075 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 138520458 1250 138519208 138519223
    0x40828020a0b01090207052d0a03081f030f080705030403022106010803090a030204020c010f020f041d190b010e0a1e0e040206160c090501030b0a0c080f010510090503 73
    0x6036001040c4003021420034603482c0e82c05901c0b1001a600403c900800640081800480d84a0811407039288120500d0940c619603040c000ca2110f40c41500d807000b00340340d4071104070343c000d05100010411060b1141441c0c00d0140d1903000241c01000a915008000b0707005c0002000348034010020781c0e0030562261300207807004880003c1289110b81402c1e50803280102444124010b00000700114601a0302c0c50100786909210b1001030311503940840c001c1d5400000303420424804418802c115940c4041c070355030407080d820074040d80c2060103d030030642420b42030380d8440038011500107401c1185101d01d003007240049e10308003103035904004503a010240c8a841354a0f00e131001d000001c044800742c05130280d540400c4170701d65121044402c06d41c1d05210258480c1412074025945d1103180c01e149209500b48040d0a00e00b60f03204140c494901400003040c08001070903540a00413840c01403101c200070354011107180e0000da42450740c08901e040100050318158020b20480b0906041646e500c075900c0b0f0000741003614 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 138521708 1250 138520458 138520537
    0x30607050702010210050405060705070512030901090c08032505011b0e040b0420030c040f06090e070305041106090f040905060f010e09060103060b04020c0f010e010609140408 77
    0x4000c40c1d074100710744e0188000c00c2c14080102040002d8500348e201ca95075918080c0c00078082c8a400208081403102c1840001c0401c03d040b00a42d03600e08140440c0c5008048580041d142140c4450001c642d038200401141c0702280620a03440f0316005600301c1c410350a2007010110344640d03840d8070075003034801001c1050300c0560150311000b101c071701c504051005444410b03144910540c54445840110020301400707207840000f005d6259180e940d05100a46644100d804c00c0c00c2103404100c0018190398000101f406540d44101140c81c6911808401e40030b40740c041d50000e1041c4501da040031a03600340180903184c480d50051044814088000115046a101c00c03001d0341e0640090080102d60582c9009090040000d145080d50601d4540319903601e410f01800010400780e203a4001540b540d850790182c482044180042d24072024044140b01e000700b502520244030743d420030000055a24075481009001e525100030603015503100d5036040403a9101190182e4040e0650350080807014a0880c44d032840302 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 138522958 1250 138521708 138521717
    0x40b0103091a07140c0601121a040b0a0c090b07020d080f041202100f20010b060a0f11010509030a0c15022109010507050d0c0e060a090905060a0311150702030607 71
    0x41100f0020040391004d030381c110841c0010031641003c00310011341c450440300410b1490007030301d40c42c1c602244103152000c074000b03101603040300344814840c0b9032405500451141604010701284194190b903000842d219803074401c80c0074060500541014000545854896040c06113000030820340984141c0107a003111681481d680a69011800e181100c3c800c02912030030481078020444200a000c050b00034560110501c4990300c4420010003508403a42c0950001c0405071900581c1c1002070503145400b0380640000d2031240401429801031091a000740b000350061450511012420798240300f2540003103070381601d00400303600032190a101070580145400340b288903d1101c42c0005440200c00b80a52603145d14003810302c0000c40d0800d007102c0d960707440b00e0170125030000710100a60707818a00700801a08001e0014000b0009980800207030243c81c01200708000c0c64540f102803000c400f415001c02003022421160b10a59460582c0d1241d48d2000301e002124500100e0750302003401c000d01981d4080210713 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 138524208 1250 138522958 138522961
    0x103090c0609090e0102040b03040f170d0209041401031e03020f07060c1401020924070f030201060911090603010303050c10090609030807030504020f1c06020c16060504080309040b0103091a 83
    0x1181d90040700704880c1307040e00035800d00e42007640307604461101a100500c424000481d540820500b04e440703661000c890080b50b512101202c41410195004a040320320a510f0800b04150440d10104c00e641038035005507076002d1718154142980042030a03804240d05521402005813002141004070501400d05903445180c0003001e031038051075005520200318840e074014448043e4540300c0d003a450781c92001420b000a4071420b058642d00d118880c000380588005503201840080c10780540007241110269881005400203410714503410380a034140581e0301403410401000421b10031000761080c034804406a481d149103070319081045501d0420100da40c90b451300e15181c00d2541041c0440da2024480c00c0501252905a0000d51000f0a0340d2145106084145003030340440d1800c5c01042d2411342c01070007103680701206401c050390f4981c40000c00414050386940881c4151217082914102c0f500034006509085900007007002a11000c00300c3e60400d95220b41040c00704022121980c1c840d10301e0a03a210303c6 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 138525458 1250 138524208 138524219
    0x30215040602120a320a03060305070503070803090f01030617100c08061809010b12070306060b0f0d0e0c0405070f0e040b10180909080a08150a0e04020103090c0609 72
    0x400a500d04045043c3c00705004400764290003034005250405000042424490b10382080071800704030141d8404418800f241000915130564008070a8901031800c41e031196a503031003015507600c000d01800049400520507002c071800d0190f40610348a105041c08200d864071242e000303c4080c050f1589506945c030007050403008104074401e60030009880d1800c0d00c091b14000780410b0310414864180032584072403a00185400d00c1c01e6201c541c0341e0600625228210001507142c0f9568001800252050352500e10b00040180a850407220f6038a0131600003414045248140c00080421038145501401010b4002d0842c0c1d460340308142c0b2036007080c1c0750b2486624901c0001015804a008940e020f103241402c80146552246c145090003901d80c1740c003990b04071805183c64075450f1641d0100110780d0900004c0ca04211411025201004403030380d070304509a13190b070103c9500035400c480b0341e84c10054540381404180708922980b175000c0e0040c1804681c0341e92643d11928945016800703400001d015075414041d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 138526708 1250 138525458 138525463
    0x160f0b0105010912020105030405070b031608010902090901030f14030f0a08060316210f0b1f0b030112061d0c030d020303091005071107140406080d02060a0b0307030215040602 77
    0x501020f20b00144800d00340495091807204201000e4140b08020002601300310042020390040d0014500264036801c00045d01c0350811440351162000c2080300d030020442510074400c0c2d4540342001006142c2a07444d6403103035455a802c0140544510402c0652058108000c000401c0710280070011b9039580e640429001b010546c014150610982000f8041074614482606000035266001e95003a0328010b0354070704403202c2c54034440051041182c010508103100901d40f54512034183c1c1d454880005d050303044d40f181d0801003030154084501c42400184078040000c0c1c11100014851000000d110711307009200540035000c0e40091050b0307440b17603101810301c1c14140854890301240f80003c50460412025594451580640b1103050703941e00d01c001000e10b803240b03907183d058586035420384178581d450300e4503000e101c50801e100c0c9000314145200000d8802d000a101450810b29601900040e01d800312508050102412141c0d49441098004405669059180c3c0c1141606065075a519441c0000190 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 138527958 1250 138526708 138526711
    0x9080a08040906080f0a020f04140103060504030801050a0b0f031302060d0b0a12050714011b03020d0f0509030606010c0606090e03040e0a0902150a02010f06080d022505090a02160f0b 80
    0x20001d421035031599602120001c6c070800c030b141d8112282c5030a036904071301250061200081c02c00c0000e924500001c20300042d03500560185020340c2c1d0758105a038850090042000f04c51140c0750007003d04014400c10841c00030080c5400071000f000da48043c5035586c0018100e40c12070701d00c001802d80d0300e9451801b94504072030188001c007400030001681c00d005072a1152100d60f50b02c1444540c400c42c00501410361310aa00c00010b09082001035400c3d6101e03030070300035a13810b000c1507404080313041402100c003014092800e9030702080c0001e0081c20796a603420011503001000400c1140c280762100004591226240104048168030100540c1c4645c90603000103a095400707091155402c0c906041c201c05a12210f10304500c4210500401e40c2c0c446003140200d005021807a0ba21004a14012001c00c40042c04240d00760404403070303801c50302c20741091007022000c1011007240c040e40c83c6039000100403504042d943c40d03078040409003005081c0416401e40840c9010f000d038044945030802403141007080306403407026 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 138529208 1250 138527958 138527969
    0xe0a0b0a05010e060d180203010c020a110109050a0618050303160b0f01030209010e041704090c020f01060b030a2304061e0c020a06020d020d0c0e0a08120d090309080a08040906 77
    0x5904080f910004201644188059000140c1e01c9881804051001120406550b98082c2c0200038841352250001c1d15400d1610b000c640b1228409010001c0750b105414000990f01c1c01803618114a1074484140c405546551003141c0b0303030030501000038040d07400780060144008080d074141500001c071310305000c2d645c200038002200f8071092801880035844a00069066441c11034030102203485609001406031411030b07d408040b01e0003e000700b80d0341c050382c00041c11001c80b40c00f00c4005034a201080d5003650040d01981c1d42c000070900003d41c50801e140c002010551030115040c0c114007090410914010086400340c1d206600ea410000403103c0e00b201424561103004010800d68414480094450b40010b601a10050300071940703015205081c0d0469640c283b80d440d0030000c01c0300291018140c1089a01e200b48541c403034080020300c200001c41c03042500d10040c16654a440007140d650380081592203400d0301000703207500000c2072400040103412034050240701c0f42074545207031020764002e458154010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 138530458 1250 138529208 138529217
    0x406170112170f07050102040f0e09061b0903010e011b110c010c21020d020d0c0215220609150306180504080f04030803060315010303050304080a090e0a0b0a0501 71
    0x4001daa001d14620044859014018990012100310120080e0161444034000d002c000962942082015401002100c00d08084d119520341d40350750040d00c41804846401240d0030a20003e460300300040c401d41c0d000302c002d106250600c0d0341d22020070b085900d281006a40790790b6400f012606070f40c0c03894000f2920704d2280380c440050701c118035610b80ca9107107840c01141881a01d001030f008005070100c840c00740c0340c0d06160140c80300b850010001c3d03032162414051809400b507945209040d90ac034046000d48240c016102403806d560300ca0a01000368031003541c003079103868442480205908070724036440041003540d4400d41c4581c2090900c007509400ca155113014907180140810003c1d01e6100c0000c1900d6404100080720390b1107060200d25441a2065000100300014002c010061024003660181b03005404642d10860f9900d007403240c0960038000640466014000500015041c50007401041224038042c21541d95840c030702c2034000340a03102203041e15101c0030080818101004a80020813007443c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 138531708 1250 138530458 138530461
    0xc1511070602070506011e0b0a1211070308010e27100603030207180c0801150e0613090e0304080a020d03050d1107060f1103070509030a0f08030612010605011202210103050102040617 80
    0x1843d1008640f42c4231301030a00c5004a0b03402e111b54010030451204a01c10b0b101400345444c9240320f24031981c41810101c010411110000c908a0380071300c5994820f58400c1d00c1d80c0009079000c41d81c1c070f89450100489074014441d10225032601d454900548004500c260000d1070001e0409460304800c10f03c203000c02000c140360044807075809a000d0a102d04441040d140214101d0b0b484008682d1040d642c00f100e500101d000070400c2100300041240c030100c0c3d500443c1040b1110042154035124400e6210f020301990140c01c03006e000d45881020071840c0e074801e00f415864561130041c18401d49031160911082c1040128051060240b980a40c0c10032101114007048210440900f07021203020203408141080800320710880140c500f08002d49000e03410900c0140c0c0184640341c500e000fa4007c5038047c1c0103140b0001300542c000e405003d480c094500c143c40b05403007051400d80c0e040c000d400036940d0740200001c1400c00c0c02d03a00109400c15020b07500820016030750314205200581088142c0390300c440c4c141e00410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 138532958 1250 138531708 138531749
    0x90105070503060f01050d0e1b061e1b0f06070f030b0a0608100b0f03161b0206030a0f05040f020102070f050102030d0c031508010c1706010c151107060207050601 71
    0x10480f030380300c4070403142041e0503141013004031410f01400000c0100580f911800032040300f0f0004042c0e04180300007a42c0e049011411040c03003640d0103080480e040062814402e0100300045901401c20a540b103102e62803042c4100b5100d500d029020300300c3c18215000042031114a42d8030203c1400c02081c603003420312001c036246d000300d44045014480c82d420002200d01040f0140446500e0400030020980701c1d50f20348040d003074084150381c0301b640c1e60b5100c80c508020b41c4400501400040c000a89804180c030700801094003440b105920042c45088050394404258080c05604d05c99213007c1c50103486201c000390b8040c4000b83c0b030315007a80c0103001a500c0840007000f070780c2c1c2e001046804220320184041343c8004084419400351a0140d000c00440c01e00703102c045401c3d81c0560243c0c0520005a84145001e807140030203104a08041d5003180c00242001d0130302e40410f02c1600480440c03910b8100018403a0407503003c80c0490f410120040f291103400041d03503020300400b002900d0150aa801d41801c6807424807 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 138534208 1250 138532958 138532967
    0x4090906061410030c0315140907020106030b01060c0501060e010e060a0e09100f02090907021c0f0e0f150a03090b01050612061912140118052a121509010507 69
    0x700c0090205a03c417001a00c500e4401c0e04601c1c0003803048010300e54443e8842040c070015816036400c40e401001401d000606042c414001c8030704490b000510803c680c0d081c40030481e450860500b003520a0741d01d60034000344140030644014002c00446440b6500303400c2100400071198101d50008044003c458140301e480d00010070401e0201e031340000c002407078086141e0b50300068000c4040c40b40c2c0c4070410382c04001c48550081140c0220300b001103080420014003c034180c0d4035203046900d0b407001132440f620091041c14140c01442d4205401006460f403814030803549681070303205c10011000640c40d103900d50304000010b0b081c1409488201c0e4030703c0c02c2000c0103002c421050802840d031446100e490001d22260044502e100000d00140d0302046010202e60602071a01240980c60614542c40c02060581c12003844100d290080d0344440a0001e000710304480300301001d50782600d001c40d82e040100c9290030b030391001c01e1010700303d0045000e002c040b139082503817140c00480106082c05503414607003040380f100d511 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 138535458 1250 138534208 138534229
    0xb0f01050409020d0b03011107021f0906080402040f0f06080d0e15070f05121201080d090b0a0504120f0c05060307080a090f06090b060906010f0c080c0a08040909060614 74
    0x100c0001a2110410450100031700940c8900715050b5180c0341308050611000740062003403038020340b49011218100d120034034141074421070250008500c07010078008684500700c580d800500040c4081156030020039250115031100040e5040a41c0e600c90803c80d011003440f03007408030070032800c01e440042d50704408141c40900300c0102c80021070000603240c08010080500283c016000803c488400c01c030020301c00140e6002041801c949288040000703120000051140403d111039640d403800f9038648105243c00e500800c0d011403e200303003823201080046080101488030790042444000801c90f50034000c28009560300000d0140c8020010070000caa00001c2e0309400400320300340002c1029140c200310841440850000309424100090703a001e011211507601c2c00b8280803120b15032191500c0005440e9036060009000100d21210b0303420011403112400780c109100584240d442c034003425501c80b280c90340150010030300c0d80c3c4d0b034511072401e0103070b00d00c105c001604016040341c01170307904100081c414849 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 138536708 1250 138535458 138535469
    0x5070b04060806091e040c030c050609011d0109050d11100807300203070507050c012f0109050d11060105090417030601030609050a09060b150304030813020901030311010b0f010504 79
    0xb00309011038650005c9205810110207000d44006007030030a03142580a110040c03000340c503500311228003c122031801400700d50780400705844050034a00040c0e150020800e142c103001d410300c0030100d4009459103560741c544410034803429083e03100c501d000d03003000155061140c0000400901c0403c115a254102d45a00703010302405c158228a00540031240c00b8a038462801361040d24008801d2005490308030700940f100c03901c144140d0303c090340000c0c01110300012488030b0311080e00290b016801c03810a8414240c403c0c0500c0c0002150840f4240c036618075114540009a00046c580344c1000441d0405100e0107001d020111203c03015810182c613410110141001e4440700e01c1c2c000000314080f42e00a50100c00100b14140007482207103040080c820040403d8a02550f016040c04814855460507140a0440d1900000d2207403c640312510215440a0001c00c6600c08008540390b80d000b60b0f843c0720016000350b1003569040c00040c8220643c5080d6604114000e0051a0700d841c640c88581c0c00c40e00360340c191403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 138537958 1250 138536708 138536719
    0x50601080c030a0207080f09130905070b090a03050d0c0507080a0b04150b040c0e030c15040308030907091401090c0203030601090e090118060b01030c05040e0103060506040207050607090305070b04060806 89
    0x1203c1c41000c0c802072007903130340040081400059005600c2d010f07001500c840601141d000d98240011600c1800380e0b143e50a004151b80c12544080c0040302d09030014180501020f04080c00c40c50701c03079031130078680000030400002252015020000300501040380380003400042010307150a00c506d60300c600c2e1008014000500c0180e030f41000003040311107a800504401c400a000384124400321001600183c0402c120710b000c0e01030040c901e101c07401c0c52a6819118403000380303480d2505181d40c17140140c0360406002481c19000d504000140030115014a8001c05441d01015886e03500d8001d03a00d04031100e001850065400600802c40b4070f0303030082c0c008002c4440312201c60200d5501d5043d05801071244071012441520305145844c2484002c2d840700c180060b0a0304e040242c0c201401e401e882d50b01071845060303002c2c0321b01d23070041c0300080294115a070400f501070b20143c2806c00030354030b09060040c2100d032a8005101d0420400601c4410015400103165900c489480e0504100c4000e00300d10000381424000d1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 138539208 1250 138537958 138537961
    0x80a02090f0907080117010b061905120408090f0d1a04020f30060105100c0305070b0109020a02120f040306240b0c0f01060f05100e030706050a080901050601080c03 72
    0x7070711641c0100780c0200740240125010702c0e2059000c0d06041080c040d500102c40e0300000d0085e40c0390140300d503201c00940284281d042412009240c8000d00601c0c0a91041180a00400340c800c06440e45050150303129022450302c89071200180544030691b20302032881035040d400010b011a0512006580c0300141c13800031085540e40307001040f80d0031004141141c001048a030401c00060b0040780b061420b1344510f90170004c1304d00c11185903030f50f00002c0c02040c0d0301550304040800030368060a400b9180600ca801c0c0203040c030f126500ca00442003002d07030103840100d80000d03104032601e07411b01c645030803420910441c90410203200d0520603180181e000041c001640e0b40c0a07400003006001400f8007010400c00b01d4202d240d151354822119070407203d54140ba92040d280c0e5802c20322018014882aa000d0f031003400080c03440c00d400c01000d040342c0d0074400c090000c011124001514288040e90181440d5164156035560074040144041402000003031640d00d00310604c0745907a0301030b00c0d0542101c0143d4000345c40303 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 138540458 1250 138539208 138539227
    0xa0c08070614070525030203030c070309081218032e2012010b072409021005031603020c030304030c081b01090209010b03100b0c030c01230610080a02 66
    0x80100051105070759442c90308200c03245902400a08408070000940b04400341c0032480002c0410341e103440100560000d00005829010b0980604840341c002c4c60180041951001c1190a06007940c2c11604c0340c08001941102c0c0d241080c1e031803903003014150000d01440c900c281e802c0c0c900010600800741d084409081040800c06680c1001e042a0b181c00c01c00c48020182104480c0654040f18890ba8081115400082d060001d242500d11550b04107800080c1207502a04000100ca1000810480e10740d071185402c000da01d88180304550b840b042e1322419900e0402e901c1a40440c80d03019105410180104802c00305d40f01d010003620741080d031500705030008500780e05d800c0856008021300381215050022080c2001c2005403c114950b9000f6a24045103980b82c0f03110102a1004a60740d9482c0c455444040048106840c01040c076810081c0c01e0701d04094960a107582520011206001030130504d0040010050a200041e500481e04484000418100c0840a02200c400401c460229540850445003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 138541708 1250 138540458 138540461
    0xc0607030e0a02030615040b0102060f070521070f030608010c0e1002030f0f03040c050904030f230d0e010c03020405090f04020a0b0703020f1506010c0f060908040e15010201020a0c080706 82
    0x3007855004040c5d4440380740c00e2004107412480165031601c19810940f45140f203500104080b80034660382e18100c4030907600d800c0c01303407402e40c445002540781c00d0465420840f2102440811405039140da550030400071280e0a0007015070743daa82007504184d240c003d8000200c1e8014103030841001c425100b080121040003026400c42c0180e62194205c4400019010048060000110722680c460078001c10500c0d05d8805010340030b582241c0050105004a004070707442c1e80200c400850540701302080100b4045c140e03d5123015508000e100b01c00a6032645882135408100b030141d04804050341c9411070a061404002070711040c0050501170009407408041010f54a5800c60f44015000d10340302295541c200307142c003e5440745507001081050146040250166519000316402144142d44042600e4000c0c1c9504070b83e0b520001d81154440d40d00c0221400107403108005d0401042103581a00d403520309003207330360030305418103010718116407041000030420b58101c080035007244d03008048591182e02d036182c00340 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 138542958 1250 138541708 138541723
    0x30a0b09100510090e03090913020a0312030e010506090c120c040b0a270510050903030909100609060908061311030f010c030b0f060717070c0803040512030c0607030e 73
    0x40c6a2400c0004000d60040042d543c00200c42c056401040550541e1000c140c07a4000c030b03040c41d903024000c4004546c01902105095618074002003d68034025603d54600103001d4081441c9400300b0340b10100c002c80c246082c4030b42540b00c0b01c00d0b54549a9031810460002a82c0b04200c141030f0031111485c04106800140000d403400742c1041e09800c1d50f20385800201610400414110300005030610440705584500c010707a00c422110083d001d502c1b001d403a8102a035a80d007203400d4054062005002040c010ba46004110303001c1e804906407001100e080120007001c8002641100061281c162410450782000217079103584400030703882c040040c01140c5000311400230011072a0b941441a0070086001e424198440c903030150340d68400300011200441808030000b041000c0d16807266050200e240800c01c1c17005c00100340c0026040d40351800d141e569aa030a040700ca5000044664070100e8140450304020390304015444496005505082d000340b00d60399542d400900000426848444140012508104c0407 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 138544208 1250 138542958 138542983
    0x91a030d0f1b030c0c14030703020402090105090d060219020607120518030a0807030b03070506030a020313021905040f020304120c0204060f120c050105030f010608060d060f020c0607020c030a0b09 86
    0x151803580c9508004001014034401a01c0100443d81d000510044103d0101c140d51b1000e00070300340851558082200035005100c90318140081000941d805507950381c0000c01d41c601c42c0000585500ca031201105910042100c0d240955001d0010f0100c0e054120003801c0f01e18000c09000725280d51741981404d100d00030308070132403483d00c40800d15034000e540129041d84200190759041213050300b450b0030140d541000344942500144200049544210035030019a8011188841840032010f1540170509154010218030710b0501c80f12401e000038a050b020703284441c94001006d5003581440e840d150310b2110341e8804d050078401941c0300c80d1b00319142c0d80c11400081120243c000d5007541d0780c50b041000e6800e04181154041980c20010440b0740c01001524052040c0c1d5110800d20307800c00b04181c2c0c10020251040e61300c4100064210300040060240c05100000f40300c0c0982c940b611904200e00d000341c041e01031000d54004024905050318001500c07020207811484100c007948541c00036906110f4801c440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 138545458 1250 138544208 138544247
    0x306020a120b011b11063a0510090b0f0603090706020f01020a02120a03020c03070c1409040302060714130f080d0504060e060a030b0d0c091a030d0f 65
    0x550311466044156025244030121061122003000c82c011540061800b0f600307400400c07190400c5020031407140075403158150103031a0614102c0740190b41800d107544180000040d0344000003411403030300702c0e44400c82d0113a0500d509104606040903004842d20040c023a41c0031031030341d4202540c080c3d590584200c444e80f101926080e601d0410360a140e486400c41d01402000d48580309070300d14000c0e814422204909604c0e405042c10541101d0440d55607480100e4482c2019000d010041d0071541c1880208110380c412a0950081490b000c00c5012501e25101c1c60743c8035407103100411000c84d402113401ca40c0b0200914103401002c01314140d0100c5802100300318211841e4041780451b4901d44100b211043d101508200d916041d407140045600d031040740100d40000c2c0c00a01113085030300380100a04840101c40c1400720741c10407808041a44e1007400e0303105a4502d102c1e1141040800f00c9482269444482c079450a95407194178000b09980702c0c0c0c90015502000f5052164881c072512034440510700405200f41c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 138546708 1250 138545458 138545467
    0xc020307170c2505040903050c060703060e01090c020604060b0d0c090911060724090803070306030201180b09060304050c030601120c05010c050a2004060801020c0609190615030602 79
    0x240426041200400941e200f0b19942c400103001c40708000f140b401e001d1181c0c00340c1a08100c2808090001c5034011818010188002300d0800b8080c030200b84224001e0b640000d07598981032160f240600180e1181d0a06840e01480103a4541d01003080760340a508501c010030201820400700318504030311400586401007007540410303840e6442c5c101161840c0203254150740209000b0411030031303201e48070004000d28020031888900c605d050811030f40c950105200010b030701240b03884104a0b64011100390300000d1380d401052046603044810740600d81d01ca0200e09010704d0400086084070b2165a031110301c210000700008003089001c100700342c0c00820140aa50312560340720210300110a8a140407a5036484020700490349501c60203401c1900c030380100c01011480c03101c1c0c940703006011058500c0d4660f04440c0300c4c0d800c400d440300d0086400511807440016519081c21217864240762018090786c6654000f4595404d002c10795114001001da002900000e4002d01d500310168000c0582e07000400c582d00104 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 138547958 1250 138546708 138546743
    0x31503190803011e0807062106060f020d02071a0310051002030d2405060d0b0307060507020a0803030603030901140d060306051807081b012a030f050901120c020307 72
    0xc0145040b90000440b6040000c4501400580c4c0521350040b0845940409410400a0b104080d6640d400c07a951650145440104403413805071075241d048034010030981c1d00d004e0081581044400e1180b050b40c40541b40c00c90900d824581d140c403100000c18040c100200204100312020b01590004100007442c807410b00c20fa41d070001e9101d41008680c0f803000d62030042d47c0c1a68180b81240c1c56101403800300000740d0700c3c0c100002c1196a422040d0652500c0b95203d000d03010719102044903e02600ca1030721102c0c1c4640c503603c10420b0b901881d401901d100c3d041071044c003103152400070581c0da45038402d0a01c100012440300b03c200c0d103030041d4010042c25906100c0000306000541c1c0c481c0b13000301d070002040aa100c1420500c96034071005485119113a610403403c4504c078420031007107a10b607210149070900d0b00030743c40c40c82d0210f1400c2200c2c040803032340044800c00d010590400c8020400710082e007052414800c542e000a828140d128070300221464503903844a82040c400d104031101c0a900440c0a03160700800c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 138549208 1250 138547958 138547973
    0x402030a0e06010b0415050d230a0b061801050901170a020304060e0a050d0509040212040803070917071521060311040902090c0f04030803040302150105011403150319 73
    0x100382031501c07070041c030001007581c03034445084805946c40740320604014070340303107008480759400b4504d0511160750340da0507018160841240d8007040700d00448004440d081c6425014121100714031851b10980c0c08000c0b4134003080947c6c074091040300c400d0030803584800c41c05005a0348490010408992881c10b20100300103240c007540510b0090b8000c01c41003007082c1d0b130002c0807070380c035018050090415130000c1d401c0b680c2c480c0719000410300c0b083d000d4409404c0180005486038425030503201201e800300080f040001d501e60000542c0010324200e1041c01d103030b82220302c8103500c13008207011701d6440340d681040302c4c641a8000d01210401c24503107486140324100a9020000500d00c6000c211048032415602c00c5491030b2130700500c0d0f00c1c250020301e0005952a500818820b90784000b05144a030300c4280f1000000c42c54881c0a9031080b4001e4014000b040e402440c0d0310040d41050300824180100c0200c0991100040c1c010340b507020400304400065860100f00103031030624514844406200441860410410003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 138550458 1250 138549208 138549221
    0x6091216030302060f0106050904050a02040801090c051201060f120f2a0605040b04330c0b07051602090601090b0f04030b0115020a0f061103010f080624120c0402030a 73
    0x80d03080e83d01340d445030451145008028440c41000aa00340b0098106250591050380c0051a0200042c94550313180403550a4800e0301c50240c840700c0184c6420000c9003050f80d01c0000100805008120031400c2c8000c12940701d400380150015455001819000c00c15001210b90b03101d49c100a44400142c1014001940b4840000d15540702013883d07a400540c041c0a2006c2d101902d54203100070b4281410710101c0b080460750510400d1003c0c120498130b45080c1201240909401c046a90380c01c0702c1d01150030b092440f2000134120380b0811904000403000d1103940c400c0c0415155044900c0941a194080100c4084d07901d5045140c100200040c030213480b81030200180100c1c2d21500d03039401c03113a076a00142942c110801c0050009a0031803403a2100045040d08901240c5118000004075000784815a803000e4209801400d240303104400e06101e50b00082101d60b03808582014030500c0141c4080b004074125140345900e45c00340b80b0984003c003000f081032241c4000c8840140007152a46400040703100076014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 138551708 1250 138550458 138550463
    0x80706050117150402030d180312020708190210270801050a06050415032303030103050c040e0303190510030b0c040302150a02030a080a02040302031c090603060e01050609121603 78
    0x3c10380901880b8419445641c4545c0d0020f01078400d0f44901c2200b911000d1245001c00010555280040002421407440d00f11100c1581d00614106081c601003520384108a0300c0600321036000e0211000681d0740c100142c500070000d01d0100b440c00304c0d0351a507900d8030308981070700721700301c0c01807880414010015440a0301c5168221010302c0b9555589040c00b08454554840c261640042034040c804525098050b10329142e1455135421004c2042c206141942c2003a007088403103401c40d00781c3c0308403450240640d4200701e600d40040c52450800100d419074000c1c1d00c41c150031810341c03580009070b202440415541e0045804c070481c0e00c003030310300700e120341e10180d01ca40002c03803007080c030a01c0001d030042a030029280e1340700c0075400451908603283c06c103954413403000380328802c100e40820000c40183c07824010000f85c021444028000041704420140030140d07070750004020140303040e00410000d2040b00281c0e04581d02540e400d030f0384000d102e0105010f088410316103d8903104441d007000601d0300c0c200001c41200e0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 138552958 1250 138551708 138551713
    0x10504030e0a06020c04020708070b090304061e21060b07060905070602010501061704020307151205180c0105070503070f050609010b01050a0e220c2c0904030c080706050117 76
    0x5403410030407600d00440d003d11401a8040040d48020b82482da0050140138080e0000d1401c00000d0355485140c0c442c100e0b8000f802d50408a010442d8035040200252040880005107412411101000f090b80c03808201000b107803042042d844110b1540fa41c0b1103c05840e1044202d507a800550500310090700030800e00f100e080c8564200000c0c218418820303141179884aa0f03419482c015002c04140c250300d0040c20a036418045e10b400024620b01da03143c1c0700e0505030389483d1941d00c0480701c84040b00721003008110540d40500e41998100ca444041107174041c00c00309003800ca031188503504103c0c0c43c5010340070004100340c0e000003c0a041c80070000d0480d11601200780203010200211b40112014015050804042100c02204c440c2600e800c01e03e0704d8103200c440c9101c0200950650b5080c09980c2c60340c044001103203014500051a4002203010080f40508054071758040ca82d110105020100080c030203410401001196010404180125001a500103100703100c69619107120354100055525034042c42d1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 138554208 1250 138552958 138552977
    0x50108071701020403050a14010b04020d0f0b1203031602010b190f0f0b03060d020f090c090f01020f10020a020a0f0605060907110a03110f030d050105180c1e0d020c01050403 76
    0x90784140200c400f03a0b0b5202c0064002c0c040195209030900000c020b03034540b19500d41d500f07403460352118806002c080f14050408a103c00007500540121019800d5040c0545c1e005e400030820a03e0020440b034101e450602d04440500e52039104a005186000036a540240310704000301c1650107005203541030751101d40303800010660385d03407004090b4940f612401414040610005503103140900001d48000e0002d0120048102254001562072500720b0702c141d261100816100800d040601c22003400c884c0a000400d0303500242807281d552100e401c1000c130300c220b40000d40303045c80e98424806c0b20b104170751100340c0c40b680340c000d854003102130401220260301a10708070001614032072044486150015111000d4681e20030300c0c1c1c604481d85005840d16202e50710401e03040082a410400040040c0000b400b000201541001c082151480c3d22214116405202d50180303e844e24200003102d80204d400b01d00200341e09401c58000a070343c090261481410751012400b06500f18043d08818811403103a030780d81080 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 138555458 1250 138554208 138554249
    0x40e09060106020a03030c12150801050604020703081303030b0a0b0a030f020a05160c1802030613020a050414011209030e0445050d0c03020c010c110108060406030605010807 76
    0x480030248500001a0b10801802020070302a9119051144907031070103010541d00c0030300e0103081e00d1800c5680c04010301e10500821981c10203100b5140c105100b02c50561030003800791001072403000c000d80035240301c089c11030f813680c02c26000f5404000d0600001e050b01c908195100c2080909810001c0600302003801e08251600003aa02d108694507207845840300ba0078500380104400810f204d00034111010140c0150103e80e0111030041c8095220351540050307500e14000c8180020141d1500e050340205005100829000e5040340030354081d900100f503411003100401b4012211500d800c00c88020721441c04540805055014400d0b4281ca40280d07401e02c0040c4603482e000300120b2140e0801400c0707406a00e061480350110f9250351500ca540c0109140400046454860800000c48080b0012403045207001c010140c060080300ca03211000d00300295015403944a1010102d20103000302d04000d40c02c0002100341d07480c0d43c8050702864004000300b00941c0c40700011681d9540c82d0043c5041441000014000c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 138556708 1250 138555458 138555463
    0x605092e03031202030912031906080c09040807030311030a050618060a06050a09091104050109090e03121312020c031515091308070b0a060b07050726070b040e09 71
    0x80300c2c2c1c903584640c15850071040340b400075000540317050f246008404410002102d4000650302550b40a404810380e8103400d5018030841d48191b10003000341d004a802d007452543d42c1d43d00030394401c1d044210145c1d107460924044000b0071460002c207200d900c2c04030030b100070b010066100f240f0800381a02c142180040740c00d1030851004049444e10f81c890059041849224884c1000d46600c8445007400701103640c8070721481c000da601c4604150503424020804015642c1c0c06030161000300b030041410801ea0004c0d9155940303e100f4004415003100005000c01c2c2442a4190f5202c2c1168000002071080100c0d03010082d1280c6d4401500e5100303201d903011100c0c51483d0b00d01c61600801c0030245440d0100d0303000d000c0c0986050b0081c40304416420000103c400b2516020007450894800e0003c40041e1510310b0000040741c05581010401c544140600030000b00005101d1007541e08020340304101c10b0b010003010544408180b100d030014054408009943c40c00c00d005001a100010010940da81c0d96485031075 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 138557958 1250 138556708 138556801
    0x906050607150c03091a040b010605190e01050403081201091a0f04090201050403080a0f08010605070f0312060b0406030b04050609070f0503100b12041202060601020d080901060509 79
    0x92103802c461000d508104a5644280f0034001c841c100401e0081c12615240c0070340540c40a802075044400081004012070550218050308050030020304042450403014651590701210505110401090300c0980e0b00a03416140155404070703c030f650310b035508103012000c00d0b03080c07040d1a00e0310305000005051788a1000e04000050002d4243c0a884140500b0070018041b0341b602070b41440000c01c030100c04140e00710000d10441c11581ca9040101c80d00c20001015a001688aa401c000d401c6c4181d100095400d14145503450701032402951400b60072010000a00b007c1d400400c041c20009070008500e80c16030420700f032100f0125002c100c6c90340c9070414000e280900300e42c2c2c1c40009452840e44a0424040c202446e0400d0301907800c0807929417500b04d480519880000010300641c901c500f040100101031002c28800d14552002c1c051506107400081d580308071014a40c401d00c66201e00040303c84d20254000002441e000b010b400850510039081480c0c2c0c00c0300c0001d02d03404010351108000c8201e0000808 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 138559208 1250 138557958 138557963
    0x50703063b011a01140d021e0408060906070507030e0f040612061a100f11150910091e0f15090b010905040209060d021207080f100510050d05030d1103010906050607 72
    0x103101c08640c41401701c0654411030183c0f039100d134240900622a5507046286204a0b800c6190660701c40c1072002003464000c00812042580e8003810820508c55445025202e05a50601f84280d0030396840700020401003140c0141504980350440016550030b50484280500d406070204014070398070b0490714840c0035030790a64140c001c04048680400240301d49010000704034649450040c00c080485002d042130b14880c0d501452001c0c64084c0241c0c0303003040c041120f491000882c1000500c0e0b00f50784618200c42081e00700000f07070300c50b00201e0051020b0003040c0c0d07041d6030344100a059109503c02d415001000f40440666070800c5210020070a02098440d0500464005126200990350b010400c0850f03800303114207d03000000111902c80d203503030404c100c0015082c014050003114484a6002d0300d4003120003141c1d0744141c1000240250480098060740556106035961309440340a8240b440c84d607c1110304161640f46000c0072243c2810440015505031041180705002099681080004078002c3d507102 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 138560458 1250 138559208 138559217
    0x5100918080702030a0f0c0603050c03100302010e0a09060e0f010b070b1306090204020a020f060c040608011e150c021309230c0d050303040510050103050703063b011a01 74
    0xc0010810700405490002c1c801021504115101e6481d1a546017030040120345c40000800103012454060040542c851141c0c1502400c602c1c0124000400100c00c0c031000e814000d41c1160081c25499032070640000e800c001c83c0a0284a9603171050310008582111401080d00030700c000460a0103209007110850380d0440308082207516110340c20103503001529411a10305a498809000584460021b0072015410740c01030600c00a054183c941003244c005d00d440101c40d0100424004160040e101c1415a00c442802e000e49089603c006010390301c10f0b421804816201c00e0000c205203034071000b800c030528803d44544c01c80b20000000c0909540d10020b00502c900c101d0611254a1241c2103810b0200c4d072000b008445c050410500800c1e15804034050036102d9820010400061200c00c100d801c010050340c0d44100a03d42c950344500b80c075130300c040c04001c001c02d40710807010032100c95140718881c414030304000429031003404200284403a2662a8040380e40d50070461400707000d05001303004a07000c42d010f844 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 138561708 1250 138560458 138560501
    0x11104030b0a050a0603020406080303060109091107060e100612030e0102060f0c0d0902090c0d060e06010903020907110618061e070c020d0b0705210c0a03051e0a051009 74
    0x741d001400004100340c0c2c084e0354801d0000050303513460040c0c0005103034400241d03583c0d0030060001050143c05400c0301d0030303035070400400d0230302c4070180004c885200d5045900003d00d400c1440600e420500041d05000c1c0e12400c060021802910480b80b444280b803082d150001e6191240c4010380e00d6103011600f0880d00742020000480c1c50300040020900c0302c0c4d007441d000403020401d038001032072050165089448142c0c00303e10201c10003468413500000d0040502010902d00d09000020130010050000900800540c00412040c5015034103000b001c01e081d9007510454907142014005002203c20900300c0c9105c0d040100d030400c0f200030480071011b40ea1480c450303d145d90704031041d108119400012030b00026070083ca0004121031501103030044400d592860380c6e40344171b19155668007015040000c19107090700c00344040c4080e0302d0111040d0559a0801040c1c50b52200c3c1e42541000e00c1c0c00680300030080240c108018200b29900c0306102e110221146038001c0c0d2a1444001103417102140420003006000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 138562958 1250 138561708 138561721
    0x6080d11060f090316080301050114120106031805010501030b0420010804020f0102030c010513020f09070203031314010e0f06070201150314120f070b070806130504030504080f0a05011104030b 84
    0xb40000d41c0200b612045900d040c141510400d404003030180c041d00c100034088014855903a025801c3d1200c144849081414181020660007449006101304828143c0e01c40131603401080b000841c0d140c01d0342181c0204040c0d0b0303680c1003e1404110889086407102c50b60041082ca042d03456031100c07843e00061790307200180d6881e0390905c4a1403002550b43d50551006202d0b80301c0115090080da88544241700000761040c1151043c00a61210070054501c503000c00c2d8104401c460707000082d40e501c00b41a1200740b012668505040100c41211100c0e14915420821003c4010b00f000643c1c4d501c0e94828022110f481d80c1c0c240c0200d017283e440361340c9220354551044040010070000c01014000c00c00d43c8080c1c0715001d06501030079042da031051484010880340801c20303900380303c10045119401803880c1885145440c0120000d088216034409016a40b81d54101250a141c80341c01a42c010300501411545035441d205003c0d070b90b40c031540b20b00310780541c24a900c1614200e0b2100a44084039403046035a10340b602c550 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 138564208 1250 138562958 138562981
    0xb0105030108030a032a09030b0705030f1902070c1d0a02031614090a06080106030c0918091103030406051c06031112010e1507020d0f05090103091a010906080d1106 72
    0x181c5030000014100c40d20f0a404c48488081c0480d5181b05440e010740080c42c44c908032602d004024100010700a007401004000403416072240d0b80b140705140c2e1010440c4030305280304000d000303c40340138005400542e404148400c10442c04007441040079030910055403100069070a0b0300c0210f40308044c4c00f215082d544403240c0150754410075130840482d41400d2000300004601c200c1c240c0e41c84500051840b000410110b80c041c0300300b0340c0008082c940304070800e0030842d4180c403112041d0b03454400d0350750b0754500805011001e070070003e020000030203881d0307036503551a0700402d290841d014201152105003012041150144540b004503580000c60310061401c44081002281a9403026001552100a0392500d1141030020b0f42c040c0740c10200f5490103082044009140a0013003925601340007042d00c0c4d1703010360360304201550501d9001346004107111180f89800c00c81091140c02d14101414840300100b01d203512600701d1400e48458100b00c80c0b034100034080481b1200c02c10401c0303603035640015021038070501a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 138565458 1250 138564208 138564221
    0x11070308090607030c060f06061418090406020705010509100606031b0302090d0507180b0102210a0504050a0f0e0603060f040f14030705010605041d0325050f030a030b0105030108030a03 81
    0x2400c01750700160403a200c2000341c80b080031000c0c442030b80e52a014060039030032851040c0303060758110b03a003400e10400000341e044807060a09002d1180341d8910002e4100b1540f81c045480d0158080001d01060a00c2c45000741c4c0c0d495a0b44108000f5400d040002c82e00a12074881c80f216003000c004c4042d00050303043e0301a0000e5021010950300169a6000076001c22400c200310030051a8126840550f221610003540c201c8031822111811504230043c01204820102d600220000c13032480e01c0e6070b41c0c51007001c0943d03140c40b0300d500c040d8228181c041c0c0062042c0d00d000c0034008a07900305010320080d588120406898a0703007140d112180c003072041c000c10b01040c010303102d2000fa43d01c14a0307044030b0b0880101e5154619048201c0450701691140018440c1d41001c0c0504410520002c2321005c10a08036070010b902c0f400380c40111603026084021070066010350b001e603810031070f80000550b0034400d01034000b281c80f0b51102491002003414034407851060351181e01128100c0d030040d0069414020700355011005010b8 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 138566708 1250 138565458 138565463
    0xc02070302090708072604060f0b040903080402090901020c060408090409080d1d011a041a100210060605041a030a060b04150306170c010f11120a11070308090607 71
    0x604000400140c5901c100c2a0244099071550001840e00d090f001301101c400c06040d0340c800001d003e0349100e11040c900c1564116130b11803404030b03181e0100c100f603a00400c0b850a26580c003a040410308401d06401c0020180184e0081c2c80e4a074243d40e03042282c609034030560b9185a101d83c00304000402003400c4002800170300c6002440483c880070580c03600030241c2c00010503040c00d103683e6805080c1c10019429504c2000711100001c1c00302174082d07040492428003508105018580750308800803076140311800313403041d010010050380b41c200a018000b50782e070545040002c0342e5880c0050200e03282d40100c040c0c41c01c480e0703400700389640741078240205c1d540d03500080c100031402c1e0784910011030004d60000250005e400c007400015010714800b80c00505031926940a4108229036a242c000707110800304500000c08001c0c280501080d101c0801210200100e80d00d501d400d0023421074404035908180024640b04030a07560340391501c0c00c0c0d0a50540c40b60850320005007038003030411204140e820450f001d03016490 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 138567958 1250 138566708 138566713
    0x6090417040902040b0c0f010618020c0307050303070f110a0807060c1806030209030c1504050d02210a020f010809151b12010509010b0f0a142107081605030a0c02 71
    0x10b80c0c642100301a038001d40c000c40d9854102141c88503940c10304011252501c8403d400900009241031003412500380842481c0c6145900000d502d0ba00180800480e6811a440001c40c0e03a130385004d0750300400441c403220151002401c0303500444420900080c00d507005a8004112615002a565511004003d402281e100740718ac1c0191407043d20b414070250070028074603500c02503034681100c81058200703440780c00e10a200710707000c0c0d00c0300046103100d905803000d8820a4451413400c9002d40001141c00c1d040e5800840480b00b01d8041030284100810300e610300b18803da90741540da441500064903085821110b070160381e0b004603ea02507900e0060155904003148003010000210b2030724040c4059031000c0d10908442050b81e0041100b42800c03c44076006103c1c8030102400c0074501c80d515495442822202401c0100340081103c40600b40c8040b2511440c0c0d00344807294000b492450344000e20400c455150200e41d5005c00036904510b000300b041c0d041182640c580d441c44c0e40d80c0c1c0000001b0042c0360320400462 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 138569208 1250 138567958 138567967
    0x2060609040c1d040506011a07060b0a0506040f050f01050304020105030a0917041707060905060f030603010b040f0c031a010207031e0212070906050a030804030303050601030905060c09090f06090417 87
    0x1001d00d28803c00d507207103001030700d2209440c0c241840ca144c01e0041c0c0c03040c43c1c10b484882045031030101000944a00641c4160046200d2070140d0000c0d454101c560400707503010000040c00508014554980d2003110401d40c0e5400d030480ca031900550b598081180c0103404214104005581c60f039456000c45221803040c0d01400761000d502000740c100c2c0d041900030301404105e152400828650400c41040209201d19001c40320314140404598540541942d01c1c4c4110808008990641d07000c1d0407c0d0760001c0041c1c0200000b0406603e0100506807540d031b441c011a2520410161040d40329149002424041e0000d1440d245907079264003695501c6100b0310408403c1510f1000181d031120009854040020010510542002100c03130454010351304c410300c94590113004000086440080d00d00310303501814001101e079982401680501188030380103026020380404c0214240109000c0c1560340342c03e5802d040c150b940c0d102007481900b802e88125038488100f00005002800500381d200d42c1031107101803241403 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 138570458 1250 138569208 138569219
    0x20901052208070626040302030909100503010903030b040c02060609060d081605010203010e1302030706030e01090f0c0f090515040c0c06050a271a09010603080403050607091502060609040c 83
    0x3c10b54075420a000040040d441e4032110079034540e04032102c81c01c100b00340710b00c1d00340307954044d5880c81000c0a1500620b54840019504000c007502c074030080102034024006c00002d40303401001458018841c611892030300b504244200d1002524030311506000e04900540d4854804001e00c0e58081a001c0302c200508000803440001001d04002042d48074130009a00e0354105458252801130081100c00b07184503034141900982c0c1c0006d0580300f2035105080010b640740c0394403220b50240c100003001815070f54404841c00104044400c1c1542140d03c6075001c01c0c2400e8481c624001924800c0d658005000c08401e514881c2c0c2c40c0581c03002c0c03104041070401d4008484c03035035510020780b2405c44a40010a036a481c4482019076480e1a10310b800c1c0c00c1400d0643c5070061a5a25036120503401c540d03200b09030100f0009104030307609604c0f150117180c21984031500c0380c7c3d403072818540e50181200c6205c009070341e076680014092007a200c03408009101e60003070040c4c3e0b5501c0d0180214648024010303116900c502c60000354 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 138571708 1250 138570458 138570463
    0x20c01021b01060608040519030c2306010506040501120213120507050a0504020a0516141204080d05040815060117090d02010c26060d12020303040c0801020901052208 73
    0x1500c1e921140140300001e880029900b100d44a61000f0306210440c01007200060340410a950700601481843c00407204908048851000f03e003c000d010f016002940d90000300c5d01c3c00c284144544050840308542e888800b400b420780500c0c880d5a0101e82001014403054100341c010340080201070746069912a650807082a07030720060241070f1000c1d0010b00301070050b810810710312005000709803010b501d00000e40c0e07401000e07841410011055244601c0005080007100d03600d07040d082038440304139110b20b000701001c08420b40c030900c40c1c0400c502c1141c0b480e04480b8091802d03503084680d004040c014200c0910a00b1016203001401c1034100300e100203400440c507503a2031026016030038440c020065884880701c040d08640d403c1900c013041c004440050480030b003401c5c03203408201000100340f0007940c6418010848428007000e0041240e081801c004140c254000007851040340280c0081820030f5407000320a0803072041680d80c40c005582002080e14400a410746410b048141c5040054642c3d5a400a03d0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 138572958 1250 138571708 138571717
    0x112020c0115060f120c09030f0f150e0106050a0f0e1503011a01030f060e0c071712091905060601050c0307050a111504050a0314031e0d0518100f020c0102 68
    0xc156000144c00f44590b0140000401d0030041008002c10241c1c1e0307101802c13216440c070004100701c071211151420082e4040010031016801034600c03c4100e044c0d141c1001500b10158034039215842c10350b00044904d0800015021565203c0c002c02da860f0802103080d540b080b000303105581c1203d0f00c8040d1155a03e0900c00d04013080c00348503100c00c403288900001010707074500c10500264070341040414400c003811000c240340c01804880c41160356030034a1800310075075507415101040728240131400d0908102d607000014818182030040d5000088100148050070810360000740071035200394000340303003035018000604101c01a002180c2c1481400e17515685000340303861007110348070070b0401d0a4099082401440211900c0034030078604003414007000c2400401c03148030140031400c0d02d50703400c00507150910032103441f02d00e20f500e034a21400000440404580c080841c0003a8035141c0800221400d504810031000c0c000014023912440781280750b400d024040300442108407035420403420344a41c00910051 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 138574208 1250 138572958 138572969
    0xb01030309140303031006030b0d061107140f06011208040503100c0f02010b030c09041109010906050906010905031b0324190905030301060c0c09050a02090a05040b0112020c0115 78
    0x41c110700341062400b000031a0400103842c00380c2e04c14404c3c003042280d081d030820700390b0f0218503001856184030700c0040e103080155100507000e1864400e1840408084034020314980e40189544140c69400c1d00030580c0d0f40c039861681c0f004a800020060144404c10003400b014580908000343c04c050311800060b007400442900500119658036500300e20366001089038440300707041e0000704100b0b038852002c0b0351180b030007549040c8180c032070710009000c0100f0001d217a02070754409054040c1940e100e6210000030190f41c003c40e0b00c96112030000480365031003034001e41e0944901502900b280d82900c040d21482039110340300d1300d42c9400380c1a10701454121606c400c43c42411803500004071410700d8042d00c84000b0b104801c000e0800d04081000d004900e0010440c2c0c111101c170329007040400c160341040c20914200b5003203040818206003d1003054152a0064110050110703031800c0e1035a600c40c2004102c6480017a0700d404607541140c1510004119800307009454440800881c3c00081c1c01e0160814078a00d4009 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 138575458 1250 138574208 138574217
    0xe0705100c170a02032a010e060708010504050408040302100c0b13380c0c480402070201090504110307080702010506060405060a0509041401140616110d0b010303 71
    0x303109100c607042c2001c90700ba4811018910b041c1035580000c0d124070a0b8a07645900b02c2c140304c40a442600e0000404400e07042130301c001c2042480c8a19a03d854400a4031200300050040c400411989400e11865010b640d1102800e03240c5407a40e030034401d030368400320070900c1800b481e80d00c5a808502c3d0030648501c0f80d4440b0200382084070003440c00240440032108940303103800d82e590550880a04045002e40141d08049035400d46a94144918040d07220f2180d48602034014101c000c03c2c2801d401086c4684101c01c40020b03901e41541e018500a0070303000c5591008001c0c47c880d100601c1c0d0800b94000e0103c01e006141148855840e0000b1a041d1108002d201c4440840001004038240c1d011440396008144c030710003800b1905001c400a02a070203075000381482914001060304075280298100c801894001c2c100344215555200f030410400c03000d10901c00302900c080c40c800024680344040b1030b94003004202014007801951210201002c003854416089040c124a49000c16201d40b4071a000b0340c86641d9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 138576708 1250 138575458 138575477
    0x9010306051e09030a0305060303190e040f15050f042d05060907020a240e060103060605040b01080a02070807020d241e1509111209030403080d0e070510 67
    0x307040c02e5204902c500300c14402c0e122403c0c072088400c00700895800c1080d0b0b103804501503c4240000c1c0c150300c2030040c1002d0ba803842c02d84854603280c200000544a050860341008103070306402e0030805031008142182042010300700c050010303140a80b143e00703000d00302400c001201103148084021040c0c100092100c3c000903242401e80c102c440303019065001d00180d4096070305041080c8040c0d510754450500902c40b5000d003512854003100e041c5246a85010303d4001d2007100604200303143c480c0c3d028007042e12514100388002c030303c9003000d0142992044c0306968030382082d500c0219140094218000890b03004a0800000004d40e07525080c82ca1540c1c01880e102d82c03809010801d030100c0880168140241509003405a20300f104821403a001001603a00b01046502c110204901220303441d03007180c0c034182e140c10040c0421548010203010038181c03020b148001c81c0c450411295690040e0f05c0000e00c4a002080441c0140115030040d00000d0001d01c100ca0156440e840050440a481280c02000a80d4985c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 138577958 1250 138576708 138576721
    0x711010c0e1005160b07030902060304110a08010501180e0304050303040e0a0501090c1205071e050406031d0c060c0c100507050105070c05030d15080a0605040b0a06050a0317090901030605 82
    0x140b40352103200250a02070f15090600c2e04400190b40e65842c041c0550a0100000322140d0090700140b94980e801461140d80380b070f1500d050f480360114060414041c00e590800411031300c20510685041e900110361808001e0b90300707030149014045200d001d00141c04280710008054408001030009802c0051500c0000d1506005200131200141e015100342828949210032064001f0200c0300c018000303520228041e50ba81c00705580d0743c3c0348074108142034800300d0f240514603944070025009454003a9400c3c00418002c01604036003030b0003502a00055042005030303d090b49400401400704d458080142c0308944500d000140e07501e54440109008540001210070070080e0a10415a00806a051145507800c064950356520300440381900c0c00c4540d2010400450209000c11034006c1130785c0c0c0200c0c0c1c0307010394a01d00322014080940d001c40301d003c1c254010a0001d50207006e84000e450b03010384100c00182c42c50726030004000310015045c000060030001d4078004c1e00c401d41c1d4540a1801900d01240c24140700 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 138579208 1250 138577958 138577969
    0x9050603040b19090b07050a0e0909031905190e0d1703010609050d0b1803090d0f0302160608070810050d0f02030c060708090405040606050310060305010b010c0312050711010c0e 78
    0x101c83d5502d800c888100288008892a0700403035240342050300c441002c0001d8a14150311045c00760700a500344100070200c43c000000304900e8414500c1c40e1024100341401b41c516000e5032a0303458002000d11103c9001501c6136604da001454010801c0b40d6644079502c0c2d0a40c40403800103d660809400001480f18030742159214006000640d101326285d5503c0c0c5a011025901504103440d007403916041c1150410108140e404400c030080a1050400007490f1512000080f0070080380503000d075945080e0740100100304e6401f01d4100e91100c045036541c10360b046a400c80c00400749407100400306800b1613582c13070340704a800410b845205a140e000300300c0e0042510f405980201548075480401c141c0001803c6041554001c1e41d00382d40c0442c003600d40d860184040c00c0b0540100c4e070144600c0202b50a0303190181c00c9982100c1c00b41000300f00081c0c4c007100464400c185260040c0200b130f00700010105010007580907560012941c035203140c2643c0002811401c0d0368582205000151604408042500e0103 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 138580458 1250 138579208 138579241
    0x3070807050604052103060108041103030c06061503010509040f03020106150e150a1b05012d0e150c0304240e100203070f0c0302101b0e0906091609050603040b 70
    0x60f55a101503485d00300c407040568407004150f24104211400441c0420401010007184801d008040c0c030741718100b48002e640d075a0800c030395051140035110007002c3c001c413440c804c403410b0f0b031b02c0903162412903030719516500d0b500342c1c1d100000c40c110740d43c514002800250441070b8100c289100c0d51040c41200040c01041944c003010b03c0d5190701910108442c03070010390881140c030201240200840300001d018240180140003040e42510951105901c2d100b40f91106d48041c016218820b40422840a0484000782d6038548845022840c081031000305445120401c05150700c144155600c00901c2e01101e502c4140d02503114988040c03e441e480700041c10102841440524119200c0450440c03070b203010020503080414603090b003404417050582e02410320038440101c05001c490001d000b02031081c030b4206160750380241d140e000105004171aa07601c0c41c1198400d80280801840c1c02c280b9180c0440e81d0042c1c00940c0090f60510035020000a9191225070180d0b118900440c150408d6141503001c00c00207014 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 138581708 1250 138580458 138580483
    0x121008010f06081b03030c0303010b04080708060105090604050603031306080601020106050301140106140c0109050a170307090b03070504030203011503030201230f06060d092a03020603010509090307080705060405 93
    0xd24005110804002400d1300d05002061249407030010410701007030962103240c41308015800b000002040e6100704500403c1110401d20032160f80d035644a40c05901d1740401c1c0261517000c00780d400401c00514058210903000701008040c2c80c60107218400c490020031085e0720400205024030b00b0440c2c550713020710580700104015002400b01d14452118400440e405005110a122440e200754240d0303038042050702d5408204500030040360745241041a5505e140c4241100c802541500314910085003406072806003185468040026007041000b46942e04001c06080400c1000c2c803000016a4003400b42018070450881e00310026403c50600038203690505550b6039440010000801c000300d004002c5990110003500014015114540080e610303102e52800c2d00002c40c14200c1403020301040c2c400e03490342800f000d807050081508607030b207582604020740b0000e0341c40282440100f0580c20f000c000c456000201d076007540c4c9808015990000d043e080107805840700e5012104100800004010840c0b0006 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 138582958 1250 138581708 138581711
    0x12030807110d020a080a020322090c0e09190e01060902030a0b0406150807020712030807021b0d0615030212030d0b01020313151403190f0b03060c0708121008010f 71
    0x241d900c2c4010359a50490301c0000c2112400003100f4031020310a200b9500c0c1142d0394200c0881e0102a107101004040e0140a414a000c4c54582c02005040c010480c41c0e224810142030b182c62030350340200f0b540c03644100340c4280003003540b240b2408060b20400e10139400581a40c48c001a140e040c20600d000c229211004414082e0346021010b20448500464400c40d0b040759107003401c1140c0d1403070b500320b0400c02d45522001058403550015410107070000075152040560790700302c40c280525102e040d0200d00041040301d0b0810b001c03040100c0072801c00d400ca0324148880a84480701c140d81e07030b40131445041b260511050143c00c042840302800e000c0780261809803000b403009500300032070744154000320055481030008800f041e55410b40042e010314100303500c2e0700264864548070304e04140e2051807109072080e25035109140080c050581d1003075204500c1d081c5000f40090101e503403942c40854280d44100000e84946c0b1040c00600080000c0c480070b2841400c4400012921600d041d01403400e40d45416002245503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 138584208 1250 138582958 138582973
    0xa050c0a050f12030706050106080412020c060d021e040803040f09091502090d020405040303020903010c0215150d0501020427021204020402180a030b0105010e01020a15090c1203080711 81
    0x6560314101003042d603000b181e00c0441460140412031540c415100c0c000d01032414880001140c58101941c030384202e0040344601d45030100c6c1c2804a84035224044015480f181c10300c0545001300d1a80e020304018aa03500f0891001c4800c031880ca811034000740d1003031546520008082c856644045e82c3d800017449102803d0004e4440c940d5440d6000b0451408014003036804120880540c4d88c22864145a64000e0f100b0001d605081c10028060340c01824980e002c0d40c203108180c9403d9200061981c00721845020440158a80b0501000342c110500d100c03642c0081c80240d0800403070360a20040000f0040d20344000b80001c0c80500300307040c100f030100d014a5a03910510000b1038014401d50b4055000d07604460040e03949034104c0c0c03461884c804403500350703400082e480b0b004000c004044030401c0c1650b00c2600c94090f080480401240d4450402e00000e00b071068580c0c1ca4400e100064204a01c0b451107150000007487e141e08118085090b001c406074009103001080c00b02c000c0e00841b0032812800700030007400c0751 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 138585458 1250 138584208 138584219
    0xf070207060f0c081305090411040612050312040c080d020304090b0a030f11040f02070c0302150933121807060c0314040e090703061505091f0e090a050c0a 68
    0x420380414401340c0035010000da0a152424281c0500c00a414010b081800c181040d003000080d2450100c031060007180307856000704001603c00071891095901400071441c08000d0100050075483c0030b00100c8020041c0140840c1d403000a10501d241800036074021070311540740102201c166800719003828050086030f9004d002248000020500e0190014007050b0400c900b940420f00030100d42083d10001c9101150f640101310356400648100c0e0300803100304480301c1c100d48803003000b40b207006021070b40100c24507074802a802e000076088000380c0d000580601500b00d6003c82c81d04075400500d007101d0724142d103400c0150651444e00c100a8441445c002010340c60300780364010341504100ca03c0074051001803001c20040302d01c2d2000b1140031f400500e02e0038069092002145a4404c0c0ca4001110307054103110b00c04a4000d00030018204887e80205030a0042d107860019619000021003c2e06480c2d2000c2e10101d005500e01c521a4040c02c514802440400650300704a803c0004801200703202e061800e804202 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 138586708 1250 138585458 138585467
    0xb1906030209130507150c0308090106060e1e04090b0402190302060d020c0c04020c0102040305060c0c030306010807030e0f16080a150c200c010e040506090106050d02120f070207060f 80
    0x74003102c2c1190100e0403c0060034440c2c600544c40e03116260103000e05568803805603000d5000c040c11803285d01d448826450340c3e9510f034281d9810380280400039030603044041c000d2401199101d5148080c0c0c8029502d410f47c1800f01e815988121816240030003080240811401c02240c04040016000c0b030f5001c0f03071411a40003c215124a16060688e07580202d15110351035028001c0700d043d658018800c40d500c1e80c0c0441014040d4100788000d58070703030241800044010301c840003100d00c0101c3c241e01441c5160389000040d02c1449001e400c4038201950303130f021030310640380030411641500d0642c03000380141d22500180810821803034200c115180c00c0040801c2c00190403074001d40c0352800142c80421115464a0102d520084129508050070b18640c540c891824010400c03152629007a603900c2d10780005131003030005451303081d0b5030141c0280310000100600e41c0f144016092002c0d0601c000f502d4400c421034030550484050707481c1d5098010701c0c1d061002c0180c04010860091060381031141868820000103030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 138587958 1250 138586708 138586711
    0x9150114090301060f0e01060f0203070c06050a090e1503060a0b1c0f02090a0222061d0f04060b040e0901090308011518080a14060c091e0901030b1906030209 69
    0x1030200e004500264559002c3d000b0300d001d012103282a440b1542d645903200c3c034640d4207200f204081a100700c411858548007000302c07040d103034010720ba03200200c1c83d14001b21015071018902d9002c10044840100c2c9810a030300c9028040c211032a070614044003814100b50500c00b000d080110207a1900301c408007a03444496041a010184c144826040c80700c1e420034144542c00321034009d5106001400b081010021580a040b203084041ca0480c00006180481810006640110703804201040000c20b40c6260042c80c020881e60013030107070042940e80300041400d0715856000901000d41c049014400010311041180d031040d9a10007d000c0483c441c4c070041c2a042041c0100c0032000c90000f018070a803401210220b00c007401224000450b075581e24840d58842c40004022078964540340c01c4840e142c07500207083da00400076180c03110310b0520807404100e4030168844003980014003200091901e552549801ca00a6004001c0142180740c580c0c0003205080c90304c0349040c0c0c80340c40e180041c000340e2101ca010390b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 138589208 1250 138587958 138587987
    0x11d09031e07050a05060f10060f140d060302030304092412170f0706141e01051c0c06020109290112050c040903050a17090a0204111608030402091501 66
    0x11507880d4110f050060030a0001400500309204020134821714002d5801021b229202e6400b460700d110351140d10490348010880900b400203a423042c50424800d0701c100041070541d003e8580003c130f40d03941c0d13030200e81103800680c404c4030f2155507209038500f014904a1220410600c510321101e5503400c0541858105c1007055014121050980780c18808000c00d0040341c0628160760881a1a401a0310701039000d4409841e81c1040c1d204c128020400100b09183c51054088503460941d040742c0c01c2500f8440810418010780d94584000081040032481480b040f0380a811142c0c0082624411820480d00c0014500003503441b00401c074000d4044121000051415070b0707400340e107042c14403401e41011803a0420358850326a00074a41110641010340000c014090103800d6110920806041110300d035800e6000c46181d6515008007800d0742c010310b483d034072416031b5040e40c44404d0304220318020390300340c0303044d40840480b80d4200c00414042035140c002030290340a6250383c2411040f20b0350000003404011080f402 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 138590458 1250 138589208 138589267
    0x50904150c050f070503071202030702010e090c042606010b16060506010302070519020f060408060402060c0f0303070305070215060310090602040911121806072105011d0903 76
    0x4011034031030401c89003400c42c00041070343c50316203a05051b03071aa0700c0008100c4089034400840a09a4004015101e181c2d03016141d1002a0102c0300a01150709001000b5800b00c1c0c0d01000041001d1402c03050b416106503102a11f840f03003110614541b481c03c2e00603041104600d100348000d20320545150980000d2030740c0010013260546840006078043d0040c0e4000925900856038001c0350300e09080400100140216411070030100e501040c00000c1c4110701401d66907404c60303030000d07000d801c24500a01e1603e48580885851481c1100d41604540090310054002030307c0c2c805100d601a810000200c01d0100c2c20882402c5041c440002a642c1903083e100f00d02194403080e111013030000755410703a00140300100c418403c42040d11200c69140d400880c802d2084400c58020a0740080762110140e200e00d6100c001344410744854206039001481c001324803003078034614000d00d42220002c0c0074140c000c00260340042840314003401c0b01b00c0c400200a040d04503580c0280102c08101032929040300d40881d96146 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 138591708 1250 138590458 138590471
    0x60913030f021609050702010b090907061b06020a0908070504020f0a11010e030f0a080f0601080408030a09120924050306010e060903012a0302190e01020a02090f090705090415 77
    0x7030030303400c04209181c040d50400f00c401001944860355002a48502116802041081d0340e1100304000d014090303d5502241d4000c5105100c1140101c07420714030900c00a0142c40182000e55541c0d0a9900c64420320000845d50501040122002c00c0080d0207044101c1d0294146101c5030300d00d12090180d110303403008001b0106000207080b0000c1d402004010440400c4ea903851840c45514240ba6000f011008000354800e800507410b0080702520314081c00e0165a904400d840741d40351048107400144c8010406070703462181c807000031046004500041c403c0c0d190319440da40351541900c3d00a00c0020180c01d003034007141c8000c0c0080d40c050304480e03101d5400d0030401c070185044004519a40211013aa541562901152008104080f814441070783c001d46087c8000b5807180388200c040e40a02d5030704100c3c0010000004042e07902414400350504418030440d4450314094000850b004011381d50040b94000607014444c04e00703414881080078107000c0e14100c805081540d54080c40e007000c4014808419544d01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 138592958 1250 138591708 138591737
    0xa0b0c03091b130608070830030c1303050105040308090309030a08030a06031704030507050a08070302310b0a050a030b01030204050c13140406050409030804060e010e0f010209040506091303 83
    0x300301c0102d070f0a240c1e030100056500c4e1088280d5a40d1103000362071191088442d1030112181d030a6010140030302210ba1440700c6060b80d1400111a08090010114003109104142c04041c1408234000214056000882c1600b014200075040d26006800322132903030010015000151030003c0c0c03003050b540d8801d9a607541c81c0d4450450038010003007600018010030b08418520403144015000e13000f66400b5100b640c1c0080c2d524010040407000074498445e641d0031000c07080000d45003181c036004240c070807400c42002c00ca901c0d5489103500015192056061030b076a04001d5000e05090807a90007410040d6400c8110b58250f0710382888089052100902c13a0f51100c0003c3e00b180085401d40d0514100f924020050340e0711001200c09800c002d5901c0ca015500e42140001c403841c0a0203400c103280e40544440b11962a1a11000007500c03115011100310741d01d5900001c1030a07000c005003146011000d00060f2500d00c01c1040005640703003d843d451103440034409104d041026164004003055040c00c1c1a500d045d03421 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 138594208 1250 138592958 138592969
    0x503011d1b18030c0402030f1618090203101502070e100509040308040501050a0506101b05070f14151b0a12031b020d231204050a0b0c03091b 62
    0x218200c0c07040c403000c01d4500385031941032103100d041031084054a192554080500040740401c8412990517105c60010a0003200c000100c00b224075214500440907040c1604c1c152a20780095121850b030341e0b4004100810201034103040301c09050300922003080880e182c1e5009648480b10701401c01c44403240000301d10840c00107140000200405000c51581d480c0c9800c000e13104c0442114269415400c1c0000200340c10b00600c1418441c2d00e005000c0c99403020503800807500c1001942c0440c1d040e102030039100e0080780c010401c845c0181400444503000e03608089842140250301e03103046001c2c04e02c9030711807001407080d541504c082ca81405c03020762102556082e000d03c1c1102e05540988003102c0d07000c000c0c603003d81c950000818401d284120525000b20310354100da80d2031080d078160740082e00d10b89550259000210620b81141349042c402c500f00314400b0949a070f51031007650201d40e07590100389000d0800010100381c0e5440700c4600c0701d0701d06515100c00c2c01501c2e02a0444030b40a03034200c060b944444c41d13503007 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 138595458 1250 138594208 138594241
    0x901090f0f0303021501030507120201020f1203071b0503072901030602030609011403070603020d0f15060f1404090902010318060506040b3a02130209010801060503011d 74
    0xe400418440c00d94400c103990a1507003501040d8010b00913201c41740b44884401d007201e03048941c040c2c010200189042140c00600c2c24444080303045010b1001200182c4c40100308051824a2010000d6940c0c248a0000341c0544425a0024a640820402200031400200641d190030f13802242403406455044e40351139a040403100c40050281840c030000c414002ca0340d01941c883c9005560400e4240d0301d840580885001c00c0000381d40c5940842030900c21f070351107a0080c10050b2000b840205556540000201c240c9602d5a00e800541c1d8104008010305540880c046a80710514140706000252003020514184140c1c080c400415454051003402c69200342d0048403d004040001031060080d40340c08805043c040e50098407950410000641510702414102c1c2c0345405810400112141c0c3c0391410a6042240000b409100c034070380d1400c0c00360b102c2e002d86900c036030440d480050b40c2e00840070014100d944103030000710800070244018000056040510032808281c1080c4c4e43c8166504170960494191 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 138596708 1250 138595458 138595469
    0x231902010209060708071b0528080106061814010206041b0b0d0e01050c0901020a2a12030809010203011d15271608040209071421090c01090b090109 65
    0x340000e4113070a0254120241110b0b520071103005880c0c82da081481212995580070f2039602207042117401c560602d4803400f1300050203e8803410301180b0756506455003114a01d501800100e0080075100069446403002e51001d010118101e03490120300c040001d5881200502c0101a040064441140040c0d4611100d000301204090300e50b8419404004038080c0142616032080e0798240804500841008001c2c0c0e0001c0d881a0700411100b04940c503134040c0741c80000c0103001d00700103520000401c54400e518000c05801d24804039240d1900e6403030001e0131000b0051208155901c18001031107412942d94540c29130a1380401e001d4425200d006000104803110140d903036020803100c540001d0041611480d0300c0400030780964020340c0d544e080c64150102c0c20300390917100291207034000030300601e048040d803a0400201d02d440310842d00c0d8134081e001c1650080d003480c01c22248031100f0700041c00484a40715400090540039140c07200d00c110001e0503d41e01406046a52100881c20001691042c0d412800500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 138597958 1250 138596708 138596719
    0x80c06010603021b01050603030306011812030e0123040302040504031715030c030619020a120221090f0a0b090f0a2a0b0406120e010f0507231902010209 67
    0x141d40340c0c8003600a600c00e1280600c0000aa19081c010710810322915108800207005036256a5462004440c9083c104207a40b04a140715403000c0740b01400030804800061181d02c2c0d0b908070003440340015200c02c0c0254480c802180741a0403c00040b0300c0303142602d08490741940d01048030f848924058440c0700034691b0402101d80890108841702038000d5110f104e000c0240c080e24555440c1d441810340341e01d81120710207200c29290291190700314542d8000c0a400080303140642d50a140888103005a034002034031a8070003455807440d003c008115a4915800c84035440007803c214504030086a00c83c554290090170004284000070705c047c00500c01d0342c1d012240442a6400079845160a04031b0103020400c1c40c0640003400c18604901d4074049441003030758000400503007000d00d480c004542d0b0101038440101c1035602c0f003134030403c0c5d440d090295601164440101054518115100900600c1c03200b80304444000c4410310070b40018401030840700903200c054031031401401e4100d020ba0182c4101c460720b98011 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 138599208 1250 138597958 138597961
    0xf0614090d052a01051c0e0d030203010302090a091101030b030727180201021b040b0409060207020909031c1808120f071e050304060e0106060c0b0606040e01030f080c06 74
    0x1140104070120340c0c0710200c07200c901d2000900c21820f4414007207032565001c1002009000c0b40340744c1e20b9117100c40150f0f40030408603100d904080c05034100001c4000d5203010980200040c021031401d5600290701c000105810050070b0041e4035080d480b40000e00c6035030705165480e407000b80291014001c81c40640f40101c0e01202c2280c0714840740c003420314103800440301180f6010ba9502030200d4805543c15440e0142d005112003a5424030286001c0100c04580744d01039907d00170ba0b10240c40310301416444602500b401a101e103280d0052002c0288010100c0c0556041040329140410f03c000000c4111005e80b64001400b07941802e51300c0c50100d450324041c1480d140400e180d950300016811180c440c0b844000e104803140c4410009462040b0b900c0341803080903002100082c186032096010790b40c080e004400125200e04020802404c480b115000310000075031410800007800156040c071608440151441071929107440751000d10085c0602005040d0010b4070407500500400d03c1c00d0310041c460034816034209 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 138600458 1250 138599208 138599213
    0x20d060c050c0106090b0306010611070e0709150804211106090d0f020f030415021c02010506010e06031e091c09030212062505120103050d090f0f0614090d 68
    0x19400c41d031860341080d800c4c40300104500130213004c0d5006030300d005002000a42d00b010400e640c4e207030209001c0205807040700c1c0001003501c0700d48212800785030396880700c25800e410b0060b48804114440d40d20014003807450b040c400021f02080540e0008000c0806c040303c0861421801c6986040341c40340482140306250502ca2101008101d222450300346469800107107294001c16a2141d4211305aa48190002d000c20481e040b8001004000c2811034415200381000501000003580e905450010050707540e0700410195507003003010040344040c00c503a02400c2d8a0b100c02c000000c00c0c680341e0342e40034000380140800c03100401042420004e8106601130300f69915524001021054544002d030b2054000b80811500440e0201e900d5005607628903600c0c018020f0001c0040300f545e0300c050044200030303080000c0864102d483c0c0400d40030707500c214003918240340c0c00a070080c55403809401100c840180807408020f4140801158000c80c1c00504069540d02c0444602000c103010701600c1c1c0350806015048030b801c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 138601708 1250 138600458 138600467
    0xa0513021e221809020406030209100920090d020307031a0a0b010327170708030109060506090117100509011202090a0501050f0105130305010e030310050f1507020d060c 74
    0x50310b0000c1da003600c01c10300c01c0c100801c1020aa4422045000021802c0e10240d0403d900000c5005001400c040303015692540420000e40c0200c84800302d00c2907240c410700a1840c240102070074124940081d9000c0406000060307000d108a6000e03510640185400b9811034400384444c00007150884141d5400110304021042d5030002264802c00007490418621070300e6010780b06405480008000c0055000c841682035581c00038214426076041d110b800c0c00710500d2001c08010004c5500c9007100507200c0d4500f92803d03041e44c6168000c80d200b0841031101c100c6030f0340c0c40f040700d186003503e0030708148154a07040f031441c90704070381908200d8024174110300100d1100604003420b214540300303a0307016040d40e880181420888400313000e03082d40300c064443c200c0655881000031700a9a485144403403801a5642d44440c01c40b42402003014040e0000f00401400c0810b0702d014030000d1500f84c80e08502e0000b10300001d9011b10341540001c4180341c2c041280302c199102e1709440080d10ba44440c6c00c102446402a0240 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 138602958 1250 138601708 138601717
    0x70c21030305010806010e041104090204150303090b19050a1b030305040201020607080c0306220c02010c0809070b0909090307020405150f04060b1806190c0201120b0a0513021e 77
    0x1000700c0d05003000025151400113006040750b00b00810302000340c4072a50760450020006480070f902a03114801c8401590305c9114402c14080b410006103952443e51070701400b10f2078182d000b8000306106010f05a10510032100030000d440291034416941c018864041d10704500c00104440c02c1072400c140da4080640507030103903001c1e0b03000f40c00b10781d01d5513205241221584811600070408600030f1002c5092400e20380c13501400e80c0b4108212441c0710008101c4d400c11580e0031046400140e440380d00d40795225400c10640707900484040045d07d60320307060400c5211203100b0302c1042402410b4030400129100d00510544030816070007001808907081c031620000003280c18428191040f001040c2145a51420740300e04400c407042c90914501300170300101007200012086048d15044403080159900000407135512072480318403519203d400d00c82900006201c0382c014000160b03070500d0208891b4440e070701c00b0000000c44104441141620b000e00d6003910180c02038600e03480c0c084180da000b0030f00c252030b0720000c0c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 138604208 1250 138602958 138602963
    0x60a17030d0f09021012110309031207020d170606041214060105010302070b061e09040311010506060408190203032217030a050423130209010906020105100902070c21 73
    0x5100c001a95034048040b215041002580440c4543d201110940200c0f0510399585808400187c0c1c200d038102038000907402203600d030f402a040013903074041d00c4080785506500b003001480105141900b00310080d203c40c900384404070b101500e80000400302c1d620103040300d028080800840c0100313001071030f1014102c100e03544007003510700075800045000e5101313109039000c1581013001038030207842c0d02c41405040b040e03a6103440e0391500190f40c1e6a1040d03d403050110301440c803903515112282210170055084400250034070b4420701c5d08010030031000b80d00181c01c0415044001145852070781a1002910b144101c8070002001040b4066014081081c1c0002200f00e0300c500399640010700003010140d8403072150342e80705008180103000510003920142c6007059141001c210209603201d0450005200084030342603d010300b6000201c103229541d00000355001400c440c002408141051000c0888221003400f4140a203a0b02080003805e100469050308010400e427840248040d0700040c0c81c00342d030a00d1400a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 138605458 1250 138604208 138604211
    0x3120a0c11010f142d0409050a09080301030809010e0a080c03210a05130506042304050103030516020d06060b03010807060203030601020c040c050706051f0501050f07030503060a17030d 81
    0x80c1d400365024000c01401140c40e551103142051150b140c0000075045032600c041440c07101001c4142400031070310b080500300c1d050311805481e940341610240c165400100001601c90400c081103001480842c1a030f0f054903800072370170391152910801211000718501041d41e0001c030480d000038100d03801190207291720100303505480c14100158401d06510440980d20820448204800d003082c0344034101810030b40b5a140c05049440c0e030380320006580742d0001c2e001040075141405d03958801881035014100d040d1415941406958915140076100380a540100e1020b0020812501e085544108010000690100c820020140c40e000d00510a400034014003103144581d5401081850000042d01e200d00c50580c028a0501c500409000250164000280900c8002d2014800241441c01110b1183c2900142c542c5810f0040e406801910843c4d07100a040c00b034104028151040741000b2170714201d4041c141140d9070b0b200c42c0003140c0101c1041d03018a01c400d8001640b1a9510340200082240c040c40610 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 138606708 1250 138605458 138605483
    0x20a080418230601230904240308030f070e0a0608071206290403110112020d0e011a0a061706180901050a1505010203030f0a0b13140109060f09050603120a0c 69
    0x401740c001c884c81c17002d481c591002c1484055541e1409812190022849003150303910141b4440400b031882c0541d820440304024003008000050310007190303aa500036000e250151050f030058003c500700c000c46000324020845001c000440c0d150050320005070428003000c040060a94038072800d496880c0424100d101d500e01007103c4a940c42d403800c1a24141d940002a500c0c2600440c00150340400380000544c3d0f1254007031208100c6801944642c0c0d030101a10b4001064501994010058240038901c2d130074418030f1462405d11240d075201c1601703580f100d1004403180050b01c81c14000b498030030401c50700000400c00b000800070b0150041d0891350044040c50028040b4030521510140d01da86c00340615401039105000207461020580140c42c1c00001c00c520005034840101c020840c1842d1281c0001ca99a8403000c1a00e400400100c030309005251283c1d003040b23107500b8a080c13003280d4000da12803044029200d601080c850740c9c003032081c030005042c4403107074583e540304d061000b401001040d2001d884408a501 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 138607958 1250 138606708 138606737
    0x5041802130e0a0807050d080f100b0924040303110303060607060914160501080f010b040b07030311031905060108310b0a06080d020a080418230601 65
    0x801000015600a0200000d02911090300d002084901c07008000c9104101c807401c040341c113210080400f00e000d50003a0810501c1010041d01d0b8890140000f540301c1d0424040104c181c40ca444020305450180c001c0a030303990007407800102c070f0028007034460643c07001903801a40405550070040c02100d00c2a211040000c54803080c69441b40000c4035074a800040410600b00015940e50005400504c40c0919240106540c4400c0e8034003640c81441c0c0a48010201c0d084c4010368000d010107602c0720b0280346010f0a903052465880890060f44207080d4504808a2003604050003030300700900b107021040c41c036030700c0749007140000c464001011070300c004043c5000042507039544510305861003008211051125203141c1d5528500301c4441c01c1c0c0700820071002066170700000710500d41c1d00d405958815000700d07007542040c0815042c203c40f4a070500a40d0b00000d08070002495040c00c0e10100c1e51200020302e070300c03090101a4000341483e408507030607400d2800b8154106403240820030b40a11002c0c0e0b150505031403000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 138609208 1250 138607958 138607991
    0x6030603050a11060c01060305010b12060105030a0201050c0307080315100c02090403120204030c2d0e060d06060b0703020d030b0102031201092a0302040602010c0c08030a2012010504 80
    0x240030240054000c400380034049111120110301e0544003600040c5003102941401d070858035150000c030b0700c0c1d035150800c2c84554a0004041e1619100c040041e0005500d840000782e030350242108024180140410f10340c1d0181020b100b036403400d54100690942d2454070b250000c00d1003000d995140e1140720740ea040b042c4124030a40da11241d071980508401d5050311540c80a50341e14580b1810342585c80e80070003012000402e042c10311002041c0c0a8000003210032446072507244000781101e403004883d20584c041003401e408030b0159800030000c1c0e038010708001c11406c01c10007515081c1c004c071008441c00611041003603400113580040c0134855a007002a08441c500490302c030b21510424030400941c0178018030510015030f024102c290f44480d0869101c001400540b10b181500c84c88200102e6400716040041c50340a0250780340104a40c42d001c43c50000d90703500c40c1103500028180c101f20b26038442141047d014a8582803200e00703020b5102540b21072581c0c4011000b984240a1140106d04280c10034030100303100d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 138610458 1250 138609208 138609221
    0x11106011424031306020906040b07020a1703040320090414070807080714030307020d08040e0108011407080a060308040b041811070b0408210a18020306061203040314160603 76
    0xb489080b519580b80e02c04882c1240b003400c1001da41083e420007070404141e0b03401005200a024900505403288603d004000c2d0140345688810401c0d03041d0300c07003000c0600c004000c640c2900d6004200743d00305059042102c4210340807006070ba40101c66201030000b803103ea04068001020140112807406844001c0241c40705098800d4006c141d200840034005402039170802c40344c48a02904881c14220b2a13000224204180082a6504500002c084c003001c18038205d940d01425210703000303000120a40c0c8180801150090864041054401c04503042da0210b0704100019900482131944550301c400e400603a6038880d101e8140c4000c006580100200981d00441c140d0048000e0504e0030005240c48501840800820454030705808110f06250003407100000c0108001c9070004038800e18151841c1d0048130305110302590300740b030400c65140040c5c1d00050490780c8600207a034039048046000030468614021900020281d04003d05480f40f141b100042031003450095102c2d01c588155030f040c0903002c41c0c10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 138611708 1250 138610458 138610519
    0x4080a0c170904150e190e03040b070c081212040206070f29010e01050d08040b0409021b0c0904110402040503030d0c02070b030f0a1a0303070614060f03030301090b0111060114 77
    0x4280064a240c00c82143c0c03690307221b00f4910102c3d40518240c0c01c3c03804c3d03038007540084900c4100498a18180010000c102001c2c081d140d00601c000d0390000f42c80b101c5d0340114500310790300b1001e000024007103407580d8003562099039000c1c1d00f020000e91245003031140801d03080030203012204e02e0803c018040d06d044010604039110700e624410141d00300024047c5a0310b500c2c40548580804120004200d41180010700080110000c01a00c84079403901c40710300c0c03102e108004860741c0e1125141e40f00c04d03654041c0c5070760030a50004c0d00021400051011034041d006980c4240c0d45800080303401103d22010f0740144101d0003041e800c0d1007802d0f454a1480340640030907198001072890a00000701895400e601c01d0b000d0442680485540000410000e071070b55202d104100c81d0507441c0d00041d002c00110b42a450b4004a040300e030b0448035000d2001190ba40d02052245e00d4000d600c51041c1c04040c2d00407100690398183c6c08094030345968552582c982400d00407c0210700400107100d404800e00340c4001241d41140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 138612958 1250 138611708 138611729
    0x6040e011a04020c070e01121203020f030a0c030e01020a090807060207081203040302070e180c0a08030d02030a0609020708031e0f06010f020f06160207050f0102030304080a0c17090415 81
    0x90240742404001c0d0004002c0003424802c0c0180414800c0202032058001d202c1d45d42ca1045400c4507140040140780c9065281d001e050062050184051061069a502101d00000042c05540710034044014006a0114040e01c0d4030016103545402c2e845802c035001d649542003260b1b01a6550701080345c4e919418170854043c2c1d003000107400c3c22610180002d51700075009204442c412500c0340303224810010152610702d403414101c0c4c648090380343e050000c00080c1c141140c148003114a0b00c20b5554491140500040403280d0000001d89110055403044e0040d1018880c2152140414030b48080030340d0003501c031b0034802d2040c0c908410b42c0c82e00c0e04d10482e1058240101c07003d015118040103503510711003204041c0c150300995030798859221080100300c2c0f203141d40e15030450081503100f01c064102440e907084240110040c04054911340d07000411030ba003141d4080304556030380460b61700c02c07228149001d100a020004d9001d6181400c01450302610208100b11010020b01031301d5411482220300c10700c2560103c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 138614208 1250 138612958 138613001
    0x30c0f030c1a03040b10050913031b0803130305130f05090903030606040302090c12070206072d0531030201030b24090d080c0a0b070f08060d020a03061406040e01 71
    0x700c251944035004611032164044158587c0000b0703030b480b1800c54200c89600360340030143c4141035200150541400c43c200d4200c0c05401c00352200c240c503120040c0301c921800c0c8151342c8403080520072800c851814030400c2e482442241ca500d00b0f0010307030916101ea58400c2c507518011920001001c0220b80c000c0300b0003082130385414955030034000c1c040c20003014181040014800f207460302d6841c0314031030310513461035010303040c0e0b8541240b0240201481414850364140b80302e030141e5186078142d101503072642c1207003002500d404803060400c2c3e0042e00c0d10700c4800000640903001666014200c14441500e2007600c007804010026414400385066414409050401c1090010704494041c0c0007442c1d03400001c2d01e0540b20701000d4035103d40e0360780150a80c41d595480007080c0ca062000c43d100b556046902403429800c0b0352443c86c8010034080340130301030a01c10505044a5030442d61070010200003141d000c03000340030307458801e6001208a00304170f0b0814011828506098000c800600c600c01d601c10115001038080e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 138615458 1250 138614208 138614213
    0xb0603011b0518010504080105070e030f0d080a2c070e3103030209180a050c030f160905150a02070f0605120c0405040e0a1502040302090606090307030c0f030c1a0304 73
    0x10621141075203414030100f0080400d580301f00b0700541740b04003000e0f1a0b0208080d0381c1c0c8140340ca840203070145c0c054039400c20007450243c1c41d40000b2154100d24060804640b0105c80b03901120300314240b294807403211b9400c40c070706000e0003000300b950b508075150b021b081d41d2903075a034201421580041070823403075020032021490f0361141181c0485410f510b010345401801d000780d40001c1048108503100c801050550b070030030000380111a006155020014601090031b500345036082c1800701c0d0f80a00940e0102200d0b020a0000300d2050301076500500e0028803030341e400c48540d0007064140d84049200b0005001d24000880c070450003240a6048500d1030b55414035112034400f241e0410307800034101c070104203020030000403103076103038060324035090f00c418040e00a03040685031240d600014001448000c03401800104096a5601d01c4a54005015110580d0741e5207244002070400e0344940000300b20200601e03000c194807800c080280c003900c0c46001c101c0c0c816503e0310f200c0c406030003614200d44107500c01040002c00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 138616708 1250 138615458 138615487
    0x5070f0516110909100506060403080405120c040f020304030e100f050a0210090c0816050603010b07080c0109110a0e010803040506090607061425390b0603011b05 71
    0x14114011181050a5400800010036404095132040d07142e0b84504040d25040c642841295004082107881900d058911358812134580914820107105c0d0080113050a42e214051122050021005204000070100800d5200c000c2d0400d450079000500002400c103401d08001c000d13004511429103550182c10b00301d5808891580c822015441107009512035122041d0490081d403060f2032040e1541e41d0b41c80e0030107141514100721000d444659112440003080725446590840303040d103151418050382c400747c80c10844d00314460b00e4105280c6600e003aa403003042c04030700030603c600140c0440e0542c3c050741ea04c0781e080c080e4480a004010b0300da00100020841450001d000f002841e40252501d4100600b039140d020840b41c0300f4800d44c6450864804105080b892844221110030b0b41c1c4592002500708400014900c40490010010007050000380e06450080d4141d03200035806244864002d20b40c0724601500c621030b040d100b50380a0f41c20064904c00202204030382c04030386101991010f007410030350710a212 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 138617958 1250 138616708 138616747
    0x411040e0109020603010b0406030b010503010b0712170405070509010909021c052104151103091302041203020106050f030601030330060603050613060605091e120604050105070f05 79
    0x5039590380e06520380060b02c1d140c020358000d240c5480410b4465242c018081c091390b86080085040007000c10041c07001225440654901c0b5402002c082e801f0581d84100781c0381002c40d062001d40c0c0700c03140410401005800140350b0182c170802d88001c10503076601e43d9400140c65004000a42c044114010408800d50441050029030b00940403680c18060841c01c0c100100f00000c01c0c1001540001014031009411740c8281c9100c85441c680b0224003100e10b51826102c3c012080d11074401e56500c2d5440900d05500d070162030281c80b1b142d03c2890070345403915020b4001c0280c0d00c6030301c0c0036105d80d030380b2120399141c0810038034100c0307402d0740700c0542c680d24154032003850041640c4541500d0703038091031a0312210389500c112000f130211034500240c1c03410326504101510300140c2d00003071241d003400800c1c0140c950140c00c0e070700e06100c1a11106401c00c20b482e0040040014010000c2d0003005001e5036096801c00018a280642d008000070816500c1d070309402c5400700140a403440c0820001c20403000c81078030240204 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 138619208 1250 138617958 138617981
    0x110301061d1c03020607110d2f0d05131202090c07050313030b01050319030e010f0c0212150f01030b01060e0402121f06030204080a060e0708100207060b0603041104 72
    0x2c0b10b070340c8400c4a80c0301102a0600a6006921840030001c046410403040140c10008100a10070182c90150043c0800d04a00ba40c2035a5444018a000119644500d9600c50039802007610784074284048024022341000302100700c54580400e00080399403918180745001a0043d00c0088984d031903c00980f1694001e010440701072104100d242a1401c207040008040c41c0f04e000e2080d50380d40f40c007080502d06100010124003008848081303800007604060020300c561000c0c00c09440d0200d005806544102490b03034040d40144045541350068840401c980c5d2800c0010300c3c1510b0180c84080d1a01030880090000404c1d541c000d02c0140035003406054280c076142d030014000361611048612102c070086003641c0f00c4c480707400c4001400c1c01ca5403031070a00750050809031801b141410b1415407181d9550b00c0403c00940620b5403810f4280a280c0b00b40000e0001d000c04d5021204c00480d0312000b20000e5110640a4542d1440d0840d0340c561880c08100b01c2c2d000b160004200d030805c241c00820440200b4001150 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 138620458 1250 138619208 138619219
    0x2d0809010503070c1401020d06081c030b1210020c1204030b0f040c1502100b04200903030705030a02030901120603030e010e190b0306041a090a051512010b0103110301061d 75
    0x130000095010b40795000f050284034000f50b195140f02d50907000f0384559410015240d00080ca864008242e44030418100180720319010480f4800300c400f1921202001c0042e03074160142c070050b4013a21515800401004807003200f01c0e030920081071416981c40c062400014900700560740450a03800e486205d003504640280c078006a080d0381c41481480c8159040b2440c03015030401c10141c290241d5174070a0038500d03002510240080711a07030901002194a110b828105030130041080c01d1642c074100240c07181950f020742200e58544c85140080e5403600310083c100c2c0040c500404000c1c0e00007250182d40c00f1a07516407501c9058182c1500190780c10b40c0c100f84890b400c80b0000c1303030921168500380d079003400408501e480c0c03030750364203000040c0019144c500c1c2c0078195201d45114050350580711055825804952603c00040f02c1e190403001c5040710b415800d0241e840242124451402351041d406501450400d07201003140c4950b4241c04145800244035400108010b400001c0940b02030481010440000030034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 138621708 1250 138620458 138620477
    0x303052d0a0b010801050312211f0801140c03090114010f0609050d030503060d050705100e030d1e12060e010303030e061302210f0a2d080901050307 65
    0x1052154014214803040d484450005118074680756209000d842d100a180c403074101d6041c6004680d940000d0381c005295000c002a100178903408803040004004c0502e503422005003000302c1031a600310b01217500880c00404023800099108414814950301404a10341d0311031039515481c5a03c0641c000070581183e9540f03402e2400304030151304090602070b000d6103d840e20f0840c10003900408074007007904154011005481c0c4075010036007000c1540e5000904482800f800700d42450501c1c20704040d07074021600007500d0340074071480642250b10300804107010750483c0c07440c6011000449521304801038a6002d58100d0380d05441c20b41c0300b080c541403a0408200003080f0943c1e142004810301000341c0c8140c0020340d444604210010f4140200c54204005003010060070909400042e13012a5045034074804405a545000b042c0c0c0050010918913010038003603076003802c05420400d0a4603810603a0a05100d9106040080360803c511071100c0550003114040c01e00042000640d019803000d0241414890040e4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 138622958 1250 138621708 138621751
    0x21804020f091f0e07020d05090607020f0a08060a0219051201140a031401050402010f14160f060c0c0201091a070b04140a0c091a090402040914030f1201081207030305 73
    0x403d1000140070982400d0b06510305018024142407079801500e0800c82c080000020607038906041d5440c017501210003841b45c0f20341500003004424503a102901a018081c00c02c00d00c8201c0360302414413220000e00281c042074540108a620b4403a00200c036103000007880040c40100c51403041124400d6000d00b6004031192261120011900800071144c5543e445104110455a102c1c0d00a100302d456421720300290360002c00c000b0b075203024078000f81d01c02d4070103e98001c0921240710032040850342c00c01c1c410406803111a000400541d0b80c41010b0780410740c03800340040d483c40940d119100003a4860350702d42c100b807038990746c48010b130700094011b035443d08807038003000d002c03035401c0c03101d460564802d448803035a06240020b01826158064030310019441420750750355503900c80d0810568420b9040b240014155903a140038010b0550b004004100ca20001c50f041c110981418001c2c050f0443c404110303081a0790381c1c400f0a42c0e0313080000400401c3c010a03c000000640a600510340041e540844881c51326001c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 138624208 1250 138622958 138623011
    0x31509010b280b07030f050309010f060b1e0a0203090904050c03010e060f0a150303050c070f09090506090708030a050307170c03191b0e030718020403021804020f09 72
    0x74540680d02d4542640d01d0200400800c540300108145008142441d040b501e0103024640b6000740342d0188003002000485150080d0f03c050b01307a5498110800c50903846134161106a0094205407003541040c401600c0a0b00ca524241d9040c504154000e614100484050140c4400040c00490701403003828000c1141d59400c0c01125149803407440100100d203410750803c2803003140500380c0203050380b901c003e9100d0242d0034020b28040e240c060400d03030f0365000700f05200c604e0160541e00031181910080008181c039026500b042c00d18501440482b0300f00e464030f400407074481038140700d5103046038000c001d24a6464000d0005e55403102490405400c4088540d407071045950f400c42c0d900d04142c000108000920f8a80e140c0303e4440007030700c001000301400305561100c809448005903414005001c02d900e18980d800c1141c2c2000c1d041d00f007440c00c42010251603010194216005c201e00ca1321103001d410000010030400395106603002002c03004800241c105101e41e0b0701d4054090315055001c00e10020242156 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 138625458 1250 138624208 138624229
    0x5091e0105040b1203210a05040b04020d020d060c0504060f020102040807050108040203100608160905070f050d06050607060906053409080303071e050c070b030c04050d0f0303110405031509010b 85
    0x12007400082c1c041b488000c10149400040841403161704e80000d1001081503000e055a120b507056030301c00044121800016912441d0410041103181050183d050050f88403000e44104c410325103801800d02c00066040e0300b40c0c0511b000e81210340c0c0c003001c0c0801441d80718071101500180042c064440743e2082c60300303036025201e4941090580e0391140c00d25020590901a103000241040c80e401c000500342003030020b00034070058840404018010038500380c102c1c00d9600c500c1c000c0800506d01a039640452410f5806402d48007419107100307150a00054118031020311011440c04c081160b464401c8000c450700700d918202081c040200541c2540200301c03044108000d6016206613252240502001d1802d42102103d4603148410400107000090321a0b00018503034060755410400103403260b6508046081034003a980c08240e00021043c2c115042c44603440115485c50b01a5034140406c14001c1d4030031150b4422842110380562002131a11110316880d68800c0e04003040c030001041e11028070001170b418500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 138626708 1250 138625458 138625477
    0x50405030f0307150b010e01030e0102040f0e090f0303060907050703020c060d020c062a1608070c03110f010f11011119030e010b030a0308070c1b05091e0105040b1203 73
    0xa011010b00251036403081401480d07410605c840c1d03410307800080061070380d4011203043c1070300c500c04c9081e011000e40588002c1d01a0405051041e682c07104a05502c41c0c09480c0c1004a00410f2a88003e074403000c4201c91140c82c014009400780e0b190040104e0f00366100300016000c500500d0780104042d0340c1c44004010464180c40c0142c0c95004803003c07a41850006040403c07001e2802c1000802c10314081035422040343c12070610780d1914a00851040160003806004103901c01c000791084c10809903428240c207880c0100300030b5403023031081c0041c0b05c1c00d10106034502d8041030b040880300341c4840c80381a0040e854502d1b00004500c840911403454401d0b000040c100c20003504ac1d081e40b400c1c10340e141c484e44030540f540e400207000040003e00840d8440a003035601500300401c620029021f5405450600314455000854280710b1043c0305054600040300c2c029684031301082804201d1200030310004071f009648680b04108140d10380030400c0001c0502c0d240c403c0d00104400000300d11960b052000d00714116 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 138627958 1250 138626708 138626713
    0x605010903021302131203031a0306240d05010e061e0105060c030c16140108010e0c0304080c0609062d0c090310140403081305100225060b0120060f0601050405030f 72
    0x4c2c0f6001d425030f58852068009c08035621020341e050340d030005816070801e0340c0c0c10300e8140342c41c0c8004640183d20b5090b08843e41080341d0f50100000c02205600584003691420190395040d200c07040503440f446054419481451540e078010b015910b441401070181c0264681180d1034200285600c9041100100d048270380c42641d440308020303a221003040741c00c90720070074a080105076040c9945410304000140c4510a080d402000090800005a040750b41d80b03103007a0100ca205243c02c01916036509001c07643c2190b180e0020007503244404683c400e0341580801c840030540d07203641388141c40890340c005861556141c840e00c069404600340d944a803e0640910561080d0180b80c5428003500c00e42d0040c2440c0c800c20f1f1081100740100d1004951700c80741720134802025940f90390f0318200c0d01040a45601d0281c22102011400c400c2280640c0f10a00003442070329010307044c0c09440542062001070070004020b5410110000c1c1e60600700a115507440801414000d0030039454601184c074000704160310301c5240d0f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 138629208 1250 138627958 138627989
    0x906130e070302041b080103081605060a05040c05010503011401030509071203080f070203030c12060310110a02010c1b03081e0106090801200702010c0f06150306050a060501090302130213 82
    0x141031601031541740d113105290950f981c10906100a040b860148030180114201280312100c810075000d600c141c16411004650140c20600324220003080140c8088035400c2e51800c000520f940075000b928121504901c1040c000c01150006401070304009000700b5040c0140500403401d890300840f4030034503078041c0c1e84e294034a14001c0f503000c5030044040c0c100001e650080c810006049800c0d02124814208890b4800b09519800c000c20310701028003903401c4241e0306003410b5104003240100501180491540207004040c04180c0540b1000e540703401c0684802c05c02200207004c203005100e055041001c42c151103190b06c1c94040d01410140007070700040000703502c5100400c00e070740d024040c80300c07140c0101c81c081135406242e500c1e5407024030666100038103101e2001160706c180861051981c10041e0091400e02880002649058a4594a000031181ca0f441c10380031662041592040400303841c01a12000200c90031034081020f0004588030803d8816001c000070318048811001c0140108401c500c803401c00c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 138630458 1250 138629208 138629213
    0x80106060c0c05032b0203040e04061e060302060d0e0f0d170702030306010207210c0e060a0906031509231c11210c0106120b01050a0b090906130e0703 66
    0xb818265101c24030a5115150805950000d088025400d0b80c0860001da902064228168254002d5a0050200100b61390421060040c01c6c1c100540710342071500c0d04070078862407035030303110888180340006500b01e401800b81d010160170300c1c0e12409004a0310421a50111229a0038170720317201d07400313881c9000200d0f400031f202d03411100e1041c4281c00452500156041d4904200000d555810350312030641d025025108040c12034840141c10583d0780e42040b49900e17840d0b1200401110f40c074080d141107000744101a00001c4000261107014140d903480030007a00b0b0446c90380390f004003a229000045c0d07042c103000788041d81c514403030480d102e40c03003c1c0341c102501c14442c5040460b0f081d40301c510015418070114100d00003007458081070301e14107078200c9030800e005803800c40c40c0c0b40d2150143d800054065840d040020409031051201900424270502400030b05a88a80502c0000c4070036108510004105008403189480d00c0c104103a8403103030262031301400c6035500c040c440036a9840c44c07040c0715a400001b0306100317 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 138631708 1250 138630458 138630473
    0xc10150807060c1106030601030b030a1b060918091106031005030705040506060d0c120e0625050a0309080702090a0506131503033203100609030c1806080106060c 71
    0xc0c08207040511030264507072039413210360f1095840341e4840c900010002c1c009a0280e03000845500c0064111041540d1a10300506120f120303100072494544010170009400740b203003040c03d0595140ea81401c10103900c105216000d0318034014210340312141d80300c000105440d014051031040c440901c0b060100b170700d00018941000a03d801c498061420001001241d49418040b10070381e411114001408507000c100c129203589161680407503031400c006172104c00c0407002480310300818524200910300368001e481611036084a9100d1340c0441d00501c2401d480307038040d500014039603000b070783d0152a00495134001131102604490301d14019070b4480c14000241401d13010b10300740c04001c0200300480902e41400c080014070500c002030420003609102070300104110094445007203416001002086015208a4181c00c100d801c8d154010a0b50350024600f4031500e0200e04890300807a08100090400c1a1051280b1180c030711408110345451000a80010074400c8a004284a50301c4200000451401c4e04 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 138632958 1250 138631708 138631723
    0x2604030605060904080f030a0902030f010b01030b03030a14130b0d0606030506121b0d39180504050109050f0102040911030910050916080601090f020c0c04020c101508 73
    0x50041c0c00f01400c0000242c00030741100c0790818030050707540d1255544a189005011103000080d05800350104083c071264054000d9603840100362814005245081c1c18181d990207482210b000180c0b160301d00202e00d03456078008003041d0f07010005010400b5142c2743c44404d158050108048800e5581200300141c0e58940301d27260f00130604589540c80080585841607a4445880c48004d000c13039030f000b49c030715940d841d0286220610fa0001326000701c150180c090350b51800142c0c066510445c59941034001c0214001e0a07c4180e074050404041500900d4040308014400144116255944c0b0810b00740072680030881100c440e01c0d0100096030751400c0400b140261000781c2c445a484007000d10520000c6d8201055101c0d10384075403034001915540302e0000070f160541544907250019092200400e00701808550903040c4d40420a081c020704020b200750000700d03c5174225918690300001c801915a140c80d4000f0004401d4500c100e600582081015034201e40c5d210141c905460744503881000071a01c02d00081 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 138634208 1250 138632958 138632971
    0x90a171903020a140f0412050c030c090c0412021809070f0609030206090409030302091306230d150608010c020f070504090b0f0a0204030b040b0402030c1215042604030605 75
    0xb03500340f820b035031005000441c2c84075640301c0c2c186005c9010b194183c40303003095800502e03494803010040d4205060154a400217005080c1c02070003204450015401c0c030540240c001e600d50301445140500e881c500864200400d4401c917800088141d880c442801920015402203000c80023824207546000c400d0209151664840400e00646507020030150781c50405888480c4025100400c100b8540d03e001c60007840782c1440c5640c090b144c50251250351580d5413058040da1840f81d8500c80c2c090078180b07025005603070740e00b0155005841080701e40001e840d00c00c640327031a07881242020032a01e4641c0d20882c00d60b01e80504410060b0b0000400390b00e190410443e000040805071410003004245403215100c00f40010504407412100501113400504660304603801540c0181c81880241003c0c074050400c1c42c410789060740b00303104030185c0e401e10f803030300600410894080310300410400c1010080d840480a00905c00d0325100c0c41680b40c4070501c180b42c0c1100d0f156840b03100280d90b407503045103400001c0340c1011740203 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 138635458 1250 138634208 138634211
    0x18050907020304061b0503041e0506030411040207030315090903020c1206060d11030601060305010e0907150c06060512030408070b040602070b072121050402100305090a171903 77
    0x340082180c01204031000e540f114984000600d01c00f40f1024000780720100b00418601c800500064104540d82c80941c4554200880c044800c1e0b0380e2041007024003082e107000d041c40c0121601d12140e481c0940c01840502e20a040100d1443c18400e1115580c2e001d5601602041340c54549000805505100c441e1424000300e031004a900c1e600c1d40d0f62a41c0310001851076005500000b005418801c0343c2d2542c42403498020704540c025a19520f005010b00828441e034a0035058050104500d10320201341c400c04d940707000640007014221070000b280d115011020658902c0d599090106058a41881c4c80300c10743e420000440d030381d52a1000652a10388650320081c4208002e00c000d01809502141c24012030303e2040700c2a407103050314281a955040700312080c52410f00710340324002c070464009080100c9601054020749210300460000c034152002150300a5211030441ca4a008081c041d42c08a50000c101400721010541556500e034070180300103000d400d040101054484225600e10b00c26091907042c0d180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 138636708 1250 138635458 138635461
    0x5061305070c06140924070c140106030804090b0d03020604060b0a0801021611030613150e030c0a03031107020607022e17010f030f02120c0402070c1a040e0a020705120a180509 77
    0xc1c207200e0018040c000c0d804001e1240031800511050414a08482720944001c2100c0c0740c0d00e1415020320340c00303880340180c01401e10740e450410385003201e0b50b0000c854240e0007800b0b01d656207586240080101001d00f41d840701c80d0190100300244248058000c409030607000f810124a1030030000c01c0418145013244c03080d48844100080320714030006101e0915885052002003400300c0589101400c0e20740024031203444045181202d1031300010300130741d185000c0e890400803000e2000048001c0c0c80f1f0400083d4100c43c040201c14014104806803421040701000600540f05500c40e40c00c0d19045648640c100180d66101035105509502a2150050401e44506120b0710b25640d00c699000122a40283c42085c03220700f110100c080a0140303a40000f8000d108554a550510380443c45284d030380204140604a11a4441909900012074054900c078050041d119034a10b200000650312007401180c1c04c0c05144083d04040006030080e2004c40c001e40c41d00c07914000001c00710700340e181c0c581c1e00991042c8440b10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 138637958 1250 138636708 138636763
    0xa020403051e100c02010c0801050316050603100b04060c0c23090a0b12030c0601090e0606060c0703020901030303020909070f1d2407051005061305070c061409 70
    0x100e4205031000310a903251045400780226043c801d02010f001c48031814140040d60065045d888a0700c01001510f46051b940d8a84040c50f580e00c0030050202421040a81c062041d0700e41180515031242203a4440d00641c1c2d1646c240d070340c0c01d401c076601000114181c580c3ca1002c00c98486001030192000300f17040f580c8330007440303000710140300c80c841b0300f074090304648011600340c02d010b420407844018058a1401e8403114501600c0e0350740c1c40b043d20006035016640020811204a02845003405100801041143c490200f0801647d10000242040b881400000070050307ca824190b07000714043e4600588030341c1090700f800305040c4003c0a0500300050f468040392459000342e00c003a6841100340300b080e249030083d80403440440107000d05000e40481d8000e18070510304014004e00186114000751844200d901c000c440903503400743c481c2d59020b0351207594992052840e130f1140390300000d40c1c9441c03004810f69442d01012181404801e010120003d4100107150300b04014403072f1402074005040c4001d10116 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 138639208 1250 138637958 138637963
    0x108030f0f07081611040c0c0b150109150e011103092103040e0a02070c0503150f19050411120705010e06030627010302150301150e0316080102070b0a02040305 70
    0x101c400315115004074280040c0640c15041d038102c0c5042c50f006000c842218207003c40900007905103548218280005441240d1143c400e00354502c1d48040d902c5140d441d40408090441c040540542c10802e041c0000203203269038080e10005c2501a071501004200e801c400105401c003a04003403089580304001901054850104040c2d44000070341e50341c0709803c0b95000d4641075118540c01074140310120011f0214817620b0f54020046503102d507140e0ba5596999409050302d841910312a1200540d03d580000c8a60b66803041d00c6900422003000ba0f1840c440c040003010403100c00f81c5050300c0d01d09030708951424074241110b8141c5403888550041ca0402d18120000b000b00300441c00185c0144800301c0841e80e245c41e03441510100c1e42c1950003480c0a900000308400c1c2e43c800902c026489000d03001110b200140c00581124181d462218003a4029507181c1d04c190388070f0f4080020503030548508034010f007915840404810240c1490800580d803002d9a0070000c00b4005d000d80201d5111340704010030070016600 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 138640458 1250 138639208 138639217
    0x90e0606062701050405040c020304090605090108070603020304030e09130c0e0c0a0c020301140103081806070206180a18020d0e0304080a1e1b0305190c12050c0a06030b090108030f 79
    0x100c02e802804141d850300122454066030340f0040d00079003400e030403001036600800a0025141e070384108104985d0b9590030008a0302c828400d2007140e81041c0b5090009500c01d0f002103500c01d02a0420b4820028002c011418074082111030400707844045030001c00b00301c0a04c084070024000884400d4150130020075542640c41840d01d4034050015079940700d4110b403020340104054242e021100e0b0815030303490030850016800110322010318001600c02d0303035070740c506401601d503c941c000d08240c1c10079441c00d4414802054110300a90701000c50a0002580302c410794081d91030560001c1d0268481d5400c81e910400d49070f030303005100320030381090006100e8500005500310400ba0800a00c481c8901d4800c00e0178610a00b82c40040c200b18680f50710910788070010f550b001b01b160320500c1140c103020070442501c0e85065201c0320003064160004d004000702000984804a1940102c05540300e0b40050310000d2080401940f188011a48451200d1510718105800e5401000300d0301c007641c0341001070004103c40703215 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 138641708 1250 138640458 138640507
    0x816230a120f23041505070b040605130c080c0307140d12120614010e011b0b220605100506070f06020d0603060c0207050316050906060a0c0c090e060606 67
    0x1444101d12141e544030b8040500580c046078003d049800590419a04641c4607000e848200a002e800494285125404032420790344c001070421101c1c1c071141d480301c015081c041c3c04540c054114410510102e0f60340b41154000b05a0b01006140c005609800d1605150040d4007103c1c1c084040202c1503403a07202c5031070580c0703003a92100761075881e030b5400542501e103101e0b104507140c0386600d010030211708012103050880586000340c8a0741d0b40b025160004423581c0c0001107040d030b004590340201400003032065001c550410f009060510048001d5101040101480001950709503204c80503c580000e41400c160007810382a0742d00ba00d0200c0303d8440381c14540c0d40480c014000c50340085c9070016203045074003a002a540c0b051052200301d0190b00f00a40d126024010035110380603070220400506681000401243c3c40070300301c2492030ba5a40c04000c3c02d504511150401d02054450001c005603180c002e89000d0500900d0029420158400c16468004010030803801040c1c100000440b4502e1036004098621 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 138642958 1250 138641708 138641717
    0x60411070f0f0602041212030f18060b04020f12040606060f020d05280f0306061d0103020906090a080313080307030e0d050c060301060201021806040b03010e040816230a12 75
    0x10b05241c030000034400ca41c0440c490b815100401030401030b144041076a015407598081c41600101c8241c401250701000b04a00f140c103030100307110002403541e0415183c0e500020401410400000341d84074196000c03d00c1c2000005c0705402708001c00007036110704405804180f42050880840600103551182d011001c0c50a110003c40d1219503000b5006034403410400548d002030a8078100b840141c0081080080c10300030a082c1400400c2c014800c10300d15286008000c0c805840b201000010740c0203501004825800c61410403507140c0035112085000f000303010b41c000035a621020000b0111010240350801c0078260070401c40f0f207010135031010f030007825003400b115070600a0489250003481e1448003509242c00100c04000080d403a6010b40c086e01c0350759a090040443c0b0b1040c44200455481607011b00c000c02101800140040d0700d46405065100d44031391411890440b04443d141000c032100c2c0030454015503c22a589000d00038909644000c07280c0e400140911003031980c035081011401c116203010071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 138644208 1250 138642958 138642983
    0xf030406060801091a0a090c05060d020f0415020d081e0705160b0703060e040f0318030602040306091713060e0303090402031e090609031606020c060906060411070f 72
    0x41036078804001091100020007043e00141740c409104600b4003c142c40300c00c9004000340c44081c840c00303241d0340d42c0d0344507040c080030605040800c00160001040031070859420f01a80f0000070743d0400400240c04201d441c6421070728444402403410000003151004c102a000c00c0c8020450410005044201c0c0c1c1200d41e00c403991914021038440c090b105002510005013409681800360309540c1500030000381d039040c8400d6495000402d201d01040d50001c1c00d0401c0d09038010007091041c0015140848a4040420842e030740b6250802030780c1241e00240d429039a0f07083c1c0c1c10b081241e4000003c1d1106100c1103940d00300803c06102d1180c00199104500a001900c610007034107660610486010090013001103440303043c4800304d03010552280c8a540384060107a0013140e452034002404c10b204014141c01103240031400c07803070070114244d00f000448181d5002c1c0402c4c0c4100c0001d000c245e100300c0d0749038020882e0385406000c00066403045d410707628248d070b001c002e400041041d00701d01c903d9040e00310103c0c0000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 138645458 1250 138644208 138644213
    0x1a03040f03030b0415030c080106120b100e010303020f28030804170d0f0501082b090b1207020d03060f0306021309060e09010b060306010c0f140d020708010e0607050f0304 75
    0x28002c4220259132091504110381036504602c5c0c1001d003138a02035881500d0304c54580d018a42210a54014100c01c1086691650b002808040f0707441d43c0140d4410b01c2441c481d640c1d5040c411168001c3c0c00480c0560403020742d07032440c0402000b00d0454100d2a040011410708007100d03280c1000c4403442d002e000c21800c0f100060034000040b415545880d8201c060694035003c05132940014080c1c6a0f852880d28100800010010400280b44003900d01340c0703d2105091041041ca59000107511201c00d0078408600e400040104111740034011140780101d031100d20740780400c0700a08001c141243e8000381031900c001801000c40e108030201c02c0da40d00140050303035040d0244092a48440640c441414541050703404507204c9101c00742140240301ca80024002d2240200030042c0901017250220b002440c00e94002000c52061804980401d0250091449078206d54401d54207105040e83c01d400982d020a030200686c0c0001d1140c504852080000340500d0304050000a1442c41450b004004501d80800030506 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 138646708 1250 138645458 138645461
    0x901061410020f10020705010b0a0506030c0315130b0405060118090b12030403062319020d0e070f0503150103050d080c0c010e010605040b0d020f01030507050c1f061a03040f0303 78
    0xc00703403140380841da81c1000300e240140207075206d690b080750743e5401e10b071404046013402800101610801442a0708580e140740d81580250401006141020030080c680402e5803900c4194005668800d500404d500c1e0005041c002511406000b2504000c541d6503a990460b0720a03541006403081444080758000d08200000c25205100460b0380660000150001c10081941e0140140c91f15011035240307020400d450405420504581c13020707105107681c02d501d000382490741c01400e040844860024843c038540c3c80040c6080090b0b00700c1c00c0100c030403240500c400c1c0303405c100000b4000c130707800c0c0352110325819951807540751022a0303c1001800b6522022803201c090080c2558000c3c001a80200042084cc10b501c90280c0001e215503401240340171440006030070f0440c4100400358001d003450810f0043d100044000300001407900041003024060240242d1060000b80c2101600c0242480c2c3c402011a240044130000c0d40b1001d0607000c020017041e540c40c028001c1d282e1054100b208014552042d003810390 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 138647958 1250 138646708 138646723
    0x1409030114011509170a020d0606170607030e0109030219080405100305070909140f1005030307050a02030c0a0503061923041502030705090d060f05010e070206090106141002 76
    0x40544180074008104840c0b000d48a1540c031245956030840c0a6988074003060050305a030b01600d603074014408030005414031040c0035650503c507440c00241245d4502c41403c825660308440b02035074101d10103029000b6810b01504c1038015010300200a0500d680d0340c0a0741c0e8006950a0742d240304010b400321001e0040d1081034500508015009500020406000500401c0304507402c1000ca100180d011410318031134072850040344100c03032081040f13840f24014132a00030001000d80c019200a0500414103031014000f42402c144103800400d40e400f0184101814110b254000d0f134014031040100708030b65600020110b802c40c210007401074880440306103100140c41c0720703400100748203611415441c0c0035440108040c4201e00030701c07490f0018a9441484400d07440191099000100f041c46880040e01c1d20180b4840482d11540000031070898100304542929400da1120301e542d12107104214500343c060008d90392003003000d4003c211150504480910100722000300c10f01400c0c0c4ca200e600c480b50300810161 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 138649208 1250 138647958 138647981
    0x120f020d020c0304030b090304060c030e030c2119051e0313060804140111270406080105010314030703080403030b120f06010512060108100b0a0b121e0714090301 71
    0x150760700c62848000980e241c0c01440104c82e281c6c50b650000313411070400b200303a505a450554902c80c851b60b881d10200c1e003403800103020a071b00d4010945400d503660f44281d040ca00c4000241000e0f1501c4030484a150300340300c5c501d07501c01c1b8170059107600c1d040050390214a00a05046000021168014400640785140110300f1718507900d82c0030390760104c1c6c80d039000b43c3c07a80e11880c49410198005184000d640e03003a525592030b5405820020710860480c4040305280d5244540240900e40a50b1503550015082d54ce4540c0040c0059640784014000e0142e4440c002000100c80002107107440e885503001040c8500051015080507a59890a2104d07510649042c00d0040000b08480e80640341e44100e0b51604020f104051041c42d4000682640f2100495003c0c100c402100c090701c00b08072020b040f840034003681644150701c00414140807401082440251944001c01d0482141605d003c6036a804210700260380900840348400822104691100305410782c5041c2d44070039620b07000c203000407901424248504 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 138650458 1250 138649208 138649211
    0xf070c0306060b190315060e120604080406080c07050a080d140a060806090c0306130201020f060106020109020103060b090906210a080c01050601090503030d0c0e0a080a0c06080601120f020d 83
    0x748000f03503a4080c001c808403045408000c0c0145601c02c0d0200c1c1d101030302d10045403142c1d00d42080382c02e0080391200c11488014007080301c0e120b0003022090411804032000c4401c03400c04101809155409080c40e5413102d2414011468204039032100c4d95110f2018000030f15000d80000c00000e1208150095100344c07581c42130f0324100d41003141d40348014101502411046100c1c3c40700080b05c01e4000a8047c01014002d40500003603146c1038418000c203c8c071400f06070306504c02c0704490081c40004111080c003d041650000480240e90301c00101555801d900c400c80d100018007801481c0c0c2d8035400034940082e0b040f51144200c00402440300c80b03500040c2d081054500400803a002070000d4040280714041c0078800070800380d511035006480129440c000c0940651080c00710400019556125003030400540c205040c000703d4880c0000c0240203103820441490700904102010000d00038156006001c007810000c42920b0070b1030000b052400035641c0c0d001c4558480d00c111000c603055034115010b008600c1e10 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 138651708 1250 138650458 138650471
    0xb06040f02070317100f0b03060f06031e010e01030b0106050a20010c170702060105190801110c010f0e03090105070c031703010807090204030308060103020304110310060611120f070c0306 82
    0x10003408080f0301c0b13000d0540c04100b0000180030400b42c0781d0000241c441944103041d0729424900f001c5050b400050500f900701c410030320000c0c0559070300005584107815031021030780c1d00c404044102001071011b91054071004622030041c4006034010703c0a50550b03801d0f16003691a110080e00031180140001c44ca002c40d4880440820030b0101d043d040342488a010761202c94009600017452812344a080380c076080160030800c0148440d1403d014103000f02443d201c41c02400d65103910305c1c03d08480354060803060695000500c118440c07001e0003080d401040c021b00c100a912040c072150f540f68820400340300d040041c001455410040035208141c00f85800018000c045845414a0f1074640e10038010400d081c410200009086d1846000b1a0140c81c0d26030b0ba00281c0d61200d80066001c0d41028000321440344802c1c1814010351420001d140d180d09a400f00841c00c145095005403c0200d140c1c40009150441000713540c080300032800f104c510f401d0a00c1443d40e52807079070a02005a03209034100800a504005 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 138652958 1250 138651708 138651713
    0x30b06061b03030a0e030711040203130b07030f050a15060e01022b02070509070c1704030210020d26131110050a0905010c2001090911031515070b06040f0207 69
    0x143d486081d6440c0200000141149020785d60f02070190020050302103c6070b0140309003000d402a64200410440c200030611080e580e2035402132040380c0c1c10300025601d94051941c0416030145030b40015542604015420507441d80820440040c0281d40074400c681c59131480c240d10030840c0450f030800d88510100ca0510320581120010302c100c44000040c45004408031340f500e48000028060402c90b01c1e800e6902610350348031040c485850102c13003006401840000301581700c84107912000c0d0200c1d805010010800342010b0400d0907202c0450200007400090f40000040c03500003113412654100d1418000001480d00c42899450b9458032604603110f03a0f60f401545070803001500301a519130722402d1090703498100442c0d00a00803075016081c510455200d10b00c031003014588094554062524481c2c103a1a50b060b44141d41800d440b40e5415000013040008648001c601040d102108403240c8109610882c40303180240103d02d2701a210600300404642c4584d2140c0c0f01008038201802e055482d0580c50 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 138654208 1250 138652958 138652963
    0x3020f0312010e0a050f011a070212010212010b0301050d0201030515030f07170316030309030903050304060c05060a0608030a0f09050901090c0e01080c0d0b0301020706140108070605070309030b06061b 88
    0x20303c1401c8002c48254045070758070080b0f00403d41b00d0319480d001000741da0728008008144081400305909041c004020050142c0ca842e004074107a4001c110001d645c0d402d1400004c410940164041c01e040b41051006000a44d5200c2c00c8401103502460003145644860032020038861080c0c00544e4184140c1c9580d04801501140c02c00c100c0c0c0703c18205075201d246800c1005d0302c034402e404060010b000c140d0421400240a5448121118000d14180c80e05035101e554080c990340c4182c2140021074a2100b8440800030708001c00c40d03220700700c0c010620009180511141c0d41c1d0148440f14404d2140704109040005c0c466440309000703050080020b002541e490b500d4000515204a5010004030a00c01144165000e40c2403030380a00742c2d401c00145004403091080c0c0040082e08d85059055408129020105d201d90280b0000741c0d410a070075a407194074042d01d8600e071010541c03020062202c24458a4003103900005414101d03508007000c0c031040e80d900c8001038158400d5000c0c40e1030800445a5249040000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 138655458 1250 138654208 138654211
    0x150d09060b1e03103306020d02010513080a05070b0c040513020403050c0f1f0807031404240608010509011b020d08010506030c041e03060c0903080318070302030a03021b060403080306090403020f0312 87
    0x7287c0a4803c2c0e005000003c900380d80c42241e94082000040030344200180880d4001c000a920600d00f490910503159500110403030b09031144042020701090602c0a0b26101d440601c0100c3e203100c0131450070f440c650780e45840307003415001d481c424001502c0b59a03060710307007045401410000458000b18207210780c1002e003181d071040e540d40300040d14002d1025a42c840c41c070745460041d03410801c0e151b01480c0c0c1c0b01846004072013002505480390b4441c00b0006610409000e042d0003000c010002007061501aa001d150b02316404240408650108445c18034554202200e00e05407101034032480d60f640c0d60442000e0a91003250f0250001640b040340140440c3d00b1a4500d90980e88a96007d02c9030f80d640038021144103015000c003800341034080010901002e0184c4032490107001c180c0c16901c2c0d2a80e00d800090400349200001c0e03001d41c00c0400000d40e407050a103001080c4103000c582e0786052a00310f4440300380c503010040686001c0d07138001c804101454000c03c00207c0c0301010000f01c2e6596481c070b40d54040c0a080 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 138656708 1250 138655458 138655469
    0x61308030301030b1e0402060d09030522170c01090303050906070804030f1104020405010f03020c210409060e07090603360204050f0702060402150d09060b1e031033 72
    0x7140400781003202245450b031b801590020b010070f0a02e8014001c0d800102007030b0f842101800410040704201d001440141c0c0725a68814a02d440c0c2c581c60103e80010f0145909802e507115085a443c1c001a81c0e004001d00c1c0669426107400f42e22940c2e10400b0412510030b01c00090a03049020500000300500341c1440c1d1a0280300d461080c01450049050009900440c000e290200da505c17800b0040c2c00f0b200c0d40c00340501c40310440444030fa401d850304003417000480031244050701c541d0000b41884902024040c0f10001d0080d1034241400d8545890001c2ca41602c0d405020700f0035482c0d0b04c00007424400d6840140b1320449a0b403070724014122050800b800401e611600f00d00860500c0c0004155011400a40f44075041725009407643e691960700308095100740683c030102045042c45032122f410314900c03511b000030780300e00e034005068100641000035a28503c080036003a405901d00550150f01c5c0407456101d5003070114400b040b50b00401c0c0c044c02c01c5016000d8400ca4241e4040724500d44203003d860400103d40307 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 138657958 1250 138656708 138656731
    0x3150102010b1e01111501030605070f080f0402010c060b13020d06120c050d05120c070302120a170903030f0f0d1d210f0304050f060a0e0c061308030301030b 69
    0x1d0a2080c00354061603030441e020f105804840103452035000c0c00440143c02000030650300c150140305108405c2110a80003030f90100c0d6500c013000303a155005184400da910003420000c032a891310103a04012070500920090401c00c0034025003081040641000c10700850050140070307812422115480290410303084001a141021000200b15035008401402a600005030001c410b00f00780a000081e081143c04030b0b96803164007110200103071040e01030716006500e4005402d40c98a1401000020048002043c40316009201c200000404401c0c801c0310301c6165502650701c52811000290450045508a507903008000030780d60268003941005145200c45c1450400c00350000900244c0c0701103078186805e400754001d801c8541d05900845030104405101003140d45455121500d024070f03034201b910201c609030310036154100615018000540e01101e4200c08010b0b22503003c001d03a0f9240f4074104454001e01c000160000789600c0f84c1002c1d802387c125082100c0e03403542d43e894a00d10000c012160105101e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 138659208 1250 138657958 138657971
    0x915050a1802060a05040f06031b0e09072703030504030c060906091716030506092a1905030f1b03010908030a0209040b04050a021c020310060c14030315010201 70
    0x21a503034030516824000303049410091a4040e424051107601c802d43c030f13809015052000060b501c82e03482603c0e024140c07582e03000c14000111800c45030000c0003101d0500900007240216005a201c2c059190b80c00200740c601007003008a82c1e80d10f4007440c01009201401e03003008150100a058116001f00222885583c3c154030407903507008211034092a9020341d400007042c4401c00c00c081045260b003c841e01501c0f00a9075a0f4004240480714444801d90080b2442d0304524100640c1003402c0c0417800d103442c14000044000f0b81c00c0341c04146489011442144a01481c0c06042201440710787c1301000380102401701d41c090462100300c140d442e54a91701440100e4400103600010341010300890069952001c0f41074215103600c1550780c080d4000541c8c0c2a009955022561a10741c0c8a010b4036002c1d0a28000059032000400002507030709214035150310b140c50041050017100420003207080120303099032500c0c2100d10003901c0c08000e202c11421b14211140f0004c814456642448a944111403009030001c0220 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 138660458 1250 138659208 138659221
    0x6030e0c0906010c021003020c01050a0b010f2d090e090303040b0106050c060c09012709061202090105060306060d020703032304050714030a02130906050c0f0304030302070f06091505 80
    0x401c98100d6034a4005040419403200609000000c080108918280581403460040f006401c6510840d50810b0064550044800ca96045400032420511501e41004400c0310343d4008541c0344032048007a41188240e00451003058844c00d0120098552a826049242852400f481c1d50703408c01e0310166940036400c0c000203001c80c0250100c914941c01000908410f07618100780d1a110340008071200c0c1440f080c1c00074400d1078090414005000e0a1a12160074084e04051a000803102650040c402e1071544159050142e0f03240c01c04181101ca08655440c1c0c0d035903c01c800b04869000b9401c0340c4041c1400810003000b01901a0888040070400701e207523a9110010030b1105400702c2054034080d2003900510410720114942400410301c50002404945610196901040c0c1041410b060a0313401540c0312240d0007007184500503039801440300c0d00a1800c0c80c0d1100e19180591001910013024503900050a030200002e02030103114540c0c00400400c041c1c1458140b0903034614401e104d900d80e951424000501 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 138661708 1250 138660458 138660469
    0x4050c090a0b0c10020703170915070e030a06020a300506090610030b01180b031f0608160c08070506090105070201150303051e033306030c0702041506030e0c 69
    0x1120f07a8160700078440c0095509081c1c0081d400150709600b04541c4102a0421482301e11240d8050349030040103120029199000c1c80039050702030030f03040400407030741c0c030f100202d0380d0000321004481d8102500582d43c01a41c2d03800c0d524401007803d0013000c1000c100c1245115980b102da030303000103d07030440140110761b601000c01c03c00070400c036220756101c081b00c0d0304401850300c02d0b0300c001441e50041c1400644400352000da94021406988242c04002000003000f05030042101040e18940d0080c542222542c101403020b0268440281307541900c00ca146803c006140c03090740403030720664010070807a03643c19075818441e80315882119111200d41c00c14000c00c00c20351052103a00060301e040c80c0006003160540d502112030390700c403011207101080d6044003195048c80080086005070350105883d000e010703200910442d140036903131050710a1078480c600042291038603400c1320791002901e40d88642d01e501510000e8000c040c6413804400100c4240800b01d40c10f1380551000d07003560643c030211000d10940004100 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 138662958 1250 138661708 138661717
    0x4031211120f060d021c0c08030406021e03071a01290406032301060c021906120527030a1206120b04050a051b09010905060a0311040b04050c090a0b 65
    0x49694418000150380240030310b520300d402100003410f20103d400207800159181c48070074486412411141c080c2002c200b20b503410350700104400c2000e1820185014000780d02c50341d9907003a040700c040290007242d40d542c0c0c041c0100c038501303640700740000322120411070f1105a4110074040c3c0f180b10083c02c2c40003950201d00120607020f5075100d03142145800e05101c3d08901400601944500e800303a1800c10200300803069150303038040c0c01e0a50302d40b800041e107030042005407000f18903854171407039440006110180d401649206030010f09240454151204e040080b0300001000b18446540c3e0714500d0300204003400310040c41964842e5403026031210300c1c2242c9104455091142800c191f4000c600328002401a019913580140513006840301184140c8400341020440001c000a08401e001006814540f03180a01d0240c01d031900100450714100010881c90f81950001601c5240f01d202c0c05589076896030000c407981c04010b007040c0030504214000e0071158100304041c0b8400c007403801d07002c10b020790040180d9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 138664208 1250 138662958 138662977
    0x1306110616030b0409020603040f0201140703020606040c1101020a08060901140a230a03080903012304020909011b09030c150503220206040602030309010b040c020a020103022104031211 81
    0x1c9003841c81d081c0c069008002c103001d1550400e441d08025400b40e82c0f0b0388043c5114034005c990080b007440c804e01c0010020784503281d681507408424003e150100b03500040c1d65510070805d0702d0004448400010940344041c1010300e00d08150300003d5040007065000b0301d0980542d40940c2d000b2000e1340c031200c0d001800c01046c16942e400c601042000c011041c10000c68500c40c0c00300704080300443e8028404500354003000c1ccc100351440e0400296024890500b44a08210243c02d14114035001d40c00744c09200b9041c0c800740010340b00d80070f540c01040c00e1040070b40c00641082016114200c41c0640c5d14030252101d441840181c840121080d00050440481c4415030942d0025960701490f50b80c69800c0a43d14501c550103582500758010b0003000140c448100500142486800075a128548141420709491502d08800e000300e06101001c0d40154001581015845e0309003009030700c0c0e441400c1200c04541010400c444515419828007080c540c110310a4807001580300740a02c40c0c0c8401d9404514540303300980c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 138665458 1250 138664208 138664231
    0xb0309010b01080708190b060f130807050103140c07170a091701092d023007050102121c0612150b06030103060b01030905010f060f0f031203050402031213061106 71
    0x111606e80c0c1b4258015005040c0041525041220080700581c06800c102c4090040b890360401c1801045401c00041c40200b81c246814040300d00b0313100105c0c0c1c1002e4042c0c0700c0c0040401c085044810082d00c1d400100c80f03000f1500302a40c8aa144140081c2552610b11a9000e400f864262140c1e44280c180250659590004442d40545805801501c80020100c442e04000d0100d0400c000060b0744403d00da40040d8180e1103104e440e50203141c104d2030003c02d2159020800d511084080240c0d9801003000d403c0e0390b0401440079160400d00c0700d50304010002e5080001705031706d803000c0460280f0718410418001c0b80581803d40302d010358001c01d4001c0300d2266403d1039104101307100410000c0c3c001c0d01700314420101894007251052142da103090030740314075900c032305421500d0780c00070300c600c124603c8550000c21000a42d500d04901e140c4400c06030101c40440f9030101a00c8038001000c0d0340341042190301c5c11601101c007560f5140d82d1145450780780d01071300400c0c001819401b0301c81d680078000030f220340c000c9803400d41 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 138666708 1250 138665458 138665491
    0x209180613090b1302030703050601031104050c181e0a03080a02190f02060a1202030f07020d1404090b0609100c020301050a092301110c24011d040c0b0309010b01080708 74
    0x103124009130302e1480407a414030901b0404400a02c05004641c020f5101e0006034007518a58030030403041c3d0381c000b031203140100814000141c0034012540200441102580d0240c3d00d10004142c2200a91001140c981c20544c00030300041040441c00090040c4402c6600ba60150800c0903e0302a0001a800019014001c00c18a103409440c0c01c200034104a5203909000084280304080d503400e03038004171101480060308804100415406000100540e10146802c030310307024154500e44801d0196014040e002517403003103440c5040c0c0b900030031103a40900042c0141c0440d01c0307143d8000c4c00d01d05010012402942400c02281340304843d0b0103404095075010820080846909610003038a030800310303051000c0e648491503000215401d0f40286401104d810180c041c820140b04540002c09402c000b000b00300301d402c0c0c0100501244035003106c200d44900d298a0341c10307803907a04003901c10083c590040f0081c0180042400140f041c1540203a000c0e1100383c80c0c00701c2d16900c40c242981d11202c215455041b0004072030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 138667958 1250 138666708 138666721
    0x6131e05060303070b04050d0207090606023013061e0c0201050a02070509010b0c060f070912030e03070b250b0703020703021e16081f020d0209180613090b 68
    0xc1203594880d401500312401d00c0469112030f0391141c42920156038a4208098007207150b0b0341448980060003d00c01c0a22015103040c1e0020760380d0036a41010b04501da084020103002c0c9892009110141d0042130f085030301c641c0300d07442401806450748541c2020501e84001c10104081424400c180c4250360780714841d841d45990019075070344d8400c00e591000c43c016114046043c0da00e12502a0180284400c410384800440c0c00341071520f5005400c141003041c3c44c0d0200002d8980c000c107044140d0b01c0401d0501a1070301d85103800c1c0c0d00c050139a42400d502d0300528101091002e03908015086580d03518100080c40407031440000c00f042000c0e41e029000d1069600001c51081c025001000414403e20413594505035055072800c2e4804c6407180c080e0150821551007210403000c0c600c140140481101400c0b03002c050f5040030f0f41c1c0d100d4080c1420519a00480e100381101c1e0b481e070541d16890805400040200000f1141c640044070403540140715510003454813245190507c14001180d030320060a582e00e0b110b50 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 138669064 1106 138667958 138667961
    0x1120906020c0d020703110d080c0d0c172a16080606011107080a150b030604050d08100b04031509080a1e0809031b121206131e 56
    0x209011b001180384481515a28581120850401d143e03a103003070382ca036004032108500c00c0c0c060000104103140c1c0101d941c4480501c03404004c4418040012084214000d040703092000e00d0783e00c0180110401900c15100304050001d08680382c41e50700f030070b1505500c019a041040c090300900203000c040d5801150095911151802410105090804a580c1e90142c040040c00000c01404400c144c0c1142ea0b202140706640601500d149150600300a50741e40d10304408100007920b51f4000031110352048440c0c401b50390300060020701e05881d58039140d088000c071030559861540e4a003180d800040744900281101c2d182c90300e50124244400d24001c0103182d00b2100cc6041c80440010030000791008000c645114820548100076290025100d51030440d0244000d616040300090f07000d010f010810009204140c00c84141554a403030841201c20b550819035400e4109455144061091445 = true := by decide +kernel

theorem cover : BRFrame.Cov 138489208 138669064 := by
  have h0 := BRFrame.cov_init 138489208
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 138489208 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 138489208 ≤ n) (h2 : n < 138669064) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
