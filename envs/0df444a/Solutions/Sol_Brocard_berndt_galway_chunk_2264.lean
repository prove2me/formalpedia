-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2264
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:10:52.793947+00:00
-- url     : https://prove2.me/submissions/db88d358-d828-4bf3-bade-29554383e253

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 407014388 ≤ n < 407194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 407015638 1250 407014388 407014397
    0xa06091b0302070204061703090112020c030a0f111504021212090f010e060a02060907061d060a03150b092e0e12070b04050a1409010302060912120a02010506010f 71
    0x10311051085010307522801060380c0c040d40743d00010811401d4802450704600c1440002c6070b42d14640d000150406055000c42d40c1094414000d1159002d0040110399110401d49000907c0c3c131003490003511034851601c40c4091034032400d00c05410241d0b8001c0341c603004600072601c403d801c2c4c031030049440d0754130034404603064480d03010b1004042c10704003461030444810701410038032440c040b00382c04140141c00c03411508005030301c81c00078044101401d00201015048070315201c100c001d0b10194208950083c100704a015250008641c80701c188264409501c8582d00320102505603a910030340c00540c2c0102000ca0301c580c0804544001c040d0710400d0b0480509200b0000000c81c2c007174100c0a55503805036102d982d4000c590301c210030032458014086200900941070300c80d6219400c080c148410042c05404c83d0001030300d042da007450190348a07600f4504481c0d0445041e03a8a01c4a0004108903203041c1413201814801c400c42541d580004d41c0241040080319402080f030759030340100440d91040c1082c130007c04203 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 407016888 1250 407015638 407015681
    0x31b030405070b2a0321010b0a050a1b030f080601020a110d030504050d05060a1404020d110a120308090c04200a05070b1611060903091201140403080a0609 68
    0x58456000e04100c503080c040055000400d0030818145084a101c044d0054000203628216000c5074622042e00541a0000c0036541d030405401c0c0c0c20a00c140c0c20302909020010400c908498803e0041b0100c80d2450056182401d145203005000f850107080400c02041400d00024080c2d440021031807003850700107403404440b901c20b0040c08100d08880a0990405c84100070200b066210544001c0e13446121300700074030083c0f8002d4000b200715000a94007001d5500d07840180005a075032401030f4070703100c0d40021201e00034003011030006030743d074429a03c030b22040703c03515038601c0034140c100646a20808502003582c140300c80d800304020071100c0c48048503080c1c003e007070608480003403500c0141540c4e01980c1055850900c094941d030790322220480705508409100c0c42c0c2001419480210480804588401010340d420803608050f164040d000e1014011140c04e01a03182d1341c8000d410110074542078445800307241c14035042c010003c6404507203030349240303082110000d00d21b0071506c03410300308040241c91008003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 407018138 1250 407016888 407016899
    0xf080703030f150b07020303090603180c2d010207030b0a090b01050406030f150603021e01110606030d18030b01030501060609080a030f03091b090501180e0a0305030702150c031b03040507 82
    0x41790400e040a0343c040c4000c0c0300d400c0c0c86403a120700541c02942e404d1240c1030300c175151f000041d2600c0255040140242440d8601c0c90311034481100f030b0258030f04031881411003031540c140101d19028085c1d100ae0450783d4200c3c1030161039801d45e03000740706941c0204808201e50b0f0300d035802c0c0b2094441c40d100081c00f005400e031202000c12200d04001c109103030160008a001c0f507590b000a4451542c100e01c0d955040c01c842143c03052982c010b0480079192031000c010b03102e00d10348400069110620417000324240a0b4100400e01c40b5141121032502460380304a0082c11542c41b0700b4114028603040c05014003044003900c010821010026a4107030107541542c60008032000e1210071405070032005000c4822648072810300c0078844080c0b440501600c919180040c440d0700d0040101400c034038410106a2640c17900301070081030200402c24608060301030500503074036201c04c2c404a2403c14450120342c0e442c01c0380014481400c090070300840c0039012403601d003140c024411004541e680700a440007070450303000300d608100c0b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 407019388 1250 407018138 407018159
    0xb0301050402031b030403051201092a0507060905010c080106090e011509090c031b170a0506060712090305100c020c15040b0f1e0f030f060406030f080703030f15 71
    0x5010b14800002c813040071200003440165001135808501203800810035807081c20004101c40d004000031841030100104404940e1202a1b0b80c81d6000301e8401d07180e58924103076010780100c40d0207540c407550821014010703040082c02070038210101c20000701844000501c00b881064000c068802420101d0000c1e442c010340b0380405d04c0000b5202c3c0900c119202c0000c1e0703044c65489141a40026a100400c1042911001502c0d00007036541d28400e10002250f07800c000c46a002180307030701202c488070004083e22000000303500c0e8010200300515401c82e030310035010060b911004070021a40f20314111001d00c9540a641c00540d07020314071210060740b007510101c0640c50b041d000109a44501c41609141031340790040030b02d01b503000c01c152400e010400200d04281d0742507021400248040b255101c0d00f0b10700910700c408090312020b40241140c0f601d00c5c000c03500c50b65890f4000340003150b10080006001c1c1c40b07480d0010035908990301c00c4d07021914042440ca039050043c00380b444103000042d02c0c0802e81e41000f404a1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 407020638 1250 407019388 407019391
    0xd030903031d0a05010501051f0815040618061505180d05030d0605030c030f030a08100503060a09060b09160c05030403120c17040b030402010516060f150905010b030105040203 77
    0x404050315460101120415107070301c0032036500d07401e0181c4240800350803c1380c00d482c1c041e1f00071405540b180c040403401410100908032010a00d28140c0520303161600e24181800d0408461640f00d0310709000007a82c29104d0f038091480c062180e4042c04000d40e03401d14107000000c22040400465002c0081c2d1803940d242c0582040e82040051981207002041d448191070364020300300100b0700c1980c031501481240b9080040851b02d0400714001c141c0480b000c100b075a2a8040e0712040c0081c8004c60011aa2072411881a0000303410041c0c01c94a5601d0400583c101a10b0305d04000d88cd4145040c41d002d60030708020388060300c505a0004a191101c0390404112090542c0070b00590309400103001c0800080c6202a00d01c2d440c12240da030b00d51103000d41c1e00303240b440c02c1104103450040b00010001040300e104400d007a2544141c0900f4450788460958002c49070410380c0141c01000030b8600300b0164803902c40c0382c0c046000f030f80c1d000440380c4a07207032208601001c40e8401e000d9101028401c1c001003196142a80095 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 407021888 1250 407020638 407020643
    0x2d140607140a080a0e03120409112808071b030818061003021507330c09031b1a13150e01080a020f0304021e10030f050105040507020d0309 61
    0x9081205941c450281400c400c8402103896030350000d0603443c060b901484141c4040300884c0a059a212421010719040c810740c414002916100d01010103035003010000e44240324150314600c0050081402c00001e40118090860080744540e03001c02e294911036500c0c030303405040e04010418842e005840540c1d8070310000f05500e613924260304078032206110a10806000e070480c4208900c4c1c2e142940b04100f00c1503040448441074800601c100d00224880760802c07030081d15040d007a4041c09049045400000b00c04051401c060b5042659800c6015400418181224000c0070058044800e2550f09514a0742c0c5100b2028911030304000c0350414a40580204061240721903203080076680d84140c220404150141200410400041c1002e2541c01c002825800b030030303010045150080008070303840300f4000500081c0c011916038040c0c00b03060040000c070815404006084080004001038020058001750340080e89690134140000b40901303140c080c540c05154160003a1012418040c011001045800f009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 407023138 1250 407021888 407021903
    0x1a09010c1106040906030b06031c08010312020c150d05070509180c0d05010e010e0f040b160921050705040e0303060d17041202180609010603020c010f062d140607 71
    0xd500d01a07482104006c61003007a0841807480c02c68200b50505001781d00d4040e0700c202c410b441d400e043e5444000581503d5116058401148180f0022841c01e4044c04005800c66454003404001041084c00b0b030491000c454402c3c08130780e495040c21901401071460302a0480c1c21481c1404c40560448000c80c8d101071040100c80c288008200c10750241c40f02a071140300b0206807400140003100032008110b82c08810001902c015050661310351030031036001428060050402054801051301c075a010030f0017020520704825505140c482c052a41c1866604104c0706842200000505418103014403850f5070441d03005075080d40c0d40e1409011503000c500c80c00309c0e03100b1066103070714940c011454042d0001e051036180d590301c0e071111881403003040c0f01c0701c40f206488040e016080100d42e540d052440f505407017a5290160715004026195409400705034084061079050042c081828040211b1025280302c00841a02d044088104a07409540f003d00844100034042d00e000400c40c14007a000b0482684a80308 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 407024388 1250 407023138 407023147
    0x30f061501120c03061806150e040f0608060601020f1c080603030c030a05120916062133140103020a0909051911161514010e011a09010c1106 62
    0x18034900f1100712455000119550315000e00003440d4144106405000d4104100040d6040c0184d0056a081d04d1030040700300f013240a200041074449070000d07400100210014050395440b2901c4035113512049820358014170880e80400580e02000900c07030a030004486080a41342942c58080322440001130801c0d805100070404200221402c00082030101e00d1a40c0d50340d114650000440281000a00690405c1d408940c0d8444685946c0c9288000c0b00d03254100800d24035184561200c03224038240e0584846c0c0e1402c51010009407200c1c008000c440030707000b07900b86454a880b03c8144400e000340940300201c0100d035400046540a40e00420440c0b203181444030105a4490500b001e41e5070440740740b020502c0000007c06050810702442030f00e40810f401090800001d1540036800d400c2009000e03002015150b030040388402e00382e021400d40a09000401c0c0b4031741c0c4070200b00350300c05002e02c2100c2a00a85900f0f0108640c4050160f03000d540d4142d43c0c402c0d120103561141e100e051400031038141d00100400 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 407025638 1250 407024388 407024417
    0x90606040b042f091f02100207120804060b060c0a0b09030301081f1d010903030b060f070b0a0e030f0c06060d02090402010804030e0301020a030b3f0102040b03040f050c030f061501 79
    0x5440041001c4010a64072a01c110000000c0c100000c00310418247d170300500c950000600782044010742c0c260300c0e01c0c0c0041c0b00e65580c01d010b00585610215950031503030000b903c0b55111808034030041a02c0c020300c05035240e42c030766510095507840244681712140d04001130411111087d98015459080300d0300001c118641c401400480216040000016983d502e8481108140d014000d019100000310303546800c01e0061500380c9603511038460300800c440d0050f80020050348195000504d034500500859403149054264a803040d4018103011144d4420880003c0082c0740040f00640070b0b603405041c2d06043e4841c0d07401545d0003103010b0030840034040c0480d1020b01c00c7d2000d1000c2d0043d03142039500401c110200c6018010407410b203c00000c026801030483c040119000ba070340419205123800031948102c51201c0035802401160840700701c1550010500081c000115480020540903d0aa80d070742c05030142015520064500c22024981009000903050000080740696170481810700b100801c0d40b41 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 407026888 1250 407025638 407025649
    0x70605070c0210020a0c1a1e0304200303090d1a0c0d0617121606021c050f09060c0a02121210050a1802130905090606040b042f09 57
    0x1240c0c0080040c104500d110203520700b0040c040301c108010b0020b403000d0892500c031060401c01c2400360480607002640c80e58030a040b41c03000c4400d802e2010b1140c64280d10142401c2c5515031007901d0682d00c0e051081e0746040016100d940d03880041400074021440c00790b80d4014000c2e90b080d040d07002e0b00c030200788805149800c508a12428071804200369007650341e00345510020210346185d0044014014030200013910034000090240500da4480869a141c9000080c203141c990101800106a140045884030209800c02c98003040998694024002c03030780c40703074001e2041100c202d540c40b8150380a200880c0d400000304004184883d101e10541d40305070359030140c0c1c8101e03501c02c00001013040c4000e4200310050120383d000101801c4203d4400c0302d9589024941203022a600402500781540050043e07107421030507904a004110b8120f06203d5850082d81c46c94541e10300321001401142008454000741c64170788603800384401040d20349468294140d18030300b855043d0064000840310108008032041d41c0d01d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 407028138 1250 407026888 407026891
    0x15211409060a0513050703080702030f39031509100c1d090631050a0207030305150604090f02041a0315032409070f08010f050f15090903070605 63
    0x80e000610850034140150710845100514004980640005074800904042158411242c10003001a1140861700010782040d9080711040b400b803181c0000f03410b84019007000044080c058238421040d06243c4420303002800b400d10355056042c1c10050b0fe0004828410062980144001c01202c45a00c20a20400200da04071030714440802c0034140c4414480b043c1d5400e54a01d000b0684050815041540c041256010280020076800f401c49104c0c0320521000c1b010185a4070381408144180d0900e044444029032185038241c0c00a4241000200e071181c041850720707111a8050405460141380240310802009280404200940c08220000301c0c04120301d8140f182e038840c010f00d90355a00386040c2e40c1020200c0448200e00942010180241000c42d1764064101c0d0740e164031411606d691004845800c000c07c0c0e400402454094003008280c2010542c000001c4801c80201001142c80e90103801d015040b0485045443e48040543e10304107047c034522058001034004110b9040000b15500c110603180d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 407029388 1250 407028138 407028151
    0x3010b1b0313170c09060d0305090406060807030c171f0503060c03011706011503020d09020310020a030b01020a020d021c06020c0a0204050a0e1b01090b0705070e01152114 75
    0x450a0082c8041c540c0b03038060b80700300310803e002802c2e5002802c0105400d4440204810f11860400113141c0c10b00d8002d108032842c0b640000c0040140740e45940000c0c1c85094240d80240000c0c0c42c0140300c5203040d000d00c4070b5190217031b82e841030711103196540290a503550f45c80080c0c0c1c82a201055900040580b01048000c2c0920390440c3c3c2243c41e0b6040024002c030609020201c1c44141e804070b4010440b081418038051034084140c41c01580c0c611030100c48074007a2403000002034262240e040306d080b515215602030404a8102d540c11700c0b05803480001203950741903489020b50b00068005140b0014580b0f040c00b6000c01d0380e102c103440702848094a611003240c000c0d0b10450f82c25000b40506000318641486200d41c003a601c1003003008107002d00070389540e903107200c0000070070031010745950900280c0c0076800c80c800038820241c04999036003640c40c1194803072040344181d884d01120302e0008140f5842c05075050a0300000d41d51030f103841000d07000314002da002c41c2c110140d84007a51307118911000c2045c140081d11602 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 407030638 1250 407029388 407029417
    0x10b091305150111030a0801030611160b060102060a23071b03020a020108130809041109130b0915012a0c08030306150f091e0604060f020d0c0803010b1b03 68
    0x41a450026003210080c00032030a142d001045484246c64002c04000c3c19241c0241000404000c24120200d40384214000c1c110343c0d858010390030003040000c1407090b2084200ba820ba0300c032902e8440ca15016503848010901c1503d406140113003520308914a040e911410520701000c003600401d140e08640240c5060560040e04406900f00a658000241c13036006168010041d000700c495859006244c01880700707452081303450743c012140d480080c2042d980c11420040c009039881c640d5008110042c10b5043e071440c014180c81d03002549405080784000c840c040c0685a07150900c8400c58030380006c0307031007070540980c40328901031400100c0c14400c1210040d020040055540e8102801040b078030040040340c030350301000c081216004681502040e152039200030355043c40c1d840074400f0001c610000038a480782d005800401c00040f0300ea4400c0d080700c440d00c019020b840c404c0d201c02d61b0440d014010320170040d2895030208010000010000000d0190700e020350f2040424450909204e801c40e4482d280c0c900070300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 407031888 1250 407030638 407030671
    0x140c2e080a0b0a080708070e010608011806050604060908011103090303070507030212070b04060b2d04060e13120e032113090507030e01091208060613060309140105070206010b091305 80
    0x841b0801084010341400803a800a9603d040002030003000b05006400403038a0700214a5400041c90700140040c260007080c842d291515414000c044050600ca403500c0d6600f813080b420010340803d4100d07030281d0030600c01381d4910340e92500242c0745603124907421421417040542d0348844030740910107850264821485010282424200b240948240c055458400e04880d0031482810741090070218002c0c03000700814203020000000580100529400925029454402c010f456815002c28181040c41201043c880510b004400c5400c880221000d0340c156000014000c0100d10007850900d024520860562815071a00050006a04c840d40701142d40d6499905102d02141c05015061207c00c4c4803000300406451900c400400c451004842070038000d01801141094844030b04a0309442a00149003100c113960300380040c020003e070403007510241c0303007000b4040307048006029840c0203a00b654000e1107070b64285070540c440c65100d012410b51000314220391a031600094000d4503c02c00161368440e040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 407033138 1250 407031888 407031899
    0x61f020c0a090506030a060c030b03031305100512061302070515040c080c03030d0203060d0c03081c050c0a0f181d0106092301020307140c2e080a0b0a0807 68
    0x314164100280143c2000c0c20001c2c1074800080d250102a008800854409a6804207070028282c00300c18039094000001c1e4840600f040e0103ca4085500542d003100000c20360030f80071251401144005254003880c2c0c3e0100d01030707140000380c0a0100c01903140040c901012940c8051608039581d00960040000d2410030041c02035014030100180741d0312000c0d201440840002030340720312543e403420702e40325404030101d0800c2d200c428805c44059400f00180407240c1d01c2c3d00f003002031900068001007030412040301400604401c0d008460060840c07003095802c00e40741074016a8001d68514008080000d0500750500c0d020036888003100900d2651010400480c1c81d00800f152108142c01c0745050117583d000800c8001d03440f6148202d0b9034006020301441145400040303096200300301d0040c00504442c85d00c80b20720000816002904001100d0202014140000003540c0c3c2d8800400e407003000000c100d224510303a0043d40415400380005d0301c000f9032403940c44001100038806402c264810303030101c03030180f10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 407034388 1250 407033138 407033149
    0x30412031d01050315041503050a1401050c07030509010c05010f0513170f190207090c17070c0b1513020c01090203060f010312050912120d0609090812061f020c 70
    0x4507180030f203403040c590300d004991a40d074002158116400f4903030764400700072403803d0000c841d005154424103844d850b0351103041c00d8005002101c0504030a51810300441c4251443d00d04450f60140d00d078030b510341000c03085401075413440400d8000755519501d42c110314020701c0d00d506c9100e02c1280d44100c0c1403000021418402c04036040f091041c0c03ca81c008000f901c800b101610f05803550402040486c1410f000c00120880c113224150380b00b000b1041c01d00c900d14107525000711028403100700b0f10582c0d213481d036142d034022245400c400c4000f90035808507001007020700e0700301ca5060300c08440141c403a034202c90080071804200e0348407032680450350f592a28440e007189014400a6000700080304c0b0b0358025410754a03402c2807803540f10055010b202d8000790349400f61f201e000c080000e04a08070141c4202c40017003d400c0300181e210345540701c0702600d080408121075103070344240c61070141c010182900f0401c42c900b44070500c89019100a90043c03a04070490f03c440c00708618003217100c1c0705a0107001340c45100002d205 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 407035638 1250 407034388 407034437
    0xe030c0a030201061d0f0402060703170c04050906010503070f0e03030403140a0b2d04020f130c0909020c070b0a020102090a03030c020118060807030b060d06030503030117060c041202010203041203 86
    0x5800c5e8801c1003840880c5e0311000c0f416402c1901114010784c0e601c0c10b40303826901c0000c000b400c0c0c501c100c05a0100049110020094422500d041d41c110201c0e81d12035004640350721040f5400c0000c14050b86059468a2240c021070302c0f110000380c211380c64640c483d00d82c14001c110366000503080d980840b02c0c000c1004004201d054200000c1d40b05180d4a41c09041d045840040c1201021704000da4180040d0075541c81d0f041029850034058546003480c2d44901e0150040c1000231181c03008035002040008400c5030341e108235501c8070101000360142034146901c0c903120f90702c2031465108564003131100d04066554030000c23000461003611342d61900c140900c00500040d0507000f004132044d104007000c11203550040c54140c1e1128052800040e4000a10000394660051590342c1c901585420408801c008000000754140c401c6a9607100485888407891507407903000b10743d102803c00c01030100f0480840d40c400d514000394814010341c0e080c96143c81c00a0301e054607168041c1d0001d548007560f00f0800742c1c120b1210 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 407036888 1250 407035638 407035679
    0x207081006090f06120803041a160305060913110a030b07080901110406050405102c0f040504111201023f0105030c0d061d06040506091f0e030c0a03020106 68
    0x240804d80c5400740410b00b0054208028241800000000302009904032082c502c214040b010840341d400c1a00071904200031480108000c01d2800c00841c0302481c1c0070851500c40e0410012542032030036507980c0c0040e03804040100940010902c0c20200000e400800402d108111941e43e508062a040d0306071400d540c3d040c800011198000c2005118442d032101c2164241c510070f450300806086a000c048540382079010300e9001341510040f000003070840c07074141c0c102404000c80b450f0940e0301148040108030780e425500244080354500c503481c03403401d01203400c4810b0b0818400043c100f04003044a00e00e0a81100720380c4d0600c1c81c02c49110342c940902d54803120500002c41d00984100d43c1400003180d5150032025040e0300c0f4040381540342080003420340044050035085030b1079884203c031081c0c442c0c0c5d032003106940071110b80c0a040001407084400168140308540e4640c090001c01c4074003400c0100130007480b03d511210780020421070050a5080000f541302d28403d84c00000d80910f0140442d41141003010701 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 407038138 1250 407036888 407036891
    0x4050403020a05210f03060102100e0706030c091401211b2c01030509010915020322030207090506060412030c0212010b01081909020901030f0b010e0702030d09030207081006090f 78
    0x504804c0407851082da4610711441102a80d2a01c44000507403414880c140300080302e6007084409411020041400000c60700c41e5201401240608101560048054007501c801024203a41c0c0c2a4258401ca01440075001c030031a4001c001e40e14030301d182058a01d44440d4541188605528820f6194420340140780101c22007080d0720b81240e444520b007140e00301400c42c2ea04046d25000807a00e100402e500110300749a0081030400800500c03410345000c0c0d0412261030f81501d8040c81860840c801c4c290614400310750550150805c02d08003d6100010200545895002882404081086d03c2e8890714804020700039150102d42082520401c641c1c240d0b04c820890f00c42e410300102c104580d03008038841d40c005403c2d101c10308444048101050081401b0b06000e1b40c0a41c4410001060003403003900c809040d40201642000c5a0300c032010388402050036160500140d200700309042045905130b00104010303200e4416a8010313030b50303800b06626101c2800d082c001c0e000c0e41d0324020801803d15200c0c041280c0b200080 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 407039388 1250 407038138 407038183
    0xa020d03031d330f061201140105040b0609130f0b100e030d030605030703080d090c0e1803090d0303090f05031803190f080c0c0306070f0f022a06070204050403020a05 73
    0x3560210f240050500d42655400c1000b1420561b146408013121101686c000c1242681411802840c1034003803041d80d004a1401e07401e04003900f8090210b50130382c280176061035518100d1700c0b00d4400400342110807014075656580144031903a00e40c000c03203820100d03c0d80e51040401e011030416041c00722050450050500e00082000280c801242540807a90003944075521441070f42140070140c000880d008000810206001c94100810301c00d050040d804801c511952030252000f00d40e480c80b8450160744d01c088000321000009129400003100315119191820550f5850350b039161030358119281c640b41c01202004040d01a050801c20001000d8840c26201c2d01c3e6078103070303d5499442e40f40e4900645510070020700e120341c003041042003180e1980090210f81940c900510000c041c0502405203c000410004e6040e00c200d1001900107040b440b003260083c10380e040b2081c0400c41581c0505d2094018505101c1c000150741d46101e403d100314040e4002d040540014030f040707800d000c11000740c144114150a03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 407040638 1250 407039388 407039473
    0xf03060c0905030613110409051606180b03070e04050903270d0b070908070311010f030209010e04021303020d151401030b04020d17130f0b04080a020d03031d 69
    0xa00e280c0c0240b104400300c4505c00c0c07036041c01c107030280d00c005a541c0c0141c14901950700300040051001e00700d000c00400d4941290f251181260306819008a41c82800d0003200e082c80805034a03030003160001c449003407008080310350401040a44c0d0085031840019080480c070880804401e41c1c0d59100c010042e50003081040c0ea2800190031316044501c0a4490b0450400160715980100c1c45000030340f500b54220742d1200c1da03d240c00511044113901c014001f800f0210f10300d8159002e4025a1840181616150040e450400901c0000c0d0000310007940b0010154000001580300e10140d00685801100c40d01440a400e48090081e43c108075107000301c1c1c00060340104082180b0f00c9621740c01c50340c12540e40b008540a4100740120400125181e2070a00000481d0805021404100c10403542c804900a40c0107689a8500b84c00e030046100da1911070f00114001d13001440e0005405000c1e6109017030000e21400c4002034202c0d20740c49072484545c2c030790092140044c000daa41c040b000c14515009122403480f40c2c43c1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 407041888 1250 407040638 407040643
    0x4080f07150f02190218010b030a0f2a09090f050103050d0203040f0306050405072102040f060501023a12060902041202060d200703090503060f04120210060f03060c090503 75
    0x40f522034030911503601410045541300c0d007503100820401c00c441641c47d6118800020755038026516401207515118901c507500b04180a041490051034205146254041d0104403010021140580c104400000041140e1516108500101e03104c044001380039811071411314506118030b0041c000355801404200000e48601c1590300649901c0240411561218900503142141e981c000b04444140b0b000400380300c141d007408045102e4000c0b503007401b620005103038020803500345002d01401070b009402c140c80c100c0e6945030841c2041e1440907541207040b1a0000d0b580000c2500c1b4121030006d241c020345120a40e10074051003010b090130210442c41c0500e0400301c01d404800d0a03000034020100407075903040d420a50340c40002e25032031030b88040134440c10410b0307403150a503c0040101d02040240344085094103000480c2845455540c0d008959515030313440d01c80c0aa44c00c0d80e80340c0c08512030317032900c608000b040b030281400400d42459400080c900707501d0110241c969020b0050304002800341c0c01c00455400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 407043138 1250 407041888 407041903
    0xf0501261b0403050d0f180503061315050f16050c0303041106160c17060c0f2a010c12050403020a021c1b060818031e04080f07150f02 59
    0x81c1c200e69400003020980c951150140382d10103406800303a003071590600da4210420f0500c2500f15600d2040b46443c1120100c0d0383c410030b004140d010343c4180c0014400c240c07400c0e00c2c0300c0c03581c0c02001800124449101048103072803007107641c5a804001d030740070700c00d100070750b80800c00055406060503802c0161140c8450358a000040010309078412002d245012074130b5a45c12180d03240710b52031450100e00c1072400c00303010b11000c61080054141900010402070100468003602480145034014540810002140020307005044001d0302c0c3c3c14118110100116003614007502100907000200e01246800d0010b00309a04141090741c54504040400002950114061404030390403110b03c950b25030700c0d4420b240c810040c8107000f44481c0c4040305400c008075011001d01c0c21150300b580e0300380d4181d9800800c4510340d2440002d28017198801d10130900d6101c00ca40c090103540004d0342d842420a80c1c0c840701545401c04260250310340d6041001700b0300003824400b95540c028800c505001c5164445614000c1d40c0e03088 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 407044388 1250 407043138 407043151
    0xf090f101403180f0a021005180609060405130b0405070903050c2e020a170403240b0409030c020f0108090d0815030102120a050709050f0409030c05070f050126 70
    0x700080083e0004401a14078803503d8800e800b00c0e0000e4940f009000d6507200b6800050348502803030340d610301019220b441101c0d000841590381c400b0740f82800050161a802600c0e4499100406000102d1281c885543c603c4007180d603004041214480300c01408201d40010f44010100620341400380040358001035454907c2d181a105c101c880021003107100c104191440303542d01d44000980207490000d07800904098006c0c01000c0d26008c060803960980c04c5807103144401040c0c400212008905814141104800e100401c0310101c0c1a0914500080c1114030a00b03040300400c050000070700540c104108001010b903020708100c0e0142c101b2001c41540d03450310041540030005102c000440b011901d15644140f54009002903458004889031000814070880301601c07210319160004a546100300c906030100c6401a08051610a4035000d01002d4000e4407425814800300601280000740100407000052030301035041140141004001010265400524112518075251650780c5052400a042d00300b070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 407045638 1250 407044388 407044427
    0x4031403101707051e18070e0607050111030705040e400203120a1b081207020c130c0f05182e02060a0b04141f0b0f090f10 54
    0x12452005601d0f045298222039003040c1180000707400c0300d8090000444441c1c088541c0d030340a108010042c06100402c9a038080090301c06006044141062402080c043c4d000308004281401300f5041e848140e402a1500340010300700040401001d180a40c146030030508000707240c0000040b500d07103000a80015a00148040c541c0f22800040203107041071220380c0c95001e01079400d0031aa00480b40f0700c5070001d8840070701142c0322204000d00044d0045039000d030302c1da00602c2c0703509003003001150400700c031401804541948940e6440d0201c5590340c42d80000c0c101c904480202c1c1004d10200300400b0000794000c1d100500206100b1851203020b6010000400311341038030b81d09000d8030181c1c500f48a82c1049003110340d001090100c544201640820f40e18412211420b0600c899a216800c0c48100c801030740d2015440411000480c624126035030302c4920007140300c1c05113141c003601d8006216450380101c405c5c0140020008011782d89041800540d181a5002c94588405088445014080b9140000d4055058 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 407046888 1250 407045638 407045669
    0x3021c0b0301060305011a0f0a0806041205042411070501050d0b2704032a060b191205161505030c07081902062d06030a02090c030403140310 62
    0x80c1c400b54800801590400000e002d20b9801520500303034003801d00e281078010f050408862940e824510608012280c900c2d00034250340e81c9503101c01001401a00c3d01d10200f190802000035540c003240042c41e140740c64901c0b03500030102403103800b601c1040480c8a009050b0040c1c0410056070380c012007554541c0e96402e1000c80c0d240e6030710300003510031880044880201c1c402d880c250704c2c07440c0c040d011551240748030303803600310210400302c48a04184a4000103440412044022080000c1385034201140c0d520001d000041000c80650703000c0201d00044e00b02e1304000321610449410700c0400c01100c004096030a0900110b141041c0c004c02c8140e600f05204804c2c0040003001c90b20400a1601705c0304001c3c0c0240d55180c44410101d020b14008003150780d40f07401032050a02080b00d04980249994406041c01140b540c4130910000d80036402030300501c3e1a60500842d5908001750315010700c014494260700070301035940d150900d400b40c160004141102b41a0000303004008803c0d0500d800642512054407080045 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 407048138 1250 407046888 407046911
    0x103020c070801020301260c100c020a050909032106030c0d0503070209180d0201141f1a030f15030606090a020c0d0822110603190c0210060603021c 65
    0x40c4070199000740199840040006034a800302134081810260204502d054568031000080c0c0d04e40c100310300d05034010301e80d410b2227500c0ca001b080c3d400f800d00d10140c14050229540e10006003030703080031a0030302243e0b000050307044805000c6e20303806401030b126007200c840c071410301101080d9180c4040f9003041c014100c440c52402030103000c100780e9012942c0241a1a110319164000d00510341c8442e449051610420030700c0000280180164418070001103c01d640c3d550f40d00d1020706a50a421081c049800482c0101045405c81d80030f007160404808900315a076820421440620002e00616010a450049811182e01c0d54007091880d00858201c554840030f446881d88100240b0a00807120480c0c41183e0144c0c14058101c400f007881100b4203c41d280510740420302c1c41c00c2016030088000c1c40810b0f014030020061900b040a160084000c15481e175034049410074040403540d140b850500580c3c40f1140381054800d960141c42c020b01600e203005e40c14a070ba580100072030079007d490815106034441e55403494 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 407049388 1250 407048138 407048143
    0x616110709021308071e050607030c12120f05041b060801031518030305070305061909020a0e031005010e13030f0f020c0d080405040f0903090e0c190215070e010e0103020c 75
    0x50b10084c016100e0859803643c6403618855029094081001d4005000503d4508078065400750780d01500d840c100e4510a5403480610f44910305040b05010071458002a1554070303114000c0508441d420010703240c100390501c0381840201081507004451980e00a000c42ca50103510b10381103a03801440ca1254003440290714000e0007204c1c8189080701c1c0561114028140d041e04080d0007165103840400032501c0305000d003c80e4490300420100d10b60407501e002c000320780d000d82c01402241035501c3c100026a1106c000a4203002c0b44403040c079480b548890061000115221801d90014030084141c2101c9109540180090040e000050148843d61526070300c0b4500074803041400c4140100f00105804461809031002e4102c1e02601e4008c51610f500d40c5651901c034443c107440a6050740303524040c3d0345060345100501c10300805600049205024404001d1910340141540207525005040d050801400c45206490000c0291007000070f07010242c4007503604840d08507d074581c00e00e400341e0b6a4104a01092 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 407050638 1250 407049388 407049427
    0x6080c181005060a080a05160c030c020301020f0304080d0b040212061e040501060f180803071203090f0b010305160f0b0a0c05060c1b07060504170f070602061611070902 74
    0x15000700380090594101340c1d11025403032003124000410003003034441c0c0105081c411410481680460080d00190010078025150703560111b01c01000549000300f6042c4111845d00f003074500b21000c05010a154107155028080c91401d8070045d07a08609203c04010781c0c02900301c010705500d0081c140f110952012410005502c1c0d4050300140043c800d030b51756008001e21100b52076040ca00090700c501c4c4203024188048050318125071448000703504001035a194292010000503007034003031540ea0340e51080041c40281c0d417020a035008140050f205d603d1402c09a0412400c034154030388a00003040144415128510400d00365442317102c8060f124404500190380801013031002404030301c105002c00085086440040070404588000030103144010384006940312541d0240402050013448240040b54030251910740c4c0710010703000c94600e03040000215042c444250000350068101d1820840020082441100c80400910b80146000d480c08841034690705a40603048071903400085d0002048078060001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 407051888 1250 407050638 407050649
    0x3060301090212030d0b0d1203020f0c011a182512150807050d0314070204090807030e0a1a070b071806120f0209010206040f03030e030703030f06080c1810 68
    0x101100003803c00303802d0392504545040c00107541400441d40607030614072140040598000131a40a5040c240010740180d0085020582c0010040c403400070300503400d00450710380c0e1142d117000c080345650200500038000c0400c4400401c0783e17941024048400103d50110b00303c002400c1d20303a00d000124801c102c803142240c208410240d410045641c0b850804400c40604a40d402030445103115600c0c01844100c4c0424032001c0d02103405480441d00d0440004000c0203200e20040000030594000e0b501d403051a00920b005400103100200100158240442c2160140c40100143e41218030007048516880c401d01a0050803141c6a601207122a80101c00684402c0c005869025107a5107645006003c0340c450181501c1042c01d141e44c2e1028a4001e1080351101030043c2c0c050092a900e644070901001c42c0c400003201016602c601038502c40e1018006007408507c20f80d408104108403103800b17402e541240d00415141c1e0481c3c01811a00e41e10b81d43c84007400802040d0100480d9201300903082c4103002c07035006 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 407053138 1250 407051888 407051899
    0x6060507151503230606060d090503090604030308090105070306050a140f03010501080f2a010c03021002031006030e0d1b08190c05011506090b2203030e011101090c0b030603010902 79
    0x48100480070080c00415903584110500400302118240d641e000705403200c5400c04810002d40c0240119274110071001c6015104503403030b141c65840410460ba0095005900240c0b16030140616200203003d000d4100c40d02e4a0180581c904060018034080c060b4400c01c0070040103440c0c1100a9114450036211002008000f0491982d45080050301d6100c449030065050190780000304484503594080021140f000c1102c0700124042c0c40159804030820006a00794400c403030040440254a0008502c10711000d41e00c50a00307841e04a018094031240044511203401c018464030030750740d002203519010b9421408440d0042000c0c140780b1102d11510740d55000351078000e852100e5032900030142903a07062040c40200b05c9041510600302005c43d0a008440c0001d2103400208140064000500100c0c50000111280548201c4024508e840b4540c421001304040e142448031668204c80011840d151078002801603844958941c201824540a0803c03204e00c04404117440361425441510080d0b1701601 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 407054388 1250 407053138 407053181
    0x10e13020421050c1c020a031b0602010203010305030d02070804030602070602070c1d01090c020f0601080f1612030f0318110306010603060308071e02030712030f030606050715 77
    0x6051029600ca800781d0344503128040e040148201000b480102a550400084d200c8241301d0b40801450140c034000c03115091558182500140c4d451545030402035100d0445032a01a0050291809041055019000f51b900c144010400301d000401141c8005054110041c3d456126140c00c100f54041e54002a1040e480801d4010400207030340e0007050140d01960005000c183c0d21400310070f0607200083c200c18000007520040021815a801803c03c034510790040c1d80b09282c02c007200074079185007640309140e01c0d4000c07441407100c42c0d0117102000f030212412403a009141c2c10040d02c050402820a4001c080040c80c9880f1410075109602c030766100c89408010744a140024106000d500170720590b00d070312030302805000060380c074004c0c840d85040300d0703100024030705107003090b03c9049981031004144242282c14000c1000140c0d418040300000d00440d81c510500e006260030000c0044410a0914092624105081c080c03682c1040544400c81c0d4403000ca2840e592840342107901a10105c07803c004084036415 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 407055638 1250 407054388 407054419
    0x60e03040e0a0c0e060406050703120b040207060605040f02070201081f030c14010e09060117101a0d24030807060605090a2313140f030d020306120a0201021209010e 72
    0x1006443c042480d07503a0741d10856641000c1004a22030b506c118404500d0420240b40064040c5202e010000d1400d040003c0e041c0452012409036400761004036a810f545031010300061a0070310464901c1d400d448411804c0084590010301101000340c5003081c0d005154514440e143d0203100d07903801075a400240760900c2a43d8440a200341e20048000c075002c540907001e03041103400c280316000d02c01c0700141c2d9103188c1d01c80e6140c00d01c0600480645540e03125070400310f0229010592410200d112600601e526507204102040c407401c50384151072040e1000c0c044a20700324aa0b160030001e10036a5080441155901064589040104003d91016421031481c608000d54404107501011003220f40000138161800c411010401804080f5a052140300507144070002151468400c1407a030180801165103c951170f040d0245140c02034200100000c0d0000304102c03d90402e440c03079070031041c8400020004c02e039842d40041e40f603204500781d01188200120380035955138440d40c0900305c5904054081c2040c9168070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 407056888 1250 407055638 407055641
    0x1050d060e240f160302090621010501170601050901112506090b030c04120201021002070b0103120809121e070501050702120304080f0a0e040e071401020a050a060e03040e0a 76
    0x42c0344060341d00c4400c00007020030540300a881c0c801d5041035000c10242284003001e4000750410441079410107414001c0c241481d110111000c0300400d100032142c00366240400041070000034044514203a0404028080580d0b00101512140b40e000d00307080b0007200114582c6482c001d2a500301c0204207100e102002ca03030311502c034554000d4030b43d95039402c2541c0307460304e031480a00d210541d8003518040c800c2200300071302002844541d400500c1441135599404100c2421350681e08201c13815a80128040010803c01241c0d880c5549051014140071203285412130b00d03580c0f1100c0d160066444000000340500e201a001031400101d40e003540409501d03410382d03082c60703802000101c82420241c8034074822403440d0301e858400d80f4481ea610030300b40c80c90320040c01130125251300006040c2041c401d000981089598803401020382d85501403000703107442841c0c54412076503a400070310024155003100841e0303404500089113a51481d0f41000303000c035940310f8440a05156100d0b581c48032181400d40000e01001d044103 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 407058138 1250 407056888 407056933
    0x18010c0819110703020a050f12060108010606020c0a03030503180106081509061e0403050c030904061202011d0d02040e03090316060908031303031209140c09010b0306030601050d060e 80
    0x890741da48100c640c461060566030100e0740000380d03000c0c102030403c202624083d8543c8d03105040c017034541c007011514020301620b800420781040b03040c1d03511028180405a41006406c1070054211540c070009461a107000d4800d00c00600a02403150203407005240b558800d401507030050034a20110b03045050341443c0d540c44850152a202e01c03500404d0301055150f00300c0c0b54058150f0940828016803610f5681d07041e5042da0000014420701d02050119201d40d40d2136124183c028218003140b40e2500007688001000e111110660308900a101c403880703044c54490890042c5ca466040e41c0007c2c0c0a440c2c000c0d414075500400700b22a81c035114041c1980e12004036a1070001c122070035911032069583e10b0300c60040c0c4174046d0203050080710350340d03080400c0880e201d1131500d03c1241d104c030000101c4401d0390302c6045c403a400c40c031049000b5074054410203c4600704285441d0060a20303041c51421401e0a0780003e8a4070018881c0a1050005c20703c40018020194800c009420f401000c03200541ca40d800540e500c07128 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 407059388 1250 407058138 407058187
    0x114030f0f15060d030e0616060c0809010c0f020c0402090a030c03080408060c04080604021011060406020c0c0d080d0506060d02130e0c1303030f0905031e0106061418010c08 76
    0x3802d2020480c01d0421a0312031400310781c19110450002d160805002035034000c9202e0390341c115a90074030034020400b40c1c4110054110540e4881000746841d4800340d00791001050043c04000d88003040c0340e4419404a4141c84200040718056550603400d400202a1032242c1c20281511a09103030000800646d40000c0c02141c0b0b60a0590780c041d61000c1600131706003c0c510072800650400380019006240c0940e540c0a500d00c4c80c20b21074003140b20340140d01c1ca0600700f00d4045814550004024450400070002d09454150031107809240f0101565824414080c0104400b00303240c40300085403040d611241510070389811128210b4440e010080f109240d03030641e205051048040001003200c07401484110344d0000b58800303000c0d840c14a169411211200f41078035043c100255a04003103025038080c03040640000c690341c1041d071410000c6e0082e6084030281da10807014080740080300200d0448132003d0b51b0003060b410101300410125140140c07508501010010201207001a00e031500f290714000880101c01c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 407060638 1250 407059388 407059423
    0xe0a02031006080f0c0904091203090201030b0307120f061d01090b13080910050904180204051f061206090204060c030e06090a0308180d050a11040c05030114030f0f 72
    0x640e204015143c242042c1e59103080e0200e400006400d00c40544020100a40040e00025483e003a6441e056030807540950b80c03100081e11180c0100c19903a00d8040d5a0300c485040300900021442d010000031981d00301440100750141c0191810240110342e07014801d40d800044600345450742c402812402005042c40803188582c84001050950981c0603000e005150301c003400364500300ea0300c030030040d4120007117100c8010800c0c100003c3c07c40f92140e00400c03007004401d480e8082111883e10400c030580341c00503d401d41040802070760030b4550020a8040042303611600709210150744080141004e42015048115003900000d40000e4980d030001410b003d407030203a038035618400480f82c10480030380b044000352644100e00c0754007480820989002040c0d171034880104200c58003582070104a031250048425241d80d0401034148051040d08038202c0e11400e411101003018800b1803401900f14041806041207483c0c5032048449561400c000707071001e50480100300d0388805060110165142a070901082128 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 407061888 1250 407060638 407060671
    0x5030702031608011505010813051c030f200913060503030304080703020d0305010303090924030f290432070603060506040f060302160b0c0706291201060e0a0203 71
    0x1521049240f07050310b030140d448600c1611482c01e800c0b1100001c020558544c001ca0100594140300500511981813007a14041414011450050111818104581c2040c1c14510f203022110010004071108402c040702c540302c40c406543003c02c00040c08560001e503010720001090006120469003d410710b54465402c440c40114001c1e400c1303054070f50a10006000c1b6181c00e00030b01045a0301d030802c110344110b590110788480b1301d030703440020346040c40d6000340e4010303000f44181000d00411803800301c090001d0f00e8070385c41c0c04c00c2c4501d40207128400080029014184c035040d540c4030060000240c00782e000b50305030280c454080c0650807a88802c0c50b88100408070b898010000742c2400c0c0712003a18100d4a540540014091400e14140c0195004c020200c14554404110000052021950a008001c2c80003010b4844000e8605070044440c89403a030580108021501680440c02c0b1070440c61a41058404085104652801ea400340104e60800182140e641003082800030069004e5441200103d5010445 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 407063138 1250 407061888 407061911
    0x80702040b04140a2007060608010e07031a04030507121e0c030909020c07050607110103200304060e0f0703061e05100e04031e03050a05011a090d0503070203160801 72
    0x1103d440d2400c1e40e1441c069580001d0f40b03100c07291311205090503071060350188107481c2c0101e80c0c20f65011a400319030040e038440040c401c1101c244a10130215044000808400c0d085480c1c07007851580c404100c1012000030000101050306c1201035516855010b042c0c040010507004000e05a109003025400c0007119001c900103440f88200b0b8070b1894160141c07116a6010b040c2101d0501943c03080010313015620659074001000d4545900030006540a01c1844c80410ba01c1000141a100c0105620f007044810b0980f0626510140e01202d4105070311071400a40b4102050a0a00b88404080d0b460454000c00c4000024841c135600104103040c9041e0000d00f88811420030007085a400707403401c0c00800b40b00340d8107114881e0000c0016402c14080c0c04c1034070f40400505000000d95010b00c51150019865809002c407001d0b050003520701602a22240c4101110b11107106c001c9405071600881c4219206101d9409001e014011181007640107070035a410305100350690605a00d00d1b01c20b0340c030217610304070080a2 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 407064388 1250 407063138 407063141
    0x519050304060b06160b130f0503030405060601090f1502100e0a0b06090f012102220c0c030e01030b0114040b03010510050c0a080c25080705010503060f0922080702040b04 75
    0x40ca1550861700c400f00345c429441d1030050840041005601c0e500e03541420011034203052640080314460002036640c1e1030710303203040da09286c0c2c068881d030305100f9080018800c4640c824070301c40c1a2008011048010f40b0200360072032130726054440c3c0c0150540703062036090710740c0c90120b00b603408a40519042c41c803948a4005005100340c0881e50304401100540041c0140c60200460301d40310084400c049245c8081500003894915072241c14080c0960260600c0841c5c440c9401002489491810070040811306901c01410b541c00c8800110704150b6500e18403401c07a0f0007081c83d030290018107515291180c0d100c5043e80402d80c401e014551055107200c0c807502a00340325000329000c1b940b135070700901110b001c603a44850594010503140e42d00c034012151200032012048100c48151242400b4040c0c40d0740c030f081b0899007000c00a42210341085820403c0055a849003500200812415603d032180c0741c3e01c50345440554140c0340002403030783d000d103444035040c45a500007510781d060080710b08200050032141040f0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 407065638 1250 407064388 407064397
    0x32b1103041e0c090e0610170604030e031e03130f21020414040516060302040807170708070b120c4e0a051501020307080a0519050304060b06 62
    0x30001d0800b8056040c601d0b814058480d582c600c2400384586880e2038541e04d00a542410180940c564030040412485001041414000744803864401c07007002c0c0002260303500c2d4900104050148480c3c04501005610b041090001d10399541a19003800d8035600740b01601d0754403070034007086508001c0c000860501585c21050007125058030030040500001c0c078095551503049030090317034010741da8400d034203040c000032030041e00c51441b5201800740359400e00003020140c0c0c1e8075003100f0308051050106000202001416400b50b420008500c001d190001113000d2a0095541003180603004000d1b002030007030380b441c000d001d03244030344a44844e082c1d4070071102c80030500500801c940440031811010324610700340400500021564941c0c2c0e4490010407071141e01c004007031685036540000c072030100110b294651140d6a00885c0744100c048016950b0b0000039a60702410a024214000c0060070070825400341c41140d82100340281090105019030002412903002214162181802e20121030f1862400e603080b10b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 407066888 1250 407065638 407065643
    0x815061c0b271507030f0f09030815060d050411060f0307080108030a0509040213080f0307020f030303041a1906091d160b131d0919030f11032b110304 66
    0x80070303a500101c450a881c00c0e400740c40d040c14190340d02d681055080c1e840c081d100480300d907004086080023a500d40207200410040110468900e01d410071304040d0303540ca089a04c0c6003501d12001c545521941840f000d06541d1601c01640a000018809000200b0401a622581f0940c85010b000c0e070f60340c4074513a143c1c4114110100044c1e0308004551b02440c180e40601a044007040c00108515194100759180914034039070120b1a600124540007145003100039007080104c140c02640c01c5051030356815480040e120340c910030503280d074070000b007024540103640f044054980405009480e50741014070001e01c0003080c0401c2c2180d03c4240000d00c1440028154155881d05030710217101e0303252000700d400c0390b04040e0b90f032032202c02400f0300080c80c4400440d00d004042074404040d5014108551400d00d000030080c03190a10300da0703a86910011a03004480307001c0c07512007400c00210000d00740030754a041d40705070210111041c0142c50b403001c00100d10320240d40300c003074201d02c00c11064030b24141840e458042110300 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 407068138 1250 407066888 407066893
    0x1020f18121603140c1908011808120612060f070e011d130e0105041b0f060801060804030e100c020918030d0b0103020408031b010b06040815061c0b27 66
    0x400c00114415402d07a1400c0703601d0181c030707038040c1e03000002800c07005020502590328031b414005111501083c801c6d40c942c15103c140d035007803403003e0796100c3e6442d010310603600a9031110080000d600e501c0b40d15440201120300016640c061402c03201401d42c2100980b40c041c0002e032281e001c00740c0c2f9402400039500903108a0642c0d9a100002e00811802010113008108115151a100e1080002c01d000e154001c40c0303d2070840710b84c006c0f0f828414481483e0b507441144d81c0340c10041c003013000d0750300503000070b040d06e82a1030300540701c0c2c0d04d43c101502c0e0092581029074100d44060300c10040107038041e01d51411144221900d2525448040014800d005036895908003070b08200034441c0034442c15801a6200780041c100907062a5035189403d045800590384529011204050175140e0711303082c0f041000c0c014084407400d080c5403c2030242c0381c0c0c55190824220020203c28003040603984d902900d01241172010b044a14503103c180780c070f50140c0c902030361032480c5d03c0108141d80c400b034050903500b5400080300da0300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 407069388 1250 407068138 407068183
    0x60f090524031f0e0610030309140d080715110301050127080601180c03050c07020609040f020309161202010e0904031404150e0a031707020301020f1812 67
    0x1025451400100c1c0c003568944035600054610040d44a82e401c1002c401650001e04005000012410640300070031464996050003c140300107034218840130241c0e058004280d48010206010481051850070054030a0714042160000c1100c0c0386c1616080044d0404240301001c00040e105004e40020300030280410011109192210b20500d400c6000301c40d0342d008928003d554011140c1009000e8020004190f45e000126100c1c4403c0e0264201c00c00c018a002c003c64541940342080901800100034441c280009560200317135226044410170840b1450115680c0c02e092900704d944001083d144d01c044c0d0751030031000400d5420030441d81c42c0d450701038486945a8080d2020043c0c2000d00820032024060021180140188048003400207807509001038004212950f1001e005c00103c0e400761442500e000f1410f00008005501c1c030011209207007242d036250a45440005e019010724079002c6060200800c40740c99403101c40603960349485094030585e804a881e050320f00d03150000559001c14100302d030070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 407070638 1250 407069388 407069431
    0x3022515050f030405060601080c070b060d080d0c030b12010203060a05010c02120a03021e16090b01050c12072306060d020f100f020705010309020a03060507031e060f0905 75
    0x1010280c2150040c64114500040c114090500c1c0e00300707840c00d4a00354080420844030b07503042800c454200380c416408506041c4103960f074907c2910001d150038043c20003080c01204102034941a502c510449800034415900c032440002d004111600050b4400c441c3d10401401d0b180c4107101712070090300b010302130004540c205001561600c0448004a801c176940007143c1d4500c15043c003c680030988039501420301d00091040c80203c101c40843c403980c0c241c00c0b8421048101007104580002c0f601c440002080b40c401c68001601d55003e144900c5605014115104400c40d580c0c800a1019500c41d8049070042c0504803e194500303140e8000c018102e6010310049a0180707410039146082920003002c03e501100d8a101003000f00401100c0c040201e0030054484084540602c40300707010704420328042004145070740000745000c50a00c0041c00f2540d035807011a50041c4241c100c0c10003402c1e60080700e0441200d442c0401c000344120b100300d02e141d0030112004a4030100a003c1c2600884594030605001110307403 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 407071888 1250 407070638 407070659
    0x10060806040b010512010308120f090d0c0c0906080708150105060328020703030e0705011b14011103042a0e01090507090512010b032503081806040b07030225 69
    0x2c41100307061000901100010b61030307105e08103010b144212540ca480e90580c0040c90300308032029080460035404070040168030000092120b1150001d8506407032425030906142c00c0421168205005483c00c041e00070560b6040044d01400b280c0c1448110b0320320042a0010502440c800c1c0900c0303600c148100b01041e024130204200c1c04c4156140e003c10300b140600710a143d0200e03440068200e000c00c0d00c4d2820a01c95280c14070260004150a0800410348226448a00540c800d180001041061141080c0c0b1440d8400d50100c0200003cad00702e61681d90a090074285400d07905040d0518003542160704220311090a100c0340812aa02050302401903400d06000c44040c0c80c0c01001d140420405881c0005c0a075a182200c41442141ca400040c003594400141402d0481c40c0100b0304400d202c0400034900300320000f81040440c0e8000100c65110f842102d8020f03010445552050790010000c41d012510701c4040c00200b401900c01d808581c4000d05200000c080d040d4400380702401d103603040c1c804001c5400003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 407073138 1250 407071888 407071901
    0xe040e06070f120c0804150603051009061d03030103020918030d0f020702150405100306050f0609151c06050108100b090103060e0906041205030405100c0e03030315091006080604 78
    0x103828203400d08410f400240044620982602c2d0004e038150041c0001d00619240c0c80d2100300c400328041c40800c3c11525034550f41c00010068a40d020740d034114070300a0140541c001c40c60035036000d1111050b07080c0d41c0a00c1395250020301042c1c0c441d003d1034000c5081c601109629508d40c14628000d9420105010b4500c4000c189800c9071219064003041400016a40d002260480081340900c150b1a1400c1109000d04c459418000d0800d040c40c001e07042c449655003545041140030102d84260703443c0710f07a802081c2d001d170005c41c0c1400309080c081000120002c10300341981c02d40000c03030b00c10441281d0b07800044a142d05e080c0c035402c03070060029806225100b000d200402c910001818003088036551000c882205210882e403d0380c4a030001c005110800c0b01d00300c01124801400c0c90030a085081c15107413141c1385d80e8088a0030040d181d0315044040200d008141790139440324010306494407031600d042e480c40e882c241601c4042c420704c0901c0003d000580714840c60001d4a03543d81c0c942825603942d03024000200307030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 407074388 1250 407073138 407073167
    0x7020612070807030e01090c03020409060b09072c090a0f0e070909060605030309060d020319090b0405070e19020c03040801090305040303020d0509150702130e07060e040e0607 77
    0x102002140461001219028007548095039869010f1a0045005044801c0700c060f811903070f41403c3c65500400c44000711030055a40403600040d00400f2883c000d40203003c0002c200d901311001a0130088241c0d0030440440c0c19003a00c40ca400301c03948407500c402e8010414240c00c9640195404e0106070041680d50180c4050f034001d5000040c8296074140c0a490058a40d01055501e034695000f0390130400300380164001400154000c504141081c0001084d43c0030300603080b090b4950120028440c2d030204000107610f800324000802104220381444410000116815119407289500c0012041c104c140003a10500c504a46160514259110705000e035124100d400b2852101b8000800d0303201d030a2199601c410311a85a284da16451403034043c0c1010100020f01c0f090020500a0010b16210100b05411800d0a403001c9540c0e030025200098000c080d00000c0d405003880c00c0c611780c2e507c4200203000021f1f9101900c0f240240604131003000290b41c01120882101c0c0c001c6004034100350300414070320f503507181c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 407075638 1250 407074388 407074399
    0x30e03030f1930060902041413090204090803041208010602030f1303050303010f0f0909150b061c020c10020304050a0308040c03050d051806120106080711070806070e100c02060702 79
    0x14200c4030160403501c4550b400c80c0f02c1a41c400741c2003146521400300100201c20095042c030f45000d402c01d010303510880209010745622030809102c041d1650010188550080041005084038285803107186c000b00c1d0100c448441c0354260031003650144030805e0480d40075030700440c60a01c18201542403600100700008080402110200000d881480614080e00c0200d20841c1d281d071410300325040fa200241e01805015103400e18104c0403481400029806601c036003008264040f02c4c4010800500c2138000d4070700c200854901c100400e0b800ea400511f1407940403001c60350000080030b5040e0491005540090a55002030040c800090041040c2d40e0701a000d501c40d1080d01c2d0f52612224100b141e0303411420300145c030000703401c9400170500115085410083d520181080144141002d580006002d0301007846030140014848034403c1c0a28240398012400362032180b55114121981c8581c290340c18004140410b20120780c84c14440c2d44540003114039a2190b228080d02d4081c000d07103503c94241a40c008 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 407076888 1250 407075638 407075657
    0x130210020a0b2d1e0714030606030c0c010203090106050102062211041d01020405101b030806040e120c1504050307030e010e0901030302060906070306060e22050f04030e03030f19 78
    0x107402030203d5074458644081d140d015074807910213441c1d0b50400108040300b40a03030b0b03510600c000d0701c0e030304150b960001090b9003683c1e881c1c550000705519400358140c440c04d150300001c10040c0322a410f411410445000381c08503022903c49500d0100d10510000e41c04180c2e81e4681800f801103210307204000d40200300031384001489032a00c2140801c509000c0c03140f08044e90001010041401c100303045070140482460070060ba07090030301ca00c2e1a081d0750b20502908014110010504d541d90b1603000f00803032450101180d201d402d60b080c40e07990a402c040c500c0d0016000d910f629401c588842c110291040d135004d00910f14150f07413a5816540d910394000e10504001f104100400301d42c0700c00c0c60990180d40a90000c0c022840e00034443c0c1d02d80b0100034003400801d824400704000003a0400060000060100d0704a204501c0074002200603104910010540500301402d120341c400007844018000c81c000d642c0d0b107140c0402c0b08203069aa1051090610840b102080752200c2c085540086100100c0c00f4980200003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 407078138 1250 407076888 407076961
    0x70311120d18120908120915071403041206110a0f140d0f1b0e09060f03031624021606050411040606050c010f05090601061103070506130210020a0b 65
    0x40f0074088521101140c0b402005101d0803108100203070600390b564440500e450100d0002c522a0010213401c44089035020030300c5402c0101c40740c2c1c50320000321403800b2603481e25540c60740701081040703000c41a100e451820402c6801c911f8603074201c810409040d103c0b00082800c9103800c4a2207a0030001200c2c3c0d461003400144988080c03802101c400050310301000c5a09420341c0c1c018600320003c2d0200f88280b242840544400e51185410300b507000c4011100c0c80c1c400341ea06000f1900f1803091041806105400100030000c104613403041106c42002d125440b000a440b02601704100c5c410499090242850001482c0000d81281c01c96540300c0e10800014054200e0b00021405840103900540c0210300c02080c43c0b03041c0e4100b4810101d40300d044e0241486141450000c090301e031841070080e0006c000c144400700100700020800c449080c0e0b03015080711218070705100303980701008407410224403c040000c8040b100e24030020791000010780003034202800d510307203840400b14071550360400105a00705010001a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 407079388 1250 407078138 407078153
    0x6090403110105090a030e090601080a23090708010b0102070b07110604080f011406010e0d110f060a030c0e010c08030a0b0f0d0b01050f030105221a010803070311120d18 74
    0xe004c400006002d000050303e805408185190b500a015900b0780701040b409aa00c080d0850708020135542c002100614084042503074084201d0803102c0301c80310790a01c0028070000455104889030341d80200095248074004a8444503184a0302a41804c103014a4020500081034802c040f6030003880b240c645582d4110f85030919440c200c00b400c159565503c2140c80b21076200b54190702c840c00b464006091003025001800c11508c004021300700780c0d40e410340c43c0d00c0ca881d00341030200401001011140c444001d10301c004e019180c900c1821001502d0f0040d4076845501540b0152103031079015110343e055507141076407803006020000d24140c0c1301c00b0203034010045865000318801c4450164201c0d0b6200e60604080c461070806480c5007a001e40e05d000208290f403562452101c00d03060b08400d10300c1c1c001c44207003001401000844064549041e004000103241d0701d0000023410841d05c2038907214070405054101a4880d218040c038044032080400164180741c80a5003e201c0b4a0090148420043c0c0f1685a595 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 407080638 1250 407079388 407079391
    0xc0703021f0f0228050106092d021207081009020a021b030714060a030603080d09050d0905030c0d140d03021e041220300601050906090403110105 64
    0x10000044100700503441e8031448452045407240010141c0740004c2c4140e07003003020708001c40d0b400440e95164440070040207401440081002c02003d101164084041d0000908041c00c10950b481d9034a00c105032420580c000d0f50b6a00301030421100b01030356203050540d900729006060f00340f841c1d0041c6000c28205003d20281110410301c0c1e0040c41e00090703040d100e000750021003004920a074401e01081210303143d44c4100002084050301c515488102c0c050056015080c581c100400c1c80c100815150000840303603010120281c0100101c40003141800015920350719640690b0b0b815821007190b04e020f90903c0005d40a02e03c2c8180c1003050002000f40201e03081403598148440065000a00c80b50481400d940c07c21200c00c10b440120300d020320f00080c08000101080d40180102009540c241c11480302e1018951340c09000703803004141281c200951104100d102e2000c1c03a0380400720300c1c3d443c2d48000000f9120305035180a480310341651604401c11a501c2002402102000304220710000d0880081c060117 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 407081888 1250 407080638 407080669
    0x1005090c0a0f0b03010603020a0507050706031413152d09020306070203180118080607090e090706020a14010207020315010e0a050f0a0e071a0301050a050109030f03050c070302 77
    0x8100a02621007006108031050344124200044038500348000341d919000ca904603186410010781d40c078040d580c255900d000d41d0030050a5401000400a85141c040e00700d184004015102c0419660707a201c45c03820314140700c0780c0c041c090744400e0300380700c401d00c0b251351151280300845074a02e5614550010501c800608405d42c1b0400310b034442d04a44118281040096001350840c006181841400013150f80e141408090060410034001414443c0c3d080381d90705407018020344811b03104140b82c40f003800340c8208482c0c0304111003840b01e80c1c0020802c0001040900646a159015002141072900c6050044420070300148041d5820000300e00141d40800409103d0110407240000a40c50300d900800d142000910340051a0300301070030031507100d40001c60700d40d2111f000c020000d2255410a82c007403820b0880e40003070801d401c5e00c82180c0c2549400034003850486800b154404841c3d601d40c00115a076020341d220082030340c128564000e000a0152001d46010a41203048a1100da0b80380c002501703040030b20b10382 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 407083138 1250 407081888 407081893
    0x902071407060302030c0316260603100e120d020d02040303080f06030604030c0b28061a04060f1d090112030807020c030715050405062109060c030109020c100509 71
    0x5410308030605102010040229003421411850091342d00c0d910b134840104018084000085c405100c50300598217118140800812220700c08407030042d01c0705160095642500c684526140c14100811902801002c0320458000c2c0c1040007042e210100c0580180c089124555000c0c000d00001034001e1024000950190ba108003050030714921011100c240544514000d401c500200404a03030004144080c00398001512a1242d442040c030415500301c07034100b501e0911409031407080d40b5809401040c01d8600103e60741c85081e40004440200b8480d81c4207040104560003828240b00f40101111500d002082c2072030303107020b0444000036042c0002600400c1c4045001c102c520181a0700c120500d41c000a140018141c012079540001c0da900f403d445103a01e00042c5101c2603110b2889079058400502d030107801c041e203540000c515901030f81048030115404020701c0000400060001801500440301117000c10326503400e0100b0740002c0d41c40029a0b120500c501003e0035070088540c800c41d031051204901 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 407084388 1250 407083138 407083163
    0x60903030c12090807030e030c0d0b06030d02030711012102070b010311181915080a03081b09010f0c021e0a1505090907090806092b0c030f09090207 65
    0x4040c0c0420750b0100c1210400b8680507034500090307210b5049900058060074404c10340c0b880c42c03001074a071061000c074140e000800380c00b14004000040b044e450003020110190740518010400480c1c2ea8066000060460103a0714002c031055402404c0c4010110600d0010400c0e01020400e00c005991103640101d862000342d000420901c07104021501142804a4199844c2c80300a21150841e000151800e0080c0280c07610050020a150703010342c20b0000c1d0154003041c0d1030f0b03407a079625450b400c0e0080158040340c0d0440c00a100104120f441c01c29480300640b04a04042c05240112400700784041185d0500009020400142c1d6582e191401c00401d0040c5d040014048903080c014200d0307041d0302440d05156519201c2c0d494607000001c1d41d0f40d00d00d060325216083d55400c1400c40d80041e841d88600100e000d0f840500212010200e0001c080d1114030051144402c515882c7c0c80ea041124501040024100c40500c000039100e92500c5c5140700c0c80e89031001b142511182c54900720781c85880102c61090810a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 407085638 1250 407084388 407084411
    0x10080601030605060412170c0d020c1908060c13030803090f150603100f09020607031e08060d03200303090c0a050d020d0b09010f11030601081b0a0e01020a06090303 72
    0x10341c20240c82c060b20b0080c141807a101c0a540d026180c1b4200030240c01ea661806200701840109903000300000104a401000b07801d04003a413a44040c44195009945080601020360b10380a503220840e08100000c080076601e010011905822a100344001d14000407800000305842c00d01642c01641c04101078020505c000036660314100302410340694140d040e00802c0031a81c0d0120303e01189a00001340400d2000780e4241400040c00e80060081d0f201c0008601801030552140104005400b54030a0000340e0007440340a8502d1403048601c00e502c080705400c4003000034404d0f4141c107061400c2c030078204042114941403500b550812550400e0360f80c0f02c0e2120580901d09205030400524082d294240251020340200d14200c001803006000401e0341d80125481c141e003540036203240401d4400400003a0b40074030a40281e640300703032111170002d0540d40105140340d04400d07407501011205100743d0302c0c190340b00360152194201c0069050650090825085c0890035a0280c0c514084c4240d90014142e0b0040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 407086888 1250 407085638 407085641
    0x81b100e0d0207030c060c050c03010203010e1e040b0103240c08091b10050c0709110304230c010f0c0c0801020d05010b040b0904020f0702060d05010e01080c0102071a04051008060103 80
    0x30418808541c040b500401c0460a6601305d5030035181207103040662511541031641c0f03090200040640c16610010000548400f1581828000c803994640112143e42c065455507005030700790b501070481d100740c0d0010000144503040e05910455028000007410640702840700864500e0b07400c100120303805404000c4114424840d0b20381030902412b00b8290319518002081340403078074402d1072052223030018100d44445000c020180c0204086c09050014800c10040d0580c1600195070844610380280e0f1007039495140a010581c0d064041001401d1020402c0c00454138440100721b442c003401148440c0d000403604400f03003440900954030000d6510310f4407061a40498505a100303e2606d001031000b4070144c40290f0031100d0000b002c03600580c5411800704018102d00c01d00c0e4000350710000002300710080d10007075002070b17040700c41101400b125030b81da0300d8405489101c200741042c010307000b840041c86420780310036001d20f1103412000e650342425242c0020848681d14100700001098164081004a42e0f15 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 407088138 1250 407086888 407086903
    0x3090708010510060e19080d0f1202120f04020f03121209120d1e1b0e040605060702042309070819020a09021b03040b09090604020906030103081b100e 66
    0x151486501924a80a8020310051400c0e10317051240e54100d45507180800c9252054000e46002005d40306640d5003294040d26800c560000c21012846121254008050b40d00c02c2e141041c0001a110b192603a0341003043ca8006030041049a000c001070301c2c018965142005030321120501d1990b0940d4489a40185500c1110028504c600030792111f94a603e005415a0070f403082462485800700e070001e140f0400c1d614800b0f00c1301110107441c0c030b05881808581800802810346189a4807407143e075002c0942400141d91050045907001402080000c2c01800d040d8086038040d5443e00c02e942c4036070118256041990f00903540f0a945a000034410b00642806024182c802d01c406111026116410341c081150106648a0380042c2680401d50b2101502075080400c03002142c5000e595032070303445500d101182e8002d201014010300740d400c0010070f00c1c2418030840b41e40c01001410181540c1c03843d621100198002500282c1161070301056503036104040003408104144071002142d801440d00070355141008 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 407089388 1250 407088138 407088151
    0x5070b0f0705091302040302030616110601050603131106040902070c060f1b060b0a090609060501050c1c1202130303110d0c1115030a02030a0501060507030806090a0908030907080105 80
    0xd221051000c0c194215080300d035501030546035078000c030820601241c0240101e510181d014040c06080045001c00320303c0654281603a5202c42443d070710641d80a81d41c90a0034021541c20034810001300380d10000c000c1000785410321580201e4a1070b80303e040800c090350040c0d880881c0403500400d0340f4040217900d004400c041c11281c40e051111800000780209840250745500520300304400000e803c1c41800d42001c603403036101418034802166900d101d080101200d20403100c034103182601c0030a00c0d45c411000c039070100340048010400b24802070700c982c428030300000103d424019500c1d55110001072a00140c2801402003501910311490350402800c40c202030b044403000340d00200340920886410405d500d0000d030308486904140c03c203600114240c19041500502d4803c40030040041600890b00298880c0c482c0c41401d0000c0e036a1010290344074003030084010003040c075410010b03030300b82801c0c0d1400b540314084c480b01040200091701c83c100254820f03910030301c01c0e030820001440072001c03d003d090341140 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 407090638 1250 407089388 407089411
    0x2405010c03020d030b120303041101030f380904050309030601060302030717040c05031f14010602100c0c081903050601140d1802030f0d12050c0d090309031205070b 72
    0x5240c0da90094550290341280002e02d561480388102c0c6440e10aa11014070f1102c07022250b40742450f0408000240341c1d030040e540000d04084c094049140329000f8083c02058500d02110382d000055500200d002070130445489225400322a04543e64500d07040c14025400740020303582d01d03a4802d06245c240003050f00000c0500d8010403d006130142d004503401100d400c42e00c80036450303444c2c03840e1400705560650300559141c411011000034008143d14616241000c05104010064000b414294051340c24440d900140c0c1200d01c180b8402e903040e03080401d244984c0d20348460b0284a55585140340c0c0c010103148031280190b203025003c01e94161040719040542401e0044000c48010200326081c03060418074886183c5510000a08800b03921094030550790050503140410600d8118035568001c0f1080100000c160406009004d6614030845014240050b600c914090010f00b54501070246680101c1c10480400c4001020908100001705070303010b1559043d40c2c070f14003410420018a00a850440e205 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 407091888 1250 407090638 407090657
    0x3030f340b0103052e09051002040b0d060503070321230304050c150a0c050703020414091b0f09061305100f09060503030d05130503181e0102060127240501 68
    0x3032480c01c451743d080110341440400d171403080e0b00c1c1940c01c1a00c40d2182d03400d094004140420610f812101820110007005403c21175569141708045d43c4d0801484084d00e1404c14080e29a02c422600306151106911420099250244681c0101000d81000c910790030b5240040280410402c040c040d00401d104120b07851038419080500b00340b403e00c00c4070440014012007007108002c0100603c0250f0096070010010001c001e080030580900300c00884a07840340d40076891070015807005600c0c001e40e1102d405404d0900d01198103040c04031070080541504e80c810141203000b16801d140d401014030401c52001c000c0c040b2071500c241c0b0580c110f1103400000c8441e0800c1424030403510000b043d20f00381400103901040945810201c1c1c0e001d96035a0070050558000000d074146103049403640d042c80c4010035245803268410703031401480351903603c441c01c50050304644010020011540505464008580000c035510400c2180d5282103c540089440d94a0344100301d22901e5040c88112200034182828040d100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 407093138 1250 407091888 407091943
    0x30513020f10033806030415051008060406060501090803070218070507080412020109060908061803130609031707050303010e07050409141503030f340b010305 70
    0x104000d55945024484924402c41064440c0d0014038408076050706811040e00c00420040b80c26030300344d45808003540240e400d0000760810030100d034440d03500120590305880c0001ca1f48405000090400c0d40c0d100c44049022889100501005009904c69100040c40c0f5141400140c07003506580d02c01c420f41d401c01d0003400017585813041c000041e40e000c824580b80d182da940c0700603200790099040117006110007080c08541803600034a04400c0d60b000340c803148015070755001c085498989501421a594000c1d401250200142c903508207000305a030410303282080112610000084441d9200b080050f41044003001030254409099024402a100e5589071801c2500c0d003175500e100611550201000310000100c20314411801c7d00c010b031049040c01e000201540100c000840c1d0140da01018181c41c02c440080140390000c00ca4040058044a0340d05015030403100d003030503808250000c5021100401c006078070081407440242050f01c18441c001003541182001e5140504d444d082d01c841400303a126049c0c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 407094388 1250 407093138 407093149
    0xb06030c0f01050918010e0a050a02070c030807061113170f030306100e031b090916180603050a03021e07062f12091903080f030c040e04080a03051302 66
    0x7000a0030b00d540c1d034010803c08a03540d60700ca5102e18440e415014000b10710515201e0a41c4e003e0000106c2c24480c80c0c43e21207030f0504070310070540c00420b580361070b000030400548201d0281c81824000c07040090000148100c0b9049070b03100a03126a4043d041d640140110035800f8112200090341030028600700c3c8810b11001e80d28070010382890301c1460450190b0354181d21a0502c2c038003402024040e9810000100719141500850083d610722906407000024011000059440081c04066404401c5986003808000700307200c01040c0c481c002d0317032240b2022002c0f034400c020080203603229a004040104210344a0404040407030400800e94020134010080a40d00c0400e025164001c81241c00c0fa64629070840f4000300610741c058082800b070303981e01c1031000e03016101903c0103440944880004118048080714000300c1400011724031402444500c001da52400050740d1711443c40741d203807480e1a0312070011460802c0d00b01c40031150b80600003642c00c0c0c401e81c18051540c00c00d104103114181186907900151 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 407095638 1250 407094388 407094409
    0xf09060c1a040212030706020316020613030318021e01080f01030c1505160b0609090321040302031309200403020319060b0a0314070f0b03010b0c0a080a0302070b06030c 74
    0x11092105000880c06640d5440d01146504018138104d81d41c0d8009484d00401070f400403030f86826a40c1140400103402e40c008244188110021400001c3c140720760369003500104401c0d240240c030001c03500d2541006072100e150031440c036048a501c80001c002180c00040081310010402c00c0c011041900410029500103003040555000035140d40d07845002100032655401091942c0361620b40840c112014046a006520300559082c1c412424968812101c41c0c0e0300e00c40c8c50600742109600107441c030b0b038441d040800f00e46c11621920580b4500340408141107001400b5810910f52556500582a900c107424401250000a160842810f00d8510340020391038510010704034a0741c00e4032000074001c11030309a0050000c2400103004040c425120f040ca140070452101c1226101c5c0304211002c02c1d60f081211310303070080304c003101c03481c0345183e003070604064440d00a0008040c8520410300000c00280c0c00801418014015983c01a00c4a40b20b0520689c04800503190754002d8108003071006040c0c8490b000c07135 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 407096888 1250 407095638 407095673
    0x81603091a090102090a030b0a061703090d080409020307080a18081c0902130605030c031b130603051912080c04090e1603050a33050c09040c0f09060c 66
    0x2596551002d80140c00783c807810560b02d03440707058a90080100811381150324040d4080c41c00410015840f0301100358074811504085203140d0040c00a6105403070120080300c01c103441003000c981000c1c1e803118014103a801c252158804900742d441000300500d9540304480d481c081c00881e0122111858481060344e00c02c003100c500d10682103001600d104042c40e00009800b640c06800450425050940d110040039030380625441b9015600c101e1401d4136000500e1014070412065640c000015801000745002c040004055200e803198800000714200f484400d0a291005865440e4000d5500d481e4440d210301e0345a07041440512414080340b02040010303101a1141060009034540d05030442c3d170714055400c0c1d0780201405c100100401042804a4244425845617071881082041507440c4004c21155166111003440044551400f01c0ca098000c0d9030070014440a003407414603c2070105050b1840b8420000114007d0f000750600d03d079100c0014002008146000c0b00c50250b140d441303040d40b5408a081 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 407098138 1250 407096888 407096933
    0xc120e010507150e0a05071d010e010608060310060f0f1502060f0601121a010809030f030f1923070315090b0a050303160c050a050102060f0405011b08160309 69
    0x3c90350035880d00d80c0300c40c0c400428001210280443d52414541e550024040c2c2d483c040317222002d19403440c08440321a8169a030f0481d101180d42c1c240f007000c6910500007480d5952502c100b80d05e100130900c8500c40d2a002e00b1040780302100eaa803c00011042101491744210403105c00b210782441032680c007007070180e044188000d5103036968503018012281080e8021880340664508800400c0c101e09030360428901c3c0e04c080e03d44508035030703034415850b4403030040015402703d40e402000020348030402c0707a17041d5510041040c0315802c0c0c0c501000d45841202e04140451280914400c14001a03000c00300503e0380c00a0f80f4a020700440c00e840030000c00b1070030030344034070030b0215150391001001d6592140c254024000242c1141e4a800200300c160000f405004c1042d6282c1d42081000704490406010481c1610010f8004100b6030b00d0390b800d40b4106a0001700240c0d025580d80e1404a40420348004c8a02120300783c1da5040a80d00b00301c102810410702604114041c540360800d00340010700142c03007008508940384907 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 407099388 1250 407098138 407098163
    0x3010909031403091005181e12040f2c131a01050f0607170c070f0e0f13060f0c05090126070810150507051603020906040207021309030c120e010507 65
    0x1010010b040d13100a1f60200c3d8007900c0e0745000c980e01307403500ca402c034982c0343c80454650b40310f8007005104621442c0201c8a0744c5600a80070b0000f80345251070003080320b036102a0a1140c403d00c0c0751850301e2701c10a90350005148030302681541031003014000c3c131210501005020b4a55403402d000220f02e40e803041070950060034041b07a80c4043c0505624806400090441c2166031950302c0403613103440c2c03000c5019480030020361600120b0425000181c06208400c141005542611902c02030700c2c2d1161402c4040313074499220209150064000d005091205615803036840d01d640c903d0300003515104036011451203400d103030603400c000c00520141c0035400891504241c44191039025448038400c00c42d0f0808007040c60b0700c62110846903400f01c0245100e1380100240c0718a02c00039038030305108000d6484082d51107548039000c51002d1419034010714030790740b00502005041c0074072451007003075270000001034000c5020040c5100030b000c8404258a000e1047d883c5c0b0321410300014002820300e0042a80150141c0c44905 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 407100638 1250 407099388 407099401
    0xb040b0d24091d030c0604030906020f060a020c160e150d050606010f0909060b0409050c0c0d0e2d040509240601110f0d0905030c030307120c0803010909031403091005 73
    0x98030391140c0d4040d4090344d81e503200d05c0610a80c4c902c002e941c1200025001113001810758130100d00030150290030b001038105511079a012402a4001e07c0407080e49001ea4001c40481e0341c04052804010702010121040c0752418054281c0c117580500d510718001c203820140b1800040012555a80c40842420844035000410328103c1e0101c025411540c000d514000001c148000050060030803034640403c02d000c1342e0b8030350104c2c401314002c00c2c0c14018542e0106080c00c035036501504184058000180814144006160f0b5103490380440d282034004291050002e0340450402e4003c440c0d0002012005000d12049182c1100c8125002071144c4203c00d60840458116031043c1d80802880d102c4000700c403c060706000a07140c86a06600d24400031a40003000015641804108840400340c014091400c044040c0c40e4142c41c800d910204000700b2000040c402c00207025803001e9030207840c015400050280c0c0038580501100010006103170410741c1401001030681d80020000c10003070781100e003c43c9070f0b00d410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 407101888 1250 407100638 407100671
    0x403030c15021b0c0f0402120714130b07120309021c0206040f1d01051516060b03060117010e0114060d1401020d0b1f05220b040b0d2409 60
    0x80641503a440d00c0a14070748850001e0304d44040d0004666800c041d4182c03504010891003164031000781c210360540001d0383c240c0034461110302401500710103403400421000085411255030042d0010800118111081c41b50103c0c0301e0b81a07840d54102040040b1450300000c000d0400c1c0d5200c030510b1501513807603030115212001990014401102030707000e2948c40d4450305a449040f01c0c0111303000594000005024274001118a02000034040c4c85032900e004451003c0c0d0f07400d130900e000d44071507445c0c007241416500e08200340c900800e41004964003c0d00500021820341354404455800d90f8141038003419603425045116401090494006800210724034161404070201450803016500c040740d0380d040c841d45500b00a05203803045aa9865100b8a00c2c1e819030440030741444080020424050415210b5214440c00c40c0038914031410080503035100030f40c0c42d40780d02c41c0d00880203210b400b00d8030f540301880384d0044c0c034216142103407c60280382c1d0498000c52004210700c42e2240c5191034860400c4010490b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 407103138 1250 407101888 407101897
    0x11a0a03020c16051806090c0708070203070312080c0910030f0b090403030501090608030304230a05030304300c030f0509041506022109010806060d0c02070e0901020403030c1502 78
    0xc2020b0721101c000385100f0101901151103030a002e00300b8003101e9013880d11441541449124005c00707210454541d0228000c040d0000c50040b40d101008001d0700700035a2781048404000c501c03401c1d140803240b502c11002060305402400c0c0010049042c0090403059803000100c80444506150020724880c035503079810082d007031654100f900510300e942444141345c0c2c560451410b90b160a10144403403940c03920881c1d6244411600544082e440380807000036485d06c00844c040300c203c004201d6136080d1140d2581c0d400d59100b0b4900f04c4003940ca515188070800158140645008400306898180046800c0d0180c1142e2450500604010110940c4519640100192141280090001c0000ca20390001e00c81650041d8080e400c0507110303941e02964491110820164400900c00341641019000c00040d00e14500143c4101c0c2d02101c14004400d440038507100d8282e5072a05035000f031150520303000c1800b0302a44c1c00350aa40060f40104000d1000c00c0d004141810020751222442c03584901c1a070450001307018 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 407104388 1250 407103138 407103157
    0x11060408070f060507020a032c060309160b03041b050f040518070906030b0c1312081903021b030c0a0b060f0415060e0405130204090203010b0324010509011a0a0302 72
    0x11300000d00029a500080800599101e83c54528000300715800301612290b1510b405403228600b51680c3c515401c0c500061500300401c0f20860380480b036201188442551550810759148001008000078000840c0058200b5642d40304e00b15071090502d408a00345202c2001140d01480d19000801c0e901c414031019004041c502c002a0748083d034942d842200a40003521054480b0a62034010901004a95080301e169640c0c4044503e0010325200d5022643c1c202180241c500020074018560180d01c041d1201c2500b030340554006958840001c7d5801c3c03807000d48110100c42d0750050003500801e0000155581203032380c000c100141c0d03603540d220028000d004e82c0301c00d140d0001d01741240000d1004031440e1140560f4900d4131000c010407032100a003c1110011144e00d160f00100e1042c100250030720781d0058440320300280011915250000200b0301d0403001c140d4003005540070204020848420701165409044115600e0380382c3d51425810300808504014001c3d4a44400940204020b0103941110000d65 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 407105638 1250 407104388 407104391
    0x40203060d140307020405150105040611010b09010608090d030e03030a020d0e0d020706120b06070b060105090d05340e0903130303030507090b2b060302030303090d030c11060408070f06 81
    0x3402d00c081c071034580d000703400101e0046090502041001071489030603004d509041e52001d013014500b0004a407100c04022140006540c0c031000c050075521481c0744640602a1501c5000d00d50504948541ca091402038188007018500684000f21200120441c2d4000781022800340c4c807200352040a0000704000354a4080300d10a10b41c410b041140c01050540440f4203e449440c0511540d10070300342903860515800b41d11080401ca100d000950000c0490303008001803515a080001407000300c0c00705c10910300d040c0c0e45a8015036014a0b8807060400e0a50781204103502c201003296581031f021641003d43c05000c5100c21f0200028125990400a0301c18408092110080165503420050002c02083d120304000802c1454041140c8800038120740c0000740c00891410382510402d0a002c00b800c52141c04c086140d101c40e000000341e41c0c1080910300a40721305002c0c218022201802400b2504c0c1c003043c1c10240304c0302d0145903852030750104006a010303400c003030101d54420041c90407006000c13250000801aa = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 407106888 1250 407105638 407105663
    0x1e151003020c0a0b15130f0501060f0c03120e031803010e0d0c080f0c03030a27051b12010c0908071403150601030906020a11070f0b040501050c1905030d0b100905040203060d 76
    0x141c0c0d90403e07c110a01c140042000e81d0700c0b40011200c906140441101140030018410300107445a115003240c510100b4001480003440c1d4400360440d80300c00f10790400b042c045c0010321420701d028420000c403441030300c00801c3c0052007900060190a40d040001d41082d10204000180d091214216107a5001c424142c942e41e141001001e030040000101d4542600380310068110340b075118003c105100d640010041031003004810001401504070a0141e80100c007800130074039526000d000711030b01c1c12150344403030b00300b40d042c20744081c5030036940d030310210100a40c9a5600010344000c0b6040c1c030800888044890960740d48801a0054511041d009080a1000404021942d440000c0c80303103030380c14142640c4000356100c02d0240910840d010320050722808001c01c20041d8020001021814110400d41d91907110000492549001d0000280c640c6d40001455034400426482040c07648502116001074407400c841c1c00402401445c007485005a6000002c00c15590b1440d841c080265481100d0b00303900d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 407108138 1250 407106888 407106919
    0x9030709090f0c060903150c0306030516031403031e130222180209060123040801020405130c050d020d0b04050c041a120f1e151003020c0a0b15 63
    0x14215000a83e243c100030760340403510780c0c42404000110ba4010b15442400d1040340c010388010b0040c5540201495510f42c070000000b8000d0241d007000d014140b4041c0f4489240d424616076206c060b401004054000304200610321a42000c0402d404800619900440c1e1f01c2000c1c0000c07503c0300c408081d512849401603201342032500c00d10b804410f0342c1a00180b002d00c4010100240d2400c00600080d440440440015041d510506509400075138921030f040d43e0410f40c04003407205a0060304180066500041c0510441c1000403095002c0c620341c0703908105803440020000e19a00601c0191111180c00281e40c03150041035401c0039200c1030380204200f0141c2441e040d4031502c0e60162054040b0b02840c2400c4560600015040d1481d02c81040d02c0b20715250358504042d144020002c0441c124900c0102d00c031524003000103801846280003084a0f100c820001080219565035041510101401001138045511000c2038420003a40e200841d080e064491907496465004c4680d5080d40004108103003801 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 407109388 1250 407108138 407108153
    0x405070f030507050a050301150b25060614091006210c021c03020f0d021e0a020d08061e010f020c03031606060f081c030b0a0803031021080903070909 66
    0x4c464080711500d024990350000d15080c1d40c070007034004c46c240309035040420151103203000600e1341c0300d00d590041c4580030150f501040c240e51841d505640007945d6440600c00164400c0710405070310806c8448141c0c610f00101300125140060285400b0410b44002d0244014858602a80380102103001031040508030030009541318004410404400038641c401180c05000341b0032201e45038400c6140c00d180c2090341307040c00c0195104401000c88071411000c201684181c1101520a10b002c0b9030182c860180e55500051910401500180c4622441c403c2d109400b582080d0b01c0441c440282092001c003003403401e05a04100b15003603081e4050000103050102c444115005100c00c51040c0740412015444901c00880300046008041e120f501c00c0c1d06000800084030211342d51020380b0b1901140c201c010001082d00030748168010107003580301206000303400c1000b0810101074018030320304c02c800d0200c015620343c0c0301090680180c003c000c0041d0050443d142070042502034220301c1c40070b002291480c5031401 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 407110638 1250 407109388 407109403
    0x20109080d0e1203013002040e0d0908031201060e030f1b03060c130308130807090204050102152205120c0f12120106080c0c1203090f0111070b0405070f0305 69
    0xb14a000396040a50820f40304429a03040c0d4402e0410301c8075a100144000c8902d0b01c41e10060146030b8440c0500d000180c1d16801181220405280548a454180900500040c0a035004046250014440d03d0440c003441c003031482c110b807000d241c19034101154401007070034280416807002080c01100003400d61101d00b082e4585001d03205804a075081d50700d100420000d80502240803030780510f009010000b04c0c006074094503081340a115021131031039403028598981850341d440014540e801240810041d80c041c054a07003a0050b4142044107450645880302c0442e01c0000040e0906d0040758070721080c8841004103100001d46c54448543d41d0b85a1442c40f5611100c03207841185910440040c5400600400180c41c604002540200c10507400c24030240ea84c40130042c0540c40303030b0106200c140d180f100201b020341891400c0030034140d92410818091400d14a02218501e031b503030305050358000f0811030b410840d18810703000050010700e0b49503881c0042c1080c1c2c056100c0665a03c08070340100c188a40418081c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 407111888 1250 407110638 407110661
    0x702130b040c0915180b130b190305011d0c0f0f0c06090705011805210a031206050a030f0609030314040b010e16020a11041e06090e06190903020109080d 67
    0x100d94807100380d02107682500001c41c00d4a02d0300000070402c0f80451940142a206050384c8820030f400d602c804142402703400c141154540d4046102c035201010343c15105072405411114410070f99040405800c1d6590a005085145854000601150180401d10a071a454018411075694859103030000d65650f400c00d881d0800d45000f048000511507001b84840090b1280d0303203503904640c0e46403400700a001030100c2402c50070009002180c1da9141d40510041906503c0798441c1c0c84541941d1540c0360440b465078100300c0c0a0031134204e042c0b000c640c02c0c07114024465032154011406204901d000c40c090089508041010f01c28002400b040200040046c0d068803a0350031400300313340d107541d50360380c01d10040d0010380090b801c0003100c4008600042201034401c2c2c405440130800c089402050140c800c0b4403420107504c41c0d503960017800490042e00662059006550003032000e407c2c00e880041700f1107001c000c2c11145035512042082054000c0d00000550b40c0c0041400e034544202401120241007000b010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 407113138 1250 407111888 407111909
    0x8092503110d0213050903091f0f021204050613120c060e06040e04020d051213030516060e011107091802010f02010603030807050705100903031e090201050702130b040c09 75
    0x21075441c100560400303203254004041d00a1034900d00549801801d019040c190755001c00c10184440f81c803034010800e60300d00000c4c10f0705410381400c500103000c071a44101c1c110854010201c402c0c200c070007101c192011b4803401c036100bd41c0c5003c4480b0603404203503c1d41c0008410083c030304a20081c8030241e08400111a040e4550542c03118500302042880e10503401200b0a01c4014008540941080b210500b080f522410440300300c18203810421010360000a625040058540001d10400c0b400b0310441807000b00690100d1080b034141003010700910900c100e0207040005d0708500e071816074400c01000c801814889400c006941100030031381e48003500400c0c164081125400603441c41481417041e40c04403038265684000d13a4070b4016003115039501581d000c1c0c4503032003503078006400d4892612135010018401d840024101207030841c42c1188613011010042030b285007001000c0548d8102044460300c035411104000002919400c0100038110040c0e120380041c80c2000911100f41c00811500c29907018502 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 407114388 1250 407113138 407113163
    0xa0b0109080d2102031603091401050a0e121201061413080106030212061b0a02011d150717070c0804092c0c0117100506030a02031605041508092503 65
    0xa0503007640300586d01c0d91807600c05010800c0070140b00764007500459226021481c42441c03070240c10740c25035000340c8a641000e03548046040c01d40d00100300810f42040701100c1c1c141424400203600d00c10240500c242c0f03080c003008001d402c00302c500d80011a18444c201502c50303141c0b180c0381c030b200500038605404124042d00d0000e0204180d440001042e62003402c030528000d19403001101241242d40050f40c4000656484140a50701503c2e803d46a8a03012110b000400e2031071000c030482500120081d1102042c40075a000c0f07a400b139110035010650044042c10700800688262030f22100601c1641d109191440c0342080442041002014107c2e00540383c07480e20051101d401c2c1c01c140c07100d850303158450100f010140f0406a1000d5482d03150707403108000b80340444481d6141c000c18026030003203c445201c50f50003c1003049560002940d4180c8071518a40303141498108101000b5122203040030200b800900000504480c00c00c00030340c4c3d500c503403441254007420711b228540000540740780800c8070069103141 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 407115638 1250 407114388 407114447
    0x806060d080a0c0c0f030b06041b0906050a0c08030c070201090603020f043302030a0909050606040b0d15060e0a0e0f061003060317030414060f0a0b0109080d 69
    0x1800c80d002a80c124014500d01088010107a81c1420014400c98004580d10f03030010703000c4203640500c0c00940c0548000900c514048003040100c0d01d60104100301400400e01c140a01030703200e12088142c2d080303400c141d580e408541b402520a00d040990003014017038000204045100e40c0005410560701c00e0701d404a100c0c0c0c072143c0540590213441c00990441ea400e000402c5074805003416034880c02c0a1440c0d499070803200f1840f188070b40e4811640b00002d41e00c0000c0d508025540820b41000030500360b03038108404d09100001440070310451082845040c0045466072010711070381d0000d20f0901f1040d4002c000d295680d80090141c855032520144034414130100000e01100b81c1001c18403c008031544803090307607143c50030844186c440400703840400d903441c00c010001901d44210a04180003200540b5180d14280c600818500c10784141d0075015009007040c4100000610103064001c0410400441c0c03880e03d40c40101c03201003090380603030039501c51a40c0b01c44040ea00980c2c055941030011018843c414030a4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 407116888 1250 407115638 407115649
    0x9091c0212030112290601030c0302090909150f0402090103020f04020c011a010f02011b0323070504090b010c0b06060918010306020304060c110c0f1309110f01020f0c21060c04080606 80
    0x81c41340300705c0d41c1101c0090901d610950203034011410504005040030400c00224036004011117002c0c000b58001d0469851161035407900c01da024490300d0302c015103440c3ca903012911800c41807100078001d04058560000d10740d2290191440b501034500204030721030124071501c0d046c55131a09258046500b0595209006206000b0b0203205010054608200080407030114010704020000101c82e10301400802105500d14203100d000780542c0d600d507070311107052020250403504000072540c14480850b01d030700c0000e0300d0340200d11361012080308c40720345965040e004100b1003071032101d9886500e950207002000b00b05050303002d50300407402040300b0815100b030307030030151a030105403184030b891a84450884100ba2500c02c03d90610850302504903e540060110100181e80360080704a402a41061603580f55081105002002e960b091008140c0d100b0007000140e15414400d030030b18000c40007444881904030b0018483d0302c1c2a04030004581d9246042e2000450715041406411441c3c002d007000318000d441c00c1c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 407118138 1250 407116888 407116943
    0xb0906031501140a03050607090f0609060806010305040c05031002180d0213050403020102090904060f0e010501050a030602070606150216080c0a0e10050402040f060e09091c0212030112 81
    0x9090a04040c0d90030084034040383e0b8050703860194015075101c8040300040c010700c4224050501c5880da140c0c8a800e00407503916115098200c3d9040210b9404100029a03002459903040350080c01e000509840e5400d040e0761801164000c1c942520800742e038100110740d2035000344425014070200d0442400c0280c00c009241c0b22000000c0d47c004502d18810354240030b0760344402e8109229000040c5407110503000b10303402c1401142c0c155000c0e9915480100481034038041d00c80351a400000820566040c034001070740106e45400058501540420200700700070140e40100f02601c0300e8040508064440c2800030750718407021442002c1619024400280b4050000f200207070380c0e100500220b805070501d1641800180b00034400b000d1034207451800200382d2181d100a201811a081e80e4084180c2071502c05482250b48200c001e004100c10b604009070f1500200b2103410b2150401012508038580d0f00c0200d01e40700050a2000d00340c40000000500417070f00c81c00f00b000c4c1a1044841389900c1c00070140b039040c0302d00b4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 407119388 1250 407118138 407118163
    0x203090c0a150f080a0b0907050301080139030204090204033002030702060903010921020c0f03070504090213020d020702040f050702210c06010e0703150303020a030309030e060309010b090603 84
    0x242e0f01810f01030f008281459028040c01400940310221100041002c5000e4501c7e1002c40c1d0000018171001c1d601b0302903600e00d10300d2032050640c1c404900307900f10030f5034221540210002c2c0c00300d800280003d1003a01250010001c048066448944034101164a0140c40030904a12221000010024010f030380490900141580140d030070468150240311043d0300c05900c0035071556850034802c000a1841c290301e61001d0584441c55248101c1400103480c081c1c4403600140305192015200c025aa800a110000ea51041e41c0c041100511b610103e201600c02e60311403940e42e030001c551101c548010b0390107810303514022982480b11b500d0203d043e504441c0b09a803250016017061101481e400c0c4070f962070040b10101031025916044803003c1080c1403040a0704224180b1032024107110981da130500541c094542c88410030074120b80f855a0182d81d440d9070000050925403101a00d0090500034070300141d0800002e440f03e65a80390520303209009180606203e4071410b0b254002c40d26608000622008100 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 407120638 1250 407119388 407119397
    0x1090606110f121308030a080411010c11040905031303051005061509150405060f0d0e06071e1e030b130b0a0e04210f02060601020d0e090603010f0203090c0a15 70
    0x3018031000c500e1681c4401a00c8003403c11301d10000602400400040a40121a5841c140c83c1d0030f207440e00300501342106550034100b1240400da403010500032040c981201c0002c990010b00b00e005854150300b50b0080c90415404152003d00000a000c2d012a54858004c9a0f1604220a6540000704009020044004030080b50f0502501c40035051011403080b0120380c040707902d824590b84030005030440d400322580b40f156503004030303408910000134021410621405c00c040c0c103440c41c050000400d40da029241d202c200c030074450b10f4038040312700810318400c030590322100c98a241c8400c900e01801a015224080c3c0c06103401b035113041c0a0f46640c0c4200d130aa0200249410000f62601d05c0e83c000c5584d000d002500e5003240d07207544244c0740140c024540c075410501e07140c1e110b4115240e000641801c02c0104040c3c10740d0000040d07802c80c690302007982e2100303030b004450400340390f160800400d004114440f0403084651001084c0001f4400c0007494100e0701e0310890b40645c61941381c41c1908241003070308580c000402d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 407121888 1250 407120638 407120653
    0xf060c1e0c030e0306191a0f13092f1914061b010903080703050402030307030809160305010b190e0a050c1204060b100e01080117030c0601090606110f 66
    0x3580300d28a40001580a464403000b1500c010b8006401d1100030f40e502ca4440007000e42c0c41c0510b0003070303001da1180c0030348840400d5081c3c0031754000f1420ba00039000340640320301140c841c2c0301c0070201298041c400080d04000c10307504013548100780020200c41c0d0500540990084010401145070541c000c0040280c0d819240050626103011107426140208a03075500480600102c0c14071441d9002c0c404004521800102c0d000d41b180c1800b800c0c04801030320f46e408260a0904000168500004503800300761f00d442d2202031030381c3e9407000d1420b219120072040380d01c88100301c1c0003040c4807054001c070841c4403044521540c1d900752034460185c05030040c03240840e440f400f90300280103000f159000e03581c4003644040341480c20aa444140c1c07d001004c8404a07030556030303502030054a0070f045064450104580c2405a000ca05400002c1d00c41101482060310032242514010200e500500948074481030020071030b580c40d61517030b060358064240d078065480082d900000882802c41c0009107090910b081202a1100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 407123138 1250 407121888 407121947
    0xb0304110a090b3109080403030e030a0c050d08090d2604260102070203030a181a161502040620150a020a090e0c0901110606060405090a09060501030f060c 68
    0x2d00c03040510f82d50400012038051350494041c1c0c069900c0e0707180f00c0c20300d1030754903421490301500e10110000c135980642e000340015000201520045d20175100c0840e01e00c1808266031500d2160b034820b044c403403034005245400c40e40803c440b80900342031040c2144000a84008603440c5d8214070300642c82200318904494420681402c4185035034100040104005864000e00741c010030328680c0602c180c4800100c83c0c01000c01545010f01681c4045d0515103218444050714030300060b054080e0172890707410000c00c1201c00d41040a0100c910f420340d82d803075078159121680d90002500c010703032160603100f060340031400b2490500000301e004207150003010241040f0f5103403944000700035045140b1110a000e000580824823031480e0132a64031903948441d080d592110440001005403c0c9a03040f1801e9900c2401401801d54500d4281c4054403400e41e03002402d40d51340361004018166445005c0c05461810001205000c1d01e0700e0b040310720500070481801540b10250085403003440200e04503295880c03e04182d401c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 407124388 1250 407123138 407123179
    0x8010506060f0d1506050a1101020301230103060e0c18060a0926011e0f09031407031407050102040e090a0f11030a0b0906010512010506060307030b0a0b0304110a090b 73
    0x107400f050880b00148078402d0000415408100e0b4000300081040810343c03003040c03540044581c0d0032819103070080d41103514004503041d58640113482814131900711003800d541a44241d0000380144a2610f48040724103000341c804101d580680324090380c1c0c0011124000c01070402e4401c40d45281c14990f240c0711403a00d0444600f405009c04c003611102c40031261100f03041840c0c240224400818091500080320700040c0741d440c1203884450035560b40c0d07810410306602294001c103100e0541c20070b0303100ea2580d40b4140d02e1b0441d4203070512000135500040204441e000e0000550261041d14a2001c900c10ba540f0f8024525540300e507101001000d40f820382d94040005034003241003009603c00542143c11154003680c0300e00224004807202c00c0700ba8400b10041100b0729200724241020907240c80204800d04011340401c01c1480000c043c4801d0580f9802c400643e61500301c00f60008085049080d0f44030b041519229440b404030983c007500c00c4114110216180d9200d01c41c2d01d909600040812100c0e801134102030740c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 407125638 1250 407124388 407124397
    0x207030207081506100f121e0e0a021c050604060207081b0d02060105121902010c02030303070201050a05061c0303090c1707050310061a0702031f050402040608010506060f 75
    0x141140030358800007078071590811568043c1c0c0185080708060340380107018030441c1c0209144c1071082000c54400742e4901500801403141801d513140300840c3c014035000515600141700240201000c0c0740c09400e6110650110300803100d18421181800d00c07071508082010203040080014005401400c08100064101da00500005104184480c10500344540c0c06c000640080d4114401e40c003c44508500298140b00440c05084200c43c03012000c180344040b1a610400708611401042c00e00c0444801d5a014084c20200158001c080f66a240361101c4024003811050352110a000d040c0008580146411112558003041800d00f540a030920b0b51400c4002d8a89658142e8050f000c0c082c0124034100d442446551890715000285507451a00c030a040c507041c0c8907885120b40e1132078401c050080c02884280003640c050201810764803900c0d10300002e814020810f507509460694001d101e03640d02010703044184120300846082091565500030503007a500111480c50b8006020421403043c03c841801a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 407126888 1250 407125638 407125643
    0x1050a0219020420090301060501030c0e010311040e043813030c021528091a04180f0c0f08130f0209040812010f05060d0c0e0306160e0301110d0207 65
    0x100304e0000c048840c18200c00b07500d0810080c1403000510720850b0500340a040001c21083c80c0401288244100052000200b1035905041603112700f2440024040c3c0c20940b400b4045140a00c4041d081c50300c0d012180401582d01c0d14a5016441951000b205152070130308400040e490f4896815625203007010183c05c00c0032421030610914651980168841c01c50f041c45103120703aa43d882c0d60300600e90880d46400c4000500d03100c11985114400c4d20640e02c44420012a80c540204881d0790304040041d41d96402242c004420303c0f401c04074014010011604120005041d0840820601d00c002d90221400c001d0b014440300803500d00c20114500c4400801d801803511702418144030310510b07942c0001c0040405550650f42090041401c0590b0000340703015038018010540b0031080f661400700810b0290040b4a00c0c120401d54640845451a0141d4505039110340001c0581e451460400181269a4050b00c00c050000d61403000d0f00d505410144181c0015010f20710050741411191446000a58043d5108 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 407128138 1250 407126888 407126891
    0x30705072a0312200c03070e1605090112050703090308061f0807020304090608060406050f010e0c0306040e0a0c240c020f0d1b0302030d2d021c020a0b0601050a02190204 74
    0x4540390403440300b040041c2100610241c85c1e05a400d60406242c4003094000c0815a030f03441c1d0a008206a041d2050380d005141e50901035115910040160340c88642007013080e08840c14081003040081d410780c041c043c254420340301c94400d91581420b025040610044e02c0b2003650452842d00f200c10b010f05202c60380506584100c03031030b05490701c01550682d21141d014510f550312403001c0c40100461800350f5036104010480c08600c96140940494441300082e021008240c0c000000c03d095440d81d4101c0d03070784a00140300f128640085464000b41400f10b070b100302c501d00341b1a054280d070004032145022000035820764607100c4440031902003001c00d09495074543c0d40501c140c102000000c02c1d034643d05400005694016806615500605003003090005602c8100090b0382c6464080c9841c0362104030440c0d45418143c0c0040c60340c0d40c8143e141c00c075040f840005101700c48001004459000502079030080c42036000c201d00707466010055446018003e074613400b5820281c0e080b18410f12542c3c0c8446001d000030070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 407129388 1250 407128138 407128157
    0x60608070e0f0a090c0305190b060a14070204050108030c01050606030915130b0c0703111203130c03050303270c0603010510021f0614150306101202030705072a0312 72
    0x2010445d40700d820b5400c04241c4602c104040102c0040441c4807012900005104000011000510500c100f5000707005012042c0161b03c07180345500c064034140740e4058810002961641c225903070701d4001c0ca9907040c056083c1400a070150030b07c030090f24000c103103450007002880c01511115484440041940a261402c4001c01010861440001c0e00811680d104aa6508032508008024000ca6005804141d01445042da405840701e004c41381d01c240700b00d500c2100008180b0746255020b4243d807020b0100e00c00441840703070300711502c68000740540c81c0c410040700404480c1e5101e0344505c43d804145a129005000410441c00c00c81c045103074075a02803059a1028400c8092401030b20351071100912125036031041801112151340e120f0f10303c0300c8221200441540f1401010800c0d2200810041c01169242899017a0318001d40071150441c41040e03082d5100e1a010b10014900e4100040944080703000c040051454240b54030791a6140780303445c00b401e244605648811522410891240082150028 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 407130638 1250 407129388 407129399
    0xa03150b1210050f0702010c081305030909040804051201060305101e05010e0103030f031b03150902070f1a01081c0c02030a050d030c110c0937060608070e0f0a 70
    0x2102141842d95030000141c2410010955610500e0040003803040da1302d4283d401c1c40d450f4200d0300d0f0542c80280403178040c1a2081515043d400c60045c010000d4114407404240000c02c55118080c20560744103880e0401c480130910440e07800d0341c0322448040d1454118166402103107041d40c20040c24038100d20203100f0520a51640308084440991021039410b01100040c020103070b2012a180700d402651030f0512480f15a00300c802c005000390403807181456652010411a401c10b45070010040881d2a011900c0b0542418500312000c0c2007202102c81590b4607400e07a440d6031009000c035042e0344070040109050b050030b0401096041d107400c03200d000e02207007a8880005aa04210f040c012503c180040d00c41802d500300c010341079608903d0480240811003103000c0c04c2c806c000540140d098021611440b4548510910841c2900e2102103142c0344081c04c201a1281030503102e4484400c11030a00400c1800d645100403149050305039403200000c0d01c20000500d081c586a0400c2c1c041ca14000c050720702ea1540d68 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 407131888 1250 407130638 407130643
    0xc030e07120312290111100e010c0807020706030f1e0e0706030507050d020327030a0807050304031202070201141603090503060103021f020a06020d0501090b0a03150b12 74
    0x754403054074562840080d504059011400d0071210005900501c80c40c0d41007111251880c000d807180f5050700b0321900501c0020b0b03100b40c1c040c0307900344102401d031001c251441c01120080c11a035903480c1d1542d82801c0d6444011403240c2c01c054407621a9501078403410341045c0e0114041c00c0c403910b800c96031035105c4040030700b18a000320303480c01a1940c801c0c000501d8400e10b103d4030300342507003039110030207242c602070800c0001c54014003141c5c0b20f1800c1490059599941c1c0200440c40d121203040c2c0303141040160b100100c41c84000008111140c020703100c40f1490741d2804803c48280c442242c0080c00254101340d4100103282035000b4044a9105040c901084490040020003d800203044211201c074158000410315400a0088000d010305402901c115070564002c60141c04002c00001300b800f0854112140f160b109100010001c2c1d803290040d56110800314010019000c2070041d10300c1e882c42d0101c0c401043c5004450b22081302d80c4115180c03003401d07508040c40014900b00200d00c2d041441c61451140d08c0005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 407133138 1250 407131888 407131903
    0x6051f0e310f140606090f0607052e1505040c020c0306040b1f050f0f031203160e03010c120c0e090c0c0d0203030915100e040303051501050f09040c030e 67
    0x3062000030401c0103401080141c0d80d03a0024000c1110f884814400300f5258403007100d0714050700390740311100a40c01501050180c40f840001512501400c48a0066001a0403a8425140b0074030540804815005200c00c11a64091100c280d494148402005182002d41003107107450618015105052040800f02c3d08081c41142c08569400b1100c2c00c11007403402d03882d41d41c810440c0780321200040a0074400844d5801c54000303401403180380301c1100184507660800101a106181300d04280e124140300040648000707802d2a40c401142c00184046010b003414410b420190700d0360341d107160080d00780038910f600808091003c442000441e41c075100294842d14006c5020f1071648880940e1096260266804c108115106104640081003405400d03400040c1c0740400320b000141042d41a01ca0701c445402c5103020f540002c1b9558030100c100400d0640591066101d12000180740140c03c0300c000045a6601c1345041440345240140186012820607900500100c1802d00303000130b04001551456151248 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 407134388 1250 407133138 407133229
    0x12030f0507051b2407110307170c0102010f050c0d0f1d030702090903040b0d0f090605041209151403060418081905030105060304060218060d06051f0e 66
    0x11565103c00c40360409910b100704441190762034031401440f51403010618404ea45020300900c103001c40f000c01ca03941c00d000304001003514041c10074001c900280c009441d05120744e001400f6518080d4006900400c6004080c410f0440c04010740c41c00320441c0000c0000e2907a850540c0103559180002d00b10301880041440045c1800801991500c5583c070401505c81c000400058458000340020003c10081c5001e40c0c0c00d450550002140035555604c00500810714450042c0003142131100f44014440981340c0304100c0b643c1969042a2182c41d48211040180a801301c0d10005141400d4441042495400740d90041d0004001040e6030031110020411110480025101000001015018000d440000581d01c40103824894119132402000840f01d0100400103403500740c0006001082d50300205826481c2c61008000c01c0d103850310280c421005014601840d801034500c451035107890640d451003520910815500e0030050440d01050040c02c0e15078280c2d00b0700038210b05030b080150390410502451641c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 407135638 1250 407134388 407134423
    0x60427051003061d03030105012003030a1a120d050a09031505010e0a09020307030b0903120c180639011e0b01050c0c0f01050d020403060b03010b03060112030f050705 73
    0x24118203003001160b0f001640e021142010510113060701c840881581d04544090a120b01a0348500c070640c0500b40c5030101880b500d0100108204141d4116813003405110160300302c20300c0c1c00d600081400300301070f03180e034500e00550702c5851160501071061005011500842c80d0600b46107980366940d80345100e01000010041e502e4000500a661858079150350088028109000e00105038003c2500c03844e10340000f0f003961528100013000031400f002147c007401d001c001d00489510700a000041e440c0c028030b80a4800140e002401c0d151840d0170419100010001d100403c84c40300d849400550020f8511000b081030f800c4240b604403800f100388541d0040200c65055484075040e484040021904040034107414050140008101d800740000c0b41041c0c0c6000fa503809184120b00c03401178800d40075076800e1000b041d000003004020016181c029403051325003540244180180c41c4105a183c030000d010304440c00c4000011403001c04d00c51002c0c0524180d250521b079180c1802a1651824040d00452030301341302 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 407136888 1250 407135638 407135671
    0x6031e0102030f13080306010f0332010b040317030402011110063611090409050703020a06080103260d051f08030a050a050c070b030f07030f0b06042705 67
    0xc0ca58003c441e90120303141c641482c081d002550b0341046800003400c19410032150804d100b2005000341c1c412410840703240e04d40781e004458414850304015208071251680700300000006200c00008042ea030a0f0307070b4001d288420b4904084404a01c0d50401002a41002100e094000810740c050104d4896100b00c140c0115400b07040c080324035032145c804103512400074001c5440681e05100c00004622003100c225010461070541264045513001e9070080590040c58450340f0380c10440c00040c040107c1e4070a90b0141a61030380c414066414001c2484040e041d05d40c10100c5450400ca0343c0c00f620208800c4ca0360031420610744809620486800b20f075280051074290300801407035045040c80c00c2c010701d0750a0065140c5810144024070500603031543c030040c0000440e030004881001e01c001d02c0586041407007540c80b0b14001c1c0207614102e0b01175880b4408646003800c040c443c00d40c02e01501c1e4650a000d800546000e01c0c2c2000780244400401e00144c60111003144603102a00303500525020b5001070840301c054 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 407138138 1250 407136888 407136901
    0xf0212040b041e030807081807060207030b0a11070314130308030106020118020a060e0a051203090a1203080402060901180e061207050312070c030501020f18061201050906031e010203 80
    0x3d0280c1d070182108210900140100003d40c0818025030280c5240f40c076210a459400386507015001d0030200d481c1600903a1404101a90300180301011a8020000c15850352540407024084404015460741c594070304100e0b21012a000b0020321440d0b03844009070518200040059400989040c0c000300d0340c104000004214980c0e0900a030800701c5e4082c4030140321b2280550000d0404580e80c800c40052014900d810001541c6400341c81c0014807002d0042003010510b2200140c480c0d0058140700d20078a041c0070301103402c071540b590001c0d4665164031403000585440d0208910760b00205007085c100210b101d1113038060014440c0200007440055804242420200d04010406cbc030018031150250b4801d2604001554002a6030101909100303c5140c0c0d4020b50704096804000c070f9040506190f00010300c1c07980e9001c207100206800400546100004181c440410900d0f200c2ca41900726179038205001445203103001180990481001411900d09084519450140004815000c00c00340d60106c20003c2c07 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 407139388 1250 407138138 407138153
    0x1203010909060e0c09180a0501020708092e0e0d0602071104050c1c09020105090d0b09060c0324011101060609090608070302010c110f090c0703031401080a03030f0212040b04 76
    0x16840f000034003910700c0d4140228111043c001c1005220800740d84c0105030809091082a0b0f40c0c40d00b03c07000307543d9500b05041030344284d40051101402503e20003c0441010209200c00b01100900038103e080700080d990201d42c0004c01120307050b4007010a07203803440001c3d29440242003062240c0c4280c000c8009410807c0f08480c4c00038500310054004021901e08145109071000c1e804142c440001102c0031280012511030003900505a00001400b03003c500b40600f48900c10b00c2180c0e100b04562040d5079492521170180010ba40c0f0055103005805e202c50001c4000c2000800d060043c0b61807041e18900aa140d42500d6480e4003100100d14801410b004425181c020000500807000051200e07504d10b900090800640d0f00d0043c0008820003002d1071203a44040c4444038124000b403914001e03041005400245a118107000c4020902d4200a14060025954068103d82c20000170303080400a0303440503400740090b0100849402d80c00c1154500c02c903240341c07010f400307103005804090041c40c1070b01e8010b5 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 407140638 1250 407139388 407139401
    0x150b061204060f1107020909070306020f0d0c0c1a071815080603030a0509190b0403150e010b010905120a050319111c0516020a030624031112120301090906 68
    0x3d003800d242072200f070700c0200c0c01160085a415030703402c90140c3d00c0300e00690406006400082c855400010b201042c0714031140902600780da202c1007040407054502c01507610200c001c800901d00c584c81c00802907032803015902e80c1c2d400081c0c0d0420752004551b108415410340d065400030048085100c500c41d100700d510491203a4051020340c01586028070b01c0c1d001921030f00078241054440e0f021052200702c45580c000800c001003d01d804016103550712032903d80301107403441ca0040c0190789000004442180c05010380c800d03982042c1c50300742545081a05120b50020b100e00240c0b40c610984441ca000183d0400040044c145001500f05240403000001881e0760740104007010268030052140031580e02c06d0070032503141c1e01d290074000d5a0b03d242004500c03d40343d0f02d80001e94004040c1340c001045c086550006000340c02800040c0d50b20030345802101c5a6041d680c000030b4040445100c00100506000c442d42c5480300c00c0c0c0c404c5403608628840c4e07201d16548260031844110380c4510419003000100e01900 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 407141888 1250 407140638 407140661
    0x7020d0f020a05060c0f070614010302040f1b080720010b030705030303010b04060c0c03061b080c040b0909090319020a03090b040b07030e04110f0304021905010804150b06120406 78
    0x4000b50001c1d5100c60b42c1e10900030300080124000055000c001041040440e807031964413070003d0290440880084034810400d1200368000c1c0d0400442c1c00d07456419100707901d1035010800020b40500110030040714202ca00a00d1441807201c405880f8003410500340700500480003d10000c41c901c00f003035080c10304143d45a1f20990107903100380010311010b0750040c10f58082d582d00c0d1512503d200340c0780c04c2a0b02c0d104450341c00030300200d141140084c00e51000a42d46112200107465410042d01c808400000c144101e100d5040e001406010b424220710301030058903041501c1c030b01168285665283c0100c0380102200c000d0b00541c0c400c103817407002c25800c0500d90780201010700d0b50340c1c1824545480101ca83c482c1000060801c4030381c0841c1005541e403980300d0340c55286011481030b01c0340b201c03070f0881c1c00540c0181da050384589607042d202d403261081580d00034240c41c2c042e034030495180c0307495036003501098180102c40e004a4035402429072980320314020300310081c0504400007c1c2e04060810344101ca4940044 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 407143138 1250 407141888 407141893
    0x70b07060b100c08030103061806022205030304080304050d02130c0206150102031201050111120d0902011101020406140f04080607030b0f0409030207061d030a03030207020117041a060402090907020d0f02 89
    0x1c600c007041c07501c1300b80c80c110703a00300c0360101d8080380d4103242c14010aa1508002c040c03501c042041300002c86030f1a49080d051007240100094680c450040650b42d001da442074504507801040140210304040850328a0a4409000d01d240148011707400b40c150342c1044240030040c0c0c00b000c2080003907496445012a02002070026514291043c20380c1c50148005014103418444600092100c001c0c080141960700c84c40b003a882c81c1c480c803000610002600c4001801e070b0018041c0004240008010b200300d404884490b1903a4200b05804940c9045170741040b0301142021f82c09207c0041c4581e0240f01c0350b4414582c41d0390000e0110b040301c04001601e1a10b21150307015500d00180d4000003a00050300d03a0941c1c607203042c8200f80b0844051900c0c9800902c410903a01406181e580000b01034040d0003070416503100740c0394140030320450100d0022100c01210060454001c40303001912000d400703c00c0f1500050003810140c54002d005010605c500c809441810050f0301051200400645c00122402c00c10312070b202 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 407144388 1250 407143138 407143157
    0x12020303030406050402031005010303030b10052106060c03030106021e0a020a170a0203300a0c12030605031501080706090b030c0a1b0309060905040e15040302070b07060b10 76
    0x11940d64000204028142940c820200c0c0555404200ba110800740b0f00005200340d41e140c0c5002806080e4041059000d8500042e40d90040d03405142640c0224010f6903607003003681410007917400714041c050055a04410708000b200b02030070083c0002c5029010301e40051201200c02900411505c1180c2d207280f500703030000c0d2401c07401a500d00b5503100c02c4503000ca099441da61810340030603040c0380c03003000025070612424400524030318043c6c42e00800480e4014070f0401c00c55203c01426004d124150202001407040407080001a6240161784003250036880c0014000d516180420716117412020003103100f640784401000080b40420004c000f230241481c01042d09881d00803660040d0202404548620f480400c810070042d1140004101418008540c0018145a420050024101c5024900c001460302c0b0021559040500a025500503075000802c504e0048042e0700b20166401f81c01282140a80c4900080001100f005051518080c1c40c0002d02092a041004085101e41c0004001e0141001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 407145638 1250 407144388 407144393
    0x317151c050c0f040b1c05010c08010509010e1b0f270604030305070f0203030a0507060e150109051801051501031401030209010302060d090b040308090d020708030a050c031e090a12 79
    0x18500402c10b00070354640d040b41118200007400740007254060340d00102440691002d5510085800a00d00c3c0598002c00c060300e922070040320300d04403d014880c0c00000c1a80108030051401e2911039010391908003c2000791045a4050043c1d070101340340d10000c28020070074040d076110381003129644209110703140c0d94610404000c180c090190744005814010040350306414805074101c02d1060541c010266503a440740b0040241140d000850141d81c1c0741d140c0600c80b002c440c00000d1120f40f030390f40d0041c43c0000761310f00340148018200091010060204042c0d0703210040d0024000d0034041c20740c103840500c8076540a80014202c4d14400d120344261381c03400c1c0041026860f0116002c0c1500c0e0152102c641d82c500200c1e4040103851002c00080200d0340c40801c100030302d0b034000e030b080d40505c1d143e500b920380b1507586407412640c81c00d11340036030016a00200300c50000c0d41d000c1e4005228102c2c0000c280e0b403c14202040b00f0000705801200751748040300010752508140360030031900c2c0c0079011000341000c0205070754 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 407146888 1250 407145638 407145643
    0x30d1a130c02100e01020903070305061b07020a14060705152e0306111905031005120c130b0a0f0905060108090a03050d020403080705070303030609090203190317151c05 74
    0x41c01090345107984e2032060404820a4048070340c80365000d42110010b554901d40302e0380d540c504507184032881d8441c80c1990012040d95003221151600208541001400d0001007600b00e100d20ba94298000c0080000e00b000817020b00c922045034501c190081e805151a900b40c181030140e0042210304110161104402484000400c0c4c0c2541c0c0c11442c0003031900741c1140f45610900c200030410b5040d01000700d0344461580d001d03000310b100b400c0b0140e0342c0e14460f07a590144021814601d0111996400004400b140347c1040000c68002010303104d00460f0b090b00d03140110380e00c1c2880390400c03900d44420b00403e0010b04c88501500d038200c00b0a181001051501e1000c16407624a0420028100000040c00181200698050710055500300420990700c00d0b2030310b0310664400c51484110003280c2810400a43c4400d01e2182c44903040d00600940b00d030b41302c1012400c41c0b01030b500c0e6045040c0219100d1030303884070a40e0400184500e4816007000c000146000c100300310b04030310201030280b1140180d144400540c01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 407148138 1250 407146888 407146903
    0x90c03030a091403011d010b100906020c0f130e061e0c07060e01060b0307030c11030412080702030111120403021203060d0b070c080d0906060e010f17030d1a130c02 72
    0x2e90320754007003182070f2500007030141101c21410580b9518a441c0020303007000c194800c4a15940c115040000c00f450004240d8031003500d88507520158101d410b1081e003d0500d0101d020b0b510f10000c25902881420345450f408959200e2044000c5600801c100188980c0050035031804501c4011103444030b2a091065400c1481600b00c01403000c1c0e00c8110850707403840c2c07d401c4500a0111103104903242e1800500c010300070309168030a900000c401141604411501008980a8841916180d00000c1c1f0546071035040d0352004a0880c2c240d0f50710703a110001ca407400030141142401903c4440d43c0e5003000c2c103000b4500b030300120003a00545020014080c80303a9942d280e54520380d9010000d600c1c0d5039100e1030300351901e0240b140040c000c0c02c0c0001e08005100d1444d4011004075100d11000c10a65450301e84220710312009010748036001000020503c0544002c010324a005091842100e28042580c4450001e4501c40c000040031303040468155152483e22a00d54800740041101c00c1003d04c511001c025030303440ca13 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 407149388 1250 407148138 407148149
    0xb0f040302100201060312110616021002130e04061b021b01030b030f0d08011a180108040f08071110020318040b0604051f11120d050c040914090c03030a09 68
    0x40551001d80058005c1d00310000035034001c80c1d40d40d00c2200600024103034a59034803c003070280c082c1d4800940c1c1e0321080d2590403c40480c541c01015103030441c00400000b944205e03040040f07071828400006860039001800380c880d9108001c0411025030400366902c04010000985096410401c1072811140004200d0000c0c0701007440c000c10f440e81140041fa0410740d01e540b01039014000c115040c1203031a0010082070482e982c3d03c5000400703004013507040c803140c080d803106903040210f5410515a03a61241c0d0712141c20502410450101c45075998405420380c2c0000411103111010301d8130b0700890b03d0400c0c3c00910520003030000d5850205400e81840b0883c400d12916171241d903503035611400c1511410259400b500303000d440c04031001c000c4c528003054002d50310840c0e00090404242405092008943c90301c02c850b442c0d41c0d240c10a604040d00701d000c2d010040c2070b0400841d0030701c8002004411030282026003611103100707400c0c1d814801c2c01d08d42400303040c08089000e81d0040000c8a12640d00c084081c040b00c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 407150638 1250 407149388 407149399
    0xa060e040203100305060f0f07020f032a0601081b180a0e01020d0c110f1203040b280209040f0b0d020103090203010f1515020d14181c0605010b0f040302 67
    0x140d48001143c40c4404540002d005840b0f001e08101e00140000710301c0d8040c010700b500b8105907581d0920101d07a980c00e1140f0048003500184002c0601605152981c41d4282e200296001c0e000d03519050b03140b501400742d01484081c0d11034140307240c41044411543d010f1307982c1a100f031500e4105400c0c0c82c10300c000c0083e0042c2c5201d9917550003507120075003c0d41039442c0090b1a18051024492030f040080525501190011090140d220b80d030302038900024100d540903c5c81401d80e4110350b501d0b220f03580400c50040214a64543d4140340c81594100206040302d450240030005840340d11007000d002c100c1d00c10440c0d0702061440e10550110aa81c3c0f880407001a550902e00814220614404240504007200750110380b07900300414120340c40c0c40c100700c08050310490341c0032140029031008200d07920145212110080f070200c0202e078402c1d10265004100c24840540d042011000b00f03400315007644903a840440701c4a102d42606010403019006440c010f105901c0e21508150944445806901c510f01c0300a1150 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 407151888 1250 407150638 407150641
    0x50d17241c12120e010209090f090a0506040c1e0501090909020316081c0302090609040c020c030604060209190503190c0306020414090a15030b061210020a030b0a060e040203 76
    0x406007a0340c40c0d80c954000e542d0340d008089280003404900900b01184182401d1090f0b294002ca814401d403001110000c09000c855104e0741402400c05a0140041c54507014502c45000868010414540264450401d840c0e0551520a90b80004001c41e02c9210580340000c008100580e44403404805480c812040040c810a480c4002842c0c5182400c680306040303000e59000410040c003144c1c16440c254125804803130b440c4002011022403007880e001d998440b405002440140c1440d50117140c0070300c01801180d501d0300360711b00001d10f4410100c1d01120000d40018400040742810b1003400d40041583c480c0f04180d90400d00080d844070000032004403414030881c5504244544000604011030b00550115130b0382d504d800c03040d501000f031080283d00840c10400400d821300c029106c8c400007480341c1c0c40c190007041e0460b521040c07682c8000c0c2c81c0e9648146003042400c220501400285410100450016130b034494400c005015580c41014076841282001010000c080e042055004049022200141e0f41d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 407153138 1250 407151888 407151919
    0x120312200318190203010c0f1715090f100609060519090f0b03070201050c04051305040318060207050a0806010e0c0702040f06080307020f100c0209090307050d1724 72
    0x21551000c0402814440d0902d083c00e11030380303506401d10950080d8000d121b6440101001c2d83c000c80020071300400a20407141c0c1200e9550031103510390300481c0e0507500301802100c1400155141105803000250280310342d040c00341c0e1621890720200100481e080180d601442d10700058003d0060541020307070035180d03903c1d240c5154440c1d40c47c0c0001e0031030800d09070000d0b52580d02440003070704100d42c040099071070200071504520b818002e035002c80d04010101c24100180710002030240001070000c0b010310880c1e02a025085604031181000390503c0d40c02010403d10744010000c1e4082a540013061a030000c80c01440130000c41900c482c0d2012481e040180c0e00d0603141301040c000d1240c03c5502007003030318014012800c0340001c40100b43c11030003154188092102d42c0c0c20400f10461640700800400e080c041c4540040c2020b1a1341d66200032440c09503424603003540c84440c1032010100d544000282c141080004030f000e1180d915820500e4010300101c440001c01030440413112a0314082d110b50040b5401800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 407154388 1250 407153138 407153161
    0x91805040c0f08031b16060c0302012d18050a0308040f02090406020d0f0b1e062104050f15010e0c1e090a0602010504022b0803011203122003 62
    0x1400720a03100c80010f030759580e42a8070f0742c00055984840e076180300819100b1420003d2641d10003402440340c034403030703e10b450010b40700d2409105040b410b554840d602c2d40988c2c0d0a49400c021003044650403684000d04145100081310b12840c034800030f5022080d030150110f200010841a21036041c1008020340e00c81d810160103c1000d03090080d803100502007048100308681c0c002d02044606a0810700001901440050030b84006c01c0020b5000942c501443e03d04480500001041c0e0300c0c040e21891a040007071424458440d402d414110781c5641c03200c00e02081140820000b01d0026807040604540c01501407401120401841003600b180c0302a404541d000d1591022608000740e071000b101001c0c02c03010729056194000c103080c0d509c82c8120500005443c2d0040c01200e100d00c2d401012000320524900854647d082000481041407129880c0c00d030010341450002d40c06024866001c1428920f5484d0090080c007000e49407074007d41c1402810707500c03541080c1500f500c0100c406181078582c2d440340c4c1180d8 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 407155638 1250 407154388 407154413
    0x1030b06011209030504060818100b040b06071b050a1a09040f0203040308150103090302060109020703020a08030108070911070503031602030c010c11012f0a03060312030b040c09180504 81
    0xb40d8a280038582010160084001c0048640325220011f03955a8114109400ca1864440e0006504080d1200201d80419404070101c0b503001400065003404c05004101141c00c00682165010001c0c102e090b014051080f882e0004e10742180c2c600000c600b4171008115211140b8150b860151022855580c01d50343c50304030504070b40349a90115100d240c80d04005250100a541000c5901c8002034940000e511a0140b00d032000d4062300186500d901c1e2096110003540b217250b05804600540c00901c1c0000d00301d10066000f0002c0000030000b143c00c0c56101c0c407c031035440020b00e1103803004024020014001005030b960042d84036100b20146000700d00281c1c154810780e442d51845510344885512602d41160504051090b400000c001d98980e442d4500c04180c8a4815102d0100700d1101100600820100405003808507240109a603941e90b660348903144507805040c80403d89503c0c102000d0701705031040d01d030b40f800d16142c00c4145901e03100c0e0b6400c50702c203003042c08108940c840d00004c3c2070024203106c05 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 407156888 1250 407155638 407155667
    0xd050a0b04020c160b0906070b09030c030703080906090c0d03030902040b040501061101140112021302041809020f03150130110306132f12010f0b0108010e01030b0601 73
    0x199910022804a01c0d2a8028410f101038000904c4102045540c2d00000340c40c0b00650103051185840a0b07900d4011710040d0040c480110781c80700f0419900f010f00140003903e0424840c0c1c80766011810400c482e1f41c1007400060803030125a02944604406a0b00c202c0300040301ca425080000e603110890020030050084580407503082420075000051540d4042e2034801140c0303142e0300800501d1810b1410f038010b85028400c103410307500c60100078405480d141da21500001c61040005192654495664400030062916a9070140d52800c0002c19400c040e495082844022005460703035404405412042038018051071888190f00480459059540140c01d00d440c0702104012901203580d1034031400d90702940202c2d0380030b802030802003480e010711142020429940008040c02ea01c070b02d500c8545a18000000d00064040c140e4036081040c0c80e00001181d00700750300c00000c104510740724184802c0d50f80e000c0c032180c10042c000380104022524241c0f4541565405048022642c6420004071801651407640 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 407158138 1250 407156888 407156891
    0x2010f110c070e10141207082812051803060903091914010305060a0302041a090106140f0c010902060f0403050c0d02010e2b0c09050f0108030d050a0b04 67
    0x41040040d5400c02400049181c0c5003203a00480c0c9400682c40394200a035440840c1c824044410711154545000f01c20020001509100116280c407840c0c500d0040c86600c4503107160400d51400182c8411907454841c1381055009e100f503084403d5503882c00a2904c2d120717010802602180203040500908801ea43d1794500508480c15414207000554503a80b10301c140c00d03c80d00101d407160b0070700b4040220380d070111502500c11100c1c040c190030064004d40001440907a200c40000c00100059a031403003034074420b5894024a5a1482c609020300a80320410b8000c04184070040810b424140316001c100d07183c840302c18031480e0b26804440e940c14098000400000c1d0b0201011603401c135414050809032044038010700441e1008696002400b94003101c011001c1d00203104c240780840c01e0309101c510816440b000161004101582d100b5114250b000c00000310b40403407102d1000c202440990140c80c0e0000d8a0860481c1607524211443e907903071140812004d00207031502e001400842c2d05a2004040d00e0303020f4070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 407159388 1250 407158138 407158151
    0xc0712050d02070302030310240c11091305010c0302040503120906070b0f07090f06140313120302092b0213180f060507030b0a090207021311120c030c1902010f 70
    0x1130280d11394204541c10203580c4041d18002074007500b8084a68250681c4e902d0b000b03440385583c00c003220039110911040d107285526004044103034039a0406070344a650f80703c0c0461aa46141c3c40c2c40703070941d66074003030682c100340c018842449242d034040307030f212119580b44011903918401ca82c0821402d024000b00601011521810000c48411080c10581b00700c407940d581d5122540c4501c1c0d0206281c8250040034001042c0c08100a03000f132580f802035412000e8a14228407202a175560503c402001503c0b201c0001c3c0c010511046504041d9038030b4114007a181d0822210000208444000c8044020040e10410070241c280140f01503551210f200e1004904d00c803031032000c0318140079551950065040310700514120001d46d150b4130034826208000d200420b1505118500710045000e9007001c1c4099034003e0313a00c0c4040d4241c0070584100c80030070304010082c6840f0749002d1400c40304140c0040c58124603550400410000d106040229112055465010341034030b403035081d0490041540c449070080940c50700c0f1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 407160638 1250 407159388 407159393
    0x230d231e0601030b0106081006030506040f060807051212030a0c1e0806010807052a100f0902040608030c0d0503100e040b0412180b070f020a0f08150c0712050d0207 72
    0x2803160b06883c0030390504003040c0d0703a90000f103a1040701151038901c01800502d00b400400e01c03030f820003a08050000e1022a60140c1d102e08407040b60034070f80c4441c04540c05030404108074103248081d11a40150703040500312445079003c046585102c02001030314860b5907003045210740c901030b071039445000701f5424502044e1250707188083c0100d482074581b80e011415420018180d18811401c0707520142803c41500021041e50002e1007401100000860a030301916000e0060310800344145c038410001c0081c0401c41560b140180811292103400209068204000300c0c442000c0c005040450311820785040c9903680d8525010500c4c095258001180030142c140c1031100b0303c40703403c00701e9000d1800340c13000c4181204414015500341320031801100100e0b400410402440350300a01508409005e1801311010032804d50009502e01c4150b0060003413051240c8050003007074810030803030320100c4001030030740c2d43c60410110001d07150282d5a00100040c07050b00203054014400d80c16113182c1e48080c8025501c400061 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 407161888 1250 407160638 407160643
    0x61503030e01080a020325020f030d0203040c08030a0504120609152306130f020408060c130605120a0f0e030c03040311090103081903020c0304230d231e 67
    0x2407400c01c0c000b481182c04900700c00140e10807a4000d0b81c5041200301101080280620400c40d4010902c040d4000d03010f40c03118011061005040481c04e02200694a00e42850318070320850b0590881416503005100e64a01d003600b0004407800d60301c0903001d003446090701e450000701810304181c005080501c4001280c4d041e20050700900c248041c44040580015a1030092441c6107500312100c2e42d2014000100b000c17403048652241101440c800b40151400741c640c9461442c041003560268040c0000158528680d440100550b020705400e00d001d6240c1011000e8601c0702d9100503080f2210940d0380d001c1302c00b80c841c0c1075100c4801d0041802c2502c2c5c940b11030012141c0c4a4100d444191a0a208844108000e20300604aa41a02e520412032410203a41501820a803180c01c4030210600d5420813102880040070005800202510454041c038100c4801762500d4000960511314080c94440841000060942c1c1101041c0060b200d85801ea00b5042c5203401d00c0d0045c03010044800c220030307460040700c11002 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 407163138 1250 407161888 407161907
    0x12251a03181b180c0a0e06041208130e01141c060c0503011d0105130513170a0905030a020325120506010303020f0a0f030c020111030c010b0a06030212060d06150303 72
    0x11036808000280d03403003c90069550407101460b004400b0011190f4840c020314030241c0840020b40143d040644660961514075a01003003655000404598426403015822000000c3c0030240f02302c500075450f200030004543c18480c1141e22800e8144121040681014400800c007500315105004e6000d004501421990003801801102d00082075489000b2000700d012904849001d080105002d101a505c2401400c01900f064612410540d20b4401b0460301066400003404004069540350103800000d000751099601090103500704881c91000b503600440d10340100881e5002d814110507600e00c842c0c041c0340301d9820058014000b08821014031500090841c140e0741303c1d8085035000c09042c02d045a9810342c202c401400082005400c800003489440e68508041c03041c141414000c6140c0655401c54200d2804509969902d440414042c541040303c100105103a045c214640001c201c4000d81c0e8100051a850041c4181c100d004c08020f010b80c00001490000001c075035181d9123700c1c009056041 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 407164388 1250 407163138 407163193
    0x12100c020d020a050a021905060c1c0305010b03241e040b062d090d050105060102010b062d090604062c0a05010e030c12251a0318 57
    0x41d00040002560001400b00e01c05a000b000a2003070941c15401c201408401e11076180318002d00c604001490380b1210007411603100030710b0160040040030342c1040700501610402100b014104401004040700f04001c80350003440070350b02519040303145590440401c007101d40702500001c0d200c00c1a00d0881d440246c41c4603000d412141031200b030602c0c000300f01c080d004100b44a0740603402c0503481a10503c404141221101450711420b042c00c2c0707030400162008585aa09032001d944890800102d583c0c2841410702c40d40341242c409050241c0c1406000782e11040c01e030000b8402800301c2d101e0380c0341880c48003030303480c3e07107900802656507580c89100041200120030602100308154070003904280e01004030180600c980a0040c0d8103182c50603004480003640d031200c075601400b405942040d1616119003284490350700d08010080c590100454295180c840c92051610021280c0d060040c4000303480f00761045850020410f0302c1c0d45a6401c01e0500d90724201800007640714a6107031803c481c2c20382200164180703 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 407165638 1250 407164388 407164393
    0x201180e1504061707060c11030a060b032a10110d1e0207080307110d0b0405030903070603141305150f1006030b030a1211070306140c04080601120212100c02 69
    0x10ba4801d490070710040481d01c085404c5d04950410310095210b10055082c1d035004613090035250320003070003081c14010400e2098911a80b984080011420f040044c0e0315100401d001c2154012044000200350155100031584902203401c141d8a0341441030038002d20224120095406d40400014081d044104081c001c0240500008075012114004114603003144c001708081c500d8103070740740c1e110510010022407095001522984460110340c640c400c081c440d5200b1402542d4404803c804c2500d040d105600013420581005402000704c064051003641000c0c050b808075030000707140e01d07125003401145460300401021980400042240032644107004e074444003012a141c030b852701000c80c00e80b0340316603c0c1900b6500c6620b4510011722104000c02078070800e8034140440d10384403021349080085a500076101140c580c15030400c0012741c640c02c1c98025001013107040c5014070b451001034896805100d106107110001d00c0e074000707640340c810049002080c1181540c07640100c1080210090290494407801807 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 407166888 1250 407165638 407165651
    0x15110d0e0c120a03120507110a06060602010509070f0509060103060b1c111204031d04091103010506040608210f070f030e1014030604090812071205060d0201180e1504 73
    0x300c400f242c140c0d221070305590351541548500301d029001d00000707031a40041203103644c4150740b260b4043c000845514810000464050f1a2003002400d5800180140489030400c010400107480c000c40904100c0760103480905082d5543c40060740202032661094000360b6000802d40312281540c080452402440042080248502c2c000141940034030354006e0306660500c004103012038003078810440040100c0d0000c075000740b50440840c080d500c1d4004200c404071549645012249001c3c0155a4051006d0794104842071501c07003072aa43e810150044c60b4582d02c0956902842c1c1352420413140c0030340100e040c1903a102900e14140001c280c1e0101c00b580042c3d424115200d480c03410560303044078a0f82c01e54401e96010750140080c8201c2d07102400465000e9910b00c03034a000201c1e0b0304050511241e1103d80444589003a0101600d82c8209002c140c005a2a040802c5581d03030322901d026070360b950280b0b00b000340301041c251000100440340c6c10508140303000800304905c07c02a07614031035904100b6203007480403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 407168138 1250 407166888 407166919
    0x60c1e2a08010203131103010e0d0216090908070b0a0902040212010501020d08090c21010507200c030303070305070e0306012303060f060f010c081201030314030415110d0e0c 76
    0x201d002c245c684001c20b550440390740b0046440c0c16074400c407011005000113442c02c00b1860840c580074a0301681c0001d6000710303029050b0700030380041d07180090010110030b102108050351555141d1040140040607071800300c010a0050100c1e0b03111485255001d1b0003107546201c202000c40a40703d00340301c2c403401481448a2245842d204501480c020020000105641500141080051040c80d1030242c040c00e140c1c4028070403545c0074095170340146c40c42e8581a54035040e1010000d566103030309080107c036620000841c011505c0000480390f100720a4600020240c40e1401301300c0300c500d01094141c0d40b501c6030b5800402c40520401280d141c8494101d03040e030040d0709513803e042e111213040b904a80304d034260000103691810040700d0000340354414940442183ea0319550404180c10140008200b40394840040c003c054018849002e40c680100181e804d43c5865910000c00e01c88030020100a15142c0e00724001140c5914107076442d0704010a010f010b2040c4410090780d8a0540c0c810581c807440100540d07410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 407169388 1250 407168138 407168141
    0x40510051608180f150a02010902060304110306010b040807031113020d060602010501060e0a15020c03030313030806040207051009031107030308041e051009081e071209060c1e2a0801 80
    0x44c0c03000207400e01c5a100d4606071444816044900d02e05c080d55250440200140c1d1140e0046105500c00d88080041180400a151070318105030000c80600c0800c100a219a0790300168070011a81e120110b10140400d205c080f41000340c0a2448800c454000708070040007224a411440c05d9a00d20780c0200490703aa1000c04640864224000d02e401801408080c0f10504017200b9403401d400341c900446002d0300798000070a28680c81140e5090342c03000086c40030700416600070700003900044102c03015070801e0940c1e21501d80307446170603401c12042c3d50765806410402d401040c2c0c640034a403059084d1800650b403030034003415000d003c40c2c007200e5103088921050802400d4a0309102040e41100c0284031000c02c1a0070a4010a1051000c4d04c1d91241400a258442c40700360120140031a000013003078964116140c64421051150720040521403050010b2265662010482e0040c507005240a8201820048096540d00c50820054401410022500300c14013086403407134036148140f0b43d01d024141d5682c0000b030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 407170638 1250 407169388 407169409
    0x3020a1404060c060e070b030c030708150109090b010c0606060509010e0301060e04081e070f021314060d1407060906020f0c0f04020705101a0a05120304051005160818 73
    0xc0210f0030f0001d071103022070119032004940c02035520481d030820341c407403900c40c00030340044404c01807000c0000200019207500404854021502c4241180a00c0d00c40c000039010840b1401550401036945881c0002c50307100340c04601c4241c0c0c00c12002c011160b15524020150b40c4496402408285000c40c86070a80c01e0501c40c14085800c9203074000c040e6103441c0c2da0701c00c19600c00c6040c00d44e015000601148980070480c0140454ad101d1500b148801c01e039481400b40011240c0400c010007450a84c1c4546281c0d8085001e99100b80f0071102200390311001d1820710031001d1002d252900740c0c45095408034801c0e412081400076601d46800301d9040c41c1c80203100c1951244004905070f003120107501503c01c0c03030030981c01a040c00c1d40304409039500700424868090440d10b0410b41104a1011207590036003606006c180b0070007620080d60402a2810a230100580c1c9200f03c0c45210f0050b50300c500840c2d9228445d40c2a41c000785080c00401c6201540c500b03154201d0b800c0301c55a80688001c1c0d8091842d036190081000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 407171888 1250 407170638 407170649
    0x100e0f090618060a18090618050618010f020c070f05060703020304120201050d02070b0a061409060f04060e04030504080106061110330e060303030405030f030702070f030303020a1404 80
    0x9400b40d00364070080744101c802c05804960441d02004010420000c10365049a881c0d00784103000500006d1401d000040c0c40c02070a0034039031000052000300c04101d01080481d40306c0100031542c0c0004030281d04040c010481007a0090100d0f02c0403e0b68000f010020a00b0400c682d5400c1d100040c094541080000d41d11909000402580c401c00040142d080881e898071446401410864100312200300c01500340e0344840022500440d1039010803c080165120b40406003000c0d1607098011003015002c02d03025200600341d24807030605490500000d68950708800e02070120803e4140761410a8a0090b00d250414019580d242d400d144005c90b00a115502101548001c032000301088445551000001c140e40c1c454402000803100f450008440c1c1c1702da20206265803003980ca510741b850216819184080902194480e070020030034000800c0b000002c0c1c07209903041820081d526140d50700c0591034426280e111000200c1c464800000345601603000d018200b000f40c0b175000d458a0b28502038075071031145000301c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 407173138 1250 407171888 407171899
    0x2c07230102030d0b060712020d080a0b010207260f0a0605070e0f061b0f0d0315050d330b03010c0903031407060f02032514040b0711100e0f0906 63
    0x40741d00000061300503190055000d80514901036194540e01c071148000d40f2406c0c00351703000604072403030507500101540d40000030317a408103c0700e000080000d4a4981c05e10508090141040e601d9409450789600d41502c2070060702104d001841a080390b9840704107003d0195000d5107803c000440c210301444200182450007080420b100c0044020040300741c00031113804c0700315007680105e03030b0300d0440400170b14030604206001000010110417004040d80c1c1c8540031401e200702c1e04074081140d82c40e54600c4090706a880300034060302ca076925401e460034614210f0045007c07186249410982034a0303034000c0c81d204005400a008445003540309503804a0544030040001e0b4083c081c9149140b2840d001d0015284175020100c5d04004815141c01a0b030000e807074600e0a0303505002c16120032804034000c40608152410014070088001c9140007440c0110721883d0800c0c1000a01c01c0100444002c02e541001c000804240c411003034180024180c00b8221001030103008407028000c038900c5c0c5001c0315403041000804 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 407174388 1250 407173138 407173147
    0x804020d0308130507090e10021e09130f0207020406120210031d01090507051206070906121112060907230901021606050304060c050304080d2c0723010203 68
    0x20100c1d10b50000034024054103104024240028005200e900010302140c6004100500c500f44200d081c0842900704076075161040040c80c451400300e8107054400807040490944400324035000c41c2d00c0c48000304107403098074685280c0c105007490f00d502804981e8000c2d141008560b40f14035003068070301c07081d20020398412004941e50003144d00c40e0f0806480d6041e07005600f00000340d03034410142525600e110840d07194010327040c148820300340502c1e0011030001d10b0008041c2400e00e031002401c0d9072864002d8004106e03810542600040b52900101d8074602012041d95a13144001ca0012880340140d0310720f84900a03003004605070600c039440c2511001e9810f00380c1c00141c5001c0b03403160340f40d5001c8041641540505d2142c01e004a82681c2d56200501843c1c0b1102e6407490140342c401d080303441d001014403e00c2403c1c000c0c0004200c2c03401c20389004001d81d6000040d017040e01d1000d60300d2100d50000f904040701d040303110049200c0010510780d045503070b104590090080b1a000b4aa400017140000e540164010300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 407175638 1250 407174388 407174393
    0x516031406130f06030804031704030f030e010203040b16031d100e0f041805061f06030509010f05090304180204051f1101020f0406020d020606010f031a031e0d0804020d 74
    0x41d0400c000c02c00402c0054104a94125075041d140f07998400ea0300c1c181c4c042030400600072881c0c90b120380d01145c9a8020710785402c5035182c03201c1d01c40700c443c082c0420200040522499001b0012180502015003521751901b600b410100401c40344000100c1c005901e1507500701e4125138503441c5600d1074000800700401c001c16180112582543d2125841c1c0c0720422042400c0140c4440c803036001c0404c0d441c03284080030741050a00b24540074000e8a5007a240341c041c0440500300310000c03a03040958540d0b15011230641c8400713140074094641034100741c125529060621805050000052088032400d0070085a03140c612814a0103c0c000c0f4440c064110080c0e14903a0b0510035042c45662079201c050030711004150004c1602e07400c80c2c00501040c0c3d64010001001c0c0205501001000b880000707601c0140003901e400400240702d1100810400d060517111000c00c50840303040100d030360611402030110703006203462907642034114042c0b94203214140a144c0c0d900b20311074031a00040d44950f4004c1c110b03038821420355 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 407176888 1250 407175638 407175649
    0xa1e051621020d060606230a050304030807020a051b100801050a09020922020d0b0f10030f091415010602061018060905090a0611180f010c02090108010516031406 71
    0xc407070032640071003510342c0ea0002418900c1100c0141105945031011014420720782c03104903030a400702c40d20305072061206031510f6030b010040b03d90095040c6000100ca88880c003050780740985da0480103140c1c0c06800c000c40f5a411603010030004e40341c011175048030030094002c0309490841c400e0007140e8010000000a00c41140da40e00240f10440010f00300c0246003800e11140f119002411905514154002544d40f0b100d2042d4022014142030031180ca22050503c980020300100d58000305000f031544454040c2600801644070032560390304404001528815000015141c070b250907450340540c9403840011503418030005105201d00b064031800291107003003055651120583d40d0007074202903243c1d0000b081c210f040740075041c0500540300040503040d1492030440181d54208440307040d0181e051084070340461100758440c0c800c41c0d081d906e4018910522004070341c0c1e0b0400b40800b80d04582007000019040d00158031040c407030702060707a000700d0f0301000712000c80aa0360f00200015000a14501242c0b461410 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 407178138 1250 407176888 407176949
    0x406080c090303190c03020106051f1409060d021b1f0e0c0d080702010e0102031314030a21030608030a09060509030c03070b09030724050304050a1e0516 67
    0xb400c070b0341480c03059004a40000030f40b50044000035031040141040540901902015000490312400b64903864040c00544001b0740305a00100070602d8940180d2044040c110341c4402c4d800b0305115a02c0441701102d04c080e40c0003410700051a02c603000f0803d4070071008100718003a1000507072028060f0162100f104050200180003c003103000361001d15420b5a0b900c850085924868161b20741c840c400d500025100c25650103005041d90410030407446610982e40f980c00940ba070060540b03914595401c0400d203805003103140101025602044c012500114602100600e203050b43d00740002070300c1d11181512070280c580080f022401702c070020311895010314007426110380060700312a00c049540d000646030440380c1d4013400031000002550100c03030400340420809040103030318800040d90200218a40118845004020060044003290800100380051420160000b5800750807010b04d0840344600e00c8111421603240c07041c903000c901c51125000d8030104903410302d41010080c03540d044902c40d40d0400c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 407179388 1250 407178138 407178157
    0xe090408090307120318180c0c06020a0e09070504060804111801180e0106050a0b0f1b0601090f0903020d030b010212130f050d0b0a0b010c060513060f020406080c 71
    0xc240442111a201001014014807000300301e482d80340d0050a020780306455800e601503954011000c1072210019119580c0030782069007a0000d1144501c40003150b0030140350300000d280500020701c580100e0303031102c3d411011140032146c00f44aa02c480000360b4082c81030344500804500f2200005002c1020740b0341c450201c0744003401300040c24a8100d03011005102c01d0700516080144058880c441664520420030200e0000000b04155403c1c800003600b40b0401d845940980c03900012030340056103204007a80c040f001c03040242c42c25100300200030798503100240501040c06140441e0101010380c1401111080c90305900549094012280c0031801390441c962607906610a080404080e966214010205d1001141c07400340070600305074481d09103088684c4458412002c00034020040340000d00c104c2e8021b0704440c00040c2c110712020040c0c590545060014250030310304810000381248170115006524802d5400700840e402808441081f4082c502842c80001e50150004450310345410042207000b4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 407180638 1250 407179388 407179403
    0x601060c0c1706150102070308031306020f031305010c17041401061205070e090d0203120702010b04020a05121f03060e100603030906020f0601031e020a0305070803070b060307060e0904 81
    0x68681c01c6014282c079040c41800016800341082021558007070030100d141c2d1009102420689284d03440f107103114000600040c044100c6040c3c4042042856412941d09200d42e510b01c80d12031404102505800790a05000d403055400c020100304070f10702c80d998000405010003443d00260b00e65846101c18001d08203620041e5660b195004100c032042a841400990b10440041c40310302e05080a080145030003518100f1180d120710244030307039990084240c80c880701d6003900b900381581c0c03401e404a0241002610080d0030502c0003c0c080c2c030762070340840100000180031004007025165906458180201d40a07001c000c3e07a9a51000d000040c040e41140d412080034a040b0b5210f403092240d800102d41e010751048001c5220004100300494061140c0890303c1c80110141450358955141d04001e480604030044000241041c0070045550341c1c00c20070051030b0000d003218145511501640d80e6940800130a441030000000062014074000555109540381e0781d9030300340020b101d101445040c10014000b03c4145c0d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 407181888 1250 407180638 407180663
    0x306090c0a03141005031b0603042a180b030f1b0315010b0c06070507020a030b0601170108062707091119030906050a02091011030c01150510050304050601060c 70
    0x141c1e80303541038007030155904413118861500c001c2514111544800800d40401c1c910015125940c0d0b100360780c0d0080c1c02811480305840f940c540313014507402d4140100c81c42c80c466100401c205d4100060b03c3c5900481c0f84081041c00c48020406035030302e444070483d50070341d80714400400b01c0d5840c1c80020941a440501100c00040c6103a1341408002001d82010f1820800820300300d440c43c0301008910b4010b0a2420306030302e032102036000326508000c1070202401c640340080105401d0307446420040380d03050302124086040e5840b101104c1d12070310301791040c005980121030388440026080b220032044c1642034008049440c41c140485c009010954100303c0200e4041c049400003241c01220725410071b503981d90009007501145840c404507036014001c0b07083c440c81400703014a00e4907404001c0341c4e5031103642015800b070528400f2180c80d43c41020710211440d400d01301c00c642813900500005098420445640d192442c0f03100048600c1e00040b540505194415070040251500424102102500401080480 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 407183138 1250 407181888 407181911
    0x60a08060f181011090a1208040e040215070507030501061a120901060f030308090d031a040b030c03030403060b13421e08120703210c050705070b0306090c0a03 70
    0x8540c0f40500c41c450f00b56001808409616203642c6d020301604140d50b40000c5c010040d1264401401180504400444150040b400f55070722040014615002e07030340410782d20701c190305d030035910b9844500c01151207600b032000c04207803044031911012080401c00002c03420038607001c1c82c0041000e4050700d004200d55030f9000116001c407072400070002442c0a52030311103040c148003624601c1e100480d07400720109403401d01010060140107114460018045a0104030181140300003402d004290701d0041d410f1000060000400c0115041041040c008a13685144030440541396016034580740300000712500101d14120b01c80c2e681032a00d159a04486039910140c21800d0050b10401e6003903040b5242000d40341110000071400808404007030070498018201c5984243c0340695a0b020b0402c0050030b000d03a01a12040010080010105400254205001c50b0510900c00781c090740c0701c00e9041d519405454030200340004190304482c0601e50241469044e60f441451a40d166000542608205030b01d40c0c181300039 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 407184388 1250 407183138 407183141
    0x301200909181c02160b0708090a051f02010e0a0c1a13180c09050a061b0c03060e1506031506210f0d0e0306340206060a08060f1810 58
    0x14504031204811102c610f42003002e445d0074038032112104107041d1250244030100c0d400003a81c402039071041c1c06039164030010002030720302080c2c1e4002030f130031031410801ca681e242c428484000c1e0441c4244c000700f20030340e8940c44c55038850031a248058400340e250b5608220500140100304c5401070a4040a410300c07810055502d216225a400380614466015085000c08824850200444003030306010750828500b0700400c0052009100d503d0030700c880d520701100305946001032100c489521000380c142d60741d207910701000100f80e1030410100c148500b110031103400d5421410396000710790080040c07060714000f48081c0c4001d0340040900307401c80c0650008102c803400c40d08031a40111081000f50180302c480d001c0c1d003071410765a54040350401031014464030f1141c8010400e2034010601000354140400c03040003c0203111031901d686035064101c1c2514551031a80803850341d0140208956000c00c155844116581d2100140c0b01003000c1d0741140041103543c91444410070451081005441c00e01002508020 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 407185638 1250 407184388 407184403
    0x30f010207060504060c05130b0c030403052a0612010b0706090219030b0a09080919031b0302041b021506040e07060e04050c1218150114030120090918 66
    0x280e4032a01c40f01403100300310860160010025192070100e00344030141c64291107010f80f52041c082c0d1680c0010741c00d80c0403041401110040c41d04030301152000c00756180d00110300342d01460000c0310342c0c03214030340c010b040d10b0020300f214041089104d200c04a80d08204c640103407a070003504101d409943d1101000c005880e08c940110040f056080c00850292440c1816002018002c1102d149a4a8201c0c3c3c0c00c001089007060340c8100005407140c60007070b002d146151441c02919040642884204402c9a19407417010f1888810740b44251001d00c080201d058285c21340c1501d16840c00d0151b04941c1d007074080030340d0034400d80ba03002d04001c00104640c1d111803c00c03400d048407904810b0018020345520390a508140c091550841c80e00402d05180412807901806900000303803928080081c8054500861102005164043e0100c041d046d81d2950790b902076990440c60040c00306001e0b500303000340c1801c000024150100c0700394914a20071b103060348075400c200c10041c009020003103804a02118180d0000204141d1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 407186888 1250 407185638 407185643
    0x103090b1e01140105120907050301111e070c09180219031a07171b0a0903060e01050606030606070203010e0a050a0201080108010c090b3a1808040e06030f010207 71
    0x141c40d04103020159400c0104160000d0744010042260811030703907401021180d0200c2c2c080403110f040e80701e0309181820b00c1000d500040d419800d00151507400c00b4410014040c080002c40c8552a003803c01c10761560342d01981101602d0701921071010403040b03485411001d540c008130103c0801c610780b00e600080c030004400c4604800b42c03154031001c0c0200480e0809030304c407803003054240d05480d10b01a0303001030403040c82181117808884880040307800546103c8541e018a1882801c05441e5171000d00700500c0c16655201c10b42e030103400d0410618202006204181c006c03500580380610315907a41c803c2c4402680322040407a05990380c1da80075410320700103115142d9202d1080e0060050030340680001000d1002c1030304104050303403428800c81d41d13094000513140100c9071428405501c0350f205151079020800d49035690403840364403195050108004401c1d0301c640001000080040b070040c40480d9202c4021848003d2190104002c248a0602a1600c5652020008040301c00b62144100c459082e42c2044070704 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 407188138 1250 407186888 407186911
    0xc090a030303020a030b0405012612071a0106030c0207150203041e03032703021302040302091e150306180a080406030218120c01030e012304150207150203060103090b 73
    0x840503e13a034580210203040b20115010b01442d410f01c40c0c00d8400c0b07660f4100381841e11f5800120303001101c00c10301850140b191035001c02622120b032420b00c0c0201d02010440c044002114000204116000307216081e0903025a41c014400799090401c044805901c40e0721a900b07520051100003501810f00410085072200305001107140c62035841e0181c01103090100782e400703044a08043c00303640001000c1180413650100d5224041c0d0318950501d000a21480c1c2029420140100400c040840d84000c0141d9001c90a103e005440e03644002e03241981c0c15034440c856140d0800008074126265945040f00e07aa044201950a14072160f03032150003583c171a03442080400d40214000d144200c050400f0729440300141e079946a06620b05020769101c50710011054141640c6c0c1000c068015400d5001c00401920518024145941c440f440003900d1070444048407030308240301030641c24681500075100340036402101d080300115544400302c0a900000c00e4a1304040e07548070000b000c1074113080f2040c0603540080e0b9 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 407189388 1250 407188138 407188147
    0xe19050a090f1503120c080708030a020703080a060f170f07060f0e040203060612090a14011a040b01020c130b061602090f0103020609040b0303041d0609160f080c090a03030302 77
    0x407000a071503d24507103540851024800f0008070300303100510b40e00842c5c136144c500c8940240c2c0c5014200350048607006132102d030700401081280a820350003021224066200d5089550764040300c0c5084d51560301070104c90104c652001c2040348402c070f00c0d0040c101040d07819aa0500b90b00e44c00140f403d805540110009840c44407040802900b08e100341c0c1041000740c0e0150b10b1450140c02213281d6102e401601407032140c4a5000035001c490900421841907800181c4130001818081c07600d000e0510600f8002c202940c82940c00510318041c07080156080040c5c019006080c030250801200d0ba01c0d108044207040d441e120a08059620742c4001c1004030203141e40790700d102c041d034018030111510042801d81071445080040c00903075224001e80360888821100071a0800c19030000c07038250b0185a1008210f207071940c2c1569054180f606186100f0001600d0861540ea945803028514448040150011940d03110b803a041c0d15109404080d84000007401940c504000500480d030000741d240c1c02940000c5e404035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 407190638 1250 407189388 407189411
    0x20a0203011a18011a0f070501050c040f08010605030d0804030c05070e0403110105091b010e04050c182418091e2802090102070f0e04030f0f0e19050a09 67
    0x1454040743d403545070b00907440d030401446000e04c81104020001041d00030541103052030100d011118159030280080c032441c100a2006807094000f40a40b6240c01401540429000c4051041e03d0440b00300070020990a020001c0076991654060001c2c0c0c20030840c4111074000c100c04200e004024449501406220b28060400404044110f040c80d603440e4189030a0200f642c40000c0e40e0b24034201c1e5100c04bc4a5003035003c0040c0c60160b006040aa045801d04e03040050044040c070141c01441c0e02201d98480300c0c034080341000124085100d1459900410461518084120002510707580d14000541241c240c3e0040010b0620402240c40c000c542c418510b14142c03080c40c10724100d03000ae21000701221001090350035001014140c000b0451807a0340030803000c0e0745a00c2000f641000305003071741861002503110b80c18610f020208803015030100303405c455581c030813074440d221a11943d0365584e03030741440164040c20010f030180310002d11088240004030204e00b943ea86401d5070000c01000c1d20001740400d012 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 407191888 1250 407190638 407190649
    0x180607081207080106022d011d0c0307060c03030b06040f08030705010615020c1509040905071a0412020904150f06030203011d0d0f0908070605040303020618030d090201020a0203011a 80
    0x510765010403841c03030010800c4940029410b4520304407029040c50000c1c45007d1841e00304000ca0b0b05054640c00c10b0207071541252002841c54107603594900396041c42041c2c1013030541d00c1070f0911416000070107040344003000c2442a84031003c1408010103051405984652a07031882030325401c615100c0e00001010310030428244a202c0040444a50413201c2c0480c000c0e019403251010390006004e040d41d5000002481025002c80384c59241c01441006030600c6400d20ba541c4400500440040c0580d10540903d034103607072000e40303003151000c481f200b455102d030f5801e01101c6070010300304844c0600d030242e546040d00b04034001c2012800e0003400005415281d80109400e442202c0d034460300d00c500c10312403641903450201d04500082c141d030078005c1c82c101a2034400c03101c140065126104034018020042810b9074410001c0013200d020b41d01301c40454540c500c404401c200c18804014046c3e00420214592900c95040b40c403030140140183c483c0011203401080c250760203140c1d08001d451a083e240001490700 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 407193138 1250 407191888 407191891
    0x70e06030a0c0806090105010f0c21021e010506101101090515060a0b040b0706050718030606031709130c090f09050103020901080d080708060a030206070b0603010b01051e1806070812 80
    0x8a5000505c0c0d4900b0002814403030b860300000341045940c2940c0e0003444060300254020143d4600b12082100021000030348440418005188a0fa0f451400800314003050042d1801190000c08103102c1e1007017402c0c1610b01c0700340e0b019071121319500e85240342d01003030040c0036403801a507803c1604d45161402c0c0040010610b4035030170446140e2028041441038a440c00143da000585c001000180364954a00545042c2e0200c0d01d2a8500303400c01c0c1c804000c214032074000c0c034120b80c0710306405100d901a5195400c0f0601802c021590007810503d441c0140c80d803179820000300341185040120400b41c903101c0602c0506140e170048403105485800400860801c2d4000c1070060210b10041e11410345c01000c0101024400340c42a0200449400417585a0361080c10b8040103682c018641980c0f00e05030f103407640f443c2d24200e03a114401c4d46000c00711450b5501441c1140ca01510307400c980740402203030100c10384031900a1011400701d1031541810124944800c0300070b20480c0c0c0607580c01030721010030f2040e00d1042c010 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 407194244 1106 407193138 407193151
    0x9030a060f051003120c03050c01020708040f080a021c021f030902031209012307060e0708010b0103060b0306041a0306160e0402031e070e06030a0c08 66
    0x80641c000c14070300c0e00603030060006070340318251003544584038400500300111501e0841c130a0351140d900216190b2190a03c82e0801d80d0741c2c1680c1d4220b800a0401b01c072090000901405030703c10310049c1c500103040da14020400050140d011420340640b400c600d00501c070390805120210358481194040501c40d1105000e074004446200a01070154600140d00a000b41c0c02034030400c00705c0d80201c0c8c0c00340c0c0040e1148402065600e5266801089240b4074a480c0f002c00e11440d800154140903040d101c9410400421120703040c11580f5084070482948a810b041c03070104200221082141901c5e401402101c0000b210b00100c000d03400c002602d0242c103907041c0290303000c000c020303aa00d828013000501141c1e500c00c80350f4403000a000881c44150b0381140400810300000000703020a41c1001d620040358504541c900b1000e4000c550160420366488000075103484200c040c1a5022a01903401a03 = true := by decide +kernel

theorem cover : BRFrame.Cov 407014388 407194244 := by
  have h0 := BRFrame.cov_init 407014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 407014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 407014388 ≤ n) (h2 : n < 407194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
