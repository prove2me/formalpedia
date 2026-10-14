-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1709
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T04:23:08.88188+00:00
-- url     : https://prove2.me/submissions/2bf63a75-6304-48a8-b1b9-770d1efa73e8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 307194244 ≤ n < 307374100 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 307195494 1250 307194244 307194253
    0x30b0102100b030a0f0b01030b09030403120302250506071b081603090305060106020c0a060c0b0433050108150708060609010306170f1204030c090510030c060f0f0e03 73
    0xa03420319580c000092015001d0708813503004c1c0480c0c4408040e082c042c601152036810700001002031014248519400180300ca001d5071030f0030b14588e180e05986094002450074190003242d401101441c210640b1010028900c07161a120801e00d03080740c0710303002158a840410110b4581000032450600c040c011180d108107072078544480c0c4c01100b40c40b04101d5000300c080215140000c0005041071104e54000c215603001031041200c014104554003409800107010005804849400b117040e580c030b8213412603080801d180040c102545000120b40c03043c03000c410080702e40034070020b1508065100b1412500e4907803d0352281006d035550701c00499419a4004001000407021405c945490300061880310814180051402d80d22000c0100d04402441c885109820581c1001d1003c001400107030601800c0640441c901390a650395002c19030704a0184400896403940019011181c103202140a180c2068140501d543d40c0c0c440100514030040014001400c030b00d09150015000f03011180b0400350090181 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 307196744 1250 307195494 307195513
    0x50409020c0102040506070f06060611030a080a020903030a0c05011a0312090102010b0d050a0201020706050a091a0c01060e07030b04051014030a02040615021e030a0c0f020405100312030b0102 84
    0x120081d4006030058007882d50700304400140303651507000400d190341c0304580d8841c5410843c10100c048940a6020783c00780410468100d40101010046503a0007015041108a40c0c0319040d680c4002c1c0a00e09150342c00d0300c00056a40045600442d040c0341d0141714600030300c449068494143c184038000e00400e601503000700c21001410f4003c1003d4090001d044c40006032034080d0000149409490501c00d41e00c0350888810036055581c140300c04070103003542d400e00a2600c0648080140485024818507018081050303114a0b0144000121410036038040300901c442ea444044604045134155400004a4549205c010785410720380102403007842c00c8a100c0d26400e0ae01048154000c6d015400305a043c05020300320320050f51180304101c060b1556540c4820300e541c1c0807070040d28040d030803414041861040e850503245800c000044800d1800145411b00e154400d900d8031060500b03511000035405800c04003000741e5940400c20001c1100d0140385c24540887c42d83c2000d034110b9040c294146e0050b041071121 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 307197994 1250 307196744 307196759
    0x1020304050603040602091c142d0a05030f040602070f0308090d02011b110f0105040e011703040f06021027060b1503040605040302010b012a03050904090302070302010201060f060504 80
    0x14681c0540550300240c034021200c0000340d50242350600c07404010702c1581110701407200144404040c81c0819004007a0565000c0c0e01c511020141a01c201002c0d0021707080e0000b000c024002880d1311340e8003004a9444a0141038480016001070103a11f00505c240000082e140040303120304070407170343c000c104a80f900311440f05100880010034016070620645038004111350f00c02031220819180143c3c0c000c0c4c0e03401950350401c0344005001c0141d5040003400c2c0300500c1081c44080000b4115012240c0041e20706020a000364103500803607015542032101c075003001403842c1d00401d0000702d00070485400c0084c0310601140e14070300e94080341118204c14141c200392001a405600603484910b0041403003503508a00301c01c51440c1d61044608446468454060008050f024040c5c2604074009007001c500800b01c0e0300342e42c00d0306200700c800d0340380e10b1015880d07144c1414000c1007150700d90030020300180860051410b01030759034449880308a0041d031809030000380b00b14a440003401951800da803264a407c1c584040e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 307199244 1250 307197994 307197997
    0x12180d030804120c051f11070b0a0e120406020114131104051b0711180705030708130f050f15090a11030c090414010f060509060d0606031e0506060a05010203040506 72
    0x109042030121410092002c5a02001b04240c2140c0b0503028071144650407000500780c07030b030a81d01513202100a00c14080082c0a90705150340c44500080300060003006001000d20341403500740703810000800028045281c6506401440548400800c2031019403150071202d0b501200c1c00c00007410754004180700010502e0a50410794100030030f0401c54030302ca124003260702d201758850f007030803a25071340e010911030900d05001007001a41d05510300310700c101b45040b41d405022440010810700030081942c2c002503400142d4a807101c405504403940c203121b0b0036075250060361a8124403517502c4912580e1902902090001c0c3d010744078418060182c40940c90f6562440f240c00c4501100c240d01d8011032248004030b841d4454520701ca1405401c0741442064800e211a003113420010b080d03061079040600501c40d42c1c859881013078000c00140e804c4291889203052100081401d9000204441444881c00510080d8a500c1610071030245007030f159292510404c010040c1c20b544203d60140e002440b04011500d403020 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 307200494 1250 307199244 307199273
    0x9070305070c0c060306050102120c070e180303011202030f161707031a060a060504030314030a0e010509160e010e04022b0c03060b030309130f02070512180d030804 72
    0x2e15041c2c401c2550f41d803046040c1c03980c01910000c0da480d40104850b690400130201d80b8070314121050303c2d1916503200c150300c1c3d520b80d000d01018101c0110120b0010805002014600800d40c0c042d60703129610340b92800740b039003070381142a8424400c9202240c0580b001040003080c0c0d26199400560325898000d2801752a0740c00000e1161034081d2050020204410fa40e1912907030b00c059544541a1a20404102048101d60444410844248018800660000381e5030450030801e101282d00da135140700103200540740030151301e000c40d42000117100107104002441040e4080610f8903101c0c480d107600944002c58000d200701c0c1400c0b03245802260150074540700c01c00c81c002c40ca10240101403100b03c00f0480070403041c0360456044162240810510000d40300f0400984805c038081c600c2c1909141c005500982c4140400150031303a101c0e02107010501d541d0488800d1580401032325031546441598206a800280080f04a4205150000041e03d4268062000706506483c1c0e5803190b1a035071280304111481c0c0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 307201744 1250 307200494 307200497
    0x2707090c2309090f091005160206070f0806040b1c03020607120902150a091703030603070b040602061f05031b100203040e040f1a0a05040c15050a0c02040f0513120e0907030507 77
    0x10007840b07800c02c1c2c0a0103020308c00c03103c43d001d0350f0012600c02c00080c500782c1c0c0108014100500d01d141403c5059000c3c1d03506410510441e804034011040310002800c2c007801d00b1907404445c2078145210100358011680610070519134654640181c645001c06060300d0807040c0080d03011080e0740c88544a00c02e600c2c040c0c4000e440d01d05d081c0c0c3e40d1a45600b1025060003040307092640d1a817001c0100415480c0c1000284003400f10142d2007801d061802c40d000e50f44901c00703040307828001c454054000c03c00e407620109400508005040301c00e081c0210819220340103081c88000d01450010041103030184c00001110100c8041c80345503406560b41d6210001ca117032001408450b64060b980c1e03010700290345000380601603070b07400310001054103041c07130511448903007a40300003040e41039195a08840741e00f1500352003d804483c00c040750b190040d480064000d02d1349200c002c50041ca05814400c4807410814264842403045000c1643c0d016118019282055005e81041d40314030050300080505119400c401e4112825 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 307202994 1250 307201744 307201753
    0x9060902030d050414180c0306190902092407020904050c0a030b090c0102011a040e030c0a0c060f0201050606090607060e0d030f0b06032707090c2309090f09 69
    0x86a00007400d02c2400307207850001039030204061140456404480c90310f041d08840041c001c08815150001080004103144904400400007070300944620b4080d000500010300c00110642e01c0f084900025001080001c0c020000c000406c540017001d40f014203e10311742d00c0d080900b007a03419800c0182c2d400ac002c000326414018402c0701401500c3d856401400303503100f14525081c601d01070f0390841c42d09102010490441e03041414454501c50056991350180005550100e80600c4a81e402891441083c503201d00f944110706050702400070180110064070810354900c103200b140541c0c12404e890017551a0340c0d21030030400c40d811083c949000202007051041d900401e01d80800c0c07400321304100e21030b090340d00400e8403400400389484041c03046610400301221454110b04042c41d41031202c4c0c1e02002c03075a002808844034460485803c200000c001c055450046c45031030181400289240f050300081780c054219032817013000c600c1202c0306685403214041c00c1d442750781c2e468800c04c0340c00c0c1201500d42e07040b43c001e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 307204244 1250 307202994 307203011
    0x3020a14030301051201090b0c0901050403050a1104050c0f0a0507060e031201030b0903070b0a0510080303010329090a06090813082a0d03032003091b0f06040501030906 74
    0x34844480038205140380040c5869624143c180551680704894a0aa0740d1610790901c002603500d101c1c2c1038008a00d14126a00c0307165003030050702d9a04c19030304090928070400b03803a10104802c0c034030b50074001c031410380b030900c000d440f8540c0d01c1c03040f800341840802441000744a0000c50f6807061000d40420f90051001107503000702c90540c00d0640c0e02c6140c0800031024a040140103109041031101c0e00400309100940c5400040c2c0c80d41003a014020302007002803629400803a1400b502c460303500c00a0601c0c10309881d640d59403032404080c102185000c20b401c0c40103031451040c131012141d21061244982070064400020582d503400020084182c1c115a082020301589032251200600b40e00580b40080060042d400c12800000d00100c11340c024038104c0e501c000c0e8030140f40d190414034444840c0d1608010900404060307040301c01c21622036a01c00d1410300801000506640003e40080b0b98500103086c0f09400388130030a1244040c000aa8142c01a6080000300803c1d4401c0c0d110413641c60082d040010720302c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 307205494 1250 307204244 307204253
    0x170a0201020d0c020616080705120a0b0307150201050108070302151309110a1103041d040c05300a03020d0f030f02040e1b03150d0305070c090606020f0a0c1203020a 72
    0xc894110050050740078008110310092400d901c00e01d06d40103030420500501d0702c640c00400e644501d52448845000d002d001c01d00d18801604140309010004003a01c0c0c1c11515031080c1e200c01031191038603500640c00e00c400055034500104600d01582d030050060f03003980318002c0355011681c1c444429498004a28100010341464611841c209100d400750350782c1c0d596011020081c040e11054800a0742074008110800a60000d03020300940c501e45410244019519400c0c00d0f1150007095001c540c0202d000c07a1821221103821068440e02c000345000070722103519103100280e6440c0d94010040169004c2c0c103900060502030000c00220300c820b407801082d40c0c0c035551841d4040e42c000342c0c04180f1464507441441206a140d0513541c52524410b22000e007149000d00020344511641503820b0f002d400800d0021051620030710458101541201000b040540d8466000c0c000b40a588038600041c0641da019040080000c02c079030f503000d500034400000081c10414601031a03540320340201d0039849400d24140000c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 307206744 1250 307205494 307205501
    0x2061804090c17060c04030210021f050412020a030f18051c030807020f03090d020a0b030405060117030f040e0903070c060e1329010e03161a0403170a0201020d 70
    0x1e0312407050584058a4190110007014218180c422150400d40c10444502029820780301101d404441004a111703940005074201071481414030628164040340c46101d11650700402e0065104101a03020702400c44022a2039801242e002030005a03002059403c0c0b620600d400e0180d6004200000e802c190350b8000285241d11904808804400b0700c0800404d1503005000c8680c45035840c00602740024050387c106499204000b003d5206416504500e02951245841c07080940001d120312580d03820281442035a50100b48a010010700b449a0306511401011055448082e0100c9a0f182407a0a10110b4450490010403044441c0300078014036001c02c3c0d01310f6141c0018907050700d031030075480080702c00e00c2812180c00450300d10080c1801d43d030b2081030400154041c1d1404900c090007102c3d40b90200107c84220310390003001e40c184102c403842d548428011400400303d4115100711510414030000500440c040c1e4800503000b04400b81e080b05907460120300a0075940303054400140360a0168040c50200c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 307207994 1250 307206744 307206761
    0x20c040b1f1805090103080304030f0504051c0b0603031303170d022107080c27060a0e090f041a07020102070c090e0c0d0c050f03011508280f02061804 66
    0x30b001c003280100c00300d070b00002c5001501090720f20a4081d81180c449075804c0c400a0401020003c04008143e1018802d00954000e0800184204190440c0807907030301100340d810030155594002000411180e140000488500302ca1030118455220310310b84a801c60644400310510317603404100044081e000080c40103054614000745204244100c07140c101400610040501051002d503030240415112142e01baa40c0c2c0d18100780340004903500030185864201e51407500c03540c11a0700407607141000c5400914030000d1714000d89080c820384c2d035880780b0f0450baa44240e902402c81007885040700d1204500c414004e80c4060240005403401c0070f283e46410310286280d100c901e03540e6072407107080b4000e08140502201c5000c11500603454468070303224114441c425205607440b40d46242051032003a1002c2d04440411940045d00d61905561250100e84840801d1404e10760110300243d02c3c1c110500314640d1900c1c1d150440300c440541001f59091103020760001c00e142c00a803007900b80304640c55845004c1ca160 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 307209244 1250 307207994 307207997
    0x20d0602040815130b06011107030b090f0105011a03040309120501021b0a0b0a24030606060f0f0207060c15020304050706110316080f0f0f030601090f0501020c040b1f 73
    0x94035440c2c40c02290400c8203145001c0c00400034401031000300548100891103c1d42c0162140281d134031002c0040c1c072034140e041645401409111000020300c04508840c6214145500030f41e1482d003545450a0b00b2500240601818590400b00503142940b5079006541d01600c00e06101030491340b185801000610250710480f1035039000607051000d03000500d0620382040900000f80220716803503490300500798004009040841e59000d9840701105d02d0940240c5401d401240c1d52070441e181d0401001810a03401400d020440a400c90b9005901c183e02280070380315941e01500c0030358140f42040707c3d036040106081d540007482c00307092181c0400610045005d18070030390040c600c8510340100a0040131b204d0181090b150024400c640c40c0c0303003e4a1070100ea1036884a08143d80765040c400b2001540913080840080000200d501e0540d44001300086029010076282c803036050f50b4480b0840c041c8800c9002c1c4900607040b09103056000c0c1031641103078885810040018482c2c03080e5203c084980140c0b803072880d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 307210494 1250 307209244 307209247
    0xf03010308070203151512030d14090f0303010e0a020901120c17061905011103070506040b041502030717041502030c070c05040b0d1203060306061410080910090c03020d0602 76
    0x441c07070100102400740c5d9511980505c285400e11010700000303180b148903400307650010555280800c040c000c0320303441c0d200200e040110031400c000403003903000100e030194554440d40301104643c075000011390b81220700c2818420f805943d51011900a0f41002e0ba4240c107025044c5200020340c0f0f002e00130810009201c1d6240c540d0b042780308105200d0014040c040a015480c6c810041c0411840340804109660082c288284250b41800c442442c40c4107140020f00035024103c00c0c0030804c001a142640a20b01614000da035241ea44164001244416941300002c0340755a0a000d03280440c11100303640c0240108100a4400500030800050740e00c115840c0c40100b07c00110007040081c81e002c02d2002d00700545040004007510000300da5840d80114024181051058035000c0c180e210381c00c56005540c0c8442e0502c03509980310040c0c2e0210300b84e0440c2501c035046209601d4082845210140e1040c02c4113401403d80d8601c0440c800000d004000003550250b0b01040c0100258907544a11b8003060320501006 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 307211744 1250 307210494 307210507
    0xc09010f030b0a1d0a0c1b0c0f0909030f031401050103051504050c040f0807030203060423030d320708131a0406181709060405041d010b04060b0f0f0f03010308 70
    0x44d00c40c003800524090285180c00500400389a11041e1a90700640d5078951004807041d50405601a507180c2d4001c05014049440c0414017503125041030404504c01d0f00c461600310000102179007922146d545c0c0840c071076441300c01005690303c42e4000c142c01c00450f02c2403180242c1b1043c0842d0a80304112040200719a00250401c00501c100b00a0f41c003c012810142c02018110340c002501c0310400341002c0e16132a6804010003401580c0f0200307800c50400a01101d03600d24189071680c010b80014058100141041d122841c0e404510b01d040d10001c42c060031040b44650f45440d0207980588001d8031000c010300302d110802d03000400c014403652642e0800c000c042c000340b0381858507600741c07042c48807411100710106002e000015043d00f0700003400b04200b10003540f14410300012882c58001e590180f5485801c06c10382c20b203500d0605501d80e50f035100200081c001e020181c428081600c42c0c0e485112000c800401110396001d080c18040d00f103d0021200580c940320f88154001c419070000e1700180d0b42c0c0074002454 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 307212994 1250 307211744 307211789
    0x70c1a19020d1401060e0603040605150a030309030611070b06011d03030d0501080d0519080a140a0504061104050303070b1e010b2805030a0c030e01050c1206090c09010f030b0a 77
    0x142c1c0103080c1032610072007046e400c6001c282c440c080078100814035511031020403070801d02c40f1540110490090100c401541c1e481c00c0c010f203450280d1105642c0700346421480c40a0010720002c40d1120358102d90001c030607440c2c4000440b5500301d02407030701001504204c0b070b01b06507070760510090054007005180400e507941441c4805051848a05040040c4203003003128500440c58071241d6004040d0781d08282180380c0c0c500e0151406820b1004100c0703001500342d400c00008100c40c1e070055020354000c800c100201440c80c0d0401400b4811760180341e5042e4011300c02e420000340f5810b06650b006002e5410700c52301815151040d500c00ea400c4c3c001c0b441100c404601000070146440c01c01941d20b00c904190381d5001003443c00a007440c8006468420115110f0301d040001500940005050180b824001c0201c0d01d040780340481e241e04242c250706034507440d0b440801c000e40b40100c1224090020400386501e443d444d5001520380c0071a82e4200b10515859054002c280d07a100e40500d801004101000000181034003107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 307214244 1250 307212994 307213031
    0x90b10030201030513030c032a080a0e18060f0f030111040305120a0f0509010c1502030601020c0105040e0705090a08010603080a030b0d0507031401020d020c0114070c1a19020d 77
    0x1104110700c8588005c0c800719500000d00303d801501410103d00c0009440a1070341158080014501c010095012640400c800d400092200c000e01d43d0795860309007401e81c1048003100c04c0c413205411801014000c1062840c00950070b15030008020400c01070401150302007400e54400d00c1414001000108041050040600c00e804a00354000801031138a65080c0300036048a032140400d60400101092580c3c0a9020b00000c401c3c3e544c001390640415039942c020032002c3e40c001c1700c3c124014020b60060036000d502680903602903e4042000c95515a2015001c844541041d540d01303500081080d000224500c0a1080c0700c055030240000665900344808050240c071142400070b4019100020201e002c10000301d03500d0241c96121070544040c543d07981100c3d0190049000508459100003801e40300440150301a01c682d1882c2000c100450b0340340d000c15a1854000e0f0005400410050065880c043c000f100307003135100b001e0200d0703554a5600b075000381c000c9802204215240d01d51320780c030340007000c940580c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 307215494 1250 307214244 307214251
    0xf0c03030e011407061a120615030706120e030909010603150e01140108060a1d0103151107060207020303070c0605090a0828050c1002060a0e060c040612090b100302010305 75
    0x80c600c2e111aa50b03c110526441043c030040c2210b50380b5050b5600c511040701c4803800301d200050095004541000203640c48000c00da40907002009409405106800d011844c80100c401a032500c90658824100e048050b2440030035506c2076020803c55514659a07111829018202c1983c0014180b019400b850030f0084240d0848103403855144010008601242629a03c504080c81c048181da240c81010402440c550b400150315a180e41d2442c200000000741d440e8101c80c0519289042040e8001220080780d0010303041500c80b5a0030812440881e605030000c0c0f00c1a440642100d1074202d55840b109009800c607000a400104001001d1003030303181a1103008007070050400504541e0725482150b84002048080e8451360b03026000303010050160a2016103406a400b512052251008500003900e840c0101d6074440c0c1c0606e00755150854040000f500c41c801c0ca000841c00d8070385428010141c401b8400ea00704034080702c3d21620402d00066041a003a03003c1d0184000c02c0d1b0000d41140f002506032076004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 307216744 1250 307215494 307215497
    0x515040203040c0e092b14340f0222050106210e0c15120903030609010f05061b0f0d05180303090a030f0305041505190c031710030f0c03030e01 63
    0x1014085003c51040542007915402000c2000c800510304054402501040d840b6070441c00100d840440c03007152070300c80c04505110948074503442c80c140c069000c01200c14000500310095940b00c0344014203051690a072f4100b0745500c00304410799200d04080548600340c218400291405802d00c0142e14000c4d42001c00b900c80c1103081c01000300c20082283d45424101c6564070440d01c0c00d800d071005084c240f04640b080402c1c0c01100c0c81030b240c03e0810650700d61054070203c1c01a1240c400024011040d1462002652802411a4501010b82c611040c0ca0907503d40c11552074003522605a10080081205604034807442c2c40e82901d40142d045000040d00181380918040d800811003205180d4900c00c0c0c14084da0b6205504003041011350030100c0b20781c016900200e61007403154002d1620755412002520f06c1405000b90210200000201150040c850700001000301e55481c1101d268000d44055095006440302a42d0441c29070329214180c2d0b003804400d081c0c645051301c28042c028075500c540054040c460a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 307217994 1250 307216744 307216753
    0x7060e0102150c0d090605040c141203040306020307030b030114061e012f0307031d040605090a1a191809050d03050402013f0e100515040203040c0e09 66
    0x1e10102d0060640001c1880c507881d2800510503011071115848415226000f01041100d442d180c9890100700080b070140803180c0c09541283d00091a1135210015403c0841010710b08251640da81e900c0650000f40450040c10780700c2c54007412544007441912901c0d00c140c1d0303c0c0300c00ca00f01707002031140180c01c1101440e001c05004540d64000c2e45c00102010907051081341180c034418075640b1801d51900e02c0b20010100380000118001810f9000c0c446a2445034255500c0d00c01000342c404010860740d0510a0540180e03190001030000344c101c1c0e02c6403100740d038480c1c43c00c1d5070101c00b040000c12081c81443d0541c0c80354030300354003407081d5800c0c401160301d107a417400030400c00c0140d0364032050359692150b075000c8101522a8009021a440f40100c0d0107180f11a050f980b0718100002e0107844402800001481c0c503070004150010302c401c050207002c801d90541c030040d00c0c21082d1150804040c0200911080b038070001c07070380c5880203034540e840118411402030000340c2202c3e00b81110b00400310005000101c240d4070 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 307219244 1250 307217994 307218013
    0xc060203070e18220501060305121b0102071a15060409021803010c05030402150906040902070302010c090311120703050a11150403081911010e0c0f120d0e060c0304060207060e0102 79
    0xb4015034403075401503019100b007002c001817520700e02501a03508010b1080c050071403160700b4180400040d003d202140c0090035421581c1005c0b2714203e010303c070301c00303040366440bd00b80d14864413003400b10b1034202c10700c0c2110798111026400841c855610961100156030360002c0c8e6502c4c08040e0030404590060110006e0040d110041c0004102d8000600040e120703186200ba4071010b408513030f003196220708001e06502e8a40e95903032001802500646c00550240d400c12015200c0240314140c8d400135290b10110b106046003004060113010340c0c804c015030303045101c0d0a9000c0041102008503109161150452240c0d0703000b01c109111105400d80813107045600300b03210a00000b80502c0c140c80039845203803910f0380c1043c40c45401b2a002ca01200c1100700652034080428140c0ba00420f1700c20388040140d50b003025107080101400042c64403044180b24541050003200701e9244540ea019510000080001d42000c084405090440e8000e511000250f4800c46040200e540c0002c0380144048090014290115 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 307220494 1250 307219244 307219261
    0x30309140904080708090a09050c0304020114090a0315020c010203040c08070f1805060f1309052e0b0307030b100f0b0f0304020f1c050f010515030307120c060203070e18 74
    0x42e81c000141045c0c004103100e0507580f9100c010750f004180c00e501c140114200a5100010740e130040d50240d001810200140c05401070103c11140450405000145458607540b5032084c01c2c03c030f10460b0781185030204000500f06a003400a1400307603016240ba611800d03d0010759034902482e070f034001d0080301b00c4420100005038005818074505071995074040360645d203c3d00050300140740c2c080d02c542e0050881da070718140501d1640c0582940da1190040300e10305652900c003880240c18080007444d40000b50b200141026041d904400c003014805070480e510240c607643d0309080001c0445006c164003044d603c081014603451000320004001d0003603450300d41119000c43c8012844020030203806803c0c941400c0d5101d440e142c0506400038a40005000710003031074a043d907110709402e200d82c2607030340c240004900183c440f4050340310307000b500600452429130540d403501c04141c4010164010320401d14008030208116000444c0b1a202560340d04c03200d1b040c520208640d8010705106001c0310740f4a00f00b04078400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 307221744 1250 307220494 307220497
    0x807050d0b090703080c010e10052701060812070605060a03150507120e010b09010e01060c230304031104050a050c030c0906071401060503060a0e030406050c1603030914090408 77
    0x54001c0a41c44195540c410050718004441d40020401c000c0000d00140201c1d040d40400a0170341341800385c401c1440714030f864000361141519800d94080d03400c4450103051b0030700d040310041c03e0124400402c10030b80e5200ba00b030a180d012341929205100005402d020000c00b4403906900030801c851140303000741980c4407035607030008100107a89a21760301c0d40800c80a03070244680c90b00d06c4140003814800c200744070018034082c000b00d0507010f0103400c0b03c20021a203044042140c905881d49a5914180403089450781404c10b184003c18100942d400c5122110390707003052000340007071030141c4010600024820140011207400070010401c1c1ca02c1c1800b840001c000b0002200d80100c1c003130880e9910ba840100c00038105129015006000408894500011140641004003110011415070b005907460104540030b8178458034070f40106030801c00080c0803542c02100904515003000c01110f04801c1d00a2825030304c206a5001640402c19408040242d0f03c00300303155110b02c00082e5003144c8241007a64038000e45 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 307222994 1250 307221744 307221769
    0x17031005040209060c060117070906080322030b0903030f010902031b0c0c09090c09060306250c0212100b030c0105030609061807120b0108041112030c070603020d06080705 75
    0x2071600069040d28a0703030f584060300c810443d4001541c0c05943d540f0310710031401c0e91840714852103010744240020040c00610466040351007681c084c3d841d2a00040e05050740c482c000010000c00c240010f0048081102048594070805050008581e00e013800c86c1c205402190591190310071034010010440054032512244c3d00e4194202c0c82c5645465036100c442c0d0800341200348094001c554007040180740b420004114030501416070b0702504584408080c03640302e074822154410560700202407103040d0499000401e2031069070b4600307610380c407003a41c2c00034038001c5403900088482d911419200c00c030501d880c8030f51690418124011318400b028040040c115000c01880180710301b1082d40040e84039101c628840c50841a00802510946010712001d0444d400f039400ca40c0307159240290981080d4000c0b0140c40c01a904403c41c0140101e402d810007020003001e41c00103406000034490400c1e03070441041103001401e02500d0140e00c40a120036040e04035203483c0c4c04141140d001c02410070503525000c000250 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 307224244 1250 307222994 307222999
    0x203060301052202010804330b01020703020a210210110c010207150e190f0f060c020603150d020a09090506060607030f08040f0c030305120f040206340f17031005 71
    0x20140d445003000a140c0d041d04082d000c8504032008050141c41c6001d003c1e0104e4180239070701f0040d2001a6004980c0c407001804006e40200c0340090902803103003040c2c0408552580780f000c2a402945913030108801d0140c2c81090030100f80701078000c09080000b4032003500b50080a100030000d9034a485c900d10f00c61810359005000384160712140042944407840318a640000c13030391300c3c09501c1c1d956400c0d00c100b11040381300c4c2c14041e60511360041047d41c8540319010f04207400074205411521840401070290308413800d00c903400302c2c00020200058031006882d4004012205000502c206242040f03401d14000030001c4e44124020016800080e07084440c010100da01441d00302610b0b0303528070341101070b4415028050b1009040034000020982d2084c01440c9110201403200143d494092a001c03171064199002944407109211f11010990301482041e0030020854806c1d521241c2d04201d583c000c84a80e04c143d80c2500308292170b07018084038840401100d480455120300d1480d040082240030303c0680500791 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 307225494 1250 307224244 307224257
    0x10f05191b0c17030103030c14010b060d0225060506130213091d0601180608030702150f0d020706050103020424030201050904110a0903021c0b01091518020306030105220201 76
    0x2800d10461000304561070300c19007441d03603482d612418040c0238100c025000310744c0c40b1005040d2a2041204ac0a000c140c3e1714050030036410316400500e041d0180d00020600350480b010b0b50206007903256100041040140a14400500d60a0010603c0500050b0124942c1c10900420070012007001c2141c000c012a5800600050644100d06001903610304c1001c8112151144d10f0010840e2400303000305031403034610444100821940c070000307181c41780901c02019501c130312900d031103102c12080c98004209074a05000c64500c2d0501e541e075100e040382c121802c00d850503581c480052086041a1165401c25160402d6110100d11204400f05090550b800000d04101012a4196683d1502c5c1c01a002c1c2c00c0410308210380f10f005000c0010500d1030b542c1f00c141e11804501030440c1005901807003201c03440e500301034040240da0130101c8003806411202020500510750080000e00c0d1241c2c4414488070218540303000da40e904029040500f07481002d01303040c0d41d0ba10070282c03148010540042e0311061a03420f08280c0c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 307226744 1250 307225494 307225517
    0x108060d0c050d060203160f0237030c060c030e070b0a26090c06030106050d0b120f1b0609010903030f03060305011e060902040509070c050f010f05191b 67
    0x1800c40101c41d4406030f00300380803014070010007402c1e4000e94400e801034a050703907060780741820840d0058295030064015030012200303100414202c42c000c84109015400462031480d01281100443ca5680300580006501d143c00808214890164101c00800c5150a00a03401c039400e20588940b0103104419005200084d401107050041680c900f6400c207000025010030912158020300748403c80304122180a40c4c51000303400c1c508041500e0503150259070f16401d000701c418410000741550301c409030b030200c1e0042d01c100d06006c0c10032901c800c2c02c450341c000c0c1c41006510a081150f00300d00c050550300c220000c1c8149107241c0d03030105c4200c04580d0107103000d960705914403005074010078064202501d40c0d424080d01c5861401c261100a410300e0120000701f0107199074000090880c002c03030280710342c400300840104043e50311a5201001a83c010425118411052803d140c04c490700b05115070801074860040281c440c2a0100500700e00e07a131000d061010701645d92607444c242c420322005000340410355042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 307227994 1250 307226744 307226753
    0x8160e10091a031e0709090c0c0b0a0c0210020c0a03030b0d02090703020a11010603050d11032215020109020306180102090307080c0a1a030606072a090c0e0108060d 72
    0x91006011200600350155102c5240b101183d00880d59100d49500c05111030408800e9544107520446455948502d500e041554840117000d60607004030402568003280400318a0b00c08007180158a81000003850301000074001e4280380650648108052061080300030b01280411217000207549840c3c00507044003038000085003161941e102075003141c140c208100501d41c05074020301d29000749454030401046641007040c01d0312040e020040c41c0b501b02c4101e28035101d020f451100c1250700b0f24401d40b801c3c404020188007201d107040060300c8484240c2c3d03404000c02c0c0c040750740285c14001c10384028003801c42150080390b40c40b4406004074260380102041034009120079816900801c0f80201034a000d580d03240da12130369441c01d00c1680d0b03210b28142200040c0b8108140d20070700c08814013001c2a815070340c40d2805c0081d10f402540c2c09541000c0100d00044448031686080d0040d0001000b407a04801e04242140e402c8510041080e1b0038000c01031a00d012aa030080c100c2036020400321201e22443d180d5140 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 307229244 1250 307227994 307228007
    0x3020403050f010b0406140a0b03040302010b1003140a0e060708041b030b040b01051c1403090405010e0907090b0303091525140a03120b030a0b09010c08160e10 70
    0x10150242c0070b004060580d464044d040034034000c40c101e90610002c0d0715000a04902c4280360103c80d44051010703410443c030302501c409141e02c64080d00000030502500004165100c415001800010340d584c420074003d409540c080c0c0340c20124102b0f0401c80780c41c4e02c0c3d82440d07580e00060030b044c040c003078424002001c100041c00a5100640d407000540781c100e60f0380c038003084d40300403d5408980003891180042030380e05242030100045004580740346035040460320f40390705600c081c04a20186000403c1452601c1d102c502900f402016401007661051600e161518140042604100a0f1a090140c0200319a0b000000c1d00c0d5034810455401d00701a2112800a000b48030704100804440300c504524409070900da8036200c0f000b03024140d02d007080070404030b000707888107603428005000c20b03824803a80a040c0c00d250710400c1b103001b001d4101ca40780d03c4107407501800018115600441a07440e00b0200351043d43c0003e00503004448000a02844c2900502c0500300e500321106d06c44c0101c42c040d049020710f921800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 307230494 1250 307229244 307229249
    0xc140a0308041d0c070c1814070e1003090c050f01030e070b0a1e0206070305181507030c140a0503190f020409110715110c06090d1103121501030204 65
    0x81c400340d45982e0765030700244503100340344120781d0840c3c00c1001400644013441200d0901e030340303c4a1564010f0a0400b603038103507082001c0c181200c982c1d54130740d03068440082d82924007424031500d4070300d2101a413004121900188003811000c0505007581d95000502c40c165400c00d48908440302074100c10f003440120010042011895140d11850200040d244040703001004095402d039a0341184c04444400002040083e0490b0801a0710000020301201d200398081038200c00303030003800a00240000c0c1b00c1450719046100070100803c6001c180440740d1b03018880e1400100b090300348290203030f1b0340c1441899140903903904141030110003c002503c4001030340c102c5a4151a0010400040e41024201070094125008880b2a941b42c003064102d495031081c01d40c0c0040c0c0d4482005440c403248840020b004d02800442e4990703001c02441103080e034410900c000c07842040e4060040c400007603101750040241107079680701070154004010440c042d0042c034808a5101d01c10800d9000000c0034600128020300c6070340d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 307231744 1250 307230494 307230503
    0x210c02040203010f05120d120506040609020d0c090503010c05031302010507051c120e061f0b1b0d05040302030d0305100f061107060306060507060e1504050f12070c140a03 75
    0x104074922408060b4098172010355207a40780c10061000c090f658480511141e010030356103007600742c622403103030807403036000300b000c0c101142d020f64541140c0144d8201c11101c2d003141d625500c400c0256588405010020075045000344040c0c109034202030058030000c1c21a14081020030705450540e4001c20803204c440c0c2d441130858003810303a1403200144030840403407484001001c1c0980b001181d00c8501910790380c10300312070180c80151140003904941c0e80f891444000325662032000052000802405050f9603c2400c03940420b0340c2c650002c076418941c54010310b50070b012084c0010b0015840004076144114514100092151030b640201e03407000509905c404102e02030102c000c101198800c60b54512100c504046841e0240c6540b426015100217006180001c1e00900010011601980000100f0256501940d40c00291b609101c48442401c58003511142d00842c402c0c0e81c040e000b0003c80740e075400038030f810307600300000d80d9110071101e841032042000030205074212004655820901400442c6d00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 307232994 1250 307231744 307231747
    0x70c06091503050601091e0306020307030e0f0109080a0c08040e0112060b013e0a03020a1205070209060405040213050a0e010e07050a09110c07030609110607210c020402 74
    0x941400800000c894000e1554038107000307008211aa0080c011036002d00d84c1616a9080300c1d0070702d100515102000450701004502286001010400c81e01c000d60040600d55008509005207031901850b00c80504103040983e85040000d50129080309d0940345126140d24001ca410356150800108602a0b60002690814a2000042c1c09843c1412054060b88510f000303001030705c0c410f001920512000107582c209000b03648141804110712002d107281212000f03504c1c6207540e00300141c5070b18100607840100c015034081d0013100301740f01d10600c00d003040c0242ea240451801c03c4585c04241900e1028200f507002d542c139030f8042011503551014a42d80981c40380410030161038420300120161079012000941175280115066000e2130124108080e20000342c1104003180c54580c1200c010200d110411382c15420078407a10074218414021900154090880490f0149141c280a4400300240c1d20340341c0b14101c100076140008100c2038003403205860100810702d481d10040e8099688201100c0d00070740c010710 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 307234244 1250 307232994 307232999
    0x207031b050f09090a06020c0a0f1203110a02070510111914030f0324130603050c01031b0305091002070503121509130f150b100e0f040908070c 63
    0x40032a40c6a00315802200c040441c0030740e04040c084100000e54a20140c0e0300041000001b0425030340082484c06800c0d000c803054031189403075502c000c5080341d2049403c203900f01c0040b158541c3c0340c011060b40442d0700040038540310030000060743d58450761150364000c100181003000c409005160319541d60b61302100b500c818549140c2e00c0c003214501100200d842c113007103104090301d960002094a48007414001c040e4510384840c030b10090041c0300880d12640040e01d180d0f5024554854840300100150386036808550341d400c51034081e0400c0c0074003800c1410140b500c05400708181500ca4030108803461030500150544034640b07041e04051042225620050002513480208940080144030590b0409403800c0c0c40d0b01c40d0385100942c0107010030a1640104002c001c01d01404070700c112414102d2107045500c100e04d14907076030f10f40c10a00e81c0419040c480d40c2c0301c4500444d81071000c20300040240d1480d00910b46101c22000840c0341c42840402ca00580d50b85840c0c0080001d0041103a074000e8208044109803039 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 307235494 1250 307234244 307234283
    0xe04050102042706060203040f030f02150703080406060504110406110f0318040e0106120210020a0b180f0c060a050d0f02070605060102101404110103021308010b0316080706050307020703 82
    0x7180b03191603003d21850084002446807010048e035061329241080000f40501d99214250300c0310000e4410303a88004040d450079200e0550000a01d03907240709407200c44844c60a402d01c4401c542081d072105001d81d0801c0b0350103104141c2e4408441c20380d00a410011206500106041d02c2c017120740803400114840000c103d000000c7c54400b8a6008004580900c5202c2c030381d5035040c1c2600d40b2413040c03040099901ca48003005191102a00e103040c0c000c1e1044810b02c400540325000f80d80010781d4145803148035040c84c1c1003001801e100d15018880607000030180d251120020560520075514507601b00440840c050f03440e00a00d4000c0101514454019034403811075081c4038006250a90b6054054800c8040844912100d130140d4441c0300076000c403001d610354036925200c0c0c1c0c5a41c21510300d0304044c0e0030041e41c180f200c8900d03010790142524100010703a10351041d041c58500346840810800103104400e08001034240003880703004ac0c500510b0030a417213032910343d01a4505003242d00010a0701c240313110b5100021 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 307236744 1250 307235494 307235549
    0x100e01060f03020304050a2a1d0402060703170c07060b120c010818030c2d0709051519030201021e0712050c1206100603091e0309050a03140f07050a0e0405010204 71
    0x1005804508e8151a40d60001070070442d09101c0e206082c0107016002601606d0711a0203004440d01904085008543d84d940d41c4200c548111000707a404440400d54005000703c1d4407900c01810401d40701c0680c6180a001c440b907a8040e410101810000400000b1304a407810700d00d00c582c4928244116030302c5030700c000e45040c1c59409400d040310081015105425000c4c000c0007542e4441039402018009280c00e182003c00030345001040800c030006240355140321515045a6032000e041c070106448191801e5100081c201401103003211082908264400c0441c03c020072804111000d52400d100c41800f245001c0c0d0a06c0d41c080c3d00b030b0354411b088005500035100c0c08102e0920440c030403195004c50031b0303c43c0e03000d50444110903800780c0154110900406c41d0200c80e00c03001c50184c02414585500d07a600d10000d8024440c50300308442d0300340c8004885c41822002c11003580b25801e214007801190781080c010480306041d034810042c02490a030041024800700f0741c101e0703015009a08800c20003e902c00d8020119 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 307237994 1250 307236744 307236803
    0x50102031807050d0f0303140103030e030c010801060e04090c0344030114120f031309050f2403030d1b08040c150302040b070b100e01060f03020304050a 67
    0x148401c012440d0318404020403070400f9160014044000b10a464894008907901c0c40b600700c0c01d0503500c07103600465900128449000390300c00d640301c44c000044c010508d4242030a22045a0601c602240180040c6401a0040c00000010f0b82e000407902c00134189498442125840540590020a41a0300055201c03400d914403904504a802011100f1580030059103082820400c01c1041400144a082c07000794001596460091101d2400c0c3d10108103941006840e04210007582d00020705801d20b002200c11078402820b404104000d03600d00711183c5000070900a00c0340d0b1b15014904604c0542480000ca4041c100e0005021246c0f240c03078108240c4001c180780ba029000601a0160315240b0b1071152a00503c0303558055800d00035a8075090307a41e00840e0452803800d06040d028800450101682800382ca04c182c0566001c99150410500c620640c0c035046d08040045200f00c00140220754016090244110807482c005a80b540e9078105a403d001407401e00821180004c010404013a400c0000d2042 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 307239244 1250 307237994 307238011
    0x301030b070503070c0308090f0f39090c0d05010b03060a090c0c030e010e12010203060405060a0303091a1605060402130204050109030212030f0301090501030516030803150a1205010203 81
    0x8030752124802a0354030f0004540000000e030f0a800200e002034072070000c40e80c00c4070145044801070180c1d0006036082104000e000c0c0310540c440740c029011502d001e440391200b156001410340d400b07c4002c6000401d200f00b24180c2d0b020312004804904903d9690080701c0c0c0391145a0b808010a507100c0c01c0003440c6600569115216080300c0700c001c41e440c1c905120742c10307419855856201600b900356900303607000e1070320f1032005052000300003160041751030702072900840007151400141d41e880c202c0c0400048030005486103000d107090075024400203030404805801d8032040c07098a0f645298039660000c4610440102400a441032040c01e403c000000620a0055108480c10200d260440c0303015001c070302461080f5030005844060070030160401c945522200c50152041e81d20713002c23032659401e5165000380e0110000301d6550b0010414001c0502c501403156445040c012412407441c0c55080c4a400042c0164951b20a22440c080581d60755490010080001d01c000410356496400d289000350030031030742201c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 307240494 1250 307239244 307239263
    0x100e031e1002091e01050d0207060902040c020a020d06021c02040e070e060c03090d05030c01052a04260a0c0803120c04050102030f03040f21030c1403070e0105090603010b030103 78
    0x30141c1d64240240c4001e40400b0740b03101d200c3e5221300000d80262031020402c50500c0340030880c0c003018400a000601110780107580c049000e00c3c0d98410b100403101c5482c10b000c119017241c150880166603000d000e001040d001040540c940b88070f0390441c0c10600080c1d0f00c10f41041e100150028040f1544a07106101c0d90f040e80391420f007684004140a4540304e85070044040390001c01001c1e1462408908941105014808890902800e01011802c4610079505c54401e2a8858800030000c400e84101c1c05c0380408d801c0c09941407921300a412542010404000c8160b416581b2051001c40e40400080e0071282e00900c0000e501c80c1c0d1500055200d030f00c1000140203002c070510004282c50441400c581c1144c1040e0700840c507001c40121244c1043d040540100e426095006d00c1c040403c51003550041c00041120390703400d45946401028040702c1042c5516400e2104040c1c4200d0070035522030649074000310382c0c00d1420180c001c0a00494052203041e8040b548290084008642d400d50003003e50f068070303c26000304 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 307241744 1250 307240494 307240513
    0x4060c061a0127031401020309061819080d05190b01050924070c0602060f2a1c06140109050607050a1b0b0d05060a05040b030606100e031e 61
    0x145009850034000da0302080c0310500e10200d007100d00781e038000c0815000c0c505402080e1681c5da00740c0d06010900540f50140c0d008803c0c058408024030546421455060301ca00c628660a10180d4540f8805080d0750f10f48401d00003d00c041c8440d1004840d00f40d2501039040010303140000e8183e0500c08403000100c11686020340d50612940200d0480e11900030090000448031070195650680b00d0700d94440d05140c48050100000044000c910900509029009040203280005500d64910070007003640f04000314000d08000c0701120188081c65800c01c2c44441641e54400d80c0441c0c22501c1d40102e000f8110b0310b840000110449090f0390541ca0300c2e000d0340c414241e07030380c0d0303c040041382c0c0074403440174141d07030444402c00300080e2401640c680c011049505900c80c4980e40c0e098051150011100c9440c150388039002c010302840e1050400014060403641044143c100c10080390b0307105001003d01c1e00401901071943c4400b4054102d40d9261000201240c4034000102c0144150842da06140e070021720036024034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 307242994 1250 307241744 307241771
    0xc06020d02030f0f090a030510020c060609010b09090a0b0d06090c05010513150210110d05010503011a01050306030102070507121202030f0a05160b0709031a01050105070b1b04060c06 80
    0x854021410f085201030414020a889040c1e036070044106660140c4502000030001e0004e00c114071202c04900c00c016199518541a6401c015000300700030701c41d003580c0700180240d4044206660503d901525020050741c2d4140480c001040442080f6502c00704a0507281c3c208110340d00b01c141114810b03a8423110350b65070f8500542e0315005192071001c2c1c44c22411780034401f05140c0000300c44400308910440d403108025044000c225030b514086150b4100c00001c81d03008880307840c040c160040c0b00a400800106104400042102c880107103250304000d03000002c2242a5003d4050f07070800340e0000300b5502c1c0150b40d04018801c200700c00a00b140c8003042c50060004940c00071094a414040030001c0a24004180004a64a600035001c121052110203181c0010800d0f80303065a1099074103446800c0340b60306508095002c004040a400340c1c02506400504c9241d901074250f40300c95611603140240b54132090306104010103d1484044000408030f0001529540640d1543c4840d004140130804160388400 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 307244244 1250 307242994 307242997
    0xc090c08010509070c020402120627071409090f06100503040b06130f050c040f05030a0c03020103090521091305132003160504050c210406180c06020d0203 68
    0x1100440d200900402141c02c140c0041c82c1c2c00216403825941c1c5c1e951031750000d000c9800116002d100355a00e542041050f06219161520800b04030500b104010b840d585400780c00d110042c03221003044081d60303010b030341042e002c8159104110300414a010520346a0100380814a0480d54a40b051503070f24000440103018000301d81c000c0e50833211803034103580d450017400540b50340c908030740e002c00d40d90310381c0203102c15003c1c03040074011a01d046285a88501d4941c011000384a0f03030700024441d0f042140001c0000c0c0700620000704495083c00d020504a41c241040c904018a6010307841c0404a8801d016069006c40d000803c00d400084509421503034045c2e0060341101d8044400740301c0c0490450a41700412071550045111030300a198014400421601013410510105044010041040d20522403843c1c10b000305607004000c0a5018100f1201500c000c20105400b040ca18852182038040b809100c05a001015502c02d400460100100e00e480c0c4a00038034000e1086074014020412600612403000c030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 307245494 1250 307244244 307244261
    0x5060108040b040f0f080a08181518010603050709060e0f010810050a0f0c05130b0a090303050a020304030c0b090a0b0324040605030f0303070306050d2d021c0c09 71
    0xe4050903907495413411401c81c04403400b0359480660103500b8002400e882e008011904140c1d4402d001d070306103003801140c1d500c102e0000a1013500304942c1c2c00c1000e0798569502c3c4e84422011a4100c80045420440f401080650005460f9009181000c901158250844821036040b903005c1c0c0e44036520310b0180002c1c014280205c03400350f000404582103076007854004c41e4128610356800a880c0160311900700448050240708004134001041d415805120000790130300034011500940c0c504010301d400100806441d0100906101c00482e55004c940e2080054401450740941d1002d511611983c03805299041804c606100e4540001c01003425100d107026a4060a0200440155001448442403034020f903100d50340e4000e0f6a070304000400b07580421002c0f4240010902865507403c5c2890f00506941468006501440c44240c207000090000343c2817103000007050240351681c0c030207110303000c2e6541ca4810019502009060024003c1101c12041082d20f9210b0810200010b03510035911003614000d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 307246744 1250 307245494 307245503
    0x801060e0907050304020a051e1f0906051303060609020306030c01090f060509061215030610030b1306020c0d11012d0c23030615130b09030a14010b040506010804 71
    0x6002c1044039019601842e0040c2c401002c030035055440300042280d115284401c05c54031803580c50406964141840411592040c4c2880317122004540500074100320007a22030340741001300006103a2075124522103168043c6502c1881440803607503400d105000703900140c411a20070b00806144a0b50f640c05950030804482400c886d60010503d0810140c1e0141c11002c40c02c1d4000c00d0070850645503044800340c072840796041203c00855019140305061521100908608900001c00000e00204840d803844540c00507442c030500100030032524100e8041c3c050349866501c0e611400c50352545154000d207460403c0903010f0000c004100003621903120b030b42c400c2010700700307903409048060820686a800a4010308042d041030b00312250300104d208100c0880c1c899201170036001000b80921450035811207038194203c07411140c20711100e10808003c0e039146114901c207140000a03c0342c4613441c140b15040003d50080d142c0c0702185828100240605a40c0000314851494000025030740e40c0551085401103400 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 307247994 1250 307246744 307246759
    0x1a090603090f100c08012c070504080f06180d230c0a030e090a02042105030c030f0702040605040b060912120d05040b0c0c1c0c080f0a09090e0d1404091b0801060e 71
    0x36040c21032403035030280001d230422404000101d0550000c00c802c0214040301070003003c0c0c03450690901c5080c0300084244000d96040b45c841040d0617036204814810003980030381050903042104c0c100703402c05d10504070f030f005441c040c100d4a0028581c00c031910303000e240015500300a2954070041603a04a100d24012000303640b104000d2528500560b54075603840a103d801283d182011001100e03185400000070650f00410004501d01141003d008500003401300b40c406114032681400001c0d914010f4a0259005c0d18404200301601c000822010800750101402d0668640308010031001619040310292003000100012681c01c0c030b0403208490948088030003400c40340395a5904a10308804031900201007040c441d001402050181c001896480c56200d50f490750b90561080c09084221264419400f213850f00790340c603002000112342c0d5894400207103400800d00030040c40c645101d0090741c2006801c181b4103d42064a45940c0010030032250301501e510341a681e8a0320100e8041207421401ca800006 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 307249244 1250 307247994 307248059
    0x30d0c0503100b1605011401081507080a090c050a0605090306011205030403261602120601060e0409020102010f0e0307051b150a361a090603090f100c0801 68
    0xb140001c0c09130388820801e203d40406440d21102e0a4801445607004055100c01c0104145034080100310f400502c070241c58001c92900710b0002c0c0855800614001c1d41d04c1c0c07a40034510401514601010141a0041520180541f0340c2d00040864010f2800503000b4800c0500110710380c40000d110f200c4031070b4400c0085180c582103a0f02d1014500c9101140140c80e40c40e011f01244030001800a810f4116144590241c01c25040c0100b060340c0115043d402c2c0990060070040c06026030280740d11410b05025100403c0c050100d1004074010300c8011103c000303081c0782c8030f0008c0f8400804001410101d0207002250510000418030804a08444041d00e071700061100a00185088110140c0403450300c9051002421b4032a2005444205919a0340352700441080c0101802c0443c111265000c1c0c401403101c4529130440c0e940e460840e10480c0d5269125080101c0020341610003040a084100c00701010f4403001c1c414000f514002d04480349a80011960100011400d5040507500f25200b00980505186004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 307250494 1250 307249244 307249259
    0xa0f09141b06131a13030812010e060d060e1f05090c03150601030513020d030c03090819020906040b0d061b170406090311010905031e0403080d110417030d0c050310 72
    0x6080203c003007204c000703001c0c43d940b41802c04041c4c0000c50040c1c080f0755940c5406003c1c0340c0784600c16000403685c0c10502090140300e0310740c802c03425a07071a07011200081404900ea1010700e0460b20355403084803c0c0e0f640f0741c0c400420159403c03090084d02a01c04482e8003e9941080545415101c0b109031a80403040c00010038541c420f8004540080000c8040d4130381c50150b40109580b951034035000d40c04901d041030300504044e880444803000302400e4000e001a1000960300c0050106200c2c0f011388541c12844c00b140c2c0f0350f03695a100000303c040060022140d400a8601440600316015071002c0c0d00500b801c41002840c000c2c4118414079035010b405102c280e030341c1c1e40c841004120540058041000300c0b0000010000c092103030a801a020382d00139519103585100f8a0301d014282c604101110106100410008d02d800069030901c440e50701002c81c0c4240c800c6800355881c012070b8403002038104500c40c0c0a054080c088000c008200780e010090010307000600d0252054801552904a0b03000ca4100800120 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 307251744 1250 307250494 307250519
    0x92c0a020d030e040f02040815070206070207030609060e032d0a0e04050a0f0c1206080706050f0a111209090a05060f01030b060c010509011d0a0b0a0f09141b0613 71
    0x3d0002c02c000741c1107840d140810200d800a130490a240d40c07184211010351400001c03010b5001c4800e2004080c14600440300035110015031100800072074440d001c10b0108445d9400100800c61203808894923000d50642407400700d5140a4295040b0780c03054000e48100c030250f800c03564051665140c0e1a92401240c00344001000c0c018100e60307081e5990101281940c8150089042411080d035841c90700c03040b40021203003181c2d01907000c1120f03a8801c10742040107540003010b440305010100c4017951200044402696501c4d1280d40540c0580245680203018100b244007400000805440300f0045503942c2d40c0c42400c4035001da0781c1e181d00c0409031070000c00f0f40d842034111800303a80700549140d0030f007003000082d1802d45900f5141900b850751200c0b15000c074111806400441c90310500006d0502daa15a25903039102c000140401e1112031300c0b200c0c1800c243e885a080041042c2d80101d43c0c0212007407440c5400d445881d130f1612038423000c4407151843c2c424a05001070380c110700e103459003072170b80c540c41c0116010b0f00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 307252994 1250 307251744 307251767
    0x80f1012050109120e040c0305010320011701030303020d11180621010305010606030c0c080d0b0105120403080603060a090302120304021c0606080132060a092c0a020d03 74
    0x1c07507403078140b01c00000b0301d59000300300030800940750540c0d208036800410003a00e1784500302e141014500703001000840c06007040000212170404804618520110040fa440400c8028803001444000000020942c4c59402042c011035118010032402150514040d01c5200d4050052400044815524694544100180350081136041900151440002d29810502099000740e800d40d645405c100007142d058094075049035074a24000707000700d05998450101d8050400402903590f503820b4408556402002251a403205c1c44609601c5498a40b030010803150702114610b02038022540401c0c041380c081d00a0f10400c55245d0007030701d014102803021100982000b4420703a400007500300b0045903d10780f141c101d98007600039078022540b1420b0940c803509450400c0b40f8015000117260345140d595902841ca944200c0d62943e001f440390301d40c00c0019070307641c00a40285101c60314140c60308028151054070916184038111000f031020248010441c4c8800765000080d4001500100000000b4490380b80d5050 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 307254244 1250 307252994 307253003
    0x7020a02040c09050d0f02180c040b03040f0b0901020c1c1409030a0c15170c0906030601020f0624060703090513140f010302120f070b070213090c06080f1012 69
    0x16804d580744006902c0c1c500d1003105952244402c00703610150b0411180a052541c0d4008003c0060b0a0040c2114640d2042e0701c600b421203207006c00480c0c1013000c4904070705081d030340050400000c0d0070030a1205000b940203420554441c07150340031b403558603080030440c440c20801d03948500c070a200307203504400f81d05d030310042015915014010500340007038095510303030b0b0240c142c820001c03c040d941d860020b081c000f0404034600070661801c00304400c00d41d040003210128001941c3d400c0d02c0e5110000141e241885c894240701d502c2c02050104500c201000012a82d08a110640a510207880b4010301c40300788203a100180004050400c180b1041c01c05a0300d24030710380000c0c1000541d002c40e15010300d0b015a01520004c0c03030044110010410b51528500c41c403c3d000391200504141e5141655040d42c2d004244941001704002240100c10340d42e480260359109881e00c0420300038000310340340100000172140a00340101e8603010204800d0001c0e900303018441c0007410b00c04800141801182e01d0111241c400456 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 307255494 1250 307254244 307254257
    0x11030f071a0405031e04030f030f030b0a0b09010306090e03250b090607030b191802040b030f0406050702060f06010c080403081204030908121c0b1002032107020a02040c 74
    0x41c4981007030030588110302490203191034901114114000c0041201c9140103a01c0a12007440400c8030002d0814441d030345030500e07503003101e030140c025800380008042c41640305000d0000001d100004c60010210041c0c26a000c00513240c070341075440f040710f0300c030500c0040c0c6505c01d0002060b078640c01d41c0d1490a00b03010040b480c0c20030606607224131800400f26181d28458110341f081c401015018000d0400034001260008030541120315807002541a42c4141c0529209801e501c503180b903042c2e4111006001c502d0202c540d03034603003140c00000100c4151401c4800d030f4644800201c00910204400740100c030540800744c003549400004441c8026011410303152039500704000000501c4481c002d0254011415440d06285080d04016121019aa0083e5043c1d0440140308040f8a081811240d81d1180c2e42c0340c4042c40141d07000403d0041c0b194850064126000f242030300c2c03485d40c000010f403200440420440c494601c242d051900d440c84141d500a0159000c0d0296100511709908481c0ca100c00c07528016 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 307256744 1250 307255494 307255523
    0x70e0c0a050708130905010b030f04060c0504080a0819110a1712010602060402011206080c060c1501261b0907031401150809012d020405030a0b1611030f07 68
    0x100c15135100740107402041ca0703880820403562600b801200c1c0100b01207003101d8154600000440221000180010b0009940d61620080c250017401a1406003c100c4100d640160b601d00d0051100d510144150046101071070540541500c10103131341c030344850281c01419041c00181e41d581428080d800c02e101050030240300c0400c441101e841e49030300810b8a035001741490b0905000150000320141d0344003a4090800d031007032003c84d0001500064111081e40c1da180d680d294415010305150160103200001c020010001403a0b90078501d481f803904801100c4c204500c4404403d0700c1d99130700451201332703100c0d9600103800c104c0c0c58104000740d4000c0490801140680d01e201c4440006d070b000740c114401c40755840c1580c40c0c210b54041c144a40c4000900020070602c00c0414902000441100c50001d22000030740080c5200022501a81d00a00d03000c0d00301c03a42c0c0300040c038060350200340448030b484550702100c2c50040104c1c1708107041ca10001449010710301d0041135981d1050700354009101600c5100080841 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 307257994 1250 307256744 307256753
    0xf161a13124e090512120a02010209120c1e041404080406030b010923120d080105040b0618090c04030f060f05061e220218010201060503070e0c0a0507 66
    0x50702c00309141a040041c001c0c45a244204107449040078081056005052a19280790400482000d842c4201da0114a26840b81c80042c40d19182c8031151102c01030100303001000c10b4054000d4484214122400d11901d40c400e1a442e40d5420100c040320351007012a0000d03108000c49014040d000311010340b010070a070303201040c10f80c81601c054500301d03200c0070005000c100c103d1b410b21561800001c2441c1501d0f14919004c0703510898072845504600002080702129801e83c0e401320b105000240d981c050f03a18080d54058080c0024109125450003a410708201d402e41d4a815070442d122a004038600010081c841001d11098100c002c1c1072000c0030f441004044042091141840c211520070b100200701c40d25106990002d550000c0c220b64000e8180040102946a800c0b07a5000c80942c02c1e035002498640200c6410080c6a0043c1c11604580c03001903c20b034261110b1009581e0003030282c000b8041c180c1e9980615998200c0d81c40f511710215082d001140701c1c03009440c0100804181ea241107814030604d40c86 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 307259244 1250 307257994 307258043
    0x1203090e06010c290a0b0a0b0d150303030b1507051e0115080109060b10020a08070201051e0c1606020304061809060e01090507050702010507140f161a1312 68
    0x642511101001310b1402001c441c01c180a034048448a4240921104030b00402d0f81000c0d540143c1802c80400f01d9410b030700d02c1d0b42e0351064140008400c0c0d102c42e460340d13030308014008040342d0040a01683c0d440e4440304403010254111800305a1043c02095480120140c001108402130841e403402d5481d894001120104424840042d1025000000c0c08002c039191410445100d403c20a004041140d0119207654000c00c40840d456002403226940300410301c0102d816101e6000e251031010008418003040c40c103100c02400c850f0b031500c03045503602141055992103c0500d4071482005900400050211503c2003c0a180d4140c15660a80c00341c6d8490841009030b500e6a0090001801840010000c420b09400f07915040821810700328a401c07030b01d4000078045e108041d00588608030801344100c41032000c102601364208000b061780c407003092aa44ca0344d035245680c03007543d296100080844904005c07180c05c980e080d5101841514201d481d1800e0007200d9450b84506668820000392416406080c008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 307260494 1250 307259244 307259273
    0x30c090a020c1e0601031203090b0c040303020f06060907050706090611090316060504060c020f0d080316030506060301061110111b0a03090902090307030615030c1203090e06010c 78
    0x40056241d1044030219071070244003d010101c070801c041c01c040c8011a010903c54192500500b00420410701c0c2001500540040700300100104030800401100c030851300043c0c000d0360300c6a400d80c0d282c400041102c41e0b48078003d98030107521440c0c81010503e06070091000308001485071902050107582500c801040350400c030440080000c002501c002549400d00108201c0303c41c0c900650947d03410040b009146000398000d01042c4020040c02030159a80c0480c1d00400c0c140c002e142401c0d000181c901081d443c1c0054038109803c078488018405918000e0050343d200f000040c20030340c00d40c1e00e401022a03100b1040340708100c0b940110080210341c481c180c0039180301c0f41c0c05039641c140d0b03880b244408031a068020684c0c6858503040442c0c00000258024010300851f00a0035015071101d800100080c140501a80014405032409408c580102c0320b8940c5003040fa80070301076842984d6a218040c3c100c00d5038a580050003d40076079002e0110348449440c080d0004010315240b90014655034030229071000d600d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 307261744 1250 307260494 307260511
    0x10e0102040e060a08030c07050409021f090311040b0637110d05040b1b0c060d15050a0e07111903030e0d030c050d0218281a090d02030c09 61
    0x40d4100f00312810040310780001025a18019460456501021602c5003260300400e4862505c9034001d2041d5503651031080f5140c080581443d414019605000d0040f441600c0100c1d44480c0300d10f80300a031464136208031054507a0181c55140360030040c00b0446c0302440040700c56410007065200c1c00c080a6080a80900c2050060303c1d110350b003044030350246207480c856084800400030100400e120510506040d15649144d04444102c0460f5180d141814040e108041c0b03030700041c02003031030f118400c22074012a81c540040306180801a40300c4081c80503503142401016a649041c034049003d0070320906a00354200d507840c09442c4040202100854003010400702070740000d465034510818864103106001030b62a140c20100044000c203a0060700700e0040c0d008280c0c4450340840c00c1c02114024052210062070003c15441040c421030480c03c20b200d00120201203080c00358800404c400b20781d03000310030890035901e1510703042503103034400c101c40d0400806080380c25009010f0f0b0302a054441ca0706050040c5101c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 307262994 1250 307261744 307261769
    0x210108060f0901060f0e04050a080a2a120c1a01180c02010603030806101101020a18060305040218070c0b2502060f011505071415011409060111010e010204 68
    0x401c1e84151000003030700040c0583d25001d810412007503c030300e01c6412a00210241c0c0030503030700c03418001c0c240030030a200039259010000c1c0c00703221154040a01c500480010200c1d0308041020240d0781c072030380101403008040c81e401a0f04510264024035501ea40944100b25404005490f244a20320104084e44461030304550415144401901d900800030340302c0301132001301300b040d20f16100140f103010090704550103180c94180084c01948900029250360189900a541d602c207401c00c014a051540100ba100f4640071400108009100f400f4650203107400400b002c001c0604025000500c1e60054982c4c020310180b0900307000003507000e0703a1292103072000c0b04000b448100005804181f0707510801817101150001c400b0002403180d25070781d45040d82e6a402c05c50f9818034000b4406d903002e2050000c0030704010001c0c030180c15411340000c1c034a0003201c01e01c0c54501860341e84582003001200072420103503000b099600041d07100c0d4814482301049070440000402c0444071a00e0103802ca80c0250000c0745400c40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 307264244 1250 307262994 307263001
    0x19090507271b080906070c23070f0302210714060903060f040203010513080d0f09020d0606032609310b031902010206010e04081308030306010f0513030821010806 71
    0x4001240c250b025807280080d10071403070700b8400145084006039000345a26860612198500c88211807030234002ca40b0400c44150301e48803882c0d02c3c8512054481203100300c0d20024000710504003055403900c262012001058690704285400c02c00d14140e2403030130b4101d20140140c1c03807903a07010000c16000d0307030402050200c00e04250041c503095a10080c8002e12074410041c441d000100d41030102c0e0301e0200280800a40255035030400030240c880390780e029511100356944002400300c10350041d01224883e0310000800340342100140c0524660700780d40c00c2464024000e41005041c05810304112164040d40040b410f4038401d0990214075580c0300c0d40d104556940d085103181c0c01c041090111520b03854012403180165940002e40e280b005000d0180801070340404102000700c13071402d488222100c803130009841d0351121030045d41c0340c0080f07a80034000740c3e00c5482100c1060040080300c035a030000003c1d400505083da11401e0a560150701c4450820003c3e02d07240054540040041c0e02825080018042c00d04 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 307265494 1250 307264244 307264247
    0x2060705340215090102030708090d0c08031209010b06070f0510150f050406030b060d11030d0e0102010b012f0f01020a0207030308010e090a060b01110604060519090507271b 76
    0xc030003c0d40b0340540f6010030105455a800100340d514460b44415029514407400000c59019211400300802ca041060f5021404000c0440903214910007144803895566a0044007800c4c0c48050392002d410410402ca6800480c0035402c200b040640100b00300d500c44025262110103c0d06201003405001c00740d0481480340000c00e080040080404550a0149a085854642004001400603840b414003a40300404005000f000b102c0c0c3e000008003500d98006421601514421180880741e00552a009161021758020b0111880741c00311480c0460644040c00403c440c441283d0380260164811405213076694002400149a2a59240d001d4029a4910302d400703040100107802000140c103020040008a460007d040400d5a42003400814040010310040c6c0383c1021015407000c4502805040005000007900444e009042c1c03001030b00303400901c05140c84202e40030900001c2c0143c21160f0200900e035400035401d4902e62006030786c0d00c50720745041c0503502254400000394501e41c181900040c510b5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 307266744 1250 307265494 307265509
    0x912060601020d140a030b010212031005090105040c08060f0103140c07050601060903050a03031e0e0607110d020a0b04140607030507080705040302011b030e030a030801080f030a020607053402 84
    0x3129030b81819030401d80c0101d051070150007483c0c0d01000300366890302c80351f02c140c2c0f003081000016906130300426600d0070041840c01c4802140d003d0715010741a2200001031609013803150810454541c0d5030032103a03845238020001c06880c10248281007548502143e005483c0e00d4080358040c0c031030780d00559580e001a26189040960503440a003d00c030400000700089400883c1707440101c0e1707152030001045c2c0c8034804990980500050700001e0940303082c5502d100391070001342c2140101c4d82ea40700c0c500f40380c0c02c2400f669582d0008900c2000160170009000001a0902d40c0e2180c005205500c500c0300c2c91401e4610910b01142203400d00002504e98090004c1a50490f508581006161a00e00e281c54195000a07010903c19044810000c5059103079106061040c208150344000c010305580304040c1030b0400074250002805148950301522650701050200001150380da0301c0c01c0d070080c2c040340d0b403410415240e94000983e46090094003e1226080030f42c6145d50030b100802091091701d000c1014014072294 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 307267994 1250 307266744 307266763
    0x213120c080c13270f0203060a0c1b02060906160309150f30061814070813080a030501030b10061b1109040c05090a1e11091206060102 59
    0x540d04611074000d1151030701c11102419030022080414140c0085003038040c14644410044c0d10741280111143c00c20100300510070400b07000310102d03030b041e449079800441211395100e021804a099180c0241d5540c9507032021682e10307400107003068202145100400c0c1140c0c401b00c4038615210b402c500c00f03010107820655140261254030304a800030004990301520510700c00d42c604c2c05100e500e120480c00900d04d240c162042070810194040c12220b100241000340206004590315861b00b2410b2030400c2c12030303114100c03d0000480c84000642c03034206c816510048050001c00c1c0c0549030a907210003162560001780110401aa0300288642c5182070400c121b000107051003880e0381015030304006950b031100c01c0c0b013200000304038290058a40c81c90700d0440381c40041c00ca150022044405c01c01070007004034800e821614203035a1581680d4440c030701002100c05003c1c00c8031034401c0c00e13000f12404104603031007000c00851140d11540351078462400100c241d910b0921184c000d40c408001c00041c1e50f814401d0000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 307269244 1250 307267994 307268009
    0x6010b0310061d060705010e0a050d0905090610030b0102120301030b0703110c060703150e01170601080f060720010f0902010e030c0306040206030a090c082109060d0b040213120c 78
    0x1958030280584240c107443e494002c5100c3c043c0411440300740070082d4003038602e41d00c45034201c444d0001ca074078095031241c02d05520180421711545002542d030400c4c032000c0348604c07001800494207881d031041c250010510700082d00d0441c810078241d40c10400b91000114042d5000710280ca42c00e14000300014140c4100c4448038119000c140615106488009104c61700104541070104045c034400088510b210400d40c40b14458404c04c000000324000109850342d403022200040d6110703070780c0b42e000195a654400504000c5a80a640065a850b1040c200d42c80b070b01281c4c00480000b0002e000b00b05c0d003542d85181e031007295242d86045031002c5603000201281704803c184c01070464a110500066219580204007a02030100000081c18009903035010103045a1b11034808202207803958900c50303a03211410000440c110700701901d08407010803441561840107004107120700c0c0a044220b10780c0608001500c850708903400f44900c11a89000c00184409070a0402401d0386204207800c2062142903158001030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 307270494 1250 307269244 307269257
    0x302090f06043f030c12050f0406080c071a0702100605060403080f0f0c060114010c0b0613090b0c0a0909020301080a0b180a030e030607080f01140a030506010b031006 73
    0x440311415068040c1c418441000c03c030b20310340449145640e80780c203091900c406900c0080c280801c03d60081c0720044114020782c201d1410b011114030655552283c241a03404200c0c0074001004218400d07400e41e030380034040d0242c03941003042655034511035003103c80107104100d030741f6010000c8540c1d0400170341c42d84408590b000e200c0d6600d4800403c101c0c1c0304602000d0f0100c0e1b0001043c1800d004540210380305000a419002d6461400c8880c06455800a006028400c0c200301c22000c615881402201c2c103131500302c240040b80352145d008000e030070701004154005154440010001043e4489441c40c40303030040d0356903241d4980740560001e101c044281c1201001910600061182c1c0702d000901c1c0140c16400025032000d81c81d031100008052601d9801620036220b01e0307041c1c00030954066542c518902c02a0100c42003910f500500741c680500450362500005241c6004020944600e08084840d4102800e148241c0b901d1ba00c8031403d045098000b0041e4034000400d0103150301c2c0301d503a4a0000d245501c2c004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 307271744 1250 307270494 307270499
    0x40f1203021b01051902090402040308030a051608060f09150a030809010e010216060807050d0c0201020a030c0c050d0f05070819090b16080d110a030c031803020c1002070509070302090f0604 83
    0x800c2c108669250340d010310303940031450800e5500c232a030454002e5600a1045030300e80c07501c81e11120240c40c044a0300340e223540015641c41c03201401410f80e203014901c010610113203801083c041c0424481c00400704110810955401030b0300740c85001541d00070f14090001644e4a0020000140005010080450456011544980140b0a28207400c0140c81311403034a800d01c1d458803030b0b088600f030144d0320050300000e20341001d450b06207405500502c5040c6076502c09000b149078808081c2c0d505c030201203025025810412003c9000d922500e410700d40c0315150f040c4142049a1912600780c40e0f0803030060880030380d802d604602180c41d045400d80e00140403188041c0d260608062402c011391014030713401480c9000124544520300c6207a00440c0240c40181c14a40e282c0c2168000100030348521400080440d2604030707031441d0360060801d070710b03400c030f4040d0024050409110280021400704044402c11800368410200f21940c0300d001c024000c10f801e60f0056203c1601004120050a0b200011481950104401c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 307272994 1250 307271744 307271761
    0xa180b040c021f020a03060503030d0b0f0a380408160803040b0f07020a0e040521090a06180e0108070e0a0b130e071e09111809040f1203021b0105 64
    0x150340f0400601c02503124541c201041e00940141d411495050001252000d140062a8003011140d0000c48038110340120b801c06102e45c1c9207040c09146d0860440500710f00f00a410021380e8901c1502d0580c000d000861250114042500300d50132800070b54200c01e0100e0010760100785a400941620400b0b14541407420307041011510034010a894881c901051000c00e41d910701c41d0358001007176005402c50305890070b440c080e51200700c9181c0c0d01000840d1141d00701c8030340f410313070050741c800f1a0040d0404003114203150f015030711401c5d403d00d1900c500104440c04030303404a141005a00809140001b00384081c10305190449807400203200e500c0c0e07a840c0107031102140e6103c010547d101e070b02c072100010b5007400d08d1600d1428030b90b96401c0350306e1104841e00e03402030784a015940c2c5c104543c00890200700c40c81c20030030f40d84070a2090761040101e4000c811001369032403825000c0e40790860f100c2c0369200100c0e00544e030359003840c020902c1d82701c02103603002c2140107920303454400112003505000d00030011031038a03480 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 307274244 1250 307272994 307273033
    0xf080607050403023c09150901060c020d060f1b02030c0627010509070501020c010201050c0405120f010906050a0b0904030c0b0712051f060525020a180b040c02 70
    0x1001c0d00c12030003000c503884901a0f5158110040d4095154040e0489000411810340d194040000f401038041500187d403c030480c3e540b04000b00b00040941da0780f6440c00c50120344084416206a0703012002ca0600d00024405108090441c41056400b04030325420450403001e903191f0f05c01d10340943d041001a58070340702c0c0102e03280380d00c00280000d5988049580038103000c00040715071410042d41c03814060001c1001300003070070422101d00341c0c00c807242c010302100120b09840c41038803000c0c0d4400c0103000510107441e0918070340d206103480d02d0031140141413081d4007a095508031481541c2c01681d400a0103c004500d014084000c0800d881849242c203003923070024001d1210712406404415843c2c04035503042c2c82240311012882408409121a04218070740318107920784401455a0340e103c3d9100020f5450041003500d00640d13114000100b40b03003030300c5c6803601c903c1190002280e008500350008221094400f481840e1145403400c001740040f85202400200c500510381c071030940d071104c0d1080000615980 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 307275494 1250 307274244 307274249
    0x12030108060105011d0904030c0507090e03191710051c020904030c08040f030c050901060908120903030405130e0105180c0112110a050304050c04050c07122102040f0806070504 77
    0x600460700314891704080000c0e05028100c6603000100805000506500114442030980184190713074086544804000441d098403c4072502c075041800641c0890445080506503c0c82a0818042038903143c010800c002c40d08a1303070801c65034603038041846103061142c141d450b40e81000140c0d880f40318817600025003a0a00400040c100824035a28070b04110220341031724000c0090138240b5084076120301c0c0074548184a4050f25008003e01ea00000c3d005200da014402100d094030b024080c0d5031000180901550f00c071064140d09880100301c001001e0700e840140301070455824400140b410405003055082d9000901203004542100d8100705c9504408550506025801d0070701d4185010b170408100060b10f01091110780c104408a1550812600480210b104500c518141c0e402c6207071071010031003281c00079525021141c078240121070010380204d00f2410607060504007a054009031048034044020041d041e43c07003a680229042040c169081000c07030150030700740090400c901e000c42e80240f5a00491 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 307276744 1250 307275494 307275497
    0x9070303080c090111120c0c0f0108060607030306080303010902090310050709180e0601030f02030d0804050a030807050c1006060f09050f0f01170c0307090b072a051c03021203010806010501 83
    0x700074074280e018240c1207105610903030a03580c881e00300c0101b0000c1c40c2c1140030340d24003034080c04804101b20301d46550100d081ea14140c44e07511450b110301c014011690460601101419603a80021900c110704001440c000e00d0321001c05030b41d51580c0024142010045004031029505280504c039600b07401218000a0b91070040e4060721040c0c00050a00241c8906060180d0f113010340c00020092161580c4103160713042c0290211078009141500444a080c0b0403580503007150400c40148002030b204030100c5030003051603d0500c0c14413001d40c6a250404140d100c400644907501c3c4410070840d500000038030049440381c140b0100051900c4045040d00200d4030301984110034005900405078007030304400803d1082c40c10043c5443c03034020507034810303540140d031314001041101c88000f4001c201c0b001103808161b400350081496800c40501214501025100490f072046d50050100710381e1501c4091200c040e002042011040c1560309000c2d09115881c161006086002c00c01401204c20005403181107400c207 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 307277994 1250 307276744 307276747
    0xf04090b0f0c0f0f0417030313110111011b021b0109050f0d0b0a020904150b0a0315080307030c1407061d01030f0212061302090d0b091009150509070303080c 69
    0x8150100b140c07840348040c1c9a82d40500403c404030503440d800042c1065420720300180c06600c50302000c141d034a010446030708070b400f000c1c032070741000140c941c00d00f00d0140700f010b041030000a000b070f10501d03083da10030001c540b1210361414880d04260754100f00304a40494200019081e01070040b000074940702181c004c140c016003031101483c1d21502d5000c00148a507402500fa4001d40c1843d64031032011354085441c061140d400c2c01c0300189080e145007021401c444078003114031304e09000003805902800401e091380c8611804890005184203092008040140c400c3d0f81c1d50310f1400240c0b400001c180c9104510000a40c0081000c0c440310307420840034104c01c0b0501c6640e40001d221000100d000d00b1503200400c003604d0011640ca5041000c4002043c0942c0c01110098545500310310a0012030041d950f2080d8000e241d0700b070f41400f050b400300d10f283d0080012001c0d208003103080b9000805991110030216905010842c0324034203070400707104298116081901a01c1294139589005054601c040c18400c5070140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 307279244 1250 307277994 307278001
    0x706080405030d0c0206041101030618150509070e04050109050c030705071704120b07020622020103020915130806160807030f090302030327070e0c0d090c050f04090b0f 74
    0x420020f980c603c8840c5142800580d20b0000002d48459041d035040f00e02c0f201d005154901c0750300a0181200391240e5901920407040300c0304162010b4a2000091a80411100f030041084d4407403006803445410b40b612000030000b80002404101e807016480107454924083c28801c0210260301120b4006c02a450802d8403080b5a04010051040d15200392010200c001400184030519050030544540070390140d1740d90380d4420381d080e61074110442e01090807041203420080320402e00c070700700c034040da00602d401414400c0c0d100c0801d40c50071200144018080b8085104400090b0003c0100301400c0e100c03020700090704150542c100c4030b0410640044c02e0000c0351000840e0103101e60300c16054041c030000c00340091034582c00c010f03480e83e009880c0d40b448018100743e5042e41c224803006000303d030900c00000b4071685143c110507541c00c4002510600c9200020001c11007102d0060050280e41801052a0045540740c00c6c10031a4940032001e5560295060001c0f10b008100380c0d41d0603580c40a03154640c940f0707035034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 307280494 1250 307279244 307279253
    0x402031009021c0302061b030f06010f0e0303040909050f070e040f02010c05060415060f0b040b0c070e0412090e0705090f01200115050f03060a02130302060d14070e010207060804 78
    0x100f04a4a0510400d101e60b010070515900090b024003402c0405d038a55104a4402c40064840c40300322803103162259a6004a810b55202d5074111420007028a028410203c00ca4000703030542e03115502c071415180d101d010744c0060000a10034a04440c0b00c0070024540341e8540104080d511030000c2000d415002c16070300880540e405403c2c22514180c4c018190b86146ca040e141c80300344a00580442c000041c07800c40c1c04903150280c0c25103041070303501645000e0304261614068030b44550004c0a80b1001d40100c0c040080e00f021f060034014050b0307210f4610080120110076004019014543c0300070f0210400b182030040c2907800c50100d07020068240d900000131a403100050ba184003241d642c50300d82400303946240c8943c5c0819030080302041540c202240740c6980d11030401601c084480442e95040d04082d0106624114541c02004020b0849407000b9016580e90001a400d4124000522401d0f80b180200d02c030925580305a02e5014a0f80e0507c502e1080504000030743e41c5400c0e01445048c481c58a000c00c080c0f0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 307281744 1250 307280494 307280509
    0x28090b0109020a1d060409050405010b03120703020d03020307080621061603180c0b0310050a3507090c0c0f12020d0918051f0305010221040203100902 66
    0x568004000440650756400741c10001c0d0301c4040080001014070380700d00602519034130118001000101098149802c21100f1402000d0280044410350f580b8a226092900c00303120720621003204046043c0c940e1450306001c0e041512414004d402c040c410810440580c2d00070401903088041901d0070301c02d60300703800d14409414044000c1d6200300d2040c2c40400180c400401040d0a40c3c00059806000100c071201406c010000002e00047c007040c0090000d105001d5600055503108a8140500014a0f910700100301c03052440e40001c1d00010800d181505108001041008421000c0c60003c0050407408443c945903401d41c00340c041c00d40c0d20780d10300700195031040c0041c0c45c103660414103400b0172000c28500171001e00e0040300740c038003d8092041500070703180c0540c1d807007012501c11181c0101c441c0082c0210300010301000f00503050003034810100e58029085481030b00051449440016501c5003400c0c41035000c01c541200d02103500c1001010031005807000300b80042c2c400300740b110100b180c1440d0f10008020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 307282994 1250 307281744 307281761
    0x2001050316020f0709020408010605150a030e0a0b0a060f0501021f0c05041a0d1b02150601050c030a080f0c13050f06070206030a09060c0816080403020304081515060328 74
    0x240c0b2031a00301041617840c40d4000c204541444000708a1550380707500340040704410b0030b038806030b804c42444900c11090203a0070020740c5480460a90381015013550b10a400103205030745501f6242c2c0c2c0c8031001d1000c0c0c0e00f2841d1801c09032100740014041e0b100c80200c8004440c07803102a070312090307407204080c816040c029015074014140c14205c040d01d901e84103242c00020380102d0096440e4608192000f07102c0300010100701e00040c400d9014040342c00341c01c100c074440141c01038242410018204000d007003a010502c041c00b1000c007940e0f942c4606092010706119081000740c007480301900d041240c02041c0c005541d4820482e0300540e00798211502e4240081c0d1640034030b58003e9006070b07001007000940d80240d400040e42502c181d4040000c4e58500742c04441122048a144085d403600031418440c013030003029040d5209d442841207a1506441e00709032030514032401901c100c0011440c050002c0c030407070704512404003503050f00c00c07908510b041108455240010f400e090303000c40b001200d022540803039070002e648 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 307284244 1250 307282994 307283023
    0xc14010c110106090908070803071431081b0d0501090f050601060903080909060f0604060309020f03060c030c0c1615030513031e120612200105031602 66
    0x3880c4018a0041c198035203035003422855518206010801451612800d0704254100a656082c00c1032951801c400743e101400400c1030010700c01507a45c540d91040c005014a40240348024218421013800042c1d00c1010440d200d4140d181081c184401480024603d244450004204000480300c20225101c40000da1001d4415401d21a03440d040c0f02c070764130f4505c00b803e1084c1d00300d0f01660398406c8111b900e000640001410380714208a207400c0c501e00081000c0d0400780080810b24480091000101c95a0156000c04003007a2990030a80c00d615007064040d01d4003c0a8003d04004d2a14881140c03143c4402004100c10381808240071312204c000f000010070441144202c400c5040c0c03500380340c2503c0d03c07620309400002420680020419130091904040e20381c0c2c90b88030b03c00a8885000c506000c0d1810603038100401c0703040c460200400000e805440b0007040d01c91600407003a034580c2809002d01403203018a1140c440c4444014010b66805400c80394460f4919074803c1140310308102c12400c20552001c00390 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 307285494 1250 307284244 307284251
    0x60803090d022701031b03020a050603040303020d14181504020925050d0f1e050c070c03060905010c0203040303020a0b0c0706050702060a15050306010302061312030c0b13120c1401 79
    0x500f0001581c6410b4180c03406448500710b417170740d994005c80c1d2141c000d000c001d401800c40b03e0100f10328180b00002c0c0d03410034864100075040100c4181000701703c1306a0206044014045024081c001d191900c00280000d540409481d01002124129600e1080074100074014002140001c9261048600c0c00c1003020001a4a40c1d080c070960038000c0803604481c103550001490034600703a0340070400f0f200b10080700c01c10780f880b020303000c040703d0410b001020b0080420f450355008202480005001c040043d016501c6414005240d10160074400d0031030b000f1480701415548104418804030780c00144010200d5801b10301443c3c03d548661b03c41e500b500865400a041c14142030501144680125040740300e040e41803001c0100819030980d4000540d4284515501500068014405030424a00401c0d0804004008441040d6249200311810f000900c090300000c0069111504000c0342d0703141c1d144c2010703011032a00c04600c419100d1550a000c203100303072014458514100410442c64516030010303150b4600c000c1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 307286744 1250 307285494 307285549
    0xe090a0510050901081b01021014010f0e041e05010f09050604050625031a030a0c03060f060b030a020d060e0709030303050906090a020d0606050301020f0c010b04060803090d02 77
    0x4102601003a560782031100d5860201181508280c0c01050484419030001c010803146642010001030500070181e0450040c1a09103000c00305900940c0311840404181020540c507100280e1010030003600542c200e150b0a00c107210118800d1880b40c0500f01c070101850340b841c2030300d00d44980105904040d4040403400d0450b40828008080348940c402c501071010340d800c0380e9a800c034204002d030400d002c50307804484a008209100344254850314a04803072080382070346e58140e0700003c1d01d800400c40f41103030340a0341102e05200300045409101080c81d0f01203c14410076050190035003090100501c620310843c0d021800d50a0100c658002d1802404002050103042c180510014070b02911400260301285c10400458000400001c155101c0c1c8044805000c1c00100fa07820420000d2449409071089501c5240103d050343c1c0030720003040c03082d00011b400c41c5d03a080340b05078041c20b640c0b140003402d100e989044000c0044c1b14000c0111803610740e084a0001c82507859100148074114100300303e010380b42000014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 307287994 1250 307286744 307286761
    0x1e031203180f030f020c0306070e030708010501140a06030b010e040209061c0507171314120406020d110d1d06070602041517040c0e18030a02100b0109030b0609070e09 73
    0xc404101d4041d91394500700701070100e0145c1e40c039100721241e02e1701a0302c18000034403510320030500c1ca8000070b030050944106030341d06d100c243d0941d2403e801ca40c02924420480c55210302e800341c0a0b4000707182d04c1c01c1c284503640c04400041d0072608003291041c001e40c3c001036420f0f016a110320460fa004600300518051907104c0b00804002484101d94844c0814020245918100c0440380350714031031140400c911103400501c2c0c0e03407020003c1d841c181c101d50b54468001007840394089040684041d1006900400110050000003000703510326281c0400f05400801c5868811a8070200322030588048114004074114001c0200e0858450520042c003440c0c0b011034041521004610614510706690b81d40143c840c104d03012100c1c9051040d5001419002d040c14200958141401529844407407041400070701d81c1160700d9203007141d200005100058000843c448070110b62841500742105007803130300354413a6066507122402608050409803151145000040e813962180142900350000913069281e1803d11018 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 307289244 1250 307287994 307288013
    0x30403200114070806040b0a0909060b0d20010504060e0906060c0d0c0b010807050604170313030302030a02010f0c020714060408121206060306100302031b0f0703091e03120318 77
    0x20f10100283c804004034405240c41d010710710f100c0500804032003030b82c1d00d0600040000d040002045622540316038040c2d18554946601900460146500c003005610203007072006100b41502c00b20341401801d00c8188035040d4400410030b0444010381b2007030311036221400010420f0050302e042c0c0d0214401c0c48007424040d0740c000900c15a203441200c01f40aa039823140d19141c0c80d00302e076000e401e40044040c40100182e180405070130244900c2c14055070310345445030810292840c41900280c0259000103500028254240320f42400b050603108204641001507074001d407038841500c1050901481c0210004066690408440003007003d00202e803210305444442403000d401017023170750030b40c0d04055002683c207007049411644a814020800d00c1c03001c2e070f403840c00c1e0000c2d080905200d00301d4441003010083c8802142c010700e9120100301e180343d241e400500d0000e0002c410341e00295012988441e503030382101000b4081006a03580985000340b4400c07060350440041c01040354245010030f020311240c06100f010300 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 307290494 1250 307289244 307289251
    0x6110c0105010503010207030206071b080706051906080c190810230402130f0207120216050f0306040b04081909091103060a03060e0c120c0f01080c030403200114 71
    0x80003400160380e1181018201c0c01000c002070096000f4100065080d4454491460013503503240c001c0c0312110481d1580710003500009422140e850392401407020651004146a2841500070401d22084d070500301c0741d82d2140c0c13011203028000d0715075602c00404502003200c44c030044c0c05443d04507103464180c1020080900541b9040304c0340030140c140c0a000c2c106ca0240c01070b1050307802510683d000c02038a18010014010200303400511642800041c0c0000c02e62035418156002f554020041c06c41c001c400200c4400059001314402d480102e058000c43d2004100d49a1064003c0440145943c4509100000c2d100c0c3c2d00410380080d42410407601c85035001f114840c240d8a201e9003c00001d050f081c402c00c081d00c019101e040d071110030904200b0000e100c5411810b6984050020344a03c07032423681c0450601a81d01e000003603a80c0204080440d603040000d1721000c0c81c8824601010542807003045c140c2c0317510001e0b001404005021011500d040400d10582c402050b0200007000101258101c040d40c40401382c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 307291744 1250 307290494 307290517
    0x4020d0e0c010801290a1b030c29011814010626150f03011b09050907020601050108040308040611040321091d0a060e0c03010311010201110a08130611 66
    0x104000b042c800000d04400c0c50580ca012214607070500310440c128006e0308502000c80030001d015800ca41040c0b100552421918404d1b100c244140140740340098a00040310244d2003400402c141c00032541007411a11811514600ca00c50a41c04e040c82a28010341030f81100c1c00031030102035000040c0c42d50b000606441c0c0c8081c15801d06001c1e051000038036480342040c0d80a009031441c410864402d031801a54800d087d1070002c00016210342c034411082c03000c80c0c3d00004080880d5090b41c04020714200310b140301c1c2d80420360b4409482d8940c107100020f00359400140000d010400054001000c10000d0350006419220b20300b10180c541d44d50b03160030f200740142d084840c518005e210012102d140d005818110a88401d5002c0f10403150400207241d200000c02044500300c1d640319080000d8903501a003015009030b1f4170f00b0784150789604500789440ca61911405650440e80b400010b90966070400042e2044060356140503c6143c441003c008214a4050000392119103809001100b000740e06008044144e1704 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 307292994 1250 307291744 307291757
    0x7090b0a0308070308070219020d03050c10060609031109070c03180e040b0402011b0b011208090d050307020108150607020d0201030b040f0b0102070b030c0d020c28112d04020d0e0c01 80
    0x323201034080880301480006d42001d100102e01c2c00003400345001d0980c00032010704551130500b52134019015201e0583c00100131a2200c0005d00600038280348c81c8100490076030701c1190f1414040b40c02803559080c001e015040290003249070030f07050040490980144102408400e903410282400400c0000c290303401ca0100380234410544002e0b03200507062240c990052555010350380b030200c4888441280101c00c031005c1100700005040c0e940c8035001000703074601403801151580002c1c230016201410207401c407158509420a80301e441e40c0c44a003240c0b0425410364850f11044600d100590140c044680303055482400c00e803031a045208941e01410462000342c0c22503d03501ea4503440041103102c00d40c0c00c1246c1c10703000c1102c10400800c2ea0001c15030380d03068a003102c814400d11100c088018080f944a1076603212810b03280c805014829202001c600c104440c8180080e048601032900500e01e21140c1032150700c0c044d40254039a5031035040c1d91802010302d100340220081c0d000800e4403950142140e6010912 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 307294244 1250 307292994 307293013
    0xb1309021210050f30070e07031508030f0d020706020d0f0605061e07030e030f07090b011d13060b0c0102250b04030c051606050a0305061207090b0a03080703080702 72
    0x107003210503030315807613001d00107212070f42e05d12400c00d0304100c4005c0c211459208010140440c40360402401d0001c00d1b0a01c054030103030801d0031000701981c407140c1c080c0d01c034105040020b02410f0380c08001c40700c1ca818101d0f122a91807412041c001d010380921103000d0086440030400d441d68440540109480c1b0110300c1d42001034649410400446024030450f00e09400d9400b104044200111001814114040c1c04c1c41c6400e0b54106000034544000c00c2c0ba17514080d00603500070020b16100b40121103d665003424130743e4000c000d011346214060003500c40c151040c400074840f1403c2d2803182d4401c0c8050041200d00a544407000ea060714040d500c124400b904640207410203100300d106803480d0b0202036601000502154480e520105c4400c18201010f441c9030050511b101c101041410135200203210980b2401e44030212030300e010702200c0f0300400c1d96020b0010b0404031404920045006030031384240c80310014000e281c41e0041707031040107150002424143d0004001050680107200c3c1d61152107181d085801286 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 307295494 1250 307294244 307294249
    0xb0903180303130b0c010207020402030403170702010603020f090a0e070602070f1a1207020304050d030801030b1803030c0c030f36031b1c030305070e0603010308040b130902121005 79
    0x4070340402800c402021020620134000d1060091803081c1d60b1500160400c2002d070009400c90380143e50441c040b03104000360703a812011590156910222074002002880d00c3c0d03801044512a04902444c401d04102c000a091280035038000c1000d40a800211500c007030312820040d40e5124203000c0c0d03080542181900190004011948042c01031240110750b007001c20350030a2503803a0001821040c15400103000c003148585500301c00a00329030007966064290f51550400303010f091030160801c04030301160001c101416000004480d00a001210020303955138200721204e003180100b003c110034a0400140c0c2d504d114045201210403a140c2004415214215030550b840212000210a8140c1c00408420795070b03c00340d412215640701e0107014071140c0e440104e400242c60206003021004a9511b105105c1a190300402c1c0784a0032005035410351465046407510801c900403440340c1c40100d20002a440240c0d00011382d081c1c0200004c510564440c0800c0c0c4030040040012150307a18641c0c680c0a000581d40b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 307296744 1250 307295494 307295497
    0x913060506040306020a050c03070b1503030306010c030509031203010f1d10051509120105071103070c0e150d050606010206160f080a060f0801090b060102010213060f0207030b0903180303 82
    0x318001000d03140380c14916910341c4080e40104a4880601000703000c4007079100810300081910500c241c02c0d5030024039203001122101c9003010400350080c0d105208000d03103640c01c4040c00c1017054241c2009600c40c5007140010789490207941000281c5074010000169207100101e26030241e420803414070144401c490480b1005100c100c5100c4198142d0038010000b50511140e189148820001d6461070825404040b0394503c2c1070040400050b903440c0c080007074080e40706e0b406c5610320039000c001e14980380d80c0380c88070340381348085028122421100307501058000d1800c6003803040c42100502082900d070102e0030b019480e541c0482e00c00d40540039070f0700084c06001c01900c0c0000180c0c8651607183c004851f040c0115034180700103000346402c0e996081c0c0401c616140d105548018a8240700104e440c0103545003c005003880035060074196030040c8522232024880b0002d1000740c595038904071200d00341c1208201c2c90301c3c8035980b0280c0030703914200911030f4030310005c001810f180b640c05000049a4007040305050f40ca = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 307297994 1250 307296744 307296749
    0x31706010215040602030c1323151209010e0607021e0705060708090d2f0604080601030f053a140904090302030705030c1e01020304110405070c0b0c091306 68
    0x142c00322000a00000c1e003d42c0555001080302c040b80d400d1088008030181080e01c0764010440585120121840144c2507024509d0020002e6800310030100c0280c40400c09e274094020303184a8500300c2800295492003d50144082c55200d0040750400d00f401c04000c1c0d11040d441e414240802603001011426010006102c0205c0b5405465103151000c0d41d00c0f80e00d4181c1010094550044000c0141d0002c1000c484500308014845411400803d803503594030007400000741d902038007844051000300004140402d5103411250031000d102c032040201d1920f1130504140c003c9092803080c01e440313510383c886944080d0200489541100b0b00c101c1c200402c055131a2449c00c02c200303242050801480c2120f05007a0410480c0c244039004990410031140d64036403d680000000224503070001c04490500c2d0301a4090940034032443c0002c500d542400c0e26600744d20a01000b40a00a642f1000400e812504c154025181e45420030784103a043c0c02e2442c0002d19681c0201d40d401d102e04000340c02410104034902c1107008 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 307299244 1250 307297994 307298023
    0x60c0515040302060f150307030303020a0f0206041211070b13060305010b0c06150105041a22030503090409020f0409050c0f01030c0813050111031503070b0403030c0212190317060102 80
    0x50300e60714100701c0752105c080200548001402c1c0c00b001c04594504204030006180710381c0b0b000d0703200c445500e802400161034050382400c5501400512001c100c00b141107074410409441c0c441051f0054080e481d1900ca10341e80305801c004e4001652903460300c410781008081c0c5046540500090743d0303850b0b00c990a806074000d40c2240d0340007400840c42d0ba0b2800703e080c0b1b4050b44103040080c04e2583c0d07041c22a0032401101406248480001054001100d454600070304001510007400220340c1140c6900360b6a0083c0100f05000359610422481075542d07080c1d5006081e400100184030300d01003407402d261960100380f5142d0003210804019022980030f03000f112400c6c40182c0d5481250342d2800c500c02d00918a4500c252401e56841d048509003d410750010b5204114581c816140d04010302c041c1403400345241c0c42024400303418041440002e5000c0c0ca00010250111070a00e40d0b5800e98852070700704041500740700303441d02c00d0780300400416410001d4200b90b400c1d4040c104c0c0b61035540c0ea0040e611001524014403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 307300494 1250 307299244 307299253
    0xa050405041104180c11010e0c030601060215160519020a0309091b030216050613050c0102120f07060b04240803090a031502070b010617240609030115060c0515040302 73
    0x1102003000c0e40c0300703100340c0f5110f10b05248006d5500f903c150850306603c503030844540141d10104010b00f8200f080d107005081e10720007000d150408a01d43c0006c2d060240c00d40685030510701d0034020541c4a681503404114505260304041140b0307510207542e81041800c1200442c2e40f450001609412600c40c09510400c8a15480e1048070120000c5000f94480c1e004903155461900005011680410500707201d0910805180400a100d0801a242c40c200c500568115404419888013194070703407050f500600e058030080c980b6000c5a04d804006001420b10154000d071074169454031000c0000c244400c04178144150030900c68603070103007030385910503860340c0307070300071042d00d40420004100c51007121100d940494018101030880d5503021b070460080e030290002480742d180601841c881003003643c0e0802e50354216154400d405901e1280007101c40d581d100c1c401c440208940a01e500c0a4015100d5045521050b09405450b00009800c8400410058901e0b10a501c1c0781700702250602c500c28061a010f80042 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 307301744 1250 307300494 307300529
    0x1060f0c080f0a03060e0103121e121a040c0206160c120c0c0e010b0423031203090a0c0b04260619020c01050f370e0309060a050405041104 61
    0x19180c60b0b003c0640f1034105940c400e40007880220100d9590b020b90706c1042401d000c00e1007503a00410501c551150041e00c281ca4849540d0395a42008440c0248100c0d0000847e01500740052290011080c0c1a2140c001b4242134449003079507800719145100b038408550b0a10703911960310080720011500c0320000c10500b00c21807072580302ca0190510404191051070102c0000d03032590041d40d00b819007039004804030040880c05200300346001401d6001b00340b00c80054640c2040000029968000b1114540c941072000808600300180501604a200c2c1d0006183c411180d039440c0b4041d87c035880340c41004d4001001490341c40b0413664252600c00e503048a640109070366150b1403500d001c144000321740010343c11307800c000005280000307003e101d00c9607804070410030561805016408440262481018110b001c0862810100c0100c0382d0f0400721407810380000881551100d5402d00c0e5101e6a104c01d94040004500b40700c403144e00c5030051080d5a401d0760140700c6800c00401040b114041c0b80902c40503d80c0d1190380 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 307302994 1250 307301744 307301767
    0x180e0408030a0b03100905010b0d110d210206090f060103030f031505150913060f0e0a0e0105040c080d031b03150e01060309051207170a140a050301060f0c08 69
    0x41c40d001000c441c40000c941a074140081c0c0b80c01c1d980902e900b0b03880d0310b43c8501d40920100380302d20038003103030190b8902c5d045030081e559408070741c46228440343c42010014544001d00460130a03054058014502001030100002c0029540301d80132241404036124590b94068911008503159040b01e03071646070350480c6042ca10055010f45420b0f020703040d20501404000401c3c0e5600001000c07424810901c05035104140e005000c1c0d01c07500801d08924003814000108000040103003420101d60710684240c0c500c0d02c2c1c4401050180243c0503401015608100610041c4003a8040c143c04442c54001140c00c80c0303e105200b41e05641220a0b80c050a502425079249664000d8004030308041101d06003800f207584039044201400b4081e0001000290b40c1c46402d4100201040300c3d80e05c0e48140c4071f41c1c3d810002c41d5660f0322184c843e400c04a0050f0131000c20780c10346107401103550410581889032840d440b224400030050594200f48107a0000501c2c0c041c142032460701031064045001e4100840380d2174800764581 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 307304244 1250 307302994 307302997
    0x108010608041707081c200706090203161701060f060c1a01080c01020d05030402130e03070c03060b0f0907141c020408100c020601060801050906040e0a060903180e0408 74
    0x707940f00240400c0300401003001c100208052031040703c02944039400c10110006141c8031382c1a914109190507034150b03024800f8800d0030340c454900d224681e40c0b00e0f02c43c40d00c200a007500e01302c000d400d8814400084080440c1c2420581540c013144034880051010755141d60a03151766211704054541014002d101c460300c284046a601401040f1054903110108043c07180d06000745d00c111020b0700401242d510b01d40e814008070740c2d0002946031440c154205034000075074002c1c01c0d80002c3c0e40140d486052100d40307142401621201030b04500035000032962410300802038015808182d103d4500c0510b142400c3c0f9007403002034083c61507603450046411050410b505141e2050140c5d5944100c0754a00c07040d04c005900042000e48a180c1c060034404100604800030f03202085c0b80700c13003550481c0e0010302c1103961060101d070440d0780454150100e0b441d080d000c81c000b000c22000001e034a0268020310414414160440c14816100b95648110828021243c00d001921401032644500200c400b00300415441b10 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 307305494 1250 307304244 307304251
    0x70302090f0303031006090909030203160303060b03070f0306050907080a0f24151719150e04050d090503191a01080714030604031b030e1207031e020108010608 70
    0x300107040e5000c0300d5002910307603001290004c400f8080e0f601e051061380c2d4009564030080000c000103024040060364069202e0140381b004141c415600a100001e05103e90030440007000b280c02030960740d0420070301c02000214040a0070707010074100b00d40007610303040075102d4a100c1c0d403040c3e5581c01d440d21117004020283c800c45401e01b42685d240c802441008030241120800f200381240c9120120345403580703000980c0181410f034010300c034103a100401b080c0182540c1d01e510020440404d0440c1c07502211010082c0307850302c54804808400c80d004103162400c6c2c0380180c026805074040310300409a40d04111030400d000d009031900342d00180401c0c0e8490b580345451940c000d00c03039244260300700c00f203100c0740480740005d0b40119011b03407020303408020320300c0c507445e050b0342411040e80030b06254541a14050b0080c0000e800c0445110480c285a4041c0342c071580c848206201e00070809890308000e200a00c0e41c070384044c041560962044400340624110650140e100d56074183c6034030b00380d686007070000c0d50030101c000c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 307306744 1250 307305494 307305499
    0x504030c06020d060504050a09030c1203020409020a1d0909030a0e0a080d020303061207080304062a0606050112021c0c09150302030f0603060405070311030f030c030c121207030209 79
    0x18100d5002070140c1c005841c50f05a1668001615480e0104100a07a54058644200d0520f08003603a004294007211480645402200da14144002c3c01c030224028411540b02c166814804900100c1040d8403e078040c003201b038100c0003a50100f0011080018035941a14042003e40c0f00704012045607015240510016200601c2d0141c150b540311102420100070100c2d80c401a00004200806488c100c40300d0080070074244e000f0403801d41011040703a230301d1241d4010030040c031442a9400c8070580307140f5101100021414140d9042ca501d501d03080c406403019020326404a00081071016500c20035100791070610314400043d060805603c10690010000000000d04200340450045840340000d200d006245405640041e035a15000c201c459080f100a40700f14400c0d000300081c0310104400140d020700380da400011460400d42c41c400000d1921038a1106509280004200c03502c10b9070300031001d0242d0b900c00a081e0350b8400e01100300c4c10201d21400c080b200001740d444001c6a09140310341e002d400c41d035501 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 307307994 1250 307306744 307306757
    0x203070206011e0f0b0a080c0f040501080c07020d1b08150105060901111b0307090b0927240603010207050a030804050c0402030112030905010302030910150b03070807021b13050403 79
    0x21004c03201c811010076001012014070005042c50201d038803602c100d90121400030040d080142081d5070300854861072117600e041000400100c0d0f4000030150844408940c002c2045010001d40d2611a164004410038600e08100b035204c0007450100c0800c0e039100c1201c2041032980968246010802070ba005891100e04000980c102150201e03001c002d620814100c02000240040080f01018641100c0d504180c03100c50414107140b8080d2a00340030301d6000412784001c0b061514890207050308080e14000700a58911507507c5449100303540001d036920441c007044018541e0759a1000741401e0b4414900000c08950002403c0004a80b04414003500544a40c080e6981c02840741c0025041c0c0c0c1007030b0400f41c00094045018400c00d6040781c18580105001e003415170841c60081900e036102c2c0b400b138001e00086c50f142e111900760030ba042140326000d00713920700800d40c4078102650020301c1c40d101140d28002510881684071500700042420701040b0780000e11003d0440840d4005002030000a0310840c2400321 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 307309244 1250 307307994 307307999
    0x15040501021902030c0c040c050409050a0b0a06050a03060e010302100807121a0102060907030206180d0203250b1201090c20061006030212040f03120525030203070206011e 75
    0x2d1605452207241581c01951101d144000840c01c200d01c0400440c03083e80780240031aa200c0c0c1000541c0e04580310030078000390390381d155075800300070300050407a035684020301c400040380c51030304000a09504a159901040181d4031500c0089a10400b800302940c03100f42e02c01c0d402d010502c500301e02c80c4e00101e103103081c0780c040c00071005140558034080008210004140961101e65a04009865000c00004010080c00f0f03e1900454054071900e001c01021200c039076080500c40d00d906400f4100c140d4003038101c40c000381405014852403000c404d00300b0782040c284280011680600340941f09220024181c00714542d1a00d40754100801102040304280302840101c096603110b601c00701444000786401408107441c10202109129010b500481c00f031520622500c0180540c8004007580503074480c0c19960099621b04055508100d20500c0190f464100070800c000c021581000d040c40c2144500080702454100801380d041c0c1c081165201c00690021004100d0303450001e600d001800d0b60003410300c4c003254 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 307310494 1250 307309244 307309267
    0x308070f15060b0306151215030114100f05030601030312200a0201050703050709121103070e0108030d1b0509150d0f050114041e0f060e07080403080a05091504050102 73
    0x10250f5000e50703980c0c1d4000c810460306042403d0070781c480385c04c1d21440c246010130031100c0700c4081002038004030008141c40d420395040c4c0c900754880c0c11200b8420501c2e084501d440e01070005a88958054150540c0b116800050242000622241643c1d49603eaa000315500807040c2c000030583c011041000460000310f440c91480801c00811420a0075070020901d85000c15001d4143e0744040c01d40010001d688508009003c1c0005200680d107a01041c0071924603400000a454040c01d030f00a0b8000100d50300000901d104000020040c096000000b4008031003c0711500d41944030f02d1081c0004281d08000305074031881d084c0c2c00c0c0d64070038910854035400c0014102c00f407400c551000b402080740d41c0da150014080b42840b061481d0040030f0444082c00185024150700140038001d003030140850781c0701e00042c070074421160442c0e0042d1890038818101c0d40307061440100070200986040d8082910300000c1401c0300ba060083c603202d078403074600807c034180310355100940200e8000c0084c1ca19550902c8201d1020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 307311744 1250 307310494 307310501
    0xd0b03100f0f0509061302040906020f13030506010501080f0622020c0703050105010509100326130302010e01140a1d090901060e0106020a050c1216062006010308070f15 74
    0x4081c04100203400d00490382c6280488502a1001059a01407402c000c0a10325024100150a5040d107000c01d440e140d91401401070300440d40b02a00000b404543d100c11104182c088400316800703503081b10a2070347c4e03500040d1501c500940e242801401c17440005102030611510762001a003070005620801551401c141040b83c22903180151941c114100070000c0c02824016980504411643c9048604090208100c5410644130042014402e080c940601d003440884021090001601040c4c0d50341c0780a45030f000b43c013a40d0000b02d010a000d4042d41109510400340200c040000c3c1c0b001510300301c03050405a80d03020404c107034407000300e1001000390540d442c2d500358903000f8032800001080303a60034070308580501030050308400110342c0000e105030003062001807801c030386030703010380b100c4105440c050982410260350300c40e10591550540340c00a1280d600c80e8011101c01800f0031410300c4103039040c05080c1c50b002c003848085c000c079200380300d13403000720303001010b84c62070140700d40e1b111502da103a0040c40d801036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 307312994 1250 307311744 307311761
    0xe01031e0614011403070503060a0e070b040b0d05220611070204021207020114040b01060e0f09091f0b01092112030e1204060f110106091d0c030102070201050d0b0310 73
    0x381c00c0b000004002c00703c41110709400e42102200507151050800002c01d030341c0d5100a0054a20700e40300c00c81c0580d440700030300c498000340c0f0005451950321030b241da4991003583c1c00b40800b06040f515080010311852900f00601d40700003a08140d03004401781c83e4558001030108207148440c40c00341000903000694440c8014241d602000040c0b001d01d1034861000f81c2195150188100781c2a00a0200310000b245020400d0546210741885092030540a0101c3c440aa92200da0358000342107806100591400251020620540c1161a6010b6aa0401e42d5058580d80c811a0340490580c0105002010030610381169040c0c0ca9010a40d80203226260a0001c5c17209010b050046503603000810300c2d401003401008100d25021040d40d180c2803038204010040d07002c241c601000c020420b4054000c0d145c0a4001200510402005005602100345c41c0551341007480d080c007245114442c950911400d06000b030f42d0546405845450415801d200400d014281d15004107a2501a030661054030b0011031080d41203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 307314244 1250 307312994 307313021
    0x3180306150f0f0e0c0d0f0506150c0a0b0c0c01020f030405070b030f270706020d09050a0f060507050c040c030609050f06060306010315030c060f08100e01031e06 71
    0x1200044640c1c00c400655480c1c00240711114800c00502860000d81001c4044070111568840d141d920301d01500d00c980100c0082040c500d042442044018043e6044980103141c220340c1e0700701101c80701d46007294038030502405030055000910000e000c10f401c440f40e83e6102c020343c12030500d0921003081c910f00b240e014401c280d111203008014842886070412095010304804400c403850b602304600c89420010700102000304c1400004800c40d4810444800c00c0c1e0788001d201c048030350068030340c0303006526000d144600304006440711100080724682403140c0342c126000071386c030000014100b940c2100c3ca6440721070b05803003602c1208443e64054407688a031100c080c7d0a03035400107581c0d00f0070703001406548001d088444620a1002407241ca5039801089940092007402e00062104580171040521980b179400503000340c0b00e000d00042c0458100e80c070268041d00c80d0303840204c01c3c0c0e0703000700c2121740116030300403415940c10720001440002c41e8840340285071221901d0321080c44006075142c0054805508003e103 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 307315494 1250 307314244 307314251
    0xa1a0a14041d0c030c0715021303060b0111060c090f12061006030b0103020903060610031409010c0206100f030b0703110c01060f08070503060c0706020909070c1101080408030403080403180306 84
    0x1404600c1007003a483d00410990407007840c5040c456070000c2640110180030f0801d00720220000507040143d4121a0846c149041084a1664030304214005160b2020110702182c020407118803010340c0442c11900c0342d1041c440c02802d00c14440180322541c2030303810003190031041010300725807465010002c0078407400300c1c0d1584a001307600f891002402c0c0d03160020050f0505d40180070058403594081401644142c0655400c41c000440400480c0904406414080c9240c00c20b410701c9020394064110031400c0a940c5c003220030075103420030a0103848200f440707001ca204c00401d500b030000400400341c16030010100d1a0102d910074840401b481c0c290f201c1c0a81880c0f50795901d41c20800e030041d8100480040040300003501c509490580400c0d02c88800810141c10f50400040442c10403140340c3c192084103c01500c12520342c038013004040c1c01440501400c0c0d039034905003586c140483d80f041c800c3c14402c5e9403002d211421529140c0d400d40f07508401400450074003107805003d400302884031220300300650103103070040b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 307316744 1250 307315494 307315529
    0x4090b0c03060a062f0313080a1e050d030f02300a020a02190606030c060503010920120a060305010e1e03041a070804050a0909110a1a0a1404 62
    0x101e000d0f01554402c01c01c0c400c003580c1050611491080288815a04498840044030000315190071440b44820b500c034082200140890b009000103803c0740418803414540c01e04203005a0074914448506400a00b01e80c0b0480c802e64646100c0e40220810144104000d030520440e9503400d06070114040b9101e960043c14203c070041006443c030642d41000b001d200c114036140010300b0003501c07005041003d245140615116070100000c584c00400155040540702c0c0c1c040e0f480e01e000074003542c0f0038402c8108650402465a101410032400c50740303c15030030780d038282c0ba14842a80359035282c4002003414010382d07039405000020481c280180681601e890001c0c10700e00c001480305082c00c1e10442d01410a55005100501403848082d0303400880700781420046403600103a19000d00c0c1da01c141c0d040303950001c400e0140000c0b102e0442e001410814031550400c01c40c141c0b45030a001c110001c2d44100e1140c0044401c2b070001901c58900200001491850b00c01c10316070b0155070040c425031181d4400382c18018440e210 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 307317994 1250 307316744 307316749
    0x6090509031e162f091605070b071107080c030a0f080c0f0d0228020105072a031a061005030a1503110901080a0b0a050c0412050d0305131a0604090b0c0306 68
    0xc2d1088441c03d00c21001300100580046400c10b040200011900030b04644207840301d40c003039429150841d511807855a040c0ca0a8000201000ea95001050b80c500c5001c9010604d503601090800180c1e038094000c110030758035038843e8500d0909008040c1c3d40c2001c200628110060203101c0611800001d40c000e00705006100e400a1405001010b001c1c2c03a02030580ea041300d003a04049802d220345409103000c3d5245c0020381000703071444a0f001c1c55000a020104001c1c40600c9000582c01f040340d00a1482c401c01c58a9010410750f407007011684160302141501000d105140548003450308181a103400203400f4238008401007030b1501e039030400d0710425142220b00a19260200c0118054008103029096000c4a5686c80305101000f402002c007240e201d00020324143d16102c01e0340c004020140c1c86001c2e01b40c682c01e03c0da071544095481c01d4000fa00740710000b19581c000d20340c914615503011500c0400752140d1761b064052460050889503100d602c030346110f404074113201c542c2401a800e100402e9504e0909004 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 307319244 1250 307317994 307318043
    0xa0c0c0506040b0d09140312150907050901030509010b0613170f1e0a0209010608040c0f050d030309020609092514070b06040b06031906090509031e16 66
    0x454401e03802080188405000300050310309400400308081041d881a18007041c030044d142651090612010034001c2d8a8802003c1e101e000b1410340410307004c280030000602c045900304603106004141c041002d203da65103c2c0e03000b15407000c0c0c405c0002940a013110000340c0f850740b000c464415800740210092100c1820014211000700c6084020b00b201c050a44809231a2242040c1442900940c3d04040302810001d03c10181143d81c02040900b440d038403120044c108120546d425180915500da0114101040c0540d907400d5070030080504c2600502030b602100542949141240c12400620030741810780c0b690303014075015070300b1018403107500c5d41c01440000303084240d545168200115100c8441d0002c4d010300c1100c8260350003082c00320b115a5030b81d021a01404602400c2c68100e80c0010400c0b00c2840212845100055140c1040c4200b47c0d44603005000d58606441100254104001d01681100001d000b140300070060078496003089980980300703078203114000042c1d841c02c0b180b164150102c180c3c0c10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 307320494 1250 307319244 307319249
    0xe01170a0204080c0d020a18060e01030b09010e0f0606190e0106030c020d090e01060c1b03050606030c190b03091e0c042316020c0301021602190305030d150b0a0c0c 72
    0xb160b80d174024003a43c00040d08240c0e01d00c103907060408030700c2c0500e808c411b441c0c005501420000071903840550f0350307183c0064660390803510340f0780ca54600440542c0d10316021070404840d08101d401040f81e80c0f00c540410016800c0324031908290030110400007041d4501030380e0103008001e00e8800050034200400040d0525035000d04440400207002020b2104035801106e603030550b4060f10309480c2e41019464007a00901d940d049241d125400c1c0080003041120005141c0d04c1040b054040e40c40102180050100110003440c5040764405041c1c42800042941c2010b964031028490440d48016007003108110a902c6000b079070710f10741e080606c0f42c00c0c042c10103004440c02c0075240c0180d00800441c078170440141c4040030b01a41000c450924849010501c00c0008281c1c10300e008000319610402000444603401400d2800c80c0241140b164060f901c28009107400c04a13600040a17503d0702240d01025001801f09000d42d03c10400350004c08103030760a13041c01603c6107040d66200d001030740a035400e00c00140440ca6 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 307321744 1250 307320494 307320499
    0x90c05060a090b0904110c0d032403020409030c120f0801140d060c050c150f130302060f072d0212041d0a020717121303050304030e01170a0204080c 65
    0x10032181a0310703a070003201e1000711140c0c4103219840d070b06820001400b501c030a0540c040c131445c010800d01e03840e410100b03807001a40b2407a1000c00a1f040b094139a4120005ca03c5443c199401a03c0801c00150811f6080b28401381d2191400380c003000d5166036065036100b2030349175500016594821064001c0d4000319818003511500604a009010101c0042c109029800f0b00400c02ca803600c00c0600b06c64003030740664100c14500004c0c0c4084864084808500b5142150007445440460010071007506000c500b001c00c03030b60103a01425003580c8a0181440c2c0d0000944414100808010394000314a014480c658124005100c0100d6500041714000d2602840c0440e040602608100c100034000e800d2030034007161202c02400e000180c0d209e07850840240600303100502216004405110481c14800003005c04c1ca07003c880d02c02d5680c640d011800310346000d00d40020003056080001c940070a0180001e003880440500d0a81a40c140d032602040c225a410380380c0c48a207a070081018040303100140004003540c1801d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 307322994 1250 307321744 307321747
    0x6050d0c02031329030129040e0606030414060f0a050f060907030c0207240f030204140d0204090501110301080d0e0604030318030501020c060f18060402041a0d06090c0506 75
    0x15180500d0403038141307100d580c0b0465000e003041d00700340d848110f01544906080802640f00e40e550003a01000421086a01001c1a2070001451414404109407019120855800f800c00e64544050102d2640050015280c00c0d05c01c802040b021281000000d105001d013420b008460304041040005640c0c0c05080030030180c001d141040f105448444160354812014500414850b644032000c3c0d040c52001d400114800c9204048a0010780c208000015002541ea944441d0550119000c904a018900440c0d8045465800245442c50070301040340f0b94038002800000d04201c503a4903d0f0840e003864a030128164000700040003d40c200780007170b1030711140d02e041540f03403447c02400046891045020041c1400001400e41801040e8007440e0f1000d5603014008541d5a002c042d011039482208441c6421809076800c0024030220001d840d03801c42e80d00c0350004244d52744507542004083e140000f034048400540803007428041c1d446c0850f95800354080d410009113041c4505217607018030100e401848c0600030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 307324244 1250 307322994 307323007
    0x302010905031506010503070903050f0a0b0c131e0b03130c14090f070201060e090a150b06090d02061e2106030604061107062c0c010c0b060d06050106050d0c0203 71
    0x7110f100d00d900c000240781050741c0b40e860201c1515201b0207074101900d10300c603003c90300b208410300265860807a402504600000c0c0d80d5049019550b224190000500a00b500c104000452074200c140c4840542000b4003541c040e03c500c43c18805030401c450010b0b1071840c40070b4242c10301c805d07454135801a01016090100c611115404142d1015024100c0344150103010300052246100b9805a4041c0001c10600c02c21414800455652512003450030340d514414121040ca05289506c11160195405441c85040443d900100311150b860150103903007006d0100090454a00c102d190306101120b00b00f0342940f10340c81c040114500c011031800c00803030341580340240881d540d40051103d0b446940244c0c0402d080081c103607080040c1c010040c0040c55039040540c0035540d40c021408044103031f00514040ca0014050321045940c1d0318032143c4140c040b0b00d00c0002d41000c41d0104050640c41400600700040000c2d081d0303101001c4510903880b03000040d1002c2030742c0714a05518016414180342d00d200071800c0c83d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 307325494 1250 307324244 307324273
    0x90801050c121302040228030c171e070f0806090c090d0804120305030106020c010c03090b18030703030306060f0c050d0815030f0123010b0405061e0a09030201090503 73
    0x4200585089800c9401002483c0301c2034041c850003031a60301800564581d0f00000b40d4900761030607095510180d0324090700901845100c2c0c401c00d848c00000d5950300c0071040840108068040c4e015108401d45254000c0410200000d09007690042000782d80c1d420043c0e564000042240070080d050f684034400d80814080400d10140a844420100700c460030380f80125850300070b00502c1b5580c00120000200c0540c0c105040d041780c0030314100d41d5140c00356001d0500f1840115901c0b50303038800080114510071810b10002d83e003480a41b51120701007580c075003000d44220000345004402ea0088001945501050102c0e03030344022041802241403c2114811090b55510f50303d030307980b24082c0d40402450000159030b07200e09041100c410200601a038494014480703010740a4600c002d4a940355000060b02c1449091000c40030314100c41c00f0010b25828641000100841c40c0c0c0280b200c601081c041410500c64a1181e2008004003111521a5180309140d480050000d40550388030308d200e508a111200900c4 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 307326744 1250 307325494 307325497
    0x90126030903060414070306050a05060a05010804210e0d060c0e06180d031718010b030a11040e1608100c0306080d140c070603021b160e310201090801050c 68
    0x140d4886101021401e0f03405ca0546041e80c1c503800902014200024444102d4042d03011500611007900c500d88040e40703810040d6822a03041e140100030a0407420000520ba10091414900302440d14001410505c084c000843c4111104015a4080c5e0b46407101e00d4140c3d0400b8800071004010750700d903810a801615020b002842e03c0c0742080c014500c8408440170540b2032101c14515502d030701001c50300742c2080d2540101809440c150400d130303076107444502201071400007000300c4a55407250200d0549104030701408050700005800380100d01c5a5403d0307401710078000301c0140242042800030100c907041c600381c2d01c09507281d070000794081c1490440240441000801c1684880e403140c01e24041c030188618030084288506038000007580035104001c20a580c0c036400400f203200c105d440e80004500e5100040c1d4031b501103d007004a580c1c0c41c2c1c0740b04012010039520010383c00a0010303420007000c1940350841c2d03c2c3d19044180040707443e14800c0310008642c0c2002001d07010304010b41c020805860625a000460b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 307327994 1250 307326744 307326751
    0x4150e040b070e1315050312040915050411120c0306010512130606080a05120906030601080c1c091b0f0603240e0118020304240b09012603090306 64
    0x109200c005424580034100e906061000a030503044c2c0410204400c80041040c10300310342e080107103440006000e00d030001c0d40c3d0070315070766688c0d850340340c03500d082021802803410412011000054040010300c5030740d24483c1c691000590341080c0d603030300608160585030240003000368103038079010700510101341d03030000994403503819070520700c0e40684440c8520100b030f11a0001c02482181420310106554002149000d0307400d114504803500d03845503440c05950382c000d0282080d0001801e0000504030343c811040140c000c6204910580307444004140c035030705030880500030780c01103844d000000100040d0f04801e50304040302e10601c0384070030700f03200e0440c408030000d02c9030908054030b810201c032100f0311104413041c140102c0041c5549086d503610301b020804c142440340b1038061812a0041c01100c11a0085900c101e0b0320a071800e8490700ea400035000340311400c0b150407c20351394a062800868546804090207002000c051890100c07e022082984d11a0048160016001030103d5115902c00240d120781 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 307329244 1250 307327994 307328003
    0xa090816020d0f081306030504021c020112020c0c0a0501030c0c1101090b12010806070c030c03030207080c160509060f1c052406031902030a151b020c04150e04 70
    0x441549074000642003440400d005881d481c0b450300d61504100803103005100c001440ca0558a40396035584040d000c8138802c032000794118003c0d600103146503641581220300c0c240305051034084042a407034004201d80103040e904600b98041c03110181103207422105000108003d00c0c050004c5131000702c0042c5040200c0c1c00c0204031402c04083e10040341e01030401a409482ca02a15503181c400319040b088205400f0710030401a40141004900524410350100c2c02168058441a2554100d950700301c000354440b0700b056034503100501100342101000d021542104800c801000c0030141400100314150f00082d11041c40b42002d1a075070101c2c0d0321000b0030f03001103800c5000b080032802c1e81070502506004041e207284403100c0c6070701e042e01c40803e040c0d0903290003180b0a1b0102d41000c01402602070107916403000180d810b03400503031564005000301e81d080d550742d03c40c00d84c003081d5103e614103a10040100f060042c0096000301410b00014280f85c810448486c012803086c1d5a032030f20302040602c8841000d4806070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 307330494 1250 307329244 307329277
    0xc090f04080909061c03020709060602030717090103060b07060f05180c06091203030f04110102010203070912030c060c0f0e0a0b07080a0507050a0819020c060a111212040b0a0908 78
    0x81031982c60385954005c801c142c9001200c1c510386441c00030344032061401903a454920f000d20200703501d403000040c5c2d02180e0780040c0c0d049415004034042143c039044414224109622080081040302c0701c0406404402d200c2e130030128074008551050300540b107006151048041303400b089070340c0c90440025800070350340303080d100c05d036962850201040204400c5e9074a0501031000000340503460f6904064188260300803c07102603040181c400480c00e0b80300540c0c0040015040c81d0051044140c01504100030a2007400d0800ba002c0c00d59480000356502c144441000c2800e14085014030740c1c0212407643e5132041200d8101c3d00ba403e111226a042c09402c0002d4941c25020400442c61402a82100e9521381c12000b1202c40c9a50741c6450740040d4096284050b84000403c0341205a50001130003480c4220001d0126080140c4500c2c00c680a100c6007280c0400c91150541a8851040f2440200078024100900001358981400d2040070880040d040c154942c1c641620040410600402d54004828402564 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 307331744 1250 307330494 307330501
    0x30c0d021305010b070c0e150f010507060c05130f03080f070804080106030f060b0402120105010809030d06090507031b0212130815060f040b06030c0705031b0c090f04080909 76
    0x1407003002150703116140d102c0c07611001003070b420452001380007494402e898692511f9200c02e4010385560f020741d51440340145919510036149810100c21310b08041c189045410300b4000c0e00d0300d40648103210744407408644001025070484842505510141c9158050060050303d9030303a4041c614440c0c0d0002c03401c503440100d2507008000d01c22040741d004000302c02c001c1c030485480742880b140850201000b2260945060076807006818180240c0d05010708503a4400d110368038120064804107002020034455000802c81d030010208644039800c060101028001501e142c0300d6070240484141603910060b540b210981d20781035550000320808210700c4c05c03051a80b00c2820500b405001e2140d80c00c041c02900500188031440032442040c944030b1041100c1105120b041c0c2401d00040351125a000c5400c000201300207928012918001d100d0705129400b180d10300409001201d44403191a19882c0054000d605110070501d00fa0440c140c01000c03100d141c000070705107542d40c0d58452192500c000e0294803080000b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 307332994 1250 307331744 307331749
    0x30c090103110f1504060806010801180e030f0a08010f170d050a0c0210020109020a150c030c1b080601030314122202040204120204050f0112080d060b041d1302030c0d02 74
    0x4a04402004e02010010000c802040b640c542103030041c0303000203031100001282e541c80303051454101d030200f000e00d21101c0320204805015000031200c03c200c91100700802400060190020440a01c2c56070319440f00b0350500761443d861fa0029032061020b942e002440706036030440800d8520008205003446030391082000001e64509900707100295000c80e81c0c00c1d5400b00c081e01034002c00c01e40707882101c050b51040d03100c50400090250b1000c03040e0015407a041001c0000f802181c441c10641c0c040c42054990740882c41c01030740c48034103c0d0482061078218000400402d41c005054251007017052003540c1c1007006c04104145004d10050001c6c0b0500d5000302d40600125244421001d510340181040d0359890300e0b010070345030010080d00102c3c011850640028501100714001034143c0c1c58105060b0745600703098507500c000380c01c440a40300c3c0007641c80da000190340817240010130044c50484c919509500e6242e00c1501c0c0444010a582d202150203004a80165004104058140c9085505022403220380c000b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 307334244 1250 307332994 307333009
    0xa051509010f02241611030a0f0507050102070c08100e120313050d1827050c0c0708010b040b120c04020d0b04091a010b0a080c0715180b06030c09010311 67
    0x318000d2684060519100025040886104142802c8080415005c0705411a030f802e070b40c020b060074190418860400c01a01c5001c03082481d15251501d02d007442441e8660908907408041c088401072182e14080203140130030302c0743d910701c0808178100f00101074100d034001e030b219600e9141107040000000005105412229407502c48141c2120443da42a00e002e800a40510011041d440681c0000b0100090040055461114403650b800d50100c0c018400204100504400b80547e06220020320401e61a08020842440180085000480d40b0310a1005010450309401e04640c0074480c1c0c0004051442800101a5031811007501c005a45038400c168043c02003801440055001d8188070410050000da00d00c101300c446a5000070351101d0f683c80719490840e118014060011492190000760303841200b0029005242c0102c52541c4c26072050003500013143e241d008820400c255200a40007813100178201c0f294003500940061042400000000799900d405100040503030107540c0c10700c1a95145c110b03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 307335494 1250 307334244 307334263
    0x3170d0e060901060806090d021002162f0411070b04030e0d0b010e1608010308160b0406090b09030301080a14070f0602060a0e07060c0803092104050a051509010f02 72
    0x20641c0c1d498201064058080c25062007420003e00c120400300c0d0800348041000700304030070141c000b062001c3d800402000070b5000300c18501031608180d42e5840109141c021003005180c501b00030b000741d156001c150081c11640d40c0740c556000320b00e41040400301f41800011100003542050741540702ea503580c40c0844503112221042a00104a4080b0008200818010a040e2210701e211035141d5a2044166a070701105080f000340040c17203080040010030060001401072240c0c0540c44038400b82c0d5502c8080703459506980840c0c04607682c165071030602080002003500300307205602540c42c0d0351418a0071583d0743c56110001d080d0740b00340000d40f81c850070b081152800810300480f00c407603900c0d030303604003e034807243c049a441c1801403d00d9000443c2a002041c480140e813520744400c07002d10043d4454151640008048503031030b1048282d4480e0165015194005080311000c110359900d08180c180149240c155001d270780145031403005059891440ca0940300580f4007841e04082c140c4070300300100d20700040d09 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 307336744 1250 307335494 307335521
    0x20405100b040f0306113c040b03011d040201020606011103090301051e01060c020307032405042102061306020a0203040b0c0703060c0f02100209010201060807090218060403170d 78
    0x14001248943c10b0310784822240284410414140c1c0c50001c45c0031072007403511075034202a14540309405507184500710351000c1c1070301e01c1c8882280711140b40000030394415000313070805840106c01006920100b4101091000c05410100524107240d80040c1d650080071708441c0c180007000c500300074400d200300280c8100c624014000c0c00b050510710149441440403905203030b90000041c00105230540942c0c60451440c0d1b000d4010040e0525540301c40d40c891540c000c480e40070745d15145445500310190701500c1c1c000c40c02030400c21b00b65102100d4810f00e56400e02c400c034080d50460020040e146015410f100d241320340002c40960380740720b04c42c01203003544903c5d049000c00c4d03800820280050b0100140400035244918420040140e03855000e4840081c00b0704840d0059000c1160070083c00c5c4103401902e030070b000600000c0b03041516a80301c1810251103411660f95a0303401303c0c2c0310800310802c2c90360031080d40041d1900c628040c01d688400003002e40850000d10101030029000b02880c103d94040405503c86 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 307337994 1250 307336744 307336747
    0x509011b061a1012050c0d0504050f01271b030f0305030604110c0303060d0c12080c010f06060203041a12010b0705010c020d0e09041103010e06071218020405100b 71
    0x12031070500020a0304003114030030400340012040040c02c200c01510b80d144401c0d107800c0d03041507488a0481c09070100a12003034004000380b1555804030401d0003450f0040313119001421814042d07040c001d007150003003030060045181c600203402580d5400300b01c800310079070082e106032204554460408000000e950005002808040c204e105240d44140518050309048509108400070300701101d40038003403444103c0060304100007241203450b0040c80549110b02c00c002d00400559101c850307102001c1d92138429101c484c800a41292412801c1c890103207589208001084100d0130501d00075601d02403130007500d032035841c00144103913201000d009549588400e414a030038913603101c901d1803200c0c3d000381e0001c40e003549c2054003610050b4008102d01010030031aa4811250f44804000c0146011002e00166040c0f2040c0d0701c2121251000c4c05811011115440140b8140c200340c10300400e400008070401d208180b410021054140d5480a0014841e0301160b000c20360751210000940e81e140c007503008001343c0380f0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 307339244 1250 307337994 307338047
    0x140601060504030312060320220f15150804060e0d0c02030f060105130906020702041a09090d0507080c030d0c031e090c061b0c1d070f0e01050901 64
    0x18404002e000342c0c0c0c801c4d039450000010185624040e251103000042007407030f481c0859560040c000a0440f040c0c03000410348031544c000d82c84003641c04900080140d4040341c8650755443c0c0070126015018154101404454a8903d000c0d414651804504a548100041803020505010140d0030070803070352080034180d40003000d00b02d601034058202003508038064098040c070220503080c040f5005049501c081c11480c586500604060300826029000b1101c5c203a00340800d00241e1154032445403076421000c00b10a031100c0c42820040700581c000c2060105a00980707007140401e0303000d4180c4910301d52060600342c03a000c1d8030ba4098110702542c00c11a01d000c0c034003803004469a07810742216204031a661250901c0a502c0021441901e00d6407102401c0d260f00350f14100201403045402c52210502e4800e280c008c1c0380c1c5952100c0ca841903680c010703024040400311580c000c82c003800344160000202c1c00c09407041d07040000e01828544580075000d051142c0800c3c0200070764080c6c0b11102140c0301d81e1010400108 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 307340494 1250 307339244 307339247
    0x7060810080d1701090b1e0a0b27101209020d0b0901090c0f0b160503041a030702060a090b070804140709021801020c180c1209010b0f0102010c0f0c14060106 69
    0x81c108808290700303c582100010307641e006446555415000038180076444540d8240d001154401c2c4420140c000084c154009421000c010150072290700640f0704514942600c10305440b1010340d2040180f182d504405030400403908012421400c60010b5404200e080c0103000190310a2261840a41038056813410840d03102c43c194010f9184612541402c4112a21064000c1c1d901c43c80707000e0504003c03003c210440c3e0034001401039803c40c92150040724549034070703030000c42e00b0000070340c0246011003004424230094640500000f40e0040442804201c0280baa485001d0a5003000e4246824010804049401c4c4010a00348018403211901190301031983c84c1500c400952011500c0500380840d00584003040d8800324420007501001482c01d00034440000d130345810305501810740e0f16400400c20000d09020701000e0001e10a0780c4460000507060324075424032001040741600b103811039140c20341a40d07040c1c7d000300200411030b50500c1c040d01e100700c0501d03206070341c41c0241e9040b20042c815a0000599207 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 307341744 1250 307340494 307340507
    0x5040501150803040b03100b0424030507080c0a020a020306180114040c030b09010905071502060f1b0a021603060e1002120f0a02090a090b040e0c0307060810080d 71
    0x1144a04001c0203103818a49403185152070900418126400802c81040108103e0f00038540001405058031001a84c441c0d125200e0b0340300f94002500e21417501c5040400c0200c0405030300c0390013007500f02030001380f522000080072807600804004a008000c1440c040304c0e81700f006a140ca81d540601168183d0400c1d100c00d40440080400c03880803582020103c030001c4c41e00070745c00d90280b0340c02100304100c141141c1c1e9a5031640802420807441d50340c0d0325981000b041c0d0802071400202a80e500410480170030880080c20000020001c0030302a124405016000d101415080f82050015402607225105014201d0400c2e0050070600300c40c05100101000b440250b038051500388490404860383c00c2e0385500c10509074080e0707850440c03c0031012000511010401643c2c41d9021550360381c018a40204900058010001c980120a140e0798400d000c003403504061007a10304c07054000005042c0603202d0740000c0d0ba102c00700e010f000c3c1000b0983c80801d4600c0c0a9405440281640c4015a202d038181d01034000e084 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 307342994 1250 307341744 307341751
    0x6030f14070914120307020907020f0d0504030b06031902060903010b090108030306030105070f0206150d21020709020f0f0a0309050f011b030207050a02010807110712020f0402031e040c050409030305 87
    0x99600b04242548071340b0300040c0c000720102002000c0c40c1846026020025008402809881076000d140000c00345442c00744100c0070501e03199126a5100c0b807d6040014080c80c0c000c0c40e5500079402100084440080c90603408002c50b4100c6030309545580680100c1c0c09000e4a00d001a0880e942e000041010b05000c00610b1041c0026002017200380c0ea41c2c0d4046400e010700300f600302d0241e00a0030108486030085022806880f00c080d1031b001136040203668902802e05415491440d40c44440d80000c203c0f6818070084008005150055003428074120065070a03215075000345944180000312201600d002e42c020031103080d003042c140c170200c01e220380169000c1c108000450726500b070070603010202c82c0d0080c400d83c0c110780d82007001401445a83d0b401940d109802030040800c0c02091820104c904008100040183c5055080351441241510511074a000702444003031080e130040c4100040d50300f100c81200a0a18000403980032a200c0e070405c0b6024030170a400c166000382c1010f12a6051680640105d0300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 307344244 1250 307342994 307343009
    0x30b10030b1203030403081f03020d050604050706050405031b151219200a020c280504230a1b080f0901050108030307030f0e010504110907030c020706030f140709 71
    0x710500010b44042d100d00c401c03940100804c075100007151540d20f1090100700001400380c10304002c680c80f40c0006000070901700045401e50b010004102c2085070500800005018a08200b8101400c01e400603480d12540034008000c4000d81c42a0000340e6a40b04051540000300b100c959035950502007a1807002c082121004041c000031304659001c03036054850b200320050290a407000c030500e0000050780c070382c2c442c4020320114890600706040c2036555204001007408504040e0080b451036070400c40c0c0c00001c41c1d2059104070b00d4561340c0c074840000402c900300c0300342060708400b41c10ba6600300300340002d0501c45d490407031882407100203009160b0040403da01641d400054400c040d1780700d00132a400e9940c00d0140f1140b035001880454460b034000e811181083c84a4500070507003180c259a8542140c1c400ca800303030b4203203c00004503405030404018541e0409890702e01802800000080070f9946c11207485940d00301a603c41d0350408020b801d501c5000d500b4082c100c0100d090600000003400074829008541 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 307345494 1250 307344244 307344259
    0x9010803030403110c010c030503151809010605040e030304060b030703050a0818030a111e060708041412060103020d0f1a01090c020c011d0a12060e07050411030402040c030b10030b 79
    0x4002500142443c51000c05075100381f401c202c40d030350880c1d903070300701a0038182503804500e0717410040d84e0341e26143c0c240c60401003e45c08540c070f004401c050070340302c0903403209000e50301c4c00300106040007000c8100c0764410781140300440e81c01205e401085c54006a0350001d021806000880303020800d400000740308480482d000600c00c00490001c1507207900040344010585020200f0130043c82c1003a0324004010440b0343c40f08001040c840d00840c90360b80c8007903411520f000d0700290900c0410710848803450310326016141074414440481015554003010301002e48540c8100e500442040460061144c1c1c996000006000c0316000c103090040b41d20081c014034003841c1c01c1c03400c4824aa48001585000d07210140d580002d0400c003105100b0301031411040e89500010101400b00b140c1c008001e400212605c204000280181803001c52400c2c85000d4000c1440b5905104684000c04110000d5070b802a80407076000907502d490000580003000507080e15908406268160902240c141d4811300342e140702690310703c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 307346744 1250 307345494 307345517
    0x608060a08030a0e0103022704060e090a060506040f0219140a02030a0806060c030c100b0d0f030503070201141305060f0c0a0c050c060d2403030815030a0209010803030403 75
    0x18220200d028401007540b040c800c1074a003d106905400c42141c1c18140145890b40310102495416104600202c400d42c00d508042c1860505c0e01c9040014051003010341d82505050040b1078881c9183c0c5030152249480c2d0000c1605a034a40e40008900c001c1440115508c110ba0700610043d003908c0c07030607032011441d001c81c0c103450a04440121110440c141c0e020b5494403480c0c140c160f80c118070240440350400014010300d03540d102e0400040902c6483c64006000361902c50100740c0595003c607076100d00541843e145d6400080c0c0d00c1c2c0201d041c0c0340d13140c10950f4907075a07018000c0f0300504090180d03840c01403a04051201c3c002008054072075081c01901621004e6076480d024800c2814259141190355504004c0809154418400c0c1d20300079109005076846401e0040006440d80c100b40c1041140d181d480c1c85501c07141c10102c10340e10004925400f051500741c91614094881c240040100d400100000c0c2880915501404612101a8000c110007615619402c0040d0b0329041140d0032004114400d001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 307347994 1250 307346744 307346749
    0x60905161d031009110a0b040f09020906030c031e07050915071703040c030b012301020d0905040e03070203010f09110a0b09150c010e0d080703090c0504020a0e0d030306060806 77
    0x140c5100c200150050504040901c140d10081100c848180d404c1d81702484e4040b1035999003803409004200150169441c0e50804c042d820010040703501000549104100c4603030151540d10549070b000062000e031036203980e10000041c0e481c0c00c00c1d0403103000320880042041a41504500078082070802990601e0582c0c008640c107154078415160007410b922090940d400e81044280c0c0215403061180e6034500c001c6039296035241a5140a8000c01d0103c00e4004188a850b080380c0c0c0d4078500e2040034802401c02d00441d5101a04e034680304e000f40b034042d03920342202c0e907000f101c100110740126901400820005054a9202c1700921003824125003021103044d4602e0076141005180741600c105e9000e80c1d18010030442005000040010301000d4080e0034420703004011400e01c10684d10000b01000b030919101902ca004001040c000d000740145450700c80c544000c01c3c00d000300b035000e9490507180181d460507a0380054403440000070041c0e6110380092170010401d42c0c50742014003110001d45604030b003609d50404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 307349244 1250 307347994 307348037
    0x100807030c140706050402011119030824040b210303010509100501080f091006030f031106070504060c110603041401270807030e0a0602030a0210020705120d06090516 73
    0x428100c80000f444100c0200e091070784825005441410718401c803942a003503490500000c04082c89000200d01005000d060300440301030ba0100000240d80c1500905001060a840e246100c03503000303039030b900c000350140c1e140c2002c01000c000b600c103024031042e4420381c0125682e600901800d8082d02100002c00d000c0c0d002d159005055400507141c80f821a5901c108171100944000d10300e8a145c40759807020606c014042c03065034051802401706c1030049501c0e0501a0007141c0700c589001490b84424208403080d079000080d20700b0754000d03151018041441e030800072010510340030036643c045000030500c4100f1041012824005550000a0181c1c03000c205000c0441c121081c4042d1800d04443c040c20300140e021001401810f219003000000120f149020441c4a4010b0700003a02607840010b00d803002c00c0d0100704942c12440c15000940c038100c40c40c0c0c0d4158854130318078020401900085450400304a681c4c01102c0900320260007000303149804d11046d0001020004444c003c1524501110540e0b00082c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 307350494 1250 307349244 307349267
    0x50109090902030c130207150902040b0916050906040806090109020a062111070f0b0702010e0c030a0212100926210c070609050601030302151e070e100807030c 70
    0x2001381c540301c1d00c1c039403e00455000c50341500003c01e83c20400d180000d000b54415181c03001002d03000098403032091040c081107481c1e0024842c804c184181c1040741841040503400c10b0192540351150b113401004021803414020350300088410b01445040001d0028154009013045000b154804451540c0301c3d030646401c64900090140c021010503014503c0b131031030b0400c401e00c800e0544c1452a0203229101d0301205c00200608492201c5440c0502103503075424020a07a05884500240a0500c040d40001c3d607202c0403083d00038043c41c0000d291200b40c07001481101e841d13040d40d4a09000081940c60200c07003226080e09012001810040007100000e480c8064030034500500040325400300749442410f501000050810b103403031004011110005200c0d0040d101440e10900040c42c3c50750461401a0030000b4800e41c00011900c000d007002083d160314034901070890310380e80c0911000c0e110004211088a541841a9001040794801c2d010700744d8030040c814403074002075604000842030340310122252030407103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 307351744 1250 307350494 307350499
    0xd02060c1207180e16120209010504030f0c0302090924010b270d1a01061b1101020c0d050a0c05010305060a0b21010e07080903030f070e0f0613050109090902 69
    0x650008540a019400750b0718900203550700d400f0569901d4141514241080700c01101c1c800c3c000b10203c1200780c01040c2c81e6000040010190300744120440003c0c241e018074070024040000403580d0009210001030741d480034540203000c0c4040e900d08410055900d00c07505000c020701d8011003000f10328211014070568180c80c0d102c4604d0b0710781a49680300c81085c0104c1220720360901d0030b41000c001aa603e8010720300049126222021500c01c45042c008800031050b400742040c00508810b20344410041080c0c040250f81c000000e0b4a40407401e00100e107002403130404190841fa40c00459014000c000482410341441026010300203030721a130044081e00c405403056a0080403030340042c4a80074810f8003400200b0300318a08032002645840144d01d0b400e03003e0340510160400c0d00b081c004100d40c020340c1142d0110015004501d1400c0405a6400250000304481c08100e2030100703c149568501c90307a04604800140000c0d103e4100081800d2402500d104890120710740440001c2c0802c5070340035171034555400 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 307352994 1250 307351744 307351777
    0x81b090c0d1104081b2413080724031b031a04060308070b0903120a0b030f0a0302060907060c080403030813150203060a061b021c0b090d02060c 63
    0x14180e403420a500901055910151214030705800060602d000d000180700701303c010800c0a100140d14400c0b0608a98082e01545502408002d8404c4005a42d8021005038031060381d03c3c41003005c0c4800202c4c10b80c12420050217100b0b800100314407001104c58070701c1d400010490300c3c4091040140e0450708030b030701105019054040c0b6000320900030f038040440040d200515107025983e5000040803180c03260400c031100700340818040140310204c4110340d03001082d13400861034030040d00c690094145008000c9100c5984509a581043d2018010340d480c142c0e0301d1040f0b03511f00c103141c60040c0d221441154140880d11131a14000360491284440c80040303500191504c5c84e142c1985c804541c0c8180041080d8407941407003884c031000420034045c0c214104030345000103071281495020041036400b680d1206080050700007221442542d0007800d412815412240040102c41405807100e5503044010054000d000f03403000c00582c002d0104241270241229401e80d5103580d107801900e000c0c1d00900c03a42c00c0c1d22110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 307354244 1250 307352994 307353001
    0x1306030e0f0a021005040509130501050c18061303080307120b0f090f060a0f030302060403031d0c01030504030201060b16050d020313060f120203240f011b150e07081b09 74
    0x3c2c001c81d084c079020110f00c1c104c0d1516850328041104c0143c00d555000c00e011000d1448400d12100707220b1160003020b490f0401d40780c452400d030400d0510007401c202501c50640025200450601010380c0d4009580c0705030015201c0c0340c41c10b009001da01004500c0d1810504050032400c03140352002108014520007400e89903d40c603074a00e0038a64500003029075800c214550404940c500c0400e0301007009520075401049289494980242030301c006000e810422510b00c2d6601e405290042110b1408000030308e80042c1650b91410220b0242840f54811401450300040c4c0c2408000d4501701c44401c0c5020760304407040301c0c0c0c080c003089170f072403058410200000008150600226216a40210130421103180a685a010068100040341c0c000c0d10650700380301c00c0d02580000a80e03074984e0740c2d003010021030f120260400101c001030b2240b245203911704c0c945007510b01150100f0003003915190300c00d43c840c0c0e42044505240c2d8502c40d07551420f8044d070012489104605040c40d5620340c00c007180100081c042d9905030b00e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 307355494 1250 307354244 307354249
    0x1603020c070302041407020f0c0d02062a010902040e070302010e1302091008240108180a050d0e031005041a060301090b150111010504050c1c081306030e0f0a02 70
    0x4000314003125050144040000c0565154014030309440265441198681002c0340301914114488107056101e2308041282d50003691054000307000c0c1c540581d0303d590f40b200120846490345410802003060465001ba05401895056101100c1c5600c03d41d020040e000155202c0c941da1225444024001000400600a5800c080c40003460160380c0300380250034014000d002400390220303402d040000034100010000d0040442c0030302e14011221500f02d100a1008400090031418001c0417108608030f00b1500c044500f504000005419401c07805454454903a80d0004201c010001c500d00e10912403d0009006855180314840c011079000c00300603040304000d0003d230b507100c1e40104541c1e8555696021a404a000003424078807a5400d402d440c00794035508000900221485c07644607400d41c1c9802c003000009040001c0075100380c04121802620100710a40b0141450000c010041a0303410101d0000b00000c803056426050782c0342c1e40c03001c0c0080322510341000d685981d4511901003a034404d03100c080250 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 307356744 1250 307355494 307355497
    0xf070e0607080f180402030f0403030c1b06020a0e0603191116050109020907050c0703020d0f0c030b06040c030e0a06150b07230d021c170712060509160302 68
    0x28040d160606120694482003815000316503070b20041400003c40e585030702c55860110290220885d002c5046042490406d8490100140002d05240c1d4500c0310011b2203004000d01681c51030000c00b241d04c903012901d0304801a402c07150780c440214281c03a40ca41d401e490020f050302c0c401e0b6400c641c203020607400c085200380540752000c1d9003884410100078035a140030b49100b01303800c1c0501a40010440c24124414015010002004542000020b20a0f07050211000c909c01e000c99804540f02c0007030049074208001d00c0f5011500040c90910700e101c00000b004503c1d10200d200da901200c0401800c00080b0080c0e060f81c07045101c140702078101120420010f8080e80c00600e103101d050940c48202c03a1600c0c62042d40f94049401500e0b0b1940503294807441c002e098076202011200c1d81c0103007104503c0041c0c043d60364044c127201c410343c0301d16104d1400103c91141046041d03207a070040d0301d030580d8244180c01401100e5039502d0321f06c041d0305260000c07407a4180523695902441949950300c03030004044104500a = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 307357994 1250 307356744 307356767
    0x6030705031f02090a1715010506040302210105100303140405090a021c180c0b04050603070809120703110d110721060c0906090e070504030807050c0a06080901140f07 73
    0x10b540c2d0901c003031041612107901c103101034441400b0030424909002c0c681071412400c104220b03d4941c031000144100d4a84100340d60441e98162002022280041c41000c1e40c4400c21000200c1581380004004440e1110313140003040b00c1c00707a22001030800480d03544a400f8030070b90264a8101444001050800c1c43e1540200303140c2300085614002e00e0941c40d0000d00f0341d981c8800c44a0680e0b4200c00304070520550040ca5001052400e0105103040d26020200e1458000105298144800840000c90302d400500c04407881d40d02010202d940c654540c83c01501c2d00417240d048241c9449607010b9005914094041c0c034012114080003040b86924299425001d0075515204903c01c052000c4c0c0c802c001403580c000c503a004845500c80c808914200f5400400c000703110391141580d80d200d5418401103603007200c1101c003505c4d0000d029030368071911428401d10f07112030010300f40d422140c50300340003d02c45d034000c40c0d2900840310b0700000e000d103800e000741e16845042c040d92410303030354134101010503000381c0191140e00c031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 307359244 1250 307357994 307358053
    0x31e070f0503181002130f0312081f030803070305010e04022119050105072a060f090b0a1b17061903080c1f020f0a08090709020c0309090603070503 65
    0x54600f029100700d8148001d82c0c03400141c454000c901203184181049a1401034a042c0321040f0900e440c540b14429a40402029402031104901c00324000107140c81400315949a03a032081120395541340303441c00c00c60784101d032564002450100041102020000038500513900101040e0f00b185000350001070442c80041486010700c41c003d901c190314074580091440e446c0c0104000100d03490281000340c2084602c1042c0481100b012211840b50007a0b51503110f1944e4208000040f00140c520070b51005010580d006008034605c081007010b075644c1d581040e0001500b9003800d91113403c4040098621070340001070304c480c0c410102d00040031030802d945a4441c030100d0700013070007607141d40b5100c90403180d02611099045400c60b0411107aa607070900c0156680b078000940840c40e014400c0040209802120106000c000f5030202040c00705804200b6080504240d9600719a103031100380000e5901d9200b201c61a0283d07117240c001400a14020a13504100d480103809001300c0d15203008a8600c0010190b048070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 307360494 1250 307359244 307359271
    0xd031215150306030204050c040e0703111e09040605061305041e0e070317040b090f03210717040605030612210309010e010c0905101b0602031e070f0503 67
    0x40401d00c0c00c0354018030361800d4400048160850042c0004c0d0b420003400e0707d1035044100000c01ca144e4844050a43c00241450001100541c0c051403444900c2220141424014003035100001c00303003544024255208116002c00400d681d81d070034498a40039580c1d4074002d0500d54071007000340d800c154010080311800480072824900140c0320060845081c8200741d80294070003e070a00401a6040c8000a0b6440c0b09480500305850500d090034684250321241e1300583d5150080409070318208a03508804540389410140140c08202e02d14180c1c00129007661030314070b210000d4a9440244045078290342e4242d56091a541d03680061110a8810280e21901d5101d00555050409a03629030012500b40403071000c0c0d0b6a003056400c050030345280c000400d0b204d03494043c52510040d0000011022100c0503941c0c1e88441c241c1e84000c0d00c6e2180030007800c8181c0e030f0442e10405c0c01c04c1416402180701d203001d00003c1c9102980809404840303041160400c002c6240a070081e0300d86400360000d558080164440c15 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 307361744 1250 307360494 307360499
    0x230d0f0e0d03090905070f020316050a210f050315041e1d010b01030b0609040b0d050109050703060c1107051311040803040609080607091a0c031801021e060105060310080307080d06050d031215 84
    0x10075010450701520003400000dc41c0000140d61300890304803440d00285881802d504081c400f044600d920781c041584a00d030340e690083c1c4d1201c091039502d10301d0b2400c0d090070003c44680b00b00b4848840e24000c800c42d45940781c00c244411540c041d00c29003e2548000e4803460900419000b404001c00c0c1c58100d50b03500107003110310000060700034094443d11034811070250040600c0c504c0c01c0703030540707074818040070a00040d80103400c00080c00085080840f20304842140e03881d000142d90340e0003030801000d1030480d040e001401080c84c810010080044810300da0321003c5030340d55a81403a8540380161400c0d000100c4001c400c021100160b50f44588030440300e0304c91440e20011265032403840d8000c0740b811035040c1000c590200300751f8040c07082030aa0170740b1080c1041e04440728100030b92030300c005004051080401001103620546040c400c44080d0100c1400c495484066041c00400d503040b03e0355500c0000d080050118850522a4090fa10703580e0507200d1034100110409000c0140a20101c6042903203a43c0000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 307362994 1250 307361744 307361753
    0x12030705010b01090608010302060a0f031e1401050612070507031808061e072106090519110a14070f020a060903230d0f0e0d03090905070f020316050a 66
    0x502285100e40300020705001a580007404a8a190b402202803002800040016032508003c4a641100b20300e840121070701d81074010f8000708180540c42040d80000816003441c41d1031640080311401d0316400131030b002c2c0e0740d0340b040091620070404031402811018000c030700458004c00240a41d1b501ca4105210140e042454079981c0020703551041c80c6e598801d03800d11004580c04589076120450305c04002d001031404c007101402088106004c030134421600c0340203085024040c0e200d03001800032800184113509140002d51040321800e0248443d60385041020f8203020584011100c03a40d605466408001e014241c007020290449141591080144032181c2c0060781d031080310001030701c42b9407101318000d8150f090000400300031803102d407442030460703040e041c240c8000203080882002918068046d002115022150040707032103240f0b500400c1425030442056004030580d015100b0300c0e4020485d69030352804c1100d54403d14282900560000c2060700c103101c60500842c00c0c1140250111030410130669603 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 307364244 1250 307362994 307362997
    0x705090c03010501030f09080a0e060903120405030d020706090b0307111c020106120c0b07020a080f0604020108061c0b2703040e070c0c0b13050402130303030e031c0b1203 75
    0x56041080c400000140b0040d0f030184100d056028040004100050003583c41c2c1703a681c4600d80011042c0422a4070781000d550b81d003130490745803590140075120402803a8141002e25009030258038464018075000c5000d1302c0c40081c0880403200d59a44501010303251001e0314005500103030078042008441000401882410040f02d900100301c3c3c3c10182020450034002800c40300f054001014040c042c003103941c0420030441c814410388070b2100b4041c0d602c604a01c002664041140c0c40b01440c0e00921840c807040203030101d40d0600c558000e0701ea000e460303520b50301000301000a50500318607110310840c00c0000302e5418856680c0c44000c11500c42014250380d224103103026056011511a580009014049a5005650550405010300b8010085001952140c01c08803840c024145a4a400b003408a40e4840d41007054004000140c002c5603075581a0b00b480a017040d842c0402d50200341401e586072500c040c000120340640d00c2c0307000d40107444101041c0120152010b20b1030580d01a40e10109803060410900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 307365494 1250 307364244 307364251
    0x9060a090f0204050f090c060a1d0a030f0503030403080112030203070320160906080712060b01030b0409030809120301050d02060c1c05040602060603061014010207030c09150506030408090111070509 87
    0x7171001582e203002c5541a14101c901400303079001d60420b2089502c00c0d44c00158070507480190f804031000e1500c2003800700e402c2110580c000f0381401106410682400404001180074a010f5a103009440ea01c8120042403a0307a01c0030000c0060b8400c111550129100e402009100c21407210000c400c122002c800354a07009480301c0e852030102000b07008000041080c4039030001001c0705005004503030b04d403120f041d000758011000035260a4855004c002c05030302c650702911800c0c0006004000030403039410700400c1c010f41203c110a0a1092a81080d80d511540007602d040301e0700181228840c601907420701071a40c01c640f560081c076200300c0c1e0300c41e503121103c0c44841070540e09075030340e0a480e50310701440286400d02c090042030094010606004202d00f601c1e088005031010008808501681d03240100d16014043d44050000040a10041400a0560049106130121a00e0300e080140c0355030405c100e0748400d80b00180040c1080200c40b41e1540a0241500c03461079910a03034500e40c0d9a100458580719044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 307366744 1250 307365494 307365511
    0x8040905042102030a081e01060f032406110643080f0f0405030306060309100609021308011514010909051306050c03040201021b0a0b0c0105091509060a090f020405 72
    0x100304102440c0d40025102d5202c7c0c800703101c9950704c040c116a0400c0c8002c042c0031f00820424003111502000c1e000e40c004603e03030250501d07016140844100c408410b00458041e50000843c018030255021000240d024040c880c80c9400e00d0506206c2003a81ca4a00001c5801e104000c8207190065514044016403450381445a2540745151404005560325072000905d4030303103200c0f038174414031010404c0042625441032041c0d51842c0d032071711859203483c605201030170b400b4182c074100318001c501c1114030b40291408081421142000c69210041c481c2651a1004141c40c6462100380c104205030004030400118141818108561070f2901030502c1568012506a400d452505408104009843c8191640100204012421800c0c1640001e444070203100700440f0701d0b03040b0035000040b84d440c800c40314001c084c020b60305992014078010f854041e04040b60748240c240104005050280c001c070b8080c0744105180009441d0594400e41a800100342c071510030b076560541c3d407490600603100c80c841e25010301c039031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 307367994 1250 307366744 307366747
    0x90d021e010305010e100909020103270302120a021903030b0a0e090d0f1b050c03030706150522090609141609150302010c08130308041406070804090504210203 70
    0x30800250590320181d009260380c2c80b401007000041c5003401e03d018182c448041c00407480200b2400120f024000040c0240320040540e22021100c40fa076100a5610a109409a80c40500d80491182d058000c0c5103454015812017811041400c9803036174500e60346032280c2400508800001c0125042d0f080c00d4018251106031501804010351041000c40041d002500e00034005e150300110090426010309402048650203240050410105025001c90400050b04690303c5541c0c0c2d09061002d4218046949902802c42a0100d041e05205a01400d50300713081c0b20403105805022094001044488030507100243e50714100b1000600d4508400c0c0800301e00001810064508240110484116401701d55410318000d03034100c881808929107800c507a02402c018001e0304207410b08214600c5001d03080410070529840110070010540c0c050000d0f100b103840c038104c41c40c001c01c05026192094079006403c0724824042000720596a8102d26070003485120042c486103c41c401082003001c0100025002d41c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 307369244 1250 307367994 307368049
    0x60306150a0903060b0a0501050f0310081c08060d030215190227010801261c0503160e010c0b06030a120809100212060f0312071a1614090d02 62
    0x424003842d010b82c201164086c58140c41c080018280d840b42210044503c4000f100143d41038800026503c002c01c509401d946c4241003000e11901c880e46102c05003000301d01f000006c560306044c0204a2901150315800500c1d070036800100b401c0701180010452107442d24000644a500741040c000b42c10611200c0010b45000d03002c030342c00441c80c10029821030703041200c5c201c0100b20b40d000810b0500c800060702408400c4942c240d80d045802e05140c00b1200d01034140345000c1518007030b0b10100461107289201c00d00c00ca500c6c80302c04110381c140c15200c203032030014220311300d1000443d045120140e0007110090842d542007015a80d035840349000b0b00101c102266424040180c00755040c8845103080c03442c0002145803000f00501c4404101001d000c45001d00c0750302c108009291130800050040c3d84101110070b4580708646031890340522014001015074080001042902d10000165105140d46441e41510600031300d01801894010522081d4807010009102c0c0150300c90040012145c085420501080711 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 307370494 1250 307369244 307369253
    0x612150a111b0715210b03010212130605010b0703080408030612060405011a040e0312220606080c0619030b01142215021504020409080408010f1d0c060306150a0903 72
    0x107442000304400e00c0003801c6807129071a89405c00c0c03044801c20340c0b0006400a05000400e009018040c02c81c030b42620b212042c0100c00600341c3d03134201e040d031040c1014802683c0303583e407003a014000d4080040204400d500400c0c005040b042c09154000301c040c00c0710302000e05244e80c0c2071810304152002c0d5510b03550750a0000d074a01c0c6200f0204140501074405000001c010380500b0354038861040031040004031400802c80a0303400701614035420940f2885c0403002c0a00e03040401c000c0c0594801e4861a1003519102200c030306044007949c05e0b842900c1c49803a034203500c840040d4050410000013a04224400c4810100010100c000d0001c0d000a114060340002e0448802e2080c25031541040688201000310003502650004189644040c01c5e41d0b002d0b690b88071480401d0107007040304c2009281400206002c42d114505621139028030700e503600c06020021949134040c144034104180c01e81a0740044020300384605200c4021504480040c1940d510400c10141030034568005090590004014120400500 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 307371744 1250 307370494 307370519
    0x10090602070302071502070e0c0c07170d03180b04030e03160e0c040f061409030d1d0904020a05010e1c2a1d0a09020d0503030612150a111b07 62
    0x4150824075030b039421a05000c081d645440a1195000c980d4022000905c03402c6a00b02b0f0f60b1608a403a42254401d50310b814044907111480841b040851049604140c8468860300480c1da55050841050b80707500215108c031122501e00400a4050020300448102161010003280a40040f0075032403904480c01d0145840d209200a40034006c1820140f005119614050600c07208407505410400740c2c1c0080b80070549450300034910300c50780c103000c1c03e8089034101d5048a035200000d202c100f80e0382d03008000c000400840480507100690451002d03001444603500410002c001d40e040101400c0c07002840c0b00b041c61404401c07801c00c540801c404000d040742c01038003182150900300c5000c503209801d410310717440e0104041458942d40b20524171101054000d5003550105e00c03113580107406038103419001d007442aa81d0784166119070141d1944010b040c0b8aa0300802d01100040c0c80c1d0103020f01c0e0b516035402c020081c00340140c1c4801030303240822840c000c00369150301351424081c2c0000603060725072900c1ca00c80680d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 307372994 1250 307371744 307371749
    0x5011b051c060302090a0228030204060906020a05100f020904060b09010305070507120305070905030105160806040c0905360703050c030f160908010e0304030c120b0411031009060207030207 83
    0x1d160030035005100581c0ca4125055004281d40740042e203480b410710300c000702d640407880c03120a61050452404800d0350306800610940b070784c0d900c645000b0340e03523028102d1385e9542911001e491038002980c180c00b881103980100c55401c060324409414451031800103421105103034806845c0c008002a080d4045d60036000b142d60200f01800d00504003403e0742c0f80c0144032a00b202040082503650800610f88600a0f02e00402800c4060000c03c540c0c0b401080c0082e291082d1000c1c480171441c40e00c006192840d05019480500c1550381c2d0f001512860312090003030404100002500e00c1d0392071190044060103a8008404401d6011048074485c207002c0000b03400c64030050a03e8001c148200300704229682d103442078a4200d0031030380c020104280c020104840c0303041190041c030b9540d42000e06007503c16400201030400d41c2d004201c00c40055035900700c455214418401c0041100c2d41d12400500810351107022528021800b130151940f203a82503407410304076140c038207084070845c2d40851000140f56040240b40003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 307374100 1106 307372994 307373047
    0xa02090405100621020d1b03050a0b0a03030f030e0304080106080c190b0d0b0607030804260f07050c030a050705010f030203070509060705011b05 64
    0x1a61284025511403400d00020906140c11030342d000e0102d40880d26040c003c0009a80301c000d2610303101e0340e64030026509201c240001400c90281b00300b0140802102000400003150150456002a25080f0014a4001ca00b010340c1c64000070103054039014104840301403c2c00328110060f1200c5e030112140781c003001c900003c0001c01500458142d074513000540702c815110100f401000044c0b030340160054501c070102008803d032204010408814804000f00710029001c02149080c1d100c10012000035076141c0c200700a0000302d038140005c00c11070301c005019206010408004901070f54480d4031005030005043c40c1040001c10080c0b001c120040c040d203440780010300b0520388880741c41c0701e46da01044102050981d02d910030b1003100d1244080d900d81c00d0820020605001494000c000f003124070b596544168425040c40404210100c0c00701d1b9509660740301800d19000c240000c4031420070 = true := by decide +kernel

theorem cover : BRFrame.Cov 307194244 307374100 := by
  have h0 := BRFrame.cov_init 307194244
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 307194244 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 307194244 ≤ n) (h2 : n < 307374100) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
