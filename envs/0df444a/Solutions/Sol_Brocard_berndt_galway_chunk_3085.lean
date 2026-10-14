-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3085
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:36:49.532062+00:00
-- url     : https://prove2.me/submissions/c049f016-654b-4848-b95a-3673d9a11927

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 554676258 ≤ n < 554856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 554677508 1250 554676258 554676271
    0xb0406201605061612080105130504021c060603050d0e03100c05070809030a0606270506090711070902030c12070e0d11030307050f010203040323070312020d0c090302031b0a030803 79
    0x28480854000038883d003061249240705c6841c0d0803200d506100c10311540728480d41034a081d103494402403202686d10390307000d1586549210300b03098443c091b5184c600060b164541c0004c10710703c590701034a41d940342c02900003540c54a041e81241c038243c60030725083d000d07a400b00443c1070108070100b040f0804a003039080100900380000d802c86d000840300d503891034200c69007603201c29442105255403980c2d14294940d591207820040030b090005040000004142d25405455003091000c0d046081d01c46080a0040c0310051225032800c64076858554034548055002a02c2c080d007541d003400c00102e0b60750188400100e0b0b4100540211741c007054903980c0d24080807480d609141c0c540310902c180c200250302046520400e0099070005a100d08203887c0180501d14802400345c00c120307030364030030210f2082e181c0d090b03c480c183c0504d4100044001c0c1100c46009106043c480c0c1c51060038220a001c1d0990080c0449046a01c02d401301e8007104c1800320841200d41607030321541d41c040360880042005c2403c40d0702641e006007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 554678758 1250 554677508 554677537
    0x170301031709010e1002011e0608101a12060126030318030d020708040e07080402010f0e010e092d1608090102040506070c061b120c03090b040620160506 67
    0x40090313001039290350212802e000140c1d15074a040c501e2030360b501d459100984078030400b88907082c2400000350b150010365142404190b074484030b034161001c251081081c9564083c0c020402a4070840219449070b0090107071141c540760030103080400064444a40308082d482c01c0285003542c80301024059020540070076900b10f484184500030640c100e603c010440e0354490802183d403039140101642000300b00401c2101449115020040940d81014501003040c80c40c3c544240300c90b22440041c2c40110100c804039420030004020840e449002d03511150074502a0710161203010002501e4000ca0802121426a0031401c2100d14140b0b50244500301d411040d400005401c003501c070008a90207030400344040e40d10505503001082801e802503050a80841c0c0d10741c00290400c0ca80d21100c154120b4884460100442000341c0014180303c1c80c3c0c0c5101512403407002c20356840c0d480c2c1c002400340034540c09000079195800703048491406c2c0081c55400388250194061003541c0b520042140c1500542c0040c1500d4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 554680008 1250 554678758 554678777
    0x21603030807120f020409233c04031e0f110c0301090303150b04210224090a24031d0708211614121617030103170901 52
    0x43c07a40e01440b001815600e40068a03a454840e080060301d40d0005510032003080d05c550101d1065400509551050200c02c0b4a00f40070a108601d041e0400f1049441901c0c1e060700c0302062035201c00d0a86507018601a41d96411003500c1924035400c0040040841c001141700d00381030148107402094400c0104201d64240ca41e0b0825200c0428207668906600301c001943d0303441c008007019800d07400c403030142c11001c0c1803500b0141849140b45c50110350702401da041c254044145030455171071108924203040c00126518001e05001450780b0250400c5404920403102c000c0c0c0813500d10040c040c03c40c2032042c0824442501d211650081d4020310f44120031103540301e0b0361180306d81d072044100181c030000d20500d0000c102c80c4100020b0400b030f881101030010941d10080001030003c1a8109010792040e812940d01c0301350310b200017001442d20748807002c441c8020f5800304010040019200e03800403a03500811801c0210f0345003150340142c5200902009058211000e200e404085144026000410040c1440741e4072 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 554681258 1250 554680008 554680037
    0x1b06090b091008130c0e1006090b0405040f1803110c01020102070b06040c03150b0d14090a060c12060801090605010b0a05070303090503041701200f040608040f020d0b0108010c021603030807 83
    0x1400915000306c3d440d21005401e00190410200c90000209520b103448004c0b203040039180107082c03046205240c4542d4443c440140f50710425445009208841005428001ca007440d000c0c040803c285289111400303103a200e01540e5006000f01c41d00940c1c03140444109540305010440200a0403000a080582c0c8004000b1280c00d17296403640944010350903540c0350340c2100c0809058400500d81358150b07800313000501642d0240001c0055100d0392004000c220080c841c01c045400b100088043c8403098141b1030700050420303041d03020741e490601441c020f00580e81c0f2141e0751100340c800d030804c403800100108829004640302e6400301640c41c2c40380b001c2e030303103001c1d55a40d100c008880c9460000c8120795403034400038400032094912007680030380c280e422814554500b070b07035106901032845044244411000007030201300c00b0180306060b450b80180b2001e01049142001139a200742401400d400750310708041d0761800c17800000e8154401860000c1411044d086a40440340d114001d0080420300ca0b181045015 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 554682508 1250 554681258 554681273
    0x14090901150803192a110301181401150515070b15100207032312040905010f0f03050714010c0c03031809020309070b0702010c1b06090b09100813 64
    0x2020b00c2801140c07a00b0107a0000480740c0801d0744d0365800d01a803011003914640000040c05181440420300c0f103081006400c0c442d801c080301d580200e50651a0000e2a034184038400c4200084034050800d0300802614403544900b00d85980304081e155000203042045249000050254402c1e01d20003c10700b00310b456918420809411fa038001e14103007444a0041803410010313075201035280e062004000c5680f640e114440c00c04a8400300312200714008044c410950001c1040e8169810000b01c100e6480380d50b008040000c000a000b2165490fa822074000740c80b44c1c0740c94010081e00d41000203403890074034010804e2403040f400390505052220f44510301c40400d01d4118034000a6000340c90b0341d065102c4084001000d041d003500070300f103910320600610101c05030008009003a280480caa4a80c0c0707100500041e00c64150483c0028a590b900805010b001c0c25800102070131140c143d10745403a40341d1074043c4c01d200c9010b0070b00700c50b40283c125070303944000c0342c0702e69845a040820110425004919034691aa = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 554683758 1250 554682508 554682551
    0x312011509230f0103051b0a030e0601080102040608070203190513211721040503070c1401030609021809041e0b0609060105040305060411130e0105070e090114090901 73
    0x31024aa400300959442c10220f4410301c032110700f460208003503d0028000c16064440003050b081d806008205064498000d600040c1c02c6101082256119030791048000c0c080e6115008200c00112500045040c0d14000400e560006000c1c90441e0407000780448112060303041000700d14455101d040c07002842c2d1100d044149502c2c0900d40e034144160b041800c004038180d00072500d2016114041141c2e510084a081c100b003d41e605260500c5425140d07070820714a98001c180c0083d05903115990f0000c0d0b4400040040c405000303080c0c0301803045540d615910400c90040580b890300880d561602000c1c030b0324200d041c03668058442c101c00c40e49021910300211206121013003c86201c00018240411440d01103420b6500c51001d180551809056640390f60300c4900c0034100234220303108200c6421103031351150442a4510003583e420400b04001310b09090203008180c6001d000305045000179107150410401040c160f4400003450b42541c1805018000441c0c00140802c043d550703076814410414010b41c0307555 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 554685008 1250 554683758 554683799
    0xf0904020d0c030c2c04060312120b06090603010902031008072309090304170c041401150c12050724051806100302101205010e0108010e0312011509 65
    0x50380951182010f402c030f403d0598000180b26101101900310b144111031100309010740002107102122a0f004600500b1094000601d40840e0b0358000d41c41c0d69019112014862600c00244403020b42001030118500c50342d505650070680410051004407103d170020b50300190030158040d0740654400c80c543c00c041d480d4100c4000380032482041d90182d00152a96200008200e403200e5aa0401e0010180d0300d104a1103905280b040e140043c103000002484030414060000e4400d2111148400c0c0c2e954101381c5c240582560448206a140b490f540324101d260354040e48070703140e1400350916400980b0180c0254508503114a80c12b0380c0d00206101e50aa00b04c02003226031070108641c20710004e00071102605d440c071030046500a5003004402c2004000381c10882e901516020b6211031215811146040141440154030381820000903881e640700b94802d0403204404020000c2c2c07035030038202030b4407441658103804220b4120001841104801440200d25613041e00b001f190b8a40d4503090306592072000140b9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 554686258 1250 554685008 554685011
    0x80106090e0303060a0e09030417070501030f021204060e070504110c0f031213020414101e050d30091d070219051e101805120f0904020d 60
    0x4000c040801d02076100030207802400385086240084c085038141d42c2600c01c0e0101c0c0402c0c0004103402c1c0e101403080b180035141c5100380a4100c00125903060384c400040c0300715400682360440c20921002c03940b01340d540b01c0b0081a143c600b10380301d43d22040090030240d00c9075100390140141c009066a9107124030101c10702d004a0240d00c5010300f038072482c24400040d1003440507402c00c0dca00240d0705a801c51107980040d5544041c5a07845c0d05001190061100c0010808801c1050b01440011152103114904907a0203202491006010a03503d45000c60135105558124180c911540300282105a4a1440580c2c40c814247d04607074185500801904645502020401b40d020a000f4a82944142c0003800410712501c080360500004c000d5480b1145030000c510141200c10400c20050140080d9041507550000702c590001c081c03103100c1d15440400e4803074503032600d001c5207002c000c95008400307804940c2000c00741840c480c2100181000780d0203421904801c1e80c0812001c01603030b840340301a021401030b5200 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 554687508 1250 554686258 554686271
    0x150d08090319050c0a050102060714070f050307022115060303070605011214060f0c030a0e101d010506061603020a0507060807030e2a0a120b0402180403200c0a0801 72
    0x10500e0504c03944040c490300466282c0814081039800040d910340000451500181021420240800328000c0d03400c000d00c002c00f00c0c1604810300000001610459000f1907918120b1100900442500d03640302d03881c1ea40320741007a80b0a6104904024030313580e0002014094910308a802c7e6540e008070343e400d80140420000e6194904240080d1a81c406034503032440c0c006100301d0901d1840303402c07e818020014050003000000003000c440540d044002d22202c044102c4824440e000d09050140007800c00703040c80d64124080da24003032641406001d000709400340c407451030700b003445826025150b54400d05400303511034240140b0000314104511002401e00703607100461410101c07001003d5400b0309400c60040d50081240910300c40900c80070521070172224514000c03e040d5000840c03101e00c02c6900501d480151880103009202481c403034070707105038400c80715204a454649080c00b03085d24180c07005400107030510415074010001010a041c01c210081c1201c0e0002ca41900150804c0346581105005944a29 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 554688758 1250 554687508 554687513
    0x7080409051603020309190f050706030c030e07050a0b0915030903030a1a030c09100b0301090204030303061502072306070f050c0103060311060d150308070201090e150d08090319 78
    0x3040b208003001e061906502c2c40c10000b014030340c1c41503240e080c45440744081c2c42c0d0400300311582c0d4040344a01d9004d4241c0305580d40e42d00e4043c000f000045006000300b410510140e040345001300d003240030349400030326150700d241c2041a4903070f203034204240881d04070440c600d10341c0d01c8c8599080914403401090307004654901d01a030261041d00e000401d08000001e40308410345480e40e000c03851400703014054400040541ea454070141000311564881c100300c5c10700000120f070301d108640043c01568003e440a011050b591410702024a03240855040141c02c10001440b0740c0c981d10f541280f900c00c0340805c60150310900d5000034001c1d8070980c012182c07080340030146d0007086800e1000c400310003000d08080020130700d5138803074842e003040a20446101c4c25000030703090188155075011010103400003607050300c80c80e10303842c0902803a031054400381e0114505040c0024003004c0c51500c40e06ca80075002e807040d03d803808401400544121041c0840d070205060210310250f440422080c23102400e080c1c880440d096050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 554690008 1250 554688758 554688781
    0x3050c031219080601140409150803033d121a091216121121070609062405120304050603042607060e0d0206060f04110708040905 57
    0x160a5a04002020310580c818628200c0c0c0c1c0740702035116403d002c4010b61300c640048601000c00c0d081810780c1880881c0110702c8900640c403100d6240ca641c00f4000225454001c0259a40400ca0f10407250000d01401800c3d0034045582c1080c01004100007440c282c5020a1099040c4056410a020252181e081c1f40280a4034013070561b20000d5401910f00d640c10140030300c548a1400046090032090005502806040c5406940c1140b64001603c80300b04040101c1c001c00080e00b06040f000c081c40f0b20703c0040c050301d03150030b54640d4000031840b0749403510f68150b4408015221004080c0d4116660704401c0700100c10b4400910035500c140c0c400500c000e41001c0400139081c200c66808a601d51062005002c245c54400c2100e40042d040031104414030032042d1040c040c0c1d021146003a0400c60041260020031040e60030203403860301d04006490b1014102103040b60744460866010764464070a144c4a540c0381440da01885124040d11a8503107010072648440061b80c0c817a600c2450001e55030b504118594240 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 554691258 1250 554690008 554690023
    0x6180a0c14010f0c0506010501360303120c0e0d0302240a060801050103050309011404030501110d0608010e0d080717040507050306010e040c0509070302040305100609180309180b060403050c03 84
    0x590410382c4d0200c03100c0c3c0312581d440704140202418041403240c40224203403c0c03940c00c00700c0300c9400c800c030242d2000350580c0c0b00008400d200450110b102207100c00d40c1e000940c02100710790141a990740f82015001c004101000844807070903025402001040c4100c55a807541d407900b61240810103084a0400014500841d800b680c8a062642d260400600000313902004035202082c0c2480c0421230080b940c5480c6e1058843c0342e0000300701e580303000303620004581c001c00541500495200e04006199035451682cac2a50000381069445401c442601e25a21b80581e44103078000c0003038501299920a00480c21001034800d0301c0948195101003420001c40c40d04222160140201e070603071491a04103907403910400c02d00c43c018248500c10303c00c00600c583d440782d819034004540101c1144c0d040d600d1039a00c14018601405107252503401d0080c04ca41078140b02003000300e10f644c5542d44c040c00c43d10388003845c0b01452410710241c45254441c143c1404543c1e4140240c8007660203103000d88815000700b8101484c0c0000c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 554692508 1250 554691258 554691287
    0xf07110d0803101e0b04090b0a0e0109090c1a090118121a010b09010804030c0222020702030c03070b0d021305030d0224042a030605090c13050906180a0c1401 69
    0x1302d00f0b082c0f21080303045090302d0403a24030040204072040c00e440020851283d40d00030582d1a08600b0000071540041d07001203410317034000e0028261241c1c03944005149409000301c814010141008502da00e544104601840c82e00d04800103419942c880805444003c6610307000e42c1da08544551140244a16025050041440340c11803864071888c10006031005d40024000750500118000350010754860f10230303141060000742001c4074465540400c86c4001c0d04603c0c42a4002e11864205400a0800007004019900045205801c11a001c0c0e00e200180d8003040807605d40d54490303040000c00303031802c00a02c0c40880054001c0c00b9040600b1000c0d6410501c51070482410201c05c07400e01000c640265183d2806a204100c00305040b2140301110140d10125440101107034a0300c81000001ca0000c40c1c941b15801007103030030b980075983c042d0b95881540d10980e10700001e90080c0c00440d484003410806001c60039200750580c0d505c081c0a49a00f411425071394040d42c00c12403050740d904010740e030103099000d0600 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 554693758 1250 554692508 554692559
    0x150e0906010c2301050c031609060818010902030d051215060406030207051e10150e1602070812030105041d0d030b06042301080105060f07110d080310 66
    0x2500c140000c200402c1038001070450700c0d20350007480c0c03406022030b2201c0a8a20b810003d0209040c00e1001314003d034012200142c08541001020000904c500382c41c03c2251426580c00303000d6150b49120310030100075a004401c00c1d40d6108504001610309202c0c40c032104501c0d4440d1a1540e01c01414801d40304002030100042c11200d00c5a10201d64a540a41c0d013641c07100c1c580161610304c68a41240341c0a214070314401c0c1045041d4080112400010b1043c40002c2d2040c01030004210090b6800034218040c05200600500314000401c420030380072101f6135034007491045034480c681d500d00d468100a0a52840404490004014807060806020303107803085580f0382c1d03211059114000103a80300c1c0c401c0c0110724101921405210752650340c0c1d4054502901c4172000104000d211032280043d05010010014003040c0c41c1c800010b802d1070400c040d2080c40100c2d01100780b0b0b1018a50741c0b041104060075410354048901080400420441d6014500c62011304a84606075410100c9455002c0515003120713190301c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 554695008 1250 554693758 554693761
    0xe03121302092206050a02120f0105040c030e0a0204150b161109060f01180b0c1f1503030503060604030b0a0212060306100614071b0603050a02090901060c0f0507150e09 74
    0xf020100100e060160802400500c0da1170b014403c0010b44181c0207000c04110911052082d400e6400f0903207412540102c40c20003a8020485058080d03d01c0962400c1d0b60341c00080d00c0b4005400c00d5000500320207002942c0145280d01da584612a0350040c81040700c000540e002100304204d004070050300e002d0002c40380b0009e14944000014103078000458064100407140000c155214035405400010740070303190095440d042481c0300d0703655405000320038614484154601c0c40c03410400b44a412545982800102c10f030900303540307040d135980d40080c160641051040bc400408074444010250081c00219405a6142403005051051510140446220b604400144001000c4240d03904040b0b4646051203070030858022100b600c0f40c0150301010301a0070b103c01c00b000c07020414030807103401d80b0700c1601d04000e503440e10701d03800f022030040c0801c0c140c0000003440184042c502441102c2400e078802d1410b0a04003041c0c0d40c40600f00b084951109510581030100e0050860f0070410b04401100b0031303146200395 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 554696258 1250 554695008 554695051
    0x51207020d150f0501060f090e130807080409050a0905010f1406151603081e01060906081302030d030b03070504025202010e04020a0806040e0312130209 67
    0x10740e840307007500510450000300a404074050340e0300300c1000c110072810b0400035980d5450b009011614580e205000141a201c03020070705040d0110014050340b00200d150306101030581d61040c403035200342010345250005010000d030020341806150721540d83e41e44041490751052910304e0954034001000024a07042c12404148401c40d0900c00c2d1380003078121282c0402106d074407001c0c8024440c0501212001c0c2101040c04181500700340b9150240380e24480d2001030081d00884010403903801c0c0079040c0007074543e007800c010940c49090180c0c1c102d682808030070078803a5254002460010300d030540304003003512139a54840a207802c3c0010001480186c038250b00c1c091039030200b107100c0041a06031488048002854401814046090240c6070200030005010749018221801c604021303003400b2030001d85024075000c4641014000e80d07155050944902c482615104204405050b80c0902217001344414060342410380e03245002d8034003407490251518000286030050100100380103002241c0c21980d11104d010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 554697508 1250 554696258 554696269
    0x8061f1e05031302010f11100608070e0106050703050306011106040c090b1002070302060706090212070905060f0d17130920040f030b0403120603030e03060a0e070501050d14090a05120702 82
    0x1803943e0900e01b040b4500c1080314261210856001807000c43d2040c04201c03001e020543c0e10a209440e0014212030905644100c40e600c0401d00b4007803440000c400f440000c001034010360145803c1441410100718006510340e2807403030f01d10129000d80302d0301182c00c03080105034841e208080301c2400541e1203018074007408a0207941c0e034929101c02070003a800010043e0500c85103610400d81664014040d001440c6648001940c910840c01070300c0040740350001240040c0b50003030700d42c7c3c0056005018080c2c284429110b40c6c2c0111300c800b071080c1c0c2681c001c02450342d405030a540d42001500403000000750299003810903c4ca205541e464450b108842000180490145007400004a944c02442e40348240d0f034501d812501c440c80f004c10703d141181410008000c042c1c00c42c001d10400101982121139035684c50502500b99940118248d5464010b004140102e51041008182030358030908003140380000d001c18054061011034480c80d031030304000702500400600b40020441c070b40103d41c0180c1824650340000b072 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 554698758 1250 554697508 554697541
    0x41202012d0b041503050c040c1d03070504230c1204080c0106050301060905010e070305010f14040e0d0806031002030421020f0a050709061e0608061f1e0503 69
    0x74040412951008481d4800b42c02100d94814003074001e0109004441a41001c1c0e100c0d400101c2d005d010350441c0241c2d50901303118000070164a90360741800e446030382e4912001400d0f01c00040303400d03000c0d00e900402d481c0c0302e50080400c0300c0410003c100078250308101d40010708102070007424010350100f02180322013003401007481e040307500100c070290749601e6024070301d006010a60041d81c16509001c0005000001984018100d440984012840307656001089048520901a078803150141034020701c60101903000c00c04080602030030010b0a0342c3c107111300c036284c010910005000500e44400300212800d040c810b207903511224103001d50550801c0c0c2e0381d0221082042007400c00700500d984800d00d12610030812522518040340a66101e9025410120303143d0302d0300c3c000d826600d42455000103001201e8850170b00f10100101105001d181040d004884500c800380c205503104480d0b0341c007078140c06084407480c4010580c1d0349451758041c0c50003001e4254048039a40c0e00301808018020001800d1890801030b = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 554700008 1250 554698758 554698811
    0x10e0a200316120303050703020910051606061e081603110109030f031812021305060f060408032a0615130f0203041b03020d080310050d0b04120201 65
    0xc2695500350003107840d01c20401040388050990308800a040420070030a403404501030380c1c081c0709580c0d45110a0302a03114041810b40c00111300c41d40d00070b0242c42500548081117032030b84030250042d4980c441c801a541e694100c0a049000c03168642c0030410700300d0b5008010aa1800a000c5030074400240c034441c82958070025000010620042c0d00c982e208045120103180c2c4410301030155601820000c1c1844c4291085843d145020304001c560340b03000c003040e0003070380d41e000307080c2d103410525201c4802c050030029060a0f00804003a01940e17860307803040068030103440305800031511143e2150b0700114001a50a58866803c06101d0075204944085411984458501811000005104003040b1032190700201000940d19049200d0b40480c0243c004500907402140b1420000140d4001d00d4100c1c04123100003580a2a4074003400d0001d003034040550390000b11084041596540c1d8400f00b03540050300311007101c4012406041204107c46006541d0302d070300c80d0b403008009a21140c84d81004003000341591 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 554701258 1250 554700008 554700053
    0xa0c05040b090604230a05030309150c0304091103090d0302030610050901270302010e060301061b1b0303030501061805010503010b072306040c0602060907120230010e0a 74
    0x2451201e44030801101c0040180d1400c054022075100c05e14420896840c480c01e01c030700d9500a0004251800005407205244000e00e4108145070401443c4a680d1100080e80e00e580414000020104d61910607110803210548140c0c0e03491510034690360402c903c1c0250102170500c18002c3c8044c585407000c0c0301e8041491414456503600302080140d07440a04030a8039824450408980d89803404c41c05c10620489101b88c0790081030505150810505010902410001455100003202c0039903d421400c2ca081d0701500040c52608400d0410102d030b00140d4105401007503d0320010030005d80d002c8400341200e200c4002c043c2c0007605000c0000c00e144010b00c50000b10f40c8012030500e0a014140d100c59140c090780100045609865000707403511441c0480e0f080e070305858484800150140003140b80da115441350340240c084281017204460002550500a070f0300b000c0203a06841d410250000303084228010315041d00026008000d00b2400d44102404240c5190444505040001c2d01c500c1e1007041c03403044464 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 554702508 1250 554701258 554701267
    0x2040203040614040606051003020c0d0807050c070608060909030a020c0f0a270e030c060112080408010e0703060606020a0b0103060914120d0605041e050a0b10030e060a0c05040b 78
    0x20542d02a0007200040c0d512491140e00f40f0082181951294080360300945040c141ca4170128010740490045841070407079500401c1010301a14442d12045910505d075003811400c16089003841032a01440340c00000c00704865500740701407840e146c1200d90f07024500b0b2000b145015540c403c000c0d211030b07074121082d0040440102c50700295a581c900100580201000607100b4651160700885d01d07103143d01540703082450030f1404402643e0210403587d02000d91070082c00164600fa1800c140c44101d10025905104280004100d4280a000d500c002da01240d0090500e1411802d04030100c03981580040c055602000414002a410b601101d044a80240d030014000840e42040c4035103842c04404240e5a00640c0411404642c3c01c90141c101c001d4100e50070044a6100d0043c0412150409661482c400e60000d50708818a00d1341c00141d403101c900d80e40031030941e0301d500105040f018181c1c01c0c8000b00781c4503100407001d080d00b008290303445003014005000a440400c1e0240545c495801103144003480081c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 554703758 1250 554702508 554702513
    0x7080a4508010c0215070801030c060c020409020603090c03070602010c09050f030a050706021501050d0305070f2a2c040201180b120609130b130c082d010603030c0204020304 76
    0x610503008001c204001e100f01d03900b03400000e458000c510302d0410701c840010082203003c5e1241407140c1c103136030744403c4500400b400c0c24019641c104091404aa1158441400f41c0040c1c40d8000034602500040700108403203101d02041504203c4503800800440e8584410a400700381d004880c0401c0f114181c4005614110120100742010700c0c1d894080c2503441945000500540d001945501c0c081040109206136601c490410110311003160025002030f6045c002100031821092820031100d01c10b205d40c1c8000390700c1742844031f8080440341c030b2002c0302064507804002c9444082c9141c020504c0314403404a00b2102030303042044100b80540081d04004c036800d6034989803078140c4e540e0400b424040c40c00f240c407440020031012107168201c81c400d0090241401041d00101c074481c0b01080c40d03074407030401d440790369403441400041400414192184100d403403001800c55018050008001543d0000e401920b00303042040c901c0400e05114244546e24201c410404079600041c0d0a0b1001ea04540140c2d6a031180e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 554705008 1250 554703758 554703887
    0x10050411041503080f13060f0206070e0105132c040c27020409061a0306030d050918010905060a06081005060703050c030d0b09240603040204090807080a 67
    0x5030401801048002a4103000d100030038081c203861b4800030f04000326562290411548045070342c0030000980e1040003c0b82409009420425040c0343c185001d81c1089040c291040052280d9440020000302c0308040b1107204002035241ca0710100d40e4070b0000d019003016a501178500045104608a00080c0c100c41c3c3d144080c1300c0103442500200450640d11a5103e42c070007002000329200d042d424032100c0c3c050005a03d40c14066a118070310080151031000503400055805611258040d54844941d0102403170241c00303038903954081c0c9a66900024203140c03641c18043d080d0481d400c00d0301400601070822401035921034804040e00c0c4242c1e20b0b6520360b00c1c18a026595800748040c41c40c000c2c000414130b40e82084556026203035152045848801c180c40790b4284e480c0d03c0c1051a5205615150043d07100300c141001401540c201e44060400100300541c1d4440340b015410910088944903000240c80051a0384031503070b100d42048030035200303489000e001d1640c1d00382100d480702c589021250780460500030409 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 554706258 1250 554705008 554705051
    0x10f1208070f12021b04110d0c030f06060914040b091815090a05070b1c0b03070902120a110f0306010e0d0803070201150b040506071b261005041104 65
    0x3c3d8088100006640019449184242010313003d1030030301d112160f035072800c2e000310082d14205822107490070454070301150103014190441c805044d00ca210507aa1a145441440001e01da0b40e50f50001d810308050010709603d0001034642c0c40f0303a0500d0141086590f641c0e0314075411001c80e007407000822103c040c07011b0030407400480c900780d01050314080002102010883c0d5000d1442882601c0c111034032012000b030940200e92004900c042ca200d200c40c4000f80d5640078486281008080310300b00e940d00c10001081c0da00c00c0e420030806424010070f1200031401c5e070046141010351a40a40d040c56064018400c05000003004141040b01d000300492081c1c807004a440c0c0300607040255590f40317260483c0080e0103018500308908038221142000240b41b4828025101620b000a080c5072500d183d58588001c014120840708005004040e4005402002408604280820196160740c00c1c0d000c035001504040c12003c0003000d880c104401c220000d00989902e901c403c04c100e40001e4002580391050561414 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 554707508 1250 554706258 554706263
    0x708190903020301060f140405040507140d1b03030215010303170c1303030e012706140f0a0f0e011803080a05041805010519030305030703023f010f1208070f 69
    0x191440109103441039122120940b00c0350405c07c02c24043c40c005210488004580182860b0024041400300c00c1420a02261801e4000c10341c80340c12038280c42c2d481c07040c0c44000710303180c4108160404104054041c0706120b0517034003104842c882c96145440c040d149000500c0d0100703008905000055038420100141d0386118034210b20000c520f03844e07190150002c0390180c841e90103d145501c0c2080d03401e03900001c1c075240981341c8810149040c0362410681e0b1059081040ba803240009010400c41160310a02500c00300059540301c581d101440301d00a403005081c1d000042c10040610180e4601b1070b03031125417038120f030361001c0311555803941030200701d4460085030003400131500c2ca180c0704228810541c2040d4140c84045500c10380d1646144007030300c0790129511000700811418000151884e0096001e0403030b01c100d0f82c0c1554012840012214807003030641900401c08605140c10004050380d0300c081030b01400480385030701e018178106020103145142d114001003041d24001000020807005441765070107d0b6 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 554708758 1250 554707508 554707511
    0xa0f020f0a03050708061c0f020d12180e090a030f110a0c1505120f0a061503201e070503040f030c08010b0607120e010c050f030a03110708190903020301 67
    0x30341100007000f910060341c0040004003036201050007854481c0788640284040d001c40c107210415941d4a44508003506010303a0701c00d0404051501181c40e286a24070084081d68502c0c440f41804079100b810010380d504400c10b08181403003000400d0318006800c1c2808ac2d05402d010180c403c01c0c240c100c510001c0e01012990b030f4080c0d060380b82c0402c00201d84000c15100070044041c509800c07140115502d01644445541c045505400b017203c4045400c0a680c12011000d4042440c540b100e03050358000001c46050b400096135011380c02c0c0801402e1680d41d844e002900360062824651010020100c031905511360081c0000143c0301c01000700801c219802030140c6404500300d0f65a900303000309181d0300c5118900d030039400c15050000301d1801204440c1816440342c6003000c80180600200d80b22382ea22000b8034140301600c80d001e00031031010003122035241c0d16000119a915031588c8000d041d200288814801c005052211100155452042c0c03400f0740d6414031040a661084442120001e18950001c0e4065 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 554710008 1250 554708758 554708767
    0x512070c140a1e061d0607020108180105250207081f0b030f0705190f151101110406200a110102100e03090109051804060b010e0301140702060c120a0f020f 68
    0x31140340162800711004c1da04c603908400720b00041c0402480d4210b0b6070aa0100040040700019800b136210b0a4005140c410000f69814091410301c1c21100d042d1401a804035845455103981480240e1509812006101070083c041c0303025403060790341020040426060304031040407040d078003031640300e164550b40007000c9070710001c901040c0c1c07074070750500380a0305010742c0a109102c8210810405000201c3d11040440308000d0b2814949100501810172240c04208000c078149510031700901a14240c072800e41d2049a58920b02030f0042d101540360082c0c0e019a441d241e000006000000c52543c107044c1e000794060641c10b1800c40100c0c184001c8503500300c5020b15102203d0302e00344c00000681b040300020380700d5200082e1900208040c90510804c03442400314040005000078065400c02c01c10840d040c10040b000c214242e0010b403d42e18401308012008101e80c0801c100c2e07d60400402da000855101d0040c0380420000c030640c2108401011036442079100c0100419840301c6604943c0c2403c603218901d91203 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 554711258 1250 554710008 554710049
    0x40209031e01290d02131518090f1e171207030603081b010b040f0e07120305030f060a0b0d1416230d0c0c0512070c140a 53
    0x200740300c10110780d120358640480000e1840c00100d4542280c0351443d20b401000c0114020080103266056089820045104103817020550900444c003100c50008802c50000b420901162420b00951755440045401c05d99030b4404a240312808911098000004040c4800d010586104400c40048000e204001d4002290042210310002c0c0080e41200280b040300394984400403410703a8014040908420000c20000300c1040d9a10050100b81c4080000450780707510200014080754042100369003c82d4076103208040800b414080000644006030441a0b0b00c0b00e80c1e1401440c50200074100400021803101046d09591a008618014558000180e0b51040d202c0003d002030103895400e0600c42c071600c0045a4401c43c01c5140384009011580d030420a0003d0412004c050209510403200083d42000079451550081c02240c22400c00c2d0b0722903c030084245e20f401e0340750080507030302241c0610003031101800040d2556000002c40308407150008001000c0c50008008440c0366201242c0600c066062050 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 554712508 1250 554711258 554711293
    0xd020c07050315190501260c030303070504060305011d13060603020405040305040801140702030d0c140c0109030914030c01080601360b0f040902070503040b070602070c0b09130b04020903 82
    0x1013546490860000403a01202e4401030390028003682004035541e00b289140d160146900c1181c0744206003c68000084a40200f8195401500d00100068000500303100540c0c150207a81d00600c2e40c011590744202000c69003050403a80601007a4060750800c8030300060048540040016680080c0200120705180c60042e100f81e0052040540550038216079a500003500082548501400d8018500e07105260100e00e0090150307990140600280c103070030560364120f0038003070070303021076440000140f100d80e9040c0540400280c4e0321403400e00d015400c600c1e070305890100d030140703c1640c00c1c20452843e44503000181c0f03051141c8640504040140d83c02066907600d910040440000745089485c03000d6201d401c141c0180c803c02d041e400960001f04800c020056084e40200991400742c000d607418151980382c04c2009502408003695100e4001c41c810052045100c115402081c0548c1d803039140c40c00300320100d040c84070f21400101c0e03602e03a07900b800301603510395404654110030000c003a0b03680c080c50b520107491b = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 554713758 1250 554712508 554712511
    0x30304030320282d170c03070314070219030905061207030b010507021e0607080a11100e060a050c13030c0e060f150304170313030e0103050601050d020c07050315 71
    0x500741914109004100b4026001c00c0c24015070f852004180c5013640d009030b00030900d10080203080001007584a5005901c1402150040003144c941603620f050116005007607403580300c5000590012081801400d54000a91070a465881d044200e164900c600342a540c0e034581e0740c0200e80100c0b0001c2c446c9018403001d18064840c5c640c1da00d08005504405004403418003070a000250080b080d10110095498034030750341844204000c00c07152402203544d1b1191606e400420180d0081480340a444061b035001748400442c100356040200850031403801c1c00c40d6908c03030150804145540e05c03004103500242a2040720b07421600038031051034083d42c07854070000001c5070384140404505410041746103440d00c2d00704030321507040007010943c01000186001100341d0002d40b0031903058195112240041c0308450146101e00355840c0326000611007400c0242040c6490328800b03042501c0c080c10030002c2d1b81c008080c1c0c0c030000a403e50060302c2d5034140e20100d10385909500103590500c49c40381b001142210500345039 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 554715008 1250 554713758 554713807
    0xf07030302340b0925060e15070b070924021006080616020a0f030903110102120f0702150403050109140a05031207170103121808030304030320 63
    0x5010300c4080c661060401042c910004011404854000d000c110742c0300e074443d00300b80510305541080d001c405900b4000290030310b100b500b04000746020000c80b50844540ca18600c0c007650403031400383c81603c84050f28487d440303004044801d5100420081c84c403400d0240c014103080c45140074220038180e050b55003140f19074040001845060051601c103012400703140c040324000c9008045076100c0a591204d8036441c0d0580781d04502c6804039400200e02100090728001e4008e4131745040c2c16046050846038a000c0c00c101d40e055510041001041781e003a8011102c0342ca4016020755291581ea100055002c103102d0000b05000c1c50204000c0240325065100d10341d2280302c6e10f0071030446c04400409075242c0d040160702902c40e4006001030307030380003041015051b0702c000c0a1518200c02c1d14000e6182c2150642a001170318a4061007048001e629048280075028030714001603030301c0152500290f1a9a031000610050401d81c450489042020039181c441011114030b50000340c603003802c800c030502a00c84d200340d01d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 554716258 1250 554715008 554715037
    0x30703060f0e03070f030e130501290703021507020a020301050a0608010501081209090c09120a11010207300503220504020f0304020d02030c0d03030f0e01050c0d09080f07030302 78
    0x40003640300b0000444a9060340404400800d01c0d0a0f10f05803501540811450f030400010180d20319a00c1c803034414680a00780140c41c2c121400c00c0d5092145400c0aa6042c000440c1001c0003024003003500010603006440170782415507980d5466041c200e080c91a41c1c03400941540c00c0c0810710070b561205800ca03c06840e1900000c2080f80e0380c42c84929a10144410340c0070007603000300000415420202e0640d41d00032400081145444060b5000c2410840c04504070764103034010b6007200042052004100c85c000784244003c00526061000e0030400c04200e0b080c84240012001c1d50446402580903224051500041900e071181d1214140f00350134821414618a1200381010205132890644250b4503c80544040a421503036281c1c2480007218a001059a0500ca2030704026001d6440030314400500b48217a0340401c2d9403404004030000c2e40e002c00d80c00c1d44141d051804200d610701800040d00d0380c2c131400d003502003003882c56400c0c50789041c400d0480c1511410300010781842856010380040c070400340540c50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 554717508 1250 554716258 554716271
    0x300204120506011d06060315040b12060f010501051905030405010e0706020706090603090b010512010b03030a03021e0315090703090b0c030412020f0303130305040902030411030609010c0c020d03030b030703060f 92
    0x4a40c00b088175090f03400701c000c1c40417034451620038000440040b005800015101ca01e0340010752040b5103507442091a500103410002c501d810301d01c0c035070b00501c028200b03d400c0030b040c4c8030003082840c502c951140c00c00c80040009028418250000721070001040191101c09844400094036880240a5680070405a40002603010711074450146d80c29000809040142d0800d0108040d400c504400c100166490b01c450302c85959061000b01030544003503e005035540e01840c02c103801451078044c012070441050041003040100e91010003041d0074215070a140c02d40c1d411105500130301e406400a84140c07881c00070840303280001002913005074040c190340302060302d000f0012640ca0202d88401007080e0001d0010400ea00e41e80300c03040300424813030701b003890801d6226030b07404049070002c4074151a1048102e100103c10301782071080c070f034004105074001e0101e4401908060725402c480ba60090203070f0020403a0b402498429402032001040080c107445c01c040d070382d09082014281c11105030004528015 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 554718758 1250 554717508 554717549
    0xd021c0905132903030403060504020613080115081c03050c0d02030a0504150c0f11010608030d02040306061e03110609091305010c0905030606040e010204050a061e30020412050601 79
    0x2203426540b0070013401103140a06642d00c107405410007400403a00444280035020030070000492132405411654000200301c01007600d003c40c0300360a50301c14081d80d08039005541c903003130403182070b000340c1601c40c00c01213059182c101d902103e07803041c110010b1a0030310120038040400540e41202c2d010b5030040340b03100c1c58014207441c2c95044840a52004000c43e0303000342501c20b25402510303440700c488071100001840c107a442510504541c090300a00711000d50005050040007428030405021340803241c807481182d1a0300703500d034403c0010ba01002c0e185032640c40d40040a07079106c100719402c00c0070140c15520f441c1040c888503540382c014801d040360994205202050000c0c8501000d400325440100142002d403240c605010050100d100010119502000080f800303440c2c1845a4004215640e520410841444103a02e01126400002030820609080c80c032113423040c0c0c80400d107084e603000c082007081c070034401c0c0004000d10980d4414412150214885030a111001c40c11074104c40c50880c01c60542042c02c0c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 554720008 1250 554718758 554718821
    0x80d050c0d0504120b040302100911240301061133092a030a0b0708040c0b1303020f03100c0908061e07120b1801031101020d021c090513 60
    0x60103100d40c41c3c0740b46004140442c4078001106c0c1c005000340141c400c003454801e007403800e40340d0030303403042d04d9a40082158000b80e042010018820845030080b20310004c480c80d8084e4881c1c0f1045c40b070f500c20060b50003211130380d91b00c023404140c20031000c01ca121105c0822a107405005090f0350600342c414008010700140540002064404902a0020b000803c0c00448c24489200c8202c002007035070144076000d40a000140d1440c400c0380211159260390742c4600c0d043c0b80101d1000401d030880e8414800030300000103076144c20840c200543e5070440b071008030508400c012030b00d40317205400e0f0684100d0925101c2e400c6103800c900880151086036042c1c3d6065a201d50b40368156824a00440450051250000322564864104040007001d4104007080805d1007800003a048428200141980d049400040040201c2035803201e003080020300291a094440d030001075281c040e926084030300c2d04d01e80b2002190b4a4403403031072240506402000c4c10042e0042e01b40000040110140100c0394074005500b03202e00500c003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 554721258 1250 554720008 554720017
    0x60503070603020f0c0304300201020712080d0c033314130c0302030a0e010c0915020f0307150e071a180405071d0d0506010e070504080d050c0d05 64
    0x1a0040c202145400030460080d8404412140704070405c1c40b04451008003030008000800030b40144031740721030f140100114100c8070340701030102202d440b201490042c1d0b00494141e04440c18030143c2c009050540c00c1007100c1e8482d0000500c0762526041c14414041d406a02042442c010200701048180603d1410303580202c605001c01c5500e803e0820400180c4003c12180e48285401b801d0028002c01b8a04818141c1d2280ea03855404a9000700030405046458820406c00220040007881030f0591448040c200002c6c0b4003504030454208601903070064001c003c441c0d141d414a0080701c0d501c4010341800c084a44d01c0700c0384410228180b48a00d0b020030b400007901000d8881d0b4282c91015000e1f004011b00c0a40e0020170390764481040b40103880040da40e14450203101e0b440300d40701c5888a107010000329080b00740035040b240c4036906c07040042c0c2c081040000c13410705607900c5066610642e11107041c2510360b4040d40cbd104a085118102080243d1a8030001502102110000b101d030708040c030500c20b0300c80c0d004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 554722508 1250 554721258 554721269
    0x1a0f07090504110d020f0f04120308100308180a1703120702060601090605300609090715111c1d0102120f2b02040501020f0f06040b0405071e050f0406 66
    0x20901a480030703880241e0040c10044050900e1b1840c0142c580045080f580003641b0001c3d090702d00f10342040515400c6929641d01ca44181a465501415a5500e0220b8051002e40b810202c80c1a00002d49a4444200b007102802e00d0007a82e0140101041c0001d40d00d501003e0ba0b41e07102c0c4500404204c150380000740045c045e100503158101c42c2030404c034046640703411500c0580e00e04440b42500754020550001c01c4241400118003804076840c2030800e10941201c05001c00c0c590303038402c05040154800c6001115801c0e0200c0c41c10b110b0304c105401c0c12624040d140a541c2403d10704018020300b026410008a81d002c000f0b80e4442242c110f0f0010059841c0d8082510100041500b04184103514503150010034900b905a48441d110b01109420031156007021503001403007550024042c84150380410800380c1c00803940d030041c600503840701c6106482e91170140009169480940105003085410300001002d03001c134803d1045021b440101a4039514010310442d401524004903404550515003c1ca40c103540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 554723758 1250 554722508 554722541
    0xa0b0c0115080d11011401150f02060c09041503060e1f0b010203030a0e16180f06050607020907050d0e030307090b03130b0a06080a05030403020307061e05071a0f07090504 75
    0xc4020382c0a0340c202c130340808107950075581c40e82c04884004170080d0040c0641000100c0221039104041d015103c0c0b00b50080d03123001d45d8400c004000e280318000e01155400c6806540204550041e02c20b241d84928030b507040100340a0030310182903130074400001d55904144003400c800001d440581100070481d402d2506050040c1c00800000d48450019080340700062580e0b03044400080c500c030744001fa1000d00b5000000c0c82c210030220822900414042c0f801c21480c0490704100d09490580012400d10804100030301804941000070030b25030081044c3d407003c1d556906d080c402c3e186a810803a480754011507465001c00c10b140720210307041e255042640d100d8251001490501ca070507440d0b04810240090211201c0d980303515001c95851410702501205601c1b41d001151a035082d0300c10141407401c250003c1c0304002c02c1c1220142e0039038081380c02e003000c4003c80c24030070b0350303586103007020034400c40f2251b12080009810b02c1404030214600e011103200c1e81444ea219481c4c02d13182c0c01008103854400e1b584034202c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 554725008 1250 554723758 554723773
    0x60f040611430507050a06091413090b0403090509150306040f02150c07140d0309060c05030d11190807020a11120a050607030615140304030903020a0b0c011508 70
    0x30001d0b60441c2d2080c04010424001088801150540c140360314219859040480200054108454480050026414850011810407030103d00c00d42c0d05406480c0f042c1014042c440c418611503200c044030a4010390400c045190a00b400343c1941002d10a150050303440c4000620f000501541102c04000f00a000d02115142c03515084610349080030103a078000c0002000e41d0320003443c00014007400c0c4140c000f030407400d894101d51280019840100078000d400c3d4554080001e0340c0482c07120240c0b80300d0300b0080ca00c20443d081852550240411a00c20640f81c6040d010b0401c403c00090401c0c0381103c0160b00d90800d00920440301c03004207680c0e810269100501e200009094502c09001102c030217000305c41668024a08070f8940840601c056401e07420441c180045d155141c004c24018203100384907a051b035011002e004010f4210300d00348403050701000c4042410140b08902c08401950000c2070098142c0d101e08121215a10201c00801c0365031800411540c04004400702c030342120703000340180040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 554726258 1250 554725008 554725057
    0xa09081612050f0714040f18080307030b04020301170606030a110607080903100204210201021b0d020a03030f0201140c03040209180f010626120a0908060f040611 71
    0x14014001e0440341406110b41100c44503900300320080082c405408002d40b40c96911050004403604041c0d0141828140803281c042000c1da80440d2001c158080c401998a54402c40120002c02e0030203042c6a000340000000980900e8115002c41004c4040c0b0030744106488401c20181d550310480002005600801c0c101003203450300303001800d021802a80030918000700e00b0300007828242c0300a07000551541c0400c041c060001c020810b01d404a44000c0c4481d024405900041c0d500da000c43c1c22501c1c140100100c43c481601c40e5184030310403a5000d401c0b01e0748c0503200c1c030b406002c480c80702131040015032078a04070340f860300e0301c15452500411000c03e40701c0c03464032203809100191a00401c0783d00011f02c072104400c0d0200c0108106070080408500000b1042e0030b02c22440d03803007041034020205002106424101662001c92003a07a50140a41815901d0306640c41c166507a40083d405000da0340243d80410000328030140d0820320640c4210000c010040590b60704031240c1c000c12100840829403400002c08 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 554727508 1250 554726258 554726279
    0x6021506060a0908010906020403050c1203120a11031008010e01230601050708070515070309080313330e0a050a0b06040618090209070801230a0902030c0a090816 71
    0x80c2d40905151081c0d500740c40e00d603071030300b51503000404a4482d40c2c002010018400148094032404000b04c40a081c8031154181c0d16540c0c0c003460302440c108503c8903000c6a89200c03a60700c04141081c0d000f048075200d1804024261148006100e003a80c25420f117400b441c100e180611651542d4620825018900c90904040d0113501e1001071a46051000411508002c2071000700508945440b403402130640c0c001c211031200001d500500b00d0b506040c180055040050f40440640c3c0e8448070740e01003c4115803042c1400b045201800c8182e0030307581c20b60000640c2840411450900301d441e0000240000040307035525940d10415080e004d442604005a40c40019500c81c040c19006440180040b640d5600c3d400795260441c20202d0a0700300303d0362900e80c0c03400c5040003005154442542d0402d6001985070000c40c0ca100d440307600305640843c4060005071103943e1101305c1c50300a40462841107407a80341030403412001c0d5114095800218400001c0000e502100291445042d048420b01034061131a0908404 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 554728758 1250 554727508 554727517
    0x100602151906180f020304030c1b090c0905031c080118110d0209030d0804080d0b060706050907050307120c0b0315090c09190e07050304141b04060602150606 69
    0x2003010703811001c25401c0a409000341000307004500c4070402200008510401159181201c0e4000c0c18018010400401d801085012919802142443c00c0303001c8140089800b500a8000d46180351034048612004c0307501140e0802602c000350200c0780b240064034401001c2d0441c000302500010403081c0103200020090398002d981d100c4401c0c01040c68008141c0c90340c41500a80641c80c282c503030100d20f888280c941000310012015441c01d003034680303041c591251100c42c49040c5c1d65500b07103a15000c0c54a1191918030840c0c1a55801601c03c21032800e00da00c403a520b6411500c103c0744284105500454900720138a2088100390348001408541441d240c00c41600d070700010501c20070b121031440e40d850540c44181859100d10480d00c80c2683e9882e080040200c88450800c904002087c0c4190500003060400d030343c0e076044410750030180d4032a40c6510342883c0725103020208021078003441040d003203070068049044082d004226020311115441310700490b50343c16509150111005130b2401305545040501c002c2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 554730008 1250 554728758 554728771
    0x1b08090a081c03050a0b010c0b0720070f1e05040c0c081207020706110a20060d0e060f0402030a020d02270103050f070e011e030c140910060215 63
    0x881140d9450010500700322038120924038407400b5805400d626649882203903405942118100802c00d0000b00082190746039000c020100909800070601182c01448020030a800c00e000c0c0d164006490310000b902d0720007901c40c600e8010717400d43c008214141895180348500303003584482c1c02502d103014200409407207280c02003c2480401e14810010901880040122515180400c1c0c16400c11550081c60070300103900107010000304065070f030171206001c216002040d41000c0310600d01d059201c0ea0790701c0c52240140c166400080010b44d00215007141e0001240480c4c00300654603141d0328485109101c80c012a4003d601d0f070402d40103803005261560408081c54005004220640c0002c41e001d804031107200c00f401c00c212600c00041080100c1081810a140c0e5010041d0010900d810a008920700c010b001c0c03180148106d00c0705500c01d42d00d9031548001560401811510503a50b0070411138282e610400300f42c00b4001680005451b1117009010750b0484629900030500041c1c04183c1108582001e0f028 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 554731258 1250 554730008 554730019
    0xb130204020c01020c060f010522020d0912030f051b030405010e0d20010603050c09090c04020301140108180c010e0109150f0f03050f0103140c091f061b0809 69
    0x1100561200e202401e400b00d181c1000582d40c00010680303d103041402010a226007a002005010b09d840f802c0a08003161f00707040c000300003040703002c20030806400356615521015117002142024044d011240104100c00c5441c00c0101200c58007000701528030864600d214100c0f03810401c030801b5035a900556200703004d14000110904800d1049003008030520f00c80000483c80080c00300e032110022040e04900410000030440c142c99540c480780c0761080001d600d8821105100000c503003c0d800d1003064a548002002155250703110360603441c028035221290360010b1341070400283c00b500150014a52400391500a106c0ea4045030700440d40d036052240d605040000e94000080d40d002841041040d840f42501c1d0715503c40d04905005007040d400315441c008140c100000e0050110f25842d1060640750064000d24100034a242003628112041144541040c0800c3c1003042069105401d20301c644002c600040615640301d0b4110703801700000c0d000d6403440d0f01c0d41c1001070000703040304000c1102d000040c00 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 554732508 1250 554731258 554731291
    0x30b0c07170903160305010b040e0115151e050301060e1c0204020f040306050901020a0f0f0804030e010903140106050a080f07050d02190303050903071505071203060b0406180906120b 80
    0x3804005883c090340120b0f901ea4440c408c8184070b15140c0a40300000820a000300b00f9506c0903040d010300680c480c426010900300a400d0905924480c04448074007031001980c002d81e40400b150001e250798024400e180000341c2c04400303480d2601c2c0a5007000c21103095040140440410b507004c00000394401c4002c655100c02c100400800110240a000e100d54024000141c841e02c86500140000d4a0000e000742006007400d41800555000f100a503000740d09858500b0341c82c0040030068419007141d40001c2e0040d02d40c0c407150940c0c7c5105412a2007550f409840140c1c10b90b50f82c18540350303114829201c0c281e140c5c011103802c0c8035a04080500900041c0020003500c40a4440c0320310b0490380c0b1b001d40059002440006500c8894101002400000c0c122011020442e400020700213140e4012a84014941516a4203603d04a80b09070040b0001d00b0260301556034403a03031a2000340007028880c900e020103542050300001c2040301441003108540c4001034001c40701100c2d5aa811000c80c0050080fa200c051045 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 554733758 1250 554732508 554732533
    0xc030a0e060912070e0f0f07050304060f0504050a1101090b120a06030803100f050603070801090b01170c1c050105060910050f0f0309191104090525030b0c07170903 72
    0x10651030b940d4107001910104c0e08000c602c0d82410720041840340003400d10b506004404102c064840d40c020403c1c64901d0b102d4449151000c05001649101851141008140824000085241841c1520139005110601c030746200541e85984684208490020140702d80c4441c1006902d501c1d0b0711041c1c20310000340030750b120380d92082c0540007079500702c440b6040004188801910a844100544401c580250071850700307210003829450140922007035141c80f24042c0755164025801040110000702c03051805240c6004d20303000503000410740d8600710028580303401031a4044d20400b4180d48000c3e0000386800c000005010740c000c50141d240d0200702d401c21039540c8010508000e4036021980f1250b6580e24200750700c40c14070b05000c015400701040c03000141c490004400200c041142d41044e60040b1380818103081480c00c0503480c0c1b056907000c0960140488aa41082d1006420b8910403901d103805505c603290861118012140c0003009100b21581006140341030340e0282c009031800030216845104481b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 554735008 1250 554733758 554733769
    0x603040501050f0a0216030c030315090203090d050403051b01050721030e0607020c0915040608060906070c0305030402062a070e22021c050d090801110c030a0e0609 72
    0x444050300c0d90303555401801a100400700c1c02503000200c944007542480d0489030286101c03094400024144290840521308150080e04007000800c03100e14010051541c54250310081e500c115081d0845001d030207014030308580504191002da0381c0040003045452918910f80b201030030390010321410b001c0144090310026900024100c005440041c408101c907440103c064162451403040100c80d0b00301c2e004107d086035000403100184001118211604e84400a02d0481400c100101da50007608056012030f45100c0021000d00030300b0001c3c202c03085943c84050843d22880e01d10710007800501c040011074094601400580010701560035140110003aa187d080f1140e0f0704458503044580040b00300700f0101d0700002940364441e0225404e544000e4440010300011959540003e104220782d0440000c900110510701821560010450b81c43d100c0101d80509115024410122150f090030000c00c041c038441400e0341c0100202d0b05c01541811058901640d440c5080d44a0740c0d04920300748030131b050a680c2d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 554736258 1250 554735008 554735011
    0x70c0b0d15090b0307150e090a150e0103020a0b07030f03050601121407030e030a05090103021804060303080405060606090d1202120a0f1106040503090d0501021c02040509131e110603 80
    0x1604000508144203c05040c1424400d034000044480b007140c2d51003c65800840c0c0715010a801c8840c2c2c080d0342d0b10307882280028445032100501c484428a804940b000741d0003072140c144c0707008550115070180e450101498910030001c00070001440340e0030840f001800782d0001e84c0c01c910141000b0022051080980c0d04035a0a1000c0c0041000b403842030103400c03901441189030054868000e03501e490980e50003e089441000180782c105540041c41032002c0c402502c40074150b08000348240103c941d80d044c000c003c0c05059800b9504d030f0041c80c1c00300390329103054000c0707c0320400043e01070200d03102c00d900d85064020442e44084207500454100d0071008030114020104880700e501d40450f030b40c41c80315000b02507400b8001c1000042d07000a05000120b840001510840b0800b1280909521402d1030324a002e4054079100c40d4010044030b000851140f2607802a0050301d40130307a00107180d50790b072482d400020070007084085e11482e002e118402c2040e0800c110701b0303c89070040110080f001482c801051081c1d00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 554737508 1250 554736258 554736269
    0x1703010303030f0506032d06090109120302040f09020306040f0914100b06030f04050f0d03060e150901030602090409170a030e0d0518010909020c0a020f06070c0b0d15 73
    0x188105505441014404108404100542d1038a107012aa5820060251440c0c050206400c2c213202002e0b1400107000000341019a03500341030104c1024040c142422044580181c01109070000ca13109100791000c4414a206030070204e464511020000e40c0302821254005031108521000d42d1418092000b00900c40c0319488024803540c0c2d0210709046604481d81e0595007000c6880000d0380da0700e419030380c00559403d030101d42da480da8504207240845d900744800c814018861080c1c141501640148200c95503090355082d00c1d80da00c4041d10400c0d1424001d0341e4480202130040c4041600f0340d0113041088409400095215142e481d69528403c0c54102000d81910029010100540c18055103c00d50701081c01001e01400002005d0894004c004215403010081c0c00a122582e1054010500030038040300111342d102d220103c02c60b120102000b041c1d000b4840c6200502c21030a110f81154621754103c1e521a00c56400d192019496500160030403001544443c0c039a419440c107804004000d12 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 554738758 1250 554737508 554737553
    0x1e030215011202030307110a050a0602250b2b11090a080601062715050c01060807060f03020c0a0c0815060301020a0e041e1e051506190507 61
    0x3114400000042105812151401e40480a1000103032000001d030340280d40e028100d503080c415000040f41814075203070700c40359020304031810008103140c0200740c0e07144100402040034280e1b07030380003440340c03284440c0c0c810140c1c0d8083c1040011580424031b00ca608140345038000304181e44a00e501c03040103481c1001e4039407071074680000f030300072951a0600c0e50380d00030214070002d40003c0d80b4008000d4519520799074203060820000842201046003418410302900394140000f6240c10740000042c859003040725605d14075072900310003040440c00003035800125001ca648900c0000e03941c903004c9010707400c14095000c00b8411011020005410301da00c0f0405003070048000c2110341c0d02c119100031544006001c1c03030f019910401000800651200050085003003c0d500450700c0c40c0e0b500000c0c54410301400c0c41481d99490008005515004070140d88141c00c50480103204580f02c104200302d114a40400940d0700580c1003000c500c110281040c2d10114400c82e0401504016050b111180303502ca56618021014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 554740008 1250 554738758 554738773
    0x210d110301090e0f0f06180307020a09240513020a030e010c050a02070e0403090e04080c390d0b25231201260f010903090503060408040605071e0302 65
    0x10402c4050008156240103014a0070020074650b154140904960360780d00050180007d0800200201e5046586c042c0c01416500e945810b61802090100d080505901044008448011801202c1d10984d0401400d03c0f01c3d440c80b440000b00254056064036080c1034640c001b54240044c00c0c0724000b140c1003d511030039030302c0c084004000d052007802d8004180c199100c00901c00804d0b130109060054a014401c880d00540b51420900f1041c01a900700d00076620410064918108400340c0e402d004030f94202c81c0407010341d4448079030250080300e21740c0b20b50400b200d4503074800450015080c0c00c1d0043c8040f041d450003500500c5100314961130540c0c04401003140f0302000a81c5450424034412002c083d00d12141c1064100b028170f44a9000622407040e414034511280c2181c01551400070701556580c60403103241c000c190b05524043d002034842a00401c0c96483c000606040120b401c0c0e110380d40c008a03062601e82018000d90755504007501c1540c24400301c1c84048809448840000d002c1d50084d002001c02 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 554741258 1250 554740008 554740031
    0x909050309190b03130230010c02010209030c040c1b0812061e010f050f0d090b0901140403030c0212040e1005030d050901030902041526210d11030109 66
    0x2508181610b01c0ca406002c0b44040150400000650384c009803007940300d11070351400c1d000150761807214124040b40c600c514074100ca00418102c03618a055030f807d100a00560394441c40a900703e0040ba211550140c1011400ca11545081d42c0108483e0496003450203050351b01f4400301c5034000f403012041341d06207800034003000744540d07450000c0c0d884031007150f0301201c01100c40380c00da003105034400502c0c2c10300c581c40c49140d441600520070b441d511245612039544800703180a0880160041000558001c0d101001040656006000d00c0c00c0c0c4103001e844020302c984990b80e046005080303207000c0c50118000d442c1000400814000144018402490106c265003408125610440c41551200e8402c1d40070f10702c541c4009401809590300f4034024207000407010a1800800e0240480040090289441050201d1141e604098400240602403019060806e40b000d64a984040070420b68cc3c0f03091041902441004078400108109200c07441c3c045002c08101981a0b0b040d0000e8001c42489900d82c840c0501 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 554742508 1250 554741258 554741269
    0x608040b010503280c1a13050405040f080c010b060703080f07230c0a02060a020d0f05180402091206010323030315010c2108070e06031608100909050309 67
    0x2610b800c80240188036030800381c640d940c04e8481c118640021031203420a050103082d03807042005011a40c00c2010b03082017055002d400d507100a03405031b6100c26064000c01c007810244140c51007140d020400070444485070720b49000c560050600410a992103c01380c49550700c94801030110140f0a407030f1941c25080c03102c0c5003140d520001300918100b000c008006603000c1119200c1d14030f00c006480c010742e9914090110207041281c4444080c1d0404d0300081e24104450b40010003951044a6a03200d260041070200c0c220b03003d1044452032200749510018066240ca000d50007401c0f20880148052001d0b2003d5100906000b4245e10640d0360030000141490110b07184802c11801c50402d5019528503d0420f407030541c0e00342485011410400041d446404101c00301e40600103c0207207520000c0009182e00c8000e141c0b000495007140000c0200c00705075860b003011001d6900442c0d09480910b10002902d0048420602c0141040e6810200303107000105181c440c41034099907800340001e565500011b105001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 554743758 1250 554742508 554742511
    0x7150f060f060f021e2103090616090e0c12041109060607020105040e040807021504060f1403060127030c090506010801052101021309380405060a080303010608040b 72
    0x9010744020300100780c80d408240c3e8004810203408034050380c88100c2845e454581da000c4812014124041040310000c0c120b005107220303100c0340048408642e6806076115207481c0c9006940b0103d10300c5070052098801d0300303440d00e62048005610900344015010b8506000b141503070203503075215000030307030200d20704250300c000d64001170030b03a812454040c1c130703900080c0785101d82c0c8500c1c1d140c0e0300540040341c10041510111124680c005080040c4100324a1032421140e00c40d2080c84042510710401c4c440c82c600034842c030010b88004060490540c1c0e10341d401510082e5507011900714100360184842c0e0041c65413280c01025500500101103c81c1c2007940d01021600003078900707410301480d000100712903035070f40d0382d0740d040f92000a191410180c01c0d2118140640a1f1a402280c1c0c00c5100e04042800c0400d54410980d41d08104810002e5036103000c0800017420340740b00d800084500d065484407903420103400c943d40000d40a00030983c1c0750750360041c0794190b41003038006100107000d1f00148004c1c00707100c0c160203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 554745008 1250 554743758 554743769
    0x180c03030301051305040f050312070305011d040318050a092c060106110307060203040f0b0a0e0309040c0908060703141e0a09060e0f060610110606010507150f060f 72
    0x25803442d410100001d10421040320a001c2e12612080058200f1024220b0400d08941c03200c00c403510350014003d08800344078101c61100019180c10000070310107003c141a503c0640c43d9200f94800f90316a61421100c0107524801c0303005a507035005000a140e110a0413600042016090016070b05030001c21400d5100560301121031100c0307003c20b14000c00d0a0225146044419500301040840c000b4200e103405c6018030b44010705a68800b004000c140104080d80c080e901d0301c107095031800c1e542c079010744d4411035482c0304940b00c050b030040c08110564100b40d48a82c0140000e420480c00c0c103940c84000d1840c133002110031400013522019078804400c00e441c1510307007103100d5200e16604003440890004150740d004140d040f0148e290102013060002c2641b103105407114500039981c5030303d00c9809050703442205442441c0a0f00706858891b201901c60304c180307000445c032800903010319100c0c88011142c43d00410350071344078558004150015925184203824007881c01c02d5020900030302d40307c0017007204007907580007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 554746258 1250 554745008 554745013
    0x10b130e07080a050717070e0c07021206070c12020a080309010b191a030c04090f0c1e0207030f17030a0c090506160b041110020f2506050c15180c03 65
    0xf107070000b500100b65030040d242c0e8070414071a142c90660035289031504a41c89401003008141c14845500440c4006041c8540241c400d82640c01e079000000c1e80e5400e04440e80310000350141c61000009110341c1007591200c42a00c115005e9004544035210945e0041c1e9440040780e55820510016052400d680d10000b00400388200b10942362800403114640c100301007007009000040010503007804402030318094100d8540402a07031002d410040009c250241c0c03414013103814a2441d920b6080072005080010323075554050008a49955a001d00d4204110801c0300d8003014014a1804045404080c503c5505076007400f103120200c4500140c40f4000795041a4000da4040003815401d91014004006844c0e100f407c5c400142d64074103140101d5458980c00a5004039890500c200d1150700040c4602e905e201003090311540001c0452052000b41802031034080e0820f000020040d050041c4003510040d210701055441c1881400d84688041500300d8582c1001040c0d6a203482d02c01d8000c0180c02050b1030107500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 554747508 1250 554746258 554746273
    0x105061503010303080c0f0d050403080105040b0a05010e04110c1606082710020a09050906040c0c020603040f0f0c080d021b0f13060b0322080708030405010b130e0708 73
    0x92140007440705010203028084001d0200d0240307503550044540c403a0f5103a450342c3d203408140401001030003040d1001c1d4001030080c1d002003940c1c50710307108924418800038801c0d580c3c00d01d0440103460940e110050305510036515403810344504441c41c010514841c2410180003280c201402404022480b504040104440c1c441000990390700f412242d081103036107440c003a40c8010614035151602c0f881c03e00c1140c032140041906c01c059030301310320042e0680340212200103045d9242000e2004940c40e28914030001605c3c00560405030601d0b0005540007400381e14043c170490059200c403506401c07500c40456844a880c5010400301009101e140c40980da144081e000081e042d5007140300d60542c0240f810320440c00c003410700c90551364160300180081107005042c030130745aa440e003032036543d0404c44056090850003840b68405020a9616002c0071b03500007001030811415868401080e00001d00851b560b641c1d45440c22119507860911315940c0b1791444003c24403891003e400d90600c80c40b64400e00e6240d00c03a07070 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 554748758 1250 554747508 554747539
    0x6050309071a09030d09050406060507150c09270e011404120201020c0708061b030907060c0c081507020f07180c0302090604091b05091c030e21010506 66
    0x301d9804481504a61059201031030050240a00c00d0b141510381c140724504841c16138036000442002110f80803070702000400d54664080d103c1d032155120050448541c06011410034484d07a022512881962030240301064440518a500d02d20400e041e403540200c008640f2a140d0040c020001ca0120f00340c003e010b040020081c1c1d070556600035100400451046240c4080d00d07200354107452000444400300c800491ba50342d2001e0b100c58098a40500800302554542000d05100e070803207021754012001408030901e0601c003103440c01ca2040013100c40c0d07030b4406c100050f8080304000321000302c0c2280f0100c403190b041c4800007902d0100781c1c103103100c49170300502000c002800114241c900b4000b0540300104104050300c0f4114001c0c41082409507100601207000316075080f481e0b0040c1410101010b07a001164040c0c02c05031058021105480e0f480154000c0400c20300c44c80d902e1101b0110710a003000c5042a641e000022011280c030020300400c500c10807584102e0300c8090042d260008001e507040308000d035504 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 554750008 1250 554748758 554748763
    0x2030315010c120e030c0612010e1b1e07120315150203070303020d020415050309160f050103090302010f0c030b0405160e192c0702070f1a090a0b0301050a06050309 72
    0x3d4880410302a0000880301d05482c24804190100e80051280340e60300b00301106141c04007028040e1000c02c021510014003400c2099050508a200c400f20081c2484580410782c18003032001340a03615081014000600000d414400c1c021400b0110344001c00c5800d4049145c0b505001560b100c03115800b1110105040f09030088210703401142c01d4a80982c1d680c1c44460310300d0181c811680444241000765440d0000070b584140698051820314003035a420410b1a0a00788503404980160380303d0703807090241041150300075400401c100d4800d0002061603909203a2120403100700411100200e9100c07400205686010300c1440d610901208840303900001c4800c00800c4401504401403307640401a4544228001282c400007001c0350041604025170b0070740724504400c80d1300d0740108090a40320210350f01a001040c040b085d03440b900c1d001c182003450011503d038000c3c2e203d200c6506802d002c008408903500e8000c000c03030141c043d801800e0350341d5140800b840000a80341d071080c41081400d009020384001c0c013 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 554751258 1250 554750008 554750033
    0x30d02010b1c0204062301021203040309061b0b0f07090905040c050105250302011514091b0c1204030b010e1312140703030b010305060307030506270d02030315010c 72
    0x4081c40b440780718038684082001451607820034001264140b01c010700303c3c40f4280345020058000c0e03080e5801c412110f8812156404140d4001380400c0c6040c000b40300091203403101c0c060013221401d40d01c9405000c0d440320b8010350070646035214010520010400c03400d8103c0c1c0088010051104104036920300354950380d0100707909009150411500159081040402c0340100c3d0b1914442034040c03403d0403092601074001c1008a420b040a15003030100082c0d000383e0b085600d0304441014146c004d9076a01c80c01501004180c40103128405181800140b0141e8000c12274650000c0030110403da6543c1141003c02c013a2405034080a00042410704110b080c26000c8030064402e5400040310034003502500c015982c1c0740144c820100420804a07510041c594903400452002ca004c1e2070411250311400103068640f906030001030216408940400e02c0c41d5030f407002910066010250f03c005c07461003c0c0b080390030404c0240051005038004410700c0300d0a900650082074280003400e10000881582d680c21882c00c11 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 554752508 1250 554751258 554751289
    0x302070e040f020909060406180506060409030504091401030209090118030f030f2301060306230f090108070906050d21120f090611072303070c060905030d02010b 71
    0x400c402040411515984950005500410100c035600c0c104541d65943c0320b084070300b41c40395403c001000105100e000e1050301c4840c0c000c1c02909180c0e80d03400500014000c0d40300304504010007003200243c0b001c600d10030160070480c450500310503540365004100c100e8001070560301c466494806003070003607001002e400003115410308100e0b00145820005034000c14002011011550402c0c2612503460300000f119505210450048000c2d640ca44c0c4048084031014042c41071654406c0040d1b041698050381e0559441c00e000341140c184104c4040890802c1c8007ea100740191b502c078120510a4100501400d006088142d40e45c402403081c50701d07800720944001440c0300d2aa89280c2c54011610704c45c009507034075005040c009218034030300c0c01940e00c02040c100d80e0540c7c20a01e041c985e0030859041104444980350020300c3e02c91140340356104100e4020103c0c0d03110b9100e00c0100700f0710300041e1403138001c2e40061030326869010700c0516040c03e1506080c401c0c03c4020031a45041a04e020958404007410992007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 554753758 1250 554752508 554752529
    0x4060c020907090f06031b020c0f010e0d0c0303030207120e010906050a17100f0f03020906060307021005100f050d0f08090f040f0b0102010c0c0c0e15092403030403030207 75
    0x4866140c181c0341410544c02c006200300300c0d00d1012170a03075056005024122501c248202c0050207161040381c03194081c40c28142e0105109400c5059903220301d1004080e108020103261924051395108400c80b01079a10460110350040344000074096040c00c45140740c28142001402c1300031a0b0002802c503a00c40c000c0b041070000c08103460340340d203100c1c40000c0465040c51b410700055040c59140d501c2d03900d1143c41a100100c40321031002c5041043c5410103011a40c4c007608004040e00d030b61040107080c0e00010320312021481034034071034012070380740f0b010721806100f0307840e0a079021a0034a103140712001e8007030f007042e8021081145140c00140e0510411074181c0d40005031070380c8a0860200084124400e0a40282e00504122503924018801d80c468030007030009070020000d040894000b65201d5070b802101030104500d0303030b000700f010702c0000d102e095204039107107020307808070b1008000a84a0740d002c1d50803003482c0c80009410000c0c4030100301040134041d0300b14001c6007031601e16540255141140e0040c0004407 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 554755008 1250 554753758 554753761
    0xf250803040303031a0405091501080c0112020c0c09010f0306050a0b030309100908070f090b0901080a06020702030102040902190e011e111006061815140a0c060e0d030e0304060c0209 80
    0x305c50403104205003900050007400b03c2c1c20140b01702d5a5448810340607540c010f000a00014456000107a00d07040740e101a154a101d00380515286e800030741040c0d0395600c0d1802044804400c03a640c0b01022401b0b09901807102603400c0c21418170600301c0c2c2e40208510501413030401d0443c05d07950000141c40c075003141214003810b40c6903a25007c89480019900190030b0b807042c0040803074101c05080d07c41d001d858030b03102c08200714203040c02040060a000c0c0316108050308801301d0754000c0389454004103410f9001500140c901552292508100d03400744030b031a482c0b44003802c0320f550426484150006141003d2030310500034000280c56212080440e0b2141040c0407103000104000f46040c4512101a5502c84003008403aa50741ca01500303801c0111012240f41d08400c0d0040356202078ac0c18404040ea00503a9140f4240d9125000210541c3c0011441d0040c04603c4000c00b002030706038040d0b1542c82c2c03c44009000099400340300079080c0e4403001080780c840d030024071061003450351003054040070580450b44041e05 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 554756258 1250 554755008 554755031
    0x311040f060b0a0305060d082d130302031506210114090f0d020d120c05272e03090807120c03080609280e0f25080304030303 55
    0x8020200d0405109810540009901c0b550180500080100740e01d0900541d070710802003280c071091a05000381200c03414001400c00000e008070b000b514441c81c07038001d100410b51850400c1da80e0049584c6042c14009224140118181031054100302090251192014140700c40000e00c1e0352003058019558000c0074404048920b001d40050700c0000701640c8a0a40f82490548592606900e00d4007918510440300044a480d1002881c580100aa5aa100d21400540610001404401400700104035042c0f001078550184010311303040b90b90702c0d83d07810440b00a0703403014001d554182c004900403104021040308000400003000200712502d84c900000d10030403a01d4207691307a004954000d40b0300002d402205040701d400680c80c51907070b03020b6280d040040e0b448108112041804071200d0b80c005c00480b94210400c00ca1a10b0070b0321178421444045441c444000e1f80b1442c10180e0460021070354081d0300200c5240c801c251480c00d02107038032080c61000c181030200c0199a88210b200040805541f40c20b400107 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 554757508 1250 554756258 554756261
    0x8131e0303050a05220f2319081e010b060a020309060c1e0a051c1706010516080414040e07180b06040e040b070306060906050c0307050d1116050a031104 67
    0x181154003907070085c42c081d400034000c90000342c500445800026400010646400c5d0300d81510108920031500541c054084051004048402c9000d00c1152203103000850720010500c000c05440209100c5040845580f02400f800d58050301e030300c580100002c204d829144c40d80481100c1103030505542040d0303565002001c10b131400c0b4101082c0420f1850484400c0301e42800032034031240c15400344040365120754500c10b4206400d07000d40810004610290144d6800c803100e412000d40c4240141000d81c10b11850722004c00c206c0f101c400d030845050800040600c94403201c0c0403075040d40c00050340c0070044a901900c82035a90b10030341c05807070b070308440c41300c0c0d02c000e2070440d03401c05031140700b01a00441d202d035501c844000103501e066404071990018030740050340306440380c42000c04448207551106d100c0c5240400c1600d4941c0141d400b9242d81c00700b00034030004160108091001d041c4c82e5607407812403401c1c0103101d90406c41030216088406c0030200c2c0404c800e5940d1141c1ca0203494008102210030090b2500140 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 554758758 1250 554757508 554757517
    0x705010818160807060203090d140c031e010e430e040302150c030105010e040f020a090812030411090712050109061a032202060d060308131e0303050a05 67
    0x41d081c8180b41c0c011920300100d01da8603044034501400c9940180e159601a40c884c011048400e130840107644c8035034089014604140f850020642c240c1d21a241d03c40f001c2401c2c00d83c02d4040c064444468490089190380921030021420205d1001d88207003c1c52810034079100144100407407491110304030114181c0c91110801850f03050040d955072501d5a2000c0c241039228040310141c000d4010715014030039918020503010b1045020015982c03940c0e0a0500646a50380350400807900150384012a100f15060783c401001f841c483c0b901d618404034640001549003c000054405102c0380038014040061040c0d030fa03030000614211041d045654550713200302d4884442c000c8251889062100005071501540e20a4003902c0002c20010b4504200c0b05106006101c15505c01100500241c00945448c80c05100c50064070b100500940c90030b100e5005100998400750010b84400c02d0000b94000190307a81030864000301901c0d03164610002104280b090288684d21000c1c080c414006100c0395044e100c0e00484 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 554760008 1250 554758758 554758801
    0xf150a0803030702100606030903020d05130e0108030c0616050301090b063604060f09050703060e042a12150e0f1605010201020702030604060e0a060c1e09060207050108 74
    0x80b41c4915250800941d0750450015407410700380b524102091003840781c0941030304c142e0580c009091401d44514211016440254291a003410307006002c202c0307005c01e0034451f00a09019004544035047c14081031304248024003031004540340711004101d825000b03401d4030b046401031600080c00310070b048003140f4640b1983c0704140d42400c0e0920b50a02440d00121901d48814080e1800e072107441c00130003400100c8884d40140c45610301291001c00c013801c0c0c560001036100040c1d20f000300f440ba9513005280c00c041d1081d1400c40b078507a08550880340b00d10f45000d4169481c6984803044003500e251007210441080c8481c00540031906080524906080a03000010b0009010301200d0365228900c244070740311112a1b020004a100ba5880042d0642c814002d80e0049a0000d002c0d1003651900e988900040c280700c5d50702e000d00e008034002000803030312a00c00d0340542551900c0305440140341c001d1325520300c0c80b284070700c40030b200351200c05005041d400660360017078600c20300b030984064403410400103448041a146 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 554761258 1250 554760008 554760013
    0x601240e090a090303141e100906030b04030311040f1419060f120905071e091103060918280606080a0218060303070303092108011505030f150a08 64
    0x2440b1201c0465400125a540641c2d030400a01241c046060304001e402e5a00f0743c0c01036408190880d1f5020f0751034505801082e40c092802506958040050955445a1040d0703104042e440400042c140c140c00780400d03143c517400c0d100740b400d802c2c00c8210240007643d0041c0d88030b41206003075a90040d00c40314000100c2c84824802510419a40d242c0104034542ca0401c6130002940415034141c4103585005810010b03034048003800d034080c1000000b41010420280003d0f40d40b19403080000e00001c540710385940710300940c40e0150b517494002c00707100850f8800380c2455a046c1c15140c4036801603001051081d0f5880070381b000030b0140c101007020504464103840001d85460b14000c07000031494400a034800b1154400d4401c61188100c484d8402c4505508807905505034004212a0700028800e511243c3c5c000c0c42080c09181c14848101e002c0c0d0b1091320110380c1400705030358000502050500032080685402e0601d0540d25610b003400d00060300c21030190400d107440d120340c01d12580c01d56407010882c010303140c0b2004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 554762508 1250 554761258 554761261
    0x21060c02031308100c0e0f0910091a04050106020a1101080705040506031003020f1c0b1e0a20090d0816020607080304120806010e090712020a020106030203010e0601240e09 75
    0x41d804c0d00c2c0c3d040b28021110b1a0303d0f2205400005009040328007513a140280611124680d6000703018205100610b605d0503c6c80014001c107040c85240f042024002c1c03e51907600c0a1306102007800100d41041e086a001e5500c10400c1d40700040704288408070114003841d00d542e064581310f409994034095034000c207078061004410044900d039403e4205040781d008903183c8125410b020306201c1c19041503045011843d652050600120394141c004903001118a21a66100b072208074103034054000644045080d80d1f1981070070440d1809200705a440c104c8002c0b100c9140400c1c9200250480c42c01e014000c004002c00705851148000c17218001c100300c0d03005400d140c0e6030001403030125040e03442101d040b10303e80800c4450341da0342445911418400c1006031151052a0f0780364041040c51800184040208030140070350503100300160014100e841366030340002c02c500707086104050940d0400c050090a82e800040100044601200c0f040d020701c400594400301c010051400b00d5040c00ac00200e5608543c3c2d440 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 554763758 1250 554762508 554762519
    0x4020c03030a2d0b0d02100e0109080319081005090903071a010b03040f0609140a0224270604061d03070e06011d030703060603030921060c020313 64
    0xc42c4601040c000c10000022000015241005202c08140e0405150354056901c83d4495002007600030b0002c0c90050030083da94001540c026524000e61300062074034490400780e50300078205102400c0800e016505007410241501c803c002c4c4201804d040004100c08030b09442c183d44d0000300a488094251005880e040314225500d5101101c2104d41c21600744e1075030500a0100743c040d060b603850410841c6503848076283e50300403810300e40d02030365a1542c1d2045a00002c94012001c0c14480840c406000d10300700070b0040102a55880d4006888041410084440032128400b00c0d101494450000d00c022018854640350b07424034541e0040d048040054082949078021400390601d1482e22914a0451400410f04da1154000d20590050030749132030105010798081c6090340d54120601d0b0300e1044032014040042d18020165005540c8240c0c3d0361b90500500d50f026412034003034052181c0c0b840c0b110000c208031001103a804100604840e9441e66901d0409200380125240c039204cc122801c030060303d55 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 554765008 1250 554763758 554763763
    0x121404150801060801080a0c050d140a0302011d160308280305060a0b07030c081b190b0603070b0d020f090402070309170a0201080a0209041d010c182d0504020c 70
    0x83c0a09000f0800e03040000031000c400091410f00c0f254403070001c0001c2d03440c0c40180113140c24015011242c40c40001624520045e0403c8080500e40c042da0021950340000f800c025000030302496012010742041c81c01c61a61070000b28440c080300d81c80589550340e06c0821016000039120030300c0014582a4144081c01d40c9a4590009801285e0840d50b10061960322180c201c0380e4803a014004000c60700b0021580302092a100c003a29440006402400400305030200c01400c0c086000321038110500d10460342001c1c030002b0840240e00140036402403807801c1c2486d54030050b90040841141402d0f0700000e0700154190240c0c1a02d0071183c01503c00c2d5102c210a1901900c45640307801480f85610302402c60703941c032040000e0944142901a121411240c481c911020040d510003081660130548803030396880c5000c070020203181d04030240710000400300b090140040c81141c0c40c984180d88139203002400e02038480e1010301c10350501e41500d005005003002034484103d90302c42d9804607511510100d140540309101 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 554766258 1250 554765008 554765011
    0x215070209091b04060e150316060801091107080d0c030f14070f0806061602030304080706091a0a05030f0403020c0603011512110403020d032d020d0c1214041508 71
    0x1c0c07269a0341d4000c03c18041c130007210302c0c42c483d44c02802c6508010032045a04240d44078000b88010341516225413900660412501c0d07554000d200281414004001f950b0440c440e0895010440036094601340d42c607150140d80307000b4106460350b03440c0d4405040840074001c0d481081076802240b02408500e1010160b006400000c03540381000c99000c880c02112248565000e520400c0c0c0180900d04110340300000d80c102410780e0310100c0e018801040301103000303001042403000805041c1c3d07076100d4441c100000c90f40700b4411a142d90310b07003240c103004084e0b10980082c180c0b58042d8a010380e1031019070310b50504a203004000072941341c11020000c00851b0951001c00350b181800b0f06501c41c014003000c20b0760f003001180e00107481040546010f00040c40145400c60600381d1603400383ca8103925206181210142c03254070f1400584c0c07144121250288566018001d1840d00401da081c400c1000460b030701d07120a004080c0a56204000301c00c00c1d200d5881c0d40610596024201c03000041c540980c10340400b4164030740 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 554767508 1250 554766258 554766283
    0x9050a0221070c0c2705040209070509040e030c0321060f01050309011b1e08010b0307201207030801060e0906060d060806040602070203070e100612020f12010306051b07021507020909 80
    0x5d100b90700041c0002074000c107030040784c0c082c00c642c4041c0c0e0381c0704080301e10b60016115035a115840f11441c00701c1080c00c20141510902c103402940d0b589180d891401c4c0400741070b4850b0710b01e100b0b0400420100d561404884c3c03e00900a0034400c8d035a5440c0340b9214010170582d16882201c02516640400380ca6000d0040350400c1c2c3d60303805500c002c1501d08002c2e00c07040c1091240b84c000c013004200049503a48112020036142030a00000080c0d0317160040c0c580d0800100c41540c07203d061012447c0000e01d82c0c07121171180103001030b0404030403070074036035011489040004140034000ca10021303515803002000c3c1c1c000002406c44000b580e12604107842d00101039032100c00141d00ca84207158000c513240c1910b98070180a207004054500c2e080b031070f24400b0350b480e0304003000c4550490303030a00082104134591001420780003212001e0030b07181d60652030100c0882d003000d45404c3c124032007090600c40100703002c0112401e4507012940600650700e00903c001c0148200d91009400c00701501c1031142040e80050500010324 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 554768758 1250 554767508 554767559
    0xc0a0b0609060307270209030a1505010f060219051002070b06030f0d0f0336030906260606071a0f0a050606040302121203010b0409050a0221070c0c 65
    0x121400e0406a0398140b600456403000170f40c0c50202d00e00c200038082c3c503c050160040242c1000c40c0d103800a41010604182900d81c1307030724104241d415080340d22942d070160030103c40041c005818410025a03030032a910400741041e103040c9038030041c0b20003009002c072140702508042d5911006842c00c1100100e0131303070302035000744a0350b100a100628042241881c083c1c140d6226010050003540490180c00034000e50300c1c1c01c0060700c4540842d0961255840d0068504040d511400000703480c0c01048081240d000d4010881c07a0742d1911030300c1d19000d685440c241200b000042c03407520380b4400242c291144403801050340baa4180380a4940b419080c01038841d814400540c0160350300d8072140d206540003214a5940304900b00001d00040c0760498002c441c101606049924035154801805a10792080e0400c20501d2000720b020003048807103000d1254008113480707040d0b0800422075804101c10541090400003180d9203400500d10b01c1c0b01d45580b1038030b1604200351600c41641c0c1c07003080c00b445617064603144845 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 554770008 1250 554768758 554768761
    0x302030f06070f050d06050402181807080a020708040b030108071a120f090a060903350106390b061906081308030103050d0206010e09100504080c0a0b0609 68
    0x855000c28458850065074440a40c00300807400102d800d13900c030300300641d6040c1d43c5106c0483c19440d5172001e40245601c101003440307a403642400304600d400c0700f9601549040300385410490095402412190440c90000d800b503107070340b0b403483c010a482c06240c1103844441000b00c00040c03a503600143c8082181d0110700d4050440d051100207164600c02c004a1080600517034002c101940b08142c0e02c20341c1703c4402d50a544ca100c0050f0b031040243d4581140503400100d401d1000d44004007120a114481d2100241e0240204100c0500300495103051181c982488030301c01e44070030010301000071041111807600400a44005d80c0c1038201880e2400081629107000b1400000c030103003410001b01c00240200003246201e00d160080c120ba901600401d903001c0304680c0e4074520005049003010394040c43c03003100038203240d440001c0020b00d0701c0016409078447c03ea4042c00c0c401501004502444c2800f42414007140c19901c2d4100502a0321404a40e1040b900c034114400f41480140024507000c0c450843d0000500d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 554771258 1250 554770008 554770033
    0x9201c08040609080f1f0905191101030608060414160308040e06010503090a020409050304050604081e1c08090703120f0806040c020c040504020d0602130303020f03121609031b030203 80
    0xe40071902c4592040c0c0e400f0241003a51010281003034106d80c1603007180800d11078990380d10181428816603820351003101200029003000f035080d100029081c1c0a10302044203d240c08141c80d52584040d0000d000d115407600030300d941c654180500c103103d004d003002c0204210307030f24a416038039584107218124040b01c40001041d4a988140c00320f80c051400f003001803000c83d440d03400f040004e1400c58000c0700c151108100000f03032600c5100280c0010310181010f40f0004409001300100007100624220b920381040c500c610703000c1d8480090b19407051440c501b100480d581d015075286032880c290409825a800f00959461099022107080d80c1559160360300002a2030300e500303000640d0942072407400560000c1c0c12840c01424664450b9070b10500003001c200b45080c0f183c90701c0e01207a20002004803080d0364a00b041c4149a01000f00e281c03040618001540f6160960101800080d40070f0708800c0200a600403042d00c0c3d030722440c01000034681100c4845000485076405600e00c401340e1200720702900500401c882c0c0b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 554772508 1250 554771258 554771263
    0x702030a0f03120606210507110d03020a0206060303040501090312020f0a0b040201020c3c100203090102060114090a090302030d14090f0703080a14160b0a050a09201c0804060908 78
    0x642d103404c2440306c001c003018200c40018200013402e180030841c68124800c2103020810164041c1c0b98641c40040c1d4880b07120783d000b4100b1900500d101d00960003088108104e1340e01c40c031315404882c2c2009403015080c0c0b00c50030403801d100790703d02e0300f90b8980b01e009906410b000b0036101d41d41c0104d100740c08442c4d0740d40e07003075050058400d8082c0306140d01c00c214940501c2811070040000c809002c06103a00c0c0385d0001941d0000d54204800d02d02c5e41c005a002190440603560104840c41c00752200c2d00d800c0c0030f505100e8000460f21803000b8a150b03a06034894003200e0400d0b00030425110f040380420000d1240c208111600d0174050070849800c103035803203202c5074050050008079146c0c098a801c107180c1882c02480407420f48404510000c2248a51800c0004a000404c20500032880c580300e014030408030b0504101440580e9130203804c00e612036140410090009401c5016003400c4034420352100c0801c1e21010006e89036203e240c042003c1162001300725001c00030058002d00135600c403a1104d54100751205840d55 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 554773758 1250 554772508 554772527
    0x120b0306090d18050603040503031e013f060902101d12070b0a020f011109030c0d031103070b0412050717070837051e0702030a0f03120606 61
    0x80703964000381140ca441500c80d01c811480081620220010f00356944081982d5a008803825900d58101005100e00c44000d0f41522030844c0140d650341391594103040702c00164802100264500b1080d01e910320030001c4d040898003051000c980404080b030701c000d040c024003078815900c0891003040b40402c4510381a00654501d01c19102c030420740500c070075440742030284a80400c1000e4105209500c0d0004140245900411088180781d0207000344100786815503007510340c0580101005003050041c481039480004000701c00050031039018800b03541a041c1955040d0218540180601000601310180016440060300851040310400f1313151803907180444981c05094001441c40ea011805030200d000000050700c241030141030741c6403801e01c054042000300c00c2e5001940d80205e02c0c4d00540d0480355100040303405680800c0c2400c1d440d0903d0300340021040449000f14401100d0041140b40554804020722030b44558000400210b080300c509004d0312101c01c5120741080c503402c040020808511078001c18 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 554775008 1250 554773758 554773771
    0xd0f12080c1b01020f0307120506010912080307210c02070504060506040b0f0903151f080c1507020a0b030f0108032502010c050a21090503030f0f1306120b0306 70
    0xea0400c800402240c40c000c060035402c184964090100c4050440200300030344c021607450b110b904664003410041c20a48800800041c140400950108800711000f0480ba2016030701c28906952035503480e070207403102081d01181c2c051510704500c81c0808403440341e0001c3c0c005d0380d050b000c07240400d40e540c2c104802d45855004503a0840e00030300040040883c1900540000b18101100c2402c0801d2038000ca0300e041101051420362140c11028088114140301e00d80350003070b0051002000b62414181f50359941c0c442080c00764068072119a044a41c0c6aa04095a10b00c55004014048070f0799204049801034106545020194404400005403008008102d58102c041c10306080c07019250741d2032406e811000d10409906100300b50703500030000b81c014007000f000d0740e105003101211000c0503455190701c42c41f107900340c8091011031031050241d564000161918158a40b01c2e09a840f170b6107846010b040d010f41e0318860518022400b0200d07a140d0415114001450314980400c00e8080c2103007016503a540030b0720003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 554776258 1250 554775008 554775031
    0xe03060c070303020928060807030524010909020d060819050a060f060b0d0c020f0c090f040204021b21090d0204091b1e05010903080a05180d0f1208 65
    0x40100090003500500342018009092480601c480d41007041d03440b0034103070b0400b0700c02281e4001f44400c030740050741f00360000501c3c80c1c100641c0c034003500c01c0482c5140458841240708070808106030980c3c840c40c1800d015201086040d5260700d10815140c0180400340581d085034000c0c0311300b00e031440144520040c429074200c002003c00400d1504c3c0c010051001c0e40c402d9018076103030303000820301e2084000100580914210002140720340301c5002400d240152600d07842d55045403444045581d1020f680f180c01c00c0000c001580141ca803803001030000c2c0f068844454001ea00f12414403101c813408908001e034280d14006410000c035036000038500754410f24003069802001c112443d000740c1401c0d800612528031520020340083c000c410009142c001640c4500240c20000a80310840c0701c407010380310004c00702820203019a6042d5910003c3c03501464010000700000400d00c006184200c0304600e84007080600b140003400c2507400c00032511601243e0694586401c81400b02c0c4040c414400700d0f12414403c0386 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 554777508 1250 554776258 554776267
    0xc0308040602090415060e030c0402040f0e1302040c17010902070308070807020a0b09030901110c03120a021c09150807080117031c0e121e03041e03050a0e03060c 71
    0x894100a411080c0e0703144e00706907201c024038281150b08001801920044e107070031408016000405291032480401980128011300041084680207990340e0140e840b245401c05007991100d0801d20f401c0190a006503005d824140101c21558014a2183d050301d12210300700e1141e030300c0f4990042a032003402002000101d00600140300c291060740d0310350700f0210510580380c0c0300711180c55400301e216090f103059446801c00541c44c880c0d9a04411030011915491000e04401d600c103c5c0040d45411880454440c03089001410f00d417000e1007070066100782124120502030b040c604020042070b02c402402614421002010500000b074002e1710840e10a55140d0b07075010850303023800444000300d40408251003d910041c404a80c10310300300b0b240340700e05140c1c0b11b0300043c0220688440074681031030421a5009110200a0000904102d0034070301c4400c2800401c0503566112480c1c04a02d4500c10001581c01c01001100b000815620100a00200c0400d0b80c4d80d5202e1071a103c01c06468840581d15008081410030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 554778758 1250 554777508 554777513
    0x8040e01062604020409030509090106020615010e03060112022407061823011104080604020a0501110a11060405130509211207050c030c010e060a27020a12080d0c0c030804 75
    0x1c10425501f84a0b04e4450305080094010542a40d4280c0203000943c100c1e00400c4904402013649418020003480c02030120195940401d844031018041c0420504403040503100795220f0540352107105d4080000c00c2a10b4080900741356650b0003402e400c9a802e814580a200c10f030486201f4440c3c40c0c1e030460120740740800320781281000e5201008440f0b07102d5480c1e184040603a01542c000d4001420a84050403841c6064410000701450b150415414040240410646000001102c0d11200d42c0140c410b580c45a070b0800103541c41c021544525070001c0c11043c9100350078401c2d0800d90060091004803008119a2000c3c0c04504000084283d6084014018561030f020080012a0880c00d14101203244c400d502c10010f040d0b9000c2602210f0f203a4580c660300128501c104180755200070b83c00c0c0c041100c00c014920f440b451042c43d505600c0080c404004010555480d14240e60080c80031b00c1c03010142808510384103002c3e400807501c0c02a102d19049490704c0300c07401000460320b450790541c0c030303214686d1300c0e81e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 554780008 1250 554778758 554778761
    0x61103030a0522060b030d020303090304060804030e060c0a03030b030c1c020a0e041b0603020f04030f060b0402040f17060721090f0614061e010c020d08040e010626040204 75
    0x50121110b00283e84010b04080402501240c0c4039008103c042105504941818a4a0309007039001c41158002c00c10800c2d40c59021051b201a51410f01c0d00300310070b0700d5034102202e441070342050103540041c1c001885000c000d0005006e07002d4510a480500400914108061f122030b008251240c100b0300601c1844e0405043e5070926281910003000b403501e4a459400500c28600308a8045400e80319000c030144914603200400c0c0b00030b20081c83e080d4600400c3c0844140d4500940c44018600c075000c440600030010150011501010b01400441d100c96545140981050b02e074415044802140d54400c603107203e011804922070011a180d4a860800207800b003045441e40b501a036880d641e0700c00d04480066010608950300c50700560000c581c03c980c003c0034540303c0c180503000612500c0b48440c00070a40c2e0f0708894501c2c03000400d0070490017111050000c2135500b40c070307040000c116034400600450203411103c081b50603211940d0352124040301c0c954480340101e0185881d00182040800020010700d4103 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 554781258 1250 554780008 554780011
    0x2070609050123030406020c06131106030a0207170d14060f060304050304080d0203030f060315040204020310090207060c1b080d020f0f0a0c1e02090a0c051c05060307061103030a05 79
    0x402c5141140500f5681c103120842e00180e40c21601c1940009400c2c5440d17500300069500402e108205a041264965070107070b400300400e20b502c2c0580320200000f040d803103150341910103954001c1980681c140180d00c1c1d600d101da014072035807014540361051103040750003401109403156074080c00204030445000200100d80d00000c0040364103100030400840d04410030b121405180400341c00440d1130341030018404440380700041003036000e030307205008040b0603002400307509400c2074041d1001070b41c80d141c121404107100315030341000041600020340e000c10400c141e030201c001a4900d50300d0740705034591070403554000c01400c000541207081c10b0001c110145180d84c002c00030080800551440d06a1001014103950040c068000c0400c2100e510b0009010001d040d100b520590184405511061a80080c0e2800e0300544154081c030b503900100f104680c080d00072502006640c042c0742c4541c100b00c200c0301d009000b0440760740b80a4001d00e200010104d02400003403840d030526401071820341c0c1d64540310b42c004040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 554782508 1250 554781258 554781287
    0xb0f03090a0c0b1c050f060405060a120f061b050f1c050c07020a050609210124230f010e04091403131a0304020904080403020406090615020706090501 66
    0x140c496880000d41c1c0321507204014090b0103d034030303141e0b04c6912200d081c500720044001940c609000412080e40040741506900c0402210000303030307079101c240c042103101103590869071072070300180c00030340034001c429280d072140c1c502c125000d0000d400e4000c81502c601624811003000b1590900c201c03151100b0700c001801c03500010482103174441000540400640f5002e81d0300000d4980006403403025410000141d034040d24056600e44d203040b00314804601e0044100302d426083c656510341405811400390043c88250310f00d2100104096030300c0c08504500c644510605600107290b00c1010703898160307410160340000e0300810714110740344040c0042d500c0610070303589540d00a0ba075150460000c0c110903e070301454505a001503494802c0640511190300071504040c5203007203240e26120032192190304a070350280c1d043c0c1c0c0700030031603d882c6004000c50095400080d0b029080034008203c409850340803c04640070084903050f030107800b51040c3d8035001030707025200025041000c180503031750140311140780302103 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 554783758 1250 554782508 554782513
    0x1a041d0901021e040503011d0c0d02130c030212090c060706090302010b0a230d020604120213050403030b100e010c0303110c24220201031805030a020a0209100b0f0309 73
    0x29025443e40c0141610402e62030f66848001c1414483c5080c00d110340d038240c2ca421201c0818a040d4090f07460fa0300e003902c00800348280203140c410780464507284c030b004040798001c84c414450030450407406000307908131704404001104040000ba508000025800200c488013030f0450b49011410380700c240280c8500b06069040d50f4031413061040a8403188041401006e20703c0c9100082031503203100940c40100c40e52041d102d40c21b20049230300036035076400031101201c0001e01003500c0c203c0300b84003180f2a401c240d0f1a000c80030745017104000526805800000302441c04603841e41c1a604446000e40361044950102c50024440031442d2000900075030010841c001d54a000e10300327000b40c0c820954a04002d80c9003180010b44130f0004064950362440c00b9640000000151551181e0485012518a1f140c0d204c068101a00d8603d41e01c00c10400000c0d801041d40c000c000e503541e4015400019589000490089016403148800a160500e41c0b0b411201070340c41c004055840e0052584031111207030405881c1407441d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 554785008 1250 554783758 554783767
    0x504180f061104260106060f1b020d12082d0f180a060608070504020301061215030209011401020601080613061d25091116030306030507060203041a041d090102 70
    0x45800713040440c0281c0840341006081c629a500c0501359980c80c1c0c0400d060040008540d90314540000341010b01690000e0a03c03400c0d20306000007010590135040242000e890120408001940490280c0c41070540d4503848003900e548440009110f094221010b80290510021841405244000b9500f000000e1140e60100d241d040c10399040c8043c0c001c00311003040e40e55108110750082404004002c0c001201d00b1402c5601d0210060300c4080c0000351001c04030303544c035410300c44c3c9198038244001454000d0a02c007020740e110ba1a00ca03030001c1040e0b02038050311507100000ba1a9400281c102d00c80c0c0c40000c40c9881c0280d55a503898003901414100d54a489500020105010010429000540580f000750103030201d600000301407495258020011040c1410065500c079600b0004441483d0780c01c4080d07000206107030a0440040003141c0004215000e050b100140441c0d00001500507910b440207415240c1c8145005242c07548158031882c1a00480f000c0040c42c109010010b880d4050000700000d03190 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 554786258 1250 554785008 554785019
    0x918291504110a050d060806130803040c2102091f090c0903140a03080906060102060114030c1009090b01050c070504050c0f03160f300b18010504180f061104 69
    0xb580100259070300241c4003203500070f0314411a01801c40103140180180000d4140044802500c40d040c034409084e5413000004501003007403d03004480204541590080caa078500c410301f40c1c0030034100300d040c3d100b0514200880e082c0f400c140f0090751012001942e00c0269440c200c80040503100b0b8241010a0110700031001001c01c9043d52501d118449a1001d03043c1444180b130042c0c00000d000d00400c0c2d0542c040010080d0342d036000991181911504030911200d49000d10020303103001c0140702c88540044580802039040ca0300300c8021020350700c0d441d40501c002d0001c0001100c1c0c6009607202c462940d800300f101003040c1d06280d4801904005000030451602d940007484144030751090301e0b291006a490441041480d61100b2108003848041c03501d121211040200425042140000c5041c082c7d0f8442580c000808c0550089411580180c50604050071611011500090911a1034051400c04d09011103080c2666002c0c003c0035031040345080e4204844d1070b204010502c2699600d410182000042103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 554787508 1250 554786258 554786291
    0xc06040503131d01090e0c180f0112031d041806050f0105041109090405070e09160512030d270501050a050601030c02100c0302040b0d020a270605070c0918291504 71
    0xf288c40c03918540800c0c07410301d85690703040c200059200082038080344500c0350000c0e90044010802d0f003640310b1542003002d107840004000700401070a41100e5a61001442c0401a071034018a01c103a443d00d482401c16a81d40003808140d9002d007040001c00d0808015050140c0342c00390044c1d40140c000c00c100e450603600c404644a1203001652624117542c45902c100c55021080445440902010746042000c50050064581e0f82d002d03080f0124074498031448011441040003c0c100da01304134a0884401d51621401c24500804041d500d129015040c5000203240e940280281c0300e15400c035034014601200c12202803c010801c003541b030b41c1016000c110005444490101400d41036200d040016512421408050075072120a5a103910500e50242c0f08000d4450440000c02250140c2c14600d59901003841c20300c0f118103858004bd19a0307440d025207804280e0050015600b000e10400c14020301c0c0340c3d000c0510384111000441c0711f42000741c0000260f009100f014603105e031148040c00228905100c460380c0030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 554788758 1250 554787508 554787529
    0xe01020a050d0f090209010306020307030e01052a04060507080310270f1119031803090305072709060212010803030703060b0301030f080f0c06040503131d01090e0c 72
    0x30408140d032103940c0010f128403012483c0c215410000c2c40f615a0102da1140414130000e0300017640400080c1619019400100c400401080200b0051500d40d28103d03113010080002c040702d140b4803107021040d2165400311025070360075803183c60400c0d0603685c40200c3c650001703181c0400310704400400100d5401c1d02e1040e072103504103a1540725114880c58500c004480b8078901101000703081500742c65200f024070045403103907441c800c003040c914080c0354400c0e005020120098101210590400810705502003a4a410340f4421800d54540c541d495190780c1c150200302c04004482c1d02501d0700580341f41096480500c03643d00c2002d01609003420480d41d4024028243c0c880700e899000042044000c0303a051007544050b00da8180701e58250750440e100d0030003101d0009401082000d00042c40c00c190440c0800b519814543da0040745c0c00303841c044c9402c0d0303182c5e0000b01c49010550041c0101241100030314980b1142251000c800b040140c3c60101d050000d094040e09090090151020960340c40d100e105040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 554790008 1250 554788758 554788777
    0xf1202150c1e0310090c1b0b250906181205010615090b040e071b080a02011d06150a09140402030c010c0201090b0309010204120b040b0603070b070f05010e0102 70
    0x150b403500c048072003468142070325840480910200308100001c0036092004042950081d000000300d0030f41c2000c0540d002c08204030704849506904c40500c0c03c2001e055941c07032151444400703100b030310168407880f001c4c4051220224030110b0250303213080c4145441264002d0f500944502104c00d100e9554980d034003141d4052405442507510340c207085c4901000002c00c0c40900f2654035003509a185080303c0a06680514040d01042648001c0852a8030f407007050003503107204c510800c1c6070b1860910310f0302c0502944500c5c4140c000d0750030052a10341c400c186041121981d44900044c7c14165507040d400c400e102c00e01c040072903002011060208001d2800e204810104807880d20101140c1000c0c010540341007248040241042518052a00140d84c807048000444400d14503036078403500d6080000f406402103420080001c1c510803656070070b010540940c0c600803405460070154079104c080516440340c0580c0982c3c4a8038504200101c0080d003d0040c1c1d1100c0c0f07005c1c000025446c08284001c0d03003681e02030602c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 554791258 1250 554790008 554790031
    0x9010504030f0e0102100b030705030319090902090a0e041a1509060910170a0b0703020d0b040b03060c090a0305160503061e040809010c0b0703150509040f120215 71
    0x1004200740c1c1241d9040280110360400004580c0c075200001e6458402c00100e0039119204c0d4008019134404004000150100405407030722500001071101c45051006100341c0050507519001072060114800c8400d0104003034940d40b004c9007801c0300203da40c04041c0080799005042d0320078802d03200740f050f0070a00038115136003485101803210041113500c0300041d223080d1084c0690014800d4250202c5001001c513110b00c1c2d10722841340c8803819218104000030201501d103249890800c01c500390b155000b80181c2c90800b07010015502d01c603050108840c0c1c403082c02c5405034003040214919284403c00ba00f10404001d01c4260b08648aa40365400c162651501e504811070a500c1070100380b509003c03039a80f04c5000308a0124140464030388889406015102038821700c4005421406030f4480c038041d118240e000784c050f6003e8102040d00500030211300c5100e48500300e0303020000c05d10389800140a400b440d0004a0001040c000b5101c45100b12050b00741c5405610074142c40c4c0b007074048016010f0b84a0701c0c46007213 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 554792508 1250 554791258 554791261
    0xb010c1103031c02180f0604031103120703050301091a0901061809021315081006080a1b0f0318050c040506061201031113090b131104111804140f0408040509090105 72
    0x80d503c800300c002901648512201548040d0755201c0c3c7c400c1da001c0f030ba000990146000b0200780420b04007001800c001d60280c6001500300107154004004504a0310903000c108804404a00040111030344001d8241d071003581280100903145c8103250000154040040c140156607943d132513a000c9912035950100f10046120040004807d0542105454001400e0450461500a81c0098410403a02a841c140014403020030403203c00d46e40601c0b6450800c005178200c003c43c1c07501c003615004d0f0400c034a1300043e04080711900c03402c201500160081d54010001d20101d0805400c105c09440c0040a182e003100052244440c0b00d1401c4800c58001c40c09840c13038440d003044034000d100c031000101d84020b481606204c4120b00007030f91180007907405100702d0f200b620242024a80003800768055500c0c1d80e0700038208040304080c0310f00c0b000140f8000c00c24401d0700303004e07410752010b01c4280d030504421700c509001038000140f41c075182a800b103680140b06070019131800307455600103051880155090a4560f40d0f410 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 554793758 1250 554792508 554792527
    0xc050d0207030e0f09090a06090303021201090518031e0d090206070c1403061504020a020c040c020c0a0e130816050613140106030206180a260d030b010c1103031c02 72
    0x42440c600f0a4044c1c50140b600e02c0d1598441c0d80e0341084900c004c001c3c5075030b4410751080c14484d506403203407884008429002540e41b9191030014280551d001c1c0042010940e0304130b0281c100204850704800160b020002c00a034003c000303000c43d0800c103c06e5400710380b504401401a03446e04014691103104000844031242484030b000c100c04442030015000303600c48030034032034110b66442403c1d0144000319005a69048009d0b0f0884c14206e80a41403034001e0b060018214001c0c0d00450080301c441400d0740c01c269840c1c0d844c4031007001d0a8083c2c65030441c10a0004000f00841c450b2700c028410402c007862030788503482c2e80d652002c4c030b4100211500b02407500d1041015080100c02c065004e040804c000092100a045400081e560310482a40c00300090305144020100d464181d45400140b40c00c00c0c0350007040b0b000c0b141040d07035041221701d0940c2500030700d4192540b0303074064803600000c400c06954951011844d50b032070b0114811048040e907032521084c00f961151045400f007008000f68811000758403080c004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 554795008 1250 554793758 554793769
    0x9030c0607090b030406091a010f09150e2707080d0905010305040c0e06030c0909010903020f07080c060703030b100c02090c041d06060f12060315040807060c050d0207030e 75
    0x6400c0e80d0800804030b0042140d0806041a240c100e600b183c40010440c005161040200f4402c100c005507410500c2c00025401903042519000caa072440e90038040c561003494001001961405580e80031404000804c4038103140c603010700070b80716003801000340080503810907900d08011a03100c441e00342d00c117a10140c2c080e81e121343e800e8010034007800e040c8002d0030b09580e00c42c14001c1ca801307240341c00a1424001080c0d40d070304100a5004510207410b68a0703a0400350a0030b400b9012000c82a00540700380c101107400b02a00207180803ca82801001e80203400800c401c200c030b240c0c051402682016110080290303942c3c0c030750500010061685e01c400318018081e20500c408504000d09142d60401d050004000c04074800c2c4524100daa000e0791410035a5607a82e0014286018a02d1074025000011614004211400142c0c82c05103100700c04440440d03120710750310f0386481c03803c6500078100c000501c07240cae001a01580100540711801d0814508043c118441c040c1240c2180701b05a00041d001a806151810316 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 554796258 1250 554795008 554795011
    0x2070504092301110a090e0f07090b090118170d050c070303030e01060830040b1c0605130c090906060507020607030e090a2a080a2309030c06 62
    0x140d030140300e64007142e1280380604001207050740314002c21030b124509945080d0302c0100381c062031401c4240c88514802c0020404542030190b00c116442000210321190004075505100da00181d8030b00c240c0904000001406811804030705041c4000d03504240c3d002c1040c04030340c0000d001d000c0928900c80780320742d002ca80750401c0c1580303d20034001d00b00000f00d02d1100c0800d40c9801d5079014280460141d5884d12034138010310342d541c004000e42c01000010301c00b044c28042c030075488030300310704581a0081c2a04170405440c4190301c207202e102d14003000700c090040410382c1e0310b085101a2000006003940e803200441c0302d80585880d41c40b02160741e41360000c40710384c0141d0310402804006408000850901070082c21b10300c910b9201a100e6800032880d4070030540314980c41e03007550718058071f0740f0401c0c20b0114155002e07040102c483e80155a40040c05c000404410100074035900e0190744262140c0c46103140c00300145144450140121b0300880710303020128005000314040c500c0a0002c594491201d04103a060810 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 554797508 1250 554796258 554796269
    0x5040b0601170114150d0b120615040b1336051509030f180901050613090b0d080f0309070e0f0403050a0507060f050103261605150103060c0207 63
    0x200d00b90720144442090b00114103450741141c842d403800140e000000c0c1e82070001e95081009102c0040c102115903220b40000c0c50700141a951010011a52840691581c2044078110090031101812465500e402d40180d5050107019110303900700d03650300449609a40b5a07000070102107500c3d44070822242e0074040080140d4070401c3c502c080c002040d95a55407a01e446900b0069040b00300750210301045410300485400c82d032030302e0079642d6079080c58140d200c034030410591540c80380b402040001001d0800500f2a1051503071881c411075481c0c00c0c250070500802600c41c807a50051801119800001e50349402416000768020f00c030382e101e241200b442880c059154000c4c80c012900c82e414401d00d03031071400d1100e400682c942461500e80c4075010342104c3c9400f0740140606102d0402e140290781116580c000c1d416240105015140581c0d00d1145141380d444069501d84454400c100300390007003810000444006104100f502c4002c000e46640b0414072a00381c105584065450064400d12034042046900401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 554798758 1250 554797508 554797517
    0x20c1509040c230a020303010902031e01032105030606090d060e100203010302040b0a060c14150109020a021005010803181c08030906091219020705060c0106091125170d05040b0601 79
    0x203003421340c000e4490006215080c045c0d074001c404a2148a2502402e944441c00d981c06c0d042103695a05000e524003401c0f448070124910303501c2a400980d84500b003104d1103060043e0145241500300c4013030061400c911001a0741195884034864601a8140160700010205510150702d170f5045004100031640e860000a1160084030b408108550b008881e4400041e004110b46603460001d8204600300a4403800c1d154024000000200d0400c0203980070b02808906070342111000f10b1002d43c10011241c00380a48801035000b03100d244034030595040b803900356000241100c4a0504094808580030b00144412101c4400c04803c10034520810004070b640020803000401c05100301d070b070804586208600205845d450905c0400c01554020464000200000341406179a10044000b540c006c4c0194083e5403506414140c141d00404000780545810000d5000c00c0e01c56444906058001080c000c54100c90a0a2060740c8411003040c00d4050300104403500e0300815589414540405081ca00a150300d0600 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 554800008 1250 554798758 554798767
    0x11a03031201030201050721050c1b13020a02030d0504060b01020d0306050a0510020309090f061018090c14070303060501171e06030c120a14030a020c1509040c23 71
    0x141c0d12a00003504494080c00c0c059520000d5081810540a40c0740c0d840c048407104a07040358013964820002c182c620346440a0b203941c4840000801502214603050030703480b401300341c4a900034502a60081c20540101d004030b0340f500310b54003540000d4400464040d1502907803010b01640c596014482500740008500d800c000460900d80000c844503501c3c01141d00405010500501260080040342c59800e0000c004de451307440c04a072501000305045503003602135543c6882000029000300480f485001888165004035424805490700402415000000308a10009100e0740c8010440c010044c55003e6038002c50618200310024100404040001c0f100c0341200b01048002500890004075500b0008010901da803a80c1d40042c0c60700441d8030089905c040404030341440c0302e0001070800750180c1314a404660080801c044151240510110000580c000c18101c0d03405191074032011440c01c003400e4440703051516110105045641241002011607110f1340408040c2c081d51121940440c103141c192443d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 554801258 1250 554800008 554800027
    0x803030705070609020d05160302040b010f05070b0601022104090506150d1a0a0b040801060e090709050606120414061006050f031021060b04060321120c02011a0303 72
    0x903100308800900b2880d581c0700113604554481283d00760700341e0494200c0e030082c0e1101c40002440d429502c0103d109503d4045a500c3c154042e8800700c000711459200d0030f041c0800c988031035440710300041c881c2c3e0450048000208203981c0d500102c600b81164400015111f5017440b41950848030083c0c0014858803501540e059403180390404c4036810048500003040d68000d00d40c10201072400892102d90041c0840008030f44030f40c280014104a45441000703215280d0344840d103241040060780e1001c480e030450310050060649a40086400003400740c11507160400200032004076020994084403810605010440411030802285801c05060dc2c1c42c103150700c2c58150080c000c1c1c0300340e110414600d030700400021090381c4000891001003140600c000307040c0c02c9607807083c0c4450140c1c02c0d084501c0f51503c0040d20943c10144a4241a83e07070222a80d0340030008140e04043c01055284101c0400c11100c401040b441010700440c401d0700900e400114032070f868188080c20b0174241c61702711402030344140304002d01d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 554802508 1250 554801258 554801267
    0x10506150d022209020a02070509012610140103051c050a0e040b04020403050718060b090618040e071a031009110d0e030d06080a021f02070f080f010608030307 70
    0x703050089a60050b59070548200058003200c0303801d180381c1140d00044001501d40740c00d0f001004080c82d070760f084e1020142c4440401c4000c000a00230300720008003003d505203514600d0104c03604410f600d04100c130703402d040040d000e1301034680303500601c94000e8616004008000c0c01300070001001c040b01005c00e0540f046103500610300d02429a030f0a0800218080300401a01c4071390000540e004003030029960f554407401e0503030f80d0718501c2c0306000d0040c841e0720407001840480e1089206840b042c1304030b02d24141144041051035003200d45403a1046114041002c20350f039580c800d6039800c1010b80c2c040c02e651840d003000c01c90442120200030304250803c000700700500e0180e002d440c09540c1c0c1c006000a000d40d444c940346509000700d0b9500b07002c0d01d00c0d1100300340e280a40003002d0710070a000c85405001c8191902c40c3d464a840178103800030341040685184415600320130840403500040d601c121004183e4862010302c2030106944421a1a0031007100d1088000b4280540005410076034011032a40c00c2c8040003e0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 554803758 1250 554802508 554802517
    0x70308070c08060f041b030512071202031e1305180403090918060c0504120308100f0e06220c110c0d0f030c050a0c080115090b0d020118030812070201050615 69
    0x410507000c03883e503a41c01b00255900c61000d141c11408580c2210300f14942d0b14925400000240c6031242402011102c9900c008202c641440054101c039100d0141c921200d009504929444820f828922001080d142c94110310f81680300c208175902982c504060801401c649002d0300700d072884504100030014060f1402e5545015580d0010700003d01c3c100c0fa90b0115880d003d60307040f020001014648802c04d1680c408940c501402d80c11a8003400a076030f414a200e420146403181401c85944940040c506203004407080b01101c070025441c4110b5030311014580100da2001c20f8090209030460340400d006481000450711050054803003c030803505603103801d180d000910b880241044820b01c40c080801c4070900002038001e81c40840051640e803200d81060181190306407130000c509550750300040d4110302d4082c0464030a400781074242101c80179001140c80c116040c0d00c400a80e503040c0d80c00400a00c04c100240704008485802400c0c500380324070028291a00a441103101c0c01c014400711090340d0000e02100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 554805008 1250 554803758 554803763
    0xc020d030c300204120c030308010501090501140a09150f02010609020c070b0304080d0203040605150307150509010905090703060303170402030d030f0b030604050c010306091103010902070f05070308070c08060f04 93
    0x25590a00701e0b965903000b070311071038010243ca03205801c502070070000700b0400c140070380e031098035000c03c1c40c0e0700d800c01142d1500040c8591030018091440b00780400c80310b00000d03c00240c170313031400030074603034590482c81c0d9084c0d1120010800101665160045c184c2e081c450790014100c000790942c0b90804510805507500c1c40307406485c0440e40000085410070501c0812944603920b090402c3d9242e1400b41800300c0180812103000908a034480450400741c03402050507800c0d5442d4054485c144859007404039990b401a940d60f03414031024540101c0d00341d444419642c40750703581c0e607400700d895402d40c40d005110205400f2425070100d005c0f41400010398006c100d0208038401da140001d42440c224811b600941503a50b0700c590540958014042800800700d4542402c54007a241800030954860143e0b0880c0d000001e80724034180c05000600c039806131600101f00c5140580300405c588101920f8441c100a616071041300d50000009216042100b01480a0000c12054014201303a20b00f43c0c011081d01d24008200 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 554806258 1250 554805008 554805077
    0x60a2a0503090a150b120105040507030b0c07080315030d0c0512181804061107021c0602040b030c030103030306050607080318010219031e0506060a0c030207090c020d030c 75
    0x2d00c81e104108081c02206401030078810030744210218900c0108002d02d02ca41c050600d130f80c04082020014020280240c0d80007000b4610036185403542e5100407070103000c2d2004403004000da440810100c1014502400d08442031554066807038007058548446000a201840050314114001c6140416034080480c1d0041485640b02915141000f00703505800300c49500400700c1003950b80001c2c8041c47c0c603200b90f104610402183c4940b600d000e50354080d0420080d40300301d002d000a00c0784000300480d10b0080b48508005030500362030701c0c14402c058004444035103030b105c008001082031591502034a0000c0200351280c0b443c04100351250707c0309201c006c203002c0d0b1a8420302156501130400b54129a050222104140320400c01208000c0c043c01a00c14080000701d8490300004440076503120310350290390000c01c2149070005410080d20000205c0c03c05800b54060428001090070350780c0034100e5464800c1d4003501c3c0781c100d07641001c2d040b01d040c040400104000d045152080c03110070050a0000340003244d0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 554807508 1250 554806258 554806261
    0x3032208040e060d0c03080a02210a1d0a060c21121e1a040501090b010e15070b070f0818101113060801030515150103020a030e0d02060a2a0503 63
    0x480c0c54000d50340b00040c41220f15610006c14046010040c048041c500d034241c1d0b1085c2d4045c44400d041c12200c812075000a0002c020698201d4080c2c42400e020031f251105120007034100f0340008840019070390001e4041507011403031108004801c0303c05070101011450404468022200090480c155041041c1c040d90b40c9140c0c001c40001c1345900c4641020351140c082c02803004072003e10b9903010050008074082e0b410b00b0300204e80c8104c82d00540d00400410b0b900c5083c464900f8041111944c565224a51585c20410004011604000d00c1510a41c41030304d41c00c85a144000c0c0017044290014040410500810655400e55001007880220240f115a001c0745222107200d64426510070010840380407044420000341e05a00311b0076681c103e0b401541034499140300c00c031132032042c0c075000c550460399840c426114800301c1d03010354064015142249400101402e07005100c903e00207100c05041e0150744200304000500b4000c1c01080f01411760b4074070443c40c4608004016030300381003203074a42091010120 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 554808758 1250 554807508 554807521
    0x405040515040c0f030c05070209150d060609020915090915120601082112010b0d02040504090609060c1107051302160c0503160302241b03032208040e 66
    0x8000026100040040219002404014001090500411010a0034105201903180c05141030308ca186802600010665a0798051000c3c90000b5240c203943c0916024903010220b443d52140354050908080c005945900000400c01c86c4941c00401c501807a804029046554031030905064200004c9245032070501c07801000030f00c4c15032403607101d22801e01c602d20000810400010710003070388030100e0450f008460369420301505540f01c0c000c810304481c0146401008070314008401011145c1040c0401030030700b602c1ba00000d090f0b81d60060159041c84c1c5a620101c2804081d02c2403000030a003d04108600700802c0401585640c2c0905c2880d203d0083c00580c0007200e0303101d030111001c80210f01c140d40c5041c01c640c6042c0081005c54020203000f4030079500c21892500c43c0140304010340f40c009120711000d585601c44200d034a07412161080c203864007400201108010b800300d10f650002103001071a22450060b640b09503010784040314022902e02900880c0c04947c0c4002120140d030400101c008013903654a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 554810008 1250 554808758 554808781
    0x30c0203030f180901080106060f08100e040506150a050a090926030417030c030a09110301180219120206070606081614010305010503121c110705060a0c0504050405 72
    0x15084005407000051030228943da6100032002401c001c8598a9580e40c031003001a00301c44440c094800451008814091001e00030b1141c6075100c941c2c40324003422603490b404805801c0909982c200c40683c494000e01c5002e40c402142403541243c2a9140344d9640d1a0000095940702a4490400041e80d40c5800e041800303a1681710010005038420030b1410300b514514032526582c0115429540d05d440a5074002801e1410340480b8000c0d00c000180c07a0842e20f4129041009120342d8008a5820b4001c00907034610340c50078024071070b4020b4550321409448045005115400c01c4003074480c51460203220061100001c001c03a803080f000d405841c5a40c8615075071a00302c0c010702c56504680f405100e800741034548800d8610b545c2c0c0694044010210b1150090001501a50000c3c0102c41c0c3c0350300407085588840c00b61328060b00501d1446c1e2225940b000c3c607415408205e652a1400e0203036940002004030a00004000c0c281e0450040f8100304950194400010014051801040d101d207403220b020902c0c04000303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 554811258 1250 554810008 554810017
    0x20c0a0b071b0605030403020f0a0f030516170912030705150405030c060c0304060b10020717150a020405010305091b0913060c0207140a06050f0313150e100513030c020303 75
    0x5a070b000d84401929800c014105401c212000c038018441d44040304a40c1101240c2d05103495070148250303500104c1a81c0603142a00003124606501c850122100d000c1190f5040b085083e181c1d80a003555160141010700c20050103616201160703a10801006c2c0000c1c2c40003600003005071807054115081d803991700d0309a0841c411011400c00912410303050003911100079005602661207044108130b64030780c000500c100307003516100090240e00704a41c00c20011640c6074000111509860641d0460100340c0c581a00040f010380399107299940c0864113000558062065a1700040b9100c01841800010101d40c3c11070300070010018010740c1c1c000041242d42c80358084c00481954005030520613500240d40095980c1d0262144640650294207020300c42c1c149a01000f0985a20740e0f2042d03d0004001c1030300d55168006040c0c40404801d03400c0308800b0504800102c2c003100040d44000c80c1407955008040d180484180380c1c282e045281409100c401c0402d5580381c80401ea05091211a040c520b00001e400d6024 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 554812508 1250 554811258 554811293
    0x20405030601092304080307031d0d0e120c0306040f02040f0f020702040b010e011d0d0f0c06110309100e0414010b0703110a050c19080703060c030c020c0a0b07 70
    0x6801c0000c61100066000302c001403141118119100c03210200031500307850240c4000c1d00f0303508100701003030085119070811041348500d07800307107190101481d411a14040c035102c1d101c0700090000039604410310b088400e46191840c80e038000c03e04208401d000a0301d440001e08020506848100700000b1034945400010007007040c40d05c10808251518640c50217035001c400c2c101e2059182c06000503081d802503005c4a078194040c0d56030040d030f100c819200d071103005c025045103500c4021500c2d031000080150070840c036403922034050703408041d28002000c0c10042c0510051501e03604240009a8241c5440000815555980c03415820015106006c6401812200c071003000740c40d034000012410320b090300c008040492080d80c48440c41c0b0808000c545e11410981c0004096070080c0607507405514211140603001c0400c40c40006605030344640305841c0040d9070b80101c1d5485e46641481c1280754140c455800099043d00140a81441500c005507400750036003d0b2001c652400b003202c50030f1050348039070f01c0c14a05 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 554813758 1250 554812508 554812513
    0xb0f010516080d050a0c080106080a020d2a17010503030906030717091b06120f04020a08030d0504030f0804051c020f0a0c090b010c0f0803040f15050106090801090b010b0a0302040503 80
    0x20070300703003650000d000211000c0ca85c0038103003a0401c14061007480d9290481c3ca0640d16003002d0b0f01c3d40a0000e002e0b40c4805400c810142d100ea1030030b4540c00790750301d08100180d8008200740990250b07a20240820b205600074220307030203c2d2001041152004002c6584142341120785950ba990340240c15107152a480c2c5a95210701071b07031800c2000107a00000c502e00001d0242c030900221051000802c03009215414802c511000b401020030a1401c84464243e08103200a0402c00403645031201140b864000724450f0b107600392600d00740005d040e04042d44048410142c038080a151401d030b103410f542c41c41d60314030310321036640a44040c1c0e5440d44284009841e403401e85050b07500d0400c26040c18056114640100e8542d90b180490301030a66008005403103e40c3d40c00098858035142c6920742d20f40c41e401c020800c0e03458004045070040011400a002032480352090400544ca50429600522018981c0c10041c3c0c0c9a01d46082c400c003081020ba505d9044401442c1220b961f08203e06048001e40182c0d80900e8262 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 554815008 1250 554813758 554813767
    0x60d030f140c01051e091618020c030f07020a0b07121101150b04030c0905090d0c051e0a050c0312160809061207030507180e250507050f010b0f01051608 67
    0x4100164041c01e0004402c030740c00c03940f41c1d91b075a80e13190780d21200c48803107071110040708201d040c00c50b1000844210001c840107003090303410070038030f82958004182420705120004101c002c51a019100102422040049504190b81c99407845010307000b036900c00b02409214680301c51044400d41158582807200000607640d82d5450303010002030f40107400215510181c003c4040794102e06032080b148508041001000c00e640c205d602966005c054280a0756540101210700000480492000f034510b0310100040801c0c1c0c507107041203800e05440d14441032085e002010303203400d0106e0401c15258a01d180e40095040f0301e20718038000303102d0301c1044491500000041498900a1501d05c1c0003489000c1507241807046640302c10046074050070f00403e81403000c04559060100e00c04282549621445500c5101e1003034100d03050b52900801d1114000c40040e4001500700100308040c0048462030302ca020080c400104100b0009491505030340c0d8007810098081040c500b0510562803804850b83c1140015940c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 554816258 1250 554815008 554815021
    0x60d090221030a0e0316180605061603080912031f12050d1706030706030b01052b0b180c0a05130e071e0e04020c0307061103010608060d030f140c0105 66
    0x4030f8122520300e4012501850725007000d800d001c15441403d00e003c1440714852420700c65644011000c40d2174248a180e6144c40100366a11800300514020b00344400d401d0a800c187c2ca4000c1546a0042c4841c6c465001001080580e0110005407600002007540d0700406030030703054005440c0200c1d9400040e81e08840500300e81400404116030b000c410382e076511809544d1044d416001c0c00d400030b03200540c05a009040c100030042c4a0342c030440d201c100c140f51481c50f1503100d49104a0341d203841216841c6c48100202c041c4803483c2c5605c2500d246035000c0d688000312400c80d2226485007600141200f1140000054803074417a44101c00300c80c01d00c200300143c4000d440e00e070f04580e11014002c852100124550320484e1010420001100403a2160f07556000d158910441c1480040e406c55444090a07200134019071001030680e004007513185e43c81250154682d0b261041c0204100c002401d22800381c21390140c1940480d81c0062940c0e0303107402e9420005000d41421030900b241c3d00c00c00c210306800c1e5182c0002c0c05078 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 554817508 1250 554816258 554816263
    0x161811030c19020613081602030d02012408100b03120304050102190c0803070f020f0d0806040b010e0a090203040f060c020102190305071b06060305011e0c020705060d090221 76
    0x541060002114030407007400d0b0310590351103509440c200d0069107000308400015a103840240700c480d444e601d071810609001d5021034940400140b0f0720025035103d0040324001c50030004a80c161582c0440c1d440c1d007603482d080d50951210354a4812003442c2c0d0701c80140004a0b14200505605000c078904181d0350391500e8140b1500030b4004511851000c2045840250704a01c03500c0d001c40840c0c1c200c640b061440e15054000e94401c000c00002c00190301070340a0f01c0b4007500051141454040300d5484140482c60304104000840384100040ca0501c03000305404965501c420581c0401e855a1001c0113036203454a0410131000140144014011400c21200c11103496040d0094903d40c070400c1d40c00d072200c80c4201010f6003510000c880c07150020f58030201301001019040120903c40740103e1000401c281c40751225030075507030010a03020065014103d0400c80520a00c030741000130310300303201070400b8904205c0003071010302c180e0b00f10351138041e110f111803400c2d581ca003405d41002e1580f01503116008103000c1185134 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 554818758 1250 554817508 554817517
    0x90f0c1427090c041806050f1e09150a08150412030207021e0310060b0a1d0d030206010312080903030708060111060f01090e032109250314161811030c 66
    0x2d43c174002034000810103e0141c00351a0646200801c9502191420780501c400110070100510492a10301e81daa482500c1303001035140102ea40705541407240e0941d0f01441400c2002c0d6001000305d50050f0041501c05840400090b04181c0c0704c025030b5030a0045003400c4010780600d007000f035803001e5204050003c8940c00e400c2e6400740c100681c1a500305410705020182110940d104d51004264100140c11406204248a04040d403041c0e070070900041003800031032880c11000100b14050781c07000740140103102c0c130314115200003102031400f80254507110b80880d8032408050503c1c800e001d40c2d180410017aa00803d024407010501904407049441c00d00704646d64000d081c0300f000a070b80c1c54240c2c48409000007000701e070f10150849160b01d10110042d00001509413005000b440c00c0e005500368481c141c1c1c0028494000d1400c50428800c81604505001030212000781c0113000030342c01201005c0c5080c55040c0d101e402c507a590a44051a81c04541154000d400e401c41045004400001045001601c40d8040c0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 554820008 1250 554818758 554818769
    0x120309061905040218060a03060216020405010b0c0c041a0301050a0510050a2d150203090301050604090b0609070201060f0603020c0f030a12020d15090f0c1427090c04 73
    0x50100d03500300c03500079007103620546010390002d8000c241300e40301000c03258050740c0015028000119059884e280c44003240c0044081c030020040e076500400c01e5103400e0080d0f80c05042c1d0b00014078036041c18903400d15a56050f03500d042c0c4c09545c0380c3c245004c540d16050001452840090001d210034a4003040309401050116814112484250400f140c0c80c10300c10071203429945800c00320f400c0c0f0090000300750300316040703807203100c00c5140401c0c0d011903000d003114070b000e400c060759070011600c0d400c1220400d4255000102024080c502d0801d01102092102812541000042e91000e15a0311070107000c03400350417580c00203650310030007803000a0141c1c0d2580c000d00c1c0180f00b90060714200300003910559100c2c410207149400082089604c0000d1075000d070b0040c841e401c1c140000294104030005040703048100c40c3e010f406030980e10650780c500d0300c100f40a8103000e0400c0e07182c03180d224148562070035190700580707088030121140700ca400d82c41040000701196142e00000c001c9809894a480b020555034010b0045 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 554821258 1250 554820008 554820031
    0xd080d110c07180e03070c06020c090c0f09130510051302281e0e04050907081e0f060103140d030b0d1e0f060b1819020c12030906 57
    0x6603250010000191620040340750040c040c00ea02e0421000c0b2105000c280c9004815552104c40d8404642000100f9007070340305407061180c05203003440c007071b04101300b1034030203070045000320100422890034604440380a4840520b0030348940311400811009607d00d400303032010520341002d010041d20040008021124222195810b44d411030440300e00340d000d511000f2280c070303010701c82c900c89071100104000100509403a242d1070a0140d07265a850703042900c000c00e000308003000c03c00d44840c01c19018042e401b0000354001c004851030301180541d01c0346610701a0032030058224021000039414070020741200d024804840d8156103a062012240b41c0700c0c80c1c0c0d52031901c140001e10041900034000c1020104000b0a50090880c0c25140c607048414030080e081a100140515000010000341c0d413590000e00503000064007050710b00034041c08598151513180903034000c40c104100300300b0114000121145030782e40540c942e0400e0311050300d04081031020150869011041000341c200001d405446141203000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 554822508 1250 554821258 554821271
    0x5031009020303090913051507030b011d0420070c0e06030f06010302010c02180a0b1320130f06110c100f1413060c120513090905010207020d080d 64
    0x10400100c80e1000350007501904207001c402c06503d0104c3c0c0042e8408140e40c10101e0321085540da1500b03000482c1580300f01a00440d0074045082c0d85403041507411503081c00c0441140300c2e0b00c6201c14048104145031442503469102c0000e07041d001c200040c3c1c0c0102030b0600e41d5181c1186181c8040700b441d95016a101f04400740740010000c0c5000552200345c800c844000e07111690a58004451000001905030317040500e100c80d8032140d052010036288500da0489000803480141d00410000410490b03546209030700308042c2c1d9070203d261008810800d0030582400d40d0320700b551600310f81c038107016074000358110201074000603503240c005001d24031040c10b2000b0744903094219010060a0000c800d030580000ea00c500100340c400e800390f01103016076800442c10604003030502d400c0203940c0e02d60780c010800207181c5455810820220f200700385007407202ca00b000e5082c49007481c98091410a00c2c480e84210648510840003441000c2d4100d032120b43e00504014841855414109981c0d8000c81f2603103c22458100d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 554823758 1250 554822508 554822533
    0x203010f050606030c0a0509060304050a020925261f15050405060a0c020415030302101116080c0313030b061e0f01021638070b070521010503 62
    0x1c01c89106580007840702d8191349804098032120303049258488240a810004480d01c3c4e5140c801651003a80b290005000c98003461040c88410203010f0941d17074403d201d450010300c0200c0180d8210340250004d00d0001c03c2d070141c20401d024013000d180482c84080110005110703110b00c45249000305d19040350385142c26255a4440100c981800e07044002c0011001d110034407031840c1c071a005048207042440e044043e8469500000d0031905405c0c01150b161110790f1003042096010b00800d942040d81d220100404010040040854840c40c0a01e4250300805421581000203a00c141c0304001d11000c100c0b82ca90052003220107a1480305d02050f142804502d0001d5040d240c00c401e003c40c126441511460448440424418000c10b4501454154000d005c4100e043c0140c4a820000411714540d20710650b0414840c00d07805050340f0390140580c01c1c2101d00c00054070b64500200d49040f64482103d02169443c3c040c200e03828022400200c00103883c0982503041d1351102c0524606a41084055600103034050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 554825008 1250 554823758 554823761
    0x60519030f1106070605010e01090c020109050c0906060706060905010f053708011109040c11030a052107020d110d0c0213060803030403180e0601020a1104060b040602010501030203010f 81
    0x40c440280701c03a019a04000028607000e8000054402c040d1031541403007100d541d208203075202604411044800c51004000c01d00c494002c07110b46e4503030360001b08144000354903284d448002c100300071401801c1060210300541c80760001c64480541003001009003030380f12103c2d100604003c0c403441d2401ea660000c0400c5916000244980c107480b80802c01e00c04c600210030032002c01d4100019034001c0c3c4a01e0000003000c600a0264242c80c0d80e10849840d510118001008200d4110741030003810425507400c01c1c26500c01c00411195000c2d0a4108640c854424680c83d80085c1c0c0d96090000c0e00b03050407030601c09602e40000349240381c4806600c0d08034101c5800798032240da46000f035540200007200e0382200c401608040d421030109103031300c0c1804500c55455802c40341ca15401943d00310009510f0310021015003031070010500c0030302004000d01c80e25081620001b590f803c1c42e194050040c00c0d580140710000e0382c49900060003000800745050300c569a80c04080d0090000b4030050b03009500b8034200210b60b00d0306 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 554826258 1250 554825008 554825059
    0xc0f03130e070f120903030b0a03050a02090a020f0307080907031707140d050a030e07050a0303091e03031e021f020c06060607030f080408090a180b03010c121a130605 73
    0x3d80c0d00c800103c580c61445030080c220800099003815951040c0040d913071944407016001e5401032006001c001100e00c10303c000c40034014102c9030740510510510180340345a0003285d4001c0360340d140075551511440c0c00e90341050b000780c1c00100a05038071058020850100f8010b407041502a5004031b44000452054507254094050b181000803001c03c0083e810500a40c424002c0a251038200d034408c03500c039004914503031441c0d04282e001c02e04072002001350140c45803144200010360314030000400c0c650f81d80500300307130010281c514240300c1581c41000824401c20404d039444002c2541060840b245c500410000d5210b0f421070b240c0707030140500041280c100201241c05032581a96185040f81000408441d142005031003102c070800300300a02100c543c2e82f5546400980000c4000c40c0d40c15402655441c02c83d0001200e060080e41018994012540c0050222248008540005c9425600c407030f41c91031f0000740c00300c10f1a071041da8502c5605600c00e0691004043d80d80c2500c1898452507414201c000d030005 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 554827508 1250 554826258 554826287
    0x1080709030308011a0c06090606030d0f0806091302030a0305190801080604230604060c0e010305150f0111150114010908060403120204030503210a060506040b0c0f03130e07 76
    0x99001000b5503c01505e14258036244500c2d542d040c0821740e0f518a084c01b000760340700b012a900c54070a002507494140a070030700d0241e01c0d0511240b03001d0b00d914080c00c8008010006841101580c0000d448a02490045001da0b0740c0202600c101c0112890080c1c025000035030611102588092413039001030050405606844041c0024500c66445a65401c2411003c01d07002c0d6100c44948a4035084041c10413019015038492400070903240c03880b000050412041112090405050000b4004001c928149100441c18103440446040803941c0040ea00d12145000c1c0700700310710071040181580c0c80c101c10f4440c11b07980d00804404403107080030300440350002140903508494000d81c01150002c0e00a0010701844042e00a02505240d0b8070703110036080d0b070444101d4804030f2655910301070102c9510b070441380e440a1103c10800940d41000c01050b1540518000d0070458800005e40481501040003120a201e8000044a0b6110380070383c81a298651507204518400d074640001c5414075000c4c19403180d2000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 554828758 1250 554827508 554827517
    0x12020c07090e2b05071a06010f0e010f1103090a14040c031e020322060903090e1b090301020d0513110105281701090c080114010503010521010f0b010807090303 70
    0x1c1007808111100d81c040000242030000801011000441c0500542e5039440d802400e0b100070311f0110000751250315517035100d00801201c4155004260303000710410340700e03140328a0f0200111002d03181c107034514030500d00540d6000040320300000360640c603a00b0300040c1c860140c4040c4540245e14909409403550306c0d411181000600c1c1041d100e5000c294090744c0c0c000c086924003c0d1140c21807049255803450302600f40d8029848004180501d40c00402c000000c0102110809151030051110581c840d01a403c00d60300820015012f043c9903001d4050380e0924480c01c3e8204001c4c1840028600c02d240010320031034406610340e105400c2c960203a400d4030f0048030490090040101e58082d0101c811548045200501c107041901d40c10100d000b0140031b010301003d1800042040c2409406406e19805070301c090002e104600c43c4201c940d03440307005e5a0440340309903511302c80c0c40b8860f10181030244402d0b09030480b41d0318200f00e501d51611590040c40b8107400a0700e880c0303160341310950b003180c00014074000a00400d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 554830008 1250 554828758 554828803
    0xa0b1309080406080405100515030606190b0a030b03100c0f030203130609060e010c110f2a130e07090614030c010e0d0624050a0303080a050712020c07090e 68
    0x264004d020701e83d8880c0c03040054035140c07101c2c00401c0080b1071040d46c1c04030041c036600100035a941010044250403080071141c065100c2c0d501c031481034090340c03d4056050f052401040c980e40c124003d4000090081000301901c41c2d600d81443d2a1004052080c04800007a03158000440b00e507000384202e9001b960001c42c2d019107000d503529840c1c040e0260810440710309a84401410070b4913000e109200400040d6135507454401c020008103482c0160900c2080750982007529403000896180c0341182550500181030000954620001900d60504280580900703090035185280031102094600c10340c5d2540404004264031000100081e42194581a41581c05401d804103290b00640d032480f104440100070360120b00c40c0d5600c10098500c10609012141f41004502c41e00340700600a01000c0c000594900d0760f09403035910000c14906001d801c0300403040d510740c0801c4140380710b1451305461700c9076044103654450007000010f90740d40b400c0c8140c1034400e2038042d25400c8540b0204070341804040840802c16803 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 554831258 1250 554830008 554830019
    0xe06160f1409011e110c0301180f020a031b06030c05030403170a0b1503010f0801020c032d03011503060603060f03110604080d0c0627030e01030f02030a0b13090804 72
    0x6a1101100034103004c00342c10400f00d030300110405020000003030354031001c02001040229107440f46000c80c03188280d05110f8a290280c10b0114010710b29500f040a80d47ca401c0140003082c4800c036035801c044e2000f00001d07442e800b0b4030915442c4004880d2640d0342080150190002150b4600056500800094000501d50f52103600312204503040740c0b0602000958400b00c0300064461a4107002c4141012401b0004000f10f0412401e0700c002000500f000398a449487c1741e81d0741d02e0341b08004501c8095035940d030740005201c030f0201206905040801504da503d58480040c0c0d82100350259020000908100c0e000c18018070a0043c0307400c84007003070b20160b0400d04540d1904000818540900d402c0b0710107000000e02038004000d600490b80c10b540300e118218003541000300a60742c1c09a85c01490311f9082c1406c20401408424070144141c040c40c064150302c0258004802402c0145ca80501090000c0188050040503600a00504030125103802d0240004000401a40c0c00490f01500070b15052008028 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 554832508 1250 554831258 554831297
    0xf0c030619090c0b04090903120212040b07170c030609061909020d18080301032609010e18161b050709110d0203040b040b010b07051f020d0e06160f 65
    0xb003c0c412034603c0c2010303480742d902c00426006a8840300c2c0041d101d034140c5c82411b0700050001c4404030300810030351402191002d56180381d2001f07040107011094840006004e130340b089404852031107904106005034106844690b0040c0c000b03941c401d00c103100d0000461171926050701d14207140014807085003500c0d46405030b81c40007134002c400314081580d210610714182e03110010104407018400c40c562501e03541582800a030442c44840c415100b1050002504158420b0000b520491172091030800b42a84088002c82c801601c00f4251b0006a18107a0a00c00398960b005800300140d1087e40d507000c1060419030002001451041000e40030350070004090000c402280c1003030072450035101c200d9240501d041da40c10101d84c001c8609440c3c10000106020800000081560040c60590200d50074800c07161241926600030002540319418000c030078243c2220680c0555072081186942004039654901d91b03143c68000803941d200042c80800c00183e0514010405a060703c2541c1c3d8480051003010000c903903 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 554833758 1250 554832508 554832521
    0x12130f03180b031303031d0a110406051f0f0e180c0c0604060e100c0509010f120c050405100f021f06350f0a11040902040204080f0c030619 61
    0x80d00c070001e10341c0c04501880c0a800450048a80340e0110740c014495040c024101c07425071200070085504607440710818600010b51015158121960440d103506010001e0002c04d15540305c00d4200c1c801c405101e820b030711030083c40c84e0346000c1c941764500110345131070301181c5000144a0181d40003038202842400501184031866000b0404a01c06203001e095035a0640340c80070868044480d142c4800c2940f4500b6028040c46070304d42d41081c1c007030051309240b44020b0301c00e004481c081030400010400c400005846100b00c40c44004007150108804a400d4000903e5948507010340e41c00341401d28084946248914134008903c206a80580590404c04048218503a1002c00c0c091a8584540300400d150f02c0303803420048006034010a490101c1e24002a0140c40410344011900036001841d480304d020001091210803030b540140c102c11040e03101c41c00907004082e05c482c0070390454030114010591000000300d196200d1101d108603410420708608065a03544101c031908072a91048502440b003089580110 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 554835008 1250 554833758 554833787
    0x2909030106080a080c01060b03070903110310060b07111e0d0809061204120c0b1306090803070536060306030a0f320d110a061112130f03 60
    0xc215039650364000c5282411654050b20070132400036a09503035003401d1280c1c20080600c40c0b00c05040d80340403940500703c8a1244000351034001050303105951a54240890740b00c1c003200d00d034208042a100c89403007103e0780043c4002c440000c2d0115111640b4640b0303000e150170088120485031710b506880c030203000d000b00d5070311000c80f40c0d51030902401c134250396100c000d001002150030265071249468180f14802c1043d4500c3d0301c1c188030000d900b10010800049000b544950603a908444a030340300c2c60f2410041c0354a03500501450404000c1c45221540b200c018150b880c04800081c10943c599008010003003c501008108080d0b000d2800040d410190043d642c040802010344901410a40f00c1000080c4804000c90343c3c0454141e82c01085607011031b5110000c58602c00300000e01104030b801e16600e030010700440342405401ea400f101d01282c10007076400420340c044130902a60034202070300c181c1078102868501e180d43c90344000404403a0301c80009245a0b0f041078010440c8501c5032000e550141d0100d048 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 554836258 1250 554835008 554835011
    0x2030706230403060c1412150316080d2607180e0403080103060f020c070b070206040f090522020603070806030106080a030806100f0504030311150c070203060129090301 74
    0x603504040c1d04400503200440c011440800e0743d0300060760041900081100f42c0800b610140f000d1556036103c001c40d40d5000070410050b10417007101d07070002807501401c0c0c410b01848004000300030900a40200d00d40c0074100c0c0c2c688480302c10b80003a0040c150400c41894030f2178200c0b03100400041e031092103202040e0300c0229080c1801030454694805410f5180212000d5000c80c601900400400840703105038040c40001000445c00c0041c2c0001007030300c4020f144212413200502060040035581e41c0350447e801440011110250aa601c40e1030350060682103a00c4d6508a41c00e100802031191094060340d50954002c04003480c0d0380c1d52a00544044401030b0080d6059942d5083c04207000d039040048a255901070b17110b01d84185481410030036220f01074a080410000b0031078044980e583c200040c0d500703030b80d4103090040030340b1481514140f4020031100d2039103004402c8014860401a54001001c00c0c0d4000e0342680d405070388031030360b50421903840c04e5101101559121000062100c10000c3d08001030300600 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 554837508 1250 554836258 554836307
    0xb0603010b3c070b06010806030307060506060d0c020a140616081305010507051c110307140c0d0806040515031b0303070f03030501230d02060304141213060c02030706 73
    0x440724044070700480c960102c480000f03010b01802922103040b80d00c1602480c11030081d26062010030f86a0146260041c0140d40724030100c3c6050769050203880c03000a000404016030758850100035590107c0103019074030f11854042800b4004004a101d82c851482500c081d01e46901c614412101210001d22080c44685284c44000001d4802e0003498090f018607554251601c49100e5901c0114100c8440c05400381e203443c118591030410741c01a41d43c07054050030003060043e10219403070660720811110401c14000c44100709801500485118041c80e0250303010800355444568406001780c118103401e5042d07100b00202d200344002030403c104060000f400752420810f00c2d45e10400401c5038513400700c0200b0344403001400003201550804290582c0b041e000050900d140c400f040018110000207401000000300083c117106210140c41e011700e203a0001c982001801706075001040d003040e41c0340c05180918000018100c0e1240e00f0200e41250010080d044d4180b5110040e18040503a08045a81102c6440c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 554838758 1250 554837508 554837587
    0x1d0d08090a0906050a051804080f070503030406060e09010b030a0b09070f08010902010f02061905060d0f1209080706091509080706020f0106051e040b010509220b0603010b 75
    0x1001d0001c06000300040780080c104410803154007982c0d080710b4004d6068003001007008407070940741c0e9081030b00840482c2d61060451046141485620b40240c0366200010500040000d41d074040f0044801130401032000c2d459a83e240b0382a80e6050642591581c40494102c021581d0b405030a60413282c1c460840b0301190b542c501a810446060b800310b00240d41d185040300a5503041100b030390b0314515a101810142c588581c003a01140c003500203141e0140d03a80c40c009070342c3c1d8030b9070352480c09026001082d862200030700d40392241c601101c04841400160302e01b000044c04140005012081d14455203a1011181c2400d410715504504520240100641c4210000d2000340500ca4100982690f038058000803518074407407820f407401648481d01030118007901500c1814107032042040d11008440214640b005480100e45034060a21101d60001007400014140310150380141c004091001081c0a05010541081030170b000900c00d000070040c040007140c10b00240c15600441d03030880c0b4032b1441c034001d0705078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 554840008 1250 554838758 554838769
    0x30a270906080606030a030f0c03050715050a0e0d17150406030807060c140f07050f0d030915090f02060c150103061d0a02010210020c01061211101d0d0809 68
    0x9900c0006001e9842009100b00ca000b0f00c0542e5200006400909070140e50780e4000340b400540352850303020400c0c040c4030501054490f508503030340340d42c00c000002c1800d0700c41c240b001c004240c1505d040792124984a547c081198010070448130003000c5444845415540078004128188000c10b0f44103652514648400150340b24890000514068a00191911040e1404000b160005010901807003900507403960004140c000710782660401c00e58180d00c40b8528508145030046000c462841c0e40141440e01400350b5260b48241c5d066401080d800e070201c102e0720900c1040354103090002c0c1548840b11800005824454002d190760b031481c208503606501802024410483c0c00c3e001120081d4403040203030002c0c51005517052461000c1400b801c91011281c3c0040c1d81c41f110407140c0d603101600401c2080c480c4101b9840b01c0005e000e6040450000b80003441d0112001500060140c0700301900100380c00014454540151860400f102040001070106e0070005100d0807884200c0754201c08211380b40342900e60 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 554841258 1250 554840008 554840087
    0x60d020f04020711011206081e211309021306030b130c02030904050708060d021302130b04050a1e140406080a150507020d0c0803130203150403090e09030a 68
    0x10502400130802c0c450004160114420b40c4080d60790a1150500c120080840c0600451000ba1004010040d81c001c4540c10007803c0640403000081c201b40385905c9071b0841000f0009000d2180071207100d292124041c80c120b00995126079221542c085040c0f260354000e40c448564124010407950242019a0308030080d900c4100e0f0a40042e000440c100c480303803e05010b002d81040361810505450700e00080450045400d290018bc03059000300039000c08944654112102d1800c1c0e12054506c04d9100da44000f4940d01903c03c060003407001440025406185207031035981c1c0000e054101641c58a4110012200c0700c0038018194460343e44c40e00020400d00030804801c000d0f10071300c0359952103800210003c08848008010a065421000400c501c2076441540305caa13150f0f200e880280c0b6511000d181004090090324001c0d014400d0b030501e1440d000e00190264441d40c0b00707548403452151540d4444c0600740085c2c458040c6a801440a040c00300d002d0303090310700f6103955900c0c0d80070520104084018000c80 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 554842508 1250 554841258 554841263
    0x201111306090e061f270302030601090b061608090d0b0f09030414091302030d020609011b0903060c0e0402030a09030e0f010e0108090708060f09010e07060503060d020f040207 77
    0x1112000c00c50103400ca02d9410080400540140c00ba140100118044104108918583c802d9640305018060b000b0705100080392015080002c006180c001c4400c0b520842e400140e10901c181800015080c0f2980035038954940042e00850812060203650411000c07800c80c00c568100050081d400345444030342200c003240b805040c600341b5a0a2010500314004400b03410801180c00410040c0000110003a10031801242030320030015035520148610150b44080000941c9400760340e00040d0201c1d40024664007a2060034020007400246501d040c29008400c09803102142c0c40000800c0440c01d1540003010054440c01c14a1064080500040807a40102e490040540e502c0d1040814550b0100070751030300241c02c0e00c02862f0501d1803400a402010f0305c10300c49040155500015501540600c9500001c102c40d000712019401e00c01d06c050b50307411003196510041c0d840c2c001c03a1501030b44001450021211103440361072854030740c5c0e400c2c003141141c442810398100c405800038507025200d620040103a01e0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 554843758 1250 554842508 554842537
    0x70c0b0f0414070f1206060f120b160e06030a0209030607050c3007020a08100207030806010c0c0b22080102070201031503081206041b030b0a050303120a0c020111 71
    0x3400b80303000390700b038202a0341030400c0e9031001105010301c00700040c200d01a2211883c40914103089171070b18101503c0d064000042d004105040040c01503201c09450529034807411103009643c0d110702031000501407400d440300c0094041c036011481340c1804401190400254003005d07142c40102c001091822100351080345c00540d0006091140c900180303e500c506400d03084009085a45810112642d04260a400c6101c944006242000c569804c01d40d400140030700d0b41a81c1004400811810003500700c2c007000e40100d640100050f00961064120082c06513021140980341c40c140840a210b0340c0001e840131149a5074000c0f180765000e0300b550507000424500f400940e840380c0c113100060981b021882c00501910300b4240c14000035a507102641c8000c3c0038116110391a56074030b000a4040d040e0326044644060320810805000d95054021000000c002e0310b80403140341e40d07081496624803620200400c20101c442c081241030b02580c12000c200c501910012a13003440007501503c03c5e51042c052001e800 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 554845008 1250 554843758 554843761
    0x4030e0418061a031e01061a041503090b0a0902040e0f071505040f03060902010201061a0d050106051309050c0702210f2a041407090501110604050d08070c0b0f 70
    0x2806000e10300c8042c064108440148060f0740220b036481d5040081c1d0740115003440d101006a00003544480010a2802071842c9260b00503a01c03022594818043e4454000103001543c001c80e009010301c120065000c05001c0c5955152400c2d400141541001240d00a0311501103010034501081a4009508207a028143d00341c50020100016142d8440c0542801424403080041110180243c000c582d040807000c00c500c007141c40100d00620306504410f014400007903443d41c02209602c0500b4580c005070b5020486a603d805c03096615010b000c132800b1405800e03081c14050340c482c40e080186c10814801400d0b00f0141c003030b400240324241000740042480380003103186990710000c11424007030b4611030000d042200a01e645040366180c90300d01181120859509026403074960b94002100c207482c0c046100d4041c04c2000c40144047c1891082d540064000622030020b0317100410494003980e4088018100000d0500081d0707050b41c40141404203200c014003440c0b000c903034a010a40e224000c0c2d080d481000307 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 554846258 1250 554845008 554845013
    0x17030618063006100b1902031603090e0f0f010b0702010302040b030921070c140f1002060603240601081305030a17131a0a0b030a050c0f151204030e0418 67
    0x61420013004602c45071000c0308200100c1c10640f08541910118054042110700708a10903441c62294034036044003aa8500184410726a0000c1c51006640ca1996416400e0702c5140e20f81000c20402d40300e0740041e01c111001004840110030080005c1ca20604000d0f05160b41c440c0710107d683c204803000015600b045107100398840b101c900c010b0390300d0030740820355051004946a010508009004481d2041d04e017100101d503a0740c99081003400c0f00801840c404080300d40c524001d4445905881090080c492564000704210541240844801c41c9000308140c0740e96440045881c1d44016004e0403c480e58004410b0101c0c0e0248010202c2c0b46164984008091407008920300541d001880100c820b05000303042c0f00000c01540d2001d2560342640324101c15070701e840c4c0303480d00213260001d0566418412104600108940801e0070301d880541141e18401500000b41805010644c601c440580a0810440c1c0032180c440e0020b4030780c0080c000e2600c01301c1012290b02140c1110301c211407241d40c0c81c096094603002c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 554847508 1250 554846258 554846263
    0x2030a1a0106140d09020a080d030c0f1b060203040221070303080c0901020c040518160806090a020a03060c0e0409080909060418020913050d0804170306180630 70
    0x10300e00c5250220401e640d40f6a00c490030701035860341c10350042d10f840010040d0350300c11400e18080e140405c00c0d900d840c0d010301c1019006140c0d40e920500400e01f100b0000c03034524052012000c810740c09640c18054583c01c3d41d1920000e500c001c0c400c0340e00140050100f4000c607215150030320701840c070300010100c640c15420080c058000040044008000030080a54a40da01013000030004070142e50118003516024464550355070030f40c1c801c0800d07100f200c03071200c1b541d454007007100115100c0e02d06a03841615050300658079aa845400603410110700001040003130566440704a81011500d4442500503580300000d080d1145110203507154540410301c28000d20b000803007640c100301c0480342001f104900720204c52604040007400703480380581000040e50404c1c80c03482c1d21103140d401000d5400c3c81c04d05900103407814030309881c00c1e250075401f902c0f5100d00c1141d48049902403280105903801d040206151040400d400038000c3d504000400b40b02200800c400b0080d040c038075843c284409610203c0c1c20a0352 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 554848758 1250 554847508 554847511
    0xd020f07050f061204061d0304140a32040911180907171c02060103030207120803460e03160b0c070b040302031e090306010b0d0902030a1a 61
    0xd00c00d8501050840a43da0307004100c500c2d1601c05402d541c020343d15410b00b9001450760086407070255481c00e0622490000220003803094036010000d10114060100c1402064a405e000d07940c58440a11441c0784040340c4c101140c45072403420000030b80d14100042c00300e0150790318001c08032040c40c10742c80a10024a007489800c00c0714025000b200b1200d14101c100181e9859440c819a802d030807160324130420008092150390310502e83e02c035074900c070054011802552203409101c25070040c012480045682d28402d1561078260b504040b465003107031111044001c1500d03100e181070380421014986003420f040b6010b5500c0c14901c00310503141503560001e1181c0c0903290041c05041c1d484d0010401c01720000307000c45105a01c1381e0802010103981d1344140174101c41303104da1036000d0141c920340c000308800c0550010040034142c0b40402c00c142151800b0040a05034051100410340c103402200050081c406450090002c618a2107000f140d50043c58000c2810150b1004040d6800344118403c100e100c2286035619 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 554850008 1250 554848758 554848769
    0x6280201020d0c1d011101090812010807081207061107060e07180b13090f150e0d080402010c0f06020409110c0708060c0a0c020a1a09030705040b03030409020f0c0d020f07 75
    0x1010008200000300413808131a01900c0e0510901400d4048500c00075800405965400b00302e240c0d4501003044140030090007441500e84a1180c80d4011034002e102107410038158a05080c01820308010360340c2d03100a070009817410883d200c0240b01c0d00c0c0c00314200c1d000d402040e52070034000c0e2190500344040c0820200d62030103840038240c00c10030424225160b0203101060a1403c040c002a080304a15080300528403a13040580401001d100380b6201241c03d40c0142c1d4402c15032400c0700c0d14514401d0050700c0d0300d601101c019020403014100c01e4040350908081c0c0e00e04500c04d44005180545074141071040f1400034000300103007207004c034244048800400c00103010744100780080510b460555a465558400c900503001000424240c441c00c40d10f4082d088000b46c9042d034002c07050195000c41c00c0318181c000d20006403003881a0880000d260402d032107200310016018020f94503203401c00c040b60000e0b6020300da170031090100c204076007020240300340410f0b801e005059014240c0170030032008503442d20704103410a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 554851258 1250 554850008 554850017
    0x91315080c010f0305090705030706080708060103090209150409050105070e0a09020723030d06300c0b1b06011d091c0e030a051213170c06280201020d0c 67
    0x344150ba8008921800d1504075250103d11681d80040413810714409074046609440341d241d010402c40c2d00900d02c240300781c00d070769070781e0b23aa0765100d40044080e14060f0102a40012031140030030060001d4111441e02c0020280001c90f647c061681c5450031190210303801c40c000f500c1035001601500c1c2c08401c5000a1413645000d5007041314503140d141c10703d580c6040d0903000c00d10030075144002940610a540c0c00584444080203d0395465071242d641116101c1d0b1220080c280007500500d0b842e4498404e01020f810541e075400150074034480c20341c5130380000d003029101c03602e02d00b156045060400089029040d11113405601c00c0c0070306114105060040e0001500341c00460508401907050307045c80d02907144a1814080c0080d028001c64280f14070200003034840d000d452060b0710f81070b005d0300040c86075042d04030202d48243c1e5120402e46400c205081500c48a4011a0550216240c8100601401401d03d405136144428445480c821300700394841c50b00c0541d4003c03450203462041407141d80d01e5aa0300341807 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 554852508 1250 554851258 554851273
    0xb0d2901030c020c03063702030601031b080f13060204080a050c0306070225240e0612040f02060f190801090e0c04050712110c06010603111207020309131508 69
    0x60340307405004003202c0d81007c42c8555400170702d800300f8880300148215074900c400012041c0c03c03880a94422a1410301107420705030040c01c641c1c40d41030240c5100319141c0c0d80c441180c652104480a110000d0b20403404401c00a00326004500783d031006000800301c41c401001d140b00c0f03d2510700e05140140814a11079040071041103000b680200310324009040054030b4a8003246040001540818641c2000490701e0b401d448614290b41024440c03132100010307454800c034601510007009028480c1e10000071004050b000440c001070b140003849102c0d00d00c0141140d041c41c05040c1c0c0c194290300401170032240f0301d0380500308100442e00083d096016104c242002e2150b0710050724000c4c1d4400d444400503001350ba451002480d801c0c440c05d28007040800981040c842080b614a042c0d010740c00032503031950759004000c0002000382c064415084240307103859000e802d04d580c2964200010303d0041010b03065000400ca003000d240e6070103501c0070301c501b0200b500154070381b02e50031501944603042e0440b4403250700401 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 554853758 1250 554852508 554852533
    0x90207120f021009030206040b0f190509030f1c0e122203050d0e0a080c010806011b02150d05070f051804140702030c0f07030c0b0d2901030c02 63
    0x140c6040d190981414218441600300c0700491070840b040356030b404880d14000e0820201580468440c1c06540503540504694450584058803800180e84c0140704040248401e615841ca5400070b030743c0b10a8400a44e814a1040000d419465100451a00c291074100e2036580c15140c80b480380754031400c80a001080032940f2141005454480c141103001841c0132119036080503220030f80400041e5920106031200c403c5d4000740503010f512203102c0c10b03104585c03010001c150040005021070000d02d05949140d49602c4050040d160340c3c24008180300044104a0418003603290354200d0201071b080310a0003035031000b6010000e011510080d00d0710b0100700c00710255181d83c0d0352103010340b580c005108031131002e16541c0da400100140310700c1d501d10f00481030290800c6499038020003c2d01a40018400f03072a02c05400b031180a40381e141d980002024500e4048051142c007030080050170405243d00380000300c02482e403540c1c0740e42c0900780c1800c2404a440b03010180c06540d05028810f0007100c517000500009100d41c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 554855008 1250 554853758 554853773
    0x30509120c090f131704081203242d010912020901061119060b091f0b21090c0f01091a0a02011803030b03060105270604020c071806090207 61
    0x107006101030f080c283c00401c100d40703807a00b19036981c150701c0941d040c90340b640350031460503a41151144000500644039025004403004007140e20580e402c82e403074107040501001c203100104444580139005050254010f041050369526903060704512540740c1c444900040005201420365040907000d68494a01000140c460141941c1900c11a00300702205c1104060050718101e4060a02030b620300d1540255024041213030310240030a01d054502c880e65545500c01800031060804868269000c000d0042000348140809441d542400c403550340090356100500d00c0d00c601c0140c2e503030811600208540e4002d450542d0303a041000740c0a092100c0e0840c502101c0454a050340032644000d2100003c40b8504c0e2031003035001050b9858410394a00701044030307040c01001807901c01c151034064800c01d80007065a103002500c000b254030302d85054890702c2c0c103580400c0e18040e5002d407100b0380041d024404050303001800c0c4800c1c00a040c4644102c03d04020f0b031240746c0306a5209901020361a8810400741d800704605 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 554856115 1107 554855008 554855011
    0x7060b090609070507080a05040905040b0604060e0709060507080c01060f080f03090913020301150803070b01050f1c050313180e0c06030a0b060d09030509120c09 71
    0xd114144441034406843d600081401800071000191043c0300610366644580b4040d400c2c150303202d0700181612015038040b100500d010040000a08041c45072100600c4043d620000b24204400042c0001499020b11002c01c0030014072202400203950898000b503038660020803c80b943c50301600030715030703480c010074820f80039141901c0c0f01c01ca0004103484070960b00030709080e00390705e40f0350915a462040c1d40c81203802d9501c4110030302441c100700c42c040006240b0200650b590b4071351071511161030b8005070009840360140503c05001e50710340e44c04042503da00103088040000c41d508000f8032310701540a40c5401ca210001c0003040c00800d0359105a20320158590500c03031200c040001ca51541d2800007001d4000b001800091005500768204160341503000c5c00c054a0004032518000070748003a1402680032400010f44d4184c1400c00740443c1c0c06041c1d17040060025240f0810004841c1c520 = true := by decide +kernel

theorem cover : BRFrame.Cov 554676258 554856115 := by
  have h0 := BRFrame.cov_init 554676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 554676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 554676258 ≤ n) (h2 : n < 554856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
