-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2158
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:49:37.373673+00:00
-- url     : https://prove2.me/submissions/8e98d761-6182-4140-9e5a-e51923d81ad3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 387949640 ≤ n < 388129496 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 387950890 1250 387949640 387949651
    0x71403070c05091003050c0d0201020a0501050c0403030212120406110913020a1d0d17041707090c2111070b040515010b0a02100b0604030f0c030b010f05031507020312 73
    0x8001c4003900308020400054409000b80e08016441d400800000f9004142030080c05011240e0f1800b840c002c1c00140d040550103030004005520300810801031142060242041e6070081d400c40d00304400f003480b07401040c800d08400e00141e502c0900001c0002da042e411502d00c000d00038805030309003640200400c140409001c0700001854000c00c000034680e031f03c40c0403082880d01c040d40082080c1c54034004204105500c0501034101130458240649044400080b2402000d520700f0048034a0b00d22200b55031109406d0003551001402c0141c440d185921420f400d01c94040c140e9482d103202485402030000a01c032850b5000b142c0318040c00841c0201c2c0b4074000341d43c4a140101c0141c107507000054550782c58081d050f00320b47d03000c40d81030010f400780d01c0c1c0c0000c80d0340d802e0310707180c000289110b465000614035001d90342c0002d02c0031802d60161030402045450402c11a8801c802644080c1d8a5a0441702032013460302849806034008031425119440b46000c190308420b160041d6071600501d8200d2882c1c4241c02c80301c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 387952140 1250 387950890 387950903
    0x31d120a050705121204050402030709120f05210901110709060303081b0301150507060605150703090509090309060d090b1f050f18041401050108101803020303060607140307 76
    0xc0115090803214414a90040006404005591706986105010300d0181c10b005a5002c000500c08600440068014001901c8000f11144d85131a04407641000031008513014003d03041c100300419400c01c0d01c07406000846500c5801e0290a400444080315420142680352049002c005110080d038030401b4007660083d55a074140e8900003110840c1940c1c8040c01808601c0204010407843e11003254100c143c40c0c1501d40607590f1401820700b4400707400d06801c150b6005208003860a00342d0f00c400e0003031002a01c41e85422565507551000c0201440080354001e2072a0400c00900106207060001002d01200c11b540000300e2400c0c51300d07440074046040701c01880e4580018419004001007190400040104a0380b941c400600240418218145c58014120803e0020003240030005200c01c038030000303900a4000c102669441610035542c03031400680c50b007800d1030041c20411000301c00140403002c1c2d070140c0045143d034032500300723005496002c01c009444001c0e60154401c3c12540903c0200005030081c00e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 387953390 1250 387952140 387952153
    0x1506060309110607030c0b150604060e03061005031914061005130203041518050d03020a0e06040e161809062606040326010f080f0a031d120a05 63
    0x10300700d1a0819841d455603c00d890034031000d400039600160f0304190503030245449006032690001c10030681d0b146441107501040128020503403035804202d044920385c5c1101203c1103600e40c076041c20311204050044a8254008400620400401d00c400c819414030071502801c106075601c442a06000050311400c0000d2080041003000746003a581604003030187c04011071460625658841e03516001c00c43c40c243d180c2c0c544284140d40e000b04148034070102d42140a5030240c4620a5000b0002d62045110002050714100344600034207103041541c00746d0f140f41c20342e8030300c5403038400030100d101d42011019010441128035541582443c4040e060050603c05404900c0030300f030038117a018038411014007a04a0300c4450a0304080a00016003e070056050b040040d801b00001c4494040c4030340b07646910300c007408400000288440500904400c6808a40a807186c080340807109945450000002030300042d800b03000c5002003c14a0302607125068000e1558800c01e51108000c1c1c144180390030181c81680191 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 387954640 1250 387953390 387953393
    0xd08040906081906230f041b03031d15040b0304150e0316020105090402160210020f030a0f2f010507022415091815060f0d1506060309 59
    0x5001d86806060700501608850340380d5250500103094000c00600a0368441d144c0e061180710348034010040781100c00c450707802071a00b182038005000741a1401ca03400b6854034030f1010f0078241e60850f0820349505030354180da0404c2c80751800000709402410140d01604101e0b0620007108044000e02c01000c003d0310060f16898203062501c004600001c016020702c2c28903e560311181d001108032041c0000100ea00013929249000480c0c1c2c50040e020701c150018070006c2c084405090b41110740754010305c200e03090315030811020801c0b85c5480801c6401c8450340e2040c800e410b002401406444140d103503924100c0110f02c0c140c0c481c0000b1038800030782031641000144041c000204207001b03003a44074146000902054041c0c00300d11b1a28181050115101040c000c0400d6140308011030440311480000c2010065042507008001c0c3c3d40d900010038001e900c62030303041c1d0744134141038120f943c031454005140214000002e014404120210034040f901c04203520303422000c01c0c202e445000c024080c265030014100c04035 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 387955890 1250 387954640 387954659
    0x90e0c0f0a110c0d110910080102130320061e090303070606090b010e032a210607090b0a0c1b061e08040c09201c18020f01110a020d0804 60
    0x60280c3c1c5009190744c405080228804034442c85041000b500e80e524290b840721071180b00b8100c2a0401c1d96194000200f00079000003440400c0e06030784c01101114003000c10403e445048066403452150401e80602402e500d9880140780030100c0152100ca6920300b41c070400c0081d08640c40444c5c22034250780d4401c1d040c0301448551040d4400d404003800c0c00b460041c050400242e9820740d80203041a0451419403802c80b00038241400c85140030702070010195200e00429000c141900414040c00a2143c0740000c0c8141d840341842d002102c11000702d041c940404400b0403191404010301c01d403420301ea00040140082c1c900340c02c103001011150344905405c28032a04580c10020000c1005e02084104414403010580d60781d01c003001c071100b05000080ba21030700340305a030310301141400402d8007400114a60a05603202c22810402114010f41044a0080d18069101c1120309040103900142c1104031512554024168034141c6545131080740d00518587e40010071801507640c0444035201c000c43d08000d11501c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 387957140 1250 387955890 387955903
    0xf0c06120501050423092b0e220906110304050d020609150a18080c0102030105090604111602040204090c02030403050105161725020c120d090e0c0f0a11 67
    0x34115130602000001003c03075440d001d6020520603d07109190302040c20602c041140c5611138030300f000d402140d100c103c50390005141c030901d01440828007900d4510014501050301d5000305001401900034868401241401400d400500300d03041d0b940c5100031000101d400019600c210b100300020000300801c0c880c0241040c80241013001a80d00c03504c0745070001014410f2540e0b10a0175828000b80c80040c00c86521103290980e00003074040c46001480c41c44148040d002541039900548120015407100c1c03092204840c4d10901041026030700b0310107100701c4003900030052941400140003504180c0c640c02041c0403651195523110141e400040e04100308030081c01401c4d0f0080714040c1074404003c0001c0060620b5a1014000207100303d180c00003001d1207035104005010400101d07404401404800b0080d42e54858103034030510a8552840010316100002110800201c1c00d907520303803115203441060b01c91080e024000550603a014890031114090000c0a841030b0925551182080e40095140ba418501d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 387958390 1250 387957140 387957149
    0x10b09040e010605150f1b030c0c0906011707030608190201080a02040b0306010f17180f0115050409031101090b0708011d041e0209072708190f0c06120501 68
    0x906003c810031082d0b40720710414001035044001542d88884401c0890780603c1519002483c01d0309140700102e1002e000006005401e042c001180d404142490400c07400d04000c407900e078001100661250300404964031403580040140c01d0104c0c10548901403a0f0411000344004d82c4189200381a890a40da030004c215604101280b0b400c42c0340c6414081d2070201444020034050500c0400041c0d020018403841d6544100044004080700c107092a05600f1a03142c40c00664081c1c80c4940a404500040103100f001c0419003660640311517140b4000502026040041065092000303c4040e00d8607074030700707000b049150341c801c0d015001c4510340b03000c0107000f020341030b0041c1c02320000d0328081d2040c9078a11048103401940018010b2202c0300b0100311100764259041c00250482c0720601803194040d0000544d500c1c041075403d0001000c8180503941e22035031084d11581840b50301411a2000e8008010b0180000c06e0140a4402505406449148400000758841e1002901c05240410075200c6841402d002d031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 387959640 1250 387958390 387958393
    0xe120f010e1213030305090d08030907090e03120a1503061a010228030507080c03070c05031015030803060d17030702070f140906190306090209220602130905010b09040e 74
    0x300c41800d14070380f00b0b0030380402070600c0400100c4071001c1e541c4146125101c0d50241001c0c0c0d0b02c0c90f190310001e4507001c8511441d440300e07081064141c00314070080255901403454880a00c5036943d00c0c1c40020161020710240e6122001c0c2000200210382c0781d000302c401011781e0703500700c1c0440540c500009140022100c02e030854002d28000c0c0106a041c1d11149050190700352905a455000c142400311180c8a8011040110704c00000c0300000c003c1c07119030b59411103a084099070501d0190482010940b40d000000311040d9a1603031003030000516100183da082a80238003880301082860342c41c4880342c0c0825441103619080481082142c1c0c0c1c0c104a24001362010340c0b800e00003185042603800c82044400a2203100300d100c80000350003500c4a01700e10380341c1d41c40e020301d10300304507564100b00d0002c006848060f4058101c040000704049086084c04d4000851114030300c01407102c5441e50802900007556224101c00000d0f00042d88942a01950307011f000c3c0c2001c03480d0342e01c0413441000b00310707204e070306034040309 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 387960890 1250 387959640 387959647
    0xf130207020a0602030c0d030f021c14150d031b020a0608040b16050a0309030212040b0406110a0506010e09011401030804092405060c0309030a11032a010e120f010e12 73
    0x31b005c10200074412450501241000074140c501d03019004070140500d600c101e50301c0c000d441c0c0e9083c3c1c00460b05800c5640d45603a291300c441d250901451046c0c1159a089403688040c030b00003038030440704d60340442015180714080140c40c2d0700141000f101c44d84450005007400c4240310a1142c0d8003c01a000b640200350740320002061a000b03031142c020345403100e060543e80c403852001c0c18001e11940074200440d8441550321900c03140b03540f503750040d004a400003140d035140e01121480001702052074a1300500188126884c000b52454101d5005040c4040c554840c00d075076840807580d80c03255000e10f1140000341c0d125401c1c50b0340c00d406c6800c0e030900c0305600c80d0000c11400d18000002c4c0d0a400f6150103407141c0340d6403a00104681d02d9803140c0e03003455806100d17040c1104244400d10365100b548581c1201a22861b20749800c00144102e60b00c107654102079192003802c1d00a40c02840c1d072000032000a00170900b800c05029907242018079805441d0110394448000345414501840440004100e00404606 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 387962140 1250 387960890 387960907
    0x126011e0b0c0c0f1c030f0927020a09030b090a03080a140601270b0a03290103090f02060a0809100c021518120c1221060f130207020a060203 62
    0x203072400030708501c03802406100c0d01009942c1720543d42d15804292220b8000c0f04c140c207460000e2607980141d03850000100d60300400704680311442c0080d503192491141d22541110340b2072924009501c40070180091112601c1e00000180c48500624800c000400c0584a001101d00740034001c000002c046082040c03a00c1a00040500440310b40ea800090a1a01e40c10120403014071180720002030403100da140c0315166000401e82172040080c01c030308500795028013166901d06840d000400ca1512191054100d0301844401d5510a51003a0303100c501070f2030617403503440058001c103a0690001c03c0da2000180180c08000311140100980a981907100b00c0401250240250082d1241c10030750018410180c1791000c103180949481002008102010644100420304014004141d00440381c030002c03402440111582040c1d000240c0d081d418001200510028515034444240d1400400389544180c441c4008011074940c1040c00c2c0b5028036202005035100b03818010040c06030143e41c000001c5500c100901e21 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 387963390 1250 387962140 387962143
    0x9030c030f060605120d0e0f0d0c080d051c050402030a0803043e060d060306062c01050d0312090602030c120a090302030f0c0c030a0c0e150a050126011e0b0c 69
    0x581d0282c030f5203040da47c128040c8001078051003040b920182d02c824801d4440b410b0101e2030f9984030840d5000c400722130320200100b20560b0350380a102c20400360801002c40e400b2100403560850307940244001d0035148800d686517180c05460b0400d0b80c0c25035401d11b00e03080c00c00300e615021640c500000325103040203081210240714442c0e00002c40c89001d005910111350400307100140d41101c07014560040d0700f807000e82c1e160500002680e40e80c0045003440c40007100d19882460700101c040b4169080507002c141e07000c01c7d5450603944510b43c4804014000c1d40c031508480443d40c42e2000c1c40c040e24003002100e90314035030140e00f00b01e40940a0402e8070510302e000085d000294000080340c81c14400d07422916202c070b00c0c034a417150a01e000d0b480b519805010300d0605d18100b0150340350010039200801d0310000992140c56000f4001c000c0d040d4019002041c44000780900e40c011403443c043c00c0c45420156031049000d46203005070403000c1c0e210190074445c5045000380110400c540c1c4000d01500c1c8982070800f1b04195045 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 387964640 1250 387963390 387963403
    0xe060a06081f09080d020a1805090430020601060306052b05030f04031b0e091e0106090614010f170f04030c02040912030b030a0b0c030709030c030f06060512 69
    0x195003001e8251409103510800390002c500031500a2000741c3c417101140c55060282d848100c0410004820304101e5440d5001004101309981000d400a03c0d5940c0701c4d5a4031704240c0380b02e0041d6030030443d0621420105030050807150a1412164090101949001d00c00760a0b60a560861881031424a01c4110758110b032036246410000601d03120f10b040c0c801401c0c075505601c11900200d100020014010040c01a03002c0320400071a03051003c00103240d6500450070050030152a080d903a40c005107603822080d00c2c0640101380801001c800050002c0d0741b4401030049030f00c02d6020350350704440020000159a000f56000300442e1042c04e142210301040318880404481c02011100d45170782181c00320701414410500c00c420194043c100700070b4a030050510300d100d038804441148c0001d0404042c524103044c080394140c030b02940400e5165440e15000e040482c1500300422450800500900000108112900300b90086000d0001c0c500762891500300312080c1c442c10340200380a6113881c0e8007203080b4180090203 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 387965890 1250 387964640 387964663
    0x1a0310060806072c011b050a110a050f0409080426010c03140c07060207080f091003020c0c0103020304050c03060103081b010501150309061e14060d020303031f0b07060e060a0608 78
    0x8030b501303a40100b005031028001c0d05000c0007a070380303114500c00070400c00003492180f980c050058074041e2203000c01004850b01c1c050041582144540010f80c0300d504058002404440c86002809d040c591950203549002401c3c031803600301c2c3c1c20359101c03101580600b8450022208841e183c10b001c200b483c41c07050800850007030000002d109001503a0000d00240740e041d1a000c990010b103056032145502e00d101d0568000c80d04040c410400305031100e070a1070207413013100c0f81191002d0180205072242c40064000f50401803068038075024801d100000b0fa03400303000d641c0c041c62062500546401080c900d0494240345140403640907850500184003227118a01707010881c103481c2c07801013680c070b0943ca403940c0900303082c044481803041c0b032002d9412290a130341c010403084101c80160711120340c2c41c2c008100450010315806034240d001000460141402081b00740103422094030040c10159654020380c1140c0c1c0700710804d490b5540e84a505005940d000e10449800c0a4860304c28081c040c01d0101e103c1e00c03013400121 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 387967140 1250 387965890 387965957
    0x90907050313061107030e010f02060c090a15050307021501030f0b19050c0a020c15030c09061c0506122b090f03200d050c041a031006080607 62
    0x400441c40b0100d102c5615038400c1090200b40150b4248084035045103000300c020034410440c0c40d800e03507c01c00c042c4032840001d81c0208403544075401010502c0e4002880f003904111410f90200d5144201c48142911410030790300c544d0b8914080070001d0520003a040c00106001e003050042002c01c0c541c0080e05007240c0c0040003000300d40c0f2031581d1844407000c11800006000d042c403042001500100010f0400450035400b543d8a003140c40342006000c0b50003020041341036400380b0108181c41c12500180074a008081e055070701d0f14003e400140c0134203000f01150b21519460300100100d0741850060200000100c1e8004c010740da000c011071010a0b040c2d4901c54413040c0b0410034540456100740042c400030080c0c107038a032856070b44909042445221183c54991501110990256a81484a90903000e80d8204025000c008021010803001c0c080041421142c81111403401400e075a0602400306036170344440e000500145068500c905120000b0500030900502d01b134003070818010201500b44050803200c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 387968390 1250 387967140 387967147
    0x81012032d090303030606021204030f0203030913060504110f0a08060a12200102030702010c0303020703023a05031003060506060f0705030d1505010e060a030f11120a0209090705 78
    0x2034000d003054000401044070990240c054203034082e0403503030365400c3e240a650144a070b1900e03184180c1c1ea41072204442e081c071400c1008108003140320546034502c06031004042c2c03071034244000d0000e511004250001e13001a952a00200980e1500b0700c02c0300703404903c0161712400c044183d05c0b105a10f004001c0716109010103080002e9050342c611003200f000d050068188103607922181003a9000a444c4101c10041505440072403900b507000000307682d80903905035154000603d143e0350840c082d400c100002c0302544508207103010382070894030f40b4020103024111500440000041d0b000c1d9070744582c14a003410b00104209001c0400c0d01d80845100750b030b070848808035a5403148000300d0302600c03412191014043c030124025040100210041c0307000c11603100140103a001080700d10b07101c107a09201d0113010590540742e400545c24100050b00c400c0e8010300340042e0700c1c6d98510901043d80d0354100316003951480029400107015510781c0365078020301c1036041107040031910f070b011841c0d51802902035028840b000c03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 387969640 1250 387968390 387968417
    0x20306040e010c2c0a15030b0a0b1809060a1a040305030a0504051f09150c1719050913020c0a1a16032c03040902040e040308101203 58
    0x140c00c0307500c1c0002054020000041901c0c401465485020710601a01c00c08007440390700c040d025070015441c81d0006103421030300d81c60301c94200303240c48412600c6400d00d40c0f1303846440351a40e52044880d004100801040b95540181d811800c880258420250b02c00c0301440d042c801c4d90f8640018a10503904041c0d4a82c0f03490030310300d000001d14015640001c0180c440003a000d82855440703400742c021100181c8443c2c6a8402c0b070604200e00303103088007450001500000c0104500680c0e41c4200e00d100c211401e1030395685070756490f880c04140e64400c0308515804002441c0c4184c4e0340004c00c03034410707040d5494403504104a000c0041c0c0440107503c801c91400d500410303078800101c010b01050f04401d030710130794641c8952228540d1304940241103486580c07601d05152818170303203402030081240c00703645462001c3c000b001c4a040004210704c150001b010030300c010321012500001600c0144090442c2d4062110249442d1030001c082080040000e002c04000d000100580c00411101030300c85941802c0228148030720 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 387970890 1250 387969640 387969649
    0x23070902160203030d06170303010612090c08030d05090601051507200d0f11060903061807091d01060506120114130f0c1d0d0b0405011103010b131208030703020306 72
    0x988a02030f41c58000080e43c002201c2140d802001241c41c0324480510ba50030764000a82c90340424882c42020426105020710500603a41c0000340092055030b901002c592900350700c42c07070340c5c00c150060034580f551341f405e120490308104101d0780105400c8450400c81400d4542d140e19500402d04021b0041203034500300e004845030714800b148d410102400f81c02c540070541c1845003481c0c0601405aa100007001882e6046060940880d0b0180c0c1000d00205031b5500c1d0380740da102180741a002d01c089a4001d0540c041904c038900d00605402850761000022007103005085142115600c2c1e001030f100d000b08011018808034803e0740b06045681040542c0401e08601e0701051400c02c1d10020035400341c0c44c0010403200b800c0a94002900c00a051740c808c401c400e1480054421400e43c0040c89520034812021030f80081e0030101495440303071242002280417100c00c1d2000002c0c1d0001c0c0c0040707844032000315541451040c8100c0c010003d241e00c1d62011204045900c480700e203444050241000c25400000150310340c0c0384d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 387972140 1250 387970890 387970927
    0x180314040801020a051201081603240f060602010b0904121d0d030c11090919020103020c07151e080604051e0403030b13110d0207020a080a080723070902 67
    0x10078000355510b611075540200384d82d0110301c040203240103150010407441e4002900741c055038005072602400500f07544074204400400c0703010101c0003120001000a012917400380001010051101044080c149000a82980c00030440c03e806007402d00c0401c0302254000400e2400040c45007029038010100020003401868401d0405400c101e2502c220360405501c000041000c0780100166440003000c8020017480c41425609003549601044600c6604000b00c8040c07001740c2c2c81418018603003986080c145050101e903030b0110300e044d2145e40100c08c0013034001409203400110030681040f0700004400181040380c0140c40c030350060f0741c1c80c0c2c0007608410684408070721502303101c0510400d40c42c003480c00034050000301d04a00d00507a0030308580d0704001480e0040c00c0c030005011542a04044662080c0d10094000074070990744641c507118001000c020505c203c042d060300500d0a240e450b101414001c09006941160a004841d1240b44505880000c580b40040d20300c038803c05a82c90040b00408200200d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 387973390 1250 387972140 387972149
    0x90609071e0815040b03070302011103040f03080d0e0f0a121b05011a010f0804060c1431051809070801020c0a052b03200c030702011218031404 63
    0x40010403400ca416003042d5440d1042c0c07400d2401004008160060006640c600041c441e0103601c030000a0006602826030b008403090311000b240d041503601c0f0030100b4141280c0d4800c0c6c41e1444005015200307194240070b5000c981c0022002880728420903100c047d030310285494054002c02c244207120b1100c0d4801e613400f20501e4a40450703189003100c1424114024503c18214480b1100044403443c50340d402980c0105400587c3d0b100c50640f03540d0350311181c02030080c0d0140c3c2c0b420000d82610b9021048060700150001d0f1164100c6c13104641a030042d650041c12030b21007102c94549007180c00300003c0e590500820008900301c0c01640c01c64031038800441c40c1c805d01d90440303142035001240c0e01002c401e00003040404030f40607a088075961120400c0c0618040f1400890b00b048004070003039030b003c1c1c6020b608645104001f00000e9800d03015850030410481d046900f40101603040000c0c4101036690101008005140050341003241d405410940c00900d030310f4000040c184244c8120301045405460155802030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 387974640 1250 387973390 387973427
    0xe130c1e0504020d0b01020606120d050906130f06030510050904061a040608010b010e040203090c060708130306021c1505040b0420040503070906151209201c0209060907 74
    0x21007202113458007900d41a52414014400e10001a00c9403921510707a044c21200440a80125490580111500c1e40b0481601d030b0404010001c004111160000b582c1c0200010522001485d0801c10014103a0b41c01070b10001da82100c01c042800709660742042350360003540c0b16100090350740c8240c03031410200e0404004141d0052521100140002064114410340c040c00d07a203d5005014500410080f40030544848032940d10861204c40142028401410a80d0180070000e082c00b09001912200001702c0d00103c914540202d043d5254104e8004141800052003000740203440e54001a8801034019100302c9201d15150f442c0c0340d03900c1d2280da1020b00030b41000400342d20800c11044240e1001d0b8402d2146600074030880200060304102842100143c0ea01e02c0604030b40409445400c0790f491840d459401d400c1030ba21107601001425603222003090b07000d1514540ad58a10790030401807c41d440d04001c1501d007401006041c0160354400c00300364030100841d280d40c0203403102c03841101d0520940748818000d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 387975890 1250 387974640 387974647
    0x9130906060305060a0b030a08041a0408060109020d06052e0c080c03090f0102070812030613020a0f02100204180203100806011202043603030e030a090e130c1e050402 73
    0x1030000100303040e0b11605c0303444810301c500b403642c80074143c0e56684100d01400c0c000d03041c0000d100070003404146602d0a840c51558a0602d0344400c651420b101c020b91101e46d41903400a028041c0c00e00e1030050100400c002c40b8074178020704d0400c0010700980700000312003804030303903072075140c0c0b48a40143c1180b210180c00c907007869151151403480669030b03401130607514030490040040203c030b5071000500405507014840a03100086810f85a92426000a88081d6201400d00c0c40d4000000f9180b010301441e606a41c0c0304020244290310190501c01c00350300011584e80104801d024088100c1414840c1e00810030b401aa00c0e61203107210454244a0b4003c1c2103280a404000920320740400c0d4100c10041c000c50302000404040300e403d1207084003058040400f1580401c60f0b014079201640c0390103080c0e00078140070641c00710b0400d00c40e0031507000307000d013001086222600303200300440382884035404880801d4040e08032400e6110100c010649100b1940d80702400440800c2121681c19408002d0902500664a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 387977140 1250 387975890 387975893
    0x50a0204080d020708071a0409201615020a02190606030506041511160b04020a034419050f07030306180504081909030b10030506010b0708091309060603 67
    0x4462441c0c0c45624014460541c0110721454817807c0813603c0851011020300e424905100c40000d090722070014125200748280510709038003588010105450710b81c0400e00c11400501d8039000d50b003004400400883d10502040c0c091075000140080f4030340d03240040c0700010620b4682180502050340000340107004410078401089a9400c12109010703694400340441c801d02c074002102070096403941001011420350200104070244406500140003501000c2c2d034070385944902c248244c80f01141c00c15800811403911030005140c12445c410311003c045840c0c144c4110303403107030f04038011005c01125442090458000e42805041201c90009109036415180c0500703082c090700404280c40b8284c1104441010010405110f2003128400c681c0842c4280c01c00c85e100c0c854202c0103040494040030300004040c080045010308050600c2000190340402c0c2850862400038104a030603480600321500520001000581003070035254007a2087d940d408503080840c400078050a4244400b40031140341c2a008030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 387978390 1250 387977140 387977143
    0xc07030318090c020d140c1506030c03031611190b040914060120011808070c06020a080d05070e1011010513020a14042c0607090302060d050a0204080d02 67
    0x60492580d00714603040503554904007050b50099000c10006810011110a9a6000d849005044294280454100203854003828604120080100c408880c203c0402c8150b1404000300c0b104100d05602071070409034440405802c05009940041c07003009103240f0010345440b08203100352202c2c905400c12040300d644180c4070350f10b0351141c001d00e00043c0c104403400340e8002c0c01c0c1e585540941c20681d110354045112204071300b03031203052000b541c0c82e65481c0d1030040c01440282c0343c1e24aa460181400c9680e8189c80c3c6000c1c161118640d10120079900041110390100341076405407071203854607a6000c64155a0900121101040d404c2519030050345c1021500280e580040c002c10701006090080280d511860014081903019800080d88155018000d010940c3c0c0c02d2940d44094601902c0420500c03245050201c0b103000c8800342d44000142c1c00c00c00040c00004101d12904003881d41004560f090460300803070014401d0300141d051098460001c07406001e89a41158010181c0c0410340c0c2980c0070030740000313 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 387979640 1250 387978390 387978407
    0x6040e3103170f0903090409030e0a0f0906050906130b0a0e0c0a03110301180f02040b0a17010f03020d0f030908030a0f0215070c1e1b0504180201080112080c070303 72
    0x220390890008000f90744050b00c0d031240c5004520380d9004505000324182040003030400901c0803400c0044205840c416520713524480d1014051400040c4001c9042c01c0c030110885440350b0016115613010000d004850304e41f0110710180d0fa03c201d00c04904211120081202c008280d84414402003140041008800902c3c028000380d045d50741d41482a84021050703400303240421301a1440503411a51400c81000090380b1045856645400140c20b05980f5505041190040e01002c008102900d9a1003040c001d00341004d80507100803840101110f007982c0100c1c00e4144614030090400c80000d1001d4185405000548000c00d102070807641e072441501c0c13009140003011074440000d0b1143d5801142d48602d090042480768185540f4403101000715100c0072080c003440016031505200c4a004000400c2e0b409d441414002c849071100c05c48680f4000920088505400030501d20742140308c0700400603a0320400b01da0440325881340004940d42c1504011256208000e80c000c41481089000820150002c110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 387980890 1250 387979640 387979667
    0x170d050c09104d010903020d050c1e0d021006080606040b0301090210030209041a0d02010810090504050106050109060c030e100201060504020d0906050906040c0b1804090501051506040e3103 83
    0x1020fa00a2460682a280301d07010040244e08005a129441c40c440c4000d084815401821204001400449a901400c0ba864680d0542e0848040f401e482c94041080718039940c05004104800c0b46440c0b00c00381c84501c050482413007203841d446501c0742680e0942007030b510070341c000b8610903001c822a00060000e40c070003104c04e0b0140e4100100e92560300403100303008880c110b029100e04006812680119248072004000344141c00c15920b02090481c1e20340300e002e204510841c0009070103030900300050035020b80c2d640064100b101c803040c60400a61700c40450440c9240a540c188048960310f10300380d014106540105400501c085440422034055810415903e0701482c010000f980762003407002d4607210100d81c0582030890001c410000b21034114020440010354104080c1d40045020000301681d000110550341a911030040c01580190f000c072480c0b00d13000c125a814580352401d992526012030042001c2701440b43c01c1185120034504e81d200c1e00da840c03c4108c1032410582146005040104d41040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 387982140 1250 387980890 387981017
    0x190e010e120307020d080c0d0e150a0c020f010306080a1a071713020301231e01051c020f1908120313021c170d050c0910 53
    0x50300641460803999a086280902561402c5407903024011841411842259601c200300700d15448a5424850b644100e07456983e0a6100c010403410000500b036014400f9508030020442d90041c15042864400103070313030541b9103c00b607002c04d100503801480b00398400340f01c0f40503448014003000f1805600c0070140b074000d51001b4068840d0002201e4072581401088500f841880124030305100707400210820398401400401e450002d842540049040440000d01382059001805020115200d1618420401c45614200c07589014005075544007011480007052240400020030340d1280740354002083ca0240003480101000c00c6401840300040c41481c483d8055201c3c08030708084401c04403070003032103200040003200c07940c3d03020080d0300c40e4403103503582078003441c00c91440c00124200c810020006440952644920f03d0280b01410303144020800341c10301e03a08203c800c19070303607800c40b207082c021880d0b02c1c00705004000590100d00d040e00312a4402e544001e410814400c6055109404002940c0c501 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 387983390 1250 387982140 387982157
    0x170112020d051b04110a090512010b100e04051302150a110106030812130b19090210020d02010c050705060a050606040803070b060a060c0210050306011803050d180b1e190e01 76
    0x100c1710740e01c0b4010361240e50005004458108050b01e8a800b800b01c20b00441e01c000175000c1e000e040080c0035600c2010144001c00c04804120f017461609216142d802445502d80c01d42201142c0d00081b10361402d0b10030009031040200701c1c0704a16204124405501c001031008000b0140c4030304104286130031031003c00000d041c280001408030803140010b072b00e40e40d600810f0001e15890f048072042452086000740c4400680c2c640154000d0b90711480d8003150300c1d01d103401a01440350664002801e5540e0642c02406202c4100705010000c0d50000d445540160140b40004140c2c840400150240c801d5921140d940d10000c11080e0030300503207041c100e004520449402400da0303070724402035440400e050f5000c0d51120b00c0580c8540404d001c0c0d001075500250500d81902019585a210290701d00c55401c103031407a600110401082c581c03c84640640a000c0c079100c422460311340388444100784903081e8800c4204e0410800080d16640740c100391079405400148020110000403001025005a41086130000d45601c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 387984640 1250 387983390 387983411
    0x303010503060c0c060411040212070c0507050f06030f090a080403052d0309090603071701050402040c0e030a060c0905040c110610060906051e19020d170112020d051b04 74
    0x150403111129051300192049030b41d642c030340d03404036030300c41c9080c40c0c1043e02048200d480d41c1c01441094850000f540764950301c1041c0c1d003803040c901041ea03001140102c0890000a82c541d4401c3c013035a81c8030b04c541036101307005da40d064011803c103c1d55a40c0100f203041c0100e000301c100040450801c1100d040540000c0d600000608050710b41d2810700c0d0070031000c0d0020071203107220781003a5000c0d030352180b0081d0468031065580c1c0c85200e1040f1008041d81d80c1d59540300d0902045141c075005d0420902c0c207070b07d0070f00003e201800000b922040c030880003c1c00a50b42e19402103400b4011010940144001070082100d841c011501400c804082e8140c0041d6000b102c2c00224038144150541e01540e2065456254036801d2800c2075400f54407082c450305c40718282c0b0307005484c0c201d04040240100034841ca604a0300c4000306034040d140481c41c18001c0180512494003c0025840801c42030440d44113554000c1441054008568480300003000940b403401000d503840e6000d00c4038500580c0021050710b0400016800 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 387985890 1250 387984640 387984661
    0xb2e0201141303080403020f06130c0506070309052101050c07050f0601030c0b09010905030a05030406020d050304020d081605071707080105010b041202030f030c241501030203100f08030301050306 86
    0x1211151404a0061852400310b0310a081140e4042c6c440c2c012070300004c000c00d030023900d4144229602a00e0216548181c0c04002105041c03800600055a041d801c0030700c1030703402504a8506004543c061400d207407605070120203840440c111440386100030405401c10008481003540402825078030f603c42d0f00360f564507030400000c2c12412250840950542581850304a120940c017007101e0504111000c0c0010a10b541d042c441854501d110710b0065a8962030144042d04003803000b1500018498280100801350312000780190381a507111060641d00c450039031460b5000701e254940680b451181c0d130004503410b44200015501c0012500817581216645d9505030b003620424000c106804405000c1007110000b0703624844541c1d48024251007080119074101031664200c62111840c5902101c004400b0320801210184065440640400c103032802240035180500701c003882504055000000030a5031105d600350402034202170060b4444075584041441d0369030001e0050318428000c807030106109594 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 387987140 1250 387985890 387985931
    0x204050717191409060702010c0801080c060706060b2209090312090c030209190f020a1b02060d060e010812030105091f093206030a02040b2e0201 64
    0x20720546408160361521880010b49840585403440d1a498403100c43c6400c2d078105500384502101c07002428a4a000e01009082d10302119910050250f2640140320608000c1003900c25010203550842e1350b02c18030303d090002410a41c1c08200d50070404200e40c2c4109100c0002d410542d070b40040468049c98135100f5001c1211110100240860030801c181c0d074004d69250400c2d040d50307008221403400d585c2d8070380100390041021510200300007072201c112412b05040d4890f1030300145043d8801c604142c0c0c50340e405040c46c4040b88020040007034039080c0604564991040b42c50700c07102c0303c4060207840d648481100396200c080c0100e00301805240c0d0780b00c40c3c3c1440784007606d040381c8000740aa40c0640f121140b0070504c0c0b2000e4182110900d10b8103004c5401d0380507010b000c41c400d145281c10200350400c0340756500502052000314071800300e01d074140f080c030396800100317030100a404540029406410303c0004601d2849503091102203520601c0042d60b005006c9819581001c0b036800038030004604500001200c1c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 387988390 1250 387987140 387987167
    0x815040204120213060b07110a17030d0c090308070b100b0a0201140a0902060a0f1b0f02030f010c0f03020d09050f0105311e06060323011505100207090906050402040507 74
    0x21407d02c038440c007007400c7d0310403031004d40005001900a40e131612020645036038002200c41c3c040d84005000c85012505208000a032001d034680441e00508603a6000028404c2d045e0103421074100e0307404603d00d80e038490300c3d01c07006104221200c0da5400380e258000e40640020004040003241140001e406e40110f4014502c005034020481440e1044c0042c05580000b00144c084003004183c07248284d215603103907400a4240e000d110704866180e0640304062520b8070307002c680c440990601c0c28034a047c41e0040f0802c020007245007809600c5405203000f10b0003c00c802100a00548200c0484141400b81907000501070616000c44e07181c0d00c40c1c11041c68200100a038000c4011a40b0002000d0200d05401c0013081d11980e030411001c0030340c8107600e4178015540640c00640740d500b0305201e101c010a0034428445a503a8030721000303211a07404049600d00d00811072107081e0181d0300d41da921a030314030310078000240a0311410008200040142c1003500c003d1104a4080740030340e142501150600c2d0041d05801102d8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 387989640 1250 387988390 387988409
    0xb0118050d0f060513021003020a0c06051f0e060a05060a0c020103020906040b1b060a0b0a0e0a110c071a0304110d06021e0913110a081504020412021306 67
    0x1914003018001d10311080c00c0c055400010b020701000000c0c0c1203020b880d010320800f421140c0c001002c4d0040200d2241180840030506104020815080e50010001e03860290402c400180e40d0741e4030b05032100c807441c5880356035404034a03142001c0752a05811110718024a000d840040c10207441e80d09201c45441111040700101303008041341c0006611075002000290805004542003950b14807007078460703401440c145583e1442d101410351903e80100151341d48100803080c107100c02825500411100c010314041e9035014400200014003e0b0901e41205804120440300669288540c00d126602e40f1464000e400c4d440d0080d0100036181c0641806580c0103e81103205403400c041c48104001410b4034001c0c080701c0250302442009050076051021340000403503c6020f5586200301c80c108203001d5036480d12425000d24043d000b10960400310251080365046007072050b0546ca800e0458006000406546988240000b40104500031901d1074002d10910981b020042d1100450064003595400e000c0d09128 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 387990890 1250 387989640 387989687
    0x71202060f0306010309020402210c04050a090515181009050f0c0c0f0f151b2205030109110420090f060d0c050301030507060f08070806031f0c030b01 66
    0x110381607400a50700444141000a1807100036070115040c0d0308028614040c2c08500c0078440010090b41a240f0340c8610989070940c070701801d100c005000c0c4278003401202d52042d40c03940002d241010862084d407504100800031010380d0120307a404c840d400011208050b4806020600180310321650060714051406545844e90550712080440d009030400d00c0441e05a00c01d420020600c0304003840468140070150b0b02030704684141c4012034200e080007805d60600c510294a140301800505029030f0042e25441e4251640380d01c0032000814186640d80107640c0c15481c00c43c041d020000540711a06e071000c0c041c4c0c3c1c10b200c03210080c0382c40a00300481c00d1003003005560030440c1c05040d1401d010105c80030000200814207203d421182101150305166420003c50f0000005000b8040d0802108000303212505d0010500422000028035884002c0c1810007400b0404010440c2560107118040c900c00304500d0380d034190381d481034444024106a0180e000030071719215400d0280d5101d69141d1040441c0c4401e4140ca = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 387992140 1250 387990890 387990907
    0x31407120b011202060910030515030f0a030503180106080703030e0f100806061308071e060906030f0603050a0b040c0503070515070c2303070b1602040506041d070807120206 76
    0x240701c2c070f001000c1380d02c08410400c140311640c81c0400d1301640c0480f99000619450040c00b912040032403401b00f68800c0d40080014410250000741a85420342d1603d0400d80b2601c0d00102d0003900400c100c0314007525400c003400840e0045001070081c1c102c2e400fa81d1227010346400c41c0e050041c00381542c0360154212415400400b0403901941d21240c014101411042c50203100781062040c07003c1503081140c26030030400c02002940c00700c1c0c1c81c001c040390740c00310711500d010b18224000c2e021442511036941450385604a50350072041983c00b5038029a00035056401d044160314114114400844086032880451580452507040008001c03040d00c801800700c0d480c111201005510350740209004a5019031194004038071001c10300400012194032909005032440c80300c080604114107608220f0102d982030000c0c01c81850368911107440150161070025041e114900401c001d401d59042506690201d1804c060682d180000d00c8000c40320500c095030340d40c0307442e500080d066100d2420081e6205009001e2583e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 387993390 1250 387992140 387992159
    0x3100e07092304021c0c050f121009230d110609150a0209030a03020a1a10030609170f0909060609060f0315030d0908010c0801061d010c0804031407120b01 68
    0x903000303030004000c05d0500c101101d4921910070043c80841e42480071900400013801c004038100740c0b2603c22140400300506004090b0354941c0d03c81a00540c0b50f46545104061100c221651000f00c0480ca140000241c10f000001d5520003007a805000003902c0c2c0a114545a500804c0450055000201400002121094035204000c0180c034100d04141e007044510099a030411060140760310980207051840030a0070305600310701549c0c1c00104000080340411909103a54408101980e600020001e500101c1c3e043c03520440303040c118003030380e0444009001c5032420124005003040400440d80c595541c0d45540c01d01000d03010b594200c42d08000c040c0a1707005680889000786074850f0044298071039030295040040c2c600720b162142070000c24042e64003030061541c28015980c0c100340e14102074045501d008401003402e46858100e10755885035003940c941d0750f03102d01d94505600384c00c10040c60711135440c1c0c1404109098444441c5030a4070802030002003107044101092805508103000c0070440c0e21f8410300d20b = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 387994640 1250 387993390 387993461
    0xa090305120720030301211505011806050301201b12070201031a010e150f0315040c1b0615050904060603030905010c0206180f03100e0709 61
    0x118144802805a07510a07520310105501c036030400d03075039000c140d003d041c10090641c9441c2c088110640040006002e03004011000103c80303c00503005a000000c2414010100c3d194940b9694415043c0000090030140300c006074601008840420041c031540d400401d400c0703910110f620031303401e4203564082500e180f6103000b901d01072440e03001504410000c42c5000741040040045000c03001030200d0300805559061203120381814201c3d181201c800e00700780018040c1c011005420f48170300500c10100403050409010b0f02c091102038903203143c4034104003106c00000c0c03500003a2a4019803900c0c80800c2420b00c2070950000c40c2c1d81d40d00a80c1e2464502d5140d80001d007191000d101e00001c260840040d07035441d039603902c5206a0041d80300084490851034010651100c0794011410410045181c40140c0e0311001140d8002403021030020344030300300c1d8000c907101e15440811a58940200700070101d2180850304500401d441103016109000e85644d403100072036003400c070350940301200c11261180c00c11a80140 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 387995890 1250 387994640 387994643
    0x307080d1d0102030c10051509040803041410093008010902070f0c06120b0a06020316060b190305010609020703050406030209130e07080601050f031c110d090503100e060a09 76
    0x103a0b0300d0400c80000e011b00e4503c030038000c52551036542c404c200c18840100495640b08200300d81e004407508040d1541081c45c0800340001c3c1c051006001c00d01c00c0c900003000780b580446510101130045444600305100c45029243c00250113092429100982c021152003041e418070303c545500c3d0303450f420150044000e41001200f241c001e0b84601c1c120000c01c03094042c06000303240c80d84d18a00389218444900b003d8800f9115054080c0d200e80505012843d004801e584c100258a04e100c07410b180581401d8000d0014071030b101e90030650404448c1c503c54106070141050f82d00800003408195a6182000201e1090600142c00141c0c20b00c02481200d100703400601c41703140e00800c44441c494480d8000c00407903581b1a25110b166100000401002c5400d11200d0b0050008407030055032080c06101081d00c2d00c045c02e00400328201c9250240410500406000c2e01604030b00048801070545d41d00054000e01e207038040c20b8070070310600490701032030121800f900100c50400c40c00380500e51200c9203030303038080c1421890 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 387997140 1250 387995890 387995893
    0x61617180a060c150e01060909210516020d0206030405030307090f080601060804050c12010209011106010f09181a2401021f0603150b0907110a030e011704030e0307080d1d0102 77
    0x1401d5016175824000c142c06415603a0300012050308520f040442c0481c5190801125004041c89410300380c0c00406449245180c01601c02082480303100203003400e45844c3c0000d41c0702202109000500c503001003c0c501c03c034110745940078101c0d00d0781102440300781107200b4002c06500004c014040c96200c4e01030369400904c103000b25260f060075200025510910003140005581d40452003095030343c0e10002004151030440d003d00450350410780150261a60760080707075030890310344079003c11300300e8042c1114100300e40241800c40c3c1c0d0207854600c65881c80080d1001504880b2031880034035101e8034000b00c0c40d140c2205030002c0c50b41d0070061a07161000b805118110500325664100040401c0404c006005440310356240000c130140301d0010040d000b080502800100032450b000300000020001c5c11482898260800208003280b01004031105400000300043c254640d006220825400040c8502c038602d04506441107d5241d06807140d440c800060410300040c0c942001d0080e0662001420034030090610 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 387998390 1250 387997140 387997151
    0xb0a030501090b04020301052a09031f05060a06080f040b270303041707050a15020d090501150501050f2a010c21020406050702061617180a060c15 64
    0x459140c21281407410a84510f0b00710801c003c1146401c0c8a0345902659400440316460392540151010040c03180e14042004030020f682c0f0711035901000000c50103007803421600c880c501e0081d0030601900d001d0325054000c80071b002c3d01150142c06032443c1442214461a2000d8035a1032361258910004003074035110342a01c0d9101510781400c80d82c030301c2001c5425130400a580c1c0e030800740303009004064030b114030f20f014400600c0711000041004c00d811030900d402105828905107020340c4607000b0b00c40d42c40b101d02103a02e080c01101c10004c2c19042a00880140728514420603035640040d245446004080d440a00c020402c0e40c49a4a040025050014005101c040302c500c90414441c00c440e11250106c002c91280c040114080206c04040112007412610550415103405009032040c0542c02c8000d210b6000480c11030540c09104505451542d0090180b01c503540c403240d00d2290b40d178021200f09440c242441170390070083c1401a00082101c0040c3e80e4070000c1c2d1820385482200004c411442070b9100c0c1c465 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 387999640 1250 387998390 387998393
    0xc0201060501050d05061816090503070302011b050f060106030606030b04050105091305070506071a070f09030602090d2301140f15031c0f0807020a05070e0613060b0703080112050d030b0a03 83
    0x18051142d20140300c823014810700640080c00d00419984200d210740c0c841e01041c070046c0d03800a24007104810f102c2c80d440e60a00107250050400310000c184860b680b1544c4000119154160094400c44001d0303101040501251000c2c00b09a802c24065984c220891301e0201d45940031301d00081d8105400780d41030f125025114800030b08141d00032402581c14034481d2004c40c1034407510000081c3c02803c6418010000c203030402d000b910b014032500c0040d140550101d01c07416281c880c035505080b00780e48075500080303140c0e032141c0080101c03008502119480d0302c0e164021301500e01c1030b90b0941c002c04900c110101140e4481d4029021031107001c00700c54041c0151828040e0994140400f56010407480d254220307000c1700c2805c010242e0400070808c07021540704114000128902080c46800e403400030000c2c0c9459510500401c10021401d004208410700d031140006003a068580504402d9100e03070b03104c082d180d03641d5410702c103200201c0b00080c0068011040000100b03010703a01001d01560b000d04820f0242c9d5aa = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 388000890 1250 387999640 387999679
    0x1242001140103140307030c1e02030f07080c0319020d02150f090108070311090d03180807090c0512010b03060f0a08010f0e0d020703020918030307120c0201060501050d0506 76
    0x34035401c030140900140043c000c00010000b6003070f01c008010021402e1151300d0300e004001c4101818090504103800001c20010070405044070074542c1c01038102c40680519504c082e0395104588070303003034141c0250f0350700c2d460782e250224452800b048035181440c06a5101e03000c11200c2403240742c08982c05202145401d5030710107180e002d062a001018407887d10b0364120000506540001480e19080529015a1820004020b403d950003240c054500340c410740207601e400c0d501c5101070709108104c1c140710440040c031444000740c1402540c1ca00c40d014005980c4c50003060380d00380113140c0d624241c0003081d001440540c0c210b0020b998080001080d04004404460108202004907001601680d44540e618009034510f409000c086442050041c410301d90072600084d110002800003d00c642ca010002c200140c2000d528207126020241c10b595a134100a00081e00210069442812140c28960642a00303401845820300b00d8106849007854612207003c80c2c030007000000c4c00d05902001400482940848 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 388002140 1250 388000890 388000901
    0x120c01020c0111040f0603090f1b03061d160501020303240a0b04053309010c0209010602010c020607080106080c0a0c050a0501060f0b0906040b032e0e01242001 70
    0x110700400d0f41d95a410090445518905a041581454200440c190000310b0205003440401e400c2181480e44040c02076003a580b4590f503510251a0703e04201d04041502c0703042c020540d8072080f200844014040d8040405648865481001d0240c0c00500004001d849071100e994029246c04145103500004000000c42d50b2000b600a1100c2000c00f00d002d10941c06d200310b6924007110041c0d100e54000741c0151001840034544410700c580712001150007022640100c81c100ea1580d0b004013810020340c3c551200900130140c240f2650014480c50300402c542c5801040814180c4501d5511f0b0b8020f56070740041c00046a00407441c00b001c03c01e003416002c0c007249040c400c4517a81442000085030f11440d0916032406101c080d00a002111010000010207070369400489045604c048044d40d10b80d41c3c1c4a64106d00c144141e8200a00d0b00070200d104041c50305220000b1381614240d501c41651130344c07a02d00100380c40071424070007009603444484680c1194045d50b60001414103204600c1400800310000c0e909440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 388003390 1250 388002140 388002161
    0x212070303020d0b03010218010315090e010c090b190e0d080309060105010201050a0612170f0414010f050301060e01140409110408010b0409020303160c051c020120120c01020c01 78
    0x39400f00c0c8100510f0840d0003410680c030300c200d009509000782082c50307079408601c2a16160501d9034030101104030b940100c3d81b200007440400301c100402c071003400199003e8008001003030009100706002040260300311050741e0389403041040700642ca0240c030030280c4010110b0300d0b141d0b9024800d0988200018600d00066128043ca90050a00f40d4074000c00a404d59801405002102e41481c105105070f0341d10b082c074141999000050483d8180c81e00b40341038140d220318440681010000a804160814081c0e6207203001d21083c0c1e0b0b041c4030286a104101c500b404280a10000900901c84528503584030b80400c0106252a940461625079215030b80c008030340c3c1003075120740b02d00804038042044240c07c3c45004c001040584003880010881d90001c2d480344110029002902092a504800d02c140510848080c000c06001c0f121404d803d0000241801d4111000305c0c00070783c1d22000700c25104c02440c00c207050414400000c000d044c0c1d4007100c155058010440b42c8070550341c01c0c040500707108024000c0d9a0b00704c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 388004640 1250 388003390 388003397
    0x80f070503120f011505090402091c11011d040b0f0603130b010e07020d0f0525021c05031b0c0a03031e03020301050a06030c0e0d03030e070602060f0604090302120703 73
    0x4542000c42942c07003240041c103500030745200200400001d6182d0701640c1c0900710310b140680e595640c010001d0000e0007030480154000049408440f00801c89050902c01140191541c02c04c0b0003000004552128904011031358104126200414a040c80c1d0011010444c008140742901d0f43c5141c081289a00304035000e6240703252a0a80d041030010b5400510701421780021500344515000c007001e95900c400d80b0840d01004440d501030800b0300c1c4108282c0e00380e22040300504050000300c06103a4007000480381705a03c5030060b20250460340411240381583c0d154000e01544c2811b282c03009040c01021142c50749440390140c5801c0e14610760f241d00c0d9031006507102c0d071200c041888017800807040e1040d405003084240341c07040005000555030b1080703a404a800520740800c1c503d00b20007007103400698502e9903981000d0302c900850101074158001c1210070107280112100355a491030101d941c1c42041d200340c28050030039000b040c140d0070650001c5080c24024011641c4040c20354080d40d81c250701084c1c068000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 388005890 1250 388004640 388004647
    0x3040b0d0212250203070203030702010e010207080703081315080f0a02070f15052a0d11030901050624070f0203070b0313030e0d0302100507110304080102130b070c0b07080f070503 79
    0x48000c25403280c070083c4501c1c40214149022580401c1e500d100303604002e414003c5a048001d9160700c2041202c0240491805440d0380d03c0c0e40340b0748441c42d5045900c08030072808000c200402c00600120840314040c145980d00901038446070300c03400b45a00054544945103130200007641c00b08030b6852242910b0b0b8480e01c5082c1020b0105c810031070441780040c005040c101c03030504810b000d1a03a659140300c1083c10082c5500e640300e000464040042c0194010088400800300412401e280194802da100e1103054038511070801081c4a0521041401440301030502014031440010600306d075012200c6c41d20103022140301c2501c03000700c1c601e0f64108031802c01040e440b04000c0010140d00072190803100400340e58807030318050355030741c0603440f00400c003070010041c3c0c1d4a90018101c20b1003558988010240807050380d6031151101c1d8024080d600c0a10400d2090300b0000000445410b2242120004c641000441140c18100b40e039035002035208580a4601c0074003400051a0190a1401401c000e4440d2004503034 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 388007140 1250 388005890 388005931
    0x1203080915040b0a020307121b0f05030108070e09030c010615140316050702030a0b01120204110313031407020303040e2a090103020a021501090c0206090a020303040b0d0212 76
    0x7030149180300240490240700284000103500840c0d00f504000d85000240e145d54031044212511100e03d02440d0055050252207940e88803000324640c010540c50380c03440d034040c00c07511302521103210a00c41e0f405e490380314003420081d1040a01540760410f480000f903d2403c980842100d00f9034003250804145048135080250001d074001400c080e001c022030074020308603d461152070200186200445e81400f800145aa0455500380504aa001e41c03013030400c0c515584076520147d02c40742c0e980b8124019482d2241030500c0c3c01c41c2900366071107080030341c200040000140c0c0d011031f000c91280188650742103080c000400140c1e01400984094951004035aa041c0303440c90079902d00c41040c8540e00600140e4055032400da10210b421a41c0d40d280c2801c015a80e9242418100d04c0c01282d074052000a03129000045400e0129400034114804d0701c0d801c5480e29218140d20326100d480c0100004d605a00c20001080a10161805410b20720692140103041410320042e00d410010704446412155400b29030300803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 388008390 1250 388007140 388007143
    0xb0a091b06111b0303090424080708010b03013605010515040c0305070c1e0b0a1d060702031c061205101a060f07020604080d09080111030c18030712030809 68
    0x11070b07283e0714020002036110b040400e40324485c131030100740078580760400b4010285400180c510400f442c041862002d50f0307546060ba807070340d43c2d6000d054195402c0204a46c900d140500548040c8024400001900c8900085240d500c601001c407040041d00c51101e41408180700388240f42c070070407000c82c00500301080c9108010071500600002c0040c10300c0c000900c8034956114118020007640000302d00a1041600542902d030030049000400c0711a05c2420080d10302030070380220700c440140c1042c29450030001d5103003a0716240111841001a0f00c140140ca14450200c4100400d41e0300780c2c000020541e84034101e01403945490401511160b000c0d010395245507400307100700e03160309103100d0b24a16180c2003607000070024801d040340ea100e1000d01280340f005558980b400c881c0141920000c032110a2450000a05145500e118003113141d440e101604e201e0460f020112486000d6580e0082d11340a01c6230140000c9006900a985e058810b00c1d40110303040714020041d003030050082e2030711000c6142c00344459 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 388009640 1250 388008390 388008403
    0xc0b06060a020c033a0813081605030d0f090305071209090e03130806060a050d020a050303040f1802030705030a0c020f120d0501080d2019080d0b09040b0a091b0611 72
    0x3c21070019000e046405c4250300444068016001054414000e03d6604100405004000c080b170340c100c882c100e11004210000009151001c0720070310500042c2180e60300310040301d10011000d03002c40d80c10064100080c81003d6000510342413418003548440d00c0b1400081160900700a480c400d40c40010050001300e03425400340010b0a20100410041c07401c01d0102d610082c10f880b4503402180c245211408540d50b04d4002000fa02018040b00d450700e41c0c4060400c1010490f10807641540e01030000d55009172164001c90384a2207094072000c0c60340e110700d0b0031040200303102c000704021400745000800f118201400b00e034405c1041c03504102d48a1075040490803c0310b206901030b087d2039000c0c40f00c0411032030300008840000c41c10680040e09080d244008141000000c00380f0060001191510208101c41d007009450403082184003001400030b05070500040e60426a809005c0062050004d4a85540c40d00080c03482d41c41584400c28103003001d00d0602d60f24400da004000403c051140c0460b0b94102000003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 388010890 1250 388009640 388009723
    0x605090112064505070f030209030d05030a0e0607030e0705041b0c08040906060201090b0105100c060b010e1e010e15030c1602100801150c0b06060a020c03 68
    0x2002094500015003112241080381c2802c6410303c031002481d030351000d08001001c81030012103911140a8800c0c0d010040c0001c80f0201c02054501c81860140c038440d10a65108802c054014014088050b500782d950f03401c0101100b41143c0c480710760704008002445442d010b1a030544001c2412140300301d002e41045002d1700000e010380d00c7d1191425045202e03d050217511a01e030b080c460340d80d40280c10500b0304d45c07242e5041203500c00d05100e00052455415801000480d002c0c2c10601c88590704c940c10030441015801c101000604441e01d0300001c915954404294880141009101c18558601284000210901e8010f000d920744904e8085942c000070120141242152800c40201c5400c3c404e8400d404064000e62051030b0100b031041404d03601c1e145807003d5030380081204800c6981180d004001c8403090040700d6100e83c038a00a10001030245a0302000036902c18102c803c681c0da40001c0c810320f40c0142d040ca2046220300e400030011a202400400b04c01541100b1000c1c03400c01051041281c074018010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 388012140 1250 388010890 388010927
    0x18030c020913030203031306061211042910050d1806050a0902010c121724060310030807020a051206012d05010e15030901140a0605060307050f0f0406050901 69
    0x510b08006507020045030b9005600308580d008611445c108070006001a070810400e020b041c05481081c44003054001481160450f014026440c0c020308030079041c000c08010700c6809003180c552142d00d00e040314806071044120f10b000703030405481a4815003078903000e00c030b105000700500e4a04000d000050288982c0020880e0082c88207950030741c0001d00d01030300414090714002804a0411101c0d02c1010f60b94010070300c00e4085038072400e0910014a940e070700c40c1c10007001618801d0158002e0708081050364440c800075602400c00c145191500030290344045000c07030b48140a120080ba6550759030590f5164080680e000b0521903050095804038407030820050001885007141001d000c1500500d5002074603801c4c0382000e1a00c00d100085032801400400ca500c446001004020f048801540041d40e9030818200c8240c1c07d48400c0003c03411142030b4000c407900300204100249061b40a080149a83c03510382d00e104d0b11b400011404043c058110b034000340300042000a5100456a22500d5150300400414 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 388013390 1250 388012140 388012171
    0x71502070515040b07080c070905060306070905030c040e071208040512011802040e0f0d0e1e090c03070918141510030c0201090506010f15022e18030c0209 68
    0x4400c2c0d605809144142014500001080c0d020803245105451407180050200d4200d651a03400600c046c00040306d81750b02030722440d0002210503100c3c1a422080360000f4016014a44442c8140000380407000fa000741c052142e1000021038281070784041407054020120f42d40c4890410003008070019200c012480c0f141e0510310028202882c042c0710120841e070440e40080d0140c400f010446c00c15008000d408881d009860130701c84000e421500f8030751107001c00c80f004070031750180d40100c550340b0003070010494103c0d44602c001003007080500003d60f0401d00c035040c000402e035070310b1003d118040f50725010850043c1d101c081a01340354100042c3c40d0f0700100c00281604403060134401203007003030709072003614010940c0714800214994003c0d40000b903003e4100059903129030f1030301d03a082c500744a98403034106242c6151800c18a08ca1001c5035543e1300e1108013029490ba01075106080c0c0c1038615203009406c0f003603900c45c000d035400a0200c0d13141410a20a4596003240c0c081d0b40104000706100803c121611502d20 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 388014640 1250 388013390 388013419
    0x180604060f150c14030d060e07210c110a0309180207080711040b0424170d0804030e041b0807050901020706050715060e2e0e0403110715020705 63
    0x2c07108042c0046007860811880c40880c200b00601841062003986140000102e001888115400100a4880a00300c04070141c6829001b120081c000c0c9a0412240d1a1504c0e5440d074084503070006c5900f02d8031407512605440040c201d4a00b8140104421004506600e20802c0640d0f1210480c11200342515001c506022003a1030f01d001611400f0001051b40c441c0c3d01d000da0182c1d8481d48001d07071840700a007040000103150242603854600c05189126201918000010788820b260301d1456030640f003001803c40011010015035801c0400b170021818131406103100081c076155407040582020303104244488003000c1b810054001e800141488007005420460200340b80d8002852000b00e8400786400d5030b540750b2900304814103142e02c0c801e1690b100d05201c000580b82c010b8440d07440c02403042d003000311040c046c20020101c071162102d0722501d80c00101d400400410b55014030b400d074003038041e007441501401e40d81005800d1002d0364000405c81003241c0d010b8006c00b5410411035001d08000e0700c0a14940041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 388015890 1250 388014640 388014659
    0x30309100b0d031826060901020306011b0309080d050d0c08072a1a0402031018020904030c050105091c030204030b0112020a1a0a120b18060d02180604060f 68
    0x20340058181310ba20081c909201c8054030380c000003850304e5500a40c1d44002404040c18032507032505400040d11498020404461046c070889000d96416107501c5c00041540700352030041c014803a001c3d030500ca800000090031b0a07061003510300c0d820b03c90742c5842d075440c0121100c504552004a85100300504101001411604022810b100c040d070003070300301818090995103a41c44202c0d101300400302180784500c4408013030340003580d901851007101503c800d104c0703104488049860241c0491064080e01c00e03400d0250501c0c110282d040340c004c0c94035610f190107030784945080d40c1003501c2c001c0066003c80014900001c03a9410440403540e640b606500d05440c1d511000c1903180f060007801304c550126181c070411591100c034260003d28400c20010240070300740210360940c1d0000c1202001017111100c110740c160001d80b00e180220b0600074580903844451009035220910020f101640080380c104104001da9200c001110200724210701100309883c00d18280025210140d100100c0301c0d407600d50030300c0f03417082 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 388017140 1250 388015890 388015909
    0xf0120031201180515121f02280504060c1e050a030e0d020603010509131a01050405180a060f060b120115020f0d080606040b030903030421022503080309030309100b 72
    0x102286d0518984800e03610702e6061088504948944102906103c1c22a11580d000b4010388103030400b6106c00c01d40003260099005190840000018008010510840307020361400c15105000b02d850074940021410b20b010b05c807044040c192040c2d8032041040080582c450301480b40340d20182c0b01c80c0700340701259000c030360140030600629110f4580c03007000540040346600c0050401d500641c5500311a0303012881000d11940a0180c0c6010b01d0801c170000b2950040d500d144c0103c047d201000301015207541e1541802070954900d00210f0a071034040000f0b030034004601502c0982d61481599140d035142040c03150a02490389c820200f950840c81000c0d09403100469440e07071407441b0b401e154800d0ba85050002e4600d2260380c000641111010080c40382c1d5440000113584120311820044404050ba400d01403880c2841c87d2103000164009000c09201110b80140d511404201002095180c1c0d129035400b801a00b003240c681107940d0022007040354101040144e03004182800c1c80402904130300002060b0703031a9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 388018390 1250 388017140 388017181
    0xb01090b2103090402070b0a240902090f030706170105090f0103031b05070e010303120908180307240915050d110d09030806030111090f01200312011805 67
    0xc160214003607200401c1c0b08503402284000c004540d43c0c111441e10394a51142682c1d2043c440703150070411204010507903520031003002440321440d101442c1c4040f5102a40c01002c242e50411300280c540c00e00350310b003000428040e1056480f02070060110780bd85000c0083d0513404607125401d42d805100d09070a032400100d05498041c90501d0305250001030a082290480c08018020306c1417100000d244030050600505883c46592049400c507a4400004190307080490040c0005c071003082241183d00414548800c0404042c060b22400d580e0761009087c3d54800181000d41c20300700c003000e084143d0780620484050300158045080801e00ca002c002e109000d0f01702942d03216680c80440c039110009807000c0e0703090080b611905100721015890b00500c0703540d090718114029820240003151461401b400d070344028401400749811201e40070011121012041c2020100404030440506984070510003811a40d43c7c0075204061940b401207a6040c020242d0740f07251480c1d25010622018044000c19890007a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 388019640 1250 388018390 388018429
    0x1d01050a0306020307090b030901060608090606100815030a060b040b0114030f180109060903120b0f2701080a11010903050618070b071b0f030c0b0705010212130b01090b 74
    0x71395518800781c4011b05150000320000d0008820009201e070150081d40603100250764810f9103444401d13841c1e580702c006580807580300f480701440c90b00b401e102e6016980e015911200580120700008003003828010560000e0300c4a80e211010050b02e800c00e805441c200c58001e01c0c0801c4200b1000d24140c990b40006012400c200301e1003000305401068902d00c14600314442c0c0001c0051200d03502c2c01c400245645802100864070170003e0441c80085481104607103d0050007000c842c000b200204105980c22003020740c5000f142c21400e810a14550766107034042c0001e40000c0a0080d428141055404000043c40381000002c0c03c040c00021800700e0101c0c0c0203244200c02025165900003801d060402540068034400000f24561003402400241035140e0181100000e1320151110020b180c0003000d800058842000740008000717002003100100040c9010f440014180382e11381c180101c0c1e241c1e0130303a1491b442e442c0c58050b00041c0b001803420305004050b0003100700000038955000c40d04e1000c40c0c0a80f40e806 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 388020890 1250 388019640 388019647
    0x7030506070815040c020d27030204020706110a020a0b010b03012d09050a1d0109050604020d050109020a0608040605071707050c031204081b0703030e120c0a0f1d01050a030602 77
    0x11184240032011091a0044c01884024040c0200175a54080350704402c000890003026034010000c903c00325440048506c50f59507040f402d5400b1b01003c0c0d8020780044441d25a1034681d40703550700c03000011300500c411079070241102914030b0410205000041e000032865040400040100a003e50303000c2c07140800e407003c940c0c4100c9001000b0001c0e6440e03907000b51780c210304103c1042024810b0b0b0348403124501a0302120404014400c005c0c0782200c3c5040c00082650344620080380241c41c2c0322214002452041e0b0020030341034040c2d80440ca0314a80c513404080410f0384101400108090380c029182e00c103c8071702e0403011200210329450241c08010348420184a400180c0307840e600000c3c0308446548020891082c90b0742071900c1d056440c0d9204201c1043c520030004003010301d100b00410001c003101d415541d02c910b030318031000401c107140c9001d089070280d500c80c0d600001503d44641c0b24203c0202b407240c5181000f0307407418a02c0900300c50f840c03600320300e0030409030010710041d03580075099016290000001a00d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 388022140 1250 388020890 388020901
    0x8040210020c030709020415031506030b0607080706060303120b09070509041103010f0f17032712060609010603090201050313050309031903021c05073002070306060602070305060708 80
    0x30101d6071100b568060289650126a58010360001c3c000c0342c0101c480f10500e56030701c0d0800c60854a40d0901c080700902030483c10030619102c1c0e0014800c04400130b012520b00300540d0b80d0703001d40e9400501c04842c0e894660341d0030010305030802a00d0088a44c240706c24410607140744001081c040009282609000b4080380301e0440352910303804030714181c403601007080e62540c40c3e140d00b610f40351442c421074174560100300c0045888c07ca524010280031030200000c600700b000b03007090380c075807200f109500c07201c0300f51141c20a40150b503d003201800080d50a0700513002d24240702c802d00c41c0c0d402c0705801c503009041c02e1241c00e0340141d905c2000c0302d500000c03224000e42800f05d146003150451040e40c24980d8980b00341484002c40358610140e409040d0303c030b0b808490710702101315001c0139800403c07000e00c0c0c04540103010b10340100380e111030311411460901110f100c0460749080c02c0204010090b0302400140d00c0f0090034420072400c4d22640d80581844e000410810f0f195994180d0780c0c210080c8500c0c204002d0101051 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 388023390 1250 388022140 388022143
    0x20f090403030f020c0f0d11030313021507080306130c0212070f0f1209150503010b0a0e031209040b0d11120109050a150b0d02100e010c0c0b0702010801090b010804021002 75
    0x71080c280250082d03503174500914545075511050841ea1481d80184001e0440e494000c21801000141d01e03c051350640e0788281c15046900c00466003a0303003041d0503d240c2d00312084c19034001c000e0300f40710b03180b00c1d5144e041c10001e07c20241c0d03a460100403060701e4001900203075500010b010030403a041301c1c025030780c0e9021880c00c840969258400206014290780810040240000c0c14142080d25661000011130f5104407404200c00702401000105200700010f1003000103ca000780a00085801d1101e0600a1000401c0c5495003101c01029814004542c0300349074a49802501d04c03001084034010180078168483c0340701d420b00104614800c84026101101840c02034009085d0306400000751102d00409003803461444030f034504240086031508500c0200b43c0380407043e11003410b40103890243c0f0303540a030f8000d45500b000071700181c0c14404081e030141c0c0003420207454a80580481d1440b10740328100c5200140c21404180c002c0c50a9a050451800c410f903444005542d0142e01100c84c05a0780800c4203069 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 388024640 1250 388023390 388023401
    0x120622110c0304090506030d02060103020a06080403051207030c02160302100525060213050d03091a04080a080711010518090a060e0708040b1501020304090e16150206060a03020f09040303 82
    0x810792400081400150101150302c07081c403804c803d40a8810380e11400e90b04030781340c240c00d0100075030044a042c07060050310720a92400354428440d0810a290821003200e03041e081c0720407144c181c000780d00c0e802400305480d0705104c86000e8448082a06003c6402c60b40000c0884201e002c800c01003040100794582c00b9400c10b488c200c420601e00d040c400c40c000d0b40b820513074081e500409200d5000c0b61102d5001503103040001c003c2100940541d00d400290741041c543d040140390088a20801d800309220124426a09209002c0c0c40c82c403c240c9542d03607510614240a11034030b0300140c1818010140490441e210708c2c0c1900101044089510301000c0e44c5d880059002030a03d0781210b080b042c201c804102801b6000403015000701d010307414815259840811501124030340d481001d0060300140410008003080790404d1407140c0306141640c50745e8240e401c1230620408690b100312402d07840141c2c049225a010310100d60002001c0e1450007215045401150460002005885c040d43c00000001d06240c4280d004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 388025890 1250 388024640 388024657
    0x12090804030b04060c18060804060906020405030f030304061d03030a0f0f1419060b090f030111030c0403120207061704020a17070810050906040b0702031303060212062211 75
    0x40319060308044c14558000c1040200c05004a020505004110140046d1481c01c80e046a0365131850395035207948090180c007d150f0100e4000340c09000105031030354140030a1608192860080da120f150030b04040080e03410714258032494038103004030010300c00e001200f00d0780d0080703001002148840066684030001c0000942c042c00c070601c0c1c4203000303a000380544c1070140603105000c00050300d0001d140034032044038142d119101d90084100000403079401c020411000001c402000064054a92684604c00c1e0740111103201c11000002814010042820800418200b01d48018030095060580151005800500f0580598003c0d000502150340b50040200a84100b001e900e0082c00c3d40b114096482c0524094000b1902814000400120462140302c0c816069080180303d25101e684520802e00d001030030000440c0800c0000400582e82400030724000c5104440c0140c0d02e102d82c00700156800000350960344500d100b114501c00000b0340c003101c0380b0902a140c030f0010f2101c920042d05442c40c03090191 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 388027140 1250 388025890 388025903
    0xc012301050603250e010e01030e03030105120307050102041d0f01060c06021c0c05210f130311030a05090f1915091a040504060e01080706030c1b230d1209080403 71
    0x84030a40264810000f1141410a89400515901100049d000c1e14050290b842d165401880100315030b2400200a0070f0011804084c0c0389400e40b60346515007a40e100e0b4214507094041c0604001c40c0c0c95100020603409060354094404a50412800412031140309101803c0c1c140c020a103040c1d006c0c0c1400101c0803d120310704040010070f202200150bc03d03000303e0240d43c000f0300c04154030414401e41c0c4d100c0501c0b0302d100e45454000e5545120795901e4210414909400f0040100c09015080d01c08000824002c11943c070342d03549403c1f0a80811805c81150b045540c007070003080d00c62000300e00480c4814020b5030145404209078503040e0701c0c11103252041c0e610240d032811401681103110141c0e80014415243c00b92414130280e40c890003401c0c0030305428410740429a025003000c00006100e58800b0100342940d103080c20382c96409401c510f0a00c0100082519407140306000c2c00c0303002900b0280256403802074400f41c20070085900018000e410501c140c010702680f07414560f01013002c050f08803005142d0014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 388028390 1250 388027140 388027201
    0xb0105040f2a031a030a0602070507150503040c122001180303050409060b0307050a08060d200103050a0c0c03110a020a3024200c012301050603 63
    0xc00403509002041245000f1074500113038484e84e0b01a0040310901ca402c007034014007a5058680d544002076210b0701040c3e03114041c904000ca28181401c0b000001501d2580c0e80c60380328106410000c2c51003a081d4841500060700403090b4002500e110401441400542500180c441c1c2050050b00c01c001e650390b45402c140c004080c003004041c0c0007000f500659019240070001a9100c1722114100e2105807080004a0001d21040c2c030014071501c0841d901c000050440c011800f40d0395280100301e001c0300250ba06018161241c080e213568144160b07944281000720500c202040030401400a4545090240800c0302c40038142040003400c011039141c80f41c1c087c0124515903500c9030a0b034049424102251001814502214000c05000c007031602199009802c001210000036015007242b44d0760700000c0446a02e402001c02d01908401c515002e000c0c6c14220b40ba035810008400c0b03802c640038001003104425694850000e1501290030762030550b28182c54496594444607145112104000141c0fa03001d02d502c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 388029640 1250 388028390 388028441
    0x70801020c100e010b031e0c0409060c0e0307030213020703020705130212010b040e071d040e0309130608151305010612210807050d0b06040801150506070b0105040f 72
    0x81da58107440103040208035541c0e201c500d050a84503e200700c940c0c540c0c0f0103481942d080b0501c00f82d0000280c7d55808035154491413202082c01e41c0c200b0700c03056880071b5640d00724101300b0760409484505042c085001d841c0d00b50560740098040a03626081032101c550106000c42050300802598014203c010000020020a02d90132406903006a80c90303a0f0710070324900001000c00c1807006803016100f585951209035034804508541d40c00342d904200c240002d0075000d081d000d464600c101413040b241c41018656803003080f410f118407001101040f10b0704610b82242000703004000310310341c034001d11030101800c0e15440f204c0340b007a601c003655a0041c0c859441e000c0006414015283e00341c51a034801c02d0701d01e00640c190208240420850f6100a0100d0b207c94002040c1600c18001040390340b801410000b00c2c80f00300700100e0621340060b000003040b170795075000745240c003001540a01c0080000f16001c5190205550311076505203010312034030780659203d810074008c006068112009007000408044c1103074115 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 388030890 1250 388029640 388029643
    0x9150c150c090316030b040b13141e0703050a0624180606050a020303040b0403050408010c03020c12090d030509010e0618090604230406060b0301240e0a0b0705070801020c 75
    0x2044080d01c24401c140100c00025408803205040303d8020040900d91f0ba5144c6400c01103a9000380035041c4458901c0e032600c00a1205e00c5018100f0580200801014182d040d01c01041c1503184103510790f50788180010400544001004038805074003500100f02d9400b4070038450605181d80c1d1901800e01091100441d440203081512000d00404c02804d002480c1d1351001a505403141c0c29120b40181c004000142c041002c800b03159401c28400d250013482c0541c4d820a460840305c203060484006500029440c0c410342c000c100b4501c0b08110360240780d01d00440240015801108071070018107210000c9220280360780108509501101c01504680d95800341455282285d482e080260b4880c80302d02000c02d030b040c10a40315010407942400c0c54070210b80143c070440350021100a10846d40c1c541c651002140034440c00c0e0207140213007602d200082d24003004842c1d040117101c84410450030003e12840100581d070320940d61804030b84048140d255584100c0c10480c2c20804650440c0c4003d600004803107101c4c500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 388032140 1250 388030890 388030897
    0x60301150905041104050904150f06170c0d0b0703060b07141e0615031608010c1103070c05010c05010902030a0803060112050903040b1b06150108070509150c150c 71
    0x9540311401c45444504120813a51403800c070703900c0d1140c01d000a00c49420110069a0054022800ca080e82200410401c0945580d0080c550115880c0c1204010b0310042e05058103501c0034070070203041c1c80c100541c04100f284d04d1140c00030f000c80c0640404150203078000d6114101404620042c2551606141807100d5100c402010310b084601c6075000c100a241d0010520000340c28080010309010385601d4885070058900c0d03c40381c1e81c18003410f055100158244031080c002030128900100c0c817904140b5016103485610000362049820030000c1a0000d094100c01d2001c0d00c1c13003420040300c0750240b070410500400600b003000703405110b070010500502c2120b401452084600740e07620043d070039541c28031100356041582e0021003584103200600500c800c00d07010700070100c4003240d8421400d5845a0481c50b088055034500045041c498450095581c410340541d4083e8503403c01501c0c000c6075802198019943d044122114100860005800b0304107100c0e05408203092009250b0701d08001c0000da50552 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 388033390 1250 388032140 388032179
    0xf091011060a1506030209010e060a02030409020711011e08280207060f060b04050102030405100c020312030703050601080610080705210a0c0305040b0703020c070e01060210050603070b070f050c060301 88
    0x10f6009000048140c400c1c02224082c0c40180d40300d03410007456000b03011007038000231004419400706000c0403078842d11a01c06040c16601a2080c0706003140c2140c00544041c6c5a00039400b082e0f0502e80d47c1c01507458101002e01d0700000000500b4584030a801444c02452003480d1020a00328000200398090100e00e0700141100c20440340c0400281c2e9481144415911607441264003580080c131040015182c450041701080702d0a04100c01c2044003940001c3c1802d810105030f6030720103c00300900090982c184169070b8400c50a09000d03d01c4d04103140000c000803640070107241000060400111100d204600740c44402c1c51030402070128104489103000c50300c10458246012610303142d13407075076250b201e8007800b4011034005075403502d55210350300d049000e9441595178a84500c40c248001074602100d1103018001c0c50698050103c1d96410300025007a02d501a1141d8402c0d809000103014003a0036030221403046511244070382c4000200e181441c02c00c040641d40c160302240c040000600d501020101d00e0081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 388034640 1250 388033390 388033421
    0x3050403140f12030105010f0302090a0f0f0602060705120406200a0c051c0504180e0d09051806010e01030f0902120f120a0203031503010e010f200f091011060a 70
    0x410022090840f40c0070034407549000a40c90005440468041d5004043c0e032000502201e402c2915140a010520a81c1e07000c000a031070b00703030b0f006c020a43d414881c0316003210403403800b2441c0608030120b10030094000340024100300d50311001d9810003964a040c4407841120014800d8803495240790103049103142c0c45080d621800380059038400f0001d0341800380003215503600c400c2c0c246402c0c404d200080108255248c40000c0e83c030b55403801621410041e1040e40c2e9034941c3c3c1c0c503540505190510a69000708614100e007800c0c0641800b00342c2c1e03041141021258028a00002c440d400060f40402030108400065001a40c0b40981607101c2c001040c0703542c4000c8500100c07407603424141000d001c18880d540e448801600700b0b02c00326010026044000c0c002c50b000600200c3c08240c05050b85084900030003091403860344d10142e450110140c182c196007101c4001d0300d00ca003440758102800c10b09120341c01e40e1500c1a8900080c46002c0350003008005c1109800320100c0d18286020801280107013142580032000c07 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 388035890 1250 388034640 388034653
    0x41e02090a08030c1506180a06140105070312180602070b0106030c0903050d0e0a2102010e0a060e041d0303040503071e02060a0f110f0c0a090504170703050403140f 72
    0x52030b0700042150710003810f000040000d150400340000c0303240c8010f418190b03c43e088444c14403400048403040c038065200309000040c014540203502c021480700380303241414000d00703003e81d401090b00580180c0c040c40d0301140110314043d2034160580400040403000b82042d02c081107440c2800305904549050300d619840c02c01c4803203c000d1041c0d41d03410303041c44000d1084d8080e501604505202d0144880100c90140c03091803200c0d02c0b2040501030b03038201e410107091714000c22845420b40d0380c07140702b507800042e0642d901c0035190b082c40303001032484c0f400102c0c06020356107038403070030800c280c103280d40080d20210311041c0c80e00e070b0900b4034115440e940001025136035a0f80502494658803003100c131012029500621151a08403002800d0720320800c076403900014060101d07041c0d081d5050501580d074003500c1c41c2010b40549221401002003a0b05a500424109460b0000300300000d241910b450b0300d02d003c04c2c07132410340300d51062074102c409103c1e0b5000107004000d174121000440500046050b9480180d5003543c21 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 388037140 1250 388035890 388035899
    0x2030c01090803030c0f07060207060903090f141203070b07081902030609040b07020c0901080c09150303040513020910033c09030c0f0309170f070311041e02090a 71
    0x20340001e54001d142c601c2d001000815034081545008100307601e05201404d0800c1c000b602c90204a030442d86c1c064075801d440380074640c03c1661006884029004040080b1111424443e5545c05800c899035490300402403c0702080101000308141d40401d684501095040d14110000400840c1c0543e08007031a031000070200450154107000340c91096202514500055940f41c9070f10b54090400b400400075030040d4850044691100e4480380d018048820040190301d142e4010300502d076500801300390030410b8090328540f0560340401158101d41c02140c4505c10980040d54000c028414044140e900404160042d0002501600440d83e040390b209800c0c00c5601c02107060301c20100540c00000b002c002c03455134282c0054410b901121026000303240c0700d171090f48660b845003040b000070101940440da52440401c545c070603e00d0000f0700c10003241e0181c81c1c1880c429034036503503071050b50100030078800744c0c06000300301c80d00c55500002c905150f80c0b0304861880780007008103000350300c4034050502070100d1410205 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 388038390 1250 388037140 388037147
    0x30706150e0108010207051c2309031207050607050f040f06020106090605030d08010e220f1e05030403081e0d060f0b0f030112050106050d120207060801030f1b09020403030c02030c01 80
    0x90f945c541200151001030032821800f54152070200c410b50900060000302c010b0501c86404030110300c246194080e98ae5010351041500d00b403040c07441c404800c003040001c90000f43c1d01154403a00700b5114180a5141c8052008100d40d034042da42000d00303c0c007000e00d000961030764150008401c9541c3ca0008000072038a400900d07848200c841c0c0c03420007044004004120b0300d100440b5a9900c01146d000c5109c4c00e003030041c0c107404007030b00c00740301640c0710702c0c00403081070500c05d550383c024a00300b4400504c100c120300e82d41d4030b454a178000c1c0e00c0098000c000204011200c3c0010f40303205d480c202a0003a0341a5200302c5000480300400351400360341d8080e54040c9022450100e490b08441c820180740400c00d045030b20340800074100b100b003600102e50741d548828001a0a481e4200d0303140f0100e100320000d410318402081c000b898504507612000c03c10084100410226102d48004000315070004490042062446408204074a465000901c0544005800428142e010500c2d1002d180308605881c860701c00000111f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 388039640 1250 388038390 388038397
    0x150c01061401081e07020c0301020706020409050f06010903030807051324031a060705190b0114011b02091b0a05070302070503070501090512010f060e0a05090105040309050111030706150e01080102 86
    0x741c80c10040206080800d281c0204c0300c81d40845c0c24412506102e1040001c01c0c02da802000d800c070b544540100e4140842c102e0f41c081c5aa00c1160022010041c0c641540000d10465091002406002c1c3d0000400e00003071141c411245c899078040404c118180da14003660500c2c00c1d08202d001d04041104103d562418428010700040c0c12919400d04c2985400c002002580e6100d44c004403104e2083d804031809c1e140e6105540c2c00550302811f03d260080d85040320301030b214a0b40040c850304002480f10542d0b01d40880e10a03480d0556010766125036103507582030300c0d0404200e05416940300300c5404103a25074030035403000c018140c103441f9509403070a482d642c2c000c0c9551006640545800300301c0c06082840383d801c090b02e0f40ca410f10140400401c01903520791a0008840b00d6400140380100100104110200140915600502014001c008c54a040d440050100a2a0207007504001120b50b0b1500c611904009581c806500070004001144c070500034140240c03890301c079200c060080c06000081c1d40b9010b1096 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 388040890 1250 388039640 388039651
    0x81012150c110c120a17190503060a0e040f021e1305090607050a140307091d041a190e010f06060504060f0e011101020a0210060f14040506150c0106140108 68
    0x41c0751a030503e03400c01080f40082d0024841c24410702d049500400c00d0007800c9441510800e012540e52180d903004078003044240003416050040802c24041c40b5120440721a00311203440c0c040349020388a0346402c80340d522903480082e5014a13010303009500a52040310108012a040f03503444401d2806500d6070055860460b0b40f52029044640000e0106000e50000c00d8018030b0752030b028207588426a4071400399001a640c600015800a409101c1c4a405815603004180d41051180721480d10f41d0381c900c0810040c4411003200760039200401c50921509680505800954038140004a11074912600900d002d26080071441e00700b03a000110640100c00b1242945c0ea25542c200c241030800c2003d8490345002040d91b410814464144c1c01208400e00c094113034202d444e0702407e00d100850020300169482c40d046190b072031a07003020801a10f4a100c0c10400003070301c140e40128040c0c1c0c0f00c40c00030304840003441c1136100c0d4400000c0d907074581040651100080e1443c1158508a400242c40115094a81100c5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 388042140 1250 388040890 388040893
    0x10e10050d020c070f0e0403140309061b090d0305030a200a2712060b040c0f0806031908070c1208030f1306020a020c0a091a01081012150c11 62
    0xd1049046031a0b0020310500507803104580c411070341d40a5682424065a10451050941d403003800100340c0c2c46010750b072100086c41105410360418264054860101814000207803408004a2015101d44420707180849002040e40408401070306001c0d00c164411030f094000d840c038111002c2c030503039800414403103078903841e688050400014030f80c140c0d8908400400007021884d411505a02e031001c480001b400740a0120b0040198031461802800341c403090812a44114141800034003a140c2c03081242c030022602d80b5001c0e0ba40c1c1c8490021905000c0c0040301c3c81100311212000350180900e032801032811611454680766415030380e8024586143c01010300034101403040000c54803c00e0204e18081d00088580e2400301d200009640e600102d0f0b000030100303405078008030045030151a0120412005100c0440288006460359214030107200d5141e45e05814040304502044c0c3e040620001040541500c0c400340061072074500304100004109203006103c1410701250001c420f200d10310381e0420030040d00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 388043390 1250 388042140 388042147
    0xf0703030503060d173108060c0706060e0901020a08150d080d1b0806010f170a020a02120708090f0105090a09020a0314131101090f060309030e0607030e010e1005 71
    0x6040004030b02a0080680c0e0301c071010001c01210b208120003c0101c030810340c184030408040d0640c00920380703003070108407081b810f0100310410403c0c00c0401c003154854441d2016030760740c10052520b40c00a103183d400942403035030f106007000100380c4154028051228540c4400000340d0701c150400144800f1548a5030b0084940c1c1e03e0180018540300c094001c0c086445030201c0c4500540408541460040c00c8120000b603000c011b01140f543c024030300040d40505031a04230170180c1e01c06080740199601a000b884110b034002b81c0700c80c22600c00c0c48035803240d5104040301a510340c102d090290130b54005101c0b440c419980c01c035170030429601441c102c9004200160500e1032046c81c0020310002504030381900814140c56010003070400382c01000f902e00c030b0801c0c036092101210b2a070808085c0e800315815000e0500c840a1f81c140801d0404205c0c40c81190b41c140f40c0458600400d00d8122a0400fa041c01c079500308402254010426420001070780103c4000e03030300d08440d1b465041c200101003941e085c110010a8041 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 388044640 1250 388043390 388043401
    0x20405011707052110270b060f0d081902010f0902031902060d0608160905040b010e0c04050604030302030c160518060a0503030c06190b010e0609030703080d06080f0703030503 77
    0xe00e600c80e5450740803000301c4c00e2601e10040c02e5043c102c05a01d0009016580c041c072005420344495140384001d4000e44d2010040b4007590343c00509400500458403800044100c0d1103140d480000703060780c041e4401000c42d11005d00d41e003030ad0030711010f4109490141d42805003801820710070788566201d294000b002054038a501c2012040340f0102d66005a03000303407040003041d62007081406a40010a0000014900b001e00040884900c0d0610f4000840303071400c203020310010488592400381540c01d211028006a00d921140108030312555001030340010780483d00206240d001b001130540314607000192070301d01c03d0304246002c02009a00809031310241c00081400301c90510f400380b81c5e0206c4007606c4e410341d042d00e440020b0b20f56002a8491104d5074450410400d030361000d14204c540b503840c10301003408141044030000e0440d4a0b602045030090f01d000c03480f4070660341c00300100801107811008840c2d07100405d020305d40181595001d20b40641c454226200b0707613410000340003004c580d00341d03840c6030864403003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 388045890 1250 388044640 388044649
    0x8010608040309091e0e07030c3804030218090d0f0909020a0210061403251202030109021f09050604030803072105010b121521010f0908030402040501170705 69
    0x100300c200000c030641c41d0710581610514480c00c042c06e814203004040903851494041c180300541c1d0400c5500d00312429046d110300d0700003502803102c0c0e13104103a004c115510310342405500340070302c0e813010303600014940c84102005001d40a950181c540c4405803a03a101c1640c0081d00c120842c40d00c0a03000404201d030030001c0c1141580948600d0300c59106403152a0b083c0c4007a003041d2181a040125201030304840c21105140c00c000d103081070b01c0c0c4083c500d81050301c038a0030b17015040d400f4803070510340b400070300c00200031580c00798810b162aa0b4000c03c2c07280d00132070b04c00d00c10340c004420300c250001107141901c0204451030005c00741c500305d90b4482022451a50341c0d840c100d80c00c01101149841500040300f01440000f021f0040300c2c0071309140340209848a0a240780b402c403082001c0c00c50111030400c0407000903140c441d10140810b50f1100c0038030326130310301845680c00e0052258103855150780340b03007060002c10040c1d010000c500580c000c0b60144000c0e40ca4450711300803400c2203184a10640e01008013003145080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 388047140 1250 388045890 388045901
    0x102010c1d0d08120114010f0c120909020318071202131a1f030c09050108042003100e010b03060603071406070c0605030603010f060b0702010e06090a150801060804030909 75
    0x101512402c808100c03550b50034419000001c02010002c0004011312810081c8000034018030b000346010300300700341038100240072400c101c0c0000e81402c4880681134686802510400001d1103521000c5640317241569514032108428049031a003800340d0b00c4001000d00c4503525500701150010700c08080b1410164420b4010401003014070328240300d8680301c000303035942e00c151074480c44019401c01d6613070780f0f41c03400c0102100c41c40d801034070901407179040a00069a01030003055115502040c50b04000d03803014201800208181e6040f40c1c0b6104100f203001d00c00c50941c00a031400203c0390024000300000c60205602c039282120940e802d030788020303001c20440c043e101c40b05101c5000038040c14542003141d00c805000c0922030300900c001c00c500205000c3d45040900c1801c00c030b001d00e418100a428140810a040d0b4484c2d80d41c064100048420100d0741c6030307540d03030403225140c400414803030011b995495072007814421440504042003250000040090081c01820b203d80c1d0b065a80c1044030f1300f0103c2040003800d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 388048390 1250 388047140 388047197
    0x1509060a09021c14071d0102100c02070e0a1406100e0301060603090b0a0507140904110d0902120607050a030203040812010608010f0f0503061512060406020403110102010c 75
    0x5005400107414120b807005108031004000074482038911030712804159220284c0c07a01c8449403e800304858960b002018a0f68400091003540701c42e2420700040745880c40807250340c0d51141c80c0480f01180142c000641c10119102e0700a00d41c4650354091100b0100e03030111381c1c1d9011000d04400007504620300140e44407014034060a01c001c00343c051001180c00c40b04203030003610101c1c0e500c502007030501c040e10420592000d00e0740418003481c5041a8020b0904d000d4118020b6800e00c0415081410703138030340d0031400e8519030711030240e52160400c1380031f01c010f4030b011002603014541c00c100340c10f000e217408100c0500c1901c06444a40ca00058010114002c0d80014416100c011080c010020905c450059540c02840c1d5542c5508440d41032000c10301c980d0050b684a1004c040d4440c6040000d0b4030003240080d48810090382340b01d803803d80840030804440300c4c0080c0d505140200c1e0100300401110f03a0150003035034003861010440341030f210016400c03509404081c20109420009010030018942c064030b4922 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 388049640 1250 388048390 388048399
    0x218090903120f01091d0d110a0b040b07180b0702060d0b10020c01021002040f030f0f0506090d2c1509040903020307150618050912030703020a080f150906 68
    0x350341038140c0101d00c1041e07400e2059122043e0041000d080d441c02005074100d4603440c004030200c90243c0031036480000c0f0b4003032004d0090340440d80311103030028000c0141558109000d03c2080c6058030308101380e132000b166040d010454491001a1007401c1142c01f605031412045c05600c2e040070f0b03400f00444c68010074030b2031000f551200040c52050b100c05251180ca2f00e0795400514000f14510000f9081c107950b1102c80c41e00602c1404104042c0010146010407030343c0002507603041c042103050606501c0d13060130015100d1b1041c04140301500c000000c1c1d0031001e003a03958035070b040a501e24240fa001009001c420b0403a581c0c03824410000c6103042d1700d4071440c180005103c0c2d483c0512481c003180c19a03000400a41c0581c101040c03000921103803138061491038401900422445040201c4814003810800703201d60040d1740c1d0800501410010071000c1080300c1142030003501da2a200000174041c0d400030082e0000140010041180c0086d02c180b8a4010729243c003200940c07002da0300c14042c06a400a0485030700 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 388050890 1250 388049640 388049647
    0x5070c0b310b101a07021509040e06100801140f0601030b100e04050c0412030c0c030605040804080f1507030c090f090603021c0201120b010c02030d0818010218090903 73
    0x8403407105021150142c8110000801494460820b140d48442540025110201290800c408002c994100e0f01500d0781103401a0352038648a441c024540a1010495001881e1902104078803c0000302140702c1ca9400c104401c4140d01c805451f42a5500d0f2041450b04208910100d54103a03036125900c2d034404d4040c5400a010740c1c4801c0000c0010384250325000102e24185d00369031841c202401003c2d03006032240c08407407916103880c03401c52103030300e00c82c0b8003404101c03000784002e0030005c0301a4000001d503041a001c6c070160a141c1001c41d0342d40d1091064182900c52000100446d04011401490100500384c1401f160382d00c007501a000703829111035503401c004000d440410014402c0200401503d41d010000500504501c103000c03025889054100140d070020b510703d00140c1c1e0040c8a1144202c3c070340000300b1500e1f02080140c038017046c000da0095050042c035a80e114130950100025101d4005045074034544042c100e02c06d400c13440754410303154086041c10785d030042504000f6001e580041c40340b01200e24 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 388052140 1250 388050890 388050961
    0x7030f180b0a020c0a0f060c020607050106030503030f070f0e09061203030115260c07020a0e04050d030510050d0204110f040f0302040b01050405090a15080d020a050105070c0b 77
    0xc0302100c0750000407511070049207400405504003c0010740b81801e9a881e8246410800106a140d07060b01c203c0d820001822103c1c0d0031911020290341a65903c04002d008042c0ca9140c05074603504200c40c95840d06240b100010403141c4103800031440c402c031a0300c1d032a4105981c003041c00454440100142d800c51120780c104913071454100002c60080072001100c9100c03494000c4024000f83c3c148400d01143d08401e1140806101c0390756455801c14140000c1030b50711110f0713102158107107034194406100c2241c214100004d010000c2900d501c03201c0d00b0b5804222503078400114200317125950090f0f54101c00301402020060815510690328103440503441810802d0b031800c8074802e91302a400c45448039421035010011401c0500907001024000d0901c00c0c01c090030400480c100703541c0204a1100c40303403a0b945028110b6a070000320005840c0c141c0035903200120084002c2e544040030b580c11104c5620302000900907900c07403000c140140f540100c0903192507c56036401d001250958855442c04000f4441048 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 388053390 1250 388052140 388052177
    0xe0627030d08090709110d02031009060b180603090a060b210a03030f0b100309110301110414040911010809070503060a06061b020f1509090f01030b13050307030f 71
    0xd196421030741c2da0034400e141c070080300b03030a0120319032104100b181405450280742c0c2503003090b0b5a102d0008040140c896455100c421107803000703548030041d0030f45005408504020381800505070602c01002c05450445a481841502e2008441c0b04401d50050a0368100007040c6807c1091500c00040050b0390b03e841c0d404c40c1d10b40e803108e404008043c95002101c01400c050b0180142c0d000b085040c0000c1003200102004180801e207202002002c1540d2141c000040000e80c41c8045e20810001e4001c00025260000c80c401c240c0c41400b42ca02c4030040303104071040f18645405484003150b407004070300e03908099540040d40e208074050b060780300314001d105002c05c6585082007424441c8000e0b10001c61003918258015080780801c03401103100000f0149914056160490b0f0f050f2054000c0d100e88898102005884015000b5920800d07800f4650900b405138210b105000141079a00585121000c0d40307480111030300c4400c4010008140760028480f9801082c0200c2440840029601349520400c00104451 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 388054640 1250 388053390 388053403
    0x118051903030617150a18170c25090506030307061805030d02031005030625090b03040807031b0c090c050c010f1b090803120612070906050f010e062703 67
    0x10906038420400d00174820042454180c0201e004da008112504101000d00210340c540f9201408072108035110004c0b90b04403134100c8090351240c405031000d0380c0750640f441007012000b00c0c810030000e0540d2008148600c0500c00c0d41d0182000600031460118140e89800241050109090700200620b8103000851000c2c802040d8280c403910700107a42e072515590416044900f5086240280e000b8000c01044070000c003d038072520000c1609003c44d0074000d9004a6038101c69400005410001006200400003400c0207010743c24481d80342c17841c01010300c0c0b17090a004400d41001801002e0010000c00448869502c8402e02d56850701e01940743c225040301c400d09544482c45100c403040d50321030314001040500002509450041d24042480500d0813018666070300403d68501d91015a0320085a0350360303600064060034a4480d025241410741d9101084014900381c42540c1c021910503503443c40350740c411000c5aa034650018107041c10240d41601c100c1882c00f6402454450700086200481c45607400c000c031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 388055890 1250 388054640 388054679
    0x150c070b0c0322231c090810181103030d020a110601050603060325050a0609060f080c04060507051e031e030c040509040f200301180519030306 63
    0xaa65079040640f014a015490f040a0b0001540703910121400124407504031281950b49219803100150340d0040b11341005d0b89881000d40c0c0d44200110700310201e03009036000080712a2a0306a403503510f07010b0392140c240c40c031400c0030b0303030400c00e0aa13240703400216104188200c08201404403804c020420101004a07030112600c0c1c0b01080c03516040c1180140e04010b071f1809040241c0f070702c90860030480b0102307950708801003c060042020381d010f0300c03201240c8244100146030042400c54a581d07a00c401a02d500d4941c01a4000541041c01e40b40c05280940c4800d8080c030941c90f1550f03d002c1c5020000c0307407640c01075903084545005030200100c90920034294529880b1031315015641c1c0c0d400a400c03c01c601c1a111118a2610b4418010002c456000b0307001d80d070460320192840540345d035651400d603608404a0a00500203100d61880c940000403404a07000e40e8201074000304524046c030481c021004c030b09100002c0c00d6030310451004100c20101000304401d14401c6c20013003111500e815240c4a61070310540c4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 388057140 1250 388055890 388055911
    0xc050a1203050610020d0f03020f1306180801060f05012105090705040608070e1621060302010e090f0a0c0201090501110d0c090e040b1504090b04050f010e150c070b 72
    0x10700c000d038a04190044440340050005010300c0081301d1000e0011002180100c0c20b050b404605149104ac0c41d1045443c0760500140b01c1c0d036040c0d2500005000a02010059000f40105040201c0e240790148160003e40b00354059034800e8078039000c0111074840146046448207250364042c0700203208d442c002c00340a4a02c800240002a0405080c0700888040d81e11020b0f8590011108204408007000c0c066000803c0d412502000f50407820160b410260400f0140341c01c100040102c09200529401002034038400d81e600e802d055456001c0041c05034003503409041e201c2c8450040f91405140d5408913514002c42e000208882d0060b8031654211205e4142e9100400c3c000150490110903603c1151a83d03035550030004e00c200d00b0100101e412290050004010501c1940840c5203180d5071071032034140130320080c0140b2205004e0b1401620784402070b50120761503c5001c68001a0030810300a229220300240002c22001504070301c181028080074010000103c4200044004500b003a0610351043c0b04152 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 388058390 1250 388057140 388057151
    0x1150504080d200d2708030403080c0613021c03021204030b1504180303020d15090219020f0a020904021c1419150504020a0f1202130b100c050a1203 65
    0x11500d8a41103e4052200720b07009540c48110361604003040e0b0413400884481003d0780c290701241103807081c50b2504640558480800c00104000001c4010090155041d0076034140f07441d142c0c19502c00201c0140001e601c0984038159450f0a4851618070040600074070464034101030821507030b0300e180e005401c10340e50805400204a00303a11940c000c49071f5208140c500304450401441003402104000800400700344e00090140406140398000d03080b020603910404070165942c00b07294000b540004241d00003000d01c5213017600e2850001c82d5400440710280c1c06001d003c0c41c070364204040814000e204a034080080302142d1032040c89421078044c000e10440710000100c010240240c908401c00c6801307020710300e442d028180051407010700310440f0120184042071607220340c40007418010301d0390800d80460103070410004407038007400708080e05c890080c1d600d008a01125201102a5140c0000540c0c0000400c00a4441540301e00344144546024400350351000103a03950380540e81160741d07542000207880d00d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 388059640 1250 388058390 388058417
    0x7020a0605100b0a080411100903030305060a18020d060b0c010608210403080c0a020d0b01050414090c06030403020f060405061603020a1e0c02031c080f0f01150504080d 74
    0x24850660003510303440d12920003e141041c000c3c0301c0c0c4943e012001c1080841404101040844400d81c9a41c280040070909400001e820041110f08030f4403060700061b0030400410f41c0ca0500082e150241c507108018a240394040c004a0000307544200001e1000c0341c0d40740070000c1d409000501520314a042500040340c0c00345420304603454440b40340260601c0040b00702c50a49000700d8082154112540078000d161501d00e94203c0608140c400e50000e034200d2000c0203c54200a040244a0b05807030013110100807040303841030511880030089600d40391590220703514403110b1034000090341c0e00c24401c0c8103d58000154030307850390038410160f0701250294401c01c240041800b07c0322a0785545880340c5421400c1ca0344403034000700700012b07814030410001202c45100c05071500c079202000d8100d80260840d100e50352401019407003c3c103910b403681c001a6085000c0f9407074030401200c141c01515941c0301e10311540d08002e4100100d003030710040c0c2e1051201c1040001644501480401040042c540383c580c5001c056 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 388060890 1250 388059640 388059653
    0x3060207060509151614070c0f1211090c210103021309260c0304080f010605030f1209040914010506011202130e0a02070c12050d0207060c110a03020907020a 69
    0x1e00b960300300b074000130b10400740c10042030211507214001e6030300003074000c2c1105400c2c0c0741c11180c409100810301c00010b084003440707030902001e41200e8081c2003000110f9a140803030303103075001384d00e80042c20f130385681d2040c070500d00d8040d208a401901c000701c41c91400011110703d20b00410400c08208487d9146c600420075482c1105c0d4070110100c004c1424004484659229034401102e0044201075040403070341d100802d1440d1b0191349100720400c0890380d40e941c56170180d542d596143e10303425000c0d40c00d000d0701244500300840c11811214001000740201101213000086030340051a040fa04640e80d401c9100205005a1200000c005200300021303403803c000c0001451208002a12a519030040140e940700207109070f1b041d82113501c2100310340f85989070746c030b52413029118003a00601000090140400c40c1e00e25a06100c1550f07229030111250910030764002e83c0c85150910408003c5030400c041c0d800400d0300c0c44146100c40c90024400b810640d1281c1c0080d0302a202039443c4001a40a6058441007024 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 388062140 1250 388060890 388060901
    0xc0506100b030c0a09081b041109030d0531031203110d090602090307090b1c030f0f021e030310050a03080a180911070b071b03050c0309030102040306020706 69
    0x10425004906800d01812010328400605880303c000800182d182e0020b1148a403000030b801c0c0760054614501001c0f40c0105039001210750b031071069261800e100c1c445100a0222a06c41034060040c0c8640710b61440300750340e0b681040544000e042106840010302d000514410343d0110101800303240c0150460901c2d40080c8164402c0c10185031400751000e8141c0e01d1203040d100c54402451021a80406515021020780250380440c0e406d40f06000c00031800d2039040c0c10200003203105482020081c6c15004400760a01303149070025010a0300720048400c058171480c4203429510160044540131820300d0b9801000102000d20f82500d500b010040c0f1114a8401e06004000c1c08110f803111001c500755180c046a45c41214610010302445031300c2028aa2120b01405000300300c2c0038410080803013040c3c02500181d01a0001301c03206041540002d50071406401080c0e0080b0724271201d0b044014560f6010786150340030310031011291000303110400d21550240010400f0758811100036032601200e2a01c0310070743c1c6 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 388063390 1250 388062140 388062151
    0x2c0406150b070c1d070c0803090a0c0311040b01020d09142106100f0602101503081204030e0405072f030d15050a0303081504090b07050a020d08070f052101060c0506 72
    0xf00d010600800759440146c180c05542c004407036035075075210740170100d15006450310002e040000c4604008103000701000c401c20202c0d0103480a0006c141240012610340a150303c0d001c0100b209003038103000d4165000d425500d03508002d00b0441203c90520349240c000e10350400c194a407a03000d2030801c40c2000890980d0002024110703081c8010500740750002e034540c0d0005556251883d960100c00552f0b04140d840714000310f0b080170403d541c5100302150714404020403601a00030130f010f440300795503500306485240d00ca1482941d038001a400502d4a907024801d5424001b101c00401121042c61141c044c001080440210b4400086151032548146005a1942d00c140d05c0790412940800c0441c0d0407079841640540342c03003003c4407440c0e681d00008005060741d5a015001c1b02c610400c0000440d0040e00803c04c0c02842c1c0c08803900008038100850703004000b1115200010141c28054400038003600141900728120120103a1641901d0203801402d1070981c8890000798141c81190b042c01b2081c0030301030704003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 388064640 1250 388063390 388063439
    0x23100e01030f050a1a070f18061103250605071416020f060d0902010e1e09040f151409070b0405010507030e030105090a0209010e0702070527010603062c0406150b070c 73
    0x61a01c08d14448403106204c0c00e414072641d40400c000d045030600441702800c00349611081380040014014601c413141c3c3c00201c400620f00404a54094058030b0024840c0300c0c0c0c070840034074110643c545c040720000321400484e00000c40c01e002804603610315001c2c0802040500740021480c000f800014002c03110610076034001e030b4181d24072540b182c801211444c4082c4003a41c0081e0300361590b00d4403c00000784098042c140040345038006500b140030b60010700920b00a84800c962030b449408086440d10024450102c2c83c0e40104820030140d4029000b80100782d000781003602d000c868041c080380c00d452046a4450701c50300000c0c4000301314a000001d80340580032111214100345004400695600003c1c050980300c1c00c021441c540024021141c0d45100350144071403190031b940d4031500a03018228074010905100c0e06401e50803038061000c2c2840d2840f560304085c00310140c070b494030782400510442c0c80d40f40216061800210f40c3c848040c1c02449558820300c1c80d201a10b150284840981c1800c0c06480301d1b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 388065890 1250 388064640 388064657
    0xd0c02101a10031104152c1002011401090f06050909010204050418030905011209051c020f030702150904110408030a0807080405060a110c0123100e01030f050a1a070f 73
    0xb072603a00e5040d00c050300d01c4840c00420001422a040d031f0030203440d01200c2c0760080e09103071608040e40702400741c3c0700c10f5a058403c2d11405e601c050b4103900b6200301500c2580482c143c0d100404c00102c080d0881c407208900c0a00000c1c1c1c0c10f8844000c20840d10048031682426900000d041226061a01c03905a4440c80d01003030010b220300569004048403200d110f814104084180548154052a413040d500c140e40b01d821100c1c00b43c80c081a01b40300f9180f88846e44094024a07115400c01000130081701c145507401081d0311010804440c05c02c0e02c54110000554009545032a0105410907d07002040074103440c0c0025a01c907414804000e1104000034045410071141c1014080040c400050681e08818402d82c00b1610766680356140d1218003916401200c2c41d82405115251144e041100340385500300c07007072900242d984000300580301c41418401e150910010b60700410100c0c100b0304040303042521400a94110111907210714155100400b0754122010482c0140481d4035000992449400706c2410100013 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 388067140 1250 388065890 388065911
    0x2070c05041e020304020114070f02010206102108160503031807050a05060702131a04050c1305151606051f081c020705030a0b0f1003080d0c02101a1003 67
    0x450039500e0b40b501c031076a500440494216030140408044510210704038a84800241c1002c00c0586e4601c10141d005d0f003e0302e004910f01d023520f45012029580c01080c104450782405d015904541d174403090035904440240845203411003258000b40d5400d0142e0021500c034200345a500a525500a01420030341c0c1c400c4000300036a07145c898044080b03440854115860f8100c900106d8030748440748c3c6e02220080e14107005000d20306048914008180000e030707403c101e00e81c1c401d20ba15140c1d210340900100100c030880001c100c0c501c0c100455003440030407010050b0500a280d200e556041358508012140305444104015084076020004400a5003010a80889503c0c0c01841c94607200041c010076001d04003a4030050380c0c1e6008110b00d5004220140c01c0b200c02c2000350030150700030312081e9851411002524041031010b030340b074003621098030340020010740360010040001000707009146542041d401040c0f240c03010305c0c0c0980f04441994101e0000880d100e540d0780200034034902134918031700074035162a10700c07071 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 388068390 1250 388067140 388067171
    0x201060f0909080909070207090e06040b150a0902040f1401051608030c09060c060405010c0f0207090515030109030906030e0102130b1e070303270f06110d020a020102070c0504 77
    0x40032030706841400640350301c007810468001c1c41000d8100c2d0300301078140144159250b0010f12642240c00b0030303200700201001c0d414030b552074003000d9070040c101e0844d1101040d403900c043c28200c0300c1c010300100808a003955645219007130782c00a610441170240003003800c0144005001c1220a920b0007480d0462800004190359640356000203000b800d030010100016400410180c11140f40c900028411602c441903009480c3d82c0c0d803001c4a0443e115402e100180e40d1840c061060b419481c1201d40181020908200300040207000060401500c0c822103088001c00307803004e21036242d0b500e0081e0355000002e0f08141005e02070b1110001217110603881040400c00c4030600411003019640f00e05807255440c241240021003102c00f10b40310001c580c200044c0c41c402c054040d070001d40e440c074803040340d2551418500301c0800414120f1401402c0748201c415500001a6941d200f089080285100c03c0c1c200210005442d0403030300003141b02d00c0944c0d070006008040c00059440d860092000b02c0782407110490a410f042c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 388069640 1250 388068390 388068419
    0x601050c072705091f060f0b0913020f19030f0e0a0212060712181a1005031b060c0114070903050601120203030a12140a02040e07171807080f03030115020106 69
    0x5550b52040c001655402c02a04e4001c0001803412010340c104242d180c040c0c1c08035070380c00b62780443c0c81103207104000c000040c014020b07202d4495081801c281003d200700b404004000080c1d10036010180d60784051a54280d40b8400c03041290710002c003c0244984c944140800440000d42d04002d40c1d201004101c0d0f0b1070b5104021036904210030f0000300f060754444803004d00c801c180450003090072484000400c0b20061300d1034a540b1902c21407030240d200030754035014035480c0d001500d42c4460441c03248119a8230303814040014103445d105c2000000350b100540c841d9400718030054400f0f82c0043d05c1d040042081c01030803c116070140202070184a0ba2b038a042c0c1c006a92032103034000d48024030030705800c0d03070444000c280e200040e00d041030540b0740000d24000c14000000d41c07085c081c02582d504a013002c6184240300d42008000c0d0242d01c1001c030f00d0b0b41c8608074443e01c841d642c000d4400c000c0c070450300c001c14603500911282e80d003801260000e5440f541016148640c40801000410071a85821030400108595803280c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 388070890 1250 388069640 388069663
    0xe0f0405071802070803010b0a140426030c0703030e040605030105090d082a091002010c1d280305070b070312020904290a1e0306050601050c07270509 66
    0x802580c800860602e0103401402000b41040001100015240301c44000820310004540e0340d950344140040f403041410f01a0f80110211450100c1c034140491b191240220403003141c0e0b00032a030401000c80456460081150011000200e41d1000301c0720f581024061000a0441140203214620f000c81510703a0300c80c89140b003c010000260003241642d409049036244038520781404845003c54144c003e61580d00c0050194003d050b04215020f01300c1c07041c40b40349080e034a580c0d143c52520140c116030112480720b00d50550303849161510154000c054a00c025100240050410f10301c0070325500b89507080c04010383c46a500d0981c108030000010303500c0003101180310b00d424001600c070345500010500401c4689a420724003c004145940c0005400a07040800d450840e500140a600c80100304008007103503150070f8464011000500c000303070194028550104061504504007c40d600741c1e549010034980c050340d00d144c52011800380d0b074840e4941c41401280b0445090045090103017040f5078600742c5104 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 388072140 1250 388070890 388070909
    0xc04020703030204030c0602060709060318120203091e1002030306060d020c120a120b101205130c0f0303020d02120306040c1106070302090111160b0307030b090403090e0f040507 78
    0x340182050300075815540610f8210a082005684404c0e02955820040d540103001c104004d40000300c0750310138081c04403840c4146a07411103034051580c600c94058040388408041d40418011180d0b61f444801034900c0e4129030040748d0132001825005d000a1800191075581150401c008008071910f4010849105a420b44030040c0c2c0d0f2008070880900307040302003818160b000c60026404100d0f56106100c84400c400303109040180e1704081007040b580984141c01140032074088803110440486c640d00c81540701d105419400007840701507588034a10706040d04140e113500c200e007105100b45981081424442140c6000070700c000202c142410a03940002000c2900c195190700d205407196120745aa6081041d50500b01c031000d080c2030300c025020350030051a040c00140c403241c405d01144000030704140300341083d60401b0380590405800703d80d2503100600040038140c840b480096251181001640b0031030196944000b0740c4e00302003070003510800c02380c549100080442d0502010a10201d092002c5031400034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 388073390 1250 388072140 388072147
    0x608030909040c090f020306030c09010302100f05130801021b0304050d0b06040b040c12150e04060b06071b03020a06182606040b16050f030a0c202d0c0402 68
    0x50482d03124420f81c0c00c1003010342d05000c14a4144c40a40e0040c5002e108110305903452039150341e06108140344d091201030f521049003400f10300c80c82e025402043d0842014509680f41c0032004d550084038107061307405081182c1d03000448520f1069010406c071070a0b411781015600d001d2030300e0001000c40d411900d025050321141000310f500c90f40c903a07101c00c1008801500074014610b4400c806408107100c004103004090a080d0004000c60310000c5180559210a03107030a055200e503120314004019280c02c3c0c41e00160208881400300399550490242281d581002c07415040c00c41c8140100b80016074005014000c4401440d02c0d03170b1110320802c4099800c8496041080c00c40108400740c00070f00c29404c1e0705a40074600610091001c1c0340b9005205003452802c4080d2002c81440480711071140e0032036803a6504050001c80c60340c0360140c1151086c0007107464030545141c903011a803462125402e00d40700b00e40d4040749081196a0142c0721083c1c003042c400300c1040340d0a0502c0141610f8295000d4203d21669001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 388074640 1250 388073390 388073393
    0x605010b040b0d0b1f0305060f0a05030604080313020d0b01031b03080712021207060b1804152d02030603010f0c120207020406090c1101050c040312050d090803091609060803090904 79
    0x19102c2a980100c10130916017003000080042c0040c881950010b0080040e68200411800e20394440d6003201c101030000c0ca00d941e56a26000401c3d0000b4010340c0d800f002c1c50b490300300541c2e03038504513007195400b5182495240d451440d0419108096200c0464000038915007000030800901c240c0740c0054110b104880740c1da401e904101c0c140030001038045c80d14000410010240b10141e80321458002040e18506003c104025105d4a50101100d0081040c101640940c0c15000c3e039401554820310f00e01d100f00c40740c4103e0125030102d040880b22f000d0b402c60b0302100704203562600340102203034451000030030001c00070104001002810111581c00007250000340d400d08640b51540208024030181c03104101010141000030050503c26549800d10f608010108003480c24220484046a1b4000310350030032082e070362400795065003109050307502990352100340b02e01150703160300290310070310004024050004240b06450a00c070407540004108500d04181842164800012158040c03c10ad42008040d6210b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 388075890 1250 388074640 388074649
    0xd020f03090106092319151404150315020904020a0c030201180507060e0319030207081209060304030c0f020d0c080f060906151f0e0411030403020703110105130f030605010b040b0d0b 80
    0x103a1b101d5109071030b21290a0f0f0200f030084180342038800030704200d5954248541001f007600c1003420504400828000100000351044c1280010320401e03c0c400b6040880600001d01207800c00c0620b800412a608128010583d0a118000d22440a0a00404185e40036100c0d260790705c265000e0743d4140100b950707440516580801609030400b8803801c3c880c060015074a0002c0d10346d0000d21841245110700c400301014444090140c54190070050441400c40d50303261000c5400200c02101074840600c2c485000c0c01513281c143e02021054051010340450600d40b00e046494038141d14404c040a42204003441000740000c0345c07094001d41c80301c10020f40b4070710030400200c0c080350300000e00300115242d11028a08640122184804140845040003101011980c2c05d20741d00c4201c80003001a0002c0800740009140c01c003004280070300c18540345040640101c00c1385410030a035007000f900e6500c5294100208911805240d01401c85200d4517400c0910388610300902c4d01441850115180c0c5840c20701d01d180c0c68 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 388077140 1250 388075890 388075921
    0x80403110f0609070e060a0b0a050702061b012c15090c0310060906090b0607150e030a021e0a020d1106120c03070e01091404020f0d020f030901060923 66
    0x129106641207400c00710b03d103c0d590034183c8910244c80480f440069900d14060080004903841c1c20282450080c040004544651280c0e0b0226440b520900101c4102007a6205045208042400005580a0408074032455803c803820501141007501454a00e18002107080d810380704c0c40c098010040c0d100d041040307040003c4800f03119010b10440404903440b1050b80c00c41c2d0200c0d0f4002404100351615010303107905a5180c0030406401c1f4034204100c5000458114101c0c0700017182d0800040c51003620411036041d030380005060401644200e41c00c0c00348000001c1107a1035400034400600c04490b6581c00326010801e82d9a0142c0003030b58100c0b81c0c00141e201c003422996000340600c02d00260b860100c6000c0d2079a002a10840005200021080d10b254012a03d043c2942c50900104514404100800010750710856010490907001d004142d843d81e52400a41000442051090746071326100c50f43c5030031200c5030360002e0305180c14140c2901d10314500c01695290201000c80c11440c558402040100750700c2c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 388078390 1250 388077140 388077163
    0x609060b0d0f030f05030408071218090c020118023a0b070e031204050f0f030109030221040f121406040503030a0e010e062d130c1508040311 62
    0x2030300c8420250400503001c0001640b0303403280d100c0e0300c00c1405628045806000c102d0700101281420880724010582c0c0c8000d50030b07084801c0c44c010a10a64510a510704111594022014103444502071900f294081c050071540b07861404200743d900c0f03142d800003a0a00c01c0101099100144030b6040020b024604060400c0e80001441200c20f0b17291034607040e480340074110741c030303078002000e440047c00079141c0030685030286461010070070305003410041041407040e900c2c0d1116511007400310709406207880030300550300e48900a8016040318000e65550351341500e10320544c2d07140118104020701c24580c031980c210007520041c6001d501c5450703440c5444c9452409080d802c1e14544580410070042040020056100f458800f100303000c041480081c05099a041280c05592a0001c400003010030b800640c0e48040c00b60240e100c100b0034001c0c00007042200e0300c01d172a05440e500324075140c80d06200c18000301200070449404100c00480540030001c0001101910050802c81801102c0360150400c021321038408 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 388079640 1250 388078390 388078399
    0x618090a0b1306050a020c0d03050c040302090903030106091203023309060411010905090411220b040c05120406111e0910030c14030705270102060108010c0c0609060b 73
    0x2802c040c0d0300c04a91440142c0100c2d100c0707007040000f070041d0b0514003d480b81c0b0041c0c28020142110742c8003054001d041c0081c40041109000e001c00030142e9a41c801c8140a00b5608001d95900e50414a008001003a25008007000c607581c1c402e03a0700000e43c0002d0320300220607405100300a001c6400703d1442200349c000381c1c50802c19100c0090003642600864094010352003088034102d0b01d02401c0054410f11480e224941d4400000d00001d800304021030307940851020001c1c00468400043c030705000d08001003c40b2501010b580e864030000030300300342c440c40502103624108a8200070400301805245400240010a41612034550385502d00c910420345190b00402c030300702032400d5890000c0c001103801c9011000c2c801d4000a401e180341c907020f4409e00c0c40e0001540d440596001394000c415503241d00c00740a82081040400640c10111381c4e061445100a00e1400000c0c81c92001c0e2000a103844e0701a0040003491345045003407090709030061200c0c002c40e0303441f11004c9014044c41c1464401001c200550302e821 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 388080890 1250 388079640 388079663
    0x8010e0a1104150210061203080c130f0303230405190807060210050606091c14060c0316090605220302040504110a080303040b0f040615030c08070506030618090a 71
    0xf1040c9900203900000540d50031030b40111044c26800c1d007038030028401e0550340f0714240d881e000071038032406441ba07026042d0752006d07242480003125091005140d5001c00782052443d40c0c02c0c401c042e84004410340075a1480000d41680a41c00941046880b4620881d8414034203c032100d2681ca0b05c01000340f0003410b80c0700580354001d030b03a080041c0d220300d005101d400c50716241000060700e40c40c00400f505c6410801500c5861520480c0da1100c403e2009a941900c0445114888004482040100c9403052680d5020140c4030704008183c1c1c0c0d88006409000710601140034018040c2c2e0780d0050681e1415091000c0306590401c40035020701c502a0103400c040d40240c108010002800b281740c0030310400810030b841c6404007958034010302d61139001c1580c00505c690448400704030714200c440c5007203410038054580024020b00e000400020561a51f000300c1c0d1101d0b690100700a6148240140801040d041e1221841c1d0300e051000280d41002d17100403044014021800300380d0041c820048102e40a41c040c09600a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 388082140 1250 388080890 388080899
    0x10e06180a0b030708010e0303040215040e0a0b01110109020d12230304120507030e041d031b0c030703030e060d0b030709020c0d030c0c0605040203100c03090210090608010e0a1104 79
    0x2e800c5540c40d80c0d01900c62858001034640d01441100b5000022101541c00c50301c03903900700a0000c0c183e40341100040028000071800455209006000340803141c0c0000301d90350884005001001580942c6010341d14281e0f841c8003684420740c4d2140c4035903105400d01013800e00c5030820780344654040c0c03840c0003d10940c3da80c1020824071100844c091401b96003011100c65680d9000c4506115241c80200000c02800da0852103040c40d4000d05606c041003030841c0d820b50a81c5600b6172850f044013412880540d185c2042100a41040c880c48d40d0003101a00a001e00d24290388010309a2220409224007424001404405e510401e610108400c1c500030180c40407241d85002c840041c4d080301010503410b01a0048450010780284204050b50103a521410342c04201a02c954008000041c81030740c26001d00680401c200000d40300b107001100150702c00080141250040c825400582e0841109201e0b4914007404100c2d005100541185e83c202000303240d03a0b0314100d01c0d4018103813102c005e10515501043c00702c1e = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 388083390 1250 388082140 388082161
    0x227060f0a030930080406060902030702030a030605041803050c10090c0e07030513141501170601050f1f03060515030a15051f0309020a030c05090c0909010e0618 71
    0x102c1a0302616281211481d1461504c00d1050100c00c1084106114411910800d000b600130b15809400744000003a43c1c3d035118401c0069a00840d541c0c4c0068100143c100b045da03405204d403102800c41030310200858516195810303203140d01e00c4409030901c94042401e04802d0702c01c002c50510010342e83e0701404110300e03514008159141a01070b41c0382d58840180020499846445100d10544070b080c0c145031129207589400c8c54602c40800f003070542e030240103c400d5484030740c0184a1f00900d44001c1003000d00403003001150038408107800079841000c0b1024034180560320480c001100e409000741e440c0510119030320540003808180d00207500000700d40d8410040480b042c000d1071003a84004030a0010f500310030200201c0c80120b004581d030003007420301d0340b10b00c4580c2c070558090b03032061320f0400041e006120703000200c0e03101a0340d10407a40e815003107405000c2c82c1044003d09810190b80785141d8100104400082d03c103c20501802028880b400e00044040e0340c1c1a54801d100b440c201450507036410300c0307402030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 388084640 1250 388083390 388083401
    0x121407060201020a141602062115031207020a030b0c040906080a0b1e071404050603010f0f050114180d060903080916030203071502240403080a0227060f0a03 69
    0x21012619034005c1c1c2003080c01000850b0444602d00c0c002c40065070312542004480c1e08008140c0c100ca101c001c2e101d9100214107550f46000d851404800022400b080080503d44007000700810920301082c080c440c010b031240c1c0d203640196548944003d03512317a1108908030542c022681306890317050510300c001400302c1001c203404501034040c02040509030b8905840c803080c1081c0c20000c44000c2d1203500007a11700c0344149140c2112111240c403440c0b6040d5202e0025046410a8000c100045401003007000a0911000c00000514013802d050300d03075104100c03200d81113000d400040f248108185100c0c007000d58400c1580440780340c1c1b00c42d0070091000d4505004011200413240066940301e03000300d015036a80c9000c606411254001c0081c100c550500400100030305040318400c080d0720034030040c40a0400740c0d00300301d00017400348009140c20785082d00b8010f02004029026403400380c0304002102115400c3c2644001003008a282e02d55843d0020011a0451040108000c42050041044046581d26030002d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 388085890 1250 388084640 388084657
    0x509060d09150c05180f1002100608120403030323040f051002092116060503161803020405061503011e05040b0603220606090b121612140706020102 65
    0x10b00c0225802600d030101140c4035507921001080f000e009440146940302044060b041000d041d1858130181c0c071010500101c0c00c2124500960850080c80a914400d032003420001c01010340105204040890104410b00c02ca0101034109525005002040324407010b0500a480144001c2001f42c0b8042c1401181c182d0610310403a44e03800703040219152440c640c0255405400c00334401c82008000c0d14040c0d400b50082c1d00c8042c000e008425002e19840791a080000c0184016112031b550307850061440203522146090903814001140713090200040030303407168401c0d86d605640024868840c040003600b108040140c0c410360580c00400403c1a5101c425491020008910300515881d154002c1100b0b541c1c44013203141d0000340c1400003d016290008038031902d0413a03010104a5400c6640350340c01a1511038101c100384a03103607041403103d0b0402c8003040d000b8a00610281604590443d03c0d070b008402140b081085140000c4c10034024000220207003016941c0b120211344520750780c0d01d0007a010350000d00c0e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 388087140 1250 388085890 388085903
    0x110a170703021c090504020d09050a05010b0a0f03050715050c070303020f0d031a2209260a021c03150906060206060a300b0406050103020f030a210509060d09 69
    0x43c01942e8108665124940d250a456500c1c102d414941880000d40101c0e81840100380c441c1450740126900b0f0150011642c011000424002241d0082c0205806164840e0403140522281080480d001145c07120641c0c84150b9000300455080d102100c86004004800c5814010b2030b40c0002010780000e141000c05c50500c040e00c2071042d44201c03e8044603e0f000f90002410824012000d2070b01d0545050420001513010400e09071980d07524403003c8845000045461400088400103044014042810700407200c0700004c0c03400c000454000e46400c0c002115412411440d4040255a4013030380000a28095403900c00405903503400c0003c019041510600e0302500400f000306000782050a2010300740c680c005460081c5039400c080140b0322013106e1800149440c3c1c00307441c9100148926001d5402a0300801b4089040c0d411070041000f20162501414466807200e5036500000d9001c1c000301207022101d032101d284405000340161001c0c0b240062055012200246411440295500500c0384c98041c00 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 388088390 1250 388087140 388087153
    0xb0108031201030809030703051b090a0c0c0303090215070302060f07090b0f0901031e0218010f0c0201031a101d010c02180a0905060c1e030f07110a17070302 69
    0x41200c0d180e200d180a140c0301d5058040040c008109040c000784500300003d000c55500d035a4039281c041c1030540440130407040440381c84035105146030540f038580d004002e42500300106900810302405942c40c2d540000c00b490f0701e0300c1c0a50709540d20465456103c1075046156691211140b50080d107800d4120b43c00d10100d120000031074101ca1044201c607068418609040d450448102d91140135074000e216043c0c1010303107800c101c0f0000c83d125858000c021400c07180240e180d2803190894400c0101045005040120030000c01109a0b808500d2400264080c00c0018204100020000070745940c000c1194220442c0c421000010394410700b40300340d01e0001002c1580300d000500c01144c140380d5030032001c2c0d440b60f6140706100f40f03070191401c2c1c50740000d80400000b5108059aa40c5410b103c0b08603003401c4405004625012038101e000c06001c0710094100e0315070300c1c45c0381c00b0050f80f82c02c05000e811003041141c01d1340c0c02c0450000030483c07440015001000d5000d1070007c074440499561051900710018020039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 388089640 1250 388088390 388088399
    0x102090103060e060a030311030c0712060c0f1202090a0312020d080f0c040b030901020c01090303060807050105040531020301032907020c040b04020f160c050603010e01030236040b01 80
    0x50f4591405500300a2000e00010300c1c40c0ca0888082c058031500e02d1190004011a800e03006040100400908034022080c04000080c1401021034069184d000d00b440810002621800d42c8030b00000f91a00a0060041c0c6460400001c25403c1410750402061031001d103d1002d00140c0000e020b00e200d40280c0c1c3c03182540d580c4c0149282d900d02c8161007001440310244000e210814046c8051035020000200050a02c0300340c0300320714203480141100b80c002c6981d0350824000d5480600410025040070b091841c500382c1b030400444c444075428420082841c032120030075185c80b80d140720111032200115806549070758490a0102204201c1a20b448050503d55080921020481030a81c45000581c02600310f441e10b200070310002e050708005956005608100030100c803000400502032808050005e8505a0f0051a20095940d85500f005210ba0030a1004009103420a003d00b41580d07415a055080001d6852218007a84000c401c02d540f119804084256000543c0c0c850501c598010844026985d81e00c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 388090890 1250 388089640 388089659
    0x304060b04271e300f0905060f07020604030605070e0405061c05030d060f0e071707180315020904050c0901020a0f1a07020307140c090123040e010209010306 69
    0x40501042c2414140d40c2a4021a0241030407000051401e204041114881d40e6103001c0c3c041d40c10340004080a0b900c120090340e4200351540741001009052155890503100c001034610b1005d880b41e6441140c0026107860380c1000401510416507002d001c0b44e4455403240703400005404220b8036480090f0264118000901d0140103072401004060308190410f181c400c141d9001a54600b404c1c0d03040c7c8030070001020019420301c45c0c10010500c003107450030603a0030940300c011156000b914030420840b40015000f00c03017103a45203158005080741010a400d8414903101d212041e2140d00242c03840e140d00c41180c2d048141d40d001040c0d80102154104013560b64050b0030500c0780981c20400d801070b40702e10380c1e00f0300085401b100030600c10f00070f4101d400c2c58000103100300050202118082d00581022440d582000f054403000c506c40b600300c0002e001000d45200100c2d01c01ca4051061582e5201800055480c4010081d01400d207050068414400b0503490354095010303501550010740005e1418900041701300301e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 388092140 1250 388090890 388090931
    0x80f12101d0f0c0307200d020606120d11071a190309080f0f0708071a13051f0e0723030a05190302031201060810090c08040221030304060b04 62
    0x15100c075000d002d91a440321003c0150001071a520074008215459040d40181c03014580003414074200030070061a0750310001b41084801381825002d42c14090100c5c0385990080303003400b000b02403403a11262001076a0130941c50140360398044e00350502c124840014400d01c2e80c0052213240241c140941c00504801001c80448181da800904480c4040c8000c00084d03040b000100019501c1d005c0e02c81c104103040d10b800b4582c0d4402c2c50b04403081c2c651501800f14061410740111792186010000200180741515400e031920100740300307110882607500c4610b02007809984000300082a0300100c03011551102c242c07061070942c0d2a0021443d054051081d10786160015401d00b42d40d90060240c0307202880e400200454000c2c190085003580814400c00c10780c4420f84600c60300030906a075500c0f0440c10b0a5030301d42e00740c0341107400640e260790900e1a00d00d4016084440d039a0080c0d41511503c960684000911182090318040c504140c007000080c001448100e8001031303080301c82203404206000c140000e110b004038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 388093390 1250 388092140 388092151
    0xe030703090e0601170a0509060f040c0501030c14030403110601050a120f1e12030b04020a1b0323030103170702010c06020c01140106120e0f0a080f12101d 68
    0x1c500c8a01401200104801e081c1c01c008181029100c5038180c149580d22004100d4000044940e40e004000f4288402c020154012200c4940e6041030305082d2113116440010f40a002e051503118046524558801c100d581d41e8044e80303600d116100d041510b0001c000014019911045104450000c200c40c45c040740303404103c810081201000c28119a104c0480b1003540a0643d10140c0814030202d003407240010008400e8441d29907424480c100d020058210345030015a24021403050021229103904044080c0b80c202504201094010172031408541010621080c0040c41031b405aa498040841d5405581030b41c1c0700e07219241d840d59001501d00b03a40e00840a000c3e000600b0060410081001c55001b0f00c3d0598002001003043c0140041c4000c0c0711070280d000d00b00160700c3c5011401d81500610603103002102000190028003800300409a4074202d008014014103000101c032146002d07004110380d2800c8075804441403602d09401559841040744c0319000310328250a2003041c10410f201c8aa51081 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 388094640 1250 388093390 388093397
    0x6031204050d11060403050a0305040e070504031208150a090b090c031b1809010303052101240302090d0506010806091c030902040b03010f020405041406030c062208100e030703 77
    0x1e1540f40c442c05040605181515003020b02048080041407051080b1000103000752911951180360a040268040004000ca400c020040c0410b000240d06001c41010840d9145001030031505da040e440b40959115034055540180107000004858025800030030310300b40103c0e40c48605582d4065103280921040382c24103100001c6060910003408a4400741c42c0300340048441d1000c020010020a0070300d07400f82c0094003c10004070b81000322921030311540d044003e0341c80d08a002541340140d290120410a860285a0000803a90141c007034440c1d8190707113100e400105403108451041c105162141d00a0191003990300410b80000c070b0140c0002341c90400c11001c109041c90510035401c0071001000810003c99000d030300e480c0d000c034540d03400340584d11217840c90710801681c41c0e19290400080320048400303401a0454201000350913600480c0150071007500350340c1d8641d600300c0c0d00030003160040c50800c0300042d003003d20740126200c02c00060000c03054031005003c00110307003201c0c03106030b80340160100207002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 388095890 1250 388094640 388094659
    0x6110615120f0d02060a2a0e0d02060403062004080a120519111c020c0d06060b1b0714060a030f06091d10050415050615030f0603120405 60
    0x450034070451001c8210151000d8400700d481d502c500a003044560645440141d00a10a2002c400218440c0840d803050070342940d1006442c000b800324000348124401c9040c07010510544088c0e45070010100452540208100d60f1282c0308e20b00342c801400c080341c1044099800d0254070106e200a04111019a52481c00801c1c0e401440c1c1c0d15031080e080300f41c07030007030400c1000d2021040015602040813818540c43d214442030a95000c0c009181019003440b00b901d400c0c203444c45040f62500072031045814003003542c4007151401c841c02e00c0b4014124503400721340103080c001011000201d582404061940120065589542c1d442c540c0604610b000101c41c0c0d0f110782c041044e24081802640709131102e2000050110340c0960b691105000c59000301d2800b4403205080320407064908040c4455409008442d908000600f040e0302c504148850010004255556441c0480d9450740c40d40070039540da0028a0b64190343e40381001c246c008100c81980d80502070310a080c1ca90801002d02c10075a010391f60f001e0242a031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 388097140 1250 388095890 388095931
    0x1080a0c03150e100504020720030c090a140903040b040905101e1a040e06101806050a11060c19090810090506090c1e041401090207031b0f0308040503090a030606061106 74
    0x190003409c40b46981c2c14426184041101e880e6280c0c041e100e1000401d0000d9003800380300703135801100c100400c0c641c25a00104000d0010b001354000390340a43d905421700080a40c0c0702c00e0380d9800005650000f9914045040c0c13003410f0550032400f0070080d03814940c001d40c20310703001d1880364803030780034074020780700740d41c16503000038035581001c1c402c1d00c0d95100c1ca032501e12084061007070407065070842e40e00320000194000414040031078000111601d0350302101c00030b0401d45000e5100c4086400303504150549000e004481074100c52041c00254054020324041d6820300c203040300401d008010700c41d0112464001c4000080f040d1001290070407040304003600509200340107090001ca040c1019041300d83c001c1d501c0280500060803090351a01030992601e006903115500d040140600b04004c2c0d01d02046009407202400041c0c060000125440d490f00301000b564659181107811401071030704d034541081001c180042070140d00e4100c0b10440c1c40351f880c1c08c0c0c2c220b070341d03002110f44075103085a0105c2501014048042c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 388098390 1250 388097140 388097183
    0xa09200306060d11030a11070b04080307020f0304090b04230c0d111b0c0915130e0d0906110a0b011a091f030c09030201080a0c03150e1005040207 64
    0x581c061030050005140603641c00860b011546040071109207070342c0100402000743d00507c07454010741c0c2c07a082c183d0f0404800d82d49440e803c0c20001d00050040700044045070801d4000c0000b0850b0f0700040d401d80761100d44440c8044001c0660a03104c51055041140300c01e1050044101c09552000010030303c586176852030014807080e44a003098107481584d480e01003a20400c080003426121030000200c01e80104404e400a02d040050001248129100300c107101441c000201c0090019105031145c409900e11030b140c00740104006100a06a80035540702800403c0d444500c5500391781c52901c4130a40da001c1ca9440341e9540410101c020080c504840040c4010000b014418141c030381859405d40c0740c0244400441d010b00e100d081807680094007403c40403101030301801a85040301d182d10709010315600c0d50b000240f4041c0d01600501c4000da540705001289072103a0004090742c1c2c2d0700410491030076603861440081203411100302e008100a0500814186424001c41c1c4c1d800d41c010051864140604280d80d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 388099640 1250 388098390 388098397
    0x306060a080d0807050c01020c15092d21130b04050f0607060b04020f04090b0105030705070b091c0c03030510060c08030a0f060e070e030f07140d0615050a0920 70
    0x343c4c1446414080429a20002d00041218012840107807402c8003070b0910a400314a4060440d0816802c1564042d01c0e45140140c0c54040b04043d240b0114102e4001010b0390801d070380300c0d030261441c0124000ca58445c8000c100109444140040c080004550f1041004040d0140c1d0003016480710031240c003030196180c0180500340040c0078200c00039018400100290499100c00702d503580c502d0380440e0401418026120703564a4a0003030034954518944600020500d106660b0005c100019035004250004000c11201540414040c40d41810111036400645580340c88601100064106000138013400c00d0101a84100c840540350f85102101c3e43d41d036121140c000414840300e0607901c80021401070b80600610f8010030300e005611965042c44a4014071280518505034001e501040b02c491034a8400602e441c21241000b426003000c020140024452a4159101900071410518180c250b2303000e80b03400a040b108102c82c16401c02c1d503911012030654440200c22800310100000c031520514140300103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 388100890 1250 388099640 388099651
    0xe091306021b0c0a0902040b0702150d0e03031005010309020a030308220c0f06020610260303090c010206060102060f0705031506070308090c01052a0a0b0103060b0306060a080d08 78
    0x1d030410900b2120103181c020b81501c510215801101c0c0e000407418804005000b80002c51010f5103001e041201a080e98866180003d0241000d002130020500c0c50300161000c050b816031040c40514540f440f0315a69410640c0e00c074a903c01880c80028840d8081e02c1201c0b2100da000c1d1100f07200900d103440c19500301100070700f803115012401a01411014407041c4c5020b41c14030400724402564140408074a040d209900040199446402403141800c8103140c020100d4001c424001502c3e20800e490705007030041d0181d80c80c1c251101000b4031450103802710f200c2014400aa0172034509542d10b200481c0d58440139142803c2030055080418001d600c200000d40e844120b8482c0491601c0e0043c0100c3d01542c0022001d8000a013071a050013407003441403112000d42c09003480c1007802c0100c24101b4040c04804140c00e000740307004060345501400014403d562000c0e410080300030b130a40c0d41e4100724003e8945003044a1081c0101d500160701e5103001030b4400151000c01c001042c001809210036505010080d01 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 388102140 1250 388100890 388100903
    0x30f010513141b130f030312111615060f030623070c02040b0604090221060307060e0a03060608060702060c07030e04090c0302030105010830030c160807030509100e0913 74
    0x5070b201c000462122400616800080003421071850400030108a8200700b1035800c0d50414046e5401180d644043d1805400300c02c0d40d81c98ac191061910074030820100040d400014206071001030759442c83c1545104503401000240a44003001100f5100350704030703144005100c0f40c1280400c40c4948a901100c003200c0c4058000105c08604900003031403500603510106c0340c40d40002c1c1038008030f40c5c000d07101010400400e0340500700b03040c0300c000a030300d0340304038092882046819510340b4225540c0c0c0075210003c50700a5004c01001d6120034107192030300c00449100015104a8011840418503901214402601035980c118010041c0c02080098600002c050355508000c840c0032000d40d40030b200c3c190091015200a20a2400b0b00030444405885040006a004d100c85d0050000c0b0306100100c0b54015031848202c2e07030381c6440c540c40c6040e02c003001002800124012400b40100354012009011440c021104454004240d036012585900c520a42c65000220140030448105036800c4d0401024458a03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 388103390 1250 388102140 388102147
    0xf030106050c03040b04120614041728030605120303060108010302040b040f0f05060a0e0f0703020a050705010c050901170405070905091009050607080f100b0915030f010513141b 78
    0xc07118842d00b003500b200301041e000107d500100413040c0701e14030500a0448c0310301d14900c0c00b07848284035210034045d00c26850394001182046204c01c902055281d611441601d03400214211000b0010102c0b8069540295891400c144002c80000180e034403170f420503511a45280c0c00c41d820310010f45401504243c00ca40c460040c080b114040e03014001040b00084400241c5151200130410595103d91085501f44194000e000c00c10b42c0642206501c44094140503a84248400e005c03640c80c8a8000302510951900070700c441015408401400d01da10242d0703441c107640b07915006000c0307a2041a00c0040c00c03548181d1040150030b43c943c02c13080d80101c2060940d4222011420f0050960f2203c1c0ca044800f40c00c501c04200107290000c072665000710328001001c00714500503603428100c00c400e0040003403041c0c000ca66200385560300c00c241c00c1c440c0d45500b00c503505d0381403051000c49051030038011644540c401070f215034054203241c0f00743d19000d11806043c2045848074203400c0a038805540023000c8141080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 388104640 1250 388103390 388103399
    0x620030a120216030806090601050a08060613030f0f03030b04020301140f1908010905060a0b090f090a021809101b1206080307050a060b0324060316121401020f030106050c0304 77
    0x640c88240828045c3d11040e4862600c00700700070010074010700300c0d07048c0401800141c14466000e92903d070300c00c1e41500c0d029910701c0180c045400810403984010004c040c0300c510b400c10449002c000f0000c50707110340c40a100c0c58100904100980c0003d0090b44a000d031034003510103142c940401c1e4240c90f40405407080c84c1035240f50840500381c1c4059044107036507a445080441c00c0003810030050703031b020340e000302e041041802e02e90006284143c094000400000d0540c049040030740280a48110030f0380c01003401d03e284510240024601030220b5100c00e5602035020b1300c0c9100849401800e0084e810b261049c0d82905e18804240c2c2e1a00200c40c0040340d1554036500400c0c04031003000144a1207014030010908050a45442c0058038030107604a0f0003500055840c00400001d460328014141c801101c00c0d00c6030b500e4201080ca010b030012903800c50b58004510008a02030000f0a000b000d600070f1504015002c1c400044070b00b1b0380301c1c2c0e60002c54007110400c0100309480c0310b20f0203442c140d0040c42c182c91500d640e8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 388105890 1250 388104640 388104667
    0x21507120915060b04030201020c0f0a03080d11070605060916080a110c030d050906130816020409062f0f090d0507080f1b0907080c160203160620030a1202 68
    0x1550045030320340c0d00005d8140199138041049061420086a1080700c5007000800320300d104000b888000d00d004004a401c4c81d02c40d802e9004880d800400b84803da1f200c0340e25040c4070014020603100f00c0d006211540120b1581e86003c40003d68503165030302ca48801d41c0b14005120f00030301403040755403c10801070203c40100c110500003008461240d8802003468184510501c0c02d0207006072580548820801d00c1c540041c007010190b8007980c02141d1400020106c9001140243c180d40300000e00e0f09103400c0142e0350980e1a012a00360040e099070120803e4084004040800c2c4100721f12103030a107400344904451454101422580d06206005850782d4603aa150282e182c109441300e00c031850f420441c00c2043c544030640c0e140014074411191031003507080090020300a020098100180c05100103070103005401e8045941030741c5c1d5409011650300344441006804200924007801c00080d80e00c40071840b5198040f10148a08140c200107185030801842007514049e00000c10381c0500c54090200c50b0300e0502c03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 388107140 1250 388105890 388105901
    0x70513030803010f080729031e13060501060f090e09030c0304030302070e070f080a0c0302160606080f0c0a171612021305160509060c07080a03021507120915 69
    0x10007000c84007450300b8140040e05121b0103410501c0c02954940d1521280803800500503092041641d50580d2900d44401d03070400740d04c0031003403181d03900d00b02c00038042040d1506001d40d011501a85041240d40d8840804646801c0001045000500800c00038015060401101508031343c001c8110ba1074000401111400c5d50481e90003600540c02c0303040100108500c0e0f4041c56840300041c0b5004e483c4030030780e0350060180500036249404a540d144c60301c00c4510b01070341c100d4801441008000241803064506100070b4086070007000624020050b0b00d0206100c00909064800c01c000e042030b8030f180c140510300c1e508860b4040340e46210f100d4090314001d250f92500c4190082c0c00c60010030340c600e202c58010312114960500d504000c00d0720b40010405440030541c10501500030300c0c980165100358100001e0b14038020729006d041e8901503c031001421a10010750381504c01d119409680c401c0c80c007504024103180e4122403080100d038401400100c1500554030411040d442003000203134121861140e0700c100d45 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 388108390 1250 388107140 388107149
    0xc08030a0612030815060913020c0f07080a02040f06050f060c012a110d0207060509031002030c070c09020702030c210109030908100b030307020409032313150807051303080301 77
    0x1003c58080c405c0c08201580d03d818090002e03108a0b1034000d0240124896140300c02605071a05e502051070010081b0500094003c0302d015022034144d0307071300c540e8003e44031404458101d200394039000500070840400e010304011110018811401d5000980500086521212140e1030075569054016010800d04a12441000710702859000c0c0c1088100080d01c0c0a034180d00e020038a0788042e49203500d02d9030001d804002d4550300d190240d00c803490000482d14142401503508185400402042041c2c6066409045c10600460b036010016688100560407481254070207901500f201e41001410f04103c190100c03683c9502102103080180d55510b0340c06c5400c090021000681810010011050100281010325031000d200700302c80e81c4a0720000780d0764803c0200003030040762200d031418103040c0078100a2054408002807200c1019219600820a0f40219030f44400c040070f4020110b1008c90b00502d03403c01c400513032a02d08254884072010754194010a1840340c4e01d000b031a40100008a4641c043e60003407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 388109640 1250 388108390 388108397
    0x10c0f05062706011a04050607060b01020d090b030f100801051e07030606170705130e061306150804020f030f0c040c0e0303040303080405100c0e130b010c08030a061203 74
    0x142800c0c8030703003440c0c44a150b51055000d450260780d5104201c0200350a411140080c0c5440c01c100c1d911480a00c1901a66003e940c1c0b04502207910000e002d5142c010b90702e119400da0a071000c031100e01e40103589080680c02038140405003400060200042c1442085c2c2018091000405181c1e80d031035014203456007100e40b084070503d030700020300558641e949000e8002c030003030409205080c00c25200078455841100014802c0204002207082075000b2002c0380c0908444e2304440404603200c032606400e0110a40b155401070351041c4034a078110040d0300c29001611400080908a000985030440f089035020b0402c1c2c5e0300540910880c0704a540c100018060f000d01c0e8406000707807082131000c00c4201e82400c4256018410079660000341035401204990540c5d40c90b04041c007040c1c0361030800d079203809003000340181514070703080c011080180c005130500388411040300c82e0300f03902010f0401e01060703400c401da42c00d0204400c05901c80c0003410b120082c59004000a03070005040da40c820f803a0303054508007601580407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 388110890 1250 388109640 388109653
    0x604060c0c200f060c120919080718090b06090403022e1512080a02070905070903050115051f0c0230030702090c07061e061d13060b010c0f05 62
    0x609100c0440a80b0300c0b01200c00781c5c102050f00300111b4035200b4503e160f9240550000d0143d2144c1d80e42d0300e500e108829441c405c01d0b081a00d404410703a0701c104d140904c5c12902c051b1003600d990300c24280181c0914640c81810343c1055218242070041c000343c064802c4041d801103000c1c1d448965800258110008a5501031140c080d041101d8401190080811560108200301081c400b8841410780140341560100c41c4640d100c180b00800c80c1081c1068203e292060300380400e02034515449074980741035900420080200c500c1301d818201d580d10b050b00c5080c3d007209a2a043d210140c0a03080800403090355810300a00102c116400112500000701b05600030070031401c0d0320000700d044000540c4125207410300079482c080030342d00081d8012070001c10400401000040c80710411085406c40a01190702503010300322809032840307260103060786000d14400940c10009200da00c001c4520228015000181c6c0a1569802c3d51201300161400d20202030620030540c0107180044d20b1303c11106241c0f806040078106 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 388112140 1250 388110890 388110953
    0xe0402131a010f030905030919030f03021e0a030915020102211e040302030f0d02070203150414070605040302060c1c0201020a0f0507031b0203010b030d0905100504080604060c0c 78
    0x1c40f2200f4100c20401d803030800f940b0b0014038000100c071000d000c21a0881400130509800030180a45900024210000c4a045404042d00020b0010554480411480070280800d100710b58840000b400038002401e102070070441800b2880c4084200c4049100141c0f80c004101450b5030380e83c101d400325528441c0841d00700002032078140c4440088240c500c0305461282400d0302c00070343c0d03401101c43d0940e0580300020001c6800400d1340c115288240e0107016212840318990b01a16198002c84054824039010584800094400b0601c0d80541d802612014113283c1550203000d225000004000554030814030084110b10301c03140220f1541016500140c0d5400600c10000d048002d540110000c0c44070030301c4140d00103034121491408082c0014071050341400380380002809444400c000d640c15010b020040308055a0113400c50b0700703440c0d083e140c0103c080a01c0c54100c880e8802e9209501c0203030001808a4002917003a00070740340c008a07503d01a0030300d440c15154002d0b05c2c0350018a0044100d4003015094 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 388113390 1250 388112140 388112147
    0x2160f15030603030807110c0d0f03080a1803031112010b03070f020114040212070905071116060f080a0b03150f0703090302030405042003090303061c020a0e0402131a01 74
    0xc0c0094185800c0c0714a500d143d4001d0003c900180401d0244105065010a00881040802c6034544018401440390f001800d01c0c182151801100b0b80000721450300140d206607090048180d40c034810341d6072030340701b0559450840060590300d030f001886900400003141149000c0b041c260280641800480c0e490400d08000307484110b1101c00030056905000860841c1803086020715445a01915859100031103030606071300300301c07883e084510228a000c0500c000b1507405900b88030021078810403142c603e84e1994058000b0300143c0301c0c440000b002030480310302c114422842c01d6084010f40f400494106c00240019040c10b4081d40d04e48480004070003000410b2028010080d080301c3c880c1001c1003100c1007620001d45900c87d60080502030f0792210400d81c1d02c1421100380c4c040c02e1801003040c9481c1d080c103444c02a200c1d80107584081c411080f00300707040f003807501003210815850b0340100380c1d040c1945850400703145180014004c0c0d0303108001c080981c003c4041406640e03082080d64141b202090301d0306e400907 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 388114640 1250 388113390 388113419
    0x20307110f0114040f05031e0405010e09090703030302090a032f01030b090a11120412030e12160204020d0e0115060f120b06090d0803072d0e0102160f 66
    0x540c40b40e041419800181d20b440d000c090b00036410420f140c0c100031007814910b10f5445203240d46100c503000391122041501840d8050015240300340d84e141c1c07290b90740c4010000702040540d04040d640c2c0100c03201b00000ba020782d0041c01da8400140201c0040c0e50742c2d8484407000f1090100c240d40168503100044155981d440036050107110034202000710715003200c0030905520380202420801591850328001003070b100b2064a001040201c00307440c4528280c6008d80480d4418015000881e05102d240301c242d4201043d00f42060507068111418a00c0c0c0125480c551005004140d030880d600b0480f441e04030801d4019440805a03802c0045011180b100c7d031207000004070390090007002400b016140c1e08961144070300a8041039541c0126000001c0000210f0520a900c000c03030f480140c0e82007050412a507500554898116521459500040081d01d2002440b200c900040304001a286044881e4040c1c140010501d0040c41126484a9120080d003104000ca0304074803581c0102c84420131034030542980c0b5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 388115890 1250 388114640 388114663
    0x1a0d0203040309030b0a150f060804020108040212191205090d12030204182a120218030601150908061314070f080304090e030f0702100c12030f0f0b0109120c0902030711 74
    0x81da0400d49c540f0500401940700074100030304100428000c103055645400704140b500740b4a10640d01c1104005a000c0c2c5045a5401e0842d2410700801c520120b0350b001d0b005032245070801501d4020402c409503a5219005064842e034024141e090202003401e01104104845414009000041000c207400b040303420031242d4542c0000000d90441810402c0750721a08072401103040d00301c09030711034007140300e00803603284d59141a035094032642e400004e824804807044001d00c5d04a440380c088007511841d803980c80c1d4600711040c0c8800210304910500055203100311085200c0e600c0e0941b410b10743c4030352081d81000c000ba44034410b550700200b000d100d0612940b0409200840401c001c0d0724050304178100000602034108081c0c40b8182000740e000d070841c0106403024042e64480144185500d0a410181c02091886002e1016501d4055100450081072042c0360061f0f0050319403091740c0f460116400400003c09030103e032103110030780c0002119007160010f035008811540781c014040b0020104c05203464804640e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 388117140 1250 388115890 388115909
    0x1061d0301060621020417011512030206040803090c04050403050d0e070f1a25060606020a17130b040f03110913020607021f030b0a1a0d0203040309030b0a15 69
    0x7042012681182c200c44d00b070368800328060180d4014902200c000d015a41c4a0b2113180150644015450380c10340c024811030b504480c10304070141c1c071081c030050060802031000740076030301c8100420049803030040a5075211034160101c891050400010500707845081c0e174110045040440c0c80c4810b034165010344aa030000c0b550044c4040741c0b5195260080c01c4e034511921307982c04204145030ba6801c2e4120102c400c90880303c0c0310105000200038004a03e200d1070001030391042d00e0000d020848610115240180343e401054030086a8103a866843c415400790000100a0801040000c0d1510088004e8401404210125030410b4a90309003030107000d06074481680310302c1c5540200a4ac000301114041180d58040c0c800d261140641d02c08610070280c254009020300390008000094242d25270080c40c184002656014078040d90b55400b041c0c003242070b10741500c05500c00d21541381c0c882010703409994401e009141c84580181d4948031003105150139200341d050ac940f5200b5000031070307030300d070702d0105c0141505031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 388118390 1250 388117140 388117151
    0xb032409280311160f0603060e07030e0c03160f0e1b0c1f2315040911100909050106020c060d0c2d020f07030201080c030c0c0601061d0301 61
    0x2403000d04540424900301041c540015601000c0c984101902c410710b4558800300d4100721440d03c0b814041d1003c52080d040c49925140d000b052852090085008443c6e0b040000701468858403429009001c01c070340103034a075210b02400030000c2c1c0c0d410060700c02c50721002c25010848034201060071210050980042c0480661901403046640715140c2c00c19483d81d50a0101b0b45407103c02d210f180c109251111082c180d00c00b03034a003521541020303a1081c000c21b4201c2240b96a429101401c21b50f4000c812a80c001501e241049008000c0c2800d4115896080c45401060245080480041e211140ca441c41c000040c415550034000780c0c0240c07040601400090000341241d28031803001550354030600e01410000d035100ca980a0320a80200540c40c4882500026001e002c6180214001001031492a80f80188901c42028902460102c3e84006480e010303521021a59140c1c5203003000b030f078000b4008000700141040031002490302071204034060b2a00c1e64130f800e41801d2500c0103494042118110b14801e03450107 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 388119640 1250 388118390 388118413
    0xf07020703120e04050103032d141b010507020109050727021b010e0f07050a0806010e04151505010e010816030b0103021201030f030315060806130b032409 68
    0xd29502100d40c07003182102150b5540c042210002560841c841c0c20a05000001c406c040e0488000c041d00d621410741000d13180f22120b0942d00d80441440b83e2130104580c05a54107a0f00b241c00000c00b5881d85403007040109440d61501c007400c403203080f030303100005035036440038101002800d01141703004140b0744100000d15030465013424100c1040315098040160300241c03051500055090829500211704001c1204c0003904160780d40b5161400b40005a074003428501061500d007011800c01581c801000500244c3c0c2048001c0301c9140d005441a00c039004584d8031001802014001c45408800603183c2050207403424002405c50000204110b0500903840d00f00701c0008100140c603441c02c0454500403031101d881f0401a4000e119546e905680c40d24804004414000030807540038800d8404c0d41c04007c07481c0c1c107030154400010140640000254400085407007441c0101c40c2d034541d6042c17100001048400071000901c0c10b00001400101118000d8000340f80460f8807000c1d07030b07020f22050060481e58001 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 388120890 1250 388119640 388119643
    0x3010303120f110712030f0c0c150b0616020a050103095d0215011a19020c030c040b0d1712010806090c1801061d040c050706050f0702 59
    0x500c41411800d980e010340c0601c1e048943c0107070100200b40190f2682d03a6009081514110f1000b016460200703041c03180e00c040c039406074421848000010381e1a881030344400c1d41c0e0000b0f40c90b4000300ea1040e10703440b074030f401400303603109002009080000c191300724642c0b1351481444030900560384101d05061901e01040003107095001030b1400300b080f94000700e03481c02840c1908058202010080c0b8401c00544504102d20a8066150660100c0042c01c0300d43c0c3e110301d180c3c02c80e510140f0603c030340c28200342c8000401852215070807580c458984080c500e4281541d40c0c0b4020540d28141040400503480315101c61440e00781800f01c01d0b51140156803d0205000e22000310b0400d190071000140344c25130075004941c0180b040303c03e5030042e00d81c9035180d40080d6960000140d68a40540da00101e6005985100300c4070b180500841c41d04010482103040b03541c1c60300c00c0640d00001c03c00c03a400400450740b28a00c0640d5180e100c0e0b000c00049a4540315280c20050401e14116440242010901380d1104288040c1980 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 388122140 1250 388120890 388120907
    0x10207050d150209090c12130c0312141306030e0a030903031d030307030327050c0d210207050a0b0c0d030b030c030616091a0d09020d1a0a0f05100b34020306090303010303 75
    0x4100c4014000312083d2f08045681c2c05507284524100d00010500c1864801140321721030171100d0503030b01030010f00b18680066441e9014080010042408002c0030800240100c850441c1903115200142c2c001820001003810355004100443c0002e90303440b41090034800381802c9000e030a4815400030a0009507030703101552861100b48062040710a5202107041040604060121341c01c00b16070119004540c000c0a5a03030101401044c0c8164002140490182e8188044e10b6400e28482d000300f60701684024223a004011aa581c0394240c0224590000340b03803420413200d0301640b0503144000c2d4a20220390010004130481c0c0154030301c0f103444400e820038849110107031524104415400140800c140c40091408803c0c0100140601c16200810300e031205c600034490b00c41e42d1888400e02c040600340014078110303401200d14484225000409002c2280c150020389412030048005000304060300c080c440b4100c5c000300007030b81c032401c41000b02c40860505000d441d8000760000c0055003594115503021b0070250 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 388123390 1250 388122140 388122143
    0x12021903050d0f06090509011404050613150510060315050a0308160510022109150c0d1404110105040501051e040b040e09010605010207050d150209090c12130c03 71
    0x108030581c0c10b49241e8081002030b0000c0408221455445400c1c0029050840301c07603c15520302252107184484408a442c4280c1e0b002c800341c5015906c9500ac0c0c83c9003001c0400035240c0301414401d0100680e20741c80340c030b8083c2e0800034a20300141e00e8044020159010b81a0940008124034820042c6868020701101034940c8000c1560300d542c00e0004a000d080030420303019202d88225941c02c440503c2e03d40c02082e008030100f070b10074109105000c10110400c020b0315091403a030b01001c0c88a14088818030040d03001664260348915011103582d800c4150b80118040c000c00041620600041100c00d005003009800300303090841c00c00780f5050028146009400c20064080741451440008500b4503040b06c2c043c1048029454941d0340ba00b1801070456802c03203064070f50b03610340f4a021900e50700014800080756402050707680d00ca0341c1c583d101004004070300181c0044a40034011103200340d49900b2042d11500002802903150f060b00e00120fa18040090140c28880c80700d1903040b40490114030004003501d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 388124640 1250 388123390 388123397
    0x90306050603010f1b0e1c0605150a14121507120f150504050f0c0f160b010e0402130203150d020607151e18020405090f030408070312021903 62
    0x5039100c1e4080707400b6010f0303180301d0b021035850841c486040388071000a9009000c0c0980c1c0303a1485003905810300c040c130300c2d50f0940c0782403500040c060030001800c40d0304140e07032050150440004204624011800c0c0c0006504a211950582000c06906080056003184203280c00401480d014a100e065a480b02d48080d1000c030170000410303603401000c28030750000203680560507800c000300103002c010840424400c2c06018400c034108404140c0b407100c2200c0c0301c0d00035100684131a28110506101400303070703408500040c95a05601d00100e0209082801c814000c001100c4151410315007841001920504040d040808501c10300501010465400e12042441819a43e68802003100e00004085002c4e244009003050703076064815009421581108000903c04211041a4500b5003000f03000c2c2c40002100081d01e4100400300270241c5001e81007690850708040a482e41c1d60b600c40c0c905421640550018042c5900c140300420030000300100c105440992031000c0c09000860f03100070510080c00300005401c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 388125890 1250 388124640 388124651
    0x180f0d12050f0403080306040c030b1f0c0206040806010305060907030b04030f03020c0f0a02011407050c060d090b010303020c010909060e0a0c02010b0a0f0302030d050a0c06050411040513021002030a090306 90
    0x115801002107800d00b00d41c542007a034945599240c42840f80d8001c03a0664000c13810181012a65402409212030240c00200000f0075071034200c188004800218104e0b06c01c0102c0301c0701540c090b1312014001c001070100c0c0313000381c40c0c15811030a00701d140c05405090015180d00031a02080440c880181c0240c00c940d15141c58800401c8510b03044000e8041c9003494201c900440e43d00c042d0018000446600b154400c1e02c40358855511703e2081d92640c01341c004003410136080f6420754180d501e0310100502c103915049200140c000e0040d00c0700c10f9100c000745c000b107001d030b88083e01c01c0c0201d42c2c108562100178000c5140074800301c0c0c1888044006800c000e04100201c03500c68420100380b034000c1d0005103040d94007801c00c0c011280d980001e00800340d950700c002e038064000d1382c100800300c40c0b095085400070061500e660480072603d907101402040001d1003580c84020181e9001138580d03036401a103010740c0c4501d00400c1e0f814040c3c01040403002e804e058840541d8010000c02806136040024907007240e42004002a4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 388127140 1250 388125890 388125923
    0x50a06030c0309060203090a11011107141c08030f010e04080a030e0a0b091f0c0804021207091406040e0a050c0d060e030a0c12020a030203040b16060908180f0d 70
    0x40e01e0603c0008000320300110801c640c2607400035004003954054200d0f141d40940d04001503031061040558109181c020400a03ca02c1c0e1540303590744a003540c0500069084101184000f440340d40c019400c1791184800000d0000d030119180c40c881c0504a2000b0350001401e01383d0391000c00b449a8450002815182c21043c0750301c003420310443d0481a00b208102e10384c2c2c5400400c0356180e070f0403145180780300c2c0e41401048122015610440b00213180907129000c4503150b41d001c10a080841680c41d030640e114002011030686568011041ca002c2042c1d02c0307501e6414283d0170401590072520701c2420541c4445200004100c00090000c0122000e039010401c2000c0b0b401e2640c007a0190342440b011620001550640644d0f1120f18000741c940552005280ca01d08a18205c0e21500b40c1d440180059105100c2801869044c42c010700384d20b81c0004c52006c040c3c010343d403000141c0d030000d80260341c150400320b4000424880040d0082c0b100600700ca9a2104844920008a40000c040f502804000880e9140d62 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 388128390 1250 388127140 388127147
    0x60f0228030e090103080406020d030510030201050705070b0c010506040e0604020102060a050604020f03091e190b10091e0b0301110d0e1f05010303230318011803021b0a050a06030c 79
    0xca000f4180d070745107685a041c420310710341c003034071032400144101c4900c0d070412407213440f403d40285040d4901e20a0240b46070011105904004002e0fa241e00179050001364540f5401c5c01025013103103e800200700c40c0303002810481250b42c03001c0039440d076400c24410000107071307400325441c0d51101085800141079100d01010070000e0003071900c404102c3c00d001060102c11080000d0fa1000203800c5280005142e440c8032445440798501c40c0079604107006c4a0803500003038400d0800d10b03800020805106180c540d60b14003001582c604116003004c00e1340072410340d8298200d602400c0c00303c00f0240d000340141810180c903103940d03200e07802006030107944d980020071708140300344514400703001300c003032040c040c1d04808881000400c0e00703104c114080341490380d51002c2c04040070080d600310f08098007114150f40d0780c01d000c180707050312828803c0c070326560f109400550480040c0c40e118140d80280c0c001d02c42050340a1941031500000702d80306202e1101d42c6410080e61741e581c6480300035100c041c234020030174640d01002035 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 388129496 1106 388128390 388128407
    0x60b0c031207020a020418060e1b13020903010507080a05060f0d030309020109030206030703020a1404030203030a21050a020a0e040c08070309050c0a030606060f022803 74
    0x7404280710704182e88000c0e00d005803003000200354001000c81d014058184c9007840303148030100501c0414415160214500f00c001c01c240c01c10110511403c0c00e407100b1082c41400d10700d4451581303404d641c043c1d0780d200f40b02900a100c141412500941095011150500c03207514000c002003c510300203039510031100c4003070806800f800309070300c0440140401c9942030703061020f50703400000140c030b8450055100d08000d81d001611010322400003000d441a00d20607005160040c8014400f60ba00401110840f14146c00c043c800f01d03c45241003000c0600c90400400d100d40b0b80340402200041355002000d81d0100d0755609041e83d03014a00300802c4541e010001c0001403a8480000e0105020b50b00040c460b9002e501180d00110303170000003900c000c14a4000720b074001d407101d0080240c19040f039503c602007c1240050130581c404001810115101001c0400801e102241000b044c54004c5015 = true := by decide +kernel

theorem cover : BRFrame.Cov 387949640 388129496 := by
  have h0 := BRFrame.cov_init 387949640
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 387949640 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 387949640 ≤ n) (h2 : n < 388129496) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
