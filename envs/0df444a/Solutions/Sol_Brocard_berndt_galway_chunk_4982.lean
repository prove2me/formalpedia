-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4982
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:21:32.509704+00:00
-- url     : https://prove2.me/submissions/8fc67fbd-8a5c-4c86-9abb-0bcd1b8ed5f0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 895863309 ≤ n < 896043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 895864559 1250 895863309 895863329
    0x20301050a18030c060609050f060f010903050706030213080102030412020f060915071701091505030c0f060f19090302090112150e240915010e0406090206070b090a03120204 76
    0x802d540d5007150003600c1140100c4003643e8421001c2240c092070b12503a80318110003030b55a40d45046c58800c01042a90600c4c0b86070401c030f041d031030130310000d100410a10102d480a08000d61200c900c1000c0030520021230b00018140d6101100300420310081144d582c41c540e041c1d40a485030300c0c50403881262074860441d00f40341258445007005c0d0035800300d4029694000b4607860440c42950540c420f103e42c2c01d60a9000c035015545a0702d80c902c03034285000c45800206000c40007082c842100002203210b8014400320b580c450303180420702c0b40714504010201c4040715052141d02d200120310701c0f8090403624003400268081c7d0039600022951000c000d40150001e9000f41c441484441c4015084001c0d004648119005024103085a2140d9807600241101c480c8140514907140c41c141000c00d180041e00040403001000c90401004998950010140c02903003000001c6074400d59400030a00798170801100807e03514500701080f007a0040414007034440f0f40b00c2d40e12001900854400b00e0b050380101d0003075403009 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 895865809 1250 895864559 895864601
    0xe06010e011e05031902040501080d02060a02130b03040605010e0f010b031302041b08040b07050307050a1d090c1c1a09040c0911040602160f0b031312020a020301050a 73
    0x15000c0300c40d01c0c10001c8807070000000b0152541c012a01701152040ea48243c034420004d8181149814040c56002d001000d00406124401410003561080080d0815664a6000078000c0d250391810640401900f910504940d40e4145464504000c1100340305d00b00c01a1182030109000f190030350300d601e04072608079040a040d600e036040219642e405000c806c0744e01c80c2c1ea802e041d000301009848002075540043e20b5502c00307407810382090004044018141400c11408000300017500760800c055403081d5a16140c40040c00d80f03403c0f081d205c24010480c0d603562180d000c4003007080c46d4100c0801401c0001c1000001c01110f202e080c507110684400c1c01e01004050078a051001190400c0101d0a07030050107401006116a503032003803031003240c041300001640540000703006e02586404002010040c46062600e111513480d20b403414030b12078124080c20100c10350000104103440c6043c40c1030660745c0e410000811599002d1034000e90350320700b5100101d000e0f5080000040304010300740308604c03007a4140e1b2001c80503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 895867059 1250 895865809 895865819
    0x2010b0a090b0f1f08100608042604170d090f140f1225050105040608090a02130c0f030501080a020d150c21020a0207150c0f0804090e06010e01 63
    0x24108400050390400700e8400003040c0380d604c00fa8481c444003000c8030303540c940082240000b0300020000f000781c0e007100c503406000c100495002502c19400350b0002c40800354035003141000341d4105512101480c000c50003150101e0030340c2048440014010b80c410484940806030341c0140c8039058244117030701050107524020880c0002c42214000120b900a280911402d44440083c05920410f0900c1c00da41c0d2203c1c1c80c070307031601c030a0703030000042c610304070b400800d0803442c0c01c0000b000c81c4120700a0008100d9444041107100c4820407507080215401091400f030001c0c600c108070014141d011844000038100384410b03c449000c0c1c81002d05071003c1c0009002c03c03036859000d001c01220004411503a010b40342c0c90100600c49075202d00152400c042c0d50300c8904045255a40701c5110b085102807040f03504c10012001d260350001001070480380118201a80010329140c1038074111800e00000e0075580b40b22118404011f4034600900548512180030410000b81003041daaa42d0401d00030081940380c2c00c1c0c01400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 895868309 1250 895867059 895867061
    0x3050d05011508151e0a0e01032d0f030e15120f0a060311040207080909010803030405010501050616030c150f0f050a140705181206040b0711190c08062502010b0a09 72
    0x4045600a480b01c4225581c1388100002e20a09900c2601c0c1040c0414800d5040446140300e0986203442d40c01032b0050b100992200415050300240040502490780c41c03045054945940d90304500422513501a15948951609901441c007116a00c07241030301500007035017503d0f940c40f0ba201503a801540b00b820001d01d62007404000c1d40312041c01da0f07507030341c00b4030510300e40341da4000301d00d40607006040166440b401c1604d0702509650701a08118490790b02400011080c801e00e801c000c0030380d600742c0303013488100890341000d1030b2842400300300d01d0805091180c035400982c1ca07608144030010b411401001256a102142e000b20340f03138818120b01c581841404104140e1003100680b01c2c04051156030365810b4000743c0011700030781a1810482d1960040010002807025400400e6802030041c240000d0140010340d407180c8030342804503141d0160300b50080c1001070244941d44c51000d002c0c0a02200d2007030911202c81e403004031000d440b1960110085281c003200c0751041c09018940780000c2c0200c070300c280c02c2c510244 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 895869559 1250 895868309 895868359
    0x9070e0415061214010c121a090c040303021b0303270d0b0a1401050609040207080d0612121404090b030c0919111801050703050d0501150815 62
    0x1541041e440e451014075000c032403164400400030110800d4038045030b0310b0844440f8030380f03c2071101d40d64034202c0b101d01500d400810801c94550005400652a4501e41040c507100c0c85e45161945c1014540d41040f07804e003d9000100103980c0a41c00725598103150201c1120300b070110010080c0c0640090040c10b00700d00b00080985450400f2100400300d50700628081031250004200a03074800f03440702c0900a0811a0348501807000f014104841595810030003c20854407c0a21060140303500042e4142405054810746c0c02c1540e00310700030700200b56150303007018628402c000203850f00343d1907205100403e8002c0c0c00042c80400f0805035942010b00e440001c000820300c3c851542d07050b00a5846489066585018082c481d0a014080319000e0340d0180d014000c13030f289450407804110081003000c0900400071208002090241307001c0e541d455051900325140d004030310101d05060300345400410702c400468000406d4012035500e520340390340c84444140300b20070580d8416801a0079042c200390762100c00c000c48 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 895870809 1250 895869559 895869563
    0x90e19050309061b061e1f060503060a090203010e0702010b0136080307200a0608040b0703090b01180c0503060f09060a170c030d0203040305250902120703050f09070e04 74
    0x2c1d001c402814444c14140b1408444c120810342151401e451103105143c04240c200004100e01d0308000b0029a1040d2459414040da1060000120010b02c0640c3c41d83d010034041c205114041d51607503941d01c03a00f02c5c040c0c001e4a815000d542408410565948100b000114000b407909401e40c501115010300c070040040d205007600d510611080c086000ca10800060140c0c9100303c54141190350003200e164a0312030310b80e0703000e07120b9901c083c010000b941e807005009400c81d4001104803001d031607101c03050b8010000560020642c54010000060000b0b440380116042d100c0010280010130003450300300c86911040b50b0306540709807054240010350038014140c990003100504940c085a84980c04c003e24411100c00c0b2600c00d50200e4548411804d0601440d1010364031b41c001103003000c0c25580c5054607800701010700c410058400203942d805982c00340a11005011501d0304554989000c40d03030a03289081100c14401190038100803d00004040ca0883d1083c03c0090140034030b1402d018029014400140007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 895872059 1250 895870809 895870837
    0x608040f120e040e150c0c030a180819030e062701030b03061005031504080a050a030f0f09030305092a0d050618060c03010f051513090e1905030906 65
    0x50514036460368400c3c59082004200280f078400540e2051760494800101a0b050146003440b5070300d6051800030a852800b00c45041081340269804660080e600c1d15511440c2a8403401000d140300c0f554681c1d01031001347c02652642c0d0480c4104051081034070803d280e400341100b28080d50b0080420b00e001c84a82205d051602159600d514800203151040660300091400072244080105240800800c200021880d00090703041c1b50907120b41e0480c2c014961550144500081c60580407031180d071201e41e2070b403681d910803c1842101402075009242001040b008070b0310b05008515049400100441e1400401c0203498001b005540c4204409070241c0841c0e41200d80a04664000b0340c0c1030103458441c16441040e1800302d500001800d00c0c10750040c20841c50075030204018451000444a1407041e0313941543c1c10501d001c05074004401a00c514401d401581c0583c000200e006581a0040403203407640304200e5203140700b1030514191055030800d00405642c0100080a2181480c1021700103446054030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 895873309 1250 895872059 895872077
    0x702030c0d021c0b16080606190912151d1015030b011503050c0c28060f05040c0803090105030105190b12100905010b03060d0c08010c0201150608040f12 67
    0x4940f0528100d0a00c100d6650310305004000100c00043c955071880d0309185400e081c24100200460030501c5111309d41c580100700c2c5203d15141902501c40c01000307110400007190b03403211609084100a80341820303108040d00307081a680010b020803100c2d1500c1e4002d400500764071003000840000910a03800e05441007110038200102041c2e00e407490078020480c1007844c0584400c032507001000c0782e00040212121850511134080b490400080340d40b12404001048810056849086018254072100041c4001e003821154145464250080c0740a503214584240c5403507110150151039008071050a400030700c05000401242c9880e07aa030140503100001070f4a0825160580303032070294800c000140c106d0b4140024401200b0f01094500d0052042d10000c11655051481035907036488040c20792480f94514510701414004004851802041c000000704941c0c00b03c1c2c40081e010b4450680003411280c00860002411809403120b0b5216070780c4020321461200303256071454004143c441642c000c014550b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 895874559 1250 895873309 895873339
    0x121e0304093b01060b130f1d010605092e080c03090d03180b040b07080105042c070915081e06040807060b0d060603050c0f01120905210319020702030c0d02 68
    0x100074522241c442510710403650510440c7e80300c803840d40e803080c1c0b00180c00d0600101640001c0e440141074446500d80307569181c12100010b803210000501213280070000401085565500c540301c0c05043d20251a0741c0c20f541e03505400102d1a00040f5214001c0d60414000705c10410703c20f900866469050794204840c1200903258140c0903402107a0448004000c407041c0400541c2000440740100000c0310144140d075004261503141498004440060707017910030039075003c0e44081c04a0800b501500c0010007006680980b1011107050764030502205005826019004104a00240c52442c0380c400090845da04e83d607842180541c06070310141d40b4a80d90310340502999580300c0500d1080d030301a03a8040395070750035820080e0906107000c4096200d000000d4400c081640c00c5010044540d030582c00004030074801e4203207681007011500380a11410035003044044807211002c05140508441000b2240c103402d03075000003040384030b5614040c1d1b042d80814103541c214900540c201ea1000d201030221650483c440e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 895875809 1250 895874559 895874579
    0x6031503050f030406021603110f0d060f0f0c0e0d080307090f090605010f08091b030721110306090c24070f02090603070e06121e0304093b0106 63
    0x91070400b000c58100007410880c4550400c0450360807001c400d00d803203d0918680d1340100511080892500640c01d50151030800c1e56414038040316a60070540a1040f00050940680100464000038500a24044100030006d1040c940b420301c5200140003e007070380395151141a11504004c00c080108840d5510200305003005944080040051840100f013003030030500090400c9542c0c100410421680404021a074000011054008900f2800511900c4007081c003090911416400c0341050043c80922002d00c0c03071840b2550005d035030054030481000c14400b0300700b64680c0d509890304000d99004000c42c0c400c524003c428106407170018400126a08a01c4106070140d42002d40c003507030080310b03114440d019424000c1c08281e003c0001c40103007184604014030955000005440340e0b0046a026249201d803c81c1080401e00e481004685c9140d813000c0300e05403da0b80d5010340507101c095802d11a500440c10801c100b542d00d0184800c0403082c9140c4110030400304001c242410b84525900d6030350000c1c0342000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 895877059 1250 895875809 895875823
    0x206090a0f15110c0f040e01060e0a050912030c090d06110307020f010b01050a0c080903011103190501050907050705011e2702010c030f050906040e15030a0b010603150305 75
    0x8a00d601c000110b20b005118920340540040c20401e000c841408509010004580b90060782011100d1603004680b081c04100244041c40c6600203941ca400c801080c6150805e543c0ca114120b200d2052007281c7e01c101030b1644409080601ca40f0030541440030441c442c184001402000d0005032000341d1104c2c4589515007607441581c800c440000000052140e1142d040c010310322400d60b014000d200c80e4150703d00007455846108101c108004040d10b482040090348805c441011500030007d015403c1c4d000c461642c3ca5000f5030b481042c0000408150000344183c0c0200360480d05d0040038a041d694989805030740c2c960207a4070407a1203550741c80b000d100d01038001d90301650740d90103c40001502100f80c0e09a0309a1001804510080024007101c040180e9008910221855041c03514116542d440041a20540650002158881408103010484034500e892540c850540803042c02c1112104400b819114030791131a014180040e05001408a035000350440180d0b0310060070900d402d103540780c550504100c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 895878309 1250 895877059 895877069
    0x1b01090510140f030411100e010e03010f0e03130e0112020d1b0b0c19020307030228061e03150306050603030d110702031e0601140103020d0c030605040c17060d0206090a 74
    0xf0004c02400180b1808541d4030b0042c95081d04c130150310080b42140030b010407140d442c1e0903041180d0b0103041e200548080d042900520000c0c03034284010210090120748a82021481c10040e0742514000103103044404c020138120f80b07680c00c42c444140060303001d0006c0400d03000e00949410408525031105074244101083c02040d101c4036075034480c0c0c3c201403090304200701c40406a001c40a100048170142c0e9001c03400e10101c940c11034060074107061090380346001c00b05c0501c0a128225410100060030768000c3d003801600c1d10b040b5404d01c0c601c549940f06504aa0005002300d501140c401c10034800200715034495900804000c0c100d070b091400460030318007603800d445a5111003880108044e07085003410030030424050000103510031001340e450340c0260781c1e040500c10303a007030072000292402071a4080d0307040f12002910f401050101101c1c1003000790141407148234540c01036207800004000c2c9403142604a06c020002c038440007003612520308218415a00c030728240da000b0010000740505540750803c201c0208 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 895879559 1250 895878309 895878337
    0xa0312030c0c120f090f0e0a050a0b090915071b0201120b0307030c0906060807050a0503150604060305090d0f0e040b04150f0e0105030c010504030201030507090806181b0109051014 79
    0x24414900038034417070041c1d01c0b0007503035120440d0612925001e603003550782c800d100392000202a61009000c41c042c01d1840c454540016040e81440022000800c1c040311030044c100c44406240c1360010101d400043c1010050865905501c1000045d0b06c6016408044858a0780110303181030f0880001e824101d196008691030355103c50108244007440c010b0701d0040041381010602c81c640b01e80041c0051080d5014501005000000240200d0850a601102150140c4004d0300d403515088058014901070b200c03221103202d0604902ca01602c6802c0c401c0600341160b071540302000050051101038070160034943e61041e1540c2e03160003005811060000140b403001c2005031aa0314080d032280203048183c1040780660030131207030701e2000d90308403084a00700d03542840d001a051b6101d580450386060366030005a024044c000600c03090203071134001030041c00f00709800da950f400c40e10007169041d0060444200d01190402d00d01f0081c520701154017607a07261050800107440c060703a00784240550b102641000e060 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 895880809 1250 895879559 895879577
    0x10e15040f0801110f0f0c0f0604060b090a1a1009050913031706060f03041e05030901021207021f0c0c15080609090c06160506041a060a0312030c0c12 66
    0x50900f40102c401c1d1002e07200100d031030310b0440f0002c2005849410700c00c0d8081e500c00942c0c0076604604005a905c8c804169040c0c8020307007024501100581081150300e4030a04000010a010002d070340324014044030320480c0403024a0410040c0540c0c41c40d07601101003402000c00002441d80c03910352000c1d100d1700380c0001840b40030f101440d018000c0c80b035281d01c40c24504e031340c4020003006494080848080603502e00d105503d0f0340e910f107000e8800c00d07103006074840f2140401800c07404015001000d407101c000e00f6000d036007150f03c1a1000199901802c032000c0d6010700c0d8020344410130200460007020051180c40c102e085582c140d01c907404101c2240e07120f80c8800750390b804110190b0b035012040c50b4100e5000c445544070b505064513401c0d80c1c3c8051030540d80c86004001003401012a41d0758050071006d60000c2502c2d4145401d00f0b02c500035050440d21042200da01000282c02898604411000c2d41d0740100c09030100c103005038085004001e400b08503410300a9000405000c1081c1c0522a00c070840c0035542c8003c4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 895882059 1250 895880809 895880819
    0x100e0a0e01081608032b0b030102210610140306030c0a0b03040302160602030a030c091206020702090c0a052b09080a230403021c140f0f1506010e15040f 67
    0x60b007021948401a45c0d0018031000384200c03807010300340d43d8070750300740c0c0190080062000381c42c0b0042c8400d000c125415840015034415150001d00b11200c0c03000c00d0041c081081d41e4820500030407007185100030001072200b0354561040e418002c080c41d0025005022110403050f00c001003031102c00d060700716056000c2c1c040200401c150b8104007100594030124100b4400a1030300708003070342d01c0c09400305240c14151103594203080c040c424410362000b05500360025030144540d0030804004d610010050b8000c42c00207000600482000b0b0480c1d0350b0141907030b20070b8984001c1c111031003a002a46c2c00c0c00000007111103c03000b03140550340a0181c40c68010391840341e440c4518100035103102120800440e0141c0080b21007160600c50006032030441c1c0e019218158520707008244e182c51502282c0001300400400c0315108000310000444c2890a03140740125203521052000c034556880340b09100440c0884460001500b40d4420010390340000000380585c1080c0e81c07030a50544944d041508112400390b00303034208000b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 895883309 1250 895882059 895882093
    0x812090d02011515050c010209042a231804050c040e150105121b07111206090d0e0d06020f12070e0d032006040b090d030218040e120307120f0506100e0a0e0108 70
    0x40d0b01020b5042c1034840d81074100310600c903c841e50740d05d0cd1b100b180200314012810070882d801020390200920400240c5007820002c1c400b50840c2c05204003115038000096444903820342e49068074901619814104018400d000000f400020310422402501101da000c4600c040740c05800c12038407030305618045001c0182480181030024035005ca05500100038094030080105500106040518085040303200700804203800f24414170006080c03d200007400080e8509036005030030180304120a103480c40d118404201c4e6211032a000c0c0540c85107059048e1400a4000d11003000e03196521070b403c40c0200c031940005824650101c60a4903082d072800e041141100c03003030204090400280c201181042c14042900c1c0503908454083e50043d6620030446100000801c03070a200044464003056591602100040032134101c1e002040d00c2d0b90400803008103040103405207c0c8a080040c042010f8a501403800b200d41f001002803058000d11041c40100c1c008104119550281c118800181184503202501346 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 895884559 1250 895883309 895883381
    0x3061b0309020f120708030d0912081b070c05060c1c0c0f020d02030c0d06020a0305010f05010e0d081606020912030705070b03040812090d02011515050c01020904 71
    0x406290002903070040e070310034244201c02e503000e8034426001c10940342c42e81d03c0d200c841d03001208648000700c0d000901c1c0c8226000094102d103d00707505880d514240205913a001c906a40c11400c0032208003a2100314040e071005044000d00407240088074a41e80c50210740320fa401000c0401c41d903040b20310000510205000c1040f1070b820f562030304c183d01511170746a4008640c00e9a50003442160722010340025958200702030508100000c0044401122614000c0f000b903005500c540302007401c0100005440c9080d0031170508940041c1c503030030b080000900401c10082c910340c50403900d84605200518054000075007002d442d034810755006981d15404801c00000031540c102c0c0c1c2020340d00422924001520101c5c0c280d08440c003031910103031031391036500c1d0900741030046001c01c43c0401108800c106984030f0000e402c4505a0311500208080361848050044032002801645c00005504883e4144a88030320010008084c0c080001428040a200007900340c0b06522b10320020115200c200040710700e0805500 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 895885809 1250 895884559 895884611
    0x623030105010f120602030903120711150f0a0203130c06110106090203040f0222020d06060f022109010e030d030605090a050907030b0c1e0c2a10021005010306 70
    0x1041d40903207080244c03490740891002c0149160340102c0801c0000340200265002e120030800c034001603107030080e0010704243c8102c103080e5240c80b03004008400c60703984219041c000d03c8080d031080040da8410100f240a0341c80034004000103102c049400002c00c0544620a014001c50364400c80c1900280403030034251009070300320a102c4e6104009110008208241c0c91000d01e40c1a200401802c0210b03007180144140441090307405070001824111440469000700d090380c8554441803a410000c04080341d031401030030741208484054000c2980c1d680340780805001c0000c0b0501d00300341c031502240082030030541c00980e000082602e81e44140002c2c80d000700d0a079405140500100a94500342600640d15881303844003030011072aa40114504048041c11a8088100070550204000d41d4501c0329403140c2c080e0b44800c04034010b135500095040e86200d54240c100300001d14035104c0d42114010880c40e8500382500303005621034030790f080303401d8082801610f0007107004180c00603100d42c00131032185a1842c14280 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 895887059 1250 895885809 895885829
    0x3010807050f030c100909150302040e0613060b03030403050111121b0301060804020103090506251b020f04090b0903180105041d041b17010c030b0310090303062303010501 75
    0xc96107940c1c0740011201c010800c100e4125100400040090f60b520760190032683c0812304048001104c1c0b0004901803045902c01d890070054844180c0b491510780e1010340e01160010150300005010881c1504208042407006055a00c2c0503681c0e907034107007141c030203481280071004045040300028904102e40c03a805030b120a54445201407002190225202c14015003040c000780b8004101564420303442240030651003011105103040c500d00d28101c0c440b03001501122a1401c0c4d0300003501922400c1c48811464694940241c124107545c200300d244d00a81d000b09420698506a170404a03c4001842d8090301d4240e018607550103c0c507680581e407030035140115050000c104000c01c1003502c1c0100c6150004000c030b0300302c0c00030b03110351510a00da80002005010b0500e424100840c3c425481010070345807074254402008101e030907000c10b8040e0383c40b81c0c8442c1d52680103079034100300d80100c541104845c0c40c420721b000180700c0c0e11900448440c2c035100d0309000001e0000704c0400d000f0b080074815240035240c40b00c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 895888309 1250 895887059 895887079
    0x30412030804020a0b0a052506020c0a1b180906020739030b13030903050f0c0909160512010605030118060e060606030a020a05040b030a090c090218330301080705 71
    0xe481449244524181e0880018008c404083c64060b2903d01942c0b03d0825996000311810b241c0c0e54081c180c8040c1c40e080a14019030440000b4048501300325422840310800c54501c411171000180340486041e41d4441c1c0801c00440052140802d09840180401d41c0c00c1003008003840000601081c3c0e880485d143d01c1c60282840030036030700c1e00120390101c14070382d180740e810b07006150850380300030203610080032071203000301d0954840390205101e0a07103017040d2254045555500d50b10383e0394081050b01d90480800c142e00030300c8241010144111403401940007c03030401d56480109084907491640c014400515981e40010805a4020501480760800c014042410002d00081e014400507140034003080c0d00040303050700c0398083e00030381740140056604240c40b482c04003902c001414401d602200e08040b02a404903504003188207540d003628210041807654003010080c01031341c0406000d0410304441203228410140300e0f81a01950500d82c0c40041a01d951405221614201c060382299205039a0385c4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 895889559 1250 895888309 895888327
    0xa2409060f0c11061207031a0d1709012a1a0610050d0e120310081501090506060c011b0201050109060b09060f0412061b090e041103030412030804020a0b 67
    0x440e200d1609400c8201100f000302000b00040003031203980c8203035148444c0309041044140e0983c1c04041144807401fa801d184451500070031140541848000b00041410154203184849003000362140c1d62041c1800c1e2a568540000b00018680202000501070700402203c020466100d1004507081e42466608859040c8480081c03088072046060703e04000022404004003a415001140c031001c1d000103407003520540784e0b841d9071558000c23290404194800000052101c100280d8400320000038140645283d0a00e90684041d06025054a500805c00d000b4882070301401e114662243c460342c011142d4484c045640031342980c405900c14010780d80340c0300c010441a004241240c802e203004903502e50f52022880d803840001e004039000002200700100c01c0408100c00c0b0b41c021245500170008911134180d006004a9039140e003406002224010b80d000b00e0b000411038198900c02490050030b6a0401e41c840a1060f00e0300745101702030f0009600101403100390b0a0481000f40900b5844da03c3c00c0c40d1480309 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 895890809 1250 895889559 895889567
    0x6070e0a03081605120c1612030f031e020d02031009020901020705010c06420b0412030225091406060919030804030c0815090706030b0a2409060f 64
    0xa42640d200f66141c10307942c1d03400c000f014800c48901e140c982d02100e0311044c09500c4160fa804181440c000e50100941002c1071b4264040c20799400240c7c150b031006000310741d50701e08078003030504200c1c84280700003102d0b10000f1844c0c090025002c1d00c04601c80058484c42c004905143e05144d680c4142e01152041280c180242d0b408035450303040d11800e080c03604002c442440c1000080206440ca254518101c1d800500060801c51302002080c020309c51082c0d100d801c108440100040c1845805c60301c0c01d040104001c0681c041e40c0846616000e401520f29000d50325014044100c896148602c03440c0220509001c100041d00c22500d0542045c50425421315099000c1141e511910800a104d481e0725902418408a0034034203901940d8041d4009071101d0381c03803908a001c3c01c07460180041c180220f0800b0754041c288048868840c14641006000032440d040e401e030700034256101541c0c2c001001400208107400e00510301c101a00c0c10841d072185d000d030980001081880d5640086d801c011006124220300d5600c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 895892059 1250 895890809 895890817
    0x30503061507020405010801050601140a0e1c0b0906061e0603010608040206040f120606090e0c01080c1b030d110717090d0203100e01050702072711040806070e0a0308 73
    0x75200d400c228010044950040c0c0198070000b980141010008118100190002d5000e05000e0b210074414100b0a800c0402e180a040c1d03104002a1084030015034910700b48019032000901040000010441520390030555002220103a2032a8071140901100b41801402a001c00c0130361070298500c5204040081c60314030042c801e210400c00030744082429036071048220360052008042c1c03514482c1e55103008030800d040702c04042c0c030068a0718a000071101d409010720320010210001501c40030070b000005441d9040041c00c2c480b0a03072028090b0543c0d030420803400d0700c8080490402940c454030f00174905810350308070700110740d107008050041c0b07000610703154100041c0005c407000745911205c421300452035070f0300c40c42c1c00a50b0522070503065040354003140c2d02502c48286550300a000940e20a00d06907550840c034864580311a44012605008200c11098191000071402d80428000000c40300740381d040e00290030004c1950405424804030541202c80c140c0001c00c01d50300020505d10310344039030b41c035402 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 895893309 1250 895892059 895892071
    0x152d031d160b0706020c07080c1e011b030306051e1905030a1103030f0714010b030d021f0b090108100b0a050f0108041b15200705010c050c09150108070c030503 70
    0x6000718524042044e10b40686200b000c0500c210381d84c5503503524840303540d200307040042800344400a0810940812510a9a5074100b040c0c44155500c4c03c0c030070490001142d241001d42c105a80c4640218450740c0340302c1348448810945a480c45000c19030020460301901d41c058003001078800f440c040000c0d07100820f4489101d41c10001a901c0c40449202190a51048007580851900001400c1081203941002540d901c06200700030030540b01e0050505558a1000d00c034040503900c0000350504011300d807107025141c1c0400c07072008100c0d1004140070400e02c9500303030807080d02ca8020003580c0342d10b503031180314031075070090203d40c1c00030140d240c0404103440c4500515958104140440054180700d4002c448501c20207281403070380800342e60b9001603400c02d414070705c0300c0380014910380e010300d0400520316052000081a8010703000f11440d280064810000d00c03c5c0c01c440501900c000046680c1d51401700034810300200e01141c0300c494080000400e004001001101885420b02d0284042031b480801da9601071 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 895894559 1250 895893309 895893329
    0x9060f0a02040902031014010806030309130912020303042006090621090c0a0902092808030c01150b19110c060f040503010501060504152d031d16 64
    0x52100c50000d40a4030607500b1028440f130001060203003075081c0c00c2c10701c03088894000c414080b190044004540d07500040e110b1030780c958000d00800c41385113009001156260641440003500019a54501411103138401d44080035800c0441000309000f490440c00c071309410200d12005620307040000081e45402104000c42c022030021591940f01840d5903003190359155030200700034181c54081045582d80c2d00c888402409070b290b0400000d035620080c001d90305d406800810094030a0406d1500141a69018402001c0030340f4070880000c001d54140010905c0c580b40300000700d400701026200e091140e003da0301468240740c00700304080031203c1340c100588070880603182544445403824803403894600c04140c03407548104002544d20f1150000d00c010411504e05400901c580e0380d07111402d90b01d034040e5118594094803103030700400b90144140ca14259001c103c4130740c200d101002c1d00c61001464105000107002c00da40703140304110f10b4020040b00740c60085d004002d2507251a05501e601240a4074425083e6030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 895895809 1250 895894559 895894561
    0x307050a081305031f0e0102121306110d0b03010605010c080306191503050114030a03090303080403051b06190b060d2307021f0b0a05100311030901020d0e0609060f 72
    0x4003840d00349020007000c2c010201c6000d0209039081c5c90383c09800703031000f0344a54942080c2c90340220042c001d8036032055401c1c440241a540300900d0b080070500c5054122007259484104010005c8004080d12035a1400c0741c0c000307543c1c8200c070281400c56030250000c9042c03001140f54540080d03d10001c0320313804041564140030031511345c1400071880001e80c100d48040000e04444d10316103075065000604841007090901e04140c00c40d000e00d9280c0c0900310b006800510300280c1440420700600e40d13660428440e00e00140f030400074032440750b4503070a518240d820f190820350a10614142d22003505003640c09140e001c000d807144c01c0000558a2040614030480d80d501c40c001502c1030702e0540114946450540d00881c150b141c52000292542c0c20f2000340f0005400c0c00940c2d0f00d00d02050320038201c4445015250003600ca050034100a14032031010400c104046c0c5800310100052600000b45010340303145400503898407145403032141940c1c12080c4004244e40098208205a44002100b541001c1c08207903904079 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 895897059 1250 895895809 895895827
    0xc03090d051c09150615022103010e1e01090905010e0c1309020604050904060c02070806010b0a0809030919081216060506130903090302090606032a07060e030711030307050a08 77
    0x10380c04c1640c083d0304078a180ca400041c0c8200c0c0424255201c001d0765090b505001a82003401b0180407069000f41d110340420b1005000e044c011340c045076085009184103004046201c0c401c808039490036042001900d49940201040117024043c40c40031201c50009008420030706404900d04024109140c8555074448140e1410b5460b40c800712400b40002038280070942c980703828080050840744c6c9041006110341140001e00238008604c190580701100e0b41545016002041200c00e80c0e000f03012000580003c0040049540c3e483e01c5100040720422800c424052414107220b00b0305007401d543e03504d1200304101448034401040c9800c1c80469010340c0009951311103102080c3c4d00b66000c0d00782c050f200c2c6844c1440c010b1640080465040300c0c401c65002c1415901c0d1000c6c00000d010a4600101c1c40c14060088110060b01c0d4046041011605034000e00b40102502e8400c25070744a00200c0c541a0030002d40d10060080c246103080c0403460a50003140b501c00e417541e075103a03a02c00d201c01c040e080c1c0c5c0c804610119 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 895898309 1250 895897059 895897073
    0x5012616030b0301180b06010c03020c0d140a0c0801062304020a0201182402120f040201180e100504020406020a1b0504020f120a2706140c03090d051c09 67
    0x141c00094005c202404031040b0f04640d60f5030000e001d403140d06500000440719881780c805c8074041350703041d400392855420500520a0080c01c0342012168819481c0034041203000402002070028050215030518514254030720b400c581044e0044a02d0f10881030440c40303400d00712980c2152110050f5401030342e03000704410803030060802410481c0300044200707207034090028a040e000c44040005d021204641550203202c3d00300c2c07040314811000c0c180854000f03100d100481910552050041c1400b1104c4d45007144002207141e1503400815000070084240300301c900700c44d0140700143c901960118601814080c0c040d5507118441d81c000c0c0b840d01d03064500f401c204901c00b40c0c000103190282095480300500c0c514100150070141c40c003d4a480b8420010700b06070303007600407135031505104216001d0f140c400c503204070014412400c09440c0039449207400007040b00707449411840740c20501e501944900300b540f0303440d007490303800b802000400000780a4a1004038010b8481c403c0e4660030342000410300c021f072030030314 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 895899559 1250 895898309 895898321
    0x1506040317091908011413060213150c110a080331060801140a141201140403080103021c3206090105101a040e1e100501261603 56
    0xb03900314600b8005a003000603003210b07581c00e40b4404c100a0241d80c1c0d40031500348200b03070300b1034482d040e0f5a40d10180502007082c0340c2c001c0844603c03443c40c44002507150030301e100c0c0300d2245010200001d160560b51405002d0625a02e4900c0f2a080707540503000c5240036090399981c010000c08080c8940d009140800e440440440420f401414100400c041c80c0e4032000506488002d01c503406072803000511403009450030310b04403000e03542000e40081401d1840d60912000c1119a0410422503503500c08500b216171280312028030451199841000c2507045205000301e03d011291281d04100350020140001584143e01a0200460381000454901102500c00c070701c090007001716419020388000d00583d82010b40041c0c0c800c1611403c29109185d80d00001c840300d6968a030381c500c07000300030300041c892151481c504e139400440b500b2402441c0081d41c00721105007001a14007040610111100f000b40b0f5800c0140110484078030201b00b2138014140b1844803001e18002d00035031350481e0307000700103c119006c2c0e4021 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 895900809 1250 895899559 895899577
    0x30e060f0612060f0411010216090c03090b18010b03060c0403111503070e0102071d0a021b03030a060303020606010905010e10020f030408060406150510050304051519051506040317 79
    0x1281c0c030f400c081c2c20525031040285c0741582c03c2c0f00403640f0750a8a5000103640081d4040f0f08503916246454014001c00905a50f00c0300000c241c0c880c0e01e90000700312400b1449000c0c1d04810741e41040130303000c890b0040c212040074241d01e0280c1c01c00c0f02045100702a81055408a0382c011000030040c10000c000221190032072001e0011104020041c00401507024100100d003000c03e8003161352003600c4202e0121003007038503400303080d202c08508000f0703021095540143c05910303501450203081031111680241182c001b1a40b290708a95641c504100b4103034100085900442c00f82460f400f03040c10080000c0c5484650040c0303600a8825a0b00140803510801072154144440c0c02a80c7c3c550307403200c81c0300d030301c0c2ca03c10b0790250f9200342000384002800141a01c21411114028401c1001541108007990079400041080d15280035007100900a812500081441603c10022110407070500380d111004803100500441c001d071820a50203a0319498400840b0706a0b42c000300c80d2000c4640b41c0c1084407103442200e0391 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 895902059 1250 895900809 895900813
    0x20d0e030c01060605310510022404020d02040216020301051503152205030d09030801090f0b1e04020408010612150203090a0609030519050415030e060f0612 69
    0x600a10120207840014110002072005980d0b4120032110f5000c0c6c1c8407131482403862000c140d2000403000441802820340e0b4500307080c1c10769544001440740c00318034a034000560400412400f0985c0280c030030324030303202c200c403503404450070a50080740414411440081c01035900044215041307440c41440b054003940107000744018034010021039240200d080d1041d000744900d86100e211301003c1c0100c01d1140400394003030340802400c0691080013441c001c1c01503c040c00204503403030001140c0c1c002c86030180d0098070354120710f5142c8240e5004580c40c002aa244131741c50094140803175540d40408162204002c0301500401043c0d400190092159510224083d031034100c0001c1c51601e80c030840f003241c6010b01c0305a4850000030104030b0591204035210341d00e541002d000c2800007442507020410300707402441c10300e05040c1d088003c403603802c654900c50008600045070802c60b0403004040d504c200d654508d014461010ba02c1000741c1d40da40060000140441071000050340f640705c034a4420410680002 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 895903309 1250 895902059 895902071
    0x60e04111b010606030e010908030f0c070804090203160318030302090118171c230d0f0e01060f060c0209060d08070303020310090e0d1805041505031b06031306020d 72
    0x440782c0c024000ca00c64a000700781810602a68072006100e1080354a030010040d0b855541d407844483c0120000800e044030401c018000e81c000f0400410103030024140b0403200580e03c0c1442402c03808007140c4000d02000701410b144803110ba4070700c00e1200c0201d4507414200961200d04810045c1e0b01000d5500d04070740700b4001c4050020b10015120f07441207080080d8402c1d00c090301000480740341aa100a890360000c10b9117001421002107038000d01c950400d25640009061103084110721003a00e400700581c01c0c2458031100c03890320f1030b1000e120750001400004a2104404e01d0064064501050000c02a1090f61540c002900d01e8503405400000144c0c010205941c54080c0c0c030300074000b074005a604140505000f8004140b0324614841c1c1700034081c03424004c00d400703c41a034003114550342032001010308000c1014006a140c42c0c2c2e024446004181c410105211800d203814145844481d46c0c400c59800072840c5a40b4051f00d4031022250411050040f0074044101800c00102030b00c18041e400301c4692400d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 895904559 1250 895903309 895903357
    0x15150f1e0609310b1807020a060e01090302060603031306052a1006090b0a03062310030303110f160503090604030602041809022d06030702060403090807060e0411 71
    0x1c0360070380d00706265031100094905440022003100e01310708803180c0040b4085041850180c09401c00c030b031310107214070403a080e0304003d680301001d0b510a5200407410340c1d15030700303c602015018841c09034000c0301a4000d50428071240384140c540512441000c00340640040c031040c2d0065804500ca240d20f510400228008401c100c04540c1d039520365125a921610b413510206109001d4022002d4103070001301014200350460b11540700405001003000c4250018202c8484c50381e4444101b00e10812280401c2004c192a504003d81075500c02d8100181100d02000312071231513210401982c42c1d000f51000100c4c0c140e14039240c80707403441c405c45e0f2183c0e0323002d280801c00000300300d80d640050050702e105080d56111031007840107807410b1740e8145400035400f501010500001a0050a040806400f01c8070050315100f00300d004a0708a50040d1195001078100004000c01c0c10f03041005074008003400d030b005003030b83e0b8580280102000048111070340b2035904c5030b0900c84106c44000642c1c0c1100026101c07d4080c1e8118 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 895905809 1250 895904559 895904599
    0x3250f0b071b05072d30020907031d06010b0405130509071401091a1e030603120904021e090f0904030905220203100510020a0b0a020306030f15150f1e0609 68
    0x3003885a060310b803400341e80401000340f20700300304400e0347c2c050980040f42d2200001600580340f118201b480e980e02c491000310804030100310b01c40c000c040d0007280e6503486050400b4401c20b102440680e501032030401e0180b01807401c00007a81412500e09000d6420828540c000403200300782150301200e0090b100105e010b600d100804010010320b1440140310485040c200440707460b42c0000c5410a52582000445003440c0e80b040b40100907a01d0000d000510308a641509800c2c50100e680f022900441c002c42e4413500b0703062000a0030340400d011100400d00d4600396400804481041c000c06000342500d4480307004104413114402c003902030441d802c0d9280d290022806da00003450b0322a951003520704d00b9a600c03043d8004900484440c1e0011542e200d01c0c0d440084c804043d520241690703030944179030300e50820004014072541074004c1140701e10140a0406541c04160b84035100d01d0a031040c03070903408160b15a941d40200340058100d4039845d2016030369030000142e480c0075207551950000c00e820915030a1a41c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 895907059 1250 895905809 895905839
    0x12070b0a0225051c1a0901020d0e1e03030f070507080405040c080714130b0702060405041104090f050c120a090b0c040f09020c03250f0b071b05072d 65
    0x400d680341c613040c3c00c80c0c00e42604001003514000d400300b0b110700548405000450091782e400b810400c00545025425002c0c0c50407034408075003c0b880c50f00400c41c840e2420802030000315038403081c500194194200003049428604000d08600241f0600154071410044004203490052100070f004001c079004880b00035000300340c1201c0701c2002a94443c01640c01c0d1200c41c0544099680341911020340ca418000000d1f19640010000d030392050060100040c1c2d5520382c050340b0000c4182d890f0440c1c8451405410700c09031070510144521060808003040b104400300740685a650108204404907500d503c1c00c03100c0108030459000d019a20450300b08602ea222550050048501003503484001c01c0e0f5800c0c0031412401000054111500100030100d41084109070040036400c14610803880e041d804d6807000010706600c1c200301c64641080040019a03500030f056868164100841d107140c0241558400740c4411940c0503554000f500b4000003888403151420f00d190729a2414081607a40340c490410b1202140d03 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 895908309 1250 895907059 895907069
    0xb0301030b09061012060207060e0a051005090c090a02120c13080c0f01080718080109020a08061009020c030714010501080c01020d020a0305031324050612070b0a0225 73
    0x55201007002c801e800034100d44501d01c8200c0d514405800d068207590194000c80c0c00f500e02036001d00400002c035200c1d01c2440d03480b04402000f0f10860381186001e41c02d01c9926102d96154501e420100408dc401c0071642807000780d4111000c01c01ba558a10054000b4003030038007132680d91210101084000300034070004008003585410380480c81680d030408140d90b03d01d01c07680207810240c00c113444105135000d540c1198104100d418a400403040342e000355006403240d90300503091a9100c0c8207140039810022500c03005003810401500e502c0c540b00e4002a11000544502c55050741c0c001042040e001082c800e03948050b5000e140c0242d0310010144540c060b21080c09050541c1c003a46e00c01c09003d44c0002088000c00e40960050140f500c0d041d1800e8a542c0c100926051008400204110000b59000943c0b52807210f000401e8019210050440e41207601c0100006d0140f442c203495030050707001c002480d50889a8919050b507980c18803490032400c02c0181108260b030054580782d8103218901c08903043c01915 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 895909559 1250 895908309 895908323
    0x806070801030308060307050607060b010903050d08040204050f07020a110102070801060623030402010f050a090e0f040501060b0c0a0803040c1a0301090e030901090e090703200f0a14090414010203010b030103 91
    0x1d2110020151a03007c1445910b41c090402c0103002c0003d03096421100d2811414108200c1441c2e0301d8030f58500380310015486000003104441003004628051152503005621150112114035061001035561140342c0b43c0507180401e8030001801c1c2e6807003082250060082e0300020302c4015a6454064200c01040f2140345031105c007103507090342d0380400d030081e00c0c403482d0140d440c03000451000c0400da64503840248141c0400500340c101040300d090242d111030182c10480580d1060f031410b4208a400c40b51960003100154804000a61120704002003075010940c10901d026600d407240e18007101c01c11f030158018044140407170200c08200c01801c02071412185401e60a200703926245030081d03160710904600e01d0101c0c0139074006000054802100e80d40c44144401107a0400791241c8074001c102c40080891b04100e00e40388264041810150811381100c18166010282c0c40c0c10000318004040080716964010b0707407210001820f000c00c211104491031101c00085542b942c40f03410000d0a03038400d000a40f0b9107 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 895910809 1250 895909559 895909561
    0xd0b0a060f06030f0b10021e0705030607080901050f15150904110702011d060d020c0a0f06020d0c08010f0b032a07110609180a110c07081218010e04060806070801030308 74
    0x41c203000031210901c0c12558050154019100c1002c03141245282c3c0b8031030348d0300c0342c00004112518204071860041c0095185c24590786000d200c510f003910402030855406003020b0052184200101d50f0000c0d27070820031960700c0880c2c110403040041c50300a40c54038607802410a0380c404021a0260700a04945000380c0c0d900340c440354090540c000500c202000d0b2908032200b0844030700f50381c11030b60207080401c140b0426241d1003002a110743e010a807860f441694042d60028150301d58035103507c21070140b204941008a50b640c07400c04000c402081074070801c07120b1038000001403060b8100100e4444140310713600e036001740b070713552852244c03000c3e041001c0448280c03c3d00b200b400c4852412205071264103800415103094171144142d0079100180145c441504c4903112003c2c80c007642400d20180c65074140490051618a150410a910b01100d844142c8420602005030714104402e040050201a0080c00d0901e066403020000c1002024542d20a44440c0031b8a4288410560701200041c1228002c0d036803100a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 895912059 1250 895910809 895910831
    0x221203030c170a0c030b2d01020f03071e0804060f03060504110d0b01050f0d0e0d0305060d060e0a0f1101031d031e220306050f060d0b0a060f06030f 65
    0xc42045205181c8100c1c0050001a01498480d00310103030344542c43c80d006c10003c8410022400702d4001c00c0784c4030421a08980c031111304001d000800c01c0005402d2000b010100b504007045c030340343d2150341000f5220010810030201c0760166054240718840c0d018030660783e55070b0f0701c110003080e00d400c3c1981d8500003420200c0002d00c51500e405040d00b5120859651442c181e402c90440e80102030745032195041c040b0a0101040031001280640502e5901d02004107800002c012064140f00c01c0d03201d004d0505143c80b0601840751503a001c00040c0940c05280001d5000d2030030801c501c0c180c0190b50017001c41ca0541d03414000c00250440e03415820b4001c0e201440a00c4503070300610480c3c0384061820030309501c103224001c0c100c06444840c40c2c03e041c500c0d000524016461407005040f42e440b0150382642d460084003002000b48070300c6040c2e030000004c00321403c3c5052000000e451040702c40005404a4001e07400b00318041d2040e0f11807001488410240242030b40d480740c000c0c02a250400350f09004624160301040c1c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 895913309 1250 895912059 895912067
    0x6020d080a091211010e06011401090905070e061b03070309031a0402101b021201410405010f0c0e0f150d020f040e040503030402130b010f0302221203030c 68
    0x18095003c0707250a985042d041003258100408942d0795032640d21503031040f41e080018486079000e0302c0c00882021149070150000f600b03c4501d81e0040074510300d84001c000b1f415a1180031039241504c101c0c0c85030764600c2d940d003101c03c0446000c000550341e4000010100c040603000100c650449118001107450782c041c0341021146160200c81c043d42200d960780d00c01608a2181b401e803c107510081d508540040119000b08440000751450141141c0d580d40341e00d048600d9035410705424414194118003e590718030f4481104440c03101c00000589561004942000001e40002c1201550482c040000707604c4640000c01300e0030300c081000d00801c40c00c48851010b09020710441c0300c81210088680c83c01c501c010b034441c000d501031034004949510030721000c0385500e061101c00c3d0049016000450312824a4010094005101803221102a140c200f02c042180d0701f10f0024010101103040c0140c1707072005a000366589048545800300c0340048284042031494821100901c103500aa034104403012a60750291 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 895914559 1250 895913309 895913321
    0x8030d090819200d0e010315080303130501060e0112060c0909050901050a0b0d0b161709070f0b040509040b0a1107050f100212010b071a0c0306030c030d0f2706020d080a 74
    0x80003d410b600c100c040c1e540a03400c6200c218900030801e01e030f09641c0d80021411501b00350cc41503219003203545c180042c000b09014000281c25040d0100c1000d516000d0401c1c00c02000560083c44144c5801c1c0070f9909500808010001381100e01c020b1242d4a4030990060091004450501e0690b00d0010b02c51441c1c14594950b14403254002d40c282519290b1404545030b40003502d8a09041000d508074024180c40e00c20302040c001c611003001001c2a504026104031040b105401a94900009001c1040541c1d68048650380040c1c00440b561400c1d00e4600781d64018000740440000c08020009848007040300004406601e2490641075801466507104990160301c00d0108072804035040e130740184600051400240001840340829102c0c0400801c4200b0703040a0807a0f2045041c0e82c044100b1403e41401d01c800805800100c0c00380ca03041c00320b1180503003a9100c0c0c006a0040041c000005407051070b070700b21103d0441c44480c1840c0341140c3c2d2000001c1d030301c02c07c51001c40d00050b0040041f40300d2900d41d00540c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 895915809 1250 895914559 895914583
    0x2070c0e060f060d20040305012f0a0e0604120c14030606120309130515010c0b0114030109050118200d0201050307021005092508030d09081920 63
    0x322481c480c1e24204400c64010b00b0307088100c4c0d5a15000344410084804000d03003d28480888581c4551450600608507044900748076081c3c5c03440c02342c80300ea503000c11840d1505071004002064441c6c10510301110701802d0440c0c482d410200004012640d10b4140b200301c3c0c0345901c0b845001440949230b20180c05001d00c46801c0e2a0190f01c0800801c00700e14003c103090b101c91285004480c2014031290019600008158464101554a00a002c04240c1c540001d0300c4800c0d00f0308240b401c905441da110210b80505210f0348541070290245c64106580a4000b1480540c1000080c05801c5440c902000107001800c0103e4440c6030b00035024101d44185070030b2880304d50b00244014009049600103441960005002c00214007480054985640c2d180c031556000d801300b08010304102c0f0980039415a200794034480b03d004003070400740401101d04004200d486400e01240c0225144181c1c1c58102010f000b030b81980c40100b0900720601030000e5001c100d001925610841d9407000144459140382c482d691041a = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 895917059 1250 895915809 895915819
    0xf032f0d0e1204090528060312020102070506181207140c010914010c1a070e030d0e1c080c06090102130f060206180c04060314060601260a0212070302070c0e06 70
    0x42044001d04c82e03840254059000320b08030240103911800340c01e01e0042c24a0300c140d01030350b031441030003401401d070089801e002c00c80c002103140100d607480b4243c0d110740050188070b0b4060012032901004800784102c0c00c00403a00b00c101034441c0b9407440c004489280350381e100c48031446800c881004540c416020301d400c69103050b1303071681000000401154a82001e0505640021540081c2d0322486440d1040e144201c040755101404115018101403c050001f24481d0800200c0c16202c10380e0355030200d8000725180b445e10340c41c0d0701900c1492b00351200e000b0881003600c5401541c0400004900640040c0510f45c0d2081d00f01d021203803202c0205c69540351501803400168085000180c070054182224000c02d0750410442e9210060000042d0644410350412101250b40821104544e41f08000e12368120b0310900b8080703001c1c2801c202800441c007418000c45114040c0c0f20120b2045d58040d8104d40c104007a45241000c80d1030505000340196001c00811900722042800028004141421842c081c00000b05 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 895918309 1250 895917059 895917067
    0x50102070501271428021e0a06050306120a03170a052e09111206060c150703020c011b080907051302091201090b011e060f032f0d0e12 59
    0x111300e07050b4800c4d52680d442903c03660100000403c508407294044c011000900d82e8800d1140c810301035401c40128090030883c01e1000c9480d15690341050102c1507441c40d1510544a995540014007000b100a541d0101030013589034605c01c0c0341e4031500400d680c2604841c200307800c0d2145080c4030100c0320101c0b505810254616081140d02800da0741d49010402008007007950700342c5409001080b52074020384014024000101b1540600241c02d88642c4943c08a40c000d0a03c0d003181d140039121040001e00c600d950008100199609004e03905507050492607000800c42c1d44010047c40303108600b02001032000c40c02150015405080004010017501e102500140082c401010000040c0d0001c20031964804c01055200043e90000d00c42e5904071805001c021110754507100d81903040895091503284040d00494052108681081040b00e01c40e00510700020b400c5c0d010200305003004108030081d001828401c040d58084219080542070320340108508102c0101f940840356501c040c2034001c1c0080c600184 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 895919559 1250 895918309 895918313
    0x8030402090606090301060b0901180e0a091a04200301020304170a030f020c0102040f060c05070b1605030a02060910060503150a06150906081e0f04050304080a05010207050127 77
    0x1e104541000d80030b00300034200780c0100e000900f903d015402c50000071102059102441d80d00c900c80300c0f61003a14100381c061850a1a0403041c81400003000c1007162030f1159400420000d54040030501a402c428403c82281014a850f40c03032550f40c2c0e0b40000300008014208140c5213410320031a401180e100342440a035110312005440d450304a0320b0503034180341e07542d0445440710580b4002003400c250041d0005a0b26070800e403150358002e115800140030807400c07101000000e01c00080e010b082d1088102c0b4187c449088035411000211803040003403080c000460802c200c0c03900001d60700d0040d0903000c1680c00c10603a0840440441c1c2c214441d03242c0c140e0003096050400c244019146412221040340801c110b80c503554115000011200d000c0c000a018801c00c214071540725480300c1d000720a01c2c0311243d03200621040d55980c00b002810100ca50701041c004941000400c1040b00c1c0280aa5826a0039090060074810f000390069082030310b2650900041854003800301407903500d042141d01071204084c0407a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 895920809 1250 895919559 895919569
    0xf0e0d08060316030f020306090d0504060509041b0302072d031116030305030f09060f0c090a03021c0203120304021c050f0303012403051012051e010e06010b0708030402 74
    0x64503070350301070080c18588112028100d258401940c05a500c41d6084185441410f103046c0f030007011007106401c00065030100507440812070301150082c0c940103031102000e4001500610002501c005010280c0208800c01c940580140162038021451003500400c804402c5841c2071043c4000c000c00c0580704620340000703001d13003000c08072040014103c3e100c502500031028019003080c0c0082c0c0221308003000700090f80507882e000c0c030351107050f90025019900b407080b881d03014000301810a032a124400b0514900c83e0301c0f502c0766034008640091003600c0d4030170300028a105404050209174020b01550383c40bc01c101944c0c0040b01d00590b405000f1810b078803050611540c1d04040e890701155540a141c42640b101d4104001450203015040c9801c61140c00f207581c031411b91894110341205040c00e0030308000d400070307100f400e42e82100c00001a802d45503500340341c8641000c1400e03000d13080c4d05142c0a600508200305502c0f0b1400b40604c6c10458041f81d0b03c2e507580c49a5801414401014543d08100040040c200 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 895922059 1250 895920809 895920811
    0xc110c010302071b170d030b01080103140115140102010e01021e090a0e1f12150e0c1302040f1d0a09150207060902011b021503100503030a02030405040f0e0d08 70
    0x1070800c10001c980c3c134071a00000503ca5038440c50001e541640f0084022806000800324428542800c1001d100100000381c1a550144405000740c0405c0e090000301e03481c03c2d00801a43d00121300c03413010880c1c60f6070840b11000380303c3c944240107600e410030f14042d4240c14401c0305c0f0411030108481920014a010310002d540c0039480094009401000028a550001104500447c0c02e400480c041421801c840e0100c50b00c90f9100034018020311010b0740100300d4180540c0150f501c6d11801194000c801c21000d23141000c00c64025030000c1d501e005070254050a5405002514030013030143ca10980d544070710070b0420100301002c81c48504200c003c5085040300d68407001c03a4511500e8103240e1007201e400f2082c01c98229040666540f91103692100440d03034490100c00c0f03d80d85010501e0000001038011030303003481c0421008441081c00001046441814501348030003000300030100c3c3d0740d40200301c0000351603421074030a09000d0b90a101d40d1812000e8107000341d1a8a0741240300420a0217a03580044a40c600 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 895923309 1250 895922059 895922063
    0xc050f0c0115060806040b0d031b2d12030e030a050c070e0f041101030e10051e010b040306050105010c1707020d0b0c0403050c030610060804030e0d12030c110c01030207 74
    0xda90394051810b200c0c0010070750024003075526481258030f005000e00050701c81136884507100d01c141d1b0200c40c0000350040f2011040d0403904248040861941c0303411a00107080a240c43e0015490032621030038005078400e075040c0c0c01d00c1507182908221701c0b40f405800b600c54441481590b6001030000040082c03145018020018215084030710f5541d9070741c010b07a01c41105803941d080340e400c00c0c0200700034001c01e8028203da4030003e02e010403000301d0011406440700039240403181c21030746070408240342c0c03801d124980b01480d032042c2c0d10032260b50313607461020990350040c40111032042c02c04000040a60098400032401c1746c1150200209820020b07002460760b02441c0100e91000102041001084003d03c03070030312913100c82203415130303450460920078980045002c8042c4250b02000420140391520002d4030112a2182059031040e1035510f001d4a14000c40400036402c10038120304036041c0a100c64501050f4040c0d900c003044408204401100e0003003000c0528a03150f0711450700100395512030f07801440385038 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 895924559 1250 895923309 895923311
    0x2306060c010f0f0c110d050412020d0605010b030f07110a03030e011d1b1512091f0501030221120a0302161110080f0105011d040e07080609010c050f0c01 67
    0x144641107400201c1d2100070b000d20000c0d6840043e13050072078000b10280314403030b1403d0060070b1002402c200101035100354010b469801c101404903170300f103455004180040d03070f5200c0c0c024042036031148500388407500216209054a0320f0039000c80d0b402c03070080180810b8801e8090190150000b661400e0f80500120351181c1c02644d80c4080f040c81030246c11017406e40c2d400e000000f0f010a5181500f83c400c543d001681850710814a002200346000307065001c5895100401044030b44580e5081d04003400d122080035441217201300d01c4201c484814041c1c2c4000e050703e101b22040070406203041302070f80d0880c800d030103100d5140c4d0011100d03014260814029000340c1c10a8074002d4903154030920403440398148950220380403204015601032610300f04a840209982c82e240142483c0340044205910300340602c2610306201c0030b080c0100040d489155012003030880a441403108030302584030345545082c24800c100341030080700b001c40c14000040c024181900c81ca42c0c0d4050400c800d1400c5500d41d9484005891015 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 895925809 1250 895924559 895924571
    0x31a060a150906030e010212040f02010c05030f040503060c090105032e090f0b040b01090605340210020d09140a080706020f0105010b0a0f0c030311030c040302042306060c01 76
    0x1074580e5101d0850008929a211200a8903200d405000c2e01c41003800d1600e41c2e40103000619040c0746da8a00c0304e84c0250085041150000640010f0b969100c2d592030152441c040015030404120340a03000f0300c12900203400311032855030340c100031503014001c0c0510b1900050041000c90400b0a803402016034201032880790f10f0102c0c1c3c0091604000e21615840300d81c495444150300c4401c1d4446208420031040151028000300711032000007062145240640802d2100206103083c000400c10713041e00701e0415001c03d4030a011034150900c2c3c2948401c180c2284180480302044900d00d01c0814861010b02150711514a031702d060001c1d180328001c072819844c3c2c104040c000300103540503081140030b0040106401600d010300e0081485801c1d10720580240c465280300b001360340c82007544002c1e054003400d0b05140c40003040203280307412400f0349034224082d821103070b010092140d07550400c0010b00460384219810000e0b03080e40d12038440c00c1d60070f404005040070361007400240e15081c40340c0145905d0714030307000004503 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 895927059 1250 895925809 895925819
    0x7020301060b03010801291819020d0902100c02060d0216060c0305041406040203060711100603030503060307050a080a110d05010e010507090509270a05010e0a1704031a060a 76
    0x30b90b0401d030312942440e074691050b151141da81ca08084421004090b014a8070b01590001c10154000940a0b581c2e46e07640b0800120060740101d040210b090340e5400555580803c0720800b8042d2260100c00e0b40304030a0550000c1c00c1038055200d00b40c1c103d50180034181400c0080c0c074210f00030340180000b0703038414112182d0340c070008a05104408200400e46c800040c03030b08003824180d04044001c0c920794040d82c801c05c28440507960018046070f0001d030a00c3c240482c540c10b6400c103400c102c0703412800b4042038203150b804010590000050740c031601e826402c4800041da03480130030131450010711504880d90412070403040400e01c222500224440e01030840c00504103155203d03400c54004a440010301c1e5990380610a2141d800030b00003000f02402ca03888406820910b010103034041c0180408852002508a081e241850500000d0100d98008000300200320102400035103c0408403812074000045408501c2c098110740c05403000d8030342000f0210100211066030020418020701101e42c4039420400000d1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 895928309 1250 895927059 895927079
    0xe0114091504140d1505040f140109110621070203121302040c030c0225170f0c0303120714190215070e0f060f04091121041101050702030106 62
    0x70a0100d040e07a03a2031800e403400022078104605607118000c95166000400e04039004045c0300d4454040000d040d4649203460354500703181a400400d5541d4520b00745041c01c106501c81d50000d80200800259071a0300c4007080658440c140c02c154044032600300301684000140526035010080e401201c0c0390000c41c540c0603407000030885010020000000c140000c6040c280208007400310503090a01480203d843d0181d15070707405150204926030050a002c01c3e19420000120040551a220007498150240c0c400c0d01d0740720401c82a4450b00c00c00c0e082141e170b814000708480f04801859800c0782141c80b0140211503940120502c001c404205004162101c1820781d034200c8100b08540090000502c0b0140c00e0307900b2940107050a060101180340c10205850f2084118002e0b00100c1c0c0a51b0341c0d00341c2c101d00c0ca946000301d41282c0c21403480c2240304c0c0d42c1906008020840310305104120008540000c1c41c0706026441154024004081030f0000303446540650042c1442c20b10090000c1692911644201 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 895929559 1250 895928309 895928329
    0x6022d060115030c0207260705060c0109020103050105090610050a020309030304091a04050f011a0705100501030506091c0804050f01090818030318191205031314010e011409 76
    0x11080c0550342d04500000c0d01807050826010b2540060503006103003402e007009242c01c0ba40b8900a500b1014102c1360040d2007840444040c1c41e000300302c251680140200301d0b00914bc0c0300d008901003854900040b613980380985c40c56204000061880c00d6445a020b412900782d0046007045040d84000e100f042c6c16980e05001a202030060003000203880d52902e500003400044002400d030003246084140540c1d401094038107419103809a000240303003200000407405610074680090124000e2040c1d110f00c1103100d07007000d41224090011240c81d40c84804c04141c0726450508507252410700700c80142a46070240c0c2c0f515a02a004405a1381580ba0705200642520420341048034801000506000400e854043c3d031610217000b0340045051039848142c1200403001050061322404107115400451907003140031700c004d44800707076010a2158192400f41c1e0343e41c00c5040060711202000d5000300d00889540036803403900205a40d0081c10300002c0e001074442e00c100151b01940307010208140c07101034498002074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 895930809 1250 895929559 895929569
    0x308180d0b130614090c010f02030904060f08011d0d0c020f03010e060a0e160308161718090412111018050c060903060f1f180606020706022d0601 64
    0x140c01c811902e850b280040b1400380c000004140380321010301440200000b0041d204070000c1c01d00b12106200080700360719601948000c01c2c0d2003820200d01180402c40581c12000700d0703d12100900801c4010601041600010b9880c10280d0f0303c004081c0d8211440b44204135200d40c0060022036081e107041c03001c242540c10f00010ba10031540004140615195240321300e80399100940060708100c00c050300500d0540b8924070000c0c202d541e021a070b51102418030341e00021403603401254100640320060000c1155080b02ea0084200001c0d21a80c3c24941054003c00d032086501c001071402c82030116005443d10340f400044140d02d48039620a4404a1101d8415003144101008008a1071100c40c908545403400c510710b014081c41c3c00340032651444e1030020340c1c1504922482c100b10a030341d0f00d03184031041c0003a80d000d6100005100b8100019040951940580100302c00300e01480f42c82d0300d64105903620081845010010790020316540645d0781072100c0103810600591302e9070303030714014540070a140000030782107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 895932059 1250 895930809 895930831
    0x30c09041509150c020c0f01020d1d060c0a0b040b010515040302040c0c050d0c020306010803120f1f1401120e032b05040c060f03060f14040905070e060315010308180d0b 74
    0xc0408103140c2031f400025410400d100901c1e05051603c00208160340c0c2e0501100012410518012a90f45231425140006006021203030480642d05010000c0d10302514160381c10b005d008004502070501d140c44104100b0741e807003031a01d01442d56081c00010080300040c0f17000c20440118801c0060000d2260301ea109000e0b82d100280d004d5180101814004107902580903981704005008251144e0001558000b2298041180c2503580d243d107046500c0440c0003a82c11402c00d00404640115010754034400c81d4000c0e60b0311403200d20042080750498401050f6200103500c06d2080c01007a5000f0014103500c0411070050808010b014440901901e00a0318103c0381a10441030902545900c880405543c50131460705012542c9800d0841014441c0d0b40185000329440400300081ca45594101c0c1f01c5280d4040121540b071a5a5600399480031425140c0e075102c0d0050a030007039440032aa0403a2416650010311051900c000e201c1c10320714007408458880d40084125080f0070104500e0740d08144100c0c5007040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 895933309 1250 895932059 895932073
    0x110c1201060f0b0310090c050c1002040e090c130527060f0906010f0e04060626010c09271b02010e19150c030623030c09041509150c02 59
    0x4080140041c660400f02d0010802d00c05c00182d2820107040008855030440300041e40103202c242214280314070300d0110300d140b0810013030754110009603006000b1138401030310131811a129468410385071715100c08602c6d8050104070003049120041ea010ba504255640645600e509071110f84907003006d4100c030f03c40410341041d01040140781c0c03078014441e88005180081d00042d0304000395450701c10b61030300800c01c050744840001820400345500c080c028065040112640c003420fa8040c05613103d01c108588003c0d400c0007400c0500034010402041640d900300307a05216180a004208040100b44d100b041d200c50300c400e10f000c1480e115400c184003c03100c2c1d0340082540340500e02a20310341290a245410146084000d100c0810004e4200c0b040c0b07400b8400012a42143c1d055085001e0000758105000c51002c404845800f4035600510010b100403d401780c4041080309400c00804a40481c3d018040c0360040d4280c004050032980055852441000094040e13901c0950400c01c42d42c00701c004c0000760340b0903c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 895934559 1250 895933309 895933319
    0x1110d02070f1e0e060114072a0f140d12050a0311090906061b06190509122b060b03061c03020d12090b0c071202010b10110c120106 58
    0x5a040c000e050038401c181d0340726402d94468043e8007451300c0b0740420081c212001c5203940e8403c0a0203000a441502025100c0b400390904540070300380c0852002481211003d10f2001020249482d01110781401154008034544074004200d1403c0c0a603255011218948190000d01800741f1030700c2258035552a40e1701e400042c079000e0110b40b44801b42d01030284003400400665682c60711200d52081042d2041519559440070280c0c00844c10764040c00c141c0079180c2001a0469234503c051030a0176001018410390b00d600e21959107400c000d416005400104004148440e41022f8000407500c0000035806000c00c07803207043c10b00b1900c0e15001000d207550004144001c0b4a07001e0942c040301030a914020702c44403010750b40070355141c400324068000d21000c030041c144041c50700da00c0060750700d400c141403540a00d046005101c03940d12103801164007103604034810744000e10503c02c402480801070070b0500858001c07201911030f140302d10080402441000d0580400d92a4400c0000d01114408004200b042c108 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 895935809 1250 895934559 895934579
    0x4120f05010212100b04150c1103060a1a06090a06051b0d0806011d1003050c160501020909090714210a031e0c11060903030405120703051c0c1101110d0207 68
    0x5c0d80826042d83c405d1000b804210b01c402c0410200140d14204040da54940c0c1c42d1a00340000707031400f80307a49402080c04100d00346009410041107000b900c80400c0740120903a0800009000d00150150000f0700080180b10140c0524028694815010448480c140d80c03203a036540b034980212a140000389008040c003000d940c0090f02d001c052860541c6440c086100540440c1c0040b071004914410582c4031030115045060340c408450a200e51507220500c1c800e8941003242c003075440035041c10300030030000c00014503014012841d94140c55400c4801e000003040d110400105002c950500e00c0c0801059000310a504410003a00c000c0b584a80c94951941d01039526280c46030b4031901051081c00380a0302000006401c038450080c220104030b6040f502c0d159400e02280c44c6004a0300311a801902000000c2030349203000413160704072803003801100c075855181d0101c00e8150030b40741702d00000b090106000e60009009128407028004040c5000c3e410f1600d041034662034001d90707000e0030026170403640c0706003e03140b20 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 895937059 1250 895935809 895935841
    0x7050c010e09091c0e060706021b0c09010306090317090d030c05090f011220030f06030a11010305070e0a060c0c0f0501090605181306051e0604120f05010212 69
    0x3040b11203000c503261003104075444048041c0c10002100784145000302c00c0e40104424694890040c2c20542c603081980b400038000e500c500a5400d201107003070414151004000b03103240c00311038050b100c50166403956843d0000b421803040218103121500b000301c074a070034588508900c500140740c01010750812548001d0100e13104441e140d4100041046203407820707103840380d110b0003d02d001c2c60180f0084400402290082010b080c40750f00515100c00c1202c140103014024500403210146101d0300e0340c407004101a5110502200100042c072040b07840c0f9103560096014036400300c2c0a0900045680c880c0000038401a000e4211801059a90107448144144840c91001400d01c40901421003410b040010b0000500c610540c400c0000005280c080c19082d11482e51410302e015107025207001065a1104c0a4500c500440d4050b509140055628030020480d1000f40703003004e029646040d080003110200000606001d1f15503415021583c80000c0c0240300034914800c1c9644a071a031070505418400500c14 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 895938309 1250 895937059 895937087
    0x3020f041b05090d1704031203090c090b0d0b04050313061b0b0c0f0d0b150304020a030b0a20030f01061103030f06150c06041112030d0e030f07050c01 66
    0x101d0406504004101160500c000c4200d500b4840c0d15035001c04001030320f600d40303040e004011001c42c44006100032080001740080d07d204900b47c40c10448092001c034122100c1c0350001c1c00603110010104003184280d80f03c0806150003410404d01100e1a07102da090118041e0b0381100c3ea64000a14402d105d91070741100409840c80d072420901e011002061100c078030710490000f80180c0305800100c1c1d00040305004460f42d400c01248519214000900003800400030440c2080c0102d070400241420030b5030000480b4480d44d4014280707040b15085845000003488000c20b0005200d0b0749c0c0c0300b0714824010000551840002d00e0b00450303908e00d0705035860007003004182c2c440d000f03122414410a20380000401580ea2000928100c400c29035241070000c0c0e002481040000d14060b4009030400101c00082a0385104034040d08804406034040e6041c00344440800054000c0c50304240144c82410b03174180c102d05058501001100d0800d40c0f6010321045070b0b0712500301102c581d4080c034446029940c00035411017001ea = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 895939559 1250 895938309 895938311
    0x207120f140f0306040c02010b03150103030206012103031e0906020d0b0109030f080901140f0d05090d0e06091315031a0c0306122e0b0604030c0b0706060315050103020f04 75
    0x2a020a8002d05000240c419803044c2d07184e12070b491045100b5072201b5076101008044032225000203000408900d403e000980040c05000c0011440c540240840b2900c11042c14001d040204c45031800c4004003c400703ca058441c10803955007411000501494078a00d0040000580c0c80c810050f920048980c400e03001410301020790350400c049200800080074407600052003a80e910510707401203c54a811403003c20030800702140c8507007880c5200000d4621034002c02c5040002d038440d84002035850304c01c070391480009070824443c0b80355070801d200038002c01d07440a00003840075080c01002000b0364101c0000108006040740003081800b40e22046d202850030943c58200003800c040e90007000030f00c40200f40f180a41d245008414486100308010f01d0301c40c0b6000c1190340c6101d0701920b1403c0702840d0501d8105441d00300101c2c2e04042c50000201c42c01c9036480400d1141c4185041200c80b0301d80c210075810790718a680d45800001013402051881543c03076040f840003400350b05500c100100c400140114901031 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 895940809 1250 895939559 895939567
    0x120d1404170d0b06030f070e12060c07141c080a050f010909031211130803040803070615030f0309030b011202030604030e04090609110906060f0a0f030207120f14 71
    0x301e481c030009406542280041c071640c80045400d040d010b0071a0701507031070b040280001002500303030000d0f140c0c50140c0132071b0fa42d0002c600903410402c40950266601d000700c1c0e81086021410280c104002031004510030083e206068918000c0f00d401c142040042135107840700418541505035001a400e640000d04c584200898185414075030100342050085c07140d01380c0d403105100305050040142c201d04252200342848804400d0b03125825039040340d460301e00e00e03180b000d40100e6000404001c1c0c900740c03850b003002103041071010b0321540c2c007405280114002001c600d69011020582d00c070041146103010b901d58548281c41c606e00071001040581c81024260306d04d190b40c20040c3c3e03000c146d140c1c001740c1602c0c3c0320400d1485d8000107402460592401800d8516107071100d410411501710701141244c00322450744c03141c1da0748018801c0510442c5031402280904003d02030004e4040e4140004142c0745140c010b04003607080d92007000001004072842c0200300300e8024081c881e503001040c1b080b85a0340410301410 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 895942059 1250 895940809 895940813
    0xc01150810020d020f18030105010b1c021605070303030524010c1412120f01090908040e040320011509020a09060509150304030804111806090414120d1404 68
    0x300d50310300c0484200c01d0b40018002e440076078280c05440390b400406100c0341e40c42c0c0b01c44103281e14072491542c00c54001d5081100004c0d50484030400d690b12040c1c0c1600e5031601c201e15600c618000d6101c50204540c50380e0500308400070035010455203000d0b52080d10002268103100744001d455000202e40203e048140036408036031641e2000324200466842400240030782d90140ca4582003140c4000902e918400204a0004443c00c0c580003e020700720b0300c4040d002990700c3d007110406481c8241c0026140020420003003010b200455a46584280285844264280810404c5000e8840190700d480c041e07440308903000b541c42160000713900030007085000b140341544c1c000c1d0207801030816204590a200b404560540c403510760a51044a000c013110842d0b55a14140c40d020b4030341441030301c0a9072086003481c40d02c1c2c039509091001c1100d1070844001002075a413204200310a14900400c101e481d6407010403044040c0710104001e00d4000c25082e43c140d00e80941656080071140c0c001c10f17241401a50b8428800 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 895943309 1250 895942059 895942063
    0x240e0405010b0d090515090705010305010b0a090b07050a0605040c140f030706050a020c0315240f040f020c060103050d0e060414040c020a050708031b010e070b0313020301050c0c011508 81
    0x80341c1d483d6240f0210f40c001c590708165040100c04211501c0c0d26040c1c2c0200001444082820002d40340245c030308000c13998031008001e0090081c103400001080a40c00140007541c5008058080503101d201210707902c414680d14181500c8081c3c0d011203046500c031005200031072601c140d00e048514181c82c000030490491001981c0c6007058400c05092000000d08541a184203000032100001c014049070f440c4c070422060701400800803501d026001c10100241000925018040c8046d510010704548083c484101044000c00c0031010603980b15508000c1924030190900c08035000b1401038010f07006130820a4006403c0c0c3d40f120744043d104001c10001440802808606400420b10594001071500056802a0300c4d01d00043c0010703101d4171640305c00041900e00003004107512401140039080808403005040d007600e13040c7e148000e681c6c10440e000d00140074164091a40b110948080134205180381e00400d003114810384910490030350000c7c0c1c00d20010400d0103004050b0b5450102803540e146844030181d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 895944559 1250 895943309 895943317
    0x60d020a031707021309151a120a1718010807031812020606060924070c14011b03051e0d0c05070b060d0b01060c050307120806040b0406230604240e0405010b 69
    0x87c4440e43d40e403c68501b290407031550041d8040080c08034501d40718140383d0f09540e1105480201d51f51500d10300c19800045640341a0f9409011a49070b40561440b1900150398903207008210310100350341e9810715411301218480b0303600918050340d01c0f4115809001402030034041c0c0101618043c00c0c1c10450000a900c800c8080e041543c13a40d82070300740c1c074403243d041d40400d0302c24600c01402400d2074003804070f0f007068004030807410f140007601c60500002c22481d05a000f05294a80a00812402d0000d90810b91841010707080740601650b805150a074032003070300e00494500300c00c0c4800260011910504001002907040d80050088030800a0100300344c0c2c90540380641401080c0c1040450b00e001010400e080003900e114690240b03d94071103c1100e10004c0003017808492044c456402c08010230407504081c420038017035480200c2400e4115403950300c0824441c182a507070ba90000c3d0104800180480c4121421408401034000302c40c0c030307452130b4130010b01e01409003802c81d1245291174010082d14a2903000c807 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 895945809 1250 895944559 895944593
    0xc0105100f140a050d03170601081b03061306090606090f05090c0a050f0403141903020303070f021906090b012102010e0d12020709060602030f03060d020a031707021309 74
    0x5a4402e0650000c110364124036803105401101ea20341c04401c16801c001c2c80d01da41130b062000c84440f555a9001158114010390391a8503600e4020000f0000b80e00310300003103078486805071544a00e140b0f03903005070302143d85035072098401075550350044c07102d2079018644030b00600040042c13000e09400ccc5070010704154406445940300050010f0b06900c014058025a004100c400000b152100e69909090145400d04c120f070301214041c3d00d02e009140f40c4e40d02e00581000707030503500440c295962088159002da105001ca103056200c0d50110515a210f045d14030140a4800c0c10085520b40c3d0b6403610300b0350200182c121420050554441c1607014a031488000901502440c003200d6074070740300010440c5148a04070290818901c0b42c112340350030342c0000791101220142a01000078580d103480c126107901406a0104070300300c0400c041089132400148016031140010281000075941383d541c3d000d00303a04001041f2007481c010500006515041c08480c0103698184001d0082c407829aa846400d04072148030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 895947059 1250 895945809 895945829
    0x712091109040c0308030c070204060506032e0e161b0b0c030a0209040c0801031b3b0109060303032726070302010e0106090b0d170f0406050c0105100f 66
    0x2e0501003803125100c0110f40052a0b15034a06210f01130a4460340310080030390256017003400c001880e0030f201003100c0c4a1400d25608211100300844070700d504245c501400c280c03152214a010501ca03c13183e4035640900009a10750f104a616814003034040d9904000090f2000044ca4294010401003c4465401b00c0d042007502d5030f0b5618142c01e20028080c0035580354202e4507107272842e456580c005032078505890140000c0007003003d42d01e082040700c040da401611124075401d521109191042004078018182d03030b00d400c542d001440c0101602c40c420981c0010782c00e42d1110010030a0603051710400680c082030004200d01c5c40c0f80c10345400c04048100c0d20061681f0301d03030680005591b8504441c05c5222801e184000d0b41c908040c00c00034080d00500c100c0d11500d5203001d40028082c50075125510711200090300780f5140e08100d850b42280c01c031850606154840c400c111080b681c448501c001d00c041d0210342c40709074654500d1406203003142e078018400f01c8405000176060180c2d01e800840c00c001c95602c8070b9 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 895948309 1250 895947059 895947061
    0x1140709060e1c03050705100b0a0306050c0d05091b01030c050a080910022d09010f08090304030218010e240d0c0b040b041d0105061602031c080712091109 68
    0x100c1c0701680f07229024005002d481a00c0f4003010390050040150342e000d00c0c05c40f14446c20a036900000c5414040313070310f40c0c81039800f1002c1002440b41d070841c55004040174041d074240f212000c89601030750f404544403c000d802c16200b19103100c0c151a0100036404080c070b8200007032011644040c3c410321074118a003041c801f40170001621110100182003a800b41c1d02c4043d0344030342c40c2c141681c40038400010410b0a040140b00c2107401c0046180c150391610605941e8008030070041c0781c0c203803803021002c0c1c818191400b00b0000800542c55246000004214040340c10700250b2400030030000d404000352031840d030120040c03081a0400c060610080014800f1604500d46440514200200b001c450b4401b00c0c40d001e02080c0000c0b050102c3c0007070012100030503011001100301c9001d201c030244c0c003402090750101050181e29000201d00112003907a92005e000c84040703844d40d40200861b2031b070500c1c0d0500010312034003c02c035006901c41100422000e0441d801d0040030390035680d240c072604a040d856409010074070 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 895949559 1250 895948309 895948337
    0x3060a0608040f05010f0c02120f03070507021207080d1d0109061202040e2703070b1b04120b0403120b060d1505090c0705011107020603181c110114070906 68
    0x10300301a140c0b0384e202008014002d1407081c0340b4090f2403840c1210340903006141c828041800700e0380442c0c040e401030300080d52039946d80a40a0b201a040030006a8005640590054080d50f0800c15140502884402058a0500010024040c40284e01103244101406c083e12803603036008800402550000c1c00c081032021505e800000c02401150300101000f1450414420a02c41c0c1c42223080450400f0074010b44a40f04e02070f40140e4900c02e046006014441c0c1c20002004c1c400700f400c01b0baa43c0c1c0d9001c0e04c00c600d071030b950b0180004150071940d81a9150b54441050204264002002d44003844180ba02404408051000038034540107000e104408503407900f940c40400c0f42c90310204801b40c40d00170200e242c00c4c03d0914010300190003084040341e0b13540c40c1c4240d500c0403110f10000d4900d8141e000702250300c3c40c0d69241d40b02109658000d4452135a01c42c440340d504246090086414101d4a2580c8622160610382003083c00c0d40c6034456140c43c1e800000c0d09100109500c0a40c04064a1490070200c0000e6240 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 895950809 1250 895949559 895949573
    0xd09061104182d06180e0304060e0103140108012c1f1404030c0c080111040302040b040b0907120501150f1812030c0b090c0330040b0310090203060a060804 68
    0x90f10700603568000c000d040da0700d00c6180e903204030141e441084210032607100001022003100e4200c402c0009a42c401d100802c1140d1107019084404038061401003200c051300d1003035056000c400e0700080001c3e516880070072215421000015160081d40881540d4820501c101649600b42495050300340400102e20301000a020741220b00c402c061400b10745164030f42424000c05500d18580201c40d400101d6034009004201401404402c0442e6140d5a1030189141d0820005258000410350420384807981d00c80c0a9850a08040c80340c40203403280e100200c00340c5554001c1b220140c004081c0d41e100340e1807818140b54001e284048030b9400342040d2104600b001080660320310316034094406a14008200020540c0c40603603241c80c2d62042060200c15111480c003a038842c144811710541560011080d8684011a00c20001c04000c0003103095601820511664240b64010b41101055141c00000e108000c00101c4c4c1f007100903c1260411411801c1060004a541049209076020440c840010409000c19 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 895952059 1250 895950809 895950851
    0xd08091c0206030103060606120e150916060201200715020708120c0712170c0a18120203150106051c110705060f0c0a200f030d0906110418 61
    0x10b0280d5100d682da40340c0080602840c0c010007001640740255400d520301103020300c0d003000100700041c0259806804070b02214942c014910030980c864009920600c0302d01b801214007601d42a4001f01e0540e200011008801181c051143d200a00400010000c1000c200d90449207a089100c00b5070350b9146820000070394020030a04805419089060180c0b805000c0c00401c2c095103c1d08485106403c103032401c0d00c2c485103080790f0081e480e01d03890000304807841c0c400080c1803640090500100701c142e280303103028400c2c019400800401000424400031761404000301070303006a01da814248075605003480103255000b002d0800f8084484074022011038031715500014541c0002c070f85002c0d10307401a4200b0f250340d0a0107540d448400c02c504408a4030303203e85c0108940b48680c054607031504a0003840c02c080461103c40441c0d541c140188031030702010850600c000c003040d020340c071008070307101a840c03c010085441d00e40c81219411400c001c100000c1c00b007140741550b640400b804c0000d060101c42440e00010300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 895953309 1250 895952059 895952063
    0x140705150903030601090b090f01030c0302040f0305160e0c0a180315050609070306060c020d06060b03040804060e01030b220f0f020a0e0d03171003021801080c0d08091c 74
    0x2805007046607103400000a10701c1190b0990312002601d0703880c1d0040081c4d1290b10407c503048599038000700300d02e500a40101c00c000368a0b240c01807500355110703080d48041d0044c1d00100c91540110201c2806101d010500c4000707003803003500300303561828100c890700134070b01c0381e94011018002c2d900214841c02000a8000c0f00031600142880505008851b60500900d8211040d6104405240201c0c80d140d00c02d10940003550305c0c40d124110003000c207408201c645000c00c82c04480464580c8030100d46880700e600594001e510440e801509c45003424005032001e002c10300385504062a050042520f0782d209428240001451450986414a50004100507040d0f8403d0a2481820203c805814000e00c0d4000d004a020b01da03541900d200c600d00030400c19001c0303a040500054241541100010350007600301d500310a50001c4034020b42d64907030110303806e809010060f288510148004001e8410305000782200e180085641d0b0303250b0407041e52440c1ca18050b60701454082d503a90380454003400754503034001130702039 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 895954559 1250 895953309 895953343
    0x1b18050d17190c030f02070308180f03010c050901020d020610090c1e090f06080f15030a1217181506041e0203090c0a080a060504290601080c0406140705 67
    0x40b00500c006003444a804000700c000541c420740000050f80301058000640394044202d070701c5c040c2000c0c1a194403240c1c00312040e9000c1011140d20318070b90360900c2485244071054aa0b2510b0303802d040d0000e07080400c0203000006540048081003043c80000d080c6c1000d41e000003d0002d08880d036100d0454580300524144411102200400360100740c0009988040703440d8a417004c100980c4800044400100c151442e00d00c0d0500c18002c10955601704600d0010f00b84080d0440c0c0c0141e01d25216041146917004080010030070354544031607807046518000350b001034103400007500c1203140780845650b440c0f6110090300700d220100100b5125a16500502104864594540c040c04299100a0025071050350b582c04c8074412071b20044890300b080c051210880307a0b40c4001e0b141e00c00a0391a040e0150a000300300310388181201d060311301d501003012050f241030500030045212901e4824009415000302404031001c1510902007040041d0344000314500700c03194a03054a8503008107180052900f608040d14041c10 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 895955809 1250 895954559 895954597
    0xb1207150305220c0f06052a030c12030108010c09120f05010b0a0e100e010506180103020d0608010f0b06031005010c05030c0a03050c010b15220503011b18050d17 71
    0x40243c0004c0e0000303443c810380e2402041991050280c0e82841201c4014901c120742e4813030022011880403010201e10303003c01c02e8030315245280203421f0030a408032180401c643c2c008001800030300000d1084184107400c6007081031009082c0302c2c1c8400c1c105d001d03035070050a031031010702c1401c1004020340001c0480a4040d140c1e020681c0c43c2c0c0e104000049013100d443c0740102d103c043c000340c9180011901412030704080c00f200d2912064843c00f441880880d2612418503808000c89041c80026102e400020103e01e4000180c048100341c4060581c0d0b9142d400512070b00090003484440c4400c012b00408540d000d003044007501e034291030302c281117006003141d00800b801000300c400300707143c2c0100003400c001c080103008005d00741095040199a0403000815884040148174002c015100d400340c49080000800049807101c0e96040060b00350362100a0040182606045418009400603561102040e50240c0d0810141c1090041200d1091030b060141151100b100980c4152040744110754014800105003000 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 895957059 1250 895955809 895955813
    0x1d070801090203062a0307050c03030712050a050f01140103090515060a06090e2806090b0102010c0309080702150706091a01090c02070b03100e09010b120715030522 72
    0x2021400401d034000e004032000603105071454840c055082c41041905c0314400c0c0c0e04000854141c0005000d002400f60812201c44081d00400146108441c1503a44041c00200703070010314240c07103024220004440c1440c061203240240304040c4c2d419910031000001001800c140100c010303040010028025010f075100d40e909404c0f0f47d00e2994443d910136100340c6029907440703404441d208114411800d508140701c010a003a800c3c86500ba10002c00c2d03485d0910110640c501c01941110080e9002c000350035519801c40b501540c081c00350110307208103801c04020240301520342010034460315400911444894104c00002c003000d100b911000c3e0703000300082010805504c0c4c041241010400c2d12000c001d00d1000011303a00d4424081da81d1807540560241042520742180c0c1103183e080030700750500d01004294082462203a9407072882c4250315060020480441086c2070240c0c01d020320b03030400c0d219048500248040f08140e0b0203c82910304900c4c001445507070b00000310000300d0721102040c80003400841e121003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 895958309 1250 895957059 895957061
    0x1110304151d0604020d060905030c100f09020d06230f2a12150613090f06060f080601210b01020c0f150705031905030405010f05191d070801 62
    0x195900254000700602004080d980b5901c403203181440c9240d40c840300c0003900500f05803010140880c807455010882004030368880f070540c0c00084841c402907101003d020300703002c0340b030051050b2a500c1000070440200f031a004078069603444c1c4000340104c3c0e01c8130050640c0c1601e11180381c5607500042520310340f50a0000140d96502c405a6400345484085000151144458411603121400b0400f071a440c4c81007031054001005c0d401000100f2414411003503000350b03140d0030018421035003000159001d060034040102c00300c1d0301e18000c144030689090b10074403410382c10008a000c000c8150500d00b5041e0b40744401218244807520104005410030a121000f480a80d0003e12024000740c003520144007101f4140700344408444d1406a2200200b05401a101c3c100700040608034010020349151503424031124100d22849054000000c10000401c010701c1801c2c800d0031500d881d004424000c90416000300320384d18030100204050240c3c0c1e05241c0e0018150751030010705c066151019079503903540d5021070034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 895959559 1250 895958309 895958333
    0x141003053112180509060a09020309010f1404031413180209180c04050607030e03030a0804051005040507050f041401030c1e1d10031b0f0605190e0301110304 69
    0x103520744054104004914003a0304000251805201444000340c40c113403c02c030000401414058111044100205951105000840c403d6103070b41c0010130482084d10000d0304a450700005001c9032a081402d000000f503002c5803c01d444000d80d900281c9607807035090b05020380e240c1980b2002c842e02c55595940c40c21144d603009003508410443d40701404c8074031044007292015003110744e404801d804100602441c5050300c003410f5070714082c0ca04000401d50040204c1d00d158040100a00440c4502c020001000802c10a501c480d440d83d0b10140520f0505a4032181d079141c0b00d0150074031070001d064011540d620b07903610101c51090700300c00318a45565a810070100941140c0100042c02d081c82c94890a0443c0d1080364000310741c400941d001081e54145030786181e0010280555070504904000003000c00c4032444181000c0c1c4c41181041507040c64000c00039002c8030320b03602c00000e000003801511038018103450b13a000210324038105000b0030160b0b500000c0c01028402035031384818a011003800103001d1010906 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 895960809 1250 895959559 895959563
    0x60111060f0f0705070c0303141c050906011211010c0809040906050a0b0301090b0c0901050f0f1c06080c19090c030e0d08090a060e0a0c0b0904061410030531 69
    0x20820707903e4096003150306114085000d0030301400501c0401c002407140038280f8040540c031004a040500b20700c01c0c29025080c991039200070310744803001c2c0020003109100c0d15006102d13a030714008500d10940c0c0c5602c10410340d112442c2c180700c01c480040040c420f80b5401c035180c1e240018070800c940402c40c903080004100a0390030400d582e03d01180d512072420140300d42002c2da50800b80e0b004440da12101256031940c4014070076030404c6030902100906000d81c101403c641850400c1a6440d1601161b00d4944100c43c0e100044079a400c01c0000c0041000c0803440002d544002d950451f0860209011950460481d9110009484c03500034010070440d410f42c00242040c00361010b8800103072496004489444003520801c0c0241c11014940c8001001c03980b040c01c1c00700704081598440780080e262034000300050340c4407500ca40f2001440c0c203c103241c00c2c440c1202410703035901c0c2c00448110b050701280111501f816608241940e41c00807900042c4032410300d40d2907154012520910038201c001c200259031555200b = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 895962059 1250 895960809 895960831
    0x204051c0c050904080c1b061c060b0f0a14270f210c040e06060d140307060c1b0b0c180904030203040e010f210633090504050c0405060111060f 63
    0x101441c000c025107d0000d4000d00301070624180e4004103260142c400710240d05665a0003001514802110103031281166441c080341e20b55803655006404418406e1040610302c5040203283d0383c000c2201c1c4c0c5030084c0310450540862500844003c40d1801e005414142c1e0b02480d00107103000c411006540000354040c0204c00d60b844050901d06120690f00c89180c10404c50b0032030b03c00100b0a04008a00151642c001c2c070840c01201440e4030007a065900a0200f5542d840e2200b164241281c0c120400d10341e2218032000007902c2a000340c41c0c0c00d020000203000000020000943d480001d280c0300801081c0e030000800203412410145000395403a441446000107080852000186024007074004508440c50078800080310401c584881003031480703c6008a0340d85a4984001d503a0422540f05410b035414244d05c48008203044988028180c1e05a52291300d48600744030030040040d201007076800c51000141e070081601d403100c0d401641c03820040950103039280714000401c0344100041100a024021030f01e0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 895963309 1250 895962059 895962073
    0x80d0f020d0e07090b010314060f0d0c03050105010e0601230f090a08060103021f02121c021306120e030403080c010b0913030e120a02130b030f030d0f0204051c0c050904080c 76
    0x100547c150381d82c08030750301000030503040003825038189416003003001030004220312500c00c240e50b20036100040c903400c00c4d0b90681d9171340014025120761401c026080f02c4242880c5c103245000c9030041d031040c2504021184600c0340441d070f00c110054100151200007100524040c10300d600c03080003a40d0f9a0092001380e01c1a4034070043c0a0303780e1807062221003071600355400307084101c001d203510540c245d03c50108400480888440744409100c3c03480038000101c0100e104100e8030340390050040c411103590419001e103074500b480c2d210310240c0000c100c40072680d224034410303100c000c2c44011500524507000c0b1941c0200018042042400d025643c0c1a80c051081e1200c0d0400000030b0140700e94401440503558a50b032041d034604c0c0141c604030aa5062741c400040000c141ea46d20710300843d003400c002040880680d440402e5032000d80480d402444d4800c1c6c0c28242c11814203142400049402500c0d41281a4844280020b04240000078010b41c002d020081e0507292030b400d180c41d0030380d05d80d4003020100b82c2d0760245c20 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 895964559 1250 895963309 895963331
    0x50106050117071110060915151d041d0a0b010b0405010e040f1b0c05060a050c16030c020402160b0f16111c031e0504080d0f020d0e0709 60
    0x2070766203002c180360382c031044416950341074054841c00509501821140301d45100741d00030540c0360143c4c0c1c0147c00300304804680510300102e89600301d1030580200c2240611030181c2440c99520052501c0389518080c030640340c11070300c00c010400801c0d10803d000c1846210304482c0100b02e5000078018485881100e0002260383d0303130300c6c1d0661240a180200b60000320750310901007440c6031603042003030341c0b030006480003403584641280381e81d07900c0d01c2c0c1c0d41d82d0010880c0c201e041824000203001c03c80e44903030303801800d01a03850400b816000900c5554905600c101f0b206800c2c0050600c10794950608540c054411940c4d4100048051380036021004201c03200200c940010720314007502d8805a0003800340c6025000410132130141500e50003c3c06402c14501e203d10030440f848420041e0403150040820341740004c00440c400f0804400e0a280d0350014006030507c02400000740e501003c44010750b9401c10001003000b210b4460501034419210510003150500b4141c1c901c014000c10010121481c6400402010307100c0c0c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 895965809 1250 895964559 895964567
    0x207060909090c180b0d11120105010e070c080c060c0d06060c05121b06010e0406050f0708070c112701080a0b010308030703110a09050a060e2d18040501060501 70
    0xc1100245105001442080750072010040404c200c100002c2c0800c030340c400c4401003001d02202203026034485c29011200106800d050b4258129850360700c0090020b07605004014144100c090b20140801034855440018821408190389400c80302d0420703110a801e00c180403031803603001800e1005000d840c103080051914000d0007110180b0782e101000e000c1c280e02a00014865401602428000d881003007074100200b80d0a01184e40a4000d0440a0000341013070309204040307940c020081c03a2211810020700c80c00300d0308240082d91140c55440c0a0340600110f2a101400c450642031481d007102d40700c10000c100c1542803401800041d485000108039a980b0440c4565550350709101070038407903610005101041e40c05004681c003803401c1c103011840700804031b11041194003091841000a1003000c00303008a1404204d44002460701d480c0001440904400142040d83e01784900b6052912400300450168111940c104000000800f2a217500c80300b8041801180720454040340c2a5203413540c046025801 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 895967059 1250 895965809 895965821
    0x70309020324151f030f0e0a030212031f080a03020d14070303090507030203060727050112050402010908030f04080f01020408030715060504110901170919021c030207060909 76
    0x36a504011a20381052201e024580f506440780c00803003101d061480404142c400e01d403904095500020740400c4000d10401f207500c51408940c40d6000300201001299000802c50b101c3d00410781d0141c3c0e680c503028601b1144010a1425000440007800005070304200400c860312514003c1c1c0940e024941000c0048800c20f0090001414a100502004001c00c7c42640450f1314680b0840407101d0407600d03a0000780c60488200c4019002906180540c20821201009040b000306d00c0d02c0203a0744241400000b0300804019402c080a41e555000010103681c4100500030050108600340d0b030350b4807080c405241c42c03607209010300c3c0640d00c00c1c0107064150090502c00c66003210302400c0a142413003850b03035071080040c92a03c0f0f060300785902d40030041500c2c0c0c1c4505c207240c00c840c8403481a07503840c19408009404010b10040c80a070a00303a100400c8100100415581d40300782c030039030004203040c0031880025460850a00c0c001d01190690b003680381010f0b000200304054494946400f400380383c1d2103007410103403a0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 895968309 1250 895967059 895967113
    0xa030f020c0406240921140a050d1b060501140f010c020303040303031d010c021b060304020a03081b060f0f0615071101091806060e01140717120703090203 68
    0x3040905007613003403c03600c010b0924040c0c00c0c43e10900f025a1500c00610009240c1102a9480c42d102140000c02c0001c1d00200d2803401d055003c1d284520fa9507c4807500e03444040602024421780303401c84a2007200008001030426805402001517584451178000714010034040c590050301100701c0e5080b03540c040c480030000d440e8018001d518140c1540e070114041e142c200f15032808407060b05030171102c0c05002e0241800400780c5030300a040004103204541c2c0114921540d00c3e006039001c0042c000036072142c1d400340701601e0300405104c0d03030740d40142c200c03c50000c82e401c2d540025000d0841803211191040128600640070400d104203141c84035810801c0c0b021800701070750403d00080100c200010180c40105203042d10504008450560300c03002c204802c0d1100042c1c0071166a00c980a002003600300b00803420a032400e1802e8254003480110400c0144186030014242031404402000402d640c0300c120346143c1800c0d40c20300c0807030030a210003401034955204101e101e4000c07407180704c00b030319200312070740c04454 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 895969559 1250 895968309 895968329
    0x70f05061b0703081e0c0d031505030106060509031e1015181508060709030602220e10090b0a0905062808010509070803090105030a0e0a030f020c0406 66
    0x524250400405910038031400d2912003031014401c080c00000c0c0803a0000303502840d0320b1aa1070399250305980c110f0140c40b11005030610f080c00001d0012800181103c25000035080c0092125075030402e8030300c035800303a90056600d076080640106689a00c400507100c2e401d403d4003200c0f880181002c482100110010782030078140d00080c8840101c1509400110782002010301d02c02d18142c40d001071035a03c0c440803200d0000c0303075251980308901000f000f41001c000e0050310003030103013803c0491000741001910f1201030306407a000b00f540020911241c0d10000150140c80c190034865a48500040800804440610b00900c91440c0015158101e00038084111801488200314a082c4140d40d802484094100c980281066240700c0d144022214034500755001d80e0340d00c0700d10038603040c4d900c1e003550f9008220f441542c0045904009175140003003036a0003a00300342800d45c1c41c1d6407203800c031070001c29510052031003a1082c3d03081c56041c150003911005460505500765400a4030710030600c0282c4800780316a556013 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 895970809 1250 895969559 895969589
    0x6050a0311091003020d0f11300705100f080c0f0712030f09060e070f0806010e060d06180c06032d09051506100f0206130c0909120e0307 60
    0x1482c00e0a212544051400d03001004144c4035000b1412506580d201251001c429803c4203051200014405c1c00c50442140e800e849445000d60440e403070603501d541e400c5154003031001d15034245003d2180b40c01500c030151000d02c1021804c5c40003080c680c1201620300120b0241c0c40420440b1907080304480d40b114070f1720720403458a0081e030380c0d030a90703640444040005c25544010f0000b04401c0341c02210240d9000ea10301003a59161a0389079030412580f58403400008035030310420007800c070003c0b5006045920215104441c1c1d521400850300306454000c0043c2050300d02030500f500345103840c00e24025203000b6650f0201080d100d00066040301c0c61906c0259540951004030290619007404583c1e111003044004518809260f47c0e4914040c003560440001400190401c240390030320810801521440c0d20307059400005102c4069150140500f481240144204481c818070846880c0c01e0001c0110000070001540c40d410314a5000d6924512a80000c0d0800c3d2440c0f4203207000181c3d4401c0d42c20b160030765403003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 895972059 1250 895970809 895970843
    0xa03140c0c0114090405070903020406080d0804230a200904020102031204061e14060d080429030106170105120c130f05040c06020c0405010614030403021c021006050a03 74
    0x31014082c503980f00c0a000401c15803405031524003a25001d0407803600c2e2605d003142144100025140c603908003501651001311411961584403045c5034000d50050301400d07503110040071943c0c07081d200c20050416403041100190400580741242c255000030680038400e001c400c00d0400000d52802c2d40c0181c0107a20038042c03d000700b410006859000b41c85110300040845170710320043c90078000618402e50955840310800c83da0404d815039141d1010b0200c42c0e607110f262075659041c00c140110302590f400c0c18503d95104402e0310001040701941445440029240e40c0e445400030007a40014071440c802141e64800021a424a911000102e004000c041c0c8407004402c0c0c140407500b0380c0803500c0d0a60f00d480709400510f002d02485144d0185002e4041041c00c0c1d0704103140a0324000c0c200382c40314000c52030600104a00365000e0384203680c401d02c8001e055500d84442c14200d291031948401d0140e0500903041403101c0580010b92500d8803911100180310300c42d030350810007401910510024040340d03641181d00784 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 895973309 1250 895972059 895972067
    0x3070906080f24040f020702040b240a03020d110d0c0f0f032007030e032406060c16090c090605040f0902070201170705181f0e010516050a03140c0c01 66
    0xc1030b150f01040f07056650007030004095441044506200c2d560001c2c0c0081907007044e0003a041d001038151071402d0034500400741000410840ca030230100d1884080f0715080668401d404950010444e8030040c00000740404801c4015400b02c0010440c261415807a501414081c440c8540d018107107444100306000ea40106401402c0812488070200c140d40e5500d80c64a010480a011240d01956448820f060300000f0305181c5000d01d07650441c4601c4522030030b040316400c003071019401041074a466485484a4000340c2c5030003603c181d043c100400960005c14258a6136200c1e000c608029510300c940f842d030310001510144940c1c0070300c108003641c01e001488404010f40052030304a20614017800e204000c0c0b04c820104800980f104000284002044000394850340c0a0000304001211125a04865141c210075022038040002d0f0612000880744150b0f680260141c589140643c443c80a090480e458040e40300c0c404001c08a005c117a803040840901c40c81101520000c1003000f0040a0015003c00155 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 895974559 1250 895973309 895973341
    0x4020c01090f141203010803091903061a030c0f090f06030718020310140d1b08030c0304150f0804170708041e061b080c0a080403030503070906080f 65
    0x2050564807075a15000040d090380b1074041c0580600f9039034015a2518001c2400d04000724009400810103200600c1410700200407030344a890100c2d095114608a00b00c20111881c0c5540080e00040c505400b00e54400c0042200c05412041141505d00e403455500800c07419058464100e0b420420100002d070061003810101a00542c0060889031040d5680004060580900024010044d00442840101c413280c0c2d400c680506815030701c41c0102d1403000085810016581009000070b404e8480d090590032039114034901400400c415039a4601e11403007855078951152141918040c98402014032a41c0324001c0540201d0300c944c1c401c0703040c0d22507849a10061b00501c45030a9101d00800521001a400f500104028100b00b40000d03a003e226503240240701c1c3c15a40102d081c01440041050218444055000e1480c0d11410158940d4258400340c1c0c0b41c00740300113005180b5580050084140b541120196100b01400d94600340400d0700c900e81101c90368010f4540c00d60940300d100200306241e69414801c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 895975809 1250 895974559 895974577
    0x1b0e1201020c010203041b05010203090d20060c03090f041116030e0a0905060f0d0b18030403060c2d090e04060b0a2c060a051c1506091a09060402 64
    0x15091140c0310142c1800c980c401d0300d007250b40c440040c00a0940381c4110a10b030004007824000365041640c84004603a02d10700940008201c40c0801c071044880c50a0700c00c2d201040040602025111070484900680d2a44071054a51061103000d44c12440d03807804d03008070401020700322007031410400f94180b21400d460304950110f01740040c2c1079525411f500c4400c0c592004003e80d4001103500d0801005010081c00901940c501642000a035407001c609a010b400d03030400c01038642155441000144207045000703e4000400f201d0400c0c80078000340b6404103903101d4111285603c500041d032038491000c41c060840842d8004140146020421041da100a465015001e4000400c3d0103860f403001400045094006191601c29a2000c0456003080800b01d03607010016541c281103400d2040024106040d00d00c81c46114030840050f00c4549c0c0c0746540085800340e4840503501e0519490f0107524040c00306406640c10040c5400c010812390460b0440814002c1805005d915580d11444244000780d4460320603 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 895977059 1250 895975809 895975811
    0xd020f0d081e0a08070509030705010e0d05060c190219020f010504030f050604060e0304031e030302040e0f0a0b06070224040b18090106030516180b0c0a061b0e1201 72
    0x2203100c0e1500c4800c0c40c40a4101a00b025036201c40c20704000d0181300000d40704c0c104011051200d110710f52030000b22079060f14400d00304000014111000a42d01881d403900003807090003039005200d520b8039180043e1080c3d04035070340b038403224552214040b40d0b1110b0200c0302070011220940c010000d270130540d040002c180818540b803807038192283c807400c8840525030b20846a540c482d10400040c4140d40c414840c1c204000d1001d10700c0c140c50341e1100c003000d6450707409002030501400d410900705402581120024040c2030100c1d19140341164411500072011103100c00e036181010f0860855103011801c90721055801401b80803038150700b0b60301802c5003040c4000041d81030b00401010403002c5040025104d5a100300c0c4001304003203020024024052010303880308041c541001e00348030303407484030700e131114140000c4d403804a5200184180e0745604402e00d904c07082c0c8030840000c40402d020004240024028000c0d50700b07102040c042a001c90714100141c0c3c6960006207800705501c1d492400031340c2c500d045016040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 895978309 1250 895977059 895977067
    0x61e090a1e15050c04030201080a090f03110607031e0902010215010f030317090303040b090316030504051009051005090604090c030203160c0f030507020117010f0f050d020f0d08 78
    0x1d00d4896400840c2001604000240d000070100301820300d610600391424071003404a0b0800d1035640080d030186002c000e06108460300007030380c00b804562004040c0c9402c0305c0032902e11207150074083e00740b584000401420740605400100003078024083d09480040140c2070400b8103420aa24000a04920b0422411802514900d41c0311606002c0307483e0280c1401900c980019155141c00303000d8284215036902c0740483d0004100d034074080407013544c0d8403d4000160303c80740e9a402c40310a080d840f0341c220040070790a07090750030b200f410b41c8280540140d0b44e0648810003500c0c044881074540360300701d2050a62250402c0c03c00004a0b204002805021501501660400362140900029103c00141c603100081d40071041198402c0d00d04820758920b442d504089500810386d481e69901a140c0c4440542401070001c0c1203400c6920400841800c40c030b40d0b0b144280381e942c484c1619803038441e0070b200c2c0950990300c0f03040106061801d214040c20441c2d0081ca12101c41c51003006011005140310820744202d40144 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 895979559 1250 895978309 895978313
    0x6170c073f030b01020c090a0518010c120e0c03061504090c17070f0e070507020a0b071a07030b0d120e09040309030b0a062304020c01020c03120603061e090a 69
    0x10500590110211004104a10031001c00804071000005254110f500880030240140c46100080ba00608013010105543d5580503000000303412081e101e44c842e61811740d1050243d9402880c2d4204a140b20404ac0440c10305e1020440c0e50b04e21344e00004d64950040c0c0042848580d00e0684000150f601a002281040040c0c41c1c0c3c24060b14168402e841d002800044003c04401c20300401028006141e00b401c200c0d82040480d00001c00010840030601c040050103605660b10102c45800800c983c0c014903540e51140e162031900c48440d4080c400c442c100704400b060802d4042e01880081035001b500c840510702071a10b030001460018628481071115100044142d512204405840349029031580f44a8500c0d510700160b1746d50b80203150040c1c179458a2000d0000c80142c44480340e80032b0840e00941c0490b149400081c00034031514020750f200f580f0010f20002ca020020000d01504946141400c52075607400c0142b5495010884907000541e000ca08550500c08440b01e40c41d80001104003114800f11481e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 895980809 1250 895979559 895979633
    0x60f04080a0e1c0c05090f070f08060a1212080108010b15090d021215010b0405010c06150e07032003041703090a080318010b0a030206090d02060708040e0106170c07 72
    0x503c0080e901c0c40c04140082c019070402200d2960001c00355807078441c5516201074010711809030028150204011000071548541d10a0440701c05452110001d0040080364078092110040e024000b002040c441c000014500320188208016804090542c0e1404090130400103c05d502440d000342d030000000215201588a000c0c07007041c459041e40080c8200140d00202c3c003a1a00b05a00280102004001c140304590b0b00003141401a40d00a001040586100601d80d0300c0003800e401980460750680204040640d05810043c2c0965030080c1c4803013001403520400301e4a1200300e40c098041c0071aa1504d4665503032501c02540c3c09042081070320454521030f500c008042d031056030800c0503022461850328440d0020b10845281d01000c883c8100b1007491030b030108485019521186100e2448003840c001552642380484501a6105607041d59483c0c9818074801d0882c0c080c05003038001042e083e8005152254903071054000ea000038001401d00c10190364600058101d400c0450011034001210010746800d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 895982059 1250 895980809 895980859
    0xa140705060402012007030b0402041d030306040608060105090c0c0f010c0f080601110a02010815030a06061401020304030c230904030201091e150f0e030a05030108060f04080a0e 78
    0x800d901800c0181420700005215490240e0304c46246200c08081c01d00480c8005104c80440fa440705102240740d480f800090300400c84083d05071035a4541361000060443c01000540c410719049800300310b9030b40c441d4403107a5030362800d0085a401c020104003144585998402810300080e484040f1851031800d411242e01351820b1031a520081045144010748180e00688200d0f8400e000b860b20440300380544550740d507603000d940e002a042c2710444001ca60381d081c2103003c810400f600035003252098006441c044001781164400d0284149580800021944c404030072142220780008428000c1c80c2407009050b042012f1148580740e003416010a40100d469a400701403045000b0b030000200d0200a08240b450090010062058000c41c24010f00c00103030300d51a5440c5d107010502c000520b24082c2f014140041408951806181c031010503144c4003e5800801141a605081c06451094a49012030b91642c541a5401042414280401e0b89024414204082c2c039500080206801d401700710404a03181c01 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 895983309 1250 895982059 895982063
    0x809060f071410050a050f0601030b19061817060103140703060f1a03031603052203150b0609010f2f07060e27070203040803030f06031b0a09020a1407 66
    0x200344003d4001407040b9580101e0240061240d49807100143d0703070341640201581d052550b210103145150305c1e1840414650480380400c20700041d1620307400341400b040071501609210340960b010a03040d454521f02e110850545001f040c60764255a960302c522200240303002254401c488000002c201ca0740220800d18000507400501e240780c0c2d118089a110000811a0081c1d01c100030b40c02590300c07102c01d074058054251070416105e0186240c580751021034440c0140d50096034003808002e0140910b410701070745602c07400801c80682c80c40c0034408113000310450030b40414404035844034428000c0028080520005100310000e466070450070200403003220030b1182d10742c4044002d000c55900a03941880818007187d044001e002c03015021064030246001080440c8004d40214034154000c10503500a02540c0e0180c03074680c81c04030381c0440c640030100c130100d07c20f22440e030000d501044001c90400c160b0746d01070b090341d0701c4504000b5400045d52100c00782c0e00030409120421000c0e5000d040107050424 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 895984559 1250 895983309 895983313
    0x604081e0328060828060603061b030c12090302010f0606050913110405190b0708120705070b01030611070f12180e160311070b010312020a0809060f0714 67
    0x412241641441e0240c00000b403100740c0c6048030610507003000048200c421110381003c2e038040041d8038090750703507500c424000030807180c1040004003c01546402c44910360000c0e60f001c448290100e44100d0540c0c40114096000c01c20340080130540f05215040310400078042c0c000441e0505403000410201d460b2948948001540440c0c802c6040c68811321241940b40d500805012010541d08064507510442c442c55200f5500384100d000d80410801e0307601c00800003d0003071900c0700e0f6981170501c0103512074513220145028030f4001134130450043c000da0f4509500030828480907030950f9a4500200311400386c41c050701c2d4080c41303c60001341c008810009518481c6e0701200c0c1d040c5078408041c110006d000c0400100701802c110512034525400003041d030021030804880f10501c40164107400904500341180d0354030344005108010300943d500440e04891040c3e030ad228640010100072610748400800080c07070b8110400400d2a607107850700150000d0b100c62014146001d80c41d980382c030136462107030461907055 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 895985809 1250 895984559 895984591
    0x412030c050105150a1206150608011d090a02100e150418020a050a210f05090c03120702120309040915051f050103232806080604081e03 60
    0x110342801044e410482c054220b196180c14180000c103078803464000c4007001403202480c0f4040c04003942150342da9044210f04501ca20792520402401da1070240180d42c48101035441c3e0400309040034000911400302c61001c1e0010540c25400c210081185041e070608000400c100281c05580d04410100004841412180c1d40e80c41c14410b80512807604100212013071042c0131038070301d0640103012501c0b41141e615001c00700c03542c0324010b00d0021512030103078103e1b03900c0d06404162a80c01c030380c0640e0051151004403008003203080b04040d0380300401700d41c228002001780032060050609002608884c4420700a80e428401d155000c20308580d800081950701d00c1c2007481d030f5120f101241c820641c0156024410505107208a4000450003210f03201e003604050b0340300b00725142c010b020000e69001540d00d100090403800d103045800001001c4000300e00d4500c000300c01528094010380309102c226800d240140106540729110103825400003002020a00a034038074a60152603a140210b00c918801e445084034 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 895987059 1250 895985809 895985813
    0xa0c0204060e040305090111030f030a020d140105011409030708100c080907030201090e060d05010c02010c0e121207080f0a1805102111070b15091b0702060412030c 72
    0x603106039600c10201d501542c4180804264407104680d03614200b1f09200001d100b80301e503a10720b50b20032406070b080b40d5074011081c03003202d00321a0010701c1d2081480c1c03800e10081003902281803030b60b4001c3c1704950205412000769294030880c8400f40c9401480142503500c60f43d51111100e0410300380c0104480d40d5561031402d509000d8014074120b801c803140000904060741164006000844a40a03e60644003a040041c85542d129081d0080007179100b4001c0c40300050825010b406002c80308580c070007090f03200e2450f0310303182848408015181500d0b001082441c031600444081c543c4002c1094900000400001c1d904045da44000c00d08040d280d51003405d0443d030080c0300d201c540c09a8211900c00c85501e103800c021180c0c031030843d8a01041404240310001c61015081000b0a80500e20500d80c050120303044007803118030602c0d00d20800c83c0030540007001c401c15040180c0c246044448821941c00c12a048211000301c10140017071030b01c085c012500d082d403101c0c00b031046a249410103c000880907004042 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 895988309 1250 895987059 895987061
    0x9150304020307061b060209120a0506040312090510270f0506152110090303060f091b08100e010b0d0e0303090712020a09060609140307060f081009020a0c0204 70
    0x4c1900d46480f00a00580f01d0078100407040e140805016130740c0100e070740c210b10b6850000100000a05100725140146e8a160051715210100c0301030780030411824460820a280d80211148207078400e01400307000d551880c150380104007980003d40404c2d04000103002e9a0b20204c0e5605081d40180c0300001c102100b490414a040e000401200501d01000701031802a1254900704800d91621401c96420100010140780b9203230b05103404401c0f0500300401d040070315801d035008a0998148079020090562a0500c0d90280da8056503129215410b50102c1c2d413031284500d40c0f071034000d881210a5013031582c1c1c801d10005004c27020303003245110342000035916180b0341483c411118100b0540340694114540f51403502d0700c0c0c40f01486001d5000b120030f080c400455a41e0006203001e0407101404000c0c2c50f8907828010004511406295000350551800d81e415146c0003441404403070071640c5030610340500810031111074074080c20140d004000b07030001052014088c00501502801a91598000c89103401040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 895989559 1250 895988309 895988323
    0x1707080d02011503020402070314031005090c04150809070f0612150819051606020a0302060f0c04140105070f08031f0e0a0e0a05060f07030c050a0801090b06091503040203 75
    0x342560701d4103610f0040c442581c411042200e804030703001610703001d460030166140c418020344003c9100d400010004413a0f0b1042c04041621001e072003c6c0c4041e079a0320b03070400d005d00c5640503d240100c420740205046520440309607a01c40c3c030b814141d80c2c40700c0e6070301039000301030115400c20340c0440c203112014031340b400b078a102d603003502c54441d580580e2251600d0794213030319102361041e40d4080c04044603030142401000c02c81c10f5160070041912618043d62003800a403544801c070300860040c06020040303401c443d103d440090080520300710302e41c5420301e040e05407511503082030782403414400140b1041d0f0100d0785d000c03d0040f9090058420039600c2c500302d038040100a2190244003280c00008109005084030210b0031640003103000c1e0300140f0f01880e040d1541c5032202d035000c01000c500c0380e035041028024000c0382c5140a80d0982e02c060041d04103882042d9140d000d200140400140204010884405260440b40141d5000382085241000780780105586040c0200c5036102d40800106220450508110070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 895990809 1250 895989559 895989583
    0xb0124020604171608030f040308160f030b13020705100b0d11040b040e030c0f011406030a32031c0e0307170f0c0a020a09060f170106170708 62
    0xe032101e8541540c5180d0b401481d6641c440d00c649010071484030040318000070391459030f0030401280c2c50b0b143c242402038007110b04076803c400241c05500070940102004000c070807150300a894244144800c81c104070024400e0190240c2d11015000649924190610082c82c04070700503806030410006d035960544c182e51005450900440b02e0320544030200d00c00312200540d4000817140450301031050800240070300b01c0d149070160940000103001024210000d020180828008000d02988003001d10200200004813969601a04405112000202a141c5030080d2000640c00442c802c081c41d811003c4031030151241c00507d034000113543c118644c03c2c01c6021203002d00d07000c0901c401168000c10507200d000c5c48000800f41c119031095058200401c0f019211900340c0c980c10300f6100c0305040520b582d6805200001d07402040c8485001c280e4a101d4003803003080d212a00602040d0a00e49108401c2c030250f000e603030000d0740d5610f100126018070ac600140c0556600e980040103e6800c1c2800c2c2c6044c50080050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 895992059 1250 895990809 895990813
    0x50904030305070f0e0d200415061202040b09010f02010914010c09090603080f0c07081605090f010305031e040824010611060403051c05180d03090803041209030b012402 74
    0x5d003110b01c4d500c4490411a0703507840b003030804115401544020000c80c800d186513502c070f8101035641e0500d010f00700c0450122080303a61034000882c50080800d04038451400381c0c500c0311008220b00003041d40070320303a44600946c444c4000502c104a945903510402c04640c02012103944070b5990407038550740f01e413100003e804000d6080100600d56981d1101c80e10401080d0f07103216101140c940040c01382032280f1070003010b101d800c0d2080042c414600045144441c01003d12070040744000c2515a2003a168850590382d01c030008515202126601541c0203a01c0000c80d0080c00c4c0030800460031600c24444282c003c5140c00e01c1070348801c021100d5802008050308184200101c00780d18426401c400540182c202d0380600b030403651640c072b012001d24070741e4648a400c442582020306020352880c611410503c1d04008030250381c0c02c1d100b0074030300301c2c15a40d841e940640319920600200b0086050b1844008818005090a640103170f0b0325500d02c60049070036488800030185120071500d512980340260002038000d480 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 895993309 1250 895992059 895992077
    0x2d230d110c06130305130602070e010b090915190f090b0907020c010c080d0515031603020306041e0c0b0a080109111b0f010603050f37020604050904030305070f 70
    0x407141d54034001071142d0365140c407000307403442410700134400ca40007008810240064180c54840195a54402d4412030543c091004000180d15980f402a00e042d54001001d191164491980c103d90010588a00c6680b2018451000c6140880804d070000140fa02c4403020f52814034001100040301c201c20341850190700008100501c80346e001c030302c1426a49007420103807801301e20303800e150740ca6005484284800c0c0745003105001690766250008071150004400311114880c3d0f5000048059030039100c003c0d00b42d4407201c04500000c441440380c50502c2e540b1100061906010b0302e541280b40103540c4940312030b1800180182101e07070300070340c0c041c007420007500284484100070340e1010039481450404104040c4081407850980b000b8007880b41081c0184000340052500c90070140d4540b220005000301910414402c2c054560048882004a00c2401040d40d00100c88100e84075101c2c80208040744d00040c1000b0100712903984801ea0b501942c0a950b0002d842d28001401a2642034021070381014414580c1d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 895994559 1250 895993309 895993327
    0x2040e09061b0d0f110409091101050f09010c0f0204061518240e041b080115020a030f030626060f0411040f0b12030c06072d230d11 58
    0x42c200c5603060901c00340040e1114003030441d400103042400c85500310900009002804041c00c1e0045079200f0b01030062115171050300700054519100e140102e0503401e4083c4103102140d0f0040d01d20110190040d414081c00000c44d6001800b125015001010b0300f46960071100310703c40d4040f41e1902030110100000f107040b41842e1b9000204059140c0c484c0f801c0150b0180e10910343e04c50f034080b1020b984044d00034055641003503181c10f4044a00c01e9144001150351000003074004080d4603011040c280ea03000340c142c3d002c0ca80c90407281c050300c031400d080626403180800038852540654002c0309401c00b0007400c9685907105003050800101034807030b072100703602c0b0b00034040400c03586656014480d600b20b0300090340001608041c00609601c0d480a40d2000d90080b0465440d60048000c0244240205c1560380503501c0700c0302a14401d801c0c41301600600c207a048260152914010003403002c11050800c1501c01e0301030352001c03244120001d402d20300b648001c2205980308009010b0302040600c081030306401c010180c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 895995809 1250 895994559 895994611
    0x50403050c040b011710180b1507080403080f07020f01020f1005130b0c03100510050d090c050415030b061509060904180305030f0708040f030e011202040e0906 70
    0x844006072040c0e60301c5003c809940e02440b070821805409200c14841440d0401855440071020301c118a000c10300500d521031462080d00c500c440b40d01000700b0b0303411800311507901c4e0711036508840300441e1000c0c010400400840c0302c42001d000e0840c0354a00ed140e84203034078814040200c00e2031203040d06661113100d031010304a074017080c280c407444003411001076907940b007400f40c41c001d035141c0ca0080d01915030f020500080d8800e600080d8031580c0400c4d0b00700c01c11a45c807024414440b0b1002c64403400104140094006280306270000f080003806601c40980071030329100003070102d035601008030602004180042040180c0710140c10351120040301e02c442c600b141ca001e000e03021300c1603114652040c01c1c00030341001c0969031940403038401da400640311a01c009181c50068025401038a64a00548580002494003440340c0c241c0d51145134041e0845001a44544d030980741014a4502c0b203051248035006030601d142e07039201800081c4050300c1d1843d402d01f0195001420500d000c0d0280e100d059a51480034107082e00 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 895997059 1250 895995809 895995823
    0xe060403050309010f020744150c040e090a0201030e16090906060801060f0e0901202a150f1b0a05132601090b130203160801150605040305 61
    0xc203080460740d64043d920220300744007440e00b1107402c1411081e00300c400e080c28044151454000f1440c2d151510808840d81d60b0058200400423505901010607544440d10240c1c0150304101620112414035450307050004284004480085c0b49070b01c80d50b040015980e045c0500c000240044015002000b000040b0341c070400540d00a60001030b0321528900300b080b07a903034020300080049400030440c3e60b496064000ca4030fa40351040c201c2031031021000c210300c10018800c00c2204803c4511090341d00c4900044207070380da002411030380c120340444421240580216041506141c1c04800600b12070700707101c1c0078104c08040c041c0108005510040400c00106400b0781c0801070043e45c04c05081d281c0000c1881252140700301c41d4042e82c0c40b80010b40c006264001800d411031420140a4851310030700b9400320349400c0701c0722064080c0034031000c80081003502c855000756417045070000d0290341c02d410303c0e4004420900d4103684400001c0e0340d12020506000030307184c9888041c008a02d400f83c40e040c5540c58070350356505 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 895998309 1250 895997059 895997077
    0x1c0e0607020a090e1f0203010605030f2203030c180b09010c0503040f030507090c030515060307110f062502060408090f031c02120f04140324070e0604030503 69
    0x18000860000395510549908020400844103000c1d051080c050b00e07860340720010007800c0d052a5901d259505031001c0c0252410713aa02966070504580e980c1c1040550001d0152030351541100220000c901c102c2880200505240240c5000c1030010000a004040c800700c6100020f50500d00c1000b03218018031401102d505d40c200b480d00c00c98401a9040c00c600f507108541c45003c41500b0800000100003011032030030126003a00a0802080321400c0b030540548108440f003000c0d80c0d42d19024000c6034030341800070719000780c1c0c54500f0b10b03841d41030611038900d0400c00610496180e0b02c00c408000c9014881d8420b1851117514a4200c01000e9034501c0217907a506010344001c1a4010110309000342d17458520900921180041c00c8070700002d235881c84000d0782490010400010702440a41c0c1360094000001c40d01070a00340d400103454286401c01e201100700081218517410b0250f10400030050102851000d100c01040f4071180c220300b06604050411004099014050078090004001050000c01600d1000d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 895999559 1250 895998309 895998319
    0x303080903040605120907272007060c020304051c052e0e0a02090c0c0723012a050f0c0907050d1a06210c12010312030b030319021c0e 59
    0x249a17801c2c41428a0301d642c01004104903040d000f02c0302c00c3c5450348402e032301140403030042000b03c4016455200120340f106500144241c1081584000703000c5074009006042c01d817045e00d04154a42c0009120121107100d40310b80101000030800074041e091010b170401d90168a80c511500f4000014503202c0302c5d0128200415680c1c442284400e018180044030400ea40144612018904182001995040784d84102000d02c1000d10111b45000c100410500f024001c54a10344c8030705100d001150200e4101800e07002001c40d4810030030002403841c1d400d81300d403841440544544104c0304001e901d08540c0710401e5106408503018002d50a40007812250384072458803001c5010746041c0c0c0403010350110108445d421940000e501150042c2900905014070603250a4070140d49400221082c02c0c0607964410100f0070111004100241602e14a00310000e0300d4240425041500c000090440d00079286200a5810030784194100c00e505102d102000e40e04018100c01d070114020008100035440340c0074900075 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 896000809 1250 895999559 895999561
    0x2031e0901022a040c030e01050a090521040905010f0510090b0d050403030902030f0c030706020a02090106030e0f0a0807020f0415030201140c070f1403030304031b1502030907030308090304060512 86
    0x1c03c03195024540300950290003404564803404000703004040f6007503800c50395442c19000c1192007400380513074852550000c0050055407410380c4035004880054441d00352008003000001401c4245004040c000d1294041c0103030464031341400e0042210f0b010380346404000341c034901801144542e00a642c10150383c000700040c40c1c1d0b680d29040d030080002c150041d501d449074010390721001900181e03a040c0058207500361280729503200002d0341e4444803414001c0d44084a0001480403030b219501404907060503008440410245060f428205160084140d6038079a0008a05c4103604000a10740e89011007510f08000c543d00c100540c980d02c403c42d00000741040300c4854504001982c801c282d030110588038068030746480d980c10907030f03030b01c54042d11450b041e401501c400b1342011700e404802e0324401c41d01030725130244c0d411034201828503e4000300c108482d51007450796104400c1c3c110744046d510800b40d8200070550309085080241c5184001072540c402c503482003100344400ca5101d4242c0308010014180c52600d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 896002059 1250 896000809 896000863
    0x130c1d01180b0d0b011e06020c10031107150b010507052a0a0f14030a02030618070b1903060f1505030612030c030304030305090a03080402011101110a02031e090102 72
    0x14111140e1000e0340b051681003d1800e0000d503403002070490743c0407003405030314240c143e441c8140030b15184500741c050f0b000310058503514100440c1e079030500a01442e00040080352000701d9600b5400154046d80c1c40e594003262001c2c448440c0c40b4081c01c0349800d00b0f14906044a65444a50311100781d40c204900840302107505001c1103c6500d081405580107250030601a11035207200c0c400e04c41403050030302042c0351401c0c10200d810045208030344c140d005009407200d40d0b26207602140c240480c90b001001445a0240018041d101801600000f21420078444242c100306800909540f0b06400a00314401e80d407204001c41c0009001603480912181401c84d12996090b002680411601046200f640800942c480c0302c004080000c40c4038078801e460400650300d47c002603581c0c5550250004004ca410341c0040740242d030048421102c80340c00c0000201c2d0744080001078101c0c40e0006045540945d10100d4107038410003840c0d103c480ca0190b04228107003446000b4000030750b11000100c50124034001d004201c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 896003309 1250 896002059 896002061
    0x180a0c03060903030f020a0c0501050a050c190e100f020115061d06161a0708150105030a090c06030b1c0c1e080a0503040e090d02070e090f06130c1d0118 67
    0x1178a0044144215140c140c07102d070192031a001d551301100c09529000010b12402040e22503180114034203807d483c1044041030a41072200081441082401400072000e9001d68030103100c4618007003d81d6035071800c0ca4030340f0300107070955100b4140c1502e1071000780c1061102e20741c00703030000d000c03004130300b2270024261080f00203d0b02c24416590b4150720004094500d009203d215480d11980d50f0000c0000c50081c0c1d17030b582044600b200c0035211803559002c501c45207a81503201c0d03405190003840210001502c940b00d540d8110700c0c1d9095500050119481d44100ba21070300d4200d41401c000c15064000c40c405000d140d86d02c0718032402c42d01540c0c4801e14640303026040303402014610f001401114045072544a02400c155950f40c001c1e214060b040791204000807200d01d00800d00e208200c80030380040800e2402d0110b41d0550420040248006105d009408080c5040800c0319600a50030744010580c2d105803410141d5050046400c083d8211702003e4400e1020500004010704441c2c1083c085030130ac0d240019594 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 896004559 1250 896003309 896003321
    0xa031d040b15031f060504091509050f040224030121080d0e071706151c0303061401020a020a1a0f0409050703060f0f030602250803180a0c0306090303 66
    0x380c002c0c4000c14040c501101c080000c40c000c2c85032081030311070083d6100f2041800d450501408000030700922040200001d10340100541c0144585c1003180b0645440102c1c04445e41201c0b074a0960300380d001403000b9800d105008480782d6641e8a5074108220f14200403082510041c440d8503560f910703000c40d0081d10402d40803107508040c0c3c858003d07030b503c61603000070202034003500180d480b5500800c1400a40042840902039a40c0d00c010003603c82940e5070301001703100f8000c004405810010041024800300103400061102a1084d14005400e5042c50849442c182a55400c40d040d90b0200b0000c20140c0d94409451048401243c0c80c0740004605c1c030010000341c01245450300c2c883c400130402099078145600720b2845541c03941e5041045c41eaa905d28018200c0d214458079590a00280c000c4c40460303810b4000f042100c03031140f010b0340f031101c2810f40181000c0700c8007004c0d0f40d10400801804100c03a0340d14580141c0481c100014500044642c56010081c3e00d94880207040d5541c8820210400d03000350400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 896005809 1250 896004559 896004581
    0xc020d021309030206092e020c0c120f010f02160f110a06030506010e040501061d010516030f12020301030b01180b03010903050a200c0103150305061005120a031d04 72
    0x14040c2c81203501d0040e60fa1202540c603a40180034810303914030f21800400d10740352108420540387d252000a00319000c000c1d8051000080e59000b0400d004446480d01030f60300b00b03554a140b0081c071035a40c00c190fa99003100c0040700041303122401009980340740c40f08000080034190b04200150740d140d84502e440328000e0a690b40d000d400000c0c4c5040014415010782c006880348000b80c0341d0708140180e5208100c2141c409000343d40100d9041e4447e0443c01c4103c141e500a05141810f110f450600c40c0c44001440008041c0c00b00e0004e04034a409000055000c40b5000c07106002c14415821541966a6005200c405020321110150f0000400500314426000a040f1a2024008004039000c90038000c01c00d62204011201003030b1b91410001c46142540651010700c01a42c0203072503801000700044020b000c6282003041e04424008010020941c144440c1d8042c0303441c0c0811050052400003030000d60603000203210303a250415060b46003c29000301a0032130000a074801440408803620015000304507050700 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 896007059 1250 896005809 896005811
    0x3020906040e0a050703050c0a0815011803080301050301060f031a0a0b132a0903141e01050a0c08010521120406020a050c19350a11100c020d0213 64
    0x50003c560b25079841035008980c0c544c2c041c0304540d220100a1094030410fa060710001d001c803030000322160f90a98030f919410304140b501e02000c07064050003490b41304c0703e80c005554001001004111514003482224000c00b4007060302c0e0000d83c07950b22600180c3d091201c080000c2c140210002c0d2414500f0360003280d1b5104010001c02103a840400302800501d00c012800f411703080c0c410307011103814400101d0604429200c0da254001c0383e095a880045054010f054043c0700c0c41000e065041c01d044c51050210785000410001800d8541803450074161a446881da00501044200622541c5c403400d190100303070304541c10046490050350480328503000c14108142c2090501107004182594042404c0700e000b030096048a45100b060010003803016a070752844007144c4200e1804008807455024000f007035420007a02c101c84030f10070004540290b04028001c1000d034000107504420030060b101c0c0324005100949001001001104024200d420b1b08074000c1d20510342c030304141d01199240c1c403290f0390021890030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 896008309 1250 896007059 896007061
    0xf0903010b1f08071b0201050705010209090906160306060906030e0705090a060e09010e0601050d110301051620120c01060b12060901230915150a09051f03020906040e 73
    0xd60040c07040c01c2680b0703400241c080000c141014401c4d00900403040c6903403100d00007064542e006540e19030191000302c845540901c2803001550b1180d044500c100080c0010340030b02d240048000381c00c00c0800d146c7d8000d140c5800c509104013644203060b40161403003810005000c050303045900c1d1501c1c580b644140d41c0080140304111007140c480d04030705d01315802c1c2e000380d50711520b407040740a007603aa045101141c2e6501071001000300c1c0c81c0c03c80a92000d03d001c0c08007204280042d41c0400d0035608111214004103107105040301c511039000c60014110303254000410009810f111190307403241e0350300c4250085400b0205481f0100d490a511840c0100742c040c9031a5aa2400854803801e80c1c40104d4525115162600002464520400010140410541d643c8941c043d41000b00702c1c0d04a0041e1425800c041c3c4c821a072500b035159212550011400000309070b4a41c11481e0008001c105e054024a0190b540f402448084c0990b9a0540e00e13030301c24600b000350700c0d644200081035590140da0f00c92040306117600 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 896009559 1250 896008309 896008339
    0x3020f012a0507060609020a0f02210703111605090c0c070e06130203011503060e0408030613140f0a0c140f030a021201030606031506060509040905030c0328140f0903010b 75
    0x1600600c12541649c41c0d2240c00340309044181d8030340c600102032000c198144004c0080d110400c500074604180309040150b1000c3c041c0920b2868890111800c00d2502040031081c0042e18003151b83d1507224888110551411420380100d82c1c035100c4034818004c41d00c1446d40031846550360380b891841061040c0c1401c40d200d6a550080483c40c0f075400b9050700c0402c1c50320001003900d003070301d01240d0f1045420100c10391454542109100a4800e50744e000707820550b940d1810194150f00c0325400307000301e645c20310400c018103291904034110380b0008007907003d1210b5618130300310316290001070700c2c928400e400701103459a0344c80700740d00042d104045010b0001c607503000022040007000d500540999010720904010719140d40003080c110f031801d010b030318040740d4248003180240c0b0741a044095210300c503200f600e00704841500f14a241d0b170003401213081d14481d1340818004105941400c070b0980e04941c50102d00c0040091111085071280000c8041051800074200c80d80340c400f500311104505024001c1141102a4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 896010809 1250 896009559 896009561
    0x30702090411040c03230405070b0a0302040b07150510080a0807020d0221011b09150228060e1506060703021c03020c010f060b040b130f08030703020f012a0507060609 73
    0x10105921b6641c40300040c180c104412204144503590040c02400b0250074800d0564050b0048000041095020003010405c0f5580710041c00d6501d2103103802d43c81d0394441c0e82a01c810781300028003000512444100800074901e00041150300b107600112016550111030005c500700c03454002c1d010350002d03c003208000518030030690f5a00748520800017000780e454003c009650403d10f02161500150900000744442110f021030024007682d5801101c0d00303041c03000a924040c0d049400182a8a8404160300e02440703114050300f1007607103900020f010464511a0340030050103000d04014042c8002017144000c06008020206c500300414030601000e40c0e040790001e02a600c010f0b0004959401c000030001c5500080c0a80400d1380c2038020000d0400c1e0a00190144c150000700c0810140548a1000584051212402c0004e804080c0280d55204070500f00079242900100444606a1519850030001e01c051241c2054512481c101550f0440c0708010480d59405500b40107058180382c0b80c0e00140c04030807 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 896012059 1250 896010809 896010821
    0x1504120807020306150f0108060d1502130e0408030711150f16081512150a0209040506061612110d17070e03030304080d021606051b0c030702090411040c03 68
    0x2c00c5044407001d685081c941c4201107501d02d00d0581020001c402c2200a41c010801e0300e9015401401c0452202a240c0350031038101700e050700000a283c0d00042841e2010340e45601070001d402c25a4070f50307009050550720003030148002070601e810010052810007000d03c0901a0300103000942d0824003460800c04103114542c00c2c103580c2c01054150108440c1c00c96030088403014441d4440074040200034001600380450300040c11114002c0b406104d08103416901c460003142d01807a180d050050300c4c0d40c00801440102c4401a00707940c0700740000d01c080310f40c080c03d00d20484030503a031100024200d00544407050303403c040010220400e0307002c0d880702404459840b0b10142800408203144a0040e00c42d418156031710300b0385103030003a0190000c0001902140031103004000c2400d561100500d005024040002581714848040b030300962a0420b2140c4540c07524030091810100c210003614020210000956034440e441000f4000d802c220001002e0100a80360b6065010000c3c000303004c1c6041d012001802444 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 896013309 1250 896012059 896012063
    0xc0e01180f181e14180a12050c0a050f06090606090c07030201110406030504060b01030203060319020f060a08010e070f1706031608011d010b0a050d1e241103061504120807 75
    0x800c200005e1240c00e242c04c429540000714006050205519113070381c40070862110441e41484002c20040c0e05007801000410403141c0148007030070070740880c84c04040c1400c3c0007030101c280c0c69101500307101141d40c4810b80503802c6a40d00c982e866907103035549016400340c50b082d840c0c040c1d820f1021030009a00d5400d81c0125205600c10344080020f0b0414500550403400151800740d016840b100d030300618200046000919035000805100f1a0000480011110b03481122001d0010300b242c0c00400103070401441040c0c11880d5400c00c4400d0b50b0141400421034008003400b8a2140031080c00b0414989043c8140b040501d0002c2614003450303180c6c11080c0c00f0b440c0c82d618403502420080288840e07420184120381c041c9400034130116000b4502010001214184401aa40301443e4002404a031000d9050f000c1c0c210700c10410150440910740386d040100c01e140881d02a4241050010300f25400240112940705504540e84840f040c0c07030308140b42c043c2c00740d904080192032000c40f0301018040b001000e007400c070b4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 896014559 1250 896013309 896013341
    0xa0b01030b01030e06060103021809070c03081014010309060e0708010608070f0e0f0612060f0403140909011a070804030803011a07110607150c0e01180f181e 69
    0x1a85070320044040f40c0428080201c907810000202d4844e45c400c0c0c0081c45050010010408038000c148009180a201070301c0e03920100322411270f40402c041d0403603086588100c043c0c0d985507000d8a407440184149000380b0b401410180d035141c0031420068690b101c0c3d2003000000b800c40b11402c0c0c03540540c0b8003c0540307008400161164400000300d60000b41d41c490280c50940080c01c00648406180d80e581e040050840f81d4400c18800031012002c0c41040300600c5410300242070b5040d800c003812701615440a0100c4403451410801040703000713440e000501411102c0c4100b595044140c076011403c40ca00407a034005004c1e0100040000900c441c2c0c00c081d5040c5e4100e000c4880b8081c9584285c81e0640c801ca507802046001c02c00c0d500400c030301d400390242001a0161127035005030151344526104880c1187c01c0140440c0782125040c80559008d218001246d0f00e100400d04600e00744014110a449144100a5030440d00c0d81488081226508828000807540c04402c41584202c0007800240044689400400c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 896015809 1250 896014559 896014571
    0x1c0e0118031112090411070f08070b1308120411120a120206041205071704170c0907020c0f03071502030408061024030e030315030c03032a070305060a0b0103 69
    0x410046040f1100c0e80d090300b80c944c60700c40700c1420300019103011000d0b0200349405204030302c042215115044102c5229442103603a5211501e4052502c031030142c040c96032510080403041c00076030413504451054081c0c0c00c80d41d1f495a11843d200c01100a1a00540e0300000714110a0026800004035442036a1150204a00244e141c102c1241c1e2807800702c4000e00b014030851003458a00d40501e00504809020301822504807801050700b5440c0d6004ea8032100b034403643c100122442400520103022055005c0350b0228103420000c400035512440c4402c194402d04006040845036038040100c0c10043c03811800c000620b8606500280d120340051041e00750318007070280002c4820700d54070b281c1d0059803120a280442503500c80c500221540d800d0398140281941c038000308903450410005035200e840078121450525000000741800e1140b10921240203600034002d0018030107040c0314811505403840f4141d5624900240032600d020003592001d0070030300030b10781880441401c0d600500a00e120a88003805a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 896017059 1250 896015809 896015837
    0x7050f0717010f1a011404050d03050d051f0902090406090c02010507230d020c030c12030a1a030709020a0c0b040506100602030a0e09060f120c01090e0c1c0e011803 72
    0x280c45180d50410032104044d80c8000140d0b0041d2803406141100703030407680c14a17440c2d00115040d400030800503404100b020500010f81d20f40c1d80140c070740c85120b0704903180ca40301c10010168100420340c0074201c0d03030540104201500351110fa002d44010040780d4000e2100c05c0040e5000b90081c0303415541040029102910b4500344030514600002030076032944213901d814594270000c0001d4106d100e244400303000402c140d80b0030350410000c030001804514460742e0390342040d080800c00c440102c80a6006006280d000d09802d580200341141103450782800541d5407401254122003903c0040c2c401080c400304101400280900041c04612071002103d5a50545889030800d0340d582c00303154101000140c003c074803441242800e6180b19040a405000c40d00b203e401800014100494a078012115a204550400c095030380040c001c0010407465200b20414202400d0741810343c401c1781d1036548103100e80c81340d00300a6010f0303602143c08240908020000116580a0343d100c44c1295281a0700242940307604000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 896018309 1250 896017059 896017061
    0x30c0a081209031c18120305091c1d01020c1c05070b031521010e15011d0a050403052b11040f0303080a27121404030807050f0717010f 59
    0x1211400020010034113003180807441c806031000d2003924007448110320b0103c0004103030003103078404103d4a4401180b1403034294001840d06000d42d8981209980b9014240200b179004108002e0f5070301c0814444401c40b541e0b100503842c1400001780f00740c100e400c8559440c40b012084488440c990300c144d0a9030030941e685e9803a0030b81400f043d100e5011240070b601d600500341c44c1c10303114100000c0000c8100c1050744500d0900724219490b80c3c039404100e40103807006182510a80c8410383c05040020342d2215490320511002c827080b200144031482181c0e94001113001e26002d01c00399126401010f610f0440c00201510800d219100c0030483d4243c40d081c0090800d1074030000c0c0c240d500780c44e2408203464141d880e586080700c407501c0203440c0745007a0343d131119065010303a080c10048502c640440c004401003c05490200c003800400100314040000404070108100002c0003200c04603600403c8a03a2903210500701541018140350610103980b0800c03d00040c40206104801141c5595000800a000703110002c44 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 896019559 1250 896018309 896018317
    0x7050717040f051009030506160207081615021204060e03060604090809150d0504050601150c03050a1d0301141b0304080d0c02070806090601090e1518030c0a08120903 73
    0x5200e5800400148004c3c10260420020f03a151860080755060f902c0d181d241c10b011b03056448001502d20301105400b01501000b0500081c94503d00411032000804840050380c10f60b4040c0490781c1c064070100c004c58600c20444403445404403261259615074030600940807200031000b69010b0702a81d0005035440c6420304c40c1c1149150403425552402c8503900070482001b5400d0038184402d8001c0c46284402c0450388541842544604014a5107504121280c0030000082488004214458a121001030750000959900403c01d0421003000c01c000c0c1e9800494038072244520350158a006002ea9000c0d00e4001154060340c140160744843c0314017010b901e8440c0c44101c2c0c02410f01312040100c0b400c020f020394440e088103005481940c02050f201d1502074144401030b6207102060703000e2001804150401e2140c0d1001c00d0316038004201c201d410342a07d2590080092507014048900a89040c00c0042407007120302696407070050f00c03000882840d1480107034010550314400c030795941001801c80c5400000711 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 896020809 1250 896019559 896019569
    0x90605091b22051603450b04050c0f03030a021b06070c1710050f060f01050f0d090c0b0703090902090a0315020903010e011b120b090705071704 63
    0x300809051440500c604402520000c1c400d02c90185103400c00e1108a00c03901d13009a0792616a48080b184001004060b20940e00e10031851101c017405808080000c8001691400c0400324400070440c0401c8100d4051100c40c50f010340402c80c99410041048404569201444002c40e020304042c0d52400c185030f92406941c040780050307031091141d600311001040d048060340a0003000a40b600f40c00da5982e0b1160031080d884a84010780c1e40714200e0b0400c034140440898071562550030070091500380c0302d0300290740020b01040d018030940900a94107910400846103070002ca0484940e54450710324501d0300524030310505403110305070342e900400d050031504221181e19416076104d80c0a14204554940258170001e00198007844001d400800610803001f00344100401020051b10f07601c0310b0f010f050a41d0040d0f41c550f55142d1500300c0b032103000b43c0f2402a82445111500c0c1010090303046c03441b524010840b500d00e107940540380004024540303600000500c045c0c0d109042d1502c0c1c07030400b80295015801035010f0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 896022059 1250 896020809 896020843
    0x30414030c12030901391707050901200a032003030f070513060807030b04050106271e06300c1803060b0f0a05060f0a11030c0109060509 60
    0xe080e5082e228402443e041001e20000107401d0b0882d240140c0c2c01000006101e9941c00781c102500072407400340c1108040384900341485040160040f1001000640003030201052020125040103036911450302440d00914401c0c0c1904c2c01244041d410340c1c1e8038480303074044001074240c0201d4140d446c1c0d41029540c1c080e68400040d425511403070074041c1e0f41c4000030407502c1048400e1106a000c400c8011614004080580340c44096083c00d05005081e103029501490096081c00010040c1c2c592104511320301000c21040000c3e035490103840070340d00c4159903001289412000e0940c000014903000c201c0115441510f400c490804844d101051000c211901c5002c0300c031959980000a000759045000249038902e004010145480c03c0059029150b4200382c0e01c55a4a80710400c0e14148802c2240d040c00c03007243c074032545c14034010009100340314800d0450006c00380483d4158103d401250300b02c6c4034000b240e054070748079103c0e000110700a08004000752002410a400314003500404600c90b00e0748105892 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 896023309 1250 896022059 896022073
    0x325030b04031823010c0f0204110409060305012a02120a031b08010807051e040e010204080f0a02040b04060501020c1005250b010501050f0712020c040c0302030414030c 74
    0x200e11026080c01801035040c04985000040d00c1030707560161a02803c500ca10680000110701001c0300115001100c1e64140030030880d51b40c000c180b000406210b895070440c0c004c42d29030900c0441c01820300641d03105015850914001008000c019086844540e19000c0c55003c001c1c480c41034901d50305002089403015800464510000c20030002c01455003400034100414007000000d8800d4401c103251041400140c0a03400520102009025200040404031072201c020f882d031050750001407072034801482c0300765991207541120350001c1d01550028411282510b17000c610b0521040e8450840c1c1e10101d101c4c600c1c00c0e02591503803a10344164010f0701c1c01070307008010151000d07040c025825550100c1e5010b000f0240240030108012005100409222605d481d001101320316107070a0b0b01d601078001c035060207803c5c000480140b203243c0c2508c06580d0030194540007c80102d806130b040035400103c07550801e05220405030455015002075004921400e41c8080c84045018003d4983c0140100d40d0301c160080c00b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 896024559 1250 896023309 896023313
    0xa02150f040909052404051c0207090b030f0a080a03050c030c04061101150f0f0f2d080109030504080c120c0f040e0f150c04050102070306091a09010b032503 69
    0x54805110188214216443c1200000d20080084218144a00485d502c1030400040050a00403402c0701d5045002c1c59003500d0300544069107850b514041c403503040e541c922429071166801c1101084400c410010b84e00a50442c0c10810841c1c1d2001340c034100800c0c103000c04110040e496000301c2e4403500080d10440e040a003480000c032100600d0301411107856403501c80d120440340285c82d8207801890441d140510403490702070400151291684a508a10840d000800101c4d41103808140c44100782d0300802c80203140c201440041d12180d8006103030b1076192548850802d40c1040040c426a03118508440d40640d0480400190b2100c42208041d00d03080040071580701c1c103144041020000300108040b41180c100500507180c001013940c4400c042c1c0c08007214240040c401c15a098000404100b101d250604101c0041d54414461100401700e0b552260790500748074010300302c10315100c10710a4a0040d820070f949000e0285c6052141c00f4828022450031000c3c1701c900020380394800303040c4803020410f50314607 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 896025809 1250 896024559 896024561
    0x12150905070315060c1e02132a0801030209010302060304051006062610060503151e12190f0c0506070f020114090a03020f0f090406020301080c060702130b060d0e0a02150f0409 77
    0x401b0040b41c0004460040c0f002602e03150245900c2c91440001154000d0b030923075800d650a4141c1c030380e401c0510460000510244e201d03c0c00203419245c041c1d0f411030381ea4469251243c0740034008c0701994a072620f04600428159800302602d0100e050005c45110401510010545085404e4481c1240c4c000d4006042018500840155074081c07030003503030706c3c2e07000702e000f00400c504808070302c1306240100c011a4404014906619881d14091150004003003000404104819003480307200081c05004000952200300000c04048402800002c0c05d030b680c0369070082c42c2c42c20f10f45d0721f1203008a000c1802c04640d20121102502969090207008003030320b81c00c0f0318640074001078031020340007035411200c40d03408d40e0400e440391500240294800c0e08016925894000800c0c24101c1416034544a090100259405a510301d006400da98843c0d04000520014000c00280c240c40385091039072006003800c00d1000b80c44008640a18200e00a40d82d4540c0d12120100d00e40407445540f03c1c61621501c103020a01c0841c1c49 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 896027059 1250 896025809 896025863
    0x60810110a080901021b0c040e06100612180b040c060e0a091107020603011211010c0201051c06030c0609091103010602120c01091a0a0e0105060112150905070315060c 73
    0x2076400040c50000304118109402002c0c0406e04d000e0b501401c1703091041e0600740308007002080540d0103841181010200021005040d00c90310041064496040368000c41c154880d8001241100755a8180305003440d081540300e01c212015250a450400001051401440740001640005020582090078414007100400310780024001701704040c00004016250500118060010310401c1c0c8290401441c1907601e00070898402e50410034002149c10050b42c2043c05d440865600f034030200b204105407401c2000401182c1d1018042c503030704050014006402540c07000c203a800e40d20090200d55040c1c000003903248001c1c850307440183e2107400c00c1400e07000c6070400703804030751a00000450b084245440310744046041c80c1c5c0084400011109210228046124682c08a074489000b4002031911300c1c0007070040000d20110521140d251503840b000030040d000c9a41c007504904074100301e50300740200010007e00405170140e0510b521600040760007402111a580d200e070307012800002507804a00f2642c44546 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 896028309 1250 896027059 896027071
    0x2502040c1e260901091b030b060105030a020c010f05180f06060409080d110a110109150f020d02030a1a0312030c0f070f1406060f1e01140a03060810110a08 68
    0x1c41c20100c80c1c42401c180ba000380184400320000c40c1d01000390805004c82c1c01040e403011144001d004042001441800c0d40a0b4400024245142c41c0d580b402c010b180640310345521303883d65500c0c0c580880300402590788024040c01086400d10202020a0300c0075655142095107640c440c0e0004001904504c1d040e001090007500c940e10150510410100c501c050700c40c424020701c4c52450100b0703259061540070361200420081c0100038080850035880d1a1603080c50201d544a142d500d88a0440b02004160116500090b009004560340e107000700e104002019201d000043c1c00728000d081011314039001403c4008042c003032507000d28640345e034000302c0004d07404071070400e501000511440c4027207071622501201e02c900540074060204c03a1400c890782401c40003000d481c40f4022051020700151035031510383c1e12041c0420294007000c03903c4001179a2030700400206001c440380000d5a85c0c0d2140d0300d03030440012550900d0449242c1200550100144ca079010003251501e0800d00030008480d00c24959650005 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 896029559 1250 896028309 896028347
    0xf140310090206190203120a27020105041511010506030c060a27150207050a080d0c050c0d200f061206180709050a0807050303070b0703022502040c1e 66
    0x30015000b000110601c0e084c6580140c2c00100d40c0c09501c0c0310649030706074000200013040240000840322511081c026100b01c08080d0140700c00c03001107902402c200e07000361030b05a081c0e00030300139040d04c011b041080c607122442c1603500b06400b151641c00e00042d90070841d1001001d560500410040c00c4404c124810a083c00c1e080080140103507a06454182a01408200b042034850549012003c0e1815601b540700500030218003508000c42400490042c8a25201d0724190300d00c0d21407818442d1400490001180c0d000c2d01244002003041b01c20721108882034100b40408586444004c10426205010508990081c0080156a102051100401d42e000070020702102e00448189007101c03020400300d80300c8007c40c804400c14000c42c40d2a00205008018041c0204510360420000c030b03480340580c040050401c0f81c0c002c040390400e40250141c403850b040381c20000328007000e118442d994020800130140c4c0140d1400407289011032140802c080e00d01c41ca10700d8a4104100110201d0b017a455242c0080d442c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 896030809 1250 896029559 896029567
    0xc0b10210201020705030d0806061e07082a03041703040b1306020d032c010f0903050a031d1b010909140627071d09100e011203020d0302130305060f010f140310090206 73
    0x248bc2a1006441030ba40142c401c503031950140c0da00846100e0f82c024140c00605000c039410310000c9400001c950a03982c01c864a5034040d201a42e1840c60360142d41c100b104054400305030744100c088408442821030784070390700303c0d8104c400c1c3c002e0a81c00c4030b900c00c03507001d2041451119100a6051000b0104d558011840000740da80c1243d00104211102008110001000041e00c01034065060286889044034106e080000010060400350f641c82c01c030126402c070105c0942390500302d83c0110048001404414418003c6c60120510050490002c0300c41074410003002c00d410790300c528410750301c2c803114080003a02d240c142c81d000c10941d81c4000080e40200720368403030362714040d40340c07119180d803405206408601e00c00903060030034210383c01700160422195000c0042000300030a41c0011111841c10f00c0742401691020400ca0801041c40e9039003010308248680028070500071051085141207500a40141d0b009036203d0003031051085100c4401d6070725038490b20b001c1c440f01402ea801031200e00d10060605142c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 896032059 1250 896030809 896030857
    0x31208010b0f0702100509190e1005090a0506040b03030a02031e0306100806190803040e010e09030d0513140f01050604021606020904020405041107030e100c0b10210201020705030d080606 82
    0x1005403c007080041d1030246c03140400000c3c10309c03a106604040b0701000f800c020ad04110110b00e01c2300d801482031000d00c0d00c90001c10f0480d160750780b01701c0d080940a0b0a4070341c0c941194a020f075030b0342c0c800c0d03020050140c40d41d44071403040740d8108180c03030084500501513a0811620304040b01c1003440540499403040ac40c1d0b402100c0b0189078200c1d08024001c0c10702664848c0e00c0e08159815042051b88000800d0001c00c0c10890f290b03101108459116415040000b501e441c0c003058040b0006400f40000c118900c0359400b001900c00004400d10602d0b1454000d1000e6034520301400164051341107100b004d4607e070040080064450b401812424101400041c1002c2d9920001004d8030305461760029400800148482895400710540b00d24101c01d888401003d814040020900c0e002140c0c0500310942c034801080146504019110080503c140b080c402e21640345031844041082103412405031099400c0050f81341070100c0c3e12a910740e1302e41c0f214021943c465080c0020344d84004110021b00c903241c40c40601c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 896033309 1250 896032059 896032069
    0xc0709150303091d011a0403050114040b090a230f150103120c110f010e0d060c11061909080721030506040207120e03010605030601031208010b0f0702100509 69
    0x120582410040340100d038903504002c1c0642c0c1d002d802c003071034450f698032000000341d81c49822581160070014400f010b003030702c9442024082c050360b00000e000c0e500f03103491000c0301101e01e014640998000e40c8000940e0b100c02ca560b41e83d490903c40010311580ca003405a040b030030804076120464611040c05d0351760960410381031074284070401401e42c030130505d6000180700380880b22000240b03519503420214080070180c0c8580500449502c40c4610ac0c44070301441c000741e40d00c602842c1520b1000a80000d8050440b443d206019064010640c00011642e0003070b4012050002042ca0081d8aa02d0b141405024600d140001a0489020070b9500f0038040258000240b907000c44101200c0d0880c010521111400c4001010b03a60007a02d280d00c40e038010b010310008502c0180618421441c40e00782280b1081c3e100e03010901600b45079028039032500540e0700006c02c1c0f1514200d02c42e07000080c2c0d600e80180380e0320f80300031240c640603000c2d030b403100b0020610500c2d0050604400c000d49115031800d0a908010309a40018 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 896034559 1250 896033309 896033321
    0x70315090c20070b041716120b0601050702120601090c0e0904060c110f03040503010f14060910270b04020a021203310201090504020901050904150302030a210918020c0709 75
    0x10101c4680f03a004c85030707981418440c1f21142010010404551481d00256101c041c80c00c4501402001c440d80124219070f01403021105a0380c0d01809104100140390841500c0c2e501c00d00c2a19403541c02c2c100300c0d6410503c00d040b1055082d4006149031805c0c0c450351551002064070000c09018031451124004901c14100200082009001c00450340c0f607040006150035205c078500c3c110201410860041e851402404641d80c0c0590241ca5007041540c82e92205a06600390f50320a401450140038010f02c1e42030400800703000604210407c2c01505030b43d00501040303210b01c00421006800c002d161519010414005503080302840c0c800782500403103a00c05901600d480810800f80215a0180c84215600400400c0041108540442c180082d1400103847c83c03240b149414800d540e81d49031240810f0f0384800720000f40da0003804032249801c90303151000800e8a1842d1000140107190310b4002e03117a22a0303c1900c2501e0f428580e281354031204038032000203034100074041d038440e00541d02d0100e00c80c0c0d81c0f48a08 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 896035809 1250 896034559 896034569
    0x80a0c202b2f0111130f030c15140c010c03060e011d0703090c150224150411040608010302090a18060911090709090e1506010c1a070315090c20070b04 66
    0x100d40d0f41c44004410168845c069000040b1000c1a440c10404510300401e214100d5103030314159048055a40c9e401c841c002a024005c5007081c5010411200c0114150f002c0385440b00d660310200215615070b41c015412080034072a04514400c01412040b124078269003060f004111402c011a4001c5990b4449031004002d4000d8100c1d012407510602c601a810003412240305544e004000340c0805409071210178000c011f05000e101c00700c0310082602501c03158480c682c2c0444c08242075483d5a140c0c40010001c02080c84241e10800020010070140301c40c1d4450348910303200244044141d0003187d9901000b905841d8000c1d00c08150004075106141c541420980c8600702541d10303d10002d040440c11011548506036080d126800000e452061030741d6884215003059007420502c030020300070324200a4602e041c0b03820003500c4c030060080c411a2601074002003001a491000c80301301e10303201c000c01000c1b6241c1006c000c0016110913011044561505504a642c00d900f5080e561080c1e103171407844400754080e501c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 896037059 1250 896035809 896035841
    0x15020102090a121b5f03010e071a0c0a15021209010f110c15040f1509030f3b04180b010806010501080a0c202b2f01 51
    0x30790707403540107a000380f03181c04488a100b4440c42d0b200618094040d90030017100091301810030b02a9061014044207031036030312200800a00610b01003000d515214051441984200e00d40008105035421900782036401e0184041f0041040c04003688038610790541d131103c021505079003000807030b000810701d0b003209200f06941400840c040100003c03c50446900aa007070350f80e4581403140c0c2111706d001058030910302407a0700003251161601d0500c0d8841c48001c4038001c1c00000d081040c00b0380c0300c2c031075080790f07103100d0181d1154902640858803e40710f480440c8525220700048981c01e41c1c13000840c400b1030000d171034010f25610a80c0940008202280c090f454040480020300340c540c0100301170700003810b01401c071080280c41c40d03514080020b8041d40c0003a055490381503c8080c40040c15120342d04040a8084030691a1003500b0f410804645444103003864100410326940051200035145686101c0b021407592403180038070390b0324003800390500d041c4c0c100c1071100440070052000710400d004400c0c0840e980c3c2d031 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 896038309 1250 896037059 896037089
    0xa0209041b051905190e03030c06240a241101051003020a0f080303010b0c100c11100e1e0a12110d09030b0604090204090210080115020102090a121b 65
    0x801608252040d02040c1c041007002c0044071074044040d160710010481d03609100c0111b2100400180c01c5009809020700b5a100e507808121000d00c851459007249241001e00c030786110001d07401d102d41ca8100340540c4043d040700102240010f071600304413050380c1c0403e141041030b9800b500c50850940e0b006540b420004007a00c02d040c000c0d844d0281c8050010104544010403041c94103080a07168001489508074400003c10481e400c00014081c4580b01c2c06548410058082607400103000440c41800c2001da038480e1845034aa207800600c40c240d0840c0310700b401044500200d0220031608107102c2155000c80c040d1401c10400243c5914800c0000300150315109001810b0b158198680001850300030100030f10407400700003003202c201c1c1e01a080001503e011403a262a40081070260103c540300035045507020803401000d07039104045a050742d0500001c122513450b00ca900302c0c00c2c2e00403115199031022011608029010018400071b0009104800b066410000365542048014050f4040780b10208212 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 896039559 1250 896038309 896038327
    0x512010905180f120a050c1f0506061e0f040e010b181f0e150a0809010609140c0a020f0a08071209120605090709090f050c030c0303030a0209041b05 65
    0x200c0d00c680580c642d070020400080d1030140303d41d0f1001810300107041800c0000368904000c0c0b0070421500c0040803401180c40c0c1482400c90726002c3c00303d51007120b24076440c002c0400d40301d2525400b101c3d000c8185486d00c0c0e5003010f803180d0049449d0320850a0b1207060b5020400060b6640140002c680205824424141c4410030154405030b072800103c420391090441c040030601035804c1100c2442501d80c00d10b0000303e01040100032a4241da04e4181d0300040f14008600c44000315400001103105a440800a014190707541c0c08003025641c80064403100c500d4400005400e40c0d003203001800907c0300b40e10445076182181c00c5070a04010a80c08103a0b105403002a01400f44020514902c20018aa142c102c0c1c0d60b520b00180706181d0a003c02001309920385a1020a01d070320020000b203030140250541c00c204400c028030340b1211101a41104454600440c8640030241c0f40206003c00010707009030203146503a403245210700003075111035240c55100d80d81c1c268000790b60145140c006005c4409885881d1f8640842c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 896040809 1250 896039559 896039581
    0x605100602030a05391614010c0b0a0221100b0913090c091d060a1109010c03110d0c0b10030c050d0606090e010c0807022406010512010905 61
    0x581203042558420000d50000c1a880002c8402080e1400b42080c2810404042c1d4640700d00d0301100500c2c03281c6050b40070006000e0120301461100c620600d416422641d840d03064081140c0000031034003003880310300080003003038903001501d41c018400c040c01071030480b004290350958107020700e51311801c40302d240c20809250b0341510002d000e401d50f200c2d560308000c070000024000021881c0307010281600c030b0f00300c0000c10010800d031401030f1108480c140402950600181c410851102d4503840380d20504020070040040b9215801d009080107402e03520b04801600191799074000e0b040101c041100a403271249110300705101d10804403074256039401e2404540e01b80303040b80d800098210580f21102100410010311008075410488030141c440808440d13103030611030f00a15055000780c0e030441c208014541c4950040d030104c0180960750300d0b8a5850b880c0c14070101e80d42d952a403140c2b140c00c80c1951070000c80150401c03141d58400c205141c07162070b2403d140400114100207034041d060703140d180c1040c42104451 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 896042059 1250 896040809 896040841
    0x8010504030201021e04231f0503090d0509031518060c09090114090f150a2c040c05040515031f0e0c090f061c0311010f05060d061a0d0605 61
    0x20071702d81854100410742c02c0c0e107c2c03c0c40c10303070f036080c64100215881d6032214100b10700490300305110010350103540b0102802550040720703103c0c0d1501510710700c118420b0241050f103100c2c1c80054024502c0b144802c3e1100f84044028007800c5200791800e02414405100700300c014454021602d050b0f841d5940030003804074404042c0c1100c0c0c0d040110310124100c0e5202c00440c036034041420001a8600d0b100d860100303184600c0065102d0b0440004500450b0003440640111040e07140400314603008800080e840c034200c50706960080005520300700130070040c5441e0f00240d0300841131024017204d0009000c0003034500f1401c40c41c2d1280b081c11412500151024603ca106421100358000c1c0200b51b03515400106d005400810a000c4241e106000c07030303e10307240c030598141104940c144144c00c0c0445c0d428041d0108291a605101c00e600703000559008200034010350740145030180c9032140020881e51450040c0a0074040c1078071801c0414105013450f5a44a201c0c43e000380149000a811304103981403c00c2d002e1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 896043165 1106 896042059 896042107
    0x50d030815100e09091c05090a09021b100507020a2003060103050a0c0f03150b010c0c12020f0f0a2106060312020606010c120e0a0801050403020102 65
    0x10700103600748950b02048943d01c40a66441812654940641c41040b07500300c090001002c08034000c1c405042c207408d0082400540c3c40d20380614408a800103079024400e031120a8807458411014010f160700c1c0c1d601d1480600c0545007644c1c019555107403c00c0000c0004007800e101e548000740e803510300102c4120060540d1191f580d84e00b0102c0d52050303070720001d84011488603c0003d141d07408100c0441100e42c00614079245440b81d8844400501d040801c882c180400c500001d800074850425180141490f0343c0d1483d0050a2070040c4002e00440d101094090318032294001c005568503a5400100d480102c040c2a044244801017103007110300d08c2d0014503840c10004080100645078426104109440d82141c2c520b031354450045a040368405400f03081035203501d140d803070b07517074401c4034174487c1540003800480c90140d9800c0003a084a80440f000c0e80140d5011a401d015100004200103a0b20 = true := by decide +kernel

theorem cover : BRFrame.Cov 895863309 896043165 := by
  have h0 := BRFrame.cov_init 895863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 895863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 895863309 ≤ n) (h2 : n < 896043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
