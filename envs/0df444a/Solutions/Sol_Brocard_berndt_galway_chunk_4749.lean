-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4749
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:36:47.849373+00:00
-- url     : https://prove2.me/submissions/c3602ef4-0781-45e7-81e4-14263446b2fb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 853956834 ≤ n < 854136690 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 853958084 1250 853956834 853956841
    0xc020a15110d2115030b1801020723071404050c04050409120306080c150c0f0a0f020307090e1e010608030f18060405010f113a030c0c0308131a 63
    0x1018806400f005007880001c110040001000404a212a00004010780712000100d910500c049007045188608100250b56410a41c40c201110340c1030020310407007549070406e118031503640100d6007100340d40d90161541d100b60300e040100400f42402501907042e0600800c00030606840380c0c040c500a150090b0f5504a03011601c2400504590082c0d06c128a66040a9618241a903540344a504c2e40b490520310103840d500c143e0603150800600b0ba8016020780324480d1136170104540500d40d42191030003181511185503071080712400f5120402d40c00d54164001c0b8040c0c00e0b154500603078001c04c20407800c2c000189562180c0610b07185920201c1078002d0001c000c84e08a8072003011214107101000240c800508080c0b4000010b0f004410000c0180e0034030540002c3c1e4401c0c5581040301d0700380c4001c1c06500034010a0540301d160101c40045a0700c01480400c1103400c41d1681c024002c01c00c0505140e66006d00040700b03502c08481c0305078003800b00300c940303a4044004000700d404040c51480d00316071200800501d05 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 853959334 1250 853958084 853958117
    0x4030509090a0b060a0804020616030809010b042307111e0f0a0201091215090b090c01030b100f12061707080c06030c0a02030c0d020303160c020a15110d 67
    0x441c01000b85096a04029905807103890ba00141d40340d0000074201700040f81c039940f00041407030184284030305100032125020001c0c0755000e48028080c2200c10000c100301400b00c0f0a200c180c070542001d06034140c0c100700c40392446003100d42d42c40d40d01c096945086028414903990f05820300c08180f40e4445503a665000503030600c64280050552654a1130090040100c50760000c0c10714245485251803414451004905205208a03084442c0a1100c1c00300700c045050702d0040c0d4089003e4a1001c5580f0409026a00550007445903040c5440001d000d460303000000c0404440c2000c2d40c040a0080066140c4080d45080c0d9901440002e044504d001104469070040c1403440c0403440d502c200b0b12940056502c04007a100c0c4000c903504804585041d0f0b68680032403505900e1071107030480d450902c1c441c106a40714015401310142d4000c0394a45d10702e010801986004545418180300302035400f000140c0100000d1a0809400070b03540814140050b0440e41d0305007544c2455442d0750000003003a1005041d20000703 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 853960584 1250 853959334 853959349
    0x2205010606020615090103050c01030b0d080d06141e06030a020c0601080312160504151403150301051b0d020c010b060d1505062523030702030f0f0a121704030509 71
    0x204000d0383c116840351f00d141c543c5682d4400c000c0f0501e0505a40e89440710b040d4841080c60f4641c241c003c142c983d078a846a52003800144143d00c82c002803c003102c0504c5119280619803803000d2035510403250b0116030083c0400646a20142c04591855420803881964103010700c5028000c0c00094095074a070020035682807a85400207101c08240803201e016084560342060589085e5140c500b0444103998180400b074a00502e00f110340242c01d00040200b0441c03000552080450356001d4009204c551201403111841080c000526040e800c1d06219444281e07000390701901a00d10741d540003050f01d04c1c4607400b10700140d100380084512643c641e44200e42c03002c44500701500600e825a00d01e4a060000c2d0300308103021110b415103055080105048009200c00003d44c00701c603141c418011807031072881c203019030340e203901a42089000e401250020b41c00c0100108000c415110740c2000303060103500c0c81c0daa1a003041090b080070414012541254941c1101c00c8c0c1200313101c0d52090715800d65809040f410050003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 853961834 1250 853960584 853960621
    0x5010f0c050901020d080601051b061806010605120604090b04120906020a240b10050405010915091701090b041a0f010524040519030210030e0622050106060206 70
    0x7400010080c0c0700c0c0907640002c000d00c6072111460540c69a80361100122003500c0307442204191000300d4020400102404a0051f0003840103000e0100c4655420541caa00c0c2c0f80c00340f082001280050044040300d41030071030000d6220320b004000103411030440d42c03020304104040d50142e90000e59000c01e83c0e9110340158401c405400d99000408518580e5a10b41d20b200030350380640c00394056142001c0105040715002422224001081030360019403585c0000d110f500984211400034150b20340004003040c1c40380c1091591407943c3c2c2d606011506120502080c800c0c0d503540c0c461150750b41c0d011440803071707041c0d5290390082c4c0c81000c41e401d0741c068044480e10340d180c018020607441541c41c00108110b50700c00d48000081d12883c14449404e000d08801d540d25030041c6d50116800c203007100c60713000ba0580c0303034035404040e240300305d17444000a070b000501201261401c42403440280d2000c408107035843d0f02e00d807450304040c0d43c6030208031512116907105829145594400000343e03103c03c06208a407e10030104c441c4e1f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 853963084 1250 853961834 853961837
    0x303012105060c0c01150602102409020903100c0302070b01051008070e0a182a02190618060614030a0b040b0c0f0a0f0207090608030319061205010f0c 66
    0x40500140d214079445560140081c0700c000780c00a1041003884080d00048040c0c2001c03036071b80d03803a43d50344c840c080d48404003400d450f000586080a446060302e4907040d400500003002c00303030f80c02c0c040c1406a100007e42c80b541050368184651802200c0e801c0160046d5400d1190079500584c81e0041c51a02c804d035180181c11440c405da01d83d981c080c07003083e4002c40d0b040d4030510f140381200a9203541741c0421021404d50300300030309902c180380d083c554030320b01c50300800304001c881da480d895900500b80e140c50320740c070907102400e0060b040078601540d40d0010a603021501405128006001084001e01c1202d850101d80c08844840d11803800308030b501f070b20072076131590010144e010b0314480c5110f5032042d100d0200140f0043c040211080410100d450100945042002c0e19580c0c40d503074810008050005112a103881e00140b0404101081052140c052202162040402542141c43e0040c0503504a5614110b518803543e45050010302c4461000503204242c0c014000001c0035100790001e01c00340c400640c881c80 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 853964334 1250 853963084 853963139
    0x3150b040f0e0307020d0212010e01090c090b010c12031404060c080f010f030b0c0708070f2108043e031506061b1f1406190b0708040b030702030301 65
    0x20355034400f0003110140c0b41e044034813401e41a85440040e280d5650484010780540c41d0540703000d00c0e104154089c2c8105030080c02c1143d252503643e0500e40c1030780c4074180350701c3c00101d208020f000068089441903107815814100400c06000d00d001c0c00c00e91040c107c40c10b841568442000308112500209640e070004015501e50700d256047c41480e10584603c3e00c002040d003000100029030381402c0e50240d0300e42d01d0388500c105039940074605000403610480e000c103076181e01e007100c03000c1002c1d402a0380807100340c1400d490318a1250355540b21840d000300d41004008000c8110401d030b41da091803000d003801c4400620381034013403018410403c2c5850005140203145c0000f10050a014445e81c0b4101590000b003808082e004042407402c1e040340c1130002e084c034041c48020200c81800300c0d04c00a60400c6503a5a01d00c031018550760b84041c10040300980310b00066019503c2c6c03c506004000c80d842c001d180c918040c1600038900750b501c00c0f680004d540100c6103e030042e0000300040c843c202548100007004801403800c0c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 853965584 1250 853964334 853964351
    0xf0730031103060127030804031a01050108070c0f12050d1d070e062409132315060d0609060b19051602180402090a062d03150b040f 58
    0x5202c040c108030305105200c100080078001a180e45100140b15400c000306150341d0f13291450642d00940802c681d0184c6203c150070f401c24083c14550704980c4140d41d00010f0391509141510f40204c0030009031110175200c0102400700c2c2001c41a082a060956501ca6440da24021258200e50050b030f402407402c02c054140d055043e60006540003500c11810300c990b40780d102c00700040c1280445001da600303591540da08880c69130505001601c40c40d20709840403070041768001c5150080700e05c540092000c0f1139401e807500c54028110102240c0c00300380d40c5d400c1e41516200c2400140650044031b40c0341c0007640c40345010b004606150107460014200340040030706044140c0076030b00a2041f00d8403d0006c120300032414801980c0c3c510001c400d103540280500c5c40c1121080130b9006145411501640106103a60101c3c104030307058030510044542001c1603640b0251601c0800d494400f03500c0546900d9010158080042004058a11003d6011407400039000c803130f00c0184000e85040d0748001940c0307454500031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 853966834 1250 853965584 853965611
    0x21b0c030f100c0203040f0303030e0d0e010c062c060411060307050a050c011e020c0606010503130201030b0d02030f1e070311040902030a1e02011b03140f073003 71
    0x4450403800366440203e15180d100c00101d203180115884240401301c0c3e07102c000141505039010449401e0303030200303944041400314419202c50210a9403180064402400130000c565150f00804c5a5100e601c1000c410304180c1c4902c0e0010000b0342e05d440107a80104003484100300381003144009040b800d45200e400d500e1300c0c1e40090300e280a608040010b0110003d0302e5030140c20294041c1201c0c484503400d9021004124240c07070002d400220603120184a0300000c10144d40c013510a8911070f84c0010409134180d46594011809003901c9203103950002c00c1c0100f11030050746e041c042210382040b800000e042e115071801d0000e2400030000f003900011b070482a01400820746100c504841800240c50200b000c40c1c652000c689401206180070300441e01d1009034000301c207262014200480c1c000d03a1502c948244803e80d200c40c0b410044030003030104101c10b8030f4141c0d031001c0300e02510045842c03806548c1480342d552940852480d07a580e44803840d0307400882c440450044010318900a820303c1c5030402c0b039403541200c2d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 853968084 1250 853966834 853966843
    0x90503010605090124210f050601020604020604060302090d0209013201050711012c01031109030304090b1201020d091205031014040905072c0c04030213020d021b0c030f 74
    0x110f40b81e02c500e4031709880c0c1482c00b402483c1000515001240001c050329807040005165640c82600c48074108804510a507200042c420300981d0024102483d003850a0002da0003588400111600100d4a89103600565940140c0f917000700180703030660390030608001c0c01c3c42c2c4c03c0f074110344a4502c280b03102d90908103e9a0100540303624591018140c54040c800000584031140160085440e200792454880d40000001c83c0f011117a05080e202403201c0c070a00b9010710094000c00021581551081c44100128070a58000400400000e059512296004104142a81d20070500e5028441e00e450b9140d040044011500080c60501c0c5841400c40c00d0551400b6644034952007600314112910b400c150aa81c1c0c3c0f9441070507010f43c031004039035405030b84152348100c840c0842c0a05e043e1003501042c10804980d490390300d0380b1a00702c1083c15482c1c6401c640c02c02518201c642e50204215500b0301400c400740c0c20318401072074500c2c007200030703084000030340000545065560f000c01806500581070f00c9601b0240001c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 853969334 1250 853968084 853968119
    0x6030a0c090b1302070c062604150e030a0305151c02151309140a0e030412060603060608010906060503120906090d060507090f0e01241101020301060905030106050901 73
    0x40d008078a00c01c04000003101d00399941e4010f015a480007031303490204543e10750003804480b0540c50320803015000c2d8004442034481401140c154642010014000820820402506401b146000a0101080302e00c542c60350704904065400700750f603201480307480001c003810819a42c00465818044200581c280140c0d51561b1030700178080c1c5203100704809480311b00000e4404403a40380c0300510405603900324030750280c4100c00f540340400c040d04010440d94030040c003e400303c100e203010017140b4140c07420000441c401e2211406940c11542c840000c40006d0440c05a100108a15000460110803504001c01250220780c0864400d40c013022140500030400c40940c0d0030f40d40201e03403d580301d440c1c00d004105842c0d161030b0010005031400003080039068011a03c441036524803000b0244454486080183c000b00a02820554000048101810300d0006210388400b101c82e1401d0503100e43e03400c9030107003643c00030382240d400f25400030340a0000782001d1043c4030081138100d0301400654034102822024181c0e48 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 853970584 1250 853969334 853969349
    0x7030e0309151e1909050415030f0c0e072d080c09011e050a1704020a05120a05010f1b02011e0b0a030f0506040209280509071a07050606030a0c 63
    0x4154000d80003020325007048000794680f4065aa0a4400e81c0e482d0542c089003071079000301c0c4800b80041080e00b4140724884074a0407001d40300c0002030554407480e800b15214081121220781d1034a0106214100107034040c0114a10740715440110752a01ca4422140c1d080c640d48084043c24514110b0156809508150844081080c103699140342c100120344041580d001007140e01c80c141c13521f4540981c03180003002405090384d1800b6050840c070702400200007040c2c501a522a4110034207009901d40080c0881e00d10080c1c0c003c40d4100c1d0b040d0341d5a50309403411080b214010641d64000301c0788034021250428031402d8288020451310404c00003500b81003040d00106188039a07034101800a940701c01da95500a160411060348000ca5030b89441ca030b88010440d0100c0c01001501c0c046800e481c000d41441925020740301e0a00d00348104d216460004048c000c0840003503102ea06800216605403440302045600700c0e5105641c0c0380c03554108545071180180400b401703540a02d020001107801c40d0485015583e90 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 853971834 1250 853970584 853970587
    0x610050c0708070312020105280518060a09110414150a0302090c032205190302070911030a060b13171f1401050406050d0305071b0e07030e030915 64
    0x14040c040c0741200d240c011401611604002105000d00c0b40322000c1002c1c01c1e54000d014540d1154003101158081f0303c100803409000194061030018160440703680050703140e031610683d12102e070405203005015682c0120070750740d81c40312400b8490044901184c01a041c1ca041c45101074000c56294219002000003200040704412401d03e5540c181d030940045400a240b104a4141303101207014070361064038040d021681e0340030001c01d2005500740d60b0b44600c2d0032402801c0780600c1e4035042c9004000040d012021405440004102d03200c0da40701e0606d510350b401e45215144d162200c1004221170690300088650388060221116100d1a280d6980544a4500500281440202106141040d40d021003d0700390400040c0406001c10340d1300c609010314003040f0168a590369002840202c4e1294050607410040840713203000440d00803001006040d01ca10910f040d07178060b40c080303660141580c0e080f02a104000e1b01c10f10452907454062144410407100155282c20301100014154450946400b40300040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 853973084 1250 853971834 853971847
    0xa020a09060c1b0b041503060315180c080a050c09220f05010204090203040210090b03070c080403060606031409010c050301123f08010315051308070f0210020303061005 74
    0xf00ca0148104003000d0140072680e82c2c4c0c60b681458000e400600490515210a400007141c80e486801740d54201e13038021907030b000d400300f08400001c0136110400d00307001a00710140c06000002c2c0b40c050060000c1010f0000b5128100742880c00c14104071505014500c40d1404106000320290351034000c07000ad812403c3c0e5040b07035095501d00080d00c3d84502c10302074450f5101007000201145190001d61056200f100d80e404030311030758181512074460358007603522002c17000c0c80010140360041d00c6185c102030080d01b2083c00c1a030340307070b840c0c4003070314400e80045000a031180304071000c0221001510340c110126200a102c6c10510601c0107006020500c1a003040c1c0304024104130600980c0c0e20708a17072000b804003046c038640044034843d00c5945221200c81070000710003408640f24a00c40d98030503061303d034000d0f5446e151003494402c81004d468050524060300030f000c00341d00e002480d80c50062801030710600381940c8440090040010107021610048195001002001032541d42c500701c10720056400d041c6507442e00c1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 853974334 1250 853973084 853973093
    0x40503071520070f0b031605030c04031509030801170c06030c0904090c0608070f0e0f190306050604060e0402010e0409060e07060302191b080903030d09080a03050a020a09060c 77
    0x100030300038406250400070ba4544540404079400b4161101c001c0300c160403540c1c0e07901091107448229940c0c1310000c821a07050700c25600c194025508503200c2c0307007a07604250300c0e52901d0405180c420700d45122180d86104110425030400c60450041c4101d440c2c003040116121485519584440b4030b491041100200003081c0800740001d0314020f02000d041080815040e24060074015202d02920002c06e0286c000280490b01c1000c5200100706c60b580d8030003c0085101c203002c1d41081003030307840f680019800c2a60000001102c0d8040040d0302500b0045030320308240d0b0600045407a15005860214980710801c801761340c00400551103a802910009071094070bc0c00c00c400144544c4020715241d02480000040b46540b58002d002510000c03003180b0007000c19600c094a400210052404007420009825404210710748040c0061003805819a854004008203800840b01d00c0e400466071100040340c407901159240c86843c0d80184003080c21490508202000303410844c02b841074030200203010740e0540801 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 853975584 1250 853974334 853974347
    0x18070c150506030c0f0a0e090114240d080a0c140f1510030209061210230a0b011d06091c0308090a080301031101050903070f090609020405030715 64
    0xa03800800a00c6651841410040035140c2a40d041c1e1081c850000c409000d45001084052407480007002e8010309854041a244e960780000d0052080b55030303c8080303101d165500100780380318101c0100c600b02038074110640c488200032042c0c4158080d10104d00c2001c0020b141c6021140003c450303050030490404980380c160a083d103107030460f101502480d0704213051154002200900c91050140802e0a0340c2d0312503042c14815801d20001c0e60120150002c50400e05000001120b00c042400603602524480c14511043c0e9a000400704c0c0003036407800005020f850706901d4243c011804002c14008800c5101c0000c01c4c40b03114000e4003504000d4980318411030740e01e49048074400c81000e00800c0303108400000c001e032002e400e144140c000c0f4542e007000a0101501084d95170360b0643c031580f00ea0659003140c9541d5606210001d25a042c8907040060164940c1c041012000a06031504603050303050501d000c48090b03983c0c1d07a12650450340180403c6c0001c1c1d4000c40d802094881d0301d000791004440d17100046510 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 853976834 1250 853975584 853975607
    0x160206061c140c01030b0f0d08030915010602030301060815010c030f090e0a0515010c080708090d020603100f061409370503120703170423010f050c04051807 69
    0x640d140e00e120320150b90104078030300203140c2624200121004076041c41310a2140900c0c40c0e510501228540c0c0004520f4000345070030612103c200d07100c3d081c400900c3d1290036401c0c1c00c03442c05030b480031004000e0755a2010086500c07420b0294002c044505900010789150912034004041c005600d024500052180480f2401010113000e036032050308007110300d10020310003554000d0980d080186c07440b00650081e43c101a01d603500c00c191500d0a0f0843d101c0b04203a4114044c4564004040c440500c00b50707a4a0024601614024103c21400c41c9424030300006e568071076111000f4420140400b00c01d42c40b01506403a581c0340e0550348079030181215904104041c01e850100c0c0411070b00107a1104075948a4078051055403010780858211650008805c0d0250150100040019031115401100d581c0282a1560011301c200d80e000b4160f5840c01d1890191900000b480030640c1d554940c54007070b0501405850b410240d0011014074150400c000303d43c2c0018900c2d0414080c41c000b6001c40e0304203201e40442130701d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 853978084 1250 853976834 853976843
    0xf0a02070210081b04120204140c0301060806040204180b04050105040b010207091a0d031205060303030c042304020d0b1e03150c0c0d03020901024e070b0f160206061c 73
    0xb45d450300c801403c207488407034a0085c2d00591500e240c4003200c0007200b0b8440c3c001c82d80c0030717440d5046a290010440f10f00000404031a002033702032100041400304100d00120284542501040c2442e2050501c01111030503030010340300741c1c100341c03807501c8ca660041604015143c20001c0800d00f114130789004020103084002594100d0056024038051540c40140c0e402525000c0e04107108a07160f060070160340e8041030300ca071125040100010440c101410301d0402400202603440f400040040c80018100e0b084006244d5540b501c4401e101c85920300007000300700719142c90440c64080004903000c20b03540e600c141c1216a210860001140c041e5900c20182c030320703801c207070700450784022104039004010313400c440081c3e8050310850358010040081d80128604450f0301042801d50525805a209031000c5c0704111803800841c07030318061200c190b000c40200081d600680e0050900d0400034046103181e1801401d24030000032810791455210340c045440c0e46c201c84200da4030f50180504214000c40e5030400c81d030060 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 853979334 1250 853978084 853978087
    0x60f1e1206040203070f050a0b0904180308010f05030a050316050f030c03040f060203031b0d06050411032a1602150d0518030c0726060f0f0a02070210081b 68
    0x603414000944684114420350079600e15a580da20000240c0500d0b004142e40001071507414003108005078003908440400801c089070541204041d8007030014408810380020321200010b21140c002d10380d8586c0141000d0b401000300510320348a841d140d004941c04015103a64140d40b507014010204080c0c9104002a000d40e5680c00c1e15003281039032507115101e6648400078032030300014014008000e491052510390340710300e1800b50031645580300d0303407004031010364240d910000404c954a0750b10420040030304480007190790341003040e100d07115101d0011000700102c2440c8005000650f0440030303203240c041101d50006a5034214800107014100b099074041e000580840c0d03000884809400450140d851811420810b09000000b10303103d02c140859204940d00c020020030076074103072008000c07010350240c45070914a1030002b042c1d81803000a43d0003448040300301d0140316001d0360481519802100c203160843c034041156001c1107110040c0c480e00c00510080c0c60000341400e800c103031140001700c40c5803840d5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 853980584 1250 853979334 853979359
    0x603080f0319090308060919060602071e030314070804030f0b0f0610140c0a0606030f1203061d04050a08031008190b130804050a2c060f1e 61
    0x103105603007085416000004400c1d0604882003103a10031109400d406581d00c41c441e580c1e490038001c0c2c1500240c1890340444801200320003a0146218003005444507a0162a40c14500780707150001080c03d08a816003080c00b0507003040040d821540c0c44403c144800026074440c40c45080100c3c5c0d5015540c8007400c0c48007006100b400304804510aa0b10039414100d2003e866101c06050060511107500c042010411083c0c0c0c0c070041c812804050400d01c00c81200315420b9544954032001641c45550003210715261140c8000c08000c406c04070a11000c1d6039140c1000100d03d4044032001040125403c40045040800400d00b072040602100308240c0c0c0000120340d8038281240c2035031049107240b080000d24000d00003421810501c401c0c200c4202a0000108001038548a60342c0009180c0000c0465044404220002d11515411b910340c00510040e405420340d0640c100c0c00f0003210030003c200100e480c1e148010000d059071001e14000301b80806403110102c0f43c03c0f40400300819020101400d9121840003101b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 853981834 1250 853980584 853980607
    0x1e0f080705060412240f0c020c0603150d0f0303021b2a01170f18060606030a0b0a12030512070216090506060c0102030108010911012303071e020a051b06040b0c01060308 74
    0x300c10310300c46c0028100308854000d0310803612144039144069001c1000c0001c29680b81084c001d92002c0300d001007100c0c802d040e0940d1407003e00e0554040440101c0d8000c0b80800000006401d0b100140b030300d40d4040c101d40d45006020001c0c05e920071402903024070307840c103240c80b0b664030450b098114604a170540450b507080000318002c0c1d41c4011900d010310340c03013802506600c2e20004500c050080310068000e50640c0c40f0448010064042d40c8a40d0b82c1018544a001407407a02e10311a040246009407900d540e903880d0a28100e09080c00280840705540c1b0100041400700c6044640a02300c2d0382003040003580b0784655002031590b20401203c201150700100c00400d030040190b00000e03081d882007001c856802600c000644103009400800444110454185500360b20a0001560b0112161401c401d1040c01c0c540c1c2e02e000040520030403001030f40f011012104010007000001c000405072120246518104000160288514017a090300d00078045004103ca48094000102450744800016181c1180480 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 853983084 1250 853981834 853981841
    0x70314042103020702010804020907020c100e0306061c060f0b0402130906050f10030218060313050c0402390a0510050c07030906050a091e0f08070506041224 69
    0x54034080781c00340c031036481c000c680648203d0301c0705076040e180c040b001d0380d4075020089051801070820055000b800d040404a96030b030070080d1040303d41502c1d9117a06103c40010305d884c02030002e0045000d15440180c4400d00d2007008a16105503a00890104503031080100003400740408580c041e03002400801c9643e410320305082450151524800d003085500d03034920030011000a101c00c1c1580006075141c40c010f030f25109400805209190b185100c420701c040798013155031507104940343c86409208054120422006102c140341588046400b54100f0400990a481d00401c90001d00381c400101c0b05003201d40b01031040380c400030594101c2554204100c03424500e4445010a190001c480c2c035040c0054860350340a42601d09144d0150b0b60ba0740420700340241a140340e0700020740b40050103048400000d50301e4084a540c20300342941449414894a400110321400c109600038806139003210400780a540c54100a030b404540b0440301c100703000c400c0c90030000ca000c00d42c000201c4211a01c3c0804400c87d0b80c1c00d40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 853984334 1250 853983084 853983113
    0xa0e150a0e010f0203010b1b19200301110a1b06051e130804091107020d0501061a040302090403051b0106150908010b0d02040b18090a0203070f0b0301030b07031404 72
    0x80c001c2c41035030000701643e01244002d0090b0781d000c1c5d07818000c44035030102071a00a010541940100d55003d40000d50040c500802d014003182e101d28098880344140d20000d00410394084154003c0c4a00100d0340410003ea00825044508000000c252040303034401c1c4d800c0c034071784058212038104154240f000c469100c1a90001a044070500301002203142002c4a03480700340115040070303006003071500b003c2c01400038111400300441c0d018020b0000c0c6015980d1510318060940c4035100015159180c84181c2080107044007482d0710113035040c402000561905c4444650059240c54415901d010b102c1c908010100c001c4c2c3c103442d17607610302100440c4c002d0114040f10404603094a400c0b40b529601d02c10f0500b0b0b42c8410410307941100f4050f03171220040c14150803210603920002d019402c1c0306083c1c1325800324400f0032119081c0603842454000154201030218101900c0c3e8980001d61050401007011100c0c032041c80018541801c080000742c41900c01d0f80010880300e1042d031803480700d0405040003d0440e1400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 853985584 1250 853984334 853984361
    0xf1d06061801030605070507082227020d0e060403091a04081905120d0f050c070201020a120306030b040f140c10030f020906030f04050c030d080a0e150a 67
    0x11404500d051400c0c48050700001121006001e6580c255610b010107810b015001c4818400280103044c00a40d803440038004150030142500200341101c080004052106d03440380d41c4d0306010703800d24110070500101c10703c00c64000400241e030390115040000010900303000c0c801658091785080c0030030994070440c045c04480318050342c241824202c00f4441d49503c505c1c8204807003584060149015400c03078038141d0340708030701030002d9941c1d0441100824603103038000030b030403000700b95111525000403010b440f866400000300300c20f00d03080c103203280d001030f503940700f04c4402400c03510142e1008038a85210f508080050365114980f1aa41e0800340340482690700f04480c1140c400409103417008042d01c0001d00da10303000740c001b407541407000c004500a50007400c040e40c01003000b0ba000c000a82c441d4484030300450080e4030060b04440a0302e05030a116040402c1901d016110741c20968207204050350005406070010f0301d503480041c0f04074844100e2490010011007490250307104404202c0c665629900c5080354400c01c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 853986834 1250 853985584 853985593
    0x41e081309020306012703050102220f12080304150c0c0b060906030712140102040b0c1203090c04050c0c0703110a0801110703050705120c010b010f020a020916030f1d 73
    0x2500401d0003a80402c6a10600145c03880c101d4110000311200e40901002c5e0111042100769107985946007607030b200c0310111840410103810100d4240080240100400302888119842401c1c110003004100c4a03100190030f80c0030120108050008810340c4041c3e1101e00c410401c040500ca0802408041d4018000d40d040f0a40074005141c500b40380a559110340c5004020b410300e81e080060240c003060004e4000d40b4444040c1490b014050780900c0100081d00c0750034101b0b6117031444141d04074076200c05c001100c000c008040c000d02058040025032800d000c44101c42c040b0305035407600a015141e01a414075003c20b441082000000c0c00414110060074030025114501a2500e5142c480d09841c00a6031340c401d0904100300400c04a445840075002182c8a407066603007148080706c4066080e0041d1184011595483d000b154880d0381040c20515400014000303032280c003041c7d070001a03c004000f40741d00c100244a2525280040c403950003001c4410040b82e0070405404201511540f151074000d1f01c5c0c1c0584078 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 853988084 1250 853986834 853986839
    0x71502070f0f150c020a03121205010806010512150601080402060910230f041208070b012408060d030e03120d06030b1e04140120031009110f03041e0813 67
    0x13103100c07804003e1760043c0c100c403002e614550785c0c44200780350f05801c4800c010150b2004214002c0c41d020306402402048020300c1c442d4100800c0114058850400860035840552012200c1d0619509181e00c04401d0070954896034941c000700395148200c0000c40e61200c0702030740141485400410030303402a61503056402c2035030210300d9102040d01c03a401c19480d244409000810102a19070501100c0074032030070060703051500307640e18a00d0212003a04011031011281d0441c000320413101808a90f001000e14110314141030102c04100c081d01409001b07801c0041c090882c40759502c00700610720a403046800101c1d601c00700305001e107005100b140811262080c0c800041408000d941043c200c01660000c6000e10740c0d00c50340c1c4d0700001d0305080740c1070030240d5484620101441464802c2d8000900743e2000700da42c0c031310340198400b4880380f0b150042000c25182c825062078103801c40054030030161403c61229901d88440c10144210f0804843d00c8401c00e40d07002100d4200300c0c400000e00120000480d03c1405e854 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 853989334 1250 853988084 853988087
    0x1b020304060507060216022101140f060f011716090b03040c0608040606080601120312151e0b030108161203080c0f0702040c030b01020d050309071502070f0f15 70
    0x1240d8820140012014441440481c035203500424005442000034403c010595004c04d82170240081ea25204445842001122001c28091841015102c411500302d5180211103000708078406071071180036004244644035280d002c0c1d4803510b00c0f14110300008071245001413071806c1c01c4c0b14106203080002c0d0b022034000342c0c241054040c0c1c0d0060390310000030b9101c2e0b07042513821102224000c0041e208030303499a20015107050140304007400b0700740d202c243c0c5200c081c5904000e04044074140842207005c3c0381549242ca1980309540c800e0983e140301c0400e8542c608405040d11500880c0c5d003008a0100c000400020b01110002d0032811401c404e0b0306c012840e59480601c922600b00019010340400c88180014004110080081001e02c5d820700d0a42d0401e801074012408846095024402280c1e03100d4801c502ca607010051551050080c0c80c11078030354600303442020340300e04103031040080038607042d4541d100c1c560080c000000640b050804030325220b5941c0e1954824010300c0e104240c44050581242c4d14020b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 853990584 1250 853989334 853989337
    0x607031e1d100501030b01060309020a1a04050418020f040209010e2101060b0c0307030c0204181103060c09010c0f020406120506040318031e030219050303180d0f110705040f1b0203 79
    0x3690846c2c00d60342d05070302e4580158094141500201d900c50104034010034105804510328100140440c90340703031030720305080512044803c0c0c461642c02501030381500c01c2c0142c0d1800d1180944100c1680c016031646001c40040c1d404214003c406a4001005021019980c61003e0104072412020f0001d004450b81c2e0101c56806105004103100503800030404100400e0049510051543c80074000244840900b910700801d0288140c04403600c415910b500e041524080100e0313038000340040510351400394000d001038900d4400c480000d1403250200c1c0540d056656692080c3d004000d6107050305444d405c1858525100d0500311011004501100a480b1034400b00e900c0400540e60b00583c0d031000741d5a03d9402a142c4000d15804900b1840750f44e4182039414520511100fa4501c41c800564490900401515003030420401c130011070f510000000d442c047d0300030306e284000c840307505000c0034040482109900b000700507081b41e60000e01342085541003201d40e034412145448a5090040c9090901d54203d80301e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 853991834 1250 853990584 853990589
    0x40204140f010e18060a1d07090b030105420a1716110c03010c020a050106120314031801090305030f090f071403010902130b09010b0c0607031e1d100501 67
    0x1003010350fa940c07140704c5012102c45401200040017604203550303460b00b81403860b5156030744102603450141400340032504000400702400300c2d100e442d8190340c105404560758110030090500d0000006d084a4404403880e0f05205c2c4d000340aa18030085a4052104c140326680200e1070100082c1c2c40782209003681045415040c06401511148800b0012000c4111440d040e828840c0c100e5005116100d111941e00744200c3c2e45c070f0790715900902580d40b82c5041460031283d2030380c400718504d100100558002503001182405007404810302c55200d8481301f5440b84200400543d00340550720341907440b400c0c1500040a944156180e00749030110343c1d203650005490350510352100b13030039a00540c400c0c0603266252410302101c0340064000074001481d900025a580110b40303071100304c156108004425030070321644850242821010881c5001005044c559840500030140b204040d0380d605c0c50007940d4030400805c010440d8091080c8400207814100c102624060f60009150b44200358180380345200d40d00403c1d04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 853993084 1250 853991834 853991839
    0x30301060f0f031514040c030203090606060f0408060703140106020a0b0f090a0203120403030305060901120b04060b0603101502010c1e0c0b01030c0f060c02130b01030605040204140f010e 82
    0x1404610324030150b580741ca080d20014140364440007072804100c241d5254034000c0c001c501021042064000c00d0000300c9a03040502810503004000304803400700005003683d0440b0080e111103948880701c0e1071560b41030050390021525401a2000d11100542c5038000c0003499031101845150350340d0340e0740d00707a9a82d40e802034024540c2c045100054100e45000d42c0b036907031219030b4106451081030194000b03402e14030000114031624502007402d006050303140c8190755010307100791038686841d418040104001102200010030800031000014100079454102c4c2080800190403d501c0c1d00f0f1050103503103000f8681c010205941c802e0035007200018414003465030240d40507116607060001c0c0409500170306902904000c1400328000c0450001104040314500940c0150071080b40e890802c1a00020000c49034030140c00c00031340d07581c2d82c000750350341196804c0c070007403045400245c466240c2c0050b005402640c1c00158018070220b00052022240012585047da0807038401000366084801940c196801e0540c0700e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 853994334 1250 853993084 853993097
    0x51507020f1504080d18050301050609040f0606090501030809040c05041a031b0c0706110703020a0b03072321040b0606030a020c031305011106160c06020f070c03020a0803030106 78
    0x807082c108030750140c24214406160628064650a5480c5008a9020040001000c854141c001003600f801081e001d880110020300c05420325600240c110100a0001750591004040d10420008030790b0202008008009080c0515a52814040c81a821040035107000303e0901542c40c4946118800702d500b5501c5880b80820031070003102611145030002040c8581610034071494805840d1040050800b40740c404008090080c200100104408404903103400c42e03500845080c4016520848624180c3c0d10407500a03449644407501202c2030303a428603500350b0710703c0b440540c40302c074288c4070006201e16102401001110086030801800d0710074200c5003d07241c205c911010415903c0e010006642100c0852005400c044c0758440250941d80a10356080951007030704000c01c07541d40c00490030713944600e001d0060142c40c5003c14844840c44040d10312803041004e407807420010440c2a80c19503000d4003074801c0454131010146000441003000780402e0b485821240f40014600c1e000004803410399190350b40302d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 853995584 1250 853994334 853994359
    0x80f0c2407110316060612060203012603090609041409070f0509040515040302160b0306090906040b040b090f0a0c0501021e0703060218030114070806010201020a0206012108120105150702 82
    0x40e54108804003c940321743d29000001140322a034940b001700603002d043c0060781e07135150100c4050002002c0ca00c486e100c0c00d012106140040c0040b081c3d912024042c0c41c400d0382d07a004980010010034500300c640040f00946420b102882c400001e00e00c00b900d00e200c4541c1141038469041100400b0101d034020800e5101e8900a01003103c101e1206402034424011105480412030300d503104803070140c0000c681008003004000c2103144c440030780ca0300500a40c0141c04282001e44482a051344014400f81a08050f040400c85041003000300841c48058441034440b20700031450300310003101c0e0780d208081c018880e00c48480f00c013200210b880c0c20714100c2500104031080c5036980c1d040107174201d882c50001a00e0304c400104980e48003070249087c41c010031030a070620380c9420200500041d2001e42a6811a0310520280c0985500003a5071415181405260303a222584034860308890344405800400d5104003288805544007004500350584204448000000303500c1d0708644158054160003070b521040032040e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 853996834 1250 853995584 853995607
    0xc06030105041508030a050c0d03180f03020709020f120609070804030f20030c01061a1c1b08040c050402071113110a0c03080f0112080f0c24071103 65
    0x10f0070358104182d0a01c4641c9964810b01403c5802c82404600407450003d4a0f000b4000203003c11740450f07120782400c220304800c1d001c0304019070081e0702c4000c18050790303500600c1c2414000c102000060030190420f56907620001c03507100042d00316210708904111004003040702880c290000b03030711901c0c4030f03036402025a550340c40449103610310210030030a22144205c502c51031503e4002c06158001c0b810700850b65041c415020314212030456100d0000c400c000081c000c05254550300b220305ea245d06950b051541100801725100a180345c02c01c07080c11001c100d109900883c1c0107681c00d0300c90f50003180c0d8080c0a07591102032000768071411350300070610b01c44c9030004032092800d107404c0c141d104500400001c00000a204a0815910454420b4007040800d8014020160710080c8180e000c00022003040c982c4d45400106100068240001000c108001c158140c0020440d01510f00c12481101183c1500d06480d101803201010008210004d000c001d0000e08118050441007400000c000025858080d06c0c143c0e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 853998084 1250 853996834 853996841
    0x509060f0708150d0f0525181d15070f080a2408011509020405090109050c1324081605090406030503190e030d09030f02120d031b020c0603010504 64
    0x803d84140a407054501580b11589442d480c0352103525904181d10301400d0207440c1c03e80854065003502411407059501c4440058080b048560030120010740c204001007281c00f5102d80140c1035000d00701d42c0701240e19071200103107180f644801000703101c0294890110481c1c0d429800150381000c150340b900840d81c0e06c2c1140d03000340003015112802503050300c00381d9010529203445a20005140c1c1d1a00d850303e0b00d071040e044a20000b0505642c08505e401e01c0c000103d03046800c1446070b400d210369a8400200e41c002d503801141e8a407142d9030b140b00201a105eaa40a4a807080080d811420200e450030007141180200b0070103000310a0302070000c4800068540c211105d030302c1206c0c6260040d40b074420010014208002030640380b0100d0788081400120340500034580750000008510030f500404800050540120424003030f290031440c988406182400452903a01100400c0c078180d2203001d98080b101c1d0740c5507100b603101d01400c00c195940034080c0c81c8202e87d40c803007000a0340e5001c01c040004005510f040d42c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 853999334 1250 853998084 853998091
    0x40b0301210f110103051e0a0f0e120307080a0203040206090411091003061d160e010311070f11040c1704020d141011040e160207080607050c010509060f0708 69
    0x1900aa030410560b441c0781050300310b00001c58034500103a140c483c90390f81601406611241148074080c0c00a10381f861110420401f03050102003542d81c04540240f0a01504906510300800040b02c22040c81800003000c141d00843c4c0c10400030f10700340c0100e803201741a8002ca80c010380d0024151401c01440030100801007000e007285400003142048902d80c2525941c403a00080030aa80340012070340c0ca0560a01041da00300c2e580382d03400e03076090030030480c0d0b01032040650a02040946010000d042142005070000c00004058012501c00030034014100081c3c0854150810b200300701c0c805481000310141301c151030700341541c800820814102c200280f4202140e071544940010314000180080d42c41c1c0e1580206c240c4060101c80c2c2003268000303035002d17060007400000c02a000049180919110302404d44000240c41d200803d40a803007010f4007240b0810011b0040c050380400d5590a003000f841c054500d40c4000002c0c03001c2d5003003100003881e04501050707482c414600941003c04503a02c6680407512a14000d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 854000584 1250 853999334 853999379
    0x8061905040f09061518111b2a0f040c02031801031d03030414030406090b0a020313240302031314030c0109030206040c21020603150607050109030e0105040b0301 71
    0x15080d030004601e1900030801841e00c5220110905802c1804511b0407240302211011041e0404514400b8400c0450807600158801c4054004000000807024245111107590075010000c104503089140e0700e054502c00003101c01c80b5010159100c500900080d21440c205840258000740a4203426050700f000b841c144d04014500020340784a0f51000c1c000180e4020544a1654004002c01040000d44100e0744001c0070524000c42c00c082c5400c0006201d01307102d00400c0c01c1d2490100d440d50301103008006492010182104108045844c2ea411840c4461068040440920440b03004521280244201c90080000d68010800b1440c5900e40000e2007030040540c1c49103210400158021000a22038420200d11036406041d03607040c41e0600d4074003440e0307035040010782c0e64840400e031103004d003501c03014240c107541035076205e40b25030b40e200c00303150585c0300c40c18201d030820800103082041000c1940a840400d2007516214a40101000112602d00540c000d001058004100500c0b40c450100107200e1866140e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 854001834 1250 854000584 854000591
    0x308180c1503010618030804051c0b0f060f0604030b0a0b01020a470415021b10050a0203010b030a24140a09020307020a020d0c03050f060708061905040f 67
    0x40408969205200c40c0c500c14000c1c0080014024507902815522249002c2440d111515045840311000c500c294811107220300004030442561210000036503080c980c100a401c1844c0c60b183c242080c101b08103d400d98800c10729090b038031003d403500b801660b003641e410441c10341c0300b991030709010030042c10700c00d030414150f200303800d43c000c0001d0004540c0001d040d0b100d2000c0c0101c0203041c09054410344a02540602c002c002d54a481070040c0084416030300c640c004940e1403100d10141c210900a1080c0c0740c40e100c00003582500e50880c0400010b0044204812003803c01296581c0036100b4100d000c2805440e03c094010030116036a1200e64200081703008000081c0c9042c0d5504000040c041519980300480c41205540c003080709180444550005004c144400e5141d03180c2182c1c000e44900b80c15400900c1744050541d40001d12080d00502c8002e581d1110032500000001d0308616602c40c000c030341d40310000f0450000200d5900300040e600310503190040705201c0c094100010040038261190640000c640d4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 854003084 1250 854001834 854001853
    0x30a031e0c02030a02070f05090c130510020f0609010e070b0309280201020d020d050d3b0613020102060103030507050c0d06020a0908060c0910121a011b030818 70
    0xe032807080355080c00c46a0002c5944e00742c401006400c0284030360007005a050840c404210380d8680e016910ba2101080c466556101c004005118240d100c0e03401c11500300070000140010280c00003044e410305807182046854070307510756a280382660800b460100858021040810003084541c01454100316020282c5081d43c0a1000103800d582e070298002c140b040d00034501d80150750b0140004690b414951003c0c29458840d001d000d0010703c503000c10065078558908030a51310740c40180e8914071042d080325400419041052298044210362400c80180740908400318110721181c035241c2110b036506801501a03a0702e152420345481c0c0191105682500851030110020b96130401d042c42c81c00d10074a8010b80341c0d01c21042c01425a4042d400400d95580b0034428050740c0e030052800d03100d40b09001ca5120340d50841d00041128003040300815160007600705081d02c144070b6000440581c0120080c0d950328280080490180b0307031180800c0c00640030840c0c100c081080025100b80c080b03c404a84400c407501d0700c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 854004334 1250 854003084 854003141
    0x3060d060905150c0703022d0102121f080c1009030210080108240c0a0201111204060c1d04090302070b130311030106080d080402041e0f1d030a03 64
    0x41904104031540d400c003c00061604000c0100b1a030014004d5590074208481e5660184d0386070201c07110300c6100a0017030550030032080c520000d6244605100b00954aa1103440301403220903c05a6040c4840c401d0b4123030000310300ba0a2103041c01101c000a00804000307044c00306020424484c80000800c00200c0c800c08000760305d607001c5807410020242d40e043e030990f14003440c250811349030701c1817100801706d11030341d0644842142d4135454000c002c203082c4650760001c042c010303401048680000b0582000c04900781c0c841018100e44244548c2c01108140f000c00354410003151300c041c501c08104204c9206180c00a4503041030307440144000c0c400d0044031840c42d100c41d2000741681020318a01303849c001100c014030400240c602500746011007600248500d41c2096240c0b91a00c118021090401c0741c420300060030b540c1c0d590004e50b1042d10b444003241c4980e54100c0b69802500003251440a62410455000800042d40c02000d41055001d4040c1d420100010001c07805009850082c4554103400299a240703031 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 854005584 1250 854004334 854004341
    0x90a0210030923030306040b09100614071a090c0d0b131109090a05101a12030d020307050702011e090b130b0a05031605090d080f07060f0c170112030503060d06 70
    0x20b4100304001c4d51640380410400007504d200d031401b1809002a101403003086d0141542c000e0540d1810b0500f90300409050400000760300814201030b080d20b112861400144480c2d5a2540c0544010010b50baa0000c0b64070901c0060040382030018010303500c2800044810100040280d007043c8a02c8140020407014000212005401d680c2e00003290400341c20141044004c100c42c0554864105060094000e1405903603140203204503280c1c010344a0080c0c6892100c3c0a008030346506a10300c03411500ca081c00f0b0801050b540010104a02080a517000c00c4503e112540301c286419110790344540382c150402c46c3c003454030381003100844010716107840e0116550034003801900091400c0c0e60346136120700d4003660818a040013005c40a05118040280c06502d1302c41c8c4420041564110a00320b03a104042010198a407060202c00380c0380e6031800030540c2d01412550804a002070309a03481680b00c18443c0c410070070280c800c0c410340c8900315009440d000040d0280340515400440109201501101501d40d83c050b03 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 854006834 1250 854005584 854005643
    0x3010f12060b120c120f0d39020907030506210703021c0b0c0f072303130f0602030c030706050601050f0408060604051510030b060d090602030f090a02100309 69
    0x82c1c1d005100395a5050404107207000c000c0c6a810020300d035601a0151444d00c0da140080d1170000c01540850484008c90344d048011480d015a2100e1928201c4c2401c00c20101c0110007412440b41c03282001041c2d07028420b015880c000c05000b400040c5001c59100c03e0001c01c4003840200300e090080880c0000581c0c0c40d901307900c00c501c0c0100c810b404c0b40291351401c0c2c7c10200c0018107600c401c1a00b8010140600e01000036100401d520900d094981e041c0c03901141c4214926800c000c14a01c40001ca1075100911030a140f0100c070180154600c00c65101c80040ea142e0007022003803004c5620910195020918680040d50003902c181030491402040b400301b000c1c01d501c250481328299104c00284001420300e4450150301090000c00b030200c40040100058643c140141d07981c04054a50005114ad0b64680080b079400400e002c508100038410743c0f40c074002940080f509803010400220015030380c03003000701d011040c2d0342e401000200c08290b0007505400400d15810700f6604004d91040c80440c41004c00c4a4206 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 854008084 1250 854006834 854006869
    0x503070f0c0c0f27050c1b0c12010b031509030913020c010e0a0c0e06010e0607140f0f010e0d0f050d240302040f11032223060c03010f12060b 62
    0x84051381c0700f1003021441100f5000c50400c61610081280c00c4640c4000d8600000481e010340d0b40d0789008618491801280c42c101c160701c14405101522503440550025102c0c0100381d09852082e0041c80d00d0001c40c0c00200d49d50b14498000b000f8291080c80e018690321650b1a40580c01400d14010004003401c4400d0340c0015400c50307000d45080001d00c9148014040145252441c0d14100d02e80b0500007004901103092860041401041c10310422030a004141c0c1305441010446401108000c040da40c3c070041301c03000406c0c9510740140c2442c01c0c9400724180c030f00b1210580700c0110302d0562407000c0b01c1d240e01c80209488034130754605090704124000890f00c03000b130304041144503201d400c41c0100022281c044203211410341c40c04403e0a11006508107a0b80e02203080c040880540c8540e002040c2017003c0b905006181d4003400400402d01c0c4401c0381c070001840c00407801c540042c2d4078880902907501c8203000d404a9041c40d0a41000350400802803d03505078403805010540d4004403020130801d9034a40501e00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 854009334 1250 854008084 854008109
    0xf03020312010806070909020903100c0e12030301080604030c140703030512090f0c060c0a0206120103030201061a040e07050d0219021c05030a02030402040603020a03030801090c0503070f0c0c0f 85
    0x40034403502114041c003502d100000313041c3d10b0070000405800710f0080d1080314a41130b0003040024040c1c1c4d05100e58900104000024008a810100e0007403420055040003407040f000b103246440c103444004146c0f410303162545d000703002c6074459440c1640d940807030342c1049520074026000103880f032206002e030000951298880c11f440e5040385040301d404500007041202d40e13074800f00005150080020301c0484404041d103c040c0d43e5103180014a0420940001c0650403800000301ca4605811702003070b4604803030003039000b003210a4503030082c686882c0c500000300c1144d040500046c49101c52070b02070603421202d40d0910030b01d85a50b07101001d0681e0400c01100900c0202c60b00340102c403640500c2800b0304641030503050013441c2d01080700a022404080c110f8542543d010000600715115070744203901641e00280643c04455991070004c0440c031b002d008020402d420407081d03d0b012030082c0d02f07890054145403114108109441d60848145892210544400049101c0003406140907500000504030220440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 854010584 1250 854009334 854009347
    0xc03030b010305040206030403030e030c0f030903010b1c080913180303050108030a05040303030b120a12120b0a0e090a0605100501021e030a122909090601060813020d0f030203 77
    0x6800c0315140300800c0c1c141820035040000681d10501140d40c8140d0501340040c600384204411440c600802c0d03500d0300140f08103010b01e0442c0600002a00020384d00328001d1001c1c550313400902c8241000055003d51042c18060030100140321a0b0180007100c0029000080c042c1e0881c1902c005c2c0c620480800000004002804051690500506000d070400100443c50850080f40041161203148405401c140d52402d90424a940c4c40811141040d075002c102c43c0040306900b42600e500d21490320080c04206615128a0549043d014139109141c006000c110650318107020361104400090030031005018800b2042e001500512825010781149401d11600300d01302000a890050303031415038000d6110003030040b4081e84d4004101d071710701166460640141c0e0104c0340694090248c0e8601301c01e1070140480190f802c03034005e41041c0180c8104982c40f1340181c47c2d44425948596080c06042d001604900c00108100204031011b030342035202900160322411203440d0402c2745080d04c48101d0040e00000f801 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 854011834 1250 854010584 854010587
    0xf0103020f040b1507020406051906110c010e0607050109060614150c0319090801110d0c1d0103270c1d010e0f040606031406061005090d260a0c03 64
    0x42041200c09440800a03540103070f001030400c6500c0009012401c00002e4003504544071030704600001c1001800251050a0700b0440000513410750080c0000620700702801e040c1d00030002805d142101040e12047c02d944000c206112455100d6581600c00390340712600b15000440b5813003000d00a00c0151030507044480c22030f0800401c0e0380401900c5031984011b201120340040c020084440221411080703e015110000c81030703500040581c024803203940303851018400d0080c00340040084201b2a10104000d89080005a9007071140e6082c40c81c1e8802c4581e00c03c2c0241d4084d601c0b10001034505981c4601d10580107a0b03032441d00c20381000444001c0070140d0100558440e0903203402620039400c01141056041180340401c0c0d20009107048203c006140100c3c041c085981d000b80080c6170003400309454080004c031542c0c3e451805480003030103600c21150b007040c4203200b50250b0396244002000b0840320b0081d9200d07145400f4100000340274031900980741d00050705610004003008101500c602c0e040d000103090 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 854013084 1250 854011834 854011849
    0x141227011410030308010e130f15060f0b0a030509030f0a02070801140c07060b01050913140702010e030f0306181f08191203090b2806050a0b0c0a05060f010302 70
    0x54080c411002005200180c0c0003540d00c2d064818007d01a0b0880d86c076041c0d1400b10341c10041010b4040c00c01030f0020070034420721402c0e9103584524070605110072b0b0b5a508400b0032200c058030600f080700704140082d2001c2403003500a50382056443c0101c0b400c1100c010300e01080d96102c0381e40c80000d0b80c0a000e04010480c828010182844078010070031364140f510300045880c41c8540070380104101d6484c003010416a024806440c629200607000c4400c640380400514010400c2c11003184c1c00d800345030001428540305000d40082440324030051414240a940103c071940c202406069000100c0141d815264000080c018401c0c20b44050070601d00341084109100104981c1100e00c242d04002c0c2100740d003030303040c00700e4404069100c002910f034400801c0f4214000c1000d42c2c0c3c000c001e800c81d403090203998030103060050002c00181c030030340c40c001035003e00c1070003122440e108060300144041010458052624040c0280080500645102d281c441d6142e074103140d000c503402c140410156005005600b0b0040 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 854014334 1250 854013084 854013091
    0x30090504090210181d09010f09080d0903050c1506091b042303011a030c0102030c0d0c0812160908010b01090e0a02070206281412270114 60
    0x15001c1060072110b8000c6042d4458a400394024058582c1e40341c28004c05402c041c8004286414000080d061044040c07183c4142c251100d03540c0790300b0141c00e204006014402e4031066a0b01c002c4c064034110030105150040d010038401034040c003000f80804134140c0c0c0240709411320004032007240441440c1810400a1f03855003d04a8150f4400440d040007011445074115020703a14683c03c10030405d030700400c42540455990a00340d4265003894991807900b4002505a489010b085041d0f891480007007004903078a0080e0040759003550f200301e242d9006140a440044105400744044131700e426031f803100720380c04404290b034078605141907841c62300c459981c00388031078014080320f04c001d000d100303c000c000034880e20081c0520075581c1c10344000316228900690448008603030191a40f0b486829180302b0f1100701911074007030081d150407200e88502c40740c49848000b40b00426040321508100d0111310940041e0401400001d498812080020f240310141c0002d4100c280900d001041103e080685c9035800d44d00603 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 854015584 1250 854014334 854014339
    0x18091a040c091512050a0c061805060c0a0f0c060219051b0316122102032203141c03060f0b160803010605070b010b07021c300905 57
    0x45003480002144000d200044070022035001c1885502d00810301da001c0034542c0200d4800000c1c1c04441d00b004400b10314412581c5c02000c0c0c80c0c1e001650340d4426243c00e4507071542d1003140352039160305021a1815101030a240100700e8211010a5040d5803642c5c1d00d072103040003e461040034210104801581041644585c03007040319500e952071310540ea429680d25102000d50f40c150802134845003182c8040142240203000c0c0ea0b00354600941e02d1128030031003921140c055802c980b0346028580201180e5485612a103002d500946c6019065045105203888880c101e241026402e4400008500800d0302e80c0300b54002c0002406503000301d10038076005103020358007600078581400c1007000000080c0c42c40034100c4114407e0349030b64405464000c0700c620942c034001071417041d010001040341c035070010140440c2441141200c02a9886000f0781402e4040e040009520005964000c0603441041000040306072280003619a080c101d854200704800400c54210b010407140b040810003580d101829200070b103c203 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 854016834 1250 854015584 854015633
    0x70c0f14011427061308010510050a1505070510020a08060307030308071b061406130e0604031d1509131803051309020301030c0608150117070203041809 67
    0x408400c40050054030380f01c0d0310415001c1400d4990f802003a11000c18088018000303a541e005400150003801e4031802008415840e01c00000c081c801d0b2944070709d00381d4000406014019180402c80c03410b1540e0341928104020b070034002c69002030000c02c07514051507401180940c4640c0140001031107158001d1000788a03034130084081021070b0f004103c10360414524501100200d032952049030700542446401048545010100a801c01065a485000340e00403034888602d25800ba941106a490065000c619034000c58003060000f4001c1c010340300c41c071440360b170120070301e0f840c601c0005c0081c040d510100700312090001d000d1804d0301d4040d01508401fa01c1c02c2c410488055840e41e03a9015441400004091200000381011100910351640006101444007950b4030b41c0c5a1620381e41c914501d01c1140c0c0490100000308031880240c40d501d8600d9801a50ba0031003000030100b0403040c14001070040015030004000106034000030400c200003030b09a401d40845c81d20603528000c024210602d0100c4521041c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 854018084 1250 854016834 854016857
    0x10e040b10030c05070203060a0c0807210218120a1b0b031b09030a030507030201060605030c0d0b0f04060b0c0c01020d0c030e1903061406091302010c0602070c0f1401 73
    0x110400c59000c51001ca2400251107403031200f0540300c51144c1c40c0b000c1e5151090f94208030402c0c0d0035811164011682d581c85403004c2d00d8004082d24840000081690307140201044401e0040c2c00354090a21036203400e40b203150a141c040045000310344068010440fa80120b50340e1000d104150101883d2116480b04400303100d880c0c00603002031400041c00306020348003580303005944d00c0e4514058401d170207401400d41d542c0740b14178039020700242d02882d0b0440c00740d400c03c50001442c03400388050300c3c0b003010340c9803940c0c0c640700b402d42d007820061695a18441d84440403688003142500d0398030605025201e03600e000c9560340242c022261800100f002c88504550144503402100c42e4001c12664040360706081107112110140300090714070309030a04100d080e0f26400800000e01140340c0001d804001e400103031050a413140d0040c840951012520180d59808031461200154440d1800300380860040700010304080c05503840704802d510300c0d4049880b0b0b10112405002074010035094460401090034100c00390328 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 854019334 1250 854018084 854018089
    0x7030b060c07440610050a0e060103110f0c010f021806160503120a050a14060d0c0b0304060905070602010b0a090b120a03080108010b180a022511010e040b 68
    0x11440c0107404400c100e00ba01414000303402c0040c0190401580030075242c03e00d948207000150708034916410040d01c980008100c04c2081ea24800c825075002a01104441d41801e5050000f28000350616040556940355102a13800e80c0016041548a05960507038a403051540d00e42941c1d605840c0c441900d00c100030010510303003003481d01d03042d140e01903610725105c104041071040c09480c01c42000e040350100040148440c3e00d0150110705c80e402e92039080240d038503018604400c480c401444842540b0405c80880d50a10340081e40d42a042d11401c4404610790325204a00d00f41e0308280d1f000c80740e003900c80085104200d400d0003094040c0c1080d20080000741171140001d4100c1c105403007442e020a40d03500396001b450b2591100a49800c0184003111000900ca01c0c000384494004d2007100815480c002c1145214940002c101e002507450100101040e00e96030a06402544a0000d040c01c0c0804034040e00b01100310999035a190b80c0c041c183c4020208140741c0003500c0d40c00c0003440640b181d0300d040c5031244140d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 854020584 1250 854019334 854019343
    0x3250e0a060e100206090607111c030b090906041104050a0221040506011e26031815070206090603070c050d0207030516080a060c05160609140309090f060303040f0303020607030b060c 80
    0x4506803505d00b49c441941040d0038181005110703036002c00b505040341c0e0341c01c8503003540003c80501030030b8400815131b9955000c590344030142a14000d200e28411130300c000c918981904082d80003049044014686139100c1621403e00011600e00c84440d8105005c00090200c03c3c065a40105031489030a0f041c2c1c036482d00380b804445682d0080400340111000080d281802001d034810618001d07104495588090018000c440c50081503a02e100c0d0341221415108101c0803030681d0782c2c01d64080c1c41e0f20b040044144c00c208803070304001d000d4000c122240c034914010034810449401000c049801802c0100d0550802d80d0800046090b6038034080d1001030b081009450010f140c00c00150040000580901032000c200d415106140740c800c0c03030f0107840303200600340012540013600a40c030801100054200c0746a4140d1240101c001d0240c0c03015410000a075503001d4080c0c40c0d980301c0c0000b000e8078507198075041d511181d100c40d9007041e8010b80c00f0004004d9815003622034116021422180c0a003030800015549a94 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 854021834 1250 854020584 854020591
    0xc0b18010e010504170408071205071a0c0c01030e0c0103020f0c010615030c0206040f02010c1103030a050a02190b061c02091008010c020a0b07030e01020c070815010b03250e0a060e1002060906 84
    0x83e10141484902401012f204c1d40016007040c0980011542e000c80078501c4507000310361100b840d0b01422115146540c020710400c584071000802400c1c1c0c4141c02c10056009400c00b401306021000700304194401e9100038421003010301600220485403c1e5041c20080454903030314420800c1d988008144804160648c4040200c00d07824a440310780c946440c940900410361003800da681600c0042044000d49402c10081c0c18140e10741e07400c4412020707807030b508202580c0d088080502810080c502181a070b0402c8400d1100c0903c405a412540d4030f2254042450060200c50358040704003210343c184146902130047c0c00c410922440107112090083c1c0791201c42d040041c000009242c1e0f01c560681d9510f4007034040d107801d80e05004c01e440c0f040c0e56030885603488004001b59140340310700c442c0011035141c0c03103001601d0040c0751801c4481c2c1010780100c1c00030540007000c07141c0424400d40c000168060340d00c41c0c0102c1c0107030034240d0311104000850340601c040031080819400542d0480401c00020a4001403402d50 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 854023084 1250 854021834 854021849
    0x70318140402030603150103032c0915061306080115020c01121a0a1205062508060607080d0608010501080d020a20060f09010f0f0c0b18010e01050417040807 69
    0x742c0f62904d500013480c00c000a0700095924032100000401e0540156040e02141180000110809100110041130a000c8403490b9840307411707030300481c0310400b4a007002802c0c00c20103000c0314a0030709a6042e125405482d544813100241014006020414101030b90030340110341400140303c00d04503000003a0040c28912824441d1a6039135641010014403681c500a2070382019040740845a201d110b088902c0d0025107044e02c00e4400d000100d0310980901c02111810140b003141c01099140d034203001c03240340d60040c2100c1e6100c1000e0281101103544c48004020b5030190081c0028014078008005094501c142c0c810351441d0428019441104d0b000300d4807890b101d81c00a0703070024502440011801141c400300740190405000700f9441440140ba500410350007100340c903550504940404110f85481052190100081c0c852040900040d0382c4a0348580111024081300c070b414288c44030460851310384841d01d021a81d11141400705200482161881120081850b40d28150400c140300e913850320b0501c07440300c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 854024334 1250 854023084 854023087
    0x20c10020c150f0f061c0f140a1a070e0603011d060a05010509090604020408150a0b10090b1b01020c030d061202060307050a0c080a0309110907080c07020d020306040305070318140402 80
    0x950741d594545605051101040002e102520f041c24182c001c0006151f04072103890b004c00c45003203855000640f80505660203014403c000e130b0569100c0b06a42e070040c11b81380c03e114070911b4001c090381e40c240c0918040d211810412009034154800060014005001c0340d0044041400900059a21000b140d5444009503100801500c1e424003090081c40755034800241409000225601000c0a41c0c00310f0051010800502c0584c514a0412100b11803000300a070100b403136124108041c0d009000544200340e07508801d54503219107100300e103007a64000e00004c00d25410004102c01800082c0c0302d9000070385114032034050012070550114450b48006003ca2090120200b9150003035445004400c5045921113012502d5001051025002e004040c0003152601020080754406003044000390b4031800080c0d1342c6550075125218141030560102805030b802141c000c0c161809030b1010002c0d640214443d60303c00350f98510600b0001c0c03042625800b00c900710217a2501c1040f10014060065841d040c2c1100d005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 854025584 1250 854024334 854024341
    0x601050c0c031c02101a060a121404140102090906010c05160b04080f0102040503030d09050a060911010806040b030601170a02030610061107080a02010305101d060103110c12030406020c10020c150f0f 87
    0xf0b270b541c0c0c070000d60a0203505042406083e1501c0c10720903400d00452050000c900800c00030381c0c0407400d030301483c0101038101d03001c2400110950712039618240103601803015200820941d1000802c908078039003200040b104000340c100b2142004106d0048800420002142828100070000c0e40340c0c864140c0207421262101c42c0d0b2010302c6824071a4040b0b65a0189003000000140c4ca0300320300d840c56049441e400b00f40d4060001300c282c01d050003003066030a00180984000d80c00e2280c1d003030034500d20798140442442505110401030300e003000040e0144560381c40301d0b0116807412000030215120602603103010f42014008000c40303a000280c4042d440c1e42400e020501c0c0d650500030554402e50742d40b05d2b54102c8443c90302c00f0480180720305c8540c040c0c0d07070032f1760144010003d287c000590703481091002809948900d000260032a03081d4080d5030481c6c801d050240ca050049000b0703d203894522660200b0999001031036040e03c0608000c02c907140c0d840141c50342224a030101c184010660001d12070b008003140800003 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 854026834 1250 854025584 854025587
    0x6010609060912210e03010b100e04050a06120605010e0709030c0905130c090b030c040e0d030b0609031e0d080c0f030403090512100e0f03030601050c0c031c02101a060a 74
    0x40c21a80c0103c600d201c02002c1c621400180020140c1c5d441c0c81c080c1d480c019004065007404d9000e0f450000c420b46803c0c0090a1403424007000780001898000c450760b49180c0802ca600c04040d944138124060b074000b107041d505101c0503030600c80c0050411414421404410400141000030b10011180b080b46c2c0040c0e0340d0745018070301001091201009102c101485404281c10b003241d408005184d005400712520100000180403c403070220f032602c12103500c4800910b450798426001407161580181c17000b82003081c1032000c00d150003d503091051001480d03050201c1074807003c12102c0c0031040c0d1440c01c05490304104004c0300d06803080c0a0700c006074460000000d02494002e9581c40c00070100030b44180b5000350f140a00c0d40c1c03141d40408030500700c14200540c0a00300d0600040c40d43c11320401c2c002840c515103589005403070591114507102214040c811540740107a03001e02440070803102d00071109072244100c013002410303c02c070344030494512440c1c40c2c1d120b0410041780c00e403502030140030f40741d10b175903410030140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 854028084 1250 854026834 854026853
    0x30a0b061201060f170607110717070b0711011d09011a0c070b0a020c030f070603091a0405030403062306010e0d0b0a02040815130b060a0306020a0e0306010609060912 73
    0xb44c1807840d001d40e00050f018600503810080070030140640c0d11030386070031004a41500001204140710b50140b0002d100d0240480044000c0c034040350100c030041584c4d180c2c400e4858220a000b80e03584024201c243c041542c202c044102100360b0700c2034a101140032100010141c03030040c050f41c054a9040c0120300e107900d0407401214008124071045078035250b40d5180c002d40607441144440c0c014001d21081c14a2410001120505480500e024245050501404900501450900b0364950f444148410b01d190031090019004d0f90060000e190348a0443c00c000d0242c0700040d940d010450f50b4003500c00c00000303843c803c0940083c5c003403030500031011000e0005120401040d40191000c1103000501004403141d074001c1045442c45e0f4152a1b0008940185040100c1c0441c0c0900340321000078842c1d03000a2020850586c020001130010304003907100d403a803108a07007140c0d4860b00031416401401c9054038080002600628107450010300c020b0505034018020f941c50310030300b141c1240350b00d0706904001c04540c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 854029334 1250 854028084 854028089
    0x50f070804260712090807030b0c03062e0e01170f0a0e010c0c0c05030102041d0c1201081f02090607110a03060c050a08100e1305070b16050c030a0b06120106 69
    0x1182c5480340114245030702c100210560600100c1c0041c5000a0009808512641141d0300820040c0407961112012010341d4401000d041c0d0000e085100c0d148810000258094447c3e00c3c2640302480000100000d4950044403089905001710300c1c542e00d801c001080d010701d03402403150f9810000750700d40c202460090594100003000035402d180c0d800e07403110350003641c940f441c40c01070410310005503554050601704d200318090010204516034042c04418000c501c0540c115403020b200a1424240113001c08040d2400c1e0401102a00100c89004001c12080110000f085290f641149014444000980e5610511000a0400c00515080306c03050341c1318000c1800a58011100340f0100341ca40900400d02d5004a5130800480c000c24041450400800740f4201680c00c0000a1107a580b02c0295103018400e905a0031203991042060210381c43e08004090700b810003040c00301e900304400780c0c580a41002e9019031118043e520a1425401203440d840c205504000107641c4d01c0c640805286185000d80b107141c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 854030584 1250 854029334 854029403
    0x20a15020a0c1e0e09061803040909060c02010b0411090f040f02040603290d020f0402130e060a09090b0414030403080708030a062301031e0f02090103050f070804 71
    0x40000040c070340d80300d10180300c4a00c081400c0e00c03000f544a0342c0302034140ea010750f006291035010100250b4903c2c030144414800140d41c03002c485c00d01382d840702070340e0030741c0c07001a02103800c0b58590403821b400e140c0900540c451084216001c0c007509501082e9400e4078045c400a00e4442c01c810a1f20000c1e58840e40c0c00700882c2c6c0d0603084d0170341d80c2d00d44524024024000103034440610041c903030310014a40306003d120304000840144003460040c0c0e03540030807842c0103c140c20a580543e00300400d62030052080102c3d0020701c03420360801d8043c035226003004507140840c3d0004892605024900d4009030000c407025034495485079500d551280c0d03d142c0030f4a035020343c1d0001030964000064400620410101a6210b2056001c052144a40740e000c007580c01da41c0340a540440d41104403040c8115030003600111040d100804000e2082c04401006d00142e90710500710407640d903800a03004060f5641406861740c802e0200300020b1007410301003001000d80c00c005001a000c8030000500382078803162101d6012182414 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 854031834 1250 854030584 854030603
    0x813120e040e071409010b0f070611030a0c091d010e09070b03040b0a0b1e10030b210706030e1024031505010f060212180613060206060a03020a15020a 66
    0x1044010b070307502114061a4110502040000c401786003540020f41641c158503009030900b00e04241e082c1c1c154101e0013007120181c6d04d0f03e0807030034881d030580f01031481410300c10740c003003800082c80401070080b0181e600244144040b1240004a0030b11100d0068116203002440d103c159030341c64005400c1612070b4105c2c5028070000420b02052110b4002035500903c140b0b8000c024002a0704108400502070f41102070108450790703040480c40c41c215110031510a01030801003659480d01e4002405074103107060040308030381c5040c504011128100300f0080a00040d0804105040c4421403c0c1e1360b0b1000b4000b030a9107030342c0b5203140e04200c041d11030f40b1440c01341d0000d40e81d0400b9a01c920f407110907480d040c100c50170a04d250000002d000405119054200c0742250003614159040402940280c1c0c0400356482c5480d0140c04181166286d140c01030240980f00203251111a05242c0000e0070201c0c0900a80d106242c04502403005d40d0f60f03031180380c007266241d01e4a42110b040720141a03080542c1c161028080c0c046 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 854033084 1250 854031834 854031851
    0x907080c04170705060a170112020a0501080a0f0501081f0b0d0210030e06010603020301080d181806150507030809070b03241e0a0b041a0c100e0102190813120e04 71
    0x4212650200307d20a01c01802e01aa803101001070504109420181d48556400401c01095000d1644190006440c0782c001c6000107036102c131b0b401a00c400ba441406958802c50340fa544c0c04024081c0183ca6a40342d083c01d02c580da1002c40000d039501103064020780305045103014a4803ca000742c0c044640641000195a819a0354002c06002900b0912480046016560040e003038184540000f00060200080c601c840c107080400030301100da2100d07010040d4560382c81c008a1001c001c901580308508656450382e503601802e10f4010000c180203842e28142e1391000d00180324960340e0005890340305280da40c0d03044446004040c602d890b10041c01456402200300c4040b4149805a20500600800309039012052103944d85824880b520441c4500b441c0d4409861417071b0403841d000c1d0000d1100410010807210000300030001d040c02c481095541c848180e60020b900e40c240010191703040c0700a822402c107684c0340d1a0200c0010341c0c008041000034103851030481851a42c038003c121a414046c0080c004002485 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 854034334 1250 854033084 854033087
    0xd1e0e030a06050a23071d010504080313030611070c03020103090201090e070c02010f21150b0d0b0a05040c020c041d0a050a2001090b1e030906060907080c04170705060a 74
    0x1051445017455815400d4405e0403a030541d42905000d90b0b090364a56500c0c00c2500004c80b4240c1c880c120882c1002020000001c143c2c10810240c50b074240088801142c41c2c1c80c6203450401c598081c0b2a014110006008020115000c8200c0804807030f028200030170751020380d00c012942034000d9004000c00100010621407901d501903c0da6110900c00e0322454034614030030106036402c4880b079032005110120120f846540e143d868000070308152980c20031600c0c294460006210a80114900340302daa40d0b40e40c1200c810b40b0f020f1040e03900411065404001c04141e01c1070094035031001203a140c0c000d903241d00700b100024a208100903400b22950b010749410b01781c5031801a0701d81c444c0300303070968194107400c4000d083c20403208a20016000d05171906003145203014954100351b0000a1058484030007010101154102d440045201f40c0c03501001c0c011a05d4480104110000007420300410010400100000c01c2030140807a4150740148030300d45d2440656100030786c500001e51b0001d0360092800304091003180d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 854035584 1250 854034334 854034341
    0xd15180209013f020d02040e01020307080a060902120a1a100f08160f081807030309170d050301050f04020405060a0302120f040203120903010e010c050c0d1e0e030a06050a 75
    0x2208982c05280d14843c4a80d00034600c0d0300c10300e800d1500519030381c00407401417810208022806101500109031051010101030032038008440c66008285491b0030044030100a01c140006850701640860404072012582035080e4030041444003050703510300c00071510944400180b02e400304010860502c418040c5030003010000d881100702c1c003003651480810b00651000c80049040e100301c0ea0b9602d140f60601d5002c40340e006000d07000c0480981e4007900c20311140d0781403021401450190b240c0c8640c0c20700d000250a83c1c01107400c0f0303c80c560740120390b00c0210f09902c2800c03241100e20482e100c01d0902d5400000a000307101e43e50003280c0c0103d0006e0700300041c64254015000340b441410181e2040d59038040290107110741220000e5054000310507186003122130001403e184800903000103801ca0130007000f40d0848890101c4800030071404103082034081d104010960904149203481035501c1000c1c200240e9a10110704088180326104550140c2510b0420490420b690055018802d500301006901c000307 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 854036834 1250 854035584 854035619
    0x7050607051c11220f0e0f0c1303031211030f04060509060103080d09031b1b0f0b04050907020c09010f0302042007170c0a110f0d1518020901 62
    0xb6502d0001c07141c01c5030242e0784110b01440d9880001149003c0481034580c0001440c802c216a11203040c9201040d501d4080c00a0000381c08004d0140700142024001901100c10080c011510100c01300411041d40000c00545411241d142c104181070490355240031002c0e242c010240c40f280749004c02001320540004241074003541c01100e04005c0da44400c14826180c2d2024040601200c9003000314500d51a11503008074086402460700b50304100c86441c214100481c1c0c0001a24103000701005000c2c0d85100404000061080d1940740316503a24101850206009521420340b09000709000200380900070b0081c0b10012a0082c8070202c1581c40c0c2d00c0101c000011030000780e0003180303803241161480751090000c09032481c01000860415105582e11421116540603518a510050000e8041c4000411a004100703202e60011803d1201d0081070000c1c00d00b10b0350100d88903811070702e04000070407404e0481d80e156074038003070703022542000400461044105001c0000e401048440001600d8840090300085 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 854038084 1250 854036834 854036857
    0x313231009020f06160f02040b100305090f010c09060c05031e040f05030a08040e1806070e0909070608071101110a17060f030607123b0d0806090403050705060705 71
    0x900300f50020522040b40903840003c040d0424070030341040440e0180901c2c0388071500c002c1004c9070030380f84040814810b8151005c40782c042603c8009110286000f40302c011400c0c2d40b138000070405074a02401c002c0c0310520314411b02d42405000c1c0c0010041c01350a20845030a20715002407608016180d80c0c0410040e801841180c559003840d1b600410780703140100d0804d08154010b00f54500b4141082002c0007414000b82002c00002784a81e01d024421005002c40c921903001c42c1c564540a81124080c002c003100c0082c401231140d0001c0c0020301c03c0a40080109400ca4414606049244080e800e102e0041490b07041042d6403c0300400c030685407a90141814081300aa002c1110080d01d495043c4140c44000c0c90300d9641c903401c114001280c0302d12038208a5013100300048003181c1c1c070b032004080b00200c50944098480d141480c1c065070103203075100d440981e40c1c00c841070003c00440721010030003040d1a402038801c2d88030302c01c40c5001c0b800b4148100f059a0001c0c0e08501030b1099400c001c40040d00030b9000c00003944 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 854039334 1250 854038084 854038099
    0x1060f170102030903030106110f0d0504090c11060a0b1810032d02040203090304030f210203160b0c0408030d0606020c0d02031203060d08120702010b06031323100902 73
    0x500001030003500d0044013031000a50941c4d0801500b034642e400f4080a50030306105402417011482c100300001e1201120b2500c0b401c0c4d0b50750400c12490f0690b84a0b17056981071107103510174192120800036880e64403050340f090016606042c2000200130001003001203c031111000b0074040510940030f009000c8903c1915030031a88140300d40b025014910300800b100c40c403000505041c015052680041d6401640d00090b01c0c80d25031030748e45c0c03c1032030b01400320142c580300204010801540014008119200c3c060300045082a2a01d00d03483c82e520a44500107005c00b07580c1000c1051b0727640c6803007528003501010060703940320380c0d002400c1001040d142c8608070043c8607040ca10b59050803d010544000358025028043c00d440802030100c203680050505500b0000700380302080402c07841c0010304120b2024007050001400c001c4802400e5503006c0040d184148010814000c0340800030300b40c080c0070340c0c2c82120f041019038119490889921404070803590381c0560502d108c3d45448503405106018030032520702 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 854040584 1250 854039334 854039369
    0x50f0c0904020d030c0c0b0c0c0306010e040b0c090109030b0412020618070b03060a12032106050a142e1209110d0f06151d16140c01060f 60
    0x1105100d015140690490718888000c004a840303004404101d038051803990204d03d0b5203d51000540d0710810501d8132680000240115503c1c05003c01401440006c100e00d44504050300d0b803100c07485000d0140c1d82d10310f400091805150b4041c0050a0081d500403c0d104030700d103024206542c00b0030601d51604018001c1c0390005a482d0021990184030b800e140c0020703c9203d0401c0c003982465440941076660104154030f0019004400b400c2415510340b00f031b595551104d100c49807806200c8002d90b032042c1000d050810610240d203820800a00302c92041280d14003451206020959010500003180401da06801000f1002943d09008013500a01d0341c0c4e400f501a9000e2116400301d82d003c0034010644000459410010b1804261180e0801c0c0030702a00c1c407521a02d940c401017104c02800c19a8140c410300c034420461000c0c00c0110381048102044030541c5407421650801030354850b1144601441000e00104902000c6603051312280c0d881a0020482d0039150041c8441060207449800743c0d918540c03010 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 854041834 1250 854040584 854040589
    0x105180604090b1c050c01030e010b0a030503040608011212030221010801020c2802010f0504080a0507062607260a061a070b370506040b0411070b1b030103050f0c 71
    0x144d0740c0d25410102074511840d40200440140000d020364840325034880c403070414136590f07040d5044015403181000396611072604401030701d880e505a20071051030a60410340e60100c2c9116001c1400e02006280060f505c1c42800f441c00109a81c00c01c04011001400c8004910340c40154014030940742071b03408881000405c2c41c00d148544074103401c0790b500040d09a0f04040107501800b14000b80d8030340313400c10a05164446007150320700304940406885d26441900c2c01c000c1c0d10b400c041e01545010f00d0b552414143d044000c040001e18070301400c403008001c1d0003404840d006092100758540541644109032203810a050307003502401146c02a10400102401c442e03580504800441d074080ba03200e88920102d030b4484a007010a0524410500850305068540190150301d8044152003000c200e0b400044c035040c804148400c03203035090001c038041c070b1518000c00082a0940140c55500e5842242c001c4079640d0100346030500380314545000044400031001000304038003c1400811505500210b84104802008 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 854043084 1250 854041834 854041879
    0x1501090204030f0605042d02040c0c03051e0c031308100b2d090403030c080f01081002090307030606030f03030b040b010c03030209041b170f0705090105180604090b 72
    0x702400c419a034640c0004845405c9250f0003800b82c1d0300e04580074150301c00b002c0070f2242038400c103032048080701c01c2400318031301482a110a540246005204101d50b81e4000c0c052388101000e040000a2084441016094180846054010b22010384c1e8503896002c081c0c0c403050099020303006560107001003591028485100305400341034028000c00341d86150b16107070306500c514095000c16800b0352580c15022501d9214403140500c0c401d58002416042903000203000c07113005013201d0301c200c0d8414010403441c00001101940c0701c80910006903a407016200091600d6565400100031904140e40041405001200300e44058000e4906100c2d150082c1c04000c1190001e080c80c82c0455000c044402c046807095001c0c20801001500004060320108080d80c3c50030400682500000e90729040c40300c041c15070030425a000107180c42104c1003400c1c007160140c030b24000c0205082c10844013142d00440b0044da070144405010024041d180d4450b00c03000210050b00714a0b1905005011079107080305603040085 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 854044334 1250 854043084 854043089
    0x414030c030a03050a0314040f020f0d050303150a05030a031e0c03020d0f03021b010c1d09072601180614010801030204021b0f030a23040e04170c1501090204 69
    0x10082c11804405540580c4c8a80050a681c400c06540b2401c2d11a04d500b4640402c1c06540201503802c9c2d414171034410000904117413186507003d02d242080c02000a100013055a4000169040001340c42c1c0111020074a1400543d200b07560500c200350100e0b05264108010300066400218400002c030142130381650701c05000b5100900507072181c2c0c00000300c00d11914446040119170f140240c94050598070400014580c0e00b120301d0103075980c0150710149900710484030300300c0004403045140d400c8158001004514001c12080c2800044e401045040e100050002142110206881e00958494554804000d40180701c1a800b41c0340000c0812400b0450785183e00d400030507591007003035a08590900000c1e401c10141a03146c0d10315103461000210080c0b000360007084007440210788400c414107009040c490088000040c4058944810b50b1a0304982c08403030a461840780300320410b0f00c40d450250548041c629012141a40200341502909804070b02c124162000303111030703c11039880e04c0510040303200780d1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 854045584 1250 854044334 854044339
    0xc0c191536080d03151a070602031b0309010504020a170d121506020c1806130c021603080d0c050301080d031805121b010b1008060f10050414030c 64
    0x220142441144010301c03025625080031412540503a2900118600081d0010b03400100340c0f2010003a070708034003545d0100010808140d030450800e03c40050300d90305108980028007190703000400950400b1070300142003a112088100e8940c2c07031400c0c610581c0208802e072030481c860142b8683c0001c3c4140002845401190244054904803000307140a80391800c0c507800c0700301115101d11110b164000c0346502500280340640141c22500400c2040001c0110048406a4880d01600a100d05c03515910000c003880c4c42c3c0040000f555825032031059152104498445106526101c00070040000c048050002412221414040719000c9003050394980003d0181805603808032401894042c401e800045114040601c070341e4400d070a5403600381c10810701a48035108442d001521140c3c42401031403031503803200c0f0341c0000c1059561326400940509012501c540030025403901090540d82c03000c10210b1501301c000c01c40c503050f030966074014107290030501c40d0484403408100c1c15400c03401c0c00705a4a40c1d45000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 854046834 1250 854045584 854045627
    0x91b220b070b060d0510061509080325031107030f0219060f0c080d02040b0310090506091b09090a0b010e041e05270304090f1806020c0c1915 62
    0x825080c00813680f903a24003502c0170701c1503442101e1aa000c6103c0c03480074250000080a81c1c2c024032401400c89440c07944200844d5000b00220341101e00440398445a030016602042c3c201080c6007012520f03d0344030101150b950040e41c00000030032100f80d1038100b445100351029415000c115482c11150f0085119000116000c1d91140300c01303e110340e135144155446030300c01a003401d0800111200301c0c0c020360080f010004000040c403d42030b480108410042052800920880c40c0141c04a00941400b40003210500d01c401140788040000205032b801c071450140c1074031403c0c80c00280c14005005003811007400b00d60b40d40c000c5035203802c06010b501c0d00c1c02c0d52840d101c2001c60725001c6580c02840000c1840190107682a0b16910140799a5400e4150135511402103480340c1c02d084800b800c1390b0220f429410042c0c80c01000e10142d8036104005a609500214016291948000302c0c80c20030304c2c44448143d000ba50340c42120318480c01006008251884010418100d8480349425280d00582c0140426079191 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 854048084 1250 854046834 854046841
    0x4050a020906041e0b030f0304080d050d060b0a03050f06030f06160203160506100f23030106050406270b2d090c22060905091b220b070b 60
    0x400c4540c0942180000d0f00c0080c14020640c1c1c07010035400c10f0680d030801c1c00d0300c035002d0030143d00e02048100d05d11002c3c0805189014a4444030b80d0b03684050b2120700041c44004286a01d51080d144e000130001d12902500c141e0310381c032501e40140140340c100d504603000c40085c004505181800144401980d6220008000d69121010318000004080e1919400c510081000005a080380d480640540b44214004e14440c00c002c0c2c022a0402019001421400c0d0700c090f00b00000160003401c82002458103d4030b440c3c641e828408607000d054039800c620741144c00d06e1800603151144030020440c0c0d44c9401c1e051307010400b5420b080400c0d10240354a0311b03803100341c45031501c82c00140e4003218458072826510000c90002c5001c089000c0400031118803e000c00045603440262024280728002e80845490566946040400241030a1070f50301400d4000d0784410001140d0b4070340da01c0040008140c07078015580712a0a03003c40d03454208800c40740f03600114004030000361440ca031004e441907075a00070f207500103540e03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 854049334 1250 854048084 854048089
    0x9010f02070524040506040602061608060f060304050703120c0317060307360c030e0708120f2a12030112060207032318090f070f050415080f060904050a02 68
    0x2503507401070620b4407000c1000090b581e1b1000c004000824154000d80030b41e28080b084464408031814499051144250810032540c1d9080c14081100d00e00f00d0300e15803207490380d00300140b50400c035400041c515104000710030226030300900c4507030310140b00b80c0d25040301d800400940883c41c4000e03134a81d50145e1002c5414404010301100705103240502142c00d0180540c140c3c1030545c422992003143c281a039442d4070462000d94140280b0721503c1c50b00004020042c505a8010365a60b0210381e0b01884a0700440d1000e82c2c441c94800700d5821110b0104040d0740c02004200302c2110001d10a02040c581c801c04500440d401c051074103484c12a0740d80044080564000e81310744000e0f52180000301c1c01c00840301078030001c110080045d11074183c66185c0d601d440c1e0205c0d5500c0c01c10000d080000510071200d5104100400d50400c80c656481038152608003242d8030000401d84603800355030054042018a2200003101507802041c8501c1070382000b103c01c805032074900500074840c009440103040c0f500406210310250 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 854050584 1250 854049334 854049379
    0x8160b0a0c050604060f0f0509060c1c0e070f23040f0e03070c05102a0c0302090108010905121812100207080306040e150f0408040e09010209010f020705 67
    0x10344103052460341c070490340e40c44038240001128100c420943c2c0d221211641c070554400c218000c0d82d1510100138508000390041d5503038200030b00746059108009944090b40250328030f602e401500d4803c090200a403600d207095202d00c00390040a04021491600040316600c40b4410300c0e15003041001544040c84031418000a072010301004840380e529090900c0007500100014003a850240c0215011907040408000d43d28201300345a43c00c104c101e0614900c6415511240b60a04802c8407405400080901c1c02140150782c503400a54040031142c000660004103411000c0c26522880c1038482001c2d45101401d014041c0a01031180d403041100b035000c045c10140b000310040c00c0c9403001c5860303450a48022400380c7c1e020500c1100e0120740030091003141d08050240301e441c03c009901801000800d1000c070340c4a44030080400720b940c0d50f82000f20b41804204400c41d00a0110341070812000d00d0026480e5020358015082c1c640060f10703000725010034910105260081d984000d0001c0600507071229a030070070 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 854051834 1250 854050584 854050597
    0x19020705090c28090e070804060b0303030c040b07020d080408030705010c020a08040303052d090123090607031106040c08160f06120204150206010e0c1204021c0f0605060a08160b 78
    0x501c500d044005c0f03001401421072500c200e01559800b00c1514007450711100303032074000b00203601940c4213105010607030250400303541c1a602400101900c62400340001030b10483ea5004c0034180c1c241c00a00441c6040001c00286040750041009002d0902a101c089035940e88404014000781300512051000074400c44c014011901454554104138038090745910f400c2c0781501c0e40200440000450ac0015600104140c442103100500d0003903840c5501e81c0590709104040d49a482a41c0004030380c010180207546140350711041c0b80441c1c109161034605008a08403a015001c4207108001c9103c0002000c4503041050350b2416000d000014a844010340722400c030800100c414030f809200209589180801d417440d0055150f00820044d40341c4441c00341400e00181c0b42c884940d2081007060020143e42c462140c11650540d074840c1c0029400e13001000001c1c00c02001032106150901950034000d40d504254003c06044401c0070325a5640c0d05455568046a9444180454070368400c0103030250200c0070700030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 854053084 1250 854051834 854051837
    0xc06050d0e0607020f12090303071115160b01080d1707090506030f0708061512070e180a0507020a020f040c20010608061b031302010519020705090c28 66
    0xc1c001c1480c0507140c100101101c0c2c0c0c8005070301c1140300c940208010043c6081d440e010845042c40d2400d031502080d1280301d61f01c0050b0041d504c601d20007078161034065090399409802e402e029100d2605145c0b14140c2c0c1a160000d80383d403060f2400200e1a40004600c0c4060080d80f0b88030b00030045403218880e208180d00404540600000b00f0000441e81c41d07550040d0303c51100040c11115a1030400ca004d090780d80051310450248616001074107503415440c01304c440303404000c0301c90505a982c03481c0c100d41c0ad801100c54180c0008540d110060f20b1140301e40124010000344e10f0a004503542c191040303958100d00c0750040d500941c000d0b85000c003414a503210014003500c0d4688524500714822244200416403207540c503507a91350341410040c04074240300540d00000b009070307141c41c0c0201e58610720f5803d010181c114040d01c1d00c40c0c104001160b010380e00301d03404100c0030520f105111001c400040e40340d928070f116890040e8200700001d2030303000e0140201d0324200258a0320044000f09500201c03414121040d0440 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 854054334 1250 854053084 854053091
    0x906060f080411030c130b190501020303010308180a0b09030705030111041a09040903080703110306010c1b030203010e0c15040509011701020d0615020c0d030e01030c0201020d020c160b0301030c06050d 88
    0x16100d4a804406c04003007030207003d0104c0c0c81c04c0c140080c808404440140c2006c0f081c1c2c11241402242c3c1c0c003000300c07811a500220140d40b60603c802e103019240203008419503001c20b20307090000b86084003401030301d0010812401c0e6080c10382d59030140350985071802e50741929450304100912940d80340807103040c4400c07020110f40b41803c41c0140424211240c10300c4c2a80401d41b000f0401c034410b685801451142e0010f50021800c50428000180c4205100400108145240c8500d5984802c003201c03150700441e0010001e0044000307406110780c6400c24104464001c0010504c0c0d89400120641110b04540000d0001187d84c1e01c1c0c540750502c4403850504504040d5001c01166001070f00ca4003a1700d01503c100020b08900480d207440182ca45a007520341c07140a1f441c42d0840c0e801083c0c1020015400d11000c0c280400c44400481049009208640001c5c141030b10108507810701d01000240c151128540d5100200060b4649211900c1400244002440d400214109100281c455070190060340340320756021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 854055584 1250 854054334 854054353
    0x25050405040c0c050712150203070219030809010f020c03070f0203120d06050f1002100e10050f012d090b040209040e0c09070f020c0d020307150302040906060f08041103 74
    0x1000d41d42e800d04410001507000030001c040c0f103001d2003000c00030030a26440061130307001da40d5151306540ca02503001c104503a0102c0061070181c02440f00c45c12440240215051040701d51501400d200c405aa108420790300e8502d024a0f8401c1a1003150708082c10703800110b0610500b0b030380d004c4c500014408100c0c0c241c015255600403055591000c2c100b000200e0074086001428102405070240e0303e49480e6118036012400c09001c41e4022954204640c00300f040030a00c51800500c00745407403003800c600b10b010361400302002090880d0582c2e0310305840040e92a89080b442100c08014500400254584100380300241000100d12580c00f29514603400303480581002422400102115440300b480c03030090308041c5922083c0e01c0e007140c15507800705403820500701c100c4048100079601c03180380c3c0005000383c9550000e81c0c10755404000342d0009111506078413a2070f00b840320008020750040d11810038550b0a04501085190180f0301b132110701609952003411556a98403440030184520908542601940912 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 854056834 1250 854055584 854055589
    0x130c0e0d080d0b0f06070f050c060d1d0606031002181206060a0501140901080603152d011d040201090504060902040f050609031c050d060e010603050a0525050405 71
    0x490340300a0052810586441980211030700b90f0303400c682404e10450b640c0c03181040360307a50101903503880f58000840d200d02000e640b803d18640344482c241d09500c6900820f02000c41221074100a0000d00f8034441040d11103442c4480c9540e40b1030945500d545608240000b1500285641c090040d2700d1400441650080114001c02d0204070b0403411070300079400c248108205428104a00e80c0280001c0c605055410b0031104d003200381d4022146510304000f042c201181503681e08204800745081034109050940c02c210040040a0f4050101c01c4441252024101290300b03010440c0d90495071480400c001a68a09134220420140200704a050103d400c00c04507842c1c03100d1081e64090a90510b0044c3d40b01d081410855030340c0b807540d01103403084804000168007620b0110f034000c1c103a0344012001d81d0800c200c00301a5030b42e00504240d4600a440d01100007800440128558100e07011514100110b4441400c03100c151502100c0f4a01d18102c1c1108922504840c004a0358410b8010316000c2d00b069180d100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 854058084 1250 854056834 854056849
    0x9132d1e1e0c0b0f0309190210051e0f130602031303020d0f050109150b0d120f0504032f0603160e010302130b090109080a050601060e040b030f010c021605130c0e 71
    0xc0300c245548000c000c06c6280b40017040000d050b5240310380c0829096900f079001420034450041d8810030030802084243e0070a0002c407171401c44c960890000740d25100d4201140c101030300700310415203e180007542c0004600b80080304440000c6811801000d01d1404c640034800503010300d60044a15174031242c00c10340820000e04c074480880b0b20603a01019088e10140203002500d5020ba01c440c85030411100040004102c0712610740760091038102030080c249942c205940d42d01403070344044c1089095541c040d20520719250441d0400c400e071403036400c00c1040da000b804050301003211103083d042c010490320300c44070313018451380b4105550516001d490001450312070101940c06503c0200101004100d0311f15640c0c0001c0301c0e1024200c40001400078124030340b07815594040601c80d00c400c0c03040c080131250f015101c0350030400300c5200180c121400500c001030414000c3c40400e29100050180c10749404c101107010031860f04560009001ca1590710304020090b00808203c180501481802600ca5019031140075 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 854059334 1250 854058084 854058097
    0x4020703080901060f062f0316030f110d030e0f160302030d020105041a060f040c05030708090c0a1701060306051611070509132d1e1e0c0b 61
    0x1d0350740080b0304040901c0c0d42910040d401400455082c844140300300c59200808090120386000000040c0d281016403161049410500e8a0303140000a0510311600046202550682c4240d55105201c0b80d0341070104c03100d0045000f0200b89401c09600c1c0e404840c80ba800180420860500b030340c0010905468141c50200460466080745030910020001d40c80c0c180011262028280000d00552600760380310101c03c900c1a41014100c14110007040075512090f0080c03201000c0031f84200142408a50b020b03182d070700f00704c9007440000d0582001038842c40700031846088003a806410301c089107080c14242c07030240855800c0304c07200e0343d42c3d13000001c0800c0b500c0c002c4074002c129910304851400d5070140c0081084911861245443d406404200096212025595484680e041244211903080d02c0d01e410302861001241d0b11804442c203045008540d9203c0c1b29012920540c1184114000c002c0b03c00c12044040c0405002da011003000c3c100641c4444980009442c860f0b0103020495403038101111941e0044c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 854060584 1250 854059334 854059337
    0x5070f110603090708100e0703020118030215030a2f070f1e0201080f2401030e06011e120512090d05190201031404050d050c01060f03150501060906090509130204020703 74
    0x4401000fa0101c02c0c440840c040000c00400c0c42800c44407a0a03c8c0c4d1140301d0312000341041100d14400e089501d00030440c00c0516401080b608040c920280c0e4521306030010340742c0409445c13401c2040d00143e43c14504284184108003c6007443c089050080e03003240c0c1001200361a030180091100e00014129021200c005a078032038809481c17502800018462000102000a000949014043d0707040c440c40040c9111071040d0f12039a40b43e44402c0c0100e01a140140510002d4445c0c1c500220740c003100e41021049100e400304000d078a04e075482d50002e001d40d40105014080c5c0c0c0048698108d10790901c0000c0608a43c042c004113800c031001c0e5106032074513200100760110703890354400202c219a40360146900c00c014050250146041503290b850316100050220f03004d003c800220002d48450a4200b50b0051502d1300c118110030f503a80c00d007103460a541c0a19003128525110020510a01901024094545035917404403c1c134203220900c009208003411011408101c10842c0300140d507507000408209100c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 854061834 1250 854060584 854060593
    0x30c0f03051504200103021209010b09101d090a0c06020c040b090f1302280503100c120f1404080d050601032912030c0a17070305070f11060309 63
    0x450900c1c0b0305221203400e0710050000801c051101040207040b26002ea04000055802100101001070340207118203152003511b050306004000c03444006501c034008646095481016540d1598411f240c940c1c4203000c0c440c481101190407000c03c40711110381d0360b84005218210b030070414254540300240310301a4808001648501c5c2035003c1d50030f15001350a442c0b4003d407544580c42c00d240450b1061240028902100e0b0300c40c40b2152415960f4001e078030b8002022002c01d400c0690001d10707250b046010300e80219800703840b0b0032880382c2c020241c5104403503903c1c500b82da0f240e0412500400400140c410100746110440e143c50b98040600380f2144140c1c091445036802c156030740c0e6494011000d1720b00081205040c903191411026001100030304010746444440c040006170313841003000980026407000c040c0454032010642c413014110002d8041c8825006500c0a8641310403038008004601c1900c500900040007408a000054084a5581741c26480740c1d1042c2000144c440110304c0329001116241c80682c030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 854063084 1250 854061834 854061839
    0xc051504141008060d030c06050907061707140d0f0f0b030c0a0e06011107030b161e020a0609080910031d01200f0d0504051608060f0a0c0504030c0f 65
    0x89901116104901a40c0401d00ca0b102444098030118005000307501410008510350704041c4182d41090502ea13003c0c00405c130a0500d0914103030741d002180507000c0407a120a1a000442c0360102019210301041d6032130b10340303074043c0c41d4400c0d001d41c01410310300c68010788403051402404214003894558048d420400946140d00c3e800309807401d91001d102c030b801180b40c00300030300c8900d400c8601d10781c0c800c5003828540c101400401110b80f8001290380040c203441c24034000c1c000d480c110700c0c2000304a0754113070ba14a80380c0c140c03440c0c040440100c21032240000d0303400303460048009003c2ea000b00d10780b10301914016003401a1000030650800e0450102400656a030016205ca4a80384041e0f00080058500030414102c1038821004c1000c04e0b045034104020000c2804031809030044201c420f00c082a042c10b000a04151400643e500c2046c1340da001001c0c28000041204140099107500c98041c0c000c004580d81c0320444118020803c2030113940800108100c0400072552041d0544003c16008400c00305851 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 854064334 1250 854063084 854063099
    0x312011e05180a1e020c0d08091c0e120a030e0306071b110604080706032a050a080402210601140105070309060f0210180c08010b0d0b040c051504 64
    0x14441e00168821514111980034158a50b040980e000c0c00301daa001980380000803030740400b40300720641510510b00000d11860080c0011980440448050326a14108c0c1c407103007400b9842d184406251340c03a5020044e03c8a22a030320400302c1034100c04028000400f03011460200504003004480180c000c242444c0040250341410064a6030000d25894640f5610460352400e0342850000340b80907102500c60f801030000f555528003128010000130f170407601d0460b683c00014016003103500150704216540600c221040f0f00d15410600c02c445243d846500e031084030321003950743c002c024000b84d030004a2540c2c1d0700002194060342c80411400c1c0d00040c101580741c10612106120318165190411030309210b00d00000c2e1300f10b12550140c498a080c00d1001801410007285004003401c03500c02440d0501c200452401d5001391118034190044018400c80c58403585000e090707959002c0400c0e0802030000314440821064000769400c02d10480f11004030a036104006012804100c05080c3e03070200c0004d0420420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 854065584 1250 854064334 854064389
    0x9110f010306080c09040203100c020a110d0803041e06020307171303170915070302070317071e0c050d0e0111070b0a080901091b23030309040905031201 67
    0x101024a000d004050900b0f9009807110100c9880380d000b449080041801c5640c1030056143c13480c84a07d04125207801c0c104000e41e50180f00c10b05807800c0e14030940f581802d00f4005000d080c915000940f20303285071a2075460a07156403600d141403c480326a100240c0000782140000c0d4012071041d61a1703030076802d100d000c00002c16400342803803680140260040d00060b8001407a4440c064002c0981c83c034540e164510182046400e80f0380c06d2080002e50200084150180c0c003404105000365140041000b20001c011900030050b01e81c540401e040e800e00440c82600420710204611451a110a05200695840c0e10b410800300c8100086241c05015040c1564445000328000c040f00703004103059440d00d01085818070803800d511381040781e4032000804d50340d025041600d503554400d540584491003a0086804040c250040c0a003402030300e51100c0e0085004070585681920045c00b031840c04001e102000020300040c0d204603401e000070721503c44a50b80e650f440c0341c0201015004c101c04803a910b80021a80c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 854066834 1250 854065584 854065609
    0x705060705210402150903030415090e0f0f0a1a030a350d09020f0d0b090c120c0402220e04170307022a060a020304081209030a031b060911 61
    0x1c100e181c40412003d6919021030643c50b140345c40c0a695107813440e1001c241148039039003004000c2050311030788400c0b20340d010f00c041f4102e8514060444503625091280c04040d0015640040c0e01305007200448c1290103180c0c01b09600355424040340e1495090764010034280b50501e4825290701241070307e030aa0b0406075550f074140e00700500860020300c000c4800e114840380160860b062125558072119421500c982407115141e410090030035507001e4039441c09203030448046580e07003003d01550a0407802410011829040d800315240900b0450203a50248402500443c1d0002030404840340711a22040d121400c842c05031010070080502450310b810300781c40c61103100180c140f1f9010100100607000d81c1c085454103940c06900f4601d46102c0240360085480c00c100c80420742d10140028058002c0382d000001002103400c0b000035102c0c090a0b02403012018010030340c001c2d0300b5070403240c01280000e1088051944c5800315204015009070079407501c408482e241a0203c4001070b1a82c2000103e150900c4880384 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 854068084 1250 854066834 854066887
    0xc050d08010806070c080403080c030306120105090a14030f3f060f03010906050c0a0801141f0203041203030b011215090b03150a14071707050d020705060705 69
    0x181e52401c0041c580c1c0b20f00090019042200ea04550000c1080101c2120300a5800051464076441c1311464242c0700d0380161070746442504051041c0f00504018001c2a100342e049401070503500a040d15544036800d00e10030118001d000810403410220342c0c50f030207042c52041c5046d0b241e414140d0010801d40701111030350b40504001c4e4100a040c100b40e101074450740d022800750340d400f0140889101003405440c0b0321070010407880c02c18082004034a0b001028240d144d901c0d82d604442030740e89101e040540d000d090080ba4000c2080e040f102d010b600d400e484008050388910440e49020f82e2069160302c580d0011070202c0004e40c40d66a041c4003580c0c40a401a000600300104002c40c1c004c00d085c48014100a200d030018041d19095650300d25501071100320034418030080f40e015586080c5640b070740241001e01458800c4000c280119410900c90b500034a0901d034014101452500c48200546031a04161510181c40c0c0c0c081001100113081808010300030842512403903150450600305000001c2e06403100740 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 854069334 1250 854068084 854068097
    0x50c0703090b09150c0a0c060e0f0103090230030f04033f1814041b091e180c110c09010509060103060f060e033a030f0c0c050d 56
    0xb031159251080c4883c1c0140904c85259600d40e5011424203003c406500a41a1001c00000084164100c52400d0081d40c08507000348002c1c01c03107030040d0100c83c2c0000c0082d400c0500001403042014101600500c1451000c40715146040786040603451039200c09884015250701003420010805c0481c0700c28140204565007501007180b03a014415006410364849001c0c1c031014803041d0090340188a4000368500c1c00f90303a882c03600c1c0c503041a044200d0010115500036417920104124154090411024105030350355510031041c0351814031525800c0300c0b40d0042d068a007580c40015040420b040c0d850700c00c06004008144002c100ba0058001c04550b03001c40850303008168150480c0e56940c02880c1503510403a4607460304d894080048000342900c1d00b24030200070110b0008200140c2010304500760181c2241124200603980b480401902031003420200e00e400b00c001c1c140302803515400c608060454602d0009200c1da083c1d90040d060b20400340d608004142921401c50900c101803011020329681b5040c0342c03 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 854070584 1250 854069334 854069347
    0x2107110a1403240a110408070f0f080a170306010203040b19140405031f0b0d140c0d0b01050d060f020d200c0303180f010f02090103051008030301090e01020d050c0703090b 75
    0x82c203c03030b08028210318409564032200000001d0240559018110300c500b10307210700e0781b210340b41d80207845140602402d418172480700040b076003400a03290b1040c40e4400082c035100c0880c1d05052025400140c03000713043d4002488081a000d4250001d004004c01842211080403198040070348007200202c1030b4005039400700800d016680300090308132601805c06495046581c1001201c00c01000841719183e80103400000d84c80c1400061049894112411002e403a1a0b00d8070004100c22408415030040c2240400401000703a454060031202645000e0320001c100100da4401010803030b480b0b01c1001c030380c1c80d9880311504031608000d414018100d070fa5031180c51420146508682e942c1c0001005080d0008076644c1c1c03448501d40c280300442c00e54003624001e0105990140420f80a50080c1204c14006032503c03000481d1030b0200c20702501254554009185141d00304021407002d042c03050040c2501d5034080200c0040c1403642e10902d4800c84040c0191a06d0f20400c0c6001005a11640d111000454050011 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 854071834 1250 854070584 854070643
    0x13110102011a060c1c1e09060e04021c05010329060d12020a060203091c0215040b0a061a030402010e06031522020325022107110a1403 59
    0x100784000403ca569603201c59207060074600d44050341481609001d02c01c0842011160000d00c1c1c40c06082068041d0384540138481c20031100030002e44078000011340d402825102508040e0b0040440000084000d0300e03000d080d400e40e200f80c8071b0170f03442152120350703040440c0f40d07070fa203a200d01100c00561070010003018100800016405e01d50164060b0030b0b282c910a0b0300050700e0080000c02d2280c0e81c8a0003e42d1207281c10554070fa200d0010108050554001e9240c11001c58800b04d240001350110411a02490700d440d19188030343d900090011108070385e90070010808101c6400c0c4415400108820150340f460203200040100d1044200d143c000c100a03c284040c95800491034042c0080503941001e0019080c082041002981c004c64800d0520000500c400030b20384881c0c010515084915005404004c842c0881c0c0d00d00704682020902601042c0081c0c034800c96070028411640507070540054041d40d5000103155042641c0038807440352041c500b2580909007070000c1d040000e40807162401c080e8103c00d6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 854073084 1250 854071834 854071871
    0x302041a0d0b090a02040302010305221403160c03020f0405010308070f03020a1a040c1703090402030a0912050a080f060108070f03090c0b090909060c09130207050102031311010201 79
    0x600d4640340502181e00c401103440703036101111481008050f0300c11420018004c1d8020352040c04141e002a0034440080c5489140c4640b4140b9049000290b400d10411910352113a449080002400d40d030204209503d10b10844e00028a42d1502400e404401285103204012070340085000c124040d07801c08004002007402c00b801d481c0703807030382026800e502c0407401d01d4100d0411650603402003a0080e0351a04002554019824501c90b034031038844c0390302d45500d410440e00000b10114850343c1903441004800614203040d00516000b101070100491950b0503070382c0708001960b40c03108100c002507001c9130400540c1e60018660b50002c0c01c203180354800307050040c0024640c400081a0105202400340300e4140c0da4031960201d078071140c1107a08080600c0c0c031203c500c0b825038000c40749144100c6091011592600011072264010f449001ca45071810102070b06014501d40700180d0518000e9090003c440400c4c0300780011071150200c4040ba074a0102039203000034181d06003017176440c110f80c0341942da18400701d1f1858 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 854074334 1250 854073084 854073119
    0xc08130e2a130b07200301090506060d050f030a05091c0201020d0e13090809100e0d02090426030103060f021201090e07180e07060f052a0f07080d030204 67
    0x40180d0303549a01603000810410580c1c04039405100000f550380178044c0020300080c540c0c034100e0884281000c071004041c203882041c84080d0268101d400401c00914185103419081403003a4240c03225805110b1489040d5001088140c010490001b1401802e1518180220001501060b081641070554000079a104601e0340c1400174006000601841d580d0381c1100f039a20b00074614000d015280c568038204ea4aa0040b007513107030013030a2042d90002c04030b01685003030110304405051680585019002c000d0f0038800a4020340e50314450410075862030b003c03104c1c9948c040001e00f216582d00d500d5403408600716140801036220301e03441031264800c1c201c040c80c04941103032104180032854059a8404500381030641d80801791110180c00b10740e00104154004e004040418001e542c5040c1d034900c400c0c2c815420200d103181c0080e104102070030941d003851060001d0291007051303c45084440078461072411481c0d110701c401c582e011403c03c010100040200484c3c0d04404d290a60400d868214070124486208 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 854075584 1250 854074334 854074411
    0x10b04030b070e041806110c150c07050d0c050d210506012105010e0609060a1e0e0f09071a090d06180b090d0503061003020a0c08130e 59
    0x203401142046200350304944001038000c20400118000d843c0c045d00079001404120b0b00c407428070321454580318540003035034001e10242020340a03600350784a42d4900603100a00c0c1205604091200c1c00c0407034070400025262084603100c1d000091168200700f80b418241c43c0302d1408000c80030364400c80f8022001c000503117503041250081002d864440040c3c80c40e0744610480981c401070031441c645e1101c155009941200d82e03414003c009a02c0701c10500020045c110703000340d00141040e00c2003201c8050300f04448021038a984c289041c1945030301824014280a841e803450301c004c0c181c140502445c0521a04009220607481c0300804040c18881c0462402800d0f0172510070300e070f40d48101d0b043c0070041c1c00100e4401150a0a000048414030f017403411030b0b9040d20001072074461640740004c1c050103902243d0080740c008100200402c0040c0040340691302400100341080220700c80000002c001d58040c00b640c2aa50b054903a400e8148200c4d4007070034100800c0442820552401e4075482641c0401144801e03000c0d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 854076834 1250 854075584 854075603
    0x105031606030903022526070302010503040c0e010b090907030b150a031d030738060f10030b0418081603181404110720040b06030a090317010b0403 65
    0x11130034245c4c06c0c000c841c014800610380102244500614903400c0d8410b4508140d400002d81d1300540e10f001d0f03041d01075100000290b00011092000d51701644c007955210f880f84002455013900c42c25005003010003a07110041001001c0740c50368072454040602d540c80030b601c1c41c00300442d0350703040000307400000b00c2040403880c0c081c00690000001c2c070a0b082290f070f011043c2d02d01007845410341c0c48259250f02c1464261240c5000c80294107800c0040b80d42d480140001a84442000c0748268040b4080d0310090f00d52644043c500e511008541c5607007208022401050714005000c0c08880d0520090340c0400d0040d40501c0c0c420010301d0000f403000e4050f540804409e507500d120302002483c0aa0f41d04118028004240101b0382002408405001c1260345101b0300740c805101c0051440300c3c8003107a0040c803030b0092100202280b20760b17810400d035980950ba5003004002060540002c404101598002e641008400303407a040c0071014150000d402a50720300054480004075854800c41000d9409039000013404180e2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 854078084 1250 854076834 854076851
    0x9010308090f0d0507050918100f090b0403020a031d0102030d0e281203020f0915160308092b0302032706150f060d0b0d2306010503160603 61
    0x701e50000840303030000030f01800c00d403003030600b00107070b84088500c245440b9196140009100c00321032124440c906188a004020601c00e0754001c10280c10343d00002103086036104c400001090000b0841d0b80224060b0f0042c040103031007802d000b001d886c694203c6401c8502c029840c400740d41d80c004122034290f0469040056045001e140321420500c1c68050883c1c118603a164400c14881803c40c0e215039644580b182114208444074103606901034009252146442840300d030203182404000085d2120301d4203020383c0303060040c40c8000c1d0b005e1605c010070380c0011401d2081104001d0100803885200800e003804800f04003080d5000d0300801052014071080540110110b5882d00c01e8140100c00c294801c4542c401d803001c509080d0355540400c0340d00e007020a03c2c1007441c504500f1301154002007150003400a0f4500020440924040c010020b0865000460640b5030004200020380a03808413206400591200e0440c500075490800d040e0041d030320070340281d5140180384240344800b8086444500700403440b101c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 854079334 1250 854078084 854078089
    0x1020a080714010203043c0f0303090b10090b04061413020d140402180603030d11040b04030c0f061d1e040c0807090b0903031b1c03050609010e04020901030809 70
    0x30411a0024466001101b88000c02c0700b2243c641410707001a01171030600020001e07400581040e900c08522400301000034003c0400e402c0a1540000b50207828045440c10745a03071100049036084804189940300c40c94140041c504a000300c510200007200c0501400e418001488074890380701002d030b485250b090000249003c400c2e0143d5407401107c1d1020045640c000d040f0007100a03044400700d20a901c00604011403070b1611600500410002e0011410080f404840000621080c5454005036800784400108450751034010009103106210f40b405851901454000c5049190003450902c0050800840030708030042e40d5402905084400e40c0301c807012084550a0758200340034280d0002d003800001060719400515282c0200c2e0b1aa945039440780d521440051680240c0b064154182c2080040c1020120162981000b00101100780c4001d80d03146101e646001ca141c0c540074011035101c1d410042d0905e0034124041c0140b0301c1100049251505500144100d0014000103214400c0440d084403580c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 854080584 1250 854079334 854079353
    0xe06040507020f0d09030303050a02130b0a0203040509090f0f1b040f061e1e12082505060906010f0623040909050c030c19030308071b031101061401020a0807 69
    0x2000240141c138220541c0840040042819010560200741002c01059041126100f00c0d03458800706d0944600300c0f401d0020030005c69114406541c210b110900010410356075011040d4087c0404c2c0c03005200001840003914205000c42000084c035400111002d0b0244005d82801c03251340e00d040307034001691110100c0600c0100320940180c2003018101c4402d440e1b1280140c0c0100980b81c01e22400341c102c80152035002030081c694062188281030980c200d038002200d40380074000d00010302052003c11106c00c41004442604960251016400042403081100c020b01c0941d016148c8200400036082c10604040e0002403503030796110011040800103114052010155800350458080c14009075000c0d04000743c0d0b4604404075030380310340a4616041002c0c54040003114001c11160000a58a407458034117694002e0300904200610010080f816038102000d800900c1461080e1106403442d508044a40c6c00c44003a170708001c07240180e80c0300f4400c49a800042c00d180711580400d0640c4c0d0b9100b40d180030800c0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 854081834 1250 854080584 854080603
    0x31c0c17042f01020f0111090906031509151b031303021c0f090506030f06060d06030602070309060e151e090303040306020a022413050102310806010e0604050702 71
    0x10a0b40c040b000d0098828210928199000d0903401c0700c103d0328003405c04030700b00c44038141c1e07043c101d1204005520150510100c5103510910080950341070390145d6024403481c035000c81d598411750b0000f103c2d4840d010001091640c001c6050740c00c1d018030082c1649101018400030748440c2c540f1004030310800800d0320804c001802d060701d6a0b8680b01c03012071250041d2129042011a0000c82d48d28980411740d400e003a802d0b28030406580a04c040c054841005000560748082900d0710b00f00e494000c0072010a60074001400c100c3c0c441e41d20414250710f040c0707008280005050400e481480c040b01c6600c1d100c030090054413400c02d15641c030118100103e40560035070340f00d0440301070380502000c82d0010600c24640e01402c81c04e07006800307a07445491404140d041c031612a050400d8001811408075280c50751540c1e4031888030344210001440e00c0840003040040886c0d910400501c01010705c00d46e03100752045680032008028410007000f055043c60051043d403480182014080d9a0b80c00000d4125442002a482c2c07 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 854083084 1250 854081834 854081873
    0x40c230d02031c020c012c10020f120706060e04050c091f0f0f06051905030703091a01050f0301110304120912060b040b150a030902060903030a02031c0c1704 69
    0x2603c0c0e114400103501c81080303a8036980441c545440b4490154001c4144445128044111035198280001041102e01c4e00350b107160701718840c0c007098445101d001c1261100140032201f2264661a107840c00340103a80301900000341d03801c103080a01000500000302401c00320012994140340d6a62460880528010800390700742c1541c03804c20019041223442071520a60784510303800c95507644c5500058940d0710490a40b40d942d80c2c1d21848031000107206a01460300724440b07140204510341680c440717000e4140c0081d0070a000b1170054004011610f01f05003a18841c4000f40c0c003d00c901c0011801030802c5010042001d0038410620b82d62083d4284038051403030240c0001c40f03410310980c0300d90800030028801c1030019030040380390602d00145441c059446c0203400120000180c90300700e80e844110050000e4100807600100c00380188101c55a0520180803081c0840d80250341312008481e880d011308030740e00c41c004141482d10750300c00b0002c3d91007090800c200d0381005d107400301a21240b134010340d0010503a54161 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 854084334 1250 854083084 854083123
    0x70806041a0f043803010501081c03091b0b0d050703150302090402061b030414090c04030303241701110721140a0c0b24040e070f0e040c230d0203 64
    0x11044c1c3c0460964410b40380e4258020042d50380c07035118007556600d541a01c0c0f100b01c01245602c0200b04d1083e0020004a4854080c001610803c4a0103020200c15a0030140100c4808119a89405110300c81d29512441525007400441080b000150100f1054000640a8003807400044c0641d1034401c200d4100708400d0070030b850480c01e080c0410b5120f0300640034040d0004030810040c6018900b0382e0040b8041c40d8ae001906182c2840c5540c19070040000c0c1950000a00070000b0050100101101c07110042650560078a020300852441900315990781c00d1818441c0400e00c248000b05040c007020041c2c03010104c2401080403030210303085d2080d009443d01c40908a00000b4908a5283d00c01c002c000e0b05813041d8810341694441d00701038003151507080003000303200d041070010207964a4903410039604000c01c003090302e41c40b946900c51500c803001d00d81c00003511036880390301340001c2010f8242480010840038401e0105100c085c000501c00304402c40000d403050340c91060b110295502446800d0654040c1118070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 854085584 1250 854084334 854084411
    0x60f0c07180203010f0b04081b040e0a08220b090d020316080706120b030d080c070b1005030d110c040b1c0605190204051c1703070806041a0f04 63
    0x2407000c0c0d0b009005030340762609004d1001a04400c40b40030b503402d84003010701900c40321041044085a100368495140d074030549980700d0500310403040c040c201c1e6050203038014990f50710300038075508108001d801d10201809403481d41000028104802d43e012601d08a85100c00001d1500000746030000002102d10249000c0e4800a0903c0f400510030080b41c006840d0719a6100c0c540d441082250038090079650140c003d0421124440d01c100d0180c1d6015002015290078100b150700c2d00030141130100e400d1000c002e8641028801c614003006502c0c8070140d245400031000c0310800c1c01d00d880d00003040e003207805035031140f200100c0c583d1a0403000314104201c130000c0e64410b001c0d040c02c401400c8140c0e10120880000925558a20414002c5070251000601a400c08640c0102c20400101036924165131800d041080541d082d81c5060055015182c941c0d607440307d9041540230801100c94140e894a00715090140b088120349558914518003901100c0010301e802091600458401020119000e0780030307c850380 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 854086834 1250 854085584 854085629
    0x1c081914100315050f15130c12050115090e13080a030f11160f110303030103121202040f05060c0f010e0d1b0803060d06020409090b0609090606060f0c07 67
    0x892040b0b0740a8464060000742281c500d50445200b0303184400c1406030703900003460703491520007140360410340900b40341d018001c40100031007190b84458000340041c01036000b10030284081e01915000d8440904142003005c40101c01a107019920300c5484240001000051110040e00c0000051590840700c2d10341d0f80e160416004004101000c1c0c1e2180c030602d0300750010040000101034a07906d0140490081040c0660386520500c84014041102c2171580742c00c00140d1074505001460085109000c03404808041c61400703060400143e040481c0244144020441d0303444450b10203080383e109441d110b81c0c1c3d86604c40d00e0340c00d03c56001d104542940c00c0140c1c15070a00710020b000862a0300e141c0e1903d80074120300c2492a059609044080d0020f201480492954640704141c210082d00c10540107241a40e42c2d81c02d0016100403803015600b000c1d102c001c2200da07051000c005c9900201c04406042d40785882d40019245000f20700101c60006804502c85001032010400040906110309400000d03034030140743d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 854088084 1250 854086834 854086861
    0xb04060c0515150105070822051201050c18211c140906031909050307030e09070906080a060f081608070807030305030a06090f05091c081914 62
    0x4580600c100c2c0392402962a144850340c2c0030340c500c1d90080034851103a00044581c0d40164405441e422410407003001110041002c03058801030102218440e80e140804001031810310414100c40c6904143c02c00503030600800494601d0711203010b1612440c41c080000c2079003440e50500c407501d9420048220b0900c000005030203a03003c1841c0008240300d40700147c0445810106252003540c4030400d00420450b0f103451001355130f01c020b1400e40d0f6944180c1c0700c10180150303031304140141d41c550000540801815485420790000d00000d0301d40c02003909045c1c0c0020095401440740c20108031144001c0354180501c1d030403450007440e0141100034242d4441d000380791501002c030701409191084410004441c1c10114520007150400000b4004042c0307103031400e56480e0b200900a1401c95503e02c0085800340081c4684500202c500e500050030f03141181c40309103050380c0040001c2d201c210071281a02c0c3d0a0340211401e9009188412880300d08190641c1c0d0009001c84c060900003500305001040b5a00000c440b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 854089334 1250 854088084 854088107
    0x7050c190c12020a14030f0d03050106081003110909030c0f011407030e190812070c02040608120406031107140a150516030c020c060d09052a190b0406 66
    0x9110080c90b9038070011060141c20b4080000d400c060800000c2041303032151403d88442c107401a007a01c103070305400c0d6100c5003420f1407031503414042641c4400501640758071040c0a84e0100009243c80d0180e800d581790040c48290003200310b8820b100c580c000842080c0b003401902d4541100a007200c01d02c401c2c4001c80c501030088007829403104200744002448181c0709005500c80564110040c152548400c2d400840d05002031905840040c01049000c0d20004520f00943c03084003d40d81e404110883c2e4810401903410b02c1d842042143d200d00c402c4000300012008507422101e042c02c0004100188003410003035402449405446c4240d1148070310001c0001164840c469841500180c143d82461101001111010f65444840100d05045004098001da0005010004070b004482652070300c0c0001030321a0f4882e00003140340540b158400d008000041144103466034482d0b404504420800c2ea8510401e04409481c5205e003c00e41c604203040c4041d88035a4014007540c2000a075a2501ca0700081c01101910 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 854090584 1250 854089334 854089343
    0x120513061112090a2f0a03030305160e0102070b13030f08041703181017190b0607020f0402090a08030a020619090b0a0507031503110a08032107050c19 66
    0xb50002c0d02c030036804a03001581607030140003804511511592a06400d40185c3d00201c40d400c18142801c0b2a9518400040214483d543c0802c1515154990301d00004d04034035140240400404944845da80201d00c4c54140c815006a59480e94600580c640c0d616400364006400405030403003900c28445480020810354002035222031083d21800841a920301c1081c0d01ca01e0701c42d400d0800c01c0c83e030b460090304181c401e840d1498102c11101342c00b02c0082e903030042500c8002c500c00c019600da0580c80d020740921038032403500304c41442c1040e44030b0b0042682e40071980e4540e845990b0006020209944110326503010b800c040e03084031388903601c0c0c1401a613544000d5880c4045403c00d94a03002941130340340507024855501052454880d10313000d00c0c1310301804000c0c290030140345c4c9071400c1c660708d42c1c00340010340000d60042040383c001011410501c0140a503d411100240d0820402401304541291400900314451200c00130b10745d94400c1c049616000e030800412407402900c0e12003809089841e2044103c1f4041d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 854091834 1250 854090584 854090617
    0x708131e050d180302040b011e0e1903050c0d02010203070821010e01120219080a081902030f190c020d08030406050f01050102150915100905060406061205130611 71
    0x3400b029180c807540c121288140c0701d4400b40502c0181000d4220070401e15040c11311890381c8820031030040c4002c030381038100000a06122030240151900d007284024091102500103507030303810340e00c42d01e4503642c640c6000d0703004101c184c0402c0c085910070002c4481080d088901141c0ba0038101e00e41d01140c100c00d24200d0010f40d54100082410f1494a0405040715844892071034a84c41c3d85d824490580d00c0e44207500901c846690300002c80b05d40600040f000644201c005035501c0c0d8243d4021402100c1d52030401e811540f0601c8002c0001d54104103e0700e4191850711a102c1805501c2c504680045980c03400035000990402d4490400000030055409684504014415981e906040ba00c105030309200c0c007801a400708500100003400a880030350441c80310016100b029164403400c401c802000e480072b0000203560361042010715001d218098121500300c40034001141f030004001c20504805103101801707503030307940403c19012143e0803815100754002403e0186290080c1c40ca812600a2151030761003c94 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 854093084 1250 854091834 854091853
    0x607020102160609020a050319061b080105012003120106030c0c020a1703091002151e010e070e120d0f0201060b180a2711070b0708131e05 61
    0x40c02074840802c1201c0c2d580c100301e00705440d4a030260040c40400d84e08003681090100e200c0c0c600380801d48100e10780d6170640300030994a1400004849034181216980d00313038242c0d940070040d800304800b811101c00340f81c104070403c0d80e0b01d00320f1103060395842155207510000400350900d5100424641c100d5455407000c002c002e42c00d5500ba00c1c0001100782c0294000034000d414007032401a100c48103c90182581120300b000020000704420409220b02180960302c03104091081c0d40700384c1e61403030b40010001d942503085158101003091187e410b0040705070f803421101c001800503100f40014505680d000300690040031540d9112034a942e00c240400c0000b42e4a004054802401406440200c41188806520f031400b032400403c0801c104076400d41d031000351104005000d01c20310301c0201289490314440d200010a0041910480b289000c2811480350140b0200f004200e82d99800707036226459040c118440e41ea443c20840010792807220080c03412102540d10400e402d0300f50301801020f44038008940e03a040 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 854094334 1250 854093084 854093087
    0x30605012103080c1c020f040e0105031f0b06220305010614010206040206070222060e10060206070809010e120d06320d1509061b120e0f0106080607020607 68
    0x700c0000240200e016540868008808032004103900b0461081341c500001d4581918030980e0f00195480b000414085401d101841c1e035618040c1c018030b000c600404602c0c0020b0010040450008003101c0a681e81d400204c1c0c064a94804991131000d542c400440329084003041d40740040541c0c0001d075225868080301061884003002190080c2005800914407941e5607070802c4090383c44088201c0e0085192091140601c5c00b03010025040d008883c4080380e001e003006455241600d00138018031246460030000c0047da90049261500042c65181529441d990740e000c085c050521045c0080751449451800e00d024510400640000140c4181c203102c560f50b01c4001100750b174540c0441c0000f02c6403051840c0e103503883c92000070078510300c040e004602c180501d865002d40e07000580502c44015846448000420210b0b1107500d200120ba10204001c10140c3c00c00102000011000700c143c0594032201001342d0001040801d8070700d40c10704000d0002540300d0100c1c5440380c03000c1d0380c240058030a00c000b141d00c15 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 854095584 1250 854094334 854094389
    0x105070206070e060706090516140108040305040e090c1c03020c0901061e11061618030b01120204020409020a020c1c0305030a05070c120509030c0a0510030207170403060501 76
    0x1d0001d41c1e5045150a0100304201c40d55100f5601111b40564415200001441c140b220002c451010820002c00314a0602c5520001da04104858104a0072004000029411009846c00d45a0700784282400c0d5840030398503072503c404165a1070b44103007002c2d4144161030041c029560080e22940c2699441092035061003031582c1d00b8000c8002040c010070240caa0003a0440395098204035a207001c0055000c00d40b411801c24201341d13000113031841c4076440800d6241e00880301b12030082c0e40d00300b454049460341e11000c6156606001d40691107c1c1c2250550640d50f0f80d0701910040d14081c1030865603030708040b070065a1444146645401131603c455181c5400c002c10303030903070a25038040e03c86600d959034100c4180f00408004011070240f102e4400740314007080c090300a00308804c19541307400d40e9405010b0100340c82c102e9030401c85481040a03a4081c0402c0d10f550b9002c500010700c9040140e2140341c01d10f04206e060a51941404100101050010900503540c000c2c81c100c40d5054464408a60540901c0070741 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 854096834 1250 854095584 854095591
    0xb06030906132a05010305090c0306071d03061003060c1e0302090a1707080c041a190b0f04050f0d1a0705090d14010b040b1f170f04050105070206 64
    0x1240c21440c00210018260081c41000078414500f24120b84800c1c0901c481c3c2c1d0580d0026020107403541c1c1070038465541c242c810380703070010b0070701d80101000c60102d40080e9664a00604a00c2040304600a46c4003d00b01c0018054882c0300050544881d0310b8500440e100b00a85440256141410000741d8003449004401003100010741d0389240c150720700f00150607000795100d14101d40e001000440700140300d0089080c40c281141c00356024101c158503100d441c600c0c0041c0c09038864815440c0c402c0510750624054648040710038165040182c2a0040035038116520403540b000001d1200056801f021804d40401032003950710481b9141410300d652400d105481025440080c48c074000d43c5004100700c1c40e69020954403000c50702d001480c050480020070004050890b0440720785002c202c1c0c01441007000e0060201c0e412003030780c04001003800e107400071311500c4101e004c03c8690400a050401154810185004000e0380d82080320000c0c2000c0382d5100c80414100c3d01507840c2e51900e4045041c640c03010070410302 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 854098084 1250 854096834 854096851
    0x501050403060e160b03100501030c0906081f120c0f0f03020409050111220b0901050406120207051e151015020c040c030506030f010501060206010e0408090d11040b0603 74
    0x140350a55455034010f0078155480302c41481080303080e01071102604460405082c10380b10079030303d9090641b4a041440015002a41072500340114802c031690b02980d030b003040315401c1c9000409510f5107100c003030040c001c21003407589030035190310082a401004080256240c4c8240e40030280d05a40e11040705194841c0d001d03e842201d41c0500800240c034058000588250080f0000911115451440602940b0546072a050f0794a4049000c90120a03522501d00800d172002019107842c440600003070461180d4083c10051202d11981d16921102990594022070780c040121048804c6000281042c44528401d02d4068466906100321000c01414503601030580081c64500c0c9900300302200350f4003014040100c086114902c4031013920b076524012200c1070390072900c3c0003601f41088810716040003e8400c080300b15a0400c2c00400040d0b600041003411140780c4c9010b6030413a265441c00001d503201342030066902480711040c65003404101c803080505140c040b0744c20400c041c2c0c070005100305408116400300c03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 854099334 1250 854098084 854098087
    0x17070203070f03030e06150a05030c060f1b060403120f020a0f030203091002070f0c150c020f01140a0315140a0e0a020c191518170c0d0c020316050105 66
    0x400652080000c0c06481d00c203040c0403a071002c0c80e0080e14901b49040303070000000300612010030701906102e00224042c04042c0c000d0310740310303010340042011441b4a0412180c00e05000480c0307813201c3c2c0060441450030404274203440043c02d06084c0100420045e04042c0304035854200e0300c000c00d00d8a4400c441010403240c6458000c6140b4600540c003d401c000d0140a142c000c94100320700c1ca05140c402040203510071401e840d400c0d491800c0c500440c98280c0c00c07890800601110350340d40076410010f840c1d18541e0440300314100810f5040120398224488108003100e03c0c001c1014180705825400042c064940c800084e011255559904141005c6005040c0e0b000445003406111051018003031551240301070a01602d80b6115414042c45d0101c0c1041640341581e002503403008202c0d0f0248100b4101c0713102d04061000c5800e14510a00c070450201c80100f4601e40ca6981c1c1c1303542054403042d2a69188100d0a807841f444002c400075181550136041248217004203403030342000b0010400c80b00d05948042c0d503600d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 854100584 1250 854099334 854099347
    0x6050904060c2322030218152707140d0b150f0304060609090c0506180301020c0a0507090507020d18150f030b030609061302040e060c04030317070203 66
    0x40010b2000c54001d404001e1082c1016080b0324640d42c145600b92101d01e400b554481e1541071003003007200c03502145902590302140810140c0c0d035401d16030300a100d014820000b641c913209106003101e4a80411550409200014101d207401c101c40d0144103041d6400380004c059031071040840f1102881c000c46034043c0d905100300500b0702082d40c4150441640500b01403020480d03000c1d0b04102e604007908a2042c82000410041006102d008005c02404203041c1401101d849694000d0315504c203024079402111702140541c4906c030301c440a402c503d04050001c41d03580c10001e04860f25540c0c80502919a0710441c5000075043c00c160ac55144a512540d02130420b070007080d20220350503100b20204648561440002150f1801c0802d006038405c11103031601c1d1086410490b0203010f0365140c03a0b4444c841c2c0c105d40c1c20031564200219130151302c0810844280d821607068030000c1c0040c124039002681e60312443c810801c451420000030030507030b800b0303807202c103110550a81c1b032602d250821074491006030420f1210 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 854101834 1250 854100584 854100593
    0x603060408032e171b01050702010c02061c0c020c01020c060a0e0109090c02010b100201090b0a0c050d0515210a020d021206070f110111160501150303020610050406050904 75
    0x42c02c03080300e02d010f04540c0841800110689030031468004546078064800e8004601d40304100418890101c0401036001400320b0001801c9400381d10700103070601c802c83e035442d0115600d100448280e8413140b230168200d1954014414024588848180e0141c0302d024040b440541c0000366030321150324001c041c5442c000503124211241808107214a0501030030440208543d41c0318000c4100504d00350b8000100301d200e101c101700340c882c601d84000342036914010742c2c60042826021790503400044640003081040740b0903021100b51140928000f84140703010140546101111000844503d00f110260700d400600c0c0018002d26a11007550506c80d030000c03100600600b010a151503625000828044a241c2c0400040d400d05104403040c4000402c1003100e0525203400046020a0f000942c0003000121024010b00d05984a50904815914000c0b4400303402c009094000340429400720f0820340c2c0503aa07078900039540704001c0d41e000004520001d0040380c1130038948510340460f86c0091850040d51503030f2701e4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 854103084 1250 854101834 854101861
    0x6050a0e0112030c0803090c09070527030f0f0709050c1c0c0203130e070215090c0f03010f1509050609040c060c031e0f1d010816051905040806060306040803 69
    0x200d0504c60940a10070125095a01452242c0d28850281003084404820401c407400000d28200a000c000e000c50140c0d4280f080352038244020a030a40c2d500d403025080002d1401210f41c0440d035640c0300359040403c04080110b420021102036030010f00454035950300d10180b5006007192a4900c81c005406c90000c0241c3d03030044400c0d4151401641d16101c4904000f8050500d01d400035080204c8500c181300c4a140e04004012221687c85c04149880c00c210740003030340710b10702010100d104421078650840107581c298040c03800000e16243c10481000450b9519240355054407480175500c2c03a04001801c01c0c01c1c0010700505c02c036800802030f8000c07800e002003a5422051004190100b05000d4412180c5040481204400d6986a1520388068094450045c400e801c0d44d21445921038091400a40742c2c2d0b0070913444c1c1d82080c142e143c002d0660541c030000f103803c2e0184400c610811518030380c243c502c3c250003400510599182c841961030036500d0200307040c1c1c3c441d01694020400c800c1000081c040000380c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 854104334 1250 854103084 854103119
    0x90f1107080703230433020c040b0612041218060801051e0907200c03120c031c06031101020c130e0102070204020309060702060601021912090503010515030106050a0e01 74
    0x41044180d03020354202134401d400c55000103803c0002034800d00d108170600d00c00c004000e02c824900e81b171702d0701303296000946414482c018240155158507070101c455940d80292071000c69098504602e0740742608022070310040d10440900464107010261980306a6101c95509135255501d403031916074645414000410202c6070122101c46103a2a02103082e030720b9041c03403406a4026034845c01900d9405200e0200c0c100001503003611580020b802d51036989010400021520320449043c2e29202e880b00c0751030540c07003501c94080b980321a403a44a940045641c0c0100140c0e030048041c90303074080800300103992b01d00742d010a45600a2064035542010362351a0042e0903200000000541020a9640410183d80040e650101c49802001c20010380540c104440e80d4024000d10081001540550760400b200c109008080c11b0061540e10b52003015002e000b1010050201400030805460201e14102101d56500c0c0c0c400d1180d428543c1c00100c41c030300400048262401d001111000342d02e4000340010800310f81 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 854105584 1250 854104334 854104367
    0xa12030903030806011407050106030201022512110d120807090b181f05091201020901080c09040216050a03170601020304050d06090b0c03010e0c1e0313050304090f1107080703 77
    0xc4039403220a0b2115400b42c2a10340c8102300100e9840c1c10741c03001a0a104100d81c5511050180c407030703400382074a026a2450100e88c01056000786255031420101407010110111980020300c107100c010402100d0a04003054044c1c0e9642c401407610b880380122074100c40f40c45080d03000d0380e050100e0034103a04540941010590001c2c000d28214480d81e003c802e0b51454110448007140c008110803005003400614a0241c0c11140001c5280c00c40801c006421290301504001c41d08101203280190f9450303d80c111607848924480221100880d0b241060f50340a1a40b4220005401c100f0020704d141e943e0708441f800390034140c02550805050000f032086603120900b05489060b06d030741c1c1040101e1191780105014001c1215141e507a5810300d06a45140400035024a20720315040120320a42510500700820140201040f039039280c5407002c1c2c06000800501d8040c01501002900140003c15507004801c05170720000107000b40f900880d8070094074004e500000d4642d0000b0002c440000740700d407800080b0100903 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 854106834 1250 854105584 854105597
    0xc120507091a120606212a0405040c0816050c0111030a060807060f1709100c03020903010e0703120c051e010c030b09061f03090f080304020a1203090303080601 70
    0x25201c24070301c0c542c12034440c44164100051102072900010009560007001501c401d4944041c50540c03080c11100e80d840b44001d0244080840e03070f810554003e004d007a080c1c80700c2c0240c4102030090808101e41c001d2040c40e101e40c1c0713030518041303500b40501c110700d00c940e001c0409800c04012031902910623034050540310f007144d56a440040e550b0042100a540680606c143c00a41142050314491610041f0b030050024000d41d200c04400196104003ca0603002c1a40e8408019480d0130886502c1c0050f1024912246401c005c0c2c4e07410a980c3c0765018040444086009000d000004001d10307031100c9050002406c080f28147c0600101c40c051b04040106a00c2070b000c544030403007800003040342519101c000144503510f40c0108030b06030b0740c580201400301c4e00807500c65815041c890001400740310f41c80e02d14801c4903900c818910005009501c9421041d821202550121240b49042c40c695401258201c2c42104038180c0030694081c024800c880035581900da03859002d086480603294000c006100300e040119 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 854108084 1250 854106834 854106839
    0xa05030a060e06030c060a0e131b090e07050a0c060e010b1309320a03020705100306151d040606110f0a03050304030c0507030c120c08120403020d061103180606040c12050709 76
    0x80c1c9c0c40c0c400e80c2e2084600c9000a4405420700c0e90100c104445581d201007086001c401d1107454400c0034195007100440c00c0c481c0d0f994007030b00c00a80c1e10120071080504541d142a024095082064021602400048401c600c99041c950052411516690000385c04559019510400c2281c140081c1501c001c0d07451a2030343c91140c1c9108249844255103040300180c0054804202c1810600343c1d04503680c40d80e0606000d03050070b003591039170220044103011007004030a00b02112001c0d611401440300e0382c0081c000384141503c401c00a40540c5021000c6400c520604031094507080001c10070b201219410b640e0035244d80c42e541c41c03c803403c410706030090700d4a009100001002905841ca0350000f02046200f1002504090800c00300398000790f07011140c01e0308820001c80780400d4100448090300e0381207803841040e10072070074000c00600c0c5101c2c9441d030084000051282144804020751404d40f03004c001c9510030703680c0c4d4092106560481c1050f0002c07072260007800a04071075981002c0d90000e4145445050250b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 854109334 1250 854108084 854108089
    0x2070815060d0506010303050c37020406030c080307110607170315040f0c030c141b010b040504060902100e150a02010e0a0605091e0601060e0102030f0a05030a060e06030c060a0e 78
    0x304c217030300131008501e000600b5040e100d41031201e0032118916040030402108119400d1095402601050300e0f403860704040d540465a071a1f00c50005103070440102220144c48041c003e0396a0310990701910f105144c2c0c1e02c26106498402c00300c866481e4480000c01d00207141300c21603605a000502140c601c4150603400f800c0940701c07403094000d2819241000b0402002014014040300d1140704520104110280c0c6012031152003403c5a03980c1d5607001c010700c04028601040c47c0148a00031200346d00ca420003081c0010300c03c00d0b130840c02c00c0a000300c914140c0b0705001c41d0306030360700b48030f540071316800a400c190300c9240d41002d240a0003c2401034000070500c06c22709800e2a04000c600a000c0710740c0c03990b50782849100ca80400c00040c469800114500f01100701c21501903a489051160b00200071425001a809902c24000c0d91007004811901d00c0c2c40b03207071480014001d41c00844003180220f1800c08001420f40304e90f111030340144400b6003c0d1001941e488288130003035024174807210600031500102601078 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 854110584 1250 854109334 854109343
    0x61b010c030606030506031903080c04092c1614010909020706061406090102100207030e0a030b0a0b09251b140706050a0512100f080f010c02070815060d05 68
    0x112207a0300010b015080c00c03c00780854001030702c241c0c06544000c44081440240f083d42d031b01800e4050611030400da8034055002c546110301c0d0810204503080181904c070001c441e50300b050200c8205504410884030100c0315030340d54400e0341700c54240010a039000300943c03146200c40311680710041c0340c4027180321707203801c0014280e0344000340440707540307980d01c40400c03e40320203116450024000f1288249448004c00000317640341402003075075444a50010f441010140a90849001c0f0a400303130104440035528109850040400c0f21407152190404007160b030315203041c03400d5a02c0f684842864800d19180c075000b07401008080500300c0140210661000010a074001c80195a41d11401c559000b8030f2511400b142800c80c00d900c11800d1103401e001034041a80c12200740e03001c294000c903545035141d468212040340461123502c0300130711011041001c548070303202083d41104196a44028812030b008020201c1e03a07801103214441050300704500308100c2031152000c064100344000c18000455206803180b6080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 854111834 1250 854110584 854110601
    0x106030606080c15041203050f13030321110f0a2016080601030c050907030f020f03010302040b0907020706052a151308030606160b04121101021305061b01 68
    0x1544071000e51415841c12440504c00307581a140c20500303051400c1c0301c0308050302000d90001c0a000002c0b61403080d4010740c01c01e581506c8582108945082c1e500d08014202c10718041b14206000149002441c18140700c2c09400c204c0d0700300b60f41c07151500410302c05102e503d41000c007843c0200a513205903802d900d420794184808004100010f8001d9030f000c040814103007002503102039120f40006004001041e240e03088d00b402c0f14020355080c0425034949000b01d00405485400350a01c0744003040c10200031072140040c5041e203200791410403061414604000c0a090110f0b90400140d125810034051148240c01410341586500394a92a45a03c034030740302072125090f1144440d69001904028841032409403507500f1001200c440d071600411074442200900c0010401c41c044d03100010b1202ea5011095680380c0350b9600260b0980a40c102460032800d9211040911000688454940c605400040c42150071003545042231407051440d290501145402155030840008801c0484e030103042c00030302a0304003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 854113084 1250 854111834 854111849
    0x607061d0a0308090d0806130b0d120e12011424032b0801030f020105030c04030b0a0b03010b040e0318030307080d050106030c0e03030a030b060d1505181003030503090106030606 78
    0x41450f0014026103030240882ea00801c100300081400070607107580b90f80e11060b40b506940030408080000100342c0001c0cac030703030001494880c40300c1c150300032554000040c1103143c60440d91003d00c030031454511402e9440402c3e0304928044410041200101d088402c05032517181004072085c001c1a840000741040c2900e0703a1509418400c7c071516200c2c0e0034054184450003103604103004194199120040c03a041c0d01000207050010000c0800c040710101010f9400659200240c0c03249881c0804444002d040d03080c5525000f0340c20400011514600390143c020f903c0304101c002c60409410f240004c001ea0b440c6824541c00d03002c2002a080403440080c020100742e04089004501c40d41341c20360040441c2d0030b0210003400c11548810000c07180d54040104e42404c0103502d0701141e089614000104188070f02c880c0c001c02d040c43d040494440c210441808001c4a204881c1075461400da85010750161500311100001254005010b1002034041c0c009940c11002c50070001814070b440c1c0d03039241c0031a5942d810010707 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 854114334 1250 854113084 854113097
    0x10b01093206160b07140f0a12180515240a2d050105070807061d0d0c020406140a0e13020604120b090114241302120a0b0607061d0a03 59
    0x10900c125850043d420510900d4078041e11500c44501d50702034010345408103550071f000200400300c1807040d001c0340362030550408204440c46031f100382002e1400404804541c1405924035020b419003e51503020b1096045d56200301c0001c0c000d09050304042e1a00785400e9110001400100d0f840102010340e0141c000142e02032003212460304c240c80303400700c19544950b04001c020000d58001030600b406075280c1c40c0d17203c1b0005c2001042c1d091045001415000c040e00180310302c0401114a5520110031b0000600940d0100b181d548c8070304010307940e1060042d5503508140c60348010014040384000c500e50100c0b1041400c1d48071300d0954000380e1980e10603405104040c120600146c01e020300090069003092100c4020440d1040100e40c081d1080001400f51442e150481c40c1901c211140d80e00da80e241d02001400d42c01d009009440781c01c000c3d003100c02c852528004c14400120030a03024400c0c00090800100310320f04006040e62030201402000300355120b070000030800840403040411a40710864440d45461 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 854115584 1250 854114334 854114377
    0xa060f140f04050c040209030f0a15140615030c1c0204260606010806031509060f0105100203120402010c050312061309020109150c080c0d02010b01093206 68
    0x64018000107000200006540001c0c003000450000e50402c10300b000740c07070168690100d280003a0400c10804071000440c0240c90a4400700800103001c2c0d503540d958110208000006000c9a184d070a0085a0164028100d410b442d220500c8102c0034641c0141d0601c603541c0340c48800303207503032002510020b1019480c0707401003424805007100030910503000c131080c950301e8817410403032222545d00c035000391255040c8002d00c004551580c070240550040c0e14015405801503081c0401990354a0404854942d0510140000851075140031f981709416480d40354021410054403082510b05204003a1040b810312282e046200001942440902115409207100503603510b860818020f18000c0c05a032103c0041c07510080303900603038008400400b644d42c440381600a1011440e07042e9080300418101804071000031681c01003401d0006500b520311503044d030080c44068100d00c01964000c01c5400741c4440008139080704030260411480e0380c40c0016040103c1070110341c445002c240aa441001e817441c0c80143c15640 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 854116834 1250 854115584 854115611
    0x10090f050f060720060a09050f01050403050604120309140309090124111006080d090f14040b030a02130212060612011707090c050c0f0c010906030e0a060f 68
    0x210001424251003030001a602900001c007a80704000d4001e000203030031140300041825083da000b407420300240000395580e40f03e0340b020b4525012440340d24800c42c007040c44010f03554428400c0e07a04803035020300186070540b6266a40114044e410038004109a07680c4550700114400c0038801c01c0c00501c00c8051035554000070305004a242c0142c2103c109001420702100b600e401366074600c220300d0340616084c00d405c0081e800403410403000070f610301c581905200e0702103002400460000b07114400c94035070000c020f90701d180c402000c82f120310580c01035a034503000d5000203003800e41218002c0140202074510030300c46503002500382801c00c9112443c031640030a60500c4071000c01126a040002202d426080c00c900c9480030310001414003c00f02d1051044d4551840c1c803204012220280101d0345c17060102d1803030000c3c010a150000803410265115441403910000d001041d00c640034481070750b4a10105080801c140c01420780718100d00075901c510401072020501c02c0c816600311031440c180100740e44800000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 854118084 1250 854116834 854116859
    0x20901020d0f0c1e050c0f06220f0305030a170c07120c0215030712020702100c0f06020c0318060c0c0f062a01150b030a05040c05130c0912020d0206030c04051009 71
    0x1129802040b03507187c658540e03038400e01038482074407148000810000c3d04440c4007001d054140c4c884590400c400101004018000c406084070bd14980e807440403004441600e00041942581c081620800c1000b00d200420300c0012640c035030007840d082c051891001e65010910b1105200c51382103805402105001c59658810411103800800c0102942001d44980001ea806020741c0880414003061524100400801d1300c4a18140c0d80c02c52402c54440c401900e0711a00da074800340c480c086683c107a400c15002c91510354192410407214400a0080071000ca0030701856450026407154020720034000c2d504125a84c480700e100f425210080c98544029244509095901d280c040802d481a00d090500c00201c00300241ca900103450580440c5944603402e1181d8000b501e5000b854000140788003600d6240d5041e08441081c07081346d922810402d80ea40304296117039100d104029404204600c000c0b000d49401809141c220b11202c00701840c2c60303550350004002849142049001c00c04020040010b1401c024 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 854119334 1250 854118084 854118103
    0xa2616120f1106010b090a0b0706020301030c0603050c030403030e010e01020d09020f01110d1b21110c01140304140d021c03021c09030c02060a0306090b04020901020d0f0c1e05 77
    0xc1442200307240b285196200c0c0c50500410282040101d00005196656090340c0d00074800c90000c40e0340d80380d407424140080d510901098030104614400050000d1180c411a4401c01d00030007080c2c10368803965000c0b03000d000c210000c011650b4035002c0c20b91000d1800e03c0100800001100c0c0010404804c3c41403118103039a408a880c14070600b5034400d0f01c440404103841591240a1804000b100100703100303888001c0001d4400b6000346280d44400c013004460001c400200c44c00c0703848100a0f0003030b003410701d9606c90344080860300103400c03003241003400300c0790340061078101d485424148041c00140103014a0000c0e1a2100001644510b06020a00f0050350103a2414803143c501540362500004100f402507408001c7d52410755503486c00c40e800d042c4a100c5003003040d0350051000342c2e1084500001005084c035402480401d91410030000c10350f01d0300e0b20031555000f5068000e8048031040b08400d440144151000508dc0000500080d0009045c946440c54035258541d40b0004400f40d802e02d00c0c82c2c000c164 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 854120584 1250 854119334 854119337
    0x160f14041d0a05042607050d080601031503110d080c06090304060f0824030109140709060b04030b0c032505190c03020c091017011a030a2616120f 64
    0x3c8140404550855604010811200c86a0f01e071200c48a90584142c444c14101400a0046004621080d43d004042070b02542003640c0520410190500302d00700301d1f407140701c000c2080960070612059070408440400046000340d0314641040b4042c1030050130310008503403a1300140c000040a00c0410340000d0b42245510242c506081c092071711601040b100c049121200700600050070300ca420070343c0c4c03d4020044140e40440540504814001d00540c0c50300c42e03029840d0150706001001c6001132344042901c04498000510f102c25446001c036201c1d6940c0050110b41d40c140d11641c841043d00c07040800303498801d0f4103640c6e880e0f80e180044030001108600c0181081000380c0300502c40302195001510110348401200c440441d6103402a03403011034055030b070141e03001c2d00e64405071102402040d1301095184c0101ca16042124070924100360b01d50103c03980083c00e00044600c0408640d00c01e500821903c40c202c0c0701e1074030741315045000660106100404a0340c1d60740340c0c4040302e8041d500c0009440000580d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 854121834 1250 854120584 854120591
    0x9060203041a100603050408070f030c02030f0a0510020901050408070b2a030d0e0c0a181a0d060e01060302090a0b0a0803031b03040203120c03040e010509160f14041d0a 74
    0x121000f0f692400300c0344220000c15031180045403c1c02941021210220f9000400700c1e50b4642502d40a0300c5003400402c140e02c00d00034522107811500c0081100c4c01e01680c880041c02403c840b55840e14029003005035074a04220040c440070805a80c00c00910004d81468102c8580f12006a022814062120540105030104848a41c0c001d0b000010684c0d800202010303010a400e00802c078100e1034513800f075501c0765100540384030005880311400c0309082c01c0e840400050099101d00c0c00748094203207071402030740d4000340e06603110404104141d100e041c0b000a100d0010a00c513980f038000900400b800d8a030300785e400355100c48000c030303d00d403e20040f801800796501440c25451310b18400101e58030706512345032640c10300000003000c66600f40060146422110040d0782c03180e84009040c1d40d82e03000b6020312580c0c1d00d01c00001003081d292100605228088126004103030078a401002c661170003000c40c44d40c080c4840b40301030a40240e41803000c1d01c081e0607207040c403145081000141484400d006020400c81c0c80c50f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 854123084 1250 854121834 854121841
    0x6022b050f03280614060c070612150e06030d02010606020717010b0d050606030610030b0105060a0e04110919350a0b04060506090702072709060203041a 67
    0x40290503550700500030004940c403581e498002040040103078502d00310348800c540c548140c9400c1e40d805401961403400081c0101c60400341440701c0d41c89480526407203580083c00800c8054030500002c86008250440802e070280031100d4800301040580245040322100401c01044e0708042040d4082c0c0d2066200130f00803540342500c041d450750007a02a0b001100c0f0050501c0260080940140940a0000d86031140172005030501d6501c074407040d90558424014030000c51043c2182d0782c409000d99400c4003500d201a4a0034041003520780c0441d10100500140c076403040515038491007008400c03191812515a1424074078100900c82e200b0014426425820000600c0420400b81100d044004400e2180751007039503100404140c40c8440d842c681d002c0c85601085800c201031943c425005600ca40c0701031099869170810085c00a40c11a1035600582c008142040a501041400b283c880c80d00491043d48448060b0380303d05407050210103640890b000003d0104114140d00300c11005000321214480d1403c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 854124334 1250 854123084 854123087
    0x80303061507081306171905070c0c08070e0f0405031602010c02190302030d020d050405131401030309030515010501021b0121140a06061d0f04020705101407020d031802040606022b 79
    0x307076030f2643c7c0901565200d00007428180140080c030f46140d00594284003541c1c1c0c9449043da210b0f03450181c24505003400001c13403500042e0b580e805000395030000c0a503041c51442c80807850900085d9000307a0400034415480c0025032592a008202e1140a041e44040b080c103600515140c0320032040800d0456000302d01c03101c6119403020540307050321801c8410341c4001048440300c4010700100c44682c49104002000081003680148000041307074440c50568040208040f12545099002d20905000d40c00880802800541341d8000c3e41d41100d050400d0349110000954064000e6010f44400705d5091b03684d502c64075054840c0c01142d07800340745101c00344205800c101c0020214200601903071001d1007100461041580c03017000e0801910f10181086488040d01c1c10300703903078440c821482100c0030740c0340848900c000f00740050182d01c1a0865001045040902c03030f030440040100a0100c0c0c504042200c40d00b0059445001d420000d20b0954004c00c040c10964140c82828101c600400603140c10505494200e075 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 854125584 1250 854124334 854124361
    0x201504151416080f0c0f060907120b070503040c0f080c01090806040201051603110102160b06101b051c170709060f030e2410090608030306150708130617 67
    0x1e60340242184e8a40d44403c00c0200701e0701070340306000d0950080c10211104600002207052094000100300e60b1510341d1100c0d03013078a50045030f501404080450703001906a500550041d5042803259407407200c0f85503104007120b410010f80e0483e41d0b903500510701d034031441d42c2d0010028011301601d8015140e00d00705540082c2091050041841c001d00d0b0750303124401410b0190010b6020070050380000d41da0360140050401d20540008406c441062049003c00c5403801c01c0349000c11518080d8903003c9000e0b00044034954031001d1014101d41134800c16038000c18211070140100503c00054071960700341142000f8101781140700600900c104410514108036a5501a4030319040008504000650842d585412400c100d40b141410210603100c0c429103586000c00034032544940e000488544116454241c030300242d40d42403040c102030f40d00500c0810243c0c940039002d02483c422281c202843c02603c0e5440c1d0003d60001c54a0091703401104400300841074214080c000d400f0740e0040154280c0c2703059822080d88 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 854126834 1250 854125584 854125627
    0xe0913060b03151006080708190222031a160f050d060e07180807081c020a0b01030c08010612030c170c1204150c2015041514 55
    0x100340c841101c4209030300c0500c0b4074041c156200942001504e801ea108902e02615846407900050200d000203040620803945540640c2c640300035508506074202c00d0301d01039002081c1d0803c1c0c03010140301c8121081e0030781403a280154800e1082c02070460403240c3c0d003010384130300418038000708040ba105600d1180d07024110f001391071842d040894450007c6850306009110507000f89561a0101d024098013a800c010302008844141d041090300c251111905138554034a8400c40c0e1003640082d400141241e140d40c2446060605481202c4540703440361110512400300f87d200742c0703441c1c006407014841c081c0203000f003001401c00035000c81c00d10119950020a030103020500509103016a1402c0c41402069808542c00f19220004445100552004140281d8414441e006449212000511007a40103042c4030b002c4507048083c400141021102c9000306100c40e4034469441000002c060780e2004401018101600d01707184814480200c14a02800d1814800c00210126100b13206034800c03002c031001002c90 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 854128084 1250 854126834 854126843
    0xb18100207080a08210a02070b1012200d140c01050723010603120f021612120203040503101b09050901092703020a05070e07050d090f0203100b010e0913 67
    0x94038039400800d0040080d880c400c050b02d1700a1402400204180703034019080c183e01942ca94019500c50264000d8455420321039201c00f540c091042d800460501103550100a1410300380842e81c0c01600001020981e480100f11011000c518080c0d001c000e040005810f403020a0030110319100050b140c804d099040320749202d207511031664154065481c02e400000045a000c00c8684041040071400340070341100c081c0c60f100522690714401291070041c0400811902400307180740d008011394640780c640d02c60720155042075210030800051b05440070890710340000c9404100050130f4289080b641c6c2d1070411000c0074020414880001e02403596185502c41c11a4240310000401901c1592929050078104001113031043c200c6820070145600418a0f565a030320403c242c0d00940c0d102e4010386c0c12600c0554082000031010311103981c41c04800d0388100d040c1805404113101305241640000d103442c100103900d15503141c8641c010350113542c10454103464440101c5114900d850000d40700c00308018094005070 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 854129334 1250 854128084 854128087
    0x30b01021c030b0a170f0304030b040b10030f06021803011a01050d0906051801050105030f0604030c02131b0807020d1b060b0316180207051b0303040b18100207080a08 73
    0x81c10364000c1d4490403014101034144600c06590300200e91401201e24001c0f035032402915041110024040b0403034080c1c03a4402d220161340e84440d110807038a1040207003c1d80400e2240400840440e070001b91447c0300d64407072240540d9803994040515007220501a13030350b010f030b0b0500c5100f000344003001140424602003032034115200e24000c01064090151080040c1070245410705100000200e05403c1604050060003440144d0341d42d02851703030b656241890814607412070300c00320700000e202e0b05400e00c249000401003200010081d60780021a82c007207500704101d01c0458040f01c0d1958000301015070004650010302a41c0c0d020300c502500c0c0c0102d1026072151b103207040760760300b0400c0700b0351703004000c41c00020b4101c440c009100030f440d0282201c0c41c01804e20741c1481ca101c00707104000c84e008461820398013502801d00000c0054920b84240c6100180d1136241c0410301c40802c080031113001401c80c4011410500041031002010b2000d100c920300b0445c0215008810b0500c01c40d03900003494503015500c400c1e101d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 854130584 1250 854129334 854129383
    0xa0308070f210201021206011b11010c120e100509030703060b061e0307080109020f09040209040e0d020a0c1a120a060315140a050f0a0b040204091401060906030b0102 73
    0xc400b012242607956401c070004140454020350543c09800030300c030351182c4a501506d80000550305a00c10f252000e42c02a5888160300014000650000c081130301810719200c3c0f41c0b45641e4698003a076081c503404002803050550303e48035240507040c0061140085c1081840d19412401294403034409005c090302c425243e01c4001c40c141c0350141104e043d1038920403a1022031166009414180d402a207000d00011030800000c11290898421511441c2d0007114840c5401c8202c0d00f40006508214240745d40701e5a248005110300c401404254110541503010b0315001c003461414104544a42d003101c62500d000004043c142504c9030300301e034000071503020030303e005541c3d16103d00098000c40c0c01c000d00c5019819501c1040c0302541d0040091030b2522a81d00d403541d503803010b00c20216502100c28214143c16240490b00c402d880e6800a089200302910240c9026280d05441d41070310700701481150044500c50041085a62014060303001d0102813a083c8840345007003000035520003a60000409003021134480 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 854131834 1250 854130584 854130593
    0xf08160c0206030405150f101a0d09060b01020f06190b150a0215010605090f061608040f0302030c1009141f080703110403051020041202030c0a0308070f 67
    0x5111203154010109a80c034a810b107885a01c0303d900341e01c600059040300d0003140020950000c0c540c8a100b28030442c00b695450113149444540d84180001e104210402c07106e502e540044c001c1008031f5014050106101c40d255000929000794101c1d400d507039130002418404a250204c1c0d00f140c0c20480044003040001c01c0c40d002581d03110740c00b41014141c002c005100c5030720070f401040d421040f03c208070808600740e0f41c03407400b82e0f81c5105840c51035501c842d50284640c254076100010b4051030312071402091403050030f40d96144659010f03400a1460500402781001145801c00891803003140030344d0310300380300441c1c0c8901a0146003107015803190a1940f40c0c0441c203d48a00c0300c038031080c112054402c0220b04c86010b01420308a8291079081c0040c0c1020b03511403031003c2034412903040703c0d0f210004104c030540602e241d500400c04070000c02c0407520a40f02040c04400301001900150624071281700090200d4410549420129031540e400340b29201401c0012640310400e071403840342c1120b007060103841203140 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 854133084 1250 854131834 854131847
    0x901171b03150307171e120403030e090c13030605130b01030f030e1005090d050307021002060708010503011109130608011505210307080d090b07030f0c0f0816 70
    0x4140c005040200401014400900d82000000c0055042d15291a180d2056804821a8042610350750b80044c070204000048480a21242540300060f40c00440084105c10040e80c459801500010303c4c092400744249414103c15170045000359000d454217002940070a4825242d01c8081c201680c2c0720f0000305100d501408074080b05611403080000307503031130786841c880c1c0d41c03a8280182e00190120401c10801d04007086840040d6049403504c034146441c003820415889141141190710380000c3c441100180c848402c103428451458001d03206a2800d0000140001d005a102621036814400f440d51822508801c8800544081c0e17040040c0011411540340648110740c0950641e43c0780c0740c200128000b140e548141503440c1100c0c070001814204101c16020103e1951002994004021800001e4240b5000b0f00381c4d20803460020481110035150440748500807500800800d4656030002c09100d0684560000d00c459411b090a01e140c034880300070802000200001d11508001969000980c090384 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 854134334 1250 854133084 854133121
    0xf030201050a0215040f2001082707060203120915070c031709010614030a0c050105132d06020a11010809010212241e04050a1b0c0b0a02090117 63
    0x1800e041c2070500c1e1400c252902c001c0c50047d901a038108000c42400200680c40c1305910005075185400c98840160801424290130309007048003a000031014000801800424002d0000d50043c5031100140480401c10400c024106400341d004050426a20740d41c0c11103164000a80d460042d09103d1140307025503e055405000300f200c40720310820842e00410540000003904c4035a2400b00e4040304040c00e06070b840d03a04c0c2900070200c2400e41014011b5510500140004550b588443c0307002641d940076000c80c89403103c104a0f11554100030407500702c1d0801020200038401f43c8020700c0300b00703910785801a1898180c980d10741007100b1200032a050301c00c250140c5030f0b032f0740c4880d00010050410508010416001e18004c60070803903558800f0031140b03000e0702c56075442021400040ca01d91444020030006000040c20078071035903a2480302c0711908171800d031010401800c0743c4030701c0808070481c1044502c00d00000c10300800c46004111746552030742d0003100451440341004450110b9290401400703115400784 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 854135584 1250 854134334 854134363
    0x602210405030f0a200f100b0f0d05030f0c070f06050f1c0609020a02030d060f0503191a0702060906010b0327030c0a030804142e0e0d17090303010f030201050a02 71
    0x650010034101d40125090302030f2000c601c12980c807607404070000350075208d41d621800d078002c2c0e41c0003651441e42400b4120000107407044050360301d00190706800d0b807019040065400d0f9190700c605001c2c0801100c083c2494042d2909040150030300b88180401c20f00c9210700e03000b00c5640301c904050410000e1442e0000806404810b03001d6441c1c2459032002075698002880c00fa020747d0801d2070019034055411030403019944090043c09440740100380104a0542c000021640d2840d440503000d104880500460300a41c9203601400d0107084c0025440c0c508001a08888144801002488400942c441c804000c0c581c81485030306004000d82d01090850103903144500031030141c400e4203000c0550060b4000d00c0395101d02d20200c500c000c2c41c91081d688250301842080c04056019000d00512200e48080b2130790a0b08040c0402c0c0801101e0301e19041c40c002c2540003000c100301e204c42e0105030035103000013640400341034001c505540c900540d00c0e85c4010203100190500800044c45000d0328400c0c0078507060056003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 854136690 1106 854135584 854135627
    0xb0f030402091f06090501030e01050f0112140709091a040c0506030a0e011a0310051501140d05010308120a02280c020d0602210405030f0a 61
    0xe8400e8a00e24007201103d4050712011000c00080c020b0795454804803490440050107540134101450941d9041504103c3c02c0b0700c1c0b580c5070703e0448440d1140e07840b045116046c0340c5501d81803110b030348100c1d01803100040380c101c803d90410740003284a5840b02981c460000750140701144281c07002451030301d04e650100203c1c9001006181c00ca500410000b0712251030044c01821114910240c10649510401403080c038901446101c0780500b01040c14002841c02c0c1900c0d044042003801064140800d0721000d0304c40034403120558030200c0c01e1550030071141d61207040039106500181000f240d9640d01500240743c20215000381c4020840040c00404d4650f0840c807003081407400d0982000802202c001c1c030801503510f02c28008007107400f4034001030f910000d0450340070316003c000c0302c01d4980c0b11015040c400025000011501c2818606025980300c80c4000800c64000100720706c4143d01503078 = true := by decide +kernel

theorem cover : BRFrame.Cov 853956834 854136690 := by
  have h0 := BRFrame.cov_init 853956834
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 853956834 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 853956834 ≤ n) (h2 : n < 854136690) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
