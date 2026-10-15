-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5168
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:58:06.545527+00:00
-- url     : https://prove2.me/submissions/4125dfb4-74b1-468a-a20d-28b79b4ae31f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 929316546 ≤ n < 929496402 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 929317796 1250 929316546 929316589
    0x307031a010f08150a0803030903070b100302030613051006060302300610090810150b0309120a09081e06060a08060a2d0507020c01020a080f0307030902030a03020c 72
    0x4081e0780c090207a030b001074142ca15240130380100d29040d481d081003041c00780000108507a01e9180840c070b202d5032a40444021140c151900e40803c0542025250381d20a8950003005020955120080e00f40e04049201d41642c45204095803442c00380014495903016000c5a40c02581e601e480c510340010781d180101181903a440441c00701d0361400080e090305500040c0807a409100c02442240848110a00f81c0021001c0c0c050004d031010480000d600200d4000040a500d906156586002099a000c00c8038440c90780e8108207441800102071038020001c03100e80e42081d9080684610106103031a10108581c908545c5d0f41030364003032450381040b00c9070380068225102500d15003040e40040e01d982010b001b900301a501c07425000c811401388400344603941913542050004140e0750b01150050a4280d41c42d0340580034080348641c455102041c0700c00400c0d00801c18500d040200030400034103520050032117007010b039100000401641e003841102100c0d07000354000d050a00c9202c0c01c100b011a49a4000740c840e90 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 929319046 1250 929317796 929317817
    0xf0f05010c1d0d02030309062d0304110d0501180b01231e012c0405060603060d020118031403130504150506090a030c06030c0e060408120705120307031a01 68
    0x44000d00d04901c0300740c040d00d400300f407010b8030f2010030f20b1405902042c41e480300002c902201002c00440403500300c00344444403000b140c078030400c40c00720b10300c400e40f009030000020000850103401c040a09000e4248941c0c000105042890b044907120601508103c4103284003000420200303e04895640d024000b0108209100c0e201c40d000412414107192006698485a003645140c2e0307005108170041c00c020540302040701007452403102405160f60104511542c0782a01040742e5082040903a48600300142c0305141c02e12581d0019225100d00088001200702d2414010000551a40c0000c0c0d070054070f035004603241c120303020001c0d544000c00d800043c012443c4c541c050404c8000c0440c120212a825124160f44080c0c04001c0f0380078818a4001801c1c1106200002070100d03450b521182c0680401d83d2501801540c1c4000c0020506c01c41c850f005450740006800440e082254000700210f600c60707400c40744030034104504211550002c4510700042a51644503107502c2c140c0c402c0007400c04809182c4204e504 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 929320296 1250 929319046 929319077
    0x601060e01030b090915250e100e150f1b060106090605070209042004060b030a23151f020a11030604230c03070b09120d020a15090f0f05010c 62
    0x11b1100c50707060380212044402095000000c1c14010452030b8940c12044060708031182d000c0d0120320010419409200105078080a840c030a1254100387c034801401c1050407141103400010b181c004010001400c0002c000642041d0304c1e0b0381c91b031b402c084103001c00f410442d03142000241c1240d51640c80041445020021a00180d0350f401e034040d800380e80329507182034000c4100c440010003001403100790b4100d441d101020071340c4445039016501c1105810f400b4002d00000c4000511000904071910f14401070309808107641070341c0b6031141501e58002500c00410f05100c01d016268151a921480b00503070000403140c02030000309886014081c0081e4010525420955a1f00c0f110058402e00440007031400408402001c1c014001c044010100404641c0c5060b141c50a0a03507542c000f282d024800c070b00101e40001900000319040907415815000340a4038040c0c3c4e1174000e140e90a00910300c81481c0c1d210160341c0021203043c11120010300075400261605090701d8018211162024a00c05100307140c031843c11507 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 929321546 1250 929320296 929320303
    0x4090501090b150313031d0d1506080109020a030213020708070606231c03050c01090c05030105060a0501021c120e030c010f062105210a0f03020310050904140601060e01030b0909 78
    0x25130b85443e10140c2502040c00c00703d4480307c0001c2c440d9102c25451148800e200c0f00b2022050710410000040001c0c5076540103c0d4200c40350400000d41201625000b0405072078640001c041d10001181301520b840082d98800b00340768003081080711080e540718424040c1c85010820212041700c5140c14000a29452000078001440313014207414111108e0f01582c02c052055080c0d41e0f024550000038000e001c030034a840c0701440110301806d40030350302e043c0c002401c2c0c0c5049140c0c07408681d01a0003409070031807100101511206445040c90a0145050103080c0620b1103108407840c00c84200095500c4084076004142594070030325443d1005801c24100f03100342c420701013070303500280c0f208045000f89240d09d20f0706604101c41e04080f00e4101c0d0985507c2d4000e190003000410340802d4030382c0c401c0e81c1680070300c3c815400c9000c240d5107030901c441c0106080c8014100380400c280c015019400061640c2c0c2500c590703d140c803c007608401c0c00602c0c070712060a09541c0500500c09082000c551000c5185041400d00d80e6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 929322796 1250 929321546 929321581
    0xc01090e04080d0e100c230304140712031d090606040b0a17130311030403151119020705040b0306040f03080705070507150906030c0903030f0504090501090b1503 71
    0x100301000440d034501a0013a0320091006000900741d850f0030310000509802049500440c002081c0c0150140c00e5010510400038140e40319502114159191506c0d120744500c190026000c1c1407051010201c0c10b411030a9100c10300074400c0d5144d65010000c4004881c442008403601d5018815500a00c0101e580d0b903829242038a5008400d80e8848140c090704440040c1d103241880381c0980880140120b807201201014221802601c4040794841000da087e90359100d1440007a10515015818155007121504880189001000d8042c20078004800c1d40300c602114603e0807003d81c1c46524204041e080c0340c0180c60011308124058141442e02d61107030444c0e5030038085e0081c1003080210001e070a890061094480003a000b50031154656280c18154082d280d80c0c10f040320204090010001e10036120780038603a075034034465a503841041e141d55010790303d40c0415040c0100b845001d1001143c658400d2207414020006c0b2000412058050401c0c03104945a035038217407400c44c000700100326040b03128403c000c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 929324046 1250 929322796 929322803
    0xa03180c051507080301030506100515030a091104140106081e0a1107140d1803031e231306020106050a0608100315241206020c010209040509030a020c01090e04 70
    0x510003595445142c4903846600002030205002000100c141315000407154801c90b800e800300080244c50f02e04004032400b0411050700d142c20108005030350081250000304100e4410003990004160f0040014140c44e8502c1b1007001a1011400411810b5802481d00d0703048186100d1070005110240f480d00b5405400803c015201920f40d0444032150103441e044946031500540c42c0440e01d00e6180806841d102d0080e0000000740bc250510b00003044428403044c1240d41c59103400d1a4503450800c90f142c1d01c042c0c00c005105204900c550300034842000440c4038106900c00c203000d596820507900c60b0080041da07800640031689001c83c180300c0d6480c1c07080040300769403203800c0242d26940c80040340b0f01c404140d500010003021040b60000e40440311038112540180c0d110914200102e961007030408014406d00c603c80d41e0348805008140480c0701da500614803a40703c0c100151400d0031140110b07060302c0c81500ca0f400603610006846070103070b07410b002058021200346481c1c0702051804010b58a4640007a2018 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 929325296 1250 929324046 929324059
    0xc05010c08130809060c150703050f1905060d02190f0b1201061809111b0c01050d0c020c15130902040609061209060c030b04150308120402031f020a03180c05 69
    0x8240d40d61712031003511500320343c840c1142e00601c1c0304094034001d030800b0b403110004242040081142240e050940ea03100d003540d0741e028a0301c04049200348d00a040c002e420260045611031103040580c0303451640445044d10201c0643d0924600792000c400e0000560080c00106020301c0a40c22242c075082c101d9044030200d2500a81444034001a00c19400036548644962440c00b10b50608241d1064091309440040c0c07a04014918411005c05ea00c40e140b00301518000758040003c4040d1010f9540140440f801c90301c101c1d2162109540480d825120038200c2c104400c0c40400c00354601e00b051100c1c1005030071030101c10340c145480c103000601681e003070303019600c24894402c0c00c0c1100462142e0180ca5250f03001074050044480d0502c0240c0204081c442c958041c9052480d408081c1580b808402c003225800540c00e45420400d45030440005409003040f03a15006200d2426101480c0c3c80000c0c22a40c0110300041c0c0d580e0600704050210340b002002c0e00c3d91241401005400f0504200445003280c0d401e42d5030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 929326546 1250 929325296 929325307
    0xc180612030a030609060510090b130f030c051c031b0201030207080a0e010f0f0905040506030c0a1e0f0503101e0914010501090603211e0c05010c081308 67
    0x400425010806500e18031010581e01d145651607000081210200407040144680700c1050181c2441d0303140c00034001c02c1d000801000144020001045440c40b50310b68048099101e60003680300e921698000e84448100341410300561030030500741c0c640e0040c026030198400045030f070301811310b00101020080b0030740c90204000075039020b5012140b0700c5070b01001203940c440030000054003075218652403a000540c0b12030030f40a0140100e41c0d1080001c1551502c1c903200745000b0400000c1c04000f4600b68040c00b501c080c00a0760b4403031110300009002c2c0c481400c02c0d54074010300500e0b4440340c035a2142d2004045088c082110391804a5141100030340420042010b00c0800b490402341207d000d9080516803400076601305204a035001e04108103640d600a100b0703a680c507404001a00c10900014001084000c0f29000401c0351001d6141d04c81900e040c00d44001c0901c05013a40071002c201d0181c008203451101d0703d0100311080c400ca02204900c1c0c24000e41c2c609140c8002200c0e00c1c44200c006002ca580001c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 929327796 1250 929326546 929326549
    0x1506050c1b1c020117091c020105070e040519110403060b0411041715010b09120c011e0e0307031a0f0c0a05071106041e08070302030312270715020c1806 67
    0x4180c80410f10700c844800c046d00304002c2d00c0f50340e00030520414880c0120604403017521407060180c580100341d80e81c4c03602d42110000003004000d00000e86000700c20f28443c00700031241c0103d8050419a10141c0042d191250710b03500300b03081981c00d0300d003801d0b208600d014102d59400e50100e0654082d00d1a44841c1c007600d80c10084503030320f00704200000b40c4203d95554000604a01c1800003410070070000e58140311107020320022140d0340c0380704600c010701062501501c8203510003119070300c0e515001e10346840302d2540c42c208046400c00710107030400c0d40c204030908142d04804080d803460a0300310402d1041740c02c0300e150200c0d07201741ca801030354002d4040003800941407040c06901c01c40d00c3c2c409031008010582d52070f9103000351016080480c2e1a50103000030540c001440040104010003100e801070040c0d0700e440c241e0001d001c0e11744e20080441d90b680203460380b170707986242ea69241107a1401c198001042a14146850031078422071120382403045500c0009203061036194420100c0b61240201120b4807940c64510 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 929329046 1250 929327796 929327807
    0x411010e1c06020a270b090f1503011401050c06070c0503120c0d0c080402010c060506030a0b09280b07050d0f090c030203060108010b0f040f091502031b09031f1506050c1b1c0201 78
    0x8c134040c1d100c40e1030b6400d25240b00b4500c00450484581110098550b4122401562b41c0d004820840041e0340040c8001002c441c003c0c50000c1425110300c055a00d84010b011828484510039a1817500c9004007003840d01c0d40125510502c60012140c2c1481c40c018580b56000800c5840c1c5a03000520090b110b00120b08a41c6040220980c0150f00919044aa160920450390369140384d0307a100c2490741c9030150078901004885034034200705030004607a0040d5a940707241607459902c10140c1012207540c80310443d01c1c0c291280301d43c08226100d45001d03d4002d203140101440c02c4c006030450f0440ea454070245800c1951010010340007090192000702e2000000340e604001000c188401402c6200c4864001c0c0400310a0780c011441341041c0b041858a01049185201d454000c4c2040c0c10740680c001c84030045d0000c00040052880030513404041025012001485c05e59807542e030100020420100d202c140d440300502041c4490303c440c07082820f0303071148000010408404041001d442c8410b03410040c043d64031a4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 929330296 1250 929329046 929329069
    0x603031202190e0102071d04020a1e09180c1403010f151208070816050d032313170a140f09010f02210c0c090411010e1c06020a270b09 59
    0x71150281510019030724081c7d040850f0100c1c4143c0c50080d02107855286002c41d1485003803d526000c1c140e608120280300100707503c00341d22100d55000d001240000d0306462250300580055901d85500d00d04c42d000b80750a54010102c6400c00700c0c2415581c0e0096441a455407007290b24040c510154011281060103207881407000241451000103500c0d0091071048154040492040d02110043c00701c0180407000c07104c545c0e041c4000c1803c0078020084002c0220850b6810402d40c1801d850b030f104259031b45000044107401c041c0b000000c0400d4800d461500070101ca11490385111441e4509580a0315401c0d2611850f200181808400c14900751103500c2044007080b0419090180c50b01c0c0c5215005a000c190400c10f00c2131214414000029123604209500034001c907072103000d1010003800200151144901515415000501041b1407100c0f0404c013840b90040d1402114010303561440454018407180710140038182c115400c802e49104d080340769080504070340280401c545c0b288400c00c002200c40622 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 929331546 1250 929330296 929330309
    0x70f0302040e010e0714070b070530060a050904050709050712020a0207050f06070201120f0902030a0f0302010c05031b180d150b0a0f090b010c050f010603031202190e010207 76
    0x100c000400c02d010140d881d80c0c0640801d403200381180451507030742e21180c456047c006081d4800c05001c00d1529003d10040d00000c0e14003d03e20074100c40d801c0100500ea05680040303504107042d00c081c071150341441004803001d440280c072202c40300e20b40b58072200c1d07890303202d482840b02965641001540300e9100f0f032001c1035154402c410035035488001000c02543c51100c3e015080c490456489e00d040613261403c00c0b01c6034554180c503035001940c0e04000c900300500d116000e00019503101c86a03030f00107070f4062009401c0144101800d90040710181402421200381c0540070043c803408000340510160b51074942055240134604441c0d5840f6007041c2015490801c00341e80380c0200c40c00030b6003000c0201d058146880907121075410410410890300b040002c15452040e04c03041e003602035003803003500700a07000001c1605041c100401002880d0b030700c203031410010040c0c00c03810303940d40c0c0010701c1016404440c60701080ca10000950070f0418082e5a020954100712644051103442c900b0400664024046040148034 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 929332796 1250 929331546 929331569
    0x1030501050f0102120c0313080c041103060d02010e03010e031605060f0702100902180a02120703180609050a0f24021c0e0f03210a140f070c050601090204140109060206070f030204 79
    0x49e50340c0c0d401c1e664614a0074591217a0b003030850019030010030009403886001e006040c03244640d955001075840102c00b4140f00e415548803e2600700c202c100300010091b018041041700c800c1030703580c00d0440c10131001401c12000c10044000303208081d2341c00102001c04402011002881d00000c1c40014280300b100b60300d01d0013100c11311003007111a200681c007404009201c05140209980d4290040703088440607110b00c49100001c001c076601280d203e0b407100740018803500840e180b41d046919240e02c0c141c0d803aa0200d8400c05c0f49144043d80c1282c020213040035200340f280c10b5080076691810004100e84080404112541d5003980c001c103680d04000c07036280f1541c807006032565064210605007a240e09803807181c03021403412000c12180400c034803c03403140301c140005803419a02c4844000302d251030081e140004210304603100d00b010482c28004113000f482d0007800141d0791031604034120071000c600ea4416050015191003000544d801150301d562088080c038240f0684036a8030426402030003660001105d000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 929334046 1250 929332796 929332799
    0x62f0d0e10051609080706110309030105130c090b0603010b03040206070609260c120903030c0d0807090504050f061003180b0106023a030b030f070501030501050f0102120c0313 77
    0x8910342d000c075016072100340011400101e00001034410000e18894541c0c180e00c840c104001ca54440c0c41c030380401c00058001c1c0d0349000d40820000b400d4a1050b94205c841c8001040340302c042040b03444000d0014180c40c5000d1115044060008800e40814810310300c40d0a0000b0010701150f95038811103103403680c4008104903041b1203040150b0303080620800c00040000701001c201a941c4035034145e4602c400e5040c020046010f101d40d9058850300010300d000e0709440f06210b02c81e0101801c5c070945041584640c0d42e02c41d01d1400c40c0300145a0490359020074003403031401c802d1154000800044550001041e02d401c0e046502282c81100244030b00e0200d881e410100b41c004508000d00400c025040b1400790342281d5010908402c0d01c074508034208503107032111040d001e4090381c201c0203880701180d002c594200003610984400c0460b040669501c1d6150254100040501c495a0035100d0700f4090038081c0c8140d440c681080700080e6880100400c11509084042001d04228000300200d03640c01e199107a1400344a03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 929335296 1250 929334046 929334073
    0x3022214060411090d060c020f0f150c03070203070b07020712060912081911042706060306080c0910030204090c0317031303110a1b03062f0d0e 63
    0x54001c0d41e40620880c24600d0700800f0308002000d0703d00c42c01d002081511103d4103503a40d00010145445410250700621080002401c801c3c00b00594243c0c1000c0030b03020806003d46010f00d4201c0050115482d14030600602041d03942c00410303240c0780e9501800d50480740d201c40e1400e0b840c5c404a0781c8641549502c41011004101c541c0d00300202c0b07030384240c00400a500070300a05580040088400e46100031000441c80342a404640110411603040c141d8103190a0700d9840401c40319105080381110b4140c448003015083c955442150002c2c24035203001c104050030280c000e61511340c405a10f0344540e0041d800f044000c03000d0800b000041d0750003881040b42010fa4606100500868801600c0210703e83c4646044188800e08481c4140f403810201a00d00700d03907540903a000c01c29154203241c3c6209114030000084c6100b40c4000c1c004498080810101d89580b4010090f5041d007011005805100700e0340c3c602010114690070740320f1405150741501d54032030458403c010001280e040450340b02c0c403c0b111960 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 929336546 1250 929335296 929335331
    0x91104060f050f060a0e241614070605030711010e0a031806170a0c051b011e11042c0a0204030209010801140403080618010b0306090709080601030222 66
    0x102c1c0ca00741c030a480b0180042d420403603113024030318107140803c000f44000c0c0b441d0b180c408a0044100b6680f00d03a07102d00b01c041e03512a074446d00071150541059442c2d5030084140f1401d2030500914054103c01822250b00344a801030141c04041e01d80e40a00940d056503181d04002900060f1002c0c0d050f000302c1d4907804660034000c205010940000c204c40400340d0000c14041d204e000401c1400c28221002841c81c0c5a2519078401400b07101d901d60200b01043c00141024504003a600c9602500d010010407801c491005140c0e11740e0000740d00f4072802c0d01d400c0c180c46154200d038050b00c0458003801e400315410f400e44454080c041c40c51460f010b0486c4415010881d0719100e6074094000e41e4020f40e9416501d03a20b0301400f5089416840c001114140c407540003900003071042d0452940401c01502c1500042030880710b82d0303540402a0004d6441c40400b1040240c2400c015001d2540700d9401c0c80d0056a035413400000e2034403400103020107801150107020040c414900341c4601078514007658400c00c100b1a87e268001d49 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 929337796 1250 929336546 929336549
    0x5031c0801081c0e0105040905100807082a011e1d0d08030a05040c0906141215040305030406090c090518030f0f0d0609110d0b03061009091104060f 65
    0x1280d8848000709503070703000141c0d9051291050480164219011100395101e1031800005810440200400300e40b0329014007445008141c0564011030315801c01c0020750910b89590400342c429481301006c1d118030900820000f8910b00c1140c0251040e011500c0126003190a500506100030fa03a00030804d10709034440825090f52035403c54040b045c65040041103501e040762100901284418004107601c1d28441d844281c10501c11140045956034907500e4100760b030150b50101c40d800702c1c0641030840604220041640380c01a680192005d400d040b49004613008001c0c10213130400401000050801003650303c8140416000314111805540d20f00c08500546000c0340d0849611101e440d84070000301000007a64501c20800010030305102568413051015040480203846070b80e1034240019819003688607550070015900209560742c010005070300150f800811310349000c0d0b8006800c2011b01c203a40356031034080e01c0c03044030041450580c60402c10349400b840b4400942c0185050340018900e15081c16030390 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 929339046 1250 929337796 929337853
    0x11d060103140a020907030f0b030d03270b07080408130e060111070e0c1c09081e03130f0f200414010e061c0507030c050f04020702030a0b100503 64
    0x20b07030110384499030944804070248020341004541000c110302038000d0300001c103074641101000139003240200009203401084062080442d60700c4200c1818400703282ea101011920b00c1102c039220780d40641c0d6000c81c0d4a401001c041c00c108103400843e0420540c401120940054105076503031035600d99030201001ea9050303c01e0390101e10b2580d0349888101021490200311012031400c6000ca698503082c5142d264061080b01e2240c480d4168005454030030381c4602c48405004140c901e41b40c205503d04a414140480c0c500e007003c8405000700100145020400e03c8080c2d4000380e803900406aa180c0010b1070f4a403d600240358000700100d45040c151120b851043c4004202c03020704c203507180711207a91040002801508201d60400c400a009400c121070714594002ea0310b0402e0f11607580d561280c608050041c0c2044a1300c64034440100458980070800d07000d1078004403411441c00480d030740000e580d0480c1c0d41c4024182403141002400161407014010010000517003520160f44000c0d00c48081e0100c85800389 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 929340296 1250 929339046 929339063
    0x90c07082a01051311060903030c010b04060609030b07030218030a03110115030b0c0304240b10030501060c020d0503043605010605270a03050a060b04180212011d060103 74
    0x285200c41c1402680e0003911031862a1004072915110100107044600e45660481001c1090800584040000300344203102e4000014064800804000a446056201d0005c0043c025401e1001c40e541411480e04020340d4200141e13150803d1010200340465944150350500446582606064100e05071045242c0880020000202c01420f0b01d0395500c07540c00040c0011212100242e007221403200150b4201e0f00a040c84445c0e459500200c1e404840c5041148001580381c980300070007802c080720304074138004881c01c09000940c14424000e000170681c0300c0192207503d1200105050100500c1240c000c0d140c4201c2d00280350788900919000c0c3c020484038002407029529252905441502c6914141d071000d68403103242426540b45030502c2e00bc0ca851244402592040084441e515101c00d88002c40c4a000a0314049006042004c119801841e00c0c07401141401c0d070011480c04526218070b4040d90490b02080320040c902d000b0b0380103082c00da0b4455040c8104800d220f00019001801070304a900c0385c0d132007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 929341546 1250 929340296 929340367
    0xa0210020309131b050706020d020423030a030f0c02120102030a4b0f050f011707050f010f1806030b12241f300809090c0708 55
    0x2103001310380d10a03010404601d0714000c10300300d5601c140c0c0242041c0340101c10160406041030744d41d100301e03401a88141051b41d40c4c44010304070150070f020041c1d02e48a00701c1c050204008070b074070040d1603191441440000c106507424048210740d03808403080c0d121141100215182e00d07041c3c00850041486a4108040c002006803000420440000220f00c1d10405029401001c2000e24244925110140c511810315210020f02d040e140d03d6124241c407500101c4806402945800c0b01d0440c030203504840c0413416000010180990b40f9112020990000d0a00e00400010080c1200316400a03d079070b0010301c4601c1112001803a00e84c15080000404000c0380c00701500300071b1041a40d83c880c0e81c00c030f01000c200d24074540b4484545412600d190300c039030161144101c040c070308202707403c3c05041a004032a80707910403e0011400c00c079054200686000346039002c1001302030750300c6022041c00303030010341480f03030803840000741c1a1203101065030307891a03000c282580c40c1c92402080c0303081d076009400ea11000916042d039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 929342796 1250 929341546 929341579
    0x30a0e1801030813170c06131d06100206071e11030c0304080d081b0d02120f0a0c0c0507030f05010e030d0b1009030209160e06070606170a03090e090a0210020309 71
    0x4000098100c40c000301891071b4100103100054004a1200c034554010501c006072450004800d03501d0080b1102501002d0b1400788208041d86080344036038001c560000040111071038104041803110203100c10101a1054014409c403245900001c0100c180d000124030041d103000000081d1060300c400d0020341b82c14103880c150456004000300d5034103002c4180c02c403440d00030350307419401041603d40e000b1000d4900804888001500780f401d50741c10340200d2416081242240300c5110303100c01018149404210190700b920b440741d4820540c0400742c08811180b40c0f120070003609500058281c15890296501d40c8900f500d07000085c104118128082c1512045c0801c501740306200c10030540340d0040a240c0a03846089141480241d081c3c4000141703c51405604c1c0c0964900004d0700040307208400108005003082044003583c0405d9290445c280e02c02105040044d41003500c4a01359420300c080781a4035a201d4540c0c902d03180a24001a4100d40640f11400c0495030120003072070304c46010741d040f12210400c241d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 929344046 1250 929342796 929342819
    0xb0703020304031e0e0901180b060415081008060906090105070801180218150c07090204060e10090b040b03090d0207060905010509061215090c0705030a0e1801030813 73
    0x60b00100012010414a074036086803100780002c43c3c401c2e1906134481c09460021403a4034034203070000c0c924040000c44940c00d404050061204c86403041da03049007070900d0284c400718044030b088000424400404000303100700c2246075088004042d01000c8594a0401c0700300315442d104d050328010055424907002030307a011f0094485c103048404c03515000b4411a84a04100c2c001d4125042040c821000281a404d0329500e03d2000350b02e607040c7c5882c00d41d941c20000c66051501c80f855004030002e074014801041a950808409500140b043c0c80f4803016140048044900c0512500000c0c400c0d00080380101d900c1c860307840518410140c1c20111800808001c0b01070385d841450307104080c00a01c6181c0e0a00007035100b01c0c00350210030000303424035040440c28078200588100848000e40c20386050b0201a170305140812400d6000030790021490328003121920341c0f50301d03840303005c0801c824010340165140d255124240107261400b07650752410040d50712441e1400071580148940641d00e450001c000c070302404102c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 929345296 1250 929344046 929344051
    0x2010219030207210506010806060a1a1b031204050303070809010b0a0501030f0b150a0201180c0e04080d0507021509120d0b0406030507030f0b010b210612190b07030203 74
    0x10b800810352285056110256081141814542d4105206a5100080e4200300d0306001c0c00217803005c0d281c149800018482c845550307a100a040155141c08901d401c80c0c0f400849007803070b010344203e04020040d03484c201d15511807075004980200f000020481440000310165004409540c0c4180254443c1c2e031405082e5100200c03120b40c4106404803c03c0203601079440350b88000402000130400081c1200090358420718940141444400040c04045c03031507080c070580d400a03840b11035181001c1c21a80b01e0307010451140c00ba01511000d10340100d414003007254103860b8840e000c600300b07200340c2c070b400d640080d2584245034040d8021304105021800550303001c2007100005100d40040b80c1040b4942d01c2d10303c05070042002c0c00b078100341d8580003c0040b0308240145400341d8054505604807000e14904040440c5059101031401141841701078228410007402400105c00a08602840e131038200002d1010a8802c40540840c03180c04400482888034030305c07014180d40902a0480c49590701c1505a0907407104 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 929346546 1250 929345296 929345303
    0xa060b120607210c020a0b0a020f030c0a121a0f0411070206030a0b0d0308100902070f0f030e060d0b150a17090a0515060306090106082a150702010219 66
    0x1600001d40d014410920f2044003c25030104003100002c9080d20302c01c40d00030243d040d0050300040105400d01001844403500810580b0003145020b140000f40722043c0405019030025000015840035040c2c81025903520041e460503042000f000d8002c0342c222a480310948040c02440700c0540360410b4546072250144030015401028a0300302180c0c00c001c4607a00003002603403526912043d81001d900c900c101e0780a000e201e500e03200424100482052010200384c0d1055203003500400000d00000c0300d10305800c64250744041c40c0003600000385030640e0b9010384507a40c1a00004003081c403075607492075500041002e523825070b140c200c1503112011042c034902c110312116000c680c01350040c1690311044555540d002905009980000c402c0b5510b250500001103018414113002c1c1c0f013404868582403002e65007116811008000301403420b038044d5211041c00c841200344140304034008103881c00002010901d10b5004003e007241d00701da1650005260080b08040e401031040e42680300d90007100e1070070201c007940c1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 929347796 1250 929346546 929346553
    0x7061512030f090f2d0e0603061810022805090a08280c09090318050909070b031915031a13110607020d0b041403040e06060f1603020a060b12 62
    0x1013401c10840a0358405440f82c61710842d503043c0ba1140f0002200350054900b01d0244078160400348100b61130700700003070305000301c644d007110a802c500c8800107031500408405500158070f0314440140c5402c14405102110b100d42d030484440c20740d0b40d42c018000c01d6084c40c2150740305043d03a02e42c0c8095582d801482c01c0c0340c0851480320101c0c0803503042c1e94101510107101d80b03510f0401d0382d22030103c0c03000e5807800c0d0011004191680e0f0380c0c10980d10000b03141c030041c0034192420070143c0740c801c190f1951503415101c0c003a641e8030000045610039036181c560b4000c00100b00414806200307074000050300000c0303522050700d000311442c20b82c25030f04440d040c1c40d502031034070031030a010038011035216100c4154100b00c2c140d074032420801c04400141c8403500c050058500507100c0a41070315050810640b02c40c5080604203540d0800c21060050b50252200d0780d4111105450ba5505c2e149490103000b210700c5004907506134031400510300c1d810540d0000d01d5085891080500340310882d00c10307040c8001c100f800c44c2c541a8640 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 929349046 1250 929347796 929347799
    0xe0d111b06090f031b03011107150e190302100e06070c0602450f0307030323030c041a12010909060b060d0c080619030807061512030f090f 61
    0x25051000c1c2420742ca00600008503040070100280c40d110211014002000d94000c0b003104614081c400e0004c444507102c600e40c0b13044015a191040c2054045400603890741e00c00c01080d0310070003044801000025041c00c44602501d038100655603890400e10503072860305003180024603d2002c07529501400141d124542441540e076140c0d006508598640501960030500158140c1e0081c02c02d601d0a8101c00c004510b400341d98001e41950840420442d80505a0800d40c00d10342d490006454044a03010324119920401484000100c80803503000402005c8e808421309c030a40400000600440748800c100300c0034400122607503035440c09030b0300b80340764034190300700040200440e140c12401580d44103840000c0d04c0701d50400000c0e4039800115461101a50351303c800a01f10750072440d000c1d0840c404441440801c220076035000d0f805021800700408141d004250142000420f0b000312140c500c0a4011064054803000000c03a944040d850036000115030b007000001c4035000c0e00300310069507604e042411095 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 929350296 1250 929349046 929349049
    0x1406100e151201060521010b041a071506080706020f121c0606030c0f0e1309020607050114060f060304050c010e0105090d060203010614030705071b08010e0d111b 71
    0xc8007182440080100050307500b050000585601070882903c400da111000400c0e411035461000440036581c0c2c02103c01440141d058005403002c89510b842c4d903500700101c41e001034940c0e02588100502c1070001e034a0984484126401c020152030a500444020907581c0004130f9031002042003280040d04907018401c1c802039600010004007440c24113122020048640b104112142075000340d0010b540e408044190a500c100c807500c0c900c1c940e240244c034820a00c030003e40310110251460100a940e1072040b400c54642d0310980340309a030064020801d501000c002d254011000310f400921825401c0d41c10409482c14030b00781c0380116000401490f04401c0d1030300544490126502d06818400107102c400502c0e41c41c012030b06e1403948641000758495140c0b21000c4d00e545410000d000102c80c00b4802c0001c104e5004c0203807000d19420402e030007480c19a1103d51040955203821078415035007000a003100e04032000400c1c216104e0031f0b42d54501c03840350041e6216241c140d13180c03201f1000001d025940140d03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 929351546 1250 929350296 929350309
    0xb0102060c092704050f0609030f040b0a090e040b09010b01111c1e0306050907030905030a0c061401030f1a090c0609040f0e06010f080d051c0615031406100e 69
    0x3802c82c0d00c814001201d4614206801c4074208513800c660300e602c4103001c034480d09400d00c441c580103a640d50046040c14540c1e440c180d21802607000c0c2900c10400070480510240c806d180c900000c143c035100c04501400c0504086d0b080c40004c40d590020303907003032100b0030178030394403484806290520280c041c0c042100c0c42e80340100103101d2084080e0800c498a884c0c62140240052030b42e0540329951400100ea0303180c40c080c88200c510081c50081403600c1c00003550b01050011003202c1e1105103d2511402400c128505480145501540b034401c00304444004410460300d42d038086840350180f50741d01410a203094107180f030140b0440e400851500248a45c0160307040000113440011b07401000452143c24003036140c012503d485549030340d103034400c4004110303040c000401100503241c0b0300050402c4400c0a400030300705201d01c200340e180c49881d411040b507803424564441009031050340d28a0801a001490040c068158483d8501c1524034035400700b03903070f4a0320100707817031615002c7d031150f10004403c60f017002030 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 929352796 1250 929351546 929351569
    0xb09090c090f12100513080f0a0c08070303020901020c120706050c120c0a0b070903031d010e031213050604080a0f030c0b0c0a092102040b030106030b0c04090b0102060c09 75
    0x10041c0301c207660415143c0e100380701c0381812007000300103101c901e0342c3d0121310042d101c000c0c140110b62900d0a01480201c0c4410040f94280c0100d03903049a59940307000c0c412100001940009080d121020030482c0030180e050700140007002c002d030701f11048140e16008101e24508400040b51b9a030340300010410503d40103002501411040fa8240c0348d40c810119821451a8086e000704000c41c0c20040050003007010f02e24076240c00c02283d00c1d024030b50f0740c03c0d40d4001c1d1050741180041c2400d54440c80710170079544c2c03040c9000030080f00081c099400241499651100076044221a03502129135203c020030307241040410303141200c440c07400500c03200e0700c80c0d1190110388507000010f50802c60040000c5000c90700104509024507850700c802a40c80495071801044c0c440c89801c8501c0815242c259032034060010f4104209880c0c0441700000c0c1c3c0c000b0781001a0060805a100604190032030080010301500e0310080e100f02c0e001c0070f00511044800c04012601c030390003200c110890035014046200385060081c0c0005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 929354046 1250 929352796 929352799
    0x180303151309020a0b0a0318110409140a0309180b13020708070b0c030603011505011d030102041e05031b0d08070f0b0f04020424091a0904050d08010b09090c09 70
    0xd80e070b80300d074001c00c4611442d50041009074200040c00c0b407a90380c1c58401c2c1e80301034504400c44003071081ca40c0e807005041603890041070b00c100d860f40c1d012030621000b002e030228101c11607000c50703c02402030b14014100010714890203000880c2d80381035039000605401510141ca00c0100b0000c840070036007000c1c0000790416581511040c0041c030101c80052094201c1d01e00032103103030205d40c6d12840c3c0340c0c0406003964044100c284280c0242e810402040c1d8001c1a100c42c090041d0b000325200c14110300c007003402801194040d114461440516890645074a6104d1042c2c50043d07043ea18440039104000c241d10201d504c5c20f540141640c50b500d008500002d010740f1485201303480d040f400c0103640e154441a0001a1489101803046009000071446d040c4500819010b40b0083c1490f030302c2c1004079040c42640310b4461884801d071101d42c0b1540380d8070380f01c0d490024210002c043e0780c3d090402c1d0400302c7d603e00307414840740d010854040001c035803501101e041e1560003030010040f09880e030700e0761440034080d001402030700e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 929355296 1250 929354046 929354051
    0xd11030f070b0a0e030705030c06011e030b06031005010603060815010e0705030903040f060f080603060f0a09020a0801060303090303090b03060303040302060705010f05040602031b0c0c01032309061803031513 91
    0x100c0d000751306000400f60140610000d686034032070265814201001039000740d2044d042000a6004d89448004080c1266040100e41c080c2d83d69510119043c0080d20000c0c501c0d440c6042c0020848503003540c0f1200945d903007107044401c540c246001000441c0001c0c0038906035030401c18002850385104100666000074628123a90074544c1e81c1d1018064040b03240c0000012506543c03400c00c0c560340c00f2586a0b44490120b00500d05400d10b111034102010000d0144250944c603010010b056440d4034050f000181051802000010b80da828024501c038550701003100002e4103400000f58590500c0250303800341e40d009024610305890342c1c0c00c10121780d100607022030b995500c49401d1490100c9a00c0b40e01c0c412401002c0143c2c0c0c07842e05d19601707001d4585480302c0482a00e07044c408081648400210044010000e007000104443c1e503120001502d6022080600502141000c0020796440800c3c41c0b40113114101c8640348406803100030945a0100710b480074006004039a0458840c9490402078151040c0c44200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 929356546 1250 929355296 929355311
    0x1d0706031415011b0302010204150c020d110f060f0705060f070801120215030901051506040b1b0316080a020601050906031009031211040e070806010818010b040e0d11030f070b0a 78
    0xca00c84d1008000c81030300541d5010400300184042404100d4841d5080d00c0c22030341000345940003446098401401800941032860788140a80740c0781401800070000814094440b100e09256150035400441c1c00c41c0c4900800c0d021901c0346043c103150500500d056280d071a002d81c208505c0040881c0c01c0345003682d000d907180700e0102c40e40307207804011406940c0c00302c004205032401c40341d074005008522045034003c060030481003017031034003031001d46010542c0b402005c01c00c503d2242d58203256000c1c0004c50111030407910030000800c102c0344001d07c0482000d400b9100c484e0380e141c4c00c00c9407102003103035030f20740540043c00310b0812885250301000307100c0e200c0c1c02c00152482c0d080012804030790258180254003140002c062044515907080203612100350b103131070002803404e400020b0120720050a00c1840000d5003055070308003103007904403442ca040041d1041004070007036200e0a40d203290415413113022039030400003a00140004000c451441803032510981c070703164055540e445800c0000f05011500e5603554907 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 929357796 1250 929356546 929356577
    0x90f0901090b01230a060f031d0f10110a0e0f03210702092a1315050405190b033715060201061401211d070603141501 52
    0x280a40031303104034a03200502c1c800c60410301080e007800f00e0030740c0d115415400080090b5540b00b8070013042c45040d80b4003c12080e000c5203401c0650350320200020243d00603d214000100e000251a694842405506000c1c1082d1304071080c000e4403801311060001540c94080c40d6840c01d00038880b80303a0820150803100b036642d030013012401d0790143c041800c47d281c07000546030342549040d102c0307a81c02900c030000070100111851485500e19907105810f151020003c0b86141c1c1600c2c3c0243d001c00244003036040c10340112190100140983c0c042e000d0584143c1c1401e4807103080e580d00e401d086098552464260345151200a25030204010390103010f1000216503144812110a031480803010407400d80340840c6e44440310906410315a000c0d0080c000310380c58a0810460640205d6403c401220300382400681200c2d119142d0507044944041050b000e414415050380e813109845006103041084d500756103019450744d00480607140111400c0340c890302100003082524041100400482c41c0504010190500b9040d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 929359046 1250 929357796 929357813
    0xa03030f12150801151415070819031103130204050c070f150c11151b03150a05010c02010c02040209060c060f01081c1205071404030c140f090f090109 66
    0x55284100c200340040820000c00c09004d580380b4920080ba00c17902c2c10741030503100307804a80e00c0c1840c14800d138000c0d81a40210701040b802c82d81c8c0380760050300301130f0381e00c840300042c1c0b0120307050103500d1780000c2c504003401c1000403031001901e010301103481003c00e814071103800304005058003904a02c0007200422040e000202029035500c83d0902c1b81510140d00d552500c070410454810490341001c1c041900248002c050010510100050720110000060786450300d0303030508611300c401d04459003280001800a03011a42c2c40101900d44121000311405840300c0045922250f004d40090100d21000d001c0001841c2540140018100180c0b49a0030010342040c580e00d0150305a800c2146400500018032040a0078410b541d42c5000055050031810764131307200240f01c1e200c03135040c6041095807000402c400600c43d60300f1941e448400007640751079903224102614802c21600c01c0d020a240301c000301a8550400c0c1d00c0c103030303a1080c005043c3d503a1640c0380101b0405114000300080899540c03065840e00080c05074 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 929360296 1250 929359046 929359061
    0x31a15030712200303071712010b1902010e0a081809010b130e040209040b07030603050708011a03010c0522030614011d04081e040b0c010b130603020a03030f12 70
    0x2581c602c0e880403080c0c207110408000c6001800705a080c0c40b00c1001040c0c50004c2110b0006074445c94094903d003808461001a00501380040ca5044c0400000122250b000e00030300055002c800c030007400e1200c041002d0b0308841407400f04040c10b400480c06600491002c1015260143e400c11200c903444684100080050702d09030000c0c0195100401c0c240000382c1203031540c40103809100d1100070356042070340010b141040c006000414414051002a120a10035007100000350352000c1180c0d0b201d52140c81560181031000900700020034882e40c298014a0140944074001d5219101d403840c14008004490040600c1208100c0c6c50b0444100003000134a64400c12a0942058844425950509011043e40c00405440f00b41c01c0c5001024403003c00c3c20003003195100c2800da815402a100100100c0000e8011503105010740840400c50103281030701074000c0300040c4801c50b041445440398a0000301211ba6070302001e5000000080c1c00d00000e400f07200500380d01d80d007904103d01e44054200b078a0080c2d4845 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 929361546 1250 929360296 929360309
    0x7062001050a020444010b130c121103270a03090312170a020c0c1903030806150f280e0f060f030402240301140f0a031a150307 56
    0x41c0801c60342d07030000c5e010f0b00303e0007034142580302108404020b60b10441200c40500c40701e030300355120043c0d80c10342580115094940901440d488070848202c04001b008043c80c08004070312404402000781c00c05104545d1250100c1d00c2c080d05603150f0640f400c0061114040c035008003448080304402d078410030440b0741211840391b60b45440090861902c1480e5109032000071301840b00d005040c10180d01c03601e01050f0b010207404001611043d02c3e51015140c0b42c600c4881940107041e04403066080750741995810140e034000e0711002d899440d41070510070200c018569400440d08140308100d40322082d58010561002d004400850700100c1111408e2130400740d410f40760218031408001c9520341448000910b10500c1114102c2c00c00d9038500400030f1500c00204000d129500480e00110003402c000c0b840d4603030b50103e06100d0b45a42c0c58500d1081c2035000202c0892240540e0450003070b0524003200c4000c16254003d5288529000c0e02c4c6642a640074083c041c44484414510401ea035501c0820460004102d03 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 929362796 1250 929361546 929361551
    0x90c03050a0c240e040e070506040b040305010e1c03050603070512030c060a0b0f0d020a1a0a0210021303060c020c030d090e01051e0108220b0601020610060207062001050a 75
    0xf5100da210039949002e40006a2907501c40f28000c0c145410030402c05208074180c4020074614012450982050050b40080350700c11408100403458103d84009001928802d400801041c0849071003195241c07000340d103115000212007921002c0503ca03030051504484090100c840040d124000195405035241200303809600201c0c2c0103490001c20000c003a0802500ea40030002030a60b840170528040c41038828a00a1211220140841d15a002034030010141c3d401d01d060000d010342c0c04e41d20550301c80c1020500510609569880c91000d910813650381d042c41c4102da00c51103281d59124406064007814000941c003030110313500c03004d072018440c840b000101c0b07555003103490342460a110900d00c410f03003089001d0300401c0d9180e0359403c8088070380c80b901c40e0f007400c00009959820184004d15080321511242c0d5548601203901000500e5002c01d005083c00d07003e0344c0c00c07560390b06080e402428040c814900141e01440e003c001a80c00788015210502840304489400103a220384c050940e81c0c142d40f00b0360200d5 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 929364046 1250 929362796 929362799
    0x1228060308032a03060411040f080109120806130906021b031b12180d060204030813050414061c021e0f0904080a120605030f10180213090c03050a0c 65
    0x45441ca0004a109050705240c0d029400d1007428401074003000f0100e0380150707a030740c00c05101f00301800c0c06da800404580b0006601c0300e40b900c4520380a80402c035402c6a03135114040ba07107150a0301a58002d44115030290841d8000601094031602420317031030f082522900e508106000d000002094042601d030130f104000e65030f0300c40d006d04008001c040015411810b42002c111000c244040f542103943c0c00b02e07004000020355074108000b07004000040d00040c00b8071301c0040d000040200340400361011036031002440d0250341d41d440500c13042e501b488441541c0c0c84c0b11140019400e1401c0742107400c40c00b101d42c8040104500c250701140c251840c020241411907101800440141740100208101c80f400b80e4200d00c841c2801ea845403a07034028500d901d07003481100607241009545640c000c100030f2100404942c0c0f0000c0b5611074a86a40c40340300c00b01a141e00b00b40005a40050f602001d041003075000c1d1525075030368800b10303050004103403240045804c4601b05200202180c0c2c05c00110b00400d0082403140c1c6800e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 929365296 1250 929364046 929364061
    0x405090a0603050c0409081c0b03030d090611040302010f1d0a03080903011808040e040305160b0f0108120a03090c080703030f12090c0308031b040b040302030111122806030803 77
    0x132486a000354030403820f100d2240c0000c3d1213441a240034a00941d0141c0000c4030000011002c1c0503c0d140340d070342612000c00d00e8804030001d5000090b429003c0d140030464032044030100340c090b105070302019001c40d40c07003000d41295620500c05025000c6c20300c100400c51140003000a0892407031580190390100380818254143e150138407504488144010040c54104c1c80c0f660b60403060301403807045040090101001a0a05006004030b40740c840c5440030305000b501503841c040303001103415140510750303243d0400086141d6200090110a451101c01c0417420500b0303400084000d414910002c0700d219181840000d0702c1c2c0410854030f005548292100b2603c41c2d46484020300b007041d5480d50328016030400c100c01000c200e98200c02c034113803074008600c0c079501c1e81e03400079240d803060020415616800700003900103101c858250151054a100314001c1c8140c1c000072a407442c407405641103c2e0f4600e10b010020640700c82031110015000c4c1e50364042504079115165040003100e1056100f1303610b0300700000400804 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 929366546 1250 929365296 929365303
    0x10b0405060c39030316020603090c03100207120e060414041b0903120801050a0911070f0b090c061804090c0807060e12030c0d050a0c1407260a0204020d020405090a060305 75
    0x7840f5042d0000c60400210340140a44500201006030007100c0c0080032940b040c1c0c080c010a00f44071f5000c3d045070003170015003003038600a600c00c0c079095030030400e0300001402092251f98407002148008001d1800d02e410950180b40200e018040c155000703036030f0903d401141d01d003040340403603035501030300d81d010003074514240301c054010008041010065404010700081d50790703402d048292007005500046d00c0460401100140c4a070542c050410307580308105404000810001d04c3c869aaa0070954801e550345e03030103000c400c0c091201501c11a42282c4002e580c0c1d4201580508002c1b80500c0c1442e42840e03490071550b0410455810100000320b51040018150070181e01e1446082000b0008502d004410032541c0e46864a000110080140000b15082c00314071642c02c2003503503600121030170001c0441c1001c681d6204041c0c41075502003107103850100c520840f425188402408008041c041c90041a82000002c0d40108000d00440ea400d103c08074841e110706001901c220b21003200003d01c5815030415a00d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 929367796 1250 929366546 929366653
    0xa020d050307140708070306050a020423120a080909060d0b01090e070b0a020319260f0f010812030a15151403102c0403080a14010b0405060c 62
    0x404d51003d007003080203150014007502200d8211100085548420403003074082d2049903c45415403902122915443c0d9009076001c110140032030b50300010b40540c220345615100c1052002d0441901889150042d0400d400c040da4080c0009101d40310220b019900ca4200364400c2c2c000b4200d40b40d59402c403400303055042180c0c0018021404040d4104044480025981d200340c4c914500805030a0000e803c0041c0280d04003580c81c110306100f203400125030922205001c0c822901659119501740128092803044845141a150b164001c1c000c0b044201c4109406648060000100e1654807040a5010f81c14900e5040240929410301c1c410103548540080c104028a488034603614000c1090080705015904110110340c0c1003449040d400b940a5003416056030b4036210003802d07540700c0c1d04210402d54003007800c5104020401c2c0400c014102e0704212500c8070f400b40100c2c220288200301c140064070308a400380c00004207038021101c0d42c0082240c072415802c44440011a20065034155840c0150072030410784 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 929369046 1250 929367796 929367833
    0x100803031009020903013c0b060f0703120603030c0308060102370204020f071a1e04300201110310060e1f05070b070f0c0308090a020d050307 62
    0x14103604050715203800c1c8221a100b0418000d50026082d9003030345083d000302d803240d110140036910701c0310355510300d50f04001c0410068010003041c01a080c1d07554854071455040d0071002e40100d007844e01c120580d954a07030001c41e055041c80810851340181c2c44c154000d502c0610700c2039a40c104c0c400348034a0040e100c2400a05024159000700c8034100400900013000d507000e80030250035501e04a1015000c081002c14818081c3d00f1500008450b01454a24002002c0852141c13010603120230744181c2e40c1d20010001c0d14280956100100040e24134151800b6258005014411814004503d003040340401c0c082d00c5000c801c0c0011915941e42d04070740a10803040c0b925950072040b4550301c2c2c4403080e407038419810b020310400c0c00048068140107440310203504018040d01d55280400c000182c4010306070707411400003290070101440010b074525214401e10a5848a2922028169851568191070074203004014820a11400100b0300141ea00c40c003034907078020701400c041c6a450019040c01004402c000e200c00c3e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 929370296 1250 929369046 929369053
    0x50a0b0103180b071404030503130e0606120c1c140f07050a090b0c0a120804050c011119020f04020d0203151203070f0606120305090a15052505060f1008 67
    0x2c102080942e0304403644440c0d680341c141c94903540c064048a040c0036541010b030030351001040c1e1802a04c02011020250b90811064072107079031f10740b01041442e102d2003480213108403460000c0303110380344660043e0002e80c1c15103c0a003e1060301c2007844044034202180c0c0b0700b400d079104041c0001c4400140f0f0003500640703030345442ca1406400403400342085444d48902d0302a00700009660342106014004005100e07400032000f804407405070001030400d6402d481c02d503558010030050454940c014250380020885d1351016054240c1070400714020714048000a91304000700b05140a43c542d102c0c80280a025224040180c880c00c3c1103078202e10700e80e0080c030041c2c021b0303403540a810f00603813000054480c0a54018100d81c4001410714000e0701401d81d50348a84170781c81081440d141055008000f40001071000c2d03170f03143ca4481d5100101d820f040110b030503d0002c18800c000c3d8440c07410a1030008490102c030760444001b50a0745540d024034040040756420102091042481000d20882c0c00440041c01204000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 929371546 1250 929370296 929370341
    0x170309040c110c010c0f06050f040c091a01050c100e011a0d05031b0304050d0f051b061c06080a03081006090305030306060c010e0a050f0f1204120f06050a0b0103 71
    0x82c81c1d0354108040b00a8140568804080d04000309000b001c103031560300a82c02e03c9182042e0f5007a407540314082d9000ca6a0024a401c0480c020005204280e40620344101c100900a4a40300565841c0c0c05001c44003d14020b03210303101044c1d159402004840144240005a00e101e412205c07803011500c54001072141130b00240000c0410000401c5c1c1c4c04550042c00000780014000d90094a1031103175510241d08180915600c009004490706c40e1502140a00e003554146a00d0010300030603a4913031a05030340e010b41c080c401d0300d5100300c1050342c1180d05c0d01103940015582d62a005000d00c6c0529594007280000c0e070100411035011841030341c00001f4903282c280400c005007103541d4941c0f87d001c006d04860241c2d0001c00c044c0b1042c04250070281c0c40d80c45480c1510042091810502e445034070500021643d40300741004148a4040000c0b1a07110300044200c3c42d051a040c8800701445213119442076403001086840b9102042ea0782c456035004070f66566001804840010002d030650740b000f0034102d05a00d24451 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 929372796 1250 929371546 929371577
    0x2090609010e120604084f12030e09060d0f030f020f061501111902010e13091a070c03080a0905160609090609050403080f04080c0a0804050a210b060109170309040c 72
    0x1081c07035801f1000c0121540502e8803e161400200540c000080c11141c60380700c0003032640000c0d03500691481a0b4002150740d80390810300a505003001d000401e0542e01c03100e045d020130700c1080304640e207814030b1064030314003151548028940102514110407256505041002568010308042c801250701000781842e14203408841c4401b204072080030341401a03100c0d1400165454144048450000100401020590b810440314062a080340c80b4012416400401c0d096070040c00100702d170690542d20304841e65281e0300000094062500111a94402c40c090546440305055010000d44026910800c03140e14201c50f071000d407000c69102118a030324000601c40400d6001d510a036101c9210100c5030115101e901d0046101c0c410a810700c2c0042c025110703090100608180107200310303901142c610341c1e400d40360510021420040c1080300c070030001004030440010242400325901c50014104451190341e40d52010000c0c5101d02480c002035040000e9407011071500d48140c4807480c14605d441c1e822404404c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 929374046 1250 929372796 929372887
    0x6010e0712090602040909030810051f0c05010e1e100506090406090c050603010b12010f0e0403260a0e0d08160e061b0109021302090609010e12060408 66
    0x906140c8a03500d9065030b10501c5840c2d0101c0e001000c40c03107020011707114203040040004000340ca40e0441034200310800610303894641038002c810500b08800c01051401c40e103007a00d811010f8041103815540345c00030640300c03142c01e00051a5002500c5492110700c42e04a071410b042403240360210345c149181c1010300c6040d443d03901e00039a000303900250000c0d1400d0b6904141c0d41c0c080842d441161b00031070001c00410703107810b15005005140c288801c450410303629100700d10018402406580301040070500001c0200b44103061a174070040650550240c600d85100480300000422036001054a407203d0080500c000c0412510492601c2441e00e41502e060059200c501c200304500c0c1ca01c04c1111542001da1140d64a03c102c0c2c1c60f885900d80042d510403903500609000e04000d0340141d04c1044440419031065090380203c542c04c11000b081580f41c0040000196245a89a02c0302600006450608c007002803007002103e01440c001c07004140c481c8503000648924806482030b54002c4180f0b00d46900002e07040c0d5 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 929375296 1250 929374046 929374067
    0x1140309071202030f060a0614040b1e0612090c01110109031e110106030f2901050d0609050a0b010311121513050a06020409060b030402030607080a2c06010e07 70
    0xb2001e400c49003201c1c0006881c0c041380b0051460240194005d20410007503642c020000c6507400072030140b801030804104412180009102600309500140c000600700c6c3e940e02c9002c00010003480c2034100800d58281500031032049601108541c810b00c1281515038115401195000c00c54000b407006241070754006068142e2081d0518640c810407448c6210240503040d00c0c1c60300f10644000700800e65032414412103041c00d5000c142c075000c04604900e0a51070012500800c070301c030000da500e891039181109104c680c6800c8081500c0c0550b40e4009400054820311081001070301400103080c80f5411070802c0d044650a5110207407191440c030300c0e0203030180d034040351400041046490480e0290342c0c00c039014142500d0401d0040c25401801c44034800c02a00c0e90140c030984032000e00c01c00c4401d40b9400e500300603200c19280a54164080000034074068403d107840c43d8004800c84012a0701001d0050f182c610000f00c2e5a040e03030180d001d5001003e258000c000042c014001007451070554280104040c0000448 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 929376546 1250 929375296 929375309
    0x3220f0609020f03010c0203071a0129040b03040303140601020c031e150c041a03070c0b07030b09090706020c03062a071203060501030f0903080703020a030b0d060204050114030907 79
    0x880c0c40407019540d644095240c2000098020700940065040c02034803540204400c44411600002d4100c054403c4230056058079101019003945080241001604070b00180702928107400400002c41c2d404214405180514070940300813a40c19801a01d136131055600424140c115807101d0b650141507a40029000740041d03016120032809180030000c0d0707040c100344813a80d000752300c400810700c01c0b02c0907100010400c46d11441810100e10740c40d640d1025227448192141c0c0000361851506502040d55061540e400c803170b69060001d03d040f03011011a0307200d00d080303800c40100c2c1c01880302001915010301829400d5902180079080038940651180589131006a17000e0544015803003100c00c820828046500c4150482c103960340c3c904007404003d029006500070340380007a0500b0080019465540201003285c0c2e895210b1900f1070346d5a400880003034002c401408201a01d5980e0190141c640c140c021507103600940015a03500d041c18005000340f07540400014241c0d40030400c02414100c04181282902c44 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 929377796 1250 929376546 929376551
    0x6091211011a1c060921020607020d02060a02210910060f0b160c08160f1212050a050403150f05010611030322050f0a030908070b030f040201020a051203220f06 70
    0x580b424141c1c005c0010100003800c54584241141a031460302c024520401110750803180c03140c1e21030808989914000c40b032a805a80008086184200702da00502000d0380419607a11740c404200429a00d82d0304182c40c02003180d0000040c2103030002c403a0003a400035058416904421624040e0031080e58410380d00c400c2084404400401c04010403810440700800d0004111248007034200d001d036400201600c281c0520b001c1c0244001035044444480316941c40d00140702c06503041d490034054402d540000e80d03450400508000110005401c101c00c89000500d118000072499610300b506000c440e4180c2007107062008100c3c00a0b500f41c400000c40303510440c01420141042c8110322502200e007600342c0300070100e0040f45d1110f460504002003000c0424045c0d51103007003142c1d071580350b05d8442903540105104440c003040041c0e032841500041300d0300a44180304842c84c600094441c1810941d10788012850b5140000901c0032600194080c1c03041c251041e0041e01401e0b21360b90b54841450b42c0580c0007448141c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 929379046 1250 929377796 929377849
    0xf02130b0d0905070f080c09190903020c0a0602070e060109081230091c09051212130e0106030605090a0b241e0301120b0406091211011a 60
    0x44098100800b41c03a806411120342c1e80c3c40e15400030401945000e0070f500d91141c141100d2803844c0c5005403601400905500110004c1c03086c0b0300d20042d24030200e0a60035407280c0700c207410594070b400c0c0c015001401242c2c080c0c40320034108000404c0c1c003140908524100124540e081c001c4110229440f0760985282100079a51000340030b2800d42c044100c46940c0c2125002001c5204012140402c103115404210980c2c080384d45103003071518440001d030b10401c00244150014851400c00e50058040310214604840c2d00c08080070302041c00b41d000101c9921640743c1a242001803110702900d80303003d010700e400e0500c09503042401080c0062801058550381e96150103020303030152222000000341424040c0480400c0f40c940c003502d0304550000c181074908101511803c000c9402d000c042d0382c103030b031034100d091848440c003901c0e501000f0708090402e44006549510450025950180001c41207502c2c0e1990a1508451146203007102c0303d81112811806100c2c0c000300040c0e480f000150031600340d05440b4034605 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 929380296 1250 929379046 929379067
    0x81e1b10090305041e1a0d0c30090602030907030320060703110c0d020601181505010503180712030f020a030e060a0e0d06050f011205060411060702030a0b06040f02130b 74
    0x1303070a5079010000c1046e100740d180c068003484c1c0008081804c1d4041003407000c00d440c60320403242e5650100126502c0d0b4140306000c1412030100d0340d8102210350118011a8138216502c4002c226031007510540402da001c0d01c01041016001801802c4850320400c6081c11041030050180c0c60b01402040303a010180d0340c01081070440d2452042d91580b402c40000c803043c04483e0140699100001c0c002c1e00c210081100d050481e091081c052404816401e5400100d440c2c40e180041d200f541001e070850005080c0180e540d0700c03004081007031a0040052071004031888906003405402002c0015040b021904000089408650041c19190f4032181c159445569064082c008458031012900c1c116400455540070005001160704418050705184c00e40819690340c545124015400c0c840006043c1d412500010f808034200c46000081d1540c0a0240752520309280d00203400c000032904216407946406092003528140342c4a030310205558801c045240103211800300402180034070541d521903800084401a9 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 929381546 1250 929380296 929380349
    0x50f24010915080a0608010209010e060d140a09060b33090301060603061503020a140d02070227090c01020c060304020d0b090307030e100903081e1b1009030504 70
    0x8020603000e5511007101c4a80080040100343c4111340e071241000c2c1302250216040c800c130780194105840d0030000c006803009010080c0c00c00d0301864142581d84100300c00007841544168428144103400062842d000d141407011100c00348503503801007500c4ca90040450001c44640c0c00c510304c0441654801d0074040c01002c04511811641d1601542001030004403560550408dc054031640c501c404400d10030700c00708a0480c040c01001500103071101039180581f50511005240c04071511101514102498010408403603a400d840034020710300441d9603d01f12036040150781c200c44144040c1c0150708410700001e6546000b40f890510400380000131a0841d9a142401040c0c1c0342d00402aa0481c940560b95544a13040070800b500802c40c1140180042d241c40745c03000c40c482c0b036203898809101703040da01c0380c02c4550081d800d441115840c4030a046050140c210203442207603490481200c114980e0400641051014000d20141078180780032040040c0c0c02c40d0540e01038500001840100403100c0d9040b030344 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 929382796 1250 929381546 929381549
    0x31b0f0604030e1e04110703031a06040e0a1107030e032406010f0e030a030c051501060206011802120c1c15050922050303160e150d0b0901090f050f240109 68
    0x5d02c9860510502c04040c16607010302445402501c04000052080380300484001101d440301d40d0181c1c042109100d0040340c103a140307803c4003c43e140082c0540154202682c03c1d0b10080d01600401d1640b46e200c501440d0400061020309206d02e080c00c040c4500b509034201904000e048a8148100d40341204a4244100c02c569400d140c01002c55040c2406400c0c0034002245488044c4c50070b00810494080084494400c58101c4520303900801c0b842c5e103402c2d4a5a200b0402c0c03607003100312030b80800c10150142d0246d0340350b501030302d5181556a5292201a00074003c0f4607041c0000901604000080180119803d10741003143e4060340c84107215550120040d4101c01110302d1101c2a20400862106100001020318030030041c0d0347c02011310344007842065400424440e24141e100d801e4035100e5000c1c0d0b007050041c0201040103000420624a20720010350f002d02c090300aa4001030b55440c039134055850602400e504030b06a01c101807800e041c039040411420300f880c600e202c0048038505108201e039201c2c00c030420 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 929384046 1250 929382796 929382799
    0x2e02030115090b0c07061d1008060a051509040b0127031104180312110c1b06030c030106081902040608101410140408031b0f0604030e1e 60
    0x659940e101c822088040000000c8500010b45038440072030082603001c1101e001c1221100140910342c64150103c0711a9141d10b04201040302c6c10a0261090725068102103039031100d9100c509a500c0c0c0310081c410392641a07402680306a2040c0850381d01411240f08031110b440f426503020031802410300050780c03401032045469002d90321001c16150040c03e84040302c4140c84c491003503680010b8941041006688544018003c0c4020910031040001d009404031001e0142c03202001c41c81d41114000c8048640062120280a070868103a5443c0d21840c8015a400d08108540c401e0550a040718002c0590005002e10000d105010010401c051101d11034442e80c2c01034800d055503100e807580801451180c1c15901450340e45c14030100030403803038603155481000c0714028100224007450004c0c01c81e88554600ca4446044c48200b1003c1001c02051000b045c039081a941d90600031014050900e04d044200300310030f020b40d0040e00510000a600201c6410402c1c0d084078103442c65440b08210921b81c105184455 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 929385296 1250 929384046 929384051
    0x1208091504030b0f0a02190e0f0316050306011706010e0a0b0a2601060605090d0c05030d0804021806010e0409050c0d0c050a09180803131b0f090b01022e 67
    0x204459520080d1203044580d01d14a204c0e2248440e0000307034002c20410000d11580380b421401c10b240300d11300c1603010400003425141d40840849c0464102104400030000c000c2c20b00c503041c800c0c1d0808102481c010320455628410312040c526842d40c031080103005411460341c5541c082018030445030495054070310000d082c4d164580c0d42e00306001890382411408110742f00c82e20305041c1c0851040c800c031b00c11100b042d10780c140f44c080600c080082c41d2198072012519072450003004030381d9880c01c101507100c66516403241c0040d414076004104101452002d00c00340302619404106069034043d6a48480d00350550300030515400324906541403e100c082003641040066144400717011142030100d0441341e081ea0b640c2d001a0b02c4085030000d803120441c81d8650079423625004030015408070000e41e480f0381000c0c040b02003030705907595a641000c800403410b950741010b10707000d11010071066103010080100c40001c002010009002039100d4210b081c0904110395942d03001c2d500318003100b107800358410420104 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 929386546 1250 929385296 929385299
    0x717040902040803030106030605010e18070c0503120702060f07140a050706022701020106030c03020f1c0803090d0926071802040f080a200a151709071208091504 71
    0x4603940c0d0000d01c01c087c0001e003002000501d55008109800e529140034104505040c03a1a4860800310400380205080020f211017050118000b4000f4040903807801c8001584c03801c0c030710b0000b40360600141803044a83c400009200f1025000450a000151819001501e07034054040075140d502a8640c090204d034000102c1e0000c0136a664510780c000621801303502c00702442e03007004a00306c504a0000414a80d800701013030016103091050324900034001041e68112511448501c5016003996004541c4008040b00344441181e017032100032030700022441d16510301c07403500b0b89585a4121540c0c2d103034a800c1da8608160341d1310100780041c001070081c809445171141e00400c00d03c0b00a600c2442080b84824440c80041a00f00000c6030000840740c01030401c104804202000c0c041c883c07148140158030165000c030010710344486d000404201c0900c1d8503040b4880000e03801d1079980010040c003a00c0310341c000d82005e110800c4c1d103d00b5a54070a800044150303c900680c0b010410b003800b459800607021001140 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 929387796 1250 929386546 929386559
    0x1b0804080f18090901112203020307081005061c021e09070f1101020f1b03040806010609090c2c0315092a010905040903020a0b19110906071704090204 66
    0x7100380c11400d41e030883c9282d9501001c28201d85040c071050101803820000d1950300c0601c081c03c2c05c0410b00c00741e0741d61034103642d99001030318003020744c4c2c4403182c290070454000304841c49900c0b54581c05801503a091040750802c1a1000090300c00c480c00a110703111880e1030141036803404a00001981020b030007540e540c10204000b604003080d0074007440c001414042100c03226030042c026200e0540161110a080c443c0188146000e00c2d45141c80346124030040c031001401e0082003100c0c6000300f04171740310340c08101e06164006043d140380c0603100042c44240b00d0028507040034441c60404a1002146000000e210f8070002401e1040000c1c1c4a1f5106544105100c0088400301da0140003070603564516001d150402e01d90503c0000402c01c80340451441007042101d820f00781c000951140c424410b503100030110360b0301d0321780c0c0312400c0d01c824840c2c5042038032025140b0b581d4402c0a13120405824941c1c2005029000100d240c85400b4004141c3d03d8034501c0e40200c6190102610041c114500c810354981c1e442e0700 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 929389046 1250 929387796 929387827
    0x20f0a06020a1215080d171501120204180c0f0e12010f060314061b090108040c0b190f030911190b0318070b09031c020f0d020309131b0804080f 63
    0xf860605000c0e6000400e510b83c0130b80701e140c0c8000c180541c0207030196032303003140070b0500741800340c9550611000c248207000302c0f07009200800c0544080a408402c90300b02191410490311452983e0041c058004902500c454100c1d101e01501c05089039040c5000c4800441b26001d0f0445680700c00c8601c0c100b010100400002400380c80c0c004085c0030446980766074800d0580002d0a810050b00d02c0e10408008000803540301d500c1240d0310500400751120803d54640503186140c0c0f0920b82c21208410803e4000c2c445276110b900f99907000603d103414001409a9112051274148041e01c9a114403ca08000c050001407004500028003005c0116a200d1400c516004200190440a41000e014404001c144405100c0c01ea507440180600105a9841b4203c41c1600f10001102d08105510403110080140c9504100b113064982d05039000d9501c80c0100380a010008076441c1d480d285803810007111010794110b610841c414900c0501e01107986407217078140403c1e50702c00d0300f18407098040005514020081100c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 929390296 1250 929389046 929389049
    0x91e15120b24060414180705130b09011209051c1709030a0e04020a090513060303030b030303072c041803020f0606060a180b07030e01020d020f0a06020a1215 69
    0xc140ca180142c402d0b04181154441c4684240c1d8001010302c0306101040c081410748450045c0076003202c2c0c0502e20094034080040080b13891600003207000452400360450020104001c00700301101e40d0504203075400180c01c1992420305148815500d04400d4140901002080c042401e0102030581c1c0d2401c4450080c81000c0c0c80c401c016109049002013035680100104a5000d00750554441310198a100d0410000c0e60142c0441d10070402c04d05e201003440d81d69080a628007495070344000030028590704d40502580c12108006120790020300400c8141ca4000f8407447c2081c0444140490440e030249550800e101030b54411030300b080c5040f64020100d486c152661204074026000c603040c08078401c00013542d03030804880c01c03a0006014440218400d01892141c403003542d210010442c000d4940c107070f01691303410041098001900340c07003644005507014445030200c1f40151020782190307408501030b00e9443c031111900502c80d40c1c1c006140d44483d441560748081100070300c40107120803d80101c0001000307009 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 929391546 1250 929390296 929390311
    0x10060e0108070f060804080f0d060b03070306050109150f18080109061b0c0b090106081b1207030b0103030807030207061b0e12060f04112107091e15120b 67
    0x40342c07000703d1029510301c094811030705680d036000c001d603555a650b440c90750410450104030601c1030007043d80d4200c00340250f5003d00481003041c1c0c0c481c5800c1000a00340e076640c3c1c0c00f90b814041c000070144242d0704880c0004100d02500d040c000015114800119014909000841710165018030045050072041d00720000c2e00703004039814000c6040d8150004a00e8100c1c0c01010045100000c2000c0014018880a0b600c5885c80c000020710503694600c07542042c046c080d034442200700d800d100c00d20510740001c40390380803002040100300d8a400c0d5940c0750607000041c003014041c0518140000c0400744a9011500110360204081c0440795a280d812030346254014551400314070300400c14412810322210300102d16000200824480d100c035030700030148000c00740c802e560307007010580103040d191a052a100100c80341401039a64118264500500300040c81d001503124a050608241c16550000000c54660340d04d2400010034030440d517158004c902056000d0342d03410f01d034548001c0a00480f42d54062007144e0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 929392796 1250 929391546 929391553
    0xb09010614240c101401090605130216080c010e100203070512041b180501091a0906030a0203062e030f080f160b0a0c09052110060e0108 60
    0x44595035559840326008180c0e4201d50040580d6160440c0c801e0200d414240904079207140503c0c03820040d0a010800040380c0d9000d84814107042c2030394207241c4030b1740104032521042000604010000340580100704031140d180750007083c5c0081c0c44640000c40c000e0340350301c000b5142e6070b0030002214034082c00d0803091500aa001d00c0075451082d10050084034070442a543e0ba05180880080e0301c04c1c2c40d07601c050016203019403000d40e032011480d004260359000d003100c2e07803101010070b4581c5d18103015901c0581018101d0f906108029489410030904900240c3c81150382000b01c0e80c5010100707180085100b000ba60502c030f07403400d014288004030703582c4a100703480c8660822001103240031300c0300c04810f505c002070420146001807004203120402a08403050080d243c00c1c6400c407071008035000210865400da030071000e44c1e000d002d82c428591042e000ca414071418070400316450540001c05c2900014002c4000384025a61814070800500c1107c030b994180303035402c10440742c40d03e40c0c08a4412003402989154072 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 929394046 1250 929392796 929392799
    0x1503030e030c0d110d060204080706030b090703090201120207020402160c05010f1106070e12030a0302040e1522020f0403050f06010e04150216020d0b06012705090915040b090106 78
    0x100f0045228a581d00f08100c40c0390300844070140b150190840c0801c1c1e418583c01d04c00458440b0040c00b1010041045580204003030044e54200908104041d0048042c50b1030320007000c0060342c00c0490100c006610810060f1107603c1800420042d10406100415100e241c1c04010100b004905041068400a0303032a04d90705da201d200c043d50384049540303280d0001d40c4044000741d403051107641500d01002c4c001c1c1c00d40000c0020369000500e160880c00e81d80c404280c011070244420040c0e40160755020401e03044c200c000140090104a88170490700c0d500c00547c050100f00c904109946d01101c03407451094401569485d541d0034150b4854021285030b074441e010f000000038441c0c0100e2106801107401c013182c0b8240060030702000d0000e51040034444040352003550b0700380150340e8581a05410b5805141c0c04419850040c00052000001144041e001402c400c00c2c520422514040c25041d160300396808800ba80b1110251803920031070070b000c039070f019001408000c1048100e0010701c1c01440c10360002e12585 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 929395296 1250 929394046 929394049
    0x9041b0b0408150a14010b030118020405010507030809010b0d1110030c0914013606090f140d050a140c090f040f15110901020705060301060c0f061503030e030c 70
    0x144642d10644440340d100d000c141030703585442e11000b500001c64404c0003a00d04003580d610003140b1800d90100307052000220040045010710740c0c0304298441504021460b280c100b100103007050084100c0034081100000c0003803c0400258002c10794428000c242c981e41807041d00d0007000f113a401c16030050055038020159440140207010b40300907502661901020541031014000742042a00c0748141000542c1c6114030100d4044003d030461601620254410382c14644003064074090360358000020409090820040c20031003483e13010981d035a400081e00000000d0002035803420301c40e0809030050040351381d05003c1281c03007000071000c541040c00340d910801d4041c0c20060030350022621942c04012032000100003c050f07882000b051441824a85090f894451031442140c4815100c480d03000c80c002800303491581c0400a04005210403070b2200d2456052a50040c0a1a1490002060340344d032800c2d400104659034000c90008859218180d60081d070300e080040041550605140c0a4007d403020300006 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 929396546 1250 929395296 929395319
    0x1b08101112060904111005090906010f0815060c010c02010b03060a060503030301120206120403180905100b130e0901051009140c09030708071502010c02061308090d0209041b 76
    0x181140c091a401d81d50b40c0700c0302030102801c0000c0040761180ca5a40506074941d07a11150300013120829906c20751101107920900c12030803800303040e0605014000308902c100d07a82c880390040e4055403c1d020700034821300b080e0202d00c0600419004d00b0711035003040305c1d041c4025415401100490f40c2101100c65640b90310411200b106c0d26030248e540c058108000500104d11041c0c8904401840504107601d0401d800721107040002043d2001c0700000c010081d510403a0324104c001c000070b84020501044141000c01100300700403d40e108005442d20003046c184401c2084481100c002c1240841d0018540f500180c003500800e02150408100c058038140401d040d14580705907801c1054100740c005c456101c2c003030410309035048810180c3e490b10480300c0c04141010240040001080711300d0414807400c400500103420743d01185607007000c660013201082011000c03419504030094101c0d522564031503c47c400720f0902403040383d0207900694828184001c0141c840e940e00301c8042c16081501f0200c0d188c100050a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 929397796 1250 929396546 929396557
    0xc0f010518070902032d0105040506010f09090e0a02030706050a02011b020307150b030a1505070e0306130609060606120e1903080a2a030b010207150c1b081011 70
    0x702980406802e224888035a4021904148814070380102201080d00054101000781034604020181c2e8004105174103050003050b4004a090810211080d02240e00030049031240c0300b42808a40c43c1d003224803104100388800084190081c05403416940c4420300070302954843da1680005610300841942c01c03451304015001c03820f2680c0c0c0503514010254850f2084251000031040e0708030343d901604885540c0c1040700c0884148140b05000711031880200308011528003c0580c0c2c1400742c2d4001c02e03805950046441c5600c800d0001150240070740d203040820041464880043c202032401e1408141e49821101d680d0103146c540c2c2c0207210021203004041d032100450709500400c160700d0752000d40001d00802c080e41d0322681c101e42c00a146081c2503030f5801d1220000380014103022407910032201c0141d01d40a00f00c1e208600b8002040120303d002108000c40500102d0308040002c2e801c3c5860800025403501384810040c2100c1d081c02c103407110811a140e1050012a00307290b8507190201c1012204803060301d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 929399046 1250 929397796 929397841
    0x1b06060f0a0e0a060506040f030213090c12060e0102161e080d0f020c060a0603260d0c11010e030a030c0801080a03030c09030822060203030f190603080c0f0105 70
    0x241c0985040c1c1040c0c2c2800d000362034502090f07103448001c14140c980901401c001c24910034440c074018030b58014031001d10042c8e1201290641000c0300100800d5940d00ca01d822030b6141100740369140a141882401007101d02c1890f0082d500001d5075003800706c0c1198003649c125019270071a40c030130100b510b80d100740c0c1c1d003c1070300062901805020100519945912a5074110340e1004013615040e501e4244030f0429404840c80c003030160b41c1d5039050061181c1007180b000f034120105072a900c4104581c0c007290450041d4542060541d8603014030b95846407140d5506400c043d035070740c020b12140c1003596405031a90001520000024601010b03088002e00c00c510a9040782d0169003d810100c081d034074214060300036413030200d06000380f40c0c400000040c2134000610380c0146422020b040c0440343e0740700b04446d658544c02001154814428030001c0e500c4090b14a4200368203508e0111401d801c032400d180646042d601c003034031790318010544011040000c210782d100005048001c00c1250340304000026424100942d0b503 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 929400296 1250 929399046 929399059
    0x140f07030818061f17030a1103071518140109060c0c171b06010807150914130e030a02030309070f030b0a1512080a0f020d05090f040906021b06060f 65
    0x80c01a003a2024011032440044d4820070031035450b03081203c1440e4521401680c55440018560800e80e03004019020040d029009589014415110034096000c0010f5850b01e003030780ea18400315000c20049004408942c03200703041301e0220190440030700800318038609031441828008240c44042c81160900016980994100152040c2c141e18040580290640440c052100b010403400c03201c0c200101da000b0b00102c03004010303890400c070700390340b142e00410320b44024044108014044030a800030044141c00c4190791000c81c000c59030882001408000010103024000002c0700d10066a021004501c90f0101d0070071201c110b0341e90900016024603600c8050440c140c0903001c80c041d4401900000c00703201d80861101c00254031005444218030301203000312104030b400240441401d402c5030b508a0102e21a001410480b0a1420054200d01c20307104554498805c189842c0615a21170340082e40d07039a04483c0840d25035601e0800501d02d400c0030005425284103050018005180036510000900c0010303051 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 929401546 1250 929400296 929400301
    0xb03130b060d0c12031101060f09020c0132011e0b07110918010507030b01020c0409080f160212071d04020d0f2a050d0206030403140f0703081806 64
    0x600603080409080507034001c16080c0c2000124401d600050007a00c02d5028001169015103409402d901e04150740c81d100e40d051100401c8100b44901c0b10b03800710389072050b000d41d403801c03521078041c0117180b01001c0d6a03000700102c08030a000c0c903c2c46075800c682c031030710150901d60341d80751201c05141041c860711144840015040a005c25810318024024461040c951310220304805000280c2402003101c5c03080003900d0b010075030341c0350354800d010b0550060440d0800300580b03280f80c80000e4880116030380b1280103545031650b00c003c00440c00101d8040071140c1910136143c0b042800700c6031104019000507403040b44010640021900007158080490300d1000340440307a0f81c0c2941e103100d044000244140c0e40468403108040101d4404841e41d40710078840e40d0542d05041d01c000ca949900307203194020003280d001c1710b9424040ca44070f20820600b000e804891058603a501d518049a00b840c1000c2c15074170041d0b0100b0400505d82003c4017a080b40381c42903c07035155540d110128205000340d040c48440180c0e008501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 929402796 1250 929401546 929401553
    0x10b100306030203030405210d0201140609060307032909060109060503030a08060409171909090e1e0316050c101b06090309080f0601090b0910090e010603120c05070b0313 75
    0xa8440580d10000c0c88c2078040c44449005038101502000360f4800f50b51a41d03031640b241d0500d080802d90004040398603ca540c100380c8042a83c5021a000080c0501e441c4100c0c030101035505286041c280100d400300c2000c0b8170f07060000544651003846030301e80031400c0010219462030080705441c41400540c0d2580d085513200820400030300640b403015209451210442c41e048410351009081e0b0b0f094002d210800450310100050982c05d081d484500da10f0f00d4640508050039002c0740f6070500030840b410159001c654102031a00754400e811721071101007203040049003040780108141c808400c044a02002800960704280e480c2a00811a1410010107071800c2d4005405030340920080f40c0245010f181c5291518050b602d429261550400c5640c0f01000400c050000b034000e5a2000c50280c8040c3c0d2203040c1140c001000003024080c500070b050322074805002c81c8100b54808401503800c20815001665804c00c040e00c03803a421602561280034184012803017841e15011207015258080140d03025000688 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 929404046 1250 929402796 929402809
    0x160f030312050411041b09080f0c1912030807120b06090111010f060b0711030c0f01080a0908030c0703080708070f050a02030403020904050708060f041a27010b100306030203030405 79
    0x83c0112142e4880c1c1d1400e000c1da0320b69102c0c03103c2c2101c8001c00e01d01d10030344280300604031207280d83c132075580c0e544841c0b440381580c20040307050060040c013601c1107840c3e43c240f203030210204d40c580d400402d98080080141d03818140e00c401d00768001e5074251181010181544802810349601d28074080e0800c40811492150754031541c10030bc1c224450034000104a901001e0040564140d80d000e07141810011036140140203501450340c0c400c2008400414032083ea80c00816101c10321118020305001052001405003580c542042e079030980d10048243ea80d2501502030a0540c000c014140d0014a4250002d00b1060256892078000c01c681d44440c0302c28054441c00b19010360151a40d4000c5000c00c1c4070000042e1504108580180d21940c00340450320b05001007203141960003800400030628100c03c4c030011500750b0010301d50512048050070b0540d5200c102000c0011a007104141a4164410114040301011b42c000d24071034070211141c8220806400303080f0180e0b00e8602004c4c0d85604100420081d030301e1b103074 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 929405296 1250 929404046 929404051
    0x90303170709052106070f031103060a060c0807080a0c061406090103080307110a230a08030609070c05061509151818120c0705060c060f150a0602160f03031205 70
    0x144180d154510704c084540d040400c2600c490010401540142d502c3d0350b007500070103e0403190300403020300b145441c000050b00004940304100c203102e10340a18030280311400c0e0844041c0da8104d031086607901040740000f080c660902d00103031a4680b0381002c0080c1040f51a513494080c550040000300b06900f15100e00803160700140200703050061181c00140046018045440002e004412108808001b11441c0350302180028003d41030750441ca03000b4000401030416607401c920140d8240090356594101030712070748056540640248a41003c01c014007540d803842503c0900c0948100b06c00da229219030312016004000c074280c0c01300c00084121611640f0201150f0f003d6003800d000c07107040940c210020300342605084548000d039000a51031002c140204140790041006981c46032a0080460216481d1800030b4084254001c1d203c000c60000e05400b50301c980c2c40e01c401005040340555900019580b05480e0b5404180790169810004a50190f40204001c50b90540c0381c1d40d004a016000200080100 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 929406546 1250 929405296 929405329
    0x5060c032a07060513060203031311131409160614030604090f03020604030f022e06050604141c1e1e080912010e121b010c09030317070905 61
    0x7016040000c40c0341c00c1003054018112602c2d416030352014460000d15481c0f1940000044d50710030014420700252200101d03903880c0e0028103100160b1f41110006a0040084050b40035190921000c820342c29510900640501d1484007101c03107142c0c11202e44403480c401807181c00080b1300031030759030b25032041d104005690001000303000080e6006a40c0d40c0001304001e848065005170701807000c200805401003e800006401400200001c030307100b000e84000d600e1664101c0f1148122400c41c2142c0d410716800c40c1c409858018085611203896108981c0400c642d1040544100303036048400c0d401000d8041403403800d03500720700b501c40f9010780000c41403170034040078400312280c00d961458650700c004465620b001c0d4500c98015503513a181240100080301c00b07280c540801d180d142c001106800000041c242c101c0003005243d4a40752410b0303000044502100c55104c50b40e42d42010041002c29074490543c5040d44c2c825241d090103100c9100c2a0240c1100449200c400324502000c28403591a0000140c40c01084 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 929407796 1250 929406546 929406607
    0xa0303020c06180901030b100806041e0303021b01150603110d110d05130b0601020312041106040512210f09090a09060c0207080d110c040b0a08070303051305060c03 72
    0x1120f0000c0745200c44268019200c48022206205c0c085034060500c00c01050b00070001c2501d41421b48810601030070031400348440061a014410402d03000c0c1d01903d41045001029145926162840e103019004070001c0b11060b940180f000f0515600a22802402c405121070f42414440c0402d11200100803801c80036200d80410b020038040c82030280166480740f5650810720002075604e2134094900c1e680607101c179065401c00d0011401c000642c1c03542c0703584140c00c81050b58031100100d001c01c49500c16070304a981c01042e0000c10b4034155100145071880c05486078020b440003002102200a50302503103401003043c2004100d800d0075441c00040b03040d08a10b0200d0b00040300c045580c2e0340d00072180d80110301c40c096002644100000d540074010b40307500c441caa04000941c161080c10b070380d032200358080700248a03070740d43c08010380c5c961242c00240015101038002c5800c0c0c01e49a040c050038a4120104800102c61040408070760f50034032780191030003a9685001142460031662944881d000c0300349250740301c01c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 929409046 1250 929407796 929407837
    0x40e0a0623011422200405010c020d140f070816030804060c020604050a140a06081e040c0825080c0603070503060f040507050d0e0a020f1210050c03150a0303020c06 72
    0x85072420804501007070003100140390082200d000541e651000217142e1504800d0204001d166081214403814a50446500c41c001805141c8084840c60206800200b0f01c20300c1300c0c200724081c0000d45002a10244400c44152207540491800649020300004182e84020b20041000c0c03801000c0128070b06c1d1008200d1f42c2040d4a0344042080700406500010f0340103507140c408009410801d00100150029103020115464541700251240514038066103a4005000004050000030004180a04246410f452211014080d140e065201207048804010108403001500b100005240388000d02d000d8402030844d6a01407003a81e45402c0204040e400c8240c0f16400c58840c0d98502c2400c0c81455140c0fa290345410342941580b045502d0071801c08030640c056422440943d030750600403944550b04841024a2410424400b0704204540d01a00f600c0b41c141800d02c40c01c50032a10117035116003001c56552403000000c00800c00034503800c2c0301c00303005a000286222203d040040091030a000c0300c0e281d9800380c4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 929410296 1250 929409046 929409079
    0x11805040504060204140901060806060705030403080c0601060206010e1e0a0b041e150806150d20180403080a0c0c0b09060601081602030307050a030605040e0a06230114 74
    0x101c508540403942107a0004040c4607255045000984403142540e06010300d40c148200900043c0307010300458814600854903c0401030108115405107600400141e150418200c1060b651ba10a014050260060000100c0c0c241512800540b1032258801e4450241103491200c0c100400003400d0004a1a242d1100008030740b182d0186d600c081d03804034481e054964182c0c03414021118000080c4000041c030718010029160001034040e0031154000d8000c101c009884005444020f003404001c013095010f0ba500610303175404803101402c03818191001c2103407100e05d01d40c0c4034112004540003004240d0180114117079240b06d92107001c0f91100d5040441c0403441a1703d0f1003104500440d001c80040e4045c2003002140c3d6400840c0c1900080400c440c020991825000603441c2c0c08010411020480301281003120540b00350007400c001d18020f4403c009a058070648240c482041541c20b5403014102007584a82c5403412040d80c401c005528a808510303420940884800c00300780c3c1c2d003554081010802403591 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 929411546 1250 929410296 929410301
    0x17090a051801090c110a110102210703021002190c050f0109051b0103020a121505040e1b1002120c120307110c010e0d031101060b04060e240901180504 66
    0x745a014029520a615110f041c074166404115502d0402006000c0003226440000354003800ba40e000c002000e4204040d00100c0c500780103800c28040b00c15103e18103071324800c250402094603a0003907090b02c40452511544000340c0c842c42e04d008051101c100b140c500c1491065450044251159003520b103252002c214072429601040825a900e0f0400500852014000121320b03509580c00c0c2029400c250030014090140c1a1a540316100700c0e4944418500c281d41010300c031406080000c008110b16070f481c440050381e5225080359103001103400d07000480c0918000d1542a00540942e0003000c02c05d0f05184c02d50703041e070407119000506101d100c4080242d444c204014501c03410b00d5a5800480d801d450b0344032131420381240b07415410b01801407658000d40d114051000d2103140c0604142c10710940d01102c190040c41143d00600c1c0e44200030402090303840c1d000c8101020408200e0300540c5428071411251010700d101284d21011600c10408441c095000e1402c241441400803c1820b10750343d2000801c05 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 929412796 1250 929411546 929411569
    0x60f020316020904050a2004150506040b1321060506010806100c02010201141302090a021305010311070f150e0606090403080717010e190e07170f03042303060417090a05 74
    0x1d42c47d03165003180400d00b4903104000b04c0d18404009190014038102c04200284078600584e1004000005e8500d03110107001d0710b0b0001480c2050110030550894034018495420800084400d142072901047c103e61023900c090b0700507180100680c0240c6140401512000501341c0102d041d035484a20405030440310801c100e01c9000841120259442c0714810018583d030000c1a20005a05c1802040400d8100704258800d554007804e000412880c1c60003112001d000d0640c0007400d40a03c031204008011342030094001c456003031078083c07243c91440020b168075183c044034815004071a500000700800d108110040d0481500d040c42610300c5040f42c40a03550b01d80c00d0304082c000d2080c0c1d209204c44804003c0c0810b10b502c0d031511081110105100394a9180c0040784240072010700450820389408405101030744a4000c200100c136680c030fa440081c410010502c0520305211018032340307100c20a050100b03030741c1c0c841c0790f20540300146491100145240340c0c0042c410a03400c1480f42c403010645440702d507091b49 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 929414046 1250 929412796 929412833
    0xc060e030a08030f220312200a09320d0809090f09103c020a0806180705030406110d060b0c012f0f0d090804060f020316020904050a 58
    0x440d51800103d10242c40c1c840c01031048080c020740c007000c00807d81c0120300c10039100c030791a0049484004000300404502e40180410030668000035401005500010040221104141480c20100c560f40346403101c0c410b0340b40607450a0103070605d0300c0780518041b020b2a0b88079109106890404100c1e0010a2104000315070020200c20321000748080c00804001c100e500350724504041c0450001100c620251503000d00642c1124200c00910b6214020300d292003a00800d880b420447d1200d9511200074031000003551a18001c8000d02080403901850a074954440c0510342c803410301e151504d03514000245000c04520b0203051061100807c82202c9010b104014a001d07a0741e580c9640320120713140d007101c0800701482809024030940e8101601110f4181491040d41441247c40d20200c000c419000e02c1201030032001d02d0710345925242040100f8016009592566545014001000304140e070340388a030030b0110b6070403203a0040030310041c503151500d1070f0b01602c6041034070300d00d03949030742c1d44280d0b84039018000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 929415296 1250 929414046 929414071
    0x20313120503041509080405010518030102220806071e0c021c06050604060e070f1b1a010b0c0703060c0e0406090506130b2803080f04140d0c060e030a0803 68
    0x90001d4034135046400015080708000141240d6500362680c400d42c0f00d4a41070060104511051012846110f0b22441c03001d030082d55900d000c2d5002d400185200d9906d6054080d0b1144041080c000000d48188100441c2e01c0c0c0408110485070038803443d418000514040201c402c0010b401615517040403006003021950105040c0001c2c500708058510050100b80100e182040421151111762412a0028402d00340701c20941059002203a43c080e0000c040c06241324072034440006c0150341d52489010040d14100c00b0701c103903202e4500780203511803051200041e40c0115010320120f500c07030740890041c3d22a0300b000c100111043c008141078882076403044c840f40c0d0384e65082080504188100d40b86c003e083c848100409840c1c1000190300601400201d4403210400303662902040707038400400052340d086000300c1c0d183e1034520100c24035075105008080701000c00b22071002e06800c1010481c0d407440d0b401440290381c5400e10004403412403a1004465251191a400201081110f0015806058071100030b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 929416546 1250 929415296 929415301
    0xc030512030a050601031a01080c0c010501030c0303140316051605011506030c03020a0206040f0602160f020103060e0112020108250210060501020313031202070302090a0b0102060108120d020313120503 88
    0x39042250f1005101c681410700782081c003060100e40c4903400101141c00d0070321800316240d01f0f280784280d00800300c10394595840e100001c01484420804201182d200c0d40d580c0c0e00b200c01c5030301980300f20b010546000d2000740f84200445003642c015006024041c04400e900381410030b19031100c40c02d54107807040d05107200041090500900340e00d0f0149100c0039600d401c00f50f1038940c031403000035030702d650052001d00745802182000003040322680454922488103100402d000086007408019801c6083d001c83c082441c008000815130744040455040303c000c125490710101480c0c0054032098001040c1d241780b00040c84071400d003400c240c00119918140360340241030140e688500c10080350951b41025041d03500610040c081d090381008800143ea0f84a070346e41440484010080e45041c3d91a000254050820b1041180740300301a400342c2c035820000d9086030a541d036548129a10740c60221601a06481e04004580d16028560019070b048800c0f580404206041503c072680010405046d0f0310004100109 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 929417796 1250 929416546 929416561
    0x90d061409030c0d050c0a080f0a09050d020a0b131a040e0c030f04030c0305040e010303080910050402151608040905040b09010606020703170d0609020901021002070206160c03051203 80
    0x200541d108680900940c41c1c62440500141d42e1103400b41841d00300000040c41a00d81142030100081c00769110640e16113a001010b1400740036040598020300090308520001128981030a484181e950050030902c417107801c103160001c2c158445201c41e450062000c80028000d4a01d980c851b9402054640c0c60f61154180343d00126001c002030052445480d09000b0b011400c0645c004840c0c119a1605007140300b00098903054503940610343c0304455410718030700000709241c0c00040040c41014a0010b564a071101d4138000012244103441c045d4000300780365180080d10103000010141c801e03074401302114803c5996141e0f081c5034480d800030194140c45409000c1000b50b10401d143d001403400d0000d11019050000095452985200180003403900e411000d900320200d400b101c400e50904001445003c1e03ea4420b030010f5402200c00a006100c3e5003501840c07055548281c82000d42c1c01049246030800400344900d0f8800100d0b01510300b040071820000c0056810048080311072100890a42c50341f40000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 929419046 1250 929417796 929417831
    0xf0d2a0f0b090f3c0a080d09021c050705091f03060e07150f031109030303040c0305250302101412010303350924060f150f0f090d06 58
    0x4036042d0100500c040700180d020202044d03a03000c8904202140b0100200880351450000b00301800703032020300005401c108041150300852201c074020b80340188001d140190400102207002c1c0d015100340c01100c0c0500c05840e02d86043c0ba005585002c09030381d1201c9031815040b18000960045401e03a80d54010780c2c5407940207005903070003480000c243c124a01a9110003a05c3c04904000385410159242c0104851181b40002e170303007585d9409000c6030b03103030310f000c0c07500b00c0020300140016500391185003007040304090700b5611496107003003d40501040c14035590a020f0a900c0140a8070140080c1c240030010810054003d0700c4a85070004100016500d1400c001d0311083c0200c610901d400750b015280903011040450500d00a0f40d02c0304403c3d641d50b00e0b070a4142c01c0c1280c0511101110006104003030250940b4405903024600c1201c090b41c450f040c00301003000540480d2055090280d043c0501040c0d50803800150081e00c14020580e0b02d08004a000514003902e01002141c000b507488003003004151545 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 929420296 1250 929419046 929419063
    0x204090b1302130608091504050d03060b091c02060f031f050a03030c03180e0106090603050f15130902060310141206060f0d0b07020f0d2a0f0b090f 65
    0x403804501d0140d03185590300d01c0f59000d0184074240041000030a040c3c000030000501111503100e118901420035213003c58031518000d0352000001c1c1024800f0400d070740a003084885503c001890a0740080a000514100340e404a505a038820021b101c1000d004d1b031280e004501c5490300c1d408440c01220701c440756a21010f000d4201ca40a64104402400000e0304040d481c1e145580609120750f05240001c0c1310704415440703800c0784004804d070500000303900342c01c00c4914066035116181070109548484103106110740460b401c94400714070000c01d09030350501250501004c011060f012400b803840da0088dca0b50f5000782c82402100d402c1039010080c00c8074011009400d00b000b1203014403102c03501f056041e42c40401521640c0b0941482e0b24100842d070310b8580341c0044d154060502000c1c0c4c41c01110203034840e400d82032000c0d980d010341c031200c080281c842d003414000c8100e1041e10b4001c0b21001030354003200c80740c2c401d012110f03003155441c840e0200d0091050907105522180040806850420484d814804003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 929421546 1250 929420296 929420329
    0x1020d080405030f16020a08010203090c120a06150b0301120c05042a0c0609050322030510021c1b1803050730110108010b0301061d0f040204090b 64
    0x540502002502c080101c8140124900d0129101c0a10745600c4108041c00031009500c078204c0000000c4440c81074000e1032050604c1d00654520001600c2800a0b54003a00280c041980105120a000507034950100e0445101542540156500c50391040101d510a0304004601c009500c00b40c0200309412000030043c000540b814003541101c0c51480211640c07413401e500c0420410b40400030001e120f08841e101c82c0307070841001d1003000340c5810041d03180d500c0f80e80d9514110004040a05e9443e03040e250040c120b82d0321400924100c0c400c00d07504e0009411411460b9600541c42500304c1c0c4141c228051180081c02c1031a40e009155031000e40689000d103c100c10b450f8100d42c045e0304101040d400f10f01107007114110452074451003400112202610b2022061003200014220751000b48001030318030b00510341c82078070b545000e41d80764982039145001c00d100307400020b0703c40c0e00900448900c21503070101d61000601200303030b1b072200100043c060342c105030068070000d96540780e44d2071a0300e00707550301d1a00a00c4 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 929422796 1250 929421546 929421557
    0x5031e04120c0816080a200a03060e07050f0d0303051b030a0c020d031e0207050705040509070801241502100c050c060615040e0c0403170c0d110606010f0207090c0c0201020d 76
    0x2812440300d803900c4c03400002402c00110000e00301140e0055007e5194602001417121800640f6817034003d00510b03c071031440e005841050800300e8242003005005c5201c11000b0254a50145550b8046000e84401400b100004440d88600c41d1241c4c000406076000351002c050108400310b0502c80240b420303000d61410010103040c9025a0121030000d40c1500621031514000342c0ea90f952030500500e8030800f90b1240703070400d240000700003c60300086021001d4072080c400074000303001040800e0000f010640d01c1030103481601003041144042c0030000358032013041801680c6543e03810311403400c11134618400b0701000c10b80c009221000c8030b00c1841003992000c411074000d203112124605071f0405000b00d01075100c0f810343d0b4038040350107022003e054500540c1d2004900040700d2001c0d000c3d4580b5080041e2061052186170142c480a900405540d1180c51030403004003200e0303803440c00460310050090858429030191040101d845201402604040360240d114500307000f0840c4002443c1c1010005014200507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 929424046 1250 929422796 929422799
    0x121e0e01050d09081308010c17040803010b0a030905150612060f04060209060408030d0b01201b0d06060f03120507050c01080a0b06030406090b0109060305031e04120c0816 75
    0x281c0040c1034418051145900107809080d62800201511034200d600039640d400803800540704005402c010500c044c140c0e030b003c4100070f4506140c00c200d40151002000d10000b03000602501c041070004e4000d0400303502e00420403d10036241c0364180705610726045600001351040140310300b0003c40c0c200758101c2c9400240350900d450b009800b00c03804e010b03100800440c0c00050901081d903505050302e015000d641c041d01c0d42c4060b407440e40d070002c1c00d0852003030b03001c5070b04512019000c6010501c00c540e87c010800107442c10340001a94000c9100111850550240340840c80c400800d9241c455040a483e8802d0740100950440c00c00c1e00b000103a21414104020040200c000020008180c11100c0002800c0414142d2206da40303010282007002aa2130b0415400b204100a1004681040c0225030040d0665040d1fa40c881c54110281d4415000141041c0e00410940b062075001d01503104001c1ca1000c09603041a8454402c120000c142000c2640c2c0440c0105040c03003008014000c0c0c0550384400551640240d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 929425296 1250 929424046 929424049
    0x150c03041704260f0714041d0f07150c0203030901300506120a05033405010b090601020c0102070608040212070303170a0c1b020103090606090e0f01150302130603121e0e 74
    0x16020b0001e860241c0c1d03d903411815040a0300c8d005c19508043c5c04103590025880c050b210703550340c1c580d00c03401050302a0b0070400b028450003180684140c0d0b4001e8081c4d8546400d401c01035070346018800c0101580305150301030f20140b030844d0040e100c0c441c4414002007240d0400300100b04070b007040b60821110f84e400288000300001d0300003040705c024170050014483c100700620b9404143c03000c2d03502c800300036803806c07001c0d0702c1040010352043c0a145c0044488144a843e10401280d0340c1c9518621079001d80d10070007043c010f8070300440721154058401411400500c1ca17201056040c80c00950007240072644001c0504024a400c0801e143d00c1440c00c4009c1210007600c4a005000307148503440705041044100c0c4840559100350010034a1503003085080c8070460b0355801543c0180740d40180b034038290240e501c01605030801070040041000508004c0c550300303030840d0200611241c100ca105100c0981d919000400100760319445001500903032505040c003420441014040d841100d4900c0810a0b08009a0300d40d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 929426546 1250 929425296 929425319
    0xc0e090f061b19030f090606080f0c01320a1812080405040e0a0c0e01080705030f07050613090e010209150306030604060c052208150c03041704260f07 66
    0x2a0303d011001035070140c81800950041c2058a40d00d03007018101704a90042c40f20640212080b603050308101d6502885120f0f1703954035643c80d03080e800c4c00203010f501955004601400000c0c2d10030206500c19100010344200b0610b03650011588070007281e103007800700010b81c0c209100100140300f8195606030503462681c031860175105034004e081c491907036440074111010003002108038075540003514210842d25054070041000c030902c148090351054210129260802160082440180c000106810350501d41001125000760f0006c07000c4000100c80005c070100240202c0c0040760711540010ba54224a2040c4100d041001d0000c4006800801c10f1045039100000c0c115030041d00180b0010f10400900400c8805100711942c07206075115103c4c26400c1d20303445031101000c440340c1070210781e00c84001d041c1e10381d1070360011034009820402c2840000d0110300070f00b80c80c0c101d100b258444036250549601c0d1403101740202c1160302c110925102960700084404110b0440795403220401800e94500d0070050310724 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 929427796 1250 929426546 929426557
    0xf020303090a1e02060c0a050f0c092a040b0306030c040c020d080406060f060801090b010c050a0f03050f030a020d0c0815041a1f080709120b040c0e090f061b 69
    0x41c00c80c0c00043d02103540c003007080c3c9041540c0200001d58816042c001c040d40e511481c0c100f03491a00450042640c4404000341441000c9070241c010b2055655900d100094007118042010000496601c0d0f18100043d02000b40040c09050382c0300307500d905288060519000e001041c030f034010340c60604030310b66964001502600d0020540343c1445117035a9880c10502401040d80002e58000c000c00d000300d1166003000229069078840d100c100804407400c001184c80010039500038086401032114000071070031100b58150f4190180c10140c0c61301c0352003910f0a52030340c000c54229001990104001040210794060b000b4041e22501e040401410328036071500c0e8130100d4408070f9105560343c003c2800d020030120f01203600040d004010080540f4003d20307059003c6003800b20040010703134460002c0c0d0b405015031800026100103045810b20047c00f80d4603101141d8018200f0f80d07000040341310010b0140d201aa40310302ca03503a5540600f25010504112615184000d4404085486c1106001c0034424411046e142c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 929429046 1250 929427796 929427803
    0x1111314040b03030c0307050111040b0909040311070905070e0d0302061f050a06030c1103070308070e01200d1d0603040318120804141206061e030a120f020303090a 72
    0x1000030440340040d0007405041c0d0700c150540408140c03008682404005464924056402841400c03841007204145101394000d41400b110300340244412410401542c95205202c3d0404110720003070800e04900c3d0000c0c65000f0030307005458400b008a143ea2000300400c4c85c8100350f4000030031080503a4081c0d110800203080413045c04500c0c0344802d07540d1000b01c0390380c0100409408600c8158544100402900d502080c2da0f01040444030050001c20300041201c0d03006405030741d10190354661901c01c036005d5141078040790400501c6601440185504405040000b5005000344000c2410720800760034a400075840541481e512070203c002515500c0c100ca521035894507050b05026003101c43c600440c6820b412000e00754211102507410010524000d00c107450500060f84d00c0e4260030b508100c5846540d0040c1140c47e0400380c0460164101104007101c07a030507000d0713000050f842d000082407510300700d01801d41c2c4070340403c403000c40086d40005040031103c80e0341c40610f2079460001002d030b5551188001c000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 929430296 1250 929429046 929429069
    0x70f08060109170c12060a0b06040305070e040602040b13090f0b0306010b0a090b0a02070918030f030906020c030d02180d0f1407150507050c19090902040b09090609011113 75
    0x100010f00d07007400130b121000e030000c103400c4c401c1408804565442201311004c56409140030030a20f030700c1c074024050320b044035031000081881d00c3c1003e448002218002c1c10444856400340004501e900c0900c010f49810f60525150021461034080020103440303006e1383e149411454518464059100403c84605442840c010036944801040040f9111407080e230020044400c003080d0008519404168103046071144a818071100341c00900c9800d10389070b5200010040f40c400070107858102e01907000800c8103800f50000504210000c1c02c160308542c030522180da1820341c0003400840c83c00440154140c5a40f0070343e41c800c0d4440443da03921910009240c000b6010711440d000303440c05980c0420000000d0302c03140110048240301640040c0581e00214001c031118052402d1101c0039080007030300d403501c036801f45032103011851508240703000034030000200340c1c2c2158036028507a00702e44501007050300a07074018001305410b151424071f150860303c85906c60b14142004102c0b8100d034941465000b4169005141d69 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 929431546 1250 929430296 929430329
    0xc040605090d12021f06060503180a0212010b04060b071e080702030a0f0203010c030c12020a09090606090e0912030402041d07090c03200717041706070f08060109 71
    0x358594840e5100401049029840700040f981c04500d40c5444690b040b890030407200407a041c1c02c2903525601034240080e00600006140b600039441c1064a1122001903802c2044150003042801c60001c0401702180e440320b114501070b0605104010041c104451428244440e65448028031484034480b44140401d000410b0b051042c0c1d04111240c4581c000c0441d40b007200d103442c000d424170404c00805e0348254a44040c0a10140c041e00444d150034550740c2d40d003400102d1000070354000b50015000c550400048060108148843d807240902501d903035103424500e540303010a003900c260001000030000b80c100503105120300840800b584e4000c1da04803408a1004490344500401d81a04040340002d0300c03c03140001043c86503a07214240c0c41149035010700000130003d4210a00043c071030440b580b1a80c00300b00580104900715010078007900548003a40c82c00ba6200c01140140000901959140d0401000d0200c030700c1d001540894500d61b941800718a900d450000680b031807281d40709600e12850030110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 929432796 1250 929431546 929431549
    0xe060115020304030f080a11010608011406041407050a02010609110c120f030a11070501391202130506070507050307050d2001050d020703030501030b06120a2010080603150c04060509 80
    0x3252944008c0c0b41000304000c6a0b034079405801b80c01c850b038602d10702540b9440070030500e05060280c076140400d004456001c989400710101c2d007652225040c10110b5603a04804510054a4000c2d20200c2d4600903180c0e4955280d46110350070850603401314030314180204491440b40700c043c000d60b984401e0b92000003803c0a40d8140600a910461000411a501e040e08007030310f400381240c108001c105604c100e2020403034440d6904c16003017000640714000c11300300601c2865007621a001001c02040e0601041d1015a690002c1280f64000403000c44c3c40e600140c105100030b01302046400c5c0280340440d0144100072450b26031641151612600e03a9484540321103900c0359902403000c840300c140203c10110340d84d06182c10001c0c000d080c02e02040311015aa04081007061526491030b2078104501300160601031065610b038103104201c50318009640100000c1525565503092460f12003c00c5034884150b1880c1000c105801c16004c0810300008501c554244010101e0450980d01901c10314240369a40342404c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 929434046 1250 929432796 929432807
    0x1e09041506051b010b0a0e0a4101050d0f0c03080a091805010e161710031505100603020706020f0d0e0706030e1506130e060115020304030f080a 63
    0x4405040c50303420000003402a902034020201101004007104020019181ca1400c0e00e42e540440c2d9882844641c00f40312200310a084c05801145645000900e030000e042c0480e19078203a2142507991107650050f1030303a00303074003924004190144250b12207004e606000c0051080c010100000d081c0f032311451441810400a042c0d0303000619007100341c2d035031142c00c0d04070001c00c0d0b110745000d40c3c8086011689859405000c0d0301449058503c001440d0511360356101001060603a68031144040206092620460b102004400f41c0034000403c0f04240312815420a500c45a42c03071051441c2d203c0c079000400651000b41076607182521075a180142c2d807a80141040300c06409560001c15210400141e0401116401e500c05ca2550b08003400780c1d0141c6a0340d08060b411251343c401b0400441c0c01c05170701c080007044c1c201030280d407104008201105070f01e5907054040403503030000a401c9040d40304034014007250384600414024807543e03200640c03900341182c0d6005002017511100400100c400700340a4120b50040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 929435296 1250 929434046 929434061
    0x804121b031202071b2105060c0306060f03010803032217130b0418150e0f040804080102121f05060d020c211c05010b1206030f010216171e0904 63
    0x38010b181c840c0680308500c80b1041036480f0303100c0d500f41aa8240070400e1b003580038048081d90420040c3c980340d41c8945000141d0347c0014101e55105804014071404110030401a502810309000110303101c2c900200400304814003801480c0000c1a0030314900002040d031008000303c680d08a15030b9484483e807c3c03040d05903000a030880d05107000007160208a001c0e240c0410400d6001d4007005000c800742d20740c24201e00c1183d030b0245040070807840c80041c0b40415800c1d484c030741042c030034210701b4a4503594215142c22038001e80490001450440c00340310b40d8040d00121a103848030405e064a0b201c0c0e24140004049100d00e1510411075500800e110101b00000d0000f88070007411001c1d80300c0f004003055610f600325406481d0344040b0340040002c04413001d08505c542410f079508401d44525200b15101e004440440c0280312981c944034403001020744840a0002e403100c2c0b00745168404201c40c083c0380000b040b01c01200c4401c2c070120107215035140c101120000c0c01840200a40c211307920002c840210707002e000c40 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 929436546 1250 929435296 929435303
    0x151e040b0103200c01060621020c030702090403030207140309060a0c0204150305030d050106021f051911120606030402281203120e01060f051c050d0804121b03120207 73
    0x140407401c5805009005250300d444d00002001131603154001070b203118806603004201110041b0390518a03016075401041000010400c680c02c0c05074a50000d40c411004480490000f0303004105081040f05c2c44107000f582200c0038001d1402c01c20420003240f418001c1591644c20400c408641400b591117907400001c0c45000b2001c580a000e40700e040266480d403103202041150362600d80001001480481d040107602030700702031604000382184481e03001c0d000181003132042c0c03d02002d5000301c07840d0510580016141c00c00395103441e801c59450160200e0301c01440207000c3c1e0800c00410005136203d01099006107210b06080a240c0411403000e034001046802100c010074000b1405002d045d006030205001d45403000c2d0500811180702085400d031000c5109402844030040f10030302c510705c2e0185103a01d011100b00c2c00080d0340b50440d200c10f482d1000898400b07000c900d4a00c140410300c1100c1149002d0702c2c6507424245c3e00300228910701081424005005804c02c01c4141180d40600960340444864031f41 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 929437796 1250 929436546 929436581
    0x50c130905011109011101050702060703020a0e131a2e0210150e1f03200303040b0c0601051206040605070311030a15060f050306040b0d05030d05151e040b0103 70
    0xd025448a544e51100f000c09010685030401c0d0300030201c05005132803045050743d0240109468402040d8080d4011810003014804d0107240e00300c80752107510303d0070f1130410101e0700825412a0018420381d8251820041c0d800741d880b04100c4200000c2c40000a00d002e5246030b9040600e0f0441d050803810400b494a40c0d400d01410728003001c0e620109850501d054501d802244e40c0640c1350300407250690b030041c1c58000d1003c81c0c104410004114605114035014050300a140303e01080040000c4c159801600305610b2108d000c0380741c09900e50302f0801940503000550b880102020440304056031988010310003040c0c00d80b25800100e84512a8128080c0d07c0c5d007010540f82c8074200070a510f0003074809103007060900d04c585000003800521030900e401060300162034a80c99602c1c6e8500f0302020b807044088654106500a4040e80065070401c000d0045681c02517001402e8180314540407401c2d2084a4517a01c5401050442c11600d000350b09080c11680c42210300103207500c080c400503000f03068200046041740341b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 929439046 1250 929437796 929437811
    0x100c03030f3b1002091f0c260c0a0512040602030403080904060e0423160311030a02060703021b0307050f040513060218030c04090b01060809121801030c030603050c13090501 76
    0x1200b44c025108100d0100c0e1000c040c052080a8607000881d00d00c076000c0052410118017002c5400c040300c907402090703030a42681042c07090b682c02000b60b6000e80c0081845511484a250034082c0602030b040040e800750102d00c2c5002e1404200a680717006a00014101c03080000b405252540e403a4854801884a502484207a10f070030300717020900c1e015401e80e102d4002c0601140d0540c000020440d4816200007200e052030306825a00c440071050345261200c1c2d011f01c90324141c0d40c00740ea5a04041d04c105440303031b4018540c1003900382d210901010950305043c001c2d480b00340e042c0410764500041c00480c42045e034000130789035078018086044255916000d4030580c40042d111507409510079200740e405006804560b481d0490405010444440c0038000c0d00c261178480c0148165071240310aa900540341c001194000c580500c010400b541c0a400210518865229100b4681d43c050052021412640c10204029491600ca0a0311000e418400350700c100c0c24020034900100700b580c0503001043c1c02070001c11191 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 929440296 1250 929439046 929439073
    0x30903290a020705100504021c171605070806070801090515041b0314010b070308040f050d03140c0309070e0705040905012c042004020702100c03030f3b 67
    0x2540046001e452502170450340c0c1520360b81c1801070f0303801070303502609501d580c0304140d80c44920030f82c07410720450f1380307403444074902c011005090050221082440401004040c45140040c6052900d0b846900c403504154104400260400311355811102c664002045560720300040c501c2c0d42030001c440503481440d00c14000b15600d070b880c1e048480c00e500e075102040180f9046144005520007445245040001004003e00080c070036000241c02c580f1443c40c078854071001d13983d81800c081000e80c00800099030750403000442540000d0383c940020105041a1450030100c8805403501c03642d0054900a019000214921602ca00e00316001454071200030442c0c1d5071940d51484100075031140410b001280c0b082d10309030044c1c61007415400340c0d80c00f400880f01100e201c82d04500c0340405403000340c0c1c015802e000c00d101580f141e4210740c2002140740d868130f403042c005140190482c0c8d41c0f0264514120301d440c42c140030840c0d0610b0b9100d03207200c4000380c4182d5100c070450401807007801c2c60002a00e901502e00c180040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 929441546 1250 929440296 929440301
    0x305040c0503190501060f0b0d0c0c020d1a0f040506041704090f0509010f0212040f0809100509030d030501120209060310062715090b2e1b030903290a 66
    0x52074132880080c406a503981800c2c050304850350007400b03100801001045000035031907020100c0210641080c2440480940000c2e4001c850720701c080e21241884841034596025107010705604c12200c0300700000714102503c842d581d990b0014001880c0342c40819002c0c01142d5080e081d68010400d51700148803c081360045007018103019640412190b0170011401e02e0300b156402a1844600400310040c0e82e9959612204103400b40024180da40d07840070450308200e62038491301446070b081305803125a540c40040e800d052415040b1462901014688001440540300e82d5114010807501103601010940300d05c00080e040400c40703042004d8080c41c200b000240c1d0340e1540d055044045c03c901891290483c1c5196000c00c0d108200389182c2030100040c020b00508103130381d000d0740301d001005d0104c01c00300481e8035110761001101180d0840002a11030a0342609502405180b420a4860044403003080b103a40c025004540d54003001300080f4002141c900b4880958600075a041c1d40903905414034107085900d00300 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 929442796 1250 929441546 929441593
    0x17120309070501181a03070302040b041212112d030403060b21120c0c030a0602030118020c0607050901120603080306090a021206060d0204180b04060f0608070305040c0503 75
    0x1c00c3d084c0c0032001e07491511400f0b5604803440c1c883c3c59988000c2801d0302e056141c1c0014140f01c181070b03081c000481d022820030b0190000c0d0200c210301e14007248030703400c14408440003040c0200c100004200007580c0001c0105001d80074101c00202c00011601c0c12000c0507040c000740d01e040c8901c0c0b0020500205104880d0420100c0341c1c015550702e82d0713501c1400c0000c1d000c0e000454040703020790302403584415403a0f44080104400084001500d011002e03907400281410f8030360b04180c1e44140c0101c014000780d92544600203960b0f8140904615008030070007125103407500248100b00380200401e02c0d00b2144d00411103840c0381e4002080c02c010040e10307071400b10800d8005440040c0101803c070b0000700c0c540501d04c220703020300301001442d17942e640e05c00c81000320039440b28841144040e024000018084a680c1c2c0c2c07003044451410012401e00020418481141d4841e4000c1d03240548c40d0508001c410707040950f040d0040002d240c045159a22030501c5ca031001c9050784119090b1140030010340c207100000c4030802 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 929444046 1250 929442796 929442799
    0x30102071b0e0c13031e0206180f030703051c0306050303040e1605070b060d0302210702030c0306060622050a030f0309080d0e06071e0819090609171203090705 70
    0x74110f8984500f000c43d140954403981110f4580c60b142800464170f42c0e49925400d80340442e41044030307100756012400e5078010685480c5070028400c030740540c41c03030003110352134911070181c0080004a1039078546640d501903449555400000fa83c0700d00c2d2456110b50010b80103010007504803581ea5a1310000002405030844510803058a40c1d4656030050f40f290044681d40c0e43c00c2030a48200d40c4648080159800030200c04800394400c00f42001c4480d0001f4489801071914040f8042d20342100c0d006060a201d200310751030741300781c01407410081c09590300c04c281c8010440030003e0300c880c28485040e4428010203604596480f4031960030000800440c000c410030f02c64401d036502c2000c65a075a0210b681c5281d41d24445012038083e10081160b801c0c00c00140c000d41c0d000382c00d22004135502841c51485000d06040540b504200020901d1040c10f900f00745024001051804102441c94244010400810350107401c0e050003140407a2001584100712040180070044601c5580e070070b14410140d40e6403d14440c0a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 929445296 1250 929444046 929444069
    0x2205030c010609060b190e1e01020c090426070503070f021804080a12093e01080106110a060c031b050412020603040302070312030606171e06030102071b 67
    0x100c0d1056071030140e00203c6172000c00031414080d01c0e1682041d940100b0258808200c10745001c80050354980e00d100714a20013120303203004500c00300400242844104001c0c0c3c0e00030381e41c032020300c8001503515008103910b004204503800450315000c80c28050b407043d000080c1507440080f4030380090201201016100c82d10840715001041c044a0803038018000840d0040c0c607804040c00400b18007400ba01c0c001c01c030340742c166100107004000d660b100901d0150f11203401c034001054040b0301441c0748130014005055101041f55070010700005000a0010805000d030208100016100700180c00041000b0100d2540c44502880164004076009009092a1f0b02c01409007084900030907005005800720b6098400c00e01c1c10505032511602441b4603503202400450441c811140d0010100d4514040300f0001d00c07942da00070a82c03d280080c010a0b25146002c9024100c55050901c1214858640703204030070107003140c40400550700c5134006030081c02600d101500014070b400d5072284104849688400b0f95408004a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 929446546 1250 929445296 929445299
    0xa0c030507020a0b06061c02040803072a061206090c0c02031b0a05120a17070b010e06010827010903051e0a090b0325030f0506060f0409052205030c0106 67
    0x8aa40301540080036000810740d13804a4968140314000b06001040811001580007884c0a220200d90155000e0311003500080742403400c00c110750600c01641d040c524819000c20052a820b1129101d6a01c101d409015801500542e507402a800140041c01250780400c034100e4401e00180510f402e03054101d102e40102454407900174250a80710070102800360140c0082405c000a00c00000c2880401501506c80d0303a61000000300c04103a0300414440c00c20805840303200601e0558800001a0012050015030340100001641d00c952456408203200401186c258541001022811081c7c503110f400342d403c1481d4001415001802056004d2171042080400d00944540008600400039001f00250101c0c0b0b00300803070050076001e981c0004c100c03c24040300505484840f0a004205102c000c0402e4465015605e61f260301e00c101584910706994803403801040e0381f12600a8407850180912041d40e0303a000c96101100b0344d00038602c030264840c00c203c0c031481a0600c035541c3e4112401c144019801c2900 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 929447796 1250 929446546 929446561
    0xe2d0906040545070303141e0a0c061506091a09060c03220e0f0412110a020a270207150b031f060503251208040305060a0c0305 56
    0x1995210710010121000700f6100006000f500b0741c0c800010b490720400062042556210088800c446003182400a1518514510340074251003500c030300e0086890b005004c207011103034440c4840c006a130a1180e843e540d907980c041069907004074010024140c1c0c0e29040d400005591588160020f075115611380c40041e07076031a00c0520044000d80303001c40003860140709010701814014017804110722100144c0c1e08100003c6904c40c0d12951a056102003941d03d10b0b000c10074441c0744560650446100049548145400c0d1250440140c0150b82c820030480d0004600c00b007040c0070302480280d10340c0240140311195655400c000045030031350940b00e418049003101c035001c480c54803c548095506c0710104c40b8424200d09640010302c2111049900760107141ca42c0d40e4144452598400214508400041d20b41d00381001c1c54600400001c072590340040e5a1030041003000c4120410003210355120310003014140740e140840050050341d1004105104800c24840d034510306400c410003698040e0340820503681d403041c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 929449046 1250 929447796 929447801
    0xd02010e0c0a03110a0305060c0426070b0313060e0a0203010b0d0b070302030411030a1505070f0c080c0a02030d02010606020616120e01060b0c03040e0a1104060e2d090604 75
    0x40007030341c400703500c0d5000c200280c0c21040c0b0754540540200108072040d900d4450900f00075044643e04802c450004041c4440c02d402200c0345075222900c01e1004005c20802c58050f526a000e008007400c001000c400201c03409900c0d0104261598044e4041c070519144e000719656505c2070140807072280d400d0101c18001810301c0c000b43d4140a8002801500b5a107840c2010350007544050001e46454003200c40c4003c1c19207080102131103051040e1001e440034003d941d454030440d10090801010015402d1082901507480344001c030743c0e59044441d17150b68010441000d8a01042100000e41601604880d90340340341d010740c4004112400398080c3c0300036039105100715010003c3e040400011441c0f4011800102d18181c0c0035656a603441b000000c0c005803a040d0170751094001d80a000e019034800038040c002107164a070015000f541c0908188030030031101d11a000907000d5801290b08000304e48803121443d0344c3c0d58108003000c0c1d400002c10301503071000008103401400300700c410502485045c0c0203e841410b052 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 929450296 1250 929449046 929449063
    0xa030507050f04180b04050703060905030c060a0e120d0929060301020406080a02030a0e030c010e0f010603030c0b041707080711151608041802030f0c12060d150c020d02010e 76
    0x2042ea060444c00c050780c0b40b0f441c1440c040c100341c41c540701d0f00c5408400190300744509400c26019400442c2c903481c60103040c074607081000f49170071021420070031aa5070070b20000909103a0700300740340320140e180c0690040e0760004001e401409000c035a2400084540d154018409412102107012800c1c1d0907076800090509030720032845540f0006220000090042c0d08603406587c00c6441032001040701c4508192551640c2c010301c030649010303555171001403824402040420f61508105000303014145c03660728007814107045610080d00d00703110b00c400101080307400b10031807150748038442405449828506021180f07402c0602c0445030019601c446a6039440c2010540c451812091110752400c07801303c4c1086102c80c1075440c1140c10403000c2c44041100050783c0686005150300140c010b840385024640c0829102000d00000020001042a111141498503001c0d40c40541981c590300d00740b54601d02601d80c1030320394859a1030346103029810b040c003580c00b00710b4007603401541c1e00070310002d07011040b22500c07261314 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 929451546 1250 929450296 929450321
    0x10f060c0f02041107020907031d010b03030d0c0516030e330d0209030604151b020703081e0a030b090c040f170c0607050a0c231504050a030507050f04 66
    0x401c08940010314068005180c0b29114640d801c0c00e0500c1ca03400301d00380240589010001c02d480d802041d640200360820308080141410080c4980f070114404643c4078400d90706500e01c000e441c4c101400c5024022021104108000301c070b8400c504c01281002403100f04080b00d5a4810000704086d03403012030265802c00080c280040d04100028802d180510b080c1c2c0c03220400c1c00005400344482c001c3c503070b800d010319881140161100701031075a0f090300c0c0310200d95044290f40541d8484c403001e401040d0b8001840700640740e00820b59640c0b40205030700704500401300c011341e40010f03000003122155180c3c9a0004801c400040ea400752564564402d0850240183d010301c0c54104d04002080008403104249410450090b07020b4603078407181100440c2582d40551019103e5074083c80ca00307010442001d00c0c1c440100780f03210f0025422145640400012070318044690b108903021200d85590072810021503000f031800078503209000756685080c48c0c603121584a42c0b4881e0040b20403076450b500b000d006408111740c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 929452796 1250 929451546 929451563
    0x706080708061219080d470a090905010c1e12090c030c0f050915040b220b01080903040503070513021917060a14150f030708010f060c 59
    0x50381c40c14009203400c0ea1911042620440401210111139203075122522402814200e5950001d0318010050740c540703240c2c1c030030100c052844007504030403034920440d041100461010040c0c403001181036072145800000039408108110001401030460340800d40703a62151009000407400c00e8010784000700c08814104a61602ca101007224500c42c04608001c07007000007000940350700580f114410440c03c0d400c00c8402040302c55060060350f0781c00c000b0200604044032032202a141c003a030740e0621030042c0c046c83c6000329259089020b49035102c08400c0344103c007110a00d000891280d40c242d019002c103e507041e010600c54408941390b1a40030044074151000a4010000589820203001001d500c0c030080c101001d6003401884e10460010720000560360f100d130f139154000004070040d01d1003100058012842950200f0003080b0100c0e00c030348882005841107800110b20384225615107214414100c000f842243c0010410500b1303500031031a117050318410b4a001d510341e900d0702c41c00d03181240100c0000d4103101 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 929454046 1250 929452796 929452801
    0x30902240910050c010c020708102307020c040e030904151a1c060915170a060b1c0506070e030a0302030f0d0204080604030909110a0e2e0905030706080708 68
    0x140060405081c030b031546003003807130030740800062421141100e01d1400140c000d1070007001407140401191034402c10b203000400001d051107542040402c0c03c03c1010b60320007101400a1103240c02800031000510000d40148090491803501c41c1d2203038040803885101c0c9140c1a203200d60540e00700003940c1520740500840c0c12591005104103540d8018045410345000001c008006450850103605d00820b00c03241c0204920b40b2800c085120742515810044620b8000b124111142c10001022962590401d0300028082c20b0b41c80481d03508040003104940e103980081c0c00c101040b00000d20302c0d109441669400012460382d200b0580c03960742c1203e000d00168402d1005c0109158404024040d008040304014501540c0d61030407401e05804940c141c020800d2034004001cac010701c60107070442d00f04041354031901d84004010058400c9083d90040d80c01072141c011190034250030300740c440d02d07034130100b000b41d0003507400d2014002d21030b060034090f00b4041e00071078100040341802080190700425070341d241c0e00c4056 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 929455296 1250 929454046 929454049
    0x50f1302090f090a1e030201060501031b0c020604051c060c050c1b031f0515040b06070b0604090503190e091017161724072d0309022409 60
    0x14401901048041c0180314124001805c41e04803042d81c20908111841803520310308010f4211425540b005041c5401c000445801d111110741e4074180e4080c5092120300042c440c008544036006540000e500400d0a00000c07106103c0b10300091207203031081c1c80c240300c20a502c4408549034010302809418642c0048003600d0146860003414114a00c00b5003155800540000c64514a6843ca6001c0041035942c0041c0318000b00220702440340c0c90010381c1c0900400d00701c04041100e0b4030039840094170f080b282c080412217950742c0d9040458666003102c1203d44a008061410003038141c0c1100400202c3e4980722640c0c5c690400841d124403685141510747c0b902440c1c8800c207010b8986420302100320b801201c0381c031a2469031403010a805001e850817004440503400e001c00d0715040520302c2c6000e0628817aa010794029268100e480d520030641e2070000c03048900e00b03424421004200c83d0150603e051810041c001170f9055018807142802145d694100903d038042d0602e80110060407186111810030610296 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 929456546 1250 929455296 929455321
    0x301050904060b040929040b220c030813090b030a060f0b030d020f0c03012705030f030c030f0a0c080f07020703020d080d060e010b09010c020f090703050f130209 71
    0x101c0c1c007410012444011000008003150180e4400f160600701581150b4000741e03501d40d0005542010001e604603e04240e02ca01e240403000a002d04103101c1d01c0c81422842d42032a00c00031201c19408440c500b4619264541180190004010410b02a40103d000140303c1e40c2c3e4068190340643c090082d080100c0d460726210060140008002c1426031a6941005aa101000007140c0030003941c0c0a4080982d090761243d00306052095118842c1e8100b07030054824201c0c224080750a0b80200174074003150340d1030340361060a40c0286841c40011080100c10000e6004081009500c1100d40c440180080e80d55407840c5070450f980e01c02088000390340720000844001074291082d421084900403501020f6403540002e0200802d20300459072414080361003940721410f4000c842c05001500c60300c0301c40d9810008094514010001018100004418064250f4440c04000e1041e618080e110707500500c1d180e41c002e00a48401e0742c41e0074420304031400107118180c0311080381407190ba000300075682c02c0d12050315180c603 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 929457796 1250 929456546 929456551
    0x8010c09031a0a0914060906160e120a0503130806070c0b1b1e0706270836030c030c01020d051b0f150702150c13090e25060503010509 59
    0x3c1107681c892204001c2070650910000000581c1c000b0001e51400e80d08240c20300d500a07110281910400354244d90142e0040130b461542c0609881c41c2310a00f51044202c0e2034291407600c060898000000e10340c00500c00e01005e042039034a403004491240d100d43c00d040f80e101211b10b1b0007914122450000c14000d00400001643d000072103c1900c0c02d11014044107a81c07040c10400f103c500d4800000d4400401255008280780818081c1c80071400d4000564540200410244000e10400d400600f40044203e20020b802000c50003031001000b07844500b07221580280d080741c80380e10030b106420000e05149000200d045440b001079026020b46208500280c41035045600d21801d5000300c01250b11983c40201b050090101b5140300400522104d089441c4a00c0c0000c0c09803421500480d4007a000550f0591500740c214615000556a4442e4000c070090f140605400440780103040040014600c079001680d90f501c2e084d5190002071000942d41c1403039904142d4070031280813560500041286181c12030700300da03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 929459046 1250 929457796 929457811
    0x150c110d020415081203060607021309151d2b020304150f09080c010f0c03021606020c10080907060c020a0803070b010939180b030108010c09031a 64
    0x2440c00c8519070000781aa040704400b8121500c000300c007000590420400b01e035100608180071855070410002068880c03160b030714064011a40f40152480c882c42c0c035440500d1850f0410710010f07031034903081c0b04100505500000600b0200d019016400246001f083c11000c241200849082e032844061a000000070324114031019404248000170b55454100000c00746580e290351001d90070110f416018122301050307003100b115540b02c2d000c18a520390b0000300c441d0b206003060404000c0d110107440c04034580040c65513034a030806403480300060050b40001d02c511811070115822040180c40007001c842c0000c0449029282d50321840381002078030700030389070b1558482c00a002c49a0302500c03840507510790f03400008210780301d0010b1070042240030a54442c1030140c00d1400301d40300c0c6046036580c03059071090740720078009803d00104030235080550245183c0d00c441c84030360128603071031b03903a90007240c00c5600244140c807001d50802d20705c00009032180c54801305917640545075840c40112681008030b4404000c0484 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 929460296 1250 929459046 929459059
    0x50307020a052e090923240105130504150e0903071110021203091f09030503061318080304060f050421030b1203090a0e132402070c06030501150c11 65
    0xca0036020358020310612000c0c081036003000020352030b460703841040c00070159080604d84940c49401c85840c0b587d0302c0c40b40341c8246021500c5209074460542440c105d0b038045a0b002d844d040342c4c10907169014440d0021248400b034400550341d01c88000648130301c01d03008000d000d1101d0a400c0e019620344840c0c08a003140c82ca104036900c1420800d540d14040d8000d442803103143c0c1c0010b0402c4110036000b0001a0b00d018401001d02a07010310750390180090102400c0284a145c402c500034040c1885a4440300c24640310103000c07074002c2001d05154089510683d019191142003105106827008a8001d043c00baa034031280c9801b4106450f040740e0b81c180009000c050804d80c60320040c039080c0e56a040c40707941c101c8200d03000d50398980d4000104261740445500c81e80c03c4400003000c00506c51480c40428411540049404c0c000201166034281d44910007042128018400704d00c900c01d01034902ea4800686500340c03404c004690b241d45000605c0800c6000c428002007581e0140030001c0c2c503500600c104000007a00c42c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 929461546 1250 929460296 929460299
    0x1805040e0c09040b040506070c1703040201110313060e0405010501050a0c03030209030d0906020f0d050d110706060e01150e030c040b0f2e110d0822050307020a052e09 73
    0x9003444070143d8050b00c21511840c04c0c481440401d116140d008801c0d410224501415599401644c800e4445c40241c600408030000d41964094003c040c503510005058030340e00c0480048112001400740a14000103001c1d01c0b051b202c80c101442214184c52050b10f41606120501d03030226800c8a15140840030503409100b036815580341000500610311154072407488403030400c9802031510034221050213403a4890601d081c04c25420004803190407614a074081a6844180043c4d036480c4110500100304626052000500300e4007030035524140d41011403342c2c100301c5184412907003a04050300c9180c0c5504041e294480f03901c1d0036805200d004801500c4000c01c0700003030002464600340341000000d405902d546c3c0c400310070342c205884030002009061440c0301c4405c03011303107554507440040b000d01840900d07404524020a400c81d1910007042c181e154040da00c495142c4192a40c0000d0000ca018984110010446240c98224180480c5995241a590003090b2030b21000c5039505100120074046a240c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 929462796 1250 929461546 929461549
    0xb0d061d030705010c1101020a0f120603151d0a0503031504090b040311010b0406140402030a061203030c12021204060b04180f0b0711030d2414030d1805040e0c 70
    0x20b881518000c500008007203145400290011100b002030a100d40d01c10481c0c41c2000742c0000b4480042c004e5444d20481400078900e1300801018107400240c80b2481d416003090102c1100e801448403400300c0324070744001c0c1810a601070399030085450300030099042480022040d42c040c00080c19503920080010810300c000351942003244000f0759050300090000646000d4440b42400f40780d40c0a14182c80c10058285410b120702d9100008850613031141c0c1d00000418070700d1065070804d0b0044d10000c6d070240841291458060300a100d4011480c002c20951442c2d000320740305510036640c2003010312024a907182d81e140d55140080803907104481e80079988080d003030700403c03c0010f0040510702c80c100c40c81b190780d01801c00100352940106007008100c0c1400d00442520004000e80e103902100c0080451016201c0c0d05004107400050000003030098071140000320300828001d01c182604013030f003d55400701180441224600d658140704401c1018694003004642440d41c098100c0c010600d00340e412903020b400 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 929464046 1250 929462796 929462803
    0x31202090a12110a150c020f03010b0306010e0f0a060608010306020c160f05030f030f07021905150a0318050c0d0201050706020c0105010503120a1b0305090d0516090b0d061d 76
    0x82c0155902c0e14011024140c03030500e03a2040028100d0084407451100761030000404040c2c48020080c0a082c401c08480301a0300c0c06d400410212000030290744c115070310f0300c802240001e0111840164000b261000c140c20082c0f41c0f051a02f5035081d951020426030850700e900c40a54091041c011051040d84110302070721651241a40180404214180001c1e250904042ca405000120756000c1d400411801105102050072038240d15416544038402c2e100d030040310185061998001071304183c00074861141100d40300c2c01440d141c409900c08010300b004e0350810f444d413100604001007a40d88014500b1000340703020942c007680b203403051410307500d40762207503036450141d800207a06104244e454400600031440c003401107041d4205141c00d00760030321032038440003040300504981940e44210403180f09800d05101d801250810840644000f9246c581840c1103692910f1155a41c201c000c6540808151040789018280704d607400188541320b600c00a40fa004000c01050140500c03ca9407803200342130f0500b050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 929465296 1250 929464046 929464079
    0x130b130c060f02011413030c0203031603050a0f081018020f0706150b0307090e04020609031b030708030a1e0521070e040b060d09050c0414090706020703031202090a 72
    0x50340c4a894600190b980031342994080041003069104080410902c2d2030a02c50b480000c607003610b08804180300340d0010074107512403507420340d0301c003018185240107164102000708623445156803070080c0d208100c4401c840402c01601e68044149440380100103d20300380407400d02c01c1e0358040c0010710b031001d0549100310540c4404c1c3c044418a40303951942403504141707042c0308010300c0304a0707100c0c0c030b0340ca0034141c010000c1405000781440f5040c09004a815511110103650040e030700a01100d4113541c0a015140064066041680c400d2007142004102c0510110903070306410102e0300c0d410ba441007121051200141d89442c00d0042010a0112540034075090004402e24510450030781414102080c00a00d400c0c0000007049c080c0703040109402e402d4841c441103807103490744603c00241c400010300c0c1c10382c00d00800c1c407138066016041500a054403106081d080c0e00818413a0201d40315a56106c500760784800301403202a001c100294101c004402454005246200b00100740001745a01d8005404440d9202e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 929466546 1250 929465296 929465309
    0xf06031a01080705031009050109020604090504060b030f0d111203180d09030c060c0302070b13090b040e03032e1512061a090609031c08070503130b130c 67
    0x44222289450082800d01402d030742c1c0042c0c82c045003010080380c1c6d80c08103144110a00c4e582c0b6100003041c02000e62003807070740b00e074020300d2507030348a640d00c40100203040151004c0c0d404901d000702d080054a800103480030024180006020b807800e00c0902075407e20a125802295809074458000310442e00b00300661207801c00d54120b012049050140e84c1c5051002c00e103c2c018028200703410b002056903880c040044804501e45910000103520341241000410780c0706c10580000410398268040d00980d4441c1a2150b041c010000c01421004100c10f83d001c03c00449503581003040800d22105198007204802e801206400d03a0504482c401140c000110390700ca02541c0b2500c44044440d258407015090944041510500c491400c001d48014118420b5451004020340018051010340f180429220701d064000c05540601c411818081c2001694020820010303544800186004e40680b00340c0e07000d81c1100b010501d00758110b503150502a000a808001c016103444034440c00140c80950f01c1015008c1c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 929467796 1250 929466546 929466563
    0xd02090c120702120d050717040c06020f0111030c03060d0b0903040302210607030b010201060302040e0d030c090305150a0902040203071706041e0c090e010f0315050412030504060f0603 81
    0x840d81d10301210040a0900d00841d04000000540701000c00140c0d9800300440344001000c0d21654030a40e45044070074058a50b00941c02c08020a100c035034003000e4200c407101d800b51000200e40e02c2095007218404407070010501403e202003031071007044002940d4403800c0540703c0c00c6514915110a03100b104102c468402c141e10006081c021070800b914274200f031130f01c40d594110071450b2001c004c80c3c958100602400800d40d039034034070030074030381c400d400000096030090b01c02c0008080c504030113501c1d61100c8100700701080c284883d902c5e002d40315800400480f034005004d8010b92480d181940c002c090060251104c180d10f4546c2803002d03a55601c010f41c001d240ca40c0714102c0c212510580c2c1600361a00500392032003240f03005021354102c110380f9106100c81620301000100201d07541d20543e50481c241c3c01030108412500000b01d0711541d5440c02000b42d0340200340390389544d00704150301c0059602c04c03603008245010025141d0069400b030b811058005101e818089400714070003403100b085410950013501e030000d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 929469046 1250 929467796 929467807
    0x8010315020c10060f090b0102030909040201090b0d15120c060e190806040309050316060e1917070b07080d09062004030212030406090b070c0f060302180307230d02090c 74
    0x45e000c880e1000030318100303c050089092000020b500e038041e2100031802000044001811603204810500241024540e060349070745500940e40011301030742c950306803800056580800c0c844d060300786c206082548035218044aa007000b40850b11140b8542c04903400800305404100e07403041c80420400980003030710050400d8900b6083c01005840d8581c0001c3c00313a00100c158494401a510341070060700c0180c00c01c142d03220807060118608610f070201e09003881e100941c01007103072921410084108a0010102c680c001d0311045a22404d20030801d0080c196101000041e0f00304085803c2070300300e0350048400061410a03203a20000c0e040380142d0b0700c0c09000c00040c0a004601c0c2c100403000320350030100e00031810203060003c0170707207081c50a000b800000d034408501d0404001800342d6000142c907121214503100f41d0f9801c07014019402645400c010540341412442c0203040001c0c02c502152034402a00c60000d803528211580a400c1c0144144c0058682c00c2d82c00150f161074003140d0188402000d02035440 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 929470296 1250 929469046 929469059
    0x106030b0f011d040c12091407061b06050a0e0708060a14061e061324020a120f0525020418050601090c09050d030f0305090c0108010315020c1006 64
    0x6914a01c50906000a0811400c14244081e02c85842c150b01500c0000b5601000c00058a042e102c44035a85d1009041c02855010403540d10103a58048060341c00301e5404546845007600c1401c40780216559040004e0700c03020100da1181c20460304034410744030004a034800302e0b000320300385841500800101e910078001e02104400520400d424000c00c009002c40d942031850025452103950880400319112280500708070b03917100f20803100f0704502c2000b2210025910060301d10307441211192142001022981603e1722400801c0c0380501d9a40f1440c1c2401b40500404140e45080c0101c40c154104103007030049800c100038684c486443c0700e42844117042020740ba44100000d55111104200000c100c40c59010000340001564505480c0c101700c0108224031540805c941c240103640c801544500030000308418181c200ca4080f81400343e81e541032105942e151111951400f02c95241c43c0050303075000042000c14083c030041194610b4a1401624000a858145240c04c0c0c1d02c5092034001d650310714081214 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 929471546 1250 929470296 929470309
    0x1e050613110604050f2724040902010206061005040b0f040503072103080402040b0a03080306040507030204270e0303090708010f06050a0302210d050a0305150906060d060902030106030b 81
    0x101c9000c441140c505030419010a0050001c1c116081c058008104012031194000c110103049243c060008481d40c81c1119070640d242c0b0001c800106070040081e5a40c98500f05030041d25803103070701178004066940310300050055540d1010802c03010030205220208030740c0c0902004159010703540360920b45841c2808201810600f0743d500c80d8040350841d40311100c5218800301c0c2c3d14051500350038190b04541e114000708002d09000342105600c414800e002100b0040313000c0146010350b070161400c00c2541d41e40345058080344902d0044c054100f00104080d00d010000d01c100a50200030b660f004222500e080c0e07045461b64005072102d4274143c014030020700540e40248540710b0041074942d420f024103071410f40442c50480c854000a409040054213407540d003804070314582c01c615002c5080759020201e08000070996004880e0308030001e030804002c80d6415500c0300c6006c00b44030004020300d0782610351408200041c0d2007a40201d0113180c4a242c00a01c411807480034500804c0320351000310b03910310400c041000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 929472796 1250 929471546 929471573
    0x8010b09030607110705180708060f033315100c1e05150c031f030c052106091609140411010e03030f21090a1e050613 52
    0x1101202404400c0d10340e030340010420f80003006410001d50003c07a540c942d40c00c000d00d9402154210080b42401d402c00141d44071010301c110b03210380d074002c40d90316181c0800101c0e01c03081d603400398550b00c5082200d5952003a5103003034180800c54403100d413400d401d0101600d000740c401c441e03036a06000500f081340040d04040051100728152490140500b5607250b94006208020501c120349426015040a0811108005c8000c11024690400c0c04a2030300080d8102154801c480d28402c0b401004490b01c9d80648110078a401d40784d0000c2a00a01818401400704103034940b40c00111901442c042650282001d0000741d019010000140100c8103280c40600803209540d40421000ad161202c14942c4420403403006801c141e010303018440c00c0143e04012980d580c038400c044c0ba45070000050084c503903840d100050203510400101c01d5141d80030440e1541d00d502c02140d91300e0305500420f486100051014a02000120400301003964031005500e480d468120200e8080c010481021500000d10041c44000c02 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 929474046 1250 929472796 929472809
    0x63504030f140d050601090305010914070504060506031b0712110c01090620070906120606050f060703140d0e0a06050f09032b0c0203041424071a090d0801 68
    0x800381e203800c40440314811504101c4181390340d0408074440d83c0c45150f0300002503801c6070080c03021030380c0d508000544001e8040c030611244590800004c0509150203400102e807801409241141c1d06d494402c40e004220b03400240c0311300000c028400c00141c008040c60040d230341e075a4401c1001a181d214180c60301c0340d1846100d0500408000802060394801a03510141d070400d0418540811070110707644c9848603c1d00a246014180300000c6400b004000b0070340350341e500582041c0001540d4100f4009003000c04d015007074011100700300031408a8001d0300031507042c00100100714035060010200c00100c503d08030a1010a8020030003500611134203000300c0341c0001140c0841200d0307050542166603203100d00075080d07481b1807660005044d00c1724100100b007903104000b0304c1840440440340c002503c0782e0041c0200c0c80d000c0140045049127080100003032038541005c41041448180601e1007494607044070108440825001103000d000d0050810a03500a0110200030184404c103207a0182c030301c0c00142c0041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 929475296 1250 929474046 929474057
    0xb131509180921020c040501090c0210050c0f03250507062009040b010201060f1508070f05370315050f0315130b0708100605030907063504030f 63
    0x10000326522020b03510f103980d8590004110051069400d83c00d01e011405d80c180d102e80350000010700c0038071a0b00004103110082e4203a032102442001c0e0502181d42c2030700d40380981082072000c1c0c6541040d03d0000c6402603c0100c0c0c0c51107000d409000520038420483c401e4002440104404080003194056903c4810a00c180003003550b4141412020034021a084039106645510f00305110364001e5002c40c000d4607182440b0840c8644030110000c90a02040440780090520400103490501c992070351000161a40d85d5207252185a8002823500c07000d0314191087c092002c5144490254070b03400350814444162808a02007622010041000d203c0d54411400703205048126011540c01152901e150795240000b81143e859a0001c0030851420700d01c000c1110150400340010640c000c0545482017080346040404d0310b440d03090071035107800151401d01c000d41c0f140c0001c3c080c50317010b084942c050140c5650307120310782031468084500c1c003000c1c0e406e01400c0d241c2e04400d200c24140e102c581e0390311410070350408 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 929476546 1250 929475296 929475311
    0x609090e1b0627010912120f0306091107052401030b04020411030f010f06020a030c0204090602040e0c090310060503030a03051b07150506030607140703170406050901240b13150918 79
    0x1402c142d16031f514281020082a031005c180b01c10f00951000c4081d0400c0c001c10480304408468a906a0b440130707206403107602c40c800c40313403100c1905591454442550031301521070903444c40d40c4480d130020f4003a2003241d00c1521612403075102101103018521a421740c400d200305a52401030982c4150f8600d03000301d421508407002503004690041140b8610503415500042c01111a0070302500078015070300aaa0701d1003425007801000f8a0903409880000f00c1103060301c034900882808041290494455644c158006002408003103000b070f44010707030100b0140d00e21241d600b01400c0740f035800c0c2d101c94030489040c041d2030f58400101c6c140740710700c0d0b50105d000c0d0b00a25183c205000003402680452846030140302e40091403d082600c604100740410066811400030ba040030302e0244040d05040b41c4040e1103610b800c80b01c0c0010300a00c511294944d41003e5202c00e003a040009402d419484910381e03e400d01ca002c10b000503002500381c10a8620016a43c07640f94050415803a003a0700c4e0304041c41100c03054140800c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 929477796 1250 929476546 929476553
    0x5091e0d02070e1b040b0a0908010501050d02040b0f04110c1e2a0405010f1806050105090f030f0f062a09130f1103010609090e1b0627010912 62
    0x20742c1000c1c0d440c240500c03d841da640d0302648140d071100c00c0c1080740d001c40104000030f0051069010740901e0803980c840d90b01d0705803241902801c9400910402d9400481960f80c0c0015003001c0c0d01c00844000e004c1d008000302c0039620007160907901c0784100703001c45a900298205c1d02e144140300260f244d103911000d01c4100c2a90214050744c070303840c160710300d070b6004a421203540c10b0b4850410b10f07881021010b0320a00066075501d800790311542d01ca201d080601300003001611030483c1c413072080800baa44144c6480d41070480103014018412034840c0c404c1e425105035002c09441d43e100304981c520b40e90702c4000404481c44e20310850000c1c06030f00280000107041c00f251091010f50103105a6080a00641c2d1007018045643c1125009d00302d04910b4002452400d902640301d000c0e8400118161340441d180e2004407a602c08010088821000100415400005c040690ba0410000003080450020405428040807072400035801d481450300700703800f2902030200c016551300510400c00038080f017030304150b2070107068a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 929479046 1250 929477796 929477803
    0xa02040c030902091528050127080303041104020a0f08060f04050a09050d080c030106080c19020717120f0901091502030a091410030b0310110706050a0204030210050a03020d05091e0d02 81
    0x47c00f81800081e25807420580b8404c41805440652032620980700c0da96106040e460342d0050700e003038607180384c03580040c9440d04103030003161030210141e0f5801d041101d42040c122600312010301040d138000b021501114180c2d603103001f01030180312040702c00989540c192800700d1900d1181c20582e03051042013800c00c010b03202d024040d00c1c1140d540307081c26203003035447d200c50702502d12481015602801c00307518010f4000e6400039100041e05c0750310890041c0741010b18031041c2c0d23540e1620203000210400b001403090a01c50080682600c071410306140301c0490715424807041141d50348664000607440401c8052520394842d51410040c10590700600641b1207070004940e8450010242e1003d06880b401280700d9501c00304a107403110220b07800100b05d0360040403891929a88081c200750b940504001c041903560020340308aa0844c0d500408485000a6440c4182e80380d801420150090650034000d20300305625902885d84118050400392541c40424144a0190440d1500b05407003584090781290b40a40c000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 929480296 1250 929479046 929479049
    0x50a090f1401031a0621030a020d02012009030106030c0b070c0501050405062a030d0603030e0f0307120c0308030f01230a060e2d09090c030a02040c030902091528 71
    0x18210004d40c0e03140c0000c03411548004180f2401310759290034041c0c07110008006004080d101341e003900e4031101c01d243c080707003a075880d0b008915461400d0400c5040000101d402401c8450b00a4008680990b50740c03035506210440c2d610401341c14030000384020401c0300d6407154002420003420041d081c6070805010410501a54012030b1090140c4800b2031400a9050891840c039500704088950300e400c20302c4d00e040900a548401c501042c8030341c884184518024000b0703018100054018003405180641d010b580d0030004900b541c3e140910035011011031030b14402103100b14584180445254588644030500000d144182211851a00d00c41b50032a5603041c043c4c01150360074a0010402d00548000a80d00d503c8000d140300d807202c000c401203406030034451aa0400da081165100559a1070880c000c0d16a280c0c1a0425803503000344e142d402c01480d043d0301501520810b4a0300140d4811950301280001c1d0003a2030444032560358096265035031a221300c00b00002020348140003981484245050028a00b5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 929481546 1250 929480296 929480333
    0x1005010e0408090f030a030f022407081906090b1309020f060d0216050610050306040b0a02031305030a12110421050c0901030605010501080601141e04050a090f140103 73
    0x240f0050190383d00c40c245000c01e0002010341d005030541d071501406008180000001601440300d4000422400841400060f42000b02d071407565034420008440510000340414100300b503491689450100520504010b810005c9000440b11b911208218400104038900d000c0d1a0400c65100010780b507142c40c42c0f194141c01d49030fa986810a280710b01d000303400740d000b501001c01165441502400000200e40d80100c0014814900c42502d5605254803410101c8014000780ca038140480e41c031404a90040d941b01c02030201d45a041200350b50303400c2c150b9000c0302d102c1c00003d0100d0500c8010004910a03c3c1c5070440703c9030014a0540781c450441551b450080c1619440182d00e81c040302130000600440006140041c252040c0d0b60f183d14080d030042c0000e026283c005030744d000c000b8040f54060a22054001042d4003005c0c1001581c400600005c003d061445080f0b5a0500002815841c0c0e0f215030006012451800704040d841b4511042c100d800c90070114404a82c50750040000c2545180d5540140300c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 929482796 1250 929481546 929481563
    0x20922060f020c030a26010b0304030f0e0a03060c020d08070f0c0203190c14010203030f2202040516030b040c0906050a03090c030f03022416030e010e01020c1005010e04 74
    0xc004580d90000d00815000c9440e5000c001900034225602040c2c040c0d40c50b1070b0400d21101c05240d500d031b205207034201f405200f44540c001c0000c00d000c80e000d001c42c10a20302d482d140a5040b10a800d0119200d41c001c1e620444080d5120401c4482098040c020038a2050807450994142e1524003001800b8501e108100028086900b10400654809001c001ca40c01c51200303c25004100b14900350b45100b00354450f8070003510106100320544d40c800300c200c07030058030799030695611901c42c0c00e01a4004002054400400e0390b5450b800e20068940c1d0051a104000110110100900c4164040c00b502c2c1c101043d144114980301c0d0201002340c001c0688070942e6074902d031442e202ca81c5100d05030028510108041c141500b002070000400c00724000941409109030309642d520b180721280e83c2c65441c0c105001d20b0980c1e01d4034002800c07102803046504541da020785400720722150414109802c50b02040207182d070b1070b5000660001d00e09010480954070580141e41008036601d807122010346024003500003480391b030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 929484046 1250 929482796 929482811
    0xe0f0a05061003150503030406020a050f0d0e09070e0d05070611030309032505030f130b030f010306181e020f01080721090615030c0b0a0e090921030402092206 70
    0x208804c2000117417001804603651161070b11030103940c60400140480703a91003051681454000041850000105192113868814225400304100a10300070441c00800440c64055803003540c400c240586500d01071030217062030b141014802002e0204004500700b59134020800c3c044070b8000082141c01c42e185e002c0303800c0c0280b070b81225081c001c1181014050104d102c0803a0001c0c042e0300342001890201c8840c0c500f8505150340b081d02d16120b00040300d850850941e00c400420100b2002c4c0c00040d18105555402c580c0300e2081d0740c5414009035402c650210714405440e4180450401c1e62084038154001d080030800b51405c0d0b14024131592b145000ba0005032003040010005900540062142d503901001c24030406058107112400b0101510044c1e601c43c003401c10001343d000030042241d813031140c0c554454501802d04420b1124011028028450300e03c507040700d090b013890012200c001901c0b00c243c400c070b07900e04290040042d10200984544c0d81d440759684498840b80090340d2101c503d960124000c60201e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 929485296 1250 929484046 929484071
    0xb06030703020303040303050c07050f030307030f140706021201060212030103110d020402030108032d090d1a010807090c2d030603050712021302030714030a0204050a0e0f0a05061003 80
    0x6490784025018030012a01008064001c40a08500484d83d0202c5400507030391400c200d20703012040a5190581c00810802c0d010a2080803811032214050802c040c00302e001c059030b02c02d540d00c40581500c1c902d03808a104145140b00c044030500400451009181800c403003418021345220600c4004c2c40014901c2600001b030715010300115076070790000d00464681d82d4407a2401e8032030b400482d080b55000c1c2003080d101e4905203a0031300b02c3c3c0b407080b18200306030400c0068001d00076858425582603482150065005440c002d40c9682d0034040c00c15400513040c824a010103c0c826107604881c01020b0220080a011802c1900030b081402100e80900105100784d01100590080c080e45d040602a0b00841901041d440000030b00e200c20344c8c0c030076103404108402211003441207020544403c4001031201e20b04544d4008280c0246030880c40c60307900145402da503040010200000c503484084564000302c104848584051500b03540901101010b01c19403402400241d941c0703402003214000d06079115410640c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 929486546 1250 929485296 929485303
    0xb0a2106060e040f03030b10091809021216210602070f15051f08030306060702010909060311011706030c0625050715090e1b12280c0c0b0603 62
    0x10b1000400980741420181070880113002080d4040d000b1909050401c001c605000e441d0501d001c080396120021242000f4a050000a86080d1000c14989820084025968a56001d0031001c003e100070034040c1745001b0021800841da6215000d0201c070030181c89003803049048800840382d80440c00680e20a003070315210103a2613171410081d1000f03600002c0e099894030113078012802880c40980c6010b201c6071003106c906030540381c1c0c01070a90507001440484c00e0390829402410321144141040c00029403100000c2d4200c90315503001752070f81400410180c4007540c10a004c6420754920024511151600d5408644d0300c00c080c10711540104400141100a406080020000b0026855041d070314041c107406c200d07035207950070b00950319070151200f11000401d001c1c3c0400012a02040c001000a076903440503400010b0141d9010001e481c020002140380003070581e10b16106500043d0a81d070440c01180140b18041e1510594419a9140007010034407160400040394815601c00c0703441950b641c4540200e401d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 929487796 1250 929486546 929486549
    0x30c020d0614130209010b090102030d111c151a191101020f030a0b01031803052109160504150b03090c0a180c0c080a081b0a090305010b0a210606 64
    0x10995400b441115a1440c6101d0103d6000b00c42c15085a40c0b6101802e800b4070459103c140940c0c4200291051005160407580c01c1d8402604c42070b00b0001c0c44604a2501040704035440525603641204588600925808202519a8032400300e240881100f44001c1846240500e001c945411202880702501c00c49400c10800d4030300000b9500d5448145566050340c005840b8882501e0400c99681040d501c0380c071a0010f0109581e000010060190b1000c1d549903000e84049100300912a40706002448170342d9001c0d0003520954014207403851a00c0c015000d040e015048213200314204001040c0c001d00c12540b400139601100129562a1100810706160078040c038059600000d164800180e1302c3c240c038103510801c0000c02e4050024200300441103902014195009118100074070107410040e10400c5100c0c0d004412002e00440303c050840000015004640f00d440024800503041c01004020f016660300072105485120780b060400c01c84d944003200b8920a2090501d40e0b04451007070100d02d811030720 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 929489046 1250 929487796 929487821
    0x12030e0f010204140915060301060c0f0c0e1e010324090204050a022718070323060310060b0405040b06040b0f040f08061504020d0908030c0408070503030304030c020d06 74
    0x1580c65907180200140d041310808003500c24071824001920301d41e5a4800721098543c0285001d02d1070b82400d43c1510300c5443c8031070903500c0f2004045107400194601c0404800b0f01405204804c1c13a10f071103c100021540c000c141081d840c2c51542c01003000a94000e0700f444509600352810b0440c040441e04e4500801c030020380a50b1040c1001c061000e0400680c2c014008040e912110081d05034005004c541075440c090300d0a5042407010102103010f25907154503542100a900e004103000c240c100840c00d21080c0e0000c0452107001c413200f031003111325040044c0440c50039000014006c49103061401046400745110300c41c0190303125100e0030100d075548002c90300a8910740c1c01a075100c50400d10b190603e9000390140907804000120040303188500016200c0c4580c3c80c120b00764404880500c10311019401c00d40c03150021688450000002900910103144640e01c0d01e1002030b1150b2610988518240142d400303540070380c01c00c00500c408242e02c003d06a503d40e0f01910600c1c08041c50b460483c000700b12008142c07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 929490296 1250 929489046 929489051
    0xe0301090b011401050f09061810020d0206070908070e06010c05030f0a230d09080904060303030b0307060801030b01172b140f1806041d07091212030e0f01 68
    0x16007006101003400d8140c0f1a00c00da5944070303035034410040d1114810103000320300d060020b2254128514080c4006c04900100111115008003218045580307141780122290140c2c0041042500035a810000983c0c010360900c3c06100c1c0c149000301c0180c5540ca24092441e40301900c10004a059001d15249548158404102c035590720550403058140d4003c10074032130015007118007000241c40351f0300d0b42c503041d00d2103400100d203848401000c600090000c0c0340301711074441081c0b050b90f1341551103100d081d000f1030285c0c0b00815882042410541400b280da000101480302d80d00041c404244c10315501815103000440701e0704000003580301c10340307400d001d0031181e0010b00c2c0303014070b0581200c0703040100c0d03214404035110040030740c10070048100c05001d0f6403142d4420b18401e00590740100403681500b9140000649001e20701902c3d5000720304001c5801c091701c0300036511841801801a4001032960082c83c40d813002180e238074200c3d505e600c10308804510205c109034a0701141d42041006001e5121840c50a8008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 929491546 1250 929490296 929490311
    0x11409121b0d080a0e0a0f080c011b080307050f190903152904091506081b060a030b040b0d03110d210908040308030901151202130b010e0301 62
    0x815034400340000e00c0078505034050380744242410064069022541d02c90380880c20803944100407180f0300c080952160303020070300c0c08001401c0003401c05031401500d5584050481d2441e000000f40031240d048106282c80c2c4039584407600440d40b1941a290810717454170300160b80d0805808440b49600403180e00000107901c031161403c1c4190080c0040003200c0c0308000e002c001c1c41c0340e015800b00304d5402c0e8107a14546914240c03200700d034240040f280d80c5064001803000948180c0ba44074080400c0007200d00344100e556414007030103029410010a83d6062401001107008036101c1c005c02d480303000c0c0a00110071f25440c0c005180d0300d590b031600142c0c02d0040107004500c80c0c01c0281002070046005203000c1109004005107400161711070350f400e400c40b4082160100007440c0307a20100c1c000380841300f82541c00c140c0501020001072101c900841c0035100410011828040030501c0c0f000220990b40f0401000880012000060301e803d110000101d4001e0b40c00150415103500580700000500807030350b0700d075180911 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 929492796 1250 929491546 929491579
    0x110c1909020f1209010e06010b0c1203010f06110d0e0105091c050105040c065c071508042d080d050601020d02300a0201020d0f0515011409 61
    0x500b01c94a402443d40701940c894401c01400c0b12202104907515401c840f0040c0061104403005205221140d011120f41d452907181c2425980c000ba0480341d01840540350400601e41e0061001c240c08800030050161003c00d0f100c003074404040c2502c02c5051100200344030311655600c0b001c242510382c10521080100d005807074031034000d100495046480203003108000c10f40c9403080c13059804030010302117600002d82680301480c02c7c444016202c40b4032440060704124481c80220403070f00241200d946141850060b4140050410310650400c3c003043c4070030b414511b041c42d40803800c40e4000781c02c01c04a22200318512061035810551300854000120207410309010403640100601d80c1100d0514100081c0d22044c2c01282c6806860160300d0069001044105481005513840b402c41001303040e0485c6240b04c0e0b5400031100340c201a00040260354045000303164502180251310141601c03613130820851134011401c2c41245040b000e1a0b0400c1820070b00140f542000c24116400f201c0f00804804083c995140d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 929494046 1250 929492796 929492827
    0x603041104050f1003060f0905071215151203091e1706060916210e010e010501051309051f2007051b0303090a03060615110c190902 58
    0x8440c9030289140030b0014055442010720a07000300b00440c1c1c00c0c1c020038036544070074010302440c4155000c100e80da080c8503000030f081007103024014003884609020860150400009000315040717204480d608140c0c5100c3c40800d203031002c00568090343c2c401c00010449050031100f41d45542c000000c00407401c10111346004a81c085141240e4480a0381031a1850341250162520002c4c2c2c1e945800c064180081090000e4084070100800d44074640090003010443c0d51001d005142d510f0646015513401c958000e10000703006a03074509070448020700c429458040070607002d102c10200a02c0c0140d0b1134003140c0400c08144248a40011107101240e101c2410b420340307800810300d44003d0400c0c402103018107151807096100340c0b807240b9000340140c064000441c1c40569602015138000341c0c540404c10817203c4a54a600041c0c1c090740c05130f54001106da080c03041010076501c442d0000030510032543d0341040901030001d110440f001c82076550454100d103104080040400e20741240d800c107030002c110800d840e020107 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 929495296 1250 929494046 929494073
    0x1303180807051306051003051b032412060c0307020f010e0114090604030e06210901050106020613050616030b1c05010b1f1d0301060602070519180506030a02060304 72
    0x1c0f01c044600780240c590030700c2110703e1031140079004601024902c13440717806680700076400103440080120b281048902d4640541c01180d1000c03101d448401d400350886119005171035098816074140707a140c40610040b50369900010f042d403d8903440003002402e10341c800c2c0043c039400c1984030000c0c0040e502c5080340c64064189809842d850074141300c00104108070000d6118000c030f4050b200c5580030711b01d01c814045541d03c1110354086800c0000b182189203003804105900c601041c100020b940e505100000707040940241602204420918a201c00b1a0000c40d0480e00120b402603640c0c815080b414060307028040c10400b0540c881000b084a9821000c02d10300a4201c610810081140c0d2001d5401c02c4507408401c03004244e005044002e000b0818080c145818040c00c550361004c010310081c50002e4255007642e000400180c1181c00204924201500e03407840108494403990000f6090030240101710b80058891280f0300d441e003000c41d405440a006034005607802418055507441e045c00e00da00051800b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 929496402 1106 929495296 929495299
    0x32d1f0e011b080a06050105180103022203050d020f3708040b1216020a240507080708070e1c03030b060301090504021017130318080705 60
    0x1641e0200b4800d1081d68400c0d041d490144a46015140c0039403000d81440070500044c6100350403c41c940c501004280b170016100c42c0c0c0d02c1c04c0628001000904101090780400c4080f0900401040c941da0703c000b0380d003ca8050150752407005540c1c0c80407445104244500103804408115143d091503002c40094641016200c40e580782c850542d4802d0744a8100c482000451a500c41c10440405501c910303c0900440e0320510350718041c4d22032002c0d000c01003542829000002401c508071006580d2080300c0c1c1070030801c924144101030300c4594155540400309100000041c0880d100b20180c40d1a030340050074902034040000b4a2940030002c0751411414981c0b11030602d5a0364864101560090030600004142403e01c1d006102e170348000c1e031095104101e2030424070160500c5c0f8064254104004900d00c0360221541d04088601c41c11150486c040592060b0000414140004280056810 = true := by decide +kernel

theorem cover : BRFrame.Cov 929316546 929496402 := by
  have h0 := BRFrame.cov_init 929316546
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 929316546 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 929316546 ≤ n) (h2 : n < 929496402) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
