-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0846
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:08:07.551597+00:00
-- url     : https://prove2.me/submissions/5adc69fa-254a-476b-8d95-6f0c23736ccc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 151978417 ≤ n < 152158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 151979667 1250 151978417 151978439
    0xb042108190207050f0f060f150603150409050d112a0303120a0603030e0d0b01031e020a0b0a0908150106120e0114221104090611040e090c0406 63
    0x44101086107040012541d1100d1500a009a607801030540c41080c414078100c4000080100b011444641210f8032a9a000e18441004038140c5a052541d50b0b20700204169140c0000916400440500591224101440050300755000404181c1366600610101c04003075520030b19900030f005810340208441c0c107108041400d811000304400d00d4280700003a0b184403030394083c400c64a181091100c1983d0f942000713140500105154803040303002c50700d56489400706e0309141c2020030016400221460540e0302e940c659418248a07006a9503680201051000050f9140384851000d40440007009031940b4480401400b542d500c0d801220b010b038000d501880c00151020001c0341518282d18100c040b0071603880c0030b03030003900030042494029400c01445c03112a061800010340728407020001943c40824031000ca500e881000c0002500031070540d2581d007803500f01500252803081c812800040c1000f100c00c00d1003040d40040d0014a8581000014010501d1081005100f80720f412034082150301e2500d125601 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 151980917 1250 151979667 151979671
    0x506040f18020d0c0305060f0f0115080402040506120a06020d0b0f091620030d0c0509031207080c030301080a0302060a0b0d0213060506031602010f0603031b05070506070b042108 78
    0x4810a4404281820003407045413910055a00c44110752060074014000c0d8800c101c101c80c5107200c070072402c0c000038549440100000b0101c40f507032a00007883d216a000c0c0700107090000e0126070440d48041114180172400c10003500d0385800307a400140c0720420318202c0001c1d510f40724049441110b50000116450f512003415540040d54400e0a02e1807850f518810344507101a0454002d9001001c0c1c80215204400700080050448510f0f0030825103003100e000341c84a0003a000401e030144d000c000140c0003406014000c110a6028a0501e4105880351a02d1880e6a200b60060006600601021400c1540410005410920852044c8408490350000c2007274800741c00c2005e8401e07105130f6164071a0402d160322201c054500601055a00d1804c0c503019844410144e650400540c41d1078910b11001d5810300c9444260b03641076603450f040d0000400300003440c03034034070030250f501303000300d2000188995541c00204002c0d40309140500c0145013505002c07071008191030700e01030418041546100495886a1419 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 151982167 1250 151980917 151980919
    0x2918060a1502010e030301061e030c020304060c0f080712110706020303060d02011e110708120403061d030a0309021005030f0703022109060a0507050408030904050402130f0506040f1802 81
    0xc4044580750080b80982598016103106010000021403507a42c8041b05140105070b41040804620300c280c011421900c4141c0c044005801c02d10041c400b00d4400d01441403154000c0c0404848907049445584060344113071401c6031245c4d4820241400301d50001050030700800004060182649040006512444010841b500c9502d00d0b2103013004580c0550701c284480d016460603d089280c10810103400c4840010b00400e06d446014000101900c00062140311a58180304003400c040c42c59803201c01518001400c2440c0c414629030014a0000400151014403050394011441c0a15070050220101d40d0840f858100b2004100700a480c929280d81c1c03541000300c3d490016a298280544046800310300e110b601a0038000c0c0050140c4520300240480c040d00355180d04100b00d4898a40540d2544a140300325055a042030200c40410314090b80700301d911a001808409020240c111a00110b860b001000901c40751346000740041800c0c6031042c14070722002110f0401072600a44800441c96220400007 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 151983417 1250 151982167 151982189
    0x9020d0c022a061204050106061d181b0a0201021e0703050306120106120308061807020618100e0d0f050f1c060308030403050403121b060c02012918060a 67
    0xb045440703410443d29680744c10b1200131400d003400e1624a010308410700c618800220820001c10110101c00b001c03420090004003202c908440c0d9018801f21a04014040215103028000401810340c5074070003410000a030b0344c00140d495403240c503030103003e030403800c408045c01c00184070070070003e034210003200d8110380e0845410a4580c1c004420314050312051b003219148100c1d0f05e55010416802800e00c0c3d0140c441103480000300c0c41050072000c5a48800c40b0100700590088001c00c40c2c0c016804041c4400400200c140e405440310003051a0580d1906102d20000703902c1100c031040c4007680401810426443e83c07400c5858140702168801607030041c2e9001110f05460100740c2801080561300000c0110340c07260070f01c2d489140a0802030045d4000c2d1009a601321610688003ca5a220340c5046c0002035103c89882c800031142c0d15490020040704031208195981d81e04044195841032140c0b81c04450400782e400b48030040702c002c0c40022449011f40c0d4444403010030910041c0c1d035400c4180001d4070003000e01 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 151984667 1250 151983417 151983493
    0x608070f0f1d03030d0c030501080a0209070c030e030601060818070509160201090b0a060e07090b0f07060905071e050a0b1e1201030f02090c03040507030b060102070302040609020d0c02 81
    0xa515002d1580410180d140c400003400c03180c2c04603140c01c1001c403820691000c2180340e03601e210301900d906e21003100942c80a0000c001429040c000c1d40c01e109114001c0ca0415045515400880e14001007a00300c103020034066010031003007010002e00c2003000420070b4003400701603140c01c0c0840d180b0400070700070345009055080b5155000b8400d6218036441c80e04468915014140140307118001c1030240181d00c8042c1621000600c0c0c1402200200708603101c00c61403620b00720703441222500581004008440194482841e54045442001543d000d8642104001c1c0c80310099004c403a14130465600080c001c86403480c0400141181d8026a0060540b129903400c4103200781c8050a032074443c1aa1034112401d07a10004000c0c8030071080030680e4144282c4072410079481d001c004a020780000c940090150340401c409000280d000d03180290801418011640145e845e0b50000e0260b0340c1b960440220140d020866035a144041e0080c00c0c1c5842050014050040070075808400034a03207049290101031411003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 151985917 1250 151984667 151984697
    0x1b120204111207140f13030309080703050703020105091c030e031905060402060d020c1002040501030c0e1e0102280507050f01050d020306060433030516081e0702070608070f0f 77
    0x81180e03100c591740c40a4030f6035002c02c040c25801034441800182e0010300c1c40103020920a10004515003500c0d00000181800b13807542d80115082d504c6640c400b5044000b00080d0140d512030104100155803280d03c900b1000d1200c0750905280000200e1108250040c0c003034020003164010804503002038060300c5603036458480084910207803042440b05150391040d60072007a00005142d010b48180d5200b642c090180c400d220030121415032025401c0b980c00351484003412602924100c0c602e00c0030078180180c0c0e00070000c015851254a116070089500b0f50000c0d207a01003004024407001c0080c0c00704449800413044040002046ea0140c01c15410610740d0000120750240d40381c100340c400411800000750079170280d204400e40700003111410038500078402003582144c140607004281c850000d400c04142600302c4468122000307080505000c0e420324a130080c201105650b558500c0c41403585030018100c15140400040441d00c00510b04000c22428038072000300503038400514062403c151422034000d0346121 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 151987167 1250 151985917 151985957
    0x30201050c0a0507030b07031b0914041113050f120c0909010b03060a060e060d030e010f090f031a0c1303061e0c03050601030b12070302010503041b120204111207 71
    0x403003c0c0031445950000010030802070316492040c6059039091213a040107045940b10307642001581c8011929034501031081a140360000104104020b10200311020f200c01040342d00c0c1d021004103550070400c2c0c0c2e0284420b0070035503526040c0d5001612101150340b200f8502540b80c40800c4500d81c492001c0f28041849000301350031907185420028103036202400c2c810040d000509142c440c00d03101842410004000c0d103010071400241c0d680640700c00072040741c03003001100d022011840c1503080c0b000701d00020441685d1301c3c4052010f14820200350312140107003e106c401e0420014a2901c0b0310800300202100340b1042100881201c1d40442c0100d000102109500c540d01d440140780ca180c2850a6001030b041507140c0c004e2405100207807403c00c40000ca89050101540c0c40d416130380b103a540419010001940b040000b91b074014010700c00c1a0505441001a103480015030b07101c00159032a58030070700150b2600c0d2180e030801c0c440d00400d0070f1610b000311407004090f500080421080c801d00c0d007a0890f005240c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 151988417 1250 151987167 151987183
    0x12603040510080c0c0d0518010201050405100f110d02130f0f0317070624060905030a0b060105040302061b0105133201020c1b0306010f1502150108060f0a020310030201050c 76
    0x442c0c1601d00f42500280028a150000c0d80c2035408d5544402e1904038a50040c07050900540d080300241000745040141e810113480105d4200c00c40c00e07600c0700c0d454200d2910030003400c03060310540f03405a540c41002020404581ea15001800c82040303d210812070079618100740c408482c0d229441544100c1100165a25030040c48000b500ca00d05082c40f5402c0704001c200c0c0d480384200140710702040700e41c860000b01c500302d00e940145905507000c901c1840100f40c4600da0241d00040c1454054503145d200e502040040d040940101c0003403200450071020300d9000c0c06603d5105448201d400d03d0b6a08548070000c01c1b414000201c600002c00060070041404500e0b014024182c0580007503585240b1072081680c0c0d181040720452a004a600090310185404101c1c58100c0d000140007081090801450941402080503c10103500c2011a1781900082c85c8419038000d10a482c0509610b20304030309104801b81000303007101d00040c410410803200e41d032200d24030401d0700d4080c42d210f920740b00300050980c902218 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 151989667 1250 151988417 151988437
    0x10b1c080d090b06041b0c02010305061203041e1401091401030605150903010f15051c0203010c0f0225140d0203010203250203091c0204090b012603040510080c 70
    0x100030800b07003400003038502c882c040da200791001c200c420245035a0000410300454190001528002d0140266120360880c40d0814030050000d0b490000540c04103145074804d610662038861800181e1100050011300d00e8002c01851038404414006400004c00384182801082c060260803403002c59141d102e507201e400903090242c9221130f0002e03221840d401c80d40003100389074071a41c2040d000d01250704143c0141002c840d030341074450f05294100b00070031900c0c003062010403918004441c00140565000d002c1c100440c0386a4442d80f20003000010000c1c20034190044c0c00012240b015603240c0312007001070618044540300410040c05d62105000103003da11801e2004c0d40c15030004c000d10176000c0710340030707031840c0c2030006000055022143c00007a030703d0b0301540d0086030b8000d90242c0140c0004e907500c50048603042c0300600004e9540d00c2541d0301e5451103001e030070400d9009100c03181c143d4558444046a0045081c0f900118241351030140003d0300d190614410504100c2c02c1004a00090180003d451048113 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 151990917 1250 151989667 151989671
    0x10903060504240605040b0102030f0f0a1b080702150a0c1b0b1206040501170606130f09060b0306010504150b070309080321010f060c030c14010e031209010b1c080d 72
    0xf40c040001c4041c0246008a51081340b9028a002042d0300000480310f1005900c100d16040c54045400302d151a0007500021061100c0e01c003d01424030b0684d03801d240014810038001e07441d55014010310140c09569156107500c90410480d401089400030080c800e00c9500c070348008801440c442c0380c40b41a68142c0d204441c0c042c400301c3d0b18a140400360008502c030741c6043c0d0f002c100507a07031102c01c070070745030b0315100400041e030403000220b0f02c1c0f0f0504140d00c5001d14102d15000c03400003500001c0400700c80c405d40d01528801e0b41c2c0e5004031024a414090a07005000446003031281c0981030746070f10001c1016200d68090020005030050406000b150709000402e1540c041d44d881780d25602640c40c610444500208850110788004100043d103070413008151080d40d6108968000b0075074041e142e0b00d95202050300c3d412480685130410003024028400c03078070b2801018686610b0064103484e510340c00030b0565400740e4140f860080441d221074800c0741c01c40c100b510210147c06900e042c040c9042c460000e2510400b4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 151992167 1250 151990917 151990973
    0x5060f100b04062705281703030405010609051608090a0b0405030a080c07030e1e0a1205010f0501060f08130b070c030e010801030c060e030c0619020601060e010903060504 75
    0x903810000c032004c642100b18039080c00c02540b10314540a080c42d03000d000d60110804240d02c0c240d000c9540c0491400b2103192408400644a807142e500500b00e02c1c038141584c1d84000100b20800000307019010041034205400c0c0441d08080f50b64585480100008504004447c400140a09402c2002880c5145c10585031140d600b010f0070101d480307504c440e65940c04212090081550100400115801c4d2030b0135079140215180728400308130450401c014480748201100414078102e540e100c000d500101942d403a60300c01c101c0c441c03034132509640c003807003142088a140c0b800400c9915000f101e541086184c610344003541c0ea0312800c0003428050000c00151219668000b0007605036005804041d0303040c00381e1540b01c0b912401d0001103c0c8100240401010a5840c0804100d1030303004620051900c00020180c810039001c45010503400e400440200310003100035425080b1042e01800400d0240000d450120f00810000d40081c2070b40800d44001403099a80e040014107000410740c80724264880c2003200c2000f0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 151993417 1250 151992167 151992179
    0x2010509131b020601031205030a0213141903080315030f0d0807110610060e060403050105090309191a0313050607020d260114040e0703030c0c06030905060f100b04 72
    0x30700d40d2800660b1030403581c4442005540c000101a4122644001c4940c031240034240d0469042e080581910311041c0c090100000c007054224852001c0d240700046600d4641c5c0c03070720401041c0c0000786509c00004452600503c0400c4242c412264421100c801480769030040c0070110703252002101d46080c09005050106180543c4542950701809440d41d900c4040c0039800c1000703031143d1040d6003520921003600b804002c894018a02500b6204008080e981440c0d42d0f0344840e42503401c1120401c5481d00009665046850050007480c0046072030009042101d0401c45075201c0c1495805210262002c0800090045c00b807290701c07220701d01e902100b96041414000341c040d540703080c01104500880c9a00c01165401c43e9010201343c005205454804282d074030745113504010b01415900315810a444100c0121268400c210f4013001354400d0791a40040301d400d0503d05900b88846d00041c00301820840140d01003400014401d8104580c0c0042c1c0c1003a0300c902014100c4492168414440000d01240000e40c2c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 151994667 1250 151993417 151993421
    0x705012a1713080d081312051908010e07020a02030307061509060608090105090309011d13050705130602030909040b060f04050a090c080a031407050304090207200301050c0301120201050913 83
    0x1251103d000300c80d0780d0a032414003900c5100d41120f207482103905a42813880401e0741d00310b032000303001e0032818607a00c0c1c2115204460a0314207ca1404404034003e040100948208001c115620243c5440641010002640029228800c6c0103001d02100e40701c054040d8605114071034940241740403c01001b20303e6840801500c41d010071035003114654a001d0005401c2c280200480b005008141d483c2d81400b808101200c0e01c41c82c108182d07d4100c04004110044c0340d0300ba10442d809551583c4519407540380414540109107100e8000004541052184e9591a280d449006401a40c0840c2a280b01c2c0c3d210700200d816402d03602180e503030060030403080c4210361701164494a401c50040e400410b10603112086a13aa489001000600141e01581c00c070030711060140151803e28401d10a036490140c0c0d80441c403040e60004042510a0702540c40d014200300300c9c403550305004040586c000c1c00180340030b0754032165601051043c2c0c10f01c08d54000c4036104580c80b480403188180d8004180020700c40050f008040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 151995917 1250 151994667 151994669
    0xd020f031e1b0d0c03020d09031e031b0b0907170312071106010b1c0209060a0503060604030b100603230114150d050103120516020d0f020607030c050705012a1713 71
    0x17015004055040040d24450954041521b4000100d007003444211000710503807401c0e0321001d1301041002071000e00d9070005030a4082001d80558501038860801c200c4550503d00300f60b021071040205602080d01d81e2101100b81d03842064900d28160303091b41ca0413820f0300c0241d100490134460f40202d0002040074890300010742401908941e12558a070f4000020300d0491068003c05030b40032800b4084065824403a40c0255440038010304264100340d560380c0c590b00c0c1d0180549200c00d24446000c2c0030300a16500d0f1040d04200c00004444082080310212000300181d018020142884c0d24545403084a4992a62800e0542c0502510a0b034400f00750b03054600402081c0811507a65550150049a0922407000e5407050a030303e016034003411319582d00704004540c41c0281146c0706075402c14504056991180640301c0f0714000d840324017806070103103805418103015402c100c1c10b100c031006601ca85041c2b0307481400d0340d82c203440000d2030201009042a8001010b12010840701f010001141c001c00c50316020500 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 151997167 1250 151995917 151995923
    0x50702190906090c09050402070206130801050601030b0d020f12120c0a14010b0105030a020d0f1b0e010906020705010309140d0c0c05090403210605120d020f031e1b0d0c 74
    0x448152a00c3c8000c1c26903c100c844200001c1000505000703501d400c0d4003e2a000d440240782c0d620389241c60111325034244856006000c0d90350348404003c46541c140c05100f0409400300c1b94148804d0fa6540041d11800b25110414000e091003100504200c60810002c41ca811b4545200c41d1207000d0310301c41d15981c001200307003103810b411440c03e51141028140038401072004141c603000d05503035640241c0340085d003010241d040015200c85540c024040d1921444040625004052604040340310780540445c844800d40342c10894004020090a47e020501c0c0c8242c2e042441c011585d40742500340080242400660000b06005483c041040039800c081034540c014070500fa182d6201e030fa07403000c200442000f10380140101e4110001255100701d90030038002000310b040c000190658940c070100f1091740701140c42c181035078807410500c03c1242d010484101100d10ba0300056191845c90048030100800000d8030b40400e040200361010b14120075802600c920400208030392400c0c198480040003490241015 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 151998417 1250 151997167 151997171
    0xf0115121b09050306101205010b0a142713030c02030613030807080f0106111009060b0307080105060f0f011b051605010206100303080c090406030c061106071e0507021909 75
    0x10b454100824824460311040460841c2c00e4500385001f0f80b0400d030f0309000c840d2550703200c900b80381c1503841c00c07070640180000c04004003440c0c242d00c05100c0c0606081d8480c0005007540d80e85007006000e800c85c0950f0142003110b10342420f17000351800f511072200c0108000c0d454002c0d1720401003440500303010030415900030313503801503284c0b200c0006030b804c5241610240c450000340c0340180156801502280c2c401c103000302c115203002a01c1c2c41040101c402016007202d070261110103025503840e003080454050402c0360001c0240341003840c00260031144c078501c0c0e903009140105035101c0356801810080c500440500b1161022000d85c0382c200d844160440108424140c0a040070840d948005401c620945c080d0300541d40072800c5450946207850001d2036032005040820821245442c1e07800382e080114072070421080700500b0001e02405007118141070480c251300c00700400643e15032000c9000c002c021800080e00812506030010ac0b0b0300c0c03103606401703904121246607d0451204a0911004031511000f01b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 151999667 1250 151998417 151998419
    0x90b09010219051603051b06090604020424031e020a060e100306060503060111010204082506171305070509090303070e011128170301080607080f0115121b09 69
    0x10580d124000d0b42a22041a504d000681c40000d00850040020090030002010803100f03040b81d00e450040101e80340065a0005000e01c030440c02d05000d000e00182c1d00b168282e510700c030010300c080410324040c440689483e51016501006100e00c02c050480c06402620803600e094481344060018240c410b0728500a85520050940c4644607100e51010350702103599517490740e244e203070044a8403291440700c059555801c1100040ca800c00f01b09047c1c03000c0c01c00c480c0d519101040024480700c09110343c05070040c0604507044d18060a000583d4650021a09810190050803410050301d820460380045401207001d030184907001300c3c008081c6200d5003503652072640d9044031500458104d103c140d00c20b020b03940544500b24200b50300088c03448a0b0b04041c00103018a25654032882200d465581401020400000051004840611903c0d51180381d0741808042070808218200031080140318030044030340754040c040600b512a88040c0c0890300510301c1402040000009880f03600341520740000440c0d02c00344 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 152000917 1250 151999667 151999717
    0x902030d1d060f2b15050108010e130f0503091509090601030912120b09011d070c020307050907020109211704081e0403050304091b1719090b090102 65
    0x4100c9004188401c603003803c00e080204800d000d012100c4d1401098032203000c110141c01d11500c01c240201d581c814004502915110000d0261101030b00401048150282040f00e1144503121046000740d1000e0141070102240c1805819070080030400341c3d1000030a030380042e8603401c100c084c100400342103901c41d003151036040055040301d41c05d910050810540b1078103101c405020b0200190342c62100306003c10508442000101d22090907046414248040540c01a100d0004100a58000d8a43c00d15a5410005400113540c40c011840b41e184525844c0d00041c070454400c0d0400c0d001c8a50102801c40a44008403850390b003180c0d582031400020b05440d03450306568055004079806a50410002c034038005040400e4008907000c80178000590350100000800524100010402800c444500050b00c0024460381e0b059100b4200040040188208803416031481001c82280c2164841d031102c40b04032078401c2c1910180c40441e4001c1c01100300101005280c2030190000c010310520918440c0000e55882 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 152002167 1250 152000917 152000929
    0x14040209010f080c1e070c08150420031b03010506060a120b041b02070e0c03160f140703050c100608070e09030d0516020c03030414040f0902030d1d 65
    0x481140c0c00500790034820102c0c5801002000d4206107111442da241c05204156801001e113a04c880351000040010030310300340703c4201141005011094042d013041541920100b100070000780001d44025140f2071010b003d4144030003448082c01001e010f5a203200040004c1c541001c144454242c002e500b8440080d00740d00d054821207014280c142c407034cd04c801c00081e06c128020014251041e8100340e0303840c0c071b0b001c440c05000003021901c51240c1c01400400e01300b081100410001038004a441a42882407000c00f80807006011201c4c16031707181400d421a000c490844440ca184c00084c1b1b58003400040c00c2d410705602000500c1070506940c03ca034644646a0020000c550540c0f181d05002e802c5500e0510840035603c10464110320740901300c0341408407100c02a01210016030f85680b419040e100030246154051050f40c0d000d90044002c1c0d410686410b102e0340c0c00d80c00314807a00d8403442d03640352500d80e0706840364003101c00b098001e01140c05058081c1806040b8441034100029040c015500c542d2407481c1c51 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 152003417 1250 152002167 152002177
    0x60a0e0c0a050c0a0602040314100504020105030c0705211e090607021c201807050a030c02070b0f0309120a02030d02030604090611030a0f0204030b041e1704140402 72
    0x4444880c648484180300312015084038418850a001e8100d2010100d0303042e001a00c061030140c052614645401c5004618ac4140d03020f51421076410601040050707a00901902d5010540d03000e41c556400c81c5190031400e04a8500c9140b8020300c01c020303190f0b404001c00002c0c02841c4240000074580701400400c8590b64050f15101a40c4074404001c2e00f00181030413082c3c403a00410414075191110129500d0750040205140383c11030303044000d0803640c014602001c9000201d0040d5218680c50300b05a44001d006100da1140201416141c460300c1103100d2003000b00b44001c1462030206511075900c5200f801c2694000c2d5524038aa01c14140402d8064000b1802c8443c1050070350025881c00103034000d032074060f4000501384c540c003c0ea90410725011406038019103220112055425030740340b03040800c050803141c841c0484103032288148030a000007802c1d0b51b41d103604030345c0000701350b20106901000011104c54882d80140000c10b46120341361300c2c10204000c2c205648201d004145203000340c0041c00128095 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 152004667 1250 152003417 152003431
    0x70e040203071a121e060402120a0c0e03120d062408180a050616110a021c12020105190c02030d050709090204060512010806010f060e0a031a060a0e 65
    0x4040310070000440f5901a8990030184810b400d402c0c5407034000b1585541c0f104491180d1040c180c0703141201151000d80b211343d070160301241e08600340f401c00000c9007a4441d00901400c0020350380e03640d081c4a6401340ba000344c00074400174105c5026a81107041429980c0020410741d40389130400d0000b05e014007080034003100e00c52000c0c00904480c0302c12181196400030141c100520948a454005c182c124180301200c00f03503000ba0010041030078102a2614100c107038000b40c1c810425910400c440051000c0703a00841240c0407030340c08407200801070082c06d05183c5550010484801d1280e1825200c0d01034011a20626100403030042071a0542e42290544447da48080c0042e00704112035460b5040d180d00031074010b000f0b0700c0e1810025880c3e140d86800c0341c0c020b800010100b40081019140554981c903418050000440a032a41c0c0d454030280005800c8140103c1c0700340003034150721410b00d840d40020302d0f0003183c1100c0ea81410340c080903542141d10000307407032080c0030b00c1d2083c20201d021040d0003030071801110 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 152005917 1250 152004667 152004673
    0xf03021005090102060408160c120c05040c090303030b0f0613060806090402060d051003140f10060b03071b0b0f0610020a0203120f04030c0905070207090b060901030902040e0d020c03070e040203 85
    0x4e04e90351440340da48e104401c6001c0401f2a08900e2010503035103e05100902a002002e600003c002d00b00750700a522203030b1016100b0350a245410841c40d078031001050482e40d060501141c082c440c1b10003d1038042c1b005d0445500035501041d02e0780c01c1d483c5d44074043d0031501e040e01d581840d610b540c0d042c818001011500030390410340404c071184194074641d1102d540808101019800c00b922650b079910ba801e030703221820307000380d202c01e11540e0248c8080c41040c0e039080280c5020000c0ea480c00c40c640c0c10714040200381000340440c940840385105c0341880c0f145c03140c3e58000c1d000340ba540381811070310016200649815000720456080f400d210750000980004098004000303000c26141110b007000594003198569004c81c1d000d210004c001035280801d00301602c0900d002113660f00d400180240341c6071b41a0302c40650b440c03c1c503d5540d20b588559003240c2c107214081c6008030715880e031800460068030013026116400d00c61620140801a40418050302c2120128181c8050540c0c820f004190b104094074040c1d4950 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 152007167 1250 152005917 152005921
    0xf030f030b01090b18040c021014011203110a060204030302010c030609150308032809030e0603070806040b04020403140d030e0a080306040c020a1704150504081b0a0b040f0302100509010206 83
    0x14180e1005005c8110345003002c412440d08400100d415941c003c5446c5003d40e10481941c03035580f610340551a145000581c101d6200d614003c0004404010010050107101701072801201100003440741454031030300840213558035a96454001d000b41109003850300043d150200210300b42140c0d01902c0e180300c005d420014051421a11078210a03031001c0c114074218400b290001848031200711003c854100340200001c1e80c04501d04024003107512613001b003842100108100321b64550031402894010000f0388002440d40c1400000c44c1c028841d903000034244411528044005100000d09107010380855a130600200c0c40050341103a841c846610014082c8205100091090501e45d11000990300c40b8411035540002030384656200610302000001e18900020b400c0c824041400d882c0c045541451512614003131a1030800e0751a100c950611140000000c03401100950325221014068140403041e250b0b503583e07480407002019a584412030080d400c6400a6003814060400c2c0c500c1d403001078003e80344079 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 152008417 1250 152007167 152007179
    0x14010b0d050309280f03020405010b03130b0c0f07080c07050609130902042003070f020a0b06100c0c0609030201030e011803052206030e1603020102030d0c020f0105040f030f030b0109 80
    0x200b01180b416040043e0134001c40ca801442084031103005096907440c44400b282503005000641b00160800c2103560010814045403805110742d10507103a400100c0d00400d03071141c021000c11032180c42905800362401040d0f034418040900d0081401b051808211105180d54001707010301801620161380c0e115044911800c1c0c0d020b00b540181c00018401840000c003516000c401c40c102c02044450b00c0300c00d01c07002c401c001d103058024411042d01040e40c00200710808056460300540b0344014401c034080c00541030385240041c044c10821103640e45c00800c0c1540b0580b2030300300400c15036992000b607001070f062040042d880b03074042c444d0181071140103141711046451503c00b40c0322603000e450007042845403560b26154000c282c5424070040c1c01700c0c0d80c000c603903e00900440c910707200c90401004500800c0500c03c20050381c0000c121082c80480f00000b15299219800c02d0b03040980080003140103500f45030401080004e16110071000328030949414800a441007812822a02904103079408119400b00031f2102d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 152009667 1250 152008417 152008429
    0x7111c030527030f0309090a02120703020702010c0b090105100902070510050601050d0504050a030e18060906030106080a1505070512070e040b0303160507060f08040602090a03080714010b0d050309 86
    0x14200b1140c4010b0080200307008a490b101d080103056059410215101d005880d000b000c0c1500201c0581c0c0550801406c445040340019002d0020700600d540000c038802164050118000d40d550813010502d014036202c179800e0302070b1004484005d41100303941d002282c240e041c0d20075038110982000080c00b07400c0c038170881d1100030407001d004607052080600501c03040c1031107400f034903124034454405000b69101a01c0e02600e0f610541c19070620075502c11482c3c030600e01c04220794030f0b402841110324440503200c410110340104a590410001800b03030044034404d0001c41242980380c641c00c1c110400460b030751510125a94026180340d0310340910b00340302050710341e4403443c00404503042c0240000781001e00c03400048d2865015403880c0c014000c01500100c10300c881030060100a103c6800c1c00c415590035a1801000304a00802c01002180e0104940c096a1144014013014550100025903107005d10701713080c044030201c02ca10301081c2d0b09040c4012032500300729a2004003a5804401581032041900802c02 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 152010917 1250 152009667 152009707
    0x11030a050318120a080406020706030b09130312090b01050f010f0c0305220e0601090f060215090c0a0303020313050406050d15110d020d0b04090206161707111c0305 72
    0x180c0f085400701c25142c5000203110b1407041d6407003103000940d928038201d07001c0c0c180356030b95100009141c07501c45500007984660402e546d016076080b004400c4507055180544140003d4500104424035141c20f041c100581c00c801141603c1c1c080340c10085001141c00110b13019a0102c5d2034a00040502d10640006030081014080c030b50b01c081031000504e00e2642c8041441d0440b0360041000301156000d20242c0c0d44c0001a0340c01501d01d500d400018141080c1c0041d43e01c0c90380700c2244002030001800039810000038000501c5c8080001d08418001e69282030013990383d0002c0035003585441021000007102c1c6482c0c030483c0e0881740064003048152100361510801500002a004081904c905260160590600044c40540d101703201c01a152107440b0b04c100c0403110400c95580c0075600d03090440015a4441058034581404070b0b15029445149140a83d00c0c3c040000040030069404101c100c02c20506041d80400d41c101590080400b101c0003d80c030007610400280940400c40030000120019001d02d0b04003 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 152012167 1250 152010917 152010919
    0xf040b0a0203090603040b010e0601080108030910050d06120308091c050a021603080c01140c0f0a050409140f090a0317070e0a08010f14040309050402130b0d050411030a050318 77
    0x20341400700001c085002644111000c03107c2c05c0c1c50a005000305d2102ea00781c03540080c0e080c40d00900360b60510604603941e1140542d914401d214421a44081c0c520800c11941c2960360080c0a010790340da601c0400480010040c01100860341d808006500840c0024410200804607194500c03514242c0c0f005440c1c582c00400d00c54114001c100d02242c0c6090107100d0180150f1185080d20350300c0604640003421038064000c941c1c281c2009100b03002c0901c031404141c91000b86880c0c14260b40d580c0d0700e8001e43c4c0d1440340d544000b000070304150304004131140c0381200381e01c11a8512241d40e400d07a50001d42a803074140311500100460400014142034011054841780d11103030b1414000455426200005c2c580905588510760300c2e915030100c0130102681d03018030520310009241002c9030381000d1394041c244545501405010b180d000c81ea420108030035800c100c000304008600307582e60380310003840ac1c03015000468081d40d070702c05411041240b60600007403401540350442c02550030007011b89031050340c10384070004003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 152013417 1250 152012167 152012173
    0x504050403140307120e030a02120c01020705072403020a0203031503010605040f1b02060408040e040305160602070b0105151608070203030f07050c0102030910030b03160f0f0b0f040b0a02 82
    0x842100b00001c1d0003180607820f2622200200b1903000c600c90143c8180582101c2c06070821301000c42c0207130b00010403500c00c03c0e499182d00c2d12070300401e50050080c010340c50050403510800700300054004c6a0186010201e0950180c8148140c103681d0a806034423603007001d0b10040e8401c000203042d6080d00c64410001a00050000c55484e603185c00080a491800d44038000050355103000030042141849190701d041c100b80090f02c0d1904e043d8441c6100c40c0582d00c11944017002c20000174042500c91400c4a949454003120401840b010341800c0e4000c0d00314204c1103458134101ca0020800d490051b0b2461182c3d0f070848850f51070102c2c074503121212101d1114045900b83c070103120f1f00005980c00d201a03ca142440b004041d12244035090042c50030218003d0710703055410401c4003c01c0c60f180c1c0c80d0560500303511418040b4180004002007480c003c140654440400855000401c050819002e070710700b190315070410540959210b220300315961040e03400c4c0e4000c4e00301c2004100900c03404500070b00049070890040d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 152014667 1250 152013417 152013437
    0x30f0901061502072d18020c240702070503071701110a030212010605030402010e010813020306070807020d020613110d0b1f0b07020102300408060a11070c0504050403 73
    0x5007160b103101c02002e00c0540c005150900c000100011601c03d5248114101145c800c0f803121400d061401a000d000031310f2070369040840d0309031801d40440e11992170510442d4545d00700222403180f022031304540381c011340c04540045404148005122400e840e4018090b007800b900c0d00d0a04110420041c00743c6403070355203c9414000c1c0070140b40250100b1511510090f079942c1c0542140404280f050b00258203204082c028003001d45d81c082055919075800b800c121055840e8408010015140010000e5040c41520704001025500c0010a40110016000c4800380d09488205a03107401003114940d1041e010400b0b140302060a0320308000e54000c024055410f40071150301c801c041500f049400400011365840000c015000d000751820007002c11a40d141e09021850f1300003503e66051040150b01c1907800647d09585903000b0440c0c007100585550b030960b48035540d4202a0f210907040714501007a40c41d003602c640c0c107050003204a8084681c0f1862142400c0d06080400c0b0043c40301510940400440c514 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 152015917 1250 152014667 152014679
    0x7020c1e0409052a030f0303040209060604150309030e100e06030c040b04030c030516060e090702010b060c0105150f010903030f200a230703020d050a1b080f12030f090106 75
    0x2d0150820b080d040042481103060203507190598561225010ba44540100001c549007c000d690704180c1c1140d000c0c145448450024069000320f030031400c00110013808401a080c0c059001c0100a0310940310500760281c60342c200070040719140d0241021070040d8071403015524103400210350003a040303117100d804c00e5210030748020980c000c0e401c11584c48946510901c10301c001084080e10208000400540681c2040b000526245240c0742080c01048000e0200b00c07203c2c001e420160840002410b840d403280501013403a806810151a042e41890a02c0000842814008602004080180c548010181c03a654084407480400c072150f40420a01000e810f4000c03042e4411001018411001032007003c0d807071b040c02c0c0c17040c03040588a40562070b000041c54414006c04244001103a0b01115403604446081c10020304048020400800d11914060000c00d4541c10103105001d440b0310790201d0f02041da4082209039580301003803591041c01c0080c0005883c14040264180c0d01c046a48004103110380c0d110 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 152017167 1250 152015917 152015923
    0x2090a020a0e041823070f06091806030506070c0c23011101180812070305060a09020904060b0f0703140304030801141c03051b0c0d0303051b030403030603060507020c1e040905 77
    0x2c0e15080820b00480002039055604209290290040b220010801c81c623002d4090110107180c8a0203006680856082c9001c51017540001c0095030010152821440c1440c1d0040080c51400307012940002507035400704291584010000540c82c0040d09158044000b8005480c2041f801c00164640e40d2100705403a4910140010912450b100b00241600c6a5007000d150030f46450041281c4c04042c0381c01c04101181c1d40f2180c1480440341c2200006039211420404640a0941da802602980c00300041d02d100c048041401040d5080c0a0f070746a0905000347c8100640e284029503018002610b18801400340c40340b00380315004103c000401520b4030407100e0200f003841c0c00c01c0100581c045134011642520f002c6141104c011013643c5180501003202075140080c00c4101d07041c034007404250741d49c80081c0c504405210755081a030151540507840b403520340b800801402c01400115035072070410011420b090700028811078541c00c0100000d520bc1c10300000100991040d07840380d58841d0f2580d8200380480e10034 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 152018417 1250 152017167 152017193
    0x3180c03031713020a0e10050d080406020c03030403030c060519140403080726060102030403021302070203010b1e0409290108060f0f22080a050702090a020a0e0418 72
    0x20782c68220018072070240d9203024503401800209070f0140503003000016501c0b0200041038404003008100240c0394003190386285213007600816080b100d422004800c3c4040701e00600200ca80b55402c860704d0312840c4040c10f88a0055101c0107000c140700d136058500040480d048264000501c50b05080c412a60120100940f140d03925010900316142e0140014107a000c0c8005502620701d04200542a00c0340c03c01c451701070100c00c1543c11148140001c20305507071082c4110750040d50001c0c00d0000c0064881068070096004441c128403941c600140754049040191540c000542c01c035900305c1c072620405d000d00001e0301d0023000413a20001444001c01401d424050300151154040e40e004600d90304214240d4a0601d024106d9201c2210710030420500e40c0882500d6603001b550544056910442112441c8010100d420000c01401d40401e4051080b54000040c2441d18022138130715565485240c5c100c4101d02c10311199100141e50300d00320b251107061079000040080402c3e220b1001e02c2c0c00c161142e913105140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 152019667 1250 152018417 152018423
    0x7111c060f0506060307210e0a14070e0c070803090703020901090b13180f0c0b0409020a03180b0601050f0c0613020118050a0311030a060e010e160e01050103180c03 72
    0x1448890141d101110b200326035100c18160b800c0380c80c41c1080d05000c0c06129003a0710b0900007100404000c640710507550010607007071040204442c08011585401402d551400e80b5a00a51103a880009034003601196000d01600c030303045000303180182c203444002c103e0780001d140d4490307803240b03507070010040e103810b80c1e070b41c0c020010384000046500d00e002c00c0246041803060058080d40c104007400902440c2c41d4080740380d41d0b0340680c9681d0946581d1801414100b055841410011400b050020b0308541e01d400400e484005542c080000c3c20012041101c44800c04001924020721900041d01d594001c100030013070301050010450405c0c484600c2c0c1403400d00d00f101c01c44043d0040403c41421560480c0000c1c840c1700054585508940c00d03e404142080501d10001d0810030f0b8504440304943c03000c0c01232600705034028005004041d10500858007901d904107003903070603114400030801c444000107441c01c00c1d6050340f0700804140e407074400110094803014842d0a2103090140300140000c0b0500310420040d44 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 152020917 1250 152019667 152019671
    0x3140103110f0108040b1f0e04060203040210020a0314031306020f0a090e01030809090a090605040c030c090c0e06070c0f151701080309090a0e011a0307081207111c06 73
    0x20907901400700010b18161558180310603003060200089200c0c0045074042c128036200c10844000020000020005a0007580e020090b02e084c0818041c1c140c00843c1b046000b901c4020b92107150b000d08990350505800c0140005038401207220085000340c00450f04000450034913800701c1e905031200e2081380d0100341d00803181c220024103000b002d0b030880d44c0d03a0010154101c1ca07200941c51a10703800607520038554254401c80128001940c12302e102e6002481550308604100501e14062920540c3c000c0d07103010999081042c0c1e14002010503080c0541c0c00342c0041d0741d0302c002d40300305190140f01150304030f8101182c41400f0320102003000d100c40920f0100609203413400c034520421201024110b20301c21080c41130500f99000c0103000680d400011241440415582841c442d03840d140610018060880344254035401c0c891500d100010011f10f80102c0e100841c1610109503960b61055503d00c0114004450f5403801c1c0606404588502202802c100c0080d003004401a0110550314115080100482d10b41e5 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 152022167 1250 152020917 152020943
    0xb040e0906060405090a0b0c070f080903060c03091506180702070e090c06030408090a0e0a0e1b010e240301090501081e03030105060c0703050f0303160320070303140103 74
    0x1c010380c42c1c114000b902e0070081c608008203156150158884050a020054000300d040742c4a07460480e0390060700114030042070b1a00345810b0304c2682c03001d500356110303110300b8020840520601c1c040380d01550005000300000c0c200381c8120207031041d0082c40c0a13400030241c00c148501c40307104082c0c584100100ea01405065050031110203d5a41c00b0b0915119a8401c106030003040c0c40c1d990440303400035040100c241e102c500181c0080c241e03400c1a000142c0341e00861080c40041074040d0804034501010000307580100c1e482c4982001801d281c002c10034000703980300c4a00c0001d0b0501d248540c1a4500320303c8040380c0c161191032011059030080c4d219400095446004004a9800340300d10b142040d0040d151005212504015955030b000601a603449400d00140b41c60702c420b07040248600440c1d1183c203a6000c440682031b615101c0c0c0040390800130070100034000140c180d1080c86805500304c2d03600325141500c160340c040c0c94559040400100c1c185540c94584298043d0765002c0203000350b200395800b107050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 152023417 1250 152022167 152022181
    0xa02060103021009051806041e0f0c2f120c160e160e0f0406030803040c150f030218030f06040210110601031202032b05010e0402011e02070b040e 64
    0x10710f202c1c0d40e5140811041c190288441d41e60ba0600154440c0e920310a10b600761070b2007000900600e411402100041d480ba03102081e1461241c0000c0e0789084141c8040090403e42c42e02a100e84d44851402201d00c1c80095034280e83c1d03000c1340001c2c072521034020100c03000915411803200c1a58085501401c8a17800100400c40040c00100d045010b000b00c0ea48000341d034100601e03c0380820070444001070900503059a042105d803900d021454a4445c000c10038000e6030b0766804d000c2095801503505440c0400504d00c0410411031010200c0c0804282e5a01c01c020400190b00480080d00301c7e4405264030002460848500d50f0200803d08200510380060700c050f060038410441b48110104540042c4480d0a038602c01c0000007180d05411030307401071440203801e03500d08400c070301714441e5000d4900041300b451006400039243c0c0c5001014800724071000c2050ba62030f400107140c91402100d000b07001603d80646c140c1c1014140c0d00c03500b542038050048550780d94a52640d19040d40140d046a01115008001c200071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 152024667 1250 152023417 152023429
    0x62303060c07020915030c040f0213050102010606090918020904120e01230d020c0319020c01030b0607060b0a0503011a04140103020d1202120a030905060618060f010c080a0206010302 80
    0x4024114140341c0b85465001c00e118800082c000b00400400c4042131040742c400b030100c8070401c400204100011141c0b540a40000d4101c0344020759400c1c0250b030045080d500502c180d1050368850b0300c0d103000c024079208940d800342400030030180354000d03100110030050700c50407038650040c1e104110540e1140800880205209204104241000f074041104902c1c1802c10240a44041d802d255a41e5665400c802040103403140900f00207162000240c003c15042c4032041c0010b0710895982981c10b00350000c0c004606480e031045074158824000c02c1481d0018842d50b12245008402a00e51802c3c0d66a440000342110034440003020032100780899034040d440d0520a07000100903000c02400f003541140c01203403400030b0741800281400c00122006424a000304045d00c84020b101d1441566421403a2005000d0104d5420441f414840c1c04046009854143c1c00340c4040e441400c1c054610f0754594080000c004140a10181031201c1080b07040c0104025000402060030140c0042065514602c14841707 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 152025917 1250 152024667 152024671
    0x310020414040501150c0503070f050105060108090601080303013302030307140705070902030c12090a03030608010c0c1104020706020d0209091803030601031a0306090604110f0d0b07020106230306 86
    0x40726926040040c4071555140b89820401030b054a440c1c1e140071b10306e01c5c0040c61881035100280c1100c9540d000241005015040944100001e9840301c005480d5180619a0b4200a0081400507003085c001449203207440342c80c14048018030002d40001102c2c1d804011030b800b0b9030502c0080182c100204103d81580c00c5040c0514040700340c01a035282000c85d072142c58941c0c5c0a4020041e4503500000441d0460008030706841c00511000100d100a01b40340700c0b004e40c2e40040b2181200400d041c800c0026103000188607010050840e0b480e620b0703031099a41e032030030044614034821550096080c0314030400700c4c5003480a490310000007a00141d5444001c400c22015420080442d02068000142c1602401d808000c0da83c000c0d0081c00d010600800f0240c1c003401501c407a40d174160b003520030282040340b40d034030000316907004900690a2090742c21020060003a460790844c0c1880c5c101c8400340d0240001b1303040c400e059900040714400010460748a0307000030940301d81070b44240c0c10220100c00001181c54144000b80e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 152027167 1250 152025917 152025919
    0xc081c0b0303040305030d0506121606140c150601120e0a02040e0f151302100201050f010905070e01050c1501030f051b011205042402040e0c03041703150310020414 72
    0x60400d444c40c0d5810b6070302d10503288100f03007481c5c94501040c6142c8400c07540b080e005039801e0560328004180f40540f08900703050b120390000900343d14001840d10255600300d840300d031518009010f140c204801030810000000e01454108003010a408003148041d1042e40044104800500000303217460040000340d501c0c1c60420801508162034072858000d0000720f50310400c0044034808019914841252140760200d000a50040408401c2001c11541940f0040c4207211445800410381d032240c0c411b1b001c8540803200c6801140784004980400e6000343c0c090f00360811080222003d08000704458030014400ba40110b41442100e40e4501c00c0007014000c4020780d08410104600541808000030000008500040c85296880d030101d014003d111103100803003800c20301140325100c00450a08000d40c06486514100d00c00b860101c1e002420403030480e0300507030700314861010300101c10b46141d0259001a0001a21060b00e00104500b600c05122441b8894400c40c401038495180c07443d00121190080111 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 152028417 1250 152027167 152027173
    0x41b0603091b060e010f03020c1204051801030206030c07052109012604060908090901060816030b0603060402160c031506060302030403140d0f2f0c0307030e010c081c0b03 75
    0x28054940d002007020010b00092a141c40d0b1400102807d500030b103c4d010076001c43d4040c200756100360644540c010310441390240d0f82d132242d010070302c4031910901d402030000130f622038000c00210b06200300039130180803050b00907820703a85286100c01003142c42521313102c00d02d4903c110105643c0019a00a609070b054902e00d844c107100d107042c0c0001d1001e0b40b100e008000402c00ea54a842e10400e001084083c1c444c00c0c2805041034405507116030019000d00400c481c00c01c021000c031a14607003254440c1c02103490300300c805403505055480c0c1c0d008100c0070390891014051f040c01500104404541c0205034500210300807000c0c0358440c038a0240180a690258001e0001e042c0100b052100080c1d10081d00d98018409604031070b140c91140d8081406001a22101034469041140341d840380740510050b0a841c5450b4034031a2002a83e544603a4801d0150200114980d00148190b0700424081c401d00500c12030145001d00080c0e5055613001f02c5074105040f84cc01d0010405449800400e05100d0250041030460003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 152029667 1250 152028417 152028419
    0x105030c10090303050d110a230703050301140d1e02030d08090c0103050411150405090901092004090b04050c03010621030302090415120308130f0209041b0603091b 72
    0x1802c0d10a840c40010200300e070024440788070b90311325407201c1d01c0c0141e070700c13030a56407010f0249009040ba0000b0b9035034507110741d406042182c40c171000d01c00c0b281a01d0381a140c644c2160700e01402100107280000805401103002884400000c80504003c0803081c0014103a202c4c20a250044c075281c0080d85d040c240501c403040e41400340c10800080d04030b26540003480e0200f1140d44601d4081c074010780011185400c80e07070b0000c04980d240e200c1c0e00600162170303082e1210055540c2e02d00d052400c1e12818040030301f076403c0110074400002c4a804940c1c903210300207040030804c1005650b81d850680422a4152410741104494100c0c5203820b00a4034011b2a01c100c06189543c00d100301030100c0a07460900600703041d80000c00d8642502c9642041503c0c0030800761305900f055640da20440c0031007801104134001291000001c20100881c51605143c0707130006600da0440145509025201c00054000c6d20041020a65041d9528248094001600031507801140e591076515041300b116051441d40714031040d0180c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 152030917 1250 152029667 152029699
    0xa08160f060912030314091011130510020703050610080d0c05060a020705150106051b160909050322080f010e06040201080613050709170a0f03050a110708060105030c 73
    0x2d80c0d009861020400c401400703424601500140202d01c440f000101c4c80030b0820900b400041a00c15180303120700c03420301840b48220080c5015201d007030407100d044030b5a0074003446542440e4076104401d03022401121400c68503074403114600075045403030603d80510174200740040c410030b001c6520224818101000404299900d80341c80300c000801400100d5404602030060100400c40721904d000d071407514031425612403000030040d51014448051802890030862114040001c0044852484000c03001d00c241c00c044a000260540401c00d03100c034441404803041d80c5005c140c840c0c2c00840346101e1038944502c0c0c1035101e810030f0711aa100c0004c0f80d2420b000c1c49813004000c201158065030902e40480c251b42d0311000150145c98840300c03610000d2402c010080b65a03040100d4005440407903201404da4201c05000366a04c0c0503058009000051350305407200040c1c020006002c0a05690520341100e401d100c4190f03140a01c1640034000c540e00c40c6004009604007403001c0300030444207032407a09444032a44 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 152032167 1250 152030917 152030927
    0x5070804021e0d0807060b120a08070c0509100503070603091a04021c0303020d0b0a230f03010c031a120d0f020102071a0609061e060309030403020a08160f06 69
    0x40c0003030b0140d1102d195480034409a01101103040380d0003801a41d40c990541010a90b40e004082c044030390038600400b84025103011000340a03010840c80081c0051000c603a101c3e5281d0700f01700d804807524130100c4004906945e804d0101071007101d10000c00e020f000d1812040614142c0701d5880241030619115440000ca416000f001c04c1031006148a0f440c0d5482e03920200388000001141d4141c1800a01c4100d01010340c55001000d84010722039080c04000e001e1810000246043e02c40c4421041e100400280c0f240c0c3e40d2a61086c501c6c5d0014460420000b110000c282910005103059000960fa040e84101d0f0340c4205030014046541547e00c00c0f0f20395010400d4603922603a2a0420003413102810a07800741034403d4040fa0021130f032001c910380b4403200004050500f05800d940c2980305030903c03000208a410844061518980545030052460507500d05000440d880a844a501804100808000340e2250b104590007003801c00c00411246c101842c01614040b85ca130840c2d9100114031004018456000b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 152033417 1250 152032167 152032171
    0x406060c0c0b0f040618050303040605030a050c0406081305010e0616090f03170304080d0906050f0f04120c0212010606020f0607030209012115080f1204030507031212060f18050708 79
    0x341006c51101c5c000200c200418940c82d0300c456410b2000140104465921401450048603410418070151302e85031112065405240200000503245d0400120308210004414135a20f000c1c0300006080e001182c407040c01c20000311190300708802254501c20281d40d004100c9802020b5000c440c04030300381103aa804803103208607503c4440280f404030100341407001c2c0800304e50380721001c410104007030020385c134003030015003c119804c62451240070000346800c3c009490980c0304a9208208001c541318101094403203214100082c0d030014107601b143d0000364400d10921002c0c00003600107010041c00e449a041ca80700009211408050040c0030303502c0140d0700440d81e1101d44100004541d10182d4010044004110300341c0300c41455001c1450000726000301181d2566045400d809841c42608410a40f04e400d108074440201203500400080002c901c1030b0f00e403901002d280f440c00c0f060b01d5010002941c280c03002e580084006014400307040011310708124468613011441b0390184418035040030050049840 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 152034667 1250 152033417 152033429
    0x9060b090103050403201b191701060801020c0f010b03070303080f061216050a0b130e04060b091e16050a03090809030f010906051506070f020102010b0406060c0c0b0f04 74
    0x303070800315003003500801e0252400764414110700151030035030105075510350b002ea8800301c2c51040810b641a103030034880c00c4c440c08004440c04e00c043c000d00e0027135410003402d164604030b4002c1d5a10075000c50250420b00003480c0d020329900050280c80880e035403550031220480501403007940419010000203401040740e41e4062090320002501d6984c3c040403404121410803040c1c05405180d440f00e421a28102c505015100241c9003200390b1a103030000040c036849a40220101c0c5c1c0c8800c4030420407030720580e094503072184c460320011680c0220304012500c11a01038454034014509160032841e201078104045901a60b5002d540881c10040e9001800510526a44004142d201c0d040c0701e0910040c14110382c0020400384c00c4400c00c0b001025264000e01020300c0458145050101144d40300c03500036a60003501e80c004220a161080c641e40303d104490701c070101203040d95281d2503a45840d50352481008010300442d15400501583c900d040b03551103101d030300010350541003409180b01000c080001d46040d529 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 152035917 1250 152034667 152034671
    0x30c1e0a03080a110709060501021005040203010605060319140c0304140a05031804050c0415081e040f0317041106070f080a0f02070b0c12030a0b030607081009060b090103 75
    0x81400030440c401841d80010742611000542e6a0b0080d0380410481c03000076076081a60102c0b612551034005458041c4641e41c016403103c0c40b902131504203030384a96049880200006081951100841c020742c204484070b00e0391700440b2044203e00c0843e13024011240c4051901950940381c0903114041170300024001829074204a6480c0c0c100c0c04003000351803440d5400c002126181c81240e100300d19007401c3c10ba8010301403814440400c02c80c0007560203480a41e0215484668280340c0514216003a20b40207090307804d01044600403041c40e50800920a01850059800701d50242d07940c1005403050070007003040000c028010003084046960031450100032881101c0160f0344118908004040102443c80542101d00024040c2d010941180c9080d0341400190244e41106030b0b220342c0803842c0d001c0d0004099050300901c000100c0d171500d66009540c800c42103500000c0c001c0c0c3c10000700e031070b16204840d0300340170a11400510007922084081e00c80140844034050290790308041010360540500c0c00800e040c59 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 152037167 1250 152035917 152035969
    0x90603010320030111030106090602030f040902030c1605011a0117010b03330f091b160501020a090303111b09130b04050303040209161b080415030f0b030c 68
    0x280c0300c20010001510b000340284100d040c81e45000380305510a118035004030340402c0300001c01500100a41c0d660640703a006880c00c1924100d0100042c0d8001002a06052002c01c03864104a410205507041e103400b400000490700000801c2c0300840038000301541c103100c00a0401081c2451800a035815111003c403032030785036210400059000b04105840c10040840a901040c0b90207264080c510a1241100d200380391103060340901c00c551f80d0540cad82d200990416140d807201051050010908a4080c80d10483c00600d603803603881c01c98110948180c00105511002c1040c035034071485024641d10ba5401622900c65046054907103910840ca8050050002c10005088500381d4440c034840c0c1ca8010581d0940c0746098501a9107035070046404070b110342d01840100741e801c0144c0c8d0680d034241e026500c0700e00e0801e5002444041d00d502c44241254001002c12010643c00d03450120383e03214800684010a030f0741c02001d41e090030746086100b00c074002d5003c44200e20042c0d980d021060030020040b00803941c00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 152038417 1250 152037167 152037203
    0x705040605130f1d1b01050c0a060b0a091a041d0d120f020f0301060201050c03010e01030b091f0207020f0d020307050105130e040f050606010212040b0a03020930030906030103 77
    0x40c003060b916000942a02c5048131603001004a0b5090075004c1c00034615203c200703801c00650340d601400540c480a503101805410001c0d01960144905000040c10465582d503901069400d032001054000581304188043c448542854002d4000b080c03100285d141546112030b560329542ca2600c03d50070100441c0c3c0403440110303102c5038400004244040411340d0ba4204012000b40e00e54028422034005602e440c00007000300401d082030b00e050300c5400403441c2c55646161100e1500780d00140c441c0c0202e00400e00389a000f40c0180e8800c0c03485141102000d616046140104425502102c0301d96000f80020041d00d40166004501032054440074280952541424419000c02541d5038000700380918107a0107000600c0180411116264428002c607491a9586401240c842103134009026505505000074050340808038040e00c0f50310450300d401410141c01e000010305c2c8110514040348502416101c2d80205081c4120740c480c1010090021450450700201061340d6100c1480064041400300c11a8031030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 152039667 1250 152038417 152038421
    0xa080f0d0f020d060e0a0905120309031606230114010315090c030f0b0609010804030302090315011e0806070816090b0d0516021203190905030307020109050705040605130f 75
    0x1050710303041011522400c03980841002403809000d0f10600c101294001b80c0380d9070132806200b192561000c00742210444c082031015250304003520074070441c0000d01401c0382c50524100e050082e10300540780070a410821200304014102d13031240846940794840018031500c0900e81c4140d030401c40a00c1d00040000700e01e01800c1c01d102241d0007140c0118105150014101d034580c02c0403c0010141100700400300851303041100d41d20550030780302e010038071100002d00802c1c003ea01800701940c0190607203648803081c0c050108150030980040070b10380540708000a2840405603458090104140100284c1c204690040c5c62010001e142c19242100d0a0340c0c0c4480354415560040108144c221081d101e5140313001c00005014111384140000510f02c41c2403891a02c00105004009003206920707213143c641ca80003080c3c8000309910f1400791030701d40d1040000100100000c40c403c40c02c1d82e000207084a0145481428000c49074403151069003011410b22880e07940c0e2179040300201c02c1040c0010f40714619192200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 152040917 1250 152039667 152039681
    0x105040f06080a06090b100c020a0b270405010324290f01050a0e13090507030b0a0f0c091203030e16140d0f02190e1303110a080f0d 58
    0x11038640c040e03900142081d00310540d030b4021a611081802180e40380d5034448119005500e500e5441500421030a50290080c01005111400070700344201d000e448646036181e44c1d1042c0c0c5288900c103e82c010028440740030160312000c1c00f004450510540d4515160803000040780302e01c0d41c254031080d0072500300003100c1c0e0f48135000308007070800e00c0e0111444150704d40c00181480103400e4003551034500c000385650b100f00101c4e00204100e8841c0400170000c01d05100e001c0301c00d207200040d20b6a980e554400440c2042094000651041f203143c041d41c94542d080c9400c1e40e884071214042d0340e0424031581686608141c0b00c1041d240b18005440c1016038900f02207010b0300241d000d0003410b000300138440c00c0445044603058140e81d80240391104070741140040c40500004e41d40050000c0c110980d80e5001840c1c1000203150200b4450121181e0a07180c0700440d004050a40300c1c04007a0000815100800d40c002d11070b510144180c001030f184d1001c5039200e4040781e1160185d40c2a142c03400140d01600c68900340c1c0048 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 152042167 1250 152040917 152040929
    0x80705131803080114010201330503120703090f050603040b04031808060703140903040b091305010609090f050402012114090a03031d0304050f040902060d0906050a0e1b010504 77
    0x40c0c0c1e221001d00300035086000c280900d2a0000b22414503560780d50050007030444126244034000c01007001c21140300704503d40c1d07500880c44100340c1c120014090394200000000c1d001c101280d141e41c1c4c54146000307072800e0316650012841c41440401000960f4549041d650b000c1d030003203981a09991145401c660a450710020354180c200b1201300804c194000017011840390f07c0b252820030105a0042442a40000c00c031000300242d0300400050000c80388400c040d080900c07003d000e0121100725030a0490507600c003600702d140000d0229074200803002d031a0040030a50008282c0800080c18140c00090907002100c4040192009041c0e012080c04003a51020301c0f03c04d6010903003401e82c2025080e032034139407500d01300a60002c0c4c1003001d413252a984541201c0b4074684813400441c83c3c44d14050038080c44031400362a45074000e554100540244e02c81c0030081c1086001528009040c0f0403520b40b540444074040c060304d9070f076481d10600011011000980b01c0d581d03070350a102144074440c1c0b00012070301449603030055 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 152043417 1250 152042167 152042201
    0xc0c0f0f150e01050103060b1e15190c0224070204150b0a030510052b0302010b13091209060509060903071d07080f0f01140102100c05070201020c0a08070513 69
    0x2d0b1800320065000754140d0f0711685041c000800c2d1002046043e001030600020203090185641405140c0340142c11584815100c09906000680042d244040350782c0d0110404148814016021890030499145a094203004113043c5541100b03a02d1041c0e005241000340070742d41c0c504500701c003a032038181841c000b80b5110310000d9036020030f400010007400c0159017181410b00035120204061030414072091071a02000004d5807204c4111081c152040c050b240c00343e066559410403c1c103d41c0311804440b0244c18040c101040041941c0f81203240341d90788600900402c086038000b40441030340031003100c8100600315080303501d0b000c010001070b051580d25801070a030f1a075010103103000843c140e4030181c4510015202d01405a0303a07480325a5019408540b04812003101c0b000501400d00f82103822514004184101c2d446020700030340744002ca40d04c14403c040854008508401190381c10055030001d0601660b00300346551400036400e80c1d910560045501c9581c0100b04658483e02ca580a80c805151801032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 152044667 1250 152043417 152043431
    0x7020c13020a080a0605030d05030a060e071707020c0a092003040303090c2112170403020618070f0b0703121b0e0306060d140a1406010602010c0c0f0f15 67
    0x140390001d5202c000c00d5800b081941002030200c8106201d008110340004d0041c0c401015034910880b044c0e80f0044c10303004c0d0b0580d1582c01144680c1c000000502c81e080035100c051903c0c0c0e10b201c001052440081c500b104541c000c1d0038a9940352640002d0300c086803100c0901041245031000f6905c01d00c02c5c8070645070a07948010007004189541031304100c000c1e0380a43c0324110300a0f1100c80c502907140341100704120040f40301c0804400038100c000914a40046894001041c2ca40c4041c1003040038015601030b03005038480424071091011100b100d61519100b03e009180e118608401812021918826100d40d41f030042640828140104100340d140c2d0b265200800c6160581d54003440c00e01401500103001541001c0100c00500b0b0001e00180150001415049511203070b0f038070490303004c00041d0030b0347c124016000004000f95030303a910041400020350242c101c0e58107050000b82110090140f5500300207840725900046246540d050103410b4210704040080700442c14561a03103881c000c1c90703421307103440c10301 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 152045917 1250 152044667 152044699
    0x6050a091202030a020327030d0c03021603170f09060705030c010b040519050709080a0c030b0903031009020903030f16050105071818090506090a050c010207031104020307020c 77
    0x2001040d264450440c290440c00341070002ca03528080c04c50b4a00169108000e100350000030118868021646500b00c038161050400110f42003031400b21900010803a17010382801050340600c0313030391150401406c0c4601d00070300e15182d2480014400c40c0c08241038000007405520100b0750001c481d20800c0160400350394003502d240965480e4003140b0740301025464000110070307516050251070b01502c100c0c0301090403110007d60841c0100800750034201480300c1720134001465a4140000800203000303d140b017040c5440c50400d400702000050120015803c10810494014828609101940c04c0d8040040c0c4940d10721020a04d50702c01c02c00044ca82c1e141c045402569030000302a8440031912940091240c0e4481da00d0648824100c06090700c85070482690a004030742180040ca80701102502c030110311415103449036030070b04ca400c0c2c075042680d03004101c488003401010810300d0010707030080c8010154285191240307800c030305814044900c900d40000208480c24070030080702d030083c90014040c40909403071728 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 152047167 1250 152045917 152045921
    0x1050c010905160924030813080618060c040e04031b0c03060603060c0201060602100b0d14070303021b030c09071718010f0207020d0f1e0b010e0a0b011d0a0306050a 72
    0x301c02e13100f4260500c09035044068011100004103000c0030f01c00301100c4d0031540e80001981101010b441c5040d10f0110000d0034003c20022039008003158010740a55a040c42010780c18001d0003043d220303074031108100c01c00c02d4480305071159510642614080302101c80f00803000760444000318001c0e083d215031880c00300c140031080d030201c030803284285010020310340c85a41c0ac2e8266001c1d4426400981c110881400390100305402030198102c0060400d0340c1e4004645c1c41d2050f190080000c43c1c210351040d0300038030800d9010800150540fa010a5900b540c40300d401c0020b40d520300829015010307030b450034045600b890140a40d407803a515000c142036082e15003001500b44003055031b07066001940c200740d48401140384a102f1035221540241144021103030b16103070242400580d82d0704462207011000c0b00c510406145868000040c86004140042d514126103da101c0d513010b40341500f0780d49800c0000702a81e0f04070001a241c01c8110758814031003040d502c00150b00c002d40340c0c000340443c3c0c1401c0c1000303184080c603 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 152048417 1250 152047167 152047169
    0x110d06110d06090e0a06050c1c0209091b1c1b02060402090105120616020703050d090906050103061805090319020f060705120f09120d02030f01050402130501050c01090516 75
    0x1a10800c207990f03441d0b060303070103a07101e000c0d0300300c0150410b21400c40464401c1c0c00c40342c1c0c083c621700e041d14034000d81805c503d05030070082c014401e00f0581c049007409542c6801540150800700c1400120f1151104c0325020301c4030310500384141031401060403c01070780390b515086007290708100e20030030714000140040a91a41e000b11000c1f0700c00ca111030000b2429103030407101c0403101d0b64540000d00c0e5684d1018403500c000c51704580b10005610510300c3c0000040c01c100031101c9421410342e14514142e1400e007801050b14102c0d04000c0c18181480402c0c0165210362141c10308c01c844004001c113840c0c95080c5001d0a40c41400300700700e09020018482e0310b9803078001030219910001d0b101111090b543c1d03400c0480c0c1034051840c081803116000c0f00400c034030801c03044100d50040e2104096650f207003101003107900e042d440080402d0308541c000c0b08120715501d148038120700400341941d003075103851281d0485480c0d08090380211418440003052001d8000000d520001025610104840d52042c2690134481e0314841 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 152049667 1250 152048417 152048437
    0x140a12050906070e06071a090f0f0a1113090b0a0c02120c190c0b070b070305060409080307141308011d0106150f11070b031501080f04110d0611 63
    0x501020510050000500c2485441c00713907a80a00005030344100101c5a005034400c1d151505440d61810321080c407e2103080c0a6a182c0740100501c0a4042445003020710f11015099681c101c0001e0101040402c08580d003000c80c01c50f0110164140b103844500100400c8101030b08008101d4204146902264005106205182c007110f400c09564038074040c0c103204024800711580c101e80c50108024603d4031030a15240d100e18898885680c841c6076103019500451816186185404140102c42d07406114240d08168191400d00540c2215100e2402510016010908111031030520303802c19500c0b0000c0d14524031982646079032940da661000d50103084c100702c0d02e422004184c0300115403520140301d40b000303c841141304207071000403840099038804030f1042c5400901c102d0f04903080c020442480b011028190200da4581c9a040c0100c041c502031440202c0681842602014000341100894600742e0003548004038900401d0720380042404140b144000815050070100d04401c0e51a00001a1441350301f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 152050917 1250 152049667 152049671
    0x201020c010e0708010e0610090b0102030f0a09090c0807021203070c02031c0e0108090a02040f09080703080702120c0303150307081203010e060405072102090d0305030103050d170c0901140a12 84
    0x4001c1d100302d0707c0d240140c07025513100c952030348100084083d54000c4001050140142c03801c0028884c15a052940040200d0000514810040c06580c90512948095200503d4048128a88444c003c1d6071451042000ca0201d800030001035910351040c1c004504003030f409001e40381c4500030704003584600700400390b545002c070b409184812129449000c02500c1364603000c00915030851aa02404001c0040070640054a500c401d18800030131a03a100074a4810301c00e5440b81c100c1d02c4c2c0303208004c0c1002c5a1542c002115242040050100c050010550b6003100b00a86064905109103000902c6d02544e98800c40441c0600810580094015805181201c0303204041c40d200c1d5803180204801c840c800c80300480851107442c0120301c0c0c4000c8034810310309800001d40040c86c2400b80c0c0300048a902d03441d07004500054000005004000b0280140441c0c160fd50038a4071301407003015802c0d00d9001c0e0007003c6d072550190118066803968401c031440c1491030480b0444944e541a4a000140dc4c140e100415a62642c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 152052167 1250 152050917 152050931
    0x60a02070e0c03041509110904080901020f010209060d4701170a0209040914010c14030403090e0703140c041e05010203041406190305061f0e010507030201020c010e070801 75
    0x2c00d4041264460782c1c1c480241404440c20141c0b8100815445100fa0f5668110003040806500c400140030302541c0611025612000701100080c94040000c2080c9c2c00d590050000080355242c0b43d0544400d07030b034040d4001c9140014005a510540c40242c0c4400440c1040c210104441069502412015003c0503c90818001072001503e12112a480d1201c020070314000140c5c0c1c00800ea400b400d9074038401040440c07281c02d01e489070500e281c035141d410100c0e07940d0b40c0c4583c2030854112500045003541629503c0c1940381c1034038040e00e6401140728421503009000009426540700c0d5003e00035024101e0140d08040c20165a24003198106020344920340000038050038103d0400c0d5001c0c402c6800580c01145002c0c1018400721705214900c2c1c110307410100034441c10704c2028184982803100c13021a500001d243c5000401c120003d041101104190800d00c07110003401c50b03205000903100ea10a00b400c0307944d80503e1504900a2280c40302411880d468030201c25107416002c2a1f12003120041c03c0280084 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 152053417 1250 152052167 152052181
    0xd1103060a15120b010302090d06060501030f0501030c060e18090a0b01060507051c0504050432100504020f090d0c03020a06030216150209360601050d09020f060a02070e 74
    0x420381c80d21840c0842c0f40c3c1e07100c3c85070007451034000300407003007043c136002d07040050510110f051011482d0003114400e443d1201070103196032600c181105d001d5020000d0003103514603207034426450043d00591081000c0e002c022132039034548041815a50f41d00d891107040501c1c080b40340300c4d110380b013900c4216001640300000142c03051182c3c058840c940e0300440a032507551078107004a1510308115012105101d018880010150b4643c428251314044000c1c0180d542c2a02280030200070203e44520709041150720140462500f1b92041401038071425034005039505043c0b210701c0d2490040f0702a0651044104008004102c2c034224a18100d0f4429504403440c261920415800d81c041c0640304076503403003010401d60224030042e00c50f00f1111004080103140003880c9011501164200041440c1703050704032440f001960f107074120541030180300703000c0c540c40c0d007040f0780001d02c148244c0d20768032500c9480311188000d40d0758080e00c4402a00f402041d8581d01c0c4c80c0b03000e000e501d8003170910035400e00c005940d00084031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 152054667 1250 152053417 152053439
    0x5131a0604030b101706060409021201090605340c081b0a060f0501080a0f0c03050106170d17040318180b0f040b06121f1202090a11040909080d1103060a 67
    0xc07440080586007e60b03500b81404001e0880d0f03001660b10001060803480d0f0503038280329401c044d40c01507a0200321460b100644600240f4a8080098000c01c1110f80c072201c043c00b11008140760009251a48000001c1d00301a860741c0140d43c80c01101210294071604851000030348000380500c680c4d02840488841200d02044400074818001990010001280001e2040080701850381c880d91a40f04a82d84985450342103889070f4100c1003a1983c03010240b04806010003244441e6445490b1074126110b80d41c40b01d8aa0640182004060041c20745040361021280704c04030002d404940000301260203103240803c01343c802001c0f964064040d110221070b503400d141c0180d410505010700b95501e8001803102c504400380e0010140b07418020b01d01542c4200440700c6141c080101071a604603161520a40100890b500020302202c400c00d00d0f02805400302450703c0252812103100200001e03100c003190510740c9540c41f030300f00d04000040c40d0850422080c1c1590025600a501c2030300c4940595072980c4500f03007 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 152055917 1250 152054667 152054699
    0x4050103081e0c060702011d01270201020309120105150a0f0303050705030d0603052d0d050904091a0f1608160c0227090705131a0604030b10 62
    0x4080420040c0b48012024150303240412071104001a00c1c0c42d4256105504221050302d90304010f03519801d075240c0d80c0074005921221208100000c108485044108032480b43c03260802c0070020418504610540e8000c4c02070740c0f417001014041da1070364405044914002c080888811340800d0b0464200b00b441d003041f0181009031180000110005411074405485a8000980460380352104212000d140c0d0750901850000b14810401480000d45841031050f01c80391074002607110071101c0300111040100007401d4000b600c014105156110107107000325000c1d04c1c80c040c01500f202e658540100084c06001c034054030a0900c03025075265921203207400307041d0907500070b0352a0000d007803000032621141c0c619041361111101c030300380b6060708a80c0d0341c0840c84451013402c08411040c00c405d0080f55070750100304540d6020420b8005002a00e040000140c421820b046001103030302d0707a818040710054405581d00c15145001828151115903a00e05424143c40480c2c040c1c070700120b0201d0015141c00d900c20002 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 152057167 1250 152055917 152055923
    0x60906051f060527031002030108010b01030c170702030c01060b0d06080604031d03100507050304050f01050105031504060209040e0a0c0e0106080a090f061a0103060e0603060c03100b0d0603060b04050103 89
    0x5203004e4000c40c01e99109098091000301040600b000120141d43c200314009115043e04400b603200d625040080742140c0d8507003101814182841391521940d83d00005812440d011240c01c642a6100e03160102c2c518021021900034540c68240c1c085401111000901200c66029409200654441404680b62a02503400601044010785e20001c1c000c140366142000c0c2102404440f8030b41000710b0100f0659105441038000300f0303c008140000e0000900c518410701c02000024060b0b54585800f0030754030101c21032190560780302c40004ca02008a2030301101d035402c100400a004440b00300416075100d02e140304085690b0707400c2c41d40014440e50034460040c102c0d00303142c0329543d1641e20616038001504403070b031007143c01680420311500040c8043c41003840c804e006502000084188034009021150030fa00441072236003a820810038140e4001564642c440400030f00c6035140e072142c407080c0a440601e904035580141000c1805580300000c2d5102c0402c4a005007401e0100354905020310080320420700001d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 152058417 1250 152057167 152057177
    0xa0b03160e0c0c2e11091e0a05060a0c02030f03030618010e010603020702030c031f0b010c121803050f0303040b1501091e0f080d091e060e010c060906051f06 69
    0x154201141907010340440007410040d03541c11045140c2074804455a07104503c51040c80480d07522160304000c0300c80100c80080d1302d6085048403001c000030749000009d1045901c1841d001541c03008107440341c1d5012041950150446152000c08c50503280c0300c0e001242d0030f03402841011515500e03800850120342c102c40c00d0280f4100140d0034603404801035480300009a805103e01c82040c0280d441c1080014800c2c41c1040c0321409401ca8030420200751848034200d141001628200715020400c141d0b05403059030824104000d501c2000491840a40150351002e80b90f400307080e034040e03440580800110700c2a8814030030354416035100e49014510a00c5101920b0028a074448180204994a02c03800410103a140d000110a60355030100306100040341c01540d948d030400700a40b402e46401c02c03440c3c000b51640b002c0c0e90580444100c060858908144611800c008003204412426400340c1940500a034001500340051f078410f0030000c010708020b581e42d00d8070100c20000d20184240c2c914584064404960b10 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 152059667 1250 152058417 152058433
    0x304140108091b090a14090c01031b022505030708010f060e09150901060801090c05191d0601050d0207030f0906020c060a08150303120108010b04020906070602030a0b03160e0c0c 78
    0x180074001da8010425002d0f0b03503a031b02d40850040842000ca503ca5100c0d0f400070141c2410220004013510900c1d10007001c00c034401516190040d4010801e07200c90102c4c61b518401102e071240007003201d8004d95102076098001d903440406e0000341034201941c18142240c0600c541da40e124290001c2c1c40d1b045640782941d800150329481e8030111083d1080d0049141800425070686903500e2030f08540518008a51105680108110f0303410a080e5084400841101e010149442d11141074403010742407905c0c4902103840000500d09038040d00540c0c00301d0b85e90b90002c44d01c0b00380c68a40030300303024448001c030320101e2603803040010454400110401101005070006040c14032462040c0c5001d070010700034000b0154512030103030007510200040c151003041c10385400a95454540c1141c2100e03140354000c0d0080d8010080381d00c2503100d210071203603200d5100b940142d8070781d41c200c01140244080c0907510341c14051010925454056040628140d8150781d428400d542c8640600c0d03903442c0b00d008403d12080d042104 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 152060917 1250 152059667 152059669
    0x10501050306030703050d17090c01140a0903053f0904150b0d1d0a05030703081e0a02030610030b09010509071710060f05070c05040f0207050304140108091b 69
    0x2020716002100a400c450505849569490400b401c000c508000a4120900141c000c00071450094014451001801009280c41d0000342942100305110f005408009030407058648074200c043c00964100701901c3c002e44a00c0081d0b00d1703505c1d140910501c3c01031110180020302d81d0138503600082d403040c9034155141882c07950a21001e0500220b80c03a00f41254482e00040e0910040010000052245400a15202800300305501d07059001540d8803940e0107183c03c000020b01c004200e40386c4980605004815a4500c20848a10049160b03000d00012403102404400c418035001f85001d03104c100d40c0490700300300c403001c2102200e480039200c55200542400400480c00e1900103540c10a03564609040b0046124600182c010b1007558801200d400d00c05d030400401d6030003164054103001628003185000d00c01c0c0c0781c041c4068058000d4620407582c0d5070505603010f08550454090b036500405a9840f195200c1c20012030407000c07120303640070404a100140b120180030600c2c1c0030b004e095001c0c1814481c6050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 152062167 1250 152060917 152060927
    0x30f010501031103070e0f13093e130209040f0b03060105060a0c140a02060a0c060605061204060e010b030a0c0e1e040f11210f0d0905011101021605060406060b0403020108010501 78
    0x7e030070140c000203a41d0740c1c0c000c0c040240c01180303056405500f1411403840101c0386840a03540642a54400b6810107049055002070741e4814041e0101c200c0c0c107074420f2603550201c800203206040c1a258000e2a00a00c055141001d8000c003d26081c00c400f510034503a0313103c0500240d44101c038585030001d20320b207070500f00140c4d000d0724800c0000c811000300e0701d03000015404205123501c6100c03040041050b5103104070400000307020300d402801050b203030701d806c0030441c030080c121443c0040c10060040c0c0d1140208032000d4000d5100301650702c4000c0440301110b003a403c1402c00b03400a402901088140c04001a0441018070040d8134650f06408501e440c3da61503407520a08146030290441d003010405104081c69510800503007241d80140307a0b0403240348940c1c89141d2400b9101031100520b90806090201c00c107401c080c3e841d04990082c01c00e954030800d075050711070092080d1003000c1680c41e4461307541d40c1442000503000e840343e0302c940800c0007043e854001d5034042d4062444000e00040d8040018005035206d0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 152063417 1250 152062167 152062189
    0x50d110313180204050a0605030a0b031b100c080409060905060607050d0c060b090c0c19080307030903020703170405010207090b03060a0902040f09060c02100b1c020102030f030f010501031103070e 86
    0x11600113080a0f1203000081055a8680c0000d0000700040240141c0d10a181300e048040b4500702c0c018518058480c0c0c2c0b0301c02d403d000c0c0c8080c0c0c0c810a982031401ca060360051900601751980f00010710f94698840074500d0040410303006541100d4a050001400b90400b0717000c6503a0340380c102d001000d0b24145101700f1945002034100c00c44039a83c07145000c55039501c80e122040e0051410441a42c0c440c00420401494070a465902090051030048080d010a101504907a0010741519010541501600302a07243c600d203030344002d0204511015002d031ba08543c01c00f41c000d03100300f40e003602e00841d80c038040807045d140402d0f80307142d050700600040b40000c1810350240704002e03c05400403400c010031b840120110b54440f80103031140c45d2107007410300f031441d4180708015106640b40410040010035001189190041400c460540386120400000f50383c000c00c1591296440e544a030341d507a1800e4039401190040a04c1380601003800c0250207006e403000c000540b445062550342d44107403c90400300b08110748901c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 152064667 1250 152063417 152063459
    0x1060308340f08131d060102010c08010e0a0905030d020a110a1a070e041a0a0603060e0f0406110309011b0507200f060f130e06030a0f031803050d110313 67
    0x104030b448120350300041944020300001c1e000345000000740040b429000c0b4024031b5141103916110440104039002a286415030781d1780c0e181d010072566080d12440041100ca88050f2161102140c1038540040c142c0041200c6034007a0b8441d001c030240b102580e9902c60000c0001451218219a0902d086800400d89944080c035440d150700142080c20100b81140c1000c040e1450301400d204100450381030002049008081d903150801100d4a040c000110f0261701400e23103d2003805d1a004242070215a801204440b080c2082c3c40741e0343d04100c0c0956000f40013508410f0747c102800e0f0001c0d0601c0d1b0003001526440d68000d01142c0340c40e400000c1c001442c00e9140b00c42c42c2d0200410355445c025803121700c003078108403003980aa1030742c1d000103030040c407960340c8668069003900e1034442c204900750714045840f80816030710204100c102006441c00f80c1d81e00011800c415401c400000d4000144503001603517409a816984401d208580341c1c540454036441074660701da10001c1400010400e500032400c2c2440401a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 152065917 1250 152064667 152064683
    0x90a140120120d090b010b0c0304091a090c0a12110901031d0102130504061202031914030a050409051e0105010e04090501063005070b031801060308340f 67
    0x21640c420540303070f40200d101c0f0b20700c10350794030b40034420800f001c2d0060f03024220451640f803c0c94111070003583d0300c0c8a00e0180949031a1596034a00048020041404400780c000305005800d24001101806c0c035046800540300040d4104040b2122151500c0303054038a440f0005c00b40e145c40e110500560240041c20700d19404640000c1e114480d0301420302c050b01310b101041505100084c6420100403e07100f15400c44210031101c5184200143d0340010010408004c66005440b114514240402a1001071000c000d16001c0007411008407035005000b0000e0b5490501d003040581ca0308069a080000c0800107240003110440060081d0340c081c0e207601540315401400420380ea80741d962081d09554031544000c0398041100c01c120121b040340380420124008200c5410380b2100c0c540c49055491100b4890b4440030346001010403000e0b81d22601183d501d0134076500030311403a81c1d245455501503028035915904c0d100010a45d001000042c0c0c44c524071034104207030110b24543c1d1074980c26804a100141201d00c1c00c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 152067167 1250 152065917 152065933
    0x109200604031716120e090f1602120a121d0604060b0d0507030b060a06050a080a020a0c06050f01060305102904080a0b0402010315080a110102010e070b090a140120 72
    0x100e8008504d4240c68455070401c0000000b050000d0700390224204c01c54441c91108080103206041405843c4d40715400401e80c0c4203505010b0003c0c0d05102d1034030714079007030441c0c000f43c0c280310a90041800c0d080c100d05c40104010005030280030204e0304013140a110150b800540c08103012545a4008201e074210092146e00207802e16a81c8034a8401194003c0f100907407454100811450100c00000060200d4244039281003001100100349010092014030314075408543e070304550344600c9018154039032246041009041150344188180024425000041c0c10000080e144040d100200000c03100640400045850070f1041c07012840c0000d81801c44803030080c4000600080200000c0925500481c914040313070805000040c01d035401078540c0f150b403980d001c008101d040b01c002a20040542c01044901c510003003d00102d0140c401c24500c1d2005100b281030200e0741010700801008590b90803240e1081b0907945804e41600390b01030448050108014013580030740000020301c40407130841070364140c51340c0c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 152068417 1250 152067167 152067187
    0x1908270106051806010f110a3504060c060f021908040302060603071208030a0f0204060e040b0909030f070f0807210c0803060d030e0a030501092006040317 68
    0x4021009012a1980e44455003040607051040c0d8035820f0940800d0344091901c0c0c42c0001034141c1d0109503440e4100030071410804001482404484102e541c0100c5d580d164568403010080d0502030213005d17041c0345055008410516041d03c04031030845141e40c50b4110030710101c3e1a02e20080c9031421704070390044c0e004c001c0c1c86d42039049154404c0307132260700b82c80f911000d00382418002e203808001064180a03501c2640c0c00d005100703490b9078a0207615400f0909550b00e59401ca100405401926000c0f0030311070001ca4089402500001d8400220405941c2080419554410062800d0b0140e0701d034912030700704201a860440f0141d000340307070190140b011079100400507900c561321680400030a50384210540c40d4111602d024500210291a651421101000c21f035126100c4a00c40074004610648462840c081010300a5018600843e4001c20740e591881e940c0c00d1546c0a486907100403a84000000300e0350320300d0300c01030b04043c40e01039016208505041c00c5543e0345032111003580312209500414451784202c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 152069667 1250 152068417 152068471
    0x7030c060e0d05070801090b10050306190b0306070306080c01031401050103023601090816050f010e190602070f150c020f040f0902040f02040605030406090c0302030f0a0506010b1908 80
    0x60a0001c000103180c1c840e800d207084105000727000c0c24804070404008010640d800240c1540200700ca24010606140401310340004000400010b901806800104131180f40c05a10400c129468041642d0346442048011422a8000c458501c500c29001006002c994440c1c0d0107000038a24000c4695500c01c100c04003200c072910801c0200b4030f511010240400c0659001d522080206000302c010488003004070440e400025590003994041c2050900407945a8480c410785031740020044e1030295031440105401d85c5907a00c40c012000580314803c400907000091480d02022240c0030884007c080502c81c10440b071901d140d50099a0090070720741110a00da03142c0c0308000100b180c40000003451310f007520621066440344840d40303003081c3c41400204142a003160440b90300940c030100000f007160003403605100341c2265410194142c46140d4040e059030030300180104141340910110780b4140ea0b21114803080341704040d80d045808490b00765400210340119902908500855464620140d041151f100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 152070917 1250 152069667 152069669
    0xf1501170c0604090509010b0604140904021309030509120606011b030314090d0f0305010b1b0f0102161b0f03230d050a03110403020f1203090409080307080907030c060e0d0507 77
    0x1307440ca03660014400d1940c030034841c041d02075400380e0b4060f04051824008080c00b0b901c4070f14440c040d410100001d011596548101840d0b000445000c0000c02d400d400c000b4050b070041c2c000140981890161030340461000100c00c2c0c8a261f0503581d90404805a40c0b40748072030940448102d09154444c0b090b128503104403102644202484001025100e14100e0024294820650703401c0506107454014010301d81204204d8560749203034403a03021040400401c42d4684803180c080f0019551001c00c0f8403456100c140000035060b80540003006113182b4420203013140000b00e2040c8410918103600c03c000260000f40303038010064140e07840364181c0c8003000c002400c0081441d04030f000030b407000550050503501032188545400f20381c100d40b8200b0b4219400704907a85aa0b4110030320840e800c4c80400d420040400440c2e10444c4007a01c18000703124917160150590304242d412802040c490000100c0700b8000003038100032246c0203000e03496a03a14200c01138903041503030030216400480340304460340890300400c0800 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 152072167 1250 152070917 152070929
    0x31602120a030b101106060d0507030f032105010803090d0602070c06120f0b06090609130c08061c030c032609030301080607090810020d061205010e0f1501170c0604 72
    0x1c0707034000102c0104031904e080107100300c2c14403400140a0b43c2c07041c0c000803200d901c800140e0b5800e0b016512414091710304012507100601c4881003036201c00c1056030040d0b01c0700f10500c0c0410034265240c1500e0754007050303510900405010b07920600c101003440c0303030450000005034051040140380500f1038640e8a491441c0d0303000000895208030005034010f250b48285100800000c40c2001816602400940c480c801c00c08098411080400c18103d6a03413401c2d0400d04610214004000b1700e2020768001d00520000c4400b54480c0004400074420a400d40701e03035554159165440a40c914000e41c3c0c1a140380c0900b0302041c0c40201140c000000407030204030440d000c1c00c05e4100450700c943c03404402c075161110003004903003000011402081040d10010b54032043d16001000540c89039402c0603038200070a4a58420300000340a4407c000601c03206500c1244000c0180d41660368000d50340e880f981d80d801402c0130742c0a12800b241c0040140041102c0a89080d10b00d4034141d6000081d0103000442716001a0010 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 152073417 1250 152072167 152072171
    0xf02070317060d0506040b071806030f0c030c0804170f070f020907030b0105120a15060c140304050d060519050f090c010905010f030b030c03030c24040206031602120a03 74
    0x59a0351001c050000390300410880f068031441c503266640c00e4a0322000b4000070070681422001c02d600c98051207060020b19164030415140c01d55807500103001d0001e06204501591400142d1383c5294801d0080c1540800c107134403000d00a480341c0e03640540c0030101400614880c0320a00c4000c082a89c00d10081c00918003401c5001100d020a00402c41e4070b4401600316400c1c54034103400250aa41c10000f92007007080d680e03c09140d00c0d91000d5604c1c024082c041040c3c55071130102040810419000f0048030561402282d400b1044141a5242c81ea68800c1b40034041e40007140380c4400e0000f0340650031071580101c90b0288070050014040030b82082c0d40c2c06a81c100082400c8408211114004101444000c0400d11f03140c140e06140c500040d008400d07009042e010151640c112120940307003040711a40d07210307024046030360340da1101195545800c1c1c030f0700350800008030b003604892a00700c581507414001d54006020074950b8070303210107041a44034858032070410b40c050040307106040d40075900580040c03c032680b80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 152074667 1250 152073417 152073437
    0x150605040e06010608041b0e1603050703060e0a15080607050702030d0207030b0c160f0b0a0c0e0f1002070e04060b0406050d0b010911040308030a0c020715021f0f020703 74
    0x402003038a84101c49400c5a40c812001004215404001d407074009400c2080c20802225603175000603000940d0b0031000e1000040428418029503014000c0c03c99031003960b042080d519801c004506580b06441005c2c0c01035800804203400145603409001c4110440000400ca01d90340c014050070041c0c1200d03a40081503001c5540415410140074110304e80301b59201501c1068110b9588001d03425001d482074022840205101612180321070292940e41c0d004002c2300350444c41842c00c4110100c044402d140c09030b040900300280640262800f00705e034080146612640e04e007410600c08244143c0f09450114031a4003400180841a140c119008900a8402140401145091105076401a0b000138040e202c00e05907000400e000c000f105041d54180760001c90307042120038140ca102d001d1a00b001e403107841c0000502c40c400b01c00f94456040840560203882c082c650f5201e0083c00c147c03c0304c05841c0540c0101ea02107141549401c450000ea050307070310001a4191003d01c0040c100d030020300c01200841d003a080 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 152075917 1250 152074667 152074669
    0x915050c0f1605150409150504020c01091b0b121f2306040e04020d020a09020c0102030411010905060a0f0c080d09020310050105060a0305091e16050603040309061803150605 76
    0x2000c0c00f0103442e03481042c0c40803112503000f4404c620910031341559a900450040d4034590f02c0000806000b4025512100400c0480c0e000f08003100044500c420700400e00510080c45140103800c4607002c60850f802d180304500055640c0e4002001c2d0340030180c12a00030f511180c00c4041d0140030f4040303003e080794a1100c42178030f1010300203907030a0540314440500c010040032a4a00036654460f905031600c2d0888425403001c950542d4158010019072800030401c00d1050070154055807140740910b1014204d00161001903035041c2c0240103903074103d031041200e044c17500d02821060882800da4501608101c000da110140c1c540c016195021025072209031007415481d04120520780b40840310000c02580d40352400156180c07140da003400c0c05054071040082c0390350000303015000e0a4000c1b00600c9056011214500713443c0d0b444000c003030100b418022000310315070070031005891207158180c441014250030040144e40c040700c200782500e100d40c0345032008800141841c2829004184140300407906504101c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 152077167 1250 152075917 152075953
    0xd0201050106030605060d1d060a0e1011030c03041e0303020c0f0c011d01030b120106150201050610030e191506090b0a030210110609070608060306070915050c0f 71
    0xc0c0c00b9104050908106101d9680d071003041305c1e10503080351000900b0f09030702c0f0f00751401520268103c0c0c01500412080088596090b08a41d01c008609020781d034200201c600c501d01210541e111802c1226010302c002012200144000c54201d40508040d407500807488000c0c16103a22003400840001e070700854411008041081000c0c0b8624600c5e018041e550a40c4000910160110110a0000580c41b80c00c00d1580d0081d032202c2841d81001e086040001000720025020301481d201c2d42080b415140008501d40744184030369409110002c0002c220422034040880c06800011320b214814020301c0b20000f589513640e5001c6a2941c0b04000c01c1c07204d008401c01c2c2c80105e4110b0390200b0199410305414800e03e54034500b498083c1c80e811507280340382000c0703100300301c880024a44110149210710014400d00a000141a9040b24401d0303850381c10f20768402050580f0b0703000507148074011400a01c0140302c64032400409484500f0545442424003408094151134070304400c4543c8100d4001c0c00014407400042c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 152078417 1250 152077167 152077169
    0x306020a0c02090a2d023c070f02090604111908090f10020d0b0612090d110607030917040e04020a0e010e071d09010e10090e03040302040f0b0a080d02010501 69
    0x2410f081012404100050028445098800c004c5520120300e45175805050307816a003001c241c40b41c07054407a00c49000c0d40801d12050000003c540c0c68451140b0a031519082c044440c4180c2c03010001190108550034400c1c000000b80c07045ea4400c3c0c50f00000079a0710036510140c280700f5600040406001041000035009140191081c4241c0d04030520f5800d16840c0091012000c070054280140e030f40343c0b01d07950500103003040d8000340e5022000203a054142c20490352940d018001541c161800c502040780d007038421480c1c0c010324001c2c036006440060f03041e6009a0143c40c40d03900400c8840c4185c1c000404090301030740290440e803680c1b120350081c0801e606100f0703c4030700035180743c0110560950510103c0091f9142c02003c8404008070700302c520411b0421458983c15011018180c1c01542d611801d035200d43c1e001c11141c0103001c0051000018003805540141000c00c4844009546014210307028071010b02901c05607801c14a0700c4e0003407056292640d01c201d40003001040054094070249020081c00d407401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 152079667 1250 152078417 152078431
    0xb0a0203042102120d0f0c020d0c0b0a090f14090709030206040f090605030105040302030909190501030b07020d02010908040b130e090f06090c03060c030601030f05090d0f08010b09010e0a0306020a0c0209 89
    0x40303000305c0c000e6150441b10845c400e15103801c1220002c10588001061300b020508001c1009084941c00582600804050905401c00341c5402c1e042d1a107605580300d290f54144245051401120104046410b010f800c44d9040b40451900c501c0300340d101d0300455496402940160910604400e040150f007a441c402c08018203410bc1c020b001d41c0c142514002d50324006e54080901c10180e21000c2144c1c10104100c0700d905040030003040c0041e43c0c1d030b81046801107000b214020090300505a003842c03240d2040c416004495441a03155050504040c0311070b0454000c1d134031205103020a184041400c0d58041605440f40074014018141c00c028811141d04101e80640810701d2a0301c103070040d4802e66404182140c3c001d0304007210755201d682d640e0040b405440c0a281413408a487c140501c003008501260300076905413540c0710711480104c803940440c0c1480c000d10848030241d0b002c0c86402c02c607601c501e20400549000910050040d5101c5d11000c0403680010119404140d41d00001c1007103007001a411584580 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 152080917 1250 152079667 152079673
    0x510050f0f09011a040e0702010c0813260f0f03100b030108030703141c0b0f0102070e0f040611040609140f18100f0e01030203060a020309070b0a020304210212 70
    0x1049070101d0740703909040c051000f03401032280402c014130030200c00380c3c1c0003040048207510150034162400b0313000303111907907800340050141c000156441c120100c0440c011a40401c021411020240703225940540d803200c1c42584141c00c0100f861a04101406408000501c281083d03403810582010f260203080c5922007100400e09000420688801005844d109601400c0045480d54504801c0080344142e8074100c04101e0760700c0c0d5800081070070f680601a103500603501c40544000820040e652151140305440e600100c01d4009190701d860311040d260020300c15080413030246040c6c410340e40716403c00c0d0003917030000e030500c402000041803201c0580c26200c0b0640e40e548d0100005030124209040084241404001e680c01040c0d810003a00b0a80008180072845113906a40703504080ca019982131005034801e118100c081109240c04d0310880740250000e100074640e05141040146803a041100c8000c1075010a0100103000b070203042c03415042400c1c00c0000520900c1d184100884d20a14243c100b00c01e034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 152082167 1250 152080917 152080939
    0x9150305010f03060504051f02340f02181608151c02130501060507050f0f0616120507050304031d0307050112090501020a020a021309080d1e0510050f 66
    0x482d0000c080815243c0011022070180d0b207070709010340b070859041d695075203003114003040031b0300d200b071941c06170031a900654070781000b0f42050101004454200c0c80c2e01d80d010340d0014130b00800142042c0000c000c00384060a0401c1c500718180090b44206003c940702d040d0381d600000c01203181c0f40d0020021b54030070442216a10686001000b0070272914420481c000c2c94044484007005650700e41c00c8611076503512420a0000350713184d080050894020042c1200c80744201450070441150100c2c045841d282d203803008107a940d0300c0c80620404500f42c0d445020502107039031250b000c2c6a1480c010140f0a0741552135440e62400e140c0b600a1000c10340c0c0f5a8062050001da0405000345e80114001c01264000d1030710011030b01052961200820003410300506e158030001c5d1100749590040398240400d07000303d8141005d03804500407401551138114005112110400c21382e5880e69080d404502c40000030b1004c01c0060032080402400c41c0c5003038501000d00c1106207000c0000b482c0262000b29004010b8400c40024 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 152083417 1250 152082167 152082179
    0x40c08060f13080912010603061b0507020d02090c1b060601110105070f080601050d020c15060d03090515040312200102130b07050a02090408030a150302010e040b03070807060915030501 81
    0x3242c900c500802000d4000307142442e42c0d56082268501154200003002885e60340c1c500030004049000c51484900c3c2c412408010312070240c0b080e40c10b0290040c10807a00d5203070507070801c010042700600d060210b80d014040c441010305145000104040020000d00250401c00000341c45681e4440c2d019030580c3c10002000240c50380121003100c411900c0c1440802d5440c0e403001600d05016030300941c00d14910200c4c044d000300000107480d002c09441244130080319100e260610021140046004d07001c41d4401c2d40c00c001070700300300780c1e1002c1c0010380700e0085003801c0e2265501c040c0410400c200000107100c3e80c424244001d08a4100444825208021403400c1c28180700e01c8801c0341c051050401c400c0002c284078050000910031045855801000c910580c40c0c1881c0070400341d0003c0e1941c0340540d1820164800c80200301c2c4003401a21380584591881c07c00301c2080002078031009521507058090341200144544041020001500454440001e410b00b008208034900c1d6000c0d440d2000c040c2041c004021f1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 152084667 1250 152083417 152083441
    0x61c08070b060a0b0c01060f090b0904080d110324040605011b1a07020610090504150216020616021230131203030b1e0607110603040c08060f 62
    0x40d5a4001c500880d240d90300707000516203011507804198088000241501c24200c10f40c0b2400079107007041621210517465101c807204580c580002190495001e401003804200f000000c0d0142d030502c00c4001c104048031070f00329461071f001503509619815449050344503c0e44008101000c11109440820840e8603140000341050540c921b55460064280b04840900c8070346c040810009190003418038072410311410080d520a411a0300e0543c000003d14081924841400380030b0042d5042580e503c0304071200034490f030003036010340d00160440714841020001603c2e41c40142c0f500c107aa0341803507007145a90f030052181c604080d0b0181a001c3d00041c0002d00f6920b10329491400c1c40286410380340341229440318580081c4a00c4c0c400e4010200303041d0300001d50b050b40d44524034115119a03001e104480320302003840409030745482e00d16850380b9803000b041c02d00d044c00341c007500c6000d004003a8140180d8109020464551080c0c90642d051424000107120100c001c000300c41c0c1211104480320204d113401480100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 152085917 1250 152084667 152084677
    0x50a0201181212090c030309031a090d0503060d02030d020102030a060b070c1e0f081c030c0206041b050402030103080304060507080106021f0608030c010603030906030e03090411071703061c08 84
    0x28419015140100f602c8075522a030710381503100c08010b450a480b0300780500903040300c1c4011280b5903ea80c66901340e03440041246400f840441008021030070144805844641005048070b40160400445c580980c2d0100500e40c5001d1150300010b980303080031481501600c4071a0000d0400304010041d1400040e0791803c0f0304120350081c940031011819030581c1003603240255110948410003014003054074180031480c801840c14000c90101070704524101541034568251313002015030440310004001c2103000002c421100032010103203994585850016040345c00a03002940e450340e011042004100507445007542009280c2000480c0e50f250210084d5100e00041c0954503022101626403103e403e00d41109002e00368600942c2e03200c40080782c400b03008107880e220907000541e4091300007821b103000e44120055020740030042c0d407030280413005000103804080d4092184a1003008040c01141d05051944482400ba13581380c0e940782846410003490428642c07502d400074503400e50803070006038502c0450b8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 152087167 1250 152085917 152085953
    0x20a05040e0606040f030b01080c040603051f020f0f070611030112112d01020c0f0d0303050405070b07080406090e01060827011d060c090d1502070204060303050a020118 74
    0x1c0d8160764400104003d401268020350ba03400d00307040003000300002c2c0041c05058441d408200c50100f000c0340e04100680c1d40ca44009095074000c0752801081c0c240908005074803c02a000c05031500c40349910a00d4242c9c0080c51961580c040858180d040104030b001d280c03282120400a2070655042991921160f02003080052401e0102020854a03486001081d009545045c44038458600589024002c040034901610700501400000740d5051820b0f4840d06224030003d00b070554019419a02030f4010407000c1c206541310321541e1400100800d044004111441c41000200d0f1140d180c00f07806040705806c3d0704540004100000103105446c2d01002840e440740380010362aa040d8488500c1c64140401514000015402c1514540044800d200e1081c4101400001c44203c1da407a41040c2e082030140051169004400c014440041031200300c10240200c805440189070000c583e0000303089030303000e13482100414404201403120030f070203100d503171450540700c2e2010440300c0244da550b0540109a84540d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 152088417 1250 152087167 152087189
    0x6060512041406071709070b0a0e010c200901080105010806040618120915020304050d0605040c0e0901090c09092f04110702040501051215070e06030712060504020a0504 74
    0x10140441507002c00d604010740c205070386003400e00e000001c0c000e01c0300410844421400d5000700305501000a41c7c00d04848030012441e007401e841207003c4400b01000020181084a65040503001c00c5ea0080c100302d00c4005c400722030300e00d5401041440007900d01607010040036454000104204000850078550003640804001844602441260f1800300741000103030035550304000c501c00c400c1d0484000000c0e11090f425a810841001404a80c0c900c0f55004464101c0407581581e80082c01540080380c11a1003001c00300c18190700c450a40c0d104003812590003101b42c2d101c027083c0081c010301940c064081c00912000780240003807070320b1b541c0a4160503442d154045400348844610356028201550040c4030040c82840060102c09a8046a41021005a00c66460080005454600100111005c9481c1005400100268405503800b0240200000280035aa5054442d540e9500006500c00c140070388030001031b0143d00140004890007900020300940c410080c40c0c1c00c01d030304003007a103040300c4001e804 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 152089667 1250 152088417 152088421
    0x518041802030624062110211b0b07080c03040b0c010203070e040e0c1003060b040611100b010819020904020c0d03061a1b070f08060411010c0b0c031e0a09140106060512 74
    0x114501d00c1740303681c48100c3c1c0d120840613000c0000b45540234021158081c50f4110b90310001d40c443d4448564181c814080c030028200724540c005038070a07010b00518103440d030541c1e0500703595042c12425a031004200b010306950002c02c01c001c064100e1803030040200160350170400001e200070250703038078245401d4003849120540188134503144240c12542c082c003040070342030744c84954031000079188501003940d88000f80190141030007400790504c62031140b504141c1d24458162100e005940780c0c2d00b80f034402c000c001902008030b1082d9890350b00060075002006801400da00079428001400c5400e950084400ca4528cd00c0240f64000520181c404080100c480243c50103014486d992605a036680318940380640700200096917000070034894896405041c2186114200400440d0310014128008001581031400f02d0161030080c07014652004541d2070100b22a031041d03c11201441c1d04541c400351403a1078415880030011150a0f94180000080090041c00d081282c06481c0c0d01419403a00c50075054000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 152090917 1250 152089667 152089681
    0x41a0a0501062007081903080c03060307060c17070305030103050c031f0e0708120304200102071404090b040b100e0609060904030c150c080705180418020306240621 72
    0xd10b41c000d1001034111814903041d0320041e228200500e03019408200c40f040050209d0040404032441824020302a005c900e05040b42518007064041040e030f07900200d02c5041c9010020700300140180c90003921001d0301e961551a025180150044405000f1f0300704038054040d21411100f017100780700510364042140507989030740301c1c50b016096000c10340c54801e1490940d4001080c40003140118000e1400f0920300c0e4074401703102162100402054010390080310204144003410205281803c801400031035082465100c00902c070000b0b4030262010741c0c01d8024441d0320800e40404070010140e10703c41d001c3d0703446c0c8980018401280201254001c2d41400c0c006000c15100780b8500030303417a6001805030f54404100c001d11004014109040c4081a005004581e41e0390040c4195402e01c0303040c5015084607000d070340070322014018254a00c0100141105c0c80d10060340e050004604c1030350812a00003080112074400080f0b403200a85090281100700a54000ca4551811f441d8040c0c0d401c2d6140b4bc0c480d11120 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 152092167 1250 152090917 152090923
    0x90a020d090f03030c02120f130509151002071202090702011d0105060901050109082505211009120f02030708070308090607090b04050405100e041a0a05010620 70
    0x300c50580d25141955120070000322901031146140260784c10085200030f2201a603543c1e080c04041c488440c41406690100051003008100071400c2c1c8284e42082c50b920000b10b00700c1401030f618400c4c84c840b50036825105041240e582c003440000e5200034244a480c203444640071200255002c0c2c050950140041e40c014000d4204000e201c00e4040310002c003950004446008003402d481407445038000c04000201584244017645c00d130380320381c0003030195406a013405500c0043c0140001040aa071200c000540d03594504c041d401c1a20550b03c2c0100341003100252a00304681001f40443d890307d000070f200b010400c11824102d9002d89802c0602c1051100c4d00107030315600400a00404140e0000ba40e84101503200755620300851004040301c07803075140c61800342c54000e030134042c2c20f01c1074100b0b004c10001850280c00c000d070000c07003280200010980744c48480c24041d8044406a81c1c59001488100d801d01e069034206500090b07501d4100003d5041100040404861642c000005580c1c2d4601d804407500038 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 152093417 1250 152092167 152092177
    0xc07080702030309090403050408010e010504020105030a050619060504080715020a082d040302090610120b01050c060901050613020412020603060429030d050c07120507080304120c060c02030a02090a02 88
    0x704045520f10b030a21f001801980729008080031035003002c0242c2c0000b10140980c6002e81d905131101400c50340c0301c2c7d00030b00040c40020829640050403044100540303404860140251420742c0e40e01e9030316400d1038244d0346060401d521004070205080d00310700301c00d41e002ca4190350055101d07030320558881e038140081e840845011035010382c0880d184050300308103480c600140200d1b4030980c3d50424541d21001004601d03000320521401041294001ca000001c15901442c4e640c0340504003079061001410419140140480c0e1806c01a9517510611409180440e4507100c1008400801e500e09400c06c141001e03c001001d500a0055070080301080c0144d5568100a032400b81010240300c1070002484000080790b5a030341b2480c068041e004030072070344d03e00c9201100d0340d2440c0a0000c01d4203910b45400b000030708c101d11000b51a2130052080c0440d18860500082000f4030038810110340203107240c14200e2519250f03611080030302880d0681040141c80106d04c41c0701d00f6404646800d1213a8403607540c40040c0c40f80c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 152094667 1250 152093417 152093419
    0x703020c0f06010f17060f0a0203090712050a0b0c0c0a033506040501230d03020c03030d0c0f170a0b0f04020a0c06050a110f030606090a062102030c07080702030309 72
    0x16040013240700b032058a4040e00b02c0e0000c00504502c0c3d4060304907183c883d04d0075104a10310f0340f500c40008100708941d80095410907100d50895055555888610000300300003401140c06401009a01c0c042c050000101d64003d0001c0700910320b401d82d400d102960f500d40310403004060000c808540303d03034a01c00407000c0c10040000c040300c41c141e2000380400820018101c500b81e2107140742600100f0056107920512035405001c103d604140b02c00b001c10441e145041520843c1140301e01040d8480c0f42c0c50174400b030601092016000300d50940a5100a082040043c90b10f50820403140500020f42d401d100724141c210b01d2036a070000b003040c044404184c60981d1200f10b03a400600020780c0f49481075020b1185458140504070410450300d401c080c50050714400d54050440c003c0c00d20000202003c4a0700440d00014014500c2d03180052020204440c1c6200d54020004151700850389080f4241030058600d031448a86011465031402c000d1004042c051202c024011280c04a00c12085407010000c4540c0100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 152095917 1250 152094667 152094673
    0x90d0f03030b09040305071403030613051003020613030614160c0507090c170907030b04031b0209010e04060c0806030d0e150301080f0d110d03090602070609030809071d0703020c0f 79
    0x84c060802806c0c2c0e030300081c3c08640c0101d12140700404008040705880c01030f803000b80600003684104a180c4040d2601070840342500800c0c660000c01640c030000140140c40c50b05203061182451428a40704030740c004a040481194540b04100c100080042c0c40e00d003807081800c1c150050100c500300300e80342030050f4001d49121071920030704510080c0c100303440782c020040b03805254400303030b0341d1406050725500d4900c00180b8564103c00802c000038000e140c01d08080c0c1d8440d01ca0040d20b442e40d000512051020380c808100a140c1d242804140040c500a4007144881030602945505144002c00d555808200c80c0350200000041c0000844d5505828110043c6081081741d440f5615044820b031200c0346403185031071038880c410348040700340d00a050848018003014081c0c0780045003200181c002d06175404007110300780c0d401c01240340080c0c068402d0303034a502e009a46510f054540f0845051400c0b080d40c010b03280829055121b034480d050032400b01c55005200e89805030301e41003840130355850500ca80a1410140c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 152097167 1250 152095917 152095921
    0x906060313051b030706050c0601030b0702031606050103230709020f070204290d030509040203180d0f080907080a140309030601140a0f050f01030e0f250b090d0f03030b09 75
    0x115982103e402c50b0ba0046050300c2c1c8003075864405039076038842d00703460400325040300e801000400c201c0951141d001c5060300540b4a0029603500030f84138103403240c2045900c65540c600600c14003010f50266101c141034001c3c0b048004800c01000c9945803034610031044c0c041e2300015124004d403404000d88411507400740c82889042c40352034003096900c803d1411072445400c50301d03046107a40b03455410b003030005415480740d42c500354120007804080e40c402095a9001d4810300701c419450f600400190310112070995840d0050364607803d00520380000903011480c15800450103009810010600108807507011200764108451044140e040d401801d00d00c40d0300d4014880001004540b00c031500b03840200c01c03038400304035a44494100c41c01c01542d02030141c1240c0c03545803051b842e500a6104030761f00400301c03048445101406c99401d01d41203000210819100c4c0e104402004d404074200e0180103010b1505006007031000c050041210001c0404003d4240041100040203041c0642e0210710071102c0034102c201d6034 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 152098417 1250 152097167 152097193
    0xa09020706061a070803151f020c010e0f0310020d0905070303080f0a0c081612020a030b010311041a0f0f0a030b01110a031b050c09010312091202090606031305 70
    0x306114400c400f1029580b001d404075080c0960111440503522500ca1825512403115208010103000c0d0700c0c503004030342000030854055400529072444a82c0b9170040001658441c0014116964004854010359590506e0744140d036012400c400c555120040c0140c540307058400c10400f82020070701c0544640107042c4040140f540c42007220f032007824000702800040d00c50041c0f0030200e40004030024000b554580108110300c201350440c4440c0d000706e03d440c4803100310001d20b900807a8440781803000807030341d01e030010003295030980650b9180e2030b01d500c58181043d207441c034403a641c5d4844c0920051182c0000456900030750950381501e8588040009560321800c070948090020700540d41c045003c9400c1002501030701c480061964222a8960ba038a2481c050650f21144049003030401281d15000d0207260412980796580958002c600400c03801c040c0c1c441ca5400603106415035005440d40740f21280503400580c43d082205504400280d802c01e82c2ca9603820041c80045400c0d40005009000300c0c01c2100359 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 152099667 1250 152098417 152098421
    0x14030309060d0b031b0303070b040609020405150a0506030c160807050a0501020405040624031104030204050412080f0903031317121f051c060b030303130c09020906070b060a09020706 80
    0x283c00703040d001c03129001c8904680020744600d64400f9941039204014010005517920019038102d445070102180c0035660303500040507a1001c031000b43d0303e01c0405803030785202d19000c404000140015100c00f80385040021480d0b20300e201d80581c0f07107044000c0c411004108005001207807401074104003a60034905a03461300c02e0203507100740b042510a90a008004c15000c1000341e00c4183c158220100d942008901c0d0b0041d0003501d02d480300d030010610240000009a1614000c0d1807090340706035403242c2c7d0042d800401400f11140989a6481ea05209041150280f400001c03260001750342081c1c028000d46034503166104400b800c40700540500b011903010b0400d4070740801c041c043c3c02c0c08210400017518903c10700048150902c25260300440a03800e0140070310101d4100c00006001e01c402180031114400404e10310b500a4079070b10340b041100880e0405022070b002e0000054035000f0310039407900d502d40000501d50f009188010b000c007a21240490340c1552010060b8005019151013551980160702700640 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 152100917 1250 152099667 152099681
    0x15120b03150f0601181d0402010918090203060705161439010e011b06150305030706061a042c0702010c2a0b0a0204080307350414030309060d 62
    0x40400c0d08403c2141e01329004809040540c0c000c610506e50103101e0200e0103c2007135001c1c0059040c4681103c0105924200203821810701540c2c0001207100403030351051600d800f0008002d01e040003030910500184c820054882120642c000000c443c030400021801418140700d080342c200c441d42507070350110507212042c12012044500343c5550046060080042d074210501d031032201e0000d6614003034009140321600030640080c1c01508005404208100003041d000f4898006550303690001c103e40007046000e000d598080c240070704005401c12040144030626000703a0040900b00d0000c0080c1003910880080200d00030000c0c032192300301c1c0307080800d0007034000c082da8010500050211200d90684048800c42d080c284440c419440d034a007180d6444483c1181c001429003d40c0c4c503001c00000440440c104050000c3c1409900141d1542000c1281c4901e52900342c40000541c141416944440c2041903040da03003190480c441e0101e060040307000203410741c815551301ea41d0025001c40c3e0b00f41d800d00c0507070202e5 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 152102167 1250 152100917 152100919
    0x8061b0c06181504030801170304030503070b0628030b0c090a170d110a1202070308042705090c1905031207030905030303160507020604121a0115120b03150f06 70
    0x42c200031100010f141003070700c0844d409030204944000400003100126000340b0588018000d9a092a4495a82074115400300401752131120f408400d0100624104d0f0740044100d100c25440002e078000300901280e03006003444007500c0020a80001020007018000b21416950000c040803d01502c4141f880c2440301d200500200c20321440d03159400315030080103a1220083d0740e10050041c1c00655940740380e80c404c000c801c2400c5004913400000010b40d0140540007134542c0d500035a0f005100c1d2810001840ca80381c111901050500d014031a401402081c90920154240c80a01d0070040c3d00403015100d2800ea440580c03d44554400c40680034180e03800b50a025110340e84450210f51b03220100f59917800700b990111074060071500c90b954042c0c003039001040c5142c0f02406683c01c01c1d60340d034510300c41481900015202040981a1100310361400b42140340500051b4210340210751408800804a9010050b00c06205981e040070440982e0104510100442050010000c03450442d4550803540820359020b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 152103417 1250 152102167 152102173
    0x7090b070b0103110103230408040b030a050a0f060620010b061204060c02010509190c0f060507110306011412150c0433081008010f0b0a05060408061b0c0618 69
    0x10f020540c820301510740c80c0112907081c01c802c0710100c150341c1e1f00348074060302c11518004108070000d0103076000c802951091400e5400090716140400d000002d070b031450350780c500350240351100c00d005e1660801d40c50012030001580c03511840c4c0405044a0040610020882d0311103008150099002041c03610148560b100b20030a1064659000003030742600c0f42034426420a0b04000e04200b0001207198120740840d000d00112058569181139803020000325070000d0b0f001030800212941801820525070700395185c15002002e99601d4540350100030210150a40d11503078883c80e200800307010410941145400c420414409802d0802224515500500c1141c1440e001003514501d007100112000c08030501c55a002c0158042804c2c04a03141c0c1d030000e141c00d442d0741030018082082102485030f1101c0744e100384030008403130614004114808405a000c24403840f070400c0148003071a808038540d82c0200498080301d0307241c403504070b086460740900505500e451190703000300000e101c90840300801d9080d40c0f030f0503 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 152104667 1250 152103417 152103443
    0x51512030910050a0302070b0708090f0c010503070e030309100905090709080a0f050a0c0305030a0315030213091a0f0406050a09051507020a081206030c18070807090b070b0103 77
    0x2094480c00790429480e40655184099401940203d0007000c00f13100926005240c161543c0d00c918040105840c884000b40c13000c020005112001c0060205c540c5401d00208201c98808c40000e02d04c0c03000600000c10080717401040d0826440400a0f50351949000380201d04599400100600d401154480d4501c11014100400c140714010902001a42c0340a009002c804031162500c0012501d240d404580320b1003003d0b9503034085003040b01c800d00a98403843c0615500c80c0000002400d8400d44404425013190100c010001a528000701244c8440320100c04100c0f01c5250401d0b00d40b01e40310300886080708401404025254960031503940c400c3d0b04c21b03031040003141c407040054011950680c0e0000d0241d40400310020004030144650340c1e014100c0e104403a242d08196a507000b481c0c0203854459002c409807024001a85030a00c444405640c050789d48044142004806038480d24001e40060f081c4030302c620210301c10b1031182c52014050001e82d40425a10704892410700c5100009220903214603104640c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 152105917 1250 152104667 152104699
    0x6090e0318060a080a020708042d080106050102071203110313030308010b16060b0301020d0f0b03011b021203150d05060714190e040207020a030b160201090309150e040515 75
    0x50f1504000a9a2450265500d03c2000c2c0025440810140c969400a0200040c1a2907100c010110703462240d480c9039400700403560f50000d00900d13401c10000c0340d052107003c3c4016680065094101d884640c1c0d8901c14641904040e1500f071441c101600740c80c040080c80c54051402c3c04003038011244603039528050340c0e03612106040c45d03000d100500d16140365184e102c01c3c0481c1d40d03500038480110b4002c000510b01031110240c402101c2c3d0034100710900d41c2e22420742c07503014076007841481c1c800d0034030075a80c0344d01114a41000b921111100da80841001c000b20100c3e0183d5409403d404441a0107041e07500b0300303070050a1050791004100c900700000b469028043e40781c600a9801d0310000c01c00054400c1045101d1201590206404403601b50020f5090001c540507a46242c2c0c0030000b54010003102605041201e6801c520340c3e4180d40d04400c0d60f040c24030301800207911621040c102d887e03030080c0040d00c0340801001c48420318000c009684c01400c2c8414041c0410a00c5074030600d080c07084a000e04501c0780e0203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 152107167 1250 152105917 152105929
    0x11030c03090603100e070504080f120405040f1418060a0b010c030503040501060506070c091b3501030b070207090b090f060d06090302010614010c0b0112030903120e01030b01021b1306090e0318 84
    0x12f00c100340300d007005100411075400d05402c80c1c43e031481041c17800b052500c0041d0f01d50b000f4000444001c10140310500041460034804c1c000342c0e8000740710300014000b84581c000060081c0c0c140c550001c04000b800400502440f1080d4031038006018001c041565812650410708050216802904001d9103440444038108d0500081e0300b080c9004d80d101c103030688941e89000e0504040080300c00c0c629640000801c0407035101c2080032070185114460048490400d82402450050389410400701c883c50311004540315034401100315803080c0940d03d2a0b0030342d41c81c400880c0d8450a4000014810742c10954590101038064010b0800d546408009001c082c40e00030044500c0c2c3c401c0c517000392492090100600580e442c03507a86c100d00901074241408030320380e281da450b00e03c0001e510780e10f000113541e000e2907001503a00d0701800345180424801040c80c5080354021500c0b105641180d0303881180352003240c40c0310014a400601c0108880c400410081c2d1010b4800f40d12544030329040141120480e02c00b040c02d14000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 152108417 1250 152107167 152107183
    0x15090105241309020f04030309120b1504090501090606030204181a070507050d0509010f0503011d04020f0a0603060311030105010305030a03050c07080c0102070311030c03090603100e070504080f 85
    0x1003895a428001401001c0a66074040c09440d45488100500030621401500003803000d88100b10354039664900c2c50600600c21440f98000881090810851300e020400807500b842d00f00d0148081030a0442e0400005401899403000c024201e50034035465106004056102508a80c001c0c0c4090115140d0b10441200001c41d042000b00318486c04881010510b0544103015404061030a00d0b07481c006054841c1c03803500079801c9000c0b00140001507404002e50b444528070f81170400301d0402c24155410a0510640c448441d001503d0000143c00045d083d95903195801c1c0b220640034003155444e507140d0000402401c0300303000c00d81d1140b42e0507444081c641414030485040742d070820080d6040c08801c400c00c03009020050b094111480b0203201c00404100681c0080140208a600050f40e8000e14600504204c01040840742c0f01d4206215091084401204480c01c5040c1120090b5503551040a400e40d0001c1e26005022076001e11410068840c2d0413070001c100f80d6804c0821503e030840b4020000c0d56441007 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 152109667 1250 152108417 152108449
    0x210050c0d20060f07030605061305060a030f0f0212150603040b070e03010c050301060828020d0212010b1b070f171507030b010908060402060301060804080705030315090105 76
    0x486007444840d1031041062031030b0140510b42040b40c1010ba20b15207464008250340302000c200b40c82c800e2041898040c420b90005002c1500c03041d003410f200c048040385400c11072203007038010240010f89030111b5200c1d6110b0304828109510411a0700c0c022502c040c02900140e800c81990300080010031541c10950000002c99100182a60b14503074540d56030002d40c070300142010050140045075810203035420302030151105070580c1c42039141c0d031602d0790003031850070040e0980144201004410744007020000b4030714405a1002409031f6a810a11100c0c4020300c500521421180c10000c0082140c000c060002d180080c00820601c40c94a403080c1d0303064444130240f01350b80300b008010307404100400d210388044180d45200350940b03039902c030000b11021949038211044000203507243c441c00503960b0072515a41c080d114800060109190070b60105545200c1801400c00344490940010200b1203240c00b11000150721000f92500d038100204584c01c41076600c00309a100f44030b05000840c1900b00b40f2580001c1d100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 152110917 1250 152109667 152109673
    0x30d15060e01032f070512071e0209160c05030d050604060605040e01122a080d0315051309080c0a03030b04020702090406090201030e0a03020f0708010b0102100f1b08040210050c 78
    0x7144600701c881c0d013440c503003421510410300804001c114280001c2000313221150103582e0b075110901d8000d2070032000500360845c4014002d20200962100302501341c0c0b045603d0003c02c44444d200d6401d940144104800a040b4032000890403215042900124000d050a4900f48405500d03020291541e001d1402482c1c0c908507460010400001310001c1a802c060240b45e000c404028101800040609122017400d800c10706082c003004500001c00103160082c2140ca002c210710b030303007502084541038521b01c500c0c0e11800c11020380da20b01821551018a20940c807002095075006410300c40b6450f0300310240c041c0c0229140000c0c407540d600b824000c8401080c3d00900c89070350780e0303155a1500010b02122000783c0c1010b503101240403840d0001c114022145010b5001003c2c000300904c03041c0c0c034000554004080a90400c10b8440460360000b071a580141c01c3c1001c04a40001c05c0d001e0003000349482980e0f03192742490804081e1000c5d401082c924041d5000ba1000010746609202c15540f500c210380056826034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 152112167 1250 152110917 152110961
    0x105070c120e04020906180907020d050406030905120a0206010e0603160b0d0b0a06020705030105090712170d062c040323040e01081f0603030203070b09030d15060e0103 74
    0x1807050b464601030740c500400050400c1c8001c0041107880e00070b802e6964142c031102c004107415103040703004980e02240c140300426407c0e003641340041007809184200c0302030540f116400401c000b010301c442441041c1c19203610b0703221005520020364504080c4a8590900285000b184140c00d01186011030a60003032141d0b503003603141c220329035040d500c61840000c0140c4e95200f5110307181d03540c0e030b00400244002c0e402014140e0a22003054210f80000d40714041541c003d41d0104140070812098050007a0420700d141c40a51a98802e0f603480e20441e04014402440d000780450940b50094003000741c81041038441261100075000b4190801d02900e0180101e1141114080c8440d80645079110501c2002c0401e41804d658141d207440365002a0007020b034540100000084094040d088007102d0100d043d82401300078950780b0041e4aa209684014001209420010312000001c10440302e0300c9205031070400440804a00300907101d45a0300030040082c2d07880e60078440300e44c802d02405180102d0024107107480 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 152113417 1250 152112167 152112203
    0x150e0402100f0e100905010306091a04050c0f03040c0e0f1b18060c1510060503190b2e0e1e03010b100504050a060f05120a0e030412050105070c 63
    0x3201c0c820b11050104121500044003980302c118400038029210740700ca101013400c0030005001d0705c14079040b00c184149825040b019030600343d4440c2064007825500050680c848440030031803072241c040761031403004000003840104009a1001e42c103d80130003010421a40350164800d0100c18140c2d20056036a242540c0e01040c1c10100000344402460405580802c00200307000c50034680111900c600c054001010414011804d04003040d8040114000c05115034100700d00540180070140800c1071485290521140c5942d00e540100b6545a0091420804000010015402c20040c1303d000c100d00c507020f007008d107c007800f82201c1d400040d401000244500717a0500a60450342d41810340603815921101c0070142030321071281c4107038641001c1d541e40d6a580d00300f03c2400086000d139449031080190414070b2400c883d49c4501640c10880190850740025281d000340c00b40030b06000400c1881e07034000010009142541d03107001500359031041e0024803041e42c494400356102c0130684006043d04141c0a299000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 152114667 1250 152113417 152113427
    0x609090903090a03060209040c020d0503070513030b04061b08100522060b03040c0b0301060c240c170a0501080a030503181e06060405061e01050d05040303150e040210 73
    0xc000d80d0308044034204220300c0c00203049280320b50f02c140da0036607000400e000c0c60304048c003031300030904524001490300c0641284002c1003403000614074000c100300030a00a250400c840c150324021a001804002d10703080c1400c10100070007100b03032032445807111407290042442c01400b0080c825481d081c6001941403412043c412543c102ca80c2e84100b611101c2401038041c6100d1080e00e010303100c80035006840e03250900e40070341c4031101c0d50440c900140c024401000183e9101c406000f003a9409100108201800c0b005500c0100c0d010303801c980e83d181890034110481343e010000c0403090814280600450b145c0031140310454400303008051a42c1c00c001041800700740540c2c0110341100080c8001c00030003860014850420102c0396101e18209003c00b031014088408008480e0001800c0303030f00300214108030000400301c803009002000c6e0004503500b0403220342c0c0544d06a500c14254004184550700c1c0511340100104030310f42c1e2450885280c00b00c0469182c00c0307402000d201e0ba5020b407038009600004001519 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 152115917 1250 152114667 152114671
    0xa06022a06071b0b0723070507090c020a02031f0605040501050d17040f080307121706011b0c0909020306091c03020306040b1306170a150e0a0209041a070e060909 71
    0x12240b007110700035800180344d45004912420301551000360060750340140b1610400c1d04484241460030500040c804920041070060455481d5200000c0a10702c0e400141c4c1400b02c10313400a07605018070b500d6900400004005e020303061480c2d5a0070800f150711102040304840003030213420303000321000101c00002120a1003e6010300b5041344407605040d502c0d920102c8921080e0400540c6420215610f0104510755242c001184078509000300703004d104011100400000130441410887c881c14a40c1010855502054100707402c42d0791180c0d0117440303000403006000c54200c103d000e48900c03c00109540000b0980c03c41c4e010346014140080161510110040c0d00045c0c04690301c030b030340c41c0000f15150381c03103080500c020103c1c07500211700e15203480344010890303011003a00315054000055000010300c10b58103841000041c00c038002440b00c0260081840c1049801d8000d400060311824070040c440400710030301001e4506143d003119a17503581e50448160304024441500140148883c00c403602c0c18005d9a9 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 152117167 1250 152115917 152115947
    0x3080a0507020901030c050102011404050c0d03030e191112060f04020402040e0f06010e010806010e0d080d18050c01020102130302120f0316051209032109030a06022a0607 75
    0x141007880503000154910405c5c1e00032508124006000c20107540c082c02050a0088030f001a84100c3c605904c44a407500340400b4002e20800c4101620000c05019511007a4214840307421125403602c5d241d802c001d8014803020030743e005015000410141d280401490b000282210081c14071a00d0352400000d2500014108a910540074400480e1203c3c0d02c00025101d00c83c27070454030003981440c000141482c0b055408890402c032a940400501d80d0304840c0b00d440e20786091f01c824450054070b00f07005030980220007640c2c0f91242840c02c000980c000040f00940454010790986080d080030000580c00c0344600c8100c03044003540c0315410805868244203070805c51503600d0030381703032040c2001c25501d0859022040b001c070482d41c581491800c0c46002c04c1002202a980c0c010329241c02103220000740e031103054444012030b181194100b00d04070001201910451140902107542c0200c40d4a4114081c2d004691005004564102d00c40c0d1042c89241500c99140c6180c0040e0010380c5540c6000c433480c800f40c2c542c031 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 152118417 1250 152117167 152117177
    0x70c0818030708010e0c19030609030f0e0904020109050607020303120c120108010612080c030c01060902130e010e04080a11060721020a0906030b06161a0112030f0f0908010f0c110d05030103080a 85
    0x40409d80754081e000e4002d00c243c0c0d40fa03140720120b100c058010031507061780d00e000394961b408010050340c001ca9280280c0340d08440580d12030075140b001900d58861801000081d01c0d0003401d1050144003040541a003200881d0510220f81c1c071100c80070b0880b14036200d0a1002400105090045001c0c0c200500b200e050700d805a0f031820610f04411401d40b6103580c850480c07140d0001c5c03c000e01a501f00614009070040048000107941340c4800c005031042c0c06480940654000502207102e10301034009100e070403d0010946d521740c50540005050340000d8003000c81c0c001030000c07851000c00028405ca4440a2030390b1a45520507090034812001040d007001d107181c100382c0070888001401c46580402c1800c0e80f1611041140421256196943c803006a0206070001111244000000c0c1c000c0c4008004541e1440c00280802c0003c10403260f003001a442034945500c2c180b4550000e4096820508020b612a00ca1090600800e86001d40c0d40c0140039071480060000c1c40180002941c003c0180103810342e620305 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 152119667 1250 152118417 152118419
    0x90405070519170d020d14180423040203070501081e0c0c011503020f01030203060112050c0409050a0c031a030703060506030f0316060b09060d030305070c0818030708010e0c19 77
    0x3c0c00d00c0e000c548035401c000e154041407000060550410240789040c50a1400105542c03001a400305103010f00350f5401089003c09201e0403058860ba8441c498034903008a8080c1004044070340c40090760001c1e03c040c1c1c0640035544000c10154002d00c42c490041500080c156008101d0f5800902c583e80090442e1291810821010400ca142400f5000b0040b0401c1440c0901a15510400044002502d240d0b8180b50041c4104081a03801104121081e0903071440404c00b951044050b9029100f0b58019080311464403080c031040350b4155008094008140d1000c01c0b9890003061420642c080311600684d15030300289043c4002902500007503040321000d0125415008042522801c6030800e004415140589550500c280461800b8200c62800c0582d05094142030201c041000e074134900c4005024142c8030390100b2a81c034425400003401a0300310540f291600e1403261483c50004120102c140b00f8407a14502050004041c070400d1956401e20000f020440e000d4018000f43d84a05034026204100c0d60034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 152120917 1250 152119667 152119679
    0x90b0a0e0d1d03010e07080d11070b22090c0509040b040504080306040906090804030f031409010e0d11121e0c0306160c080c030a090909121202040518040b06090405070519 75
    0x31b02c1c0090094880074106c5140150001001c0a0104082c540d195009002c10443c2c0f2110a00700c48461145000790452030b0880c006c05009482254803654405140802e0308042d10344c01805070001c00b00403141444542c00711010803050726800d85018007804410008124a45016442411014400c8401003035845113030f1144407254109500544082613000c960404040d40182c0c96003141a600340c1d00350402e00950700081980c60040d8009004008845141c400d0001000d5540b0411200408818001d004024416200e81c41000c450a441c5000c1d01c0000307200074041100fa1103403030040c0040541e95210705480d407410011f440c000d02403160410200000c0380341030006152019040000f169a0642004000c2000481c0d501900582c1c0c907210840340003540f00c1980f500c1403001480d225400f00d541d550000000d2086074049644884e10400410b840c4000d145001e01c1755008d420a2074003555460188201901d080328014441d803c032003014401ca1905403c0381014283c0d0003406114161148 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 152122167 1250 152120917 152120923
    0x12030f090507080309030106050a03030503011e05040905010b100c020f040b0d17041406160605101203090305060f0c0a050f12091506010f0e040f020904090b0a0e0d1d03010e 76
    0xd0000c5505130000500c00c0c03074904003405204000d00707042c0e5200212070300d103440003825400107026a01844a90a030b429500030010100b00002d4400104108845401c0d464058000c080219881d03001e002c1b89140c1d500c03d01e002d1080d01940c150003500e10001621901c0400004194041c0c51a901001c007031000c10101e01000b40c00c41502c035601c04031565803400c01c0300d0180b40048040c0041d12400d000c0107401980d96000e4040681d0580c02480420603480303911940d10100b580d0b80200010340240c80b900d0003410780c4400010102d0b4000e0702a2001c41c2c898501407849c0e5503044032159441002004040c111521841c001d0140c0d01040d52203d04011210364440d800381e0081c2d480c05140e90202c01402804000312482075080602420002420207803602c01034110a0b001001071301c0341360b50744c1d44008405056011a540703103d0060040012004502d000d00d41d400003034545280300340c42c100d01c0307200d1500006410304003041a44c48640e1462040c01d00209409a03900055415540768450310014040070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 152123417 1250 152122167 152122169
    0x702060f1b3f0a050a0203041a04140303190b040506100f050405090a0614010201090203070909020307030203030310080d020c01051c0b151b03040510050a11060708060a0b0712030f090507 82
    0x40106949800d009104800303403080a01754406840c410814000011a0804400400c0426020010707140e0b5135420f110032650400303605480305001c00400c000c8105103000c2091128941d041c3d040000c07102c80b074184011218100e500603044582d1140c6814a20b01521800c00c440450b0700e4002e03d4103403030300c0214015070340644807008007588482e410b0000003644082010b50310400c2c402000710120340c1c0c0010b0351b2240c5a1143c03e10840d03a50905e4015500c0510000c406140c000d41240c0d03590804508002c4454082d20a01d00300b40551207080c00300700d1000c504c0445213501650b42a00300a0250005819103802003100160a5034540c2d00c03007880e4407948007942801541000180d01c413464441404100d110340c051007045904100400d0010b07940d8089140072180701442c1194031041401c606a46078014086125030a1250b0030801c11402e5020f0802445000241c50b14038115580341d160707420034003031841c0040c2802c82228105407814469880480c00e0401e900e400b103269000754580d281060f0803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 152124667 1250 152123417 152123527
    0x1f142d010822050d080702030306010e1903050f030304030917071806031401090606090e071a120f0601090509070f030f0216060f050c070c06050702040902090702060f1b 74
    0x904d0707005542d6800c03c44980d4044803e0002d1455460010b0000b8101120f516410b881040c84146151a41017512000030166600c80b084641412501c4201641d0f504211030403400990140c1d000714400544040c0e0421519040000781040e908107281c0b409151041419451000e548240010100c1d0314001865400c1031130100000d02000541001400e880007070f0007403480e4a050880303c900c034090000d5008100c440c0c0300100b050b402c10803000494a403040301d04c4152801640b0f4140541441c660411900402e030980b98104855a50b105114440303204840c20804038081c45401002c0c0c501a4122014040301e111005152180c0031084590001c402c0c50184c40d500e5968039a82d400e85e41038401c464100144440050801c041a61144030400090140d1410000007003461021500c8540010315820b0740201088042c0ca01402e0095803100100da0310410715920501191108444102d8101a14080034a6078a020308418843c0c4851000e0300843c201c5890001090011a0380040d0015041c01 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 152125917 1250 152124667 152124673
    0x31a0402011b060e2a01110a1b08010501081c0305040c080d0f0210090b0118060e0141061b0102130f0905060901030b1f142d01082205 59
    0x2403c0c0e0700e24a040b80e0600c803960b01c00440113103a88205d0640c0840744082000b440d1051210010204403170074081c400000801c1c40135204c8080400c0414902d100054420030b030001c00160784d0b10011aa95001c8400c1c1d0303080300380a5004001803181c42504003070790080c01264030740c0c000d03a985c1c99280c1c039007501d4541400004000444028105034140700001181c00100c0d0b040c044503185441d0501d0120046c8036104407010503c2c0c1d00c6d2000c44058110500609040c0010304182d81c0d05c01c0d292a011100c591600011070308505400c02d28440c160b044042411072011a55440704403c0c1406200d40c8504002000b2041e020020104004240010200c1c1e2403e6802c98221a113030100c103e082c540d950b008040340362b09100802a141d107a445000781101d4109100001c6510354450300240100340345600b5141005120010900c070500000035216041c0c2a104105546c2c4514403203c040412440f002010000c1c860285000d58807541f8003a8000c0e1800c58103076030302c41403541d150401d100641000c0711560 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 152127167 1250 152125917 152125931
    0x109050607050315090405100e0a080a03141e0103081b0316110306091b040b100924020703020d020102010e150609070306120320010911090c04031a0402011b06 70
    0x3d485458084e541c600340c038001c0316401e0507a00e80b601d44640300f0010318955501d4030044101041001104805a000b860036540c40d10400b0009015060420203c054800a80701054405c01c041d5151000182200390542c050390131075582c1d041e00e0f80a2850b000030b10b140c42d611040013071001c0c4010100300790f6007100071000d0b900030703d0080c03080c00700300d80264441d41010b410881b0351400819044600540e111100709c3c510841000034000f0441c440c130300c07034111028007698001180c200341207034282d801420030140101e0001c54001c80c0d003c080c50000b401600884400c20050410106800e0050b10500000c100e80a00c07406403891300081c01e991104051406d4240704040c14501d005941245480c50240308843c1014400c2608215107000101000158a00607841c0e52030942103421100c00b0400a0054510f036080c903000c5440c1407040948034074203032008500c91042ca13804541c21a079000d10000301d80c945402e2081c980c80d80017030050307060100c01e207126540100c1c0e035411070780c0c1c3c0c0b485000002445 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 152128417 1250 152127167 152127181
    0xf02040e04020f0609091305030706020a020d09080705011704020411030f0a0507031a06070c03080315030106050301201b01020307051801031e020a05040506130302100504060c020609010201090506070503 89
    0x260307407008074490051804101505c010b071605150b01f40d002446041086403500d440c40e0881c0741d4810703810090007003031000c9085846150701064042c2c1d0303004542e80342e011441e19000b019072501c1a074401e1902140ca08007003420959101056107600600090000400d80180d1003208a580e03c1140c0790b881446a01c420052801a188582600700c038051a00b045411100e021054403200f2202d0350f1072080601007524002c00810040160203550310241c03181e1a4208004e851500d100c114401521039400c000003c10681414816102c0400e010031802c04011902a0001c0c1c95a02c40d29001400d0840480b0100c00b21400b40010342c09090903a41c6e40d540d410700d01032130001c5542981181d60401d400c06001c01e0804948a0740400c110542103001030369503400d03c00580d901d101d40c0d400150020b8000c03d9001100350450510821039000f13031550001e880304508102ca0701d2169018207004141104d00c0000942007070070103844110418000024021000e4030352034940b00c0212000c0c80090030002c100400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 152129667 1250 152128417 152128429
    0x30b0d080405012006010b070f0606090605030f03071218080d08010521060606030c0d09140f070b03150a030206031305121809090109120203070309140609010807030f02040e0402 78
    0x40c51041c102649844c13032034106a1510780c83c042c8140558000b010034800184482805511103075a800007003007000c50755803c2c00a001c0c2c4580e01c200b034824011214191658280481228105a0b0005503110b2071010810142c0e4034210301222644144a019408184a4010804002580c1d80340e110f02c0a2503141c441046074400d50700b07010b00502034621000e40d041c9207000480540041040312050780320394942c0d041001600034103040d01402ca06000064051000c18210035111250000541c1c45845260440c00da8a1555204d4080c84010400c00203003d0024403000c040038640040c40c802c0b100e170baa900060b8080e00241c0d81114105000b121500402004102030303010302040310702c803a00380b4003082c2407681141c00324009a4054848100010803000080d1300106501b98481c5103200310110f5444001c2d96600107080071004500e42110124140d00380e6202206a060300628003458054010011609400c0c050030380c600b807540b00c540b442d200c1e10150014001404206001e4082c5181038010810 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 152130917 1250 152129667 152129687
    0x3060f050a0236030709020304060506010507030918110a031a0906030714030f01111809010b040303050a0314070e0112050c03160c061a03010509062401030b0d08040501 74
    0x105948104510031240d40f81c1800807070203181d0a20f19040184014410b60500f1000038041a07040c06504030101e002400e035409903006d940202d000300641c0d40c5050042d03566105110020300406c0c045601001852b4101c07905081d296007000d804180760b0040b81809042d900404503800c0840c0d1100c108075681c1d07650440c072040e4400c1c00c80c2d15203480c2c00c2c05d1740403a07110700039402030200c681091200c0301a1070701d040008419a02c00800200501400710005000e00d0300290b01b01d40c60115254030101640c0703000c81b03070306041c0c5000c034011518181c9180d805880b20f40c420200715082c561108840c00a07000502e01d8203100d940c094840b0078584212000042482240704821f00e109031600060101c072000d8281602d60103041c0c415a43d2262000c2902580d040500c072600625503820900d484085030034144000445050940c0280701e46c1d110004c02c5034a414003218441c03e008094485410404100c1440254952040c1000103545000da0f01041e0303c0c1a44130001d99101038001010040c6507841001c0071 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 152132167 1250 152130917 152130931
    0x2060c030706051509071403060d02040b090406270203070608073606030e0604020d152a0c030c060f06050603040b0103031b0309060f17130210030209011e050c060103060f05 76
    0x401009981c7c1c189620302000d070099014181c1902d0000854656500c00010310000030710b5803c440c070709480c10002501818981a002001a130b040d94884454400c2c158103050f40200503100180c201181142c02100c000c0c00c082c100140713100b0440700395080d0442c0d160b890008800725100b1f0007640810080420142e40544105454040c40c0c000c5034002060154219a044549040c9c025050809007140450b41d888465118900710a50203180c814640d01003c5070306611300c444440c520054107071141c620030800500070800c0c010007000090b01940c032180b1075503425400003444903181c102040301034000319022507401c141600140241500030082d840c0c0b20a4244001120b5034403079800400317554842c4a000c0c20b0011442c49401c260b4002c5014600c1c404141c00f007910380740350008240019200500080c6d000d40b108504c00e1400912a008441560806031641c83c881425050005405002d00c010041041028098885203076010f010030b80c02140129004114101c40d400000212480940f1503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 152133417 1250 152132167 152132177
    0x3050606160609031b0f1202011b020303070e0d02012120030a0608070f1e0b07060f0b04020a05160c030f050312061c031b0c061d1c02060c03070605150907 68
    0x480c001408041c20390310ba1076008187c2c845600d80d40c0010781c050a045801c804001d0310010402003400e500002540c4150a2650f0310804010008140009070504541c00303400900c0e8000c02600b4a450040e1590f202d00f0b183d600001c050303003c50304e00b0540384150080040160400400e002041d43d041c0105005006c842000c0c0001a150000b0103140b0300e0030744200c0d0503100781640402c1016619121280043c14400212981ca909924003a0003c0c40840c403120b039040c0c0b5108a60b61130742060300c00c0d13540c4200a520b540389000140c02ca03c1c1c506070900f02c0100e9020b030349041d010002400c000a8040030030f10800046840e800058031100c804000101502d000f00c03c0003d65603141854492941c1031950503080c005000e400e00360f03204a640c501c541d8080c01d130002494001823442da00c80d40d85903824508801801448151100708201c03044c2202100d0844500141007101518141c3c000b8410042c0e5281102e00c0c4c03201650700d80e4141e8408079072300c0c1208028980003198a040c05000b1651141040c600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 152134667 1250 152133417 152133467
    0x60506030c031605090301050c030403030e0105060604050d0c0510030e0d030c0509042a0909060b03090322030f0615060201021315090e011707051903030305060616060903 75
    0x600107000080460602820250440301c3c0303640a4001c849410760050000c0c00710346020181030a281c2d105640171000280f902c030407010200418805c4901074040245030a00d0310b40340c40300f00303d180c0e002c280381070300c0d50340c070410300002c4030341d00d408800681c030a49403404500b4941c8880e003036050100d2004540141404d10044078100d9030300138116040d4800c04c460001d01200360218482285006554070100100c14200d00c400d2203401286000441e0b211340c0c0c3c280400b03a224213000d4010b00060301c103c05258010320050050016540c00480b09106c09034070303030349180d5480c2c440c0c50440e4911002074590f44d07039425042d540c280410070f410010700010f000035898014141c1c0455041070305072003079103000b03040e60b100110313a90700c00d01d508001040340c49075941d2a940c40d06402e46000c2a034510507803007845074075070000e0ba80c204036805c4052117040c200c1c0440030f1403468506601400004200c1984a10b00b000740d1428400c41038544d10060740a00c0d4001034a03400b80c5000790004625115030300d003606500c04 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 152135917 1250 152134667 152134681
    0x3101e060609080a0b0a0e0f0c030708012d1512050c09040b04060b01050d1d010501120507030305130909210302030c07020f0d02040603030f1211040509090709020a1206050603 77
    0x50307020005038084505e828650b50000b1000c000c00000e5446070703050288200e1522046400100c51890000880036200710b40e5481d14440d00f00d400e98400e859401100381c03030040c00801c21081034030b200a000200460003401500b036040c3c54404c01d07041400a201000c18400034001d0401c045c03a6025030075901240181020f0f2952220200c00802c0203003401d4443d2403000069129005440401c445540284000c00311880502011010420801125883d00300005000700308460b843c0900b98010001d8045a42180c404413840d40c02440c40750440100c9a00004d15462540b0820340e0041c061491300041c000c07846000c41110b0b40b694071450401d0300600510a5120040049400381581110380a404a5900c0c0200b0810100d002011350301a24004000003030607000300d0b1103c1d0035801640c900d5420714844c18810b0450360001c8144450140c01d0009002d54100525507680000c003090490781c40130b40d1100e0f0f1009992141c1280d200103100b02441c80f00038429130040303401508040359010706601c0c05075 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 152137167 1250 152135917 152135923
    0x2030a0801050409020f06040f080609031602010c0302011e020406020c0f0a050103092f120d1b050f011d0d05040305030304020f0a030b09070303080c030f0402090603101e06060908 79
    0x70103203610a1303550345043c0f01103558101c50004140c1020f09001c0d05c455440368485000100307072180c001c442c041c120010300658400300440f5141290101802e0303a100c004c3d00111101c5a203c2c404034155966118601d4000482860200000c805008090307691410301c2c100034244241048000d01450400c031130800980d03100300700082912420310f000948940f150801c41340c0021500342440420f80b41d41c0c6946108184a0364482c4405000d0f40c1c1141e0503051740050550302c2141c04014400901e00303801c48070780c1007040c621040fda1401081280c030181690300c2601c2c00c6444281826043d103010704c00c1851048018030860f4508442e60500070b05180c51078903050f4581c0301c01003000b40310b2246140c4c1d03861540da5844c19400950342010b1041c02e02c0c94800f00955a6100d10f00050707020940c07a2000815180c9402c00701e920528084810807061b8941c0d46c28041401c84c0900003a80c9405100d0f18466400014410045803501c0110345500c00202034916104442c01030f0080c00030000201d0040c40030702c2c400 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 152138417 1250 152137167 152137169
    0x50102010e120c01060b0c0705030606101d0a030803130606080328050c0f060a27030e12030d05010e0a020c0303150105040f060f08101809051608070e0702030a0801 72
    0x3440a43da00c4402d00c0c102801000245c12000b004040490342914030200050040140c0307405404460b1692200700810542d84507140605002441035002e40074a028500d69022021402602d4401e0340c0c0c1c0c5950358203a06400444d556440c0304c0c115503500c814802035004a0004190100c042c62400c5124600d2210b900345e4894950074405141c103400510905c0b403821100c1c0c80c0713001c40590b54080841c514154650b241610204045800c0c60f4480d208200f5150414455402801848807100c0441c6d03802e0380e0001c1c1c5c2c40039850380700310070541040940d14240010714090354241c000013910760429241404180c1d010b403c401000c1d106100c040120040001160b411401e449954020b85c900800121014801c5400c04ca03241081c0000029450390007c600c110b03941201c2c3c031190401e9031090fa80c0d20040b91648600302e6142d51303160003000915490b074024200320b40103205030f80242103005246c882d0100103512443c0b1b682e00101080140303020003a00710b074210300184040d51400c2d00d4003800a04d84401 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 152139667 1250 152138417 152138443
    0xc011112090a0302150403110109060e01112107021c05150c090a030303061401030e070b220f051003020403020a0b0c100c020f0f15041b0e01090207020406050102010e 73
    0x20000303926a080d030700c102c800d600071940203103010160084180a89515080703803004488880c400c1420101642c00340d901001035a500303a8545943c5003c0c0c13001112070944010200c4102c1c00781d451180340800c05040104c0f10b040b00103098556810a52060140882c0044001c4c840103a41064403070009102141401000403441034400c81c0c0e8542119a141d0f0784680000c0aa100354071441c00003c0580540100007140c0d00c43e8800b0020303c442e4030044d81a18241e010341020b503001908188840c3c224640030b0040401c6400d004414042446000c01007440103030400000907041d10008c02561074883c1e011074056189140c15420203181d40d01084100d5030700c2c020441d12040104512000c8081040103039140840400184606a11040040e4a0f0540c005000c0214060007040e0040c1c51000224414800c40c2a1803a034000da80f151104424200b40107070711040c003a5220b2000810310b0f031001a0714013825407044016502d50207441000200c65070350f07000c14156410302d605003640d007001190003a070f4191 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 152140917 1250 152139667 152139703
    0xf0216030f080f03090604060501060e030607080a06051c0c12080910030e1903020d090f05120109150f060509010b030703111e1902070b0331060e0c0111 67
    0xd076140c40c2c2d40074083c2e0319020070040408020491182000a400340c0518004c040c00c001c00d90701e031401119882ea08214494156105201040c080e40c030a0039410350008040ca0006009521000001d408c0c181c1e05002d01c0482d44070000da1414800441e96100040c0180e040120000a280d582c40c038444c0159045144900410351403103030403d029800c2011824201802d99405071100c00c5140c4803c000100140c0c0184900c3c00c000c04941c0c05407940e201a42c44081d00300035058075200802003086000305608145548464002d00087d038869246030100c000c007440440c503590016581011901075038402807241c074049004101140c0000205c2e07820103454900854180d60715240481d06105c0c642d0b8030411070340040f80e02000e40e50b0b1600036011a688030711181c01d0504210b00102d90712107040c05a5042040104041880345206c005000301c0b4441d00c0c002030440d01c0c1c0001c1e00190740c00d4441c505076909502d0307020403078840f5000c0c0201e000c0300d1000d08040300c480c080f02480507500e01641000340c0c1080 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 152142167 1250 152140917 152140943
    0x100b01030207060501170c01080613050c190504150903110607110a09020702130209030d0c0c0902040b03090f0109200a09020d0902030d08042f09040309060f021603 72
    0x2034800d40498680d65088001030055507074071201e004040b002c0a00d800e01c5400744011001c12503225070a03460141d18002c065036100d00010030b01c4d00003008041c2c111070350444100806071001d00a170243e03180b2600ca84d11400c0d203030340c540354481440003038031030203c001c22040001c14000a078244c0d400c00380d045400c1e0392840e03d80940c1e1130034441c180c01c08060035034090400c0390b000600041d1070300108401807080c2c62040e121140038188000341d0007a000d80990542041004e800b18511910410b44c0c07485c0200d000c050034036030b101c2c8010b0483e8040d0300b01d040c07010400810004088010031031820f035003044800030440503030070303480301c62000410080310303030f09451600310900080c0d65807544a000b414010404640d940c1000f00d04900400906004a000f80910b00c8048560344c000e44040740700341d8121030803070000542e960000310361200404403903c84030202c1c80513140548030b050380e40703101d03a100b902d070400398605010010786000642c200040031076200d08a10388400300d003403106c1000c0ba6031005c880c4844e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 152143417 1250 152142167 152142169
    0xf0509010c0c03050102041503060b07030521040b0105090105030f0706110f010e071403060112020603070c0f0308010e010f180f0e060a0b040c05040b070b090106170f010c0302040305100b 82
    0x14405108042c1504056000200a11906600800c100c40742c0008020040c5c00c1c01000741d040e52818071602164610500070800030078010700090401d41c260f004000d0354007650000001000c0c3c003d54040e1011400c0000512407400c201202d0f601411085006000290a5100445c1d80d1161401404100410a12020400a8100401136645810800900c00485010203980c0c1e00c202034496180c00031a0403540e031340c950502143e024107a82401c1e92110104104d88c090040759030020b40280e040014400a04000c14400304840f0380742c0348030b40e031588100d51429804003081c417410703004002900400082045184407400d4015080310301c035480814000f070f0b0100c04070010f08200100d01050701072031080002e80d200d070340c3c00482038032011502002840c41400080300c0a0185000700301182d00200040404902d0383d1080c6540300141e00c00101d5600d44a034210701501d14000b84107410b651000c001c1c04010300081c00b40300c0d0041c030285030031410145161603c5640304425400049059540d03106182c42d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 152144667 1250 152143417 152143427
    0x607020609011d030109031d19090510030f050a02030d031a0904020d05030a0c05010608010209220f06180515090f0408190504031104060b2203140d020d0f0f050901 72
    0x4408000c00810003125242405000c45a1501000800c5000341c000e1000a2400805030f00c1603440709c01204000d107082c040000014040604400300c05d240c1840c3c00000a06128000f200403481b0782c0c06000c1b461400c1c41070614015142d4180c801341418450104900e0b0060340881c0c0c0c9140089503450070036111030000c41c03140f00f84100003030311318040041e64041d200c0d001101080c82c1c9104400030404180d0703522400c3d00300d010711642a40e0011800140741c101e014842002e141d401081c60000541035603180501c4220358840c0e20128283e64801c590700624109449070650008002c5120401903400c000007034180c58006018012005484002ca000d002d07a40054441c0005210070710a46520308403030103005500a03100440b006500002c2c42c080c1410b141c02803104555840e00e9072070a291000006807581d400303192a503440345541070703000004a640007140043c1e40040c40003521200d105400001d04280c4001024014003045e10040d88070030b030744000030b040b0703806040ca0501d403203885803401251 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 152145917 1250 152144667 152144717
    0xa39030b150415031b0603060f0509041a101a0f0415110d0206310206090414040c150203120c07020f1002070602061501170402061614010605060702060901 68
    0x1000b030000e0f102c003100308000d401156032107031001000e0300310545d52480101c00391091402116186071010404100e039051841c070941c0c1040c0b140d02c00c00d82c015100c100e40300b103407501250000c0a0300102c0e40c0070003408008910610076045450981854032000008902d424800d51082c202c0241c4051849161544108640b1510352400c0081e00c810542d45000250758400986003594031082c2c6005000f4040c0c1c03d85000340440d8600400081d5241c103a40801521707800c05200150010b4641c084060081d105440c100d1140340b1800c0400750031820003042e144410702c014030310303819944204001034045203005100c0758042c0411a500b0780d542258804190084815044190400041c0c480803003000d4000c1004402d40e94194200d440503910003118580031044841424041807a42281460b1103203c010b03100c1e4450300140040780741412505151070340040111003910404403c000c4010015820301840000b40011101075003021032070f40001d0380703038440e8007039603414080e0716241c0010220360320032410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 152147167 1250 152145917 152145941
    0xc050f100c08030606040305100e120412030806061b010501150212040e090a08040602010c031a130509071a070c0f0b1b01060e071112041212020a39030b1504 69
    0x9062001c0327240a00094083c07449001c080d4015110a680161a40c6083c0c400300c44240400300280f039601e4170240c9d50060b0107082e0380d4001100308a40186110019440c840c2ca90445000045540c03400e80003880420280c0d0755441150010380f001030741300d01c20b03c0c151800d8507140300c11480680c442a920300d20f07050000d100102a0703a408280002c0b020340650199074080c6590728180700402603009800c8a01d2681c18503554809042803a25042c03000c0c0c2c1d408550312507401f6045039512501d44026105c50041c02c0d007005c0c030144000801c00308200c40a00b100700103121080a151000d42809103411040c0a1072407080929859810f001003000000d401c03000007000005052190b070b080c001002404a12000f0703c410b414815002914101111141103078100c030b40a0302e14201e00a00c0d40d0780c9a0501c51524003090451017012103000c04100c1c000d4418032544202c0120fa050017611100101c05d00215400b03012800c4004201000421075490400f503000c03440c24441d907001810840024010075400402e2 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 152148417 1250 152147167 152147173
    0x1d090a06050c0a170408040b070614010803091305062209020a0306050a0c0809030f03070c2a0504020712050904060e01090b0418030c030c030507020d0c050f100c08030606040305 78
    0x480a203906410080c0080102c6a59501c0c44c40c6800c00141003503c0181e4000303000140401081001c5040c03d40503100c035031700c82c4401290044901443c071244000c20380180480f50030009140e215840c00c036003480d10340380142105000b980741c20f07400150854001c0d416203c100a035008a001d4600c0c10381e00c80c00080340c0c02894203444c2916401c01100502d0100c0e1608180762411a500600c3c90048001600c21803191005500c0c11060050321811500b01070018410721603083c10640000c0c0341d44c0060b5610410f5034400143c011190300c0c1c0d0520056256001c103018501c104155004200340840d0400a8049414030302c2e07460648a0100d0001e02c910350211204286070720010652441a80004003000c030111420f00c1061070303040304001907108016004011a0300d400c200c000107809505070741402c600030704190781010300319004642d2403410304500700c0b40384540300014011450001003100d01828191855081b03050402c0024000c0d400c81100a07007100030100004c1c0c06580d40c0c10032140a15844415 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 152149667 1250 152148417 152148421
    0x70504031a0106110a0804031b030b011814040201021009080405060c010608010e0d0909050408040b0a110d02030c12090a050415030c0519050d02010c05070623041d090a0605 76
    0x55080328075403c0c002c6000040701c000100b200e4480c002180d1010750b4200c003c3d603282504d150b0324052000050212000800d80200700080429030005019000b41a489100c501160705034044170304440c1c04140e00c107003441200b403d002c00740c0d9000984074030540448100245102080c00c3c84c601c01e002d11381c8160741c03001000451034000441900a4800c865140d0002d0003803a0952088035181c03030b40000404006030302d0060400401c215070f0071081e00240074100c5580360985402c2448a43d50040540c90007080c1c2440c0911401d80003005294000050780c4007850400c107880c031b0116190580006001241c20010665180c1a80d031500e10b000103000052003086500d8103090041900d082c01d201c251104111104d00242c54101460380340007a0280e0303003040e0700a0b03052a0410422543c9030b04c05a041000c002c81205c0042c00420001d0054180b1b516400015142020400d844282a010b681c0c109201030204105032011440c116180000d420303c215001d070f85031800d1900e0228120409080c136420001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 152150917 1250 152149667 152149703
    0x1d190c090e0f0606190507020a030305030f16140c0f06010305060106021203010b07150b0910150e0a090b01020a0605100512010c02060a0f020c0106170114160807050403 74
    0x10060007241d900e14641c0304580c1e902c40d280d55001e0780442c0c1e1a0f400071010401c0c0d02c3c620201c0b0b00010014680e5081646c1015925000700c1e00c004001d402c00c50202d00000b050012004030011b205070302c045001e82c6400003050013107004001c0c41c0b80c0d0300c0000029001141ea8804c0d90030074000710380307080030720001c42d0055a5641030041d40d5030004e1088001600501d90070303000f5080d002d422a41a15241440507240a5155450382441214106050021039458005007900e6490003040303806201040d0801c0795241c103000e4400714045000d90913200b0b00018179a4180076448040c0d19108844140c0b60000e00103c90500507801c0111080300100494509801c02c40d0701e440259006050712030540b450b0509180300403101e0300f01d46001c0714040250b44078a001801e42d0400d40c121105d5508156809070614251041c02c6082d00c40da07401040f00142501c90354081c41609200b00c4030f030b26501c00003078659814661020502845410300380700070003115000080f0024011421a401543c0c4082e00292424000d5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 152152167 1250 152150917 152150927
    0x1f0509131e060e070504030f080c0604030903030e0103021804020706090206030703020d050f061807020c0a0602060a14130807030201150306050f0109150b030a0608060103050a1a011d190c 82
    0xd59280d081900c0d100d4040f800c000c0a498040c842c1c0001d40341c071454141140c881c080d50220760f00d002c840802d81000110540f0070103000940c022442915811200c4d82580340113082181404200d904051046c8865990810f41300e40c00b2080100540d80140d640800c1d0401401401520b040690400b000009100442d42c0c164020b12400c010420100680d445541040f8030580d4141c82d0300350712a129007440006986000000d68205019004031100031550300041000b60700160311010258200c9400c002d03a800c9980a0382d205c48803081c0842c0b080d8a031610060f4840356004070060140c040103d45001050700175440607000d580040d9030b8a40181d524504080036140850b0301610301c5250a000181d40740353350241150401c69280104843c07810503603184c1240d000100085e4681d502c50600207014138051001c58061801280503100410700c5050802840e1400c40c0c5c24018030aa0000411580000c0e03030800346450901900340c1c601d52a158001448103502d84141201d41d494010140c207003a401c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 152153417 1250 152152167 152152211
    0x10e0d030e0f0109080705120307120b01020106051201060602011406060406050d06030204060b030402100c0c050d0f0602040902031b0c03030c07030e1008090f03070218061201050a020304020f1f050913 88
    0x1590450700c00c03000801108d0490f0009488007004191000c84030000815627130047c0b04503102c184000241240e0f070740000f41c480110000c044d02184d560f00da05004159081c00f5801c0d09030911001c10b1024101800450346903c04c91203000104403022540d0310261400d5000301008540061003800303415100c0c010384105a1099a00301d105c0d03d0547d413034a03102d03801030052a0089403c410050f8003140740000340440c22198500840c0e075000c21071152030000d0001d2002d00003500c1316010060322490022480084807211504008168800f441540102440003003240d501c2080280c242e51510724600d002c2d100340e821040041e41c004504014180526400101c0e01d00c03403100d050481c2c1200403500c543c03030f40324070a07000c0294102d044401c00841044c1240440e50700264060510050448810030300c03401c603102600e0710050240c000050000398907250806000200341104e0002078030b5821003400412240b40700300682809400304c2d00043c1a500c407180c0c80008580c500c01480071a03102c0b01980e0f454404 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 152154667 1250 152153417 152153423
    0x303060e01120c03020906040e15150612040303020a030b10020a02040f020705031207170103030c022713080d1a090108070e0a0e07031703060111010e0d030e0f01090807 74
    0x348000000e42442c4008603100000e811240d030140c89404d5400b03024034000000d1000380c0254031141e040d0305050742000900c10100c807802100300c1e01d00b410a02242008290403100d842814240705944035a07804018064101c1d40c182030059444d15002d009401a15806541e03d80c0704e903200d0201b114854012a0076007180f0f03c225401c12444616210510480c014194082c0155205100d151160000da0210380d8029045061245a85091090b1400c811800341c1040300000c038080760800842c1094000316295000ca41c40740303044020f0601c0e070b0000c989002410350005e561340018410601c0038050881d0003483c50407000f4011180e45403815607240c808544514090320180c0000a00020085816015610341c10000b01d042d484040818010701031041c041d060074059241d00200003145103003454210500090510307160703c1c14400140800d410440d5840450341000c200c0e440400d0003007a1031008101c9400c00041c0742c000020a9440c101204854407020742c03074001780c40c09000c9404090700303040384 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 152155917 1250 152154667 152154689
    0x301080d08010902040f0611031e07110102010504020d110a0801020315120109050606100e0402041203020f0609070b0c01060807060216120f02010806030c090a0b0102010b01140d05041a0103030306 86
    0x60f0710020601244520300c51800d480c01e50b007509001103072140340d140507800758400883c0e0801d110682c80d007aa29a00d001990300c5610006900d070200070f5684040f02507444240000c01061502d500415505405810000e0040c50011030a0b140743d51029041e070090301040c00215100e1500410104944206007007140c42500c02c01d0301071030b41510500400d41d4032a07004018142030340720401802440c1d500311051805021280e0307000440360f1114400303000104012184545407900c07034140030341000743c802e08420445d0448400c102400c10002400e008441d101c01c82c081e907401c500c00440740180b0f565080b401036401043c00024100358000350515448076403404900d00b0580d9003400e140c9415030300c0390091000208011440140d8040d4500541c084000790550301032482003000511580d0040b00d01d0b15445580c0e0203103241ca0759092040300c502c09400e09041540d01100c5860700031500411800070041e50316600040d0411071a0703042c0c9988030152140348041561a40f070058041e040c140100300e5816 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 152157167 1250 152155917 152155919
    0xc08070908060402060d0216050109030c0b011d060616060f0c091508070507030314040308040c0b0a080a02181f170f180c030d05090f0102010507050d0c020a02060301080d0801 77
    0x1d10100d4090b006a6005100e280340a10540d0141c02075001844c2d9104021040d40d80800410000c1c081d00c5d24442c400d0740c1706a103900c41460564031050060304111480c1a41104038000e903255060300300c1d040402210038a0700c815181c204041980b0416000610541c00c00084080c10030454200c032507900d1280d04d405500396115640c103400f01102c0e50151000441d9100400c0e4000d0058005288d024000e15010508090046201301c204100f5641200003e081034200300501c691400030304050b15108003d0382c5030031680c80c00140220005052103000c69800510560180003544074680c0218000c6e01c05603412541c2d800300c1c0074480504100030302241103451946c0722a04a0814544101344d010402c011a441d40004011220244090039a2030b10078440b44a40d5070b0b070200075024101080e40c1d100f582e900000401e11504103805030b84d03170b41560305150501104603042000c1d1190741800400015191240300c60491802c44582d0340a90044000030002c2085c00c4045299110101c50740c030703980b801e6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 152158273 1106 152157167 152157179
    0x20c06031509150a03020402030c12010e04110a051c030c06020c0c03010f090c0324140601021b0604061103120108160b07030e040209040e010c080709 66
    0x201c44048100026480c09420807030780700700101926100065403501080f181d12071800000e200d141c0203c0010b62400e180400e80300c090100c06034507032032965607501c0c0b4410000d0a0344c0a0b21030800e08003941c6010704111020500301d072006020031400456284130003044044c6200105c00300503651011070007282d042d00140c00310705484000b500c81403040404050031250039400d240041410414050b020640d880b136841c0c11641c2000d41ca40700791401d1189280c0f6407a043e0149940030381740107000c1da02889900c080783e204d03070742c2a003c44441c182a186210840004000002e501500410040c4000703845881c00b0001416542d041b40d00b003118654181040c501e01343c01c00070381540011032010000a4440360a0000d1400b40f5030395240010b5920000c050b0303204a000f4600135a00013906000580b07c50b4000098124000002c01c110405000014007640040d1100e0000075072202e404100 = true := by decide +kernel

theorem cover : BRFrame.Cov 151978417 152158273 := by
  have h0 := BRFrame.cov_init 151978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 151978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 151978417 ≤ n) (h2 : n < 152158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
