-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0830
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:02:17.834981+00:00
-- url     : https://prove2.me/submissions/cf7b5c84-f9a5-4e9e-9a0d-45406d4b1b82

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 149100719 ≤ n < 149280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 149101969 1250 149100719 149100739
    0x10b090607230604050d140901030c020a0507120b0c070f17040f030b0906180c040b01050c0307030305160306060c0602093c060309100e030d1e05161d 66
    0x80d4050300382e1000e480e1075602804243c10b0602d0407604008118541300200b01d100d484202807404642c0031101005d009080008071103001c3c400580c280350350b40e10094201c2c010440c001402c451241c40c001c44580c13040c2e80c50b107215912402e10f03400c03a004d107000c082c02b003076480b0180400203030701c040c0403041032100a58641d007002d0762072107500c000e20343d84d4000b103400320803010502030414400c20406d90440e05ca003864070012004455074903030751280c500d01144074a4580540c509140d001c2c40854025820860607aa40c2d0152400c02901400d8107441c80700c0006d64004031081e4803486480344000350380d460f5449203040e0450b600c0f158041d41088811941c4541001202500d00b040219101d115806002c1003000d414540c1031058404011000010702030f81003001000503002000c5104621584045000540e0050b0904210718501402d206880d2403840c10540012241404140e03170602d201307981c0103200b0f982d0389003000001071a45aa1460110303d000c905583c0203074010608c2c40c0c0340390000e4640c080b4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 149103219 1250 149101969 149102003
    0x30109110f0d0204060e030a1106030c04030c0801061502070e0106080406020405031b0418020102072d06090509070e0f040c030b10030f0c0203070f0303020306011209031d09010b090607 81
    0x1550010300c80b401c41550010741000358503000350001072400002c4016040544281c2c48041240c1440c0c8003041c420f64000000403564003600094401858000445000b090b1307c81203014001c01031030094001c40180742c51442d00480c800900b25013500c1007000c0c00a620b03480e00100380e90082c2c001d00708458594080c0008511034030200580e20303e10072500d0641354010150b40c140320854048002091805080412502c0580d030000f82c0d00c8102c50303c20840e601e80011000b941d850364281c41c1c030f200c181d8a9102c8000241c15a00500007020350f03804841001660301c800b081038502c010f006004640100d1143d6101c0d10515095211010618541c280403034042d42d82000100c0c2400310700f140201082d0b6405903d48102e01c0b901c94004c10404d5400150320708015500c40004400180301d004080580000c0040c80741c0e4402ea80003c000703015103d082c89082c0040c0f074042c1c20700c21a42004540007108000c0c1900314039201c1c2e1014120350005c0c00040c46c026552090103075a5000308000e45030482544040c1207 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 149104469 1250 149103219 149103247
    0x12020609040e06060108101508100f08030a0801060305060f0f1f05071509020303030f090a0210050409150501120f020702090f06130504050c100e09011707170303010911 74
    0x3400040b540050415458504009071081e2006004078030780c0843c5040500caa4890424070140e81c0100f03003001c052a03a1680c1e02c04000103060341104050300146170000940322000400b804640c0f060303850b45840340c0e0b2500b100304d040ba4001c848042d8021155482039803d41003103080882d0f404d401819200000000454036201840c3c3d00880700d0002e000001e042c000d10405c0c3d00488180b01403c1030a0000381175540020760f40b800f028010b80c03030031400707080800c402d5070040010544055014004030724880c00366002030803940082c8954400a0300309581207500460200704c250a03030348161a05252400c103000d000008104011140004581c02c20289025940d409045c0f8451516008050024540b6905101c508014003520070030245c2400180000100003050302caaa100081c1ca868407024911007007121460318500d180c80d08910490004100c201c110146564044482002c450b1201d64681241d0081c4440010740c0120360400d000611007104281c020310790101c03195490b5400d24084102d014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 149105719 1250 149104469 149104481
    0x172a011d0301020d060b09010201060504140a0e0709110307121515021603080c010c09062304050402070311010605030a0201080a0b061b06040507050f06030615190206011a030c041202060904 83
    0x22100c51b8045480440c0b580d09028240c0a80700658007405200c449404038031a0781d4002c0e210102c0c0725101c00c0000002042081a80700515400380203002c89a004014175000e544240e5500c3c0014240c0118020601928010f404062107241c1d0800f4003a0324002069101d81400001201180034041640001c00390815001000c0c5000d000d125584109110301182100c20b06807501080c000c01c100c04010013500054181e10000c0c00c05510034210700e07082c0b2002400d1103507030096544544007268070024164402089090381000781e00811007591241c08041e45d070030342202e000340043d03041740000399030900340d4000c503150500c098441414206000320b0f20040c04409400c1049503400202000144502044a140200300680b080c1d0040b00386030b00842d031a844001c010368000d4001604800e000b540c18001c64040020200d1026009001400003c0d1901c0007840341030803100d01074555522150300b001c11a4084c00d00c920509184c01c1c070300b103520703100c8201802e02a60700c00001d01c03c203c1d1030b031102d020314 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 149106969 1250 149105719 149105729
    0xd0203030d0606270e04031b02060a1205150d0303150305060127060506040312021203010807061403070c0201180305010f05061207050609040b0a172a011d0301020d06 73
    0x78040d41d0401005200b0041c24900030744c02c0d100c2440e9401c11000b03000b0f030001600035800d450400f05c0080741001641e403150144600070f4100c800081c140101c103503c6551500c5806040e14188100d0311b84145c83c41c0400c844002003584200203e66090000b4084d40c00300c51158107081c800303840b0740e50300e4450a060030300903400b41402c01018240190000e402130908604004128810840903007044003203000b6014034000100803c0408078a140f4403070081110117840b00c10031685c250b681d82c68404240d00c419a61040f5004582070b0070000c040300502c10180d902c0344110342e80f500807603500c0d90011910001c0084100908592000010020640070b0041d1400341034020800300b024240700007800810700d190710145841d508429014040c0303984e4941141da441c80111404500020804000b6461900c5070348105010340580c40c811400401c041f90301d1040100c00c8070a01c03500345045500c510550701c00c0b07032043c2c00100c80d9074840c0102071050484144424000e40014102100c03503d000007191a95002 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 149108219 1250 149106969 149106977
    0x806010303030b1017010302060304080d2f070f1b0803160b01050d240f0f09020f12060a050403140c0c0a050a0b090906061e040303080a050705090d0203030d0606 71
    0x1290760300782003803507407084130000380c1c540070f10072040384105148104c406000080c03060308000040f4040c02800400d40c1c00c4c1c0548410104580c40303242030220107034070044c003040284408243c12150640103540650b1002c5d42c010070142d440c45226541c104401160005c02450040703c00f07000300e80c454082000d8100550690140102c41e80182003c4000400503441144542c00c01c08188000400c2142440c80740c030b4030840b103008180e10405654029000c0c01c0c1001143c4c40c41e022807010b81035115041005482d0003600c04003440c0000105200007a8908460200c6035840400481d0701183c40d5801580d201c1d0003171030070384004c8918041c203203010b0f8452285140c65500040c02c2d80c45514080111100401044981c4450980341c00c200d528640503c016062191070031000003045c9441c0d581c11103c0c9003009068042c1d04044100b003110840d0444d00041d030020340c0c003100040310050f90b0b120f00381c0521441e459043c20300700e1840400ca44490400310403a01808203002180050745680540800780c4182e0325 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 149109469 1250 149108219 149108231
    0x20c12030603060105090403210e10021216050a0503070203090a08060f09030a020a020409020f030706050406030f090305030a090204060314030a110c0907110708030d021b0a080a050d06080601030303 87
    0x402d4503210303040c0c01241c03043c0f80c58014840000c1c0c02c25400c204000d441c003612519007040b00e0192005080340c5580790414002c00281c04d20101490340108840d407e460350301e03102034a5600328409500c80301511031011072010031801c80c010f4020070146510484502c1120301d400250004601580b48903400145154014400d00420903e184421548101174074015400d00c0340d8013100039901d440102010b8041c640c0c0e00602030664851181009a184003d0100d504e559651540140154005d11450002910700107003214042441c0c01030303803401270b0556192801e6482e4104410700070f104042003268850341c0c0307020000c0091421510600300050f2071006d5916201108006414090801e0100038039030048802c04605550b401d11032034000c11a89010140300311f61102142c42d150282e080380c1007910021603100849002c42d0010101540101070650000c45180b60150740c0e103042410042101f1001d000341c14203540f0078000783c03505581c40d81c0041400c40c1d030b8415031400d001c03080e0001c0d400652101 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 149110719 1250 149109469 149109481
    0x2090d0602070210020109030e0f040221090d02030301030c1818060c020706050325020a0c03050d090501210b0301060b0705070e061005040605030a0e2e020f04120501020c1203 77
    0x422034144c2140b54002845500360f9541d00400e400001000070344220891400f00c8140d45650381501c84220084810710414030000c20120f038802d001720341000482c071408101152107880482600e0480b9440b500a510590414071a0756030240394000c1542d820359140445140140c013183c4900441e4015880080d00e10b28100700241030001d0b5400001c2440000c2050051071020304c0880c00e00c03040710000400210744400f40880c100101198064100b240410700801485408200080624400e4950b1340f011a0742d8401503400102c10b203040c0c480d00c82804010380100c1c0c00c0da0400206036600134000210300c1c0e228000d140568001c804182e0f66540940000c1c080d0b151820a00c5400500441e4246021102c2204c000c1c11407003640110010444003002107260a00c064000e102e00c184003105482c12520303100100303500840d00c4c0c2000d080064000180c40c0c1c410010784200c988c3d11190003400c1e4030706402c0c241580c40003081c02004449665017081070038030881061101d0f03225034510300c0429960303040103 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 149111969 1250 149110719 149110729
    0x14041406011e230a0b2104030804030c080c0102040612050106030e0601060c0303180f03020606040608120f0c07060207030c0906060e040915020a020a020901080f0c010c0602090d06020702 82
    0x160000b010b210712201400001c0c00071161004100c034000d5210120703005a154900c000f44030b02c0050150011014140801e01a0342c201c05400406090030301ca4450b900206261180c01c80305603000b401080410300880d000c680b143d070045140c940181e41d078500d0240c0c0b20300020f007241d0140d4060310000e10100c1c110300b980c074013a001312401420b11f0f2906200d171400c414a80303500c0d8181807182c042400f21100c4d1680030107009400a0700241e400701c61070f0302c03034024500b052040b448403460100c00500034100018014a040e200f00f100341da0b040c4000b000944510000c440d0307154011069a06400b03001d00000d41c00440c2004920040c00841d1302622405103107140ca40882c0c03840d034000c003c00360b0070420305015040d8000c60020200034211000306071180a42003c00b0342c1800081c101c43c8040c000078a10980b41d4000a0300801e040c400d80360041981e0b65446219201c101b103a8885046030010414444950701c118101c92489010700c00051610300c198000a855126004048400075000305240d4198981 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 149113219 1250 149111969 149111971
    0x20103061406040b130f03080a02060f0f15011e0c05120f1911070e010501180b0304030c032a0201271a0412080c06010501050a1205060414041406 64
    0x1d940010904619610029846005034000d603010b100c03010402c0e6480c800c40a103000003c0c1045483c04184a0f140d08246001e60b0244058401600c6030401041d8034969400d070441c4100603085195006454584a800ca0f09424603178440c1000905055050380300301010500c0903c0382103131100392150041c0e1601e01d0801207490552481038200340f081c03a581e00d0700b030000c9132504c1e0314400c000380f2009046203041d503c001c242803248000c0c0c407079010003251a12078059198185c8009890303600341c00d041125004901803141c01440d103e1035081c004180000c0c0500003602a40d4442d00b011850300b0100310880303501c50780041d00c2099509290810006550b040400c960702c0003140304031503d0340c1000c030a0034210303802d01c0d10401ca040f0a007140ca01101c110400b082d10060044140450701c02419401c000102d0b070003295105205001d010000500d40d80070f0b07012250440b05036181d001943c004408141c000708002440c86070020b403541600250000f83c0040320748110b00c203d5030040740103401d1020710710b0410 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 149114469 1250 149113219 149113229
    0x60411120307020d020604080102030a0c03381807030504110901050904030c0311010e010209030118020907030213090c0f0305010906060c0615050604080f0c010e1309020102150a0902010306 83
    0x1540e1036412a1050200482d031806405890324900d0607003034030101e1030f14401c5601c052500d510100900803032440b00e401c281000b510968041c003141d20699081840312101c3c01c100d03420050b503030190f03a0ba121003000e804081814010048008099800d810f0b009160b42101d040700040c0d0390b40c00f00010031001491444548800360381484066047c00081042500040d001400703000500c0c04102c10580708a01007481e44d0321040081c003580800b07141060103900300d070300540d21035400c20340e05885040700d6110405800341c00500c980f2640d240c84030150f000358000301e039141101c0c0301910b02280c1c5a01901601c2d0001410750368400c5120407240703006048034410f0300807041d618240081000266400b65404800070b402000018020034409102032100c15030354000358101c0004100042c910101007403c440010030581941c1424140e40300440b0480c901404155004082c0300c00f06400c44590388c0001c0142d4070600480740300d1000702c40c407100140400c407546110703a9111702c001000c55078140241c8000b01 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 149115719 1250 149114469 149114479
    0x61805041d0106230f03010905240f1e070302090a030807231b0a0305010e0303180601051e04090c030803180f03070f0c0e012c060a090510030212060411 67
    0x14895444c3c502c40c2450524924030500324110310000c1590203500c42003070b080c0e210003103846001d80da04803132002c05005058410450f002d1000120051b10903418503100e1900101c0445030012031584000320b41a0251500c410550300f80510000c42e2a44c00d8800043c0d801780c1d501c2501c41e0351625007842d12100b900001010850000c00700110398000103112000d004208042002030021440420b20300060355102410b00c2d03003000b00071036001070044001c41c0a42c1400c1c2d5142e2001e00c00c00700c80c0e6910301c0207115154200e688281030140400000d004007181c180e006001054240c0161211499511103400c244c44655000007440003a4000c052580c602d85166030280042c415101031031034980c02a048050001d00c14498080c0c10440d8004001001c0c0003051030700007042d6110b1078690101c0008a010040d18408c0e404a400c4c0b000a40300054803844000b4001f400031400c1ca030301100501006009810188100c2a000c0016512142501514490a0005d000c0e80c9801e04040301580070200b8800d00407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 149116969 1250 149115719 149115749
    0xc0609050f1206040224041203020d0c0c0509060a0806090601052706210601120b10030b0a0c05090a090f0c170109050709180212150109061805041d0106 67
    0x102501050f05548190102c131072401000c80d44000440c03041d041501080354400000c0c0104000000c9207182000328025405c943c5c00301c1000320150385854159a01421801102e60f0800843ca40031540f1035100c40050a218003841c5e40d80d01c3c07103181c810309070340000340303900720000500040c1031034500142602d02d034021084410312248245612410302410340b9010701c0710b04c42d01c01d00c6034061400316810002003804031007256a60709202e40105003080c2c41103600c8503100020421941100400c0c81c1940e800885c120a141c64001d0b103d0020305448902d8018801c4c14805e407002c541d105084840141607954011034500184040c8000b11018005030a09003d4441c0400e400c0d9500000114107417249a03600103800c0d140caa01c01d6802403100d030b10601c10412803400c00703403164505070094800e800d100c0d0300010032a01c0310310f940c03211000c046070031900040d00b1036000c0200b540301d1901d41c590250410801c420860315080414185c40102034820030780d9014802c0721101420920401c0010304488002a42e0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 149118219 1250 149116969 149116999
    0x10b091503040b041b14040e010b03032b0203060603150d0b090a03120e060118110f0408010c0306051c0606050303130f081b010f030b040603150b01140a110a0c0609050f 74
    0x2080d0305007130447c0980c0ea40c244040e4585003d501c494a02103004040f0380c1c03510340707040340118140201c0f280b03404511041001c5480d00101c500036a4064540102518107540e40c0801c801200c1c4401c59003030354440c3c445074000000c01e074003000040c020300d400e5018202118007800c02400324051000d401c600d2900d0107024480e205004180d00e810354034511035040e840c51111411201401c02c4444a000c10301001420f45001d00c00b04000300b0441c0d112500034001111500c9080d4100c0301f0b280303d50364110710f022005011017083e0f4030710302590f18401c5030001955911140440e1558200300a00c0d9900702c4880c20070301034403404c3c5008000800c060001411110304222024440100d110441414420b01c00d01c6425250f00030f0300072050300c1c031000d0803c1254641e207003030040351110740c640a010340c24a050034840103035104981909a42c120040b0341803078800b043d10100c5010001c81c0f1040c14900a148a100029140450120085c101647c60904542c1442d0410690010b13180d8105e1180365441d2510341 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 149119469 1250 149118219 149118239
    0x304030b0601050c1227010c0512090a03051009020306090f0a020607060204051c060b01030908070206092403011508011d06041b0206040b070e0306010b091503040b041b 74
    0x64008028a0038079101c0340f807402d29600d07150065808800303111004c0b40c6c010b14001070001880c03036170500b0320602c0c00008801c001941c03104220078020f03041d50090300c3c66000260746800100342d05907002d464085001e039241c03106403d10041c0e4601180250311254030b0410b42c03504014003a0002a090007410b40d1042a112265907079140d240001e005400208840040c490250705807002400080d10301d4845460304803041c2d0f141255410205d420918011034482c2551183c410500000e40c0b002d1240e181503015000c015140e004252a198031031400064400c1e80c003079214608058018401002e5202e505080101c1c15406003428000308001c2d40c00010000500f49686003502080b043d244002591141d038003080241070f1600081800131600d10195840581c0041e515100d04d01a089015880d100c03050f0031908849030040031985588160010b1144640c52001041d81c2040140709454103501000000c00c290000c68041d101c0c880f000c4104428400d50079000a892013048020014290030012109 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 149120719 1250 149119469 149119471
    0x6041b030515220609020a0c03030905070306090b09010c0201020712080403230a0315140603070507020a14120d050315031e01020901020f0f0601050405040807060e060a0e0304030b 79
    0x20201522a00801d034100518107414041400140011000300c0e0002601070002c0100a0704034201ca190450015000c0c01034804d49003510503c0e80e440010031784d00e85084002d800407000a80341d6004101c400000908144500304d0890700c00e1206141619000b00c10364215a005100c2c05d0a40e4010058840002c03403401c0ca00700164030701e0400315526155400c04440310000b42e02500b0390101058030489081d0795040162841c0e11081d07400340805008072540c1c680440301031180c2e101085483d01001c19900e8840081c61317208e249481c0c20f6003424060340000d07503082e400d944041c1046001c40d40c4e18003d42040401f00d01c0d94404c45000b0260134000382c0005103540300042400018400200040703466640078400c40c0c904034858a84140d02018000109000354881102e003400341c85481c00c400c0d003070b00c80454601d80c0600d0b0784020b00260f82c40c160622007d8400200f08544c240c008103c0240010002d1080f04c04c2512118010011071030074070701c0303007046603101442111143c3c01400208001680c40c00b5107 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 149121969 1250 149120719 149120771
    0x9020a0b1c09150c0e0f040e030f1b030a05070c0608040b060f01020a05010f020a09080609100f0207020424050609060d0b061b0d08130b070c020609030f0102120604 72
    0x5840380d440c2000c01e4804420030282041c503080042d0315440301d178000c100c0c030040742c0f00b101c0040b041c5282d901000111032214421034015042840307580f05401e0304030042e100c3c039804022003800c010f404411048c10b59010341d007294049580461020103004941c00c07044050b10307c0c0c2c01c2904c100d0825403201160544000c1a0300d105982c5595250b61f00d03407090100041059001d40248032101951203020040d4104101410000b4420200005e1407800041c00d1401010110050041e400126030302e51b01400c2c070313882c404074075a400b000301c82c006032258450a081011034010340283c0e0010780380640000d2a41f030744114840d100900c01d0f0030459407043c007182c801c51091040014502001c2000c14401d010352070f030036281415200c8900749825004500804a00400c1c0d5400d4401d0f80d0303801c25107564118458010b844188401e00003100c9a0090101c2c40b04c090000381f51904201c01720b40000d203401e00c03921441040fa5000700e81c43c3c9506401201450b0082411581071000000008504504070800501 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 149123219 1250 149121969 149121971
    0x6100f0e0412020c1003060311090f040f061104030b150103060f050625050717061501030b130606021b0d0302030f031b04091d070e18070e090109020a0b1c 68
    0x14484032034001c009139015000080c00c91003100c40c40140140c0142a203201c1641c0300c08071010341c1d00182c54011000342c440c411078030508100e902c880d248c07629005020715040315002d03612142e1204c22006040030f04000d51240c184d404c02d61820550f00503105400402041c14107003880305c01c3c4000d01e000120741d41a130358145c80c0380740c44d280c0c0d200301200020041102152035140d1071000700306120303011405401b51074500b880700c100081503524195a404084a21050043d214004110b856100360008030b1207000040498000102c00d91070041100c003150f1040c40076900c81081c130f80341e00441c0c40c5038241d902c008a9040c1c0d203c04194901a40307d1046c403c100c3c0b03500600000140044080d441c10070058003140d142c5540b80ca44032002e52005003003030b50703041e80b0756410810340244190000410000365440301c0544006a240c1c01c0808488001c1c84000c041d250148150102c0c007101d0240445120f444001c002244000c00c50040c8220301d13041c1d40103055211030801c1070002200c4948040458200c0f83d600c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 149124469 1250 149123219 149123243
    0x31a040e070512070303080106140f09030109140c0a060219060c050f210a0506180604020c190201141306081810050406180b010510020109050f06100f0e04 68
    0x6508008254000c154004800f20f041e803e0042d0001d0341c40c3c240c91013070f216242541d883c1c013425101a0003004040008034010400d4074429903500002e411140b201400106880313109a503104c103003064008180302540d01c2a0081b007954500800c961000780f025002900301c441c0701050010003500f0456000d00060385138140800080e01c110102ca064620310410365271620280342d500c003900118007500c800004d40110102d2400d004c6407040e50300070840180714a06035112070604c0d000c0c90400402c0c43d0750040e42840031020144082c04101c1c0b0150031805c0b08407200348140b0000d009400d10424078160750a0074025180b5226a0b032203840c1c240c98140c03c1a4642d562a00c1e007038040031207214008940c60055444079424680b140e0011401544180400d2103c814200f40c48200f074103000c1800351110060301c004001a003090071806440340070510004c900140e075920382914080030001c0a100a80c004004c02003c4041144100c002d0105005103002c1d00f1320b0404c29480b1070901601c00350144103041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 149125719 1250 149124469 149124491
    0x1a0106050f1213080f071502180d0c0b0f0309070803030405100509070902070803070206160f030504110d0c090506060301060c0320010e0a11100512180a080910031a04 73
    0xe44603e1003d500c484190755030b8030101e030346583d0794003c8201140d9080510588410b01c031080e000b40d842c0c1810000800d00f035804034404014800c54444030035664a1545100400ca403614000140800150041020f07601e00300039144610f001c4059001c41c101d50418800d0000103071010071200300e0b5006c48170f0702103025100ca0b04000d0500010390300c03e00d0f909100044d41020002e40c1009180708000d0754080d50400d6403042d00340401d110b26246500001451400c800070801e0080d0f024a4205000e643d0b20111210280f021850b6204d4560041d01c0c1c8046503001004842258050381e90f100c4002c1d1070b001c0c00c40d45001e2003d041d529010310300909000e40d00c124a0300103002c0d400d007800f4100c040e900030720000b206084c0d882d80300c1030090025241050824600701c040d0400c541000100c455a43e0350303500d00510580e180700b202002829084401c0202c2c00d080c0b8135120300304025a2041d0240c0c1d01d180d56041003d00700a4600b400a26840c141418109007a1070355800f0312868086034400c0c0d40108181403d2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 149126969 1250 149125719 149125741
    0x20a051804080a050d1b020d08010303200705120102250f02060d18030e01020c0105040b0315191e080c09010501080703020405030604050703020a23010c030c0605041a0106050f12 78
    0x14603004a51103292044007a00301000800d4000c58080c2c0d5001d031080051023003000ca46d42202400040e02140c4d040200280034032082c05000e040d505804d00340c0d4030098a400014500000000d40b102960b900802d02c00d045014498000c4d01140c0301600041d0600034690311485080500f15010744500008102e0724010241500310340841c50b0b10304a0031540c0c030541d16010380180030000c4002d005200b1440e5003001c82d4000e030101d82c00d4910740a01e03682141d41d000207198580140d881d025270080b9044904d42c041e50fa1038045c14010340306004600552003d5010301d0380d0912020307808030003980d028054102c00b98580c9164507054400c2841e0021103907807403500c1540644116407007160144100c0041206100c4017243c6107007500e100716960f40e40c8960300d03079030802403008045009401f01c0300050200025030160200e0140a0b01c6424485481c041d103803140d02c102c400496085d034040c03001144540300030742c441c3d5089001d40700d141405070904503022901059030003602c210440660021021560040705 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 149128219 1250 149126969 149126977
    0x80a0312051e1303030507140415180801241512060f0f0503060f090628050a0c0f0503010803090118050a060c030806090609060d03180f03020a051804080a05 69
    0xa85420b9058a05141071080e2000031003120070f5000a02c0c00002c55500c078422040426501420299942054208030b0701645c481201d0b80e0000521921010350084a000403027003030300400c02d510000444120710b80044001540d002a800700614400c4028403508100d0306044101454a1074600302038806680390741c005240580016002c003650308030000b490070040859000390743d02601074030501c1d02c0e0041041c00e0842d003038400c0141500b0203000a146030411b401c031040440d2200e41c14000421810015000702c8000703407031300da00700c5031210000c4800e40c1d0041c422007900701e518907103280741d5850320300002c3d01e901564460a04001140074030145115080400401401c0024074046c034280d92240083c0001e10040d000702d01103803c4800080c0e4034504410242d208660151402c1c505070340b4401006502c2c1c103404411010b002d00484008880c650004200026160712010760109904500402107080b880f43c3c0300700d10807203e42c2c0d004a13000c0320210700b0581099010350302c151100100c43d005d44503070003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 149129469 1250 149128219 149128261
    0x90e0a1508030408010e1e0c06030403020c0a090b0f0a0602061b0c030327010603020604090c11120409060801050606182404030606120b0403110a1401090507080a031205 74
    0xb00100300880d03c0c50041d4092140010000111003160880845545d280c803405090031000750004803614201d410180010743e4003a03c42d10648806042600009100340d1a641040d041039580b508510918280210791407410503045078098007040c0f130024003d5a03907130000c000c020075205514031001d04203021016031b030442008070160390b1245000350300b1072940c5640ca5150081c01420401707001c06d00718180301d0309040c1c0b46c02500062506045c40b0200016004c041c1e403000421103000328504c170302d11091168102e0b82c1e055400b902d079910328001000094603007681182c2841d0345080d05209007607441904886841084040f200c0c0308020443c0066401078070910400c15084000104003000c034510300083c019603100d00820012182c0702c1d03410324040d44c44c003036005080b0700c9944042070210340902c180104c0c04d1048403c82d8030540441da1840901904800c200320540e443c2d2100c0c008001c801d100c40d038090030903d402040c071100b480d00c0c002e01c0c50b05001c0050000769a10300c0403d0415a006800c00c00b590 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 149130719 1250 149129469 149129473
    0x60e010215150901050a060504050118031208010e0c0c15060a17030c1b010e0f060d0612050106090c021005070212180901061b060e070e0403080a0b01090e0a1508 71
    0xb141110380d0801a800442506108800c80d1001180c0c0b403038032030840820384040d50344c1c032802c00d4108030065409041c1c00c100040415000c1c03000000080040360000161401036030303000c5007945440c40703410100300b0140502e08040000c0c40036001624000413514042c180040890b80251144004160f00d51140e4120700501780550340c0032103601d032001009000d080c00301021074042c80404400c2c4d0b060126401100350004130525003141d002c0c0380c98403000c1e03400403004081d6031600d00c1c020100170031142c4a40c000d50600c01e8484c001020b21a0030b200700401060002024000802c180382d0083d04e030708030300c00340c480d41503070310300c081a900c034820011042912441c103006a501c50b640814149000048010244a21024000460414030411558010b100180e40340d1110b10003940d282c6018040c1001c401c889031282800025480e040c2c400c1503401180070f51903d030301909004070120b05031170611103010b040c80030603d0100940e10346040b2003540608411800905410031000c0707035801e00420b40c42801c083c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 149131969 1250 149130719 149130721
    0xf06050708041205040e07120b040c020106030303050c03040c030f0819091e061b052409070e160309051609060602010b010305090d140d140a06080f07060e010215 71
    0x1198000440c0390045010f01800e003203c410f110021a070510481c09001e510542101c082a8014002c501403502d40840c25408070b131001e80000402e04450034a080d600050703440303503000c0040c10740500c80e594020340a03540c994903502d4103440740c641e031310f00b00d2000400243c9480c000b01c0038404030009a0700e400f00c08102c02400c01c460300000500700c1c1d03c240a281d0310401c4005000821450301000343d030854500362200e80083d4204818108400d107a11000d0781c2d00e0060301d0205071a810780d807171140030314030a40d491032459082298203a498520250002c129402140b0b00b0302110904006102d482c9a07014580442c50322520f180c00e40c24040e9080198203c01c1c0180400304151509030440d50030781d0950790081045e00d80070300046041c1c89003942c0ca400280c0100c108100c07014030522079601d52840c0c0500c0035141401482c41300301128400b01826a0120880090001c0c21032035005020007482e100c0020400c50240104c96503c414a51060a051002071550554181d00038010b00400703480041e480051 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 149133219 1250 149131969 149131981
    0x30501020f0304110409051203060105040906080102030a18110f0f06070605060f18010b07080408101e050606160c090908120c0712030e0106050a03050307020108060603010b0d090f0605 81
    0x141d80c01c19034003103c0d60800088000094109446007002c4190850000c1409590648004005a0001d4800d60401c281040007041000301b40c0291001032009000042c0c3e24a00540410103c500e40030000d05c030140d400344803c0104e0032150b03101e020b043e400c40c3c1e0245482d00650008040359840e90030160001008034603203051043d10b80c802c9229143c20749510320404044001c008a562020200d1820004224014444880c1401c082c0500c0b6100350701c510701c0d00d0348903030040e07282050a540301c401480d20b40c03002401318216190a90075010032401c00340102c1c1024400030f1514040e03264000045140d075850704003440500d914400007440c079000108203051050801b80c0306c0790701804203840300b010a0004100c2004e049002c5078001c0d600005171000e141c01001045000c0c084900040c0c08543d242c5201107040c2c0d1384c10038080011441080190782d0b4031070920001d02007031001041f10344200e400788010030410795118100d56410104e2103000030840c0107443c010540020300301d40540054984810410 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 149134469 1250 149133219 149133247
    0x120506030304090f090b090304050a03080c0a0501110403031403070504060c02040f1d011b0e010c050c03060f0405010506010809030f070204020f030c07030207090b060d050613090606050a060c11010806010903050102 94
    0x55500400101d070445c1d94050010f941d0f4812849a1a08018bc00c801000425400d0300600303111070556003502c02c840d005071101401c2d6400985690040080013800304105500038244110702400c04592508601c1c02d4040a082400fa80c862502449415014001199610390104c01580d078500390070058018101c1d601c0d0381c0002582c0380f030b079465071800e2000d00303c510b000100c98034000b49960b18038120341c0003840110b5035000101c03021211449001c0d02002d980d501404114845c5692000701621440c060038103600303588016005a05101101007409511000401194100f0010b04007051b03a5091620120b0f00034410f00100b5458004080700b8004114062401401100c2c042d030b007151851a25081000c0840d0b0030074000303c4e4448000c1010020301011074028a070701c0a40109001420b004404a00c1c040d1040f0910403aa81c6580d16414005494415226000f520062400d48041c13291660f030411061707150190641403202038130000b01c80e030f8460300700000910303401402035440301c0000301108 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 149135719 1250 149134469 149134481
    0x303070507081b040501050a03021212030106021c0e1807050c060a020904060803040b0d050a0b100201090b091f021e0c060a06060518100e040204121110120506030304090f 75
    0x58800f820800700c8030b80d2402e030084034182c03000140075503085840d590802854807003110340d80e00c050040041c140031000101002c0c50080007160090315500340c2510758200c1060070440301d202403200d00c81141409172104000c0c4120500c0002e00e007061038449174001d40f8103000b05150390302c00b0300c00d10b02042440ca4071031300603061314502907400b0b0201549800916850b0300540c01000351824090000710005061030b004990000d04100c1d000624082c0040441c0266a68030801c0000d40e465400d60000c0203d03080d1010340c0120340d500940310480914960b2464000006d10041c001c80e0003142c18015a860500381d0103440074203200b131990f54032075000d40750b031600804c813030700146a4900003002480c02d0184c001c40f01e200e60a01740d0416074100401c00c001031210040c102c642000145102c403032080d196880280068100d41d03082c5c910200342881c103108121096090380b40241c10705c84000ca0075a402a40120b80307150480c40108160ba0750b03030046841c40c09154003918140f0300f08410620354103c254000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 149136969 1250 149135719 149135743
    0x7090e0c0a0519051e1314091b04050a06050711040b03100203250216060f0509091302060c0c09162c04060303120b031501090c0c060507020601051008040210050306030307050708 78
    0x1075881e156032130702c0207d2031f00700820006401030032003000101e858404517084482c0c40f64019000c3d00306515040803410420a9411400c0801c00c002045420303c1308841d060606900b0840f81440901091030100351113445d80580001210340120110700300507881840b41c04e104d4552640c00080001802c0000e50300c51034800c2c4158458903015000c16103900c119880440044a925074030f141100348400d0040940000f8112218022810410001a51458014006454190000e1013000204800c2020000d1b001e8030f40240c140d11103508d90074407904500c02d1301d0009224030040240414030240d4110000119038039550040ca400c902008143d04100d003122041021541002007245c80400d059480e6101c0740c9036026021140010000810990001e02101d9002d143c008041100756850009803501582d00b00c0140e044440103001c2805c25443c0e00c00115007610b031a151070f0602d40c000c01c0d48440010110b03c1082400800905651010412164500c0d0b204088a2080d40d455016644610f502502 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 149138219 1250 149136969 149136997
    0x2030406051006020706050403140c04060611010b01091202120a3c2001090b07120e01080c03010e13050a061a01030c021509120307090e0c0a0519051e 66
    0x8042551813000a07102d040c0c2e0ba898440c20f00d45810751f03d44c460080017141440d00c4074414524201281c0e110307405880010100360701d60f03000c2c3d44601010b103402e480c0c40005844c104600003008101e03155480d4141c140c00381e01501c40c00d401903010003206042010317204026003854a4525440802c000140b0cc5030210703034000d8004d03a030003030f444e40d44030700c0840030b590018018030b56040700241c41c0804002c43d05080901410a400d0741f0b903580c070a0354403a80040c50186d0b510260b01210302d0301e494000104003800c80092901d40024500392582d0084d40c0010f000e003110001d0480000b40b030000c0302d802c44075901c0741c00c0421581d02088500c2c0140140004000c902c1d1700c1010914030100a500a020345250004a42c000d045141c08001c0450000800181025040c1c462070010710001030a200085024407680d0b9280f8144508022440410060140c0b0746845210308120405a0310f82c00b40c10355001d41030003c0b026918080c64030f0b044030300d03005d07110640d42e10450302a454050005048020f2016400d100c40d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 149139469 1250 149138219 149138251
    0x140f010302030f0601030f150905010e060405010503070b07050a02060f0d060e13060b0d0b04050607111203010501120e030307030605041a01020a080a26010611060c09220203040605 79
    0x100440581c0001e80d41408070a03002c101040c0f01c1d6000c2e4201c114a2aa05a000651a001143e10320740191040c1d10072440103544e80300602404d141d45103120350050080d9000d0180b0752414020a966160521071004003d401003500b804200041c8000c0b0708072a0010300c129200c030050548400103070b010411603043e6900c2c2400004520100030300380c601c40c4544a00100a5098076200c0382c2c09424595420380e80180b8800c2005c0001d10084000350085000304003d146602c1c001d807000e000811880208401a444200d154480d5200201220f05640080c0307403070381c0d40c1080c49803424090b2502c0707005100e040c00301000304022164542d00040440340f08440c1071007104504110f0004440d040605a070040c2c004441030b1b808a0801c0c030042c00f00108920305000c08c1401e410803901c2e01000800408030000c2194010801a40c0c000c21081303400a90f04061304070f504115032403441d64826180080e0140006900703001aa072004c03a035915403100d01040c255a286000e00d411001400102d8110a02e850b9080e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 149140719 1250 149139469 149139499
    0xf05041202011a0618011e02010902090708060328060905100605010c0b16050c07060e13021323040e06100e04030c022e020a2001120f140114 62
    0x5098001a56014242c18500004116001505d82d0000301050601451130365140d542550210101455001a400000c41301c409104010f15001e0107048102000789a031305101607646c010680f82e820300190110760b500110419001988035400c100088d08180c5091340050a011000c80c00c00c01c4040c02e2081080580c2e2a00019a2408a0a03201034650342d003240000d1010b01c41c090b45c2000006090928034106000075106904d00307411501b0400c00140e440c420107080f401d064800844054821748203509040b13948070f03000c4400c2c445210f04502c0c90510520400612040100e4400c0d40d41f000d013040c48814103c00c4099a201001c2d00c0400e1031006400000030080000a8414012541a0b076506c041c05225000c200c000c0c86172030209461400a0301c4c80550044071110b880702c0100c0302c0c1d00076183c115000e06140c0d1180540c40e0301440450f09502e10414540e9001c246a9960b40c180c0500082068160000c84000c02800c82e550104007100400407c00802d080412001008200e03003d100f200051 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 149141969 1250 149140719 149140751
    0x8060f0402181807290a0201090b0a0f060509070509040c110a030801150c03020a0b0a020f0414030c19030312060b0a05070510110d1a1c1401050609010302060d0f0504120201 76
    0x9070310b5288000780500c192940d2100c564014842c0c0401c6e440017188010315601c4510700c54006442c8112030503513410050503c2592405094010f1204070b40501d903c2c83d0040d4040d1003489031002041c8566600c4004551003400341150300c0400b0300e80401c54800c010985006000402c0038001c5912495501da40044010312402c03285644503415800392405500c01d540b4516488805050088016000c1c4140c051100c180d6000d40000e22074500d00b10504d11600d4141420b21102444032401000b101c0380624200744401810411130794145018001c03408600c0303c0c440144100e402c00118110002402d00905602602408240c2c3c003400503142c410040c21007107400c4481d080c0a00c12030200c10b124003016036031903074048448a1400c00e41e000080c191440029106001254203900342d080424401d014008044d00d800501c1c210348000704401d0074200c002440e070044c1480000e00c14000042c4e010169003c070b800041820f1203680040c4580d0400741340001001c8540005100158680440c0c21000d20305 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 149143219 1250 149141969 149141999
    0x140f070603151512020c0111030a051005030303160315080a0c06020303040507180902040c021e300403050109030f11031602060901020a0c0f08120408060f0402181807 73
    0x100b840e0f5000c40b07643d03285055070355141e0014882000da509001041243d030003800f0740c0d1003c54000011035070302d00c3d143c0d20710f50845502410313008203c3e02c2220b090140340c60000440380c02c03400c803c212240c084210381049015100f003d031000225039501d5030004441c4800114404828401c94880440d80d46480040342e90340403c07580540160322046040040142c5400789801c681d9607900042007180c21038010030107640c001c40e00c06005074440070420900500c1c034945410b5249038200a08100d81c00d030047d0301880403840340003035540b1442c070558190740c2181d0001c54000b0340d4400024003d046190034003030600c4010740c1180c03003c0f51000c4c0e002c3d40c070300d00302004131850000c41282d003c0c1c104041d9000d029580d00107a910398154803503408560040f441072042a8020071814620200443c00d040005003086480b0807016800141800180004180070584e0b0f41c0c000a0040344e40d555075124000207074618010b00669842e03501340014030030501490b4450f000c660426900b00c9500c180d84004450740410 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 149144469 1250 149143219 149143229
    0x81515031b070f02190e0f0a05130506010902090a0e01060509010f0f170705041d01080c060903030d09020d0602030403030b0307060906211b0c211b140f07060315 71
    0x1d03140f007101c0300520f03026019030045c01c1000c192184240d03c070803110f403140703500740e510306e5050000000b0414001414020154440c0d00f4a43c0c03a0b20307001d0390740d81e5030380c0c0c55006008202c3e9460300820215616200c00723050340300034641c01803840c3c42946d54580c00f41440c2d0154403e41c1c0060f08001c01c01c0b0002d801101303050325a00c507550b0340d6901d1038003040704c5240900d4040c00350410040104800a01403da481200318285403080b4448102c1d450041601c2c0760610b50f421240c0592401e205480641e1350100903038002c071a4180010508158620001c0e420b0f10704040d00500751380c40401804103045c0e0651062a003680c05404503000d098581809582481003032040380002940c06610402c0d504d200300744d40c1011091442e0200c0c040c01d02e20092054079003803801c844000b40019142c102400f004e070303400900e01c0b261501b00916002070040020045101c1c034102e044001c03a040c2d418004c00201900c038110039001d040544241c400c13000c2c405902c031141446014006070800c500d940c1c4411178004a441110 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 149145719 1250 149144469 149144483
    0x806010e0d0303020702031e070e09060408040b0a09090c03050106080603010605031b01090503071d100503060403030b010507060903030f0b03070506092b05070306050a020316081515031b07 83
    0x20340d09640c11000303507000740310032031f014024040d02100c04d550410503079010320b442c0c2c00a000c02c0380c1803040702100d02c00001c02c55201c0364089410b00011541440464064034030300340d502c603a80c0c403103560280c4102405e544441c2000d03282c0a41550860b41c5a800b05040c0d03042661181e0241d01c0d240f08040c266042c0c0e02800ea81504540c2c82990361010349032580110b03505c1810181802075540c0c0019050414076403002c00700040f200c4100442c822482252680005003003580300105083c078022942c0c0316401000141416600c4e04c14134402c0c0e02800680d181140c1c07010f400d12014240c7e14000b0050400d41d1603c219050420400440381d01c0c000c40c101c3c0903140b0260190341448034803070400007130400540810004032410000803855410701003011341c40d40c1c0103c00511f02c603440c5107840000c481c0018920310a4600c14010700c050a501c03648003c81c0c0c84210b00c0d00c0c0c5070f0b40e210084842c5003100b031119803d610203191200d10410b900340c1c0c40558070529240c081400c4000c00307118026040d11451200178546 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 149146969 1250 149145719 149145739
    0x60103050a0c17060112020720010f021c140c0705120c031002160503030108060618010e060409110301060f091407120e150a1b050c120309010b0409030507030806010e 73
    0x10440e0100103684201e051401142c011501664a03080740d0011388140c484d4104210009524049c4400b40203601da401c3ca050760a41004280094482c149401204035864241e211014014490044004495508080d20ba1b6441c1174601c1c0554030b60242c4207441c0111090500a40d035040081122030403a2800742c0641200c000007004000258400c118290a100844810101041d81000a5800b8095110080c000c80c1030950800c039110031840c414004040a513801403100c00c41144880d90003d000369000304007000f00c0d140000d03902a4081e401c1d13030107600c1c001d000903480b2200c0c50510120341c1d0380f440c10814016207220760134900700121850400704030a0103c41d821483c855000c03000c0518a982540c0d16402501e600681a4009a034215071980c0ca855000d201c401c80c81312910b25501c00340c2450f034a04410561019120841481d403c540d0000100004490803c01e42110300307034400091042001d0303480d604d40680103402103801a000260307080700180165025030303000d0340c0f4040014041f001c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 149148219 1250 149146969 149146997
    0x90715140304020607120507030315030c03020603040c1a0a08160503010611070801060303051c1a0f0d080408070312050705150c1606020306100513030b07020f1005060103050a0c 78
    0x300d68000740080381c002c1d9040048601188031107000100c590706544c2e030382d551402c02e4100241038841850030b041d1040142d2804000140354801400c0440e0380c1030752415120380e00c509180032112003c1e8007a6143d0999000c122150740741140003400c28403010f0316000c0b0302d620351744d20389140007103c42881c801040b0104010f100b10b0780544500100b01030400100d415035502d0360300700d07802e44100da44114003040d07022603a2480c6007014849a810001503140070004900d08210641c0303141003201700b40f80070f030000394068541510345450b001401a0040161b90f590740e552a81030742c0d40e04c0c4038030050390024078041c581066144602c040b154640c0d0084020039201c969024942001c03d8003800f403810944041141d17a0324042c403205800340b5103028200068580c0340c100180404100001004010420200310b51040683e03001450f109898001a2600c2c0c160748a1206914100c00c19807408003034450901954145a040d40080b40b0510b4283c2c1c044c0026220420140161503603409001c2c040f415002d40790807 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 149149469 1250 149148219 149148257
    0xe1e0f060f0c16060f0605100e0a170a0209010e0402010e09090703030807050415030b01090909080f0702030705030307080304031b0b0f28020408120306090a0e0a020a0e090715 77
    0x80f00c0b518607004004241025a035030812648201e051004658840341c0070031042c07500540b240d40700d4605082840c030b091280000512414481e0144072008449120310b990b8035541004103100c07040c1d01802000d0156119080304955200c22a4200e001582898541d140c600340144100d01404040c3e0080003ca81556010303150000014440420803405000008848520203d1102d258001d61000074074034881000040260003503402c16003010b810280a503000511481c100c5214a1003a00c400c1e03196011840000d062280d2544155450711020400c9014840808021070240b4401e03115094010031102000c0c0d2504440303c80a85074103000b50025030401c0744c0e0803d0652103a034440c26030303800c02c5040307020b880c00210241700c0c00306890340860140583d810802081e845046c41d150b1403415423400c140041c68101000302410203076070326003050048410b41040315050141d40206484000340d01c9001000f0b076214225000117052049420004080107840040034074001c40b0f655403500b200315070100c0c017 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 149150719 1250 149149469 149149477
    0xe0c13020705071517010b120106180b16020a0e090c0103060b0901080406110a020a0605100503190c0f350c0d050703170a12020c0a0f060e1e0f060f0c 66
    0x40505c078441103203001c4011640e01c242d0103810004a07c40d03c45048803442c0f40008016004141800b5034211844160391a480f441d4007101d0101182c9942c0d603144801d000c0c082e101a1034000d4001c0301090380443c1040790b40c80d9841c45001e4440c21180201c507102c0044080d55404d224403e0410801c00044105501c60111980d01a01450740403490600c42d000b0522690f108030309413401a0401100e00302003103020301a00340c0142918072035604860400b4000b03901c0e044202024451020152806003c01a400200e038004003d0480d5118045565040c006250050f0325448505004580e424500100030225407a44210914008000003000c84040c404100390b80d60094445100e02140000082d162240b101c0031610070a10342c61310b81d007610102a11101840304060413150060212804490300085c52a000607044440c11140c0895800c3c040e004100115110050380156441181d07031110407551028140c06410403038010140030356145440d40801d41d001621700500301c0c041800010f20708090 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 149151969 1250 149150719 149150759
    0x301060302090f0d030e010e0306011404021b01060305030405040c0203180f0f040509100b0a060507080a032c060106030603081204080c061311090103032106090e0c1302070507 77
    0x250030f42082c2100041c100c0507501c1d804030300091a10070304003da541c1c803054130081c05005500400055043c039214090000c024072405001e1a800b1843c017001c1c0140a100090010900c03000300110750701d03810055140e60090081d180258107010805141d01e100108032a00c0b0130380030a00704080029101040003402082c003d190340103000c44000d6141fa0390318465540500c04070401404102024403801c41512006080785200d8840c4410400c45a030300700045170307040c03079110198941c2c0303c1a1007006ea0051805506107040300e100d6615260400d0301c16080070185084510845484c3d0783c0e150000c80503105076020041c0b030310702c05100340303264440825000c41d0847e106480c654108003091030050b240c00c500f205c0150a100504026209114003200503c03421181580c0518040d8103548026040e80d50307461164014035140007621020803180c0d0301410250070441014021000a90022540d0302070003d2014032038402d00064804800c114801c07600f2032039009015000080ca400018800070101c01c140b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 149153219 1250 149151969 149151979
    0xc06010f0e060103090c05040f0b09010e0108100207020a0f03121202030105061803071e090e0a11010f0c020402040b0a090b07020d08070c050303040906170f120c010e010c030b030f030f030106030209 87
    0x40f03008e43c2c0354010502801916000001d80051a1040121184041e8460840c655101e0014051250049101e070001406c8800251717454143e440898810350480e4880340000c64040c002004000c0411000f208049040e81e940749110743c2102814202d11080c0719099001c041003210f850942c0b11160071094424008045c0c41c6c40c0c03595015102007440e1a8a08503003d01c10348002032080010f1072003200b1520030f01000800d100c01c0140d840c80c500080300503900341405010540d4002551040007032410060f8090810742d04c1d45d40c0c8500003001c5410903254000418000c0c075001c105a003401c0305860050f40c0003031019644055549442d6440c1c0d020690a94031040c0b4181c0102d00c944080004200500d2614000641c080c608440640701442032011b0030480d40040002502d10f0700c0025504a082042c080096174030308403a454140142103d1001104035420a014800ca0a400d50300c2800c0c20801a800d4500307418141400070b0f1a40305034410641c8580013800184400d601ca41c0c041c100310200545 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 149154469 1250 149153219 149153243
    0x11040b0a1e090504060c0816200c031e0d05031b090d0c080714180601030e0a0506040b06090f0c1204030302071a06041505030304090906021902030c06010f0e06010309 73
    0xd02c60003600c0b03044030251354442d01c0c2c482d000c08107607110fa4000c5d449060086d091010040c960b0f0024806d081b10512800381d43c008003940900d6a03820b1080e2060031300004c0403543c002800c481d2900c10000300b424059040c4c080c125103132644500840861b40700d0400e0400e41c018400d1250505804c03600b001082c0c40d000300251a10300001500041c0640c060920751008140d1b81d0700e001c070541c01c1400010055070103100a54000559401d80b6420300741c01c1582403c3c04140680d542c0100b17031901e03010003006030241c803821080c8800d2148040505009603c161031021141d542d80a50204810080c1d45450f42c500f010000301c800c65031045120754101d8413230700c0c0151810b92261200003600101340000b5505418003010300a803480c05101b800048072404c000b401d02c16150030f00180c3c40e400355206144030320740c665a41004007d0542d0407200c00c5c40c03c958040101411001e00299aa0000c42d1040d40902c9087d00108010030440300100896a09860121141d0b50b10780046018041c0c03c0c0c01141c0d071421843c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 149155719 1250 149154469 149154479
    0x1203021009061805030706050a02090121020f070b010e0603060c0403060507050412110108060102012d1d0d120b0f01050d060e090f101401050904050f06070c11040b0a1e 74
    0x103800700150b4003c0d13000f10b8882d911030428800310384002c0d107041c1c1d520380704112401d402d9800103100301c054a05034611720014010044060041d214100f01c03440380c240c000482d24204400b11f08414180c8010403042c0c0040e58a2100385a5500000d55428100702c4050000308002a03103a08600e03480580d41c0780035420145d40c5d0450b18014807040c003017111515015400c9013a10350784034003115482002440284500400b81e0754140850b040c04542e01409103410038809501c42c03031038200e480384225145500210817400b02c202900c54040b104408000f4000c5c07d019005902d0394018000d0307031a401000a400c05481d81c0c01545c140d84036080701c0700700f5521a1000110459007201080c8940703591006405801b4200100c00e0800c201c5001d0444c0152a00c8840541308038840201410345005075a2503100f9200c9081080c070340046d44020030120b104400801155560000b10f11040c00c1c03003941d00352040004070302044280c8254074403941d00050914410800b0241c1006000501008994000c2d4180d440e5 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 149156969 1250 149155719 149155751
    0xe0d0209131110030e060f04030f1416030e030613020901050603040311070f1d01080601060e01050408030301090b040b2202030a0e06010b03070906051e1c1a0a120302100906 76
    0xc0a8080d001c130350b8507088101d96020511006501460301840d070905440e041e50068141a1540156420483d0b100303d6014590383c2801180c0e080c00032a048000d0707107246840c0041028041040300c6000b802480d01140100918140d204070700c55005020304400d0382441d090021030f801c020000d4003003000c0c0d03042810084906201441c003403e80d4441d004d0580d414282210400c1c0094060715800160000041044480c0416400d0544420346005010b1108010040324140181c0e000755025000000001964000c3c0e5840743c81e4039841502c00303105c510009810001006484038040e014418203d00c1d148400390310754011903000810100002e00d4880000c10f461910f00240c00c640c0340c101d4000140300c6125003016000c401081036241143c80d10b080400c6c1141c03007441d0503c1502401001154a10a080e040040c03126035038402c80007008001d942c5804100e040096526650095040789000300388105403100c4a0000c3d078064006000d200e404900541c01041c082c2419a08c030b0381d54000c10000000e107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 149158219 1250 149156969 149156989
    0x3120c150c17130605160504090b010c02090901020c010f0b0306270d02060603060606030709030b0c041d19151a0405180f0604180210020c03120a0e0d02091311 70
    0x4002d00443c0c00589501e40030f02120b4018010710f000e1000442240b10240d8080102c0d000d94100000200700b4404e014010f80310421820b5000354442511003c004040720158050260300303011030020700241c52031100003130441ea49141c203250150404400101c038a803404510400349121880d11030101a04000c0701420310300d04101c543e0041c1c02c940d080c0728452a0801803182c000d003049035424a1030a1400018040d07403003500c8000c003c0c0f020040041c040e1685802590014a80701e81c11100ca4009203003481c117006011110382071001e07401c3c0070990b081c0b07045115240c04845154078000c03001d410034410207058004000304031400401000301041941b5001004c0840701d120443c02d00b41410984120142c43c0001080d8a001390728049500303a210b81040206401c50780c0550f90b80d070005414103401c03418000414607568140c820307007a280c425030070105e0050000011076606c00640d03110301401c0007151001988040d501225000200741e0194024031000e02d00c0e40700d48203a46198641d000801c0d081031b2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 149159469 1250 149158219 149158231
    0x6030c030706020a020f0a1202011d0604030605010302130515060c010f140402120a0809041802120606030114010e01061115010902031b310e010801050103120c150c17 73
    0x4c030700e01010850400c1c0c89203000c0e40300b0441d4070b200c0c0c007402e0070b010800c003d060000c003904015a012103951802076512601480c544080c180641e0f03aa140c1c101100684020320041f40952031104102d05480d03110700c10b090040c6106100d0b010b4042850003004503039040804150800c2d569070309116086051403180ba1800708410110303d04515190040002c409826208001c007500b025103a40c0c00030309100100c5004107030444000520b0b00402501940302200344030000d420401c480c2081c6100540000c00c5031040c50200c000f03003c031108517609480044001e110340c111030070300341d4014040507004c0c014904d40c0c01c0f48001196603c024408042800100aa004038511940001482030300b48500180314404001c00c90382c0c030b00d04a440d0001282c04007a001c86a07410f40b0710b180549640d010754091000c0203202e80350314050740f540c440b0242070082c0300038801282c1d140c100486c2c4a01841c060a0507140030380d000400f00c0800f02c103103c0c2c1da030f014140d62103540301009004040701c41d80015141c00d06000300 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 149160719 1250 149159469 149159473
    0x40b0706150b0a0503061005040b03090601090c0e0d02120a05160f050a0305030d0506040f0c121406090f0903120403020f1218040207020301020f0f0c06060109120b06030c03070602 79
    0x125107418040079046560000c01c0403250070448225495008802c581c2c0002c019078807400703171000d9044111098019600a80458800001070101d071860000c1c074076050744e0811104100350b9964103c1a1030030014801c01503002030103540c1000240c81c000783c100101409401c1990305416596032002d04144c43c001404120313404400f0300f0320240804490100c0544015503500900506540754a5607a0040040180c82035458100140043c0c41d26007042c0b203020b8010300284041c104480c000340c403440d03100c1041c030381e064a0f18040250043c181208540140d030081d141d0800b688500e20207440c1c140b4018510b11442c4820480f00e0011100d4024941c8611b0095015140621300c0c0c0c0b00003030508440962951101d1018449040c8141d0075271800c101140040f5001a500c9456101203130280c0281401d1a90120011840e00300c00b07441ca00c01495180313442800e440035941c4120042d19402d265000e130445030209040c0741000240b40300310f22900814002c044990b855000d40010f0300d056407070f030405001a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 149161969 1250 149160719 149160731
    0x10303090f0501020d17100315020d0506040c080103030807020708060720010b061902010b040f0203061201050708040b060d240f1e051f0e010e1503060a0c0203040b0706 74
    0x101003040032100940002d01c090502c3e850211002464001071b00009030306034400501050101c0c12491514000710752001484403d211444c414000075003004d1942c0d070515040000007030f242d01e00791044032503189058586588990854400315411280142404107500c103c19010904a40400c480e920540c410750340c0340340c001c201c0f201c0280001c0c143ca0000c003840c0c0c10b02000810a640d01000e86400d4400e0103004200040001c8040340505241204903030010315002d0f84080b00e11031a00194847e0310160707155004200f503181040d00701c0c1d100302c0744000015001c00200c0d000803811000c5540028000303003020b59190481c0c5522482b4414110803960403018041c44502c80700040c092103e600703c5145040044005181002100c0603044100d40b02e400d40d201d000459002e20701c00440500c0091400800c5e0702c58540320700c904141c1080c003540300d05022501c00608290707100f0075101c00c442c0c0086c1c09000c094a4a645190191244c59001803e5000501c408112403002c40c0107030000a000700c4000c00c01c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 149163219 1250 149161969 149161979
    0xc08100504060c02061303050906120112050d0c0b040b0c2502040609110405090901111b06100b070210020715020105041209030203031e070c03050102070309050609030a06020309030f0301030309 85
    0x300e51034001c3d59015908a03400300b2500c140c050202401d070035090708103195140925800103007644581e40044500e80030b00b0b4000325030080816440720005200d00b0494108108140c401d565055440000811904180c0300040008040c00c1400350008204d078013003801c0c5910355103510f00c0c03c0350b02d04c040315004e80700400003400d41c50715023f09001002c41280412030340d106c0c01001c501074030580c0680c80c01780d56440c010400f0010700354410340e030b906920541a9200d0192019020010184002240c814850540440c000c0340c8a0401282102c0b50268218a450307403581c01d00803072a000304001000c5d400340020000d07240d0004000c0283ca00250b070700004e141c0c6020700e00810101c1400e60084200300034003000f400141c80c00812182180500d01c0f9222940040503494816403298450040600028103000410014150080c3c2130b0700c0c0c40780d10b4820074641c441c0c00748501d81c001c240829034580c4c800305039100840e039154001d50b0090420000d51f840d009030f201d40a04c070b6078000c0e4001c0340003811850303082103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 149164469 1250 149163219 149163221
    0x8160b010906080c0d0c050307080a0605010b0a0806010c050f01051e0f01030201172a03220c0605091305040f02030601090b0303180f03060103050105070f03021c02070c0810050406 79
    0x805448110070400ca000d083c000c1d125074414100c48058003441c00040e8503000c0c0039111450400908000f805c65500c0d50301c5d0455035884201e03000080741e0700e50405002160718502c2400f5900540081c1d650840c55560fa0401141e400c2401007064449004000304981d4103803003030080030b120f002d120000b40c10481c000c200c02c91030702c4002045100361580800c010700050ba406056074000303040d000001410382d01c603500c0c0e014200f00b94007817020b28841c0b801400520313981c1b0301020f14458405006010089901d81400380703542000751701e000b404800051803e012942c0648040c1c43d80010161818600341c484050354011140c040d5800d070f510b490114245000c41c9002c210190141040040a000010004000c00e540c0e016840f00381c0018503940b8a071506588500843c103c086800504807941c0b542d5038108103000308426507000d800200390200a603081c900a00840d0802401000e81280c0e2842c03243e8220020741000004903158130749080c00240a8604005903162000e4100780007419040a26201e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 149165719 1250 149164469 149164471
    0x8250809070f03020603010501203304030c02100302160809270402040207060b040c0305010509011202090c0c123c0324060a0801080705030a08031306060308160b 71
    0x602c500d0100c0c02c050005840310400c0d21b046034020700348001c400355a1440388040810510411400f40300700e40a00c2c030701b5500c1148401c2c01c51081c8850081c0d8103004d55007550780b504115406804600d802100c48018100300c9050002245580742c01810824940c0714160304401d8a181994190b40110f200441894100c10f15502180d5117580000d2500a40241031400640103001038800c5501107142c07814084241c000c961491801002044800c4d0480d4018008003000e0061601903030f0540c00209560380d0700c2d4a8084580c0d0010030a02c1203a45420780742c00c86501440100c0d14501642d09150300080c4044041c042c440a110504415031400103500e4188660300c040358440701e210407444480351403400044a40241d604221442e40e4207070321106000c08a140106240c002c8070010f009045150b009003098142e030341d40c0c0191100c05030f5030000c140e500c050400002d088100c00308041390300d10107845846022035214110209000355286c5030242d40ea0000d83c0c07056182c6807100030000c1040340d410581 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 149166969 1250 149165719 149165729
    0x907080603030c0f0f0d031b03020a0c02040519060b0a05070f0c1d18061e090a08031602010506040b011e112a030d0206010902181504060f0503010509070825080907 72
    0x3042300c0b041060104120030301c605102d00c24940d0000f80808003d104a4458000340d0f00900300f0321807424071030151301410404000c801c0009241801c003080c0090b420049030400c03407445c6d445500781402c1c0c0d29080c403108100d40c422107031400645000039401d24020600e600c1000d980030015128508454040812140c243c01c0c000d05401c0720080080c60503a00f040303449400102840e440c1c455845420385454070b00000c402600c000f5000c02000000b00300100e00403000c503a40e034000e1126890359410b1000f541c819101c1d060104182110f90540340d2480c00b42e8142404071841c00d40c5040809001035400d002802030201c158840f6203c091941e05c00b0803000c00380800c0e00b074000300040028185c00a40f5502c042c09481d1015030001803201c60050721400f0a4140f05004041c0702d49a0100c1e110310b4400d900600c5a40c0c0420410040c0c050540e01510540b8129000900182000e0703855843c11250018020103107030004840d07040151803245155101e4140c0c0d56582c543c0b11041c2810f46400b40303801025800 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 149168219 1250 149166969 149166971
    0x206060402090a0801090803160f1407080c070311010f0516021009030b0907061d03121608041203080c0319110f0705010501050a090905030912030f07121202090907080603030c0f0f0d03 81
    0x640442c4bd60100d02c03488d4070710b000c1030b035551074000780c2c41c5c1000a1301c2a940c1054003441241d1010060140c61142015040f00980f10044900501502510790b03000d107401e41c0951706030342d0a0803405824265080e10440c40170f07103804403001307807603a84203003a00381e05640c0240c091740315502c01d110513a040781d00100082600c08080d40b4195407040045e550b007801c1040f01c987c030700d40480c0740c01c204403950382200000759010610715215a00d0364295004108141b009400060040001c164480318600490b401400061081260701454082e184003601e11000d500300c1d5840200040b91070786d1454006441024450400400e00754500000c024403014607410489032580740050750300c000350f0300200b154035030b0806403011903035043c07440b552904500801090309400b02c00007810342e04002c00007aa88480900355140c045543c666607142c94103e0044045040d0050384501c0440c20321401200180e6214000074126840c003050000024180000724038592a581c3c07040c00700080c003240a02940c10342e80d500c0c0c07030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 149169469 1250 149168219 149168237
    0x9050f010504051e1c0308091c1e05300a0c0518030c0a0b0c0105132a1707051c02031504210c0203100c0206060402090a080109080316 59
    0x20000e8002880007081300c40503118a044864192201058140388400b043c03c0c00c3c000c500301742000b8209071000c440d081c41a0082103203456450a0920000c030711110140d4a20329210200c8403070311580094800ca600a214080c04003807004104401c1150b24858654250800d2101d58207904090030809030602d14800e0801500e20550740d4131a0554208110440035012545030040110341408501d07020b03c3d4001040c0140420801d084000408a100307907500200400c1c1e50748503004120800109e07005040444044003590600c0090500d0000c4001004803031219a55411076200002942602592141c21811081200b1301e0a03000303640c101d41c1075030100000c020007540026100d040c1030654001d03420038400800c052140000122083c3c500c0b0007401152107201c0e107005824613280e01e2089220340b20703c200100b2901054002d5000e403001c0c2d070300249815210b180400020b5006000c10907000f2402e5903002410603024001d41840501402c400b958a00341a4102c200700c1800803121024010001 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 149170719 1250 149169469 149169479
    0xb0102070e0c0d020405031006080d05030405030a050f090a0e070f0302030405030409020307052203110303180111031219110301060e010c0c09090b010e100807031b0e0709050f010504 80
    0x30701c954050380d4500c5080e80c814155060400a0180b500201d8040c81a5650300c011281641d100c00b042e070307a58604440420f418000c049a41f880100c40050294006200d070200c1c241c0248050301815007050b0078030382801c1b407040200b82d6022107540505802c052400c2801185504482e840c201074006103019441d52409443c1c00da038a1207240710700840706a00100240c882031107802921003601080d4480340c0c241882e502c07081d02500325800192044000e110301403119241c0081211001c5551001a042d404411070042d10044d00001c441076541c002040740c1040e603800654100e1042032a05003003a030b10341d40424507004032404d150561034810001c00c0140300c0181c01821002ca0000c007440d10f400c0c4003000e854944501500e59100d1400395007403400501c00c00409210030740c140e40354030800e8115036032490540d5080c48900c0c421b0350041e8024800a0012644c1280b0624008e003980c41c00f00308041e500c0c949143c40c400700320360600009000c21814405403520110008403050f09107005400c041c284 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 149171969 1250 149170719 149170739
    0x303070f08090a030804030506070f08220c0506071b0801060b03160e040905060402090a06060f05210705180f0906130603020310021b060903030609090705130608010b010207 76
    0xd540c01804400000c61030310b44030380e6055201e0303001d03603408041c01c0d4450307543e440c203d0751f5100b0503075030720011030b00000307d82e02e01070710950b0002c0c85081c0401c006020141e2600710103603400511602a40d10003000d0901091640f5540cdc02040e800e88a540800c014041c0700300c0f414035055007074000e0021641070a0f02040324001c0f80068a82040e00300d114810055402102036030048000302c0710307540240c00c1054200174440c0c0424680e1042e400ac0d00c40f020541c5e1155010400c5440c0c0340103100105242000680100788501c0190800598003d184108100401180994180c00b210304600190300001c0200c0300c00700c070a140f5014254207480e96014880b000000445410009040500844e90ba0a0200b030f040f42e5030304030000841d005802c1d5200641040c040c18007030341c014580c048100340281c8180400c1c20000400b00e00c202141e8014500715206d90040040501000d4076220f01071048107008203440d6104202c404503110303000c00009005141110642c02d40768001c603028155042004108481e01c00 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 149173219 1250 149171969 149171993
    0x2d03030f0c0c0709090807030e0a0b0409021602040905010504020a09020712050d0f0e240405060103081b0114010f0e130201210203010306060e090f0c09270d0905030307 74
    0x80704110a881d424421201454070b203080c4d0003420f03428108074110061180070300041545038040d584440400d80003000f40110b0b003041d0b01c030b020314018040000f000400350b40d501070300c1820300302681485001c2040d0009030030355840b14403d40c1c19035900c0003800300314648492024024030b0801411b40c1010a20344402c0075002c005120340c424890001007591002d035040d030008401000c0700c0010060b5201c4010340d25a01c80d100083c2c0c0444240c41828007400c1280380001520843c4d005004100580c2540e0b10000240c00909010090004000b02c1e90a2100c003030086e81300c0c000340324510017480c0d032401c40d00242103111580310074542000300c0280091708641c1501d800c640c0d034080c00c114125008841510305200162070030312003200d2020002004104c3c0e550011400ca03190358103800144e0310369600f010f40300c62908028000c0e980c031002002d0440d06154a801e40d1000022008000071000d03162001018072603521200700c2a0420000c0c010ad090b00038041c42d0280a064000310b00301f01131580c0e81000f44203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 149174469 1250 149173219 149173231
    0x21c081003020603040c14060c07150c02091305010b060306030c0f060c1e010f0c021e070504020703080f070e0a05040f021303080d18020a0905040c0302032d03030f 72
    0x4400000380c04852046110000715030180a4550300d24240c100604849224000c030080340c41d5201c5100c406141000c15606180d03e0b00001d40816882c2100060036040c00c0ca0410043c8044d151214016a64080c20644524026624441031804901e030041c04c456440588512841c5c0900a1280b19140007440c421204015112683e0301400100020304038000c15040004907c100d4160014802c0302c000c2031118030700c01e80000c0c0100c101040c08101500c8c80f92401400692000b8502d01e04c2e008044000e222215a180c217071014152981c01240590b445103009502240030081405640c4910f0503003280d0120062400f107034130301440740000ba10380b542885002d110741e859454450280b06294100d0b01781604000244481c5503803451700b4400b50f008103213004422032034401102d0004a89813851080103500400003d9800d050140c490001e28010f082078685000d0301c034021006031000c000a00c4040d5100040306010030301910b80c0b44088202c0c09080d0a150001d2082c03085078920300d4040c1ea0001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 149175719 1250 149174469 149174477
    0xa0803010e250815060d0b0307080304030515070e04020a0f120504020114070c0e01080a140705090402152101091a1c1b090609050702010203040f0b06010203070807050f0c01021c 78
    0x11300c500c401d024460101110895015000086540c100409a8440c6070745880540640d1a21544d86643d5600c1c1d00a9201c05009500400e400300c2d01003030101d102c42d502c00caa0f81001e03034a000065022508a8100610250200d0043c00a104a8076040740494528a0781143d05121038641b9900003442c415608004444401c00480c0d03010402404051001c040d00c0d40003c0b9240542c0d5903800c40b5501c0803c0306056075482c648903090700810074081104002d5480c0a44080f00035182e80c0c0c01d00024200d2031000d529080014010400c0320384004210b0405510302620014180d414110140102c80f440502100300c1012030007080200d440b40d0342205101c0c0000b91880480302c0c0706003040d110007042c2c040c99070b400894029001c201d40d8200d074000000e0310350241082019039603201c03040c2e080b80700c1a00c010300541d48010311400016155825030b5445032041c030603241803020039610038071280c125590454641d04084002d048418080001703202c55082440201000384c24a4282202104503480103c104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 149176969 1250 149175719 149175721
    0x1d0a0219081317030402010809070e1302060c0f0709270f06090c0612061215050702160306060806070212040b03060103060510050702040c090609090f09050a0803010e2508 75
    0x4500c004807100300180c11004090344500b007403143ca511030b88100c808034081010307980401c4101034002032607020342d05c51a8800f1141d03114000020806106654201e81c07100041001481c9000c2c18041200c9003011240113104070f909140c232140a45815582c0000d50300900036182241491025003081d9064101c2c030805240c000c0c5082540150940080c0130345502221040040c1075039000e002c1c12029003402d5010001c964940c1c10000b00da0542540141040040606540e8007222960016801c215030f40101c44410210015504104281e64070035500c041d562182000502d80a200c1190300c03a41500c003030541c0f101c1c040d0001c4a0380c011405901c008443c00300008886034000c1d4000005004002d0035010307100ca01c1400148258441c0303008070702503030074016186a05401142c0e0141030383e07440d4407003260650030310580302e0050500c0c0c0c3c80c00d4102c40d2540401070118030140140d918840c0201038241d42c940c1404000305c903c2c42c014211103912480e041000052a800b0381d41c401c205001442d00d42c0d42 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 149178219 1250 149176969 149176981
    0x601030507020d080a1103240603040b0a050a0b100903140c010804030c03030b09040b04050d392a0803070f120216090b10020303040507050d1b1d0a021908 68
    0x406c5441c404801e00c010000a10400d200906880d1088460000c030744100811600f09100302c0d400140d400405c144205008198081116007116a000b842c91100080c81402000080e1004070541030060214070401d074240709109030484440c0020242c08024503c032100c100008064110080005e0100b2900040f503104041c841e42007c0e850900c010208985c90034281490f4020b0817080c0d40440f090301c00c03841c840c10101d001722429003000001d41e0301c840001003100c0490052882100c0886210701042e00c2590020381c0002c40380104245084505d10070200fa54003103041c40c55545c000301d40070b0b40180004c0c00011000710a0018143e40036a42c54038502d071800f4241d103000011804048019111701c070124840700c10742d00603960890f080f10a0f405554001d00c0c103a03280e100c00e980180c4203402c81e050138030241c101290b400305802e01c030308804458020028101242c0d0215504203200059021020050005c008141ca58000800000440c90212042005035039462004081c0c410f0064241c00206 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 149179469 1250 149178219 149178221
    0x15010f140105070b09010b210c06030901200304020117041713050603070e03071a450108070906020604030f030b03030705100f05010510030b040f06090e060601030507020d080a 77
    0x180c010340c0301c5540400c60400c1c5d1000e601802000064038020f4450814402c0c1c0198010400103c18a54001030302c0c4051844050140c0c0307a01c0108030403190f648551040e04901002503498014a4a80d540c00d612400c0ca40f00040c182841c280c10380206c03c00760400c2c8000700381980c0324401406d40302c00c00729645d80380c1c941b01c54041046a61005502800100810200982212030301c07001107802c030241d0344069101c00ca01c2884029038000c80310b6014082c020302c10542c40e042d200b10340c89c00004c03540f00d5009901d40043e60440030641c00032903840240c1c40c110f20595800601c40c80e0008000e041035590182401030080d642d601c01030002c0c00700309241402d0414180240d101c4110100083c056a5450a650400d02e944022880740005000e02c0e0100c030404840841c481e00d0305a030002020310f1000030741c01d5000c801030041d640134280d100d03545041c5680910401c1c0b203004000c141b44100440c0c52240c1d9954981011402024603041c0b604040c03c03c60010fa01140510f100045400c10307116545401c01c6001c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 149180719 1250 149179469 149179477
    0x304060b030c450405010509010c09060e0d0c030812090307031d01091e06021b03032b0f0c0e0f06040512030c01020301060923010516020f130b0315010f140105 70
    0x1180d01c03e00c41c29214103080c060001244940d000702c0003030101c0e441d9220b007142215210b02200700014201d64060240621030200c4002c281001803c3c0e0704900d00b81e0300c5002082455a008a89001f000128507440c40000406035509c049008003640c107040550310080c000e0b601c9038189114034131081900c101d46a000e10090b174003514505514a0440c22800d0201070200c130a401403001601c110000004007600040b1140c6880c0390160256092039035250000e032b41a01c0f40e06440300d500204050a0340001d0440c4224040040c0e0140003254160030321f0030240141d002c0c40c1100c1d00614000121140e0f41e01e69004542c00c90b0010b5801034845454a2034140c2180100402c03001954000400042c00c2c030b922000741d4050318119046182c00454285055681600344850507000c58000c1c8600303018844841140041240040e10180c8014903d8002402011044d02d00c2e4070f03d90343d52494090182002c100b0341c003041301c0f056444100d6504080b02c007010210203104042d80d0500084139030085922440a903 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 149181969 1250 149180719 149180809
    0xc0621050903030a061a120709080d02030a0305061c110406030501051003170319050a0912020105070806040b0901031401020913051504110a0807020f0709020304060b030c 75
    0x1004a4100184002d840f50b000b5102e1005081c200320300031070590382041803074100704003030b9405514100748500c0b0110b03030410003004007040c440e8074000011280d90501c040740c00b0340c03d42c1d4081c6a0340c0d441000080c040300d00c080e001501a05909803408101c24001d50411a41c58100c050f90b90b0680c003900c001005401340d50030090140d4201000d008460001c0c80300030054034407a02840035402d00030349a8100380d00048500006c01404800c0e04c011004440c1d10007604400310031004100b00c1c025450b00d440c450888419400142e544074100b14400c0e6014505039003155080310180301200c010760000300e4500d030600001e0041d0106081c01c0c540400250304662030708802510040c4804000d8100400070f200c00c82d0350f95525544c0d0002e20b081841c00e0300c03074440c00406c1130051a041805011007101d60070401400d182c00d62041e808404081d400403c0070703800810300f0f80805030366441d00c0d00d050f034180c800d0201c205000380e02c07401e10f01d41c0544c0c400d600034000c00740400d20309048a503480c80fa00708182980080d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 149183219 1250 149181969 149181971
    0x2c041d030403030c02030111030c0a05070317011503051006020a020111070e04050609010b0414011217030c0c07080102090f15070b01060e09090a2006130825030c0621 73
    0x100204040c4c110b9a880d0000340210002c010820310b10420070f403070740b20440380d81c0c9550100708a441c082c540a02d002c0c081050082c41c1c103503c0c0301c10105152440c00401e8001441101c50840c405281c0350303050042a500102e1400c00b015298a03144000c1e64410000314000d06000c1032110030902103000b001408010840b509a4016500b46401d00030348882c81a508290749500300078a803000e5003858011036606103204520301005a10304a1a4134416004d044116091140041942000003c8a0245000c0c002910302e0658404100f100c3c0c0745011500d500407036403039005004030400c80c1c0d00c4d50503007015985c007500e50400c0c800c00c0c00c82c1c108a074410356034002c0440222600204101c0e61122402c4c0851400b030b2651741103038460340300889d07580d204d10701c00400e070443c604000c2080101c002c901d05001c440c0504410704200c54801030500c09052508040c20b943c0c0b02800b0722483c0e5050b8415100e1010b030202c0840051800c58a41043c81d0300366019000500c5081c50500e0b09030000b142603c007244550b044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 149184469 1250 149183219 149183227
    0x13080a1d0d06090b10060806040506240a1d090c0a02030c0d0806040c03140402040e16080f0c010c1a060d06091101031505030a12050c06040302030301062c041d03 71
    0x307400e8004094400f001d440401035100080d0f035920750302030440300b07507011501c0c0c45060f41da6000400000c0c0000034841c68000244000030603003151055003480006036101d0016450303400e82c520007010141d8041c61300450000703c2442180981321071014a400400e010304e481da1304c501e18103040e480c610451080d61708903c910031b00c401d405a440340159025802c1100d0900c465114007504405840d6a600f03051604c420410108005140aa22140c0c0510a00b000e80b0300c80700c0c00c40000520407425a1001e2401d4122400108405006201d100e01c5e9a40908010110030026203e19940e0700b03c989124129003c12800b160460780c8840030007030740b03c0d400704007030000d01d0b0f0614202c48180c40582c90366020900340fa40c00040d9460070b54654094885c05801031041c84220307100c111140100c1c03800729045c0041004003001c1c00d501407100a01c0355010703030021642c079494400d0050944480b100900340015007000c0d401c03040c1d5200b002c550741c4880d04a60100c0c154120103c20022108160140c40707561000103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 149185719 1250 149184469 149184473
    0xf030c032a0a060f0c0201181d01090510120f080703050a0f02010b10080a0f0204150f0e09270d02010b03070b090102071208040510050306040513080a1d0d 68
    0x920303250410001c2010400901c404070601840c55182e002c0c034008030f4451403080c4906403082d0740d03405817540140342c400c40711b0044525003c48078400ea000702602e00c0001c1007111041411640c03841c010807001c8070402c624508445107111040c040e0040c50401c203081040744e014026054000004140c010025a584251524010b0070a612141c207500c003040650340340a501d00d0040c0301d0600d4030840641000713280304140508540d990001088016032580e140b03002c60114855101420180c50302d550500134030701003d10040c080d151052061020801c3c0501003940ea40c41d0103007815000901600240c060301a104c0c0e4240c0b40d0000c181180455229801c0e07080d0303c1d00d905401c907030b00401c010fa041d5001c05485042d116400d10420100d640541c0c450141003200090040c1e45400700390040444074205500c88001071a00e810882c89000098004000d00c503461525100e06a00017403002c055050300e40c1c0994800f0514061000044280014050100b04040b1540e90041030b541c00200b0500c0503400034 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 149186969 1250 149185719 149185753
    0x102070b150f010e061e0403061103040203071205031803010207060c20010905070b1c0903030f0506030c091b040f08030c070803030c04091503022d0319020f030c03 72
    0x6840703051003070000202010b810350084888801a1002411103481c1656000f04480300d200f0032401c8a5900404000010100f0040e2040c40a40c1003228403060381c80c141307401050328050707164100f284002102880b5000040000084419000300c031110020080f0310000068020700400a0103001503003000302d1400a1540030f0382c843c01c1c60300765030000300c80224031810040c01ca4100000050a945c00083c0520408903050060b05480380e142800c2c82c5414dc914440b101a225803c60441c0440c0e00d810030351207904418010035a100c20150020702944c00749000242c4100800b800c19030418060010a20050710080c044402a00c00750401000440d61079170788175601d60040101600c41d000711a40410603c0012088900a1324080130403810f050409006400070582d0203108091015010000401a12441344400d5809518040480114112a03c03c0c5044507241d000a100c5c0e0821000f091402c07010842e4903041c940c042d42c00200a440050100785070540281420354580b0401c03c1d4900e040300a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 149188219 1250 149186969 149187001
    0x4060513140c0a02030d0b270a0b0607020d0b0c090402040f0518100b0d020d0f020c010b041803080408070501062d0e0106050d06150903050106120c030b090102070b 72
    0x6072150341c000641e03036070a05460a000d0f0800703d03001a0020000c0404c40141600506028000141032584c018044004031b0345009070b08003480d040280d41c0c4104803100d00c4500c01c0ca1050300c0c1c10303203049103403002c3c0d5400907440c4421000020114030461022882d4894810b065640b149000b4004540d00c3e9100d00c0100307000482803050074411407402c102c10751280841d90b0214065100c803040c0c2040a8100100c43c3c070b00780c210741d80d0044c7c815820300c229924504203010300e054003000402c005940d2620650942c2c2920710010b0304c81e01403410400502201742081240b983c10541620b082c580a0f2614074114080d07224401e0090515801c2c1940403a10104c01548207002c1410700c7c1488046d041c24504003002c00c140761103000d21078505480104200c50080f801003800b07420103000092101d8880600e98281e051242c80c4000181d2000c20a1041103070901c546005800280126000600c0d01c0c0e940711400c6806000040400041c800030805a14094040c1c601d46540160030a0191504c0c040c9180d900729 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 149189469 1250 149188219 149188241
    0x170a061a0706050a2003090a05070f050f010c03020706030f0e030f0324010504090903020c030a080903071e0b0901050f0d091101030219030506190906060816090306090204060513 78
    0x3c604004283c0200f52403044140d00c000200401d0f080d0103a1040c05641a00010b000c203080b40204003041000800520803200905010518880c0b800d0801c8181700f15604070a0819050000803c590342c0407a4001404401711049494045030b00117464075500054508400b0700c030900d1001061030302607409002c0265104400a0390a140751000300c0d00d0030301c084000d10003491b021030000c000c2405454040d03089118428001d00484006d0a60100440d181401441c0280d035400008a1040890300d005d005410007440045803c03601884030843c88541c0d03c080307100d650144200003070703c00c2c0d0301e9004e00b090318141141c002d130322516000c0300d1403081c000c1c1a490608030703004410403501c0c007403540c028070035100c0d208499012210b03142a8510207038001c01d0083d00f1641c1c060100c03483c2204040c03040e40c0744006481d01e0b52001c03421518100001d030900c10003810074000141401500d0740000d51203140305003141c0d008140422254414004100200029045240c0250032181c0b101c4108101b030300040c80001e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 149190719 1250 149189469 149189471
    0x180c09040b09190f030f1b0303050103120201060602070b0a022d0c011b03080c0c010f150e060102030a0f092103020c0102011e0510050402070c061707170a061a0706 72
    0x350300c101d040f00d180100e0000404600c140e0014101081c81980e01d0300001c4003034104140c0321440c0700b2225000c99111041100000c3c0c8aa005008210200c030101c441c0031070600007401001d05003e0301a4a40344640107036802e4410116540342c0b018402c201c3d480740b181882d0301080e50161032022040c51100a120031b5411440f88504208a55104407011015070520300d101000c444520350302115a91005040041d50b01340c1400fa18412020078403c11541110490000681c00504039880101c004076501c0701100c0c4008004201d0716980200840306150610319048034481c6020b6030136540025150065101124581c1c01e092241c00040350010007580a07400301c0d550b003440c0a004a090b11007400400b4030408101c1e001c503a000d0b0150304a00e40003004001d200001e41d8440d40842d0480e00148400d407000702400e9000c006c650f400c04d000100c0d50031600c3c0345c00b5162805031005442c40e07070784406041000c401040007643e01c0142e5801080a00340d00c40310b0341c04440c0f20008802160b00507181c03c0c0c0d405 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 149191969 1250 149190719 149190733
    0xa020d2001050a120902010e0a060c11040b0a030201080919080d2d1107120314010e0c090603070c05070303030c02010f0915020708071a010e0702060906180c09040b09 73
    0x798050340554221240c0d540d205500500740020040c05032042c282c04034140201035a040100e40c0d10f07414042d01504460741c80c0d0103107036185d08105e803004101400c42401280761900c00d850b29100d00c0f14400c00d0300d4081c245243d260304c421003c01e00e000c16949480b881c808024a03a202048800d40c020a20b941090b041845009800311104c40000d822000419030407a41094103686003250f50007000310701480d404154205949915042d2034042c0c1a030309100083c1c0c1d0b0782656080d1510303051007540500012820b0400f18603005a400e9164461244040d10460340400011140b900c07407044209960b0f07001c000c0e107914650324680a40a0031806c440d002c0503509041da2440f10345d0080c482c0000c40c51700160141401400700003454000d501c0801c041d41c0d004006c000400c040b80280003a074403682d000c80025410340d0708d801d10140002c48007400520841d003050091042a1600141e00c03600f050320363303880d0140440c203c5c200c40e15020700300c0c05c00c42d04050104100010710100c00e03145449414030f40203807103076 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 149193219 1250 149191969 149192033
    0x4030809010f08060f01081f0b030703060f0b25050a11010306080a020105070f05030c070b0403030806010804080702041a1302072310050a0204090204090b011d061602030a020d 77
    0x4420f50440e005608440800c0d8407940640c400d02065130050101078009100400320640c0f0303040c400050300244181e1000105100e00c0700d80c507103e031b0001403000340c00300c3c6982420030881c01c446124070300c030440d4508081402c621406200d00301109042da4400201d4080180c9443c0010081841801060101e890141c00180e88400412060f0a1903416500c052802e895a51100f011080141c425203452100340076080c2a0705041120001511078409020740343d52551a00400382680104050f041100c05002d120001d600e42041c1e0706010750445010400410080f09041c0707115000300030a9100240b900040c4803140320b5801400310f5406801d6a0010154060017410111200c0442001d0340d48242403405a0031802c0d407029410000300d607800341c81c2ca0743e1501e04100f41c0c3c1040c3c1024500903602c04141620b90b030040200c5840c202038040b032000c100d0802000460300c0c0034107004a400040616904002c55405200d405070b40d41e07005064041c2d034005030170842c04142070040d50b000b01c12402040946 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 149194469 1250 149193219 149193227
    0xb030106060c02011404030204090506011e060503010323010507090816060206070f0212030c04091406060405010c050a0b10260604022709100f020f090f0d0804030809010f 75
    0x4181d61181e00c0d082e60030025503004503000e080c1100300d002101018000400141c4d00c9004840c800c0c0c5c0038000910302c55040c020900360a80a0304601540484090400c02040c0d801c0020350b81102d07000b02c010085001c2829074452071820700c5010203100e501e400300308402c0c99007024588058070003a10480303092440b0105003505402c401e002d4a00981e110301c001402c101d08c245080c0c00c06500c07510503101100e0000309062650f803c187d94403107401d440401d00b841001000d1140403030282640350f52117600c0c248103012800e1489540a01410065406c00070418003404000311460a0b17800304046155182203001c541030101d007030003546400115400e05650440142d6080e54000791900003078840364540c0d6081000102c2100800c0031138050024440c00000c4040030b00601c5422440d000e0100c42582514400441d9403a0a5407034070148140701c68485e28041c41e0540d40101d2090b2040c25001c4100700000d5111140000b00610064000801000700040f0001401c02560300f038a494550070b541c154195 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 149195719 1250 149194469 149194481
    0x9060d020301020d06470f13120b060d0b0105040509010e0a08071202030301030804090f0b060c0616050705100b0607021203072f0f06091201090b0106050a1715040f0b040b0301 77
    0xa0a50701c1101040c6d080c064180c00038500c0e5083d41100c1072030403805804603140b0b10506e41c000c2c0c109001442440f400e1006001400c1e50001c070844800503510041d5440503d0b00701c041c05418010b99a510005074451000d5100e102c10751110000c807101300300e07185441f451580c08030104803400441c00f009410218000030959060340d62200c03c407400c0c142000450f100500f88001c00942454948043c3d980544401c00100441040c44015100d40d10f444a02411801c3e080c86500081180130401000071460209205e00303001c083c1d020100e418100c09002505030300616030044d501c4036041a084142c039500000812560b4070828454091148030300c04e0147d00b0040d90304040c0f841e2001140c1032068030346541e4465903040020555402d044200c0302080c6000b5450780382d07000036950b070503020061040c06079005005000c00d2400c5440c2c4000008028100740c2940d41030400c0400341008143c02c087d841c0082008128064001c0015000d02c480c090301401c81c0080d42402540340400c401c4507400c040c0621 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 149196969 1250 149195719 149195819
    0x1404140c0d0807080d05010611070f080d03021b0607110607050702010c020603130804080705010801122a09050c12090c030303130c0302030d0c05150609060d020301020d06 75
    0x1500028102c0c0ca544a00d603100050440b02840304200d050b6500406106041c0030b04866990141108e0000d00b1040c071340742c0c3c40d400580003004084410821501d0000c0c510098001501d005030300c401400320b1100c001216100d42d0841401090204500e6603404260091440301c1901119400c0d15904001c0c0c4a5204100010b070000c4c9044c0a04c01c0036050400045800a0401054160050b5291144c0a03d82c0058100ca5615002000100890369120b201c10303016010b5072000040d030500343c0e80e5407014803130b031081c56101007503400c003940e6a1100c030401d40c10014001d110080c01649000d000382d1310283d00407046120080401c2020452109000400c01e154003000390040d440d40c1c0b0b81303480908042c551a441200c00d40e10a03407006c401a2410302039030500d030085d80c981001009041ca002130400441c005603c409101710002c04c40b0a07a102c080480c1c0041c0700780c2d8000d1244c41e081c00400d01920494094594203400c100c0300081d0f20410751076020101190300e882510400303401a0f6880103141007444 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 149198219 1250 149196969 149196979
    0x3020d020d08150d03020c0a030507080f03031504050603031b0309011d0312030a0603080d020304030e0916120212040b0105030c0105120604050901090507090605180402090423011404140c 82
    0xf44003468280040d040c021035003c0e004880c64281041c000840c2080e01c3e8200301c0c0e403600112010000080c08019403800f001c00c00340518207502e011041070410b44540700c0310300e100d19103800114030b01c1e84050040390301041407504102401400241e8a0b03559034064a241c60003d500b00410803841014544404030f0b0040c0107014003c035410314000780c221a0005410701e04d40950b5104000001184040240501848c0707000c00b68492900307040181480d4410030405015038004410042201c004020400109429040c075010038034407982080e0003070080c2c0c28004d42807060081400f0510404840c0030341210340841c1203520104904004582501414614103c2190b80c40045000d503e81a007026610007111800001c4041c080e031242e51a003a020350110851076501c0c0d90501c4a400c5c09403200c1d620320305418042d40340f400c0603408138100040061007d040020011030908040040c44082407a425580c8001d00600c12024032107007046c20184c0d011110001c2e03c15116646400114843c044480b000741 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 149199469 1250 149198219 149198251
    0xc0504110306010c06180c090e030c030403080304030302040302090a0902040b150703110c032b021f0f1b02070501171015020a12050c0f0109170c0703050a03020d020d08 74
    0x19688510384c180c046030210b4079080c4014600c2c107505008030101d8003841e000100503103407410300400c6500c00707404070466420800c0b880c011900c0c000f049804607607011042694039641e6090490082c05141c00003940302d0506000d1100c546210340000140ca8000c0300c04000b111501c4080005a082c101d4441c1c0d0501020b00c003002c08603000345442c07051088040140c440c2d1403490380c0080d0501543d1084010400140e030342d05526600e01a80e83c4001100b140010b180c050410a407405c050990050003c0d002034075004020190200c58200c602500e66001000d04c074200441d8002e5180d500d9401000d0004520600b9130b4004440000745a015060000401500c50b060100c1380000080703450320441988074003441c40c00001c124000c00400c0304103680d0307401d4843c810019440d041400324400f09a15a0505070844003242090400d03030b40900607412891340c0d44214030a8a070405040d81d00c090702d54098406038800781900420500040d245c02e40c00d5549a60300440d041e034441c0300c259404800403000306 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 149200719 1250 149199469 149199481
    0x5010206090624012003120106020a0b010b0a05070f0503190806100302070f0c0f03150912030203060406080703050c011b08040b090612070c03020706020c011d0f0d030c0c05041103 79
    0x820600c0458061420724a090300c42c1901c00e41d84582c8400c1700040b54000290100700c880c81030b414a01628941c405071910310110784a00d40b500c0d406014000d5003010008c0c11000507405681160000c5503c4070007607000140300e007010354982d000a0502d01e44c0420300100d03900168802e002c520311440005103204413421100d03500b14001d410a4804480c002d030042c103103001280f58440250000c06407030a1300901a811351505103041c400892141c040d141c01c1903007003400182040740007120740402e0700c0c0c0142c40c0d5079440e001401410140d40103060707030300031104040709010b80811000000c644c2a2614481d5401100c18604000c9034401d02429071803042c03106001d001c146600420701000d00410030b03401c000c0600b0402105400c1602c00d403010403054410502010340500006c00140254000342c0560340d241d40c0044c01c3d0107100e116184038445100e61030300c2582d40d03241150b00c450a0142842811641c2490050002e0051340300550700c140c50458009240c0c54280202c00c1ca550300c40e540b041c1142c80322 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 149201969 1250 149200719 149200771
    0xa020d1d0d030c1b181a0604080607140a020d031e0f050a1503020d030509060f12060103111e0921160503060402134704050106020304030b040809031204050102060906 73
    0x10382c016000f005680e40c038203401d580c4000141000d480710310080d00150030101d2000d81383c0c0340461401d1043c0b240501035374200c039401240700051108a42800f044046404000e0b00700e919003003409105d030310301d0402a495031040d1a400304d40f048a8018041241e040c42c0c0d14603480181c800d21009510003082900c03400043d2081015104801014050034101503885010101d9070700314140400c400c00b0800100b04803580c2c10300980d00c82e1001c11113001e152009561180000703000d070319444000500002401d0b080c075215400f90706144100d0485420b013204000c480300e41c90b407280300c409503540990502c01081515000c61384a0003150300610342d02c0318013801d001c120081c0ca01079601a81481c1150711905490f074601d041c4440c072842e082c1000c3c0110f03102c190201562104107481c18000c501e4000144803641d000421203065a07002202c80d04c142e030b51480c14110b1441070032031294250003100d0401200e40d10060140003990401d07001c1c0e0700569900c1d64415941c500c112840301d403014542078100240710391 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 149203219 1250 149201969 149201981
    0x40314010b060d0c0f03050603070b07080d050106170109060b12040f0f0c090f1107110a0909080301030c061b020f03010f0204170c0102030a020d1d0d030c1b18 70
    0x444002103070301401c80c000102c094100c0c62001600548591454405a40c030094404808100d0304080216052500100340d4030744603401020401c4e003001030200d05019103071080e502c52109c00a02808550b031510402081c3c6512a24001520a23568001049201a03400340b501a02d4000b02000d090600015220310a0300002c0c000b620111280000100413908058603c20707524003880107021900e2a01a03008100e4540d0321003145030340d2408480003621143c130790072507481c1d03a001184483d0602844000580d080c0056118001251500c0386510401001c0d101644c126401410350560301c5640d11000d5440320b0940c46e00c80302d0b0031010343e0f00200501c2d220365000c00f000405400050102c9480d80350a08981c001e07044490301c150100c0020031010002c0082142c126402e10185040c42c0c180c2c0000b95803031040341101002d00840340500e8090740384043d40d44100c034200a003496200051414090700001455509035802c40070403515054000d1618060411074001c0f2081c031002800460303004004080f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 149204469 1250 149203219 149203253
    0x17040f03110303070305090d031514040e031b1009020f090a0f0612050c03010b0109121703010b0304021002060601020d0c08040b0f04060905030606012f0118140609030403 75
    0x41c01032450400704001440c411541510000380500b49000c0c4903140c5003a2400c0301e030815003850416060204001d1007881203030410081c441607100b07800001000f42c00d204d1a060003500c0301040e240412181c0c0c00c0c46240400e166400e407202c0442c2c83c0d401c0c1007035503601b2001035081f41e25511550502d040592401c0e80c441107401c00003803c01c00440d03414003500c0c101d511250980903000019024804144007400c81500d080f8000c0025018447c0003900c1c1d01c2c22407180b02000c111000e4500300303111000303000340c408044078240d940e0b507581c40341480da850f0307081030314181d0140c0001520f6120300c90000580a014400c160000d0200d91080c10341140c400b20100e0f400c071025202400002410100c4102400d10040250764490300c039810000010001e43d2241e204a1096101005200040c0d802070980c04020300c0d00710481001e0801c2d60b00031b91060f441204910041c4d0b180c032012a0303504840d05040108a40324811141201c4007000f05140c3da020103407194a19030304100401c200152140e55400c1c0061 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 149205719 1250 149204469 149204477
    0x6090e07050c0a12020f2a09040501022b14010803030a0213331b030c0503071a0901060501020c060d0209031207051609090309140a090614040c17040f03 67
    0xd8001d5540003401c14004d4503070710140c3d00c010f0b040000c03c8424000682c1b00000c5658020181d0000a00c070b0000c80400001240184e82001c00b040600400f03404484241d070700003090000320503030007071001d010703103058905540c2582ca083c1c84042408440700c40c0070704039048000114119100c8028240085d44402013001481c11500c0340011103036a018040c604071035403a07899044070f940400390100d03903800c0c150140e402c21a16600225401441c03983e003080340f613058a40b10f03145c20b08030b1800521310320820101600e0100034101540c1440d040000c918031a550401c02402010340d5000166641c00d0f00a60381e0381d0000c400d2204003244040707680540501d540050450b29403540000c00c250f92907101c800c060b41e0541107001556003020b0f200c00d442d001005111400c003c082080e403001814929280501191400425079403e95030b9a4440103001800c3c00c4c0201300300e20381e65105a00c01510309017180602a9080006110005004408880c644c1281804504d851b540e6603580c01d007200c1d140c61044042c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 149206969 1250 149205719 149205733
    0x50415030b0c0406030b270a1d0706090b04030507050d020a0e0c0d20070b0c041701090212010b0604090b010c08030a14100b040b0f0d09031806090e07050c 68
    0x801d801024031800703141d0504185030748a0800d90000d040d0b800704041c02d0702556031024072a1030242841e62030300703554038480307040700840c3ca40074003110103401809010b90010880e040c420a40c0305c0c0104c1c41000301d41c0d20343c5030390510560f208a4840c60b8010f9100c0075040782c000e00c10811080c14040c0c20701ca82c1501c0201014040303500d4015080700707040240c4140001c07175004104500740d0780d0702c0c0c4500105c01050b08442113541d41e1400000d06244101c5600614510412002c10709481001040e10090036490540c049035085001c0c005009042c4500c09178406d002049207118020418469100c1404c005040e5902e002d040c91480e0020303050010304641040180030360240403940b104042c5019074480b210200d2106096402525603003070142010008080d6204e0801881c2c0004048804075408149035940344c0b451407022203114080d0b043c100c0c0c0d070941484100300406034003a4446000042031004c0040c125218001111480c10030702484403070040c0780021481d081e0166000d003480c200034804607124 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 149208219 1250 149206969 149206973
    0x100e0c06030906010f05150406050901020109170901170f061909020d020702090a05070206130c0f060c05101a13090204090b0a1109060306040c0215090615031605041503 74
    0xc6900442d9015015040748005000524003602004c1c010241101c1c80365075100300c60b5405050344200e00c920400d10000180032102d590007900400c0550350014140044881d02031904074160b4058818180003480400c5c1056407031b503206500c2c2d8012203001c1d49140b216602c0d44144071000161071030042980d104a10006011400c6000a21606030700d46070160f15002e151040c4041040c02510099000f42028200841d580d4006500c503801000744d40c081e840d0b680d070341c01d05130300380c9000c1c1d0030400c0300028110002c503855401038030b4607014510400442b00411a01c2d8006c1080310900c00b88043d0512000c40905554a088210350101d443d0100c0001003070111640001e007142c8080c0b1003110043c91200811403c01714a01c9010043e40c440101185013044c0c100015156200080c051486240e441c424030100364420805243c03045c1002a0780f076454180088515130744c540c100c0e015558a048910b0120041c103012881651a00070b501c00d0000c15800d00042101030803184c40407000c00100302c500040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 149209469 1250 149208219 149208229
    0x601050d05070203090109050f010c020f060f0408012703120f0209031e060703090305030a020714060907091a010c150f06120b07111f090b0108010c0906080108100e0c 73
    0x8010340301c6400440e610407003030f0000b41c503e8081d23a11285c8282c03a0321281e10841e0340c0090240c0400f5030b044402031110818000002ca8500640320108500200800d0200710803c056016030f0505034188100f40341082d034807032048480520408014001080440080102c6141b0b8114002c010b01c02940035041c00105004a468075000a802821000c10034050000d406000c0c8501c81c0c0000891a007030001c030783e403518080c06921010300347c80080750307000074014103104034000c07000c000b11040350a4442904180541c1c0e0750711005030203442003080c0f8041440e451494442a050fa001c0c2042c1c503241060b4405444c3c00001d0300c1c0040e84c8481440e10303106c1c001c51041d01841385d00094003180c00d00200c1c0c0b40b80c40c1840c00c010000104031030144800000e6a001201000071110500c2e140c0012003101350790701446070b00c040c002d212001400c0c484440000b1940c08019003094070701150036a01c0110960b030740c1d0b000325144030003031007003c06981101d400b640c9501c41035000700d50404101070807541040d283c100850 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 149210719 1250 149209469 149209471
    0x402010e15030f010807060203040513020f0406080f0601020309011d03071502010f0f02040f03140c061308241302060405030d02061801020f030c03250f0e04060312080601050d05 78
    0x4801d0074000070821494080140560b405042240c005004080c01e0240103580d0f4452030007050b104800c1005521402503083e0100d0304011075800c1c05a46940d0355140107032441c2815100c1403c0342903138078001880d40d4400000c1e20485d200583d6903000c8036031450070f20140b49020071450f981602038030700003080107003040c9240c44401c2c06a50000504461003d13000782110406510080203e0040204105031036011034500c1c02c3d650480c04003c078402203d0704203480c0920000619400420201c0c02410f0103074040100421103622006541c0c425448061769044044043c0e603040260340d01a0101d108005901205601ca6201425007450a41c481000904c1c2c17241d00a00f1000590041c01040146180400c0104d84000200001e44c10040e034110410241d00000b0504007041c44080002079040210220030364502c8202d100c41c4504049040c4010303c00402c03c0728601c04100c1c241b01c5604541043d1064004407034229803c1507800780c3c0200121102d00000d410340b410024140445240130019100d00303 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 149211969 1250 149210719 149210749
    0x30a0f09050d12051003060203280b1513030b0604110316090602060c0301150e04090b0a0c0c0f0f060207120c020112140601030e0102040f0602060a06050906010203120402010e 77
    0x40070666202c2500405102407441008a254107290500401042d02e016100030f5130340c02440981c595072044142c180202c1e00001d640102c8420f845502468032843e8410020340c1800c0c0d07141d1220300e80301c00d095006403180a4140316103949013642000840d0704c0c6000744d41c0140c0c0046c03002c90b10212884030040c243d08251607205100320310b02014042030703804c98039040c0103007114000f44c0041d207000b03440c8680600051090300200b5204056101c007103441424001440b260040080141124030309114002c028100c82440d0401d2421445441080c0603285290b031840d40071680c0c07206100d959441c180724001f0510201d4030207030207000303020010309818039000c102c25482e500c40c14100400d0000404c0404a400d40040d0b05180111000e0705104488007582d101c1e03000c1c02d012451040081c2003d0082c880d5601611780c0305550140410659804501c2034003030080d0030000c3c015aa1030b070b0100843e4402c281d41c0b00d40560700c20000c0503190340d9040c1c00b40354444d005040490300d41c004d800126100c00c01030104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 149213219 1250 149211969 149211973
    0x80a060b090906190207020a0e0a05040507050f03100905031b0a05010b0907050910110708030a0206010504180308070c0b010605030403020105160212070f140102090a080a120302030a0f0905 83
    0x120228070306203003403001d034404090401003040c0d0a0600009a5020008111200d134640008604d020b54035024008001403070301051841e160721304039130349400514050b10111600d00503c03400203602d2408850f445203c0c40b009000c1c2c82200c4103a018480101301400003114580001d0160040303a51417121003071090281080905410910740c03900700e00f1640b01c00b50281c451003c2105012006a01805507680c40b90203581c030001108000ac800d03500512594004511407040d07020100c0c26810100241c1300041d00d94003180c6160342c80307804003c141c510580048844206801c02d102c0801d1098080640010b40c42c1840c440021541c0c4900d01c0c44a4260030200c04144000184800c25a09224031684101600c000910300c01c40908000d403502404640641118000720300380302071040007010303041410b6208202800c0e12100c0203120b4081d4100c610191300c07034411440002425480031074064007986d070082000d400c1d000740324400d8001707400150189818582d2001d00e00804121407007204480750140c00 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 149214469 1250 149213219 149213231
    0xa030809060c10020708130f0605071e062c0a0b07030209120f0105040c060c0c0302010f020f15070e03150c1602040e010b090109020a050409020a03150e0703060b0307120e07080a06 79
    0x45101f501c48829441544582118a8100b0580342e00006030707403441d030740607011451400080f0300d455005171000324081c0c1420310b0210b100c0c810b1752080341030158962000f42c070003402c80300d80f803000b41d22061080000740030a801440007614072482940200301c94480180f1a160f0301c907050250764a01044c4c50080d8005a5468080c042030020700001d0200600300c0d45024500c804855880701810845403100034188106101c10f0710480307000307008070960a10f44104075501340030039000304400c1d00401d440407004101c02c0c02070540c0740c6c100861200c02c000c1002c60322032100c0e2241c2080710f0450748100e4002c0032002d604000e100c01a59070b4020001c0c0300d05940004184001244200a2003001c1a40519103443c410481d55401d15003010540781221340c442401600c440d09508194040c2c0349860805001070307100310703002c12680414442e141c000d100c550383c00c001d515102c1e04401294801030310312001040c1c1123015040c610a154001d00000d011150954442da655850858640492103404032011601c3d11 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 149215719 1250 149214469 149214487
    0x80d0b18070504061e0e01080c0f130509060d030f0c020112020301060e041508122107080f07090e01030b040302070e0106020109030210061202090c120112020f0a030809060c10020708 80
    0x2c0030b118814900000d101454450700307171000d00b40c03100d1142c3c490706120400001030000360384101941c80d0440350360308460342d6900300f82507400040b02502030704d40700e140041b02040c100e06002d03540203800c540c1521150080b440201d025101f00c40b20f441c00f241045001003a074814178402d800954000e0815448080413030b444801080305a50000326440070041110408100c2e0810024103100240d2403040040c1d940c100d02c2e0072010010b010b0581c3c110702000200280140c40d54842c14052140720502c106604544617503108451194076445404090b8036001d0041c4081409209000d070410301c24011540b2070740d541e441800440800343e1120300940d54408041e07060640501400190b0305020303208000841c2000700154070210841e2000c1e000ba6407500c00125051410400c40c0d070018401041885907607942c6018030315081e5071501c228001c0500b08041203240c1000d041c0b01c0c0640781c0c084001d40c10034850401b801819000b150703240d0850302c508442c0c88603030b203ea44020100d2501030f1002c180d0f19002c40c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 149216969 1250 149215719 149215727
    0xe040602091c140a02010807110a05030a11060a020c0715030f0504060b0a0803030907090507110a060504060e030a090308220f0905100e0c07021206070e0906010c080d0b1807050406 79
    0x2089080c0f58001030740500043c1ea1110080d5480348607802c0c140320220800d01450318003c010700004026120024400107016088030904038000b0900c1e00f2181180e441d501c03107106038050480c51120070340c010304040c09040c0004007514020f601d149170000d8518002071625007034480546040d20a15916000d811107070402c0e6a545014203586c40041d499400d000000301d0740c0f694a8410300110039925070214113100c1c030806814481c102081e048643e501142d04161000f01000e4a00700c40c0b142c274240013805419008030585601c29016200c5e8282c561442e04d0707401c1d0541c011000d503415403503c0c551101c3e03908800c020a001a058420004001d03a0810bc810001ca6401500c50001d0700c83c9041e0801c80304044510441e840540305180c0780d1112001d02c0490141c040c104800c01990146208100807151700134141006d10504596900d015140c440064071110401c0c400644004401c00030304142c001d141e080a030b18208003400d036010207a4141100401101d0030b44000d070004070001000c209150340 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 149218219 1250 149216969 149216993
    0xf1b0c01050c190c03020619030b1507060b0609060c0a020f040e121c110a0e040e03070f05070b030c030a0b010206012106060b040b090a1409010e040602091c 69
    0x1081c24414038000c41a11890355500c80100e0107001c005008500703004010204ea442c400655001d0405510343e810403140c4a8441d00380320514000914080d06896540382001c016110140d14031011442d0204075116080034003a6042c0d080d803c25010440c0403040d40740d1200a1101c001c0740000740c03c1c44210b40c41005020320f901300e100c034440d5040550101302c084001c036009940342403003000704d5581d901c03a200c00e00002c013100c4481e9468900d0583c1401811122800a048083c070980d5500103111181d0104001c81b0012084403c0700e510901004000a8401a400030200d00031821103003010740c1c0e80301e0710f021588101d80c06c40d01d403136002c41800300141c010f010f403a150082c2400501082d604154000b4030021207030f020f03a8410440445a0001e100031540004040d0103013481066441c2d446800d0442c00741e100d86043c9004416080b00003480c20061482e011600384018400d02c11a403034103285032241c0304090800d0b51169802c2140200d196540c04455242c081c2d1000b80700405d28050500d4000000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 149219469 1250 149218219 149218243
    0x305160c06020109030e0f0306010e04050a0b01090b09090a210c080409021c050408030402010c0609021e1809100902310507020105070206190b1201020705010b03070303051804020f1b 80
    0x1507002d0710700c1f89a8000c20141d0640d2010b540041c43d9554904205140c4411300c000545024445c400100b202c0610381c01100341c0440036150800b4a8850840360340e558007003110007624607030021503240241d48104100a074402c240d440c0004180041d0388030203c0300c0c3d01c954070803085240e0000e00c2d031076082140700d1682e101150180307003049940b8241c0c030380001c1840000c100034100980000d9280c00c100007a032000d900c182d0050442c01c0302c041c104040d8203824602900d030f180b01d500d48200c041c10070340404a2b41d902c212840781c080c0c144a07140042000c058016244120703400b008002507243e444d600e0203c005068072180c840c000d001940d100700101180c0f40940340c5804c5905050400000c1500010115041202c40f268051140d1058107410000c01c6602c039074903401a1801c400c081000d805401401d400750085000300f000380030040415958800900c401000b041052051148000c00e40020312104440540054540340c0700d810520800e92248001401c0407804264000d4106c10420841c0740c050 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 149220719 1250 149219469 149219479
    0xa1e15050a0f080613021807020d02011b1d010306081615030c1b06020c030706020c06011203090e0405032a0c0415030807021c0b07021603030c0305160c06020109030e 73
    0xb6052161264a07103100800a00c911040c410b0b600c0115241d104000c2c2500c1d0104000c0136003070034645d00007515a0103082203507005600700f1580c034608420490980b00303801015128240400302552003001c0c458800e0400c0c03414580e40f03820014a484051210b40c11a04002048020f00b6042c07030368452004940c1d0b001e00d0704240c40c100d05a1341c0a03811000c0f0484c01020034021400d00001441c240d40a4892045003c43c80d010204104007008070365000b03481c12402e100309803500e9030b8a9403200001c1e5450382001500240310030104110f0f0480c44e2400e0790f00180200b007500e2502d40d13580d55040303420b001501c005060742c5c4080700f500c02160050180b164010812602031094424608500f06504a00d001c040c2c402e42d0006030100865844000e030740c0590302c00c0b40c15100140281c0c1082c41e80c100c0215041405801414840c15418040310342d1601aa5403540700d9000d040900d0328100c5070350b00054040762100e4440689400031500c100c02d48001041941d002003034003102441c0c001c011814101c1d20a000d1 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 149221969 1250 149220719 149220749
    0x1e0a0308011202040905030409061403060903030c0d0f05070503040201020d0e010e040e03040305250801020403030c1e020a150e0909150c070602030c03040b010b0306090a1e15050a 79
    0x1940c0404100d044904103100031a01d01d4070b600004008140d00b80c4010003500c00000c00103012400c5821400442310310646805441d9001c00900d40c40f10811555502039420800010301103c070904060000304540380c200140ca03446200b2900304542090b20784102040c00441003004640e410401c00c0c5110b4024500850018400d50001c1c060fa0140348803288110f840d0b10303420040e894100240c80042d508902103603c0c0304000c240350b00744035004049003078403c1e90f104404500f8031030500854040325459030b41c050442c001a103030100700500205411201a00e05100440907950b91248000501584030030800302010300c20029010300454180c0034001c03403104007080300110000c1031080b0200d480140071581540d859074203080e035210741200100308900c04420722100d0300300380001d0361096105050f4400aa6216014244140421112154051003600000d1019942500940c120911858194207403c0e5460050000d64940c80b41346520b001d1401d50420441c03400500460050401c40080505 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 149223219 1250 149221969 149221973
    0xb0301090302060720100501151107030201030b0f04051611010c0c082104030504030b0f130f020a081005040204052503020c0a33180f02150c1e0a 64
    0x298038000380180140540000408080d840b5079802da41752030444001c0e00c80c40c22120302c035040141001c0c040d000000340c00b8001c428502d80204507001941c500e40000302800340c656801180540040054a80c0040702200c1254035901c46005190181d00009054032024030b20b0310000707011300418407486107907078140395000507656000000d000200750080c29481d41c42502d070400e4550301c0007031008009101d101600f080145076105020340306892003040e48040f951a0701010104a80d01a5103402805050480210002c0c4112160405c00c80c400340807110b405079203800541c01c100050000342d062070b032910104011850a882074542c001e9103200d40b402d07008440c01c0016908034111140805050780014420305051040000900c5c042c0d100c12410070400460a18031b940001140682a14050041481581c00201d01603400180d1440c110285d4400d519110b1356105c501920050781c000d103d0101804034031030100d00401e20028510010411071038004c52002c1d00c403d28849240103600003450002c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 149224469 1250 149223219 149223223
    0x117040b0a0b030c1c0c170f0f010506010504060f0c020603150a12051c030603020901170f01061a090f04060b0c15130b04050319030606021212010905180109150b0301090302 76
    0x110340c0c11165840d20746100545070001940c0d41d40e810146050041c807242d41f9a55030000303080c1403108103070360079a000d449100036180d003a10001d80314130340850402e0105100e603034481e600549040b0158034081040c01032036000305442d58811345800c0c007115403204119440b803c24191a500809005c60b03100825081c6498076529004030141051003070610060301c04105111740c000c7e1028680080621641c0d503503552110b0000f003441900309845004809480c0341d285010b1145004690400039a0300c5103030b40d5101212074941c04500b415900205505081c080781c7c80303a10840c4050301c1c2807080da42e0f640000e0384407a40703040e0b12240c0c0002d220b03680d8810480e50f007450b0703416444086d52100b000401c940721351900a096008400e03082c06480c3d00c2e21030100100e41c0c1504036004817102e5400750703003d11a034420b8128031031088060005552240500400040c007940c0e000680c412a5804030385464450858202c1c25070f2102c9505503591035200c0c1155113003681600c90403c400e14101c008208544a980d0003079 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 149225719 1250 149224469 149224489
    0x10f050910030b1303031a0306060402030c0c12070203160b0405041806140f010b1e090f0a1203080106030204030506040f03051309090b0105060301060813020117040b0a0b030c 77
    0x980140c840c00042103401c48850112005107a0000c0c0c100558a0071040da60070040c11000e003a8006420700002e07500f6805240c801212400000e400707000a07aa448003030002130f500203821904404410000174015150510894403540900010581c1c1c54000380101450041d43c1d8200c040040403500c41004031710301c56002c0b074040350000d440102d44011402c658440344801000043c01080c1444a5240482100c00030b0600c140210b0070394154990303d811150301c403800b540a0848190380d0100070768a80b21002d401400c0001002408100e107494400089044e640b030507800226841d00d01001c070010160070007030740ea0142480b0319007103050070720f19102c0b5503583e14043c0005c3c0c130030313400850f02c03005261094045501d5680a84140310095039601221402004c102800751b9030b80d030071040086007034508641102e040b40c2c210b5031402115218002e620804100e010405c0303042c045c1e6414006611112041c1c01482035000c0d20078050645010381c621425503040d00300c1144aa0005c2101c0303521507440d45060 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 149226969 1250 149225719 149225729
    0x170108150415060504020a120509120a0c05070f0308040e06010305130b04060b0a120c08010c0915050c0a060b19050a090b060c010204090203011a130302090406150b0406031103010f 79
    0x42d07a001c0240c0c001c81801030a0540107240c1190000071541c5a060700140750180703200e06002d04011580d41e4078078194440c41000391b0008401b80c10000100d100d44142e810841d401e0280c3c00b176410351603503802c5c134920070291503000b10741d42e43c3c0c0031504010000d10300c8280d070307400a030a080603c03403480c15801b41088100d00301c0340140001205d0002c9001e02680e90301400140c034000c1c0255071b8050b01c41f48404406030305008110b0724401c3e8540042a01e9406024030354000220f03849440700942481c1403d0b0324402c040d10400c1c100201440640800c0340d040201d0701b030070b07402148009280c440b500140440c1e070078034070b0010b0140c2c5450407040201d6102e18513141c00312198a600045e400340c01100140c0d461140e01c0c20251a0340c0081404511102c281c0c0c01503040390000c0016240030829820201a64000c200c901038503104464000c10160410700c041d1580300c3d109034000140b000c5a81044c00b48400303242c0081180c1c0c0c00107e014040c03d40c0612a00d91103e8080e10024219072401e400007042d03044501070317 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 149228219 1250 149226969 149226983
    0x90b0a0506360c180f0a121a0c090907081009050601031d01050f130c0612020705060a06030302070801062106020c06010b0d05010e0402010804020111030c0a031701081504 75
    0x8070442d8208489003158001030b410760380b41c5030404024030250f94005030312490000320741c0c442014a0f4a0a548650014080030b0714145000780313800c9907030050300e0200c01c0641b00350030340501c001c802102c8502c0d440c0c840d403c840402515110341100303012103d2001020701091100e0101403001801c041c580910072075004240108a965414004902501c06000059015103045100200300703c010740119200c0e4200e410a04042d6840c1c04d410244882c0701000981001f035a07620a104861081d0480c04440309240009841d110131369455174030b4448d04a56040c8410f6803220b0600c10198140025002400703840001d124860410300c19040d548800d0030303510609203c2d01c840700100a05c40c2c069a04801300364007510b03180e603035480715400036512245c4d2a1075102d141100214001440569590140d5010b0f9a4001940e41d0780d40190740f01e84030b07001d05209a110601c0340c1d65400c8000c110f0a44010b01c6130780d5480c00765403181d11840315a032068110301031640114504e03814451120201a52060300528 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 149229469 1250 149228219 149228269
    0x10203030a05220b310f0c030c03080c01050c0307171302040603030908070f0315020714010e0309010206060f090408070303272109090f0609020d090b0a0506 69
    0x4000340710364040c0849401030f4000c1e03c15040c05100740342c1e60f10528200c91a88540301d0070304c5265840c407144814229494550244000c04100c01002a090b07003441641e84000180e22a01c4421148140754422240c04200145904548100303000729504031412464060850400300e2010f01130b5034014007403035103040904000451060b600b1070341d00030302500035004000e4142c803410020260345035402002034a103c1d90000040214096401d00308480c2c210151010b42100324882d08041c1d40f100c40281c5100442010004032108284502c020618607400215070b5052000006420320780e008042c54071070903020342101e07802c1e206c8803500c82d0312a82c0500f40b04c4e90bd81451030194010400301c1c00c18a84a81895004540180e5405003402401d0103043da0240c145071036800b500c8a480711080d13420005140000400800e00283c0240003403840780800890f41c0b5844500250032a00a0030b03000c0c001c41d071159040c0081c40526408150003046100e414043c900c2c215000c00d280101d41400b140060031088 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 149230719 1250 149229469 149229481
    0x10e04020913090b01050102070f06080705090d022101150f0b03090f010c02010914010903140c0703020d0b1b04081c091d04050f010e070306090606080a1a07030506010203030a05 78
    0x641d030424140e110b00c1002146140c1c2401841c0300024003641d40540b00301100400d010350b40d80045c0d0100c42d0b0995820420b07a039400021201d075048008400d80040000903c840140e0f14070303200c244003a2601c41c40c2907801c03020705011401c2d200d40034558494070f03003110310502090301e24039100e8007a035074200c1c2a140c0d20346400081a2508a42a01c42000781d480d280115100703903419008501c0c86030003240f594035030002d0908098200ea6100300001c01142ca01140c1c0c86064590101610009003854181d51009a072a0040380f64410810001c0b41d40000386420004940c5400400440174104e031007034030b4102820300a40b00d81d1141200f401071440c104500001e9202c610a80c0200b0191840a4004840e03000c003180d103040c0681c0c2900d00300d40ea0f005503080c0e01a101c1e014450701c480c0241007001400d4140c59515200010007138003009951311920360b10003040c040b00400004609911560100000c0010b40152501141025241d2420541008180328945e0380c00819242c100c6c8038486c00144585940c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 149231969 1250 149230719 149230729
    0x5030409020c030403022e0f0c030f1211040509010614030103080306040b06040801141f061b0804080615030604030801031e121205010f03020a060507050312180c030a02010e040209 79
    0x7548001c0d070140c09040200404060218a120100744092154814070180317201032341c140002c4840e85002461140c13242c070120341700e03241b080d1000c082402c00e004070210380c2c50010150766100e1000485601c0004080010b41801048280140baa528103103810400c0d07040485d20030300c410704c4064070344c100110108401d80d66540c04106010b80040c90543e44590303520041c0d000c2c3c42d0007055110002d4140740081c403c182e0110104c1e030300d001100d000d80490741c01c0c11021783d0001044040020200002d04414000a00d904001e0007d400300400405141c80c040302180c0e0700200f0a16050b01a4110303900f400b0000c0c0d00311402606480d484070b10300520b2203e50301d42441c01131107440050070b4020b2440c506a0095003180070080c9a50114006000c135a8032004450780c4a0a544002500642400000c000083c4500090071441e84914192031522004900d140d031030760b10584c0c1b6030484401c1c0d50840e41590034104140c2034206800da024048203402500003901c800040850b040c00b4507000544402c20b580c1d5 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 149233219 1250 149231969 149231977
    0x3090315060506070c090c09030b1801020906030a0605120f1b0315040303020a17091903090812091e0f04020a03020408060408030115020318061b0f0a03090501050705030409020c03 79
    0x3c0c080039142e03400f13410b0003000c2411512640c1d14103464111282c1c0014461903a460a494103d440c44403140ca802480d20f00c040c845000b000060356080c40710754283da542070015030040c0c03411580494035508002c00c00c26000348400400000354040001011207980105140100e62041c4610492812805011a0a00c40c400e6140056164020100801c041d0507078068a203030b2100740d0380c155658007511018815240241c0300601d01d0744c03010080307204050f041125000302500c07134984042c82030380d1211124901010581c201390250008191003445091288001c11042d542050205030145480042200c84444981a5025503000a070703250600f8040d40440d00100394090480d0954078050a010040383c20038025405511182004103010302c5c80001034880081d01c2081d540120386403542004001d07031140504000c0700c081c100c03010309054824031019038242440b60150200c6201450700030310b0b44900c0e4015030706000040c003042c0c020030302c000107a5003514040d18005aa600306a05028a1801 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 149234469 1250 149233219 149233229
    0x5040806040501060806070903020a0306020a050c0316110423062710060908060a020903071206051e0c070f110d1401060f0e04081309020f04050306130309031506 71
    0x890031051008201c01580440115600902a1035040c0c8030082d046403520032511020f548032146400a0000c03030901da0080c022500c1505001c0d01d0007150743c42840c00e641140c0802c2c1c03000720903580341005101d5590022440c15004450410039006038184a10048901414801c84845400e0002e909a2220501101090201422906c041407891012154418200e443c280500740d10300c0e00003045400f4200c40410313141c07400c020300b045503182d4424200039086034880c0d40d0b1610a40d8000520841480d0010300014004d210114003440c10014201e0040c0140c4079810b943c040305c0c010040040a4030302900c0d5550317404500200d0450721401e04480440b8800c0e192940001041c1c076540801a03030610441c00f0b0307070a4100911902d0360340c007007110405005108003803003035010700e001a0008007144000e10301d03407007403491b01601c0e40d03207c507090400c98004030610b800108000800b40b1240c03900300440c0d580400300d03840550b8803117855a00181201c0c03103484020001d0282071642c1041d0f8000c3d40102020340 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 149235719 1250 149234469 149234473
    0x40b070503270d1701030b070c080904020f0d1d0715050d1a011205090604020103020a11060408090f220c020a05030307030f050612120a090f0308030f06191401050408 73
    0x1030b44002010740381c078038002c03246000c01c038158101410090a480d1060407a030b04010040300301d6844042c00d0340c0248603440c1c00c64584804024034801d9a4540c0301820307211010060030382d185e514045120085401e0131008409010301440056000e643c00901002a0384020543e402000303454401518103000759200000294100020240b20703181007202e41e0b0403158240d031600041c0988503002004c5030300c25200f44405822007800940954020380003060b13801e130b091406021290710000010f05040e02079a00b150340d100c0c0011b00014510345221002c000540c11181c80700011100c28100b40200391f143d00904a080c0c407038003900f9800c1c0c0240301c0740240b07540207000c5d6556490a148004c00800340010702000a51904007c01c0850400c000e100704070160150043c17a480203440494900c070740154200c0c0c010058118400300d0071888100150b03008602c910035158480c1007800192022060007030105006042c641141000e41c103100f10400112803241700e600801c00240001240c461042e074028072454 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 149236969 1250 149235719 149235781
    0x6020102070f060c050c011112060a1508040f080c0609010605060c070306090c170c012d082503090c06030903050d0b150c0d1d01090605030907120503030403120203040b070503 77
    0x429032100003483c0c20401250027030a0759070b840c402c018204000380182c4000b20009010302881c41d0146038103d801030b0161008220514442d034610b01c199015500c0340030035800c02014403d8000090107100c010b4001194100c2c20034140720030080e524000b41c4805042c2700c1c2c5038481031044c413511003860005084010400040c2c80000c0f2260703682c495a1003030060000c0e6050b40d4101d41c6445807200502429a151620100c0ca1000d084c00c03103080c00b010300245500b52101e05442001950080100d045441c070b81c4000c0340e50300090030100c403060141d030701000178141010302402c0000d90000c00c41d0042081d0f840d0000d03c0307851000220310b4510031071098941c07407a030016114190f59400140c1d43d14040581d620000c0d400701014143d8500e241301e5139110b0208001c1d4205028035400740c40550750001d2044101c4030101c1c2d64100841d0042c0d80c07004186d4041d00000180320606a01110403003100104980a500c0c60402e41e9030901c200d070000380520104040031001c20540c0014030070180d00d102a000d42c0e1965 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 149238219 1250 149236969 149236991
    0x1c0b12070f06080a020f0f0d060f0602210a02060601050a021612020f0a0b0d0c020109080d24030f02060f07140705030d0806091803070602040609090606020102070f060c050c01 77
    0x301401d0380502030100700000001340000380c0d28021124118140c2c0d80044c20144250050303e1141c004050b070241894442c4400300c0c040020f2503030000244031a500800d407581140011120f0103121b0b190b02c2c0c0300c0c3c400c10824055800d8002802c0e9402c46820f01e0016a0364034000c0c3e0803802c02c403e210004007480800344002a442000038203955080d03000f180c1c1d4000d02e0140781c04000c088a018403801300f18003428000221a90b220354004a8500329600006c1a0006075a4620340345506c4500c0c0203901e280e40d00100b1403c1d00a01030381c1082d50b105809246403060464451a418505035003001b03104900020310350740c52074114825510400e038001146a5000c46420042d0b45031042801030034000e1194500c8080c1252180c0045405140082d10905840d25144003064060790040300c1015640300070400380000841c2c41c4014002481039070354204400381000400ba040e9441540000c003160700610030b2401080945203221300b030541c04800080c0f1100201d00c00d540e00d0155540c051065440d003103420320 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 149239469 1250 149238219 149238239
    0x2202040f05041a031f020f0408030a0e0d0f060c17250207120b060406180b0a050d0203060f0603010b0a0f0f0603060f0e04080f07060b03070b1c0b1207 66
    0xaa500c112824000322220544041e0f035030464902503540744d486030541101e80d4404a5000c052140448009441c004071451110b0141d800f075440940203901c00961807448a03480200380901070345c12911441c070843c043e1035031469a10700c0000500500d42d5191101016070058420203442045544001540c0c42c2c46840c440c030714510144896400e00783c205084012a101041d0740c0107903128500304803010542c50b100c4038200d28004102c0c40d001035a4180101c0c0f4030704640d40c20f046071604641d0200d01700b42550140850386000d42c0c07085008a0380c003947d407001660b020a40d603521455901e502c01c1242e407040002400341c21078070100754001c08035503804614898164201700c250750f400c000c0984013035a15141201107034094400ca13a07404075240d0043c41040c021440007034200e4002d4001a0400036001950380103540310030b4040b50200d03524082c170200d03800c050003040000d289600c607850030240d01d40c0010704d6544202c940100300b1aa180b079280302c943d89015000d080e5101a4027103903103c54550b07414003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 149240719 1250 149239469 149239499
    0x509030a0c0b1b0708070b1309060e220201080c09010309020616170a0203040b0c01020405090f0f09160512100e01020c100207020105090d081c0b18060a05220204 71
    0xf0a00c01241c41009202c4001550b0011168440020300b01c480c17030541501440d4110180740f104c680060000014411050300488014148400b1414094181580e0b03074000c0d4080d0b01001d8041d42035120240f00940e80005403240d1182580d850981e96620540c0101d0084c030344044002d6000c68041103030043d408221540d1071020b481812202c10040e8101c461101902680006400503801048144240c041c401d024054000101002508150b290400607041c2030044400f40c4003000703c5d00411245c0c8a030f17101d0302d0f03070000c90000c0a071103003441c60b00000180c0c6080b07009240c008c040c0200d00c0c1810303100420811003111816101005080000600e1a000c1c2d0f01002d0703901c3d06071113504045003440070948219190154161612480c005003c0d0521a03140c070402d000341c8401d04148629401140703000c810a002d0f0948840c00500c49011000f00304444400303846240c4950402020005d960729485981c20503036504551148038200004c0211901003241d82d4100c0c03d03d400400c0024a22010380001 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 149241969 1250 149240719 149240737
    0x3090a0e0702010606080402030d11030d02040303030c091512050603240720150601050f1308060109020702060904090f020607030f121427160e0f0106050403030509030a0c0b 76
    0x4d2104070340e15903049488502c16903020303616400811003103151074010a000c0ea801c000f004141c80c14205005941c8040743c1140d8015030100b5203402203000a140c1c880f96031009007180038012490b494255500078000c940302200c051040e507468000c152a40c0c4d040066130545050155294112003103160f40104c005426650100460000120a046200320074443c081c050a020018500250213600d6008641809040395040c080100f0068050100410007002080c06503e0f103041000e10304074000e440c0200503030003442c0c2c191040c0305c0800143d4540c0100ca82080341200e02017a803c0d043e04007900400000301c4003d50100c000500d1070201900901303058103020807074856840c10480461400e080c0e0b00c1800c030380b00b84400e8600c00120b0128000600800c805401e606c4507880c41031110f00c44d17182c014842880c0354044408881080711341a994400c651001a00544156552400d00c001d09540641e0000030184180401c2c80007103601c08105844030300740c010701c800d003032143e64044004c896400080a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 149243219 1250 149241969 149241971
    0x11120115090b03010209030d0807030914060405060106051903021321060b181305070b1c0501050a03030504030201140c010c030509010c11070501140403082808060a030305070503090a0e070201 84
    0x100109074079041c8291a03030040047e0113040b440010480482e181c600c028001418550b4964100e00400c030046448500e0b6032203c80182500c1c00d0504120b450403505074021000c001040142111a004540488040d04a036040160301c41c0002c910618030070344180c00c214001903103e001c1c0d00105070440b05030005140221010060070100380e00b0300c884081c0754242a81d074122180080b4250b5208144039882c098043d40aa5100903103070036007020590b002c40040d00401e130810402d00c230f03461401c1c4a0759004042c00c0f201c000e070039451964060071a001d1888003070f0601080c81070a94010100600b11000e054803a4002c12054000080c0500180390a868680700c9620700b500e0101442c2c05070301085022140b00000f00540e502d02030046500c3e04107131810440302641888000006034903039028210b640764007003100228201092341c020a0446807160007041142c03010510000d62070f0704107100d068a0b014680155100350700d040962443c442c0310ba10581040d404000020004803d031041400740b850360b80 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 149244469 1250 149243219 149243231
    0x9020117150607060f05090c040c1b03050a1103070b0708060f090610020a02090a240b1812060403021e0307050303060607020d051c03050c03070c1112011509 69
    0xd0090008004840314402107011807180402850007101038051144101000b00780c0c2510040d00700e040d01d8040c0c07814483c55004a4664240e0320b41400348880b42041c51400013002c8000d95603007104035000ca03c0180034000e00003030b0120740b01c0c807031908110303032044010440c0d0b0f640300b1615007039454200440c0c01400140211001c80d6451614031002285400c00524026480d280d00007000101e001c220140c0301507218000000c00146c482e000c00394422008078400284049880da400402803c00c1c0650000c2001500c1c0103004414090094402000003c0d180c401c034070790040045080701511500c05119445100200000c06500050b481c401b07054010100110400e1401040d81d43d01070a0340044c41e0750801e00001d115403e00c24050011140010f15111a4420300d865190a20140f00d05010810b0030b40c018894140340c250090b1904807407146c9010b45903103040ca03002000c1c004d1b0312034010082c00000c0744881299170b4041841130400d21030360080010701902c8148020700788081c400c01901d641004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 149245719 1250 149244469 149244497
    0x5040f0b04060c0b0a06170a200a0905040c0f03080c010615120b0406050a0b0a0e03061e19020d06140303040b03010303082508040b1015030e190501090201 68
    0x1410703034007240d0b05a20f840703001d100c01c1d42d100c000c25036000300302d04144c6076034520002d50b07040240d90306403032905060050000401c0320b04003014516410203c0801d18200c0c80c03410070503038440345950303412074988280000380c54949152201812040d07610040003e40000c1001c0144841c0100800e54480c040c8000c2052a0340c80703c8071221040340a00e6440804c0405120854018a5070084144044001c0000071840c0d01c2d00c00040c0c411a0541010400410202c3ea900b4a6500700c00c40c8401090110014039191800c0c07540c140e5480c6408103d05403419011000c03d0072000310904028102607401800d44d2106181b005880040c6a9841200d4a0301804d2103281e103242004021102601c0340d9601c014074580c01d644003511038070000707001c0121844201d46040000c80091644081c0000c030342e560818541400e0034414004200035010191080d0f805404005046d251440954030074518140030680488800c165070900b0400500c03c4012011219032204110065104401c07591003600d0341c1048101107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 149246969 1250 149245719 149245739
    0x70e091503100f0f0c031b03060305031608090d050606130515090403051303050303040212010b010207141305160201050903030118180501021201030506070c0209040f0501180305040f 80
    0x90104290503410010402c0982c858581140704121180303000440c8022494851030200c41e400c084020000b507460424445040e03003c00500780a560070319051115a0460315400e40328400c201c540621013495059140402c48140142c40b85110001c01c0010a1600c0c1d0400d10b403101412103503184101040c4c80203203900300f01442401c0c01406c002050100c90b40c9601d00344510740c0d2000c0d2040e41030010512801d40442008110b0901540c03094002c0d603200e0810744140443e5140400324121382c0c0c0d040c0b1a01d00c071640d900248210888a0351084e611919030900c010a001907000c800d448a25410001003000c6403240300c840761400c104035070080003e65a000b4600e03441c0e020a005540341800c01c180026000c00b080d0f04041079045444d030303d80e40a80c0e80c1d0b940d10b500720780c0020f010300003141340c02c0c00400031701c00d00303200c415070200c950305100910440340e0b070002e004950020402803004913040b5403001406400d43c0300001900039035069440f0300340181000b43c0725820900c40c07960082d07203a0702c011607103c1007 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 149248219 1250 149246969 149247001
    0x10602030f0405100905150405090601030b0906010309060615030506130207120f03060f08060402030d030b0303160c0504090f061b0f08090c090a0b01030510050a05130603050303070e09 81
    0x190041042c2020f04007401c1182543d5160710b9001009034a1002269a80e200c0c0c094482485080c2001d590390fa14040074400c83c01c8006103800d060600d0100c030028143c80354210b00d41e000d1024640010446468500800140a56002820740740c1d12041c01c00710407605940700900a000c119400d01e0001c21070105801a44240e2134020840c01d1000314070309045000320002105034559041c08219a9251300030960a0607840e80081c420b41e01150902c0250f04040c403441a01c4007542c9014400b0040746401300380d0700c3c1b00311900351101280c0c1c003810701c0c10f0007540300b206000307060001d000f407040c4001824042c0502c07900709c2041d2135903464010010b14079401200c0c1000c402995882e401e000d0302256070141c3e100340303000f0071048107070041c08035681781565150030700d6100e81035a40c400207800390320000050031100018011170403008a04c109010320381d40c04e10150102e82049a104108020340e2805002510269100401c944008030500640581000b10140c080c01c095030031440743d9942c8501070314012a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 149249469 1250 149248219 149248237
    0x207110909030a050c12190f0207260102160c06080f09101a0301090c0602071a1602031203010603020301141c230a0602030109060b0304150b0a171501060203 69
    0x8403c106004910380104081e005580f41c01050b1130003031101880340b0f605580702e036020341009034003010020b49454100100e80312090080c402070802e5400c116a52200002c14904960071036401041c58004500c01d4045940e041010001640054041e140c501c86c80841e80c05040c1c0030450b81340000700203032442d174905c51040005200a1680c800307400d010f88020902141c401c40d03881c01d0144200c100b41c4007400307400152403244000d1a03c0c1841d00d00000e0a100113a000701c400000110360220320003c948040e03800c6810345101ea01940580d03880000d2414100d401000806a404000051402c2c5c00d5400707141203c0307280100254001c89401007100c404101c4190041c3c500501404401080f08526544544051060000c0b0401548090b041c81c0940c4058211125030b0000014031210000307001e000e00030114800e0341c030b0460500b99540170742d41c44060020b200b102d5136000e00215a96174461604014040005034040079000b03203c800740c495502140c2500042c210342c0c000509944000122000c000b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 149250719 1250 149249469 149249473
    0xc071a0f03150405040b0403020105070201090f1211061009060e06130e0c04091103010f090b040f0c0b0304080d05010501050301050a05060904110a020a050c15030a050a110a02010207110909 83
    0x400000c0608481e800c0581020000005502d0760802501c0342e00c2400d010703034001d41c4003080c0b610313103440c0007070075500010700c03840031a410040c80034006000421000b1a40340d00100d001949c441a110442c0c404d446030840350054800ca0303040c8040d1b500005e100400351405240c041c00001e84070910030ba100c6400340c035030641005024036965200c00e110780c800e4929030824000da880d1205005c0024040d02c04080050760314085540603100d65144c24412103c41c0102090309000301d41c2ca5480705641054020300c003a01c40030b5013002d03c41c2084424084040541840f001190722820b0078240300c021500500b00c0140c0083c40c040001c5a00c0d0700802c1a60b040301c20091004980c03900306028000141c110815941d01301d529450307400ca40c03400600c09018003101c1a40206050705240c10841d24003180000c03072600814070911800203940142040f6a07000742c040328041801c1e1120345411005000103481d05d00c40d60800304035500e003d82d06400414116000c1c501101808180344101f0445450941d102100340d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 149251969 1250 149250719 149250727
    0x1f050607120c030c05070b2116110a0506160215010e0601140d0501240e090a180f0302010c0906090b07020409051207060207290708060a03050102040801020c071a 71
    0x201c0e10540354801c6041c828a4040101c403015a201481c040710782d0001e40c0c0c940b5020402a40c1002801d2003c0046c904240000d1070714103020a482d81811508000c09082210030215169030582c00c004403d5000c0c0d101c0c0c100d50322460000c1d0b4010482e1500b00c0201d006006040100101144401001e810b0320003d801e10100c1c0d40340c40c401034031600300b4038100c10300d100d1302840824034001141c402c4034003c00a11b03a52408001e204640b0054840b4501610000d1024804d40404282c9900c107001d039120f80a601c1c002030303800982c01e080038a55280840204010b1411106d50b04059064007c1000d600003500da80c40728585411040e90300854034010100c69001c03e0241d000503103420b401c41c22849000e401510943c2c001064a00c105507c6a10f05440c280e130006070110030059140800002609000d680c160300200d031141501c10b02c2006000e942c100b11800700454030b60369076012090010346c0c3c42002150f5030360307032003001da4080d400107940403800d8000c06c0000102412900446246400c1d41d030b40b01071030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 149253219 1250 149251969 149252003
    0x206010e07090b0c010e010e16030609060207020607030f03050703060501050d05100b270d0f020409050f0a0b0f09060c0a140f1b0106140f090901020f031f050607 71
    0x4155001010714003082030035840010203101c0500100384200d0150008030710f6003403900b65a400d4420f00c07007111500e81c0c000c0103000035628411450f4019240d00010201d180c160310701b44030002c1d005024010b5401000021170008060b0401e18120616007161014825a0b41700c250540480300c2501c620350100d0409c20202110600c16031002e9440745280555a08003529449030004980100032411201c190b9017501c003070ba05413448208030b1004400c882c60071700c10720f80d6951500d001141c400024002d903160840d01042040c00e000c01321041a681c000c907a60801c8908100c0b00100050b5103c051003520322010130740884000c20f81d1403240d1102c0000310300e0005185801c603282e9012000f42800c222040c06803040315109103000308994134660300d00c03085181169140d5821070703000b40e00c41c6184601d4090744014a840e00c5003034840400c01124070003072031351714401030b03902901c42d400410341541d800000708600706805200e2004070320b5009400a0203a43c4610500416110304c50028100c2820342d680061 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 149254469 1250 149253219 149253239
    0xf020f0a080603010e010903120609020f091e1c0215030103020603040b040303060302100c03020c030c0f0409150603080c0d1d0906010e0d0b160302160f1703070906030f0203040201020601 82
    0x280102d0060000203010b04000092030868010880c102c000408170304600d48c141c80107001e10400340c540818210310706413039070148000ea13128164441e03004030a0000b0807846000380380421000f81c8800b40486d84642200f201c26000c440b600c0b44121b02c80d40030949001c07504010081070768140c0b680905440d2541e01c0719165a4a06c00d4003d1040342010703101c410210040c1c8400c042007124000c01c0d11801c03014800740c5000380c102240d64048034040d501200e10724515a43d04005020310ba072003030b107000821290b030b41031003680c000e10400e41c051600d0a0038800410801003400619052202c01d054030f1207102240c1c0d04440307032400020000740c3c40000a490380303000d2400f00c00302d903000113050400980c865404000300b105c4408a19003901d0001042040214000041300500790603041441d04614111101124014110380c5000140c1180b901240035803c00210b5002400441e019045150b128540060010710500b5503020b81d0f80045d01b0000360031103a240500a40e4001e6a0503006407000c0d80c00c0000c040c0f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 149255719 1250 149254469 149254471
    0x1503020903030c010c03050708060d0308040602220b04030302070501050301030308040b0c12130201030b0105040509240a0806010f05040216060b130f060e06011119050c04110d0f020f0a08 82
    0xd03414082000f80103001d1000748100280c44600c1e0320085128a401ca00c0900302110040609004441d45180000001c2c0d04c40701c40b6601541c40240182c440c0e040c0c1820410750f00d080d42104100c000c415001040301031601c0c0103002200d11a07400c880d04c0030f4076080110f406000a2000074045240e01c0d001c503000605003003245070710070054414581424242200c5640b010402c0e500303000d0301041d0380844015542c1c1801740c141e44940c01c0c2080351030a4a4040071407101280200100c680c004004c83c4180041944180d41404070401000400e50316160305100d61168400c0c8900d0342e4030110307118000b980d41028000e0799000d40e890028460301c0d034001c1e2900c2c006421480b1100b948a1040004240025664860303101c0c0724000c4000081c01ca03080820120b4035810140003030741840b4582600d04084000060300d40e1110124020740c1c01c0d005c40c10301d0441d2800180844050b8051f06050030551900d00c10340140101c40782c842c0080c40804a414100c100b244202414201c0d45039007000300c81c80303060040b4105 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 149256969 1250 149255719 149255737
    0x60e160212030f0907050f100305153129040f061203020105010e0f1611030a0e1e0102072d0f061103040f060818150a0606020304150302 60
    0x925041c040041c04600e1580c802c03901e408080700c0e040e05011041c182041080040e10081da104280b0f8117185c4000f50850481da40c40d14209621880007031540c07070018001c0001d4082c050100c1d185030255107200c0240640ca80842201c4020381c9084181d400914043c0d0620030440d00301040401025817012a204140880d0f40768104e0344821109100b580f0912900006210703400001d9000d815a2070700034251134041c0e011071400f070303600810302038003440844c55542c11409000015040f801c00c0038094403069655203002031640000301e651610341e50440130054030494225110501c5200320041c00c0d464142c00620a401a0300c040c3c81444009040b81d20300c520495182d50301c8030011070f43e4141e0700746503080e500710f005481c507124001c2044680040070040101e41b15400b440c1002e0402040d016615103a00c240c40c200a1408085043c000c92a103040503401c51390030030346030040c400c0c4044010b4042d09642d80e01d080d520700503002403014400b2007510141c5030541140f0000c45103040303040700a50449900 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 149258219 1250 149256969 149256973
    0x20a05040c031803030e12090a14010c05060a060e130506070e04090c1401021e100c0c0203062e0803040e09070b030106090e0a06081005041401060b0409050a060e1602 73
    0x107a5820078008581043c560b52007540c000c00d22140d10f500b2a82482000407c4252070302c0c00340603850701544d07a0b440708819543c1c050154901380490000490b02040c01400181c42401104144101c0042c80c2d003015003079800b8802c0d02c1c0300d1502c80c9003d0554611382c0400103400c1da08900d001c50140f511400c4007503078191000304046003c1c6a0351f1160140400c850b400049080c03000034034a41d80f960103000380c1955603480507400401d5021140010b4644034141301d203801c0c1750350b540344003210580650f958040f201c0d005421110245407061040d8512100041c41c0d2520740c2581000e50401d40741d02d4015410b6a00c8000510f0815191032030035150036001600090b11401550000705010b480403024500808061b65400b82c0385e4a881290030025102400c880f03189800c01c1c00a00103c080010604014451684002915511800c0802a03440c11042c00340f00c0d075082c09000245c19148101a00654084d000100000e03180d0410300b80031201948645007450000400040103a145010324003510001401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 149259469 1250 149258219 149258231
    0x9021504060507050f0c011704030201020d050f0712020a05040501080c0c121803190b060f030f0304030b09010c020c060304260301060f030608030f1c0e0f1603020a05040c03 76
    0x58160599005074000000045022401d034007486004c2090318a0076082d00041c040c0c0d4462200000c100081e423681c02201c40003a034001ca805c15100754115501141c140004114608003008200b136144001d0768102c00040da260085007490b0264402ca03808142c054443d14606450301006482116000300820300d2a5001e001580c1075140c1404500300c5440308401c0c0e5580c035000606071040c500701010300180240d005021828a002a0840500a480d0080c018009940d25000010754600c2c4140c3d08540500445074420149403002000d04145c034440c5001540507554202d1f003508a85641d005040107074080d801070345540c1002402142c00c240a20404544001d240700d010109044541c0c00c0500d1050000040140381c1d800540300070180303000d19080c0704540ca0407034295034070f009e91084101c602030700007032020402c414030158082242c042c1d2400d000c0c080c4500591030701e580141e42580001e001d8041d201005086013843c00301a04d0780200601d01c040c0c1014280401850001400c00615079252 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 149260719 1250 149259469 149259499
    0x51c03050706090b01171c030b03100f050114010513030210120504050606180f0105011409030a06090201090f06120203070512151003021c0b0d0f0b10060e0d060902 72
    0x80241d0f002e0368042c0c13042d2081545810308590228020011102040e000414200349111108205185a0060346008a0940c03000400207041c040b0036a02031102a00d441d02030101c0e0003030b0350001030485130a615200c01181131040191064801c90380750311010301042100b40018a07103140501c021580d540391044c02180120b00d40c02c200c450558094070f043d40000c0420000d03145c9800f0084d111a81d40302032a2160400702e08410581030103029003418440e0100031078003c042002d040d200c0d165001012140300200a061131002004e900100303a001501c1403201088441441514004680780b580d2010007042c1e4200c9110025003015100c001042401c10000842c99041c1505d103004031041110001141500000c020160352540620000d242c01840b111910340750791200d8059034015118007041c0e42108000040d2000d540200042080303c1d010002c0007803000e01891544940d550b1aa00c44d4902d445a00503202440b4006c81c00703038080c3c0c0349403000000941c2900800c0d021840a03000b800004649 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 149261969 1250 149260719 149260721
    0x40b07080c07050d0803040308092e112502040b0909030903061f0b0304060f0501080d120b1c06060b1c060f0602120a0912080c0f0601051c03050706 65
    0x20800a860080300824200041481809008000c102c00c89980740031826582e039145480c00018005010702c000c4a00091640f24140700710f0024424030746040038801000315103082070303003001820f40004918101800d45968000c0c8200e402d00742248c0b80e99804220722000980741d80e8050325049030001e8641000000540307440e41d5041c0100d02c40005142ca4410000a041c41c2603001024042c0c490421600d03500161074503c1c4400c281c0c1c0142d6807d66403690f41d420404054a00c0c04d680001c1d09140070000a205100807424452010459031303281d41c46c1007802d681500761211500440c0d0301204a105a51021490648046615100d00008201c0070340c4c4403842c1d1800e03000751200030300c021800c01c01c00c1481f0559105240180982907485a12a404c00c03078000e5840d0b00061001613014400550080e0003800740041c03000601106415080c0315580d4504000f680e08076042051441c454a0301540c410b10000c1605416618080c01000400c0910b440d1621f17241034050081e0103100040041501103545 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 149263219 1250 149261969 149261977
    0xc030102070b0103030e0405011410020f060f0708010e0f011401030f060807180513060b030304090c020307170c0a11010c02040906020405030c0303030903180a0b070501060e0606040501050d02030c040b 88
    0x5414070300b42640c513605000c3e1110fa400000350740700c0d500d001c005020780501031601002c5440d043c4c88a00e91842e0705a400d80c030301140d5505500d810b00c07984082010310012131071841d10854655455144999039000420941807042d40e443da802d03038900005110503805001c050410560500d808a03c204809100c8000c60345550480304054115510910103018507120703146240c030003140d080001e0318251040f84054011000010030710741c1c455030f541c022079078200309903400b1301403000342003048902402010350380364020b400c1103401c1000582401c4c221150b000c00e851040084070050207510307900365070f01d810300d0070324031100350510041e40c030b00702c016031518400d25031010322404005070781c0c508110406183c454641c848521030b5000300300700b2011913030100c1071b50200f9400000d504a4010703034a000500404039608401103d4101042d800244901500700d07808640426100c09840c2d100d440031f02c50b4030701c00d6010382d901142c0104504401d00e00594001d690010025000d542004c0d1514807446d40e40e80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 149264469 1250 149263219 149263223
    0xc040504151e0602010b10020606060702061b030a080f040506070f0201021b0307060e01020406090909080d1b03060603110f030916080a0302070605030609180c0306070309060621140c03010207 84
    0xba001c030702406510303024400c1441031a400c9607220b039140810703030000359a000014015401004003259010454a030901941c4001c00095402105121141d10850b0f0701e4014503043c0e0000348841002c0b80307040141010a0f406190040081d200f6a50349031002d841d030f5003924402c0403c66500700070051506059071100340550b10500003442e60350105007030940c15106403801c1d1001a07441000100803e5030048507020844a00400105051301d15041070000c90003840d07100b40141c0c0c18688030300c402a01e821056030040d00b503030f14200915506c4910071012605072001100c2754110400803080040e06160285a00859071400c032400b070f030070b821130440d0704000e11703402603085a22181d4072768101601409803801030705032031601c182945080070010f0781c4682e000e403841d0b900208011101020503400d11070030141d030902030304491250401900042c001c2601d41010390314a8640703140850000390900742405041c40c44020500e0040094807094508102d00c0c0740c907400f501c101143c412054400780003500380301d4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 149265719 1250 149264469 149264519
    0x3020607240203180f010c0e10110604080a26011a1b0609070e06030601151b140d020c28080d080f09010e071a040e0907060e090c04050415 61
    0x1841a00d0251400300b217282c1d81961130741410469001c1d10b60003c080168040c048901040ca510004402d035101c0d0f011141550709801103104110512403050000d0100c03001079600d0307408805681c1e8418840a00d441c061041c0c42c1400c100400104c0d00420340301d415525a00c00d8a49070480c0070580780b20705815124003035003542044081060005e424040e200c0103001e204000c100714a07000340025145d101c140604140c0000f200101e000440c031810045d030f11080d601072450302c0c0d00c012b07041c07131954502e01218030a01d510444000c3d51105201203000c0c00d034003401604490150b9203a040c50385060120003950002d001800700c00194922007004000fa05681549401d0705906000318066501c04008226402d1a03041c200200d000d684005035103801ca603120354803480e0f51b41819420010354451907002501141009090044000d00850450201c51054440c0c620300e000100500013541e10844649503503038428802082142819004000503c560002d10a201500d84030303100300040d20b5200450709a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 149266969 1250 149265719 149265751
    0x50d0507080f030c12030c0d020d0f0e0d0210020c120403110415030317040303020f0a030f050f010f09020313060c0c02010806060c070303050c0708070e07030507050403020607240203 80
    0x305020b00c102100040010099071a00540345021a51500384043d07030030b50b402c1c002000070420100700040d2149030315021025903680e0124840980a0312090091402c030768642191106611030014034141003000d00e0f00540b422506100c1000001e4016500341180d6014811104e041da840200042010750300c55400862600f00c40000d0000b21017a102481040c840080313018030120790004c0288240d00f4802000095035525451304401a01601d440052801c41c0403034903a882603007580000c8800522400108141c0c2d8403d440d1444200080c440c0e420812131045061101e4040c5400a582c464a80d00c00100c081c041e555441c0c086a00041601001880101940e401c5623440030308142c014400301c0342030b4289a803400340c0039240c208502c4000c0038800000348608200c00c0a000002c020328541050700c82d525910041c80c2140041110480c001a00d8070f070002e804203014006880a590f0050610790510602c2d0740d852460301249401c0c0d480804016005440c207400500041d48a45d2001e8011111 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 149268219 1250 149266969 149266979
    0x1401030b0103031407080301050603100302041503060e071a161709040b01141b0c03060109060f150516050a0b04110406050301180201080606070605011d090c0307030615050d0507 78
    0x4400d40e4845107410045042105d04c1c0444e500b1019241501c4040300c10b1662a00e071025000c04001c041d90000b500076082c8100c001c0d01500b041d940f07008807406144180000d80c07920860315102d603464000d85200306520449142610700307220180c18007c07003407200d4101120041c1c070340103020a400c00c0c02c04040c04000640004a0820b405405850442801c007211481c1da9034902d01c9003802007000d02e8604c1c0200c2142d66511800030042400d03140b4026040e140316503100e44808003c5c04150241840066181200140d0f4080c1c4070016514081240d031003904000c84034107100c2c40c0d6121120141c656119030024140425180c8c030305e55009603c074074981002c0d034004806200550350b456101500c2a4900442c0c00644c1d0300080d41035004a50920308001583d648000060071b6005804000c1e28031898100013084911410b4000500350034070007284070003541d4101500d03a65100e000c0c20140c050308020002c100280003600603402800401856601058840c404070300d0003400000c0a80782c1c0c0d4804002000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 149269469 1250 149268219 149268227
    0x302010f0e0102060415060902040e06030601050a1d190c02011d07050f091305060a09020a12020105071106041a0909010f081b1906020105060f19181401030b010303 72
    0x1541a4904000203503206560011351186401000602803060941104210301c0881d03001c0b4001e003c0141c2c3c11500d9541f214020320705031104071032150080c89444000b146916148198004507004010301480f5050840d00066034902c0c0600140000c0d1040d100105030440c0c50300882d41c109465500008003079254045850181d040c5519540203a080b698050000740c954441103284e40e0701c144e52002c0540c80b600a0880350844680001c5d003580038807030031710404610982085010328000c45030707003c2a507100c030000d1920140819000b40820b5040204000045c0c002c108008824401099a0709040e903d00a03040740c0e111820102044140c0096920501c2c40c107022240d02620400d80282c4c0c1c028101410360799604c1503825200955141100703100a25901e566040501b901c2016404541a5807468040e000c1c0005503813084c428181a2030412150420030141102c12030003200e039031541c52801c180b0401e009000c101d40c2ca0345d0b03502d03050000090360141041c24001c1d442000e44221540c51418014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 149270719 1250 149269469 149269487
    0x21306020d0306060908030a03090203071d150102060c0a0c0c050a06031514060a142502030c010c0c1203050c0102070305030106180b192304080c0301050f04110a0e0907030201 77
    0x6002e000c2e01105c2400a160004207846c840b102a0500007035100300c0d030000034509010341d440403200c0381e24007203482d082c410030030f4041c1c0c01744c084102d4003400c00d83c06400598541c941111000c000510512045040d107114134400a440c60042d8130829003107840d000800c40d2131482e900f1040200e603d80010136000c0301505004401000040305030070200d040e5000154040c81824006000c21150040581ca50144c100c00c490f680c0e1151006801074080c8403091081852215106034820b002e0700c811420f95500440074031009a5100e803000c4001421309020440c020f450a80540801c00c040c494400010024402401c805000381c4881e42c0300d624080d80200f109004403029125094445001c00c007e424a9055486d40000e58000c607000c0c4010000440e50701902070f280139080002c0130000740741125001c00500948090ba020384075510141400d15098501c199880b51540d01040001004250b00161500c10044000d05c02840955140d401c103800c0102524005d00c1e035000800d0810031582c102c8481 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 149271969 1250 149270719 149270729
    0x1d041d100e03040b1312060b0f01020105040b01090c020309030a1a061210181e021014030105300114360118110405090a0c090e01021306020d0306 64
    0x103101c8800701c03980d040e40b01e018511074441d0003d0085200c4450b200000350600152038222246646920103082150140004101c60360044010046000480d4418021144038580040c6401c0d103591a120f40d50707000340f84000da40c0c41140020302000ea40d590781404900c021600a0036012194040b04000070202100500303818490030609142024000022030b00039607650300300c5070004080522000b100001c0e0310300b042c0100000700320445030365650114a04420514002da80c3c99410360081c0030203440c070405282950302420001e00040006151050404d0408042e00d28800b02c40c0c080010801c03455102ca51040140d65100d0448134a4040304203c440e42c0120900d20856400d86083c1c0c500701701101c4c00d07d06114031503a0081840c040365094025070500f602400c6c0601b400300c0d040c200400000844000e40c1c0c440d504080100c0c81c0c3e04800526140e03403541281d00b0030b480502c0c0418880040045c4020030b0790a54003481560324982c0030200c46801840650003034805040e1501004088983c59041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 149273219 1250 149271969 149271971
    0x210d05041a04230109030c080d080c0a090b0304020a0306090c15020a02010519021218010e030f030a120b060a0314060405040b0714040f0b19050a0507031d041d10 71
    0x20030000981c506201850144200703000f0303110381a200c030040710380c1100f680000d00783d07401145001540c20000108000120703100c0d40c030040c098a0348048886141b054032110720000d230501c0c4d003c0c4002e031019001143c0140c4010805e00d840c41d07407682c07803105176400140d040e00c03900c041100410041600710f81d00c900b80300c80c920240031003a038943e0000e0258020107051403040c0a6640c0c410088500030000b05081a44103071007107841d42e2464501c0c0c50161100108a0b0014140841c0c1c0c240b1418001f07503100c00700d200e0001075402c08140a804459801c205001143c0d1140c96000f407240503180d07480204050201ca540118009110020840c401140503014600441c90714042001080701f03184060f40200b06032070511440070324540048441d01854001041d0301403c4c03d00091246412030080c0306503203a12500d440030304c4c540d00e420344160040c0702c0000d000c14030070058240024418000c043c0143c04580c554000060341fa00402c044401d86000300c0c41010a0003551900038508110781185540b103020 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 149274469 1250 149273219 149273227
    0x2070c08150c0702040e1b0a0b0f0708031012151107050c0909010906151403030304030504060507080d24050a06021e0a050d0e01080c0a0e210d05041a 66
    0x320a000072a0040c90654080c03400b082e60811540d580d0006220806d01000b15030f1a44403520034020700301d0074000f034984900640c000019146001000b6501e000d07060524a505001084d101d220046d48001c2400100c02e940c3c5078081445180700e000d0b12041401011030f0044101100d01d144101d4203061902c400d5007200b80300402c00540005250300d141081540e4183c5640c07210910705025106130400107000c7c60508510300764030a1036020702000ca03040d81e0041092400340c1c005241e1030384425100580000c00070402800340502842c010600390f48608601480c0c1441c0d1120001101c01c014907032000c00410002551162600c1c4046c00040c1801300c07034000c11135150050107562030801d0041c8021031240c0c240d065006950174420100500d8108081c1da45a508000d8000c101c0602c0074030050101d030602d00460104502c0b10155801f810030fa48420440501d14004c10108400c1400c4c034000c1030303540020518a0000511072140752008540394181c41d18140b106540d186040b06a0f40c03055000140 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 149275719 1250 149274469 149274493
    0x1090504080a0e0102120c0309090a180605040219270b01020d201518030a0c02010804061113060311030c0f07060b0301050708090c0405010311011206150302070c08 72
    0x190442d10740750014109a60030110b20001030781050089218410340b6072000c00c103004070b14070101c000c20b54000120f0f8001c4455850a03007106c2100d191500c211150105130004030005003582d0300c441e82160004204074008400e0050b0b1b040c2d00440c44d080600c010019943c90780111081e0b120384602c4d80b00155044c030200400c040002e40d03510f9010032110070410045600c412542041e020000f800b1309130010b4400c160104030980600c2c0740299146524888048069003c01401005403031610030540e496104101d5950011205140d003e00155034a503078401c10341e81021100401084e051010460141000f4a0b002c0060700b00c800d600d85031081c0a9082082110b1100c03003a081300c2ca81050509041c1d118425810076000401602c02c0c51034041d0300e01030038845884e4010b58582c0c45000c41c1400c5501e100d14038400e1209403042840000e000c40c14214180302c80707602408046640d02421507000a461b503503a680d641da10007041242d40042075001032090144104803111f8800703028070070010540b0380019 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 149276969 1250 149275719 149275733
    0x40506100f0e04060b040e040201140705150915010e01050f04090b060613090c0215090c0102060106030b040f140103020a080d0f050a0c0203060f090c040b15071406010303080a0501090504 82
    0x30002034810000350b4802019580d869a11020103010a50b0841e900c4a440b084480c402440a41e0242d0104800445098800d04020121000150310002404110040c207401000d203075409040c01400b4000c4511000040c118540c80c2ca00801c00302d01807007000d500d00020300c5843c400302c12043d4059410b0100c094046120405d03041d410a074140d800b01d6480701954100c0c01c40003282c0d0456040681082c1c0400003035030340014803460b01002070780010950b0b21030640b0a5501c218680b1300c0c0b40546c00c004010080c1da4000c0d4010842c1c05005800440d030030122180101c11100030583c8481942c18010040c025428240c0421010302141802070104006411000d130050b8214a51101040400990b0110543c860141c2e580640d0f4003800312511824025410410104100c81c0b48a551140c042c91040500d424010143c401d4406000c54003010654880d4004a62140b07e060b100030140502820a5000030000140214000e07583d4024a00f0541c41000603a28181d006440480c2005c050002040503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 149278219 1250 149276969 149276987
    0x1e14010501020102180f1804050c0102120702030a1104021306110616140c070312110f0606060f1303080708180109140603100807080c030f1b06030403031e020904050610 74
    0x846d401d50341401e81e040056030803030308030002140d07500f140003d20040020010341c40d07a50070401d8094404028203805c4011903406240c2c0065416448422143c0110788a0000131004e40b6000c3c00161a0400902c07001d9440741442d0301c440000798882075290707010401486400e0f00000040c0380c1c1e400c20458110700800074034003c2d130408120741000400d0002e0035010080c1600450380300851520800041c84080c03c85c0ca1040315215483c024090160348440010861034415080206502c1c1050761401c1c40c81a40c0c0c111465070401560210360101c0401d10085c040c000c0d00348210400750395007451014001010021801e9107043c4681400144000340640340e03044992281510440e89950316113000b000c400146034005c134a203002c4c8440200344e51802040051020106504440c0003034904514559a40c110b0740400428100a0b240070040d03103441002560418040d18002c40c85404103840c40300c00120401c5c840364100d0303001a244803981024040c03903500c00c90895411003103000c01240540a201 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 149279469 1250 149278219 149278267
    0xe0a02120a0c17060f15030a0c06080a06030803011211030307060c1d1503150d03020303010503010c080c0a050c03041d06090601020d0c0212120712030b06030c09010c061e14010501020102 82
    0x5441800540e0020f0500901800341310018100c4201d0222270401c030609450a0007908002507100c40090f2216034a801b9a1b03080340e50060403c0e15603882c2034a8140c07031014041c01128064242e0500990940d020005800628090800020340c10703201d030070243c01c00c034622107101e44450186503801855079072038016600e40031080400320b680351740e41d00c031114031b070400c06941c80d40c40414900004140b5900201840c1030340c4059008018600d145181510b208404865032211000304210941c1c0c40e900c11405401200200c504990515880e030600c00e11081806414440249840301004000e207801d001c00350b0001001c1c000303070240c0354081500030448564100003074000c0c206880c01c000c410f0300030042000c11140d550f10481e240d082516000c1c2040080004c0c5600103801c00070400c03e02d00c4e102040324058409820091700d0088000015a40f0743c410110586406e80d0350103200102d440c81d07030641a13400182d4440020035825960f20040b00e00010380041e4116881031003a40032502210031712400d050 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 149280575 1106 149279469 149279491
    0x2010b0303130510090f080102130e04121d030a030206060301050a05070c03030908120a0b0102010f021e1c0c020a03080f040f060e0a02120a0c1706 65
    0x2c0030303a000c0d8030190a10071408014a152214a042021180d410031035440c5a44102018240c00142d0103011180d4001520280b100c41c151014805000031083c3c1150904294464039802d40c0c40104607828440c004020000c480e41443c41b5524440d401401c845402c0c255107002074640c18150b0340c080c0290300341004110031000a01425100f100c0b140d03584814480c254a0031000b07015180016120420200644500b501d41c0300b034803078860716442c4c0c1d000c01e602e42c511000a08503004180806036061046c817003011441c1040340421121040d00e0a07168031290345100500200d20320707040041c10603180840d4130501c03a8010408040550003526001c4050b901e03400c00111100c42100c009162a5004200c1c0002a966078403d0401405000498401040e40c1e4040703204208900c0d02e4102d130b035200e4100c0008001248802c0b03c003078000c10310052a580210f04055aa4060290901d4010 = true := by decide +kernel

theorem cover : BRFrame.Cov 149100719 149280575 := by
  have h0 := BRFrame.cov_init 149100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 149100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 149100719 ≤ n) (h2 : n < 149280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
