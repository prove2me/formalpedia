-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2315
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:20:23.494265+00:00
-- url     : https://prove2.me/submissions/f28239df-c5a1-413e-bbb6-638bf5b58a96

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 416187050 ≤ n < 416366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 416188300 1250 416187050 416187071
    0x23030c06040c030b0906010509011401030b0d031106010902041404050703093003020f04060f05070609080a080f0609062b080901091e0303030b0103021209060414010b0102060408031810 81
    0x2103a44c00401203080ca03000a001848a039480d4465281955281d01d41080361041c10401a801480d9035070b00f4a50000400f40c40c1001c040d1704c0304140300d40d00710300390942c0c055907600c100d008140d02817030281044442103001144181e0401d50b0016500c050149404204e40f00c085e2110700801e60f117a0051010199071021015480c01c41c00c1c03022000c0d2506240c1140b401d5016103000303001c0e01030350185008110862105124040c814030030f5030f28141c3c002d0400c018a500b90314008203294403000329100030500c8a0000340c030000181e42c2d8107100c2c0b500a880e144183d6946020408a0400b070302081019880300040462030000380034010001038442c0025a07501e0b5400130014001101c42c0d400107841ca10301e200028200d45440036000304480c0e060074007140f41c8101e640141d02a0180020081040d0100d904118418000147c610300070b80c0140015268018070401b0f01d0f09071800514224056070010b80818009400d0400a55000550701110848d403215005a1350400b103404640c1d03550b40c1d88075002c41d43d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 416189550 1250 416188300 416188313
    0xd06050405010b01110a0302031c020405030708100f06120b1801141506030405100b030a14030a0324180b060301150e010810060c050a211b23030c06040c03 68
    0x1080e400045d0000c03e0714030107a0354000d50b00e101c0c04a0035a04080740c1020b41680d0503140c0c060b600a08401000e031640759072940e0b44182c1e03510783c00f01a039000038200b0200e04a00b449500c201002d03503001400210359600b458071055000c2c44d014011080b240120341900d05000420300c26903803512040c0c3c2e0624203d080c04048030f00712406d4086654030a0800f00140000107100041c01400c440e01c010000c40c500c5003620000b81400c409460103885821502e24003510144040000c01601c08244c90030232558910803113606071142c0034641080517019024dc188050342c034019684d944003951000101d240240c15000c5501904203a21100e4880c1d0071a41c0d00c00d46a0700300d004000040d100380781074004c92803e03000308904501c1c64425403040c0903030704820000303004083c84040fa82d0754005d56008000864282c20186041d00c0c261070900060105405401402e007080e80c403002d054011034a620200b440c1200454601034100d4130705c0e91444104210f01980c801404201c0c4114051200000801e02d94100103 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 416190800 1250 416189550 416189567
    0x40e150c27010507151506030207150b0f12030409090c26190f020306010312091a041a1c0b01030f051e0a0f05090c0f030a0809010305060d06050405010b01 68
    0x100c2054030301c1414401140d900070140d0300f40c50340004101a11280914804005100501022205410f8200045840c2d90942c0003000300354421041000c1d00e0304100310800c1210096503100798411403543c41c01c8403900c0c2013130700e9200011101040e64030709a6501c003c0b108540c840d0303900704d0b15000d00d0381e402c01030a4541c070003885249540e10b1003882d8000340c14194031b81301c41c0f080d60500c0460888540550034404c14800d00e402170799002e4103d641c10758503420450202e15201c0094000140e09440204800d044110345c1c00e0039440e5100a14201410b0200c03111030708035200140e0a1004081c4125084448a0404450090514200003035031840172000142034525a09280980b2070511040c04900380140c041d0802d200740102c1200425150b810001024002d841c0a50398400e007401d060102e111070100c0c0315465844102c03802e07108100000181521180080f0740a44000c6085c003030380c0d8540d402504602e5010800400c0c980141e0010303610721b012140c007514155420381d92544424019600306400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 416192050 1250 416190800 416190847
    0x7051906090f030c09050406140a0f06290f1c0c0215010b03040f0303020d2a0f02100b060909070e01180f2d03120801090614040e150c 59
    0x4080b20319080d0b8031500e44004180c4122000306584070002400e0024aa03c100110030700100100c5040c241400b0300805451202c0403684058a03000e0001203080c0c100e11680722104501400c0380a906001040300e00350340040c2c1041d10b106030100b1030100718907242010995202a100c400144803a1032540091030070390401c44100b1603889034001407001c2c00c0a481500e9105034401030900e0000c5003481c08502a003e00716090181c1c604044001d902403011125803104025401311884000044071022544402c0c070a064401607008802150310812594010800c3c20601030b061915017541c03c00410b0030389008440240000d261f524000e0069030f170148c0040205c403441444180d1650400d01c1c1801440c0d894401d1010300c08144000080110100c9a003107080010200c2000c5030582d030b81000c0d010011400c1340b10001460300b60001c142c1c402035101d4001520710f4401d1550588060900b0303c40100340244001d10b2030300ca0b2522201d48107261b0142148500240940c40e6198408484c1032000600354000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 416193300 1250 416192050 416192069
    0x150809120424020c060f03090a02060c0703030806100503041202070b210709030b07030b0a0b0f031e012402100507050405010e040204120b04080f040303021608011505040e0705190609 80
    0x113100a40d9900c0d05c0650f64100c84000b400d5580340c980074803071850040d6001000350010400b29003606010000b10b6402e00f1240207441e4550746507103490801c038001070203124100c0404c0c001e00101c0c0100303032095001501d1048900403646c000351520032413403554000c646010302c072170bc05421b004004500300c0b911903004031a9061114000c0d0441ea034003201070100400000c201583c41100038015941d03000040700401c10a000154dd643d80d4800c5010141e02c02c481805c200c02e500d114a010103941403150301c1c12200c0c00c50301a003150070038072008100103141c0f0000308214422010031070860740e40c500c0703007a000341e030f407902d8160340d50345401b0024181140254806100314818030040000082095001c4052540000005900d94a6141500030f5000d20782c215078500d00081008020940c00041ea4095600d1024034401c80341d6842100909a8401d1009110b030300303400c40307400c0109007000c0d0801d140103a1040140c407034058840d00840c0b129952201d000100c540081c0b008c125290f0070040c842c020b00b8100700b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 416194550 1250 416193300 416193313
    0xb041b1703070c15020a03050319090501020a080f090c011b080d150b070b060d050106150503060910051c0c170319020105060603190b060706051f15080912042402 71
    0xb00060340706c0b2904040602801800000105014400e032038100c1100b940750405c12569803541030890007500102c0007280890000c001160002001c020824801c1001800030841000340700b0044440c061300303840140180e946240c0b041c000502e0a00335014040a02100103002c90035504441c261040300d62050b500c4400401881d00403950240700a92300442c1070b51a07050038102458070a0040c03149900c40c0c064040c603c40c1d800007269003c0c00443c0104070403a85030710262180918031024550600c035040c0d00122030683c0410390200d0702100781c1c1d890b004204038204681c2e81c0400f098030300300c583e0b42405a43c000191a4202521941c5c015103900480d100030000b614024002c100e140c80040c00b038600325590200d001c0301c2402d141d013150501040260001d5241e004510308a005003409a482c1901041041798010140031085120b4040310103403400f0364281501d4180654160b840644040b66500880d20700d04810000c807401400209080100c80302c910031083e019000001a01800300304540105 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 416195800 1250 416194550 416194589
    0x180a1b09030b060a050603010303080f0108070501091211030f031e03040b0105090a0f060b03221e080c01020f0c0d1d01031a0306070e040f02070b041b1703070c 70
    0x840a00781e07640421064000e465a000041201c446a48080c5c0e004c20008004020907502031001402031030810342010340c1e6601c44150300d07103e0800b806818002241d101c0108881102e1a20120310302c1c0c05068618040c58180300400c0c2802108a0b007140160300018040d131000340035000ca100341c064000b041c5801c1d410607a07501e0300604818403642c1d20502c10407010511002c001c0e40300120340d01302c0c0d400070803a03035070b5500181720541c104035036140003400000d42d40c95003c101d50080301c811031340c0146941c06c00030592070099802108010b0591b0b43c40340038042c2003d04002440105200240c001419485211b595807103854850144881020803048031040420b490920310100c0380703c002401e003c00c0d6540441c0d0b845d0b1007203070b0a0708074035454803505051000094204086813104182a03a05105207400c0008034001c0c0d104203040280036128440006000c00c0d510ba0518209c4030720030351880c42c01c80d9200340010b1038580b101c030007440c9500009200c2040004041e030020050400328034551502506 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 416197050 1250 416195800 416195807
    0xb120601081009080d050910090308010311120c01120603020307030b04020406080d0219020f04050f04060c14090409020105070506190b011103030a150b04170106060302040503100b0d02180a1b 84
    0xd00344605d9030075843da00407d092038014003507440c1c02c0c2d4802038100a42d00c00750800404040080c4015200100d10b1043c1c1c11080c28103403400e005087e1400700400002c84c1c49001114070b41c034083c0d041d00016503035400c084016a41841608001e40c001c41d442402403c19004001c02c986c99503000036801e40c811519108880e03004900030300842c0102001c03c0300e42c0c0c0c8a0000c141f6018203d400d09503c1803400b000c04c80c0014125107440d0146000305020040740700228401c0d40c20048800781e0725903450f070512643d01f0502c0c040c1c2020701076602c10301d000303407c00080341e03519441c1c480b094030250101c0c0c1400145038440920f610542c1c0d41c0c0c6509203030400100c80c0d1040410388a2001405d5012826141c1030841000312440c0c0c4428000c045945580d6a2140e0b2507e00c6005000740e2a902c80070b0f0b500705600054264442d000b6038099881c0140030b0304e452208041448010035107030300c0c900d4001d01e0168025026982d07050200942240c3c20303480d15280e01d010b504441c1280c4600b0326082d0702460042180503026032 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 416198300 1250 416197050 416197057
    0x9030e040c020c1e0409021203270114030c0c0708030403050f010504120c060b030304060201020903160b030c0c0712030f020f01090305030606070201030b120a0c060e011707030b12060108100908 85
    0x108440c0780c1004c0900c0004100503244407140a0f4000d880311840c0c1416080000c0208610028010542000804030801c1070810040005040c0010104c40710351a03600810001150482c0c803200b9000d1500c91068003450800c1d21030382c003c41d0941c0010404000b845000d00c002484041840c0c020840c92606554101100c034000701c0000800030716802c0c403010081c0d20342c030184d9034020017402c903600c0d142e0b55080203010703510420800e4028012040c00b07016980406a10b0015580c0c82494541180c1d034811244172244c200881e42509032054410000b00b0703840c0500400900d40c02603880008c00c0c807013000702a240200080b0710280d240c1c58803251501083c0c3c080c042e20740010040b40e42c0c5580d08400d0004070060300e114601c403a03100740b11918503d006840041d102003454415a06007205545c0d410081d075040c0c260303d40c018085201c2465240c40211403c0b02198040d10500300040c580c0ca40802299100c2c1c44181030315860707031043d0300500c10301200304200c100c154030560341031080c040c0b00d0380e41803020700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 416199550 1250 416198300 416198329
    0x604060b0111012007030512090d030b0306060a050910031205070c061b021e06040e0402040606090e06010f03090f0302101b050702090601270501140f070f051009030e040c020c 77
    0x131408240081014880d80071503185901001d086c040604020740f15580364206803202001007441c04280d121a818007145251080c231002b400b9032040d602d003d0a11a0200006045005040301c010f0040002a880620a814000f0035550aa201c804928009001c602990000b0060007032038820001010000b41e0b103000c1450b4156a2001d03210700650511041d03081808071a0b030301000104011031402c10580040c4d00c40c0340202c9051051035503410382070300c40040c180250301110921b1000508154050b0348281c034442c0a038079000440344c8182e20fa020a20307082d40001c80040e0000310b8040c0781d039001070150114400350721581a410782010340c07014100d881001402805600000009441a80a43d40383c66100003030706103402d004155003140000380c91032802840c0c04270b9400b20301d030710070390800320252400ea01030810954a0807009460300107003840000720407030340f5104103204c041c201455801010403c46c440c3c0c807841280440402080240c50401070080b085503c40050b58200d6a190082c07120b800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 416200800 1250 416199550 416199611
    0x110c06091f03061706091b0a09051005040c0503100e01120605091006080d08160e060d0b04021902060c09010206010e0709030204180201170103080f0a0507050604060b011101 76
    0x540c880d4003030b03029010903400300c414410901c00b02554280f02095152150410800343d50454210030303656000b004086081641114010f00240200c403015403003141c11030b103104080e45035643d5802c009020788959401d2000018804414040c22541c10f4050300090400e10000704905c2d810721111079180c01c80d101c0054041741c1c40c1c5d4003040e40c4010a022521618a1603001427200940b0b81814a40d110120490fa000240010700040d0011042d20451032101040340e803002038174140ea000700030060b00309410701c02e03c16568100d444101e81e00c6200401205009990316907940100750400b904207c8000c0c00010303200801c2003482e04d681c0e40032036244c1c15200c06600654840d00c600320b0031600504030340c000030340280ca047c42c00b1655082d00551180c86078400d030388a0300d400d4202600e205031170000303200091124501744040c04030340800c28050322200c103252030101d00300340ba039841d2a890404252810341d81240c0d22040c3c1419960700c042c00c2322681c0c02240081c80480f84201c41409100d1903c8404c4c2d501 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 416202050 1250 416200800 416200849
    0xf06081207080705120405101107140303190305061309080d0c0212070501270c030201050d0902060f04030506130c05010f090806190f0c0801180b090106110c0609 71
    0x1c1100c0c02c810b80700b04582083c22681c1c038402003103500c0c040358450301510744106941e100000700c0d24487c294003a540506107015200c0c09103448142d075800704402c0641c50381400700384555001c0700010840110355000075503002c0b42c2814090b081c000e142ca00d441144c0b600d90700f00b00610001c202664100c5080240b400c2000400503211202242080c00c4e0f429080c0142c800010288140081500070401c94200d031030381542404980380c111808040e00c44001060100101401c001641c000d102170002550070b420040742d0702e040341c0d00080300c0b83d100d00d404801c0541e000ca03060040c00004c000280d400800b904014003160300d140c4510040b03081503c101810032661000584075035204c3d900f2400140002000ca0759141042c4000c0000b003801c10400f40c90070f0f0f24040d100e0300107019030f005501c0c14207440d4640301c10340d9091400742c06580c3c5000e01807940f000c0c0c440f1300b42ca00d90b13200e0080240c02400f140d5031300105000420700050409841c03804991151009002e003402c00d42d2400015400e49010005040c2c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 416203300 1250 416202050 416202053
    0xb03151b0f030c0a020d080f040b0c0f0403050114010506070819020c09070809010b06270402160c2c01050f0d05010f0603110d0c0e04080c0d0c02040f06081207 70
    0x12481010040d4503054004000e03c8a40814070000c1c0542030380a8007507070a980801d650845000508541500c3c1c5030071131101040100e030550700c0064100c10000c01d0350f4903104e640b14240c0503650290703004039442d039035034a000c40ca0f0401c40d2200b5809000c00701c5610f8074084aa031a40e0103240500f110100d041007240c648804000d00030014030300d40b9100a004010a032801060181045008642e10070295003040244141840c00e901100d00e00c0d2002c0690701981440e4810503401001c0c454501c030b40160307003000340f010f034200d9804d10700303414500c901c2c1c40000341403d0003096448814004c07605000085551250781e141c8001010141c1580c0e42030703d0110f000a841800101d410303490a4004d0240d503e00036811100c010b6035000340098034050004c0c248028041740c14040c06030020200034042070340c3c120007808035900351005a82c116008200244c100807590301103d01300744041c09000c3c00701e2990005041107040c14014038100d9051181c003041010720741400c041c4c541400212403980103600244100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 416204550 1250 416203300 416203351
    0x50f101d12180306040f021305010614090a030f080c07060503060a05130f090c080106081507081801020d0b040e031204030f120e03030417041211010909020c0a060b0315 74
    0x65003402000c540080c28a420a416218591b000582c00307203941d141ca510103a4017501901d412101140e4035404d00002e0002408800d0b0407120807280d02c601ca80324008007140b082c4010010b410700600e00c082c0e07103000d0050703c980b41541950000050180a00030042140d0351101e090b411140141c0345038103080c01c1020070000a01da64451507919520303040701003051104500b0030400b624040350007001140d480352a20799445090301004446407440c0c1000030f004a200d050f02540007400e4444ca0901c41c0030b28206142681c00400c480d400207607541c0040c0030340d481d0034043c2c030340c0718550740015504d0a010956003038180301008201a09001010a181031160310406010442000c10300301040408600b40750b941e203940c0107480c19034001c001c60810000e0094484110740860b046031040d2000401541d50701040a074403141c88a043c450076401c0000c0d1f40c2c4460004054086100016080e280c149207050300880782d20403641c0f03000342d0159001d580509081803451b030f00490300a6042d244c01c0d48401284 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 416205800 1250 416204550 416204587
    0x40b0a050d0f09060e01091511120a09030201051e0414030f0a170a060f0e06010c0602160201110f0c0409140d022812030209010c050f101d12 62
    0x40c500741d004040ca10143e03001e00034403840341e10288104078590001d14241c801101015000c03144041000011001c50380c080f543c610b4035000d1a5040c004c19400b0305050f1207045801781c1c0343c0e40d156040e250405a0a00c5491341c844000c403001e603c1644601d131806c2c40070303000070801408141c4010060443d410b0030400e44011a428a0119035180140c4000070240c54006060090b5000800041104002540902019150401848104603107044d0b00500f43e1500541100d040c0005080344a000c51000d000914101c400e02c03801e00d0824000d80300061810b102e903084c0b0a0b850f042600b24084591001ca00c80b07807258030495012a910000d802c241102100c4801e466040340724a91034811120740204051031940d25414018052806000741540c061107c0c4030001d0280c040502c4040f0014000c0c8e000e4a00c41c94103160000c03080d1001da94140ca0240318082c50301c101d900404540320582030780d014001111415070030318039020003011411551640c0706000a1380980011880485980030711242 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 416207050 1250 416205800 416205817
    0x2011a04090501110d0906050c180105030709030b0414100b06031506040807080d0f03020a020606090c070606090b100203211806010b07122f12070b0601090f0b040b0a05 74
    0x4003aa5515117801c404004d0940203c119651420a0001181d4021001c2660a90190707504040540304503c001140c03540e1004200c0740030b00ca071440c0080007042c9080c600c0c0b84114031070048060b10f103106045461400180c8a0340f110410306100d00201c85403503e6081c6ca4119440c3c1c85d01c040d2403400c210004e1040e00607600a240e10340b054640014201700d00052940209905803034003282480c4401e0308905921540c0d8907080136034401300104003070382452012203500015403600207040160503540c9030251000c0340d1111134156103404101485191020082110190b2070004520b000e0710040d0340d0160646252018a1103c01000058594684a401c4c0150041c141050300c0c001c0da101c16110300e05801c03074601a129440201a8445418043c0701c0c042501c4480c02c1c410354039103820001192506402080c10b00090207002ca0100038440c09502030038055101d05100c0c2014540480010241005680660341c80c0004d07420800032502548201c030b055902c8550016034078007448005640c1441000b05 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 416208300 1250 416207050 416207081
    0xb01030e160603110301060212131d070216050a030627030306061205071707020c03070605040e060307030807060f02040e010e160809030a05070f020301141602011a04090501 76
    0x1108020003150080c507816a0010b480030002c218030203100c3d66190209006080143c3c0c4039148900c117010022001c0c02e010451501040d0b8a191540315031804505034103851042c684803030381440741c1c0d40e40500901c1510180c1d401c043c0400391174800000c125800a1002901300390780c1c0d034280c44030301101c054141c414480400322120303211603624004005095a1084100282200460020b20151801214011106070355003e1007903a00780c0100e00c1c8040040c0c0366009500c03c0c41c91142680d101802618020142074a901d5203031803900c04030715848917004120b90b1294000d01030500000d0020801d884023a03402c064001412000c80003690024400c80d080866012103000000484060401c1d5451040c0d001742c807100c2200644403030507a000202510304140700e030814040742d41450310510240500301c0c02146a0100c96186801090866030314680c02006124111f04000c1e00903a038010f000c0d40c10240c3d00c0200460b400744034400c00d0342808800064442d580310b4406500348102504142c4021843d4031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 416209550 1250 416208300 416208313
    0x40f0207050a0303050609040f021e040e011505031c1416061b020a0c050d0501060905010b0310081b011b051516021906200a031e0203070905040b01030e 67
    0x20040c2e40c4940a1108600090400b00000d62509004803024041c03a400040c04c651001550f003080304551824034040305104020385050455aa40c2c002c0a1400c5aa0390000444502e0030380c0030b2501f10b107036810640c0254081c45000d28003402161040700c060700c1e640b400309402c2400115085183c4102c5821320305051110301140d0911109074000d280c401c2d28050300310700c010701440f030590721060402c030083d04404500030308100d50304210144074010303403250000044017a20307400d1401c1119400e800000d004903001c01003291402d80740030b8030406820000d008020649445040744450b8864140080c1000300f5405200c0490b440f0030b03600b909080d030200a84000540d5425400d640e8001240e881500201ba100901a0140003081d40020019402d050669407080c90300c1c0e550140c48a2100307040d8503400c9280c442c2c19440d00d0400303801e10760029900030640256052940c076070444210019010b041c810001d0000f4603400480031001c90f00c007620042000291100180c4c01008240014042030080c2c1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 416210800 1250 416209550 416209553
    0x307050706080a140610080727030201091208040909060204030b090d030609020c07030b04140a03020718020306240c030d0e06100b07080d0615020a0309080d0c060506040f0207 77
    0x3080c000d101d01c08101c030402c13040035407001468044105481041e0400c4504100d407250300e00c50303544580d2041d01824159080c15036400540c0d00c400505003050520040710006104541c0c1c0005036800410b1101004c400840c1103449a19051090f441ba40e03c03031550321a00700701003003125010b44004603002001d0307141501c0c00c0c01c40c0c0d98070303031508013910700c0068605200802c5c00c014a1007600c92040e00ac00c0141445c0e811941c5503044242d02038002d480904102e221400030040401205c83d55912960140110500d04802c14200c401410051211a80144200103403911403000103504524030003100300e600340d0042088052807251904850060100240c11030001c000d503042440a8400d400803681c0d540c0d6030458000000c0d4040c0180201c3c403a0401c400c5010410107000b07000d1500d0b4003080002c6441d6100c500008020b16416241e0150b081000d83c00145038100c0c42c9030700200300c0c2c0307030140041009006000b05140245003009005c01c1c0da52002c90401d846a034840d0a1001080384110b5482055 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 416212050 1250 416210800 416210807
    0x406030b061504061209020a090504140105160816090b0c0c0a0504150506073002010e0a0b010b0a03062309070207030809040e0f01050c0d061706180307050706 70
    0x40794400d0091010110a4041066680c1140c045440c42e6994021101080314100301400c3c00355002d0341c2c040039040012820840c031380302c0c1a0059206940240401a15540c51400d58030f000b050035003050030100e41d2001c00d0340c1119a096121500845501d40c2007042801034a03d4142c940110200d4203010501000c40b02c000544007a003c00126070405103ea50740d0200f000b6102891081c0e07165051921081045040640142420300e01c65404401c0f20030400701e010031040d5036401c0c800f0b10b03109a49498804d040e0207101784020808090013800c01c00d1480d441d0080c0140040c4103115407000000f441300c100134842c0d44660007030301145010740302081100801c9003541e0b040310945c510641151005c50f958a0000900f0383c120b07584103400e41e09124a120800004040100c400c4045001c4c9103c800d402000a204861040c020003007016102c0d03003020041404c8548940000b812121030280c48090b0f6880003030b505501c42a1803102001498040c07090314250b0060307a4009100340706564003c1545500b = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 416213300 1250 416212050 416212073
    0x904150c081e0405210c0105070f0809030304020906090a0608070b03100e010602061f0302030a03030f0e0120130b031303030c03060308310e04120c02030624040603 72
    0x440c00c5842181c1a008440180b0070106a40013085907108120784500728108a000050201d28813184606020703454042c14296a002c603a170b4400104804c01c8261625000f40070180c1000001c40118290f00d010f80c0410701800340038064a118840d54000598500d04e030f600000044c1001c6003e40302025551540017080c0d400654000b00b07140360003500410140c0c41203404904884131307580202a1078803450b20179022480b80c110141d0811040300300100c050307141044411440f9102e5580002c010511802041c200e035100c80804c0c810744d06044690780c000f041c50080c42d1410b08402600740e80e961503404c20501c2042c1a074401d1405450200400108210f40c400c13503013481e0300a880502c440c641d0305608508542003408000c02c580400c0c17000c0c8664042c1c240561200f0380807003410600702c2c03030010f150038240c081c1d81d405510300e65003200c100010800c074142e0b091100e21050820310800c1055070300090b2504001072100340b058161858400d281000c100c904200400094070803c11140c6070b0520040070007 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 416214550 1250 416213300 416213311
    0x118080a08042102090103080d09120518060306010914030a12120f0b0a0b0a0201200406020708070518090a0206030f010311010e03030d020f04050a060503010305070b030907050904150c08 82
    0x1000020211581c0e1890b045218078280d00801e07005c0c95070b00396034441c0925040540060042555030b6600c42c00200c6081420b040a2280d0316426141d5100c0203603001c2c1e10707011f02d800c0c6010305014000e21a007030f60045500c0081d00e46c940c1101c034100c1a2040420b280c007442610240200c1442c080c014442900b110840001c64004039050101604540700c180583e41a030303100d5600400c0c012010004074041e00c02400c50404280b00100307040680545400c185c010400c4020502c40c8001000c212245c3c040050344000c1c00c405010f802407629140000d0f02c0f0703d00c2d0024858415255030002002a58148103c10410f43c0c000c1c4416201d040140b0030f044103040c00d0104540d0503844e640440b006e9800b80c2c020807090700d40200154034003819200c13040082e404c004407181c0442421303c40484c81340c0c0c44044140203050145c0e5455280d47c550700740300303240080d42d0340180510300d001c1040c02a50310380818404165042a1180d110359112450081ea2443c606401e440180340780c9040050b05a5201c1640d9000b403 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 416215800 1250 416214550 416214569
    0x90309080604020102070306050601020c03010c0e041d0a080a021f0209040509061b0d1503061407080c12040f0204020c01092906040e03070b0f06011803030503060118080a0804 77
    0x200d880303051040da00d00c0140c801a0140e0310445013000010860b4004943c800300c1841030350b55518402020901b0f50b000482200c001c42d0205141e030a050402e07126016070780c46090042c1c1d0030b0882d0b1030502515003403800d4010780305c610001841c0c16118001c0114007140042004411055000552100025000303804030905c541d0510000c00c080c000009407041c01540099a0722181c01011203992502d98000643d4050303880d1902c2c070122142c04c4986030800114000e00c404103c2072016107505031b8520008100d41c00b4000b00005028004412005440c0101652040304000340c0f0f5500346590b41e20f821a40080d44035000080310150311070103410044495100e4002c0403040d168030800001c03d5601650031460a04c1c6100002e034481c6820380004040900e088103a03481c103421600c4610441d9011200d046401c04003006208955a020007940b60000d003507400d4075200382c10340c5e500030501c0c030000d4603150402080d0116001040036078500a0000c001d6841140c1c180221440c0181e150b07005403090302c2d01d1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 416217050 1250 416215800 416215817
    0x90411131a0304030e090411150d05010e04030219150903020102130e071409131113050105030c040b030709092d060f12050102070606030b091606140a0c050a03030903 73
    0x84000a1064074065036042e00c031102031a600006128514000a0040d10f0351400300e4404501900d0300c02c444840954000209e50384e82e064051510207480040e8080d140ea05905420000842c0c3c0c0401c018107440c0307802502d200798038a1820708501c00d10109075890754030b80c41e10101104050701503006083c041020b03c032084601d55280402440010111076003400b00d2908407010402140c82c800504807031000501000072048600c0c0503104a03051803620f0381d00590000f6003284014548114000100402d18005103507280c201a9203a5501452140703064603400480460b910a002d180d10780d001e4101004100302002c40240c0c224000005140040e03407405107101526640c1d48540181425584580c103218500342c901140f46040100d86402518a550f0a01c601400030707960703000d1400198040d4011940504041704403904046800c01860700e0b01074441c10801038560003440c030b801c0c0c040c176240c9000e4542401010a03581500034a8000740980204c100c503204158044d402214041d020fa500c8000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 416218300 1250 416217050 416217089
    0x10e1b0910050f12030d0216020909030711131d060a0c02010203040c05010c170c0304030c06020604020f01031109060f0c0106050a06021b1507050601030b06010c021509041113 77
    0x10303041a0080b42e030402803080d0050510b0900e0705480651810140840740b4000940c4107590813a0000125000044680c0000c0310940c60031002150300001e407540507600d48039803541c0d40440359958809442c001d02104806401d0341400e076120100c206a00b040d1500d6484000c0d4200341c80708421a001c0109030720700000304007154814401c2c0c0348138660101c1501c118600704801500d0030b80c140d84e000c440410b0360f0802c81d000342419502504001c1c0110004648445c01c0d8505098102c41c160801011503100008210241e510380442d0348001c542806c00050000001086c00030700c0c414401a66049100005c1050040c20954020613882d224100200700058a5108101c40c074a04d40c0b0544005030700c003a010407501d89200201e000d860b240103011a41c0102ca041e5182081d4100f51000c1d00d19030880c0004000380054502a582e222130b003440e000d2003940c8280e0000740c1c0703031b03800003525001400045103d4800e500c5650192403880c8880340546e881c2c1d1208101000c011405000707203002940f01140600 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 416219550 1250 416218300 416218321
    0xe03060a09020306061216060f08130b1303050910020a06140f070503090c310b150304020d140f0f030315100306090c0f1706061b010e1b09 61
    0x480d2542c014041c00d82c0c0d80301c140800540c0305241c16a0b401c0c6028a55111954905458180000300202e4641700c904c1000418081c1410780001e10b41c1664010001c140000607117105001039001c440300c51400f141070b40360300b030440f401e024a56140741c120041200304551140c0003e4031611080c4038007014002110b21030020110701c0c40550f003449064068102041a40307000304065540241290129212080050002407210402003804000100104a001c200f010a98400407242500442c14410b4440740707001304a00010360154110900004004030f400c41d40c0b07040f40028940d800014075070703d40e00d41c024010f85035460980050b00e1486a0210072003800404000d90340b1511010890880071804401407007801921044001c04241e41c2e44030120b40c25449209507400c1030403c0c1c1d550002e05402d070101902c48804006100c195520910410045540c0d0404452051200602c1600031050f00449180902180e074445080d90007803602d0040a4171030401c2ca501458001c844149850b1910000345 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 416220800 1250 416219550 416219561
    0x7050c1c111008061e0310050403030b04060501020709021c0f020c06070e100c2a080f03090a05040c09080a060237050c030c070f0312140304060908040e04030e03060a 73
    0x480420119070004d1141e1428001000c548610000062109603c441c002810200b8400350f45a815a5840070310050540c544a900d00301413007600c0c01c105607420f2a0000c2d6981c6c07940d10400051320b03000503942900704580c260401c1e80103640241444110303001c42d0444040c0d01702c5541031110f40f213a5000607811900c150101607440e0000360501851466103402101c12840403882600e8032681000c4000f00540b149805120a00c02c0c400d21200c09410240403a0400002c66111502070b4800d200b00c1145513501410f0504131401140c000480c0710894000b590380e030342e4551004802c1d00800204105002c0e194009112000c491901255101c8624501a4015456000b1442c5500c0a1181550b01074060001071542c3c031413020031281001d2910750078a03e0007409070404600d0000d00b010400c10050381400c030301b03a500e1a5080400504405075402b100c180401000604110303180c0092005100886048901801408111590518081c28050050300c041c083d01d82c0280320380d000140c800504d41c03085 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 416222050 1250 416220800 416220829
    0x20616120e30030f041403120106030c0c170a020f03120402090112050c0f031204270204080316080f0f12010e151203040905130302010509070b070807050c1c11 70
    0x4540c10364032101c0111904c001300a000719031440310f020740c07078000307140400190400320190980304100d581000c80003001c0e200c1c124505001e001e1703030000c8000000c0d240e40446040c0320100c0d100948892403030300b003289031030b0300044a0075942c000002c601c401605d0041019108900036608010166071310319071510300c0340101001606682200c14041214507041100240c400340c014100c40c190801107401900540c881d42c442d41520011008411110120410040114071110811400e1501e0164065280d00c01c0c00f899204040c0b85400400401400c00d00392030520905600040c1c45030781e03845a44120b64031100808070000203003000054560002078009100381c0301c1c4105244040c0d114020b01019003999840751081c0e000900c8045002015442400c0c0300d40318242411090310385900f030107400c4410180c1107111a4010340d0042c003d020040c8211881c450780105090341c0c812460420508040c190021240e0040180300e80705d9002018030200ca060b80d0245c0121144002d90f10100840100072185 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 416223300 1250 416222050 416222143
    0x1506070204020d06031b05040e01020f1207050c0601090b0909010b0f040c0c020409050a02180105010e330a110304032012060405160e0601020616120e 66
    0xa404014201500605507554080a0106426031290748480b04004940ca025203034500e0b0410801c490310f41802004103d001c241e008600c1d15500824000c0a4420a900300900101c10000b1403406480344046800781c802110540b1440d5840f50403040180038840360081c403480b0680d022401100c07042c0f00b00080c000d00102807441c1c003410070040c4401b500000f00d070442400b6007800c201c00907071a10300401420908c180c004e054641d2140c4108810b5001104150350b1207410080180000d0340c02c450501e100c0c03d4100c0302c1070001188401c0b00c80d08400b00c0840ca0070111461002c3c0c1442510681c054201040e640d2110803041d410f20140325a28000c9100103480e00182c0002c030040005e1400d5101c3d0b000401500c5c03010700c5504041135038030b410300039181290164024141d09400705289550040500721380040000a41000720000750f8810f0080c2c00401c0320548449030170074003802480311059402c080503080c000c0e034241191158440304c400c0400321a503040000810740b013042d2a41d16201d084110394 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 416224550 1250 416223300 416223307
    0x50918090a030f031e0f0c050f04210501020a1110090809060a03060f0f0501140414010e03030d0606050c010501090209010c0f08070812180d0e120c0a0f0e1506 70
    0x4404580c02d42c9260b00722018184e86071703101c4d2042c00105810040c03040300794002040201c0d605100304219041c1c0c90102e01044418801e5094000d1010100c40031100c1002d030300c40c1da4041c484030500e60410704100c01031603036100141885c2115048030104520709228001d41d000000c0451002064900010009144901c10441c3d851586442405056198807900e00000d0058441d0104000b4134000e402440480f10001020449981d021042c020781d0b052305034689040500c3e0104241c00d0744003044055041c4000d01076944c03a40c1c2c504100b500d040c2d041c85281440b032035a803500040c00b030743d00ca2103004005508000000c034001c10703640202e03001600103035200b44c3c80315456103071081141115802121510410054840030883d4003000d012f407500c1d2013480c50070740c2c1400c0402c01007404640c190f0f14000d42101c80f481c1d0049030008101d00b16680d094502d603030192891104c075800c100303421406550103010000007207440e025107155041070310801c3c2d94951007501c0e038a011000d490102501203074800c03000c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 416225800 1250 416224550 416224553
    0xa14060103152d0807170106051507031205150906040e06040210050408100506040c030603050c01031107051903080f1501030f1404051b06040311060a02070b0307050918090a 76
    0x2c24003101c1c1080b444125880c03007a555001c1c404412929031040c0d10a5020080622045d01b444000d00c00c825402c2000300300152918007c42c1e0b45946044c1402c814040200703159041c0750240315540c0106051200c200100e10380001900e400c1c0c0301c503a02c6980640c4038000060054100f174415090707120f80040041255503116030802800e1522160701c54100b040c20b10001601c00340c100503480b4505261200403905180150038041101d10000d8148101400e00b8010008268082040e4603488001e280101d43d860521500340000c2c03054980082092242c00008180c001c070003241c0c0488244641d0380c0c22566118800328080c0c1c101d080d2081c4240c0e070b0101d4003150956000c4c0d841100300c80410003010401280480082808402c11101034580741c0048482109841401041042c0040d04942060500d8115210441c5c02401c0350003190143e003000a00f044d44600070002c44000b8046580083e42da0320700020010b0890700402e29850107045503500d041008440c580e04907200e115200010040c4e240c09 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 416227050 1250 416225800 416225819
    0x615030c091d0405280b090102210c040321080c1c05070306150f110d050403080c031e04140105040b07020409060e0321010f060c08030a0605090a1406010315 69
    0xc0c0040740c5600c1280842c2e4003884240c10324a840c140c03504400038414840d400c060803601c0d8007d0010b0301c140d00c100502c0010700d9821180c0b28120701a01c00c2126255034082c84010144a990409003600d441d40d0180c0c1d0440c407011170b102c24880c1c0c903035a48140a440b0b410f58022903004035141640e40341150101a146101c0716806680c2c460141d260116100b03a807004208141d40030301c1e40340c41c002001000aa150302d03030010002240d0306007000c014507000c0a00a0300034618040d038040106882400940a0303001e01040041d170f0b00ca6072500b10100041800c0c0c0303034100901d45c080d124120308540c0c5041c080c03e96601034001e40d170441d6071500040745000400e50820004080d031440c111803a80d91141c3c1915240700c1000900308240e0410307100200038816880040c00c0c1507059000e07880816041c0018042d25a0058442070200c0c0d00c0000c01c0d40302d8551100b5240074000790f410058000100c101004117000454200d82410448000c10200c00c0c0c84020045040d00c202075946208048040800c01c1001d41c0d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 416228300 1250 416227050 416227109
    0x5060a050a080a121701030317060303131701060321021218090402120714091b0a08090c130b09060d020901290a08040b011509090c050c010615030c09 66
    0x1952910080c00c5c0d20540310800308000c280c10950000d0310254511120a00310a10540c000904400550030141c5107095500f00402c2d5000300301100051a4050700002c03030035004000916840301c4041028408131b40c0380711031005042240d00040c401c14618407041c510140449a4121244c3e0354150a0000007042c003c2c03010015000301d0b00036884280d4140f2011013881920054034034440b11008040d041c9040100c11034000d030400602164200020b9416540d40046400c1008541020f8007140e46442805050100c881040354002088690380c1c83c0c2d5110340d17800010200e408642c100d1543d251b03003040c000d102e940c105000390083c3c420300040c4004e42d907006144112484450f122202c0070044d800320401c0303402c05082c0c000828502018081003100c42071299002d45240d8030480c1250203039040040c03520b2510b200b16524190f552740304821041c42202201c00c0140118024401c969403009841840c00004c0042c40000785041c02d151105882580034004590714213504101c5030000006e60007280340c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 416229550 1250 416228300 416228333
    0xb090111190302010f0b12071a22180c0918020403060216020301050f07210908130e01050f030a021002031209030408100212130c080102070605060a050a080a 69
    0x100307a10100d003568140316202020103210364008100c00f06002440d60540e1000c00307090b84100c82135040c0c55958100000c110045400303110801c9010030100d008030030188a06035a01d0600c0c160503110400601154810000319100d4142401c218554a0b1812040391010300320040042c102020410510a60190103251005d440d0001450b080e965a100005c03a4486180003504884078405401940b50a200f415404015001c0c1c28030a49070140c40109038051648041003412607203c0a01801c04503948607481031588038a030a5527484c01245a140f240d0740e071384620342e01c014140c0004a1942421071700c5441c0000003600822005006a00700488621020310000c2148000d214000c901c40960300028000c1101a015598950900b0126401e000c0110107441707070b803401007140160711741d003450340b4991041c40385200c81441d407030a107032941d03107a0180d600c061801c1d8004140c100601a46904c5503004400c12907110b141d20740d8480601c08040e84034801c0100542241d034a075400300c0c010007281003040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 416230800 1250 416229550 416229553
    0x108190b16021c02060a06080105010b3406020c0c0a12060f0b0a0611070f062a210813081b0102040b070309050301050703090809010e01050d022b060b090111 69
    0x8984189900c00d0889041c0e9450041c5d00c03500510090071501d22901004d0039103100240728940c1404203240d5a44518101c408101c60604c1d4088990b01c00942c80448007080320513048040c1200c0d04200d40070703410001d9400d810380a000c0c40115249080100c0c41c0c1241c2c5040c0a020b60f00142d48c54071001000205960900c00c0d03151001e003034940d0b86280f8008090421611840c01a00c2606072862030b10300160040c0220080d44101813100d103401c0681c641084a04010700544000600c00d85400c0c500d0507200204034031034078008040b9464043d0440c0040f40b1680d907950607590707188140051001d5078424080d250980402c803000820030b6521410400080d104009881e1554910b007000141e0700840c401d500013001c802c0207001c01e107400e001c0c4580041d414a8140110041030300c4425003481b4020741d0906002e0042c5200c04964012001d94080c84c00d00e03801151566038404c2100c01e4003587c080b1000000760781c00812803008550388a0441580c024012403801d2141240064030400d41c400d205604c0c5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 416232050 1250 416230800 416230813
    0xe060d0c0302030d020303010e070305060a03140102091504052e030207020d080d0609110c0d0e010306090f02090312030702070317042607061b0f24050108190b1602 72
    0x160f2020000b8640c445075580c000c583e030f0340c075061800d145400043d0000c0101401c1c0700601007181c0e0b84155400a90760401030324003141d058104098020310642800320342094084070f10100049100d4050822100c064444001078460400c3c2c0d4540780101d0104417404065646041c13403450300c20f60240113851301c00340c4207c00318a030703076103440c21150001d1548a555a84460041c4541822802003810119103803003200c7c140315a042640303444101090340300c3d04101e4802c40200701c1da03209401074130007000d80560411403900013803040d00280d40545080c601038401c50543e41d002c012840c048a206407415400b80581c00e06503900c0d49510f90f180e00b00400115814000810000b1150b00e504485036607040ca103118201d10307031194906081c1f459004005200c054400030014054050304407802642c885414039034122503190500300030205a034402408040140400c1041c1d019a0000d8141c0e10400200d8001c80407580c090f91943d005103c0080400c800e02d40450b0700003285d21007014085c0300320b0041c0c0e0310 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 416233300 1250 416232050 416232053
    0x1803240c110723030a2a03050d110705131b170c03040804090f0c020f0619020d0f06030f0507052704030201090213060e060a03080f0705010f0519150e060d0c03 70
    0x781082d01141540d400e00c0604020710401d08101303251590540006c04819543c2c5191102030b01d0786901c221031024410400003080d0f00b01014407207070024003001800d003690aa00444240c00604c81035042150229002040c0160f01d4041c2d1100d8145a0044407070740c0fa1075031000c110b0582900040c004807072140381804003251441441c050f2040c800524140001d4110307180c24001d00e4038041500c007907a107400900600404889040380d15221180412001d40e83d6400070702410f009221248180e0203080c0361030404800c110080383e103200c6160040040f16400d60f1981d04104580c07c803500b0aa10480c0ca80404116130105402682e501078024000002c40c080390f9008140c0c10080c20340c280340d2107a51010300340041d0780900320064000070291484480c2c141540d84182ea00d100341c000c0c40b41d242c5c40c00326045003000000d401c0360030071100414052155003019181001814a01c8103011003403401e00b284134840c00100e22b0b884088075140d50114189403509020300001c0c201450302642c416003000000300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 416234550 1250 416233300 416233303
    0x5090d0908071514070c090506030c04050f0705091203040b0417011b0f050904050a1e050c0909130c030302010606030e03070f0206030c0d020415080709080a031803240c11072303 78
    0x200a10ba00078008c5000d2030031004060a00042a6070288594501400d0209100906282c44d41c003248505149a41d40024400a5560158401001c80c01e101c0058013003207901d1404c0181c012100b0382403001450219040b009403e9408124907190044012800c071801c4c00d11881c0d620043c0519401d00c0b51030076000ba0007150590310101c0e0f0302c0400c1a1124611854400010300540130b41c0d541e841c080110307051400042100d440b03011000340c4140011070114600001d010450240c40da841502000010ba5900d00640a01444d10660011074070301108092680404001c0360341c1c856021039041c1d42e035402503082150680010380400c4e000c603000d2011f800403a01510050001d41b0710f0494150011a21007001805940b00a00700000c200b10800204103611001424503503460f898208000084810406540c02c0da0490f03002400007507158005c10f14a00d08450421421030301032109001d0203150000503903080454991284190b844048204142d441004610755881000e50510170302000490009 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 416235800 1250 416234550 416234573
    0xa030f0204021e130f0f050a0e0709121a10030203031b120c01021305150304060b270717090c04021b121803010b0f0603060f0405090d090807151407 65
    0x100e6001c03134401d4180000c0d113000d205d000041008181d03804a00b410a00400c911903214841c0081c6120b108022464990080000d5000750043d040281d041800f1400c0c44181c020041a4504245600b040411141c2c00c400140313005032500a40154602121800c103402125548100a002c40c000d1800c1086407803c00d400a0034138cc1b400200168540c548409001001c400c0c03a0f00081c40340b01400729504d19480030509030303a446604844000356001c0000003150901198881082264400401080c0111051002503000e42c0103680c1e41c0c1d000c003500c4068000824801e42e403582c05a80f100010b40c480b8a001c0e001022804a104a9601580c2000032000d103005950b15003881c107041c010600352580c61401c42001c2c1c01240072070080c05000c00540109191440c2c155250340034032400000100305880e8011350900484024000b0402403030492412a240e01d0030310b100800203a40700e5400103000d10002000700580300d1841002000c01c2e80c03002c0645121104065801100000b03100d090003107900034451 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 416237050 1250 416235800 416235817
    0x180306070314060d030f120f0207140d0f0219110301020f0306011101020a0903020405270c031b090105010507140105090303040311030a080424061d060a030f0204021e 73
    0x100740400d122120501c40b46000f02003501401051641801295006070740c0c4040e9500303410300280d060348000140c009000c0e098036104500b0300028a000c10030103000140043d0303903414025a200c00003125822100781421050010040e031050550507240036803583c481080500c0340d09000e40340702c1030038017107420390b00402c0740d00704455404002c100140d41c2206140c0c66101c0120002c51138040706540140c0b50300d06500020740515603440001c0c0020002d62030a151014000024009131444171080700c0e41c864042a000740a0300034520707200d80300c16005422107a805002000d0b032030240e00304001111070341c002031000c2d01e81d541040d448038651942882494060808075024650328503150401806141440006514980c030801c165050907500812494000d84d000801204d006400d01050801e184e0002034002c01d181b9110300010000302da0742d503c0c1d4211400d10303520010707030b9612010403000c81d6403031001800c620300c152010303001850698024501811507c00700c07001044140440c1c40d694110242 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 416238300 1250 416237050 416237057
    0x9050a060303090e07081603090f06050601030f060f05060708070c030b10050d05030d0b01050d0e0105010302090901050f0a0b0a090c050903010e031303023a11090105011418030607 79
    0xc0c070034168044025030181c492245140e08608001c4030003441d405000b8494200d1854440a09400a10039084030561541200b0031002c3e040090503c0002800b040d1101c50120f45015410a01c0c106135004000440b4003140c06070b07400600c0d00041c40f506a0000c40c00712010141005070f4800900141d8566003d540616050034003031400c0303030401c80da6041c9500301c180708442120204001410000c21a000d0406120001c03502c449044010388150082c0c0144035a01801c1015031030211005511050489000302c0b000280e40c1c8500c80482c0c02c842050707400c0c111078200003000801d81c403829001a5006140a8003030310b28075a903101c015040312541c0c1c1c07400c80000d030300040408807031800f405200701000884025502c1c001d000195100c0c0c6e00f006201c000c1c021603081007034000c03400403c060708580d11021444514285907000c2c0c040301e403116001c2c045900344000c800204490520900d014160741040e110881c684c181030a10302c100350000b880780c40500e8082400004c06032428030420b4000c201c0c0d0348 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 416239550 1250 416238300 416238311
    0x19050313150e06030c0304110307080f010c02060a02070804060c0c03020612070201050f10060c020a08030301240906021504050313090e0d0212030103080c030f03010b0a12200306030709050a 83
    0x1001040364411100c010f00c40c41050090060b80c4408100303c81c4c01650144500020b40301010129090000c541d00c003c00300c0c0100d103181c5503c9001074200046540c1c80380e0039141c0c0e035070760320015100f280034954000d03041e140140424000c2034040e01121038258020405180302036a40d50000380c1e01e074070042e0826219880781003030015241c1c09009254010311790a4081600c1d2618407142c135042c0300302e403055008005100c1c8403d410f546403610283c0203001050282c81d9607607101c044058000307d400040082012001301000d6019109002540941d001c65018103502e08544121450118002c1c0040d18140810040c1c441050001410007006003204030303001c42c0c1410310420050a2000002050056400809003184480141c0301181d06503030b40045071986230f120244509245008071245040511400800452050000006020644215510189010100b0040e00c0c02c0c3c0d104c1250710004140d540004000a5203d2400756520410140171542c802d503483c5106026a90180d0304881c001d561607 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 416240800 1250 416239550 416239589
    0x5121c11072c06010e10050d0902120106030215031902090a050306151e0108010e070323060337060b0a03060e070b040e070c0f08040b0a0e1219050313 66
    0x1100d84942c00b200900384030344092038610211b142400000030740d9040140000c0c02e6400300f411a03001c10360141d0007134801182c3c0070b442c6003618000c001501050344504964003d000d44200e152040f240306401034500620211440761044000c1d4200c0020f01b070b0702c5908480089065101040054410142019503100e021202014401c40616083c0040500c55400103002901d0360011901c0c1d044400c204420a000d50b1105070460080130601220003000002c80361098003240f4014080d0301500048081d02c2c603500668005003248074064210007041c10080d20824075100032110581201070007070001081c6940380000141504e030f4030760411038846594048805407600104000d2019101c0d038004a840d00e428601e41c0140000010003180c10403501c010100208407010440740c0081c6d5004805948513500c481642480740c2202a41328005504561175840390707d065440310041d08000805411914118070030200c0901c084d1400741c0b1640310402c00d58a1081028000c42c0040800c100c92100c0310400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 416242050 1250 416240800 416240879
    0x703080a0b060c150c160b010311060310150309050f010603060614061c060506040e04140d08010b0a020c09010603060302100302040317180d0c05121c1107 68
    0x505460b01954060044400300140000e043d400500740300003000e2269140480c030380d21031207840700f4203818038041100801080000340416050343d2140001400c024603007424444180411240e0000c8051400c0042003002d2030700864281441d850315003c543d60045448052800d244000d085040341e5442504009119061040c00050880b4860b05241c0c0161203000904501403989601e0006d81003c0e6450941082d55002c00014000a402503403119074440f10036a43d8482118165411044410b11580241000c034401c4400e07145512452126403c200caa81d4140d0011310004c419886a0103190311b2581c2d6403103086008242c25500442e84505502c14030103079503211680e0009150043c481840003076002071035003001031501c00c07a19481b00620382604c00601d04041c1300341d42094808a4110511011b040d10009894054410341524521454800e079600360b00c0c00c05034059200003060118892184200b03010703010040c0708403024a03032074844200940c4482c5c00c0c03000c03403082070981314400402e0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 416243300 1250 416242050 416242061
    0x14010807121101050901050403051510140904030f09051c0606171b01050d0507110105070207030f020d06060e10030b06010504051008060a0b071506080c030d030507050d020703080a 79
    0x4002080300010400c2c0c0d1507980c04610802000c0c18400f01090107a40f50f481401036a0042d03030071070100c40700030a01c4909944509020745000765081c0e007102020561480b80c41a0401d481e002804000321680d841d00e003100c0c0c08101e210b01c1e0703080090740303007001400b40c3d0381003040e8240002c03c001c00c1b0041105c5d450b1403012034020350b2103140000c103000b00282403000c0205042d851010045a0300340004030fa800125184e02c10381c0c14012000d40381c0818085082da00c80c03940380f4180c01c0340b00208419110b480d030aa03070300c0c901403000402c44001c0400c26401030601052006120b449014041201d54031034880c2001c4540884000d541d844540104000740a001444103400c03880a0030a06d10b82030401020442c0c902c0414581000e2200d41d0001c0360075904c0304008100200b4200d4445034407040d0915011380e0070843c0901c2e0340e1100f0f040c150007054031040404c80c0500c1d0000200107200c05241c4800c00d034050480140b040003403010501c02c0c0001403059000405105129613640c409901c0d0450003082100e0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 416244550 1250 416243300 416243309
    0x60e18040b1906033c1b090e0303040201021605030c04020739060e06030103080315060a02030901020601080318101b140f0c03071a1b0109020a090510050103020c0f0114010807 77
    0x20702c6000c0030b2103080c114175011151500850801100c00c642d640026035202e00303074454904140307064000c401c054401300156006902c01d0f400d854200c0d500401c9821510400d000d00703941908080c07440001854030381c1c0100042d61103404c401c40c5414045030400c1940031165040c85007140c00300140311034507103540c00718009012142483d012100740c0201041490005002c0200460f2001011401240080b0320800300c11130002e10041d500c451f00e0344021340301e03080138280c84d026106003000842c8210000c810b403205200352515040e000c1114000300b24480180c5d9500d1020310a8002d500300782480040c40c5052541d0007102c143d5a040e0724208a2854034503108800a901d400c0f604003524680e90203e540c2085a03220001540d44080c5a503454105c0d10030382050380c01c00750305080102c00340c2506412801c24035000311120744002d59112241c0090740d0f0116909404100410001d1140358003039405000b480800301308460341f0184c05504e403802c5440040e04241241c00d94030040000b04810800c08020b0f0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 416245800 1250 416244550 416244623
    0x303120908041205030705070b0d0f06050303071b09020d02031506072001020c060301030c0e13080a0305150402120402030606011803020411070c0906060e18040b190603 74
    0x315140d21410002d000307a00415429503140d810705402c2c01010020380381d203250008103031900306a031802408030780d03406021165281e07400d2500701e50110751030744150800c45138041c0c06545040980e0b079801600c28070b4500fa07602142c2548a001c05c0481c1c46101600f0450185140180d99003003003501050000d000241c030030f1040008005500000302881598801208040b688015a000e0b00006038104078128000540190f0b000c00000700384190b4444400407035120351640c4500d0389514082c0011110000070180c0b0f404401c01a0704102c2d44640d01c203a5210344401c41d1491142c1c14000044c040e603121654030100501220144010762034140480c6030800b000f4200024441424501040d014450f41300282c404c039a5000c040758050340043c21241116031048100104680f00d00e41100141114041e82d00041d446031000c00543c2020806944541020328800c031071550303580d84841e04054018101820034000c000140070115090081c0d201441c4249034420070710411040b0700340701301052400c2c3c0500 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 416247050 1250 416245800 416245811
    0x9041505030d18080a150b030a02030d08041b2d180902060903030a1812020901170a0210050a1205042d020303190e090c19020705100207030312 63
    0x3981e00000c10a02918841c28440c03070303180340c80b0700002d02008103030f11111050240e41c184000300811035000030303054820b000040000f408032000b41075541902050007505035104c42030080c5071a000c0c03102d09038041e00c81d0380300c4d10f499030821492018032815607210341d00b0020007422501d1032090044510408000402c201d038074407440c010414000d000ea10b0900c5208641c0c3c2c000c200c06540700c4004540030300d50082c007101ea4820622000900043d8800d40000e40c809003030318081800301c14003c80115181e001004c1844c00d900b4060035000c078480c1e401040300070340700d0f10000c100140c841d103003190024001d0b0f40355a0b0329580c0e007034006481c0c002c1d4102c403592090b180c03800f00400202c540d510b82101c0c80d1a00500c2000711141485d0800d8900c0840010798184400b00303004038044480481e2540805250361aa0b141e00315010510980540c16241045048000d108441a40b410610141140146031044454a0303642d80041000c0c00c2484000da001600004010b005041e0428100d0154604041d400c004 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 416248300 1250 416247050 416247059
    0x516050a0512092d040f060f03112403041e0f210201050103150c12050118061e14130608010203090f03040f0b09130f0e100c020a0f080c0f0102090415 66
    0x41c943c3c0903451648030719a0746c4034186c910003041c1d00c80e40182c0340c3d1400000030141c49003412800040040640e40c4940c0a20688140c841141a0403002c01e0022418540c1507480700d68072020408018102085000810400035012aa40750aa410b050303000c0c108087d2641030250f101c1051409000200341036a0409004000241d85650035600f000000b090000e1080700120044594000c03444103480741d1801d18001294003078091072411641524031804114847ea81c0703002e071903102542d08803038226500c403010401c03614140005410305040014280b164101b40043d001d1300300d4585400000042c0c5d03021040080c660302c100700e68520402d0380701c01141461325021740303200700c0e1007980540409644c0108101805480e59841d0441c1ea5001160900603440d010812b0b60081500c841010007511038600f0078001c03804540300c0c40580075a80c1d8040c4c200020a91591580c012041e18200d4044500f089041e0f50b54405000c96407450140c5000541e80e10030340410001950041e0b1305250041c184c5050421 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 416249550 1250 416248300 416248369
    0xd0b031f05061017040c0b040311040506011d1302090d031101050f090d030b010302040902070506060f0916080612010e0706080603061e040c0b0d0c120203070516050a051209 76
    0x7000c3c4025003600c0084c43e0b9071480c020072030740346a601c4840120800306010003041b940f49050310b1042e0007501c00300324642d40c0740300442d2014031142c1c2c240392091003081e84010f9400c0004a00c04401502d2001528296280300803400d00144100c0540008014020840b008002070003065008031701c00201c40c00905001c40613540783c0001120200c1415550704540e015a4020740507500100451038046440b6415820945d8032401c1c101c0350b03588101499420106e01b072404010301805240842e168201404810380107480740c08024040b194000130424904107588801d00800c4440e220300000340424515104016020010140c0007511070f4020130f040210028203200c8c01d400110380c00030a01c46985841c102607050004540205010300c9000801d50400c9a0036000720031070006a43d00e02c0500042e8a5480c022800151240c400040c02000760382000c100d50380542c02e4141c020070545d041c1840f40c0d0303a598070f02001200d03002001c01000c141029140b4000d040c141d450701403003902c405004100e20b1340c013 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 416250800 1250 416249550 416249567
    0x91602010e1f0506030705152203060203150108040825080301030c080f06090a0204090206280f0302070507053601090e030c06060112240306060b0c0d050d0b031f050610 74
    0x9038102d4404a050b000c0f0f001c40c000ea89c1d041c0c458040001d6038103034482c02c1c010069801115144c05030058003e1000c50795101c3d005240c891034102089a040051902181e24250303c68008911000c01040007031012a854000450003036205134407040c40e55245c80c08103400d14842c10508003464000d94100100da500100e25070751426411140002d0762440e52000403002d002e121a00301e410459000e0001c400f4150440414070308e000b6482d003081c90921040110181c3c85184002030054000ba8010030407030070076035100c0c0601407038010598001e01c03d2603464440003a5040c10b200bc401503050040207540142d12842c0c0080080a01441c41c0c0031040303881e99503a80c07000d0034050400400c04040101082d02e80e010600320410300103101040c60705071a41035200c16044c0800e441700c1d0320307011000950b1040d0100311110400f00e000078207204070811030140d40e640c00c00003903041803c0e142e0564041e04d541c14801c0d0760710320410212040c0285c41b803c8600301182c2004001d00c1c002c45100c80c01080c0301b038000145 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 416252050 1250 416250800 416250829
    0x9010303050f16140f01110702030a061109060d02090a050f0619110f0a14071a0a12060305010f110306010e0f06070204051006140405091602010e1f0506030705 70
    0x281c3d82e2070340002010380c0140c0d000360000d000040042000c3e43c01107800b09811030268101002032041a00c00303840c111113803203540e0000b50305a02108000000841d990480c202603000000a00d0a001e0300d04003240340f07a0301c1402011521a4001506405842c20710800406454107840480d0208019808683d00707100d403104803803410f981079280c41f0ba100c4c401c1c00400f01c0c4aa0b0b00c0c0a83c1c800c2c502000c129543c9440d08102126012802d06a807484110001200c0d0115205882058802c85d0b01c090081550740c040c42d049003c004166014088404003130041c40d00441c480d07400042c00d103080c0c2c100309080345c4401010710150081002401030980e444462088416800c841c8540b0801002000600385c3c41a036500075006030802080040c00207040c10b08800302c0304a62112450030300c07000001c44603440b55015581d40700e00e46901285070340f004800300115452540c000051300820000d00c41d0301d4252051201030400300ca143e6a201605400c0c094590401001d03001001080d0410340000e1548080c03c08 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 416253300 1250 416252050 416252077
    0x10902060f0403030f03421403060a2a050424081302101d031009030809060907031203021c0b010f051213290717060108060103050907090615030b0901030305 69
    0x10900d50300d800380108075070a03000d030900b03600d80340d2311011a075100c40a403020908c00e000307010000e606e0071003902902004400040d001490300034403001c0780300500d00c00c00e0443d04024043c840415907541e044d0084040030788400e003c422860744144000e2202c40d000b0200300301206440c0301c040041c0c8601d40b8140e4002682c2c10000c903030040503403030090034641c01800300d40e043c4100035102d42040c0c42c07640900d2400740655528441c55680c01c0c801aa14101560040030960000b2005c1020a00040d0f00c201070401d50704e000351404c01800d51380b03c02407450003803c1d6816590303040c2d4020310f5070300000d0740041004541400d03070801c000d00c5220129204002d200d12002d408600600c001c205400580048501041061012038804480414410f180c222401d1000c20f580d0511401c07610625601c040c4203450594503103090f683c0b1400110060000545a00b86c18030070318a01042202c06400384c0e0010781418160b400040001c1c40c00182a1078008412a01400e0820014400b20790300104a80c800104003c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 416254550 1250 416253300 416253371
    0x527102d0e1c230c090402180403020d0e010c0b0f0903210601030b040504080a0f03061211150f030c0703120501170105070807050a0305040203010902060f0403030f03 73
    0x941034410000c14809035521581115184081442e100c1c0420800ba00071110601c0441100060f003030003400c0c0d80c09440040d801120041c42c20710303040c0907007076105101814036120f40a8402010120b08402c0e181140541c001c950440c6151b6130080840d12000303c2441e041e07844290743d40784c11030300c5000508941000050500002c0710382078201f0031075400b00445032403002c40120300740c21014500e40640e0224002410700d2403e4030301d032805000d80e42c00303079400c48825440c08000b0314041d030b2101c0720700c9124802d241e1901000554075942c0fa403582d1a90f405200800040c024000820107803038188040c0f0603c4030820b110140c00030a0b40002d40303500c540c01150b00760b595200c5003020784019240204002800f400c100010603400802d485030070f13118810800a000d1340d219030f4420b8450a400300c03401800070700c0511841504a110307030080c40e00b050018000044d41c0b00c40d9004601994010f102026110000242c20003c05520000000c03084000707190130030007145025440c109070908400b0484002000c0d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 416255800 1250 416254550 416254637
    0x5060d0609050705060708120c0415030504031e0203040e0a060f050d06060b031003030f02010e062206090303020a080f090c01030c02010209370b03010e07052710 71
    0x10481c040140400500403500c6c1c0303805103084000c5500c900075194030900b0300f0010400401d0440c06503800c0d0f13084100c00a610b103c210100310b0050200820580800480204490b00300c40d0400004010566541c042c541c0e8a04018040b45100005040c01441c94944042041600d00b03c602c100142c034801c4a41888135000d505010020f840303560000084c0c1c0800100340007130030703c10720f00407400c5a100741c03a400701201d41100d09030300f00d5810ad41400421f4001400003074210240c40c0d0340302111030700d040341d101a20502b0b0302c80c10308840c0200d82c12004650b0000f440d111998220350750300d81c0030380d000c500c8001610301a8880340c1ca801244409505050b214110140518002e4041e54030341103020f0b000c05407076002100130000880070110503403034900707500107002502e00d100035030700d000d8443d10b6540c5c0b46141d185c189420501c541c010140350410a0520511040945024102c1e504000301014001e05950540400907059a40d005c43c6043c00902c2c01c4001a99801d4540c802d590b020304954043c844005 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 416257050 1250 416255800 416255803
    0xa05061812010507020105040b0601080f220b1e090d17100806090601032a1206060305031c0507030507020d121d0a0506010501020a051e030d0f14060405060d060905 72
    0x40d40d4000c1c0300d50800d400c0180c100d42c150300507407240d80034800d501507548800c001540c59403000c2c0d030f0303080c0304401c441d00060001691003207110511005500d4500e01034240d0f00ca43c4040380041d1280700200040e20f0107400455135114400e50446850ba01424030b448288101800099098106860381d080442c0000e910035003500c2000020503105080e1510741c5001305003503444150901048030a0b1425500c0310202d1315002c41d004503c80f2a0303007114002d050034100d07180b0300b007604003404075500350b2200e00101c0040c00c00d00c042e0543c0230154403004000e00c81581340700244c9a000340b517078003090725040401858581c00075065242034901d0802c041803001c40f500400142c1240c01c584003815000c00c900061004000440c0310115004400360343e80ca07621131004903241c8812103070180080d4040c2d4400046100380c295070500500c523480c00c882c40c000c20021923400380c8004101d440d44407a41c0302802944414a00d00a42c0e0104d8101c50410003450100c00281d80c10b5a142c05c00340c40b15a0701e503141401c1000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 416258300 1250 416257050 416257069
    0x1505090603011a131d0718140d1e031b020a1206060f0b090109090515130b040c110c10080c0702010201060308030405012a090303110a02100302180a050618 68
    0x81d9003440036041d4958130f017001c0c0000d1001507003031102c1d456000694203070b2042c0007100a0310f0000c203108a40d1032504025103494016001d840c0c4d07002040344800c0b0300241c2000003680690209000002c8403120038103003d4224034040c080700000542040d04600160303144809c460580380300140042c4030080300d080c42d100802d00c40d08090794181642d4400b244804080e805065980d80c266240515103072600c0c411801d40d48161141c20301030600708900c404a113400e5022220100b0201c20020b03a09400c01d00040c1940c10350303145840411318040f40308003008014001d51140440c10360300034603000214080107000d842c0081407881440c07008a00c00c01103a200f0f4018000450700070710a47e0b220305140c186079000703001c0c42c00e01040741014482010f45802080080309a89400b42c0c13155800289942c03800d0303512032007000790856540a111b11050051340e840010f00c240c40741070b5500507115030020320591030210f9401041351003103003480c07802c11190b5100c400320b0341d48118005c5c03c0301030f580003000230411162 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 416259550 1250 416258300 416258317
    0x30705120109020904151a091906090e0a05090703020f0a0e040c080d020d08040803060f0d0506100f0308041418010e0f0f06090a09020f060a091505090603011a 70
    0x203164000042e0304116802030700102408640801c4801c0d48400160b8010f500e81c0b06d4401507901540807000f443c0c012201074910f082c4007800c1c200050120708070a5410305901e400c99400f00c0e11f458070900484466515043c1d100c41c117480100840d06002598580d05c04c528440288100050b0107624030310707141c4105440c0109060300705e40c3e000c0c0c1003e2900c0c1c01420300c7e60041045074850044d203010441d00c000b50601c2107480f03035180c0b64040c1d140c42d25084c00a6200810094220f0302110354040384d07072540e00503a5078543c05100584114181030b1400801214560300c241145042c4280034000304030038a00320b80865040c01038901c42042043c0104040f813041601a032946180701c030000038040000d04045200d9495941a40c265554809441240d45816200f403500118420000344247e076960740036816090000f400c901f80c64031500c0000b02e40364080110a00001c07128501041000c580c0200000c01c04007605095080c42d503c0300101c0c550303000520450f0703000345000510220701c1307403610121180203 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 416260800 1250 416259550 416259577
    0x606091e01020f0708060411090708070806031905030307020f1b04020c010e0f0d0206010501051c0c03111303020f032e0605100801050913230f01050126071505030705 73
    0x2964541045441b204101c0341541e0034414003540041500d0250469440b903022519296802d40303988400b2a100e560082107943c041c480c4190540001c1c91070802440d8061103030000f55038034601050003d09190481000c0c4903251b010b82c4000005501c05c0c0200d900b02c100a5400507111040c504607036001d040c25400c105024040c020406801e00c40c04180c100010603150200e803a142d985400440e003602c14100c00607509100f04850564142e05030f08070400c41160b42c600481c0501002003650125400a481040c0720b10041d4810000c5040c0700350070701400300080b8050301500c03240301c1d841980d0380d1143c43d12003080ca01100001e40281a140d00003809020b014018120f0300110410103050801c0a001d45440342c90f515000441c55100550042581548039104018a812403141404101019241c00034240171f078208009040d402403040500034690190081d02414405892160380080c03480d0b68000b80e0043c2d01c06000321582995003001c4040b080c5403c565070703514030b10f04503158000ca002d2a050b5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 416262050 1250 416260800 416260813
    0xe0a0f120602071e020901150f030207030c300804110d020a0803030708250c0b0c0f19030c0807021c0c080a110d03060302150a0e1f03050606091e01020f 67
    0x3403c1c4813040080703416100780d4007001180d0b05e03002e410240307510401d01c6a00150a5020114403d4071075005401d010388a800c3c500d041c042d02d95140003400700c8003100e044c0c50929030f025041030035401403540e40036081a03007852061404c06448404000e940c040c01540500e000020440442d26181c407003100921020b03041e40d8690034040001000d011003920f0800160f0320a0051146184100382c030308100d6a901d490f0307880b22a4041d03444044c40000200102184003091105405038240c070802490441140061403491080c10350303015007100d03034203030244082001c0720041100860700003461080c0070f07040e5140141a051411300031503101c10b200704002c0ca1040040740040800d81c0140104d030086c4826410744041c452800700881c02c60b00c641c07002952058401c0c03d0166400b00d0034000384020041c40c030300031440141401c08541c5c403081030f4004001034454942070807881e59051181c00d81003803080710410b144ca44003a00003082c1181c0040503c40300c19a0352102c3c02540e008100701d40400c1c0350002542d08 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 416263300 1250 416262050 416262083
    0x1061532030403050306040b1002191407030507030b09071a090310020d0b01030b100512180a031d040b06040902030a14070c0314070305030117010e0601030c05010e0a0f12060207 78
    0x305c0e017042e52510b0140d810094107040341d1408100107178250180d0380c01080c114641b0030500740049d00d040703c140c1d280c0646165109210300103000312006540a0070042001524614002580c0707607006000d0103007a005107205012180e00f900d032011124806010107500d0340714003400030703050040000c15400d01510014200c0541d0754142c000c00d5140c40262030400c204c2c00e0034000e01000c00c0240d0100000a07508110000c004500c4038540c40c0c0000d81d420290182c15a00490b140c075024800c801900494080014620316220400c50740042e49415501404024201800701c1c046000310b001720100103401200189030881d444c1e011200700000b5001008990400382c0340541001c03680242900000c100c004006040082c44c01207600b12030b4980e445500c2c40c0c1c13030500b0030f41d00e800307014100c1e030507554031440c82c081b0420040003c030340070b14022942e090840386007100140100c1c10021219004000c1d03c1c80c100404060a000c8e84212060307251a100c60f2074042c64500020f205a20b402041e43d84107141c50389 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 416264550 1250 416263300 416263307
    0x17010b0a0c03140f031314070e0703021e0307021614060a0c0305120411030f011112040507030f03050a030e0c0a090b01170406051611121c0c0c02010201061532030403 73
    0x142ca0a009807e04007082d04003045041c0c8450850088410704a03c00c0c0200d59a117102e80c0c010f2221207100d00f00c46500030f5948209055076403040d24800c00507845840c128031a401032060302002407400b260080750000b640380c0828011701580e8446814007402c04500e00603d4015400c0303c0800900c21700585007881d207450001d600d0944400c0c0b4600034400d011041186260510602d24450381c0c142e040780c01e04410411401582500074000c598501a842c40000000d5074500364000c0c1030300c661200780c1c507901485802422544186403404c0e083d8000250b05d20a600c45402c400156807900c2d00104e044500e030401a40d80e4180d44440540c0d044810040006000c6079502040c0074503004e44141350810210a401c443c903800030a400344480d000803502c1000f802c07601000384500301960f0b1400c220094200703000030407500c013170090b81d020070300d580241000c540c0c1c203210784e20142c01407003114100f215526500400c1c4c4490f6200c188140e81c031180034102170019007141940e0300d2203404080f0340e0b685414a0000c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 416265800 1250 416264550 416264581
    0xa110c01141e0a090302240609070e0612071e03020903060708011d04030215070810091a040b0a0302192306030a050406060e0717010b0a0c03140f03 65
    0x11007203241c200002c61140e142c0300707aa44040e845407200c031103082e071212801c00d4014134050508074207501c90884c20003807050701400c482100190b00001c0b100d071441c110003030042000e00104403034100101c8080e00b0360140c0c0c546040c0e0f0900a05400d40345404d0307407400390039101178110503140e0341604545007107008804e906400a10a510059041e101140c50752107094550302c1081c096101c151482c141007035101e015107650960310038000d1044400c4480f402604002c010015507214000600080400031000400603691b0002c04180008001802c0c4044107085012511500c051003182c0f20740000b280741d51512400e202868005003810708082c0c082c181092034015500c00e41050300760070403030550440e541c00c001c4111160042d10252841c0c0c0c07900840e40081000410440d00c0d03658683c40030030b082c01c0300100700c0e11031840c17902c1c1e0803a4502c000f00c15030380030720059001441d00c0d42c040040d003181503404070500c007446600d81011034010f960841d0514040c05600c031800c8411178044104281769030030014a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 416267050 1250 416265800 416265821
    0x311100204090e0a050304120503161406060d032f1002030702100605060901031119080601110a110105030c042106180209010302010e030a020603010815101d0a110c01 73
    0x1041840c1010f4880c54079000181030142c400c2c1c1062008001c641c80c07510140300b00c248901d056a14042003811084101d080494094400c41d0a6000ca201e11020070000e00da00203008461200450310f181d9002004801c040404a85002500840400c510000d014000720380c0059802da03041c100080c84954025002203c0c0140144240f030301d8400d039807009100e100191080500980d03c0c0000c2080103501414441a0010f418074040103201c0400c482600d00c10300c5071403143d80d5204c0c1401d061000400d5820714484140c1540c00102400300020328170b085440c9118420300b80300380c03640d0322460030740c0742c5002c0c90703108461b60007030080c00c482140c980a440c0c0d9615449407a003040f01c01011000041c0034251103a00940142d02c010040c00550b000381440001c03c2030007421160114041c0d808500903030002c0e8450714043d4850b45100060301c014040c1d480d808404c43c034010001600d424040c04180d1015074440f81400038440106010b0034071508550034500394850075a039690103030b508042c02444080032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 416268300 1250 416267050 416267069
    0x1d0c03011107120305070903060e0a0b181c0201020c03040e010602060106051908060f1e3307020a17030d0e030405060d020d151d0a02030606030a090311100204 70
    0x54680501e005205440d0764076000011104020b840400c00d400601000d4846002d00c0a00b01c000000611180203010607003042c2c0d07015140720205490190000c4101500103110305d861340203d8014468009000c0300294a0030340e88a84100e50180240e009100d030241d0301c0b405000024000c02d025041018403812551654211100c980e40c900c03044803140101c440c42c0c0d82903142c00c00c07800203040c8900c103230030b4105400920580c6540c14100004052010380ca4250598001c4420303103402d6460301003107035280c00b403000d01d41150004843d00c0b20490810405917010541c01301064203419500d07a042d5502c09044860f202c03488003801d003216103603a6001428004056400c1c50541d003000113021007aa8119403001d80640d040c1a0851880c101a41100301400c50140d034658a80300408400c0030300c9001028680320500922084000070601c0040052840809500410620000307880d114202e9601c0160710300c0001e2051000d00e41110711290f0780c0342d01c40f000e20460303039008448400c540c0140b0407510900c5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 416269550 1250 416268300 416268311
    0xf0909011d061509041e06090e100e060c071406010e010312030c0e1002010227100804020a032003010f240b030c1308030409020711010305060f060d1d0c0301 69
    0x10403c01c00030240b51040244000601444c60746013419041071016055403071807008010381c040d6403001103d405604c00304450383c0328900304c0c5114009003c0080401c251880600508002d0815142c0e1035002800500d24940b0028110b801d01c10320120600880b1440030640e042541d46150303050705031174280000d50305803131032131001c00d105c60103441080242405921645c1d80306440c2c00c10050218242243c850655408200710105c0d100c24080455000441d5203030715134101002c00601120030740c01e10074141440322078010b10001d60740c0e8058041c1282e502810805408181010710100074821902054241d1b0074a4407210541110b07822083c10a40000e1810f41188402c4103072421021551080e14603c0d00d00f00046100d20b20f00380c00504000c546854039a2089a80304002851079010361301c90240242e01050702030070800d01c3c85400640600910703007800241400c0e4006045041c281040328847e101c00a00c04024080d90780010498030100010007d112114540c040d0f202d0107040740240c480e500e800c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 416270800 1250 416269550 416269561
    0xc1204090b0109061715061c0c020d091d07030b030a050109021906200307020a0b04050a0b0f0313032105010e060306070804031b1401020a08060103110f0f0909011d 72
    0x100010000310700c255000001039280d4521b19891a03072040c0b01103411400410280c000810340445c100c1100d12521400661800c4c00c0740002d0600c0c2404541604000108504000700296210200c19480c400b800120031500c980c002a0010f00a40104a1f058000c00001d4020b008040d0b0103070080e14000d0f1002050700c07861f00b0390303805003251a0041c00e010400402d0302c120102d028080014030070800c402101e1421a4540000c0c08166040d84149480c000018040c8600d050601c0903c0040081d0b2041c282030000c1035980c6c0781e443c000102016621280c0744c2203038080c144039400200078900c000d104032564000c010700e06400707000c00b4024413a6004e2000d0100e0f07100d0030b0008410380305805585d26030a031a11a80d404564003c0700400d1a0701707a4090f0130740750000c03c0d81d5810242d00340748141e0005039035102001d000703000450000d0249041c94541201900b50241d400115260055140e030490342d5001a03085148040c0282e0345c03c40e41202001002240c440030080b50041100f002c1000b0800e260341340c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 416272050 1250 416270800 416270807
    0x1090501020f10110c1501090b0607031e0c0b0a0218100906050c1203130b06090106050d0e031204121719021605060a060f080601050a0b0c1204090b010906 68
    0x501040d12070b55070019a62011056a40c0c0c032101000c0c481140e010714040300307140fa40d80fa1401003202d101d00f6030b4002004010b450064864035540040944100c1d080c0140b581b00030305040b02d070508030340c0c00d08030450f25401c0301803007a0180c0b000294454103208840c01d01d4101074000303420101d4188150414901d10b41503038640305085500f0764201d0f5850040c00c504100088543ea002100c0850b124410000c540d039001e04a0400f551180101002c0840a152581400004072101610362402400524014003643e81d22004580c4221442c40d008a07030004641022403540c0b09520b0000010100f0409101c1005460380c01d0b41408601e9030b80b03003410126003c85d800e4109001b6903200100d03e03003602264074a003425401910280700751044081a1780060744456040280c1211000d00700d80e40e91009001a2000000c81d0015000324001014690705060120354803842a0141d20000c2d540031800c2c0c00078400400c80d8079034610101c02907030303101c2c0d41e42c842e000060b11860000f1404100d03410300110b002840f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 416273300 1250 416272050 416272063
    0xc0611120c121c0509011e0c09150216030b0105032401090c05040905040605160c030215060a0503070b04090c050307051803010b0d05060a05070c0209040b07090911090109050102 78
    0x100c02001d0054800000514140b40d070011401101c402c400301c0751203e000c01584075040c404d4550b480040b41165074441510140b64800014030350191a00c200680c5080d40310b05803034141c8500003011012880c0040040e442d140780015018140d0070b0b50301000c02000f95541c160741c1200e600740e00b16201c40001501040c0750740441c40c42d040c3d0000960300100f0120480e80c0051a8490303940c2049854240c81e601000141d4400f120300b6201a616a0b040c812000b00614050070189040c0c604600d481c0ca4641d002900c5001510100d0944000d800106800d580c440c0341c00d2004080080407112001d940d088400259086807281d4801d081c98090550b040c540124100d9200d0b0140d59101c924150f005604401a400340002141d09990f0700c0460a0b5079846031503858030203901900041000385404e03907445082e5080142a47c0c200400941c0b198016180c980d039007504189e120180020560700d1807800c507502c800f56840059294105041c40b41c550606600406e45001c00782d80340415543c4400041e0394424 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 416274550 1250 416273300 416273317
    0x5060603070c030e06071e0c090509030901080606042606090610050d060f0c03021e070b04020d03050c031c0b0904120509030f0304080304080d090806180a0c061112 72
    0x39a0855400e0000e88500f014018130100142224148042610b51000030003003001c58001600640c900c990900904407000401000c002d0011311451802c444900e840b8060b840c1030906203c61075020561a03618101568050135890800c0184500103030400b804908001c21810007500494000c148441c401043d0540f00f94410031340410507503d0001400b02c0c410070200d0565005a9907019109116418040c0803d03080d0309540158440c992030815407100c04a100b0040c076091001c0010034000750030400203943c8681c046919000420340d60805980621800050940c41c0c00006440c80e0880c04000c11a07500c000c0c036075000c000240210b81400501482a50080d202c080c1c03c0810800c801c0c45000249001e400c06000e6602484160400c1031941d042078108a0164002050601240008210b103040010300c52400400d46807406e6065600c5000242c45003200c5044600c0c030444220007040703840c02c201d80c803d001e0148665a0000144080c1103009441880d026074044001a44140c000350741116 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 416275800 1250 416274550 416274557
    0x903051e070b01122108010501180f1203050d0c050d0f0b0d0204020c120304120809120d0207060603140a0b09030f090405040c030803040507052707140c0703030c060506060307 77
    0x60b400e100195001d4401d0880031214912a6031114410340340145605901c00030359200c012055060800140855000d41800d04ac101501c680c01c100200d01e003407280c3c0480d200c01c00d40c00d07144070481c10101c4503032199250700c124550134075005608440c0d021004016943c0810410030607841115030100a581ca0381104607408140c0314404409441e01d03030700801544100c2002c85050403010165492a900212001d0381c1c45c0060034900408103030003c064030351183d94140540f80c400d00301c108903c4140201d000c401c8250758045013810411041741d00c414051a00080724800fa08460340305255510348a600890b041600f1710040340a521000050f2140c10790b4a252950805c076540040c000100801401941c620092200010100781034030005c44c05107000b03102600700f440c02d00c1c003032107040c070820aa05090120a403906030b03904902500c02a40081c400d01e44a482c82c00c0c6161a0f9200d40103000580b8168082d22030700108054205100351600c9114103024004c550302c0c00700b04000c5000031169400070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 416277050 1250 416275800 416275823
    0xf030306181e1906141c0503040603020c0c0d0501020a0905010e01170a090f0f0521370203180d0c0302060d0e010501140108240f130903051e07 63
    0x20380c0002d40140d4440c0c5500d03d901a1071031580700c0075081e0381865100c20808050401d0311409400d1a4103070710140b0585d0814019032183c03956445550344614031800003016030100e0300c034003c501c040c03044c40701a400003000c00303071007104a048c280e0007035000d000c0f0f04000c18080c2d00b0004003540180007850049105031203218603944d800000e0712103404000c2ca400c40c46580c0b1516072002640c00f142c80300c182c5000d0031341d1501da40580c0ca0041d161524001c0e0100b000810140074010080c0d40c0003c98829603210200480307031000694480f901008079844036a0b0340d104070ba003099a0f03580e00102401d8000d041007441d1203801c400a080c84804003040601070105150414180054140705008081c42c40381c003100018000342d042ea17901e084680a17013010094400c0c00d021032181d0340e4815890f07031b000300c400c2103412040f0030f4180e940b1650482d004015405800c0384840010955141c0c0c003540400070903148140014001450002c0c09580a9808042080742d1002e21164000401d0144c03206070354001c0c1e0341001d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 416278300 1250 416277050 416277091
    0xd0206100902160f0614090c030604111f02060a06050103020c030a0302031e01090f05060f0d0303230114121c0309021c060c03180f0807060207050f03030618 69
    0x1030f40c0602c2c030f8603491030140e45908000819000088480328000c0c4030000d8070416829814031a1207000d40781c26010307489804652055540410200d81007a4841c03201444401518041448006204170100d201181d0010f040c01243c1c0204041d071240d042c5800c20881c2d95211030042d0101c3c0265420b0001550003480300b10440d5009500850b080003000780c0309040700204001e003040c0110241c021804094480145141b01941c5000c5e00d50405411035040b00c01c0800380010072268186800040c04140e2a40480c82400c40e004454204070040c98403468415a1100321184a289140710210b01801300c83c0b80725a61200702150480001e40514950903c0d200c10000403005001c6884069034007155505940c00c1c041124102c800080344214000b080301088804003a04451100d00a400d102d202d0243d100002243c540d20880003c1d80090310503114075003814018024091300d8402051031103004110502e614002000c0d6228030b600b04c401c0000c86024001c4111409002c1d0f61410810070242c00102 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 416279550 1250 416278300 416278319
    0x31f080f0a080309120d090c0b03150409080409020c0304050a05060f04060f0306090e06090d03020301140913020d2a0e070c1505010b070b0f01060504051309020d0804080d020610 78
    0x1034008401c2011150b413a10074405110341903216a82d84211290b9801003142007000c3d41c881d510041009e01d10403403d514258480400301401c040480b44119a2510500b04008001c01070303030080c00d0041d000b1503c0d030782d01000032076803a4054011540310710f200d11000500c0d480d1490032140800c0c00b07100e900341000d00d0001e0540701c3d8a40314050700e040c16120b000118a00080748550020150301710001d00d02d40c02c00a00440c288418001c0761010940100010b00c661100c18000e000c0c01b50b4182c0d8001e14a40d0346482c8250001c6030150000d40c0669400043c800748101c16039101101038214004414003961505c810000b80d503580b18200000e182d10001980840c056080c0000301ca0040d0f0505200d070b4800302d02c1c001100c2007600070107051080421070106120078a01000c1e80704102140302002d81d4100704002c0e10501441c42001c1c0f154100064110041503640c1040d8810780d8040e10900f400b001c1403070041c142d60450300410f035481c0b00301107002541900c0001d840b406011042c860401c5241400900b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 416280800 1250 416279550 416279557
    0x1c0c02101e1a2d031c18140d050c0904050705130b011d030a1a090c04020708030406021c090c03020f1e10091d160c030210020d06030206031f080f0a08 66
    0x40803140340303e40baa0407040d18140000c082c83d4501c4d0700d48580410788000060f00003000b01200c05800c000440f0240f15010410782200e1812800b140e02460000702483c01501d4150b81d000803e8200c284901440100000003a900c070a583d82120b403001051085c1c04200c0482e040003048a000481a4000c0c1d0a110034403011000708400c040d0989928a0158940507e01102c810401c1d440b40b441d08100010700302c06000402441c0b078210b03411761030324280d43c440b84194007000c0c201501e034550001300034042c0200188004401001000244940c0c0151f0515074000142440160b0283c06081801022071400b152050110300380d0045e948503854280c000c1c0010002d044030640b05100e0450004a0304100f003038407002c0b66a4081c41800314915040e5000e200d056000b400c20001d2054184245002a4011410034404091080e0040c0c40341c181d6030003d0040d0001b940081e4000200100f400460f8149907980b0502d02041c241047c0000d985000e20350741c61081400300c28041e004054101c0000e150140203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 416282050 1250 416280800 416280859
    0x201030b03012406020c090a11130308180405090316081309060807081212040204140403080403030b10270e0108211c0c02101e1a 57
    0x110389104201080c03c5614503854580600800100030203410380702082d207005405603101500708003180b1800304080d80790151074055441d4903100212000c400d070b034043d1040401001d4039400b60583d81e0420904035480500d10b52506081007024034034a040070b0041e070b8020a000c40c0107616000030070308115100c581c82c601c2142c48080411915200705000d030307401c10251242200019459203030002c050700e400342a500903465500700c2c0342c9010a8282c03000c25144030140100070b01030b6550707031031001070020000000f200c41440d05210038041455844031045100d1407007034604211481d01402003041951590800c00c00248054800004c0507501c0d0700b1202e240c0445075075140f45982c480c0c1c40c410000000b600031500552116200545503400019081245146000d03210310300380c280a2451000c080482d0341c02003e584400c456084c0e10310810005002c0319219404009a007a16030040074420940445508424103100c82091b6141c00c0503103a02301d010300107140024038260409c42c6211080c0a904 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 416283300 1250 416282050 416282057
    0x20d0609020f09100501081e07080718030b0f07020f030d0c05040905090309030d030b03210c072306190806060f0c03120708040b1803040906150201180c030b040201 72
    0x41d40441501c8107001c0a010382c00c8861207918981c00c1200041004070020012300c015807400760305c0d03009000c02e205001d400604a140801032550b0345041615001b2104030700c030b40d07a02e003079a42c00810300040c07004e03c41c01101c514807c202c040d219460100e039100b0402d8200540c9800c100192a143d918039800009150200c0c20b045041c5692100420119002240d80e08025080082c0908940c502070000301c03400d9429050402100085401103aa0f43c22101034042031426440da1a41d406040351b010b46c3c580f0a0b15200700d900360343d2200f881240d5060558004100000e8850200d5400e00d40402aa800054029040c1d00100344141084618004c05005650403210400142c04102c110500601455140d50002c543d00d0690040c21208100010941c500b08007401c4144000140803005e081d8000341c80b5000400140c80d1a00e0842c01d512555202030ba10620b4003a00184900341308440100c20009600208074042c80010804a42652000b00412944045130240001040351601d29000750040c507 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 416284550 1250 416283300 416283319
    0x1030e011107020102010605091009051302040c020d021207150506190e220b0f0604020d140a0c2d05070b0a15090c0c0308041b060503041a04020d060902 67
    0x240508661400c1e41e00c881a2100007404025540c09001e050000d050a03504080c092604094260740c010690007107000c41a1602d01203800c0d503280411034000b058005204020400340c0d58070296446448032030040242c015202c04009500186043d5050181c0010101ca13a001c52408141d009080003011164000079042c0007a0102d84844503800c090015000c000555040001e5205000880315021441c1d150b503050502d4005445d880c5d80d079400c410b10020140803a1580382c0000c0190142a8203840c503540f81440110050040090130f1703001d280003c00070000360304001c07012622140682615581c3d194410f0f50171070200320f0580c0c4250402001d02d400c0f818610309695001c0d19400c2034511241c416120010283d00e841c00327201d000014030410300308004003205800c0280c204c050603907018003844521400201803200c10704045680f6050001c6c0494030540302c41c4050040d40056030140d40610745840710341c0c41800c0e0401c1c211300072600200700c0c6a40062660340c100c060050800120380020002 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 416285800 1250 416284550 416284571
    0xa061104030c1d0903070222060302040e071403011406010503070c080301151106090d0e030304080703031e0807050f031816150302031005060a02070810050f0c030601020d0e0103 78
    0x14036660060001c43e219040c4007400e242e0300c07881d03258028090740c0c2e413170700100301b240d006a40e0b4248a5865088050a1011004488941d0001040b80742c3c4080d4120b802c3c1645841c9080c00401c03d030042d50014007904c1400b44410b002c4c1400c03115120207a03049030f541a004a03115600443c00f0b581d00000e00d142c510004140d640e100c00e00c64000f03911424102032003842020300386410002c260001c441000040005181003250180d0350340c80f0320707105801c0c4603421796451031980741441210301a056036801c82e4013007070307803032900808800e913080e036882280c01c16000c6480a603120324075580c00352006942d2a4101403524222480541c00604080725050640440500142061180b40800081c07400304002c860b1034002e5410b20f00c20300508090415204004001c6c0e1030030a41046400c0d81c01c01e80d1a46d0b210390030b00c00d05038a4000650012002e51040145a0087c6000c68011901c00c90365503102d1011500c074081d030310000d8041036816a02582102240036215445441c044201102c14503000c1001141c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 416287050 1250 416285800 416285813
    0x20a0902160c0e0f01090c0801170102040305070f052404050f040f1a271506040b0d051b090105030a090507050607081b030301030201120b0301020f04140f060c0a06110403 75
    0x982c0543c002401c51020882d00c6618802c4141c01054601c205010940e41700c00010030f000e205000c0c00303101c0c6e4104143d040f00200b0940c1918082e40d440811a41010f4030b400f00854442000c0c880c5034403441245019102280c2149220303c002c2e4894441c46060030f06000c10003d5100d040d0040c1a0016a40da02000503850113001da030482d4145400d101da10891544140410a5610380c4d040207088010f4058031204081c2c0503400344d0101144082036829220480019201d120b5944400e085120115021045848507841107000380c2000c8580f482003522000401d20f5030250801c0c10380400c00510015070620015000181140d100d03006a440054032040000c250b50400f03001655410303408140d9044440311a680c040d40d00c1d202e54021415036165600090000d002050300269240d01d030720190100c0e807400d40694511110403118075880365200c51030440003202100585c0c5c070441c0a05106c103911300f41441110a04100c3e58007900221005448d0313200a0a020020394041800400000001c1202c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 416288300 1250 416287050 416287073
    0x402070303050f220201140d0204080f07050415050d060b0a06050d05180604021e0405070c050c0a031e260301030302070f050a260f0622020a090216 65
    0xc6501d001a02d0b00f0140030b5699810fa0003848000ca1107805121000489482c2c24420901c560910b440d042c180a010180c003c00c0c054010600101030011402182d0140040b50007030340c00c2c1e0341c2e00440d1061a512030800040d10188240d840041803480e001f8040b42c246015403143e51400742c01e010039107a00b107a004c240e403400d003030740180000f94001c200c0060250050003100d0f080030201e400c20b00c400d0b00303c00d040e54603581e0182009200f0036105071080b03a00d007492810204100c5004000704a280381052010f0808154024200c0b424012252090094584600e01c40241c2c3d402c5904a005854181111043d40b0200c20f825149514817543d5000b103680c03c000f00545161020004980341e5146160103441c3c044d4a810050724400962824001034691005101c129000900c03602c0e281401c41c20038462a500800d004000e030b0080e0040210b544d1000101c3c24081c2c41007900c5401c0717010f00b0310003007001e44054500080d44080701d00c0d41080203204a4000d88440740781c0004a25100441c0d9455090185 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 416289550 1250 416288300 416288303
    0x50702040905070b030601031a030316020d1e0c09050f041217100e01050109031109130f050703200a1403150906070305011505070b1f030c080c06090a060804060b040207 74
    0x4070300000301b001c40e5915000e0301c0103101042d000341c0107800710240002c1c1c0764080e8140f154a8050311004050540d40c0318a0626845a00061940011281d0240035103040300d101c1001c3d50310452400000a84154a00c603441c440c2c034541c3c1701a11140c9032583d031709610645200e980c6040091000035114001020603041d40104440184a90058546030185c140c01038141c6c411414080700d40001c102103880d462540e03402140c00c1720100e03e1556a4a46804603080d40c40d0058814001c0f912510200000010b100042c0c0b4050403a40801c005400c81c000046400c4007503103500002074440030050041c206150300001c40c0010103680082d46c8100b003040d218441214005850b0348000240b20080d40c0510030700f405015125001c011801c0c0c01d807801380191285004c001c20040c02000024880c0c0441c44021000301d00c042d038040e0b012907407802c10906140300c0d0b0040e00d0035401241e496008529040b0b04494246001414091901785418000d071483c2c10024400d6504030744401c0d01e00d5460b900e6100814006 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 416290800 1250 416289550 416289569
    0x191106190f060b180a06090915030c1707240302031e04030216080705010e120f0118020909030c06190e07091a04090203030405120111040314061b0a05070204090507 72
    0x1584404e24009220109529840c040e081620007071250640c80b41e00001a2502d1070404075541000d107050381c032407078941d03880a44400a0540c01150360080c141c0544403c4d094175040b0b40400d900d802801404040d0850031940c2014115401c028660094001e5071b03000003814041c0104d0700ba20710001122031400c0300e007100160070840b022640e260341360005102800100008201d100c0c104000600711400c1c00d02d002e0f1042d0000a4a0b1880030820803401128121030802803160008048040d441091000740403440303603414000042c09850004190780414030306000500d419150400725042410030382064241251b202e001c4400b00d0b00d010806840200f100a03c0080c22640c1030102e801c901a000c0f031560300c543d040031140805690000241c1d420b6400407142c0000e001001d100382030060000411610310703c00041000010b000d0207150241c040711404040da8916903407e24240c81c8075070790081904541e10180089071040b4460310192411500c003920000e8186802d841c3d142c0b40c100e940e4054040e8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 416292050 1250 416290800 416290807
    0x180608060709030b01060302090a090207150606110c01080f04060e0f0a030504090e2b0203040f0305030403020a0e0403020303130c09050f071b02010504030209060a051302191106190f060b 82
    0x1300840c090103540101031030300d02181848031500000c5d03000c07505841058202c1e60046240414059180c0c414503131a2031042041050554402019160f5a001c14594400d401400c546150550080904c80d1180c8000d001c00b00080c0d41d41e540304c00003042d807410741c65043d01c14011500b031194010400651131034041d48809440382d1510440000303880801e500c0030001c1e0800c55545807000c4c071415900440c14407107203c0c04810703641880120f01d140a1603100821010303426500000348030000c002481900d00954003645032584074160035800301d20a440040040c1e10410006013070a60024090700040c1c41003400a603520366601c140c20507104142c0f01d810284103250240440c0c190443c08103128035400040c41c410b4403500c2c1d00060600d0086210282c0180107000000c0e0540e59505000d10140c8001000c083d60003915040910084d00500c109921000a056111200d14014030a40403144425002840b2581c1c50090b45a6506202c51034542c0755501e99650754070814160003000302400401807495203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 416293300 1250 416292050 416292053
    0x3020a020f04230a1e02090f22020a03090b0a05070f091508100305030c03071a0606041716090b0a171c1b0b0106120b010918060806070903 61
    0x10307604032140802d101c1c520b029500c2081403000b01d2124034038491020801c0741980c4958510001e4101c2e10140f800c0040c07050107543c0d66880c84c1c6c0c09081074007030644041c0d0407040c4076030a100014100003804299880107490300f58100100d60010200c4200c0d502d00440d02d9615581c070000e4002d0203560280b0006e0b160030403c00029407204800c01c6003e094903001d1190b9140c00c010b140780b5203c0c0c100040400c0078a41c00100000480d42c150b80055030b018003100c0c0d45500032100c0039240e4000303180c12580741c2d0454034100e4030703e03c0d1012000e0060000500040c40c0910308550f0200c01040040000801d00400c15204101c044281e0303440c00901505001240740b1402100f002007902c502e4000d8030b120342c0c200c4e40c4d945440320000342d42d01401010840407040451103280c00d440c0070000240000c1c074241d100250204010612900c541211580e0f04c9004070707074282420390000c1d00c080c4451140041e180740410041c00342d9017600300082c0e007043d0300c0010712503403a0b0600b01d05121086070b503a004601040c00400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 416294550 1250 416293300 416293309
    0x906051504060509060112090b1602060702010506130506040b0405180d031802011407060207050c10020a171b030403060b030f15010311060408010219030b040e03030a1802060703020a02 81
    0x6240c500c08480c1000745030b0a1400054841d07201416103030410543e80001004900d8aa02c0041d0690300700c41b82c0740721441c020070324407030032007070003581000500901c3e0200d0840e5005000355802860700810540f42007241d104040d00a1000400300f9911949500c520803481d01c0354441e140c003821b01401402c45402c440c0b071045250021810721102007601d03003c0800705030480980060009542468170120410400361a03044a0148910240490b84005115410000d000618015007001691549030f400c400071400e07602c0d4241d0301c00142140c1d00d600307a80c00710a6882401049031404942e10040340441c058802451900550401c9401ca03942d550f507500a403408002000301d0108010040c50b0340f061452010503029010b1200801c2100680d900d480540c0c0eaa0082d20090301050008544504d400307d000304600a50700c10800221b8501000358845007010701851000c00010390003149182c551050380c8004287d0055111141900d080a60300181d803a10001e19a05020340d00800c4051490700401 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 416295800 1250 416294550 416294581
    0x10605090c18060901030605100302070302010507080712050c040b0408010f0b060304020a15020c0612060a150f0e061b0307030908030319020901090f1203020f070b0f0715090605 78
    0x41001c0000380840151030790045184111100140c61440d2155101e20040c1c01515190308115407042201120902a40e4154081c005081c0030358028021a1100d040c00e81c1c0c8034078140c980c24002000d440b2460503c01030b07034102c250004c0310f01d40103500c0c040c1d56a10000c01500030b600074441694480184d1100d031074071030041c0704e5038404c1140d04505e1030a00360f0005600300051300c40c0b8104500c040915200c890f00034804500d61001c080e1040d9910307084028042d440d56011a6031754850307082d49601060350120110301000400540d19040caa407605014281c0d40c0307001961030306501c0081001075080c40881c214202c00b100b006070303000f1503c4100a2401401015403074000781e80b02d070b10130710803c0380d081805920380d2140b20f0130400050b40c40041900403030f081003440d04201d5410301501310009001000b00c03000801103009600746c50768100c40000c3d40d620340130305100da0111281c0500407000000c8c981c038000c001180c41044845100d0030141c1c801c40603280c4a0b09c0696609036214104007000c208092038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 416297050 1250 416295800 416295811
    0xf060d0c0b07051e0c010f050405042d0b090a0e03070f05011b050c0613150606020303010812191803120206151c0b0a0e010e03090301240306020f09060c01060509 71
    0x20071100d088910312241e0b803507030721702c030a00d0401404102c4c0300d1509010300101c0d4064580500700b030195000c6d04d5052194801b0070a0500500340303010038620a81c0e0300724403940010f0840244030481907100d1040d01c01c041c124002c00102180401c100380380000e184c001085203100d200740e001048049111601c66210030003010311409220003000490840c800104010f540541140001d4038041c0840c200f020221004510b409402843d0040204c2c9040e000000b550488000e07004444140c0622200030741d0074010428407072020440000000c6419000e8008040500d4504000c1d49500e07a503900c4d0b0000060801400c000943c01c040244042c98821701c3c1031145440b0282c0300c492000d031401d2103108000c0f07010580a440d4035100800301e90700121540154451200100007400381c03240d4040d00e2502d030342c01305044520030741c038244119454146140055640514105039080710303d00e5a09d0306406503111300070700003607610100903c160540d01d004c043d22504e000d0f80300003d08142437000b480130345940a0301 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 416298300 1250 416297050 416297083
    0x60d20181311031507053103020405010b09061b011e1505010908100e160b120a05160c030507060e0f010e0c030307030c0203070308030705120109050f0f060d0c0b0705 73
    0x6107008503200342008179006812842c1c241e03030324958003524034000300d00440c04030300404400740f104941007034501407179003564002c803010081642d070b40d4060703d054490040a00c0d01329070f0a101c0030502804544000c05201c10000001c40c40c21400d01425001e18041409603000302d41e00e001101202a4044007400030307250a09003c145203090034100c55443c4054400f0581c01d580340d02c40c066118034140100c05140c041c2c194420012a1101100c1d0259000402030050202c10540080c50320020f900419028a03e401c7d4003215202d03800004aa440f03480c00006e80500204104d80b800050a5102c1c0c0754000c039500d80502443e00c0d81207030760b40c00c4d54407101c24001142e00c041d10194a55402000700c441595250412040d0140c051002c03d050045a81c005008034101008000006402030002c280e082d6001015110b580c2c3c030f4541d40f0040310400e480032011280c8000010749910140421150071501c02801c0c1c0400070388503503500b84625115045001503510105206c000c1087c10400d00306003100031365 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 416299550 1250 416298300 416298313
    0xe070e0c070f080c0f060606160212030d06091107031e030b0d0b0403020d0806010f0f09150e100503010609051c02130c02100615180909050c09060d2018131103 70
    0x1a00c6001d8001d41c14820210340103440215565800e002f05086110401e0303c1d00d6503445040c92009008500c904240c0f241040d80502540030204200c440389685070300d0f44103034518150012090312104c030124109050b61145c400b00d180e42d43d4214410510b1007400001024030b003030301d0000d04001524281b8818412654103116081e82c02000207071030311003607103402151200d890f50101d07811105a8413041c0d0705802c11034403440c595401040810389100c01d43e070451450410701000c950a2100b4070502000608041050000d480c1010b032001400d4000a5403807030001481e00001c017102460060030380d5031039a89650700c0c0030f641c05010340340300c2c44045003081024629015a85004417040074040c0d081005910ba400040c403181c52481c00900401d500421500d08980350090f914000301040c1d81c4181d0313245000a0b07151500c10044841a0b0348080c1000039815529803080b66020390341841680000c00c64070039a180e21b140c60900388075044810241c02e1101560520401001c8182511802500280c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 416300800 1250 416299550 416299561
    0x3040e1914190209040213033f1103030907050f180402040c09171501090b06070204090c1e09150b030f150d0b07120e070e0c070f080c0f06 61
    0x81d600680c40104094400c00c10380181003000000d120740c4000a9100d48041404101007440480c00703420789101c1e446949a048881300c2000c030b0f20b10444004e108800d156000354050f100c0406c0784231200040c3e4200540c3d402e0b6000002401d41d002202d1400e02540044010072562070719101380f045604066a6150030851102160500d142c0001c101900590301c83c008501c1c094800c031203510092400482600c1c0c03245821101c3d9885005003400c10b2204d042c2b0f000045001d00c0c2c1842100404ca10041032140f91007c00c0d03080c0708c0600b0100300f081d80e1201811500240540342c080c4540c80600c840300c000300d4903500745100c2c0c20484403400a50005103403800400d01c400b0046500f00d1b81c002e07500283c440c401e691101000307240004050310745a000012840b00314100b00c42e01c43d8071130240c0b003103490310b4042030041c041c0c40044849100401c02c981d4020082000000310040003035800100e04c1008902d80141c60701c42c40030503a11140e08070b400311070014241c10070041c01c1c00a0b40d1000c808034068001410030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 416302050 1250 416300800 416300831
    0x60a020a0c11060d0504030c03170f04032708030c0f0309030d180306020406260606190203040504020a0e1306030b061203070605040b0a110c070308090a030503040e19 73
    0x110000600b00d018060101c0c50035564981590f1540300100001d00140c41d152030010540c00e044c4038101c000c030381000088141e10362440c0c41a48962241c145040050341d0743d440c101d5005c48d900c0070060310390038100f405900d100a106044005811003000455035000482c0d18180740010880444401c5d40060050124590f004601c40303004442c1d6107084da10602000c030500b800300303440e580001c00d02031001074005003454010300f10700b003145000003900e444140300c2041c4c10798102044680e0356101c1000c20241590013020b44400d0300c2d01003244101c07070500e83c81c7d0000c201240e106c26030b80380100310020000200c034940403003000b54545403010207100062940d6030300210008041c014521840742da0081e401450000c2080e03420107500900b0500c9241072504002041c01c41c02d840030322003a412324620a070b895a159088508454030700004000c841d1640d19861400d070001010640e000c09200c1001020031010406400600039800312324199060007454504140000380c07015040b9414429170a060049 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 416303300 1250 416302050 416302067
    0xc17070306080708062502030d090c05090f060117070302040e13210f14090d0f0506070e0303180f0334150309170705010617060c030a200c0c0102060a020a 68
    0x5900c8100480c446c0b0f48000c0e401c500641c00c00d0480380349000c01d80c03014002c0c903070700c0c50003280c41c155048003040d03d42e42407841c00110225042c0d8045540c41c4450b850341d0b001d0301c051a030302500c00e10380141402d8a49510080241c81626055104010500e400042c0094071402d055406900c00c60000c6800070580f0140401c0038614013242031040fa0340c0c0c0d07908440e00300700441d490b886005112207a0015286404607450480040507580352040000040b0a5400ba02150002e143c004005505155031844145450500181540d41040721941e200e4010f031010052161480110740e0503c54401d00700007021345240c00320092136121904140b08005070040b00c0410290240d007841c0c08244001d203400d203030842140c8500501600e110020b0b041c4c05100b010352044080e80c030103001691341c1500d0b0010550f52101e0941d02ca0015000803c007050001d2101c2c0e11403d540e0342402481e000b07080b01030000318456007010201d083c0913000a0b1410103190707418040540e000000100850800c40c025000610809 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 416304550 1250 416303300 416303341
    0x9060610050705100525080105030709091e030507060c181701110a020a03030f05010302061209010f02370f0513050301020f130f15030c1707030608070806 68
    0x30000403100c1c1841014014034014a5001e1380900c01c5042c800c0e904110f04902c114483d408411301d4210715515445408100d040310742c01401426900d0a18002500602c0c3d11441213450b40800c12982e1a030082804030721824038025154107031282d890f03080c0301c0700303481c80402e54000700001e00944000329500c21441c28241d4a0212912034142c0d41c1442071801448800e0845603c41000b10b445240756a00150201181c4d220366414002d0b0380b4441d4150007a50400e020003980240e041c0940e844407501c00c604194082050000820101010058141240e001c0004159074294850907000d42000009980002c020f184940f0b000c001a20700f4000c1c02442d03a9420340080140006605040c54401c0150070040d00009008650382c080d4a83d00e03c1140d0b108180301780003500b164500080e0541051440011030f5000042d550259200d80c900724010001d204000d000e0104080414108640728401c40384245001c2d100003503442c0c20085807529000803540891055800082000f40310325000c00520350ba131 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 416305800 1250 416304550 416304557
    0x403030c08030a18152304030c0305130609030b0609070f03050603120c0706030501060f020c0603072c0f1e0906030f0307051c030227061303061409060610 68
    0xf512038001031005014003007101540503044180c02410300c84040035280d17041061610800040d102c1074680f41282062040c1e40000d8078007000001d021a02901141b6030f11340c0700380341047c581149003000810a82e510b4001c1c00001b001d814084c020441480e500d240c1001003102d00c00128a0680750043c5490016036a800405482d0001306000340c404200911112108469584c0c5403a802c2d69460ba50b01c107180700b0800041d04190000580f41c1c040e03000040c031017840360301420824001c0c00900007991300c003030200400c0215011641000081280405095078180305e004080203142104010411001c554500e01c100c0000000551202d5614000f1440d200b05442c045559580d910000e8140f00400d82ca03c0c43c180130000d0014200480407800096039002640c10002d06d407030a02c030850889c015959101907141c1c0f4900724444480b40880f403e000544010041860050301c002184005415035004480c840d407511001100e10b007a914103079502100d00d000412140c80e044000032850340c00e91044c0401d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 416307050 1250 416305800 416305807
    0x40b060a0e1f030e0706030501030503040312050d050a0207060606020304051809010b09090a0614072c0604141509061e0f04030f0b100609151701140a0b0403030c08 72
    0x140c0300e841d070070144800308102d500c0440118100c0034000d06118090130700c4034060118003040b82c6000c2d00c9500d040e01d8110000350b051a0955485140d00f000700c00c10b10741807140c1440740d601520024040ca5100307603c0d8810141e01e42155107001d905170f42d1140c00c00000d6404c01c0c001404681c441c1c1261070a43d1204040304011030f200c8034411801810100c002c9a00100810308202c2001000203100d503c41d44160703020003503454600340b614542c01c403c0d81d96200080300403401d203070701d1a070b5821000d00f00c0003a14140c0207081030400004520344e200b940315900101c11481840014070784007544034601c2d01f4070b480d420302e0181e000f000514644206d88041c440300180c2c060740880180b18100307649000f402551610758075500c90400c1e10700e02c0209034003240c4d5014030302c000032404441c4440660403a1350340d40b11810300c50304045212100883e8500c070301041000c03081c0c2a07580c81a42c945054000c0080c80301c0882005000410302558007504c1d000a5083c090401041001075801284c2c010720907008047c0644 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 416308300 1250 416307050 416307077
    0xc150306082d060c0301083a110d020d120209030a120507060e010b0a081f0c0512010e060301050112051002070206040308191116140102011d01020403050705040b060a 73
    0x4241002c02001d58803841100100124030a10303100a5060b550800110348102d25400e048038440b05400d00782c1c441000c07000c200744001007003504804e2102c0000b0b05010418400c80341041e8a4503005c0c50f19a801603002c0c00481100030340010b40c00d100d02c2540b80c0154640201d10380400d541d101d805000504103804080f6900e2401c1c85882510400743e8410710a100070711808201c14040e20241030f541c1d00c0345095000c000341e0590300041c8010b5031710300d0134071411400010002c000f0040039046440d80a026081010140e0359003150011070181040f01d1620009051400c249030840704160400c5040b16400b00c10781010410020354010034500c0084007507540c030114804260b140c083c61748000c19102011130100244001600c1800030030007181d4840e03001114954609a071800401e000c000140441e61060000211085444491000c10b000104018441100c40c10003c134885502e841c581e540441c00f03000f00300d001d100710402410116824020203e030103000803900e200c2d4480f0f05081c025035014100313 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 416309550 1250 416308300 416308363
    0x10518190b091c05040513050f06090703060902070c080f03040f171608030c0c04020f0405130216050d0f030c0512060102070b03010807140d0507050603180a0c15030608 74
    0x3c4804201119104050b60020b03000c2c113950000c1c050584034a06640070071103c0040c030701c1243d1090282c0d030400301070303602c45078248425910080d160608064540320040341086c8180000e040c254400c0e81c03950000791401009a00707107500b030107219441d90000c00003000844907c1c0c140d20240e9561004150a0300140341c01d107031528105010403424550031a03c0043e40b01e40101c0604000c00d80300e0140c40810502000f0803040788124581c10a0020061100b80458180318180598141a0140040c030380484c1424140520038010720440307140c2d20003118a180d050740440b41c046240081c2c1010712007282c00500180681c01110300020403900d0320400162141e10800581d401095100c80446c0e4030f52b100e20f00c4c103850b06024000c0d004600082c005040350340c100030f02d0344109250004041d1284a0502e01000b0035a07101501201c0c02101c500700b4524514402d00c50420312034482d2a80045461400181000c2d1106040062003031525014040014143c0030844900b008008000b03a80c02e2018980f105 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 416310800 1250 416309550 416309563
    0x80319091a0703020606100f030f06030213020318010b09070c02130524060f04210b16030b180601081801151a070503070201050d060e0702010518190b09 67
    0x2a20300c0c0e032103034240c6038030503001070090200500070b50a5440943d9494107100d0151400c55040c40050f24040f02c00d000c0901c0395201c1c181045c00410085807681da21303000035115020824083c142141e0001c240044038410001241140c51504002c0c0544070000c00003503400d10380104882d0034040404245030465a60585c03481c480c28031490f0400040c14911009001c040c0300e000c68075071201100a07400c0301c074a00302c0d050b94070145058641e14a0182444d10b041c0c43c582c0013a001103905d0428510900014001080b85e80c883e040e40090b200380d101307071030a004080c0e50015090500681c2d0038110401c2556120541d1680a1420700b000c841c41d4903100d440c2e01c03000300c940c0340c04c500300e51801040211301d203803008074041140c0e1503240004d1006014580815907101d01d04008050764401c01021005500600180503c2c06d202280050129a0349515003110786003100c080006075034a8040100d0020865111a88400342d040100101d030210400301e00301010406020308219100c00025008a204029a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 416312050 1250 416310800 416310809
    0x60907050c0d0903050d050c0604121e05030603060709080a020d030e030709090b0a020a1d0607020406090504030935160b040e091506041a04110904050f0108031909 72
    0x12030300e41c2d251003180140304140031301048556006405501466612400a964005c01c00c9406010b06884030f58500c025185a0440740341440100c0100d00420303035154166000d903030015110f16640b4640101050f04050b4018408001d2001002082c01308038000240702a50550503249100140b10038241901c1007070462031503681c11b206803032002c500d00ca101e400c0804164032820310503105840f6103a400b0144d014400106000030001d94804000744e402044c440b0410390094061460540c054000c134085e00c0003504284001c507101e40600c01050340c0191003400601200b103440403c0ca4030190b5607100e0b07140680b15030745241185002026035007001e00c034640004100b03c2420720400c0e5a50100d0344250014442c40e15403040100c00a044818041181543d108662250101d0b41d503400341007200800340460001c44860b041c620b0b0300f42c540c030340344208445c0d2581581d1040d00d80070300000300401d80308014008260740c0083c0700104500400001580d04030a038101c5851a000f4400e003049542c2d10f1181d01 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 416313300 1250 416312050 416312053
    0xa08070e12071a03091c05070209070306050f0a03170a0e0a030f03080702011503080a18061116030b010303030504150203071805040b09040201031e091b0e0c03060907050c 75
    0x6180820700001405400b200c20586101041250310300070364071039010454074140e65410180c0803036a12100400044038a813034604007203003000090b4002ca00310200031100b4001081d03071050140000c1c1340901d03120a0003881202c1c028541d90560743c4440240160002000141c1c4000c51001e100e82d00529103182110030150400a12942d2400d1103a200322a0002c11b5002c2041000460b0b1414418020100091442500400c009255a0f28031241d980312407000d0b410480402075903035004c4100c800c03800080030a40c0e61070b01d1861030480b0190401600240401c80d000c0212420000559001c02007811640c15041c00180c6980700c1c00c001c951000c518800243c0e05200004104000341c00c0000d00c049501c20110040c5407503251024441250b141ca603800b5484a03a400000b0015031082d0090240c514900f14080011086981c0000c02e40701c51500031200c108894200300c00c219800c7d1030004c01000c003420316805a003050002149240b1010b440b45005081407800298928040c0080b034103450000d50 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 416314550 1250 416313300 416313319
    0x7030905010e010f050c13050120030309071503020408070504090206070525050603010506070f0212010e0c100503060904121e03140603030c100b030a0503120a0c090303050a08070e 79
    0x203095000b04004510303588036a1901020070743e15403941c0c054419840c0b00d40040c031f80103410b220054a98501d403600f007090304071601c01c250b07511203401d0018601841401c00101251403c11945502c050035211a8400700352041c13000b0002c044000481c8070032110b00b500c002076102c1e003034004142d0b00c0c441c048010b0005e100f22008007050705118900d0404206e2046089028680c85100300411031100388949071340b0100a024640210340000742000c10075100404010200c00c01900480c07e48081e114460390b00c2d04080c41042081c2403984114120b0f0704c0d24900185980b511000045100c50041c20191442990340d00c421041070050f0b200031800741085a9106a4441402005014042140800304404c210348081003403820004250f59600e003401d0043c0040d2281e464000000b01201038045070b06101d5020344d44007094051008200c140b6205050f103140d49003901030741302a21040d9406100700035685604001280c0e0102c1a1030030407030189030081c501c0d1218002256801c110000c0c0c46e030f001c44190b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 416315800 1250 416314550 416314571
    0xf0a0503100842010909050c19031410051018050402090705090a150519020a0305090402030a1b02030c0118080909041412072112050703090501 63
    0x120196109240005040c107140381c0b262030050b15224075514846a801c2c8148800c0d0241e918101c40445282c015007580001c6003034145582884102a0300107403000341d440b09400b06100d4107200c0942201c40569000c0102900d1003d1f543d8058403502c00582103c00781c0000700868407091295103040510035105000d01d0038480c116a105003407511035006900d001442000c5555a40d00480b4812a0002d0885181d90380d00d03c001d84003680002001c5502400811020442034504003046248082595580b501d40c4400c441200c0b4101644c5903031000d40d4062000400000c1d4010304445034444150b80150301c03500c41c07041e900c015100c040341c40801d4a98011141c00560760002c003400301c07d140c1c00000c0c00f0440924504842140d10200058620203041100e04401e00b01003640030b82103440f804c00001c00f0800034078400d05014030700e007400c4042c410001ba00800d000c5104441503105150090105800c1410348001d0b001c07070300c11403c10490545542c002401180213074006149150054000d1052030b01c903 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 416317050 1250 416315800 416315807
    0x40b0c070215211303090e10090501150e030a15090201050705060f0703060f0f05060f070210110c010807020a060b03071203050d0f020c1f060b0c1f02090f0906060f0a 73
    0xc1002c0c0d075094800000905454220100c2d03400300d54041e142e06c050503080c06401c107074a02004028104201a12000040c860b000d8807955000300700102d5140310000741804024408041441118825440b0054440114540d0001e6080402c3d10103000036440129100603141800b41e40c0b400f8019003d0078081040640825845521904040e03408015180c0c4a419100e07100c5101d00600c183c80c1200706c001c0c401030801c5402007004458049038242046229400a8000c4200000342000164641d0783c18181a00030000380380010740909000750980303006103000703507030f191070310300141c2601d80b42c0310f04840c25201800000050800004d070241d1034032450038082d21541c05030300800d42c21494242d43c0100044c45200f52100c0b090303094054402100d16581700482680c0c82141501c1c1140d507282c1c00a07001c4c0a400060143c08072410140601400701c0e1642c0850410740001800e4503801007040c0074051f6074081c0112603580c01154640c805403500804a0b807980501c002031917088000280034120180c1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 416318300 1250 416317050 416317087
    0x4050607020c01050414010c02030a051903140304020105030a1e0507020a14060112020d03300b01211a120703050610060c030e030a0f1217040b0c070215 67
    0x35000c072110062110b004444900c00c03031040103a60b00040002240541c0300f108910043d50000301250000203054560b01d081082c443c40f454441a042200002090340240342c40c0200c05000301e556013103180c1600068900d100040c02c0100c030326610480d40c02400c0c900000e0010075680c1201c200300030f2034803035006940e030300c0141000d03215440304100c41c0030f040b00f00081d928140c034214014540364445907400d2020071041e0315011404c0c03150850b0400c40318036080d44041c2101e1030810740d00c3c04220712500084120b0b046044028100903590380c0348692681841100b00e0048440070002400000780d40c40310f482c00f200b151049520100e510152100d480e400210001a0b90055083e51300e5070701c0f82d0300000c404080510415011035880c0c222500424040c0407c0406804d0103020340301508096642d164100f0b003000011038084043c8201411095802001546044c14074600c0c41c10b01c0c01c081d00c91400b140e030001c1c8400e81c411000100c905c11502e401c00c0d010485421000e0241d102c4c3c0c2d24000f40f808088 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 416319550 1250 416318300 416318311
    0x402070b0109020a0909090c0b0a0210090308010609080f0a020f032d0607051206090a060509071206060507050715020c0604120b1311090c130303030f180201080a0f0b09040506 77
    0xa0803030f080450b40b04001e1240c07860741c3c0d034003c0448d0400ca01c1c0103c0140c4940100131410258040c028070020315004a0044030300302032080c0e5907841c00b0760400380094003030b103003c0d041303e602a400902800c003000800108000b03c070341c040340c84145088410000070f180c81c1074403241c40b041c0021415054140102c0d020040100054034050743c08598402004445600a45580c55a0300108a01040d820f0500a00e841e0b004400d204000c2252500c500215031410b8042d0b600030006504005071501940c181d10464000e40341c0e625005243c484280c40380c1307544215070300804c0f1072581004451030340c0714000c125179403030100c02600464496035901038154042e00b02080039102090380c1c10004000c03c0c01904586c8400e50b000c4445411801c5031400d101448000500c140007079030301041198800c1c5405030a02c0010b5109540218072085001d000105a030402100b2214014036690002d0042c4e82100055a010f0700b040300c00203030350380c18a42d40400b520b6180d041540000900050100b40300c000308a192148 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 416320800 1250 416319550 416319557
    0x20d081810050105041a0d030302090d060504211e1206170f0c0a051305070c02030f0a03140a0507080a18030308042906220c030618060608010b07020402070b0109020a 73
    0x30741e0490400a48070b03246e00c00035840014042c8880009000b50f01038005650054640a040107040c0c3d154811528103a0f410703112080c0344000400001180800462100001e1514a4880d1560194003640904022002c000e00000030043c18402441d54000300c010b0029402101003031000a0f04141c94000d101b002814601482c054401a400e06070403c00c00c0300ca01a02c9100d101c42c0c800d904000070840a460746040142105c15400503070703400c00c04416001c0c02c490190891110603e00030700844a440c181040c1c104042c4101d101e0b2503042429984003580040c0600c2e6249049502103503800d00a450360414420070080100074540c0c00314030584568891a00300c2029007082ca00c2c0344982e01103100b042490502c03407000660700d040c406080511914884110b0464980210803901074408e80c5000d680000c2d03613072408124881804c2d50350701540340d0f0a10700300412410148000d0030808140100907002c00c00055000031512264101c0b41c0c000d4105411194950311a002800654440786180002 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 416322050 1250 416320800 416320811
    0x1b030c08010b131d011103060a0509040b040b180307050307140303040c0302041107060f050f13030512191b02070b1213022808100c020d08181005010504 67
    0x61205204482400380b004100e40150602c41d007280e80a07005110b0020040741358500c103121040030034050344044100d04e0700805e441e850721400f440098886580081c4c0f00d0580c00c4180004140c031041500e8205810024100c4e4654030300a0310011680100d41c04102480001840000d001010010f440031a111708070440f650201d01400f9a80d03404145c0c0d0282003c084650200014070340303503000c40340e13541010300c40504096658030380d202112509400040000c2e124010010308048012903291311101030181c60b081d0400d0354400800f00d004984101c682c8081c2040450b002c08a009080301c1d15440f480014030002ca05860f61200c28203500c000302025101c0c0a0020030050155011b807000303c01c200302c6107140b995855110402c80054604280d821480040324070a52805049418007100d803403030810300e0014540407410b032500350716040741c1444510f0003405e00940c59020070703603141c08010f42c6410340003501c800702d00d0124040ca12200103003034803035542d80000541c2641c01c2a0704a95084030100710 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 416323300 1250 416322050 416322059
    0x2030a0b0d0201050901110c0a0f0503010b01031509111623062a070c0b030412030209100c05010b091602070b03070503070813171b0f030301090b04091b030c 69
    0x503036001c201d1009003c514240322211a6510821032444a00e410000b02c56142807242e02041845c035682c1c01072851480380c400c0912181c2024001c27910350324003e103810050441300700c0c0950650300745401003249890311061916030010070582504c2000968140008060b00c50346804c801d0603107421416024885502019148140d02003071141c840d1410400c2030400c02c002c0005640c03e144a143d0008030303850244200b0010505021001c006088640300241d42c078240303800e100d03680c1c414103888501014010056140a901c0325070183c1000006ca00b420070070f42d040d61601034090001c4200c081d030014500f00800010703071880d4090311080e040b40d40946403090340356290500035120445890300420360802c0403c40d0240305601041e401044030501294040503582c2e050742d624044840310602c03400c00b08100101c1c80c01d4214043d05080d00c08000c1c001c89901141640c1c90340014403c41000543d070304084140c0b500c0b030b0703007001007599400080aa40d1314180140c040e80c0c0566400169007800c0010070208 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 416324550 1250 416323300 416323309
    0x2030c010c0c11180a09030c080d0509070b130608090a02090a060603060501110a020f01050408060c09040605061e030612010e030a030e190807030936090c09020309030c060103030302030a0b 83
    0x840c4011220381c4d4480c81c0d40c404007070202418003d1700071010801582101c5000c5541c0030081e009485484602042600f00801e01078540b2800c0d13082008140020419003000281c0000d56804072951410400043c0e070380c420a240c200020300708080d411004000400034800007640c046030070f42c1c0042d202005600e48075401112544000707030310740540381c1c00302d81d5100243c60700d030040c41c082010500d00940f90075210002c06081c43c909450010440b80d020521104918041c00b660020b008251182410003100040a41c2084c4021101911f080000408250991502c002074450300d0f01401c0207000301c503c40c2c0c02040d030f00c0d4024044800001d140c00c2141d40340036030200d414501002c80c1d0356460a124401d488241c2140d00c900c00460a01103a4034001611340141c80f6410040050381c1076103480f102e49985581a0281c080c00040000c91400031624005902c049400b41680d00400e80140c4a98034100980d00e184200426080c0d1031040c3ca000000b0158560000e520940078008140039002101c0d0074403 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 416325800 1250 416324550 416324569
    0x20d0f1503030c1709030f06011401050903060708150303270103090503071203020d090501091101140a050c010902181e060d060e011d0c01022a010c0302030c010c0c11 73
    0x40009103030450340700101d0189030b004d0b115070854140712840c1c941c0440c0080c1c039000e84402c001007550002e400401c0385c0c480d40903200d2806202801d100c4c0c41c041000c000280c6442008040509000c100c00100b14182007940d6500c0080e4400790071a40e442c0504211410907640700c410b0512100c5200382c12802c01e510174000c1140565000d001107007403000c2540e614110030113420114040507400c2c811b0048001241c003800802500840c0005101825820044010750503505018144550240103103040344044046800c11281da20741152a900b40c00c42480c050703c0c0c04131010354407000580701482408802c0140038068401286c030b42042c492400c181c100180340844075140c2c01000d81742c000001c03e00c29008810701c01c6842c2d000188404509690184048226190010390b5101400c91425541c040058260307000031000701c0700396041c2880311004044800745c40281042901160303a01018000c00c150382156004000038000650400e034020a0140c51a4064864107041c01000d174103414003510b403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 416327050 1250 416325800 416325803
    0xa02121c0b10020a020636040c1713020f090103050f070602010603111302120115020d020105160e0111030a23090102060109110706110a03050f1621020d0f1503 70
    0xb4041c0d40216800300300d0642c01c45103064101603091030300d2640040b501075496a04250f1280382c80d5500c6400018401201d00c00f041400502c86002d543c40003085050703010f640c1c0000c0700703041d0f0310300c95000b1b10116035181c88000b4241e81201030ed074000320030802d011401304018451441141c90f00d07030391404124280d4042d0f21003d0a62001a010304e07100303003490896501039991074130700035240281080c03482c0003182003640301580d00780506003480000c80d81030101000c8012248024860b501300b00c000c40a80ea5400c460000901240c020107035110b034010b0714012041c1030342c0825251545101c01c000340900304240e00040e011140241900e154104c0b6106032142c01c1d0313041c5d00030540c503800c0c138481d20b0080c03080f10503503056000c05010381c400107180c40c00380000803401800210f440700150580a015244040c240304000d0030b10381c04000d4148484422030140300660f00e080741b4904508441102e1408000101078200e500024056503a41134a412503021024684020000342111030310300f240e40c0003e03010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 416328300 1250 416327050 416327053
    0x4060e0f03030c0a030b15131a0f0d05060301090b040f11150306130609020d1401050f130506041401030f05060718290a1701090516050a02121c0b1002 66
    0x24030a0345610961009204106c0640201c01c100300e1034440d401907401c40400101d035072128032006e001d08000f0465000c030041d04402c10f5401c01455404a04150181800b24a4410342e1580001d01c08c0c0c0e001d4001c00003642d0802c0c2000c02504044c1003012400f503800d038081c0e5508401c0f12040c201802e282134a10110b00480072070604540700d42040014020700d10520a400980f942d1010407231a42c603200038441c054420f04d0000b8000301190406240c45416403140e031040d90343e00b00c40e0239242c4556804000b000c0803003d00081c40d6803044005002404512640110f0081410004c820495640542002c99004100710340341569403450803141c1c1c1c20503c6c2c0010540d40c0d40b00042152800c180c84444440520081ea5804c10303541c0742004090b9003200c031500c0d0004040540704442d0228100c00c3d180500350001052000740740c2103010f20005800d40c10b01c0d40411000182400d1417074421700800314114064a0000d83d0b8106c0100d000c0c50b60000100d01d2420b051411810311b00301e2402200c4088054401c0c0c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 416329550 1250 416328300 416328307
    0x1471305190815040f0b040f0b16090f06080606030a0f0c0504330c1403030f04230a02062a2401030f03050705070e01060f0f0f08041104020c030304060e0f03030c 71
    0x70340381821b402c40600704039a9a840250715500046892103998803542141c4100307000e623805000000c22049541e40144204142000c0500410b5488a0354603030052007500e09540e00c1d207034588000024902940f00c001590300c0d1000e89442c05500c2070040040310601020344e42000707015260980103031400110141000000ca07454002540110303010301c0745074040e000114109240b03c0c0c40c1c1742141d0044070401d41c0d40c40240200002c12441058a403a10010740c28503005405900c10781d00d54070f900844001c1d110350300c045811080c01d040c0c1540340d5410045c0c40c0c3c400c880c40b10500c2e0416682c2441c4c050030b80390244110100c1846403a03603e1818100d036000b40080c201c00c0c00075101a10240c0c0081e0041e911402541000300e4811a6a00084c5c020281179803407581070803c107080200080b01405599041200b06e4001c85c06450b400b04880340c0140c2c210800411040c0e0760400940244100b41101455000203c100014013120f540124085003818055400c2c9400d840a02074580c8003c8907600040501030 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 416330800 1250 416329550 416329553
    0xd0204050601110312090d050a2a020d050d0324051504050a0e040203070911032e0605130504050106081302011701471305190815040f 59
    0x64010341e800041c10304010190b001001c41c900e046038400d000c066003038041c0c5000d1002aa0040012940390240c03403500c182814054000203040701c440c1c0143e00840d8007803565032a00d005002c8aa200c45a07030040461000c0002c80c5445500e440f0b1440184011900d820381c840c1620f014903512880d1031201747c030000815802e00040110966904c0b400014078481444085400c0d105c17038101c0f501070300d060040384100f0715103841010728200c016041909290700b48802420b51000e1380061300d0300306078842c00c031a021041d48806c1c80c0e014455184003445d20503e402000070f119401400401c03001d1202e84552801c6a2113000b80008c0e03030020300c6600c0001d40c801000414003940c1c842c0e0a51a00d205242514010480c10084c1102500070f800520b02c0c00c81d11500c1c01d031107082502810182d2600c1007070361296880b4804014520381c9181c2045580342c3c40000710010342d0b800d0b0007040c20191078001d24100c3c00407481e020101c60158a4000e5202500c2140d00414411401101c07041c40341754010b1201c108025a03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 416332050 1250 416330800 416330809
    0x501050d0906060e0f0117010612150e010204091e0506030d05030c040b030a0f0c0315090903050c0601060c0c0f03020f100215090c0103060509090d080c1c09060501090b0d02 76
    0x240700c150740c01d550b90340c0045024034480c405076004031003101412030194104811440c46818515018031560325140c004c103e44500006130681003030700021160a071007a2021881c001e0030038400c0c000855480001c010400c40c10035801019451010800841c1205034440b820040301c0b01a42c940d50b050b403090401d003410600c01e10080d50f000822603652420196149041030300c43d0000e031103a0104c45e0301d4402d801c0824015115841480216207404e010100100307140d01c030780c00d02900908000c541c59101400c00e15010b4012070b0201c46500341220419030b0340c1d2000034a8a10056130031078110402180c0042e50b46088081c010580b60000c040d94500c0400c0f904104180d50360701300d19401d44c0507544034004085440d05840e44103409500260801c0345140000400710b45494104a01c1442440140042010300092500c218501801c2c198199140c4003014040b90050344258100300650044107000c5510a80244080d203204034003e00050362140c003080d040e80ca1080b02150040041007840d80941340 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 416333300 1250 416332050 416332061
    0xf0e0c0306040e101e1415090916080f0708060106021b01260a1506170403200a0309050d030f0804030509040f15080c060a030e0c10031407090501050d 66
    0x1007041354220355802c2c0d80341c3e041e681d407a40a6103085070f0031801d0003620038882c0510740c8070400161451a15140c081440840300817460501030140c1c0400d00081c044403400c01c680c4000c05085403040040c00d5841202a580391601103110f4014040c48500003100f40340015014140c9a064005d4188020080b40014452005050090400014011860800903a03000005d003208c2980301e002c403a4a00001c0401c16540700700c19980390300d01d02440801206a2002560782d41100d0700d00340301c6d00c0c2c1e15541000c81d007120002c0600301c00c800c0c0c0f44013090313455803001404030030040c480e4580060f62039490080003501c1d4040d09002e00800d00d18001864002e1041d440c0310707400f52290401504062800012604507010440e020074081e90f0362140d900c404400109107401400200001c0869140c0000855454054076800b901811b03114412101d4544081c0310b010801d05004d08002c0103182107070700003809000904d010800c518403190101d07010074483d1500ea0155201070f101d807403404045543c048020324 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 416334550 1250 416333300 416333321
    0x30204150f1710050106020102070611030601140904020c0d020616020d0f08042103090510050c090904080906070807030f1e050a20030c0709060302090609042108010f0e0c030604 78
    0x1403c00008010320462241e02e0107030500d03600040e240d0805282c14401c4549007482d60810802c2401001126030b44140200484a60300d4071803030319030006601007000b90062180d41da0480c0502c02481000d2a80056058840c41e9070074881ca4000b0280b81050761520b104000200000d00300703000ca03089241c0600c0c039160708540f05002000740d8480d00d8808806907040c01251800080e00d07036640d0070034400100284503100c2c0103036008200c54140150507031181c4c41402c036070b40d00514013000041c0a01807080e040d1000800080c0c01e9a50b00c445038030700300105900c080011400305250303042244075548544005034109500e41d041c000c2c8114004420780d0aa0054140d01d070400401c18400307c07481003a038542d41c000703c3c02d110085844940120000e402c2010f541c0001010503c0c0101c100050b030365064500e900010169851105510341d0b05000041c01c800303a480030300e102211150704c90039175800302c1c4a90491350712000d88000a929000030100024064400094822040c0042640340c50254410b013a00d9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 416335800 1250 416334550 416334553
    0x50a023c060d0606020d030c031505150f030c070c080604150509190f030207080f0d0509181006090909020109050415030209041a13240609060b0301030204150f17 71
    0x844050a842c0079208190070a600580200003001d00c255014040c09814001504003889600304000b00d400c040995840b440d41300d1114420003611000500040307400581012a80568030b00d03250440b00c10aa0007035104032a181140e03080040d030100c02040090045500150002c0d003500b94040c000090000500800741c0c900a072080440000c5003115900300c45032007810081045150b80c10040c2c10603c85910030480c540007004043e03c0b210012903107031032000c0c0c1070524540311907c0001040710300602c2a114514a0f540740c0030300c01000711000007002201d00765640d40c90603e407a6005201034920007000213000c107030074002c10f0005107400d03040078003c4008480011501c6131740345c001a9509034141c0e0281e68500c104450b0600c405404420340345d01010308031008a10400c140e80303c5120032020b0010007103480000481e00d4080e05241c000704c00900201d0801e00c5072076180c113070310140d44e8400c1c40201c1c07040c3d1500c4c0021101d4002c0d00d1120741295809606400064038100d2624140f60302c0754015104d0317 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 416337050 1250 416335800 416335807
    0x13030e0108040b18100905010b030d08040203071e0b0409140c0a09030b04050f060c0307020c0105030106080c1303170a090509010e0c0a0c1a04021003110f07020111060103050a023c06 80
    0x41005c58450001c00714001c400104045c00f06006140c2002c14108007602000750010401001d40c4000030b4200c21034511007030b14108140702d21480c40c82c880c0c2c55041607901d40710014000a07805e181f1b80101503140244107540c2c0b816210803246600c40e104840303955000c1212460100086950b02015962083c05401134402121a804080e403d091089a0101c120301c6e005c0148401c07160704101039008283c007130904601d90350400e100609101001003225001a02c00070b00c4440030340c1111010002103501c00c2500320a03001c080c03842040740d00b12144690004106900005161030702c0b00c0c00ba4129120110808101d8560030300790f228030341c060041d00b42030028200009000be0090707800350340045000d511040c0c041c202841040074a881c40321a1400301418411210f07111440401119500a962071003541c1d40c00b89840107a62280c607281c00c3c0803d42c000c24000105000740881c05410942c0700f01c544c901503080d0f02c100450501501c851001c0d00c0220845403075030301403882c0143c40f050300300103007218103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 416338300 1250 416337050 416337073
    0xc1c030e0306042f030a02040b0d0b04060f0b030703120f210507140a021c110f030a020c0102030c0c010e04060b1606051e0606030a1413030e0108040b18 67
    0x1a110090f00c0840319500112120340c40019211181ca140e00800c0350000350201c500c0001a0f81d645004501900c01d40c0d460100704401c0c0c0d03c14048040060344840103241e9842d16003400001804030030780030000302c1d0800860101c1c5140118628003613a0340011403943c00004280200c801120503c8804280010340003864400c3d903c40540350600d0140000204003460403100042040700c0e020308c1c2c05100030b420f100805d1901d801091118503122615101028603148030001c40740c0002410001c00d007801080d080c494240c5c0040000c0c50b03c020241c0860355804841001203035640b007041025003054101c00044121984681080c10303000b400100041490340d22035100c0000d039409449466001c0c00b41300d2201c01082900d02545034090200940801000c0520000030035031500181039500c40d02c00000092480c078660317440302d2160102c03640c800c07900346000780201042c21580710066000ca20504a181d01c60341c4a20311186c440e55001d22140c0d4646c85840600080d142d4281d00d1251502520070f0020 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 416339550 1250 416338300 416338303
    0xc03120e010b0303040906061211030a0b01020304053007050307180605100c0b07050c0c0103050a020c06040c033e010c14210f040e0c120411010305090c1c030e03 71
    0xe010305160000e5088d217042d80143c45141c0303001c0e2160840703041083c5601d86c02001c0701031745d500003241700340451015400c0c40105e00b1481150011503000c051140f030404281608604d540e00b0750640e0641c060000329440001e40d41d40c0c1544101c5901d507010180500002c090500a40c00050f052070000c28815121000903040340c140c1021080004d504840a109204840d01040e400c00310a050841c90400000318590312449825855418181c0358000f082c4440358a504035030801c2c400506a40150400d0b1400010400c86c03840305031481c100e80b402425090781030003d01c040c8a00711030f48949250a2025280400301540300d202e034184001d0550381c0012070200c180708c840030481100074062080ca070340c420022900a488068030108020700041e2803000c1d682c002c0310140c4000ca610604c140d5154160303c0f10310b105001400c8c0d000c2d440c510030320040110124460050038400d0301d0a0001d070740c0300e81030303035036507000354484217510001440c40ea581810310408c014204500a14041012240090119 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 416340800 1250 416339550 416339557
    0xa03060f15020606040501030309051e04090507081506090609060f0d0302060108070f050603041b0b070f1101030e150c0403050312010302010212210a180b090d0c03120e010b0303 78
    0x5106900010485040c29030305001d0b0f035034001800c0341c003004103504544009106104d82d0160324007544800300400c416685c42c4030f40300c4000c0070042081c8108022890810384642407440340d45102d10480b401c100c030703102c68250803501c1488050582c0c020303582c40714100314800a0141a050300400d0a81c0384442e40d460b0400f05485d80c3d80244c0042110754981031a0526000342035004000115900f070302030280380d4038801100d82260b042502241c2118444000c0c2d41c0400c620350140f680081c001603074230104194035940144c0305010b04240c00461040300c0065040d221480c152040c5508040b28036040440120b06854100c01c1000005040c617031a540c4240ca15400380c44003000041802004004540e8100000c840182030054100d00342076030085019030070681c11614041290340007000480a101507400388551030144080c4402110950410443c020001c0d04c22100c00d01480761012001ea0288400081290341aa500f0311a0014101e01e800140b00000c0480865521000c010700d1964040018 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 416342050 1250 416340800 416340809
    0x1e04020625050c0a050607060e010b18070e0111100e011b08011802040b0a1409041806150b0901030e1c021509010c0c030c02040605061309052202060a03060f 69
    0x410400d12040c2002441c0c207090f224070354030904ca50701e8140b025072105d0b01654006580041c02203000302140c10524054000d01010319040740250010341e04140c0c6007110527001707481945800751590690001110070280700c0540c41c2d0254001551100070020980c4034044401c0d14900006920012007540c20f0802030b40c42c0510f000a000800521964104030000300d00390951310341c1189040d1401a15115030f0054210505c24000484030281480c03110300101d41e030b00c4800404c00c000c540700b40c440c4c20200074400ba40070780300c2a1030305051b05031039a20103003400161a80c0e20800e500b40040344004402501d020700485406009126500c4242c414014441c4110001c60700904903142407103d030803c400d0070003440c0f940c003030b07050550390310365541c020600701c4186415280c0303070710340303101d180007007006001c1c1d0fa8401600b0a03400038420b18181703120010031003039800403a070910040d10342e04d01540c2d007114041ea8003104a0000800d0704014504440101440f00c41420080341d04d550f10440700059690300e500 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 416343300 1250 416342050 416342107
    0x42102070b0f0a080906392a0f12160204020f22051e01230c07090608120702030703151505011704080d020c0a14070803031e040206 58
    0x440343ca0f120f030442e0300d45912403181701c02421a89040b90007010200700c8041c0c01d000f078a402243e00c095034241c00302d10b401c210348440242a40c0740f1001000088440c140a40102c0070765141000c04554078001c02c8000d6520303a04002000900c000c61901d04540d440212240c242d44805500f54006844e640007034400308941600e116195010004130020351009101140da61409000301800300da0f80d442425800c000b180281083d89061603c016550280030b110400810040c8412000c80c040707015000b40b02021101041c0c0c0d10b025035414110058502e0f0740187c02c207a80140440c51405031444d000b90040c540000d040394030045e641d4640c0100070384041c1d464078915840b26880c0e081a130141d8404801080c082c1f0300f04608050301c00702215a4400540000c00d070034400075a145c1c10044540540329034203068000d44800b1b000a1402c0721000c02c103200134503041d00610800040c044400700a891046900900010f03559035800c191440c030b000002c100700c1c0d00c05424030442c120603600c1254000180d10b01403 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 416344550 1250 416343300 416343307
    0x60f2e150305010512070905181e0f010c050d020d060b070302010f05010512030a08102621040b0c100c12060e130206070f05060f150603042102070b0f 66
    0x20000302580c0051304000e0040360900c450341c041c10700029010040310a000b00004160700c030140c000482d8034040d10198268412520711280c3c2d40c0c00703a9004110301c08000101d03200418402d09890a840610a0078000b050b0207002a1030410b145030000d02e8182c440b55400600c0544070740c000d040d1070b0060341050700184e55940d044072541507244585809040e00b101c0c0f103003c006043c503025a0b42c1c441c40483e0320070800a400071941141c8115609400b4040030b4000c1280e600080d002010700d82c80d072401d100000e02c550041510121034840349181210b81c258490b614240c101541082c81d0303171021108607120702c190080d04001072024803c0c005980340b0382e940d88010000c1061032406903070040e00244551040e101c2442100a00350200d604240d5055070240e45541140c20300e0301005441707c5000e0594041d5400b0400000782d2549010700c01c04100158901d003920400900c0300c00e00044500424949540c83d0364a00e5025400d00f00d0401070b501d204039032420781c988040c4901504030a00c05c800c03104011 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 416345800 1250 416344550 416344589
    0xd031b0b010e180102070c1e05220f0504020a0521160603150608070c0219120201022103010e150307090b0a0503121b03040e091c02060f2e 61
    0x2100700c0f0350001c0640c40250b0608030b003074883e083c400d0240d1203403030303443e0307411801451820070010440002030034000c0007000310902c4444400c403410324248140e400e9910700300019045800e144038140c003454001c0c0c074160240d42843d05100d11000c1004504945100d583c01c14402e200080042d9091210140300240c08149040300140556401c081440f442d01c0e00d9003014005680e100000c6640401140f5118031410114000300340010b80780c8010301d101500c40500402c03102d07408011288014070070790890301485c03410340c04a80644261600e001145000308010003a45010a40d06508001c82e10000d01000920f071700000d1070100b1640c401c458460725a40c40403558501040040c0042c80103030042c04c0014802500412a4454089484c211030050f400711004d0481c05c0051320040c2007042c031107032058100710804507943d02044c04182c000b036a414001180042c400b180702030140d81110030480e80b40e1902640035484661204d181400e16a0010300d0f0410b50308801618001088440d107001c0030448007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 416347050 1250 416345800 416345821
    0x118080c0a120b0a15050303030c030402011701030302060a05040c0e100e01080c01050409240e0907050402070819140f040305101b0804230d0e010305060d031b0b010e 73
    0x240d800310030590000c2c2d940c1c1001c521041c140581c440c2e90002e0029034076031820789114110030310350010360b01444044108680f021501c4001c43c040d074004d88425042400031103980f003049c007090200a005801201c0807403c2c14004d13400c5550020710914490801d980c440e0f4210050501c21503400004060f6404c00f0006150030131800c501520f9070301c016018100302c0000181c03c610880c401c050400703980d1081d610101d1010b44160580b8110031101105c041d075141000c5061520569400da0540641c40000950380350174030884480c2c550100361103040c00a00d080d003001d4240d503850043d0074002c0d4072030310805410031100140712582c5001081d60321035065040c140d2400f10414142d2200500c2c100341e040c0a84400d2030300d40c04409242c07030310603065595460902c0440c0304013944000e440741f041e10450030007100454141410800795603940d0a218507140110299103080e13403a82e800c10440d0460801191080c3d4800b15081c442078404003a4610a540700800a0300990040345c204076914142b180c046074 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 416348300 1250 416347050 416347069
    0x207150e0604110f030a02060304021f0804051002160219090c051309050403020606101404180506090714070c0506030a02040e010f0803030f060102100606180e040f08090118080c 78
    0x303040c0d0341c0d13021468400004c25a207801604000e44180300c0400003034219618200c0c821314661765015218103a1110810192a000d030681e8103c4090050b003040c20400f07441c83c429a200e8a440426151006526409204407000c1454080414008008020031140143c2c069030450f80e05941c0d48695480e031080f2030420030407043e00402c0e84241071505100c04203500184250b0000c800703c41d00791014a950354141c1d20aa002c81c15600c40240c00301d40001e070000c0d140e10040174469812828010359481804100801e00219000302c040b0346518680e510600358040908001c901c82c8403070403503050f101c04c0000c101e43c0044548165040c0c00103000c1c0702813615a0344c000c2c0103000310100d8000850900c08469100c0c00010300301500c030141c400000b41568400c00050301c6402c0740580c00c002064565200404002e01745448104c80e00203070800003412400c00e01035a00c81ca40000305142d051849588041466100f540014108071240b0390310098101598407600c01030a01a0003402c40c48a01804c0c0500d510 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 416349550 1250 416348300 416348333
    0x3051302030f070914060312031e090c010f0e130c050915030108010b0d0807081806070f0c060c030c060c03090804080f0c060a0f0305040203070801020406030e190309090207150e0604 80
    0xc1704501400010344001482c858600c0506041c0c03522a6214800ca01074500301d00c645480500d0004203103d1051000b084e450341034032007079954076601c0380030480c2554005100f9044c1908590f101c0300203000440c10758400d04055041303141841c6030074140c00000c0e10303a10281c1c0c0301496882c40003004009111091095403400c0340c054030b0f10248241c0503103414400e4001c0c803030081c100c1840040d2002220700c001408500b5500002c0040d034440c1664240b90130440512401112541000800031030203a0148200c01403080d0705035190340181c11701f540ea100c003030012680c2d664240340d1180582c40014405002800282060f04000d1100481d15195203280c030007c2c402c22405001c0c02c220040595030302040c0c074490030b41075003008035a546440c404030f490f0241941c4098040c1d480406e0100b55254540c01c400c008102c2c00e0210352448004a200c4895000c52400c0140845c10310042004a224240c014189450050888448a001000319841a82c00740201c1142e2074020000300030810489a01200551 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 416350800 1250 416349550 416349581
    0x1e0d090503060c0d09080d0207060c11030d090812010b0a0f0309110904020a0305030f070201090f0b031b0c0106090f1503050c01030b04020c1912050f040603051302030f0709 76
    0x51500380425110900034000c6440420300013420800e40c40f860300100015980541044e07919458800800029040b00d901141c4250422940f00071091040e03055600d100c0d0700b00080c510b45110380204000404a00c02c0864500c101802001e60320240529418000c1c41c0110705c156544103c920020302c4200000701440038540f0f011014030204120180c1e420f00184151083c01031381d03c85000042d003650311544018441d120000d000082581800c5c06886414402e032102c40c0107540740c818221000200780a0b04400400500010f00c182da40e03554016842c85010791918982148900e100b82542d5141c5c01825a80e030b1500d990b00c290305c503284200d908445048a122a10505691301c003034840a480821504054940440c1481d613600c943c110303040390b50350504540300c00d04803010345400310a5508096a14140b50300103448541d000300c00716070414003c2c2c81905d00e840c0c100501038000300009020307031030381210814090005840400641c6802d400785030042c0205454a10104141c50801c4040f1105 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 416352050 1250 416350800 416350817
    0xe0d051507051312051006030c0503010c0518090417070c061b02010e0f060409020403111206160305041509050708070f030506130206090303030708090d030507020d0c0c081e0d 77
    0x181030345015805883e030850713001000c0d58035424042d01d440c1e0920410000c8070300c3d1450000421403000004c004840c01079000380540b08040b10140c405002d40003a01c00410151800c100042c50480017150b030041c86844035520b2030008000a4000e03412201007122000101c4c1410b00c480c039001000a005e13202c28a80e41e1510046546c00208030103898070419020342450546e5001c2652040300740c070702820401c10119200d0740d8900702400342c4a0105071541c010801c415001200311030102e00f242c4940a024448680d10b40b0161301100105402402518501e0017161160000c01040c001c00c200e1074018002400c0c90b030b00b0000041d0509071503901043c0d400e07140050400c0003803004901d2513802290380491100712139086c0003040140c401c910301c95525002c000304111340c454006010601807010a8210b5a50300180b05003507003202c1c8140c80320380240c1c1c04440c01e00700c414400d0200314003052184228209081ea034116051400300c40398035440842400030410101d0310f00801c071003060b9500314a0000003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 416353300 1250 416352050 416352067
    0x60306010e1909060617010603110108010609140409080c0c0a050f010f03050a1107030f08060402090618030f06091e0604030f1419030c030e070605190e0d05150705 72
    0x48102e11400001000307901c1c0c0818000b4442d060f0711810082c01c03d01c18514011030500401c07802808a404122103500e044500c3d01515481421302074140c604a45400c03100d541064003042c010401101d52691058880310107900050140700641071503043c03e00103100c003a40340d0b000c21441076910f40059006410032124040d0903a0300006407813425045082c00201c0761102009480034100f21850b4040740200000c82074101a80485612051245580d9030805920380d1000c020507841180c81c115030111061008048007120510003c110900060454004098080c00603042100848400c050783d0001401050703005452042580b1023592200a011240f50650b40a4800c80b03080590f00204000140300320401007102040724211705090780858013440c1e00c0c610080c0500404d0034180000390910042c0c186503440042c55506071a02c0f0b031101c90410b020641c00c001c40c014048040020040c00e0b80707040c846900e400310340030748a900980c05040e90101000300f0055901c0050100401c00400300314850 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 416354550 1250 416353300 416353321
    0x1b0b0f091c03200a0f0308100801060506040510030b04060305010c0f0212040614070501060807230f10052b050f1003020105070f050d0c03020708030708041a04031208060306010e 78
    0x107400b05031001102d0910145440068500042008003c5c06101c19845040a164100d42c05505c2001450008001a034030b404126082e03500034481c80b500300318180018840d0b45007011485818038002e1400182500d05540094292105075000340d9080e551440d1010565a10600480010501d40010200d004041c00320341e100b4415486000c080091303844c03001010780380710310444084c41e810070700034864103071584082a22440c00e8492008405161510011500440d016058030048000c1080d2005140e010511000b0000148402d00b0010f080000c60a20b021500c4d9100c00700e903a2000c201e9420a840bc0302d001282c00240c044006040750030100031251841c2c206c201d0a690f82880c1898503000b5038504a00c3c0c2d1450050018402e0140c10006481541e02c4040352800901075800c580c1043c1d80c0780300550316482540c3c0098088030003040180a80b00c032619161480120041d4800d18040c2d0360740741c4010808070365001c0c0c000905480c0c11301c6039038038080110714058801c4405400305820030b00c0301d08 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 416355800 1250 416354550 416354567
    0x20406050403080903121b06011205060f06031006030b01081b091b25020a270e0f07120b010518040f020d02041113090b0306041b0b0f091c03 62
    0x40281034002135441154a00340100c038002c2d44403d800f591942c801c401320640e468216480d050951040c2000003c2d24a44901c1c50406a50018080d082e9a20f9150892402403001010690144500d540c01d000d504058132480004602999105000b5410100281d0400c0e065030315012000107054a0341c111a6605444d40b604064401c0c0b44940b0745038005241e00303160084c10744405000c1141080340015020f41c8801040d0a4400c40b202c84e101a244c00c40840c1d480d5035500c000c0c04280c1d8a605504003c83c00782e00c061540c00c011030440b00c91002d103400c00b43c50482036801100c400c004e03c4031400100136002007854094136080b903486824541c10034500350140002031000d041014070150320703810754541401c410607464016000b404070754004031900c05180e00052602031211221303100001c10104520900c60304210080140274152540c0d00c5015945c00045110700310304a80782c80000d80000444014050080080145a15040041c04015144000090115511b41c1c0b45030f2410000394800e210 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 416357050 1250 416355800 416355803
    0x151f0e010f1502010f110301180509031e1201060306150f020d0e011b03020f0c030a020a0506090112050109230601120509121206040506180109090314070c0303030f020406050403 78
    0x300b100621640d5000c030301400300d00109041c090b00c0d107034903441070400c018025030507900030780910810031220b40007003c2220030813540420700e0341080c400040d001042c8002e410709141030342e02135401e00120002c00c41d03113414285c0c40180483c1d03a1303420400c030210300709030700e10380c410f032113042045e941544031002075181c1210003044001c0011171405c40e0150fa02802c0141d401040c0c0d83d04070f03104010140b502969070b0800c0340b218040b5104030070103c0200e150015454490f154007030450411240703498207000c00c0e40c0111081030f0502ca5035102000304241540300701e034001c04a17440049204600a91400b200c034203030611b002071070445042084000c2e60000740a1620f0b14449000090740c0c3d032000c000c02c1c20060310400c20a00000c00040e400d1120b00c42c081c00c41e02814088604010546034101000402c2c1d260780d00001711480303244010051441e031035000300c6005020b41011071a83c0f180d01078103195640200412900101007400601c14190300d80300f148908110f50108619081c2000340160882c06107100 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 416358300 1250 416357050 416357069
    0x7180303120204030501090506010509150d0f050c03060406140c0408031c0e01090b1e09060106050a0504050d0302030304031101020c120904060b040f0e060d030804030c0302151f0e010f 81
    0x407010002400da604070380040d90090000c000344a054030708503031074660078130030148641c5c070440100700f1041c8410844e99024070010034606800e59a503803006005120106c090b02c1038060000c40324120349007445201c0c0300c1e5102d85800190360039202098060810054880c0c18804014001440040d60001c102c41c185400344030b107034994400004a15001d48001035030b2010725420003516a00b0080c801085601800542c1003400b204813030010a240d02c40811034500040e540000010011580070340002e00ea082290300e030180c40d1985840c00b2503803580c02d4500842c0149d02c0001080203060340000d070694280d078800001d42c50128140c800580d18402d07140740041d10480005e42000c9940e4550040d0010284040302a07240ca0b51002e080350991100e1007074141070f580c49c00016046240024030002007076415168640300e9200ca403000c644401c0c42c00011001e51080c1880e168030102c00404e141e2107040803441904c6203842074800c07a0420344450380800e0309801160014441c46001080810a03160000b0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 416359550 1250 416358300 416358317
    0x714071401080a051f14090105030a0c06181a0403030e09011406091306270504050604060b06070b160f0908030306062203061d0a020f060f0714060a0507180303 70
    0x17041c01c0d022840c080d45d0241118250140000c1003000380c81202044882152410256039841e424151201903140004103000000d1500b0b0106a014032a1070702c8051030900c1440e15140c440708500c4001c0c80208011114003008a03040003015071114a0702c0c00c50506075501802549031440d1400301a07990b00150f4031800c00071560204549034818283c40c1502403110601c08035590300c140c1c1424590a805481c03201214006201120119000d4113014540c0100101440d6555444040082025842c807543c410300c00c020301d6010a000c03000e22801400c00c046020300076107000e13070701411908403c8000c000f80480300c2c500700a86071021040c0d0350b1124003650b8296440311000ea023102c050740510b100e0780d4000034028000c4148041c0c2c0d4440d4480207900c00c0a1204500c02020150f950201c40d4402507008255034950072560034010090b0105190a4128505050319580c41c0d405000c80318502c6c04080d8030840402c40c1d12200c5000e215005495420080d0088120100c4104c0308421400080e06215015 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 416360800 1250 416359550 416359561
    0x114061c0b1302031312090320130509010c0305061503060d0302010209030a0804080d0905130e121c06060807081503070f0b070c080c0102190501110714071401080a05 73
    0x10b41042119440d600c000311355074a0300e40c03d400d8040403502419146c0c9041101203040e6030f40600c6d2103105807030b008410400d16108560030b402003806d051600942040c02113052490348451402681d02807400d000c000300303a800c20307124000e00f00d503c0280001c4c800c1e1142c8441a0b010407420085a030000000c1c0c0b0020b50851032420280d0191250181054052103524120001d02a50001501c10741c0d1488055994641280404a48600040c0106a0f0117030690b5003881e00741c040c99104c4202041c0318070542c0e100714200d400e100c00d1a0483d540702d40c54500d601407081a550030500c246e8026000c00e040c081100d09000030020100600145858a141c0c03481c0b0200e0301e15602048000e00400d00c882c000408651034040803049908824030031203174114040f1000c2441a8089454050404180d0080c00b030380f000540d801001e40a003250a0300c036956102d03607014007511844000c0c00503c0c0903041d52403580440088161030024142c0c00400070202c520707400e8400b607038080e0015400c80c0e1803000200762501c41 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 416362050 1250 416360800 416360809
    0x405060609030f0703060b18130203160801060f0b04060813110a0314062a0f0d0c02010e0d0906080f090c0915120a050303181e060114061c0b 62
    0x840c0e03011941032041c8151640c1a040004483c81034911404051001c0e440300d60501a00070507248801300d81d07008507000100300318610744270b0300031050005040b03e02d1551080d00100c501c08041d0490000ca0351960014031085121005141c0104049060030780b500c1c1c6004801460701801404410269000707450301c00134010f044500b41404400142030850140d62840e021001c441c1c0d17481c01300c865015180010f940c04094100c82d10352100d60314060341780d40c405220032040c82c0e8004a0182060803082c0b003450b81c41c44a51107a98036a0b00395030000625038101c0132115140c12010603a100c10000d01e80300502445510a1610b03420007900600b4268588a000c1c42606007240c2400e0550085071401c1007003050100055040450300c07041c4d804544078040004120707110041c1d000098410b510030030101d4041c000d8101b405503c4d030341c40d8007621100c03280030750001028080445000b0145d440080140b00d00c40200c203204400301d10484829140c43c511503c02c00c035619002060140d030313a9a413556002540c88 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 416363300 1250 416362050 416362057
    0x7050c01020a030617031602040b0301150806040317070905040b0d023021210906090c012109060b0a08100e0a0f1205040905090f0c040c0c0204050606 66
    0x14140081d51038001c12240280140701c0c9100e208030300302d545034a040c01c4001c04002c0b203c2d5110180342d407405882c419005c1c070010305084891703140c1541d40c0b5400c41000402803400007014111502c09031030641004d003402003124541c00442d1118080e80300500c4034843c2c005803584101c0b4415100480d611440800184805440c00c8010b03401114010318043c04081034000400c80c002050090201c0302e110501d0b06946d881120402c4e1000003400c04916030300717000c1d40e02034005000310400507a21144603860a0003244000da83c0076405901880500c00242c0d010311070200c40c00b400b86411110000c0b015a404550b400c0103d2000100c3d940d5280034050280780c2c0c100091040e005401c0850310303541c07104210b5803504007403d00311000d45031401e15101d10744045104401644c02080d1600e01c980c1b180c50325802d0789210140e00302400010000022001000d0250340c2c0b065a00318003404014006600580c100010064403511030361800070903511311904184543c10302130b0190b8001410f9580c4202252940c071 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 416364550 1250 416363300 416363317
    0xf20010f1e11090f01120b3006150d1103030f0403051204050d0b07050d05040f050c030d200316060b13020903070e041b03030305070e060f0a05030705 66
    0x242000d80ca071a59030062070581c0c403100c21503a810403180d420404a010075000b0300d00c001e54060081c0c002802d2a6200c2d0010b080c02d54044c2c0400a1000040c4d000101c2c1414850152403201c07802c2800d850b01e41d00c400c0380481890f5110806049685003100e0000021244442c07058410804d50b841e0005005200c10a40d02065028048954440340207e41400c00d41040c40100c0b214810855010b44602d07030002034a00f112006030a8520708030850b030384c150304584000c0080b01040020301040c00c1c049558005c55000c4d60185244020340702e90b901b0424142019038001c1030280d40100314a800581d400207105900c003449020000948009000146c110f200e0303202c08245101603140d84100f40a01079101d890b00311011a440645403050810f8042640280840c0a80c9074003d0881000b4010000c042c19511070320408401851866041c21140301b00426001900000e81e15000c10000c1c80d080b80c0d960a40b03c000721402c0c2e0900c0c405c400a905244240e0a10500700b0001001240040b4000c0c0c0c20382d80c024 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 416365800 1250 416364550 416364581
    0x3120e01020c06010f051908100207050312010906051c02030c01050901020c060f130f03051207030c0b1302130920211605060f0a140c01020417010506010f2001 70
    0x4e5a540501c089007000902896100f2001d0780ea080c1c43c40c0304188a00412140d04030040c2080c1240300c80108002d40120f58242d84500040103030007030003480c021a0313501804d40b0380d000060841c188800c0c0b01516460240c41122040314110200160f03a0005002260381c40c00d1900c1c40e40c4494400c0102d0034075400010441e0424004102181c01c0c08504004d02101c402030020f8803003090380d401e004a11640345201c0a0580d8120084501420300c202000b800d166000c0e081000141d00f169580e1002c007a412118010107940c0340340144110700d01f11300d1007040c5890340c51040c002400b83d51641e0f4003522000c8440307901119241c00b00e00060310b4400d05000c03001da10b490310082100140c400d80e41c444604540c11910b40418610104441c6131810036107985848100819003041e002000035900d003c003e0200340e15030441803040b414001c2090006202030a200314080600d0000c1500031400d441d00503041034180661140059009a481494400000300203484208004000d548481c0180790000484900c03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 416366906 1106 416365800 416365813
    0x6010c021503041110051b2109032b11030a090b16050d020a03020105060d0f1e050601031a0703050108331302091303120e01020c 57
    0x80c0c0300b03240c404004d42d9144002040d20500c6950030340040d00008001028041008400c0010500d000052054a154100e541200125000c9010300b5034804200c40800796820000c51102d42c19662494981c40452201c0c0100610303071061510100b10b804501d80b02c00b04000044a800d10166a1040c922508006c50030300325a124411501044007141e80d20000304100f407001455160b200d800600880c41c2500c1d019080d11001401c5070f02ca410290b104001107110608481c4102b0390000f80326940a060b441401000440c4200c050120300c5200300110403c000e015a02c20304c40090000e4200b9031755001c00880c2a241701b4000c0fa1040e8001c010400144102203244441024000302007200c00c80b880c90b40321040364411555003880d000c110380e0300415402d040082c290009441001c0290141d41030702c000d00010b2051034180b83d8156130742414152035900394140ea45841184064403070 = true := by decide +kernel

theorem cover : BRFrame.Cov 416187050 416366906 := by
  have h0 := BRFrame.cov_init 416187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 416187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 416187050 ≤ n) (h2 : n < 416366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
