-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1108
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:16:40.884178+00:00
-- url     : https://prove2.me/submissions/5cdbd212-0e14-4599-9113-5bd59508d5da

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 199100719 ≤ n < 199280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 199101969 1250 199100719 199100723
    0x105030c0d0206070b1609150e060a0e04050c12090102040e070f02030c120d0c09150e060403050115031709010804022b030815120c01050a0c0605010305010f0b040b0d 73
    0x1180c81c1c11501c04a0914010204080c01c07182855042090f2600e04102e481c15100150360741d00c4140780c0700c041c2490000300350705901d00000c400c609412120308103100248150f500c0d90511038088030b05030300042d0036642e084816030aa031101140e000c4801022032001500603461000035030500303041200100302c000e0010502401c001d020f8840b885600d00a004031010503c00d80c096844840c8509486403040d4401042503602a107401c4084201c10b01c503a4074038060301e509140d1a03908403000d500443c0e58a506900c030b142d101702c0400001002807000d00c00c00b40e075900f00a030980c601e40c0c030350b00340880c0120b03e454001c4011101086502e08681e8440e10781e0340d210703604070b40005111400040941c406808090203105a0208036000000e15401c0000b09100c5c43d010040d480707440d030042c0140510b100100800c520301c0d6011203070521031507001e6400f030305072a24070346019800f0802d2034a43e1000d031503003a8015211650344224840f0100054090a02130560540702408120021030124121007030000340 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 199103219 1250 199101969 199101979
    0x42d0603050a030302030c040f03050106030201110109050601061206090f0b030d14070201200109030c0209090a0c17010b030d050c060109091e02040e030a02072105030316030902120a060b04050105030c 88
    0x5806441c280e0250b88c040d0a0b915091030714980c0320b03d001d80c0200154042a40454002940c0900980c414012514840c3c3d0143c05030a240c1d20706042900c10a4165581c0d140d06615141b01080501041c03081740c3c007640442e04040381c1601542c0c05d1500f0a58500400410000040ca44c0b041040751070045610455083c070b48241d00703011080007114175156a18203104a5420802900145a40001c0000c0010b008a0703820080e6101c041606607540042200103040d402005420007010030b600e00c03000074007000d850000c2010304903075001904006001582c0d070040b03940803403202041041002000d01401014508010025064803404542d0302880014001c00000c03038500003c54030b542e000f04002d001d8034405c40740c07101000c0340040c0d00c0d0000d50042421003481d80244400d401081507224a460b0741100c0030f0741c610703210170000750511403070b4440003000e2585442e11280142c5882c141c04a040c10004040c01a0040d9842c0c4001601c004007100b502c62814280144202d0303601250600c604003040307070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 199104469 1250 199103219 199103221
    0xa15110106030c120606051009030809040e0a3c06150b160519030c0305031e0f010311030d020d0e0f06030a05060102060a0c0e010309020f042d0603050a03030203 71
    0x20558050012500001c2c452102c100c0d0008140c0c8040c0404020310b0720503c000e1060301e032148240a40503100180070b40024100715820004502200001e0850f03040103080800d000d00b81002c5603190a41002c022100c1c450680740320740c1407900d400a4040c50031040502c01c41d04c40040e5040600c44801443d003d000c080d42c4140b0021035403098912140205480c8a80a84072031840382c2c2c2d0b10348103a0080781a6803d000320003031000c142130305149000c1c0c880c3d850343352403101c910561411182608001c2c021a40031390060b40b600d07212100041114800c000c090450b145170f40c107625086024034101e00c02a4065402401d00030600c0d1740220f0180c050005501c0c00303141844403400021488903030161840d030841d1000040c0584a410b540000340b14480070b03001c481c4140c8503400c103417003200c0d9400541d400141003d40303a0020703588039410854181f40000c0148206040980000301164004161120826000300380044070202c1c400f04815408402102088003628603140c091b110103074081c008080641c000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 199105719 1250 199104469 199104497
    0x611010507020a08090d0c0b0306040e01200f130803070606060c03021005100b0304050a1101021f1802030303190e0a02090a0209030304080f0105010617060d030c11040c080609060a15 80
    0x3101c483c807685d0001f60031004e0f2a5940c0300140141d000707aa050b405075042010400745440f05002d00324204c0c6003019001d1140c250f44502140a4201031060061058100303d000e102c01c1d40c071032141c3c0244c0581030156079540c07078910700141224960b0b440030052068050f44103000c80c0d000b00703541c19142014080881c035a0340d043c003440c188900030b4008411040e80803080c031091260014840482910079041046030b070b0b071201c006907960000e514502000820502140c225003009401c81240348012480040e54185203900090030364001b01c030034800b5101c07040043c0c4ad20b401c841c05030191801c00e48025004c15103076030f0003081d085040244001c2250341c00043c511200d8034104100c80050614800740e443c2d102d4040300c6a03004c0c1c1803e1107013500046842c00f15079880350104041e140a45002000685240319950313058070080050241a1410708002038034010390344650003500b0300d10045541d200c04a00d00704082102046001e0841c40c000c001c05c000601c80c00c09182d11801940320b1074106000d04001003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 199106969 1250 199105719 199105729
    0x1150519050904181511030109180609030e030606220203100302060f07060506030102090a0302010f02010f061412060c030f040503090d0b0a0506040e070510030908040f0611010507020a0809 83
    0xa090598119103881c040302402d49079907141901035842600d104411038008080a0b05031b682034207240210341010001000604103035804518990784010480c181414661241d134111850b50b54160041035084245100c05c0ca400c1c40080d0340400215258950b1030710b900700000700c50004172600c0741c41d10360000126a400000c0f411140c0190703030090405544102c055601829174000c984104c642038140008100070313140c180241c0c0c1d045000580f400c5809071441d00111041c405044101c0b0544d503039117a0700300500d4043e01442d00900041490444000c0c1b200040c4058994a442c03910034941205003401080c0030391000710707504044040d88101a940382e078200a8214450109030541c81800081c52404000c9090f0126100d0340116404201079035540d0148000d50707190207072410a80c4c20404041c011841c0c558002c81101d0030510700001c408103203544000b41c5a1150300004480e42c0040c000300002544240c00101c0e96031400001d00080c00d2121001e56180349104009094403000b0500040e270703440d1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 199108219 1250 199106969 199106977
    0x3070807050115061115190c0918020301180903090e100302010e09040308070f030b0402070b01080d0c080406120f14100b0403150f1811090115051905 66
    0x8080515034511891a00074000c02d04480c640c01c40c100007000002e1181c0c0a00f544446024002000e17007041020079083c0601c00030020701d043d2081103d07401c4c25100409503c03a8095111042c0c90703001c03c4500741080c0115401c002e80c20b9aa20500410052142e02c201d400102c001141c142004103045500746020344458001da0080800800040b04128000503038050420807603000b0f8890300c005004400500c189010201c6004d0042445400440c8809124802d14170740710344a4580055085240000101030342d110301c0741919201d100790014440c4540910502208109071309042d0185410340d51501c100740a10b114100920410707100c4004252000c2d00a018200860170b0200030031248000042410301094411085030f040312540071801c10a08421070f0103903a000b061051040341e0020080020f0900c0000c2c40401c291140000038480030070500c400341c2240310f2000518202240000c1c42400710050b030280f601c90b824a503070f0030a8560020704541411444610182c00d900078804c0030b03101841 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 199109469 1250 199108219 199108223
    0x605040b07140a0b060405010b03010521010b030f100c050403020d0602400b0a050924030c0d0b0a06050f0a030e030f0d05060604060212220b0a020d0c080306120307 72
    0x75422018080101c09504c1c6807207140120743c00c000b0380e41c0b02c15095403580002d0141c00c1e00310500031047c0801040096156841c3c0700c0d50000820400300000100b4100203980511001540c45121040b854042a000e01201c00342140f034101e0825145400181c000b010b1070030060f04980e40043c10141d90b00009441d07203060a05040c03101801103c40c1d030170786450880070500c0219075044030750100d1866a80d004a03103005e0030560301c02c0c0c1002c0c03402d42000013030074442c881203400c0364407110b0610280860783c010718490b07040b42c031509465112103030030b8506440300c2c0c05082e0b1041920700c200f44102c98024058901a40d94440d00980703901c075004040c0d00038012500031194520001c180515110101001000181c80c40311042c42641c8a1406000640c002c81c015000980c10400c2001c5042c0b40000c0a0144043c511280000004000304108158016500401c6442c0c40020f541f00115404100c02860892145041c0003858a0f940302c81100e4040030b801c0c0c52050000005c03014060504000f500c11140e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 199110719 1250 199109469 199109473
    0xd090611011812020f0a02010801050411090312040e010e010320030f07030c1404090f0209250914030f0607030c0c0602030c04031109070c030c080409090f17040605040b0714 76
    0x4072400c1010880900c07540c400011701c124845050601d0000c90b04c40b50595060b1140da8160342454100000781469400d001410b4030306008500940d0750811401781940c0c80e02890664450400e60605624001600184a00d412400040001810143c515a12100c0f51040c02024035070a50010b821b0000a480080c0d007449121000310074000003003d094100c884500c50b065080041d8002d1000f507911501d0042c0800101c080401c01505022082d19444041402d8008210500410780ca00d40401d0307411610000345d00031428884403c1d40c840785c00c0e480500310001e103550811007405a603aa00000c008008064541d030121a0050080c102e200715103034010f20540d20391030301445c80c8059070011320055a014200c44007800d0f5074145a066180510802da80380e118240300342c1c405580300c485a040440d1207000400000030b48994503c25001c84900c43c84d50303070b94198036600b081c45d855007880d80207207000e84042108008544d00802200c1c00c8070b524911507900e80b0817138140f40b03041100c0c54410a00038 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 199111969 1250 199110719 199110761
    0xc08030711060153010c03050a050405030a0c0804080d32030705090117040501050403080705130612020409050f041b050109050603090f0706020d09080d09061101 71
    0x103400c9080111944080d03812512107a1360342d40c80c80d50b1003c07050500e140034406940b200c200d82000c507100c22924034181040908000b0318581e158203500c0358881d00d10b0243d5542c81c50752003060341400ba05405c51050b010610050070292102a1280f288000304800d020300c00001170204982041540d0003010280f041e900c09451080000d400140c4a40c0e1008215041c100135204103120b00625820014421449034210361791054269902d60050342c0c030a05203e0508014008000031200e50783c440c91240300003207941e08240c500988121800741400c414010b041c404012020705445100003118080d140c40382d268007060b05840c00a104031b1300404003481c144010041c42c02c0d100c0c20450301441c8a04046003094107a5840410269220300030315001500c0408100100d281c0b0901031500306044c04141c2d00d00d01c2088500328070b00441988601c3c09a00002c03014130205030821100c1c1c004000304009406006042c140007014425180900c4007888001c007404102080c003588084010700007505a2252 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 199113219 1250 199111969 199111981
    0x171609020a0207090515031c1e030b04020f040e070e060f16061406191d04030e03010504060b0103150b16050f070308190f0c1e0204090c0e1305060a09030c0803 70
    0x3c02c055181b500b8000c0c465204403e1028071031401642d0f891100380e42d0240406945081e101c601000c880015041648031401014255a540b00030100712030a0750b08a641c40e4a48450030742c04d840010700603420320800c2d4001009070b4580e40c0803580c0300646854415030b0350041d0717040030030b50390001100500064544811551905122561240101c0d0105c0c0e9154034041c1101c02c3e00e002151a001d1121000601c0010400090418085540062003418454503480c0c41501180c00c449080754103a60241c0c44800d01503065806203d0500102d09a5900070281800d008440089104011180b20942010a284018444140409045000321000f0398a2031580c905041207a42c00c220700b0400a001c0350140c0580700c40c01005018070303036495a207440d42c880d402c6454552071881d418803103440742c4103288a0318006a8813485040c0040344601e01a0319040d08050407510300140041400b00c00c0d61100b4008804035000003003040d8009403613000401c10411a1500303c0301178021100042c2240004030910074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 199114469 1250 199113219 199113241
    0x209060301060b0c030d0b09040c0302040b01120203070207090609090b0112060603020a0602010b040b0405130b0c130602031803060402011706030102040f030303020d0c0906140c030c06040c171609020a02070905 92
    0x306c80459010300110201c3c20421000f82019900284280b04004d42080181485e4100f1110035805051035402501c0e1007000f003050740d008440d03490050304420f406000030b06861003007002030b0042040401071203515942d4102e075082d060186154a021610000d41009000c1c0c1090b4040c2d81c0c00760800c01c0c1256a03810103806804181c140030300c00da04042490805084c02c0c0300b0380b80f14043c0741446441380701d078545400707050fa8006030918030318980810040f145100c0301c80419000340031940c0115910702c403c0040180710400000424880e4101905120150781d1000011907151ba02c1c2c01c10340080d4940800190082c89a40d2108035510003d0b80300005164056024003012001541e090005d880c094a0444600450340600c0c40030034003102031500ca40029001030a4060f8011044a2070f080114104515040c0111000c555900b201340003400b96640d510103101c030049002c0c00038040c0400c11445a00c0e80d00c51802074000e1680e000c90011045842084030200400009808010314100001081 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 199115719 1250 199114469 199114477
    0x30a1d18070801090b10030c020c0a080a170a02030406210f020a12050105060406050702010e0a080706020f072102043b120a0302031b0310180e07030209060301060b0c03 74
    0x9000301c2c60300000040c041042d8040d803a03040200400040e80038100e01c5090740140f400d09207140841c4691050710f80b02d5112340f002c03c0082c1c03450000a10321014a0b180101085601070580c0419400600c40d50501c190000292019143c0508044282c4000c81800003094070052103201501400c3c9075a034160122198000c01120050b03690b00e4500e5441d511803503050b81c0c401e215850300514200700400103070b1320400c040c0001610501d0080d03210070390340e03000801d90b451541200b406504442004c210181d0104092a1841c08500140440301c1c075141d060130681c2d031010100c001a2131300b003030340038210340e2550b0200c885254485070000040a0003108020550f40804d0908048144c0c0504582103480001d0360090a05040c061179240210690044005e074101606816071202100d010356083c1034440040c5201c1c103a1410740072055464140d1014114504c9100c00e0700c06842d01da00c417060403e000c22810240c0e90140e5100c1016180d040100c0e0040c04d451b4007a2080d448041021240070f4400320040c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 199116969 1250 199115719 199115731
    0x4090203010f170d05090a090504050601141f0e040609020c06060310020c0604110d050f0f010609232a0c0d09051c0501091205070308070f02030a1d18 66
    0xa0307506500e660f000800001c03400303282030310382d402007000880d0944908018050b044020b4441c1c000c07170350340c3c0003040c0584800b500c048640b074200703000502454216034200c400030701c8101c1c0e00000003081580c075080900c035120f114100700031200c11900170540340c0c0d4018600a2010340701c01c40d614280710b03c12544860f416a4903503c00d00407600e02013200001402515284c0c1c0550020384180d855a0f0380711082144084e07240d6401481ca8100100070403401c2c0040001501e003040074088500c285d07460982115025007010b04514a826204201310741500c06041040c00c6529100300c1d2501c03100306400042068420b10403c950034000e0356101600000c1c0a1b044202c044401c403488240032200540d00300038140681504100785148108504032481691550140160b000051544135900c4103200380c8034603014040422000501071082683c050492541306220745041041800083d40080d00d030720540850b0703002c210708100c0c0d00ca01040c202a002e401034100603c4041204981ea400b42e41088003120a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 199118219 1250 199116969 199116989
    0xa0206041e0501050c070b0304170a050307031113090203060f0a0f030b151f091a03040b060102010e0c010c111306030b0c0405060d180c030b01050312090603070807050706020409020301 81
    0x9595401303102960400c00040c8054142903090a4110906400082007503032507500c682d0482e651042024000c00c0030f075045030b407400e41d2480d00da64041e094a51102c1001b0032030800300200c04000c0382c1e2000500a4038485003026990b070302c83c000043c0341d4460007004281c3c440b402c0707a40000c44e07800f1043c61400710b82c8580d01103501d039a0781d507140e08014000f200f1560b402114480c064080780305c81e540e6840c3c0300c3d072503801c0c5581216150201c1d5200c520341c0c00164002040d002051000344903002400301d500c41000d200078080c41c0100d00c04a034031112040002030501c2803480741401040481ea141c0900124007901628100c0306100e40f4001034645440142c0b070101c18031003c58180c0c4040c40c100c0702528009820280351a042c550518002e1100c18425680000c08001a400144480600b00000d41c0103800e43c543d20350500003018105490390840d2880078904201550150719044180ea0b0721046a0400103401d5460102c00d544504c6801001480d041c0f0005000c12000e00b80d0307014505990190751 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 199119469 1250 199118219 199118279
    0x1110d0b06160206130306021c180201091a0702040e03030a0b01020a11011d0d03031401050301090f0f0602072f0105120a0b030102040807170111030610030c020a020604 74
    0x1040c01414403829060000c0c02c02c0107500d81016040000040008040c080800d4007159680d4070b0742c804a0300004111615111044900e246610703132406420198030700300e00c442c0340d490b48650010b00032603800e104009102105080c288101ca00c001e09454103990041e1080c4103403902404481c0d20b030ba004507010300c0c1f010303c2d00c1c081000952000420210725035002d0441200445003c00655555100c0c070485040750004c08001386140c1c07500f25140b0705c10351198601140b40c0440c501394140607141604414066854603a28101007106006602450b5070031122014184d1890b04108019105603000504019003041800400311000c122100c011752103d001c00c1c68403282030b00111890710940131281100d102c2c07013000c00c081d200c0d541d026258a00e0010001850b00355501c2d07005050101c998003980000030181c0c4c1c80b000100c000c1c02a03d00281350030300224518902040098032174040068a0700415584254104c0b03035600802c81d00c0d6115800801090302c481c0d848000103000d0301c0c041c0506102d007440113 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 199120719 1250 199119469 199119491
    0x40602030304020a0914040303052d04051e0a020402071505040c0305070605071110230a030e061e040317040803041103010b0105043b01061b03050405101101110d 71
    0xc070882070307058808a0411b20315101c50b02d04070007410000d028242d45030341002c3d80080c2607041d030382c884c0403408001e241c0021900d01030903c0e07030408134800ca0582050314400074918141c0170100300380e035180780c0c119801038a0304501d0403d80f01c03603040250103240701441c0106100a1045004070042160f00c28400c407034059031a00c00c1164140140100108901000000c0c8503007841e04001c40c0c00e800031036250500c0300d8100000c130080c1703000e85e9610111148000041101d04590305014803032112482038000d00a508100c040000d21600c54070090242c0c3c44004d001c281054450f5000800c5105401c0740700466080904207204076520903582150a4400400c10742c1184c00e06003d0000c001005031074050801b4540043c2d4507205540c903810001503030540400407850005411684040e1500b0000508a58100240903010010822401ea001c4111020010000354840121400e9a00179075a190307003a041e0710001d840a80f0780c0c2040c9401942440706c404c044c4040d11020385030110545409000b900181 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 199121969 1250 199120719 199120721
    0x30a0305013209060f090f0718050d020d1523010e070c020603060301020f0c03090a0509134d0d080d0203130c060207031b060e0411040506040602030304020a09 70
    0x1c18002aa200d9480403402c1e0070703141c003c119560041000d44a05001100b241c001100b8000407500183c0804800050044043d400f0701d400c1c0c0301d441303c91090358482d82080c0014080400700c040c003d01c40c032298078011b010420000210026400c40ca0000e11030082c402401b00080c9551201e500d41c502c1b81d060000030300c40c02c0c06a52500a28207505d444010005039000e01c215544001d200e00c0d0159020408002c00442c448000c1c040d042c2103102541d1102c002500b00b00c0502445e500441c0300b48a417605000002406041400181d40d00c094015401980202d4401c2917070518070103006500c3d140e035496014281004500541c4900c211229544251036000700001c1d0020b020b4050803e09041c01101200d150541c001c5411035264906140c12102c00c1c0d4415038440f8464014100581021030100204154004c1c101c42c800060000320b00841e0900d40020160000512440e104586031900c0c000b0108960040382d005c2e02004e010142d4036038035050069038a9105440490080200c0840010b2401d02 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 199123219 1250 199121969 199122029
    0x8070206090306090a0521031b1608070b0a020a02060705090109030b01090f0501090c090612090204020408070311090609040f0c1e0806130503040317250b090c01080720030a030501 79
    0x4034a10260031900c9da01c0110455a07503070103151407454410030100c145901d141e201c8403c01445115071560b505807030b241c05211410081c00d2001c41c1801800703803040058010030301e154420501e140070781d00c6a2226004035026095540050700e9070300d4000010445070203d8101c01d0f2010b584400522803a6070316600c143c02c032200c804084c4001100c010b410301c04c0500c95030820922829219002c03650b4001c2e45c000401b03d0344254820225036106180400410145a001140c2501c1c110381c0c8101901d0030b0700104803040b400802c0140076040d4403103004108451440320101800040381454003c050f030404070f041e541010f001c0ca0015100702400158066001050602402da118000e5410b052961707071012440e2071070005001582c0418881c220f501e2201507041280c4001414020043c2041410181031034440503040070000e42110308803c1c2c040c0d801c20000381d00f0800d40c4c0f401e86521441e08004030303280981c5803c1c45c14140000a0b0b01411305030b240d08524160b803070074107440e0803003a8588000f040c5640d03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 199124469 1250 199123219 199123273
    0x51003020306010506071b120c0f030f060c120c030203271509100c09051309050d08060102030708040306061d16180815040605090f070308070206090306090a05 70
    0x700c01e400500c03c03030030040060551b081c45a171402c40340c5210080380f03c046c90381682000070014202c014810a202c003144040001b80f0040301c0511815045458001074008a04000340220b40c030344008180052081c0e03e40503022105090800c40d085c00010000c0103984180c5001204005140c0005404c84451b4400e15080310000010310100c1c0800030340412441c00144140d000e4080d92003c006c15080b1405014480c0c2c40b1591501c0340c0c036080400308840000c84803c205407440c0303000d48510000d1300005420109502c5070400c090259200e1004038518841d46600070400c20340804c0000c00c10100d03400520540b02901d04103400600c81801c1041030500c11103c29a1044130041200603c60042c114546408030214900694a44810b68289007141d01c01c00010742160036030400080c03001c0d43c49003640104001000e400d0354182030381c4941e500c00450101810380f0708001307120011550b5000450700303c080080c1c01d079081494042c104a480d403502c8401070780c190203207102c1d0300d65800c50b414001038900 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 199125719 1250 199124469 199124473
    0x809221b0512040c030803130312020c030a120221090c03010b01021b01051306020c03010c020304080c0603150a03050703050c0906091303030603050709020a090b0f03010e091f0c030510030203 84
    0x14865550b5a0070540a80141c0b110400088044086210384000f140314400f0012803250205051030020400d03035030b40081074080c41c4140004640c4200201c01c459030404946000a90301000a0103600244644400c1c500b2500e90750928481c0c00c9081d1a24520541250741070f20842c250728024107080c1d402805110780180c00114444011807a00c0850343e44082040c50064144401c1c4a020718245a0381d0b0040307005a40800c820300f04514003401040085135492002d18180307031404060540e0350007503c511501c15680031001032240040604035071030480004043c01c03c004e03a6810425140c90b0203000998080c022902d51a9250074442a03040c01008042c040021942d01e010380d81070f0444e0303003210807010907441d00310010101d20304000c2d5a018054500c4010382d10140c0000147c801c0c101d0341d2181a4446060082d09408170162003680e044400e1801829599502d0b207503858100224462801d80c100381d0320000903603001445d03001015080c0151020461071301c504840c45071258a5110080d410707 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 199126969 1250 199125719 199125727
    0x60906120c1e0903011803120c020319090f0e0108120903010e06150a090e0606010c050a05070816050301021305011206083f030703090809221b05 64
    0x3881065400754000c91024a103030501c080c04082c03440380e090402030b0048400020070420403a290071302c12600c3e01403520907003c1c1d48000c142c0e409000004482480502c041d914480303240054024811640f034005205400843c5440400c4040d0102a86004a0701201c00f01400070818060820303406058400d4000200000524402c101c0031550048446581554891860340c203000d00c20003020303008407107892412100d0100311091100c8803065601c100d04140c108401860092000b18400750020020b10306030503c0405400e00510b00000722b40020654482d82c013001071402404a80106124103900f0060b070030744d0303444d0300700340c240d008450700c0c10b816007104070003041035601a4041391450310403d000480c00d01d0b43c0e44107081c00c0c103850b4948035003a504202a5000b1032000c0320000015058004546850b82c2c0e180703042000d00e800028448428181c1e902d04c214180140381056444081006008940380030001d1040200044c20000c1c0300c09150901c4020b09004c80d4854480031401070b41e0341c5490030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 199128219 1250 199126969 199126987
    0xf05030a0905060307230702040e010605040f0c090302041a060307090f120822080a0b0118050103200a0e0703020d0b0402030c070215070206040b120a0501060801060f12051303020606060906 83
    0xa040c500c06c402d8143d0601003000704010707242c0d070103000f1044030410b000080052404d401d00042e6014044240c1d0641c4c41c01c050303140140d40020b255825030780c05450000321a02000b801d1240d17900c0100c00e140e4400c8001c01000300310350307009080000340d8a0150000462a41d910f02039004a10801c5000303000701024810100c0310400380b1183e0895090411302c21400e42e9642c0d0850b400c100301031000b0b5a04c0d11180c001031103c50a030801603000d541c01904200304d40d616540310a1341003c0d50358440c01c920315031258000d030155120991803019014550311206107080014015008bd4003540d0f4481142e400d00d050400d113490640700f580c0c481c030292a02d00d407800c80c860342040400094502d0b584080441070000c0405600c0c0c00000c0d001500041030181d50300e01c2505120480f11500500551001e070401005000180e40202d11074111980b42c14100e0440e40c2d0903405448000d1004035085680341703000300b00052640040f414031860390103a025168540c032880113015441c0308000400381c0114040000d400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 199129469 1250 199128219 199128257
    0xb0301031509080a122417010b0a061e030507080a02160b040b1b071104020c010e06040b100e090a0201051e07080403152c07030f05030a0905060307 65
    0x2000a00141c00209072850f42d860440759000071441100142e420b1a0480c2400d005200b038816404079000c0201031005a051204258407450080390410000240045038500c02500070030709007c40101060035081d15000e00806401c400000004440441c3e6103900e41e06c0c0c000d00c903060117041240d841030321035612028114040e5101112004a01c90090301d2400800c40000845000d28810055240d5500b4590b14410f520180191002c41c266400c0254400080c403c050500580105690158483c041600c409005085900100b0a40e00810007040104215516803031700c03d811200740074020641350302100b203521400300c1b0740e1103440d070042d007a0b14050341c001c0d0082c000038458481d021200c040045802c0859400c45032089464003804602442000080c04040200d800d06d03050401044804200c28080003440c0003040e040022007100c000c40503c4c042c421100a503401060303490880c2c1d550301d4426500c2d44002010300000f460900301140d0703882d141003142e010322595510882b00309000c140083d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 199130719 1250 199129469 199129493
    0x1401140114040305010c02070609060c1707050d0c021011060f090a0804061e051606050c1e0d1a0a03060c050409180c080106051e030a0f0f060c08010b030103 69
    0x281400401d5614072101440714000308095480348001090242010b00e010f454240c054004606110f400001801025408500e000240340c2200d00021120f54020809141d4440d4485c060440e00400110210042e040482d4102c0c0034030aa405918001262030104e400c10300c1260a8100d236000340c1e000c03440d40f040181800d604040110151a00d41080350307603d441a5000340d2141020920b4080030f840104500e1500704a42001401e00034540703800c4000e440304100c0c0c500c0300104903036a140d0128a021880c9030903104007000c0440e01200d0100c007040008250f8000320203d110442c100000908804094000404907040140000d20b40c541982c3d0b070040500019a0000104603082c000020103200368041e905c0e00059800407011160568105200480120341012070203a0501400304020f40f43c41440404c01800c50001075104100000000c1c1052074560000e00481da84504031000d00615402c0c070307001341e07104100c01c0022405280d000d84411101f441800f0700c2c0d540902c010404a03405074005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 199131969 1250 199130719 199130759
    0x306110c07030b010608010801091203020a09090c120e03090105041205012301030201020616080c130b0703050c060703111614060c0408010b0d081e070b0108030d0501091401 76
    0x210381012081842107140045a62090b2000505038004011007500000c203640500742180c02440f142c1c0e10f64645c3c4c003100d03038241c0032355040613030004040340b0152107008800041c002c0118240004081d032a002480440003207240e1401c50b280c08401482d41c0317030006c2200c02400f4181c450509061070300654000c803c91402c41500c040d522040741908089030341c0803420704140e81548514055041d400021700c0c004c4002c040c0c41e8080d08400c98034030421b400074030295016050a81103035a0340302d10341101c4104000b41e400403600500c04a160f100f0180c11070058402940810f007180c0d120b40d6119401c0301036a2000c0c0d110240800c040041d0440201048111007030540a418181100406650741c503180010443e05140c51a80206d0240f0030b00c0130a00840d501c16004032142402050301d0b07102c00301a0320614404050f8500940590702079541a0000e60740f8940d0001c0d0118550340e034a16605403240d101e1066200700360328007400410300d0219480388048811321007a6410650b0b091004000480d5006158 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 199133219 1250 199131969 199132001
    0x91508070f03032a0606170303060a0b030604020c0613060b091b07060b22060920030919030c02040b06030c070209041e03021c05040e040605190e030306280306 70
    0x4e000c0700c15002c41d042d0101036104031000500149441130300078881c200040c50350380a400420502043c0e54420b00e00d4020f8070042e2403001ea90b903c402c000640244907041003d4001d00500007001100849500c81e209014019071052100c80100c100304081100304581d002d050f400d00c00e400304030030b00c0c500c0050000d0502c0f031500014241c00c40300005100050320600c07803031030210040c00e907404c00000b402120002c01d0000c00502c00d0741d1070001950f00c0c008902001041c0c507c80400000d103c0c440030070520041e48101e2000d088058001e081c0140716603840c1006134042d03410019140700c541404400c5a120700520103055050204940c2000000000540f0958840c0900301207404203000c118101070556103c2d40007080508484001030030049500740d914030501c5002d000c104058003145001c254065881040000c0300d55030315046921740f141d0101032601203864144401d002e05400402903006100c111800c08552081200050451b1143c04004a80013207400301080065420b070400b2142d0202115 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 199134469 1250 199133219 199133267
    0x3040e0c0d050103080d0e0f15040203011d032106060913141f050603010515070611191b0210030c02030d150609081612050a020307091508070f0303 65
    0x41d25015140203801c01d0790b0450380003600d00712290f000e205084202c54010058201886d040c6045c98560b000486032600001142001408641e82075002c02100c040c4030760300080903102c0f41c003196583e4001b003101a0301c1d0854104854000c003944c81006104000041400d89010031583c10701c0000d810782c09030031200c00c0c0c075035007003090101c2402d800ae44174014100701043e103410800d84000c6200f03141d501c118041d0b80100010b001d80e4840345002143c17040e03040d15484c1c0d90041468200001c003119400c00d8036002c0c0106000b4449400c032481c0d032884100c83e0780c80704a50303001524164800244400025031000000d100b01c1c1803207000e508240c0e82d100150065034141801010003d05562904102c04c0001c40020028001c95400440b8500548a07e40040064a0207411303c09100e00060040c009007210045410040060030000340405a5000e01607070042559145c1c2e800103014504d141445218030058045084032001075a4800c50b00513201c03030503103280741d80c0307041da0150103003284410704c1c2d24600 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 199135719 1250 199134469 199134487
    0x906040c0b210901021e0304020d02040207050708010609090c050405092d0609010b040e190f020a180c0201060503030c0622051b03070504050408071101050c071d07050c03040e0c 78
    0x14040394843d44940c400542e9410701402501c404100d2101a604031800030b100b84409038640380c103c108040d90688006030b464a80c0e0a04505c1c00c0b03030a82c040c2c04690f00740603002c00c0030502a0441440765100d04520188513444204000940307030101c0b9801c2841d40507682000b01900c4040140e03e4041e4003100e000b07680e28400c0d002a0030958111004080c0d80c5d103d03d40340041741864410811080b412070080e001026101880c0f1034017411040c03000e0840b4450a03906419581c03601c100b14001e0440403d55030341821902c0c0000080c040d580d08507000355182280000305030501004503040003941101030000d650361aa0043d400b46080c0c011a1100210782c0140c10000b42c08100d0b0011010001002250082d07000c0c00701468690a0b0b001140a01d00781800e00c400903030700c1d03410340307217901d074003043c040c200d0001c1100480f824001c489009c030f140d2040c4080082c159004198075615a0351140ca510000da07500b050a803590711845462056642c81004100b000c211310284054122241e4000c00d0301d0101e42e4 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 199136969 1250 199135719 199135777
    0x1030b0301180b0106020c06030412020c0402120a0b0102120d18080a09081b01050d0e151504060806060f15070c06030e010b040e07060e270f0906040c0b 67
    0x121402e8060448040341c0e0418482c100340254014201480106038080c15403021510354040a08010440485403440705003090091244514489001d001152600c9000103160f251040c140c0f007813441d29141c0000ca100b65440815680303542a241da0202d0719204580c85000000e2124502e402128110084010000386580004018980680d5215a209810045400c0c03c010440483c0ca580020805050000da40c01c2800d031010454a0304000640c8140d5181031820646945090003c112a40040201c402525400014898001eaa0800540d525114090f50f92042501d00c03e5000442144c0c1a6451900c06000400d44800310041402d1004c5a603800c140c40c101342e0070078408a41c49400174058440700b40b02c4c0c8000355008560502a02c03600200345511146103014400c01c104100c1d09802458480b419a0600c56031030044800c050b2012511140d80c0840c00e42d41000921a6400451040280000c280e40616040b00c00315405074a040381103440c561100300814902c0400d0410000c1c11055 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 199138219 1250 199136969 199136981
    0xc01020c0d08190c1e03080106080421050c01180b0117070b0f031518040b100f0905010317030f01051e09040b040c050103020f09060a0908031912020403080702010e01030b0301 77
    0x241c031200d104d40d8161034011110700c4503220807a114180b4141da180130035400240d403411a800c070706080380d8507101c07414000c40d500d110103142c41c44032540d90106031800368000c0003018003880b000700802c10707260f81e00380e80c2064841e0b454002d0071540800c00140414011104180f2041c00b1140484688580d100c0d4003100701e81066140c0341034508007004000c5c8004442d03102600841c4220380d008105465054885c6a5034009030002c2c0ca03803a00200001d100010171398540007c2c10010018007142595000258082d090902085a40001440e07144619441183c2034902560300c10400c1121a030810090280a20b0000541d046401003801608410f4940325100d501450050006440320302c0e140c00d22100c1040170ba4003090401d841044509100300103071090390f0340041d04650aa644810800d01180c3d00184c3c0c2e0031803421070200050108401c0c01c2403400d0b000c008169202c011504902c01c421204034020352002506115040140c000198272414402d85450014100040d680f10b03035401203401c40300e03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 199139469 1250 199138219 199138267
    0xf0c0f0f040b0a0b030609070e100c110604080601031416030308040c0902270102031903090809220507030b01090603021c18021201060f030b0a060305100204050f030c01020c0d08 78
    0x100000340422807c051020540c85411420125441e00c09000850300c0541e01000c00c40400030505031103000c0217503800d61401d1200d001003170315407030702d0702c401036280c440c3d03020b10044410741101e4100050325140825880b44601c80540781d48285d624689081d244102c0041088804000b02e52021402800620141c0b10300d8007664a042010b001d12000000460301208100741958814800508a00418032810040310901c1c90302064040300d500e403c9842d4006c25030034560001c40c3c1252413881030400407038104215100003050226444005007901140c0122101d5800101d0080060100358000c0c1c00800760b880d090f12003120100600c204035000c80e54078042a9940f20100d044441c1940380402150403140d81e000d00030030010b450003042c1c0900c80c10f18400200051064030000d05419070584c428001560040241c5002d0020300f030920b0300a610074010350f132140010755410091800c00040c0041c00e154103800030140d845000342000b030070310300d44c20003189c0b6214108008030001e5800024201110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 199140719 1250 199139469 199139489
    0x319051e04090c03110417010e060f100f03050a030806060c12040501020d030509030304020f1f09050108010603020a1d030123060a1a04060302031005030d0c050f0c0f0f040b0a 77
    0x282c2040303008400e40702c01101040805003800c59542c80009840225400c81d600d06000c00480004e040c1032901420000d04080700c0d82c01520100303e039401c000402c03107103d1101c540711035620a031a100c0000444a1380c1c0409071196000d00843c50004e40a44856a040701d001491242450b200498180c036104400403d4110504040340420440d6010024000b100400d0b05040c02036181c002a42552400000e00c0a031180a4240451045854600c080c0c0411100090000302a00f500d24014110612905c1070500103001c00c800055400e100340700b1b840100e07120744e4401c1181c1d020540800010502c84050a906541e02c820004034050840c2140b4100f001c101424041c03460075108201e030340b188540c4501c10302805022501044154201284d09450641c02c00507201d80350b03004000e60390310403038001e141c16214001004c54280d400400115000b0303c83c4080b6241000c1031607900ea10382c80251811a00505c003880710304224030340100c00d02c48016020748005108004100080d4580c8402d500c025074034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 199141969 1250 199140719 199140727
    0xa0618080c0106140d02061e07021306150305040b0411150a030506030d0915080a090c0e06100e01140d110313060b0d12030e01090b0702030d061203020319051e 70
    0x2d0360714041c6004da5513804542200c03d01d40e0540106240780b00da0384500c003000024015038440d1249600c240c0d800c140d00501100000215014040000c0c04c2d03070701502030305500314001110000e03c207008181c41a5407044804071581c44035910366040302c200020040c0c1c00752480c150051052100405000e02807020b98000c039031410044103041c1407400e541301e1601001a180c0c1c0a215440c146081c01c8102462443c18800310798403551160002c10000400400f181d40d481ca00007001814a0401401a8011903540a00070740340703042943c2c480302d604c1c2d005001c10030030741c03146544404000141410b0810043c01080c0b00307590001000b29035108541401c803c8805000305401e0081910401909440658500d07102d034505445a140750554104400c007010340f02ea012a020346070079048240c031301e81d0080315001c41e800e25040280d141d40160225036429850403d0002e001c41012140b04032031038054020b9440c02c00d004013854001c000551100b82403200402861803540320807904000514416141540c40d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 199143219 1250 199141969 199141979
    0x12100503010f0f1a10050c030d18060b0f0a06030b0d02040501080f100207080d021c060632070602070c080a050a02011103030f0114030c090103060204050909030403050a0618080c0106 80
    0x44801082e5402001c90104600c0440c544174440010340014850502580740c00a000c1d6403032461240c138516240e89400c20100c05d00140390001e011081e9440b0702414886d81202400b032001e01d05d07200b4101c6600481c3c6000c10031a1502950000101101c042c203040c0d0b0b0600d00d60040340a845c82a440108550f01c08400d174806280f044c0003e8560946484007946031503515214084a801464041c414441c1d00241b444e00050000780d01c580409000700040c1f0038542c1d100b101401c20320541c114124400000c098105e00c40000005180801d411940002e0070b2100d03a8403142c3c025001290304903000c03244801e0105080c20b0411003403601d107110344000e00d42c50010340300042070b2400091201764198030500610020790314141e8800d056071484000b40b90808203a10021746001c550300c1c40a50081d10810000c02030052540040040d60810b071224041500d801300c255940b8883c031f01c005002d64202444000020b801500700c0d40c01220782d60701c020022030039034952036050ba0101c140250260364841003000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 199144469 1250 199143219 199143221
    0x3040201090b180405180a120908030c030712030207230d08090607080901230a0b030604080a08040203030702102021070825060b040203060612100503010f0f 69
    0x4094000480d50604003011078003c02602845844104e01c10343c2c5500018100b105403410000b8204681422100e0004090429042c007508150b180d0002034003214010074a642c000003118000d040c3d20005515100d2540c0f41c1949005480c00d182041513020404503000c200b450781c0b80b60341d00c1d441c0b00070303000e440e9007031012030345045030f01079411050004010810100e80000b20b103042c3c0c07250f45410401b07010307075a0b000309038014807154040c5c1061620040786405120003603d8514803036400d090042003083c480208140c3e40e0070301120000c2c078000f01042a04181480b076030219410510260890741030022981c00600590341100c480d000081910024244140816401a030f0046d1960090488183c68034902c0400940e070940c1403c42d8800021020708112008080b0b40e001c079030036040c1211035105640d00b04c2e9481c9403004103880c010b00348442c0800d06c3c84c0c180b003124041c5400a001a250030302542070b12440600c0184105906442020005003a8800380541d01800c45030f55400681200e415110700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 199145719 1250 199144469 199144487
    0x110c06070815060f09150408010c081003121b02030102070303230603030d020a090302030a050708101104060c0f0b07080a06060806130504140a03051305031c030e0106050d050303040201 81
    0x180100c528400c0b080c0094546900311001010003c0c140c0703036070710100404507100b84000844e0051074000050002585c0d003041d4050200030b645079031081d2460b140d150403185940198080a01400404106050041d002e0a038408981c00e241040038651349182e00083d08907042081e06a020a88520220000c40c4004c0e40840701480300d14100f91440c00c2c12404690741340100407a40d08429030004160901c2030103000c500008660080c11124070051a140991f25098203102d004410b124010425601140310301885000742d02c42600070303041518148040b40e01065080043e5803d000c030240d00c0002c6406219804d11400680d215880181004000f0300103c1b8072551100c400c22a001c020310250341d640603400360fa50030044002227040e84a274142401c110940c03ca400f0680c0c8107a02014080640007009000199a100070741d803034a90346c54080c0354407041070b00c034146560007041d94400e5095009600c442468030502c40001ba00e96124804540c42c05400d40041d0750542c4003004100c11580e100c4154 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 199146969 1250 199145719 199145731
    0x3030f0f0604020a080604020318061e060108070f0e0103230601020705060a020a0204020d180302011410030f0210120c21020412080708090d0623190e01110c060708 72
    0x4604c2e04040100044c104500508502e05c03454002010444a00ba1400d14503480400034041e2005404c1c0092010591040c10001c00b02d02e0700d80da80012540c0d801424040d10030030813511000d49030205e00c0c20454008000e005c400f4141170b40c50807a40400380005031041c07501407181c0c2554145040440000e854040180c2c005072041c01c0c2007041e503800650200d00300000c20750680b03001d41c13640324104681000e00640e40c0a83c00b0725402212100030300d5415000100c03403500d082080d2005881e0305a4203601c00a02d404050041014050b104005081440020b0008182c034030344404403c071a21007603404e0711459800c000004951903150203041205085100e2810f510150440ca085e2420b8000706058001c12800380c00d0303040110700101805040012208807004c001d1084001246c45c1c504403000b0500b00741d034110b0140c0c454140034a601c0c1282c200c00d00441203002c280d000a0740e42c4404a01500d41c0c100c88007170b15521102c1500303240082038064800c14504102030510f81c03400101c0140140c034001d043d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 199148219 1250 199146969 199146971
    0xe0301020a0516170f1312030e010507052a01081006080106051c05010b07050c0909100b0f03030705010603050607031811040b0d08090a080312160207030503030f0f0604 74
    0x100d080c0094000d0b0403100b450320307040c498003290022410502c040804c2c80d40c030312100c03000010780c131950824040b006004020700c81801070805905d5080d0040d243c80394582c010042001e501003c1d005600850242000e140701d00201c800c05a8112000c008980a8500710380603035106c09a003115541e0089800f0f684400f4004015400320710b003110051850a062250400788200090720100078040b2034404894659680c00620903960350304110050713a840554240d86c5802010180045881e01c80e241078041c40c02c80008100181c22a0240c400420180303100d10b51080d0001400c81298806001400501d4003600001404c2440c5083c540d0a150005020070205840c1290b8071807010745c28044548034503000b80c4001c02003425040420300400c100c0384031651010154540c0300420000400500344460103031a90307418503558102c0300b560b81c041c071115020080d0300a000502440b080440340c4c0149030383c0b4411204415541d880342815988191a101042d100707603410803100c002c0300044141c211805a170 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 199149469 1250 199148219 199148227
    0x306030d031b18151206121113480c080304030e0613030c050d020a0b03060a03080f0a0f05090105030f060307080f060609010512030d09021503160e030102 68
    0x2025107110626588060140406a01c00d051180f0090400980303481080003000100c12a40940810701030210307030b081c80d401e0517400314045065211442c0002c1c2d1100c1c5609410380c00301d0070802000b841c007864940c8541c1d40d003000022101d41d103c3c502d0060100400d808914000e00b5401402502c800e0100900d4240a400d1054140c0c0d100701440031140e082005070340c49403101e04d000c40d08418000c000c1035003c0380104003d14114903000c480e4045a218400c8100744c01d0341c400620a100c0b02020019512a140c42000c21903054500b00860307101360300600c03200019881c1d81d50f1103000d40011aa1a90107200032510044103500581c1e100030040d4a41040780c00c3c010b00c80300080c5148401030103681c8105062000c20b45545003049040041c1c000d58081c0c0d1000e81300c2c0824035a0320319088031741a10030341440b00001024142102c09813150b20518000d14036100340d080f0f8902c054202481d00304d0300301d0742d2421118204114a0051800b41c4002c4005410208014800600f1501a41c0c0e01510a0344108 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 199150719 1250 199149469 199149491
    0x60e2409060f010e070203090a060e010206010e090a06090804080604080d06080604120e0103140109141302030c150915030405010b0405240a0305031305030f0d050f031306060801020306030d03 84
    0x807540c110b829201005041e85c0d100c10b000c030700f9400b8840d000b0350001e40c0d006000c20420717007040442845a100307900311441d030307a45c401c007441e50654191103804145d000010340030042121500495946406805024a80750b640c611152030100d00302ea054403c08000308990309914028005c0c0c2008040c4c000c018601424141c6a000c21f13900310b41241c9040c40401940281c4a901a81000441e00041e201c848050f41e558a2850083c081c2c5030b8406203220f02e200006100e81040d04580ca800a4019000709130751a90300c0700f03010312050b00c20403d0290a806008032072079a502c03254a49410380722900080c1c2c413400e03d49400b03429101001100ca10503810710b000c1041441d6040070f214900480544100070070107000d004640803000c0e607000580741c0d00001441000070445d9a40c50b2040b1101902199030144174a0901d90b107816030060041d000460800202003006690300107140c00c1a0342c03055203910103040781c5d42c1c40116800d03907001c0c142e242d4022040101d1403400b4000103501ea50141801d00c6804015 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 199151969 1250 199150719 199150741
    0x2d0d020105060906091810051017070e09160b0405010e061c20030f04110102030304030909021c020c01061505040815431106070c060e240906 62
    0x50842c0e028003c51030000b0006c0c0c0e600ca010200300010322040d1202403007000c00e0312014040403074002c03548900001000075216000000381c0043c10f11500038102244c00c1424007a00e0030f2010349004014401d104150001401c1c540f5900003c10f407102c1c00c182e556240c08005001c8030510074442c0d205040030b2001c682d001c2c04600c90850030940003480002c0031561103000080015801104042c1c02a0200800015040400b001e0b40500d01406142882c031504000480e0380b4401164000d00041154408000314031854014013002014043c46010884520001c48100c1c0c01880048000b41c0d11004104402c50300c10318880710350b10040c9040c0385414204290a5560380b142e0070420011404400092202e844044102c1440c552100042202c4c104110b41801c11120540310168412074071b040c0c0700b40c0b09000b40740301410b0060301c1018000c0d540d5112402e550180c4142c009480890302d0f000f42c0014641e080c00b95000184d4035000c5001500180416500d028500503c1e4864507481074090080d03075403030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 199153219 1250 199151969 199151971
    0x4110406020c1018030c0503010f020306060f03090123070e0105040b070b0c0d1104080723040507110609210a081303050d150602190b060d03022d0d0201050609 70
    0x10030303503191000d041d10003804c91314219144d11031030342007803000d00c080b04103c41c40c0c1c082d00803588124001c4c458064a48000400c034441034a05c00e0380640104210300c1d00c0140b05001d1035200b0b5454000041520300ca400c070308403408100c100525071100701c20802c21819003000d44146060380030f01c2c02c0b03070401d410403614068a124019010f0711104400d000907a0101d85e14040b50b0f100303407404c0710500c0740c0003c1903c0080d050f00a8000e00c0118003450001003510082c003c0c1c41000120300c01c020841c1250307000e080c48000d18026040380104181050195841d02040018078001d5010000038448074021181c100e040d0320081c106040c644004000310491035910881340d94110140064280350907416207400e84081c81180340070200f10f400c010354101d4004080800d00115075154003550502118224000c14081c051400109070f00841e10101e515400d10400c0881d80c1071007030044070030000906169041d03290a040c4403291508104011302c038100c1c42486105608007950000340414102500000c0829030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 199154469 1250 199153219 199153243
    0x10f05061c0f0b28030f111e040c0e0a0b1620010905060304020d11040e06090705101e05070609060f0605150a0915050702100203090411040602 63
    0x20500790380d06400702030200d480350440201005880401d504100140c88012100c500c6219181200c1034007502c251600406180c0e01d4100a0f1241d00b075544002901044e00c10981c0c05184100042c4000e88640100c0a2500310b40d40342c401042c1a540c041106039071196034031100300520800c0c2245903031241042002990074028989407151200000c22805120110000e845034076022148540b1407403040002c031102800b0b80e5414211038540007440f805100555009400000011414010500356403813a014807030001c0022030b4245402c40d00c0c0d4907005040d20711071440e0700094020400c501c0c240301e500d00385200505103a0050303102201c1c06000e204241e0280001e10070001041c00070460241c5c010920542e001500700040d20b0810b0743c902c01045103008030f50080400d040a81160004602a2140c1070030640c1e4110704141424510814450006500c4042c03000620500c1e0040c1d5522140da29041e18540c0155103e112100410081d5008508440d902440030401400201e030701241c5c03085940c2c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 199155719 1250 199154469 199154479
    0x1203050708030402030c0d0b040302060c090d02150912100b090403120908040909050c09150d0204091106040b0a031523180c07110312040302150412030807080708010f05 74
    0x3599500120b070811b813054004907070003000390a00c4010098015032540c0114000d07404c4501654514003521214800c04003036950000807411450010300e00342c480d0140c20403502c1c54941c100b405200200d85040b00e40f800036002a041255190101c080c503205c2c03400400c1b400c072a05d2a903400c0c50346015202c000d81150201c20180c503044180300b444184000c46000300940d1208000313440301c0381883c90b120101c0303444403442400d050002c50594042400c0f86480c0150080485890503400d5003040010700240c14211010b032071809204480b551440c026000400d440040325030340b2241440700404039080c1002e5518596810301007400140034403402c0c0c0503940b650031580b501421680340001d20320f1200c16516034a54254404000e1401035007005130035154450b20205001180d20420592240d030f481c44074400075134090004201501e803002c0c400345940c21403e00b0741e2400343c94403000403580858074401e4010504800510038a03680c405820355115038245130241d05941028181c101c840004c1c4500ea04c10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 199156969 1250 199155719 199155721
    0x5060702090a09050a06060303021c09060e2407030f0302040803070816150e1009080f13080703080a110d0e040507020309280e01061e0e03060a06050307120305070803 73
    0xb06202da11a40d031141d0050210f92184803149000340141c6030601040703005000d51115000c41e16514006034218180540711049042c3c00c08001b21140c1c03d46240065111071102d0245913444141c005004130005840209a038074115810080c110007280c07500d1004040c81003008001001c408415030720a903030700c101381c00d5858a05203480812140d00325005005401b519040580c03150070360f804881e51542e21019210540c141914400031100041c44c06024083d08120708032441c000903000f0012202000c81018815842e17281040c07428030140c004940000b4000380c00d0070780704d401c03e905000041c600b40041042c009040300042c403450b204058603000d0782c0c03504007260200c0c0c001d006640d010400a040c2040e9100c4038200b0009202d840404d202c076041c0540030204030304040f502c4082c1601c0864031800642c083d10707107150681424000c680c2e0100900401c804101c0e940900115008503031580d40487d0391b504140406091403000e41c040314100000055903400030750800d0a48403842c4e00f0849403922 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 199158219 1250 199156969 199156981
    0x30504060c0f020402181c020609040504030504170c0a05040219230a02060402040b030a1703040501060906060309050106061e2a030c060b0306010317030702010f1d1203010506070209 80
    0x40071100b428001e5005001041c000c000040b10004800c210307a040359408072004621004001c10403814002a40240007003203201c3e441c0c1000d0308002d400900c079280003441d00e60348180219002441810701d4a260b0030180b0301fa005881d001041d82c024080c200c42c114034128000301030310543c4051400c07071011700c5515001400c440da10300300c1c0c1c0090384181c0400b5964440740c1440080d1217030b100b00c0c1d049119901d440302c00c10b40d5050010703a614160b540710248003023901c6041c0d0614120341004004842540d2200808100501140180801004540c4010501c840b41c0e140c01403d55205410000420012484c0c0066032100501198504a81400c04000c014040801d40a11940d40401e242e04211101c0180c010594040c501941a600485041000d400d0190416407500340a100c0a040b141500c0c1e01410f4080b0600011034000d0850300000480c042c40780118002d4403000c01007807a024040c4000f202c140c440500c1681012060150001d155605020010b9024025a00d0290142e8042c20001c0c60b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 199159469 1250 199158219 199158233
    0x6150914040e01061710090b0c1b150f0f04380103050601031403090a06050a1e020d031103061507020310150302120307050d0e030c09010f060801080a030504060c 71
    0x14418400003407140c517850303c681c50041002c0003000b81480c440d07001144020b0031107100e00200a90b0000920704141c4070302080b00da5613040440300d108a00054030040c0b24407841002081c202618a2103404084e181c1400c8549a003640140074034003401c4441c0420000a00031007415000403d104104900c1c59a21041000070241c8404c64445190965001005105001491b24122403041c0c184041d032000d0001010345901032401c519400c5a00c01e0342c107202c400d00403009040404440e00c1e055614041da1000104803104501c01e810150700510b4400e07a00503450302a0001c00c40006424901d14103000700412a40c181010094408550102e408011540c0500c051049011104000e110580c9446420541c004032880100c1c03040c0141840c05124481c04006c2c0d6420a4004c0081c212140303886805503680011544072079818080c104170b80150740d80300380450380a801844a00c4405a00304007004d000300106820802f083d07031000007810300013507110341120240e03101031402c0d50740881c662038209 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 199160719 1250 199159469 199159481
    0xe10020a0804080609011119050d090f0f020103051609120305120f011401080105010e0d0206040f080c040b010c0510020f040b0414130506280806100305010615091404 73
    0x10160700001800103401d40c40016a24000e00e0320100070450084481c9050445110301160700c03a003810408690011140514041c2038001040c01c0086140c1c4500c0d620240803981e80c03d011100400704030100000d65038940f10702036124903540540c0c114044041005400f6881602c5400c12008220142404042c498010b40c1c15004201030508a2801c212009440101d8240590a1a540d40c078110340819031240740201d04a6206840d602600c061407410700c011610858026608048104000500c00d45006034040051200e040a04503101d00e07002080b05441c1c1d4201c0103030402440d01420408960701141c02400e041d034047c0b005075030f07000c03903d0505420702071fa61040060760008200000d00481801100131740b0300f02141d002e60b245404609005c2102c205803400d54004090f0403280389080c18030184010040c0340702d81c48100341c645c0c6a500c0761401d034003141d00d0014108828020000c002e800d024100240480301810008040981402001c1352100e1140000704020005460096103495020b4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 199161969 1250 199160719 199160723
    0x8030f0f12010602070e0906010f05010c06140a060f05040b092e0b09030f0d02030a05071a0a091709060901030b0415030b19061d10091506030c0509010e10020a 70
    0x107205250303500d02000e511440c1c07a100d40101814200300182140c01c2c04038003107058032004001002000e017048011111507002c0c000c126109680e4140300b00f0142005003405106441c450000b041c0345d811f003841c007600d01c9020750205004906044e03904010799541d518290f131005501071400d40030f0b0b49140000b040e40c03140003003680044c10070580c0421751469203001845030440c154100c40c614526400030079603421400b0903c00042e0000d0041c0010640704000828500d405900c5180c91000304182411088000703494810345035548801c1c4404001d01010103100344800624202d04250340600401e4052007190320710342c10140d455001100782d543d250f02041841a1a4040c0b54440f07071a440c00400c1107606031444840012000d0541c40c03181d8260007120150780c401d1303080e18503070000c0c0c0740140c410701d00c00b40080a4440c3c540702c01081c0391001e44548561540501c000780340b12460141d010341107031a055018030070403904001d24141d59800520603442180c2c00c1c3d803080300c1c140500000f24100b01c060000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 199163219 1250 199161969 199161997
    0x305160804120218130803190608010c03060f030c0605071401050f0f10030f06020a1e02010603020f0d0305030f040606050d030504050315060d060b061c0c030c050408030f0f 76
    0x301190002c1040c0b41040341c14400d03540c20410304005045180d81107030841e01c200360001c01c0c0040343c000441c200081d5400c0800c40d0200e1803c0701c41c0c045942e0030764800b0341120065a40d59240b4240d815450b000b00f00092100148035134100703040d0381340d10700417805900480090081c000b50ac58108a480006400120b107240020410b03818002000c80c0d07a01c00c1600c0d040c0340410284041410002c68859540c12072340c0c0b0090120406110390b031074201942001240300203204141c441100d407c80e001d014044494140d070300009585040d40b0402140c140d403005107601454590140d040017a411004403a00f090b42d030200c0241c140ea0302e251000143c61305420003600080da00301d0080800d42c00030f0251003504c074210280c890f0007125180d00325a00400f202c61030351203403566401d0804075109074000c1040f10700190504d85011252003a003500b4803451004c400c2c1440e0340d6508811213a501d031051a0f5460000e14242e460301381b800107010356078080d02c9030140c84608000f0b6901d05204001c0d040b1056440450b074 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 199164469 1250 199163219 199163227
    0xa02030d150b0d020a1404140904080c06040503030f011401050405040209190f08011d060f0709030c0303050c06060901051530060a14090103060c020f010f0b0a050103090503030403051608 82
    0x24001c0c019401c45810180440c105003441045a0041c8054038143c07040846d2340110072050000304040000064012744d0030820402c00308000381400c0c01600d21070b07030042c8000d69880c14200000c640344c000507803104620140340003034100c482c0e138400100e8003119011180940c44060807000500f4000404087c81c1141411050000da0840900c40d002d0854400c400200310599503010b140401140c3d03401c0441054002c2c1c030011321103401c400b041e9a0001001e25010755459100e540c1c140c0b0f03954580d082603000c18008540d4403d4401d04102484d030151060314100040d52406e0003146207255840280e400107100410b00488000100412041d2104843d080002c00703085480450181502039071058080c000060000c901001108510113100801900e000e0b070300e80c0ba54035444c0c010b080000fa80e0086004602d030140030319000b40610502c0c1094007400060901c0d05004103d01da6410781d00a42c180740c10040c4510200700b011058039401901400e000380d031451003044444200305401d40003442d1400101d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 199165719 1250 199164469 199164487
    0x50306121b040c020c0f060f040f061205060301140403081b031e010e15041107020d0507081c05040b0a03110d140f0903070210020f03070f0203070b0a02030d150b 71
    0x10060701105a01640e081024034503d0008903213034020101102c2e00084503100c00c40607424100010305521880d440100e0800f0386403542581c3c034043c250701c90350004040100301122010340d4843c2c240c11440407002008500c03100c440f22070101c60010320180500001c40c3c000351000703400351340e0340f0140401504000d54038a040d100c84038460130042d81c412031020800c0000b1645040030505180104603a04030321409208610822001c0e1146030000d03030034880180030080060702c41741c0102030752a1060f00581a91428150b4192900b50040c08403e201c0e82459800c840f6145c02001302c0c0c040d1806194144d40d5400c100790142c02400c5040001d070088200002c000125904039032120b203890951036013003441e6480e13210101c03000350000c0e25401096081000604018540041124a40d142c2d60041d10421020345030f46904540140500b40d8112002c07244100c218903040c019000545108030001d030070300c00e050074029036038040c0c0c96416481d940e4075064410714540840060000301024640306940e94660 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 199166969 1250 199165719 199165753
    0x2060a0519090f0b090d091a1204060f05060405070e04050603070e1806070206010b0a0518041a0103060515031605070b0a020d0c020c010e041d0d050304030212030108060705030612 79
    0x4010581303103901c58a0104942680109509904850360303510000c546017840784000d450151102400051181040715a46c241d020031001d6204038016040091034a01031000700041d184c005021610440c50041000001500920246140501520002035941c0c4540100345800350a410116201c0100d004020400855240891501c07a244055802e80e0721400c03010380c1e50786000e0203a02c0130001d0a00011b68903601c1440505881445504112800200900420211001202c11a150302c40b00b0042504558140c000c200052900340c1e1030490b0303040d8425245100e808007400c032200c1e0210401130001d95a1180f020f4031806030300801c0291007404c24054442c025400380c10401030450900c4c0310000e85a00209180f0b20398101a1140c2d220100381c10300300001405c240441c00075081080300001d104010400c8010300c0310045849255032418941000703071034404540754856500d40100014003e210340468060b03045145402d0550311ba448a400040704600211420380840c4281d0b481449481c0c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 199168219 1250 199166969 199166993
    0x20f03040b1e07120c030b131a010203070b04120c0b070c0309080c150310081501050a0e0903040308090f040e0622051b0409020a0306050406060909020102060a051909 73
    0x20514215001c41d40c400c060b0700220200325258404103184a40c8090102e805400054091000380740000b12404400700140214241c02519a03903950781c1c41134440c1031040b40184a0740320201740000e40c00d0461966604011480c000c0005041c50755801c0b460084502400800031410f038400d01c00c840304e00d01031000818200c00c609050b8000303241000300088111004c10740c1c0ca103000c0040c0c82820320300301c4070003501c00580c4080c04d0031a0741d0240d02800501514103010007004c186280d8010080e45d4548020010314090507000700f51901604000d00c0380c50b000c00401c440499520001c900d4881d4161310000d01c0e0300c072128000d190060f00300030203020201ca010a590f4031a04610120b8094001424048925142540c6009189030701c0904000840300f2960300c2100c440d18010004600c201b102d81c08500c400c05140e00844040e034844092104000e00d60140c1005031081e290100705e500110b8000030340c0c0300c0018240780404c0da0f640c00030903040d24100403100d4803850542000e0281d0401441d2081c41c03002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 199169469 1250 199168219 199168231
    0x71a0f0c12040e0f01051005190905060c010501170115090b0607080c0a050f0c030d11101b091d04020906011202030907031a01060212030703090b10050112050c041206020f03040b 78
    0x35880004a001e02d1f0002c107046c44030090703030303a0743d801c01101564005244940300000c0c818000f491000040039966070004180c5d4008410011540d5407504110015840e05061880b60030707418254598043c8882c000c43c80102c0c0c01d04203002c50710030a034a011a9007407140c0c14001e0000180002e8245400e00e001070840c040c0c511030f0b42150340b03200902802540b03c100c11a461076254000f0080044013920442c060001e0310744003019212680c01d000100d0b400ca07441c10202c1000960003180c42c850854028101038010011001d952070703000c0c2e00508100600400a1009105604030800f00d419070f4070940300c41c9280314403800219502d060600b4803039542c024910003141c2d08070183d85030445c01d00841c1c5049040300d80079001042c41d656890215101a00001c050100301079030744001c00045134042207042e0281701c8000c03541c1d0196080200040215002c40420800c490503c424400c28503250000c4808464000080440f1951b9528004020344650f0200b040d00c1074022050006100c1d42c800100c1c0558 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 199170719 1250 199169469 199169491
    0xf120a14061009090b010306080105070206060a120b0c030c07240c09030f03031112041a09210a0c0510020d1508100203070e180603071a0f0c12040e 65
    0x40c0e40c8030100505002040740d0711002908289041200b01d44d2504440290310050402241813500d40350380320300710f0b041151a100142c0c020810b104d00f6051141400000e02114105503c2c44805501c640c9401e21010b060003100c1c1c4000000103201030300c0007065508182d4001240007803801000d25410000c40d00d10140d132442850451004200350041c101007084030b900806011a12075103071419030003440f000c0700076040b00754100484410010b00c542120300c91803284480418007840d03141e140300c0c0d80340b00400c4410b00e0351000c21a420f0401003800285140450f680d0300c9951100301d4681114904080e0b07100424901c1a1020112035260b00d4001d402d42c507010940400600c0040b6041d0603a425031486011919004030400e072035452050b80045174001440c2c18003503070502320040420716809070034404551603da00d0040c02054501404aa4001c1429041c0d440d01c003009000d18400e244079041d0b8800070385e0740c0060b03882c00c407050501a40000c0403400c2d901030b41b55551814003104418048981c0c40d810 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 199171969 1250 199170719 199170721
    0x6030606030b010e04020d11030a0504150b03030d0e0f0111030105150403021c0201051207050c060f06010e0d0609170703030c09030f020103051503100902130603030806060f120a14 79
    0x11807207449a240b108905135103080034640640103100003984160400c044d86a100c40ca4101204121402103008040e00c002c00207035071406003030240700b03c000b500c0242009801c1c03c1e040d0406503000000e54108500c1d0b0400011b12000c00d01c0007600d0b00951030500c410395401c00001d8001c180c5e1260140d4102c8209a681000d6500d000011b1802d0b48a24080258051340c841040e80306c1007410385601c10294810b04002c0d02c0c1080c014201d500010f012500310700001c1e0b00041603079441b04188225500704d00180741c400c14a041c040000b82248000c034410a004407919070145061000380d0300303e12030150300040740240164000c1c54000c1d203a1320440094000c01e0801c4015481d481c4110600000c50741c0040300030072810704607801100a007102600c5480c900054101640301c666040c028408c080c8039000700002c14512a2043c80802001d81c00c8945006240440405c080b94205948a074014012903c1f966100300f8006880b0b401d00424094400c481c0c010410002110100c0e400a042450740018045003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 199173219 1250 199171969 199171979
    0x11070b0a0912050d0b100906050307020f03070c080c012a03030213081c09060e0424060206070e0a0f150c0f03091d090d11012d060b04081f0e0a0606060306 68
    0x51b0807111350150002d25401810003510344102d010316007044892041d0f030b081d00203c94032580365400505050300c3c1400d0080042055940c00c214021210300b081c05d102021551103000e60051980c0841c1c91541a000701d40003100301486a41260610280140c9105006440e983e16070781e24001c45480340c10701a030781d442d0124550300607000c41044803003542da08043c0d41440020300001e008001c911031031400d6400c014045682510b02802d0241032150b005165a1602ea1802031807004042116070045030003101c18000c0e564500001c20684014400d031803018800c101045030080c00c0c00c04003400c0f0f10070070f048500801d58031a1440d03084134a200b00803160520b20400384001300a045d101801c03981d0083d01d000d08a1401107915072601e2211100000d0750500c04004d030000b07100740d4019101034032121002d40010700510700c511005410140c00c0c1c03e080504100c01581c1e0b858054039110b8000c4403441d03680d4034000c101d804c040703048140e41d02036500640040c606000901100d00a9030007103803c107000420 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 199174469 1250 199173219 199173229
    0xf020604050316020a030609060c0e060403051525020d0e040c020a03080a110406090f1202060406120603170306040f1109011d04060b0a110111070b0a0912050d0b 71
    0x20040e07400c000514a4052100c40c3c85948400880d0308030307040119980d00201090fa640700d4918000e01918010407100328400c0001d00d03064130071140310702c5580148020702c082007000903086181c503100300100c40c6503141c200149840000d146078000e5004d80e503110710524181e0224000841c1c46084e00c03090090207032203040200b601d032040e11000050303000c24018004070340719489450300020313807990000300561b43c900d4080d00d030303840341d080701000c0390350030300c041018200340f684440003480740d62041241c2164580c0002c1c0c040c41207101e25030800250303480301000291180d01440007140d00a105803e00300601803100c0187d0012104240b045140a1041c02e808904e0b000f240c00114140b0702c03a503d81404017005644c007460000c00c2004010008112a43d1511140702da41d0251880d007100d540c880d482114014000850001064010b9052001c61800320307004030140c80000d9840340d15040b0559500d9a004010620544094001c48110340140380140c0c000000f00070503c414401070084c0c0800c401441 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 199175719 1250 199174469 199174471
    0x1060e0904031b0b07020703020a050d0c050d050709021204031706031f020c010606091e06020604030318020306010b04142202070c0f0303081e16030e16080304060f0206 74
    0x40d800000310000100064071580b030000c03207610000a08410700016443c4c50441d407800b15412000f5078046201031040d440c00c100085c00900c422560b000b18010281d8500c1404440e1f0701c1078034000c403400c0c4c01031400c102e000d00401000e840c134400110348401080d1755035040c000060300d0542c0441c0000d00c4070300034415641c1d1124451800a401004c02c1641404d182507603401c0c40e00002c8019600b40304c5081901420302405c0c0c01070110340d4501c0b000906040c1110403003003004900040c0803c03a000104281034010800a0b401601070900064800c128078001c003103601034500c000e5250007160004555a034060300600182c50101c4050040140f603542441006464900301d12125242420401141c080e25002005002d00c06d020502065545540c81d0f0703c01001c0780c004601003441d2004000c1c1c501c542a465001a86044074502322505000d0801c8007a035211964000816850b4185210361007010082910480c4080307440c1503031160f60b024582d031a03400c50301502c00000c010204107002c2c02c0c40001d0103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 199176969 1250 199175719 199175747
    0xb0a032717030c0904021303030315080c090403050408031308120f0f070c1a0306190b0316020304170a1203050606030114010309021f02010e19031107030c120b0106 72
    0x8000c03204150310009075650801085400e03149010044034502e9200d078000341049150344517204500d00e055207405401e80c8c13002c2d84a440d50b0106042c2c10001d84a0005000b2039580e000d4a00300101d49070343c1000c41b4507104542215485200002c2c007044044c84c80d11080c0100c904540698612016504160006209d0300640c8003da8405105181c1240d40c3c0d940180701c00c0d0b04c0381d200001403a5581a2404404100c1d4040560154003c010040541080c410102200900c618035405c030606207007400344a4040070300405c000240d001c0b10b09580310700030011035014000680c3d0340d00c40b543d920352205685d0041c80408aa11412a200c201300c032501078000d49004030802442681036a00b050031848000480b803501604050700e42101e40c01585901885011f08000e950b03010023074606040010b0f09640308001c114010380d1110f02d10075400c004814105483c0c60b0b042c40d040e9402c80034100030b01d10340310140d00058006001c0d0440020058a0b0001441d00c442c45000c441d01c90f60b0744e0303040c1521105542404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 199178219 1250 199176969 199176983
    0x3020d11070f09050c07020a08150a15090207062912030f09190902030a0e0d020724020a020909030c070905040c060c03032d0e03070c03110a0b0a0327 66
    0x24010f81070260009544909000c0e00740f420103509030000b5010700c11544c400c407000d8000301303890381c4585080782645510032a0018203108410701031b5102c6007a10901e10407002c003c0d90100f00322041103017541006a07421303e5481c07154503102a004049079081d1004105502c2420742140031f52082c6004000d8404141051001d81d061030307003d07010700044070360740c2412034026889a0400324859440c2e1011358018030180c03500099280221a42ca0b16200c3c081c800e041c255070203041d041101c600c0c003210b0203013003080c40c003540c20311003010210581ca8580b205000035440b01080c010402004400809404061071001c1103540c11642c98120f401100e50544018007810400c801c00c0c44814000c00c6405c007124400d10300061003120850602c1c0c41e2050701c0402d00c140f102044a503402403820750280949507001c8001035450700070190798000c00c03c1c070070381300003003000c000c10901c0c04180e43e5454040000f440000e02d0303a40d0b00c0c410408028000d01c0d00d916940b01b19440e2240c0700600001d011406c030740d801c0d40188 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 199179469 1250 199178219 199178249
    0x90b011a0c0d0513140a06180e010e040302010612050c061b0102030a06080105060301111b15090303041e23010f06091a0d021302030402041803020d1107 67
    0x40c50900d022480c200c0340890340c60810250008610802c409404001c00350f41d150b031a075070041c0c1203648a4046a0004515000c8503151a000d66100e59800c4215081414140210310168404200e8803420b944004000080c0000008950000c4c004140c070440c0700e580204207468540c0c4200d00034041c400d0020f09103603c803e02482e80c0e810504010b0070780041481070540d00e003c17190b011909a920480e4003000054603401c0c10022510240559500608120006d00c040d50043e0b4826010b4001e20039544060207429a070144e19220030f02080c804007000b240e030844c561601e45949680c0364420364045410618601d00c1a00300d01143c0102e207102d80d4042d0040c2c00b621a03d00075010007600850b51440255070b0741600261a012034810b03000140300304540030503108100c1c0b1000242c2c41c24a03681d180501d144500c91001681d0307401e203016081005070001601c903103980c0040b80040031030681c0714010640e11001b0703400b0b0580000e002441400030780d54005002c2100c4800e16110501d070700ca11800303808051 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 199180719 1250 199179469 199179479
    0x103030206070c020103141f17030f1602060f03040c0b041d07140412030e030a0302030708031003153201050114071a071b020108010e1305060403020309030f01090b01 73
    0xf1070001015801450003040d0416030518140c00e0300702c240e40c40e00e54420030302c204600b242c07013480550303000b84031881520883d03501c1c1104c807981702e01c1048000c81d140d01c00020301003400b0b007842d072030000ca16802400258541805da500641164410b80381a66424565040081c080000904030760954030320b1034401c0110248810034058446024000d4401d006410a4178140303000645c01800003000304064402c141d00383c07824090300d02041c416407280242c11000300307100825000030403244920340c40303140c01e0358070368540c000a100d9a42c1604014003c00d0035a1180c200b05e4660b03040211140c2000c0400c0e02600800f403898055601c1641c811405429034a004001560262880c5000c6e1040c0052007454076065a40301c2451f4980049800c0800d01060288401c41e54002504040d14040c100c42c6003a0594680018280810500c100c0900407004000500b00702404600403810f5a4020b0440c0e0190605103000b030340f20340184010300d02a100340c08ee101020001401400b08098201e0b4942e08564241 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 199181969 1250 199180719 199180727
    0xf170a110706050a1b020315060a05031b090702030d0e0a020405090105130b0c04051c0308010b040602210d1d0d0903020d06020313020a03050106140901060206070c021c060f050f010303020607 84
    0x800c040d17003500d000768111000503840a008440403410400760b40c0ca01d40c50700c101042024400c0f904401d000341c0c0f140c8007800d062200300e250a00210302c201c1c1c40301003543d00d01c2c900324954842e160b00c0021071824087d00003842c0000141d000c0c0e8881c8205d8003408207980e5402c0c11400c80e04102e07508001d0b444507071400008a824034045075000148121250b1410f91500042510350310082c8092030000c440c1041a030515074401642d85c098454540202d1510707181c207000079601c4081f00280e1001c401c16820035010311003804100c0e0250b1100980a01c6658a55814214000003800011a00e4087c150070b4454051280e40050300750396005201e00007405403600d60b48020340000300020712826005c0c40c030502581c2c0300294000114400c130300120340c981c10141000e01c907201b89e80c0c1240c01007c1342e50040c000c040d000709100303a1055491810031031418040c00082c031160307050044020281e4001044a0030b02c1410b81140400214400c0c081c082d075100c206211310000424400030780143c00c520041096280f017 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 199183219 1250 199181969 199181987
    0xc0302120a0b010e030a0c0e010602030702060a1b0c1d0105030c01050a08060d021c0c0503010b1309020f0a1d100614030a150603020403060b030a0c060c0f170a110706050a 75
    0x2c10b1500c0d164040801010070714040e007014095409861000c03040001c0c0c0c200c07030200c1d80980130301e1029600b004c03c107074003049050248400080038005010441c80800440752540c815058004251201c50741e0b450000307043e417039500718080080d42c031000d00205480c00c0005400c409104103a440c0780c64420680c40480b5054405844141d118408941100159803480e6600b40c5c1a1301043d20007040c0185440c110b0500c4c005d41e40414081c0e41030001c0d521603695040d204c2c1d070040940c20800b196507585440000d444d8448048295881a098000030804048941201c80e1400001104c41c4458480c44080700c48070300248500030000312222a0100216102070195800041201021407080045900080b4034030003a0050303800a030b400321b003c005103c070602802d440c11409801070b01c1c0c0882244c0b40d441404003540901c900b44500d4a007450300b0441078240c6040c0c1d103600a801c00e01107095079034182d4030642c049510b94002490700898944005000b0503802c080300c4154071083d140403410803042d0b41c0500 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 199184469 1250 199183219 199183241
    0x702040f0b010807053105190b0f0309101109040b060f37030c030b0f0310020a02030c150f060604080d030c0e06030f010603050a0204050f060d0b03190302010c0302120a 74
    0x2074030020088480c1c1901004211000741c011002209040900780035110070015142c000381d20480f4410009e26026404541d0004603c0603c1a030f00d03510406002c1c9800540010140030f64607114101c090034601c0d03000350203004401c0381c0602100d100c840c00c10805005d03c03031010303218160400c00c0c42800809203e801d0729243c40c080a560b0ba107200200c120402d1010302c1c2c0c0c0d80011a8440600e022420782c50702c10407074220340864804030b0441586012030381e0740491203d200190740d030010300020142e008000303684060a140c02101c6c5006261402c96198000a59903a80490f001310049105442c24500b500c00384d9148000404040e101203404078042e092849045082c03042c480d00700b5040da01c0786002180f145080701c404c2481c651400c50b000303040300c40081c6142141c41c414403060013155154141c041c1d00400c200d960769150040e020410700140a0072521513803501c1201030071502111401c4030301c51404d02a8000708440c1100a60a0b4207a00c40c1c40c602602d403842e03240c0011700b0100542c0c0907403d092 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 199185719 1250 199184469 199184497
    0x7081b01030e0303090f161202040f110403061b0c03080403180911031b0406020c190e0103050d08060a0501090b0307020a0506070306080c150702060304060906020a03020702040f0b01080705 83
    0x1407004242e8504580c03040c1e0f0b020081d500100c0502548203800c1225200c00d0030341d0003182124600c1c081508a008104000c000c1c8100e403901c44402283e0b0313050700320000d000302c20054955100e40d03900c0d101d00200940303040081d4146411501c10300c20303809911140c003c2601500c5d40c0300320743c0e43ca42c1c0413525055060070801c409003865001003045101c40c0300700000301003d0794001d80e481c201103a0100810903c1d85c1d2030300c3c0000c0104818006260b020520a0501c0b01c117139200c0303c020030111010b41c04c1e060250005549805800700000a00c8000035078034201804603100c5c0aa6500c0b20014010082d80703a00400c0e0128682610070070116010f4002517610801c68810703100511600d99501d420b00c07105451480000c0e0b11005c00340813083c4280006c8888050444440c6495406816050b81a0040c41c20291007002c012000800340b100e10341240c0e0031640c1c030280c11551180e9000014009412003031f07060340220b1802001c0e43c0340441d80d108040c08614141c49411160303840f024102c076143d0040851000407 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 199186969 1250 199185719 199185731
    0x105060d090516210507140102010603050114071202070c0308030603030c0105091b22020912030406021014040302070302101713060c02160504020f0909072007081b0103 74
    0x100d2410722041d0303490440000b03078008261401446629010252a051902408a84d4038400081c8000f65010440741986420758030140359800603801800242c2c80607015508140c880e0601505018046100c3e0300b60342c56506100c903000120400303e026170b503c0100400d8420700b0920105025102030b5038080c000600b101d00d005a142d800fa402c2d2a010b42d2180d0299101c03808480b00c0c6600c1303c021484100e810313110960380148640b028043c04411000303015195500260039a80d903242c0180b03070042060014100ca035100c3d5100380003581c0c0c6100c55541040c242c44c04480011400a0800d220301964043e40140105821a001c10805e4018241c2c50018020103d02c0d02c1c40d0301c180344d5503483c82070031754a10002c01018182081c105444241c0e09a0f800c540200c031394520040b01504919096030f200780e50041c2c95007080112950309205014020350f010700a00d00700900e0a90007850002500c0c01044c2c0d0901c1d01c1d6031140a1944c41140303024090303841d00608440d940c55256600740e9040034105140229407 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 199188219 1250 199186969 199186973
    0xc020d080c06012d0e0402030f1204091119120f0606030b15120c03062e02010e06011a1e03090a060e060c0d0515030105010f030201081e0105060d09 65
    0x5a030340030040540c45a0010b200401598480f950319465011031507840c42070b04c00c10a01c4201e00601c060280254030500c0340042401e64400300002aa1050200c044594015808044180940052081038405414260302010488034081950b40441400e40c2604000c000c03807000761032142c40200440c0d030182d030750359012050100ba4001c9400030b080380c0d01c0000745103140f502802004280000c180c100c101c8108080400e01c0030303100c00d00394054030042c0c6542d120b45940c40007071304d01005400f03c0d80c048085a4000140006d400100401041154008120482c08101e0341511060244202c00050500c28000da504042490007411100380600c2e15510205000000d283c5076001680d052409500c030f070282d036003084141c5c070a4046507040d040c0201094680001286010300c6040303030000d401030311040400c50a984c04a4100c0014800800030f000e1913848540204c0d0030282c5c0d100a9000a06c0c1401184800251a012840c0001c04000a0310240c0c00c140034424580e00178406c0a04088e9901003000c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 199189469 1250 199188219 199188233
    0x14152e02160b07030801051917010209031b0f0d030e040f09050f0a03300c0c021206090d080c0301120c12060902040e0d080613140906041a040f02010c020d 68
    0x70290282c4215035444050504009200c40c10503081075006400c2500c5028480344031340203520458540c040d1121085501441c0e880c064000c6002443e00340c0f0400c4000700c81030f01160b61031a5804402d680542501048c00c04101d1049400100540400c081c2c0d144250030b401e254010020b900003210380890011100d03500d00e89008800444021250048440380007003541c01190072643c0c1d10b9910300c11301a0130300304c100044842c500c2070403014030030780d195441201e5a0141c13407440710007500140812082c28400c00c00d15100e00c001c03206218a40940c1d540d44800ca801000f00b03900500d101041d1701e003542e003003540b02402000d40340310558070129060030011300082c1e808200000c040c0309050120722400e1a00c14041580c15401e500c1840d82c1120601d5111954410b42440d40701070121203074000c51000c10905401840d000c0030811504624404200107030340002620b41c01603204442101d403007c1c0d00840880ca02400741c400402d50303088100c1150156203d100000003480c00140440c0300c065140e0303600c103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 199190719 1250 199189469 199189513
    0x80a060203060906010f080a0f0b060a0f0806010f020c1c0506090703020114042106020c01020a021b01030e0d0c030e090405010e060603061320030114152e02 69
    0x2904540c0000801c0040d0a050b000c0c950800420300384025030039441180a403500310020040e00d034241daa20800008070410f038001c0707050740740c002d092280e0301c00250304001e00d05c42c2c03100b8400c030100741d86e0800300b072480d44940c4019001c00001d9000d0122407040408000401c218502c465440c500000711b20302c0840e40c00c1c8541ca000301c1c0d000005004c0180b8502c0003514031503410404c3c0e41125030a2000b08480010b5090407081c0720149030b03081000768024580100240075218043c02c05620216800051940001d600c4100c1a2004a01911034040c0070044003580c80859080d00241c0158028001c828040c918440d84588241000e102c0030b00c0c02d00205000b00001c4400703540e56916800141d40350700d01480340c40c0e0422025005010030345006168039843d803040200c02441c0c00e03a0480c10f800f450130640303003003511007070002c000740304010300a140c0c40946030042d10f500490031603014090f9485d180c00c20f0b04da13004800d0a890560a500c20310310f00ac03604040c45c2001c000703502070f50001558004180d9154 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 199191969 1250 199190719 199190723
    0x2109120a060e070e0106020a0309171f090c0b0c19081603050406080a05010f0b1c050103030c0b09060f060f120a03080702010c020705060d090317090309040507050711010f09080a 78
    0x10300700c3c01c0c0350500705182103006a00c58001d6410040020011035400b1403210151248124010b12410203109064035080c4204080325010340100c0f81c2c0c1107401300c0c87e04407143c0d0602805a8a00558844260344050702c03400c45000d0090348101c51001c1d00306844080841004d0080d03e00790f06200c5c0c020b103031006104c0c0075842140050030003d000e0010b140c200354041c1c0c121505401c100031030341c10709800300c20200c160300a052034004042184070100d9404c42c1d0110421030342c80000e202e10b51f9649009003080000d6202225440c101c03d001071301d4a20005201d9110f114403a100c4400d0303490301004c0c020707010002810540c20000c002d15210581404200d00c86199100356203584040c0fa103184000d0031a10600c0d00402150060a001c01480d643d0000b41c0d928456a80710000c0e80320150b19054030192003a190b08036200499008000c606000070001e0f140d91a0185c07014800c85c0c1d126041200c00b0f20034280000c1c125091090503104551040b140780a10a025040a1204c0f0b6104c031810342c5003100c103d1302 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 199193219 1250 199191969 199191973
    0x50c03250b0f040212010b01020c01050d1e0c020114070c200d14061506030c03070306180603020f0108011809031b05070503150708041e0c03050f2109120a060e 70
    0x60001314200010040c000101020007045039410220000303440d15100c400300703030401c0000309884c00c00c0c40c43c55000c2e44510100000c2c10300440d0161148402401c405040c00c1c01551810f01100442c0e0700c0f0b400303103510415841d031781d40c0e514000654801944000c2070407080082c0b2158922904180c641802c00d60000b4014002c00c0403502645008134500316000344507408a50401c0092165500d4030029650000c1907594100e881c0d6403410400c0300140141e40c00640354005503405800e21140079031005040c0c80c02900e03280100703940680192201802071140d100c9041610103807105006440d480f540140384285002224011000342c01c1c8501161290140d840d0380000904100510b420000c1c8083c80c008042016103926001c2409808440e0040024040500200f40c041c0603000381a44903a005074003041074071090b616800c10a81d21000e00215100e03600c80c4403a03048000080c40304a13050608010381041c43c1036032800601c003205580441240292042c1c01c0c490000901c82d01501a2001050300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 199194469 1250 199193219 199193221
    0xe0c040603050c130608031e220f150903030309050c150d060806090c010f0207052d010206010803090d0204060b040801090b0a140f0618040c05010906050c03250b0f 72
    0x20010083c4145094a0a5528145d0b08105142c00481514143d440d0145101c40c1230b641811048254070500300710702c0301c1e04403101e48641012041d0b500300302620f00039440030300c90035155030303150544082401200002c142c4106042000a12a81029804902c6101a1004d204070704d00464891a50346c0100b40c2076000119503283d00d80104c1c450030b030050032901d0041036581400d007080c80d1201c1c05804842d04000e0001100700b200c81c001c11500f0300400010340050b100b2440c500c415014000c40405070003903040d41d220425a698400554203060b2417584026601d000c00c06c0040100143c40d0290403030b00540c50320300c00104103140c000079200824207000041030388000351410091004004121419a0785451141130030072840c004c01c0390707221807811f050303440355143d40c000594945886219000242d0101c0c007013204110140000c4000c8072001e0700d910300441c0d01d440c000c2c0d565016000300d0300c8240d8005e108010140d500c450601c003100c00912201e180045045c0c0702ca80801d8021614644450202c00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 199195719 1250 199194469 199194493
    0x17070606181802060403230708030703080108010e060718080106080307060b010f1e1e090807060c0201080f1807080318010521070e0307030501090c0b0316030e0c04060305 75
    0x40585810110803a1103401c1e07403000b50340020700038000c50202500c00d102000028447c0000142040e1100030781320304540034699070b22099603899000d00b4007240010311420000038a8074050142c2581c03401100040c0201d99194041240c03510711115000c0950f40101600040c01c09007072141602802c94100a19502c1c03480e07051034000c1c0c40e00c02c107081e030400c030030480208425a80401084010b0403482c0c01a081490301c0841201c20741d521070010010140712102c5103244541200c01c541c00c0b69130b000f080e00c1c0f81030368a400c10703280400070740e5010740410600780008500f540500d4440e40e110004a50942001c903184090514205031504081016400010665071407c1c01c490001c0c4854002d00c0c4c045e2502041a22841c00d2241d1800788801c01014100490007540c01000000030002c0060115640d00f0343d2810b000d406812a07510070746030505108004668a104841100e1240380d0315500780045003041c00d0708800601c003864441754203000d10184448103603103e000d0680254017034402000009100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 199196969 1250 199195719 199195721
    0x2a051b0313030317160207090c090504020d0509010518030d091a011e08061501050d0f02032a091c03020f010c1d0102160b130810050f070f0206041707060618 69
    0x9450075601d040c10709082901700303500182c25401e9503050240400c01080000c0180e959001e2a00f0240d07101d400030a2007204101c1c90340c4050f00c03440702c080081c00b1076102c0d45080e6148030b8402051500941003045443c0d514441b0384c0060205a1003210701c4207103c51010700040d01f200d002c1e02305c00b00366038012294103020781080880001400159000c1d00035418106c08070811900362081c2241400400b081c4000107c441d41d100041c030b03052103601036503680341200f5400f00c5003800426041e155a006020525010310b40015245204001303044815906807000020744102c00c00d075012401c521400c0b980ca51240001c0c001d08002e01380c107445504410381060503041c1d81a41507a0503d0440d40201c0036004250000075142c0c0c11240b1801e1003a5880d110000038030044801c5401803029480b07a0340c0300040502c02640241e00c10070748110140d003162a40780f0100c810740d41c0420142d005074081c00100c0d0200b456440e034805090460440036252410076969142510129401091102c2400104840700191 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 199198219 1250 199196969 199196971
    0x207140a090c02010e0d090815150904050d0906020c0f120a05030c011a0f0307090b0103020c1207060c1704120509040c0e0102070518010e07020102120108012a051b0313030317 77
    0xd030601f44046400d120016603186004005001d0b03104200010410f003100125038102c0310000070b040b1400c0d520b014202190307152900c0c00b84100040c03450300001202403000c600d0709002c25000782106032600c080c03c00c1080880402481e551640240108400003070010002481140c4001e00081000021031214100d403641c090a510301581003e008520035640c041260001d8440785000042c10b8618003004900030f0058001109040c85130f512405007c911a4000c0c01c0c1d40d80c450b0324280b04189084a04a03444c1c02175a00b10001c2c5100800841e00003000094850380b45002441d00c0b40c00c140d1305c40005010303625448c4842000c40c15003440b4500c1541d0600c59400a4031040d201c0c00201c41c80b01d001ca030119803052040c18540a42030010400b22407007901100d010781600c12400c00e480d41c603071208034020b15201c620074000036244102400d01040c1928803140d20101519000d0030b00c0d00314541c200c110143d800038645580010801304c2030482200c2600d0000d0350007a81c031400b510154401303090b0000c030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 199199469 1250 199198219 199198243
    0x90b060307080403030e190303050a0c0c080711040f0203040b06240d11090d050616090f0e04030908010516111c0c15020301060804051c0207140a090c02010e 69
    0x1081000140754000b50100c1c2c0181c0d261034001842e801c80e40c40142841849595680070989002400301850362680100f40110140d450422030000c50b0701c819903540b0140300780144100010300c80800812480c0780304039410300c405400495880c0300039813204100e0380105c03001c4584892071418840181010f070403000300c3c07514144a02200f528458040003841c05030320b21200106450b006101600303010700003501c01d007050180040da03140c081840d21a071600307011580364000544043c148000d992080d403945044489022124602e0750515645802e8410010000d40901a4407400050b480e03000344a254400da46003032048502441a49001300700030711468090f10164800003034440418000d0b40070134101007030350900180410180c94500351504840c54405180307403001c00005042c2e034202c03507528400d0340b207042a18403004035204041c012003001450b0305d0050340120000c0c086d081c100e4038a0759030340800030015041c842e941c40c404030550300c1041e181c6006135100d114140c8460010441c85c60644 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 199200719 1250 199199469 199199479
    0x5041b0f020d08011401110a0b01060f050f040b0a02010b0d080306011206140d02130c0804020f090708010e0619031536022d0907030c0c0821010f090b 66
    0x540302c030000800984042c000c4100703100001c055005039a01070341070100f00c10f800a00781c1b0b507521a18242004c04180034481c0c1d0010030040900d004209200700229110380410440841c20039080000795205074202846103419503596042c41070f080d44d51801c0e400381c064405e002c52962407400600050800705241d0142d140e46042200900132100c84162900c2e80072003e4904506103030341c40c00080c01e10140d80030418202c900d00600381c050f8a0f848484244240c1c026035030007a807095030006020140004407045800604401c4c0103002d03c50f240840107801020041511503c00b2410328150328440c0780354400c0b5103084030030100304407018550190b02c121078904501e00d59101442c03d040802000e17501c100300541300d10342008104540d43c1061211000c0d00100100760310303004010a20300d100610100c554400d03034121001039140c0d446809200585181c40d0b0341d031429440c0503070340c000880e04405414951001300c58880c18a045010802500030045034010b20407583c5880481070807244642d00c642c1c010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 199201969 1250 199200719 199200733
    0x6040c090606090b1e0403080301030302120315010f05040f06020313090603020102100b0105040b04290c0c130e0f03071703070c0213062309130b04030c0302030405041b0f02 76
    0x2c9401007044001c0b244849421541c4640c0b00030754801d00d140c00c1c2408020103c0c041004400c1c00260b9002e54144d078800c0e022601211000c4030002c04501044603400c0d88214540e00105036548903104107003080d1b4643c10482d003480d803954200c03041101a50090001a800850010010700004480c0e1005100011040140700d0864000035200d002100c4054001502d41a110301c2592041044038014070161030156212034072100240002d0074107c070b01003c0c1c2d095400030540c50300b6408040b16a00f89840380100b29585101040c01064440c02e852440d00d6550340b002d40300390140c140230480030000d200c800396a5a0189261030344200490740d203186400f560030f1040204554101d03086059090b01254580314005034800d800000c0e001c580c000059100d8461b500ca204036070103494030b143e4039104a540700b0340e503540d2010f0700c50b40b16026034000e8074000c0c82e10041070110b4041c80000310803030300900c15207207003076110303070114041c0e81d4115441d540010110482c40c80b202d6201c41c0c8502030882030b00c090700d06 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 199203219 1250 199201969 199201979
    0x30e011d0303070503100302040c08041a060a12061508071701060803030a05090118060b0a14180402060d0513150c090902090d0b0c0903070b0703020a031209080c06040c0906 76
    0x150b8000200010103005001020503050f03140075482d03a0003594018028010240340c417100600b000010349084440303481c1c10170080403181503540d88600c1100040c0c41c4800710340c6018450b01c051201500103640e51561a040b2110006a074200a40070b400c2c40b8004140081c5084c2c18403081e40b03c0c807060700030f00d41d15000d028001c034803010044903040444014041011703107440d42c00600520717800c001e9445c0200360f80100410080c554021011070f0100b140c0001c43c0c3e0740c0e5404000d100c0300c1d0806240c0d50023041011120105010760102c0c68009002903d090f04110403a080c1c0c07402c581c82079516862001c81c58000b40100001e0300101000020280005e000b0b00b10302c0c103000b42c2982c0b504d01a212503142c01142403c095121a485610748540080700c00625003401d22041206620a500c1c0d01e000f4090304401213614440c00e4200d41c0c00c103a040d4014811110542c60031910b4560f00c0303208070302c40b41e16000c000021513400005031465400f250040c0080f0b00b0589848044c90304d00340d01c41c819150500c102044 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 199204469 1250 199203219 199203223
    0x8060c040501080601090902032404230c070c0f05040b04020702030a0b06060c070605130f1208071104020d0203090705030708072306070c0e060603040b1305120a030e011d 75
    0x110341c0203003406000d58843c40c005030340e500d80a0300802d210070f201004005040700c0146010840c61008456242c0c0701c0b11000138030081d00c2c004100320b01c0364078408030030484200580a0059015000d040380307509088841c1c1c0c40c00310780001c80e1312105000c08a0402404036141034411180c1f800d034201c03030452a100c2140c1c0030a0300d0741d8644001500d260590000140c1945450044511810806080c0c0c1d80040d00d8480141032034012010b14012101c801c103000c030b07000d882d4941860955030341c640d140f1004081a642c80c5020f61001c0700440702ca41c0e441440102503202e90025150603070079200c01688915040411900d0081154091482035225010400c400030f808030341c05007510f07100710111021072a0380e00000c2114480c0c01740540c000e400007610b0001d00c04044400c2c0c095981411384034040380c6a200801a0901050310050181000700001c1542c50340c00310700940b01a8412015515902007419a0090325040558400c0103e900d480810312480000e1040300c010828294424059041941c0305503 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 199205719 1250 199204469 199204477
    0x2090106081306061d101409040c091b0e0301090c150908060405070518240f03061005150c0604030e0d050610030c060c02010c020405060a0b0c1608060c 67
    0x30140184103011449a2004000404142d50850741c1448030307640c0c5d440d0b583d06400c0d51505117100e4500c0d4002140800b1070286200c030031034886040c2100840000010040300010140040740c0c5528030140c0050000104d0140301d00307041e902198008403c00100c0054154685200c0c07043c40303030345409011b00002b0394203c40101902c1060614113240350300c110b815511485181c10008061043c0c2040000f0440c0004c1c08200352641036600c4040c840005100d002804000c1d941c4113120040c01c505040034031185403a036441518001e080f51a200e0a1001003400d006040d20b208110380d03001d0909010f01e0030030405030890461181c200d603180c00c01e448206501c44001070401810028450400c0034a0f40d40c034044c3d010401c0d0804180c50043c10815041201600310784022a0744140481e000100c1c1806220400309258060319200f640300801d034204002894020030b01548080c00d243c0c045001c0303400c4805072286c0340c2c003400100303182c5ca41d0400b42480c0703484551000103968846000c2012588400040e5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 199206969 1250 199205719 199205729
    0xc091e060509010c020d050d1b03020c010c030917102706090203031b01090201020616020309191701090b0906010302060d050603010b04180b0105010f02070b0310080304060801090507080103020901 86
    0x2640c0b6444100d0040300c10503402c080103940225003100d5541403042c0464a155883c09585560704400781980c1880d07101c03215084041c0141c0c005141c0c505d410b5020710850000948280742c0131040c03545400740b80180c0390103a0020b451503440741104c011401030340d129600407024001c00721000d1115000d0f5511200c115404000c11840d11107815038219142001503c1d130b0084410714440202e51600c107014000d0a100c0c0c4181d0041c4140f07408030300140801440031500c680140d01a45c070341996481444004e001c000d00c11040c4c0c02020700006012400700c1c0b080314290721070800106194880d400c2900380b03220007a21045194201074010001031380d4160444d40c660082450210b103aa942c50002801084d01c1c3c4007064200b070400307800040c100100d600d030344542031007001ea11501c0e0740c0311401140d849200920a00140e80b0240d4103020710005a406150b001408070f04242003192600021400c503046a40301d04042000c03100103210680395030062030307404100c80c0352041c2a5031450300000c000d11018412 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 199208219 1250 199206969 199206977
    0x60c031512030d05070c03090509010e13150c0224310804030f050f0105160324030804230d02040911090916080f101d010c030c091e06 59
    0xe0300641d9006200395404600101020071592078180800341a01d0030821088001410b041d10104241c50020304980c1070390641001801c4564a402c00248058102c80c8252245452500e4030b03a61401c55008a8456100715809400f00c5000f94019820300340c4250180140342c404481045001d40f20040e40d55400400c0f5031044402c0322142c0d80845c040141024003a264001c000f4000c414080d8808800c807000e41315100f160340302d03411308210901320784040d9800300d0030001128520405612a800480c44c4250004903543c140c1240c002018941c4040d80c021902c44102150070000c9000010000b0078400b4040380109412507813100054a900d03030740c90001d20640d680c00001c030034051104041001d050018128003d40d0070000d8455641d0b81e00e041d0140d02c04000b8641c00b0a88800c081340b06c40700d001e854802024447e05804c40540600055850380301034858044080444140074012070a81000300d490004035a195407400074000110303034011512840c001348034000940594540030013180e40c5490 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 199209469 1250 199208219 199208239
    0x40c030509120a120203010803030714030f010b0d0e0a1a0708040c030219080604030e0415050f040c0212070b040b0c09060328060b09040c03110a030c020c06120702060c0315 76
    0x2000b41e035080240107072070091178404400810a404000029801006192140e0100c0d551451a40d450343c40100c3361100041c090384010060300e60060701400c06508c01a01c0403411030046d00c8101d20b00100c08005a901880625141e20b41034401e41d00590011070300c1c601070341e040c54640c540d20300440151000074020385228042c5480708400f2951034019010143c29502d180c10a0700b001000c652406480b248207516007075220700404c00d00700301841200c80140c01c4004c0c011b06d0104010007001000e83c5601540a030707502c0d000c3e040f014140105502803207a9804c209505050030f03c42d20510b001001c46c03800d170400700000c5803d80e556500f81c1e58004040a4000f00200c08030b03005800120030701c0d01640d0074600306800490f0312070054000c0c14840754103441c00c020f545c01c660341c214151a03416010710b0b80c414040101c000e00600c43d07041903801e8140c500445266101c600e020803119030042d4500344510500c0000d0007500c5a051200303d8000916407009401c60401c2c0c444d06c080c0b1320001c0d4820b03114240d000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 199210719 1250 199209469 199209487
    0x31407051c1104060303020604020102160609120c0506040609080705010503010e0c03040521180d0224090901090b010f030b0109091503050f150702010e03030105010f0c0b070e040c03050912 83
    0xd0800d01c080b900240051240360703030300d103400b941c2d807a410b9074121301501175800c060104000240c0d01100710740340755a44e00b074014500a02c5200e081800c960a03204142c082001040549440000344001d00703680d5200f5400b5440c1c1220242045d0301070f008541000f1041004110140307951945a4110305020304059503a2038920b0031034a041d40e480f902103504a444400c1042004000c00907103045070520020740c1080001008100340d00d140044020340c400d15240603428869048606100c0c60500c2c001c070309141400090028041c45000d80c080c2c0403041d202c00c070100c45568002801d40d080b01c0f03c0d04040c04010410400078012411900440e118030f40d9071207884090034900c0307d00348000c641220a4412841180c80c840da100d00c04280740b040800301c9880410001c0384148030b02425a101840a5801c503424180111602d03103c0c2c4d41044c0800c9400580040030400386840140a0b0505440d070440c821204001d00c015650b80a0060b41410301d0101040342494001c503120f48504001e010181d6207110791 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 199211969 1250 199210719 199210733
    0x100b030112150213171006030210030c02030d0906020901030606020c18150409050a0201020c060c060106030f06180b03010f090804090f0e0304031115040b16080f1201031407051c 78
    0x19010b1500300e44c880440054074600d035640018561001c038081e01d55206403805400c00f501d801e848000d401808210000410034865030200007490103500c1503e18010181e403407007060318134504042c0c40c0e140d0300056803115503030503206420052a0340d0000d0901404254001207800140c0c20108403c82c05013400208070109080c000501c3c1c8a0007081003010034840c0c1031035580c400494004070b0240c4203904c40b600803450008199400c081241c4020407050b4308081045001d880d002e280441040d4a40401080710b0101d81100300d101000082d00050351503402e0109400e45444d0388a06c03030400c2c60408084041600501101c0695140c020049210400041030500821070f004440103c0c0c040450003200304011042500780744034080710200400741a14480c014144902d215605620f80c003005004c0d01d6451003104c8505541c0a84400c07414032a006442005a5001e0009102d010000d14014002c1141195058503031101c1e810051407540e09180100b0008000c02c452205a402c0100e0040100108 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 199213219 1250 199211969 199211977
    0xf0903090d1506030b090d0305040f0305130509010e07020d0e1c0510050c0a0905090f0f040c05100e04110901050421120c05010b09070e0f04020d0e06100b0301121502 73
    0x1030b008000941c0c0c1c0b4140101001420b48808500c0d0240c9602c03403d0840c400d004480c0140d0700814041e0148210faa405e440551060a41c9489541d6042002415913120345585000b403042806a11b651315044d40f00078140300701001d4107401c0c8070150610f48401c0e00c032010250344103008a108410800d6103030401c10300c0c00c104000103940781403c000070066000102c0c0b01905c003c000c00c0d11400d95a80d00c03a020455080012285240314100e000e002400c0311000c2110245c020303014101300c00c4240d0700da81c04a21078841c0b20784c1e10340204e000b030220f01499044c43d10402f520180d240401a0030900c0c5440000c2480c4154030503822044866910203c600156080c0381200b40c0c1d00c505036a429a00190015181101d0031806031200d501e0310301d407480c07203051000509200780481d90380d25020004980c100000c0c44610000c094200e613091211005d405002d00c22010801010f0000700010f1030030006011034841182c000400c0b5171018030040007040e0048031484c044960100000701c41c0440303814880001d000e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 199214469 1250 199213219 199213253
    0x15101e050405090406020705152a0913061d010e041101050f130f120c1505070c090e06071d0609131b110c01050306060a260f0f0903090d 60
    0x9000241300410240385c0c014442203100e0705c2031310060340303c00d0208052402c0c200e803980c1001d00340c0c2440140c111484107038070031200500c2070701504200713848002c121014030600d0854160307541c9000c01e11111840b0003802000481c00103600070700c0d6040c000c95945601d030142c40240700d200e120700c03e0b0005038004e42c1900c1030810303005c5e02152114034100003072502e20040d100345082c0104404022540b001c05002912549421024155842d442c1c00c451b41340ca88921b100c1c11003001030502400c0c002669075400000207040c84900402c09000488519003415005040c52090025042013040d02c1050421000d01ca0041160f066807260b2490000c5850072101c1110104558503140740c01d04129a4214403400c40380c0580c1d5542405548207004982c1c904042c00c503103010440a1000aa42f0301c0c014008060010441c5858442d1441014008602300740d001c01051041d05540100000203103540c00c0e403640003211114551060802d4061a07072284109001c103401580c4c20006070f01030042c10050191880 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 199215719 1250 199214469 199214479
    0x60423060d02060304061b080c1801091e0e012711090909030c0f010e10050406090503040f0608090c0108070507020312030a09020f030a020a0509100302150315101e050405 75
    0x80b62911b01071005041c155024200074804031456141e21744511040d17403080414105040ca405a100f0343d1b01002980350702c2d03060401480c6100421911b44c140e88210624080000c04c1d0320681c00c0c10300007281c108050b046010490120704014080c401010000c484409040100180b050500c00058a45114442d40541c100030b000c2c060081d1004004003d10810042805503170f81000e0351803001d4280e0b0380d403012400340f42d0b01c002107036452102c2560009404c184030384400148030704207540e81c2c0d0440d00f01c2c0d4425815181029010445603400c101425401050740c000340a86a80c4040042c0288501400b424200680400c1c80021900c04200d03c440303107501c89a9498407894503408080140c1400c180c128058510494015043c2c1000920307415400e40c0241f60466450902003403050201c0c2c010316842c0080ca400c03030300002603158000b81c42c1d0208031136031030070340d4030303d4161140211004c10030025405410345072407100350741d58030084041301007580400c0d00901e8140204100c4071402190055940b217 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 199216969 1250 199215719 199215721
    0x30204080d0906020f071a0a110a0506010f0609030c030f0f202d1023091e03070302060a030f051602010c2d030f150e060423060d020603 60
    0x40d9030402c2403402255540c2c0d08072a4104000150b035519010343e4402d1007000ea40140200310003184500241040e1502031614603240c04000507030310300c0d08514401c240c03a030360002e00041c815204903000d00005000b40c1d080000742c20346183da46c1c420340c0881c1c1c072019010303450215001c0204001d01100301081d64100d000504480030f55440481c0c03101d988824503200e0700c50218089641140b10040c506150100c0e403910302c0c225030a00601881d4940740c0500c204000210791403140c0380222813608414040143d098681b07890415082c030441c400c10700f441c440e290501d603100640341d070307000559107098943c16240f0340d480e1000d05074203038050a441842c40030410300b000708018102030203112101e119015039000307001413079110405507000c1419040303800c07031340070010305882c20340019101c00d441030304242c50001426580c1604c210110b40000c0c2801410030703001d80f0100400081e854513940c0128084404021a0044c01c00c00d04d8042d400d0328100c18140d0031840003481030790b00c04490460071a00901240d40c2d07 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 199218219 1250 199216969 199216993
    0x307030f081302061c06060c030509090601020c060a0f030b01170723071115250507030c0b070620180604031406090114010f0b0d0b0a0902120603010c05040e0703020408 74
    0x2c8242c41107650700c5c40030b240000000f42c8034801c10303480744611303090b45480e80713080741d50428841500002002a415440b502244140170f4560074000e115040131540c5a40000840301e00c01402d48011000c0c1c641042030005968410900070144180c220320300f8201200a25030720100c481d40c104e0b002441100700310b8007141b2001400005c0c900c1c50f40c80e8804440e80c025401104440c615180204100050b031100c0041035251404059009041110300a0007100c0d00b50740c2d65a01c012840b5031640001803030703400114a030800c00071b590042615031707602c5110050f40021404d8540780e05000d4450014401c50348083c0e2018141c03110b508440c00356030400303032803501c91700e81841c5281d4895055420100540c60701c40314110513484640c25070b040c0d800da6107a07102c0940c60044808519000781e101c2c80c0030b080da6000003c802e55100d2440700300800d1050b0000d81c42d154202d180311558000109094003903410054080c90043c1d00ca0115400c0e92507403070300818035480d056800c070000c3c042e0344c11121170351140381c1134410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 199219469 1250 199218219 199218247
    0x1b0310030210350403110c06040906140d1203020d0f02040f0e010e040f02040902040209031c02010f02090a05040e0f070603021c0b0114090f060310060905030307030f08130206 77
    0x18480b00805142c3c0c800c80d0b54001c1c03190018040746003803240003c004007042c0081d00c14032002249441a0341281c003803031031040c00071700c6691141d03004c64072060351040704002c000301038410380d11140d00884004508560710740702c1c03540a400d041025000c0550000c0c0403074000203164403140c0340c00008402151035076103401080001a216015400000c00d519000152581c002c070f00891107540c0c440c200c4054601a07030700340300c0541003018007283c0c0f0a40a00009150303071800c204941180c4025400118010030000b806801c45030402103070034510707004020085240c0c651f0030041d81120401d6a0010310b501114040c50b040545689440006000b90000020502d232705030050030b414601004808643c1c010030003503808480300304000501107112554440e6896a0910107810802d0003c5d00030000c2d46106000104170b0780c070880d400090140e840406004459002000030040c0c64142c0046103400a00e8a003d0501825400c00c0020010700500080500c1030203810907a020b603025203441d03120f1405800c140 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 199220719 1250 199219469 199219487
    0x60501080609070602030a031d100c1101200d0917030103120807020c01080402040f0c080f0f010302010929072003160504020306061608041401081b0310030210 70
    0x80c100e100d8440840c022060201d0840d080b945950003c1d89042000181540501801012400004c2c40c0c603800302c2d10108107020170801142c2130000080c180400d68006004020654810300440c2e144c8a0340400840312000308a00003084140301544501c13001c01807601a02c42401e0060044290f2155240300c2e92550020390b041e01e10a001c008a54401c0b100c0c00c441c010002c03200240180d00a030404490341d4052404950064006000410710402d040e0000c0e0584003a026080005403408041041843c44401290740050128203001e140754035640000380399460a0191101034802259032030f04ca00305041c2400540800e04009507141c2d801e80c10003021314410078141741c0900303036800e00c000703040d140c00319048a80b0600780ba512401c043c00d00e01804006d401c010715060704071204000c0e02d42c000386400024007500e0303c01d080c0369944d18148480c2103004240069070390b060141c2c0308103009403d000c01403105805041040030075100d036200014203201076041c0d8800383d0000444a00b010035154422010 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 199221969 1250 199220719 199220729
    0x30706020a0c120308010e1003051f0f060305070b0d02040806070804021207210203190f1505011d070e1005030907230f03031b01051909030c03080613020403060501 72
    0xd580340e543c440780180c1c2d4205010008000440310001840041c3c41200a0b80e040740c51425005e1900340c80740e54403031410368080e10b092081c85046115416180d0203015048407440c110000f444980c1ca103580d019942c1d55180500c100492000c5480641c000d00c0d5415540181140c0044a0141c1400395015003000c800b6107003070f0700a04009007034a0b0b40110004000080380e00414030703503c49000540d01316545081001e01268180903200b0110001815410921003250160501c807400404e68a41804012100c142c61040f9900b00401000642160150490401d0100300f240305287d6451400704c800e48034100d100c59100c0c031100110f080c280e902402441c82400301c5c000312407085407a0074549895881201618241410401517040c990609803000c1c56404005000c41e42000708480303059603030311040311040e070450b9558000c004a100520351003041e500c10070a0308101107080e549004001c03c42c0e00c0b40c080c2c18064030001017400c07038030b03a80c5085103c943c940b24119201d64030303440c2c114040c107003c2c490 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 199223219 1250 199221969 199221983
    0x103170d021206120a11151b030c0106060219061d0109050105040c090624021f0c0801050406030b1f0503010903170601020609101104030c060f090b13030b090309030706020a 76
    0x452816850005039048a250300f2095091074510001c0030030002d440c0d0303a402c0c0c7e00c0b50701c81800400f42400c1c00034040014242480003540e19540d88d0440d260844100354441021584001840307900b4403a40e83c2c5050300c15070008400b180e001e4801c03624158110022640e01b12543c40e1403024824848198000e5014510800072001d01903902d044200541d8000d0050568500011404480c0511103003c6400c0f544880e0041c0c90043d03c8903124100300e400061348804086032100b000300009a400403460380584001c6504006c110f05503182e844403a100200398821034808503203c04450060300b00c4150080030b00400a10188000d4640105411080403400d03568461000c0402c4940d03001154040c0b148003c0402004022010380d003800c0680708003046100c2042c800c100c0032001c03c22410b4080c01400d01c1c0c1d00c55002240407500000c0105c04103500c0001260000d101c04031084030b44041040480c0e8128110300e01c81d844050b0601d041d40310b1030744843c2c1d061040c0e1800007441500444c00e00b1000d405410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 199224469 1250 199223219 199223239
    0xb18100c03140418020918090307060c050427090501060609050a2102061b030403060e060a0e0d030b1309061413122a080315030a0203060103170d021206 67
    0x91003107858092809140004800c04c0520408842d5640c06807886a1005001e0700200d601101c2c0103000c800280c41e0361245810028a10080c49902d000e042001e03c05444c2c210f18207490a070b0106220035003035524841001c000c6254184440242d00288001508007000f0010140d0325480908040350394400d483c041c1840000020704d40300c640425149951900390154880b500315800c0080700e5029004980c018819084081c54500307080000d0009188621400607001d4003240c076140c5010b031700420210f107043c10010a010000008100e21a5042490a020802010020005104a0840107218442440c04001c00148250703900540b160311140c06480013261a2070440409055000790041c04842000c0c40760f00b40188190700140450400319004c0c02c00e116564000300707084000c00401d6038484d03400300900c5003ca0604448000e01310381240181400d40d01640400e4403980148000343c42d00b41d0a907144d000c600e812100300c69042d50600310866580b010004000c951610960341c0bd40186003d078 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 199225719 1250 199224469 199224497
    0xb0915010b09010207210803100e07170a1b1202040b13060e03030a05120403030f02070c0504050903040f03170c0304080a030311030c070f02010513030609120801030305040b18100c03 80
    0x88424680d00344000642446c24101d44511a070755001400f41104031280c007130005111003100c0c5101c0c0c0036207141da44000000b200c61015400c161809044010001d2074603030342c151180c0d44c055404602a030681030a00001c040102c400b8000c8c0141e078094203040000080e8601d01881c80100b500a56a4030389840c145040340740141a900d02550603604003041e010401000c020074858407540d401131103460b010030944420a5444107903002010101c881d4580d4843c00c3c0040d1605004441c1e0014041c1c0046051528203d030300444041540b0000d40a41c0302461411a2000d018080b1001d00305800101d0341d071603540f00b40d119a00c084d17502041c0c00080c640140041c8800c3c00a0460b03006048010146007440d1094941603814000100100d0611008110450014902c1002c140003540243d8001031002d1181c24803041940500503d401000700d5240107100194000d000e807001da80b40040101c0c1c44090240030061380c5000802865400f000d05218400b1990f88030842d0140d036807080e9204600c5100034 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 199226969 1250 199225719 199225739
    0xf2104050102060103060b04061a0c0705040e030a0c050106051f030501061407030e0a030204050c040e0f071b1506170d0306060807120b04090b070f1701030b0915010b09010207 77
    0x5016541c0160061801003021503010b802407141030784020000940035903580c080c00342c10b0340c0100c0016071a81c0d0101c4c0b0510307800d906121540081c501600c040c00b0311464031011584034800c001c070034001d100284020b1030900c4425030104025050141c4101c0d04a0010b040c05104031108890250000781494008500d041c840d03015550400d01c500d4080e41042d03102c1d41c0035115a00f04e05a61500305400300c80c000056641c40c00380c00d014066900c801e680c0d503402d14a464000c65002845400c030006d510090281c4503a002090a210007059910180d018560341f418980c00d40786408683d001c1d5040640105101001d280403403501d010700d40c03c480c60950b60f00029015035026128030404541080c002480c810300980510b021460403600000b054041d482c0000d08a500011090b61146108030400c42629000100d01c3d00760181c07070400c0c481940b0821486c0c1d00c28a01404020120821100400d0455100f044016100c1c00387c5412000d00d9a10380c44ca058603a0060000180184206800014a4900 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 199228219 1250 199226969 199226977
    0xd140a0603050c060f0d110405010e0303030112110a150806010306080c010831060501030b010501090b030411010c140105041b0b0d2d0c032003060f0406080f21 70
    0x1010300607154500310001006520b0b0840074455100c1d040403c00302075210000c0c45807c40588545000c0ca0300d50341420001000000825041d6000c0e900820040c001c0180962030001c1c4158400c100d20740e1405040042190068564000070340715094070441074249412182c214451282a6020454960350710022a40d41603002c054074082120325001c2010803803048800c40301c81840120400b4984031f12030010744449103010084e00d0300c56681c1c0050007000400f00f8024010402483e00e20403060500c0590381e40ca03c006000101602072b8030200a020364014804840c900c0d412041d01d10841181d800601e000e08404c58045807046149400700c0005000003507c03600761111030346818200010807603140024103804084402c8028265402c4032520202d20b00071400e98590350300070030300011401000c1e081c0c6070303014400d580c0f4402481e4070003c00121035080d20b500110072100c0c0442141e090307000c0b5000b02180d4100b40418060901098403268002510100c0f024100699800c040703410600d440031805 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 199229469 1250 199228219 199228223
    0x12050403052e0b01020115060201021207020f15070c0206030a0506030d020318010305091c0906030b0102010612020d02010e09010f0e0c09030703081c06060c05160f090f0608030d140a0603 82
    0x1e400c040da41d2410301540c1c4044041c0f041030000048104214020465014482d401a00140c1d000244000510680d0a0789a0050344d9030000b002d0038a40c0310303903464440b0b000720046101641d01500044041d032181c007420208503005042c03240e89007420006074000e02411100745000e4403441049078403507480001121503071030041582c0b141c060103820044016040c00780c0301701414490903820344040c0c4c002030600e50981c0d80a03141d58111030f1030000090240e841420800b4156450326804100140e80c2c440e80a4400b41e04460b100350703030220340c4010388052188800141e0401840c0c0000f082d464455203a00c401ea80743e500c010045a660080c444809128117030700d10790190843c0a0410000c0c6014024051016072641c020000b00005000c00c011560650320180010704401b5280741400005c0c441c1542440b111090789010508115996503001501e1080005155403142110210f0800d41c0c03080010f091100196542d888066901c50007410b00940e106004808040104959100d18841c00b02225 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 199230719 1250 199229469 199229533
    0x409062904050f010201061706040201080106170c1c0e0601180905070e04052a090a09051b060c0303040804050a050d030806061303140f0708070b041e031205040305 72
    0x2424103090200d03c0711101c640780d05564076514086685005a5910707003d07449036000400700ac0c80d007030000600d81101a84034005200b1510504103800400710321880d4410442155241d0782c000340660403d01d100c0e58017107a80f41600c3c1c10f083c600d03940008100e06040390680c0c03502164501d0110308503030032100c481d9070040507a8403142d000c0140b034503184c0160381e200d13006a00340c1c0d40c403154803131000c0074442040b00710f028a048020f0b1a00e40c10310b4040c1e8060b400c442d00c0388c41049088660b542c1e50399510200da00c051515400071401050070b981c0c910464504008100990340c5038105480c00c0c038003541083c0102485106009000b09281c1813615500c08000d8160740c0714000c54503040e040c807440d079102540100d0806008003001c404a0506058009401141e00c001c20080c04058400c1e402c004c06904030300300235000103400f040030740c1c42c0f41b082d1000e03582085511014030003441506490003100e03a02c0141702c2c107500d00075101d0158001c4050f004036801403096135000441e0101d11404600b08a610240e00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 199231969 1250 199230719 199230727
    0xf0209061b0102071407060305010905040f140708100203091b0a03030309020d0c030803041704050f150d141e0402060d09110604140310050c07080a030f0204090629 72
    0xc07180601c40010030300007440c00185896980e881d00c024070100c10000040c1944040307420002164144101401090703582d00400003418680d45840100e05460000b40241c1d4002c0c000304441c0500b803054100400c6540c1c12a0700500b081414000650411504a4030602808440c1c0c80e00c040851040f00000780c0042099034140d0559070141d000703264020040c1d80120301c0241440c000740c54110784502441c000c48055440b450a40f400414031034903880d038031500000c1400200810b0715252400452a0001c07640003103503042592411515005e41061106d505040001524443d0348004010340542203070303080003182081011140f95a00000d880080d00080100300c2d2955000b902d52110a02c1e601c5890359800b40140e0000040e11a04181c0011149100c0741d000701d542c618040020f04080f4050500600c014684551054540d0040d114080c109400c00031f4000c1e034580c4203620800816101403000c42d143d544440307034000100440c0c01807121400b030910803003902d81c2da0351201d030011000c1411910300d0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 199233219 1250 199231969 199231987
    0x109031e20070515071104061401030e12070c18020309100b1c0510061208030606070f050a08030717090714121905060606041a09010c0f0f03030f020906 67
    0x1d8207074040300007039038000e400001c038440d91050020f5500340500c1100c180c5405050400003406007107640c845100303e02d400e00420402c100c020b45100e400c4c0c801d080001d80440a03040e0707a0309000d28403681d010080340004210042200707419484050ba200d540141d46038402c4104440128071003900c1d04c1102e540081c402d86004075031a08030707040560b030203090720b0303011000d21091140020105204071119080b001d00ca0402ca00d491040f400200a40c003503110480b000c0e86c0b2109803501c806082c2602074280000c2e02c605020482c4c1c078641d4446e80c00021500b460040c0e0802140640003a5849000207c0600000325621201100980640600c03400740104600d0100d949400400305420143c2040c80ba0000b800310001c10300400c980ba041c81803100482720440c5c9003142c1040030003010207110345030620040c05907500310303c117090187e4018020300340d44224040040e155500c000b480100620800c0d80701904100a110f507160282d07120391424007901200845c04401c0c0d0140342681380d0880c80c18000030f80d0f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 199234469 1250 199233219 199233257
    0xd06050406170c060a090e10080d0e10030603080708090f0a061205070801032012030f0304061518050a0219020a05060a0501080c01140d060f060e0901050d0212010b04020a020109031e 80
    0x40c0117031850232001c06840c0da0320000d60610b4030015009020031ba907542000203904003e2242a40f628131031400700100ca05558ad039220900070140090568200415129181d8880c014442911310000f4840b5494641d1140014448080c81703802e03034511070501001c25869402110301c541170301d07404848040c0b511180b084403a008902c00924079400220ba20b176061005130288000c1000e1480c12016964a00d491308010051311804000c0c21704550b001581000040c001c0c540c1300702e041d9060b00020649407512003001001e4060964820481c0006c4028a14074540000307071002180d2180c4103951007907a43c10107a4003115024032a10441d40c02000e10f800c1b00e980304d041e044601009005150b401d0501c51100b0382e048550681021507902501e007024440c4a821054028140d0001c443c0011190b0504d008034843c0d5185820084c001c000440d50403100843c290084401807001600840d1503140c2c0b00c0f8001e0280001900503070224068000801d0b140e00ea444a41c0368808064848055240300020703107030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 199235719 1250 199234469 199234471
    0xb010c020f0409020103290a05090106091703070c062601030b06060c190308090f03030c07030c11190515090904020906150708070b06030c0a09020d06050406170c060a090e 75
    0x28101071f0f9078440c1054003111325090b40f0300310340070704411501030108106110104003a500094403480c0c41400410400e980000030505407183c00400c08490b404004110349107001d1040000d00080c1c501c0b4022502c0c42e4840701c2802425400784000d034001c803051140d450307854028000501403050300d1001800c582000c04c020b00014142d03c00b01e401e00d100682c10601c100d00c031103100f14005071841c3c2c01e118100340100081031081d2203c401452442c02d1150301c0c1f6106101e0807030002c0074081c030300d00030009104c1c00700c0d040d22a041001d4800e05000301c2108090a001d0030600825200d01901840d141c19041e6000070758046c040042c00082450321b0304e408124020000520701d561145441814485a0700b85d04054001140719141c25074440c2d01d60310b41004401401050070313001758415910007505542e0140305d0070840300150001030340d0b54081c0d01c0810150034580c2100d40c1080c1091070000e43d030248544800707130340c580d40c0003626003514500302004090311400009900095929109100101c0040455 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 199236969 1250 199235719 199235723
    0x52202090d06150303080601090f0e0415021326030d050406020c0a3507120e06180307061b060506012c0a06020706120209060d0603050708010b010c020f0409 69
    0x911428950b6035103001d4401400e051031140303d02c034000300201504541c1d0990440d81c02d09004208600705078000e0b214103104d00c00d8294410f01500441e0a0000003c8280c40c20303103405a0640d43c1d04524002d01d070525106100c0c0d100d48030031100031140c0c019000143c0b203400180800c080c2d403400e007110526501525016200f641c806900300324110003140c08206005a6600c1004c1c00440c04c01c075038920003500d1821020818054900c150160001000c0000300ca00c655488941c900200c24940d0b411a09000001e40b403d80190000402e01c80c02c00d0b904000810740c0c8030440031200090b0301c0700c00c1100d40d90f82140d00701c050340c664420041e000484980140f5482441031415007080c80085d04002119020940e1040410706020700e85070403810034407042000780150380014880c451904034010002c00380c00d810074024076404214007040380d5690040324548401544144800313034403814055280e405520a9800c0f541c64020280690b50080490010554000700440c44207000074082c0700c007905416101f = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 199238219 1250 199236969 199236979
    0x30c0e011107090204061701050a0f03021c05121e040e180f030a0c02120105060319030e13020a2d03020c0c1e040e0a0803041b080601031b05220209 65
    0x1040011031440640000e009547d124110540d00c52124034908806030010360040540120602000101c250b040007241d50580304a00c1d10414501c18a40740918508018100c0c010302000c20520350740d80000e05030180a1000d08600c1440c000c018841501c04c030300c54601d900e240700c80010612800c107150744080b40c9803801900d6881c024030654500396405000e484010504540d951810f505240c0699080383c41c01d880200028240000000e54075400200d6a81c1100c4e551002901054824035000d0050000134120820001181d00301001039005607180d6000604c103402d540c26412400d034244001a2142d1815000300000010308a001e9030050fa0382a020348216918281161a800720b0400c0c41c0c001000e202c1289030500c41048140c2d03072807101601041e40000f41040c0810081d01c122500141d100030486c1001010808103400100642d105204500525000105120711100c3c00e0650050100c04d2090507904c2c1c07c100310007140780b0b154406400b1403100c2c40042906450f030041c40c80503130040c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 199239469 1250 199238219 199238233
    0xc021206090105070e09070c060b180103060207030e1c0825110301050703020f0306060c0a020d0b0603211b030913020705010b1804080a03020f03010e1501030c0e0111 73
    0x44000d15003003041e610395145a40d28403c0000e0301d0381c01130001c00800000c40e40300aa40c01d004070010008941d900c0c1c00381629a50f05851807155079403001d8814082c9218100900c55a901d0a155000390081541039000c140398400c610300502e0030081d42c0150700c0400501d02c07240d80c030030f03100c000407608140a4240e41c01100264000d54081d0791000000c41d034812015a030034211950305040c01e650000d441d9000b49030061051070310701680341081e00c0e4042e0080d03034150749604001007400d00c0c01c166004043e42107280b42d0f0514082c0300d904000c051060805070300f103480b034004180b042242c85000c080c0f65a098a000d000c24120310394103450000150840508603410106c00f00001402e04010308d21407501590300081460030000300b0700800b070300305000700c0c0c032152240b42c4654080b1081d000140002c1000c0e00004290081c00d00039415a040203070b40031070850701d0707686600511600b044241e485411410f0074404103c02907109009070f00641d4126520560ba04820800564030303d02031098400c40340c010b1030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 199240719 1250 199239469 199239499
    0x10315200f04030209010308070c14100c06140c0c01060506090906090402042403060605090603030a05160f0804142d0114070b010e0702010c020703021318120e010513060c02 76
    0x805d91a0186004101c1e465070f8a90f01d14106400780754544c04505082040d0310001010b90b90019a9020a0310a06002e108035140e450150010800d42c3c140c00b0721031401005020842d40018003900801030070000070018141c40b18204034a074000c40c00b195074842c520030000ba8584c02c01d6201d06800602c0508045a119115480840b030400315074500403040244070800c0040c02007030300030100142000c0c0d904000318206500441d031039205141800060110002d011101c4d58a10203000401940100d82d68611402e98504003d00e58014455060741030109144202249045100108001c0c0741c5413007106c1c0c9030160304e01c000660700460141418030080280d041820400040140340580c03041800340b03155810840c4040c031682002c4e06180c02c580c03401000e00b410755000514042944d0301100d15a42160002e0402c00140140485855146410000a50411180507082680d40100d43c44111800441c60011aa01d00a160001c4d0150b08441010002c1c5401000303502030749400a414111000c1c000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 199241969 1250 199240719 199240729
    0x1031d010905032104020a0b0a050c0307060f230a0509030702130212221506090903020c0102010c14070b06060c030c1606052a011d06010315200f040302 67
    0x20760300680d015080060508148484140d84041d03840c038200081c142403c00b038000c610848160300a200081b903000a5070082c280c010750035901c5140074001141e1b516003203850080d004d40000c4000b4900581400040c44181030dc81c4ca0042c0c3e80036409075060f200fa45d94111103406880c1c0604161000c0c0010489132016880300d13900302003c4507514501590740c0303060030030620b051b980040012a64032403200d5002c4510f00707141c0903190b041c1c2e04105004130707403642c2c029050005c0c89640d011401c2079290003070311420150082064a1100006d80003040405541901074964880c10841d00d20005810003014000554804650b0b4100e10094003407802d100c105034400e031941d84410100030b8a6800030f20300311800d240300e00115024145928096007084500060701e081000202c0741485100850426090000800d610041d0911104112242c50071074203500c45403281020300003610385030040c40400c812080c65028070f01210901c00203003e610031352602c04140d103400801d13035000049001c0100001507625 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 199243219 1250 199241969 199241981
    0x601021915060608090f01110706020310120308100b040807030807050a0b040506040606080a020603060f01020c03420c07031e0801140301090203060114190602030403050709020408060601031d01 85
    0x142e4503010b809080c911701252030300c21501100c841c16814143c112140c650807205940c0c5d170507032207500580c40741c4420003940407102c2603412808800301405200f10501d903022403454002c0e80124103401d042c41c1c8401002ca007a00c2a40030310b1400754004802000010046002803480901613016600350401c0c45d07886811a00061708e050311280d1042c03003400705111a51007508001c0101e40c0c010501e10b03040d540400c185020042c100b500c42e014804486440364002d000c14101148000c0982d00d900c46410500c099110710070200301c118052011800d181400c80d0300001e0203290f0404441b0010381e030340b000121415402100101c00b00320b08400c17203071011401040b1041607480c81e034503041000d6042c5015110075000903529940300c7da050840110151b200422598152510703004030380d03504680080070848040801020607590000804006245030f80030001e4001d80c1c1c4104169001169100c1c10003040c0d000b0303402071500e00d8002c1c501091040d8040c0d0300042d50000c1080380b54003441c003035076943c0d030856035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 199244469 1250 199243219 199243229
    0x3006010807030c0905070e1c02030f1b011404031403070615090b0405240409080d0501050307060504180902010c050a030c0b0604020a1b02010e0307080d0201060e060102191506 77
    0x1005200038400c001c5003ca0309401352820310b40410180c80c04600080c004190f100c60b69000741e50401c0f2000c405004100501d041c20b8000c0c04640300c2180c003600d03041d0b40c2c031400350700c01c036405543d684240c44946c03080902411549079a03c4080c2040c1c00c40d00c82141d4074815001501da18130080140303e000403202e005401040e0314000314901c44a20f4000202c0c01c1e11038600303005114601d4502040f0040d444214050310310500140298590b41c0341001050040c030310510041c1145401191203c3d001c0c00755000181a2141641036401440d41c3d070700f055401c0d001314003496032a03120030721305000f5400300b41d40003c403264014034000002003842d88a8500341031044800303400207038000b00c2d0103052040104089030001d2041d80c0441c076025403c40b008091542c064002031200203214100002d6a100d074030b40031076046000302980ca15507030701c14840d561804c544a0510255081c030b0750010b08551200c040d544500d0041c0c02a050142a481c1356038030f14401450300b11500804e1441c2c4140d0584a4803401020388 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 199245719 1250 199244469 199244473
    0x10605090103060c030b04060b2b021204120305060916020a020907020c100936020a1205070e0a1e09020301080c01020f01180221060a0218010206040230060108 70
    0x50201c013001010b5a1001c05c1c11070141c1d0510008210300310f211f10031030344000480104d2240b41c075500a07080620608684001c1c00060012941c040700705071000c0514056403042d081c140c00448603140c154141c4504030f640c10f82c04000c000020b00d81c6040780100240b003411901c15a410030394654001210a403099681c0d070016444044648518182114800b4486109040c4110729034600380e01c080d04c656440272840e952540100d1440000804200c1c200030030b900a4800359102c0d0b11188004018a070b0500f201e1f108141080e004c1044140030780810050f001000e4038084101e4103103040300104004041c010710607800103241c0040d003600d691002e5406800f0043c040c00d0000b040c040020b103081410350f0715014a916243c403002407443d040488142c49a4195a4408140c0c481c01c450041c0f1880d680c5e809200703024240030403c644160368014410245406040c043c43e00b40c0100490f5100c0080300c0c001d402c0340c481c66040f102251002c4040b0344000500d1203012030500f210900d0341c140301d000e9100170803503 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 199246969 1250 199245719 199245731
    0x1a0712030902060a1e021222050d080702090711030906070305090a060201240f150c08030106080601090806040210030213091505041409072105010915050702010608060402090901060509010306 84
    0xa50b070b0840110340854454401040aa01020301104041c850780c9010b181e1640c14401119440549604100c010270004014440d900d02c6420844003a40c02500d049114200700c2e00028100c40c06010f04995814000300210300703105060090103002d46c061075094051150078085122180e4841100704040e01081d400401c100f200c501009442800036044540f030309240040610944c1c1c2c00b041c0c41c1e01140c4403003c080052020b0244146c80c7d84404507000780408200100224410780c0000c907250048400f80c0c1c600209641c2c8030a12500d900090341d00941c46198480d581c42c086100e42c01508a00324210030384040241e4038502182140c402c60f0003142c80e5900e00d5401c0106103800d2003001c0000c1c20715030300c40200e490240a03050700e40e0081d01420806044180c01c0c0304040c000a80498582c0d070380f0100030852800d49007800040c00d401081c14075066810000094031707892060203404200c800c0480102660f813275079400c1016003440101a40f90940d40c0d2840050700c2c3c0d9900344c40302c0c001d60250f0800612 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 199248219 1250 199246969 199246997
    0xf140412030b0d0206120408070b09070e10030305030604091401090605061207031e170301090515010207050109060c08070506071101150506031303020c030105090d02071a0712030902060a 82
    0x15078038580c0a5034841e51007083c0315000350711104121107602d074519890b0407013a9a14079000c007150281010191074120781e5401c000c01c11400040c4c0c0802d551752010000620b64405000d14405c441030300000380007407014404105030717092a400999006101d010b801c9200b00c01d852981d4212560380c0016602e5603110000d000705410302d03108100d11104070030301400c20242540c80b151038408220f4a000d035484200c11982c418030640440c80341e0b10010000510380e403035a598030940701502058030180b407000c849001018582d0300004104044880c107859a0b4803e42c40d000050703442d00c00044007503480d50400c0140c400054400d02c04d15201d91090303100c0050840a42c050b041c05c40740d4844000001209000c0180455a84c4c202030b079034442c3d04160440000b80300707443c00301e051001d0032840329010b60070107040c4101e100c4003192031a040441070f82110081561100020b5010454500025495030b040140101141d1041c003222801d140ea801c01140b01c034015808668035500440103a00040c203081c1031050 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 199249469 1250 199248219 199248221
    0x12031b09220605180402032e02040f0e07021b060c16060207030c120203070302060a020109060e06060420030105060903030c0604080d0608030c1c0309021804050c0108190f14041203 79
    0x2240300b010508050313240c41c2590100e030703407811018070a1800c0302201c00d0301505404a0300003042e810354924415134803039944107040c022003110f5014099042d9501030000d12080e100060780c44815140221807103010b030208041c022235a1014102140900600d04004020510030640c0381c014903059000b03040b8545103003004c64405003a90813045408a903c800031015a50006480040eaa0122071a0303a0380c0034800d41c01d0340100b540d280001e2020f07040604810744a0b5010a5840c41a00c058805000081106034062540c0711003139030030301d42c101061005101e54145440900407802d8080d049038641210b003e046440c10380108c030102d8414400041c81c0b5807401d15806100002c210543c000c500305008003604507200e003451002c403d5261101910a44042d00c1794001c54102a00a400d24401000413441c0b0590203600312030507102485140f00860f03c9501c07440c01a4802c1c00301e450420381e41c2c0e05040b080700191400c0d201c030002c419141c0440c00c00d4065807103170700ba01881c82010300c10024010090050 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 199250719 1250 199249469 199249489
    0x1030c06020d1809020f070506040b4201020f10050403090b0301030f060506030c0a03060906060e0f0f07020c04021602090c040b0d0504060912020f12031b09220605 72
    0x1081400c0183c01450800f0302d08441c1903d142403005602d071051129050020f0040d24806402c40c8548000e000c01c1c401000103035070180b03451017140d5403030341d5005005071002c4080c00000d0802980b0703801c602400807042041d6405281051040c0d580c400100d082d5030f0301d40b07201d2640500380140d81c0c5050108040c6c011070004001c0c18200185070540d85103403160355030406080c0d806400785840344000364139598140035011152100400e0400c03500d4481c01c2c031100404031000e0443e5128038080c008100900d000d4111031080884280030051591740e810441034241c805000e80d015840b0307a102c1d803c016602d500240c5400742d40800701a401d040715004010860901038010150b0130001c110174402150290210342d00214041d001040a8580b4036000c00140a0000003801401c204160802c07050f0b80132903640d262909402c00c4601d004e00d103030340100951000f075070b4010031740150030b00c0c01401c014408060071415400602e01c4c41032103440780d400c246602100a02c0700b24955949400e1102d458000046 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 199251969 1250 199250719 199250743
    0x60f0f010905072a05070803091243060509091b0313030504050901031a0a110a0c14070603051006050f040e060d060e03040302040507020c03100c0207080601030c0602 73
    0x14425070428190107003404041880c0f40c0451800c0d807404e04008801c0700100b000c40c070f90140c12103910340d43d41c1c2c103080d80705e411028041d40700b06460070508500141c0042c41795240078850380c5d03810440074180010200c4074403580c050f00d4070b400b8007007085103c005501070120050506444403a41c40c0c0b0b44100300084614014180d50708202902c0300229410b1151054075800b82448003c820900b41703d040560303140c011944502d601801d1800040f041001c1c070800610202d800141c401c505407138050054042c0c85800000d1000c1d00e0003800b0ba401f00074800d410707540b142c42c011040681143d8000052a0800049401c8040482e44407400e0001240440c2c4428000b084145071050400c00c10801503074242c4140d2044540c00140040440c4403980d030107000040e415442034040103041b400c0071245403203800520060384114603000000715401e002081d4250722080040240244a5088040f0030041010003004130440c80345210120f0380140800006002c0c601444e481100c481c58540028075011402c00c038 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 199253219 1250 199251969 199251971
    0x903060c180308090102031b030903190809040203130b0412080702070302060405040c0201060b0301030f050706091404091e060b03280308060f10051c23040212060f0f0109 75
    0x840d4204503030150003001500e5000050300c0e070f141001380040f442c5003d81c1d0702200a0001c003080055210000100074001040d0650603650326118903001c0d90502d11800d107008c0d001510400c40d91401e841c2580c02590322006200e241c030040642c2ea240c6500414080301c1c00c03615400c807100f9028009030000815075020072584018440700d8110b60101d01c2d54007807880f6050140707803031f0ba0808001d24000c0d040b100c05020404074441d142d6130b690070041780c11442c02d202a100d501403034101103039242c45a01c9901c00c4e0340411001840d1000c1e80d0050000802403684182d80c400418004664000d0f02c0e9860240828001c12000c2a00c4050000f050b081942c460b42c18401d0701615010211420040d20380c070000d854250030100100d6480c81c0c0400c401d0030740410030a602c807030400d03040300f55540c10502070007407406010074036900c068003008088219100043c903610044035841c4071025085007120310f980d1140c4017800e094549404103800030301e00302041e0380c480b04000b0008100007096184004040c010a48418 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 199254469 1250 199253219 199253237
    0x6041b020606120c0d02041a04240b0901050412060905160906050607240e030d060611010501050a12030203120405030405120c0906010311070b09030d06050a0b03150a03120903060c 79
    0x100260854022010081c002c7da2180030300401510a800c003061070070800b40c82400030001d0005800c00d08074030607080034001c1038101400300d140944001030b030720380000c10b0310390030300d4982824610783c8100050f22003142e0380b9440e00d2803900040c8060000d00c1c1078900701c0e80e0b030f603001c241000356617420ba40850300068086c000074400d54000ca0447c05000104400072003900d801040038031400c030082c10031201d00c101c00307101c001001a06250594041c030115940d030350350503603031001882c00306090716400c0c41560b5000b9403400040c0102030740c583c548101e0b40c0c440e00445c0d1402566680d08a2500401c89040d11a904045010000c0d401c250a4041c50043c03690041c0440c0310720b410000e540c581000d8011410107035030b4000841c882e90240700301e461b407541201c200d030702038542051483c0e83c07076000c41e25400d99181010400501d03070818400010541e0b052214060460750b07007080e07940315103122500c0241d00040b00180000441e200c1204201490034580d180280b072801e50900c0401e485c002c020308401c020b5840 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 199255719 1250 199254469 199254493
    0x1060906020303040f0209180613030305010602010b010804080f0c1b0a120c0b1e07110102010c0e2d0a030804060906050f0307140f040e01030b10030302100506041b02060612 76
    0x101405c80c22a0b0304903070341e51168850132248038040078030841405c1d4038880c04040c0103410a09205030034025101340e600b84113507a00e0b079a00701e003610140d00c070b00350201d05404082000213990340c020340031070a1032290180c02d14469014007807130b0010100c03860100b102c18512080050400300c07400b9019003190090f40c0c000390800d0391000400586485110703184600070031a900c03112510300170502cac4440344a41c255203841407818409001c0d03c2448003030b0b005d5843c1c40c9200c200640204a030900418001b031009045010081418004244414202c18015480c00c03101d00d040e0b030341d0b06401e0055802421070503101c90030450301904410154003d007050000a0103031540900314403081380d6002001d45800c40d0702111400340b0043c140120200b2000c0c4210100703003c80d94094003084541201e00861030b04030f00d9110483c1a020a074268000540140c003c0c55864402c0d11640c2c014541005019000003660703010202100c030200701901202c2c005070080424014580b82c1003207a03502c641d91401c050880c50b0600 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 199256969 1250 199255719 199255733
    0x30103150b01050a121815050703061202060c16031a060607020d060b0d02090901090507090213060f0210090b060f1f031e020a11060a0204050a2114060106090602030304 74
    0x1a0b00701302d0400c20b40c40400900b500c010782000f2400415007016031b00a40e01031400800d50008002c00d805900e01c0c01c2d002411700c510038054001110412407120302c40703080307603001d12109510030214401d03244103103c005142d280240e1043c80c0214016407105a15030102a200510500c1c0039002600c074040510140c0007594070300000e0001640d015000044442904003c5030440030600790107903000c9404810001d0001064004940300b41c840d80a41324602e4032151100c1c1207002c0c426107948080d01100050000324040c240c1d0340300c803206500442d0300003407136402e036801900d000c0d00b01114180504414002e1a041040b1048401d44003228201c404600e031000c051501161900c40008064862580780d400d90b86085031503411040d9400f05555030010b03060082c10b900f00d0794250383d01074070400e0001000030300c440c1300340c42c02d407000142090142440c010404459400001307c840c041081c64450b070001a08103081481e600c0c1003100608411762415101030310030b601c40d6100c0400d54004008010010319a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 199258219 1250 199256969 199256977
    0xa050601020628050c0406030e030f180102121602040c08090a0303021e070606030203190503030103031d2805041a04051017070e0105120d0807021908030103150b0105 73
    0x25040c400c003443c0c100d125000703c42d4209140009141c914080602000c43c925070010029121292018080315940610542d0b60340300704404183c20500500824004540105003c95801c034140304450289000100b401c035954080f51030900ca0b400d10659620443c117080c01a41d9100b544c40c10902101c0c6880303c0065141d04802c03900804240d030000341008803445600300441d13014142e184540d00c40040340750040081c129804143d20078030504444008145142503078442e00b42d0700c43c0c09541543d2030360f41c0c10380b944500b44081a8810090302c2c0c107103010703444040c00c0041110301300551080d10091030f51503c110407010b07003040c1e004030b0404250003407044030a4400e03044c1e00401c1c2e800064954a640f5402d11641090308091600d2480441d03141035444001861020740c0c980c00140380c0301ea60b0300c80070810318141d00904078020350061072a41c01b030580590f604036400311290050368604002820260303001c08543ca01185c000742c01000510501504c151a2052009003c0f401c02884544c030001900c0341c01 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 199259469 1250 199258219 199258231
    0x219030c020726100e120a02010b040e0303040c06020c280305030c03030711010903140304030905030105011206050603030724020c0613060b0108041e1109070c0b0a0506010206 77
    0x600c540008a42500c20020340006228901e03000280c12a140300032118810001c0f07039941c29201394130080c2c00a0382d043c800e100200c1401c00040150072104030281c0ba8a4002c1c00c07541c0295581c1b100c0c030002540310703030042d1041c40841030051561b0303242034a003542040c502500241d003150b0094811810544030302d001c1605210190f151121728500034400326190003001d403c010601e00012951660003e0000701942c0100e001c3d448200110314500100c03070882c1c0021001030700003180c12446462643c00315000b141c101e0f01a160240c03180f9141c8000c07900391a800e90103c110000d51005201c01e1003c0b40c070a5a800807022005586885e40036250b100d031140c90891a02034018041c1c0d44c8201545496049440800106056580c0762901040210b20b8611941d01526201e09100351154250320441c4114031540e440520714081e284a9031005280700345504044426000309804000b15950b042405482014595541c0481c1c119038500607040c01005411142050308000a01000d0781c4c0204116030300003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 199260719 1250 199259469 199259471
    0x20a0b010909060b1503010f1d070503090f01060b0c07050103060e180a140703030f170703051b03010305100e070b07080f04090e06010509010f0609030f020103020408030a03021c021903 81
    0x40260800b10001c0910303104e91a8031012192550213800038000103135040318441418259180c0c0d035800b0701c04404200c0550441507452050004540c18011f201454104414000711a4420f0310000c10608450042d003090305014008900351800c01c80402c41200580340a20b010f108d15450491038130b01001c0040d2180c00500c413a84082d1a00203400c02406401d560050b80b103694002d4509580c135114026030206400182c03501540404090040c400e03540d5104001c0c0c924141543d800008034001d11002d003100c408200b411410407564060b00c8041d501860040002d81001000001000d08807000100842030a030031001041201005503410b0360303000c40e008108a0b03641c1d5840400d0000ca44582d0700001c100a140c051070b590f50480000d02c1c17a060f50003e803003541181e42c031800c0100210700c0e03510030540040c06d001c4007031001800180c1d44034012441810054205512604841e01b5908009010310000c0d07400f298071054908401030303181f8014900d83d0214544102414211100854a220075081c9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 199261969 1250 199260719 199260731
    0x10b0c19020103091703041203140708090705190e010914010b0711061b1006051c02030a0c120606060507030507020904020a0503010f090203010b0f01051209070f030f060c020a0b0109 80
    0x1da406600014100343d4054049031020890607058045904196800e440414800c580c221000b0300a1140c050280c07402c1d0013500340d5540c0c0c0704003200c0c106001480783c5030760300031002c1c0007c10b900c2d482001c0d551000726101d9111802d0600038096201c4c003050340801c1981e410006400500360030302e086581074550310700d14550707030740c4c05810100328188000c020680c0109001803440d44d40c4500c10101c18101d0441e005a07604111401c030b100f0190303440f030f001da96440702007502010b554819035060041400d02c06010f480d8070b2080350b03c4022a04a240c0d006099078104104101c04126892140e0405003080303081040c100803072528000e005001d03240b0028002c0d0555800308096544403400c0364000d040080003448803003000c04400006d0f02d1501401ca01030342c02d1400030a5980f900b030650b000501d90695803942410010402d065400300080c20044141c050030b0345c0440c52144403c030040145008421802c10f0043c1860100101e861060528003150001da070a10002603a000707049044407919500401d003 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 199263219 1250 199261969 199261973
    0x20312090c0109261b090f04080901030207140105010305010c02120a020d0507110a03080d0b04090506060d0206040e01080607120b09010b0f130e0114010908030a03050a0b03160e010b0c19 82
    0x500311613180c1120710f920600c8014600b0790005041425181c10a07a030388040340d1a07210309654400f1041e00d004001903010301c4881c205520070340c09044914001c800160500381061500c90843e8403e070400d84a80e5122048804007070740400031712000305004514103141240b040d0f0300035200d442d4010035108102e80081c1503030511088400306003442d1030042c800001a641d0340307040c254950101c01c500c0c40d400e041542e039220f24500ba205035031120fa04100984041c1d0384000401424541500303007240d0001c0240000300d6540302f650141e50207040d02e08020249807c103403201070603103552640012030481c00c0404a00c11a1500c2c14410b0444880d0303400d05494600c4841402194010940310300c0c1c103484500c100080e14070070381e03070024101e81003142c55130002120b003001140e41c0041b901510035568410072583c600d4034829802558440701049000550342421000030b4103046100a41503030890403c03109000054200800340d00622800300d0980c40c018400e6107507601e404c510011202d40c0d903003008040341 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 199264469 1250 199263219 199263269
    0xd030b060f13260606060313080a05040513230a020d0c0903060c02190b0c0412080306040b09090705040221040305190e0108010b03060310020a020312090c0109 70
    0x36038405030980680c4602800800c02c2c0080c54512036081559500484001488600c03400d12070b0f90b543d050050045980c8140c01e0045c1d40d80040c214401c0c206000013184003152040c0d002d01800c640d1076079030035680c910744070421840181505034200d404d4504000d8800c001e0b2204408041d030400d44228840a5440004400007802584c40d1000f981d402d002c1444965503014410f81c042e02c1c03103040b0802031510100001c0744c1d94034242040c50a2030141020b00c3c1c021a141c40c031010342c058801804180b40c103407950003092000110f55021180c000010007444514a01802040308000040da542150751078211061980c403401803141902666001840c90140035004080400c02801185030304e00e241040d1400608680c0711b00b80c810300c034141107000302ca5624480c1c0d1441003440307816540e801069013401050011a48054055035040c803440b9101d101001141c00a0700d08070415401031511002c06041580d918040100032002640048629140b40c0c1e8000100300191844941c1d40f008450302074000032 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 199265719 1250 199264469 199264477
    0x40f0203060a0b130905190c0b0d0c0e09160e010909051611060c030402011d04050109020405030c01050c030f03090a05100c030c02030a090b130f03150615020d030b06 73
    0x690540621010054010b0305030304140c11074038044c2c441c1107100c0d00100300a02200c3c0360f40001000b64104070300075201700201040b400c4080e4010103000e859665a07041d40c48065120f0300413040810344610a170000c0f16001210705414a1094509200346d00e04010181e804103c2100e1540a01a09a800361b800d6442030405001902601d2410401800c0c07095660b010038449951400000d2100c4907030100c2c510000c03551070700a5101c0c80760242142c945a005664034600314222030344514440c800121550386a001d0b00303000308480c1c03400595403400c1c101072600f04819981c0761030500804015000d00c203803000084410b01c04a0a8106481c0d4844144003400c2000c2c00307401510521036291100d214800340d502402c018012502c1c100100810450166207d0140b940448003055507800d00700000340347d0b000200704c0b2103040d5004841403911102800d45c00440d80d003068a0b48408441d40104203c031034071501001d030181119201600513280700c000e40d01e0340d4000c0c4000802d515000861283c0d126202a2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 199266969 1250 199265719 199265723
    0x70c03090608072c09130b040308071202030a151d0604090f050703050c0a0609050f01080a0f06080102070c0803040e01120602070f0501151403030d0515060406020631030305040f 78
    0x3090081c1d8901950485085016540310712038807954002c18180c5044a1b0301c3d144842d80003103d91481e591326181601c400b40014803030405e000c00d24214843c0d617006403006601c40d00d04140e00092414240300c5c180e0110342a03400000000100b502d080d42c030024011070040c2d100c4401c44000c10294240e2a100d81c035540c0c4194000e040f88603002010082040108070055041001d94210062079610784003207800d0102482030784c0d0010220040380c0da15500c900040ca622810952020030300300d14a804d01002c86400303034810040ca0f540450214204841c41106000034102100154201400c11445900b134950601c50341c070750b080c42504200100320302501a81e070000d800c00541d02140e029801c0a80c040c02107c01d889039403548618010904841140040c20040c1c8094001c5081654802201c401004c0150010461000521410816540d24070042000c2c04c40c690160580341444c501e040146c1180c00c8070310719002800790303250040c00c0741054200303034858140c580400c01c2c0c0c0700c500303182294050040e40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 199268219 1250 199266969 199267007
    0xc0518031002070b1f0b09040507180618080313050d03030e1501090509341203050c06070305070f0f180801230402060301090e1c020d08070c0309060807 67
    0x12100070310004c095600d1042007072081503101010344543c0d42c4c0705845103020302c0c0d0001d5400c0c0018091403c00368415540300049042142c4c8443e06074000303100520441d44040005a000b20091103500b1408401400401c442802117041c40350340602e00380c102459005e064011320920300c4031414075110f900b00100e003006141c1500d40d0341c1d9120040040c0c00750240910820581001c0116007460300011b01c24420106010a403400000444801c82035001030501007407041c1030107039003c105941564900b05403d4400d0f1651076640316800032117404e294005100380245403800c0e04000c80076801c0000c120358080c082c5071103102e0601c507680c143c5050380020049030b89003c88800105441c50158007441d0700c04d6a0705680020585010025640f500080728000c1d0081001c1c801000300c0d550a4008070a110341260942d0000781400d86100c944256000c00d01006a000b05040c108664000410ba90880441d14181c18005040c2d00d01500013a0244114010003910500047c2040d01c00e181c02c820454117401 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 199269469 1250 199268219 199268227
    0x10f06050f04030b0f0403111b060c1e0109020405091219030f0f0f050a0b0d020909010e1b040c0908031b0c060f0409110306030a06020306060714010e070503010c0518031002 76
    0x1c2d00b9060a44212000c5008c2619050042031706a4001500851441080e01558905229130706000c4642c1109183c10994410309080c0d8a021041c0e03e03000490b40c0b074090000640c9000381c01008151800600170b01c03800d4020140210940080d20103c92a2210300c0044d0103400b011881c0880007010200027007624140782040401c0e4403090b503081280d0300080c2c0c0000f4405a04c406c030101c13003250b440c030060342e030320511000c202340050600031140c5611029800c000500b03250600800b074100411000500355013801c1c0790807000280351034491000c0b40c1105241041e41c080c181210179503030703119400d0340c50610820294a108440b00801020900b0f4802030050b0782c680d04c0241c001e5400742c000d0f00848100b47d01300080c803068507011a054038400c40d40100180000317030590310340c50025031004d0000c94111104021003030115008003841507040783e0b59000012410210f0380324038100015a00018407a9041412507244a0b030f02205882540b6894403040036504911400607260010303403150044018004a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 199270719 1250 199269469 199269481
    0x606091a0417030903060115121e050c03090d0903020603040b10080304080a0c050f060703080c09041a03010c0c02010509010f0e0d03020d08010f06020307060203040f0c0305060105010314010f06050f04030b 90
    0x40f001d00140c4c4c00907030403128142d0321035a10344413040300030403214001554103100440c02307040380d0044220596980350f0600400c18410300c20382500c03001c4a10162100f0000144903000804010000c105140bd1030030101460640d4005981e9202c082c0000d0a00324a10780443e40c0384010042100040045400710780d40c0d15552500d1a489030f0703503d036003510b200341d51a80c0003d07107040c543d08100000d039000b0300403460601ca55400750740e4540b01400f002e5000c002803000bc1d440751141d1080b414032911560481100350721b50020142901c4851000c0000c00900028070310041c1d800100340c030170844003401c01d050f802041c42000c5620780701d081461580150341c8104c4400f0b054020440301e050a04d41c0c0d036228450380c2c851841b0740d00001288508801a84200320440101360b050340590f400503c941d40c88001d4440039251030050f140310b07820580b9142c0001c0d004202c5503030188114414100040ca00706910f40c9044040c90f041b000c503104400500400240003045641000b003101c000d10342c4031840310307503504040f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 199271969 1250 199270719 199270723
    0xf0f05010c0f2916181a04080307030905040b0102031e0f0d1a100804030206010b090f120c01121107060e28020a06082509050a080606090a0606091a0417 67
    0x81d41c0b44000013040e41c07900040036200b0303003c80b60040759003088480c2d403a24000d00504402d14001c00311a0050050002069101c1c0c00e10040c410103020355100e82034503040c1400c1008888180d4140390555000b0000c0c01441100300601c01c01c8518a2206507458440c960410742840c070442e941440c80515040d80d4040891080000f903d00d0001070782c1c80c4a001c4492241610f400c82d050360017902580c404801008444010001003c1e0010007078074800d5078180d5240400c0c40810780e41071600158100c00005005035034060701d00c0c464a03c05860900009491214050040c881c840018201e0380d1038215111801808020420700d44400703004140303c690303100305007200000b80c0b1070040b845040740c8030000403182d10929000380031355030070304040301741844441c1044052481c01a420090101075080042c481d51075040380c500410140c2c000e00141d241010801c03c0e03407a002400701301c1c614500354050101c9903000d284001a00e078801d451416600b081d4800c44001d005035030050b07a03420032901801035a0000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 199273219 1250 199271969 199271971
    0x1080a1e0f060f061403160e0d0807060b010201051b090d021c0b0601051c09020f100201020409200313030509151909051c03030603080f040f0f05010c0f29 68
    0x2070f40007401c140301d807207400880e01c5c40c18103040c2614042c000d202040f01d156500128443c1d07042d0a080400220b00550040345800c150000700395034003203000c034052042c043c241c0180c41d40440300340b00030841c919200482c1e15200c0c20f542d2398861400b10105510580d5101d84015000c0c040d0000c1c0102d140002400d100d07180c01d4090002142c4061203940170442a50040080e03400c200011100041400b00c1841a00300038145458140da01070410141c40304240c548134041c015018240e400541d07100d0410900b1310a94803400189031f140c400c003a032088040c2841000741c0c0e030440803402040c0c030040d009007008c844500400803460b0707012210400741003000c0b80c0c0d10024503034041000e0b2300703001e030080703006080d40d01102c6441025002401c20000344c0c031803070004540c1451288282400920300e6142d448104068011890303002070036800150900080310460030a000510404201d5082c49042c20002005807000003401880a000a4001810003140d2042c40075a40792484101c0c0800c03201943c1060100f038 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 199274469 1250 199273219 199273229
    0x813210e300102040e060402030405030712050405120a0c140d0c06030c08010909020a030201080903070605090a0b0c030c04060c1106030a050105040e07030c0312021c0507060f0b01080a1e0f06 84
    0x1c00194100703140018020b5404450300c189040e205559800180000395000600c2281c241c0010000700300092442d0100366030300081070307583c662668141030511809131064401050f00ea0301000790140003901c801a400f0540301c0300e0a0110502d442d403004240544d10038500241540382c0c108c03010034640d9166010001040e21030f9100340103a6a82c0c030340c9008540000c40301070340000e50070070103001650180840395008100c0c1c07821070307181085580726181250001c3c1e0b00c1c007940d0b401454085007480410424150040310307210300a49541070442c103040d81d51280b4803c64041c00542400c0781e00740940c082407103003614005070032130343e4a2401d550f46200802e401d014840c0326518159180c07200c01300025240f420340354070004040301c1c2810341e00ca0744110790014011008600c210302061030591600c0c41030140035182900c499031100c401c0d00d80306040d00c01c440360802d40c2c03c1c60480b1154140e81c0c4020865048400c03c1c0b8002003440440c2000350b407060333120403504041030502c12240440741c09903110400302c1d5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 199275719 1250 199274469 199274539
    0x3030c03111903110f04030b090c0301050702070e07050d110a02011a1e040b0303040b040806070c1a041b06020d030612020f0915040603120813210e 65
    0x8032070140112020301030b081d110140268140c07519030340c2c0750084e80650f034540d4a6000060034044c2c03580c0c0e41036881d4000d8100b120111104000e107c03a01307800700801c2d004103900710300070b114610780104000d58400e0b051048090303881c803480220720b12038060030071a2042d0f464100d0a00c0300301485a54523040f07503c0b8401c110010740c6050410000e8049035070010100d000014004050000b40c41031401450b1590980c26a0080e6154500300203594200001d0004280d00c0c00c5030354442d07140c600500d0400e400101088188921001c0841c0003a52a6040000300e040541d22280b140e204c9042a1891000403181c020b02c5202c441c80c0072801a40008030580045200c2e41c080c411144c0b1114803480956035982c000b504401c000503444000e1034203401c02c0e54400622107110150800711400141a61800e40c0181c0f44c0100004500392042d605c8803103a5800b0041145541c0707840745590b5a0317886140050340d07120349021181040300d034591143e401182c50400092107400341000c035071403610303d114540e19000421 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 199276969 1250 199275719 199275731
    0x303070e030d0903150c030209040f05041e050d0c03050702032d120f03070c0501020409020403031205060310020a02010e15010e16020c24070b09061b1602030f0a03030c03 75
    0xb00e100b21461400c0d00d5000c070402c00c0241c0410001c801800c2c4000003042851340a00031301c8900d4032a0b07c1174902e1200594030200f002c1c102400c241c6801003100f0241200c1c42c10107500400858000a1201c604000754075000c1c000f40990b05045449024042c4000d40c14000c00f10407220040070012502000c8106a01a6030810309040c4001c0d030b00d007440341c540c2c003800d8002d202c00407100c0d24030005554080442d09000d07030030701100d07940d480c2240d2064100d503005030350114042c024161b00c8110302403075402c00b0900b00650704000700000d80e0b4034a0004659842a00055080074042c400e400021701010410103e401c0d01c000d0f4000404480c500b4000c82c4445110040000e00c240d11002901c0ca054125401420f07002445006100700001d400070b0b00c417a40c2001365a42c4a040b610342c401071540501403180b80700d0318182880c450781030440141203231150800e00680b0184a120b0b001c215010719400050216800400d840401e041142c80c0300900707080c0c0528914501811740540102c402a21255010058 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 199278219 1250 199276969 199276993
    0xb0d0c08010909030207140303040e042001030e060402240c06010314150f13150b01022b0c051005011e05041103060603040615060e030106080312061e030303070e03 72
    0x85403003d940150040c0d215400c204408800740e0409202039402505480c07034151505011107401d607055404882802d4400c104640050948554455000e803d00c3c0904c018034680400036079a04018001030301c0748601c1c850110a5060910000b40c01820315102e568980001d40a100e807200c03800d2000f540d004004008624500c0e40c0440d280d103051305801044030b195224503156086618000b1b00d903030300510a088149010410003251030204404104c804a00301c042580024184407a6442a4502c0301c01030707c4480c4034030f10f4004036114140c00c0d403810894140312803c20620f8040c1182c0f034801064500310003c41d10502c2c44604003003070031303080300c20080459448050204079901d007103603000755840520202e905494903000941e08039000350404980f0080a9100803151126a0700050203e04168800b0126003003c0c002c00c00140140c1d40994144040d1b4030254000c440010202441a40600a003110b5000e042400038008000a0203c0340c4a10300940007408000e82c1c82c10840c070a1069156940c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 199279469 1250 199278219 199278221
    0x6090506030a0b15060304060603050c0307150509010302041508040b0c030906010b0315150c10020309030406030e15010909020a2301110f0a0b0711030703090608100b0d0c080109 78
    0x4040c1002400522555082d0385503490020005000c0c01e40048900c0445042690b03444090350065001350300001d0031610b149012131400c0042100d00f402900090810021940504480600345059007030940c3d40d40c0385280101d0080c4102c0e0096400220620700c1800c4150303021009921461080b080c0502030344131075402c0d503e10300085031403491035804070005001d01d0200c0ca015607006101142e980d0465040c810000b0080c0041902081003d9804541040880003c200b05203140600308011886c5040803405161a1300c110701944043c541c40b07030311052029808110804c0202c02039102c078861541c54503011000b802010b02c081e0311170030b14030b03d011401d02c0404c2200703278402101032011000d500c0128010360702d0100203900c02e0000c3c058200c0d00c441c0690140400f80102c0c0c401e46105640f03103170807000a840c0c13040c02c5440d01a90b502c00d01074030740000d400c00020742c20340340b0740d0529008030b0b50390f68414008410207411a008803040814180c0f4035602d103400c261030800c6140c0b2060344686e243c0c1c5c6018 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 199280575 1106 199279469 199279471
    0xf0c0c03020c01090303020606190e07030903021002040509070804050c04180515060105030712060b0408030901090b1e0c0708031306020c0a0e0109050a240504060905 73
    0x400d541840b0000d0308030b0003424010440750950300e000b9510080200124040e603801d19180640b01541c1c0d07261802441030030300380d540d1032801401c020013030103542e002140948100d044d6515040120300030384003698005408858035a03510301046171300c00c074050001d0703d0a000f582d180c01c4103030310b440c06804200303482d0840001c82e400d42440c0451401c198004580b03125600181400b6a6a1f40300046981000042c82e20041c80d540900c13a00d001860143d21051804900040004114401001501000f0000d894129010742d03201d48000daa40301e01e000280200700031000d190b214100020250404101100450348003517100c175030360380c07030b551100c40680e524142a01040000b0343c3d04209060010318103071f82040c2600d01d40004400300703403418011108500d850f41c00090f0b80500a42c02a00c4800c118503803103d0030000d22101c400904594001d00d80a542420300209801156010b05 = true := by decide +kernel

theorem cover : BRFrame.Cov 199100719 199280575 := by
  have h0 := BRFrame.cov_init 199100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 199100719 ≤ n) (h2 : n < 199280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
