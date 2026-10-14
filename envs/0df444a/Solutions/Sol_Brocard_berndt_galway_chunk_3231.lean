-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3231
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:03:13.399814+00:00
-- url     : https://prove2.me/submissions/84ce4f94-5b28-4def-b06b-725a5c6bd74e

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 580935251 ≤ n < 581115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 580936501 1250 580935251 580935253
    0xa061d040905190b06060a172205071404060b0a03270c1703030c16020d12030f0f0209011710090c05070317060f0409020a030b1f0e270f 60
    0x61240f105191040c0500c545001d0004012aa07540e042808080d00c64416010000756018081c404218008000310b6005004500044010751208101d07101c4108210000d86081d0011a0108441c18400300101601c0b08251003c0c0425840d0800c03030440d50140d0110039040c907458400c4101e101c20701c0c1200c80c041d0601006800c84841240c2002ca4260156006e00c0581c0c0c03040810b00030344100008140c2e4498540a4212894100b106007140148826418126080866680340c0c2c00090001c65040300c1c20561503600141c8008400b01420684404106820b17450388108020b408a0364008010790070b0b4820140c88d2001600c07079202c84a03a0103060361019020b1440c10103c500b24640c000e00429020b40a603a0711411840da42c5a0601510b60544110340d001b146c0f6190300c2014205504580302075030008020f04092035480d03c03401240d4030115400301c081051f460620061001302100030001d01041003400d14507191081c60800c07025003100c5140312040903244031b0221240708000030f5070001c140d04 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 580937751 1250 580936501 580936513
    0x6030a060e010905040503161e030e10030618110702040507030b2e0c030203271c0b061504080d0503040c090b0d080c120403050a02030c0a061d040905 66
    0x5942480140554000d00c07a03a003041500025080c1c00c113000d07460213650048051f5180c43c06511405d1751070103d24004660882400545481443d0444040d000c00c0f4042e45440741881113400401613440082c800e51000c0c103180c42c44c180900c0000003451036005054803000982011100c200001b1030103071010007544a410141008085136040c1c11400740b6100c00c4d541c6a400d0319070f0000c905800d0b011001c52000e4501139007218501a80b083c0c2d80511003900a0055918000c4600c2c2e0090305442e1002c0404900002010364070349604184412216190341c0b42c0d1210000240d40c0d0b81c8040b01da01c0036000d1031098800162007185401c2c0c00c01214000d0040108841c0088109a40030f852600704507400c0c0c8503400000300000d481c8180340105481c0c0d05000b00101c1d881c001030345d60100c903034103c1182d509452217040c1c0402c00e51010200200041c5001d0401410300840030b104042c907000004400a00509030303914100180c81e002019080c02000702038400c41020402030225008042c94100501207100307003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 580939001 1250 580937751 580937761
    0xf0706020f13120503070b13050f061009020403110d020a0b0d05060a12080720030a11031b010915050f0f09030706020706051614151911071b050603 65
    0x219000740582d2038040e01e00d18095a450300301e070900d000b1501c8060000e8204001031000241d8050346e05601c808580c6844040e11201d480e614a8100310301c408021036400300044c0440080e40384000001015540c40c00e510b09800d56445904408214444c5405140e422415008655505142002900034000e14a484025841952000d80010340f10305001d40d010307040208104c0c40102c009030100780c021012515001c181e5690700101a17203d4540c5c40c8206011019505569081c403c9810681c014803030700c0000c0920381d0415042c01d0745103c1034010380d09058940c06407641c01103941030880305a24400d00c0f09141c110401c1c1c49601c41c910b00101600800500c1002c40d11060025000500c02a400ca0300000d4440300240d90300c2c0091300600010410501c00309203284444a04100a00d101d0b9146400309242c3e50621840e0014203803249a240e00010b041007038040642c0107174010b42c0303420001448008800544500148a142d00103003c0300e5801080680c0c4c0c40c02c60701ea5000501026000d25564501 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 580940251 1250 580939001 580939027
    0x519120b01061d09040b0711030a0309050118030906050310080102040e2d01141f03091a010509070503091606120c05131401090b0a0e090f130303020f070602 69
    0x109025140120304251a0046200710b40d01d07030483c00407400350084849444e035031a0345020800080041d81080a00c4030b441080200a0003e0203c80e1640e84010074141690701d04242558090200300d40b5035200e140c24100401e500003558401c80b041c9003019650b0340ca03604141883e4002e1904408200e6000207800601310307444001c6144100140a41600c1030032072400c100300342003691a2980b100840080c014040c40c1c0c55100000612180144946d03c07400701580c18184070b01440c1c4200c404665194414428000c505058003003000b85001c00c8840c40d810480082c04051001e0450801c20401000203000300a08020100e4a43c5621400403041c540d99040104900c0d032130120702040d103007081c20300078409010710240c2e012504054030700100780f03040407032010100e408011007a04211500600280741c0030300c48000c0c200440c03199540510800c1001c2405040113001c0c100141031f5850f0b0341049060f040003503c1500480d45484c0241e1754504804a08400b4040c400e0013400761440011070a5400700 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 580941501 1250 580940251 580940273
    0x9051515010f030903080105011b0506100303031808071e050a1202070902040b040512010204051309020405220f2301051819120918021c15051912 64
    0x409a0751840c0e050300103001181a10130400c401000305085500603c003070340c0624040840c00c01d4040407942d12203190b843d0286401b4054948400c0003046550900506900d0300903502554044041c00a4003002c0e55102065442015800741280d0100340041c01c41d403403800c81001d0080e800604841290126081880b030b2100d0303071042d4201520400400180d1562175000740c800701ca6200f0081c0381090710389401c1c0181c0d504501103030000381d5401c00c400304155940b0514259803e581c0b810015014942e4418841212000f9004030000304410350b0311884ca010344036401514540c04a4910300d809442d103010b9445150b040e1000200400346001c001614505601c01403040c9544a5000c09041c050b88d003164490794588040d0070303207200307000da03070341c0031400000000781903034013910f0b0691000e07a0307444007299031030783ca40184000b00d0740000700401415080403241220b401c03010010000f400c11110080444800e5200ea107000e604491000c0f0000442852100003c00070111074203208071042c500545005 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 580942751 1250 580941501 580941541
    0xf030103080a2007030305070203010f020f0304121d0d140d02010e060a0605030307080c0f030f12281d12030403090b090a330801060221070204090515 66
    0x980d42c107603d414694204084000112501014011190464404039800d0780003030801d903055034880c1c3c6542824610740c8018500c996a40d5421034590900c3e161084000440c06000d01c2002450300c07440000d078031002c01040040a040710f0403140c2c0c08203440c0121004080c4040e604980c092020310741591074064218802c0074650405561081c2d4403486110125905401000d426070300a10900d40013410641c020301c116171825048138604261012114650b5014210700d82400c070700400c0b84030101100c1003640380c000c0d91454441120441703000304008172400000210610b1074980c0c0c0700300411030f0260907043e1008034120544210254089480c80c4d00d500503076040740003c403002000510000d2490940701c69550081c1480c40340b40c43c000e40380d1044000c4545034103d003101e024441501491220040c848007019484100300c40d807400202134144400b0052000a800d441000c042c1d030283c055044982d00c0b03a040341c001401c0199810980e1410301c8151024a4240540051140080c11881408402 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 580944001 1250 580942751 580942757
    0x6090f0b030304080a03080702190302030a200a060f0f090b0103020a1d0708041707050d09080109150c0507020a080f0c01030b0915060d0914060601020d0210020a050f030103080a 78
    0x904000d014940e49100300d00c148480783e000182c90300d000900c070b4844960805051301c111950071a8500c3d0b041515005120304401507400059400f0503c2e41040c00f84410400c810820407066012900e0241c807071205c80401484d00780d4031901d50380f07035800315444194102d10448040144510602d0159202d240030f0005034812000110b001554004008001501c0c80e4816021492921f402005a40740343c00548120303001c204050983c01c030211442e002d0501640210020329040c01c0605000c0d142031081d0b001045030384d050981180100c1c40f140141040000b1a050014058135158403c8500d030091200083d8003900000000030100c02c001005569044d5078001e8071b004000001c019001ca80442c040d41d50407480c0c040000d00c00f80c54000f81540e6003c03010704024500310f8282088030480710000022036200c00c880c400d420341d181041140c00d40c001800e0004103241c000c8840040d5680480c11501020190000b62030103801d44240190740c003e02040c40100d840b540c5914216402c2d0300000124000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 580945251 1250 580944001 580944011
    0x2040609060b0706091115070201031505060406050706020d0c0207080105010e0105090a0519050702010207030201060e0f010b0f0c0d09151e111c03050711010e0c01080402030c030106090f 82
    0x34440d2038410300c01100c08481e0114507201103903554102130610540c0645801c0e0140c603080200340c440300303002108008220107241c0d503502c1610025088072021090034081e0b0081e42c20500141e21803a003200c080d00c0d1942009a100d917494a80034001e446044400c1032158180044182e8003a00005c29400795600c0400a2040d40c3c2c0302c042c8907401c64024401e160b4007080c4c900c0411006001e0358041c1d608008080a2248500001c0c81c0c0f400030340c0d905481100050b0340c0044d208050581c284105c0003d0003036160040e401d403c1105030400380c50300600075039030b500c900010101d4040582c441180c41510081099414103040c0d900060850900b52003140040703c418010760f00518410030fa07928002d00403c404510800107100c0403a00984400c51180c100d104051600d240c154249003800085249590003040c941760898008100701a10f4031070741c4450781042c401c1c88c2d125001181c4e078109000c080c47d00f014160703500c0c00042d1a0200381c0341304a401d5407a20384003241d8601c494004155460303901700c003445 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 580946501 1250 580945251 580945259
    0x6060507150c0c020402160f0b100e0906070522030b25021203130c1410022802130507020115050a0b0706021608030a09050c0a03120f03200403020406 66
    0x203903002c0803035400014566040307000040c60075a028025207010401c10222400d1305640b0702500a00b400f1003910801c071442c0820050a0020003c000680000031030704040e401c00c5020f140d90f45502420135400d018020031048444482045000c5030303040d00426137161580d481c10248900c2d20107641d030900310185030342003011810b46011f0a1400602d40c0e4010300c40480711369a528080e40018140c40491389419100f8804145100c044102521800e140740003c1c16034607007006140c030002c4903e20155007044401d40345880101203582424116503001d4141d6814520000c1c80c3c1e5403130341030589072445c03405050080b0b0a41c154807000c403e00c4405c0c01c1c0c825941c3c0710020403034140007601c070310300799213000304800000100307190050b00c0c01c01400156034400e01c400c1d507100038040e0012141d1080091b5502a040b00b80314082182c582401400ea42c0404000d09680b035100005100914079414000c55191242685200754000d1114001106d4130140001520000d100b50b5442440240e00c42d81c20050003103 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 580947751 1250 580946501 580946543
    0xa0c060e0406091416030b04020703091509120f0503190c020906091018020d06150e0409020906010e010c1b050108090616180510050319090c171006060507 68
    0x10802007031041a2044c43d0b64104d0342640006002120300f08150320b445040300c080d2200e0000d071081510a4840500c141c1c01e01d11070000b440c0c038200513241000010f00007040215043c030108003440f5000403203851621054200306256100307000a641903030701510080c0440550011580b007000e4403c031076480e80354440000b0415500b4003030b20b81c12144400109d040010791002d02d030900c14102c60b42d40142c1420651001c40084034019440842420304100c01014060740c03060480c51030000c2190100b050043d15004240c811200420081c140f00351507040355407582c098101e240081e03501c854111000380c28480b02600e020000d01c035490200c3d0500d0041080400b000c038406115a4100c04d9003070b041203031032801711001c04d070b0703142e1003120700c00c0708200032841d625280003680c035aa9182c1c440c0c69403070030805100162450102c075881441840d207026040040e081d800b05c48111520b01558448031004600918140442c1038040500d151030080e00050894002002d003040340e002d00300000001c95000804 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 580949001 1250 580947751 580947761
    0x4080d031a0a080606060d090b090303180f0316050a2f03010504050a0f1a10140d020112050c040b190f1b031419030608010e0d090b09030a0c060e040609 67
    0x41c0c5280d030000c000240342406c0100285c614552005000b06400b0815158440c103040c1c00e0711280e103150000020080309032800c006961202a01000504c40f1001400410b070300c0c0c0c002c1d802009002c1c42c680480405110701004010034440e0410324002080d042c1c01e1040d00106900802100e01e803044e001c0303489181c9010311a0740d01c1150080050221510a40c3c0c035104407180c076a1046a8282c210403469070000c29262515101d6840c90720030300702c141d0030300007900300a520140d0b05522a0b000c07201c8120043c2d901c00c1c20f2510304501c1d4040413a4544601545950b1405a90009007113500d003c524400c100143c001d607143c0c050203070348412502130208001251020610709c90200050350f102082e00c0001d00c07800c2c42c0040d100d000020113051007080219580c9800c8400401c2000940b540d2040c080310100380300e110f60054420f402410400150301e00517100228a04c80c1c0c2078108404141c0c1d85d56038500f40021040e065214914128594580e43d000d0100d05002010700c1c000c914162020a40c040715100d8 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 580950251 1250 580949001 580949009
    0x10f0c0c030504170a08070f0303050610021b03190302030306101701060c03020c0d0f0c0f061205041505012907110d0203010e0d02101104140607030504080d031a0a 72
    0x190500d000c2c1071044038181d980c4c00304020980343c4119041c59021079104806840e04900ca9521180600414100102510005000e01b8820503c160296501c82e0300003910103038011294140719222008503000038280f03405504403004c3c080044d00598101135000c0b0045100d40c40031101d817010100c041c08220388020640c018000c61290090043c40ba041c012016201118803e00c1203540384140580451250403000c042210840c99050146e410460310b0031072100078181c0c6583c204a60b03803814600401804444500c2d46605070385c0e501140c01c0c841c40007003880009140d41d20920465030b5420718640840ca07011495a80300c8070100c48030921610000c101d8510940140f01c00040b0340700c0200700602c460810000b03d034036640c0c520b0840700440040c05161351100d05a000340030000424035506050350068001042009010401848801c810340810034840384166101c0c0d4490402c1d18051b00c071441560440a207510a080c45070490f46d6060704411415402e0181c00031020002e503040c0b001c00c0c442406 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 580951501 1250 580950251 580950257
    0x1150203070807050a0c1401080a0b0a1703070204020a3f02030a15032003150c03070c0c090903110c100e0a050604091a030604030212031512010f0c0c03 67
    0x10000002c60760030302c003425011380a40c055805102c801e076580500220f40d039102592495044c0380b224465a00551b41c0350f4001d4080030103002c0081520b0000c0c0e00320301580031b14660301881d80d04c0d1000e017050401c10f07103200590181c0119a140405034000e41503a591417071201d1030189019907880445d5114008140c1900d003800d8605010301031100341c601a4100030180300480b0b69814000700d418003140105001980241c494468800b00340341c011904139400c15185000c0d500480f02c02c4111760b40d030b9207410f07400102c0d02c02d41901c0343c03a0303100c0031125800e1059005d40b000d2051078010032031014aa01030a0018444e48034506007a41000307185444000d00811158004444801502c009000300b40780030403944018038205289440b90700241254000d03070400f544070390f0385400f5411407103030b281d0b540c41c0040e4040f0700820721032400c1da40080d564030100026008900000c00469401d0240500964100c1c8000f40100800c1c4903484c0d0190080c18030504228905042078091500b190140e001c100501750555 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 580952751 1250 580951501 580951507
    0x40c0f06051207030b041404031206141e210712080d0c091e1806080303070302070309090e0a0b0f06030c0103090f0203120c0708060c18010e19090501150203 69
    0x1590041c20b8071801003111040c9501e40c0012083d580d104e00c81c060203405010407c200d80d0400c0e040040c407900750303200100c0f8402d1030700106200a2001c51307485a00d000d4120703500c5c010b003900c054030078078000002c02241e90800b04e24141012081f201c1584640b1514800d03044511142d42d401c0b501c1e1700c0114828020b810760008000380c0e90364580036007020100302168140301076a40c0c0d44200b84c034100204091402c2601c07501100510021442c01c0c0b03618201101c0f80c0f41031103003d0500d07080c039032284006801c4405065002403081b003014040c0352403800400c1d0700f032410031196146407050780e100c200c6c901e8100c2e142e00d082000908003c071402c01c243e01600000e801000681144001500107250640b0242c5680358034800e0070307006940402c05444003000151419481e032020007145490110b55400c000001d40250040114030041c0000341d070500268002c941c0400401000141c4142d004902103e821507925910240700c00f4200b0426001c40b00e031a44100903d070f0380d4a00188103020710342c2d40040143c00070 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 580954001 1250 580952751 580952767
    0x91903030324050405101503020903010e03070305090d1a0109060303020c01020a170c01150b0403022d0112021b160e010b040e0c041e0f06020a0b040b0924040c0f0605 73
    0x4d907000d00d5100c820414202d1096071150010903151041d010441e0000e50001088181c41c2400c2c003405a06a07603c90045040401c00c1c0e44c094118020113000074011680480c0c061309111280e0200324a03022180c4550ba40740d40c45040c01000750500780000c2d40980320f0406030f03100b10352000800076401504050f84020315040100d00ca000e40e0301c080400e200940d00c0341a4180a419800b51010040002d184142e640d18a54414441d01c448071440701305421222040c0c2020004050209120703003c024170348080b144000c000144028002d904d1070300007801454000103610395000074680307074400a82540f07180281d914122900c204909000e42840b1840034402080300821185e4102e401103111282c031410180c0b1175120458225501c0515143c2c1c4003041c804101c60034800030300074003600e030601c040c040102082d211418150805040203142c03c4c0644009210790703e0500101036100140e0920005499440c06605401c0b102950250380d08420710700001150280e100b1240d049a500f912038905000d61 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 580955251 1250 580954001 580954009
    0xb07050a1101020c060d1505030f060c030703020408030a031d01150308030709120b061306051c1113020711030c0102102a0203030709080106120609050309190303032405 74
    0x204000d05503c90844612132503079540700074118600d0300d1580000d0391803042e4020b400800c002c3e48502e00031381103e111a51000000f00740d142e40181c0d8481801e9480d21100b00407402849a54000259400007240c4034854030340c0b540024042c0300c2c0d11600d418200d40c02101d140d080f0b0f03800443c2c410110381c42c22010000120b00b00302075a0b1003035060504828917942c81d0740e005029042e00101b12840d58280702001050300e000c00c200300c0e043c03600c80000c2148070708040101d66030003004811450a500041d002ca01003001001c2c0e83e03600c401014007000c420700403000030b00b000b80d0404401150000b0361a491140203003400a00c2c40d1740c41c04c050b4000c004075000000030f1401000c0d40005d0a2610304292a00d00889024445000301001194000d650705e00c3c00e010004e14060880c1c0210348540d041c904100301c0030f00e40700340c04070000b80c0000300010415201e1030003919510070f11091640010014090040d000c0c040982c10f001c032402900c3c1400030130244402c0c1321500544251042d424030100d2020f000c5420 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 580956501 1250 580955251 580955273
    0x13080403062d1a30100f020711090a1104090c031a0f0108040c030c060c050d0c05060601110c090a021b190809010c05011103091902060301151209030206100b07050a 72
    0x50100380d400c864103008010540b8151002d01034002c2e9034401c01403400c59448511440021000704a021070820304a592912702150f000031000744228602c101003000800c00b5880481d80713640a9200542e03a42c0d540c0380c18405004250303035580200e440c045d1410b280001c1e04440000d442e100500051100504030019603500d08007400a54580c8a205c1d40800081e2080020001600050700c85032140e40d01850304d58606a2542071120400400380b510300e000400c002802a00b0200908111500094002c0c4840c6080740b07444c00b4560041c500d40511943c10041e60041c100100710000ea00042d41e20403181683c0e8064524012980e80100c0d0107480c0070503031141c043d111201c014500800d503100a0789480f0b080d03844030b040d42590150000180107000408010300459244e403183c0524008600e40c0000c0c009010522400c00d80d14100100220240d1080d00401d0036140c01c04801c0003007511070b040007540e480b412582d01031418040c410110b0100310240a0302c5c4c3d00d60340f010080c10b40040c03036510000c0c150 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 580957751 1250 580956501 580956529
    0x1b031b01051b01060305060f0a0903170c090301061503050708090a0201030915020a0921023016030b0a0b0d060b060f0c03210f13080403062d1a 63
    0xb00c1c0c48825540001828000e410041d07000340c00034055030a040e002030410715005041107044030700c0c0c40d1400b0300098020724600f140c88078115180728541d48400080341ca9104a614540d415442e00700d0116000300e41941100500d00d09540c00c0003190f40b4401309480d001e0007038582c5883c650040014000640c8030340c0000b500313240301d40c1a5000e1242c8020050b420f0340c2100c2c1c500008100d006005002c081d84054500c100c03151424001d401d1000310b500864104005270320001c110b07032110a845400082c40d58204010700720b4410803140e20324150b4401161103442404220b5100d00c40c00c000c1855184940110448210003d00e81100070031107541d44001484140b803810380101c400d016074161015910043d140689440001c0e594071610307203612f054070124298182c03c2c1458807400340015200c1c3d0024456003c60240d60030455000369050200e500e01a83d44010501402e240d45079000b440420b407081c22903400034001d9000d200140b01464146c03402600d004c1003c10106d5400c13a5a460000c031031801c51 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 580959001 1250 580957751 580957777
    0x20f04180905210f0d0b010311031608130b040f0c080606061b1203010f030c0803130e0a0b030105040f021f0f0f120204090209011b20010e0405091b031b0105 69
    0x4500d00031902c44d540c0010010080a82d51460802182e580501504c2001126000600d10354500010008032010030603844400700a2407030300186055045c40301400c80b15170880040fa24900d814585000000a000d004603240000d84200103106a00024210300a140040c076550409592000090070180e1140680ba414070a0000840c040c00510001f54041e00314681814016801c600b00030f003800302c3d2648100c1c410713802000507401c01003159282c601504c0c0d200d0004139031034480c003001ea80074000307010085515500e8a002c1c0410000c0e4500c400810350b201362284032030560548400c99580c3c1c901c8903581301190040c034040712218883d0850500103e00c1e800e0560411084c101e001c4101c3e04a034101e00c0c0c13a5540011188050340e004002c4001c110300282c132030300607040682d1b02c4013040b4000f08a0a0940182c10700b4000ba40ea000304501e2000400c00f800820030783c503000d84050380c0c0d00240030508200c0d082c00411b2070528100880c1c503001807290080c0c2001552289401190700d640041114110 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 580960251 1250 580959001 580959007
    0x15030a02070f140f03030f0106051615090c050303070b04110a0314030408120301060905060706060504140714160b061203130614070b061e04020f0418090521 69
    0x2882a10b0345081d82401018070004100d08a00100d2038680301d8440d11003507a0080c0104a9902d0b0300d12500c5041d50064035000d9101c402c0a00740c0040c41204080041442c5040c20050100404a60100d202c880c0910921400c0381d030380b441490740f00c0c0f08502000c1c3c0041003ca00003004a4001a80400c509001030301500398140d9036100e148003800307a066001419080000c0400c41c1c101c0410207001ea0200d0b03003002c0c0385154908100030b84a0081032140350700a00010031583d084c486294070144c01018068400c0c40985085103060704036101c120f40030400304030004100c00c450070349102903503803459040884500d4131080b07480f0940507050013044a0340c0045045507030300b148803050000d449440280350000c0e0b0020b0401c071024002c0040d00b0112664000e00384030340720108078840312850b000341c025a080041ca4038035076943c0c1e44050000f48404c0d006800004e0b00c1e40c007181d4010040040b80c1090a91381044007982a4150a6410105018011380e02c4820304242ea804d0603210681a8841c2402c5545 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 580961501 1250 580960251 580960253
    0x403020c1c0212031e0d06050301050f0a0504080906070807030f0323040507150206151c080903010b190305010f091101080718090501060206070f050313020409050f0a15050615030a0207 81
    0x1104203070110303a281c40d510340440c1c046c01980aa00a0002800c1e0480088c002c03071901d00c1d5123a001c1e03240101522180c60f1190081000c1c03002010442c0c0002c8000f62145503104018140102c0c41c4e0311111048000038040d401200d82c481c070921420281c0180804c1c0b0002028031a0b14400d5009800b5100307494a002c3c8a41c0007451320b49264198a000c511a00680b43c40e10b4554a41041054a400000e02031091640c034030344540b10b49504848601d030301c240101c0e120341080c80881d00600c0300403180c5410161210340c108a005c1c5103182d8404480c495002404040e07043c07092042030300e003201c01c024020a801240c0000ea5070003803022a5000300c00c1d10382a00e511a04000e00d085100c216807014594507a103100510000c0c3c4c0c1400080d5200010703040458600c00d858400030100d2200400000c01000c0700c034800d00440d07580c0d8010401854110b8229a607101101a43c642c070749031f04080c01c84260030031503400044a161400743c548a0200285400340c6044c1140303182105270b100810031540540c2c00c01140c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 580962751 1250 580961501 580961527
    0x903060a050f0901060501080402130b0d0302071401020109120f051c0f060e091507020304050a0e0105011b05190609200405072c04150801050403020c1c021203 70
    0x54800c5126440c08a41400c0803009064081c030040c103040840d9040040510041e40c01c88081a0010750580d00d015030003800c00a190014003028040719803010341d810410b0107240e40080c4550036038880305030000102645000680c201c401e0910020322510f0700300c40180910340280302d000c0c0a44c500c0d0070040e11702403559040d02440c0c0c1812014064280d0b0720040e01c0d003910f08078401c543c041d14541c400e100302814080250b50740c03080c000f200200c040c1880c8000481c0c0300d10034019100140340150040010503280d502c03101c0c01b46c0342402502c0c0041c04035000c00e43d804014010000385950420040c1469446030b80e4150706076400143c0c01e4491a0f01c903a039410000b125030456002d54218014000c920765102000c100655502429220030000d813101440c110349002c4d048904038000c0c8130300d0862080000300c0818090980c50140e01004448031000103460001074101920981c8258256101c01c0076807001c000ca081c1144000341d8074114001450401400d2280c1c801c040840c030882128248141c400040e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 580964001 1250 580962751 580962763
    0x9040311030c07150807120905120c0106080f0316030503131509020102010506061e090d0813060e040207031e0e0a1d0a050103050a020907030b0901030b07110d020d0e060903 76
    0x4183e02004082051640b2506804030281c06450142030750300f04144000e01d116103900c0740c02c007565074480d20349013040070400c0390f4807030140615540d64483c1031030000c8500038160b074800e864860003442e200804182c0d02000700d91020190030f6100c0c241140302d44045039107410041502206101d603d2841d004a2644041441a030014500c04640c1c045184002429903d0241485d8000e5501388405010444240d07400b880c50041140495165000480011580d00c0d8954015219130400180d0f004118580700c03044042d2411925074085040c00e94060004920072800042c3c0080e41c80d036200090262024565603280e080c07840c04036080c007200300000304421000d81c40800d090000120030703803180d408103007119400500c078a8100b107558915101c4588034001454000d1252801d000056640b42c042c0d4070600f801080035080c0c141668480c50040034800302964100040717808d101e01010000c80001d07a4048140c05075001d4000e4484210080d079054581600440d808801444a1034440d10100701c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 580965251 1250 580964001 580964017
    0x1806210a0e07180c09051c17030109090c08031306030b1207060806120111070f020109031a010612090309060e030102120c0301140307030c0b0318010e0c100f0206060904031103 77
    0x2020911008442c940454104851844c01c0c40038000c2e081100d599001d124030a803403400c010450b403c001c90b151126101d10310026001c0103000100c00401c0400666001d0100d291203034000880701034507035001990704e0040b008180d04240e40c02c8802c0c0304251003a00050341c00900030b01031146502c60304007402d05080d070507004800050481e5040010300d20b44068060354004040c2c0007004641401c0700385014600c2944000750919a02546130700031a4481c1d07000100442d0003584241d0b08032114149401510002c2c0300320000103100300000e06e41c94806100d0105141d900d9180c80d10f540389001c1050720f02d400d820f801154103550912501050f10746640c071407441031030907820040c0d481d0705026901c040c1001c6916010f01070340c0407403402d00005e0308264501c07013900c48002d03829071a540d88801c2e00c200f42640a5900e54207500f0540d01d40124040020000c07906401118100c0d003044030503200315240c8a140161000517070082000c2449421f118003c60b80050080c0b40c048002c0c68070b211003500d140d2211030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 580966501 1250 580965251 580965269
    0x40f060e16031d030f16080a0201020301030506010f1d0c0c010e0c09090f0316081c020a080105100c030516050a031716050a030209040f0c03021806210a0e07 69
    0x5540829681c0c58030503900d28820340c0003900300c3c5102805001e6034078016450344404c0710b400050300070628422100b0318559142d0004003990399203401d9800a001c1e410a1000302e07070f10301c507410022071803e40c418281e4040c0c50032010072400c0049903851042c0f83c10009400101c80410803c4503804492007801690810003890000b021001c45150500210280040940c100f507005000105071101d0f0100889060841c481da089000d5407440c2404143c91188401c0c1002609030146001400c0c81c4940181604040740c1e11005140d17a07940b03043c0b1041100800c901000075030000c2c0c804c0d000038010750281030021860741e0f00340484032a82e91020701d0b00c0041030040d00402c20369125031295100301401280c0c8800a107440c001c288a11502c060854080c3d401d090040c03640100d5801c0d12074030b40e58001144003c0b000401d028042c0c2c9660080d001354003005030b03001501105600c0c440b660400c40100c0b000e402c51540c16114244441c08201210107018004078902516000c20b2503604e80e04006010207007203000 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 580967751 1250 580966501 580966531
    0x61103092a01411315050301060804031b03030501090b0a050310270c150207060c1101022406030d020318060304021206190f05190218040e07031103061302040f060e 72
    0x4c2c000100d44615403241041ca08980c818141559100d01902d0448510341003000031a2280c0c03a0030b031400020f01805030140581002450145a4550082030490703140510030004601000c040c01480345803409129050790008141c81e035080b510741c1c00a42c2408a02d200c068041d0500c14414042c8826150262136004c4c00070750601400081043e0082061040d000504c1658a00721000d8940d00c14040d01600c0c4108120b107880300c59009124207400041c42e401014070900503042c500503180e07815104a4002e104030400034650600000440700d000c880300c1428240c4644850400040c1c0d0700003002241c1101d60ba0011540140041113000d0142c00311643e01c2c00180d1102400343c0450750456940e01d40c660030181032001c055080c0100c4400003605050240c0d5451040c04c4c1008003001000f54141c00615100a0140103440484d0290549100d2000705010321080030815039075200690300d034100307032182d0607075600189040c0d8001400c000041101003880e5a0390f0050b040301d080c00300c17048072584105c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 580969001 1250 580967751 580967767
    0x7031503060b0906090405120912030c070e060102071805070302120a05060f0603040305030609070e120601080706030c0f0509011b03080f0c190c061103092a0141 71
    0x65a50f056000d04142d546601e10700d001d84685544c2c0c0300d58084000e03008800600500c540d12140049444510342c40c0071030b907a0701d6030780d80c6643d0740b240944182e42c1641d2002d000300d00c10358800f10f1317134504445010049a00c0950440f800a00405005d480d07541419400c1000a075903009403d0014403a290b503080005140c40c0c04028414402d8140060070302c500700810402c000a0780107401e13030307030880342c00d4070899915620358900303490030000300640544c803810382c003124503600c21b00181050580b484c06003610f9690341d8030681070303054852220380d203000f08941c110030303501503842200541141c80051501e01009011600c0500c650b81d100041a0002050720042152610481c25500d4001c0300362400a0301d402d0420141c000451591051641000007000440d414419590003541c60300008640b92641d0382800a880d03640c503001c04c0042c54000301c2048000b4030420300306942c22600881a151140302440210420b50711003d840d00c0c2d201c03001520040400d40700c4640c64110020406081c11559503c14 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 580970251 1250 580969001 580969009
    0x60207090e07030b04080d0608030f0703031d0c0d0309092a08040803060409080f1204021009030203030703030e19120905030115092c01050a11070b040b07031503060b 73
    0x1401c1000081d076445044100000741c40541ca45502a0b00705481036180d100100540c0003504041d800b01c07103d440f000c103005403005600401841075030f100b918100304ac105d170500701c00c800410480130510160002c3d60321462508058005150492003442c019001c692a040d051023120300220460002c0014444484c152900c07010902c04151100d04285620349050340d03944c039881c400104013a000c0c540350394190ac1007100703101c00d4800034280300340300644500131071202c3c1154190840c4d05921490b01e61030500e090034050f4005109a03a0081c000d1440c3c8003140d10b054020b0030312480321103c144194019080390040d981410b0814610030021900300030841d40b4000c060102e9a000b00b4807991400d1207400c10020180d00003030850340f0380754001c100340385040011800e411503250034419096a81c414130071110419400316200d0f4a0512082161403486007034010b150052101c01000203000c2004500419002215590711a0181c41c020032194500f94440d07034007080c5035100320340042e290140090a494 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 580971501 1250 580970251 580970261
    0x305160804170a17071d190f2d0602030d0c0c06231006020c1c0206031f0b0307201f091401020307050f090429010f050c0706031d010606020709 63
    0x18540c0b400940c003200b11003040700c903e90711b40360003071007a200c50380c5010340720000340d21a4000b01059010704000d9035a40c55039030340500410001c0d82002e2149003d00810195600244050310b41c40e07070003541000f040f0080003000302240110b000610a0402c44500003401500415220a065404400190500350100c9140c0c05010f054400d03030611080003807018640c00160800c003c102210680070800c024010040010f48610000e5040a000401c0029445000190450320490403040c0c45a40366107125621240c002584d010001500c5c0007a0010903084140030240781c500d2042c15030301c1c4a4080403541c503040318460b03a2564866141c110201c1407205048129030f42c9100c01000354035625003810028454415401913420020340030a60f00040d40325588071901c41c036251140315a00760501c08100148254914000f40051f101c80b45618100e403192040e03038040f80c550760051030068203161056000c1d180b4800c24140a8407160403150445000340180c0e8000c3c030064000c6d010b03060500e805581519 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 580972751 1250 580971501 580971511
    0x83c0c01021b011d041401150f030218120106090c0309051b030c1002030f1303020f150412081c02040e010608040b070509030a02031203090d0305160804170a17 70
    0x4004650103520341d80009070b5032845403100740e0a020b90f184c0d0400007030050a12200c5500c40384002030000ca200050070681c00742015454940701e6400b82c4540003103003648182d49200f50414035030b003000c81c0d4a007000010b000140003400c1c0045009070b162400c504c02c070352007024182d002a4440c2c4125042c01010b02052580d04580d0350100b10b0380c40881c0101e9503d100b6420b89034020105040e1705e0951500c28800d0700e4090180b4010541c2d82c41811103100f1552400340402d138405d05001c9018452403414065000301c082085101324201131030000070003000c0c2019101035400705002c011401c1340540018040be080c2c400b50030016161070822440d1000120705800a80a0006a40a12020501c80905203910641c0340c5001942c0e01501c1c0b000c40d04040703040400030742611441c0f400302c0d40040e810000c2d5100741c5014048070f07030201d1560011415036000b940c90303018a41c0007402c602d4640b4403648190b58450701811021032a2045081d40c1c8455074030a950040004503282c803c801c103504d251050176004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 580974001 1250 580972751 580972783
    0x91305060a02030709120b18150c0306120c090402010e0112050f0f010b0301123c0311030403110d0807140703020f04020c0d0c030908030d06090e07083c0c0102 70
    0x40c41e070556407551640c4014003c1e0003201c2441e4100344804000b00840c271028100040d0800c81401c2c0004030361441d41040d206213210310300000c40f032150f118000036110004c0500400c4c41802e510359800541d0030313084882095040005000c04c004442c545c80c041c55014030643c0b035810304107103080a5003118090040e08150300740c0000300010003081c10ba030400b002c1160740040c0740031101d9006070010240740c46e90601c3c504910032481a0100f5800d2034225139240c44d07009403150000140c0100c80c40da200c0c403c03070100500c2c22624040c1e421141c1000000426250703c500c090700d140408580b1440d002c0c0980001810b01c59000722024070031410483c4801404410940d0203504106003c0d51b1240c03100c8240c102c0c4400c00c900c1307a003144113051240c4401c9000b0039005050341d071342d080240c00c10000303002c0740d000b04100b00d401c0010540782d00c039001a800c03049800c58005484020b4400c00482030035080c6405114030100448046480d0207400100810742c3c0c50424010404146090300190a00c5c2c80b01011081c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 580975251 1250 580974001 580974029
    0xc0f0a080301090b0604050409060c08060f031e15160e0315040605070c060f0902030c09070503010b1309020406120c0e030303070f12020301120302100911091305060a02030709 77
    0xc03154401e581c192038903d007000c100120100007150042c02143e02180d8040e060404113010700581d5446000140665582c41d603903952101d0511040094140746142c0560169003100c4150700710000c00f0f4520103510702941e4035040c200c0440014054151000348078001d820510f40400c1390060360300a0a66416800f0b403c8a0300d01842264041400401c09811103440c0c100003104240f0480f064883c06621142c204200821448994001d11012170700324024800c0755660107403454140395240c4604d905a40e800d14680c01c00d0107042c4550003009801004040362840401c111000e1300281c8007400b40c83d5140c1d015041000c038200c0644424829003400d0107021080030440da140401225444503007400d00b0859100c007450120746019241c104a4940c40c40440013098001c110380002034554029421581488101d9090404907004000000d141030480300b4000c4050400080e442e03404105030160401c951026103c95040031021220054010307400020804110740000c03510001c0c003204030407105 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 580976501 1250 580975251 580975253
    0x6080f0d110601062a030305010f05010c05030910021f050a1803020a1412041701060b0c0705040c0507050d020c131107080304141e120a08070c02060408120c0f0a 71
    0x24031140180120020046650301045e1034100350505015516000351910031020080d0070010001c0a0078061801081516040090258480c4c4120b0310110f4222010714079042200d41000002d040910300f05080d0b00a0b04000b0030404450b0707098036820000204081068540303940451f088440000e42e40c1003124415070030101017035000403025920782e407010241d01ca1000d2042268680210301c0041c04d03007202d001402050362500483c5000c0c0e1485007000074481540c03260f001c2e0f0502c0c06440f0b581d29496210000811540c640754002144040d160f0070440c2c07914106454003800e000703882c030051001d64004481402103042c0710401403200e180542c030400c01d2820b41116101c66120b20a0080c101c1c00d0040040340901820300e01c14404103424000700c40c90342c00342c00c404036042d00721802580c00c903000c0c2d030074140040b0a40720229010031902d5a504600c581c3e03000410b4640d152240800d036006001880080b4030000200803020742400d460b01c2c3c040c3c407104422412480c0c644102d0700c070190f035089144420 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 580977751 1250 580976501 580976503
    0x50a030f050c04050f0412031803020a0c06080402011403190207050f0d0e01050d0f0b0301090f060f020f0912162d030b011a090306104101030f06080f0d11 68
    0x5d50002c4d80710b820404011281d54048010301035041045042c101c4080d2a003040580009034072602030310641c0c14004c490b548201c00c0e078140300d0403103010b400b00f24000c80e484007010000f0010f5a01c540c4030b0b41c1d0705185040d80d0b01e03040d00321b070481e0300211040e5101d14022140d10608001c8001d050026161116455030110300090007406031145800781d05031500024044083d0b03030341201d041d008000e802080f1702407850034150154070500c003003034603028505003120511f4051402250704003c2500c501358a801126004d0000700b07a014410101c1e10b0045901d910070503070400d502c5070b006084141400c1c040794120b5821b19443d4a180903044114801c1441c01c03c00600a061041d04452400d620701d1036040034030480789040c0c42001d40c0140d15000d0345082004615060346454196180804020500f840c1860b111001d01503100034121204000030741d80180c4104c186820341e00d0381042c0340210340000c45c00060400e5880d00d411022203038015a24a40403c10104840c0100340f06618104036200401d42e161 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 580979001 1250 580977751 580977781
    0xb0916020c0607050a02030a0c0e160f0c0203031209061506070b0a0b0307090e01060e0601020d080c1c050a06030506070507120f2001051801090209060613050a030f050c0405 76
    0x1e03015990101d00ba070305004092220440b519000f03000d0b0354000155103006034444599004000c0d18003100b00108482c1c02d0f00b442408084d942644500f003510816150941301a038540804a070305100070030240c0300c82d2451041850007882c8400040405040c95402d9140e0645c0e45119070f4000c2200b031240c00c010420380d00e00603412494003100081c6c140b41031004241001600d4010407409410040c40e0451290154040340443d9031030318240f10b0a8480800480e21080d02c00560800a481d82d4041280340c1104001080319600050004040508500310001510320403543c00790344135a0b504007002844424000d90360300c22001d18046141c0880ca41c3c03070ba44a1060810b10380100400b400008184074082c13450080346008660b4180406400000464040c2c40101c40e948000ca001c6104102031140501424440540c0184903c0003551150117200e100d4210109482c240c1601c4400010542c0717440020340051401850901d03044150b03800c00c036103006688035400f402645418100a03410b0708010306 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 580980251 1250 580979001 580979023
    0xd1a041109060d020702030a030c05010b0f030303070f36170312090a0803041b080f0304271104060912020a0512011407020a05060906060105030118060f06030b091602 73
    0x1d441c0c075181d07a01c030f810b8000c1c0a2104001e4262142083c03141c01d16422540c3c248071244100c00038004c02034003600307000c042003c0c44980b0f6095401440881c01c640d0103102880418074040c07a2a5620900c48000c5514041040c5001d021000441099442d1469290a50320290105a102400700384034901c215a50384195603a00011780c0b110408a039968100b40b000f10502900b0420450300c030308043c1403e01c04000c00c0d00c140e5542c180392400008645c003000c520030384410a050701440c00d01d032801e1705000c0101c1a2450503503646002e1014004191030a10800c1401d03420903101c56111414503101902c544025048241c005001102400042c1e8483d071044040d5142940c201000d21400700a036400743c400c500c1c484c8000c01c0d448080240c1e03954001740401401d030259041390010f0b144d817520b080d03c611064420f240000c004100601c010248031001c0d4211080b000b10002d45596a03450940040e4029046940000d0315110140c14500c5c0c1608419000ba0342050004011303030f00450040d40d42d00620b05 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 580981501 1250 580980251 580980259
    0xc03060319150f0b01020607030b03210f0d1d0a05030409020d0902030d0509041104080d050703020708030f0d060503010b0d022809050412080f0402010c0602040b0d1a041109 76
    0x41c1d4010003030002030110107040d039004244040258800300a001c3c10844445034014030401d0001a2004d100740148071541d030025000d051200f541b02c240000d00a014882c03027040220070403245c4600e40c140001070001c0c40a0110004114880d050590340c1c031060030030f500040d6032041050a001c20380200c219402c03103881c804016920b45600152602820910300060360500501d0b52650f80d0300c0e0007000503c42c14600326401c00019440c0401c440300c50086004e000c025a1080c2c0202d0030944c0254000c20b065806401201c3e40540c3d90340e0b2076441d5501c0014440350700900407598140015860203044090f1500310700a100680101000c40e08103114504041c6c890360001807440840c050f81081c0c13048074100010414034840d218000300c0f003c2d00d000d03a811901004207200942c2c03602d100d49559409046018001040d0703807143e400448034006650000e0711150750130080010505d440000900313a591004801203072040d8018000e19601034140459070149080200399a0340001c030f0741c1100d0526600316 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 580982751 1250 580981501 580981543
    0xb010617191a03010e0607080618040f050c19080606040c08060409020a1208070b010b1204031116031a010f0605040b0f0403290a0902094b0c030603 65
    0x107100c0d415200c42d031002c0c64055191000c0d04240500200b10280305007240d03103581203262a6003081c0010400c108856050f4584d001010900060007800d0000d0100d000f074045a07070602820001880c1e0b0181369072441e0440b15000000c001000041c44682e91100c0c0441d01081040940380c03020f850180000d0215101d5950b40071403104540e22078809101600c0d004101091912540c80c1004c0c1d141c0c007030700c01039421501c89000014001065000c540d680d060500c2060144c1e21aa58166000c4089600c0325485000b02c07046040760076031400c0301e40020350064840c03914829a140e50741000000c10307000001980b071306070307800c0c002c035504602186c0c01c031000c40350351079070b0b8421044c0c80d80a14010350300000c090000d850310705190085030012040c541e900d01c00c0a00c945446a51345181280d840a02c025002840030000455000050084025a692400c4541704043c0c100d100008542104403480e001301241c501c0341168060660020396010b09541445851030414a001a80d07900c101c45140a980c4a08 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 580984001 1250 580982751 580982771
    0x303050702100e030a02011d2107020d081902070f14010c0b07030b1008070e060706090c031b0807050f090414030c0d08070507030801090c020114040b01061719 70
    0x81201c0c440705060382000f00710600905080d20380300c0d488401030900541c20b1010701000d0200904103007600c504044000c0031307030021002180031101d8003103000811041c4144a010096103d2100c040400d81c492000741c3c6e035401c225500c0321170944410200d07100310b600407282403021400040d02e40098071503004401d50220344110040700d0044965900504d0800d81d0014840400d81541042008000c02c81d111071041d56210408c868801080b43c40742c00051005001c0426410548000c11281d80119400f04159410b034651040c0c0405a0340300b02d4041441c0264002540c1104c0300403009040941c010300001c40c64640090160195510000c0c4079001c48004101004010a0100840c0300200305803520350342c00000154036181b000300110b002c20300d81b4002030242485101124031040d0705032116000c5900382403030400241003a10408080d503581d030034401c2181100051a501c55841402096215070400100800c99460800300c16501c0310310f50b0601400540c0c030007050417a51035000000a0100c41 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 580985251 1250 580984001 580984003
    0x8060303090301060e06010813051c0311071b1e05191a070312050105060d09080d090b01031401111204110a0e0f010e090718060306020c1b06070c030303050702 70
    0x75003140700d525629100000900e4071a144e10141705200076211481d06980d030046500030408517860003411600078981401110701d000e81b0003481c1c03020514000900e40d5a0380d061140700e0b030000006580d407080c0d2400d0160102004c3d06404090406000c640700b1410125696440c038000c14001d803032140e442004002c0340c130b01d501650344004081c840502c40ca0110302d00b40c669903d501000b000d80001d00400195202d400b264081d0342e04a44001c1d00182c50700381e00c44860001000c030608100d500f54010000d0880403c4030340245000c107801207810785a17079403542c075140f0070795800d0b045501000c2c3d041406981d9440d028170152001c80c0e01801d03420b003840d51103140845c0c0d10030108480d0360340b0101c83c2c480030981034081600944a0f9849041815003a6252200800d02c6542203035040c9542d4010a01840000418400f00d09041d0000c003000c40c8107501e03907980c40c2c10b98010950510850380201c00d00d80c4851440404450340c2c01051b03416516202c4541c44042200f0014007014050581760000300343d517144 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 580986501 1250 580985251 580985257
    0xd030c021305010b030405010e010b090601050d06181e0507090b0309100f0b0102060603070302310c0e090c040506070206030c0c1c020c0924060f07050319050c0a0308060303 76
    0x201c5004100c0c0d9a11030600c161150020350b0159031561a0031000010070304140b09405440304c0040490850341c1c2c8110045407164401390401801c15210b03440012010f44003005071211032000c0201280040e920104082c1e88920a69030b000c60500749418000c0f4550440d0322078040d1085415110355a54880b185c203450f121a0010220f1054980340425165003816841140c001e00300340d0a41c1d1843d103a42c0f081568400c051300029500040b0004150404007221513006804401b2a400012940400034010211132141d51030002103400080f00a02d2443d01119480c0d1282d0b4211311a81058104404070701c0d80d029523203009016060004c04514059200d80036960410070303603011582032138101801c194041007160840d00c09845500c41091103450440070691292800c25404490003880d10707040c90018205204e000e03000f0204002c00c03c10030324604000c01c81c00e40180000c42d0303541c800c813000c0c502405011480c2e204000c01881680e0b29500007250b06c0c095a80c040c03600b5403058443d03d0002e03044d84 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 580987751 1250 580986501 580986529
    0xa0614150f071704080102210f062205160201111608131e2c0a0203060d020a0f0e0a05060f010f0201020d090c05030c010806011b0302030417060615090d030c02 70
    0xf0401050000d5440b0054004010742c14900702501c07030000039214200d0380701d08262111000401000000b400a042c0610054401e0b00800c144414550b1230700b403140d045580070380340180d0600d12001040d0005409025403d0b07244000790211f8a0f02d8a4000c550100804811004041410003d910b90009110503048400340c4011000707141860801c008104c1c90a0591142e83d40301c4083d1220005941d1a00141c00c03421b4040f14045004c83d52445111002540700a111540c4009103440000140e1941949540a0090801640d040504003003546640800c018100c1e8680c90900040018039210f024007003d40d21000e01b050707003843d80310440980c064040c8601510100d132a090480d02440050900b4a084640039800d40d159089130a0045030101c8040783e859000ca54440c000345044100000741081032802032042c0ea08250300d4040401c100000031407142c28591008040c441c131072510208510800d480c103040d080c90541d000010a480000102006c0c013400840c91203982551202c15410300c5038 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 580989001 1250 580987751 580987793
    0x1e0103120504030b0a02030a0c0504080705040b12030a0f08010f061b03020c041a09062e030e010914010b0d1203270c1d011208030a0209090a0614150f07 67
    0x24603017106401e00a4104441420609091500700d600c0180100d0032103080c0c1d4803020140102c641010140b00140c40c4000e2469044500e07003000828040d0180080c014440b41a034880c04051408040185560010781010420610007030040060381e420401c1e840c0000121600c4480000d12400d0a07402d003502c0904080d0882c2c1400049131842400340e801081c00f102c100d904000d55220b02c0207000304c41003d03480c4080c40c032051644454107000c01c0307908003c2c0a0f4580c036010641201c0e0042481c02e4030300c851801c035040e1040162100308002c0130700801220040a0381c104120240c65100c140c11102e01c94014401d26545800307810a000e807500000e154088400344142182c491032070581e044280d5482030f14101c0c0242c182c0c40d2150000c41e48214101c6040300040d1150704607648a4180d86d40c40501603c20440d801c100384101da0300c03640c2003d44243c81c0039000088070341c9801100c00f9030201e050103c1c0d1040b2003402c40d0340c0031460300d2415035002881d81030742c40c1c4c0c40d8046850130340310790505842d0754540 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 580990251 1250 580989001 580989023
    0x3091513060504050103060b0c0c040b03030705010213090b1e09090c120607020c010c1a06010c0f060501051e01020316080f03040615061e0f050f040e010e1e010312050403 75
    0x20290308a0b00801c00c5510a90741002450742d5120f900c0240c2c01071136044032180c0c2000000380070528103900321407984a80103003075030f181080315600c071822a44032001c00d00303210245000070002c44071684660403e60301d0550352401e40030381e0300031680025108828040e00c00c00c00140424000202002a0180744402503d40207040200f042815a54142107a1840062049000c1e5100079440f640002e19916400450098601c6541e17040f060302400060489040000c0340041001181c1081600050f0600442001641c4c4d4109000c0c01b05290301c280406005041b5425050b03c130303036400411504408080e5202c421512158a4106030912a0f150002d52150012041c0800d0001540c411040c0341c06d0740340390044180d0341e22400c0d41c0c1101580c01005528a07881e02d40c2c51410b003d121280c80e510700301d1801519020711151400c2260b0065044080c81006031030040c0f01002c11303003d201d6000120701c051400140c49500c140d02903148140802040811103c0013100c0e201c0c0650700b43d40142d640f00440c449 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 580991501 1250 580990251 580990259
    0xa0609051207240e030a0c06020f1611030d0e0409020d0f0b010e01050d02090c0901090f120b0a05060a06110f060a09030e2d06090303030a02031e0903091513 69
    0x50b942d09400c0380f80b90701e8540301c800c00f610114420305032030110390320146051560005d41035540390a0b0910948100d50204611544c08a44500801c000303221040c2107222456603042203620a405d0160342d60003a8400c1c14040f1325a5000f00d8585500e01c0103c0d40443c5513a004d10125070b40701d0203c200204180da0a006000420a8602c0018147d60380c040d0301061503039036502040120300130711001a4215102601141d0446894070040c264003c0604090b01000e0303031078240c00c90340c801135846030303984140b0a00300008020110311440d40258403e501403106e41029400141c07400110b11540d0140100101c00301d200110501001505100001c00d40300d1518011500401034001040101c0003e0b800440b500040d00d0014566440300341d541d103101c484205030812048044180c4e00324240d0040d824840380785030360f5080004500c28203000300050303100d0a0114116100d52044520090310320f8241e010801d82d08000401d0301d1a41800322614aa10107110f41c052800303121f5805803480240001801107 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 580992751 1250 580991501 580991513
    0x3180b030a020922090510090812151005032a0922090b0a0e03190f0905041d06061005070b0a1413030f0e01270f0e07021506030a0609051207 62
    0x4030500d00810540d46481e8100d503154003150340c1e035400104281001d2241000e40e00c28140c41c10b60113000d261070bd01032411400000317004070700301c5400040016030010802c040b0080e481600d44092036aa03820b4a180042d529102d04140525003c0c94003c42d1041d86140c1500f88410110b21601c1328a0003c0151b88040d080c240754000307040364240742889c10318070556007004000088407000c4045200740c00082240260031212075101c1112003040104442c004245641c0c0d40c421117000c148101d032034081c00c0c009080d030f550520300000c012a110702480181e030449542c0041c226582c965005010350660f40e20180b400c40201034080c1c10400c070001840400949a101040c044403542c000c0d203558209802c104c03402c80750303030402051132070004d502800c442c1101031801741942455140703200403184c115101c0b4040110a0070030f41c05600707a000707100280302d8107940502200c1310070010314400d800305140c440c011a0780e585115400034a01640d07102c441060010500c07014203044c041b180076517a1000d03542828 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 580994001 1250 580992751 580992761
    0xa06180605010201050114011d0f040c030207110904030804120c0c03030315050906060f0f0705010c2102030103080328060801020d050a06080705011101240303180b030a020922 77
    0x4540075601c0c217070000c140552030a1141c03100b400142e580a140344518060182548456100035400071045411410107036941c0c000c1ca1041d04107a980181c03601080d04198002c4450241c80d103004d03244072024030010a5200301c81ea50b0040c2c1000840c20705040b09402100d80d089003900180055426040101c20107038560400c0040404841802500035102c000700300740030b2800c0d00d200d58412401c005c4115030080070000b41c0144007600c6802c1c0e0a2940b01e440b682d0075101c00718540c41c00510020360188601c0781850031060031011240d021400c660465035040840d21015010154600d031400165518011503060481602c41c01c0c8418411340703944144580c00703504800350300800503040000060f141d145900c143d108a8101000910b42d080c0f4240055594060010385032100c2c1d52164003841000107141c0d0034815200c3c801403520781031460344c00d0040461a6801d10b1154690500e20100b100192130300680b608040042c0d80169540c07000c80010f40061041800140f01800e01001015001019800 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 580995251 1250 580994001 580994009
    0xa09270311150f0702070501120b0d080d0c080109291207090204150c0203061501050721030b0d020907050d060f081b12030a080a02040b030f0a0c030903090e0a061806 73
    0x500f406a12214000d82c3c40d025107004250010702d030007001d40d003141a07507044181070040140c80450960015150b000c00f40e03000c00016445a40c4401007051059404044a4010080d50b00100110800c0040c1c0351116000c0d0b4000e911840c203d10402002d558980901c242d0480c43c8034121000780b035589843d00042d410512882c10202c030320842448000c0d004841143d10180e000f409800c2c1c40e5100380c082e44441483c0503403681009014016440090001848a843d00c0400e041094495000e000d00a080d0380c103014080f8090f64a0218110040e199240c000d078006900c1d0820a44801083c030340c00000344442d42c0840c064a1401070b0020300600c0c00f084200596580130141242c0ca200002402031803200701416001681c010005c00004c10b210b0580181c00003800310001d0720b4143d0b00c03200842c07150001d403940440781c0452020700104080302d202c4c200d5050340c9418240300c0200e00d620090180d00380c0d031103410540c010880000303000410036071208019115007070380b101c0c000e050120000001c1003a401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 580996501 1250 580995251 580995271
    0x60d170712090503190813031505090606040603050a0303050a0b040603030816050406020601090b04020f071b210201110c040e031902070b0d0c110303150a0927031115 73
    0x5000c03c00d400c0c0854001041308001000c0d0300c10003040c0ea589195940201401e2000091220020000070051000030b5058003030f00f180410700e801c1400e001420b08502402c00c6105a10302001000003580c08903012480b541c150500144503912400940c3c0130b00401d62503183c0c0646030002c00700805070000701550040d4401c04004200c014048820f030703001d00c40c038000c14001d1f0717000b04010044200a9008800c01003005000541414003000b129440c980200c01c08580101ca41e1916503c800000001e4034010320b109401414a510300c0110010f884400da6400303410450103640c3e2108690080001080341c6001900420003074905107802922504050080318500800c10489440b00d48001900d4066504e0300b0b469074a024a0389007020005d02503031103058184460819104038854050024600c584003014003101204c890324100904c45055810401140d41b6211100d1846030f8249400715581082d011900100e201905042c2c41c41c1040c0030706131000b8880c125080c8004503a000010b4042c6008807 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 580997751 1250 580996501 580996517
    0xe010b01142b091a130b0702121201140102071401031a030307031e090807050f01020f120310050d0c211202031903050405120f0d0e0a05190b060d170712 67
    0x1040b034180400f02078540328501140710817100b0124416070603464000400303004503204840c442a08402c42c0c0c000d140d80f00000040200108100754041c01442c29034030007440074140050800c040179100304100b9100743e04040c0d4031104440041e14011000400450040880b500c905c3c90b03140051a1001904a81c25011a4124401c4c1d9841c09010307000150384104010740907880c14003003406608081d02402504611540c500801407540611006507119440c0c8841e43d92850700c00000c248044843d80141d0046000000c40ca003c115001c042e04260303603408044c4d07003030750710213000d4242c440d01078040c041c014860703200004030016000001020181000603401d0225040e1030800d40498000305d40c050320075000b100801c8401045100100b04100e200c9090601b0000c40310750060841d801c01d00d00d4500d55019a850b5803d0110030458810745c0442e0b500c613603152102c25540e8006a86000d030540740102d0f081c2034141f040280c002c1c4142e58504034103000c0740d160501c5091602d4601039145024012481c1d807 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 580999001 1250 580997751 580997783
    0x1012060b01021203090c060703260f012907032705040f05010305061906080d4a060904020a120e0705030c0d020a0506070804090e010b01142b09 63
    0x1001c0c4c0e4826030000002d0f01004d5000800c0c0f1900394803601c401c4007000580c0e882c1c1d180070354028014035001700c0482807034540762404003103207007140711706811500c400348080c4610f50f20092041500241e034440740720801e44071442840c00f610701a544101c0486c084040002500c003d4910a00c1e140458004075400d02c200280c0c05107000480d0710078000944290030050018550040d4241e071481e8140944000180c16641d5120550a01c4020382d900c20000d550b01c101c42e1648244407220411a5404441d040c7d000e0300700c81c1038120349007405620841c400c03aa1100d030389180d0b61382905071111b4880c007820640d500d03c440e0030b000340481c8490000c50300603460048058500e80700050203000b51030015004080170414401088a00541d0b610200d034080b0b00c0800c08982500c50401812106116241c00c0361210f0402c2404d07802d45145000c0400c49a00d450710040c02688d1118105240c0c0400c100d45a03503803048144100c1c0703100c1c444500904c541c03030540398442422040358801110302e8065032110030b0940203 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 581000251 1250 580999001 580999033
    0xb0901050703090f081c020301060f2c1507060c0c050f07060813080417030903100c08060d030e091018200a020a061a090106021501030b1012060b0102 66
    0x40c000760002c0c000301035410000303407143e00400d000c4106d400500c845991a50b446400d0b41d10981100001503040c0c580f00d07440c00c0d0841581c03450031240844041600740c06060f1203902d20f0b00b00510900c504642c0c1c003481ca050400008980c042904244280b20103100c0000c05842807144000440329440b58103070100031054049800790540c0c0055840d010140c403800c50002c646001c00a050783c41e010304100000e040084452020042d03c03526000d5a110a4441c1c101814104000401300602e810030360044640b07640034980f55400003088610304011001411b080b03658100d000c42c42c940004003031082c003000d40300c01401042103a1240702d060156079042c100c178009580007803000e81c0480e020800070840da50390003005040f074400c0f40c2c81150010b0f0215210f800542da0040b50f24510042d402c0c00c0c612103401e050385074501408890000b440c42030600019a9a2410140300c094208207500700440d03602c400309001d4000620002c05840381410741c5013003440003801c2d80340071705001d4802c0101c0c0c4250010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 581001501 1250 581000251 581000261
    0x140a030c08011e060e0303090303190905150a080a0902030a2303040b040510030e070308190912030c02040e03120a05090a031205150a14121204300b0901050703 70
    0x4550341c150b207210ba04c0c100c0203480815020070010341c140024030120000d031318100081d103081c42038108020820203200f10090f06c00031864211b540201011928144010030807011030f207810b440c0b841d1601d10340c0e440c440c41030003c2903440c1e0001e41c5030180507400d000b409460b05600403104a44044007442c60100d503442aa607114034030a140440b4020700c0300300000d1401c1d4a25088000c030504011a8017032503515400d040c58419001200d000d0400308185030f07200c40f01c0b0308500505001d801c041803814149400020401801c0600400b0018005440411512150061003444810000b102d848510388140c040c216a800c0702c41c080c0384c0d440d1000058101c038000030465603150300b54072540e08024100500b00054180142030013800c2078400001d50003501c4180d02400200b103040188501d401c8460704110808140c0c20314003640358044081052203481c10401c80e011a004101c1c0802030101c00350303040f00702e07104030700c0220b0050745040b041d402800140d0400c10702c030f400680001c000550351600709408482d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 581002751 1250 581001501 581001539
    0xc17010e0102030714030c0d15061b08030a020d0605040c050a020609010504030806091503070f0e0a050103082703030d0203070206090f060f060d060c0e0a1a0a08040201140a030c0801 80
    0xc01c05d08400000342e29a000035600300c581b145001d486c1165071030b4110203503140c10000c07600301a800c071010010141e1200100c03000880802550b1815089515100e200d0302020303024616440c0c0c00074a64106070031583c40b020007010040c0c000d02100c035000d82d01820f2500111947c20141c000d2000048070110b040c4941442598961180311054031280103000010b6001400d0f072171840c44811050000e56001c0103050014410b0700354106030b00d4104003100700f000d040904031640c40e03801c1400501c00105d00f10240c902200c1c0c800071280c0e2850103ca0300c001c0707005080101f16018000049d140c46c00c03290750f0300154441c02c2c0c15003c485158503000c06159a0300000400a1820f40142d0045000d440141007890740106004104e010741000d06d40302c2c10216860000e400340803c0e02c09180c0407041c1013640c0c2901c020040c20340400f191103c0001c4c0811180320360344e034407803c2200032030015085a020307076404035026405804031034031118046000740041a8400003440450003175800003500005002e0300d0940a = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 581004001 1250 581002751 581002757
    0x140f040204080a03080402180f040314090a0504151208070501110c1005130b0f04030e040c02030d0209060f0304051501120206190905030a0c090f290d0c17010e01020307 74
    0x20f1502074030100c41940d0f02800c06ca9005000c200d40482e202c13204100f141c05912800030400c900d00703082c41c0103000c6490103030750090241c00512494100380d403207a0b2003804940f030581c1e010442e01c1c10740941c000c107405150010004105020002001c0c031510744043d00c9402d104200810043c03600d041030f4550703401b40b5041c52030107910654114117201c42c02e4210301d412968a220340003c03a00c007540c481c04c500f4801c40e018011442114104000c3c95400306540e260781d01c0c01c2e1410000d013402c0080080d164442c6c01d6001e40d07a42c3c0c0000e101c01950300d0745400c0b07803c5440e00703c99507500c03401e080c900380d51a80044028a0456240341001140d5204542000050158010081441d00c0c10041c401c20200f104241050f0074030441d640f0000f420b45080c080091403900c079005906100382401400011180801d1146030b0743d52510b826900c02c4840b0000c14624080030720043c030480c400c25000110310040024001b012504416000180302c590803501540840407640203001c040c9054000034201c0c00201c0388a000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 581005251 1250 581004001 581004013
    0xf07050f0a03030c11060f0910141b0c0a031a01060305060603060d030c1e1b050d14010209040c030e0d170c0f090414090f0102041802090d050106140f04020408 70
    0x40d0044c2c2400071103520581c0c045200c040840300249480e00300b04c04105214800060611381440d0650b00d0044120103030030599900c0e00c201210b121140503c0220145401c103903003d20f802050100540740110400a0407000e03140e4803485d1541d603403100c4400c8041c00b600100004107606000c0c1c002c40d0310414000c0c103606c0c190f50303480040140b0212904019002e00191440341004a9080101016607405041c4000d081030050301d02000c0c0c0802e800254a02130158100c148030590b504641b10070000d4000b0081c4e6544034681c0d20325402442000c1d0710560152403c0e05900c0302ea901347d00100015074912041c1c40b140300f20b5002c02e49002e04048a04c4080a42c140c0026100c0f60750f11000c2d0a480320481c0400b8101000d0001240842c0d035011420440c00da81d41080212071b020802c0418444d4040700c0c020360405291450600040464200c1d1000e10b03500812400d0303190b1640c012101c1c459810000078051181e81b900243c050380000c0350210300030323282d80b40c210080b81418001caa045803d10002040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 581006501 1250 581005251 581005253
    0x5031506011d0103200c1002030c19170109061d06030c1513030c0509130b4b0105060f0906090a0b0c07080606090f0718080d020f07050f0a03 62
    0x28a8510307800c080c0341450350f120441881d0040e0003138141c5c0304410300d07410a50341e20307902141e41c0e240001030700740310320514010030410080e00304041c02d4824940400c0c0c6403d02400e403003002030700c002c00c0928159000145a00000443c10710386d0f0000c0701102c0c0843e1000104644801444ac00d08404855045d055448408003142e40e003010f600845800c1501901345090104c81c5070061798143e00c0350720a907020b50301c2d04414000c44c600350743c6281d00152480d2003031850450345e0f5900c071001900108403500101900031480f43d03110b0080d042e80841413081100d829917200b0481c204500714400c0c1040da000c43c03c80380000c81c00c1e0402d1411a056030280e41103540c1418112420040316a00400b0780a0300441c040e480002c059408102818810004a0180007002d040c841d02c1c2e0324205004020301e00c82c103030340d8080c41000340c0703056205508601c0c6460701d00d80e4440300c65180760740c0c5401640b00c00c0c2c0038820380100d83e81341e03640400c07002a01100002940c249680c0c0301c0412100d00c050300c404540c41400840104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 581007751 1250 581006501 581006537
    0x303020a0e0901320a0b09040c0207060c060903020a0b04050102180a06052d210a1401090f1b1d0a032f10080a15061209030e0d0c0503150601 62
    0x50611103c45134000703285408a0200782ca44c0600d41c400700318510f0104680d030452429008000c0070807120310003008464a0548024050a04690090b180d10740d680e4516080c5803080c03150b942c1c2213800c8603000d1498289454046d0007948190560783c000c03000701030889890318000d20170b01c0403642c1d1607440c10309280d0003c900054000c2000201d543d019403025103210842c00c0c20780500300180034014511142610700301e001c0c950910041466102a14180c0000c0351440039009080c1501c0030182e001940d103482e40343c003500a20912141702e0340003502d10340840304540e104489140c84082041042c8005d0310402c1400142c0300756000c020940f49d035046054004840d070300000402d4101038200d018490303040101281c15601c2e1350b0071001c005001c14041203d03903840c5000307000ba0f00d0105000358840070715004005120113a54184645800d40740c0b10701e042414804c00c500c5c00b801c000104005200200b42c0781080d07416940d44181030281c0101c1c00004d496620b12025148902d0781a107520a60340c12000310b078 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 581009001 1250 581007751 581007809
    0x10311040e0c0312030711060606040909030c021201020901170c070303200a0215131110031113050f0604141005040b0a02060103050c0307031109090a0506040303020a0e0901 76
    0x10895602c154008440b66a074204058280500404605076a0307040c0381c440101411407089441909900420030300c1070a0720380404880c110392125000083c00b074070354642200c00919508020b948207150465080c1c90000650003030900d59000d8035450f01a8034a180b442103070075012a1a002000c10601803000030030301a8000125002e02014611300b20724200d00000c400350001c1c40f282005a1010322400d00c000e10300340125800002d000a00101d512484d034507090000000d00006004200725130a50215034000c1d0851b2607440500300e4155280c0504c049032500c0170807940308840c440d40401c061103c81e82408402c440030f680c012041116605040300c24410711a210081c00420040104000a00d080d02c1502400d0b9401c0d603507000c0d0850354554245640ba107604007851304c0c82904401e00402c0000c515200280c850740b416908103e00d030740c82c3e184040c02c5c00c02d842c6001e0b00c50301a01040008155050b4000c007401e9443da207502c1a610b5441c1e0a0100d242000d008242c3d450344156105281c1405841031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 581010251 1250 581009001 581009021
    0x8061005120403030209150f072a0b090405100e22060c030b01141c15050603010e0711120703050304020a170a0c0806061f0507021c0b0702010501031104 67
    0x80e468100c1010301405245401c0b5020b80000c1c5d40801c002c0c0e0070b03107001e844581100c0c402024850802c54003203a405201d10a10900408010b024a03211283e158100c1e5200c82003580c80454030041980da0950f180310ba800306021b50301c40da00e80000240c5048810f0b60203000c1d61110303050b08405e030b40c0e019000344507a8035460386030f2003040b1108002800140c0e203015184e141402030b40c011800b0460000058492025504c42160291092103049035450174035034107603010310136800c004c035545600d07011100e1100566000190440ca0000001c2641c0b40481c8100e4011880c2e50365000c0030744906440551524403045900c002c102c801c12803400400d200e5000765030024001010309000c1581c1d4501d05116650b001e03080d1406400c606200d40501c60440940401003070400d01a001c90300e46040084c0c09003407030b1a050044a9400c400c0c039a9028071500559007a16030140818002c0c1400441441400d00794000c00c86440e4114000903908520601400d13040329400241040d80d582c0308420003010701210f01c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 581011501 1250 581010251 581010257
    0xa0c030c050111130503011b05091504080111040807080a0c0b07080d1a0315040f020607170a05040302040c031521050106030818030d050901030f020f071a0a0903080610 74
    0x82c090f5458092070009054520a07001c19903501460102410300303441104c02c0c0b1030300180d140300c200c014290700601244d860000458a50541c411800340202c00360046420510196107800841c14180e0f47c03107001041a01d00781c408640e5417594500300c2540d81c5003510802010700d4442e0b00d0400031840c1070809070600307074464041a0b04002d4080481002c90b040005081d4241039a0140300c1c000e801c0510078a030036501f10010003c1da92601352a040c0d0b542e140c2c088024098840080c6050510005180b480441c0c0140019140d072103054003030050550700580003e0348150710b031005107a0218000d11403c1c0d503194213000e200001510308000c100c11030389440585442c0c4850321268000254080c401c40d8007640c03168240980310030750001d03446441d100211146000360301c241800d800058101060f580080e0b001d10303001c150001081d40440207805501c1920075501404107000040040080301103105000c0c0d05400031580d032350408001d080d02d81c1d1620181c081811100407038003a007801040c2020007003043c1 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 581012751 1250 581011501 581011511
    0xb0f090103240b030f2508190602120403020105040c0f0312080703060b0d09141f0e0a0209040f050105070503070e040b240403050105090303070f0c03090e01080708120a0c030c0501 79
    0x140070a040404100380c0d4811900501c940080e16980703400c5141740b40d0146100891b9250400d060a40c0e80d01c460004c034040c0510ba01d031580e00b000134540459122102c008903106e4641402e20b00a03000e40b0080e03408982c40c401c82c18020075800e02d0110030504894102d50360341d0040e64241c50035100c807074003d4400810552601c3c008242814210020000001d503400000354000300e030f00f0000d011094a05c12103943e604041b40c00310f1580600d00300d844903035000c00000902516606146440c00d485402c009400ca03511b6020002401038508068031758034000d40080c003050390380140440d450322040b2100c0001c28261501d0701c00504140d070195051000140c0401c6003017031500840091803c00000c540d50040000170180108030080c016513411a41c154029425802d098034040c0400083c0100f1004011010a0740401c7c1440f030701b004801803030051101c070100e584528149403100818001c1e2050b0744141070000d1002e132648011600ca0410569500104585d11342d0b007110380001e500e0b001c1c0c1d620f40d00d030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 581014001 1250 581012751 581012771
    0x3090509090a02031e0c270c0c0601090b010f0c0c060e0112050c0a021212240a090b0307060c1e15050c07060f091a071b05010b0f09010324 61
    0xc100303205c03020711040118200d9030300c280c10180c84c0642c4141014099080c40c6580c0c07990143e0384803200c51003070011a880b0600d40c1d8074a460b41840c002c0350419074051040b44000100000c03580d1200185850a98480015001c1c0313603c150385640414100400740303040700c54200b20091040101203030703000c0145030200c1105051400c2e8019100300381e906101105002814400c0b054040008800000d102400e0700e060408802c03c1380d4581800400c100f51119030a01d880c95440b141e03112044a0701c0d001441c0545207500c031240b00e4002d03c1141c8480e40a84035050780813521500a0184d03460380765104520710492000c2c1301016100e10728840b41101c40141401d591410512180285881000c20194068654100b800d05906484c0040d41e0800c680d803415015101213111468200070110400000c0c002c103031178224003122501100b070025103504920692a1081040c190854a46d85400f2039030800c0c109040b90800c0211030702844014150341e20044d01c205001041c4183d0000381c42d1011000481d1a01 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 581015251 1250 581014001 581014003
    0xe1003080f0f032d090c0904170a0906080604200f040302030a030804020312190e130603080705010f02120703202b0b0303040303081902040b032203090509090a0203 72
    0xc00c0d0740b06203064010760030ba029007502130100304141c002a0841c220281c20a4501c40b41c50340e02c810185401807001900103018020b40ea500f000203140c40030106951203101301802000700865004034000100e000000c42e0107440c2c980200b4600b01c103415041103407034500702c1d510305c869032020307901c10381040d800d000001c01750f030b8244100c5901a010352a29250b900c1e05104140c2002505d2003500300500003800621041d592070070307049200d01118200300c0003c005010020b0b114194503003000c40380c00d080035030100c00c010114001e801d0a42c85003009000d070100b6010408141d01807502c0d07016800200100060355184a500088120348100e940020b820008034401d04040d07000e0ba0801001c80e541c401d400c0341c0000d4a0400c402e00395107110041110319060b20000352207120b10702c03024080244040102d05402d808801e0382e00703800f00001085682c0c0e90350340c501000c160021a40c02c000009002200d98845502c20fd9051100c1c0d03051b5280d01d84107040804004105101802841e164403850401e0401030318 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 581016501 1250 581015251 581015257
    0x9010c0e0631080312070306030c03081326010609090201020307170d0c0e10020705060f0c070e094b03160b010503010c0509100e030f031804060e1003080f0f 69
    0x3c40400555a07036410344008901110010f0304a20415107030540070004140c198400a040d00c0e403042001b07a84444514521500f0170b40e9410013040c0f00441d45008407110111207038010301c284008001e01105a803030040e030084411444019015030402c02c02c041c00194803040341c50200c035007548a030b400c0400120601044450600c2500d0203e00480724071500713481e0960007080201010301c010f0801c603080034007046807406151002d040c0440045074141124000b8403618003d4a00104240040c1c9415000196214617212085441d0801c0e50710307000d410500044406444c0d1030418024000c080301400003a084414026800041e0005111410442d24281d549015007400b50b200c2502e69410070b0201401c440700451031800f4000204000d18483d00c5001e0821910354545c180b440c50b051030b90010a04200c600320501c01c440c04005816419100c00103070b09640303010b0a071010800e00345c60340d2000c005000d056514460703404190600704001582c02c0000c092400107a1030369428841e8422450700190 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 581017751 1250 581016501 581016509
    0x3221202160503010c120b0f15040f15021207080408011e060b041229010305010912050a0215040305130b03041401021c0c02070e0f09010c0e0631 64
    0xa000703800d0340c84400d000000c0010260204400800c081034141001405662540401641c0a07840c1c401203401c640c3c1e404540c3e00300110140444608492040c0e41006980c001c0c0560311b1074100041010070741c0041030a080991903410b800030840c402192802100b40d8100040c1110081c034200008035482200380a842e003220040c0c0c0d111482000c01c042e207070301030310350540082c440307241c00780810000c44000658520f0240d8006812820f20307800302e00c68070612010740c1009800c00c410407000204100c0d0561081071914000c1c10480c0542c02d001a007200d0b284940e1303141c100180d001c601d00c3c80e06001c10800603600248a4203241c0c2ca03103810b0b40007810807111960f02515000c1408002c100034000380e5000c0c0a240709241008610340600045040c250717030b0b00b698801004658680200b0320150080001002622003240c0f0841c07545004c4942564070f00e0b04840c2c1c41425400d141d03070722070480d0050b8208048080f006007002c2c10601c5918501c11504041c0a0243e00010b4142411070b6010040320900068 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 581019001 1250 581017751 581017753
    0x70c140715030b120d09030f17070b1f1503051504060810140112150b130b0f03390a1212080108100203062e0216080303221202 56
    0x5400d0f03402c104600c13101000900d80d8180c200a5040c03400a034032240c5070041da54820b0071002109428104114070300502c0c0030301c04907140c0c0018424188049607074910301c1812100c070071000b01084250120221140341c4500041c0d001104400070020f8000e4010307a6202000302c1c860911701055000107016230b03806e944403803406e400c07901d40d00c040070750303a40a1840c032050f07402115a40d55243c0382c0010b40d6850003120240004072941b060303040c003541a411500309040003d01c10400d02e102c42c1e20f40d1004082c1d90740014410301000169041c10b06011550482400404564006002c0d5000340c503124000c07545011000410270454103000c660382c61865001802c03030f1810f1804100d055107090f00f01c0f004010221024800308400400c5580c00000384500d007500d8400700941c0340d440b10300100e0490591000400040c540d0307644e200048840ea40e940238a01521582120000c0d25101d41464110105008025941e001000041c2119000301d903080c0790688040080c0700d41e050b0a449126844504104078001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 581020251 1250 581019001 581019011
    0xe10050309011a0d0210090801230a090b04031d030f0304090513080706110f070b040203101a040903090506130501030f0b0325080d02070e0a05070c14071503 69
    0x4900e07002d1055044601d800100541080984000103030880510354000380b042d040182d0071489944554140e1004240f080300074400c0d0502c860791400e03a814881407004107004c0106c000362101001e809881c0d141504800158801c1e00c0e02e440480d61080307501c20940d1500030080080d042c603102001041c1c1c1c240150b40240d5203407800c1402c240151000608481e6041d070030400380002041c031000469051642c0000c000400842030510701ca180e0003400703a0100c2c442c8000c0340100600c1030b80c40180d84194401c9082e03e16600c0890f9100d0100c036060b41d288200b00000385d01c00b83d1141850fa01200c0b409009080071b44d201c581d070790001841580220018002d15840e6101040156054006c100d51480344207002d024554002e40880e03514034164400d40c10140280f600044409001d5500c0c401400c030035419500c881005c108060358a040a1007194181d0b0008030004103446080e200d0640588810750f150384818245843c1c5150f503910f104040c4ca000e00075102c0004020b29040700e903510f08011504c000c14 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 581021501 1250 581020251 581020261
    0x30106050d05010b0307120b0a020c1c0c020f010f05070f0f050102070c030b0601090506030a1a0a060f200d0f02010b03070608150306072a120207181112070e100503 72
    0x208040c80740d44104a00103084001400196903044107561101a0f00001038441c0c601d480a50b2400d00103c2010380c0503102e481a523100cc0d03a000c0040c481c1103000765065412524007000460314126403201c4200080c070288543d200013101403102c40c13111401040035100307021003038580d1400c80e0300040c811101484802d1040042044d49100d4a0384030b402402c1c0001ca41c0e02c0c100200c0e90622000b400b8085071541c400c032111410f90640650508044041c00220255032900800740000002482000103d60a14a4002c40448000d00d002905100380013a00503044e01d242e050340c81c05025030b821030a55491783c45c40007075510104901c0004001d01e684682640c1090780f6501c11106030a00b400d07000341c00c207004000080f504444040c051034510141a031200c2c140926801d10030340921402000744024041503060345a0000f150303815210403c1c81658170f0140c031000c0c1000c54a008a2003031a0311400d01002d214180d4000c94194440c20a0810150343c10540d400540f50700540d0071107001140c03000c41444 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 581022751 1250 581021501 581021503
    0x120509040e1626030a0801051c03020a06020304022e030e0703080d02070c0e09060403030e0a03021c0c08071a10030f0609020109080a060606030b03151b0c06160e090601170402030106050d05010b03 86
    0x503801c0271003081401048410758034000e45540540314013410681c0c0000105045486d010711486020000300742d52041e030b800c0d015802d401ca0300c011a031040003a041c026500b804050102e403450480307034040041494841c41c900200044d41013040140d6401080410005004c21403807001803043c1c10450242410780742c03620300642100c9009900b03803190f904c042984d000280d00090b1440020702d1610403040003c24005003282d00d150028401090148086400c03c2003000192840c08010344031055155503968031400c10020320300920003d0411214045100042403140e0711070780d000350040c90002061a00c60303004625200c100d000444446030744490401000c0c0d414414862441ca080b00030702119003020900301d40302030001c0c100f00c05a000610302008070f4841c04003111040710f1702000b80c500c10b15145886040c032680ca00101004a2141c0d004003204d4a0a03000c0c09225100584400003100c0680b4100141f01400420498140d90b852401080a944015084246034409c0c00007050840e2190181 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 581024001 1250 581022751 581022769
    0x509040510050a12051b0f150d020a050331030806030a060905210906070312090501151505210406090516031704081c020307120509040e1626030a080105 67
    0x150107810207050b5030f4180381d03103c00e040808403004440402082c207408e030103031145100d0070904420369440043c40041c4140c2080181d4800c150b4001500404004003112002e1401c3d4134540c6d6600010301c40b00310740003a010314055504500c01800722015601d0690340c00d8100d1780c154038192026801200001c00c00d440580003043c16424540d0080c0c206442840414414007542d0701c001c0902a8115021008076215444a1403098000b002070000b844000c070820780c1e80d81c1c1e50061f51010586180310002c154081c404a0300088100821107422100501400b604114041d1084804540700c0c00300c00b020900401c9004408003180d9010740b425480c500e05004c206202400e00c11100000384010071414501017000a81c0c0c3e035844540308114551107008a04500c9184001418406a1000440d506034050050100d011090710100300c603452248105a41e250080a110109100403a090281c2807070001d4480c4a84281ca16055450680501ca1405c5d80c2000d1071a0001915040040280e41b41151117 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 581025251 1250 581024001 581024023
    0x309050c0415090b1c11010908031201031e050a050d020c03070b0909180609150f1512030f0c03031e0f0103082503020c09160509040510050a1205 64
    0x1085071881600a5140342c1c00745201d07507500150768003640441911078450714010101240c01c0030300480810b1030311901c2a4000c07003240340042c1c0b501c00d0111315200000202c0302403040041011030343d60301c1d544e201115088000c1061a07402c1e0791a0003800003410402402800c103109002401c3c02c154001c1000b80752004041c41c440c8070740d002c000100940c2c807520045440c004015143d01085070348100301040f02011805610403e0300c81c41c0d08000d008040840c680d5030081c0d04c554144036584581c0c410003c000015036900c0301400450040e10810f1420b00c42260000c6c9140f01502d0901c0d58100c0100d11981010221070b403070742c00000c20426400d0b4030900c0e8050340441c000070692142401002c02001041c140001045041d00141d0030031402d1203418242040c3c00c4903264040c10300d40e2071400a413921101d522840c02403142d60007180c1307441c0c220754031310100c10903654402e0b0404100008100261070060f0000b80c081c40f030743c2d5000c5a0398075a41e4414002c0e20050003017034141005840c0c0a071400c1c008840b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 581026501 1250 581025251 581025259
    0x7060e0a05012003131203090506070b0a050613090b01080f01091502030c0d0236030d0806040b0909060f0f1501030e010b0a170f07080a021e100309050c 67
    0x4001c1c49281e0700229000e103690205100d0894403d00c0003800740c41d51099660420071443c80240014140081d40c44c0001c0c1c82c0c0c800d60b10314040c1d07980d940500c0810f00440c1c41c004d001c01c200b540014a0030701d4640c000b513400640204005031264001e1031500480e04902c006840c2021014010300c0348400c2008144490b031103090082013030101c03030740328007025202804108040b242c000000c200740950b81800d41c2c1d42c0c8081d220085680b40403112250b1459070701c1410074910f02c01100c1a000c880340001a80810096002e006000c45455400046840074802004140d001e80d80b48d100342200d4448426a520840d00b200090138981001d03480000e10640040c181c010141111042103843d42d0407480c01c0b1700c0c4400c20308020410307000c00c0681a000d8040072444603040300e00c88000290880806003841d46145045040c0ca4503d150b207002c098603800280600031203a0310804a8170300504015010b11940604490a034900303024201c0018010400004050000b0b62583c001300e05204040c840c0890b040c104403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 581027751 1250 581026501 581026519
    0xd0504301403270307030b100b1306030e010c1e0309170a14090d030809010e0114010501030e0604081803030418020d05070f0906030c02070803160c05180408131707060e 74
    0x20009176a081240801001e20168401140c0110f03c0d0b0708078080540b038074040c11a1148255a0090444880c2e0310900d000a0308003540304a012a041c404c500d00f07840b40da91a4201480c0035035480070b0303021a103021a802c00d66034240601c040b40010010602c610b01c00d0004c0c0c0d9581400600c01041c13140001c9522400890801603019a50749642140078120341c103041030300780b544e1036061440c0102000c00e482510743d400c000c880800d0f4100040342c0c0f416600c00742c800f0801c04d846009582d60350303441207400401a201c108481c40702c2450a05d480c42015100408803031800d611900030060441da44820040020340114060214181d0381c0686070b4000329500d44040441945039008045e40369511412091541e81d003180ca14030351080c015031018010000c102c0317a0381c580543c0e0034200800351150588444100c404046000c1c80d1000440b2902214032201b604c0c2c41e00d030b5807941480c0782d0080c0c88502204160745000140c0300d0b00300d501d4820b800d039104080e00302d032031074280041d04000c0020050b6100e05501 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 581029001 1250 581027751 581027827
    0x90507050c0c21160513090503030109090602090a0602030711150d0b06190e091602032502090c13150212030a0e070e07020d0504301403 60
    0x18804070002c2003258a40c0a100c0300004910350900c0c11410782c0f0f49406032440d008802011368064000f112825580e032107419810841072400c86140c140e0042003500304100400504030550407045550b409418014034090000c1d000900381500350340504050f03080403811205228040203d000c0000040d1010500c09050012262551013008403c80c5400c0d84e405250020792901e5080c0c1e9082501d408491420381e0014902a00050413581000c3c800d10701e000005001d60707059035007144440310030b400035810844440c0c09500030001010880c05100c0600c080e00000d83d87d01c0d100140a6210441d155903103850004901e00078501d00d03004450190202030100c2200307540051140c0110710307080c0c195034407a1103880040024120060702200c1e00d200f240030101e094005000c1c1c244c080c0b2016002c49440c14400d10090b00c8600179403081d5410314038080c6040c07002d04444c0321032010842c803021940c12003a03807a5444c00341c018240004c1c40525400407404105101c42489851211801000151003100c40 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 581030251 1250 581029001 581029003
    0xc0d0c030b0a06030b27030a080115050708030112231e07030c0e0906010f030807080703030b0301050c04060219020d06110c0d022113231306090507050c 67
    0x400c0c40000c250107035400c0001d400030000c1e841a0091580301e8030704441410580541d49a141c00d440d03105d100010300c4a034400703c0650000482d4000d42c0d0584441c81641e03e400d4641c15189040040303501880b0701004000d0000300814000c40c0a01602c20b0b148050744500d041114180b00c80600041d001102810002108000052a40c603180113512080c0443d078070943c98a410800550705c000c0c24030030343c1e00001c10745502803020281708003140301c00c9400a0b0b07a10300c00448003418901c00a0445a010081c15021070011402021030030f01034140851960200c101082c211202241c210100070030104080c000c00c2e0781030041170440c00703024018440b03107800d94001a040600b002002001c9a95814071610145404016503240d10000345c00c0e2980420b00c268080c0d10f8080400c0c1800e00000e103061140e01d11201d9000b0703a802c0300e41048072a1849401d0030f048159142c401c0140145140c0040c005208170340d0790300e00c8076417100d508120101c1d070300385407245280c03d940b0060240130a000040c00948c4042c80 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 581031501 1250 581030251 581030273
    0x8030916090213150e030a0503070b06060f0306090a180506041407260106050d151b0f08060307051c06060f06021b06042c06040e07090b0f04020a09080c0d 68
    0x20b12405640c901340030400041e5240e40070002016054003e0707410401c20b0000100141c6003548c042c00160071103644007070401c1410711a40d82c1c1c81029240500c049400e0b400c2491500b80d010846c00c40000d02e8001d580044558040407a00880d21a40080e04200802840b002c810014010140007480c00500301507240700f0b01d180d40084208980301d8000070665564094000d01c0007080c0142162000d40d00c24101f0b55040410702400f44101401c000c10b038414410103480c0d020180440e50744011800c035039003400315209200502000e6051285500c042541d036110003401081502000c1341080101491030680143d0300d640e400401000c070a1a0308201c10b0760086491103089030300230071400e05458004001801c9021329000502c061182d04bc0683c080c0121028407035810318900c40000d6565a5801008240c1d01001c0c101350741c0e500303c01c00800c00030040d900710300038010000b0264030282d10854040b504a0700442c08040c005403000303204100c015002d00040c03183d041700790349600303002d0303510349507044540 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 581032751 1250 581031501 581031509
    0x60b03010b1e010c02060706060e07020c090103080d09020a051f0e0a0b0a081009050c07150605012703050105040c0e1005030303150303070f0b0907050901030f02010f0c08030916090213 81
    0xf1075807111210841d078440003101c87c441d91040c000c000e255101d00b9281071005080380c1090140c4103240011005103860074500f0704030fa80c0440050716140002044001a0000040490b0445070024011401e55182400108841c3c03402c41910560082c6076801480903040074042030050300500e000b88050000321044800c14000c45c14050440c1e1a401c1031a02886086e912800b101d40ca45405c0c40038030a245c000400f2002d00030651862030484c8020000101d800d130348520b40c0410b8559221011031411305414503102e40748103c00415680e52502d443e800d5030003c407000c0344ca0302043c94050080120802c101c0d500211030042c0d000030241054080383d03880c4006060182c0c5650740e002c990f40fa59500b04215103803250300c034515104000e40c40c40c2151440b80203444e2160940074410002c40d280c00c2020b01e041c100c0b0b800c42c055410070302c000c2d001541c2039100c800710038040000c01c0089402195150f0021030095410000500284102d401e0012006002da00070400c041d00401c043c80365501c602074082c06417 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 581034001 1250 581032751 581032757
    0x1505031015030b04080a0f051314033406020d21091406010612091703040206070c0b13240806030309100315060f0210020d0b0904060b03010b1e01 64
    0x1441000d020900707901d030720080210520008002c10050800042e203000c0840b0f44078400041e0960b0010303665801035a42da4860034000d01400c12000c004c00e510a0a0650302600791245510744501032119100038040001c00690083d8000003600c410040701c8005014a1000d000c240e191580001c00c0507649150391943d81070441f02c00e8005244640c008440182d200d00108252025010101e444d6002446010040391f0101400580f4003103c0c020b60700001d50102078811081d05010440341c0c9500050801e0f070b000202844542c0001d1205011030000c1c2c44102c000301e4507040c180d402c3d03030500c1c0499003201031340290015260803010102c2000c80b00c001901d0504249540d50240424a103006400300103501c0340d506407070300102e660164080d40b003135080000e240a80c40d4a4502c140e035a000c43c840c0e42c5006030b01110100d4140710140e07025040004e9140c9010480c0310403100010300c0c0c20301c1600d040c0c40140d905c0d00a0141440e00b40709002c82c846c4155200c5042104140c03d1401d280351103142903041c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 581035251 1250 581034001 581034011
    0x80d0509031603050607021b0a0b1309090516120b0c1b19172a0319211b050a0509030a0b040c090e06010b0f0d050703050a15050310 58
    0x46030340520a02d6280c0207030540207410b00d9a2410b204e56908030a44440025000f40260150320010346030a544083c00b000e8031014106190290107a015130048605a980c00380c0c96901003101180d900445c1d4503a070145008060b8020280001e50462200d41e104405002111410000060010114a134064802d0340d13481e0325080414002c640d0140e1481044840c0d00841984030b0382454800c094110042c003030f298170080c1d00801c10125880d882140007144a40d005030400402c47d8842021005503640484250390030600402c3d82080509400e40d0700e080407403144501807500754024000c8030101e540d290000d01400b40c80ba9090072688007000340d11400c11900190591b5224090310407644001409000c6414030351190034a81d100480c140e4003226201d010b8940001c290b58a400303007102101c0b143c00540b0b0541d10b000e031040c00d59445060142c80ea80801d000d03071032501c40180300e8a0702c108600d0714080fa01e49820141c51045541c40c40007070788100300c19441402191400100745908124400000171 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 581036501 1250 581035251 581035267
    0x507020a02180f0a0c12060314070e010308221a07060c03051015051308060103031733180f0c04030b010306200d020702011d030c0108060a21020a0b0301080d05 70
    0xd080001940180c46c0c1d541094000001c2081c0d440720925003803030074002c1d1600d080e2550200c0d03900c00401c1c40080c0c00da00341440501005801302c440c0302c41c000122084022400ea44114581d110350035140341d220148004038101e0b0034000d0170b020308a950909403408001e949040200400d1060942c0070301d2415009031845400b0b128010b1003100c0e8840800301e19040d206a03078242c4561303240400d001c00c40000e1030301400003c0600c0c90f2081680181d42a114481400c0050000f01a51601d4144860701030841e0f9043c00c0c07501d03111071500821041418100b00041d1601023544420b9030809004a0b030b07181740411082012540f901c0c403480c10360307038040c1c0c0100d4510051000f011507651446803101e00f0900004440104041c40e600500005200781c07070702c0742c2c540c1e1000c00c1c0c1a00362501e08030b400e82642000c2e5033307558158403803140164450801801c100c02a9100c0307000340700c1d1490615000d0548525900d042e0258034160003c50024494080c021b480e66040030300c481c4c0c0360307007915801c2c100340180819150 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 581037751 1250 581036501 581036507
    0xc0f0f130902190b0d0c0203090a0b0c010e060c070b04150c0201050f01050108010506040b0c010f0c0203130506030f0403030c03270b010806070f050a02070e070c02120a1110120507020a02180f0a0c 86
    0xc41c15038000341108030107070310703441a82f44586c8201d0701800030f50310b80b00402060440c0415607600c01c040c496441c03400c010b003d4440c403c0b4003070010402c59031620710400b60090000b1780d00c1041491201513000240341c4c500700410203401c1da0b0607006030f81803140d0310004001c540c1e60700c41201c007580c850f120f18a450b05242d080c6580940303040f4500001c924144142e001003558004050a01d14013a242c03001c011580d02c0c418040c03580300a58010548030701a00014000c00d0194010b02c1103140f061400041914002c0c140641000e40c64180e541959486d0f0f559a007400000002240580465000b0741054100b8080150030403c02c0040402486004911380750001d000340b001c0360007008401c603845220b15048100514000101c40c0480c80f554540b110b1400703900c00001c0c8807041c940d0140a054034840c00c00100202c0d0100d01c0e000d03004101113408213203460483c0c1d0155034002d8105030020302c00c0040a00c104000805854070308400d1500d0031040100303d03a03200401c0e580103002d6030000500c50202d03880c22 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 581039001 1250 581037751 581037757
    0x102060f131b0303081608090a020609031525080f070f11152403100b060d060b03270d080a09060e0a150b01020c0f0f130902190b0d0c0203 61
    0x19100d4840c10b0000100345600402a01e00c03601b6283c110002c3c40b80140e105984100c1c080e41c40e20f1a681c410605880142000e070000e180c01c21000303086401040d2000f0340d90072804011241c40d540d5607003200c0c4228505242001900da890b41c0c90a2040035807901c542410a0100000d00309420400d13a0500c001c4858000d000d84101810b1007400d8036182c10000320100764003041075940e5203c0c051940d8039107005140d2081001c140c07200041c00b43c03048a11840004024102108880c0e502c40030400c003141840c0440c0c85400002c042954050343c4900e014408e0741907844584420f209880704910884003105004162030500c0c3c640e41c10b00440300d0b20f0300b090350340c003d01d017001000700007a1400d000c5088400001a151600501c20a00f00302c01000c0a16a5400c1d0360380c142c03800c2d026074055018000c0500c0d0200d0b510803c10b00140900f4a204604030000b0000001c076000c907110207545000c50340550801c005d80a032507060004c50034019501d8403110f02d103144101d51803180d00c16650111001d40130710900072 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 581040251 1250 581039001 581039033
    0x1a0a061a0307051e18061c0b120712050c0a0b070b0403020109080403030816210203040f0203070b0318010b06120a090210021515010509100908010204030b0f060102060f13 75
    0x35000ba9200c008400706500001d171300426100c11207101c14851900c0c00c02c5a14002ca181001c9014240d404a251302800c2050340f820350042c070010f03c1d10001d2200304481001803460258140115803070303062090420b24030340c000c6401440d0402c4141f000c0d0b01400d0031a602150b101d0413a000310f07540c5080403030041003003020040c488103000400106160b070081216020ba012024500e281d610072841c2070b0350280742d02c20140ca04012040803d00b2000c0035a003d154006c0c091301070b981a0000d198000390031b00c3c88941000c01124008800c0c021044100c41c3d0540a40140c07000800c000085070000442034004c044195440c5a1200c000414002268000740c0e1455070107041110816507002c0040d458040703800d0a18a00c99691000039000c10300c005070140114411b1711164645028401071103040c2c1800070003034080c802c0d50b034000544e0703603801d10003880114000c1008480606100c0c00b04007690001034001e40c11507101c0820700080c4e480000f403060300214649404001e0951511b071160601c134070a40 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 581041501 1250 581040251 581040277
    0x18030d140f09040f06170c010207051905060409060614070209060409081c02030109111810020703080307030f0e0c33040e0a060e0c030a0203041a041a0a061a030705 72
    0x281c9110b00681e0381d04a401525a1401000031a4855440703040d610202c7e0500c02d80164850328003084981025980026414440000090155111000b003115903100d90300000300f840d99800100442a81f05c0c2c02100d54051089443d0700d00000e07500000d01500340030f011036204580d40c0305050200010031040380c0d038200700740c0c05070300c00480c201e0314083c02900248110029241400c0089081540100484884042181c1002c1c04001c010043c45215504100c20401b03512a0420100c040740d84c1d400070750302c20041039402142000709000910b0964010101cada01c1c15a100c4245088960350b0058250000e02c512034070a48880e441b16049941208039190110340c4800c0010081402105440c0721845046015030a00904e80e4501c680e1000c86001c50b030000600c24180040307109110103800460300940183c14071038903071018034510210000184c070215415451418104901c0d0b0b141100d5660004141d001004514075000072003104010000b82e1400c2d03d000000050b8086004406590848034603107 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 581042751 1250 581041501 581041511
    0x7061e0305182a04090c0909110d200a0e0a0e010219020105010e0f06010c110433080607090b13030503032e150309051e0318030d140f0904 61
    0x5540800d40c0c5003c410f5450361848480915141d41040d010b103000e1258014501800385107060418401880c52071400c6035850006466880b85d9600c020b0300b1080903000e611284059080c00010341580d40750b114032280220b81415042294080c55070441d0303442840b1850224a04013040716550080c0326241012044821188402410701d07030543c045410f035581d41d01800d0007600d420a030110141422500c040c00100a20500b03000107540c06540340d6400320183c000704105003201000c00c2504c03c5c00b4002030340c203544205c20241003048510040b0040405c0d4000d400c0500344508020190350141c02500c03003a0034000f40a84c00900e0200407580150f070041c094035240c0c10030315017100400451144658854000d0002b8070b0441070030010f65004c41c1c0e0a42039071045030400f007000398091b12580c501900c89010b40d0102c0c2040549881040d1804c60001e8080e540d5a1916040c440300c5415602c0003034040e034445429403d4168104884803c41c140020301d03981c5800400d0b00e07404607485422040b540242c00c0c1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 581044001 1250 581042751 581042773
    0x3180602031e060433050d0b1e0403080c07051f0e101506030506030f0d02010219030e0c0118080a080706050705070b0a020306040906020705030c07061e030518 70
    0xc1402c0002a2105014a032260f280d81c010002500d00c0c0806200e4442c0c82100c3c3e85280030309003044401e9015070020740d40b40d000d940303000003003941581c1c00082e0b5640c1007020820880c4115080500f94801c651a005d0b0a1070416031002004140010283c554100c800a0414203100040000c05140150300400e4203006c817000907002c0c0a0050070303007955044e10506c180e292001d406800752544095010710540c00443c5001d0048010f41000341c91070350180203000303042510a10034032a41c03444401c2500056580c2d07201403101910b80c0c0641000004040c549801c4c81e00c48107000c2500c6103800804d03e80b8000246c0c4c2d8070000c511000d0f040d404801c2c28890b20000800b041b40003000740c0f28141c083e510810280e5220a420703103291180e0a030013490f201d44500014420056580510b401560140c8005204811030b9a040101d0340301c1c4805491a031f20104850a8018040061038054483c52a03c41c151540e02c100003643c4140180000c818103440e100040e600c04107070b4080c65032400c0c40004a9604182c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 581045251 1250 581044001 581044021
    0x1b050604050a0507060f0e040b01051c0b01080a020903060c0f1306020609060106080108031902070b0d090605070c0f030e0301090b07050a0206101d0903090d1505090118030318060203 80
    0x1804021100c500624600082490042d241400044501d46070f407d20143c40208010041c90a1066075040c08400d010806001c0c01c0301c1c0b103020203408800b1000460901d01c20014100010040150600c64010860484161000305500c0d8000e0300d21034040f91140403540741a20503001e492641c02a05111480c0001c49680c0018081d00440340030050718902e98858404690360282405440340700c0c0d0040140908000780228001094419031041c0d4480c01d0f1641c443d04416030160702d20480d810703103030704030382003404524814a40c11a142c0e0a014192850b20360303c194034012901400350903c425030a451109450a401084615030300407080001440c2544000d002604150b00c40d400610030b031400118241400001031060762401101130700c3c0d8400e03a440c2c0c60700c803000c010175110903400103019000301d03a00e8401409a03041c1c4641d03284110060203c04a00464a005040c0d1a80368141031031000b41c41e40b0f40e0442c964046d0107240104040719440c043e821080c03a501001008203100000700b245d0015 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 581046501 1250 581045251 581045263
    0x1020d0309111f0e06040609150306150c0311010507020d120b18090d091a0a0203090909071701142214060604150b040905130501020705060103230d1b05060405 70
    0xf581e25072104082e071420034130205024502404000c108107040901c5003145401c0148411700c0c0310319010410136140c0b008444111402d850303040c08114020300c0c070810103400c502400b040d1040714008001510b0b1044c0e009540f6000103031108103015a15251040c0001b0302d4000c000c3c04e6a015002d20401681ca00c442d01d50380d842103501e0344407400740445e042802e901c0350a45400b101c0c1d201601030b10500d40800920207a80c0002411400c0d072100700000c082a48566a11a1080e01c169016040051510980c2c0682c5400c40320f00416691401c8003505002984d400d400303800401c0943c075040c148245040030706840c0c8490602500e0040b0300c550704524000001500c911650003600c06011141000e9840464240c41c0d004608e105001840141300072296584003a9028519081035001d2500035140d9600720f84c0818020354540e00030708014000e00802d00359146e201c0c1070842c20100300201001c0002e41310700c0d0300e07110401041a600c040400c0000c0d401426042d40740c008040d5002e03420145095595a0 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 581047751 1250 581046501 581046559
    0x140d0f140a0f112d191202070e01030b1008030c25090518070512151b0307020601081501030206160305091530040609020105120109020307140901020d030911 69
    0xa04824161340e2001c008500b0082804a2850b00000e503a45541d42c06060303004180c0010452080d43c800186260f0040c0350b550007940600d0000c401c038203125900c40d5807130001e50008d22440e8010040820100e0000545108021482c0801506034481c4003203c2e45415456210a40a03420300040c070644094008007124488408000c54046907030300c0703051042e492180c0410013416040003102c060307100144145694041d8840700d04180403000031480b0560b0ba082071f01c8006c0140d020300300500c00444100030100310340c0f000d160381151944c55603000603d103208409811064503280e416500406000b1402d950f40c4101c0241801107103501ca021403074054015038003115040c2307510881030644030b5940a040c9000d10760003827001c195958545405014200b00841241084010001e5520762059460054041e01d529600980d0300d04000c0c600600c010402a2042c040c030b6420040d42e00c540c0c5e0005a003014680681c100811281e0766802d05207901070303a141c40507402000f0202d40401030150308940c07414030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 581049001 1250 581047751 581047813
    0x1303023d05180d051c09020a18150b09060a0e130212130b04020d0305041d01081c210207080d020405150415050313140d0f140a0f11 58
    0x3200d103100c5220f40d41c0c4841009803022400030080c50411580c94600c03403c5e1031000c08000300c1c541040c1d07030100318000000c0d40102d044901d00c00108001d007005000d903203500720504881031441030404000700442d1041c507100501c20640041c0511b03c240c010301041d0908000144142c5801c60880d4041e0301135440384040c1d0401c3d498a50004020114503204041c0040c0c00031198012541c3c0d030f50920900c03840c00c2c4002d9081c07140911000501e0401c03010364028401c0c0c0b60780320100551500801d03030700e4082c41c0c4c0045002d1414920030100f40952203000310350708801612402d031011151100c900000c0c400e004003c1c2403441d0015202d0001203840c1c0080c0101e0700142e07400c2e025108800300c050058083d40c0200c000b903d6a50f10600142d038402da02071500404440381d00620303055265180029070402c0300384580a500409800e14680c1c1c3c00042d116405c3c50a810001c03132102000a40703900d41d100300740c10b45040c0207150800c510707151310030411102d075041c911003125090301c4500007081c1e688189003040821 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 581050251 1250 581049001 581049031
    0xb01090b0a02030a0c1a04111002120a0e0612040809090a02090d0206160804120c080d02070519091d060a090c030b041e05070806010b09060304030c11030111121303023d05 75
    0x55403000a2841b0751410220bc0c4608000c071080341207900d1210361281a502807410b00c41950408150a0114092031003201d41c50707500e505120070302680040003802c1a00507403051182044d87d03260780306803d03540759040303e5299640b810702c82c14108071005500090402c0384007040c045400004456400307480f5008007a4855801d81da07980c800e50b900b420200042c016006282d0410150800140c00e1b1034071100c00c2e9450010b103842c0c1c000402110303081e446c0c1c0301201c1a00302598900210501c11140c011481c1c140038040c0e56040e0329504040131161200a2602d5a00760008040c04040d0740071550f85005110440301005080c1462580c4074181d01401e00e0501401000080c03400809048401c1c0c240c01914060640da80d03610240c07840314880b40c06880c01307031800c3c034180c000e40d80c203118a840c0b200c404a1a90745400d02c0d00000c00384990001d00403c06114900e0240c00401e400240d4103108050025400f03001881940988c9004a19008503006103511582101d01c1e100c1d01d45c0146100b46038140310922 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 581051501 1250 581050251 581050279
    0x60f0f1302180310050144010c1e0504050d020301141e151e030f1c02070e04050618030c060109050114030d080a0b030c030a060b01090b0a02030a0c1a0411 68
    0x30417600f00b8030600c424031075404500510444038540303103188012140c40c1c0c0b4520102c5210740e002c80070940310340141c0e681d6565408500031500b000300c4541448000d804650100a0040050320030f108601a00c0e214801110b803440031981c00f5000140c001c400d21070035198a0030116080285214002c001a46140040c400102103140c02081d6003505000141380251203000c550401c0312078454041601e13018000c403000345003104010040507400c05001072810100310310800c00241801200d0300001c0b8010400d40a00000c00c900040315a040320103400c00c010700c0850f0200036441e51081554210b140d005000c00000d210707400d40d0101d0304942c8403001000700e0b0710710401007646407c81d1500d240e01181c681e402141c5010042d910480ca50103016040300c0300c1030070083c0001d2520802001c00c0f9030503911030b070040e030303155900001301c00c001c0c2401d00d80ca40c10800004000384d00c0340200a421010044803110701c0c2c05200b00c51a142d81d200d807040780001c1e094101401c2118034802d1801c0700e54007440c4045c1d03541d1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 581052751 1250 581051501 581051533
    0x9030f0c0315040f0b0709150e060d18170a0905030334080d0621050a1b0b0c0607180509062e0305011a03060f0f13021803 54
    0x18244040040c054002440d02c070b1140e9105902c041c200b61040a4003074181000501222046400740001ba112440d4103440d02da83d444210103100714050030842058501c03441900c1d5642610703200c056040740454502c100001001c240703145c140002d002e21a01d01080301001e42c18034001d08829040f41e42d54003102d0b0f00c40d014140e8070711a0744002510310107541020b135015010040e500301040f0a40c50710500550140c0c40d841038542005441d90038240c0d444c10108143d001d0701c41c4810340f001c001d8444003401079940e103815441e4110100080c00360528440100c07d03060b482240c94020300181c4100c2500c4203100d00c1c0140d5501d0084440d41c0204a40701c80d070a03a28842072a4107401c84030007d1009550385e454806010000c40e0100544c024076410364800e031220401d800c05c0c0a04003080c1c1c1d400045035850326044c40b82c40700b01c8450000c42d01a0030018014a078840c513840f024190025291401740700094804101c101906209c08051a440800d02e0600c0c800b000e0743d482c0c500b0f07104030200c03120340074034841b49 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 581054001 1250 581052751 581052763
    0x6081e040615091a0301150503100b031009050a020310060f1406070605162601290f040905160503160512010e07080703060f210c0b09030f 61
    0x100086481600014005010303500840081d2440101803480d040c0c0c0c4100c80c0081c0d8080c1019003030b008160b06414070b0705040900c00c1c03101000380c100000c0c400314901030100307846000d2503482030242d40d1182c1810040ba10704001c0c10141d811400000c0000984c1740c100280c8a00104008174400e000d00070f58401c0004860280c1c0301564000c610010016281042c4440340528140c1e000e40c000130300340301280218402d442210b21030000c25100200800796290014507403410504240745050010b01400c483c0e00306110070038107440078078401606400940d139007074a0350035100080743c80700040001c0541101c0c86903c06081200c0017a40c1c14485526001d91002d86803c44030b10920010300c0c2400003a0301d021401645115400050030004d1500b5210f201030002e18500b604409803207008401448069540100141d902034480d203010015a42848000c9142c1f0f007080c82900c10b08840580c0f4810306890803014181d0341948075081d0040240c0c0e5456800c1e29803c0092000e201e4055201c2c0424030401c0031441d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 581055251 1250 581054001 581054041
    0x301150c08090409050709090c050901091e0c211521030e01180311130b150c160806010807050307060f030923010e0124030803070509190608 62
    0x10341400c00381c0040c1403000824a000045d1503600c50780200059180992080384c03e0359001d40400e0780040e0404080c04818401030b400f28040510780081c5896142a410305445044101342d404a08120300e000b04031001544040e00d041c00141c0440c0c0d82d0520040c0d40c0c840d207260850002780c0307a899540c8101c45440980c2e481035450302000700c1d080d44800a80704030f240020a550505102c0e44a84482c81980001440c0303400c1190301000c0404070010700d140404070103c80e03440804091044c403400718046002042e4654880d00341400100e40b1a00805c81480310450311030503000d0310201c00e030766084000ea03600c1d13003880b84144d01e004406010805043c04101c1c0380698505803510324040c030541d40d00328004d00e801801511000e1015600580c07900c4e90f041c1485e243c0c01c1c2d4100102c0d13110b0000b0b591600b140c600300e80c0c0d01da120f54032117000c4220729610050041169005400540c4941d90310f0030903540c91040104c51a03002c81d030004819858451510300000381c40e21942c80d40c4181d030b5a0400150b4249080307031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 581056501 1250 581055251 581055263
    0xf0e1b03030f0306030a080a0201090506010b03091c1407032106060504150e1c0605160c0b04060f0501030507030b150112180503040b040315020306010c260d020301150c 74
    0x402620807921940c000c5402101c042c1c00c5030181d0300b40d1f8075421200e401840c000e1006035103441070396050100400c00c007030140000414081c80c2d0b0030800303038072580e40c007401d62034041c050012072000c500c06001b61800b1000c141442c003441d548811a2900600a001c6020030840800381c1003165488501940320741c1096500d180c03203540c0b4080c01c0440362440b52204c0000403040100264840340c2c140c80d96501e49c04003215040c000040c5041c6490320406a0300018100011440c2204070340c94082d130b1100c0c0308007038260090010100c580703490034048050041c8450501d01d080c18074000000300f00d0005080340440b03001703144441c41070326002104017002d0110410140003075840b609200d074101d020361043c0840740a0815001c1c2400da207030b03a020704641103036018011202010604000388451050000b4090f44075541c21891881d240c030000c0c0c40e40300181c078003800c500c40e80d1030702000d03025109500c803000d080c02c9007200d500c40c40600180701c0654001d0265480310742c081c07051514224010445814110f44c040303 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 581057751 1250 581056501 581056507
    0xa17070311010b010813051f0e060601140d150302030d0503041709010905060c010f06090e011104180506150712170f0f0a1404050a05120301140f130f0e1b0303 70
    0x3009403811a0810007d9075a402103501c00c02c540c07500c3d0308056a10258110000ca01500102049800c00100410003030501c500071000700c03501c901790b0080b2000a020401d00103482d0440e46580f94002449800c02500761080003051070300c0036040005980305510548001c02d00d140b00069042c042d008840500d0b0220703800a4043c411440c001e4040c02d4001114000010301e000d01c502640103840c0d00d6400107000303558601c1d00f45800c11080c060040300002500c1c7c2030346024500039a4903000c0440c40581c025242e80c80c00404e115a80b40407480e40360300c4d01c1c44450354881d180c50401e411038880c005040c0c40480d00c0000000380000d208806c41e4403c850722030801005540d5400b5000380003000a0031a030b00b00d5542c0300c0011300c44a43d0a09079000354002c4008000280c0b1602d0b246280550441089540c0b8005000400462803640d9060300c0d440001c0d00e4803100b005242c1c02080c03c802707204403010340c1ca034240340303a4080c1c0d05101d5001c02d1100b0590021030341d20051100041e0301182e06200ca45801d03070420 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 581059001 1250 581057751 581057761
    0x9181101052d0903010f0b030f01092a03020a180b150d0b0a170709062112021501060503060931020a0f03030203040303110d12050403020a17070311010b0108 69
    0x3001c0d802c1d06150786404040c98520030b80c3c002821030b0f034109140107105944818055a07820100090420806820b000b0424581551a0000702c0070306802a030300080c40041002c0c4041d48000341c501d0086501603c02d0044985039a8290405086004514115460807440f640645084107150061030b80541c2c1d114075004020411602619411100a4002e144c2a03030000e079640464520396104c00e210805005a0740c1404140b00030b5503050380c484820300b01a040020400d105480c02c2d500190340c0038400382002440d5400a90500320582c2c0c44204d4541e03d02d00015040350054000e40c41800c2c101c0b4280c609555691569101e034126600c00e0300c2d40860481d03034080448000b138480d1000c6000600810000742d5407041511031401d03d8004a0050b04086070400030180c100e0316005c4607120f9403028062600741881c0c001d0102820601440c101030710381c0c02150606009000104809821041c1502d0402654442031510703442600c08a000072803031441440275a0b81845800c807103050503900c1d07180a0701c0b2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 581060251 1250 581059001 581059057
    0x4180f0327032a080714040f0905070b1c1803390f05030a0c1202070b032805070e0a080721051222120b01060f03060918110105 56
    0xd000000c4183c1e0500100119083c941006807400510180b00041000a018000d001c1070b01c1040c0529012141050401e0b0001070740410100f041c0c0702c0b981131586d01c41c51455113414217141c106078031400d124135104601102403101c2240090150180d120080300f402002030000d107507400f0b22240c401c2200d925149402c3d4030b41c15126425028002c5100502c12031040d120789055a00020f114004500e4441c040010481d00542c3e003c40c0401c0d40c00904452441c0510b0030205100041144581030350411306000e10500d0041c0300700300e00d108800708100e1407820b038402a00d98424070f0380c000d203c0c0e824480000791840000410405540c020140114401d400300300c62509040a0301c01120345000c5d4085420b24001e590010700101100d20040300c40e00c0c001822a41003a03042500951601011085800b0100714000b40b10390440c2c1240c6400310229944180440c01820150001880c0d1801c01c004284a0751031001090300301070050750b1080c016110040151400e2295040b4140f14444604002800e410 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 581061501 1250 581060251 581060303
    0x1030c030905011415060307120b040204031e021203040807050d020607120306050405100608042604240201090c170304030c080d0e01110c04180f032703 67
    0x90141008201d032007095440c03078207441d900e0f038044010145013030802800e503024204402041c082921014510304000c58001e03c010040f0801032102c0791036111030040c54566504840095400250704000c030308800340d04403111428224107030b10509004404144108010084a00f140c241e000148007092502c0b0600c0b01d540b4407220103030380c0300f4420300c68040422043c4101a200942c0c42d82c0029072103060008200841d41c0c06801d6001001c0b803900d041c00340680090780580c1054125a406c0b1700004070900b011915040481c11510070400401c000a0800c20f004001c460002c031450504805002c00400702d00300c03080010040c0254a1226080041840000b1211800364401040d01c1c40d00f44c403078480055030070707481e440070b4919400051844a243e03400b03a2040380c3c0316400d03e49003150b074001c0a100b13076030343c1881080d07180b20355503a400640d024011212980078a0381d1100144440c5005801c0142010f60b03280451440030b201070300300c00102c0c400101414203403544800d002e000b05c0140324800b0003000c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 581062751 1250 581061501 581061521
    0x6020d2102030106090906090209010c060b0a050301021605061b03060d2d0210020c011202090f120105010e0108060403020a080307050903070e0604061202060412080d0c020c0a230103 80
    0x100c0044800103460080d000650282c455500d0310590585005030800c21100326600c4170708241e10600c403540c1641c2c0d10044462980d90400400703d61405100001a2070408991115074198400956150702107030006c05c101f407060098050741d020350366030740b0700f04100c682040100b507204908000141d080c3c9404000d00c007840e4041c01c1184551070065403030400700620201c090390714010b400100011868190304011410140340b0182180302c42d1100080d1581d0390200c02e0783e0704a600840d100ca000e0316201c240310f1480d000188491070800c05440101d00a10f070a015101041d190f400000c2180ba000040c044c1c0070702e6050b4001c24241c001c0e9292035034143c02c0171300b08408120040000c640140d804005035400391900144c5840b09003004001c20044840c1d603480503000d184c0d070301c9261000d17075500425039040b9480717100c00c814417071841c0c64113065a100e05c600c0215114a840d1890303c41a1707000a00040c2c020090b220791441e181c031900c80d900007444042620001590080c400d00041d40b090b00014040 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 581064001 1250 581062751 581062787
    0xc030210200a170903060a0b060d05011d010b0304030509010509040603020d03121a0d020f012303010501090501030b03210408011d06010b0f030f070e0a0b1b010606020d 74
    0x1e180484006400914918003a0080c2c0c41807059005001c05124a548482840c25240b132801c18800302081d29940020100d01c15550703a00c1a41c562619401c0859800c16810203040040d985c43d4a02441c4608134a00c1100e2003089000c000b1501c3e14544044900860f0107403a158200824080110360681c030680050f40c20070b890305400801600e5442c0070a1803244640c5400001c4d420440202040340c4001c014080080b1844095030320315140e005040341010f4042d94240c5d1480721050050b140340600044140c504401640011400b503001405541640c0c0241d0303800203920f0343d802c01141030355a03501c083c541c07507004111604504501c540c04060004c04200b0002d040c541d4860303000c2c1c00c54580f05d5040c07251118070300380b5403d0b608003030100a000d407810b2070400e03052115410813070342d440c08018a071541c4045420081a00540036946400521030300505003608180c540108d0304e10340d04580308100800040c0f40c01c02c0340c52681802400d0a55665034000c08203105220b90071070708028181206048 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 581065251 1250 581064001 581064017
    0x813080309190f03180f030605150603190609050105211c050702270c030c071b0603050f1b0f0f1305030f0a120f170901051f030c030210 60
    0x10b100c09224020880e4000c80e0040d1030942e25080282201c400031442d501150000501030050032840e02822041d81d4024800040a43d1480117101011094514140d030044000c4100480d00313481044a03034480e0b441c400140300c0165940d040310260b4a003801582c0c0d0003148031038551500119507001050514400080f5210403041a00c0b558103901c1d000b0303088000031000251142075040c11104080c808900502d00c40220080581941c91084054112854154000003084100b85024145c6040381e80040b01543c111006808030601c1c3c10382440780780040b9040c440059070411008030175034407410f00e01c0d03907403c00c030f5028440129143d40403840840e49014107205003440c01011902a10045841c40024111076040408161070101d010440c039007a940000714400015076128000010711000c0d00301148034292001d0140d981c165812162003041c3c40390700c00c000e240b1205400141c05a509104004c4409030b0904013114406050f00028000c2c03111184100300606107901100c500550501c0e003485 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 581066501 1250 581065251 581065273
    0xf0708090a0902040906081507050724060e060108060d060c120f0e1e0c091003050a051b030c1c02010c0210120507080f0403120f060f150813080309 65
    0x101d14250b5045004860740c013040038405c0b00c800703128480140c03026100030304261120084004040400401040c10000049251000c0003080030380c0f86181e11828010702440794091000030010035061045401c80398203e07000c00c20b194044c0c1c0c00d0380d010b400041c00440b070814068503171070003401e04001100100540c1d4410716400c0c020600c10744030154042c0901164080c4c0d0840254501044405a408854007600391640c0441001503038024020090707a4044407075450716041d070444984c903030026005000c0c900406082003404a40e080300c1c0d0951311502541c58810300f061661f580108001e403904103158005410381c3c00b009903844480140305240c10862030015070302060103000c0700131401001c140450304440c55142c030350040700d90141c520f2078400024a0700110804035880090800360071b00840304440108070303e85800501841155020920015030780d03072880707e0b658040e84176a51702c40034444041301e119445450746034022854030789244203140d4a42c03510495684083d040308250320130740214803 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 581067751 1250 581066501 581066509
    0x2106180316200a0b07060504020f0402030f160f09090203180a080d05010b0f04060c05010e190c080f070e0a0b0a030305040915050a090213030c2601020406050f070809 73
    0x6002441030348640011010444410600d161902d42d0341d01c0748501c2003007484100d581409a508071500302c400440c440e207981c008503010354a910324081c1c120b0f000104101d104224464402c0c05a02c0c3d8034042c50003034401c450100c0e0400364404001000450050742000486c0035074010303580000c0c0c0c001c3c03285035885018100c0b602c1c0200b0b0040171510300c100401c1d941d456050521629004007507540402e45000b072281c1541c00c040c81180940414802024601402c1c8042540f0200d584005581120343da5020b005500070207062401701201c60340514400071030304110110340b001144103428020700c0d0041c10041c1c084203d07039004050509150351490a0019681c80d419618000d500a844041da982d00701500a402d50f000700c030001e8030f02e0308803000070003094035103a03400400c645e402038005848815414800a409910368009000441c549401003a295001181c1101e2018800d00480c500c901846071b00d400c2c0e0069102c4c103004170342c0a0140d5a10110690010000e152244907406d10742a8004001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 581069001 1250 581067751 581067787
    0x30303011509090603020307030209090313031b0501020f0c120a120306171b0f0a1205071e030f0f020a09050a061707081209060f0301031121061803 65
    0x10092041e04072107411403007508401103002405401006018075411a00420380d150400d110080c0146107150004140907070a0091358281f04040c1460891141d882c1003c0960116981d615034414120070000202d56000185041e0104040e20142c40b0161500f002c22910034800762449000c0d0050864050004be0039404010000c0100d490005017241000c403c03031032004007100c40469550000300f0103110758038020141140075900300c40c0840d070b030200d42d000f00300c0c0d110899100313048001e894004002048008501e0000741d42c4a0048a0202003462509030b01d202c2e014400508400105c1c404d02000c94049c02e0845440d80c00030340003005060b6a90507500071503e044610036100c0350340341e8003403110b08914040c443e00940c000d030040101c00e081100e80c07501c038540921584c2c42e00c440000c0c00d465035241c050598010364443c80b03400ea16981d480c2882980c2c42c41c0028102d100b401800315582800480c64110300c40b0b0729100000340800d40e20b01e442081c400e620128155107070b100c20b01c48811a50810441 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 581070251 1250 581069001 581069009
    0x30405030d0c060501050913060506120304120605130c03030c1106210a150915091b09120807021012150501120b010f05130b0a090806160516030e03030301 68
    0xb807007414080d5803c082045540681119208514000a021150b41a62a5207414070381201c00045d45480302c40c002900405000d41c0403555003c045400a4a41c81c600b901001c0540036034028403866072040307441040b144600c01d000300052800c40003071000c41d01c01c100c0008058030990702d031100707400850b0002e50f15800c03000460b500c1844590341c5040c2e040d40e101182d50412001003040c418240301c18010b0646110768000c205015540300007842a000410240d50300a00048404000000c1c8079640341d02c0c802d002c40d901710b003c10402000014103018030341e41d640071140c005174035508000e01030303082280c1d9881c0c029600741008201580700c002d8082c10321a01e81c2c0e03100d040c00c4818410740b40c9800034110b443c0c1401c6294842e494401d11030496600300c1e450301c0b81240140342040d44e45c01d0800c1c2c042c0388111075412040c0003080104d0040f01c141d0701300d0b880d8015245d5031800c40c4c3d100d54551f1032084400308a04020380c000f49050020310050f09086040301503440c8681032995104106001003031450308240c0c8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 581071501 1250 581070251 581070257
    0x50604030602030115020c0f040c0207030b250f020307030c0212060906060301360227061c05120d06081203060909120f1e0c1e012a02030405030d 64
    0x1006420310b48090900c0d20b04031800980407084c040e20001e1602380d03414250500645e12814640903051080c841b20020f158401c80c010420709150b0f004081e07404c143c01c144400c212981c2c031071040341d500881064600342c1d500e60007103241258550301111516235006040b60494090981d84180c4082842020311819180b4018202d5203000020507081d01c030043c02c20b170300e04d084581c403440c1003410b0b4884c9810044094868201042420b10208000303a840707000ea00c000c5442904e00807014009010700a008501c00c49140d5400300f0119490007800000e000011b009034840344005800030001d0001d00741d281a0880c000424039524103410307041080c0c581c06806038600020800c03c0303c0c80d195200ca600304800300010182c4a80810400c29140b03e44101a80264804503040800b51b50340303485d2030816034010030507035201c0d402c5411141d0341d003d10030030644085200140c071509007070703051040d184070701040b1140001001c018900f03403031140060440e030021400104000302c0c298a04100d0052141a00e80d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 581072751 1250 581071501 581071507
    0x318060c0206060d080f18090f06131b08040206040f060203031e090703030e060d0c020a050106090506060d110426010f02031e090c1c051e030406110106050604030602 73
    0x640003410460010303c00d9104001e909200000705800c141078440b03600d81c00042c0b1382e07201c54500044010850000d0300d168007643d84010003083d0501841d80034040d0318196100a10b20010f906600143c1d0843c00c11518200d2040d050004c2c44c511460f440750f0458009401e051a041c4c88140c45041040143c200b0005030f400007090240407008072003040d44540310840303005220705040a1a0f41c4a41142c80050208141d10703400440b03558403041100d030340f110041d4040101c07004500e0b010703460b0140d02c2d006544039460701400003118145030203407902c90603001b13191038038125805115000820051407050b084201c20721000c2000d020350b0030b4980c0c0c546030000e41c0c03200c01d00000c1410350a59091002c8031041c14018000d2240703091a0b120030900341d5440c610b0031925a84d450f95803034904a0030b0200c0c15400a00c80c11813012100740d1610f0b40200034016016101c3c50b00e41f180c1286c90061411400001e01d5004110070803006118884440800040c070300082500d40e580c00018480b50000d070030541d0381c95400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 581074001 1250 581072751 581072771
    0x507030e12040e1911070b04120c0b0606071b0e1014010e060711040c1d010c0c060c080417010218010e0a091a1309110102030424031806 60
    0x40041c10060155038080c1840c05003010056a101003000d040284440c10490100444a40c00d41000f0705203c40340364400c0d03c0d9030b100d09140d072100704261820384119140c110340fa500240307d43c441e40c200391703003101d09058103481d41d0042c0200b590051708151075100070070a9604050803140b0350310300103101410340b400c2c090a1500c0e2000c44403034160f10207074082c0d0b182c030358061079641c2200c01d014042c00215402034031201c00c0d003007002e0040001d0a0203541300d03250880d480e1220350010601c0002105001c005034003184071000554041c910420040e007015084801004068800c2c83c08a007114820940326040c10380c1c031a0040d01c00424202a2040c03650081034451a00d0200071240e5483c150900e0310510361450000407400d591114000e450312143c44030703031440c8402c40c6021807a9081c01c0181088500b583c80005941c010301d1403110403103507145103501d801c900e90303c0002030303d00740c1d1070324000c4440b01800311107030708a0701250340b07002014161160159101a04142c7c41d2801d043e00515001c6601e10b02 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 581075251 1250 581074001 581074003
    0x50703050d0f090506030402041103070801030318050906060901020109050a050d080f130f020a050a090504020a0902190e0109030c03051e19020105370f1b06090c08010507030e 77
    0x20305078452003000440415011403d9012403400100d076801e42e4595074030780321800460054040342070303004d0500500005002d601e13035009500798104c0c1e00036601c03003c0c800707030301100c0e0b19244025220307265002c2d0fa03d20100c0c1407850720000402c140a014000003a803a0025541d150605a04070010b40c0c0c1500880c0f080413540360401c0b0102d51210080c602c0596502c0c2050641580381d072040806000121812040700c00c43d268500288043c100050004100c1e0f40d81d4203100d00a0601207900f02c1c0a070041c0d2000040100c242e000384c45c1104aa01c03119100546044070840e11039242421140c108040c070100080816021960704000c1c50045000d40301146000d0024070501c1503100c6500125404100c10400710340544186100c101d60900e000355131542a448192240115120003150003000140100983c000070101301130b010545882c0d0881515003038038255007031001c0d226080700410301e0807103940006085503c4240c045200c0c1005100d0942c6502c802800c4450444008020903501c1e00544e8072144 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 581076501 1250 581075251 581075263
    0x216020112060e1e0703050106170403030914010b01090504050405070e0c160f1101082701020c01020c0d020f070f050411070501091b140a1a0c01020a02030a0e0415060f020a0b0405070305 82
    0x1417641821700140d450306c90020310350034070000c03504480000380000c241014803a810140d034481d000200c52804450440c2c586009100b50090680450401d6500040d142001e0140c0e40c481c035000760103020001c0c5404210828103e00801c2c0c0c000410040044070701c1425800401c0840c2401035a1403007000515144c80503003004448101d905101014040281000c850303402c61002c480082c2140104455080200b80a40142c03042c14019500124111100345000204841801002e0382110508407c2540c000c0d25540b150140c00003010b2401800d0080342015004000c0e1058140f8015203001c4e4583c50b02d03400c49003111012101e1400d0507004100d401c00d115285405481d0008064015110000009031000018421481ca0750070780034004504054031f105584143c80d45400030341d5a41100080207460b64082c3c032120b0086002c040185480707041c281f041c2200400383d1285501c0d024102007050315901881040141184039046840000602280740c80e4019840f4800a109003800c0d8500142000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 581077751 1250 581076501 581076511
    0x7170130080c031314280503060405030c012004090207150513020a060512040209060a052e09050d0303092603011d0603031623030d0f0216020112060e1e 67
    0x715942c403503502d90340c0d207802841c82070074a06d076651152485503114031300050a41d03610250f8503020b40340800c4103010010004145801c0c0d8540200104104030004441030503880345004280c40b411320092000c5075403030b4010301d20b90b40100d81003407586404107020700070356408803410740301140c0e0944203c00f1030034107e0066000e0301490500302d040200858900c5481c00c4000c002a214075890b00114503161100180c00010b06405050307c54081400c0c9928009007420329a000d100555281d105881c139031150311501c06030380300107219207008099070301c00304c0103008094000c4d01c5c121486040840030300c20078540c040f140810384565917140e615040000d82c00b00700f00c0342038100340c2d12000101308540c0d80200c100c8121803c48040041181d540d42410b0028101d50211112100400203616404450000240602c122000d1091003101a035a454405900a9904101e83c0c7e00306012008010360140f0207114490348004d00000381c4e03a036071704116241c01c50265903070791a088500f44102c00c40d40c22884225404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 581079001 1250 581077751 581077769
    0xd03060603110706020f090a0608150f0121270506090703030c140a0506040303060e06030c01140f0f07061e09170a0e0405040302010507170130080c0313 67
    0x41c041c90b141010391881507400003060740b54005000d4601041d00001c2d10f00c240800792442c45000e4907070743d01510081e025035a0707050b070084012043c2c21528280402121145043c2e5070038841850f041e443d01d8040c000092030b01b04260b103d205480c0036440d000103105040903a18400a200d00c414180581042c102904400085d0040807040c000f094001000ea40e0981e07000440390103501c2c072003078484d003407900d01c4070020000c0c02440e09000c245a803640000040d07418014070101592a10410184e80e0b615071400e542c01310705803850501c5245001d0300a0301041078404500352414100003840c60099001c20340407610725a803891643e20220148180101c04100c2003010806440f40c1c1c1c80e444260003010701e4440c90b0f84d00000794100010700c02c10b106400310402401c18000341c00c0c1850043d0181c14101c9503040040c42181180500d1540600e485040742c110300c0e20308842c05148820f1000bd503402617040d1b01011000300c0c15900042d8418010046110301d0380295444509401485403001425400403504c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 581080251 1250 581079001 581079011
    0x22051002011401060509180106120b060306011e03090206070b0106032009040c0918060e09030703090504150b040303080a0623044d04030f08070203031b0d03060603 72
    0x10520000b502c143c1514043e05000d40c9915104000a075250900004000807080170400003503502c0c0c20030701100701039a000c042132107058450001d11056000440d0240e001603440559481420603041085800d00014036000c2070220594000c69140d5103d01000c031941c2e620385004101c00c50707141c4a41d129a200d802d070b411c01d0189900c8020b040b0f43c001c158180380310303c2e0340d154005061405407190000505900803120043c800494155000701014810f00c140c0c41e004c0300006a1300070740801112469945034880c003c0c014109404d01c0010210a40542c04200e800c90012510085980161008500c6030b91038401e5031401020304001d44025a03c00507000f551a030010034511600d16002211a00c04d0f200024403458070313484a1000c1030300d64207280302c03041003280091220203d0340078000400e80c072145540340c2001c0082000d0f4144240c0c8005028842401c0b2401d002640c154000c1034050700050403641800108107a2038450004d081c0120141d600900c40780c100b4640500074040100424101042 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 581081501 1250 581080251 581080271
    0x10b0a03050f1006240221070213230c0403020306090304090c020303010303120c0c060e100501050603010b0306010503150a0f1409040c12030306030b010609061107292205100201 78
    0x2c4043c008410b100b140310f5103170850080842c401c0211095510702c42100c00d02c400301c1c0050f540c455600640c0103a010b80c640131602c60082c1050b01480341003624201e40c1b09000c00c003145400c070b054280684083e00c0c81070104800000f581d010040c1074015080c45000d166182d01d82000b1801301c07107914480c101035400600c010404250088040c0000aa102d0b02c00b0400a00d141000c0342d001072001c42c01402d00303180444410412100051140d820007041e40e0402c441d98a0303030104907490000740305507408010200b001810700c1d48140c0242d0b40041401e2400c0ca00d464240c00001c0c050900c940140c41303051451310003080b08200b82c044a0b8414541613074500c1450070103456140100709140200381d810f8010b00e82042c2014071a41c00803004540004400681d561207000060421145101e9400001c10b0015000b079070000120301c5400b1182d15284600b803c0c1c107858401001d880d502c60000c1c540350410720031603011900709008007000854100361502ca003405c0c0000c0214020010750a03001316890171303138544 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 581082751 1250 581081501 581081519
    0xa0c051e0f04020307021606030c02010b03030c0a0807051908071505070807350f010501020d0806010e0a08030a0c1203090309170106030804140a1403100b03010b0a03050f1006 77
    0x30301e10300740ca015a50b91346848046c0d103017001c10340b5150348040f04241d00041d413a5041c0d0000401b40c1440d4028001002c10004240d641c0c040d2010001d600d0304280c00302000610110300801000344500706440000094060140d000401c0d00c4003601d0b662000079019003002a222020005803036186010021803e005800909041c00205a4070506c44044402c0509500a400c50002070f501c4d10034254080300c0c080c1c0014810041a240800c8402c070782000800c1035800443c1d0b50003441d0181d075441c0343e03954450004454140c20f035240190030010300d01d0003184012060000b00204806900d41d0804400f481c0b4012241024050a060826242038241c400190740700d03010f1b03003c5803800b40c4603100c0c2029264256005042036030004106000000f40051048504a45071242c41d004a8601d002141d171590001c240c4411b01000a03072640200f1001c4542150962110090b00806400047c407507400c4c1012a103141c6003034109a4695110311201000001c04010064922540400074002540783c10886 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 581084001 1250 581082751 581082769
    0x1e0501031a0a0204090e010902120307020d2004020403060e0601140604090209042304171e0705010608030a05040f0b070c0e19060612150e180f0a0c051e 67
    0x12001c0c600d062804189411601c0c0c06030b03409031140c0c0c0c0e800c006442c07039280440d0090103440c10403402a0030013a40c00a0b401070200584050f15009006407a094034680d0702c0b219201d00f04150321692481e100c1c05454940c032170b4405080914860a800a07041c2c00015210303181602c164071480940041650070441c0f9103865003030300c080743c0e41c405026844035060030004000c0c06030403401d414401040319014900d0101400358030300503405031107212000c1d0b035200680c10007803180184034040780e00c0c0c2605911380c0031012710041241c1c9008000000702d03075489694003400c65125a032807074006030740810b00b0b015800c0c003484080010412510758600d048142d555010713000469100c2e20840201500c0080d003040204c05d0501c0101040700d408121403a00d801010745480c0712000074504151500d04030110340c6044202c40c07000d45004400f1b40220350303945010502038243c5054450141d000d41c10326540c07150342c10801260154807645880c0d19850401d03050084002110140c000300d103204842400650300c1d11691 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 581085251 1250 581084001 581084033
    0x403020d0c051f0212070807021504050a0203150a0b0d0c0e0c0f030709180b0a18090c170c0a06050702060310170a0c1a0f0a020f101e050103 62
    0x600341c03a0265040c4541414150500e2260a100070b440b10440d4100a50061030603584100c000d5103107445002003102d1178141155407002581c000106080c81221002c0c0240d4014031038800c6803405509980400e0421182280c41c0990b1740f882c105002c040075141c040d400d0316000176621082540055102c07820007013610702c10324500404490210f051b8060070002c4a582042c0c0013000c82e40c0341443c0d0001401680303c0d00ca0012403070035510802d44e48000500402d452414020204820326041071001d0000d101c02003103214025944529200c00100003500000003400d46980d2442c0c424100c1803202d0811f1900404640706012841c0c09008654100059560702d9806550715520fa5a07001d01080440025400031110b40101c0701111a0320342c1c0018065841a00c0303074110405503a500d00e0100300b4158038140e03040107041c00344540400e502c040f8011b012070301024811107036803804042c4824180182000140040c0740c5545039100c00d881c8034402d0719aa214000c070304102640c0340d526000340010303490107 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 581086501 1250 581085251 581085257
    0x1b1204020a050d2d14060702061003080306010f0201020d0e070510030509060a15050d05030304060e01020301050a030305030613060b033301050c010f050c090f0a15110708030301170c04050403020d 86
    0x2801603a4402c2d403410104c1155100d4035000e2108400c41c2c080303944032811070383c0e180180700c2d0000040130442650091401c40f603100480c2130440d10384500566007268601107801c1150742c01d000b501c894100034090b080d00b00301000080d10101c1c2c00c250910007140ca409101c3d605142c00e002c05d0200e04ca6001588035400f10103c1000908815030480400d50390006622141d8000305004015060040c003000440c0286e12030b68041041c005034411160a13400240b14956011007400002c2000c64001c8006560140c0c0c0100b600001c0240000c00382c086440c9034200b0000d117480402005800c8583c0701030780080e40d1303104401d2061019180c2c810320448074a01c400790304002d40440d0408061100350050000c1d40421007042c040c1c1d20f0b01e0070201840da000002c84501c82c03140c3e0760290145e4180313804d14100791015442039820000032180d0990b81c2c017020210081d1b03035208400001a09450600245000e81459000c41c07903c6c048a240c85403410790210081807180e4500800e001c0003a0700001c00307501c1c64190b42 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 581087751 1250 581086501 581086553
    0x150112020c0a17093703020f0d060e0d0c030f0512010b07141c030b06040e15150c060708010e07080a050907080307060c090b0315091b1204020a050d 65
    0x43e00f0341c2d0302c1e004004940c0e4010001e81c44806040b403c400244c0000101c1c0112064800c14000546500b1891484065000b2642108200550900380d8001803000d00030003000c610041820111441c1c4000e0f48544400207040c03034408010158001c803d140c0c100810f1411600300490851000d00008042c0f0400b040c0c500000303406000c00c40c031515003a2a6200b6034064a038222801705000c03403d403c02600200000f0728001d003104103481c2c404151000d449082e144186903039550407040c1c0903041d4048916601030b42c00e4400d0703c0c1130080300e8001c000d1810700001401306070510443c060030101040e00114800ba140c40e04000600c1d91114440340e00003c807200200d8035840e150314442c02d183d2160001d1081d400001011010700105400080724214a0346d140c2c11090356507282e041c44d600050742c02d210151303403040032035032280741512501e030f042510f50042d9003001c40c003d00d040c0e42c541e1010745100c2c20800c00104110035494903410310340080500352000c2118007403e40d282c0100303114144044c500cbc44089 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 581089001 1250 581087751 581087783
    0x60f1d0f06040e0303070810050a060203030a0c050708030a1e0209101d0312030609070e030303040f1a01091a04061d0405010e03070b0405070b04060509010e03100203150112020c0a 79
    0x950494400c0310302d00f105403a52428404001065440d007202c1c084008082c4c2d4038002100d05003880e008003142c90350340c00385007162203001d451800351140440740410004244485070104103103600450185820303110000320960540410312003483d041d420380804c5441400100c0e19a00d03030b0398004009117064500b4031107140d01701041c86044003818109940603c107441d01d541800303d0000c0254002e140450784110b1175a6154821036810046600140e0160070034000301b8001444400c01c0eaa07054030030001d49540c00c0984a400d02c0c0141d09030700000300252181000107909640003c1024240410f0354113010130780c201505030016124003c0c6440d402008a000a814030400303502c9045901002c409480da9401107081070394524500307840c20350342401490400141c1000407811034084034101d4450509001c4903400650303168404088586d0580290008800200000d10046100700c80c11080c10207000902070004005001400310f010b03506104011440c00c1e400000f411520169011100b03c4d41e90001d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 581090251 1250 581089001 581089009
    0x105090628030e060f040203071206020717030703150312180b0408030703321c050103061b23091507050c01080601020a0f0b06150409060f1d0f06 64
    0x484250414410348040040c80560680103d0340d500240c0b012203529469500d04c195140000f40c400a616602000c001c200d005110001c0d40c0c10140620307001410044603854a284402180028401c1740e2400000c00c407915030144159940340103107841c107500b00c0e82140d5850505400d0000a5000d000501c83d041c04031004504058001c0d100d10750301d96403244c1e42d039440555603800504c81180411407000311021140510003400002e004001200c1d601d0226021900d14660300c0f40440101c0895410022000340e1003074014280298414203000807000c5400191018400d40c1c01180740070170880001c03a6182e06a210b41c42c15099a0348214147c2e5401c1c424000b600b074042110603036041200100c3d00409105000c207420007405401e80b21403000381d80f00b100480c0c440e0104030000b0700401d4140c40d0340010030783c101c0035240d2011020f0001c41c280d200c64014920160003980c000c054803a1104014005150701ba071440c2c006008150321165401e1003a400910a40c0000300004a100d44890015009540f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 581091501 1250 581090251 581090287
    0x80702060c0904060b0f030124050301091e0510030302100e0303010302040b01020712080d0f0509100c030b12010e0c09101401050f0715060b090102030a0e06041d010f0f0501050906 79
    0x5175140115642c100004a0305e00d1a003003482103075541c1001c0d0221a09990001d0360002c40082160307200303403a5a0804045038020030034003100310442d2035aa501e544078183e0a1140038020860591000200c518500d4000d00c0c00b14000c4210010f1800c0c5103000c1541100001900c0c1540d604440106442603000c0040345800314075809800350751350b40300081080c4000b0500030000000c4041050092840004118055550964040202d940048052101340c589030740180c00c80c2d0b0061801041c0d0a07804000101da0740340d4000c21601c1c0340d6444000b030070b007001c0801c900503c0c003100b61490880d501d040c41c90380d2285001c40c45038560250422654070080da100b04210781d0b18080b0500810384480b03843c1019a4074444407508400740fa4030306007020800840d210207941030404140d00651030004010b00444010890522040e0404001e0102007050000d08008031841c010300340031442c4540c50402034101c19405a0700c44200c01e100e1a10912150741c5c4503040b5111418190b17102da1342c03002c41220242c4408 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 581092751 1250 581091501 581091509
    0x1508011a0f240f2206080408030105010809152e05100c030e1f030507080c0316030b031005101203050421061a1e18090a050d080115080702060c090406 66
    0x8000100398100b01200e500c912404d0041c1c51540c0312003038650009407001c401c103640241031242d081c40104119071040c5c04081d440168a016501440c0d460040c414091100b81c03803c042c600c0e48040c0107a1540340c203000d01304110b407070101e505903142e11305070201d103104000078004400c000200781c5003028140036503181d091a00b4064007554980c0d2840e40e9400704002400e0075000001e040c500807407492817245075240c0c019a4006103044ca59103d900c40e42071110f003940c4206092540f54502204c0c1c607a818803040c2d00e94296400c000c24145007800c14007480c03101c141c008003211004c981c548d2000c81d52020a40d000d4803001c00341e03900c4044119250b03544408541c0d10041c049414034001a0800045000d410781d181c2c01500d0115001030340c51641060390990400d881d4210500d610340481d032250342c450b2950810355200079a0040320f0381d5224541031070842c50b10b0344003086024004101034030b1644c1c09012141c541e40f901a280b0304103500004d48840025003034040c0c846011503081d44560302c90f88100c00030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 581094001 1250 581092751 581092777
    0xe0606060a0e060c0a0b0f010e070f11011806020d0b0a060e0904032015010f03080906070f02060d0c0f0309151a03071410030603051504061508011a0f24 67
    0x50301701d140052840008980350ba010406000c00014080044001c070f43c00340180380ca642c81020b94a440c110ba1034042c441710301030b040d900d54005215040f041c40f51076103024040c420250b42e928059902c4015940c074000c505019440003501001450f0340648054680c02d0708803103084190b2203e06007121204003d0b20b20940c2d1201c18500d0320100e4100041c80e400000b0302e06004003950303907511400241400c5a100c043c19440042100500500d0b0501c002d1803803a11902e10703030420b5541c58000c0345494000380355102d861981c901c09420156044030030090001000d18043c088072009640c2c00c2010b80841c0311154019483e400d0340340804007101d100c0c0c1c941c404058111108156a290000c12450581c01818000c6030f04201841c8014481d0007150261b03500a8011b1542e0800e0b8114100b140200403c240c50850b0365014641d221080b41c20940018156640041600c950400500381c90740240c00f13109101d031018886400083d1255440001240124495415084003c506111440c464214400c0300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 581095251 1250 581094001 581094013
    0x3090a0b1302030d030b0609190f03051b040606120e0c030d02030a1d0109150c060f0b0405071e0f020a05030403051e0102030c0f0702120d0306090e0606060a0e060c 72
    0x95405514a0300900d000b18201e600380401d24606400301e4008540d105d0b0048000c0240d0130490038827045041d203610351054803000d0301d5640e030615440508507400450785a04420801403041d8842072401c00f0700305c3e080f1002c0001601c0d00304d01909080d030714888582c8080c1c44105000c44294140318060342564058251404440b4941d40203442c3d0b400590200c002c1240007000d18285130711800403481c0d4203010707110116505d06210340c18000d501464100f10801580a4407400081c9007800782c0c0541562126010801b000030204101c15140000c15010030001002408180c425190907810940c070070600b000e02501c114000100e08186000340090321a11001800104210000a914a004a401002141d10f82c0248982401c0c0d11083d40c40c900014000d01c80c1c1c24108031010300801025100920030361180c10702044480c144419000500003084c0d071079100300f103a0b040c6400399001d00405c0c00090041450030a00081e16401032019040400001d40b01c0b8101e1070300d403282164040c03900f01c4100c4007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 581096501 1250 581095251 581095261
    0xf070302270c031009140403030e120d090312090f080c070902120a0b1e01140702030d0801080d020c030601210b04050d031a03060f0703060f0605030105030c06090a090203090a0b 78
    0x74180d4015907034441203139003950001600e000765106106200e45a20705400c210307102c5841c00ca000c0e00102005408502403d80049258201200100600c0e0094440400d0003000c0c0e0402400e4540c040c6154408181401c8200000a8400c9078020314a43e0044242d5103a00407160303850321b0f00c2006d4010b1148984001090407141800c29181e0380f00d400b001c2c0c3c0c1444030200d201d040c06401003000100d41c00d0024104802c031060340c082c2e014140c9030000d080d0701c40c0c1001c40c40e0300001d1038030626000102c00315910710018000020240814043c03810240020240c103420000444c0d03a8010502c1810309036a6036140d0030744082c08148900c801c0315040040400103060a040880e11007204203000004a444d01c810a4000d03400d46c0c1e4681c0640100070054501580d0f00f030900c641011000300000c041590f550380100354400070803100c07009020a90303a02502c0c0d605110626282044143c00f2034407844040c0202e081b240d903411700510a4582003440942c4a0700d8941c00ea61910600c40401000d070325501c42044 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 581097751 1250 581096501 581096521
    0x70b04080708010513031704060b150c0d020303010b0f0903030c030c071e05150919080f0712111315060503150d08271e10020f07030227 60
    0x5419110307002d008104588649a4030031249100b20700c02004508503d07403051712101b46d0101c01d54894010800400d01381c01500000e103003400700e4030f42ca070b000a034040340f035800608040156075812240fa00095195504100001405004d100f54400704100c001a000e101c0d03880600070754442000349011203845403055081180c40c1c00444c05609080c4110f00c20742d080d1919103418440c1252400307003000504405d062041c22003031b4403101429030420941030340c0303c2c0209914505c4071f0090089202a0070060440c00056040049990000200c100c00101030000710b190340010001668003101c6515407040008414005009060744078030201640d241c00013003c90300800203605c1000582580c10f0f40c0c03003a030000c2021a00c01e0313043c09800324005001d51404000c9140f03c480100d030100d0034408032007507442c000030000c0c80003580148459455034110102401c00c40b09600c04403106001500220781034100d480da907202c0e184406842502c4100114502d009a804d114041200c002c43d2175100307180c411615 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 581099001 1250 581097751 581097763
    0x41e02223b01110d09030e0a170705060712030b03070306090602041701021c0c17011517041e0c15020c030c010e090408031e13020307060f051605070b0408 68
    0x20901c41c0c0300201d40211841841401c189070031480c001c900301104070000100600d04a0011000d12140e8580c1284035030320b03540c20a004240048035600340c614803c1545080c24550361040b030040c1c0d4140003c00010300040440210b1203130a103000180d56003100300081c07801d501c40d400a42114a4411114184900d40d001002501e080707905000c0000c0d01341d40c0c0d5500301d10035440109650307200700310107501513083d9400028600c90b0b10700e0203c172400071400304202c5d4100282d10a45c1907220a0404500d0642c0028580c030010a0001104c540c0740b91646403004c012511200340100d1080ca0403814040001a0005001401112100b45807403401300174007035660340110070968031a00c101c1d9103400701e5610448401c00c21481c0941003503940e495550f1500c003c0d40020349000c80850f4050360021040001c070140921925400202040b4005640107060800e242c94000d00c0401c030441c10f10b1641c0035004000ca4040c00c5038030008055000640c1030031400c0c4001038000004a0100107000240c1c4040003400c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 581100251 1250 581099001 581099081
    0x611041205061509093c010203060406050d0203030d2301080a0203060a060f050d1e0302100b0d02010c030503070e0a080d02100e0703031107080303040605041e0222 72
    0x2070440e03000d0f840020003044240480d0b444c2d041d940b00001a800740001410107000300d000303000803c0c2c0d9261b04000d403081c800c04006c5506da800da5002c801c200340c03490980541c130004d0105880b05580c101c02c03500400c2e2644600c1c14000b1000e030315880302c07803484081d0700101451404079114014455071100d01c0a42c54142641041e882841740c0b0010a4890038144661800c45058440d050060b41c80c02d01448651030446405440b2417000002c54131a0401c1a40d07103244951003a4041d0110808009101086a05107005a80a81c801707101640040c0d0300008451406a054284180c482d42c0c1c1c1c02e0100d5800d420b80e00c1c07554004041140c00282e95600240307048080d00390b902a10a0b04c480040a10100ca030f407201d03020946d510605042011a000d210000007400b40c200a0302c035919280c15825140da4000e0390215082d43c2c0d1501004180300506011a03121481d0343e00d500f8044649400140c03800b410107000504e1116144051440e5400581c4404400c00450b444400581ca0b44d0107452054403502c04 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 581101501 1250 581100251 581100271
    0xd090f031e0f0e01170a05060a0803090109030b0414071715090c010e011205010f05040c0e1302030a090c150e15160305091207050406150c061104120506 67
    0x3201400c00700e20000c2000203145076848840c952040030044610034802035030281480312541c010403402c848070039020f10035100e078103010649003030440c2401101c208a80c001c98041d042440084501e84e8085994401c40f50895100348003034449080800404808640c201c09920400c00e00240b54854080b114030241c544400b91600320f0300490243e0031b0803074101d41786445500a103050b16600c0d8042c281000303035040189002645549100c0f860811a0401c0c0c02c4030b0720400101d4010810b51507c0d002c0c0e01031401117403030000c41115544c4081640084100050001d031074000c030004850101d01c0d4003407445103400032401b50b10b050340c270286034001220000c0f98600240c141c60b035001c401d080c6880c000d541800c0e06403440b4500b08400f03591004001650340c3c1101000380803c5050710036580c100d0550160414000505101c6103032038100000c4940c00d074081c1b1426001c1981d00c21500303800c0003561400580120000c1000c2485034000c9100d4443c40e0080a020b445120030501444400a4454841c2810301 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 581102751 1250 581101501 581101517
    0x1140a0206070201050c0c19080702090f0105030705150a080408090d0f02130b010206070f03020d05190e0f0703081b01051315060509070c0201030914011413170f0d090f03 75
    0x5031498105125a0300300e40c800e48d11201305510b008080024001e02c103130203a040e403410500c41d42c4c0000d030011425030307a40c07440c501013100600c918503060064400800003191a500c1d0b882c0641003000480c001e000c20302c4240038042c000102030107045012100d00e100020034000d0742c1d030200d10f003084880c200220164040c1071a43c000d03446816046c45921324121050300140784030741d40c440044812201c000c10607810103800b4483c8090310909401100d011300c1c000744903111540c00301c5241104462008042c51015070125003001409240803580ca419030b50012030385540c910465107522607140b1f182c7c9018100350b191200300410380a2960101d08a18858030301c00403410004ad440b0000c0d1903035402420b6129407400d0125002c035020b010300300405807041c1400b0500940c0c030b80300c80240c800340c48408002d99441d0038030510420040580c20303a1240c071400f94190703030162644a00d00d0008281200700c3e482100043c8050700d0318480c0341030724850842864280720786280707131800041c0c00c0301501c02100031619030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 581104001 1250 581102751 581102761
    0xd05040812070f0219051008060310051006052802030a110a050d030f0f050a0b0f090c0702012a06140f041502090406120503130806010806011401140a020607020105 72
    0x40044410a0f600321003d075000c5000b80d001c00c0482c4982c2c50060950003ca52800a11920340b001350940d6002680c4410503240b41042c20301d410081c03200814000c0c68903040812018020b80988034041c1e030b040b8034015407992210708440d2144441a20100ca020164203802e1182550000c003c0c00c03410600e60300c206d910b8280e9040b03641d481504c0b840042c01c3c0d41018003821411442a803101684403ea0980400e84081c83c041c03180c1100c20540b1103440d000d84407000e601d12400c01491b0809010800d0b145003c2c1490400e8602c3c03054062004020b04116030040700403403440b40f9400a418042d0f03015a00300b030b9210b6a00e026001098442ca0381440240c1400001e51403941d440c01591250b03400800030030019005044000c020b42c0800c01c0c1039840741d6200c001180c11685810f9003090603204100070750352110350a00c0c02c10038080650021081d03510000050050f0903012410904445031041c00300019611240160341d1014032112400b01041d010980482a6500060841c001c500c250000c0000c0d46070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 581105251 1250 581104001 581104033
    0x602070c15020708060a050c070204050a1a060a0206131a010e07081540020304020a08010216030c0309050913030f021b0d0f080712110d1704030903050d050408 70
    0x841c404e030320b041d4100d000054422201e40c0c1040d54400580d502d5103240c03400c03070390001d01101e80c26078080c045c069a801c102d100c01800060300c4070001c982111090304203803202c40c009580350001006041b05540714010032041080721103810802c0f09091426600540e102c0000f10803e480c12642400040d040030045100c408401d600c076044031801400c40040300700d24040440720311540000600d602c440155030010360a49981c1c00000303020b201080541e0380e050074010808028110b400020040e481000b0354841c0d4406070b44c0342d20704550325041282c1c18407842d00701610b0583d280d50100c0c3c2c000124100300054141001c0c000280075211b9210901210480f0745c0490751441401c0300c0600d00840f6890360300d0145000e5501070519480761a0848002d0b00f80d948013109500100d0088840f0b96040c100c80d01d01d1900204004e84c0d994620000702001310306960300070800e060040d40300003880c0c002408a1300385480361005030007030b617001812209042c0e20000c008000360301520541e282e5000700f0300003229080c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 581106501 1250 581105251 581105263
    0xa030c301a090a06020309010c200304050d1a010311031009031407080c010207030e10030209090609040503070501090c090c1e0e0109150206070801050d24090602070c1502 75
    0x14110218101c051001d100031031490601030044045481401a0100002e40500045205030010400450070010780c40b000b50049032000c03503c0e082d161a0741c800c0030030702c0c0d000029101141c5003166598000d000c00d04001c80c2c0d020180702ca4091500800002100b07114200c0e110040482082d0102d030052040d0a814204171480c5240040c0018105011180600f050030b000e400340500030788060b4901600d00c0d035220700f26404008120007049400c030200000b8940b58454021418031810154a131000d50340c005940380000510f254844c50b0b1880105080c000308005031810305038080020040c2907468140210841aa482400d003130700e090a55a00100e803203070700c403241071800000700d03001c42030031103002940c0003440c0e602050f040000700710000030562401d1705c1884081c0c2180c4c000d4240360030b0500005010000580125005008095020700080c01c8083c10103241d03180400d1981d0034280110403072016041040002e031404e400460f5007000c0c000b03103040b00d0080703844c066621144001c0b414010b0782c0b654 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 581107751 1250 581106501 581106503
    0x12010c0c0809030c0a030b040501061a25060510180e03030411030a2f0a081507050f040e06030c0919090c0f320312090a030c30 56
    0xc0e860455100050407403009000036803001030985500300d2140020403104101607000741d07040240042803009011003841910b002d0100146001e80c4058060b184840b203220700c0704922140c0b099a201c865282c083e01c400c9100c010750144081c003082c285080c1e9040300c42e000d80612480e9241c00d01c502991041343e0320801100c0d907a50405182166229102c0b1110b52186402c000c1c1c15000e0a101140020300aa4120141c0709540211980710358080d501500f459034500500350255041507014007821000050000c00c1c2241580c8880503581d402c0000c5405000b40044000303615404100410707404090700d036851040c60281d0898003000540c00412070249010b43d0032017211610b400041c43c90b0b540350f402c091507039030082801032551550792462116041d110740c8a0505030b14030303228012500c40340003d084002c801501000082000850019403174039410300c048510200002051030003034550103d00c200031600807a601c0e00301503468043d0208454440c0700ca0360030401c1e9900d04052814030943d070001c0c136 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 581109001 1250 581107751 581107757
    0x605040c090e13121701050301062402010e030307020304060e03030f030412030204150306061704020922171207030e07030b040809040e240411270a090212010c 70
    0x940ca01485801d0b41c0e10003901c410140c3c0094076541010490007442c0380b010720138550702c0e079a010070390303403400f550790354068110320300c07030390605500304006d601c04e844009126041202140311540c402c10300303a004149c801506490350101004100745140c004c0080e20403a007803911203154500d550410141c40c0c0c40380600310080b11200f80080b5001c44d40800400010000c0c908006160030713100c04100c024030084400c00c5000075120700d01807154990244104450702102001c03070721641820f0380060301c6210010903001c4070811116008248150702080c3d880c43c00d0708809110074528805241c58008c0d40058a04081040c2440208860603c02d2044001e100c400f1800f421400d0b096a441c1c0d0701500001e042558038000078440702000d80d8991140041c218502c000403c02d800805440310001881e000d5030206084061040102280c2c0240501e40380180440d100d410310100b50724503105800060041840f203042480400a410140341e0203800454000c40340c003081d81c010f01c44100d00341ca030078604803000 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 581110251 1250 581109001 581109017
    0x40f090501350109060b04060b031302011206050d0f05070623030402010314252d051204110103050121030e060c0a0503072d080715110705010605040c 66
    0x800c00e484210303016610b0042e0012030030303044559090382075400b020001d0b40c40d242d5920142e0182d00e0309100360b030010710700441c8903800c525001c00c40031071a024030140a414002035a45900c224080c1d90720000c09080000c100c3d00007810641449100108600c030100c43c41e1040c0d11011500500800d4824480c0d00b40064070030000c0e6114000b0b8450b07420180089050640b0303480350304251841442013034400c040d41c6c00311041c50070030000740ca54100a10300f103d006001d104020024115403800e40b228074002d001c445030030120306a09013150b4a04c02e505c0e14824805c1c81c18140300030000028064a072280f400d0f80c041c089170340c880c00d6031554800000c0800b2020b07182d181c40080040c0c0201203940c00c2c0203004101d1400d00300580c0f9003d08042d00f54004507420b4200103103120400c420005804044c00d42e07844000d240c1a40000800526801440054030503c80401e0f110100b00300a1130944200003a024240010902c0346a0980c06400c8100c00312000d50134100042120304040c41900343e411250790741ca0760 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 581111501 1250 581110251 581110289
    0x80316081902180d060b0f0631150c0308100e01031101110d0e090c07020604120f020d06050609090a260d02030f04021906020d0e0123040f090501 64
    0x4001d42c84000c3e0a6945041c050025a0a0703489011040c1c0013802940b001c00c0c0c40081c0e00400c91070410010303d1a101e860248034440e28080c407030f503001100200152850000041c107074800300e03991b001d80e031207205440f00740e19802e004141d000d0403d2031054400d40b81c09803592106000070702800d0040c0101e0042602d054010004a11050014140100f06060a1801860400416040c00e480707490050100345090040041c030f05004440307650111000c2c005a003804000e90001d066807280c0c3c42403004860203c0128828001c1e00c07421184016802403602d040f450040c5058070203000d0482d82030748a09101000a15100004071706084404e600400022a0681d41d00d0b400040c6903101000a08000c1d0034403181d1840d84441c80194002d940204101a01380380600c1000500c1080c4583c000020901d40360800c1015000104018405060704190b02c49003000401210b0112100740a0003286554480c04000782140310001c00954418040d115a02504c2c0d03490303482540c40a10902c4030305100962285 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 581112751 1250 581111501 581111551
    0xa081b10031b09140603010807030605060315130c050d12030e0312090102120c0c06010612020702030a0f170705210f04230a0501020c010305040c1208031608 69
    0x145003000c982000510107907654091049840e40020302d2002c41c0c90501c092042110141e1654100d42d800c940151956040c00c0b181503c80906200c003c0c9405e4880c40414002c1d03074207101d03150704440e44c400d10380520300d8403400100e61000c0810003034032407884c5114080b40034203028250003051a00980c0318400c6245500045009014030103080d00d00780401c1c024103140c6031410140a000b5a0000e0003d61120413040318280056005840c1310020710301001614015100814405d04541082c00d165010b05400301c80c01001c0d1284600081d41401a501e81100300071402500c41c80c034a010b0600922107040321409668180b1030041d01815030b900ca600450303e4008000360500051019400c00c2d810040e01c003561489541158008134a21111044c01c86522500d0146040c0401801c81e40c43d1075a602d4000040d45412a0401c018101754031103001805000918410100800703031030442209101250802c034035907070820364140c00381680004040501c6480313054428025107145c030090900d42190700f000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 581114001 1250 581112751 581112769
    0x60f030c0503371418070902030c04050d1a010902040f170c0a17060a060e0a0216080408010603031d100c060609060f080f010e100903020f010f06050a081b 68
    0x300e61002e80f8241400d40070400c1003002c50f002400541c000c20b075100c0c80440108030074402003001c11807000c1600002c02080c0e00080c420b0442d0b4881c500140d82c1d442d455901800c505c181e030003187e088480c2050b084e00704a150500c0e5035002c401100c00204d56600d52501030103031321551090320b01035640b4034010300c0314202c00e032540e240c038000c0c0c2c0781200c0c0141e1255000c20b884540075441510024001c0404105808092001943c0403550540c20440701e4240320820203000030140c03c0f081d1403640860382c24185a01035104081d805d030000d404648966441c40030038064121400128006240a6148515000040480c0803000f0004141200901e281c680803280b49607003c0f010b50b0f80e1130301d94400007004440c42c8078290140058100c1c40364107900740070400386400801038944c1ca00d0f030316200c941ca00038030011500b0340c031100f80c02d40042030290315818203e103021300250a41c440b6510340111030b00c01483d03a038008801c48a0649062840c144d544413640c2d00d41c00e00220b07028413220240700d140c030a840d1000308 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 581115107 1106 581114001 581114041
    0xc0302031e0709050c070c080706030e0109080301030210090306090b0a0c05070302060c0306060721030c05030f360109020102010515150c0f0303090106060f030c0503 73
    0x350381d00043d00c00c01c00c106648402244440601c40211025079400c00c840b540b5803502e940300b25454548600c200c4e004030f4078101003000000e0f0103000d03e03150650010b141c641141c0c6542c00740b18070054545508000c0000c0c440740800081c00501c114414140075680740c22003860000203a4003122903049031070341031090a00400c400643d0018000303501003074055001d0340302d8a40b080441c07198041c1f40c0f0300030020b0502180d01c01c8554500040c0d2460030328241d42c02e021800090a0554480c8016940c0140f404462000a8060101c02d240c0b000310f04e441008032204481d2402c84020580c170800b886006036512030081600b55a8240510307038100702000b0702e10710300380a024001600d880390b207400410401004030390f0b1103000b14103210754000f40c0c0040301a42c5d03682c9007040d5610700030300150103000085840c102c20114014841d10600c90122000c0d29040c4c51502c400110070494048211 = true := by decide +kernel

theorem cover : BRFrame.Cov 580935251 581115107 := by
  have h0 := BRFrame.cov_init 580935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 580935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 580935251 ≤ n) (h2 : n < 581115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
