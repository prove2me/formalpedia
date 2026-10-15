-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5054
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:35:32.840206+00:00
-- url     : https://prove2.me/submissions/f0178ceb-0659-40e3-b5d6-7a54d62b5122

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 908812949 ≤ n < 908992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 908814199 1250 908812949 908812969
    0x103060e0a2307090c2114060f030f060a061406040b07061805030f07030807020a051b1315060908030c0606010f0c081809060a080604080a0e0306130201021b 69
    0x1800148a5281002e034440c0410000c001001040000c002c04a0428070082407a6004001895010143c9500380c1c542c078590320502d0229201081c0f0340d46292240020009102c48085607036505114a0300d000880d20030610000703000d8800101d00083c0d20b450594140350310814280c0300c502c51102030000300b103904a4402200c0040e46d020f00f0001c1c5030107501c3c1440b400100100c1c03000c3c1a5101c003142c1002c045d000360000b4007505000303840d42c0c010f5070390b11501243da0340403443d0010410307044041d81400c4d00595080049485a0007007515003400fa492010f2002c6440300ea20b00100701180101c10801a6049178942c000b50038040e014510f07101d101d074034180e40e07514003514140c100b05e03445006003003051140b4002c10f80c03903901a44440d9580300300306103107040381c1d02c0100b002e200c2c2c403080f00811441e00c0c21000c404126400da01c0505140d42c2d844d00c450285801620300841440b4800c000044941e1f0188445031049628440880154003a400020b25004503065a000c85040903c108445a81c03100044 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 908815449 1250 908814199 908814233
    0x20a0204050a1803030507020106050d11090a06211109040b130312090b0901060e07020d0806030703050a030921110907120c032711090a060803040b030103060e0a 71
    0x114540d141c05442074000d20f04454100110b00302128048105039054100034002d8546da40240091611746082140d031419580b0024400c0810740c60300c20399400c1444100f50b200b652144e001a0640d40c8074201e449503482100c1841070140e54019080422034412000f4540c20001d0b50445018900b41e61765541006018212191001f60b000b941000c051003190308005a0314a104244241720452030190440c2409a034042059400e02d80301107207070b06d02521090310680741e80d801480a208400c005445c5000044c100681502800401001080b010040500c00034032954480058a180c145404083d12030803403a0b240c207403080303001c000104030b00c1124445028022507801d04552550801507a959011100252015003000460401c45806603c0071061811a01c00c01707040240008610921540c01007005103101d940c201100440d05082808603030100024800142580d20386107098559040341d480a80c9000001005100b00840d40c01202c2e840c0c25108014800300e50a6502d00c14040100106 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 908816699 1250 908815449 908815451
    0x32601030f0c050d03200c0618010c020d1a0a0c050f09030102120903130e1303030b13050f0118020724090219080607021b37090f0903020a0204 63
    0x1144180b003115030905000700001440da003212081450068015446615911045201001c05a4800c003010800041900300140010b280441e111928020801d8081006041104003880030700144c0301c048000300b85c54021003894100d00545881100e8603800140343c0404107003040b01d00d9000704d80240035100003502c6100703c99111101440803d0080c000c030400f8800350220202030200002e408801445807011076006030b031103284c0790941c844900b20141e8003400c44c660308201c1c2c000828403907441540c030440020075042c047c41202401e0826958140d03120414031840074010850405c4001400e000512680300031b500740b005545507008640c01010b5050382c02c045407120700c503d040d40c80d4428004036600038403500c402ca116001350729058655010302c00e4148241c00100302007900000305056031010503030040e440e54441400340007500f5002172213080202d041e400c1c40c14000f22103103c84561018480030b80c1100b245030500c0d0303505a44500c030b90a80c0b04c034a070611040101c1c0e40801d8459245030184e030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 908817949 1250 908816699 908816723
    0xd120507030e16080c010e01081b0c030c0c0103061703030406110f040e0a0b06030105031903021005010e07080a1104060c11030d08070809061302121e0a03260103 71
    0x1c0c0c01808000300010201c1c040c043c031001a1641c140480402c0d124044c0480b80c01034003000042d0f0790462000003690115030f81400241c00480804010180710324080d49003820301e800c2d81e09844ca16000880d0000e220b400c03140350300d0681d50f8541b168030000e08020110f902c0c3c070300f000598180c030782c0320180c00903100365221090b1143c240c1042046414581200404650355640d0b04030482d4400c8040d00e0400340e20b8249039140b00c4514209040c1c074140c6030018007034500070004440700140503684002c228150f0292100d410030000d000c0c807856000300b949440c00c4a00d498500e400801410005000c03841c2c40c0d1030081401c051510352010342d4261009410a440b400c550707070510000c0c82640740300903981441843c04d40d40039190300020780b078000c5803140c44541d21521841c500a840742d504444000707100c00840c00d400d025260400d91214000c0c81d403025288040e290501807504082d03442d402c2005503220a11000400d83d004c58034220020741c0e041301ca10350b1010601ca20381c124506100c003600d4805840 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 908819199 1250 908817949 908817961
    0x209030a05101406030d051b0c090c07120c2a0b0a110f0a02030c040b0103090f0c05031002040509070503060613062606030d120f020309010b120d1205 66
    0x1840c81829004000c81c1c0d000700501c06100c01810403510700010030300c118000b10f091070800040280350581ca82e00c401c0e0804165400c104002c50846102003910710030000620101c0e00d80480a5000740703111001d059490380e950419104d40da814040c07203020003041c4002c001c0820b4001d0030031040d10181c200352440c04040001040d1210740213070020b048640f4005406100140c0085003c007180c45079105903030700c2d803483d00c01e0a0b40b9040181000b07901070b0030034880c5600519003a0f20103441c00c1e074141000036014107503071514150300036000d00c116014418620b09104600c0d08101d00241058411001d500e810706060100360042400b62145050080100115115070b450720300f9180c010700120000901d03184e8a1034000d1050040c1d01c61446516212401e08001d8000c1048140c420b00024004011002e03050b8000c6400080c0c0c03d12200e0525950034103041880114002503008a200400206502d60904104a18100c00c007070b104000d540b04000c015040c9401031451030080000c0b6000203620b81e124 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 908820449 1250 908819199 908819203
    0x906040506030901090203070b0c0d030f1b020a03030f09020a05040e0a050a0c0609050108160c0618050a1b0303081605091c0303050a0209010c1b03020a261c03020903 73
    0x682140360700140210030800090815480043c026000310100c50005036180105007652140f1140c85405030820100e6120450007070300f100d4090003105200192015031640d100214007588505080183c22403800d2000341503050103444544503100e40104441c85050f400a200c2c40e445106140c0142d4a90400b600045403d100e030600c10341d044810380b600564180742ca00140302107030180b240401e4007003902140c0c03540f2071103841d4482c0ba0102c40c10036443c4d08031242602c03500450f900c1103481544480d060280354441c020380310010b0348204020700e00007043d0300e070001256000401d140b030140c4080340c00300042030b0300406540e00f011101415000c0180044400c036210b200c1c00c1c44558015190442d40000690803803c00450a802540d007007009807203118142c0c0030382c45403811030381c0040e0080c80c00c1c50104000a1204509031800c48031415900c0d0707a40c0c0070407001101c039405100c24480420507000b46030301ca0414410305c0c6805801601070395020341c40714272030700000441810030140c0c0403510300380940341 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 908821699 1250 908820449 908820457
    0x1a0d020108091501030b04120309021e0a08011508240f070903050a12080906092d1902130209010207060302090609041b1b2a090c030212010803031b0906 67
    0x1c2c030401160f09603101e040800201206450480d04907440303084607103210f0f20900c2103842040d0300400c10b141c0c410041080910381800ca030340c541e41c041e1001600180b111800d200d860b02d40c9045403800707012286042e03246814640002040d41940c260355040c205008210100c1d160b1104110901c056142c580788422a040c2400c2c0e08024101d1054441480500c0304070012007a0925195680317103920340d41c503400141c0707500e4140c2d046246a4003c0d40c40525030292a5100700d101001201d01a00010b038104116160030322404003602c1380051010548250301701000110f04505080409603d800b682500003907407215170748105801c156001c00ca882c69603481401300c1e20070302c200610920800519400c9070388140d480010a4000c41d650621000380760150512945013241c0014103119031402c0c0412194501500e06d500340d1540440e510040751504583c8140e0b1407242c0250f13030040e20f904040b100d00c40b2002068002e074455500c00c0c004c10200c80400e0f40312002140d1a81e004a8444d2a0345011540a0103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 908822949 1250 908821699 908821723
    0x1404080f13091802270403140c0714031c05090f27070816050702060c01150602060108070f050306061002071203210e10021e0d0f1a0d02010809 63
    0x2003001800b0a00c02c200070b0a0640f078600844400c40650244290300200079050f103e0b09603510b00d9800060086809990030010b915540c2c0305141c54524101201c900f0010141c014140c3d081145000064030f080401912451000c80d80c2403000e961600b0501174464090110140d10462001d941403015450b100300b03100005040c82d55808000c01001c0401015400c02c441480c00101c02c50700045025601d2301a045000c4281e480d158501040e40c0c0031322003280c0c019045400304e5901e03243d13030312600490204103400800c0c0d981d010b0850385d41071840641c204003542e0300043c0c4120b41598241303ca95070101c0c0c604d4101c20201c800e0b481c00c668055059040c954070381c0c0f15201c2410751030a10405c1c55005044a013046032500e850044040029450008480f01480003083d80d0f0b0088940724091a2254010f00061710241007010030080c00c544a8200c56000003007400750507454420726507070015180281c0e07400b80710307500d4074030840c4a0000c040f0782e600321840ca020b410010300d4000f00e80d0300d030002c0c090655044 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 908824199 1250 908822949 908822951
    0x150f040f14010c12060b0409021803030c031806030609130203070e0a0b01031103090303011206020c0714010809060903160804121b0608010e0604091110030506041404080f1309 77
    0x1581d81c44030a00816001d03840310003013204003407191885910b80c420413081c3d550703c502c181e080a051006200c025000481c059646150b0407169058660741000039000c00d0400500071565141010034640000a801000500540302401400f4242c1d45100c4820390103801030104010f034186600000b0300d0f00c10f01e5406524201119810b009206c1d140382c01966000c042a20280001b02542d80410400d1004803100c0c0141d070424001489162402d4900200b0715001e500098100b6480744030a0b07040001507407142d1141c21880c4200c2956503000405950300074221805440c092403c069110340343d2207040602043c80c0400044913041107078020075a0040c002000b004240f1000918102140300c00c00d0b0000c4004099560001a00c2842841d105050302c11500342d814254403800107200142c071541030100e401580b4203d00b50304a80b1056420303e04045035a802160906001082c082241c6200c4c01c240da00b0300e5420100b00200e007aa8084034521041d001020395110b1080f401c3c140441001e81004c6121 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 908825449 1250 908824199 908824223
    0x907050904020f10200f0d0e0109030b07030b0f0306060307090c090f030507030516240314070c021309080913090c09060315020c19022b14150f040f 65
    0x181e41c48001c250a50740c40d5904141e240c0140c6848940d5a01b4440e4210226400031101c00c4080c0e00c1081c0780d401718407041c140380c14026102d96400e11000c20442e00b1000082e0f40e2801c100300781c54070500d01c0855010030f5015010038104100441e403600302038081c1c0c54982d5142c00c00311144602c04c4029200900c03441c8100000f0903100c0ca00940c0324070340d034401942c1c0da00c40d508216051000441640045410002c0c85854001010b0448070303030341c505914580141030392006400c0202c0c441e500c29078401c1d042c542c0c0329a2118800d02c1001a600d4018014103512880d20003788001030228040350b40c907050407a00b803109440c1c80421a4090021448014005168401d0025009044da0002d00c1520b00c00ca6540d07609041d24100300040740a204601001d03580a00381c44c0c070078480d10f0a4130842613070001e4280c003132405d1004c02150380d281400c034000306c0380400e42a0040a01a030907103500c1c80800d460025110031f030004c520f402c0c41d07450090181e20380c031b00031480410108800c0310f0540c21142d60000c2c8043e10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 908826699 1250 908825449 908825479
    0x2060f040602010e060a1b080a02040f08060712020f09060f090a03050f0c09041208092506022401032910081606050307050903120c240907050904020f 66
    0x203014040c41c00c050300d115090100350320706124011f004c4500e036814082488030451160031600010040e04112142c0d9007040301007214410100e0304005032030309200401060908010091500ba071a050012140c0d1052103e103c0060306070b070880700d034601d04a40745a105c00500b10310440911820006950000704070780008200003002c914a03010310020300c251000c107118207003032000d940f504460040c08494181103580362580186600d80d04010a1800c95102440c0f9400522a20040302c00800c4564030b064810403480e5810440e012040d68140c070103698602041259500e0031106003c02041c109001300f030a005511032a40b812103c0380710600642185c01c268900410804081c001c1c00043d00400c164001076052281d4151b08451060340c0d0149995140e203400c61740c0d41c005808156050040c850141403010120002e4a8030b001614013500c080c10b4091142c00740700c54a40200071004e04040104420314070040f890303600b1210141c40642c0c05a81c0c520029000d48200020705900c40e5440b0a001070b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 908827949 1250 908826699 908826701
    0x30106020d120b01020c1318051609020903030702010318080a050d050114010807050c0c03060405010501060906020a050a120302040513050709050d21090e01060e15070b070c02060f04060201 83
    0x7034a041036110b0302c041c0e040c50340e4110141c1c3d00403031020380541c1c82010322080e50304001040f2907500080150010703d8000102d501141704000c0e4034107540c44c0e40414001c00600d41d11103104401018480c00c01c5240c186410f01082c1c0302e010f0104040d0502d81d68061800207201040b90b41660140e020a046a564502c0400038203c0e8110303800d100c103c03034500000440e942d8a04503c00900f050143c40b50603080c3d448001c1154954882c00c2c81c8091405810740c64030703642e101085420700440c0300d0000401c9079810f1541c000c0c001c0c41f040d0b01c0b910071075000400356004150b001c2804200c10350095000306148030140b41c2600a4070403603121a40140010900b400502000d52100c0d005a601d85e8410300c00e01d0783c60040215a90184101410009000e01d40b116640d006d081e000f04070b4243d42c10001607250f51030201403090340e02688400085800031071450018540b814034200c4803811401040d0a181c0d807a1103c1c0300d40b18004202905000000075100250740e103410030740c0c103602c002280c003d07a201e8495800074 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 908829199 1250 908827949 908827963
    0x90203060c0705070f0626091005190f0f15030803161e120506100909200a0504060207060c0b0c030a061e030203060c0c0c09041a010e060f031b01120f0203010602 71
    0x45c5064021403540f0240c07080c01d07100075000301e85908c0101810a007a2aa445c02010040c026152403450301100c1c95095208ac0250b80f50304490760000034070b00c0c1c2c50004040a0717810404408550a0484500340f0000d44440d0603690071603048281420245031414040d2401380e04442c0c41c0c0026a0416209948141e00200003c0c1031100b64805020755100c0320207120442030040b440c0004602600403d00c6940c426a00110900c0d0350100c440c1100345c0800241c1207254400000b0384001080040c0c144a4180c040260b040241514584030324040c03031548841000890151107030f03d00120010204450b01c01e160000d001508070040b1851541444060118040e1b8061004a0181c020706001400c1000c1c40000c1d90404481c100141000494003010056041002041180c110003010703802030f503c6070032071904c034080d008203c161040c904100c420010820021000280701c0c4e13001000c1c000d5000703a54809180306030000e09020815009400210380a40000403c4000180c030100001611541c001800 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 908830449 1250 908829199 908829227
    0x50901050303221d011e080c01050d150b04030c0e0c0a0f02010e12030109060e011503020c07090f0902011b1208060a17070509090a0b0402131b021e01090203060c0705070f06 76
    0xc02c0e01c4241b0706d014030403402c6030712583e00e03030f41c00440d949882c0354000c034010041682c0c40c036030001c0d1000148400241d003001c182c01510b24404c001c01e051040100c10700c4210040c081a81d181c3e8514030303116600482c9071207029180e404004464441c101014000d4002c000e030346043c4d4054585d44c00d000d61101860750400d10030b43c1c01603410814005282c000201009043c0c4074100e40303140c0d00c0f1100c03980a80180d0310034605812184200341c000070380000a07200f4120494882070022681000c0b90000501c0550103102c003c40100e901413100c80000d60b0380f00c0c103200b03a86075070038500301c1640c1d0000064909451039118281c80100da0304a10301205002c151201611422a001105a114000340702c0d034824502c0c0e401012454420003060140c070349501003000c84801142c0c0070500d1405104003c608010201c44040580e00500e0428600105150b540c0c0000d030a00c0001c1000400c1500020796401340600002404c100005188003409818040b00d405080c1600030780d44400e59685004100810038489 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 908831699 1250 908830449 908830469
    0x4120305060a0305060112111f0909020a120f0608030d140121080c0a0204021b060117190602090a120b0105040c05040e06030c091e01050901050303221d01 68
    0x210a4603015100100f070f00c2e00000109400c2e07003020001e00030521140d03000d607a202004030015100307a41b250b182018003a502d030185018030009020180030002190031484019005000701c0c41d41b164403c443d214564031100300410031840c10f000440040401d604000b00c00d010010740d1b040100d40d29040700d00300c030100e200c0c9401107a0303071000c1080501c0c0342d05140058540c4a4030001000c0b841c280d0140880c4021001500c0c071900040d80040d0403a4407801c0840301400d0f0890303204059050900000e07004140c04180502809030030b4040300c1c0c607004c402c0c038200c9090382001c0464040c420140d06446803454003509425034680c41c1c0d9414035000e14002011111108088000b160608082c00f404080300d640703407102801d082c107080b042506a0002000300d50103200b4107a4400c3c090b0307146017210340151041030310303c20a103812440d15210500160002c60040040c9001007041e80c0b000001c403042d800083d403100000b0080b1143c41c200c0c90b4810340c0320120040c520101d01c503001c1c120604c594101c840d0321013 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 908832949 1250 908831699 908831701
    0x309010f05210c131409040210030b0a030605090d14091c020a030c0e090123070224060109060c020612040c18020a0e03150117010e06180708030304080d110c0604120305 74
    0x1070f1720079402c202c9200540007849440450010300b0501c00a94886426040201d42d400020000c111208401d0b4010340b08151034009100c482403043c0321040414200780340440c00d41414402001d06817044402403030140140f01090798010070550030b00c159150b4000c0c80744520036a242006402185d441c06003a01c5420000040307802d4000c14400d038034242011340d078040b00c0c0d0b4001420054100344020920415809020545240d103003068182c1c500040038003840290390706103a000141507100e40e030010018028098652409030780c45800780e0b0480590030825900580e2649040010078460703903c42c1038203102d5142103006000144d006050380d031586036600080c1252000405949288004100c070a80304130000600030380c00b0b07416600b01c00c1c50300c800011a50340b44402c20189010011580310130003080492101d0400c81061000000902040000318214207294a0b9144284280402ca842d00ca0340c80300c052a12441e0b50090390401c3d49458180d9529207442d09044440d1100c110340140002d181c40 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 908834199 1250 908832949 908832959
    0x2041214010b0d15020a2a05012418091a0105040f09081e0c15010317120c0a180603050f06091005010513030c030f140309010f05210c13 60
    0x1d4071500b503503045540b0400d104d146242c0a0002c2d07001e460414104045c2c440504004441708598440d800400400c1000c1c141260030440e0846031408040408000c900042501912000c00e00e80103031041800034410841c4140d0b17200c4010819614003d1082d80700380e0b891784000c4102c19481c1e04aa40503941400000c020360048002c581e5a00401441480148855803440c40d2030300b02880d03240d10082a0b9450a006a03c02d02d20f00744c0400c0013519550301000c014000c11901204403440407410a00080c1800b150550300b1140720401400000c082c074010401d441620710505e5107002c81250b002d58903003003a0711200001c018101c111001c08170703402504080303a00303403d1800c0c9841c85802403050300309201c1c1c10100112400c0c3d12000700c881c4254581c19010011500c00c00e207450085201d0340002180329154a800206010302c00031360307580e5402c203210031000c03039030400c040517103e0000d442c08954400c4074030446a46130403200c180340301000511042000050365a00188800c54035031074540c8603140d4075 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 908835449 1250 908834199 908834209
    0x11805010b1909030b0903040302040e030f070f11041d010b012d1e020c0306070518010507150507050c0f070503030d0209120f0a20010c030f020102041214010b 70
    0x80c032500e0928801081a20381d40382200c2d00d4800e85414a25100311060360780d80759000e4524042e11101e1481d00b0001e0100218a018490803148945c480060750801c900d401216036a070180c05405000130881c0c41c1311000304002d81002d102d40000013482000100c40000c071150071141030142d102c8903586000c034584800d40c000c82401ca12801614a11079000e140c680380c611641815181035014051010681c8541c4c040c141c0e0726114104050b401841c203540c40301d0816250600160600d01444420081c01250b4208480100005002030800300c0d42c0740080d00e000060030f0010060704103503901d4601849007042d802801020b40011250840b0454086803616175241c00c2d40d80319184d4180c0c0200079200c45401e0340d802520700e011000303248022596000c00003504081e410038010155030012511502040b48501681c00480342d14454200e1800450b80044c0c901d600ba4600a014051a451030755a4140700350100c0d0017034002c0d8141144031100901d0505040307171000340720210b15401c02c544e0944074242 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 908836699 1250 908835449 908835451
    0x30b0609030a2a0905060a0e1005060f0904090506040c050a081b0f0306070320071e0c1505070c080d0206131e140114070f12090b040308011805 63
    0x40103040c00788940d544900851980c0e80300b070b5281d0b80c01c00c440301a10f4020460002d000345050030004c5003074900b00b0200040d141c4946c1180d401c011185040c041e4400c3c042c0d0310344e42a20000e561641e5075447c1c203000d82c40540521100d03180d00c0f03800c121016080103004140940540e1181002d083d80303540b11010406c40ea1810b0041d2039003988904201200b1005031040c010071410701400000112014002007410081d0484139000401d17142d014500c0500440c2111413005a43d201215003029250382e940034070303040300c519004241c489a4040b9001d0000c1c1c16691001880c00c0b104030b00c040c0000e400d0140064100c4070054400c0154054001041340010940ca2150035540e0301500c0155a41a2400b4608502c070b81d059608445110000300301400d28402e8010890044c00100001c10800c2840d80c00c2d5164000601c00f101c04c004184640343c1c0c1c02c03100013158a031042c1840e84100c950000781d540142480c00001d420340c1c103228144010305800010150503076a042e204000c452441220200031340d40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 908837949 1250 908836699 908836717
    0xd020d0f140303150d020a0812130b040303091401110d0c023a0f05031b16030b0109111317060106030e06010909110307080f190b0a0915090c030201030b06 68
    0x18088a0300138052801340015012284006d24610f0307400e448107640303886e20284451307018920100203000440700001d2110f10000b005444036492400d811660000d08034100d40c428420100c1034065003052a030702480c0c3c00160940c07214101c40d90a90100c2e0010580d0b11061001e074001e46641c5025a2401407060b000c2d8036800d01200c08109003070000c03c1d0a4079074000f80405071440501c51281200140051004043e40300f20390035041040c1020890481c104250141c00c07845268411104000042100c8025411160f08850001d2001d008078000c403c03c1c03003004401001644842d4011400c0c41010f002d07540003403000004c503089030381ca848040c0d01b00d5000c5a49044264803c40040240744a560050059584103110b440c0d10603801d100030074505010f82d0050b0600c1d821642051041220800c444200c2d10400410551801100e0b100c03229400000b03001004403030344540095060100c41c40d00c039500c00406420030444540c2c0c0741451900340e106808101e000034107101123602a41b0b010800d40300104 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 908839199 1250 908837949 908837971
    0x151706010f0c0b0f060a05090f0a0b030c060304080301061b0c0b0906070b0f040b090328020705091312080402330703180803040617060d020d0f140303 66
    0x61240001901c030450803105640400039101c04079000181802201401003921101c500d42c1410064100310800003c0c0d0005802080242c00304410340780040c02042c0c000c2c0c401030f0005284005038001c203040005004026800400000c10b0004000360100218100e038810b95440d10044d030180d44d00700303c001e01c08a016040394040131060014407034000c02041c03010320003062a490411030b40d0303420842070401c65551030603100040410060000ca05c2002e079120503050f003c4c61400140c034a1201802000b07003403480340301c1810352644034128020807880000d04001007501c1913501e80051001c0c100c011892088802d070310049182ca041901424486004c0d40e80100792101c10440e100308051441c030052440624005090844c00c40d80f400342c00281103a5000796035070705841110542100b60700c0302c0750f0b020914951041000300980d40d0300000c1c0348910450392a8604030340c7c4962000804c11210b0b00c6029502c41d441010410400c8074000600c143c0f288540ca061801c81c070004407090306e0b030200721280c4440c0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 908840449 1250 908839199 908839201
    0xb1b0c01020d3002030f090708071a31150e0409110a091514010509120102090303040f06170103020604120311030f0a1b150f1e0203011517 61
    0x22038094510914416a481d01d1640d402c081c1d402003e4034482480840d44803a58000b080c00b9481034449851580300b038034036004016031464461100d03518581445101c000d50020021800e0507806c0400b03d403075010361505030b0152880d0040c0d8801c40d00c03461070846418041405e2000401c60034080c2143c0202d0310680390f1804108400c4144805070410f031004452824a006090000f42d03980007903500540403d080003d10131501c8202c2c45000710150300f2102c8888070035171824a40e6a071003001c80d248218107940220b0712b03100610109000e0b00904a81c281e05000200e0041480b00000700180112109c6590b803e0121900c2c0004000c010001e00010b50001c8003000300b8411109245e80350050544213142c1000c94420144070541540c000c0c4210204440001031000d4013280e0101c00c610100280c542c810b00403c5007035582d03042c1810911000c0b80c120352503c2c8050792903034041d80032200c80400309901919a112a400001c0298024003410040d030034440300c001c1c240b5108204059030710000140524035 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 908841699 1250 908840449 908840473
    0x10801090c0f123b0105060d021908071512180303200f03040605061002060a050615070b010306050a0207110d1b0314010c030504030c0221070b1b0c0102 67
    0x3200258440440340e2a4442d920b841c0e14a03000101c4d440300751500c1c0400d03d141c001d06480203902c80c10201c200002c41e030500003806403070b555007007001c0c144c00c1c0c2c12210240c0c00e01158080a280d103030302e540402c036140503141d030014100003c01c00c0c0c40c180c40055980c2041c0c0580b8003103810700703c603580320b84980e401b14011003620000707020380d00c0421000c60401880c0c0c111600108160501d0380a190b620b03641c0032010040c8402c000312030041c10341001c03003140c01c094614040c070030003542c807200140000003807601c9001003801901c440c1540040c0c40020450075580d40041e04103a4402e40c1c0c20310040f0fa405142c0000195446454800d544a0381c3e40703d01d2400c0d240c09000c080204502118a081da0908030b04c07a1600300302c10080c500400298810030401c051200c40701b007141d08680302252081c007894207201c1008000b81d440311080300240e60442d07502c003842110034505030101c207118515405a01c22854040759125411000e00350078100043c3d12014502681015a1181c50501c2c075030b40943d0110044400d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 908842949 1250 908841699 908841707
    0xc030203060a05150a060c3c1b0602060c03040c030c080604051b100518031c030509010506091807181d070f03031b15050105010f17010b0705120c0705010801090c0f 72
    0x80e0f603260880da0441c030342c1c44d0f42110f040704802011412800141d2911004004601942030454400009c1c800d51071483c004019458035801086488520342c00070004040161001e15080038682207102c880b15592604a401d6a81005440030b64071f80c41400c007404201900e8003811b407460800980958804005410300307499903001041d040030b032010b42c041000e003103480c05c0110034403174a041c5000d003921094624015041300c002905c00030281e41040200656502c0704100c95420440b0101e40801102e43c0300291410503d06410400750302c4500c2c2003007801104503401400000c55a01100030500c040954420340e26100345c4190b103084003a0040420209004da003088400300100d0f800404400c10664490041c1004d83c5002c60003d03680b40c0041c0155603001c054055512900d04100000c0d203030401056080e000140300c1d841c3d140e9400112142000014002c0c03034000050300c1140e644441c49a1003c0da204e22907030045900140f06003000140c804618007a00901d1402c43d1900740c2d210450b0340b0102c1b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 908844199 1250 908842949 908842973
    0x302010e241f050f03030d050f041202030a081902090a060e0a0504140a2705010207030e220b01032904110f070f0c0b0d06090608070e0c03040c030203060a05150a060c 73
    0xda850701050081e0303119001f0300e000c0c0364442d1142c4403000c0102d207894030b0140090340a10304440c04540c01442802006074200f000700390850720401440e80225003210806c1e0103449000d485640000c40c207900010810f4103c590700364040c0c02115101080c03502c0c0e10038842210490310800400e0f402200214500c400d0a078040660003c82800188041c031040f0850008144141022940c5030750008a0600f45540451030700180141141c500441803121a2146406078550342003c3c5e1241e5900060850341e800395000200c003c403507659800080500406920002600305152405282026046e40381c2400e10402c5800d0070480301e030312904040d4140c41d02e0101031441c0c007040700c4000c10410007107100c0344000003500103130094420116071103040440382000e4420781d42c400440750303010403c14400058140c000c0c650042d440745116803295624107080c100703002a13510280d0980580f0301880b1408100d900402d106145028000302003c011200f80111420644908400603800c2d1845800007408aa442 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 908845449 1250 908844199 908844229
    0x206040c36090f1401060611100e011b090e060f061204030c0206161106090a03060e0c0604060f020c0d17090f0a1217120f040302010e241f05 62
    0x103102c00039030b918a2403034092144203644d000205000e681d1005403d0042402400c0c003445c00810a80d40004000da03543c1d119119008283e4642c24000b5208209503c4880d998983c0f080303807007030741100310f4011f0702801083c001c0b40d00d40c4480100003401800c00202d0001c40b88405010301c0d00d003541000884005a801a004078100080c100d050340c027581e034080143c40f950100041c038034544002482e0140a8031504001d45024010612032382c8412340d1181d104a04894110070041040c10352540081c3c04d00d52010b5001d50302090100e07000ca038050780f000030b24610000a40840e180c0031031110400c50700034003441000780140030807a5410080544c800c041c02040b00050805c1d4016003564002a003103151603000460008010780d0071000340310035a110007401c19041c08219203003130444440c400081e5001030400d1180179074000403e080601c01d6101c1401c0001d4681601d94801c07502020400b10403200e903c854101805034040f0b0660703151140b240d58000c1c9800688d9842c20300d4201030012007e020451 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 908846699 1250 908845449 908845451
    0x160e060a0306030f15050603010608250e04060e0d021209010f120603050321090d03050405030f030109061a090901182a031503050606010e120d0206040c36 68
    0x10000028070101c0300322145031701c90500e51414014003080d01013101c000030400f5109a060820400c02c483d008180d04244454088800c2d03d500301555a4a0b403180c07003640244c1c0c036101040208810310089500c0024044100c800f42c8d0380481d40520202e07a5041e46003000d201204042007603c10941c011800c000c55146142031484d2000705c900d00c0b01c021601a6402a07456030000a0080c4604d441451026034521000d186c040041c01c1004000307940d0043c0d21034880901da075450100c1c00b0701c203081055843c0707203510317202d5140d4941e11014020090402407041e0144025580508001c0c00411020b1391800d120290192100741c0c640385103040021005481d072b85486135180058210040384114009407d44005820f07142c54101e8000102140c600e49442628040c100409000152000c5291600040700740b0703000100c140c3d40d10000380170741042c0b914103295108e2a0ba0460f409900441d04610550183c11110741d0399a03282c000000c8100901c0c0f40c043d804080741481c1d1a0068008075020442c0c1c9101c0c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 908847949 1250 908846699 908846711
    0x3120f0d061211010f0309030512040f0b1305010b0105040b122205030315010915030e15040b0702101b0c050c030d0503150d020105070b0915011508160e060a03 70
    0x41c4540504002c050b007502c00800342c0c04103202d2541c0001c5406418415450304101003900303074500520500801c4c0c2c0c400e0181c0c3d0140c0210b03060003001c0400c1402650850f10140450404840d8080c8440a8030012120741d400c02c11807052541c003c0c41600c08480300110401e1801240340f00040300210001c1c880c01600d41d2003000c020f1a4003a840e40c2c10001440361b40215034030304054801c42d540e40e8504001e24100903144100384200d00641c005422000c046040c081070840034a05040c4c200765801241021040310041084203112207512a41e00400c1e00ea02916502c0c0c032172010b004251811080f600b040d9a001110001000f0f104c0c503030190200c0e0244003614099401240040e050a180d40c00010000724048180300c403524a040c01041924802c54803080403528913800a030242c02981c1c80600001c03004000600d07051004d2040e9101c11428191002441d0384031301c0e2a5201100c0d00020320006550000001c406608542001051074059290180e0502030700c07040080302c0e48842001c40403d43c40e50 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 908849199 1250 908847949 908847959
    0xb120f09031c0506042a02060a0b06040b07031704060b01030b092403030408100624020d030506060903010504081c0e07030f050f012a0e010e090901140a02130503120f0d06 75
    0x2014012804441440d003980b20b180d0502c000d28146001d404274440c2ca28150407203019560710000c0700c00311100120034039118411400c083c3d40d00440030a90300310460101040104001041d408040341010980341005408044003d10040c10000c0750811680301207000c503040d064420640c0055500350040071649411344450710703903051680d90082079010035144c807010700550b682c0c220082d0540103a014241940c09807444002e54072050100300c00107147d658004140551180011100e2050014000b80a2414207140c12440b1768018140040e00d03510029a01451107118003400c5140031031302e00102a090f08544a124a0800c004070440d014440d402d015440200d0a018400b1100383e40740e110410510b81c0b1341400020201f0341900070400c5969215009181c0c1c000115000400003605e80f10160742e6020101c500402904108610b000c480204010b48016070380c000b0841d429001d082082c0c91580c4a00385070b0341e034440441d5218980300c2807140d2a4138100c2000608560801d0080211302c0541d00c0d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 908850449 1250 908849199 908849231
    0xf0b090d150f1a1503042109090e061f0b1218060103050105271519022704050106080a321008030901020c060d060b120f09031c050604 59
    0x8034204003204101c80300402030504d00b00c0c051401040241800d80e107140740a039203c20086403440f1a013100c0604140c502048281b083d4901006000070ba2010801a02a64511075840350212140c15080c10040f0b04124403035815907004d4101c8400c02c07021401d2034400d2500001020008203203c4100000b81507508846004110060080d0b008000024207400e00140f0a001c03504c480f0305140d611050f41a15400b42c03400090300d18070b460101903121000351105403106604a510b0441924803c0c0042250154840000c81a840140c420303805040091150000d03c030a4071800d00c00e610100381e0b24030014020a0319034028500e000c40040520344545038100120001c2010450100da0080010041000c2c00d8881143c11000c1c0503204015410300002d00f0000307503100d1009003d01d000306004100d04000e1401a08070a024081c1c5880303882e250030407803031014801c0b8801c542c41045140c01ca8007089406c440441124a092100c09640121020305480d00d405880003800154205a0f54003540212440e4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 908851699 1250 908850449 908850461
    0x5010203040f0e0c12190615120903020a060c030f0609090507030b04031119110f0a0501141207020d022803081e0702030a0e04110703180b03010f0f0b090d150f 70
    0x1c06c685040401b42042d0018040320000d420508000440895803843c1c65000703040390b4494000c800380071030740d9081898100d05000d0b000300c0c010060340c10000001e6000340c140d08400a50b070700c86ca0041145698503102d180c00d0300ea0464000c4c0150700103c5060001c41c91071507501c1da000c1c1c00b0b4103203d040c118805150519042c1c01c900362920a178403d0100f103003084035540d400d6000000880c1d40c0c450b000040310000700c902c07c04e0310034070741840a92860924a0441201602d8011781508404a000d1800d0b120182d21003040211a0005000755404550190040702c030b00e603c00529010040c2950b00c80d40d40945d01c911000c0c1c0700d04507034036074110769411014842302403501c07a10580c0d02540c0c841c8031030a00544000021b40145114608240d0601076a54240d0b00b91045a40c0600d0035400241c0e00f0300401c01812002e0704140000080040081400e50f0303210102012945c4080e030f655902a074400110180d03008200d0700300ea04c9084c0e0003194001c2046040032031130141480100207800748003150020100e41c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 908852949 1250 908851699 908851711
    0x13060f050c100c0e0904150f2315031f0f0b03010c030f0f020901050d150e0f0709441009061a01122003070c0c05010203040f0e0c12 58
    0x5158071851005640c003c410030500503055403180e005d0304103696401c04d203414050800360110354560007912121aa034001d00c00d20590410309070710003074056004230f196880440309841c20740010403e0a80a060014244c150600c11502d020902004040392001822071050002e00480d03e410542245907020302c1507101c2c3c0b81894400041c1c075032214852000340c403191165100c0d410310502c07015059980000440e180010921800111a00070007484403d0f00f06640140d100318400740c04214580041051241c0242c2d040c1d00e80f954595950b84451440e401b91202c0c8c03aa6400503400901030305144144080781c9080c000c8421210000300ca58600c2c6042c40c61280c00075065240c7c1c1400301885120700c15540c80300c0d100c050b0701c0e0300d864800c0006000c4407041840001116a90b10040070b410800c1158070601b40b02055400e40d90381090700005206820720802a44c000412400024107507000000300e604844d40030020101240c5450b0400d1a003800081134a240c141e420010600240401008a4807c074 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 908854199 1250 908852949 908852951
    0x903041a0714210a090e040f23011b0f08070c0816030e040e03090d080d0617010f0605091803040b0a02161d04140312270313060f050c10 60
    0xc00c0e9007520300380c04040010010205002c202202c01036911103c0171055502d58203003d0810384803440c00f00c2c090341d0200f201030103440c00ba04e401d90448801c2e20441042424200c024040e0b50700519007480d4420140e1042400300310304c10344038828203014964455210350b1609200c800e000c2d0031b46a500007548a1407441c028001414880020503810240314001301c14152410040c6290890140d80d0364420000c03141c2c841d00c0c0d040d82400811800360704491884a4a40051049a80c1c4500c91001c03000404031000700d039420a60110703c1c2864038070401c400c69200426490b800e8030741c0c040507a49603040c606a142035000421000c00d100c20080c1c010680a56154018010400f80000744100c02d1615000f03041c480007152031400184016503401908a038003c40c0092420007110009855407048a1440c0c081c001d0746000c112010000c18180130507483c00400340740d21003810321140d80d1640304100002803042c03468101402018866000e820107141d0704e04160740b519024501803131401c1c983c1b02d0304400003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 908855449 1250 908854199 908854213
    0x50909040309170601031101050328092d061e1d010c171f0e1018060b12060a0302120a060612020d03080604021317150903041a0714 58
    0x103d403005901100d4165107a001d02060350456032165400c1044462440c10003034080b0114803801001b0302010305001043c00442580e00c0300c0411100985117200c070a855191035031100c0011414035030f41c2407200203000004000303c00b4250744e0300c00091480c0211140601112001d1921801d40d40c814407481f2041c2c0c120083c20780c1400e0303040d1800d68004001401c00c2105110b1023404011086103400d4012000321102502e0b428603d04440580142c0d5110041c1c21030b0800503c00440780e1158400240c1c2c1850090f02c04031840642c01405444c064481c00c0d800040410a140c84c42d003028010b01c0d00038074010245105540d07640c002034071030f1108410082d42500980a007070f040144074800c22009199200c060241e402c06ca400040c10f00900190150034400b1000008a172541e0300d6044400309031191314900ca0098451101103035180c040b6001f4101c2c0d220703401c40c8090b015a40070b1f5007803003011010000c514090030b16280b0040d61f00e0040000d1540c03842407000710700103412003620141c00000e45c40141a2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 908856699 1250 908855449 908855459
    0x306151e090b040305100c021504030e2202030414030301050d11030a141c090b090d0311010e010222210309051f0e0d0804140319030c0b0c04150c03050909040309 71
    0x2261b00c2c0041f80d0080d5403160002d800d81c940180420b642c00303a01410b0a455860440022491050511000043c0c65041003200302050380c05901460103580241103200b913200154001541d240310a01a59a0002d202001d8100090441d00e406190b000c0c054255080246203580c0e6201540e16641740f1072403034024000540002d270480c0d2400e46100300c240352103640c0b140b0741891180188142000980981c4020320b4034024540991185480e1100440080042c41c0404516034003d400c0300d000700d42034003141e40c484801c00000e0078194060794954185610401c5801442000462010742e08506012600c1800680c0381e580d03040384c05000d03440b10301c244d00821610000411101621034101d1007060a01e0140002c42c20140945007a83d81c40c90b0018080003500300000c2c900000c0c10360b4400d1f2050003001c0c0c0d500f0190302801390b5030fa17207110b140b0307121941d10f1308540840d25006a016810150185003601003500e4030408940b1074050003410720914026011000c201444011603080d0041036510408002c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 908857949 1250 908856699 908856701
    0x16020705040209150d0501180b060306040f140c041a03240112090305091f0c080a02010e0f0d0828110f1201080c01050a08010e090705060301060f0306151e090b04030510 74
    0x9082813410034208135a4902100080b081e00000c0c090a00a554030240b030304d3b0040d0260b0006130f1942c00c40d4040400d600d001010b04d5440d90060007054000440203c5030520710840b0700a4900806012041e14069501c011004c10026803048009041120424074449142e850b072180703900f038a01076035a06a031600b0140903c05c04008003c4440329903000ba840d10001300790b102c01401c209039807188070749542e080e50420484c050000d12815038075174013030a020380d07090010004a1030200601c40e01c601c00940da48d003000c141852108000000380be100004022000d041e954008030003070242c181a5420b200300000c00e0740c1142c218961170100c451500e40140460442007040880c105401d180c003915105030f840b001890a1410320038120694840c0000c284c00220900c0000051715010344400d07125a0350300f10082040e9494085032001c20325200b00854a500c101201c0c503069540d0341c542c0d141401c0000d0341c44080101c07001e245010848036271004100c160b1507000a00007107000380000e25040d40180c44040c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 908859199 1250 908857949 908857979
    0x1c1a06010f08042003030c03040e150a18231e0a0c0504050f030a080c060a0b010c0c033e01270315112116020705040209150d0501 57
    0x40c041c0b008910401002658065415184103400000c4013450318650000c02d145005012889280340000b25000c0380c0460210480352041141164403d0000b02030804c0c080ea00c4802c1c00f40d44802402041d08004c540300076003040b018822488242c40807580b00508941d2100020740d80d1584913299003505411038082d0080c155000801900c04011461200801500d10b02c44c030710401c5e004140c1c1c02401d059550f024020318039507682150303c403070303a80e000d114100b038452500b254403000c1c3c1d901d0f040d80d01ba0154811076110001c96840314440c9071040c11902c0d981c40b051080608843d5182d61f58000c2d03900c1c000070154655803001150000200c8141d1203001514843d2002601e107003c0f40182407038807a001c1c0c4940780408481e0040b8107842055091210381000d08440d45284161410015403084500300301605841d030040384440b4207070641c480c4d10204d4403109000002c00b0059004200a0045241580c002c240c0d040009003849442c084800900c442c80e00210341400049a490380100030318045043e081d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 908860449 1250 908859199 908859227
    0x10e160305090309010c020307030501092409150207050f07080d0207062d02190b10060507050705120a050609030a0807171306020c0a0609121107051c1a0601 69
    0x74002840c003490740c1d035920700961318414104004440c0c04415500c042c45483c0265030400002c2c00140350604141c101500c00402c0d009507808084802c0440750100d1190109643c1d11840c0207400802503800707071000c1d4200700000c0e00c1d41c0c001c0c400281c4401504008034030040c41031102400d24a00c810b030001c0c1c04c00300990300003414403e00345628075510300c8034040f81303c10010b440d04541c8034948100e8101d00e03040180400c4400083e178100031405115001d0702092090740303c0d03220304505a440c0c034000c4805000e00c0f007004100c3c0d030011605200a1801c03c00d0004800c9000b421600c500d03140f600c4041c9000001c3d5507001040c0c200044c0b00d006c5a6112000c81d07801400390038401708800900f813000695190046c841440550680c804101b04030340d82c2c048890481005003198049225400c004c00103110030345044403440c00e92148005d00c9030044825144905801d0064218145400140f08014031001130468064500740c0d1401d0014200001c080700c184030910f4881480d10b041030015051103000c7e101 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 908861699 1250 908860449 908860451
    0x305220c0302040518030c16090603111002032223090103140a02040204090c2a083f0c12060f130203070e040b061207081e010e1603 58
    0x400004503100800600031a941901d0000b8540e450000c0c000401503014405c01050000150020711483c0004129009101044c0d82c0b140361561141094100c400e2848024114207030343d1650300b25460200c460040811803401624500361140300381c10301014013510b8a2003403078a01201800701111203210045402070640030942d01b00321001c0000c02c24113051000402c024000710ba440c5040d441440b103601910380c041d01c25074450f9103c2600b80c0103010317054826800a1007044144200c20000c0d0b151142418136080300200e09840b68447c4102a844442901c003030340542881d0001d07549914140c900100e00d84a040002c1d10f40148100e40c0ca5031010341111500d89041c40b1012039200d503000d03510340040048980c004440031910200d100031414070416900b030351022042103034031034204894603071070f442c01c45040024402020400c4002e0246010f125901c644c0c03c00002e80d01d0340550707a003540000310000d07695aa441807007424500760740260021055280c042c070501c00c005015461510030310724603081c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 908862949 1250 908861699 908861761
    0x5031309060905150d06060509130515071b0201050909270c1e0d02190513060b0d05060a08010c022b02250305010f091403040e0103031206150305 64
    0x50104c0155554001d202d200d41400c0300040104843c40d030110008143c0034100301c985141000345003100484400060304e0500a4008887c1c1819014400e10320071981c3e07440b100481401000d0741daa00010300903049041c40300400c0700031250780d500c120319032141640148080401c0507d91020390000b9011010102c43d07480859030752501d980b404100b46658a210040c010520380482c000740d0442d4502030080c0d0410707040646011418100907808095410075200c282c400c140e03949010f41152001d104550000b50280030156201806402407508444000c1250304455107070035000d800c4075030105109015034050088161070844400b82c40d40c0c02801c8411220308031000420203910b070442c6003655560180381440001400040050f401c01039508000200b01c41c4d0b00c00781d500720003002d1012066441c040c40c12865002000e0000031101038079906414000180d1070340d0307029200c080d60700100d002c0898035680302007003000507550303400c1c1c000b91159004034140c1411095440e0100712102038400c1501c3c030030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 908864199 1250 908862949 908862961
    0x50a1404081e070f0c0b120c070816050a02010e03070501170604020403080c0a0b0f0f07110313060323010810050901090206160209060405010f0605181507060e06010e0703020a030905031309060905 86
    0x10350088d030000240c3d85159840c0440d26000681c1d00c0340b0b0300318401120310302000f4024400001000d5a40e9032003a01d0707800700400d10408050751100c082c89040d000401001480d601d80d2240c04240350410800743c40981030544907550200e494010034501c450345d601c07507054001071110305581e0139000f22003104901240d040109094114039070040202052000000d0100407001c4200105c0f05003001d0380a20010941d225200100034103003a0700300109002001c1c2e001c1d6500d022068104e41298821001425010400c803d100090b103c0244610001e550360481c40380542c6502006001d410403030040c20304101d405104029000030050603e6006034a84401031090301540200c50f0180c03002c070b060840c4c0380da0812082100c0e00c42c02d884840c4d04014020319540c0d10300407410141ca9070a01c134403400d00c03c080840c1b1a85a550000741300e100e00748414100440c40c07403400382c2d008202c900c541d450049103051164071113a00e1070b84030f4120f0611021300352400b0072010100b44100806003440250501240c01c0c1a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 908865449 1250 908864199 908864227
    0x8121905090f09152106060f0d142406031b030709021b0304090501180c0f0509043b0c03070b16050a0501050a050a1404081e070f0c0b 59
    0x428203005803441d07000319030710b01800c040ca2601307640d0060610164412031008980c0808030880006407a1240201060140c548092503110b4101e024010b48961310307280e2508120700145003500b9a080c058111001201c92244014009202441c02000c02c50f003044001d143c94140a00100c03800841280c803031014a58001c50180c1c00c075014050007607110010030f9140f0141820b50650040c05100006002a1000041d0400b5041310005001d42c503a160041c808603058a04020103000025010b903491112103019030090406c41c03401510000e1900c3d1384510309244a03041c220200156030b180c0c15002d00c8159403c5100864a600304080c00303180d18a403000c00da0fa072445008010303900c140824000c2104402c01b4605003066041300403204038000380c0c28014020a82560320141090820380040c3e03200c4803d0066500c0f50184440c21840c039521603d5007082508580e020311040780340a100c1d82c4402e1500e002030012180a54610043e8108038030b000270ba00c041e03a90140003081000c0c80902021452 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 908866699 1250 908865449 908865469
    0x804030b0609093d0e0607050304050304032306040309080d02072403140406050a05010f120201110c0a0608060436061803110c0a210203070812190509 66
    0x494143d01403036042d111035042840c0c40c1d800350307000301305001c4100d40050200d50f00000d1002059805840e225204c006086aa5100c12600905140d0007003004000041040f4100d210fa41c02d1542e680c85420a081c130309d0307030505900344c40607000a080c40c03034180289182802100010261400102461407800d903800b0213403444491024045440700302c98441e494000d030422800c5c0b10152103c0080c0b4075252074520010130003600d171080700510302400482c0b8120400007141c1a42c0d881c2250f01308240c80c0780d0044409082e4008200068000d07000300504a84401d80018040d001ca030b12070301d17800c0c58103409100440b04103200c07a850a4080304241c040c401c03d00d2075411910706c0d801c0403c00040703200b41083d00192250150b00c1050012284000742030592010400d00d21b4100c440c10345180d0251300c001c124251100f4041d240c0c00b151040c044944000c01d80c100384503028400380540300c090384c1e501a00e60070500c031910302003121307100010060a01352001c100210502402c1c201142001112404a082151 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 908867949 1250 908866699 908866723
    0x7060e010e0d020f0306070f0f1404120c050405090705040b04090b0402010f02010e030d0504061a010f03020c01141f08120a030507031b2a0b061512040804030b060909 73
    0x110b2041003105640b1080100712203088050b04450341ea0070f0007080200b4030340c00c1c2e0000c80000b41da00340c40e620003540324440c1600280d00c050205401c1900b4050144001004c1c40c0c01100e500d4218803000030b103034070b0300c1c002d4a03c03c2c1c1c2c072400a010080e1800c4144030076250f01c0003038584540d1502402e00009020740304001d030801c2d02840c040c00c0c100079881042e4014004e10605a10034817003c40c4440c0b212813280c105500c158486c08050003543c41c0c948000940404003401e2034040f8100c115040c18151003a0b002d4028141c0309400426103113a94400e41c10303c0c500a9416490b0a04100c4a0104204a407580c070002844010010a00014900b0030030005000d80a2a0410542c40340c012840645c42600701d040e90f68141d441c18182c503050818081d100c40541c40b1805d141c005010001e030384401c0e49240d022009508011803581c1c642d04c5008010226006840d5400303010020b0000244560341250303000c0c030844c03081460540d100d00b035050125600c04003c01c1c081c0303e1987c002c00c1101d08007020075501e107030710 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 908869199 1250 908867949 908867959
    0x5060a0b190e060105130306052203140c03040302060c06010614040b030403031d011a0a060e010e040b0d0503070f0b100302300331081b0d02040f0902010207060e010e 73
    0x3c2c031030388012580c0380302d442c000c00081c070a440c0010060241c19032201e40243c407441c205481c030680c60a5140f42580d0080c90180101e1008041c00c030306980440700904000e14a41e090701d1900303440307034001042d40e000048060041c0e44010014000e8030b41000c800f2403101c5040c00d0b5581400e1074210f800f8054072000b04002c04058070b83c0c841410780204400310706084008100280610003c1491a1105c03003d03900c2241d1041c001400006241c50140019001602040e0744036441d0704560024003002e0401d016107603401805c0d100703041d0045002440900301040c4a034170175540030481350500d003224120150a82c40c035000035420800040ea1202088070100c450294464800c0d10789458050380c50760310350032404c400d01000071007210300103400d038940d101c140d41c404141c158100050b001c4058460035010319017013984a16800000080d007101412200c6c50000d04020010030341c0d0f4081170541d04084031038007015403906001000c668060100d80c0103800c0c6172801c103820504440000b08078001107240c2c02c2c010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 908870449 1250 908869199 908869201
    0x106050f0d1e0209070c03030c030506180402120601060c110306280f0501120203010e011802010c150c0c1101181503091b03021e0d060c020a060905060a0b190e 70
    0x850521412a42c010703400900c0c0221a2810300341c041c16000b03034800200c000070300e4030940034003450007171040030f0150f41c000d068480c075041e65600d4043c40240181050b6881500060082c800c00001c0003c2d40c0a04940e5446c00c0c0c2040e800e1500b0b108020015800c0c42c8650403100401035601d080c00004211100365140940380541007200890050058407000c04129052500204441c00c850820300a40c0c4d00c260020010000c1c102c5450f422208242d46c0c140c240e80601da0548007640c03003200c007054150302a41010312018041d41c540000c4944c800f20302000310b02c0c00303070b40032042c48070405260030709800c00c2c02c21392075a051640d50034034120414041c001c80c401c8401e1107821810b100e540951107182e0320880207c030307180b19900d80d0360422940d40302c220301c41c10104d00034480a841c402014800b443c8003408007001c1009a58440703004d024444821806c5204103084080070450034043e0900141c081c102500640c01c181c0b0803c0207440c0c80c64a09405104506903c40b0003c01c0d0010080c22200360000007952 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 908871699 1250 908870449 908870483
    0x2a010c080c09121b01090828080d06030f15150b0f0903060c0405040b010507050303060f0111060a0f2f0d09081207021e03070f050c03011d0106050f0d 66
    0x1401c19600000120fa104550009060406882c1c10740f00701c000907250700b207040307a444100360380c0c9600c008100b50303e8a038040183c1500c0c41d507055085030420b2145a40e2401d00d90085035607421580701c4c0d401590a01c0810030300005000081081850342d0808a1060240038240040c64215480c00e210b00f4003020382c0002c8000e540c060450035202501802400d8400500b005040742d1466006030203043e104030314108180e040b940c002c0c42180c904d16444805181180e0300c01041168400e09184154140981c0c007039895400b2400b0300425100c0c0c070140c000014ad55a0f2403040c0c0e0100ca04440703c0e85080b00d0945006041c4611152006441040340c00e02c4580d0749a080030120f02506002a00404030719021851a2203140c0300f001c2c49108001c19400c6510b5000304d000140034040f01c681d4500407541042000c900400d20341c04905205070b009004480e2500392000c003003421a0350002d500390b09410408103485d4182001e00482c4000d10045a500e0040812000000c1c0302d034051b042d00030f0500c42c6103000020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 908872949 1250 908871699 908871709
    0x3061305062815030b15040612020c03040509190f0b010909050c090916110106050d0b0601020109140a05210a12060504060303050d05100e0c0c10022a010c080c09 71
    0x540303803c69064107400340481c1c3c0030b005402009010742c801c04501e00c3c07018510320381c40706880881c2c0316543c41308501c001c59107092009512105007411140810000842d10751290308026000d00c40141140341202d4000043c10308032061080310b0700c140f504041d201029603910410280565152050009103504c51262211041c801c6c1250281c00080d090200030003100c0013050444c108816031128540080f0045a103422aa003d000340356000301c00001d02c1001ca400e11030400d5110b0018000015100b65580b950380000d9924021b114140d40541d03800d00c2007084c1400724884450403440b01024500307104207110514040d448030f260030041403004c0c010392032580f03800c8800144409070040102c00d4580c00c2c020640d43c8000c0140c2445400c20002c141003c245080e0842200c11105c1c680241c1d0321241c40201c0a03921048214035140b151810000c3e2117050303031008010317072841c0100c4c80d07412003a02c00f041240c0e1010941c0da40300d80c1e403400100d04040c0b600000d03c641c0c8480e0000503540ea5410341d0300024 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 908874199 1250 908872949 908873029
    0x1030c050904150602061506300a0e070b091c330615020a0602160b100501020f0a15091e110a170a020607110d080306130506 55
    0x41d40700f414414a99155040c140c14070050701d14590a07101d950340c8011070700480c00031a044803070304a80c0802c450162109450503000010412000318a0a5a00501d8403001c50341d00740c0b400c104543d5600401c141c45c2d401040014000d1804001c8142410003000c001456654020034200e0b1504144851508012055043d44103080d8600c0c4081401083c02c000113580c8204100d60302d0007545081030201e1250740300c10301180b40842c01d030300a0500540c107684039070103504401b00e940c000341c929440c0000003035640c1403140c1c03040150800f1603040b070f89800c000901c0d141340005128031f02d0300403003540e90100b09207801440484c0c3c400100810156480d05c3c02154030381c03000f14016004110650140d042260001c458240c0d1841101d248545d6900e58944000075a04110340b41c05c0c81e40038100d00350050030124044d044060207071500344030488131000403540f42c0499000440b50410b00002701300c0c40d46811054502c040b0040d440401561030300300d0104218109a0080702ca407901440344500710428601e8400e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 908875449 1250 908874199 908874217
    0x10833030c19140f060403060c08070809030304030f020f0f011b09180209061e0a030606020607050a14090d0812010e010e04030804060b030318210d11032b0f0509030901030c05 77
    0x321b956036500c1c107242e40100700c1c0310700c031100144059000c01c0426205100e03c1e03000d034107808003451071500d4903541a14150704c5000c0d042d080d0700941d000c02035000710174007545489071240070002c01c07550314414028505109010611081c411100000c5c042403c11440120854001c10401a03483d0052400600a07000e08800c03085c04140407200c0d003402d115154040c1000c50000c0c0c900f03011598484500342e889500403a00400000d50500c49407140512034806400c07011480481035182040e488003140e200c412041054452000001d00201f003142c0c4040414010141c590001000f941003424200140001030005800c01c003810001c6424450a1340c000c2c05038042c01801c4940d05d03202025207020700841e590040f4400c113249240002c10b8581600c03251070400040026102c60100319100351042e4904138008107051205000405000d00318020901101d0b04079074501084a00c410b94260613152080d403075504040c100014402c03880800000d0b52044182400c010684040d40f9200300c610740118100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 908876699 1250 908875449 908875459
    0x3090604060504080c0d0201050f0703091206090b0c0310030b04020f09190b030f061308120901020d1a1005090d05070905070e1e010833030c19140f 65
    0x20026079a60000e0003007086680302010b0301c034800044410014030415103a400303404984204241c0d42d02c281c05c1002440e41321301c03a00b4420b646a465403622403c4440c500d07011a4541e0340c400301402403008480445a000c201e90000601c1c51508a2032083d034003003144001072200458401103000c41d41c0e000b80c2c120310040041c1240d2224944581000d04448904240c86495450500c4009050801280c50703088500103000411051701c1d00303201c0751200c94240c041500c0d0000c00303020b00c00710713280b0b809030050284844a0000d42c50b1881503062070200c40c0341c03034941040c440412013040803544400540019007140c9041140d10303824035101103001f009206034020b00d1402041000b040d422031590020b0301031030f0a507071420718085000e81484202401e800c050f20400303c1e8444070000d0b541c840d106003641b019852110038001c9140e404d014818400c00300c16811000f80003072140003203081c100120404190210343e40c0403050126840311b101681103008841004c0b448040102841d20380c0d05400c1d11034800500 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 908877949 1250 908876699 908876707
    0x4090303020f0d06060e0402090901260d08090c010c0b0a0b0a0902070317010b030108060f06030a020a1409070f0e040902030a0c06050409050c040b0a03020a2a060e031911030906 78
    0x1003030700004d2882c3e00a003808103903401e10411041c101071090341e2034180042c140140036400c25003814001f0715030901180f00013180c80c9a18041d52030911824034002d09036101e82d08941003c0940d00c0c2031a00c88070410341008907010688012800880da01394200c2c980328400101800868042522031040390860500103000260207c2019031143c0c0d40c60000c4100c42e450529079032100301c04a0244820f114881d1603074030520204041d40094003565420400090031604510290741c049600015140c0c4110010310105000f45c910b8140070480d0f603400303042c502d0b1440203012001d2020744600010182180100d41d41e403164011500c1c10802074080c103422038048460607540307400c0108264031900450032280d003041d000c00c003101100e000780d400380c1c2c1a0041a604000800034100c00039000444e180b41000a8003030080a1039954241c0c80150241210421416520b142401c00035512405140806a4000c0001851421003210030422503401440d1078002e4144802c40585140540c4080c590b00001c006 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 908879199 1250 908877949 908877967
    0x50907030b010b1c2d021326060609070c0c030c0b0306100f08040f080d111e2a0304030b010807060f030c08040b0c040f08030307030506120c04090303020f 68
    0x7101a141d1001346480b0740000701403000d0f1100039600c1080203681c118001664510348440301a12154416820010050418204884041003060564003491440606140301002121100b00302941c42ca645030003800b9034101500801c44094004050f401000745c108102000c01000d1071381e0800440c0c00c5680402e96513141c1010410076402994032234400d1842c15220340c0ea80c0d0255070640d40c05c2c0340e640c031544002d0341d5a4440075204c5070110b0741180c0c2c0043c2040400b0b400c100318407030360110b02c07003410340c01d9182d50204030300070140668880748109107442446008901c1c1d00350000340d00104450160b030121100b88000080c0346004a400042a2450000002c54034040c00600c610441d030007565680140d12042406a040300c1040440c14001000e4500150219040100b029001140c40794102c2c40d03d5a54103081e6401e44c0309800900e4290400020b000c4080d525000b881e8011034119180e68a49118010080e1344034440020180501d03240c44444080c90f00030742c1910300200031110f84d00d40e106125 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 908880449 1250 908879199 908879219
    0x301090503120f07080a0209060c0102070f05012009060a03090c0623030114010309020609040f060311040e150910050903090102070609080331030c030b07020607050d050907030b01 79
    0x2418101c1c20480c1d100000f0b001801040015000b549952609031a6407035040b8008080e5120081c1f0715080801000034081d0000244002d000c000c0c001c410300418942c00d4074044e030a442c1d0b070004545000c0c40d04214404000c801e034040300e0010314112111075480310708102c1a4050075a4010240064503081300024003143c12141c4898201050411381003280d0500700050320720b000c00c1c0a508200400703940d048209500036800107512600041441d0300700f071200c400080648100c50300a85411741c0764a020000c0095a51000c00001400c880c10700001c000000c0c8240e403602580f0500103110555030100b0701d90030040c400013040100328801400070703240520302c0399981e52214407a40d00500c03c1c400c4c00561340e40b05d90025001e68900c0c501071460038800c0340c440c3d00543c0906612904940301004545068019402035600443c0300c0c000062105155081601d46008014004420342d0082010054496400301c112040a0344000001a40351070300c035402481c100701c941004281014460001c1110028 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 908881699 1250 908880449 908880457
    0x4020f0301030b070f0818070801151802210a110a0509120f0c01050f04090501060903150e1905150403200a11040c111f1a0a0308090a050301090503 65
    0x20f503140c0e45080e01d034441c04803820169401c902d00000c00c500e0128044160a21403019003107100b008880e40780c0d0300c52000500310f417210700508044d000705440401004815202c294444036510004600b460074110481298032010070500000710004800200c44000d994401c0600c10703e2001601e0325044030030f9028000d0ba0110904601c074103080c43c5040d155510009803425500003c1010b8860103196174015109908030300c080310f000c1c0b0420310001c503888945100d094003c2400380d41c0c64640501d9810031011841d04100107620780da003040144c4c804164005030700031784d01400901410382c841c02c03410103d04280e15000f0341201008800288030605520030100d04c0b001010300e104515010320803840707903035039985e0540040c10921108984e1165190950102c014802a07003000100d14502e000c501e8100100302403100340b8078640711018049040d81e8454009201c1c40a02100703005190a40010884203484c8401040840c0001b00e80d00d9944030319040b2130090001600a0100c1c3c8a18031b005500d0707402c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 908882949 1250 908881699 908881703
    0x10c02030711040920030c041404021903050c0915130b19050f060904060518070807030c2f0709061a120703021e07030c120306050121090204020f030103 67
    0xa45242e40402c1c0303460721a02c201250300c0310003004401001220b200200c020500030740d52500560500307800a81f181d01480b28a008080c0603402a89414410049404001444a044034840fa44240b0014030005030681c028030701185c2070030b29076854800c0807400755000450190082070b410142400300e0000d420007a41710a00b11401c3c100020004103503825058184180c91740072803078551882c1c0b14100000200b40206002e80041103c40c0c80e00d000c03510050101036000b0a5105d46020000d0150380900b0f034a8018402e45001d1010310b00c2d111004219440702100b05c401007a44449040c101d4620003581040181d040080e11741482d81d401070800101042e00c5000303150b03240c000a142e0703085113410072208410b41d8102c2e10760321922050001c400a4014443c0c91921290541d0070028a241c2600a030405612980e50301e0742020003880c0084101400103524814103040c10400d1086a81102401004404020507400701040f1041c014024000031100690807910008015800f8110480110706981c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 908884199 1250 908882949 908882963
    0x9090b07030b1905150c0106030302030a021501030f03051b10020a020c060a05030f0901061a09011209030e010c030e090a09200d0f050109120201050115090b0406050901050408010c020307 82
    0x520402c2c00700111031810f801160700314501c2d0500c21031a1a84903401840c5501020900707006001c90b0180c2100c0081d0000d901503400866100070140e4100401101a41202c00445080d49160703111680100002e9004060200101d00d803a0900e80031119490000300940464000d800a103481c0c00c001d40c40455082e00501558407002c0050920308210b482c80c0340182d4850b45141d64000b10030800c440050499101e55480d0b035000070344540580b04441c002e45001190980d9103086000240c0840c0d90003020412070b89c1440d0840f001300340c003c0d10300100c071102030070102a125214642250501015161103510003407020900c4040c440a6002c0c0c0002c510941d00e1802c1d58003003038001001084060203907a8040b414821184c000749100c032142101d0780c030600020510701203c2c3c1d03c0b0a01048221a9400103079500d000400400440200e85101d0306007a0801030340c214200390101e495880307a4041c10043c00000540707281c1c3c1e40d00c030b4000c82d0002d01080700200101c0204002c001e40b82d0344200b006036802 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 908885449 1250 908884199 908884211
    0x9060f05010311180408030c090a080a060b0f0405090705060f220e010b04122409060b0a050f031207021f020319030b0319060605270912071b09090b0703 67
    0x341880c13001460240390024441c80c11640d8a000c6004a680710300401c94101c44a4107000036140c80030001c0c210b94601c0740300085680c03040e02c010312203c40d809004a40c03145091105000030075030042a160305468060300c00564550040703d04902600c24820781d402c1244500c0031071049005007510120980e05000f00c0301107a43d0b47c40366940c18070701540c01400d0409111b0000d10000981600c02d5002c000429030980d10300001b90707542001107494090080da003550f1101a00200713031400390051340c0a0003007101d00041c03104100c004a6916a030110a0455000d000111841556145500007454100300d0700c0c481010392034010029102c6e00300545102425403aa094415114040d002c0c2c43d80f010700c080c00600040c1c0c404c116a04181c902d140003500c1466898501140c5900c0341200d0f003004a907104e00c4100201221012121454001840021070740c1141d0b10075802c1890031000c0b2015150044c480041190071000c00803c0440b880d07011084417440c00403c88108074078540494858000b0352010025 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 908886699 1250 908885449 908885479
    0xf04170304060212090a170c0f091005040b0f0303070f1b05061204031101020316021902061b2406101701090f06050433050603070309060f05010311 65
    0xa68081c07809240090f8003c4102c041e1134005000c041c0003108001490700440568603081a4190404203c0e60502d54016140b009224100301c0400420150107448043e020700d080000380680b800540201481642c0340c00d9030144a0f551042c0307440710b8001c002d00381c95079484280741445145071440707811a045110f041900c0c00501c2241c03041001c6400c090705003880c0c80014442a064000001c0044040c0507c50281d0900d00b9002d201a5101d03040c1582c810365020b19503000a854212402c0040620303c0f6a00f44d0040140c441d078050300e10803801a02089020710101000342d0501401c400c1000d078103400c500e050503004844c01a02c600035103060304d00240b40c1e10444011078280c0740c00110f2105800100e001040700c9011948141350303101c8a101c000a00507110300000c3c054440350303c107050381d60640c840c00d90340142c4c403240c008245451100e810b981c0149402c0c08901d490200410803024190380701e0f00b01082c042e03035400100784101104400c00482d82c5074030301004522154001b00e401800c06201d0110 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 908887949 1250 908886699 908886703
    0x304031a0615090a0302130e16081213030f05030f03070512070e0d0b06040e0303090717071202091b070c03060c02190b0c04030506070503091c080f0a110f0417 70
    0xd0080c3c4084c002100e00e900395024400002604164528803d035544030040c482402840380216600925000700c181c186041e06403450800c03c1a403640d0035500402c4841d2414017200b8031901201ea104900304421450b5042c010b0541c050214002d220700d00000400040c268003500400d40c5005404511441b07440708003040340c119404000080c0c00007124840a4042a00155000c2d4007020003400800c9400c204c80f807080c10b540040d65141c403aa03201a800303102945011250b1381c501c800740d0b03000b0300b01c8501d4021074007030b4410307031020290040a0150100d21086401a84040e50078040700d042070303a80d5442c0c0741041460f400c0b84001d494003854540c41c030f03000c0c5101042d00b10704544d000210201324881c54640d0046d05001501c1c140c884a001c200010025074144403041c4140019201c01e80c480c0342c5900818244a1a401c01150500108041c118410740210760b0a410142c1c40c00a0340c3c550303aa0310010001011000006001c010000c65442445c0c040503004105840c8280e1041d001080c541100310303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 908889199 1250 908887949 908887957
    0x91424040609090614030d0c1110050306030d020a02060a23041e0503010c0e13021209030403420915020a090e04080306060c0c0a1d25110304031a0615 66
    0x9035060700700010601265100e80c8c1c80181c0c10b80100a50440c22120030006405025000742c2000494800301c200440352800f8000284500010b002a050007125030340050078a1250801c03180a012100b082c0030480c083c4418008020555039051a54880e1200c001d0307400c90200c0340c000061180842c002040324101809800910720498942491900c1007404101c41e214070303490301c030446a5007401104640f028507100c01d07000f801400d0183d40c0d80c600b10300700f0411010340c031000409a040c0c191000c945c0e0b440c200b1590400400a91100160901e40e00c41e80005052403009c064440784a8116203071452800ba0300501c111103a46d1155588541d8070381c481c02850104a5003c2c001013424030014142e03042040050542010034000d6440c66501c2e10002240d003415600112038562180041da801c2020b005662a0407400030320f4210315040c404d10041c82c40030500d08000d01000703444081c107004481d0820644019683c4074403c0d40c1d440d04002070030700e860002110190302c564201c0b04032560b03142e4800b00b16 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 908890449 1250 908889199 908889239
    0x11a040801151511030f0c0a08070b09160510030507110609010501080708060408040b0306010216081b010e0904062c01020915120c0714060f0f070914240406090906 72
    0x5c0c0d404d00d0f010079401c007115000402c0a08140c000c14040c04000b035540d070010070707d41d0b10598005441c1e0030a058504c0c034100340151424038580d100c94052100b55030741c90111850003040d180224450750380600464070f80b00d18404680c5144100e40c10701c4041f61040d04900c2c141d031002d40072101c206540d64103142d0f9075482660080c01c0064100428008503003c1c00003540d000304180100d41c5130100b001030310721100107154020309640d0801240044d4401c4a82590f0400c10403d10f850319420107401c001444820000e04001d028541c1c520007401d90102440310018107900390511490503d40003030001e4042c2d4810760300c01e807240d2a4030303c00c114500990001d9603082ea40c2074049510701e60342c0300d904074000e03445482c081e42c0c0c2c0120100b003801540c0c0108480c2e4486c40001080e0b080307500f0000310019a140380078000340e003840203181060180c2500002c60045150046a0010800503224226107004850300500600e9802c0010040341d55504a0b5614080f07901d4a50200f01c0c00d60b4810000d0b40302d140403c20 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 908891699 1250 908890449 908890453
    0xf0f03060e0c1b070611070504020711040507030b1c30050a051b03090315161b121710030b16140a091a070b011a040801151511 56
    0x101e00032480100203001c0c3c91039540742002c10910074800103403600025600140000c1c20031601240e04500a005020060005940a500346940769403034a0000740e1224910307010f181d83d0302c000b9134441c0c4203400001384064060116512a45810f00c0038500c44039003241070342c400400e0000c94111a052401014401d845000051080125007000f00c2d95a40420354000800501788043c4650036920384e00a80009400c1004595450740700702031505001d00702c1c0d00c42800014020812408452054451164040520b0858211807000c4002040988c21000160800145a9a114070650408400022070400c400d803092550b5504a2081542d030b11030100038014190348010408072410040803083c4444103050400032904207008120040d00038020180005800000c108050307140540d0f000744509041c000c2900c1c0c140551039110740c448040c031501c1c59544810f20151103584181058401070500c200081c00400784071108007117001800d0250032002c16080c011034504900402c1b810407010b00c0400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 908892949 1250 908891699 908891701
    0x50c07120206070b18191a010302130906020f0c0601030c08030c0c0906061b0102190203041a07020d0c090f0506010c1a13061409010b01051201180f0c0f0f03060e 71
    0x20720f2201341ca2025007403013a03101c01c041c0001403140342400403d8000c1c0c44007415a02002c00d6040c0f07211500c0c1c4e1000d402c04105107100042c009a01e0700010a04401e1741404042455009490980c0c000d118610412841e1800468001c510100c0800c5003412a170041c2544000c0076182c01c0055124801d851504c40b1590101b41844a641480c0c212241e2182009011600b4014055405511003046c0b0f2840c40d1103942c002612504510307510942081580345200960410341040410460142000310019405401140712030071035942400c6403541c9984801c00c0000950b8400401c0003a0101c0c000014074141050009500755114841d1400e01d507406ca0070b4a544840802d05083c074514010700050140480c1080d0350020521a01134200032102c0c2c21000c0106140c80c021490031507503501403860411504129507140f03a09410b030407a0548802104803c071b030f6200b40500303d00900102c0c456120381c1e0304101ca86280103410089041360403020791500c0607040c814200403070840359240a001410b0070700314 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 908894199 1250 908892949 908892953
    0x6010f0c060902130c03060e151e061e0423030d11010e16030b18030307082d0f06040507020a150603060e07170106240c02040c050c0712020607 63
    0x381000c00854000344c90880381140c0051518260340c02031000c0400709445d11010042081103400480e03101d104641e0400601740640005005111200d00451000f4130041840409550340c0d4122139001c40140841070843c803081c0c81c1c51a682d0098401c050406120100082c811b408050714111215401001f500d01c0d000390590642c0e0090020305650030540da0394203040d1650a040019100482181d08540740052451804460365030009000814007510300d4003080c903580c800000d894106189003443c0c06a60303210310b032801c460b0038000c681006202280301c0740001100c10424180c003600000c40d9550056460900748030540e50180d5820005034801c0e503034903011900030407104842d414050004a1030a6917616807505032004d1840303200b855041180100810903a0300c07550381d00002d0000007407110619000000d8410301814001c2c14018a202940b810309034800d000701c602c2030760700400411201c0b039a984c004200e070300a4081c4010b684107011001ca0404411004611503075401803005280031160307 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 908895449 1250 908894199 908894201
    0x71202040903020111040f05090603121b0c031506040f0e0c1e041d0d030e0c010e1906020c0a050d0b0103080c0f0d0819091104020309190c030b06010f0c06 68
    0x900301c01d40465503039290040c01140514000c1c0010106404101036175400d1400304507482c4006065070344a68403000e100c08000083c4001c0d11158818683d41d0749082082140081c00c000c1c41d2071406074540103105407920036400c42042540144003e4800300700c3c1002050705101200c10070390940e4807e9015550025a9151100c0341140c0800c00c03440c078002c0e06019002186c2aa141000f0120b01000ca000e107200c5480400c000800202585280500400303010705501394407a4103a0319281d0400c8007800c043c8003603880b140039000044c01c1711100806001d42c4e80360025142c0c00004c0300c2c1803064110250010b41840c1101c1c0030041140c0240e440c881c681d2969a0f444c0960348001e00e4102c0600600d007016040c45800e12410700380c42d00b180c4501100d45465400700c5030142d18060104e04842c41c058002000c50b003001c0c01d5094036501038400580d41e45615254078070b4444076101810b40c1451a160047c1001072031100241100d00c501e001010f10744452006480f918a2203000400081d043d84a400100783c40d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 908896699 1250 908895449 908895461
    0x10080d141b0118050c0108040b01051507020d03031b02010e03040e040c032405370605030714090901060506030a02070c03020429040b01050703030905070b2a07120204 73
    0x1012074408104a6080d221820346101400303000c0520801840ca02c03e20006211018100409203000c084601d00f5513150324001d001806070038091421107050714410000c49044401094008140b1036448585d03280043c0900b5054184050b50700c401134001c0c080a005008030004100d84030059400c1c9410b060403201c0c3c10308010000c0e1000b80c1401c100002040d510420b0513401d00046845040c5070000444100a60748050200e1441c91100e11582031100312001c2080ba8106010020303000b0225a0708106010b80030355048140d16000748c00300002c00c145440b514075690f04007691510710075030311110720500322122440b5054218200300b0008252420507401402c1c114840d034954103810b51290046012a09488007001ca118070844000c4201003045a240d001060b0850b8180301c1074a1030b03000242140500c050080505407150b4080d000c2003003d0024901400003072a245031a01442e2025250a22515007000c1c58000300d0507800010810120b00b48058945010042c40030900390b81c00d2000030a4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 908897949 1250 908896699 908896717
    0xd0509100b0603100504152612040e010e060d0b0a0b010201180f0206030406020706050f041b1a0f2106090a0b091303020c030601092304020d1101141210080d14 70
    0x1c01c047d0049400c2c500c4150b004a004040d0f01110b24145030015070b20314144045100b0b5090241c01e110402c00300c1ca0710380140307041d10004a14010b4545800c004100784000a00780100001169800c1000004043d0f00c6148064006d9009101c0034910120003d03544010711006061004008005409402c161004681040c8074a40040c41d010254030b40710200c0314141c07205118080703200244400e01080c80034000000f1000c4610b0301d1518503000d8081180400c04100140081022640b40b4016140c402911502d21030a410100310a105071a4604582c0b01110310b24440e614020104802c1b00d01445003030f4070748001404a10f5a074540070395880f1a211541c50407002c40c4201d0b40100030503103062000b0741c002e1459180215441407501484030600c0d0000d010b405030380705541c0c02c120141c0e40d01d001d506d40546c0c20003400b6410b40a0f20300101e949410441c0c9047d12002c001407401d001100b1850b80901c07076500c0c403200d03044058650a0013a1100f5682c2d03038800015603c3d88070980b000320480000c0070810 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 908899199 1250 908897949 908897981
    0x18050a120605042103060f050303030f06040b06040803040f05210307080d06051e13020a080112030309081b010f02070f030e04150e0114060328020d0509100b0603100504 74
    0x2c4d05241c014400c51301094a01d0000a85904040280104041c0c05602401003203000d942141307080246424500c00c01020944180c2d00d034880140952075080444018000800c162135841c4e8071038003d14903482031849180d00a0300c00354500c010100c00054030710500342c4008051807030b1112a032120007003034200010b01c005140d5560380002d03441d5601c41f00070920850319811203000310303644020070000d60303031fa0381c5050801130040181d0420103074800340807419220401008040c0e411242002c800801c1d51242c000c010b6000082c5185030012511000104102100d00a002d03408580341d420b03090740160400209440e05d490240c40009000e1009044101d0024000042c2d08804070000d1500a9040c0d21005200c002e0a0050020090340c0803582e51141d000e0301d102d03155080200c0c45900300490b035402d104130050402800031501c043c6804840c1404042c0d102482207040c40290035858103d600300e0b0045851030040c020046e800d10b94140da00c1400c51030200159949800180000390102c100503003800e07 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 908900449 1250 908899199 908899223
    0x3070804080d1b0815010903140a06050108100f0c120513050d0c0201090f0e010b0304050f060106110d02010c140d02220e0702030c0307120e0a0618050a12060504 71
    0x1c00440c8180a0f60000c0081403002030b50410b080605070b900301411080411540641d00e1280d0790700101140300300c0e90320924a0102d003500004e140d082c103c2c07086005101d107040070300005040100103040d4075212984107040200100c1280c3e0030302240c40c40c030448000b00c0e08484850075102411380c003840e407084811114284130f20351643c2c0c1c603040581c3c903520b0b1404030780a0700c20182903517800429100500510b4481c541028104800c40c4044041407040c54461100000007504104085c0030000309a80e80070115104c95854010240880f020070b04007a49502c83c0081070f280440c4140070305142a041606c030034070b2600c000c0c070a0310344a501800440d241d0700d4080111081500070103581104405a50f4507080c0d0361030400f01001d0400402928034411580b0601c95140300340d4020046170b00c1d15500c08010b0f11801440d030419149606003519442c4d1090b101000080d02c070380c0004400400344030b8003080c240d680f40c0312010440c03820a1409003e40c2c0c0d0700188040000902154045a005402000b11184c1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 908901699 1250 908900449 908900467
    0x1815010609140d240b1903060908130e040b0c0333031204090e07060e010315120b0403031b091521020901410f04080c090a0b060307080408 61
    0x14007a01d41411034000900800e50440304c91161044c5c01804885c03518500303002c4148041050780c0f5001c094249075998080108225816084a8001d01405e422440307843c0e850081c0b10081d81c0446041d11483c80c6100001c0a0510f107108482c03081002400321040b2200c2c18051a582d5416003e40c0d40e000421821002d070199410810094628a1100690303581c074100812076041c0d40f0401540586a80074000138446103030820090802c100080c03800040031070100c0064860501e01e43e0103400f800752003010040900000c0750004d442103010342c400740a628401e061000d00201d20718440c10014441305400e21500144920456140540b4686002e0b4000c2c010141000c00c41c440f07461101d011f81c00141c1401070352300030381091460624449200462460f081001c429081404180c0090803206171b090140d10f0f05402c1618807209500c1c504540f22a01ea026040d03a814030400200c0c460401c1100091918030035004104160602800481c21030300c0790321301554070f8400030f4000c176180c031420301447d10 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 908902949 1250 908901699 908901713
    0x6120d112103040c0e04050307060f06030b13020102070614070f050c060318060f010f0b030915070224130308070509061c3603030b0303031815010609140d 68
    0x1a0780a40006656601d08162411149010b9581d1019a1000071902080081003020055911a0750400404180120300401c5400140348a070401000000000c0910105a800c00d0764903a2407407003a0211900c0a4507900123852002013000401d00040080291100013841c90300803249141c8114112090300340c91000050386900100e40b0715191250100155070700c0c0c00f082200540000000d401102994103003104d00e01d402c80d4030300403d900450008041800c60108101c52149900d06003400000e904084000a4841e909080f00084c4544803111031003003c0c410040c4540511240e41d94521250915030303058883d4900104040d044c050b0910020a180c0c480308002e00da1044415810482c410030709950008075003110b2449a01089100c080040ca4141d4844940a04952a013404882c1c0030340d103021000b80902c01403483c2c00d8003000c01802145004540344070751810b490b0b000d95000b03580c01c1c000d400e41000c091140000060385e070001040a4001200b00e1310fa140b01c0546440150f0350f498550f90 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 908904199 1250 908902949 908902993
    0x304030812130b06040e031204050322080601050d0809130b03010e0c1e370801020c070905060604090905010e0d022b05070b15090112020603040605071b11010806120d11 74
    0x134030b0b41d4100003a07015000740f01c40e083308a0f048100704505001810040b00c070f40c0c1c840c014011359000300412442c1c0710507c030f41e0038169091854018500d174078201050300ca05e800344c0400410030780290700340408513800c8540400c4000c200c010207054144140300c8110321b07100079009c1350f040903000203a00c00460385a5005c02c00740c440c0c000c80403c1c800741c4100b1a02105c0c400c0807482d4011442c6900c18442042e0140c3d0204aa01c1206c01100f0003050f507841c0c040000d0110700c10795111020641c6040d0850003080b10641004041d01c00ca07030165200da50701910240d80341c5401a003036104440c1812503990641d90800e0030b99440d41c03100d1401904211041d5a0b40f01503020945041c3d02e0340c5602400c1082d54600641058058144090742405075103841d13004c03070100d0101401c0107210907120000a140d807449031042c2806040588603103051082c250030300c400415200d0b0324a500090b4114001a0340b030505090a000c0400d405000301301c40034500500300e07812828102c18140074007330800c000c1d501181c1c0010b08 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 908905449 1250 908904199 908904203
    0x90207021e12030703180e040201120f0219030b09010506030f180a08070b1006050a020307060e031e04081011030a0b030c06040f06110d0503070513080304030812130b06040e031204 79
    0x642103221030207440e010b06d800591110905943d0641080300503640b21408400c6040039100106030b140c0501c681c403010b8090204445031524555400201c465450740000c015900c0640b00f00d00c0c503980b56030030b00500e403004840c0200b07981d0300c0354042207154074000c0b4010343c5103100200b9a01902d2140d070ba01ea001d0344c0010b0054440e07094900134001e800c050000b03804010085401c0540ca0100b03002d6010b5217a00484001900085c2c0d0f40700c0c4600007040c00c2c0115401403c800c4950305980a0075034000000e07070807a000c0c400311445801c07200350980b42c0c80c3c840e030300e141d40da8901041c0c155510001c8140c050041103004a4060042c01c189120301c0c0c0b2840003400103496803419040106007010310080c41c040038000d0b4000c0b141c1c000c001442d223041d04071048a400071290b18106941c0c210700c003a9545411016480304a151200040010038400840c0150000d0001c02c2c0e40e0540700d0f240e284000e1000c4110480243c981801d20011544510b0540d02280d0101010004c0d00e0a1030040c00d050082e0040803a81 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 908906699 1250 908905449 908905457
    0xf071707061407081807180213060c03092106050f180102160f1a01080d0e120d0e0d0f050d030b011b030e13020d060f090207021e12030703 61
    0x4a1010840280074a50807500700b0001d10010f840c25000c02001d5042c0a49900307000c2c3c05c1001903c12050042c02580060061882c101515290448080000350f00400190b602c44c1c1c0d69200100e1424801c8000884968142e643c0365451428903c0d100308110300e910b542d0100450a0600c2000030704a801a03901c541281000302c00b49247c000100344404000d0181c0ea800303a40b040200d034030845555881003035802e801120001c01a0010b16100c00116095480f213168900380c6400001c0112001401ca800e00315283d84a699503074090080c0040f554468600a10301d40102d052124074520500f82075501c1c00c002002d044030b408454a400425100c022802c0c0d984e42c101000621001d40c0502801800480c00c0c80e124080400d8158642c103444640070004081104048500703105658054281c2c002103078094045543d0390304a000368000f01010700c100d0b250240818000942d41c0b000e442a00e0b0401d401030304000c4c1c445800410303080d0342c110b194000c5030b01821720003040d40d441b402000500882803007516 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 908907949 1250 908906699 908906707
    0xa0504152d080f070207051e0f0d230316060b03010c1b0f02040b090106030c0e0105031920030c0301090605090408041203090509090d03060e01080d050f0717 69
    0x1030942818142046600c180e69621000c1c548202e42c00100b065004508004108039a100c4140c100e0402d0400e6100c5640072a80a2042071244084826008110300454021466414000074004840082c000280c07030f09400007104404031030702103058150320810500b6285405c0701d020000d100100032100640c1c5803503648a03240310600342485448101a0617044c00044100103186411103507a1404005060080303401485085455075001008003950003401d0407515a184c0070001c0050944d0181e8500040581ca2540c010354021011640500d62400c2e8103d4040c810080c010041d0101280210010b40b02e20051082d80700400007a5029002ca001d00e41d130b89514218132078041e5941034015501c645504014040051520700c03c482c11030b117441d5195420500c0a09094452403010341c0300740d42011916080120740c4001003840c03068804151070820529440d801c00100c0e1034001d00039a850350b442540c0c030500d500e00907400f40010b02803c0741040d1030041613595000b001c020b84040c1040c1210085 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 908909199 1250 908907949 908907977
    0x2c090604240905030a05120c07020307180f0f0c0201180209011703090a080c03070807051e0616080306030d02031908040c1e03060c0e01020607030f020706060b120618010b0a050415 79
    0x800541c200302d2000280d4207004c1140c0000341c41d80034500c074565814001403710186c0421130340103d6240303c1ea00104001d01e4504c2942400079205c031919000040d440c102c00d0039045051300ba02d020f112a0040d0445c0e030540e003001e1680340c1c4034070899000b420905c000c3c0b202403050f43e41c00c840a0064481030014012062401040c14607040e0f850300300717020036000024144001d89640a0780080310200125882c1c043d4002404a0201d20460300d88506220203034542005002c004801107010711000e4007200c143c14100c5008a840b4040c45000b00c240c0507102000000f018880c030052a003141c001c000e0f1489031503030340c2d45240c3c1c1407990355003c807400c070044402042840a284150751b400e025508219030718166140000f521004000c10f0b603000d05940e4840b084191980c1d505945032030346d102400f0820580c44444801694000780544030311542071400089260800c070080303501f40c1102401002850f42412030342c2c4a40d402001c4040c080200c140000035070900071319280c90b41000030743c44030010b0320040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 908910449 1250 908909199 908909227
    0x9050a020301051821041d061c11040b01020319030501031a0c0306011d0301021c0e0c0a030308090109240510060c030e0a2c090604240905030a05 64
    0x146100c4d0305040700300302d11480c1e050201d41c8560304421515541c0d81080d40c581c11384454000c1d030f04440170320a070b071080c03d10300490041001809240111001d103155442d8091785000080e41c000014480e100c0b40aa0740c19608054000101e4004140103070303410401410310307038210703000c3c0f0b40303148000640c94030010418000600300084001070b41d0b000e450032a10780880083c8191002414403810404c40f0000c00c4000721511100e0011203400600139981c031499070000c1c0108072240c0041d012903a282440c41c401503607001032906005a0090039004032146162001d0790659001081240d0329501c510415002440703c100400d040d0000103129450400303042c82d12001ca440060001c0320607541d54000384001340e005415110860344c107191034403000e5002c0c0040b4260220b640e015103640c1d490b02d10f248080f44d142d550f907490380907000c40084030b4982d9020050380e907c14003501d000d001180e908403140b288500507001509030352220710002c1403400d03040d500c461950340886681000100081601c078098821 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 908911699 1250 908910449 908910451
    0x403061103220f0308060d050d021501120507050d030309020a120b0604060e1803040807080601060f05070b040308150315060a05010305060f0402070309150302070606050d0308240409050a02030105 86
    0x10074001d092003151a5500385503c5001d810141c2030141072030004036159158605c02444642c130005546440e000700101946d181c000d82e81201610b44a10004540c480c60384201030102c582160040c01e4140ca08000d10030391100a41c0e0a804040d152407120b005604d44105141c024041c020541a04103000d003000058104060f020034865030401c4420000e01030520041e5401051100ca00c480c0f0084441540d03246110315440700701d46004990001500c12408201d02d070480349161100101401d0302c0e5012200d900c00c003280207181200d0740011034082442811401d40c0212503003100701c00c6e6028903000038645011440700b841c108048108004990901c01c4451000701020300301400603040c40c03000076083c603242c03100c220b0065078003040b4041403500c6a10ba550042c0b8101407110540000408010b01a501c03d82c015105103041240001e41400c03d400d5410940da050381e110010341d20769940c2022440d8810010740c03051459502c0c02161642c1b18407070590250310420083c1404200c91052500b03440c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 908912949 1250 908911699 908911741
    0xa1203050a020c07061b050a0b040203060f0907180e0609060103020a050d02031c1e09050108010e3306040f030c05120d0809071d04060f060506090609060403061103 72
    0xc0180201c04a90b00c3c000355141c10388005d41070200080780000025001131450314405051440b0b0b0100300c80c18801020001400307a070098040e00c50329541c2d40780c1f8102407101a50025000d500040d400c00c0500c07054494107e1004c6015002709802124680b524a8080e05035006222501704000400c114900a07030520300902c07090380c1540c1d09180036000a5200d9034090040d00e0503584030f00c0700707080c0e00f403040542c006d1100340049000601d400c117280042406c10b550003918045503204e0004540e658070808a81c0c07156080030700c6d410302c4c0d41c0e80c880b001100c006416603003a000e01031140b00e60b581d035840501500c003a2030100d041c00040d0b0b1640c03c142180402540c0540d02a42c580c0c1030004200c1004190070300a00c4450908640703a84800c5003c03441c12045911007030460a50300620b0403140c9296040a00490003120244405031055a08004644d607a2040c00d500583c1048030715003905000300030b0103241000808690505a607512030b80b084e2201e200540c2c54031400041000601c001b500e020720b119038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 908914199 1250 908912949 908912951
    0x140406020c130c0f0c06060509070206070e1e0105071410150902030c04050d240c030c03060f060c03051e120901021c0e0a020312090307060816031107050a1203050a 72
    0x10841600a481c50007691005010003140b545c1200c18440307240c00900c01448050100c0c405450100310082d1034507420380ea5800010506151540989841d420782841c1680449250300c00f00043e80c01540c4a80c0b20383c0044880641c50b00c5904440c900a0140d8401c122111002181c01e06a401e000480c801d441c0c1c02c0480c0f01d910620a0240701602c0006030b0b4251102944c0410701b0880d5820408110209000e0b0000c007180021007a58882089420021451030582c9050103450303110380055082d10300074007500702048140031082001520039010041424000e0401c1494408000e212850400d4200d03204041c9400c000355420f000304030146034650021400c4021824694000700300c00a54580c20352001100f81c03035008a820010041c014003900a80c010300f02c1d0f401500d03015215610750401450a80320303000f40381001030032500500b8000c0c445e9003031000401d0038142d0044294010300d20141c00c864805014400310300041c0c0c041043c19a400d00408400d010148174240003003e4440c0100058030b11 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 908915449 1250 908914199 908914211
    0x250c061b1203091515060306120f0303020d09170901020d08010e0a0911030312160318080a09030215040918080a230409050f0c0703170601140406020c13 67
    0x301e5204412054454201d2802040208142c140081c841c1a8201800e41c8240b5105203a0074040000800300304030303201520148080750782d4019840107038041540142c01c0d45841c18110b80041d00c2a030083c0908848070303d0000b40341410341c883c0d003029001406900c45012002680c049a0368042102c003440c0c00081c0380141c0158140171f40c141c14210054551080c2544640300701c0c0401c41d030740c1510b212801010f400c0b66102e80760210b00e0540c005041e54032a19002084400360000c3c1c1c400d001d2580e0b81141c071680d40d0b18805040c3d4480c1e0084e4010b00c000c03000c1000440c404001a60b42d501402c1b03056001d01201c2d40c456042c0310801080310800b2030034056103084800d0210000c3c40780400d54804884508080864484004d02405404021141e590b00f224002074003141040150b48868060100c44803040704540e1800300d500068419a01d001d004142d0440381c901038443c0c8540f01c0c81d40090103140c9003c008100c2c200c6a44150899001240907801800c1c0321052800d0410042a8186036203400b0300813 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 908916699 1250 908915449 908915453
    0x11406040e120d060b030702060412021204050d0c080d0c140604110d0c08010e03130503070e1308070f030c051501150e01090512010504030207060804080d02250c061b 73
    0x1461580b409500c11412003c52140006000d69101a004000a4180035580c3c505600001c1d2603001c1110225100c03000c0465110f0101d100040c4d002c2c1c10148050050325103410301c020000d000040300001c840301c0000f080d000c680070300c00b8003100c680c90000340c540da44408014900b00c4110748200d600c00c4d134158027440810000c9003c14a10120114007a511181d41c000f01d8140180c0c9950b41d6008403040f90f0800100280382100080106081031035003403129041a143e200b055142d102621a1010410b43c02d404034944440b14110310132800e10490f4840e14100d42c2d80d40311100c1d43c488003070940108094068020520405010440ca0300c004118031303030782c10360500e1094040c4a030003440070030810540700300462890340a44008009804014000015000d2521640d40a00401c90701140107005480001402601070314200e4061a449468123081410b40e4503001c4c001d400c070881d080c5011200e410b60411015006981a030042d0140d070120306001c0c1031a00180680c4044103c3c000300015245203100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 908917949 1250 908916699 908916703
    0x609080a2606060f03060f040e210301080606010f09150909050c07020d0b1e0c0304111005180d080c060a0e0c011205100803120105010905010e090a0b0a09020a02011406040e 76
    0x4d541c1254040705481e601c6842c08115041c90f04104181c002e894145001007048001078402c50003103450b000764150981d1120441d010340402e102d0030103598041030200d601907000d0354000f240504075141c00c2c40c00d599180b4075201728000b6403176481c02282c1551014045420036001e00c0e83d22070800f032081e5103000c010ba80401c0f418014039501a01d40c880c10404644d101d14900781401d102000301d02000040e09081406401039841502c0c12900d151b000f160440c094201700700524548200b03a192641000008000c4942540d0346080c4c469220340501000300c00075044001415000001c000281100d1030305244400c215000684685426880700c5865400c907170b401034148c40d41d1681c4c07007000318060700c60040015445c5826040510580008030300601c05003201044903040300d50927070310f444506565200648070002d04018440d0005016000604140d03099004560008809410704032400d5030755800c082242c10070522400141d442d100c0c42558500340a1311690005400c5404201003410041865 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 908919199 1250 908917949 908917957
    0x90302100f080402151b34120501060506030c09013e0a0602030f311101090b0d0213140a1a0705060f010e07030e0c0d0609080a260606 59
    0x240f089009030300b40c9111805100982e501c40d10013062101d0a03600180d041921164407605900c09030887e80c0b6010307682c5201c1240b0030754002800c6058500103041139403035040005c003200c090300c081d92621000242615414021445816202c4003036840c0c0050000051090340b152040e000f09150032103500d041248075024404016001e08801a80a140300d80c0c05820168003184c0507101a1000c030400151000d50010140f05110280e9504032902604a070b02800000701050310b1520841c0180700c1340041c05590304005851414140f1900281e0b40d2440d0200381d034072440c60b0180f400c0d004259060140d801005040c09446039010f01e00011100e10041102c02c94640304040c5a504454441002c15400c081191100e58000041e03d2061a00d0001020104820721501c0d04481301c410004103000d100380300e80041503003241d0241800440030001c00290910b1284241e52850351000d00c02c0003e0b00c0c2e00001d12800c8459210441c15899130b006481e00c01d46540c680459400b0504100000356035990112 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 908920449 1250 908919199 908919203
    0x3060a05091c120c0e030f030415050c1504060c120e0d0c08041802030f01080a020f24030a0c1e020a0206070f02030f150603010605010e0d021f090302100f0804 70
    0x2039014200d82c110200c8840703410400c500d042516180c910301215a100450f100c40300000c2c3c0845504600c660a40c03981c3c0d1095100b40311424203614000c500d000e01c11801409180300400c02c655480140e41505d040807001075508661156542c0c1040300641c1d000800d48660b0030b0044010042d002016103000d440780502c2d440081000300d9030504900304900441600c001d401100c9400030880c0d150804200203500694103403140c0d03072000f0000101001c1c002074000d003072035020705a07801d2402d0140a1000c0b01c820f480b005d04400c03101c0c22030512000750b008080e5110786842c2801041280d8015806000c00034071041d000c0b9a003001401041e0303a2070700050040000d0f54140c030440d903250f0960030300c40103036141108000c4d41341c0648880d40c03001d80300006510462001e211051511520b0f408209804c0b11103d1003132601042c18816031410b20b01d41400e9401d1950300180102400714a82900e00781101c01c04501030b070204103a1041802036040c1410380c01d410f6560b50038159400c400764800500808002400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 908921699 1250 908920449 908920483
    0x10c0804080d140a0b0103110f0d0902040e0a2102160b030703020f0a11072705090114160f02030a1e091509060809030f0306010f092303060a0509 64
    0xd0201080b071640901c001203200300204069041036242c0401801c1760804007400641088a0b04005255800440342400d03080c0c106075140210644e948030140404c02c10a0b6445650340c6e50300e042068041c04852240d43c4122884006800080c040880203180c2583c90301c110760010700740081002c4044e21a8068071818403135a5225500c15400b00d01910500490511800d030215400002503004400880702580d654142d4003410340320000c00e00c10103400402e007820301000354200c0051160640c45580c00c01d0a001c00031a04840341b500c00e07d000e0009441c0066840c00144090103075590024110309000d00c00c2c405140b5120700048000d09640034910710070145d0070b0300c080e142c201501640700f4100824000110000d0396003d858060641000e0340310b0000454080400540740581c044111f600c1d084540d24800c0c15074441c40011075081003200f2034803041c05070109002c101c8000c4041e48003181c0078440c0c079121054109005241c1409005480120001e042a0500046840c0801e12140b03603112804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 908922949 1250 908921699 908921707
    0x7090207020f01050c010902150c0118080d1a0d05060103030212030c04051203130602031e040830030112140a05060f1e0a15230915030607021608010c080408 69
    0x141981c010319100000035030001800f0f00d0f1100d984507a00c082c00c15109606d00130030038495058cc0780d0400341102840203069480421206500e0041c1c5d1740402654951020756070101038036140400d089041c60344064445600440c010030805604019000d41c01c10350240c1c1c5801c0d400d0001c40306209002d43d008040c4210741d101041c00c01047d0810584105200c0105415a0303995900806500c80d40010304004078044d0560740c0d418810580004c5904a0360078070018540451074642d40140710000340e41d55091840449071001d8a014030001541c042d003210341c0202400182480c1445807908800901c8180350024044000406c102080082c2d100882e00721141141d030b582c80411a5130044001c560b0100b00c1580140071203607405900c41403894803030442c40c11081e40c80d02c0800c02d1012000310704481d0412020010410f605005103c01d81001041c0706030090400503d00080c10000220b64a0005030b000704420252a6100d0040c44028011040200459940080014410313070000b400540240d400103 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 908924199 1250 908922949 908922967
    0x2206050301150c05152202090c030a020c120c010515060d050a2403020901060309150b0301060e160810060507020d080904050906040c08030a081801240807090207020f0105 75
    0x7003c240d102d51090a444032001781d003800d03100f608020f03120810342c04640030507200c464111360f011413603154008100561580d503441c05000303140d0009241201503030702485403040c50707901003041070b1640f1003c1c2010340d201d00300d0070621400c4510040c042d23441c80030a030400601d181c032048129450358844070740c04039259440888103005070103c10448510010703480540b1442c1c1d412408042d00342d070720841c0d980c025a641c61104805031103a80e4000b03411038a45071280a8184110340c0021802800a0000f151885d901c1c810320b42d1001044800003649000c1c40c90300001070307074002c08540c1e2209401540088550502e44001d29502400720002d01841e145584101408280000d44034081c01c02001030280345064008240c442d03006490440340503007034040101300000044190b0301240d045956003c900d036a1000e03101000c00c011800b40740c244d583c4800c0410400c09a00c070a9482c0c107100824050340384e107032480251500c1f01c0395101c0400e1904c1409044c0c010381e21101011001c0009103000c0d034980210ba = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 908925449 1250 908924199 908924207
    0x1e040f060c020a0e010b0901020106080c0a051e060403060b0f0a03170d15060e120c031c0c06050f0117010b0d02041508070e040c0504090f170f0f220605030115 70
    0xc0c0c0102042118001c000540c06c00e0900050200d51002c0e4028005160b503004407a98400a043c0300541c01070b030180013031015080c4000b140c050b860703e292244e0b14240441010a080342d0007a0800d0381d03901d844841040c2ca505141401403031500090784c00c1c094892a54682d510651064041d08980c0040040d0603c01c0c000d182c0c1052041d40003001e403148009035039120103441d0710203c4050350300950b841080c82c02810008511101d0b81c100c00390240504002c24007a2190009100000c1000e00c560041094081005440350764401c4103601a01049541408001240b064002c4100341c916814004051010380b65151168001981610f01150400a0030750110b683c48241c1c1258610348140030b00018000081d0710400d0240d0f0041c50650525500d4105000941d055160f000d443d0780384101c200000034105005048101900041c050700f06000e104002c1410381c0f064241d4000312201044010300c503a41140c0040403102440082169941f1303000d809000c40c041442800504200002090f003c2401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 908926699 1250 908925449 908925469
    0x7020f150a0923071a04141201020c0606120d140f1207030b0f1c02190504090c031217341d010906051c0b060304081e040f060c02 57
    0x807120001440900440f0f10701c03140444125614041d100c1d000c40041c1c1c540c80c003e5215400c800d0031030500d140c2401c0c14210380003084d4205c241d80d00042042460b001c00c040a1015060031165440540035170b05200c0104404260603450207500d54120014100d806500b202807001c114640303c6619460321461200480d090045010842c0044144810000001d40c5641301074905d40d0b0841e00349400e030b62110309125900d500761348040e81c0b00382818070400252903c20740341000700c0040c001804010f6124008038003695480300d003c44d00303000014801d000b0008112080342614125107030a8000c940c0480807121b1401014103010b40040904500d20104844460000150b043e4008464200031100d0001016403080038000c0e0180b0a84010f0442c8540c802c0614504a46a43d541e45003001c640c25410b4000c6050614800400780d03513600310704800d4039140c01551089000702d80081c1c417401030b010ba0907a40c281ca80e1103510640e00030070007072098000e0450b603501030b10300e40c0ca0031551403440343c800716002e405 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 908927949 1250 908926699 908926703
    0x1c02090f46060306060503010608191805060a1404140a1704060e0103051014031c030506180601050304030f051612020d0e06041403031b060f07020f150a09 68
    0x240841880c180c1101030340c0c030418803004680324040850b91410300314102d0b50305000b0800000c400b0801006a984500200c0e50410190300711290205a44403140c0200d9440014802c0d0f03c04000c05440c09009041c001c06500100200c41800154080340e4140044d5600800040908055401c60941403404225191039664810640042c04160032600c0b41260044d10a4600061a001114071103501c41d0040c0c5018408610094050904020040340840b1410f5000764061003031210030402000c01c00c4074680d07491002d0300d000444c2d0908100384002007410200c080f441c10304080502419903441000c40e80d0080d054508400b0240d40300c00304485034410690916001c16a1004000a01030741568007004d6140f10b808036801c211500205490b942d02d0208103940c02a03052008000034420421f441d080c02100034240d0303140582d18624030714a0b014010b0f20a5888d40000d08109228218810198000c42a40020021111141a500e03602c60300080d01e40d09001e022804034894204607001807004030b07 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 908929199 1250 908927949 908928019
    0x10912092c0423011509150506030a0e010f0b091e0103080310080f0d2a0f02120a0609021003052511070b0c2119021207081c02090f 58
    0x4030007110498003911001c80c0296031085c14107400201c100c1c451040b8903070b100800791652400b62130102084942d400040006a019444a403131044140082c8980c0400040e100ea0020780041d0790001d00040840c01041d080c04c80554018076031050b010020824112a0f006801580d02d0b030715202d4010140c07210f41c0c0089118403403100340c03034100c40000c04c02008a11a60b07840c4a1440c691149804010f42070101c101171003640401c421000c105c0b58400a0b4406d070000c1c1601140b12848003041307282410000301621410741c1da01c006800c41c41c041050030584c80701483c0074803d0307050445400030b50f15001c074000d5031181500e00212020074013507450f0b000e807103400da01030701d021954450500d4000e0388038020740f241e0380c01018802c1000826160b00c1c20107400c0d24403401ea081c80c814a044031000c050307001240c0158030a1680001441000100511803148210310715a11854004a0024131511281e110003070b403401880407184a1325406820301c0d85640032648410b4030390981c21340401c10301c104c0c2c030f22110030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 908930449 1250 908929199 908929253
    0xb0603040f051204050d020f030f1c0e0d02090a0b0a05040c030207050c1e01050c15040c060e1008060f0a05090403090e0c090d060203090f010912092c04 67
    0x2101c4100351040c5160b00610960740c4000429040050504c240c1c00385a500c864600201000350030703c4041c0200b00700014040781c0c0fa802c2649200c5217000b091241000c030705158040031a68059115000002081080e100c1046107601c56001a0000000070040c3c1020b960341c00074969283d441c40002001001c0241081040600400b4020042d50081c4400c1d41c0314800c0e510710160505002c1500340240b1400c141c40400142001c0c01150f007680a06c0708120030b44690703041782000c0c844000c040e030f02403441000482805884e220001e13005c0890b000803140b00c0d0302010403140c4901d802c0406103510420841d0910340c66440100000c0116800c1e800040d00980104100010503400c1f221240030b4036211300803680d040e03030340036071401ca41e1240d40074040e0804580f442d010300083c03131034001c2d41d0041045019610030340d040651a50071102583e6069035600301d481c07000140301d40c1220303c0801810250800b42c584184201d0040079445015070a036500c3d104080014007400209030780700005400544a00d661 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 908931699 1250 908930449 908930453
    0x507031b0803060f1c1e0b070207060305072c0103091b0306150315021602060703030f0e030c1b0f06040e060907030902030a0f020a0f031a07050c120a030b060304 71
    0x7190402c03110340c0d028001484050603140f9107140310002c51712102041d00203010403942d5010f040c54525124110300d2000344088800604011000c84c0f154450303a00400720280f80c5500203007501c002400c1d41c0c05010b403c01600311b050551621074001c20965104202c000380800004070001c00a0050142c05442070b0030b4030102c4144000300c2030044a009038414041220941440318080b4061311000b400d000c0344c034400b201204641d801801784183c0c00343c0c47e102c20b20030a0300410840e0303208081c1200003e03910108851070031440d124003041d20880000039824014400c0c0400d5076044407045002c00602c1e000151181d0307030344814404c105444c2c06002d060301e8a6441805007040b03201079a00610030b518401c000344210b07110344900c2501680082c000c10716002907444050061014005c240d03003040592a0200740c07a508800094019403042400d1012828450f60780d6a403280050080b8017088020003c1c8603030800c00140322032048581c4082141d50f100d0300c04040d4000d02060442c590807001c04020801 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 908932949 1250 908931699 908931713
    0x1020313091a150a2a08091809031b010e0708100c03090f0b0601110316020315070221091e10030924090c03050c030709060b0a0507031b 60
    0xe05030221030110458491800b003000b002c5090300b000e400c40c00506100140f0030610900b001c1c008150340c0c40070041307601e40c030f800030101c0c40080038030035100a035000800004604040c00498412180f0345203085903402d00d40c90780e907280d101d40c900354141c0003104048028541820742c0950004820f01e802c580c0da182da00c2ca0381a0b140c00c0901060709126262440c41074109002c0c3c0a1f10030007590003098460108007a5035400c4030500c0140089041088105001c00c00355070030401400520030906510305000719500c1014600b1a548a011546400312818001c0d4250000b411000341001c5403041280142400c11280b82801082640b40d03000c60500204401a07140e1858401d0030030b000d0359a68404041c1000a400344d40003c54000c01c4d109000d00d0403000303c6e200b0b0603004071100d01c03500080342c0307001561039007440e40000b900140c446410074610b0302107619042003100d008015030441480b141c3c0c609140007200703000320090f0350203101c030024070102018459083c03c0382511072254140d40515290422134 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 908934199 1250 908932949 908932961
    0x105010f0317040501121e0507052203020306130f05030d0c11031c0b01090504020708040503010c0f0c02090606041707180204030c030609240516051908060102031309 73
    0x107110700d2100480d0701441d03a02c0104071826140d040c0c5408113902c3c12541018024076400c0096400e00050311039844100d6071074080d80e400b524183c0d94454690705224100b40134200d001c198169490f20b080c10403c0180c40c08920183d1010805001d400002013a042041c62062107800003400781c0400590501110b0f0a98030059103010540e40352602c01d400b00c0c510b107980c1e00c2188035040e485413008810f900c0003038481c4c100c040c41c0d2030189401250f06540e04c0224017660003c55086840d0f040110b418007840c01c0c2485000c0c04500b81d840c0c5a01c0380800c060010303080c03440a80c40a40a1010f0200040d0f003925210700301c81c01414075070140042201d00c0c40543e034035904135000301d04c0780040d8090011402000c40c000d480681e500002d020340b03ea0726541c1e901c0c0042c44103040440303800c40910383c40b1010100d80890281002c09102000c591031410501c0226003482101c030302400d1110030b009082c0e640061440d40200902ca606290545449040050307146024500c01c84150040c10728001c242030955802003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 908935449 1250 908934199 908934203
    0x4080712030f2604060209040f0b09061008040f03020a1211010e03030c0406030b030a02030102120703180b13050c0a08071d011a030a0209030d0309020906090601210e0105010f03 78
    0x2119989591500c00c8403d2501c0c100d511a9010210842c204800c82c800368603508284501401440c03c80560081403c3d582c030b251000b01000e9513036100c8a106c0c01c045141c180d01010440c0c4000071000303413542c0500750340d4002e44003400046641c2062410103000b04008200f42c1d4100c2c0803604e0030012000001e01c1490002650011135003450300c08140c0d13400000589010b8030380201c010381070508151049000b0951030161540c50300c96600aa80981c030280300800d0b070b400f80c66411407581d241c140c0c409030560300e014011102c0c0074030b640e8841007c900f002401030b07000b0070b4070392400c6d0039148641040e0386082d40034012103900c080e001000044002d0005201002c4030b01a84000c05400c041901200400340d0134807403600b0160b0384919640300a480e8400950b07100103164001810008018042031078812030824030804241c0e1588410150314041901070b503c40c80c110303410206482c01c2e000080900c002042d11a43c2040041c10440441c00c00f90008030380c5541d11380c001c00c020341c0e40300c40c500d0001c2518441 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 908936699 1250 908935449 908935457
    0x50402040e01060e06060919030c030b130305070f06090b0924060a05101101060905070306170c100c060f0b0411030f041e0b0702011505030c0a0b0309030408071203 72
    0x602032041418010710f8220313001c1d00f0b1401c4143c0e0b24031041c00b81c5170340b1a01442d640961104654891543c1c140c2c2013001071801100b220881c241940b50098501c07001800c4c00b10003510b1030002e0030010b54840111910340764403c50009002d102460500c0203000320781c0009048103810400c004820b200094444124102203448242c40707a84200e00c0c40803c40d060362401d80200c4448003c0c170107403c1900030b1445920491030948030178041d4168560031160309400c18103805482c3c6040c80401c0758035010b42c902400c402c0728035480f00411540055031300c80e1328100541c0034000c4d229520349294069000b1000c40c0b5001802805201e801c001020014060780d0002c030320940c83c210584003144d082d1000d81c0d01c1707000c480103504503c0d140d6841ea03095001079071080e2036040c440303184078200080815581c030b8090304282c0c00100c0d224003100e0402da003807005078112602035404044080d0780b0b036072844004000c8820345400d6aa403512050019415442250410207180c840e407500000c09010b80b01d002c20f0340500a6171 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 908937949 1250 908936699 908936711
    0xc050f0d0f050115052212030c02011701080d0e0307170a1e020a0b0d1b0c03111b060c01090804030b1b0310060305150a0b070b09010e07030807110604030605040204 72
    0x110b00c1d14460152840f010004905000c40c1c03d80d484104581c8a00740e0841288220903070f50f981040447c60341c4e8000840001e014000040110b5802c000c60000801340016100d01560400106a42d5119031040307550401080422002594400f80148005030103080e6250b42400c032482c1600e40c0e80c1584d0b81085407180c84202041c9a01e81000700078804c0c02d9170040c40440007901d07046d103441c0c0300e420864507101d4456036521214800c03042c80c1d032101e00100c0d080e200c10108502d070303040240ca8481300450006103600901c0d94452010321507040e208090008540070303501d480032580d00900400d82480d00a250590000300803040c4004510f4581c46200401003001c1418056001030f0b100f03000955030742880071a0204184034450007500b2880e8446250315120282c07150b00b200082c08408154070000340e5550004d8810144403a00b054141d1245010000b03100c042090814295103060910010304004408940441006107009090b02244002840b1544840c0c4a0901c5002400d059804a200f41d00d460 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 908939199 1250 908937949 908937959
    0x30309011e0207050d050f21010608090a11010f020a0b09060f070c02130c0c0605010608091e19080c010c0504170105060d06020c030705060a0c17010b04090c050f0d0f0501 75
    0x8003c44141e541e01c04090890040403150a88031900b2006040c041c009040c015003101c040707440c418030201ca640f080310484951420078098621070014001091030f412144118000c02c0303554814189031402817a00d007d0145050004905102480780014508000e40d01441100302c6c0016025001e80510706085080d51200d4030151a86142044005d40104040450300310012050f40302e0951000d0074241419221026614242100c109030041004a945001803010060b03003044074130101892202c0c8002e1070362062000c079a84240c0c100400500720a9208a003003001100030a075044a042c101c001c2c840b04000c0b16001c0c1407500a0f00a2201c0490748140020030b00c83c050013120f00584d000f52001d001e1403d541c448202952010a10440c1031200300308640c0044c0081101a20801c1d100100007501458040002d02e280d41000303043d481207190340010720440c034042c0c04a03411241e10070300000b0400f400c900c058590740146034507102041c001060762000c540c2c641d0450905440d400302c041103513030f88813 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 908940449 1250 908939199 908939201
    0x20f03030c060f2809030807031812211406041a0f0109050d03080406050a05071b2f031c020316110603190e03040302090a0902040e030309011e 63
    0x4003201506070b1080010511480310075041c1500241e00c1520350760103240748550030500c8108820020b6030140d4031012201410f9000c1c0ca015003048940c5801c0c005540e0b605d5240b00715902c298405810b564100701c256480a003c1c0300c0341903c00341c8041d074072500035007007005200090803400e800d80c0c80c503214100000c03880c0c902403103403102071800204011841c01041081c0714000000d01005418080b5a01c004a10350381d50060300c44110340f003a0740c0e5007060300c1c01c0d20388803068803c0502002c08480c2000c00b0f01034140e40000804d40981414096074200785100c0c01e0000800f4020303560381c0c010211440b480c0d503115982c2c1c3c801c1d02d0360040079821503280303042024071300111199414050005070401c1c0031040c80042d0402c204c080c02c40c020f8801c540c0c0e0360701040000d2520340c025070f0b0302504202c0610b01e6a85031040b80c0240050700344450051801c0900d19000700700301680040000c04603542da0141d00f000c554a5038408540600e801080380e03142e00d4120a4030303009041e520b1004106201c10041c4c03010003005 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 908941699 1250 908940449 908940457
    0x6090501051c05040c0b190909090809090c13060f0201050f040201140c0319020309010207080a03020c09090a0507180b0901050d0602030403110a08120a0903090311010504170307020f0303 82
    0x5041629503282c4a400010303001420054401c44030003600d0316001400f228560090003c1800401005074081d45100c405410001c0617401040103d04159086000c608801c095070b28080d800d81d2040b001d9515140800010702c1010000c12071072a03e8131010901c20380c8032170b201514966940003000203072102454082c0720041110300078000382c1c1c03030700c044100d80c2c0040c0041c2c20110801d90480b401c1007104d90032010110f080052840069101050820b40ca42e410001c1500a00249020717014a00094070003d480e10092120700d80203d0a42c40450700381c1d601000b50540068120b000e44a030540c6902450016155102d500802030382444c00c541c4191402c886100c1c120740c0001c0040c00300c10303810750b81c41c0083c1d08001d20950901c050701c0301d50240c0907401d002501c003c4e44140e19283e5182400c02c00c100503000054031604003103103440204800644c2000b500d505580d08484000c07006606803004030340b24455600700c0c55070040b104003112507940e0000041c10100344212520b036190110310060580e00d0003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 908942949 1250 908941699 908941717
    0x7060903080c131a0705031204020f0a03050c01050a120e062706060d05030403050610030b010b03010602030d0b031c1d10020307060c090e041a011703090906040f050c040609050105 79
    0x22400340404c1100300503110071132500c00310807055050800c241c41c0c1c9411078106505900404104000b00b100311324088103100c0811000300d61000c4030a0030f40e1140c985d11701e01e00307411034144440043e0416906006a02c801c410a16403002404600d80c403220307064440320143c5d40682256041e00519000752800c0700ca4144541c09100101a940d503000100000045015025151800200b0010011030400c1c450b00748075080a00441c2d40c407034550710740280d0300305c0140d004181d010343c14801400615400308c226454045134041c00314406943d100062300700340c8940c60181d09100307983c507614030458101c881440e6160002c052442d03050007400612801029a038481c80041c0c0040003031400280043c0d101d030203d40045c0c5000c40e0110b84885107174490b00420b460540b03a84840080482580606641c06805480c00c4a006015843c0380c81d0160395174014604090300c249100800035469458a80c8441100800100103111504204051455030386c80350046400040d04040c01040b1540204100c0c0d00d919 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 908944199 1250 908942949 908942977
    0xa030834060b180f0103140c0a0b0903012d0f020a1403090a050604030503061003060b03010b07062004180c080a0b0301020c15061806211207060903080c 67
    0x160a5615000100b0818041560040d9220301d0407400c80416405503228941507444e1010550640c1004101c01d4072440d00002d69610100d401c0f0803985036000040c1c21a2010703041c03207840794a401c00181c050b2089040c4407101503030f4a10054010740c02030b140150440e8482008000260000064005a04c10442000049000114402d6040d8843c00c01076078001040b0050742c0c02004507649050030503406840540c0040c0010003801218a00041034014096040c101004498906200300c012404148203460000002050381c3c0180003d5402070311040781c01c04180014080c50400c0042140c20501070080309000d141c1c07403100002500d1040400d18402515401091780d42d00301820098008031714981c2c3c0554080c0200550040308100040041c803914244a4407490720303d0a121915048440003454809842c0911034940c644021401036013402d103e0b0f0320440420091070700d14240f49010151410f1000040420a100c1c1030790040000d1442641c03144100d454901001c80640100c0c0d00808000c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 908945449 1250 908944199 908944297
    0x301090b19091a0705040e0103320604120c0c0f06091e030204110d0c030605040f090f141c0206071404032102011d010b0301051e0a090305090a0308 65
    0x1030030364426150340301d03002e417610500d01615004c507140c030058203030701c11030b04d12403000c1145800e08107a1075000764041120707509070b6506541144d00d035641c580141c4007030000c0b154900406880c500c604901c24815810800035030b601d0b036641d075032504450006d1160b40c00003007007848049101c0050000e0f4005000000345843c030010700315000c000091421101c1c0c5040c03920200002030812006010f101010300040c0c8001501d0381c83c2c1800d20056905c1002081c8207946031100c0c05002840c008041e02070315400c5001b00701e001411030289450484400d00c4040860080b808070340d0300a50005080d48214025542c910b15200d070850500264000d50000070001901c0e144c0c0030b11030200c0000f00c101e68560510001c5403503500d0040c1c01c9444505401c1c0021242d4461841a1f4141800d014a075002511015800c034608030700f490760fa210a1026040f0729945441d81503600034140704030252148000000c1c22060081d5591804d030725654080381003000d0f4181d015035001051540c40904030300507140c2d44013806a07 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 908946699 1250 908945449 908945483
    0x6090901052e09050f0a06050108010602070b030a02160f0507153006080a0b0c1e1308030313110f0307060e010504090e030a09170d0806030c0301090b1909 68
    0x40c10004405034044811642c000032078500e10f00a0a02417850383d10189a0350030407030340f40425202c89070015414040e020004001041d07001640000710341c40d40c00c0039a10782d101c0750903800c064482c01051400b2807007440000f109004c090a19142e9003403192044410007656662801200c151022110021607400307034580c6012000c01030304041310f0000780d80c0c03501d01c1c06e403a000400880f0104e410640c1c456011b10081400c00c5400075104e81c000e40721103100c0e4101500800e011305060b5508040d0040a400030410b007200c482e80591000281c003024003541e803a49841c810700d1100e41c40215095485110b03290480d0824200b04410b0310608201034050209241031100a42c2c4482441c1c60250412800700000a44044144194007207050f82d40040e65807445ca124000300241c60542098505081d01e048410403441300141c02080c904050500345040da466400190504404481040d05942400e101400f041074403c00a032148210011711200300034442d40c80070840c0c4080c02c000381224625000980 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 908947949 1250 908946699 908946751
    0x105130b010801120807120509131401060c020102150408030402150304023a05030a02010b060f090108070c1a011815050904170711030d0c11040b010e0a0e0609090105 73
    0x10020740900c5d000c034a0304c8030070380c0c500070701040d040d003d07000042c40494150701a10b0901c2c20188071103954001800121541c1c2c03042078000c64188a013000740a038100f500000c5900900072801e0a2500080c032029526160800c21869401210124030903c2c195245890400182d41903d0080ea000741603507001400c090b000300b0400451341d00e03428040d082c4011018220214044201c0c4031407140010f0350b100d000140001c5d003034521200340544121004d100c45050260000203440307008200f440d0500c1300c0e88842500f520402c4603501d000e0000c2008040c60f09113075110310070a41c101c0710044480700d0802011300301d5030100d4503c8896801c0044d80c8207802c000d9072405181c9a0303000781c0601003c1314486244024080603900c2903d013154030724955490000d07145402d1103100c0e40750303880d030601c1120000183d98003101007440d03200c076920403aa54101c1001ca40d214100d1403514450140aa07501c03207440382080350310381900321001c0c0e00c41c181980001d6840c03c0e060168a001c0ca0400002c0c01d0719001c21a082c0d8 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 908949199 1250 908947949 908947979
    0x20705030315060903030f25051c12020a05070512040f0909080c060708010311060a2c040f021305040b030d210f0501080d1715040e01090b0105130b010801 68
    0x43d0311036814060392070107680a1009004030103994001d070303aa440e009240d04c010980502d0954074410182604000403500210300f400c1d00c004004036504100c0d5032040d0a4a0b1802c80d8005a0304092000c40c203002c0158100c4000c0c00d0705801482103803607044082141840318820380c0254002440c5050b030400c145c010070f4000311405c4c0d02c1010b4107410446600021458400112000000500c00c10010000d000100b40c0361074810310f0036180a031074841c0f0010003500724001d0542c2192050724040d00000094480c8169642c5c1090042051140784482400d040103504030740341c07941036031f0041500025640b82600c82c1310480c10010340606070094001c00180d0728000300c2c961002ca5910504503003592400036210340e1180c5171401500103013550402d0300340b91602101c441d484041c4200043c0041c0c000000c44c1c0b045521030001c0000e2400040c6080104002c0c000c181d035426115030a01c07000204214021540781c1c1078600c10748081d0200020000004c05503128006071030f01049440e4014810144001589 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 908950449 1250 908949199 908949241
    0x504050d03110a0602030f0906011d0a090c0806091005060f15070f0521070201020c1005091906030c0f21060b0c0a03030f0204050102070b070606030507080607120207050303 76
    0x10306030310b200c60807074603082120a1074202c0b1841c0e80042004000c55800e142e141d00208080c0052440c0e6040002050390210008080d0340c0e42e81100c800100b0030003076500300d080c085600c175000340c100039601c4087c02e0b62040c0a0b01d00d6401406010b1410322404403c4c4201441000010301c5505c090660f003090150203080b55003003150080d001c01c020f0307010840042c90310000500c540001d0142d1030036480c0354003121182240c0180d150b0401c01000000d070f0b0b0b0000e5000d04403402210321401d40c03c1c01c50000ea42d0703841a17480103500142c00203440400f50380e400101504a07910351b1000d212007107640000700c0b100c00d02c1c0242140030403c2000c160b00c4a00c050400240703203c0c0c2c0503200040c1d19881d6140c0700c4c445e8000c403c5008569200032010030406503d4051030b00b41081c10780c1e0540c03d02d4100710003c1c0d1503e88c00e006c0c000c0024030206d5000e0501c5207a40081006680100035903c06a854240e00c03074442034201d40090205204100313051484500d0301c00c59170b0094112001d5820f41e1588000031021f800d0701c2e03101d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 908951699 1250 908950449 908950457
    0x60f01080c0a0302160f051c0503061e030d180509010305030711130609050a1109030706081509100609081203010b1c050c07031d10110313140415060504050d03 70
    0xb920728102805d802200095000d4a0090f130741c443d051401529120120781e408885005079115611007540084c10341c2d401000c1102d4044a120543c014240c440d401300840c0c170341c5880707104803401d51180c0040f46825030307001740700303d880c0902d44401c14820200000c0c0300041c4668004c200c0706000c42d021100c0d680a844c80244107203114210500031806071042e540240000300d584800384004034110380300d00c6a68408244070142004813140020f902c804043c45070900380108200050340287c0302c2d00d400f103001000180403610303c1c2404030b685041b03031307074180120404511801c1002c268031200007602d2401c0201240b0040c9140e0925010a40940144a9030154841c03410503989079405180141c610615140115a80365219418000d0141039007041c0070b803a00d03501400105140c1c03103420015420344901d040440040340c0e0042010300c0d500c51001c03c0740f02810a4440030528039020032080202c100c0845050110311180c442e041e043c01c1c0584101004207404200c10885401e0001d002680725000c0c1c10 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 908952949 1250 908951699 908951707
    0xb04050f04120f03060e0708190c30020f0306030709020c0613022409031b0901060c031b060906051e07080a090b01090506040615140d021b06090105060f01080c0a0302 73
    0xa006c0a0910301a1101c601292802c4100041c40086901d88407406490480c00e0002d40e40800c0041d105518105c80c002d9034030007002800e1400c014070901048a40382405e0115540d201003c49175049400a80b0650322a005070b0030001150f114600a4404881e6410050001d0391103013200080003804401e0202c3e0041c1ea103103505156a142c0b031800103400c0645030060380d079440ca22410035003010300c1489480110f5501203401a150f860760741203d4155081810141c0440300d484c20305480800c40c0c00032180007080c54030211820400f5035003103012b090f8460b01080c0101d41343c3c100c01d641862400140f40e5031065003540061480c40c81803d0845d0041065000020000d01c10313101c2c00c2200d0300c03d80000b01000c1d02c0348180521800c00d4869038004088180800c02c46034100400144130090020a5040d01e440100d244141070045504882c0c000c0d00e0780050600d8a011810072580700d40c1c0c1154030348640c1d480d0400041c0503052040642c801c035001603480d94030386d0b901d5050040070740c0c00900f5500308240c0e0900c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 908954199 1250 908952949 908952959
    0x30603020d0f02241b19081207170708061302220806090709051023180903090d1511030f07020706140901210b04050f04120f0306 57
    0x454103008090240030748160821890050040e602c2480350b03264001c80b404020080d13143c400200391103801c549414218100c1240701e810a01d002d500c240e00550050304048110104013800300281006024915045031941c1d40700e00555001c170103200310782078056803000020f45161180510707a620a00042003e400600210300b003078100c1c0c000d05462600d101c040b0040384020050f0710000c0d402000c403103000708518034007204859284c0c202c511515a8407500c071004141c041441d2104000544803c0d441406003040d0780030f40c60010000548841d02695100780ba4010240310424590300c6001074000031071a00030180240700165000c400103a034804003905044110303107514091321841c840782d041e0b402e03220f0810625981284c0c802400c0310080d03600c003203010400c0d107410440e0000244000310036244c03142d458400582d401c0740d422140310b920b00825400f0001c81e102d5640004104902500d04003c1d9640700a02c5552844050b107015000c80710750041460f007244641d1109000854518010503220307562 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 908955449 1250 908954199 908954209
    0x18140409060f05190b030303090706081e04030503070e0d1124070819030603170c03070b07120c0305090a060b0d1703180d091703040e040c0302192403060302 69
    0x50350780042205614141480070640c034041c5c0c2c0c8080c0800c9019610f542055010310340c3c0d484a5110350003e01c40720318002000c0781c200381250303c140240c000c00341031149001d190041141d80201c0381d000114143c00e511040e207003010441c0701130032030340100030300b61507000041000503000464548803001041d445007600d000002c3c1014110440c454076000c1d441d5484505070424a100700c029600c101b625005082002c1080c0c03d01030f040490000c10002e035515a107010841c20752045c280c001e01030b044034100381710310190b1158001081d400c03506820000c4010401d2b00301c050320001d03965404036030311070018540032070711070751141c59000c200a2940b20b00341d00c0f55072500d600340742c0044d5022020350040100503405076640d040840010600340940390046405502414441c824042d0f400b0309030074000680021710007001203c1c041c00310203080800e2450686170060544001d40803c80c02040c801c51903105001080b08072400341d540ea442412020003100f094a030100d10340c2c050348001c040d200e0000101684803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 908956699 1250 908955449 908955451
    0x504020c01022d0d091a1e010602030a0e0f1f0c06270f0c120f060f0209130b030a0c06031505091e040c05100f18140409060f05 56
    0x114000540c50781c0c02010020449554031107031280700e043c05000c2414400300070307007112109003030100001a2071a26080405140003086070045240321210180f0007038100c05041010306a004400c241d1282c1e80300d4008a84074058001034002040203060081001c3c6002442003954880103880b144443d10400c50750081020302d80703485408100100d910009008641c00b83c82e4001c140b401d0805898290041d503903521400e1107401400c012969500c01d803c1100c6010840001c26141c810410148442d04000d41d4111020303500f122104d10780000036994003d14001d54540107401422520b903008110401030103802d40300c00c40340c0e040c01102c01e201c0002c0d01625001c2d001d0401ca550002c2d41c0c0c001030407842c0c0ca030b144541045114440800c204949036586440b03900401424980454468486207050340c0d410010790401688050700e81050001a075014600c0c20038200903036a40504011640321400000b4180e01808d119207040255020300f504140d080b50007071906c01d202c00186601a004602d0440314 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 908957949 1250 908956699 908956717
    0x308091002042619020d0f06050c0414090f06010f031b0905100e0f2209030c1a090309040504150c02070602010e031c0908250308070c0201020604030315050402 70
    0x40c90105610b81c081403e107180c40001c101c002c161006600380300c034801c007800c942d0007841003a649030403070204035a80e001e07003110940c481c509001f1340c01d11141d1030b00d4035007041c01500101d280900c180e042e24602141101d00a4400102000450301c400d0011280c400f51000345000341a00d450080d4940080e014140c1161845e40e514441c0050504041000380b03e8104614410440b00f10a41c8036242d0f503103156822020707030441c1c4003482013412030313881c2c0c0b021b2041709600742042d440c2040d0f030b6080c5500701104c41d0600e445001300c0c42540d243e49000c80041d00003590944259030040c051f240c0d242c2015031005801c180944003140100c103d2110150980c0c00500c00700c2c006030003007030040140300d07024001c1400010402c00507601f045450b8400048154090b040200405d440c2c100710001e00410504030b40000b00162080c1c0b1062001c06604c54003251102c1e000c41c0002e0f0b02c00002060144604106910700303505030301504640d02e0320748084026040c01710085000400410340040d0035a10385c402002544 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 908959199 1250 908957949 908957969
    0x15151811160b220605070e091b0a0905090a021308060108100c2f060a0c2102090607030c0209070507030203090d020a080f0f060604050103050718110403050a02042007030809100204 79
    0x101d400c1e040109025010044540102300034001c0c4a0000508042040308500a05282e62076011540b01211805515402182c2003031010301408166051a0010f000607d0586e07682d41c2602d90341d44602e596140709219020f1345400c0801c1d1542a141c4940103000040402d1620000c1d07803c003c807841c0ca004001040c24000c40f0b883c034240b540d20785801d100c8240d000900b0f060807c42000c1c40c410140080360070340030400d03126500d8110901a1035840e416070320b50b00000b4140c0380d192417107803074045e281d480c46010991149004100041e0715610401c01c4030300151b030650140d0b050184510500c8055004481e0407030340b01c21080700200c4c207004100a000c4d1003964440090040da10602d200c0c43c1403201c0645203900860405005102051001403035a08482001c075031654140e10344500e103c01815881582c0500300302c0002e0001c1407040000c3e4841034140211020000080c107182c1c16810000303c01c452619244e02030100c000468000d0300200d40c07140703070700041d10200b11310180c800d01203034056040201c140e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 908960449 1250 908959199 908959201
    0x20607210612050f0f0a0b0a020d060e01030606080303013b0a15090b090f1024020d08010f181b021c0807080415151811160b220605 58
    0x4041c0420044e0150740d4608040c14000c02201c050340d0326130030001d1010300b14808080114400e030441d54101c0701c0546054600f00201501d40800d604130910a10050740c0c03103400d10b8000f26a04c0b8001c13088078126001044041c000c013002000c0c3c2c8180000700620b0801482c45a405007918800d010650361140703000110010750303000607415030113400080782c20210388245010107804203515104022070b0041d004a41520b81035030f03100302a0943c00020740058602e10a8030707520080d0b0118980ca690380030b030456000c2e141030100072941210410400d20034050220724403413042007030400290079458141a21403000c20031001c456414900300c0305e4144a080103030300c42d030f08514680c0c410700c2c403420b152115481c000b803040c1440500100450406080604078118010a6501d0b00504e640708151014100142c07907100c3d940ea00d400384080e0800d041c4400441d080045041c070702ca2409089540001410030020105401c1e5200c00042840041800c0d00300c3c86200181c00244050500c100a080d200b4030010440b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 908961699 1250 908960449 908960453
    0x11090106090906080f06010e06030f0a0503070308180705010e0a0b030c040807171c09120b0a0e0307030c0f0f02090f040201020d0e0d0b060a05060a200c01020607210612 74
    0x1c84605031300c05080b5800120041c3e08002003c0340b250f04552035664040c1d00354650400190800c50505582d80507807080310004001c025020018041548c02621840f070f1542d5078500160071344614450402280c3c004180c02d00683d8040c501000f020000a40f910071080d44800d495842a031054030707038102c0c00e0f101040802000100f08103113005440c1d10718a81e8001c0c00e90008095031008071744402401d8140a040c0c6144180c45100e00c00e0050070f920703940e1000500c0c603041c2b26030350070002c1d84c10300030703660510070800b0f04198000221494035a1580d04c20089500985074071038000940d0307500302e5228030000300c03600c05a9200d0703540030300443c1218a6000b280c10305100282c0b4008200d042c10b000e100b5500d880b840035a5400c0e10140080340c00814407174486d036035000004c0d03030b040c420f810441e404180410f03840b104941c82250356244052800c84000074441181203180e42e100d11400d01c50050340040005004244603c0340310910303407016150301a0f51414420084d09480040d00084503186006002c181 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 908962949 1250 908961699 908961701
    0x60f08012f0703050c0c0907030b1206010518100b070c06020f0d08130311010c03091103030415050a0201020c0109030807020c09150d03020313030c0e160e0d110901060909 75
    0x2120910629001d04448611019454040d044002d01448404658100b14020a10507840f040c940144101c01c0b134a400d802c098000c0c205001002d00070200e094507030003500c2c0001045416100014026000252069910040d00308000e0075452551800800020011020740203040c8862003454040c225070f003406802072600403245035540840e8070482c00b0000540e00184050b8002c2c1c80044602c0e81d101c2c0718181070700c0c000d0f9600103405d46507207090030b4264580d90650000c5a05c92055103041540d005030800c0540d00d014502071895400d60b040003034041513000d280100705140307040c000507081c0042140124210742080e2010760104100900b0099003642c140b05100341c0050881d080240b60071f20032200007042c2d847c2e40300d03540501c4c183c0d000081418000c0040d01c0d00b540001200c04d58464482c607103c44200864800d000d201002c0402080c8a40c050f40721282d054095940c0e45280c4050b0310b000c0106100010324160f40360300f54031000d0401506d681c2e2485001c0c0106807183c03450589024a148 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 908964199 1250 908962949 908962991
    0xa08030a12060501140c010b0d1407080109170a020a0b0a02071101050a09140117130c150203030601080c0405040e210903061303030b0604060207050f01050903060415060f0801 77
    0x207458030340241030107103a0b000580441034050079a81240c64042404001303004061210025500c6082d0103411410406203522050103040c0240a8580c0c41c0e82d1600e40500f0f9466410004055820b000b401a126402e03232405048824054411243d000c8295180d200301404190b448248581d000a09402404410000f5900029007031805030f16020641e0001020b4017414090400c107840d144801000d140c1c0b044000e030344105244501400e2508200000402040100d242190080c048020005d01c99580b01c1e980d0300464040c0c0c019520b1a0703030f00801191003000042120035044402d20010502c1c2d25184200c900c00031a0301c0040003901e6160701c60182c400e1080001c074401ca08200000741090314041100f41d048071861000d5038640c1000c0c94160003038030780318600c0b0360800e8000c01e00080b101d80c0011110112076003903901000b510941001120b0074802d506010b038042e404a80410005084120030020400090a000590b680c48079034940003080c0607880110903a44400810010b5180740100c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 908965449 1250 908964199 908964227
    0x21203070b070f1704061506021606020309090a020a090b0c0c3102030603010603060c05030109060905160f120516020f01050f19140a0c081609090207020d020a08030a 73
    0x240d503c001c00741070080401075460f0010f00002c00140c0131034100003503a00001c00008089a022103080c3e00c42d00e009540b00c800b0004a80c500b0205000092101d00200441c1c41062010740404160394503040000e000e03522030002007040041c03030300001074000d40c0348020303040440c0d8200c05010f0b401035400070803800003044203195510300554200a03082000e41191307880d01d107070400400741c0c49981e40070001c0e0051695a101601e41800c04152003a0141d100d0700039410303a5441c2c1020044552103141882c211802201c00034910005004100e607068095201ca0045154600d0b111002c985080b451030180c2e00c2c152450302e07665504000000b000c82e018494681d01415910082006241000305001a4540034103210104004903444003003884c629005840c035854030100143e11030908800482c001c010000304600016681d0001c11031880070022803501c3d40a155803074078020781c20120014029845048120313880315600f0140801038a031b00541a0092104402a43d120450607a0240c0044022004 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 908966699 1250 908965449 908965457
    0x14240a110c1203030a150f0f06090b1905030402030c0d111305040f020f030304091a0f031b060d18060e151e0402041e0b03070501050406080f06030a021203070b07 71
    0x2d00c0c0d40c969000030540394080c90058000c501d0381c1892140003100d012981041d2443c0c158900085108100c111020003210b40960b581504e6a503100d01c0d010b15402002d0607101003400586008001c103108070091500180020240e40d86540100c0015140039000d01382220046002460040c5515000c44011840300c2d01e90001d01481ca444e035108508d408030410000d101d10311106200216440400c20781c0c010707001e18107081002c1007060107200e44207482300071214401ca0034900103000314100480c2c0d64106000c0c0071030341403800711a10100030300c44d0094130030500041e99507008500b12019000c0e4810009015200005500441e130360b11074185401c0c000e40d10039840c1c485042c4229400038140c4400c003100300c1407482c0e0b41034a980c030006000e0012800c1660005c41c1d05601d0480006030f90340314400070502201142c0c0210341c0e400c0191a140180d100341004581d6080000710050700111005500110040030384100482e0b0364002010400c181840d000703207600c0030403400104812440326039048901410 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 908967949 1250 908966699 908966719
    0x3010c090e01090c0302041701050610052109030f1305090703020f0d0b150c0c1201110421020301020c070303090e13030c0303060e130209010e0114240a110c 69
    0x18009070034003040c41582403059650100e0342c03070f41e8030036410307140a4001036001ea01c0d40401030030400d010780410f54942d403080500060045180c1d01660445651440499000c0349060380c0c1886520a80d4006205c541302d800304000ca00b0580340414000d00c10000b0400050300842c0c200024084030500042501007810700c1000b130400c20700005000c0e0342d000c000200740030468a00da90b020413482001c0c4042c44070401c41c08510803c00440100d400d040711001503c00c89022034030070000e06d090f98a0400201d4403c80100700602100030000003069601545083c40c1640d20f0b550350209089900517441c10b80c0d00e0300240c4040c01015827000c02a002012501d44040340740c10450100c040e60340840303e00a05000340c00b840e8108050003174000100506090301d52909500d040c00e041264110415002c0340300e881007c0010603040844c01c08503050310842c801c8600c90001601c1406074141741c400000359540100c44c06440300807414002000c1115141c1c0e10f1404e90300d41d0036045850702844041d0b0b1441144030030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 908969199 1250 908967949 908967959
    0xa0603030903022b080306030606100e040e120a09050108011a04151809021c0921021c05091f1403060406030b0906071707210b0d060b03010c09 63
    0x41e07030740a40c0d4044410340021904c0c020b100002c41002484805000d100c0030aa400784850310f00a54410754040d000c2d100b483d0355030030030000c110300c0d80c05510003c0b41c3d040b00c0040250505078080802d00c0c000008a6100e8900c0368a0b0620b660495200100043c0841a0600c40342d41d0080d060360042c440b180b048a40070754007200001003400b460051341c1c0011110341c0491541c501c00c60040c04500d800101980c009615605d0304406548520548615491082942c0041c030b5440c1c41041001904030a10001141d200701d01122414100303a4410218458130121078480c0c0b0301c4201c5401c8000c86a104c441d6140040300a02c0740008082c48480d2801c3d03610b002c51288150001e0080180281024165079070b59225400174000b840c1d40d42002d000d101108007001400d0000042c174500500480e15103185641991011129035131381182c255000580f900d009410030302e080c0c001c4002d01c200c0420302003164664036005c6004844a0a029508151908642d0740d55050a20501d446429940b0346100014104 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 908970449 1250 908969199 908969207
    0x90e0f07031b0b070609060b0609031c030b0a06082a0d0c1b0b0a0e0c010f0507030203270a061806050c0c0405040c030c0e1b1605240a060303 62
    0x29200c041d0a402c601c04001402c4602402418090400100c51a46425240c01d107100100a0b0b00c4045a54900d0b20000c80100e00e044415202d000d40e0060090074044980d02c0c403a40c02c081d020130322005050300c5031603034240c50b43c8108514025129075541d614052400c9220032008401c0d130008080c19148200c030550088451004640d8900d03110303600400e500340056422951702c640c12164a101180240c580c800304003029074500d000304500c40050000d142c2c2000c1031911800c58408203130210300000603801d10a0300036400341407298024019079061601444403484400320291f1505400300e181110628940b0301040003102a0006203805804d912401d405c4c010081d0550040200b80000401d2541407040304101c58402d021028004ec001410700b4034100040815500003103540d000540381c00b0070840707071154200d4440c0c200b0f1603c2e00481441e04800008030b911540d41d81e1181510a07030480b001c1501000841a0485566020090940c06100078200c1ca0700107092100028100801000440d501c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 908971699 1250 908970449 908970463
    0x6184b0903050a1803080c16080321041407060302070501230105011b1713091103070309080c07180c020705100f0512090a06050a090b2404090606090e0f 67
    0x340d00303060130800d40b00f01c100d091002035640000e1041400143c210740525010840c200b8180342c10800ca04e0f070f5034a07010180c1e12400f0b10050446a0500349140340140200c56a0041c1c01600841e1180741c101c84010825041088603007054010075000984402080000d2080d681c0d22918104d03c9404198642c818000004041c03080e141049a0007880e40300f2250000075021206500400034944205070070420040340c0c000c01130f120810021003e000034074400c2d034002c10110900d40c00304107107159510b13407080e4010011402c041d11092800c2c000811139110030071480014041086031040c010403407004e040241c4000c07950200454219007401c204980b10494102c2c0782c03400c9814042c0041c541460125000d0080200c040010300420051007070154000c2441a9050300400c41880a951038484042c15580d141100910ba00b00320b83c00191405034044040d44010481c80c40350324840c1158002409480d04484140e030b81c1580c400702004890740c14070441e20380201c2c1c10040c00c82c00841c064981d84400d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 908972949 1250 908971699 908971717
    0x10e012102060a1103040f17030a08011e03020409050a14030f0d0b030309090c040305011b050702150c01090b0f0703050f0408090d0c0b120a06184b090305 68
    0x440410b40d0f4600038043e00c4204502a13590b4100c98507503030344030100d100b56402840740728044444d504501180040c08070441d00090141d880311030b440e03440e06111071000f6221f2800c189100d1040200030006a9031030040c2d0600602410041034005a9802c08220004860032000e03065071040160480001003441941c040401c2c0850000d01c800d200c8011034150700c580a03a40d03501c180381d0001c000081180e14042d2050781e001e0030081148201c406150741c80d040c030055440300422418882c1d5001490020307280303944c2040e051040c0d801c110f01100c1c41829241ca200003110b144524000b00001041d003640c0c465070012061600b800141054089009586000f0b00b01510607503001a00c1c0800340c4491040e616056807200d00d40540d1a51010362666541104180201440480d00401c1420b80b25004a40c00c1d2107024003101111800010341c08000c054403040d451702d20f16449103a40c11703040010740c0e00059a0b01c440b80f4500a510200c1c001441c1c14525080c0840300f442c212203100865070100c00d48150407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 908974199 1250 908972949 908972959
    0x160e0a090b0a09090506010e061903080c0a0c0602010617070509010317070f0f020102150601120e071203180b1c02070201021509070603232a12010e012102 68
    0x410003000302d81007081c1c642112140c5414600c4840400200207540e5049560500742000161074020801444550080007910131b0030f080c050031300115284800038030540e841341c421105ca174201c0781e030780c203283c01d81c21791151026035512a0104440000c01202c3c00e48044003102424a00f400c00c0001525600107020180104d43d106252040c1d24008070700b01c8640940080310b440d06000720b803030843d4445861813412030050240c071041020403c0c410f042c07580038030016111458102e890300708600007456400d210f04401c7c4550b4900040c140040f000400d1440d001e5606d114015004104a440c451342035800b01a03a15000c21041b40d0000c030405140742e528800007400760fa60710103800101e00d041108a0100c85e1440103405000307402400245940807107005440074408020030118110b0001955800b680b03042c110380000034900c0b04500004480210721410850b000e1104042241e85c941015042e0a061036070030b030050040d000400b0605004003641c1e101c80c42c403c581c5c0b5214541600c1c0c2c844c0024011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 908975449 1250 908974199 908974211
    0xd2907031a01141b19050c0103060b03150906030c04050c0d1104080c0d080702091003050c150d0e28050c0a061b0303110d050612060708011401180e160e0a09 69
    0x603000c1170202c5c84100840c0d6400c00010300c001e0501e5030329501c00103101400710f07103001c2c070010301e020030b02c010b8900c1000300260f5040a07000141c01c2c88401d9000604103a89030062000e42c0351070395a10b201d06409000300560302078486894001840c110f03803e06d525610085000c4c80100010300700012980e01000007038517002415113491034008028000c1141c02035000013a0b004020100e02c0ac0000e40046900850464008a4480003032040c0c0c0b000162a19105000402405175200095004002000301c0d00080712102c8410080744481c042280a4004440e4012084d83d401c0c88000c1010b1000001c0c210740c0e50007414070705078001e0146403840c558107820103805802e16040c18065402035102d00c403141c061359910000020b03880010700080300c2d900e1080d441020a4400c040d00000c106100c0c072104d4441e008164204101c41c1c42c01a0300b504940d0400645a00001e64103800b0030088006006420a01c1d100f401c00c00701d1625004c100820590810000c240110010394034120440308980c0420800205 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 908976699 1250 908975449 908975497
    0x2105250317070f031a010e0d1e0b0a050627150901060f11011107140a021801031e052503050f0610090b0d2907031a0114 53
    0xc9180e2034030301c980e1032640101045106908040303100c0c501c881c143c2d0200004069500c0c6500e07149101c154590014031303603410f1029141490805607000030701801031059010903d081441c03040000d02c2c0c04443c0215440c043c8800d0340468040e17203030040c038112414542c4000000c084112626402c8094441081c2c8501040806075100c4001c0880d0b04040d00305255581c6031036015001349422501880042c03030204150101140c18403451001d0440040c402d4a003074801e46030705920314200c0e03c10010500a002d11440160381b0350300c004101480c1601e0491856144d82003000c1580103c005542820496144c2080000c4001c80c005000c10900480c0c40018840540306981070403094000900304d21808040506040e000507007d0f01c0341d8031005000000503280c0f030001042d140d804c4030f40358200040b8034020000500c0c0c0c0c866003880c0f4041c0b0441d0b0005105545041107202c400303a88140c00b103642e90020081504d02d102c00d031000701d0350a0074182100716890701042d216124103507006000704080311186031 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 908977949 1250 908976699 908976707
    0xe0402040914070e10240f050f12060a05030c0f091816030506180d030513080315030601050d05030316051905120109090f02040f0b030a21052503 64
    0x91442d902e01c040f6083e0f1501c8401c039032210f40003030b140c54400e00c01d12400026007040385850030084840c040b40b00c944007030300744805584c00e10702c5100043c2480000d004003210310580001500403103050541c0c01002d03080c4407082c4009034010b600000d000ba00440069041c644954400004084095138040d4559403060f42002c070f4450030fa03142a41c01e000302d0304c80c181a203001043c52426a0f00610070b48581e900c0f008098601c02029a4810070240c1280e01c0d004030003400b903842a50b00014016500340008442d40c0c405507241e0045455100c205645810709099040400c0424050501602c0240e0344142d50f485890352400000e1a03503840c0070369589a10100e61090b016102140d071513440d2844024000140600a42c0046070010210380c200e0700000b030305814034051015072030381128010240d800c030394082c0000340c848100091413143d25165903200684042180301c001502442c4036146082c3c4020b0030f0981406441882030400c24103100d100c01a00f40610200d008858200c62a10f9180c46446d00356 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 908979199 1250 908977949 908977973
    0x1b020402160809041404030207061202130801020d060b1e090d050303070c0524040803100312020109020f0a080304120609060501060c051c120b22060501110303010e04020409 76
    0x1105040103051480810404001038402c3c000d00700d609015088070969101d01e031080850380600160702c23504080002c83d00481c01030b441c0c0340000001500c0c15a8000064003440120341c0243c88aa40c0043c600340121001d03c0380e0400f82c600003c00310b00c0c1103441d0001051038482c42c2d0b01d4071411440041d104505030f9421624070200f542c8601500d03203920701210040c0c50311540000a0300c031405108115952021038480e5840071003080d4003a02080e441d5500c0e4008940c00c01014a00c41d1091104040301151010409191281c600d90010410112503c14461038401c0c03074000c40e02600135403c040c842110040b00f0b407416100d50903161850b500050810714040c105000c0c001d80b8461400300080f80042d80442078189550003901100d1209036110b01561212025010303080000d02d4140b610301041450b03070001c240e4114002e08040c0d0f107803185035015403c050044820505940e40b90420001960485041c0303241080c0301c009982151b1510301c2c0102d428900802c001d109982d200c50071001c2051402c004 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 908980449 1250 908979199 908979217
    0x1110a17070e100512010f1d09120901110f0102040609080c060a0806060f0c0106140102160e09030918090616050301060e060d050403020d0e030a020f1c12030603030e0a061b020402 79
    0x7801741965101d5110010200c40d0043c002e900c00f5000f13116a21303440c6103e816000e0f500315001010b5000041083c00140d070452a40c0d17604218101e1a1300c240341030104410090b203c6d1180c0016600c900d4400d014116141070303404914182c00c102c140410740e5480360f05440945886050004042d5a0280003404910400c060950800000b0827038083c008070550007441516030008201c000e0741000001681c0e1159110f000e40150103a01e1414001d10040d14403040c0c1206020048a042c403c4c80360000307184a0510f00c107013404079440810011340f002d080091681201d00b0305400142c4424203040104140b0050055109001440c1214185a21210300b05d840e20821103c04114a041500d4000c0d1507510540d800320025884424081e62031802240040050740d00515160000542200f48200440422864401e0300225146540402c0310289180300c41111a5400a04d6505614002d0400002e0307284450103040d82000912003544c102c854810450307001048400d4070703000340c400076000e80b00b00703d16 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 908981699 1250 908980449 908980477
    0x1b0806130204120606061706090402191505120606030c040e130f03080601020601230405150d14060108011506300f0b0603091c0c0501110a17070e1005 66
    0x1803e00b030045139032068054030400d666040380302e5007412050481c0384003602c909510000c1c0c400480d0051406203284040400c400e014136403c036580745040c2c903003004501c541001042000a60b42c40d103001540e00700b0f0380031404483c86825400c2c42c407010036550095005200d200144c41e00401da010094000c14960f503a803080411045440d180f800810410013070300e086015114a0001242071000c0c030742c400748241800c07500d4128000c2004100b01c068030000c1c1898000127400d81480d8420340302d100e80e843e18140a05503520205060108503403078200140d0103048183d250004560070000460f40c03100c1180c00c40d203071501c2c40540303c001500100c260018440512010100c0c0c41e0402d04079500035160032885a00c08000113084841030064900c011128500070360132a201c0d840302c51100c0307611814441c0c110310b400c10b0122001e81c0c0e09421548060059008140b010a07000519644038000740303403010745440c0003902801c000d240074060a110b12040f502c00d1f100380da001d062040c807070b4081d40c0d02c002001c14 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 908982949 1250 908981699 908981729
    0x30e101b03030903170402030d03020904060911130603050402030307021e120c150c15100b030f0a0509010e0c22020d09050c030312060112020702221b0806130204 71
    0x24010b001000200011004900c80540580e8204150240c1764800c540141c00313080481405c00048000b980081d402a520070fa8519011424081500c035180f14054290502c0c0d60301c040b03560080c01c0602e00c0da4403800c01c0500b804100001038a011064031800340c1e055504100f003100006107280c6c00c07043c00300215080750b501d040c01c0e24514400510f4904180041d0b60900b11040c511405032150b115014500301e4651041000d0108142e5020f03104e64004000b41d00e02d074030700303845060745103d9a009860040d8400504014060901000e2195503000850303d40200608070052008581300da50b0180140e120f0607812070000e00d0704401d00070b1001581c01c483c0085544041500004009094541064545200c2c01da0b000d05142000070865800c000c0081c10408540d641e0740045035036102a10050030140c6e001e2041e079006845041010341c0d4510700a50350890503d034000d401045446031800741c071a6401c5a01c1c0d989405410a041d5034100c0d1080d650300c00060551803080c1e01902c10751740802a50b2403608 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 908984199 1250 908982949 908982953
    0x2090406020408160504150305071401020c0d1a100510031e0c020109110a0308040e07140708070b0919020609030304050a0803220e01050d051c0306170109030e101b 72
    0x444c03000140e40040700d04106005888035190362001c15400001e0041e4080340741071207042044541c0010301201481203c10100702c16020801e4040c5401e001c4848900ac031102401e50242041c0e1a61310440c0d200ca5548907030710b05800510b0b01c840307900001c81410f95610750f50118525041d007099041e04c080f1000d2141c440511402802052000402c0e0749218424003071140d030f440c003401007900302d0741c002a5280c1803d003811b801c0441880060035540601c03c4188034808006e40c0080a000440c0c0030b1010a500c3d4074481c201642c072800000c062045070b403c681c422514004064404003421354040d110291109403d402007441c50bc00d6800840d071141042e07074006054080007004089140a0034035071000704c0007000ca850035540c0c060140c120f4181c0c0c03150041c000b03400d00d8044405031a002c1c0d01202c007082c80948020b0100b0081c4400c03d0b0029480b103600f40050755100d0808045896000c0080100200c40d07140141410603805419110b0480084920711051064462080c0d41051210014650314a4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 908985449 1250 908984199 908984233
    0x70519200a0507051c033c0e04090308011202010c05120a0f08010f051c171308030f07031b081c0b040c02061f0b0301090605030c091302090406020408 66
    0x10501c11101407080c0480420300d03003800c0c2081d101d0407840d03130040c000ca000159800c0ea00c3c100e003a03019800d417051010f070010a100d041640705a110b001031400c144007005c6810004c1601864441d45401141086001d0700002d034011f068504440c080c009100c044400c41c0300488030070b020004040e1003441814140203000040700000c0a680c020f03602c45c4003041d03c44001c10b441d0600d09100e450701d9014610004c100c035040402c0101640448281714400084199450070707900503900d40344542010011410300c12401403400120082c1c0f0b8000010360078105035141c80021881804002001c01c8002e080c880030904504c0b5550505950150450b07031a031b42c0d5002c4c2c03464024011401c603511030341404c1c408841d5003403a05c50141040e01c154043e0420b0398a0701e0032220744001c1c42071080700840700c071500080c2252000000e1806800c0c000c10100d90240b600e0300701498840340355560f5100b0100c0406000e0601d110303c401c51210741c0d0680d081c0003103a83e07d0414000030f0240da40b180340f15000d132082130300c40c0b4008 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 908986699 1250 908985449 908985463
    0x1d030901030c1106040201080a0f020c060403080a0e07120c0807030818040501080d030e03090a06171501020303040f0f1712010803042126030103030e060307051920 72
    0x80e40c0400902c00c00050031204085007480801154104401003409548180c501d039a1000743c160002c20340a1440c04d2a8080742d02c030030342d040010b8110509110405038801da10171307040700301320106020490908004c0c40d01d40e0036501c621030b00642804180e030b04226030310400c200100b80e2201560052641c2c3c0c180794000781d0003c0300c0c8445118410460740d83d2440c1c58800d0f18162401c00004010000c0c8860054008100c00d490f007620134442401002040c0d0b841c040c00e64042c142c00d0b40c8001185a988156921221001d021441881c10540c2c81c0907447e41c0c000290ba91058001800e41c0e04491103090204406100c03030b1003c0c103490340c4070502d91010390450300140b40f041100340e100040c5a0740c80c0314454890180b03003d4580d6155540420301e4607055500036402900e8081c4003c0f1066103030002c1141c0802d98055000c1a00241c088010428550020240000c04000380c2d03505d450341c6040703040107090748500d80c0880c2c40c00c0d00542c01004810b00c581c89030180308508902c490302c804003194403075a94104d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 908987949 1250 908986699 908986717
    0xc020f191502120901050310090f0e06060a21030504091103040203190b0a09020609040203150a12020d06050702031306091802070b1b1216030e0a050601181d03 70
    0xc1c0340c080921925100040e54452040341025403070410001d403004543e01d071f001070620601034200400108034894144124182840700c00c8001407101894075a007401c0050040080d4441c42d16184200080418180342041034074001022000403465403500340c50901440d00110071407803601c40c1c0b10410381c28104c000c6018500031070484008007200210600c964808040060003203403010049045940203801251030540b005042600b00312101c8041000ca8104441507009442240150030080c1010703a01030003d44154003103c0a140740c01e40100d0074601131100300078402550350700011521442441a144219071107070900f000380da07407600014400d0304640500c7e50306c00702c15905d18078803031400c2c802ca440469000b080e0507490303510f13484038400012111404802d80c1004019607000200341075400c3e4800c0c00d81c1d0a1030082d0210540000303045071240c2c2c080801661028080901041000401c141101c4421000b0f220305c004100d000009894401c0d20f00d4507510000002c07101c54040403000d801e44039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 908989199 1250 908987949 908987969
    0x206070605160e040504170a0201020f180109080303310506040b07090b040e13081e070c0f03081603141b010c08042402070f08070311030903030a0c020f19 68
    0x3c1410080100700c880954008000300c21a002ca981e00908410144c0400d417814000141000040b08400a80ea480700411026042c04154100015a0070900100c0074084800085085190070341d480b22201c0c220b2240d501c2444404840805503480b42110950090303401400d0302c40d2401e10f0300e080841140140c0d500400b16042900202e8020703050b2041e076007158989034000005445141210030040b11504054441d90301c10828500c1c03481391200400c100141d80050a540c0341c42e24241580030100a402c0b000f8001c140800030030200d400e4605840158032685481c4d000c001452a05481017032403a40480e140e04000315511400c8005460902e9558808000a02c00d000400000720780a6108440c014040701034418001100304000382c81c24404807a250703006181c030000d511580036010110004a03200c01c4002580c2c4d0405074800c01a0f82048603c000540c104590200020380701e00a05a40c00d0030000c0e031019090540d5984020798100385000350801000700c40560340c14196000340e01401c0100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 908990449 1250 908989199 908989217
    0x18020703020c01030c09121a0f190c17060a08061509100501020303010b0c0708072414040902070c050402030a2f04030b06040b120105150d0b0103080304020607060516 73
    0xf54000d02841490002641da00481c4504180c0c110501c00001081914075507001d1200fa0503000900185e80e01030b0042050529452502800c1c2c40705076110300e001c055005082c0508010000e8110700850840301d4441540c000c0b9550b00b4012a0407040c055010b516140305e40c400f0b101000c1a02030807004041001e4a50a4965890200f00d170a140361038410303a03006a10420040200d01e64400141440b108081705903464660b07107104141c949041c82d0421118008490007141d102d0070710324004100004541880c0c00c0403038000d014502c4900941c031991031f100c1c1d000070b0100c08006648180340040c000c02001151241010441c602c01800d1000d40d525101d0143c010010a92400124103c60b00c010800c406181c1400c5030303120150480b0140900380c009071150030800c080d070354030060803c155074190000511440c1c1010031003900d031f0019080071300440020403ca000f24210300ea100381540c7d041030955980e91524404502288201c4501030301300c1c0d281c28180207000621200901c0624500d0350780b02c0c40 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 908991699 1250 908990449 908990473
    0x603010906112d03040f1b060206270d0e03070503030403150612050d201009030e0a0f0314160905090601091806110f0c060108010c0c03050304030e0a1802070302 71
    0x11112045450240f074405000243c00180e4130f61300d04000354450701c1013284846c0960f5854140d4195a0094409600040104201d80c0d029201401400340e030402028813a0014810194950180000344420004440e144020701d0f1020480500103140c090102d0382c0c2c1c1c0341d0b2414031008440742d9901d85500a0f0511800291141a00e1101180c040d081000b609050a00341c006032044084e0101c1c0d1480543c6c403c50340341014905010000140c550340c400450010181d1a000b231564016051191080e100b5a2091000144c1d140170a8103696010003c1110b00680a624524119499280c2c0c0100b6001c4800410200c1c8280c0005000c6c0000c1c1c802c81c2c03030341e0f43c80b00521001d03980d15110403d881c43c608046040400e4540d040343e800b903040c480e050307894030780300000b4904542c1c0102010103851344604010481e0f00e80c01d02c100c0b41c160000380344c82c030110001540e00400b036204c007400107030411000c0803d40701d050343c5050001000b0040200003240c50103402014502075000709800350091301038401e40360b0b9 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 908992805 1106 908991699 908991757
    0x120510090c0309030e03070b040b030c04050a0605040611010b060910170c04030c1226040b0a0909150b1c1d0105040c060908030d05060301090611 64
    0x35260f026414040c11340300460003454001d1340b02c0c0108202211550084d00c0c140d58403c1d81403030381c81d180c96000c0d0b4250b01485d008903501210811000450340d4214006000b1038601c0d4450b8548001c805841e6400c80303e9a5004030f40052040110006501d0300000c501041055070802030b80000001c121048041411121384c070040134005014010b1108409800c801040b82850106a103040340d03039a080c8400d15001c1e001074424800c650070555517000010350f80a0721001100c0341d25540b01010091003061a4803650200511f031a01d0005c225207003000320340c159441d00300c1c05031a150070a00008400140940c0e58602d15035030b030004c0e46100249010624001c0c2c2000d002090500740b9040032201f943c0e1036030000d4103000640d03000300300d990400f01c2510710115140c58001016a60000400d014201142c2d00502a51034084c8141e0300002a40c06000340c010f0019a03045000c10701e000c0e0103 = true := by decide +kernel

theorem cover : BRFrame.Cov 908812949 908992805 := by
  have h0 := BRFrame.cov_init 908812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 908812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 908812949 ≤ n) (h2 : n < 908992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
